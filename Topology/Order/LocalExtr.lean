/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.ContinuousOn

/-!
# Local extrema of functions on topological spaces

## Main definitions

This file defines special versions of `Is*Filter f a l`, `*=Min/Max/Extr`, from
`Mathlib/Order/Filter/Extr.lean` for two kinds of filters: `nhdsWithin` and `nhds`.
These versions are called `IsLocal*On` and `IsLocal*`, respectively.

## Main statements

Many lemmas in this file restate those from `Mathlib/Order/Filter/Extr.lean`, and you can find
detailed documentation there. These convenience lemmas are provided only to make the dot notation
return propositions of expected types, not just `Is*Filter`.

Here is the list of statements specific to these two types of filters:

* `IsLocal*.on`, `IsLocal*On.on_subset`: restrict to a subset;
* `IsLocal*On.inter` : intersect the set with another one;
* `Is*On.localize` : a global extremum is a local extremum too.
* `Is[Local]*On.isLocal*` : if we have `IsLocal*On f s a` and `s ∈ 𝓝 a`, then we have
  `IsLocal* f a`.
-/

@[expose] public section


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [TopologicalSpace α]

open Set Filter Topology

section Preorder

variable [Preorder β] [Preorder γ] (f : α -> β) (s : Set α) (a : α)

/--
Definition of `IsLocalMinOn` / `IsLocalMinOn` 的定义

English:
definition IsLocalMinOn
  body: IsMinFilter f (𝓝[s] a) a

中文:
定义 IsLocalMinOn
  定义体: IsMinFilter f (𝓝[s] a) a

Depends on / 依赖: IsMinFilter
-/
def IsLocalMinOn :=
  IsMinFilter f (𝓝[s] a) a

/--
Definition of `IsLocalMaxOn` / `IsLocalMaxOn` 的定义

English:
definition IsLocalMaxOn
  body: IsMaxFilter f (𝓝[s] a) a

中文:
定义 IsLocalMaxOn
  定义体: IsMaxFilter f (𝓝[s] a) a

Depends on / 依赖: IsMaxFilter
-/
def IsLocalMaxOn :=
  IsMaxFilter f (𝓝[s] a) a

/--
Definition of `IsLocalExtrOn` / `IsLocalExtrOn` 的定义

English:
definition IsLocalExtrOn
  body: IsExtrFilter f (𝓝[s] a) a

中文:
定义 IsLocalExtrOn
  定义体: IsExtrFilter f (𝓝[s] a) a

Depends on / 依赖: IsExtrFilter
-/
def IsLocalExtrOn :=
  IsExtrFilter f (𝓝[s] a) a

/--
Definition of `IsLocalMin` / `IsLocalMin` 的定义

English:
definition IsLocalMin
  body: IsMinFilter f (𝓝 a) a

中文:
定义 IsLocalMin
  定义体: IsMinFilter f (𝓝 a) a

Depends on / 依赖: IsMinFilter
-/
def IsLocalMin :=
  IsMinFilter f (𝓝 a) a

/--
Definition of `IsLocalMax` / `IsLocalMax` 的定义

English:
definition IsLocalMax
  body: IsMaxFilter f (𝓝 a) a

中文:
定义 IsLocalMax
  定义体: IsMaxFilter f (𝓝 a) a

Depends on / 依赖: IsMaxFilter
-/
def IsLocalMax :=
  IsMaxFilter f (𝓝 a) a

/--
Definition of `IsLocalExtr` / `IsLocalExtr` 的定义

English:
definition IsLocalExtr
  body: IsExtrFilter f (𝓝 a) a

中文:
定义 IsLocalExtr
  定义体: IsExtrFilter f (𝓝 a) a

Depends on / 依赖: IsExtrFilter
-/
def IsLocalExtr :=
  IsExtrFilter f (𝓝 a) a

variable {f s a}

/--
theorem `IsLocalExtrOn.elim` / 定理 `IsLocalExtrOn.elim`

English:
theorem IsLocalExtrOn.elim
  given: {p : Prop}
  proof: Or.elim

中文:
定理 IsLocalExtrOn.elim
  条件: {p : 命题}
  证明: Or.elim

Depends on / 依赖: Or.elim
-/
theorem IsLocalExtrOn.elim {p : Prop} :
    IsLocalExtrOn f s a -> (IsLocalMinOn f s a -> p) -> (IsLocalMaxOn f s a -> p) -> p :=
  Or.elim

/--
theorem `IsLocalExtr.elim` / 定理 `IsLocalExtr.elim`

English:
theorem IsLocalExtr.elim
  given: {p : Prop}
  proof: Or.elim

中文:
定理 IsLocalExtr.elim
  条件: {p : 命题}
  证明: Or.elim

Depends on / 依赖: Or.elim
-/
theorem IsLocalExtr.elim {p : Prop} :
    IsLocalExtr f a -> (IsLocalMin f a -> p) -> (IsLocalMax f a -> p) -> p :=
  Or.elim


/--
theorem `IsLocalMin.on` / 定理 `IsLocalMin.on`

English:
theorem IsLocalMin.on
  given: (h : IsLocalMin f a) (s)
  statement: IsLocalMinOn f s a
  proof: h.filter_inf _

中文:
定理 IsLocalMin.on
  条件: (h : IsLocalMin f a) (s)
  结论: IsLocalMinOn f s a
  证明: h.filter_inf _

Depends on / 依赖: filter_inf, h.filter_inf
-/
theorem IsLocalMin.on (h : IsLocalMin f a) (s) : IsLocalMinOn f s a :=
  h.filter_inf _

/--
theorem `IsLocalMax.on` / 定理 `IsLocalMax.on`

English:
theorem IsLocalMax.on
  given: (h : IsLocalMax f a) (s)
  statement: IsLocalMaxOn f s a
  proof: h.filter_inf _

中文:
定理 IsLocalMax.on
  条件: (h : IsLocalMax f a) (s)
  结论: IsLocalMaxOn f s a
  证明: h.filter_inf _

Depends on / 依赖: filter_inf, h.filter_inf
-/
theorem IsLocalMax.on (h : IsLocalMax f a) (s) : IsLocalMaxOn f s a :=
  h.filter_inf _

/--
theorem `IsLocalExtr.on` / 定理 `IsLocalExtr.on`

English:
theorem IsLocalExtr.on
  given: (h : IsLocalExtr f a) (s)
  statement: IsLocalExtrOn f s a
  proof: h.filter_inf _

中文:
定理 IsLocalExtr.on
  条件: (h : IsLocalExtr f a) (s)
  结论: IsLocalExtrOn f s a
  证明: h.filter_inf _

Depends on / 依赖: filter_inf, h.filter_inf
-/
theorem IsLocalExtr.on (h : IsLocalExtr f a) (s) : IsLocalExtrOn f s a :=
  h.filter_inf _

/--
theorem `IsLocalMinOn.on_subset` / 定理 `IsLocalMinOn.on_subset`

English:
theorem IsLocalMinOn.on_subset
  given: {t : Set α} (hf : IsLocalMinOn f t a) (h : s subseteq t)
  proof: hf.filter_mono nhdsWithin_mono a h

中文:
定理 IsLocalMinOn.on_subset
  条件: {t : 集合 α} (hf : IsLocalMinOn f t a) (h : s subseteq t)
  证明: hf.filter_mono nhdsWithin_mono a h

Depends on / 依赖: filter_mono, hf.filter_mono, nhdsWithin_mono
-/
theorem IsLocalMinOn.on_subset {t : Set α} (hf : IsLocalMinOn f t a) (h : s subseteq t) :
    IsLocalMinOn f s a :=
hf.filter_mono nhdsWithin_mono a h

/--
theorem `IsLocalMaxOn.on_subset` / 定理 `IsLocalMaxOn.on_subset`

English:
theorem IsLocalMaxOn.on_subset
  given: {t : Set α} (hf : IsLocalMaxOn f t a) (h : s subseteq t)
  proof: hf.filter_mono nhdsWithin_mono a h

中文:
定理 IsLocalMaxOn.on_subset
  条件: {t : 集合 α} (hf : IsLocalMaxOn f t a) (h : s subseteq t)
  证明: hf.filter_mono nhdsWithin_mono a h

Depends on / 依赖: filter_mono, hf.filter_mono, nhdsWithin_mono
-/
theorem IsLocalMaxOn.on_subset {t : Set α} (hf : IsLocalMaxOn f t a) (h : s subseteq t) :
    IsLocalMaxOn f s a :=
hf.filter_mono nhdsWithin_mono a h

/--
theorem `IsLocalExtrOn.on_subset` / 定理 `IsLocalExtrOn.on_subset`

English:
theorem IsLocalExtrOn.on_subset
  given: {t : Set α} (hf : IsLocalExtrOn f t a) (h : s subseteq t)
  proof: hf.filter_mono nhdsWithin_mono a h

中文:
定理 IsLocalExtrOn.on_subset
  条件: {t : 集合 α} (hf : IsLocalExtrOn f t a) (h : s subseteq t)
  证明: hf.filter_mono nhdsWithin_mono a h

Depends on / 依赖: filter_mono, hf.filter_mono, nhdsWithin_mono
-/
theorem IsLocalExtrOn.on_subset {t : Set α} (hf : IsLocalExtrOn f t a) (h : s subseteq t) :
    IsLocalExtrOn f s a :=
hf.filter_mono nhdsWithin_mono a h

/--
theorem `IsLocalMinOn.inter` / 定理 `IsLocalMinOn.inter`

English:
theorem IsLocalMinOn.inter
  given: (hf : IsLocalMinOn f s a) (t)
  statement: IsLocalMinOn f (s inter t) a
  proof: hf.on_subset inter_subset_left

中文:
定理 IsLocalMinOn.inter
  条件: (hf : IsLocalMinOn f s a) (t)
  结论: IsLocalMinOn f (s inter t) a
  证明: hf.on_subset inter_subset_left

Depends on / 依赖: hf.on_subset, inter_subset_left, on_subset
-/
theorem IsLocalMinOn.inter (hf : IsLocalMinOn f s a) (t) : IsLocalMinOn f (s inter t) a :=
  hf.on_subset inter_subset_left

/--
theorem `IsLocalMaxOn.inter` / 定理 `IsLocalMaxOn.inter`

English:
theorem IsLocalMaxOn.inter
  given: (hf : IsLocalMaxOn f s a) (t)
  statement: IsLocalMaxOn f (s inter t) a
  proof: hf.on_subset inter_subset_left

中文:
定理 IsLocalMaxOn.inter
  条件: (hf : IsLocalMaxOn f s a) (t)
  结论: IsLocalMaxOn f (s inter t) a
  证明: hf.on_subset inter_subset_left

Depends on / 依赖: hf.on_subset, inter_subset_left, on_subset
-/
theorem IsLocalMaxOn.inter (hf : IsLocalMaxOn f s a) (t) : IsLocalMaxOn f (s inter t) a :=
  hf.on_subset inter_subset_left

/--
theorem `IsLocalExtrOn.inter` / 定理 `IsLocalExtrOn.inter`

English:
theorem IsLocalExtrOn.inter
  given: (hf : IsLocalExtrOn f s a) (t)
  statement: IsLocalExtrOn f (s inter t) a
  proof: hf.on_subset inter_subset_left

中文:
定理 IsLocalExtrOn.inter
  条件: (hf : IsLocalExtrOn f s a) (t)
  结论: IsLocalExtrOn f (s inter t) a
  证明: hf.on_subset inter_subset_left

Depends on / 依赖: hf.on_subset, inter_subset_left, on_subset
-/
theorem IsLocalExtrOn.inter (hf : IsLocalExtrOn f s a) (t) : IsLocalExtrOn f (s inter t) a :=
  hf.on_subset inter_subset_left

/--
theorem `IsMinOn.localize` / 定理 `IsMinOn.localize`

English:
theorem IsMinOn.localize
  given: (hf : IsMinOn f s a)
  statement: IsLocalMinOn f s a
  proof: hf.filter_mono inf_le_right

中文:
定理 IsMinOn.localize
  条件: (hf : IsMinOn f s a)
  结论: IsLocalMinOn f s a
  证明: hf.filter_mono inf_le_right

Depends on / 依赖: filter_mono, hf.filter_mono, inf_le_right
-/
theorem IsMinOn.localize (hf : IsMinOn f s a) : IsLocalMinOn f s a :=
hf.filter_mono inf_le_right

/--
theorem `IsMaxOn.localize` / 定理 `IsMaxOn.localize`

English:
theorem IsMaxOn.localize
  given: (hf : IsMaxOn f s a)
  statement: IsLocalMaxOn f s a
  proof: hf.filter_mono inf_le_right

中文:
定理 IsMaxOn.localize
  条件: (hf : IsMaxOn f s a)
  结论: IsLocalMaxOn f s a
  证明: hf.filter_mono inf_le_right

Depends on / 依赖: filter_mono, hf.filter_mono, inf_le_right
-/
theorem IsMaxOn.localize (hf : IsMaxOn f s a) : IsLocalMaxOn f s a :=
hf.filter_mono inf_le_right

/--
theorem `IsExtrOn.localize` / 定理 `IsExtrOn.localize`

English:
theorem IsExtrOn.localize
  given: (hf : IsExtrOn f s a)
  statement: IsLocalExtrOn f s a
  proof: hf.filter_mono inf_le_right

中文:
定理 IsExtrOn.localize
  条件: (hf : IsExtrOn f s a)
  结论: IsLocalExtrOn f s a
  证明: hf.filter_mono inf_le_right

Depends on / 依赖: filter_mono, hf.filter_mono, inf_le_right
-/
theorem IsExtrOn.localize (hf : IsExtrOn f s a) : IsLocalExtrOn f s a :=
hf.filter_mono inf_le_right

/--
theorem `IsLocalMinOn.isLocalMin` / 定理 `IsLocalMinOn.isLocalMin`

English:
theorem IsLocalMinOn.isLocalMin
  given: (hf : IsLocalMinOn f s a) (hs : s in 𝓝 a)
  statement: IsLocalMin f a
  proof: have : 𝓝 a <= 𝓟 s := le_principal_iff.2 hs
hf.filter_mono le_inf le_rfl this

中文:
定理 IsLocalMinOn.isLocalMin
  条件: (hf : IsLocalMinOn f s a) (hs : s in 𝓝 a)
  结论: IsLocalMin f a
  证明: have : 𝓝 a <= 𝓟 s := le_principal_iff.2 hs
hf.filter_mono le_inf le_rfl this

Depends on / 依赖: filter_mono, hf.filter_mono, le_inf, le_principal_iff, le_rfl
-/
theorem IsLocalMinOn.isLocalMin (hf : IsLocalMinOn f s a) (hs : s in 𝓝 a) : IsLocalMin f a :=
  have : 𝓝 a <= 𝓟 s := le_principal_iff.2 hs
hf.filter_mono le_inf le_rfl this

/--
theorem `IsLocalMaxOn.isLocalMax` / 定理 `IsLocalMaxOn.isLocalMax`

English:
theorem IsLocalMaxOn.isLocalMax
  given: (hf : IsLocalMaxOn f s a) (hs : s in 𝓝 a)
  statement: IsLocalMax f a
  proof: have : 𝓝 a <= 𝓟 s := le_principal_iff.2 hs
hf.filter_mono le_inf le_rfl this

中文:
定理 IsLocalMaxOn.isLocalMax
  条件: (hf : IsLocalMaxOn f s a) (hs : s in 𝓝 a)
  结论: IsLocalMax f a
  证明: have : 𝓝 a <= 𝓟 s := le_principal_iff.2 hs
hf.filter_mono le_inf le_rfl this

Depends on / 依赖: filter_mono, hf.filter_mono, le_inf, le_principal_iff, le_rfl
-/
theorem IsLocalMaxOn.isLocalMax (hf : IsLocalMaxOn f s a) (hs : s in 𝓝 a) : IsLocalMax f a :=
  have : 𝓝 a <= 𝓟 s := le_principal_iff.2 hs
hf.filter_mono le_inf le_rfl this

/--
theorem `IsLocalExtrOn.isLocalExtr` / 定理 `IsLocalExtrOn.isLocalExtr`

English:
theorem IsLocalExtrOn.isLocalExtr
  given: (hf : IsLocalExtrOn f s a) (hs : s in 𝓝 a)
  statement: IsLocalExtr f a
  proof: hf.elim (fun hf => (hf.isLocalMin hs).isExtr) fun hf => (hf.isLocalMax hs).isExtr

中文:
定理 IsLocalExtrOn.isLocalExtr
  条件: (hf : IsLocalExtrOn f s a) (hs : s in 𝓝 a)
  结论: IsLocalExtr f a
  证明: hf.elim (fun hf => (hf.isLocalMin hs).isExtr) fun hf => (hf.isLocalMax hs).isExtr

Depends on / 依赖: hf.elim, hf.isLocalMax, hf.isLocalMin, isExtr, isLocalMax, isLocalMin
-/
theorem IsLocalExtrOn.isLocalExtr (hf : IsLocalExtrOn f s a) (hs : s in 𝓝 a) : IsLocalExtr f a :=
  hf.elim (fun hf => (hf.isLocalMin hs).isExtr) fun hf => (hf.isLocalMax hs).isExtr

/--
lemma `isLocalMinOn_univ_iff` / 引理 `isLocalMinOn_univ_iff`

English:
lemma isLocalMinOn_univ_iff
  statement: IsLocalMinOn f univ a ↔ IsLocalMin f a
  proof: by
  simp only [IsLocalMinOn, IsLocalMin, nhdsWithin_univ]

中文:
引理 isLocalMinOn_univ_iff
  结论: IsLocalMinOn f univ a ↔ IsLocalMin f a
  证明: by
  simp only [IsLocalMinOn, IsLocalMin, nhdsWithin_univ]

Depends on / 依赖: IsLocalMin, IsLocalMinOn, nhdsWithin_univ
-/
lemma isLocalMinOn_univ_iff : IsLocalMinOn f univ a ↔ IsLocalMin f a := by
  simp only [IsLocalMinOn, IsLocalMin, nhdsWithin_univ]

/--
lemma `isLocalMaxOn_univ_iff` / 引理 `isLocalMaxOn_univ_iff`

English:
lemma isLocalMaxOn_univ_iff
  statement: IsLocalMaxOn f univ a ↔ IsLocalMax f a
  proof: by
  simp only [IsLocalMaxOn, IsLocalMax, nhdsWithin_univ]

中文:
引理 isLocalMaxOn_univ_iff
  结论: IsLocalMaxOn f univ a ↔ IsLocalMax f a
  证明: by
  simp only [IsLocalMaxOn, IsLocalMax, nhdsWithin_univ]

Depends on / 依赖: IsLocalMax, IsLocalMaxOn, nhdsWithin_univ
-/
lemma isLocalMaxOn_univ_iff : IsLocalMaxOn f univ a ↔ IsLocalMax f a := by
  simp only [IsLocalMaxOn, IsLocalMax, nhdsWithin_univ]

/--
lemma `isLocalExtrOn_univ_iff` / 引理 `isLocalExtrOn_univ_iff`

English:
lemma isLocalExtrOn_univ_iff
  statement: IsLocalExtrOn f univ a ↔ IsLocalExtr f a
  proof: isLocalMinOn_univ_iff.or isLocalMaxOn_univ_iff

中文:
引理 isLocalExtrOn_univ_iff
  结论: IsLocalExtrOn f univ a ↔ IsLocalExtr f a
  证明: isLocalMinOn_univ_iff.or isLocalMaxOn_univ_iff

Depends on / 依赖: isLocalMaxOn_univ_iff, isLocalMinOn_univ_iff, isLocalMinOn_univ_iff.or
-/
lemma isLocalExtrOn_univ_iff : IsLocalExtrOn f univ a ↔ IsLocalExtr f a :=
  isLocalMinOn_univ_iff.or isLocalMaxOn_univ_iff

/--
theorem `IsMinOn.isLocalMin` / 定理 `IsMinOn.isLocalMin`

English:
theorem IsMinOn.isLocalMin
  given: (hf : IsMinOn f s a) (hs : s in 𝓝 a)
  statement: IsLocalMin f a
  proof: hf.localize.isLocalMin hs

中文:
定理 IsMinOn.isLocalMin
  条件: (hf : IsMinOn f s a) (hs : s in 𝓝 a)
  结论: IsLocalMin f a
  证明: hf.localize.isLocalMin hs

Depends on / 依赖: hf.localize.isLocalMin, isLocalMin, localize
-/
theorem IsMinOn.isLocalMin (hf : IsMinOn f s a) (hs : s in 𝓝 a) : IsLocalMin f a :=
  hf.localize.isLocalMin hs

/--
theorem `IsMaxOn.isLocalMax` / 定理 `IsMaxOn.isLocalMax`

English:
theorem IsMaxOn.isLocalMax
  given: (hf : IsMaxOn f s a) (hs : s in 𝓝 a)
  statement: IsLocalMax f a
  proof: hf.localize.isLocalMax hs

中文:
定理 IsMaxOn.isLocalMax
  条件: (hf : IsMaxOn f s a) (hs : s in 𝓝 a)
  结论: IsLocalMax f a
  证明: hf.localize.isLocalMax hs

Depends on / 依赖: hf.localize.isLocalMax, isLocalMax, localize
-/
theorem IsMaxOn.isLocalMax (hf : IsMaxOn f s a) (hs : s in 𝓝 a) : IsLocalMax f a :=
  hf.localize.isLocalMax hs

/--
theorem `IsExtrOn.isLocalExtr` / 定理 `IsExtrOn.isLocalExtr`

English:
theorem IsExtrOn.isLocalExtr
  given: (hf : IsExtrOn f s a) (hs : s in 𝓝 a)
  statement: IsLocalExtr f a
  proof: hf.localize.isLocalExtr hs

中文:
定理 IsExtrOn.isLocalExtr
  条件: (hf : IsExtrOn f s a) (hs : s in 𝓝 a)
  结论: IsLocalExtr f a
  证明: hf.localize.isLocalExtr hs

Depends on / 依赖: hf.localize.isLocalExtr, isLocalExtr, localize
-/
theorem IsExtrOn.isLocalExtr (hf : IsExtrOn f s a) (hs : s in 𝓝 a) : IsLocalExtr f a :=
  hf.localize.isLocalExtr hs

/--
theorem `IsLocalMinOn.not_nhds_le_map` / 定理 `IsLocalMinOn.not_nhds_le_map`

English:
theorem IsLocalMinOn.not_nhds_le_map
  statement: [TopologicalSpace β] (hf : IsLocalMinOn f s a)
  proof: fun hle =>
  have : forallᶠ y in 𝓝[<] f a, f a <= y := (eventually_map.2 hf).filter_mono (inf_le_left.trans hle)
  let ⟨_y, hy⟩ := (this.and self_mem_nhdsWithin).exists
  hy.1.not_gt hy.2

中文:
定理 IsLocalMinOn.not_nhds_le_map
  结论: [拓扑空间 β] (hf : IsLocalMinOn f s a)
  证明: fun hle =>
  have : forallᶠ y in 𝓝[<] f a, f a <= y := (eventually_map.2 hf).filter_mono (inf_le_left.trans hle)
  let ⟨_y, hy⟩ := (this.and self_mem_nhdsWithin).exists
  hy.1.not_gt hy.2
-/
theorem IsLocalMinOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMinOn f s a)
    [NeBot (𝓝[<] f a)] : ¬𝓝 (f a) <= map f (𝓝[s] a) := fun hle =>
  have : forallᶠ y in 𝓝[<] f a, f a <= y := (eventually_map.2 hf).filter_mono (inf_le_left.trans hle)
  let ⟨_y, hy⟩ := (this.and self_mem_nhdsWithin).exists
  hy.1.not_gt hy.2

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsLocalMaxOn.not_nhds_le_map` / 定理 `IsLocalMaxOn.not_nhds_le_map`

English:
theorem IsLocalMaxOn.not_nhds_le_map
  statement: [TopologicalSpace β] (hf : IsLocalMaxOn f s a)
  proof: @IsLocalMinOn.not_nhds_le_map α βᵒᵈ _ _ _ _ _ ‹_› hf ‹_›

中文:
定理 IsLocalMaxOn.not_nhds_le_map
  结论: [拓扑空间 β] (hf : IsLocalMaxOn f s a)
  证明: @IsLocalMinOn.not_nhds_le_map α βᵒᵈ _ _ _ _ _ ‹_› hf ‹_›

Depends on / 依赖: IsLocalMinOn, IsLocalMinOn.not_nhds_le_map, not_nhds_le_map
-/
theorem IsLocalMaxOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMaxOn f s a)
    [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) <= map f (𝓝[s] a) :=
  @IsLocalMinOn.not_nhds_le_map α βᵒᵈ _ _ _ _ _ ‹_› hf ‹_›

/--
theorem `IsLocalExtrOn.not_nhds_le_map` / 定理 `IsLocalExtrOn.not_nhds_le_map`

English:
theorem IsLocalExtrOn.not_nhds_le_map
  statement: [TopologicalSpace β] (hf : IsLocalExtrOn f s a)
  proof: hf.elim (fun h => h.not_nhds_le_map) fun h => h.not_nhds_le_map

中文:
定理 IsLocalExtrOn.not_nhds_le_map
  结论: [拓扑空间 β] (hf : IsLocalExtrOn f s a)
  证明: hf.elim (fun h => h.not_nhds_le_map) fun h => h.not_nhds_le_map

Depends on / 依赖: h.not_nhds_le_map, hf.elim, not_nhds_le_map
-/
theorem IsLocalExtrOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalExtrOn f s a)
    [NeBot (𝓝[<] f a)] [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) <= map f (𝓝[s] a) :=
  hf.elim (fun h => h.not_nhds_le_map) fun h => h.not_nhds_le_map



/--
theorem `isLocalMinOn_const` / 定理 `isLocalMinOn_const`

English:
theorem isLocalMinOn_const
  given: {b : β}
  statement: IsLocalMinOn (fun _ => b) s a
  proof: isMinFilter_const

中文:
定理 isLocalMinOn_const
  条件: {b : β}
  结论: IsLocalMinOn (fun _ => b) s a
  证明: isMinFilter_const

Depends on / 依赖: isMinFilter_const
-/
theorem isLocalMinOn_const {b : β} : IsLocalMinOn (fun _ => b) s a :=
  isMinFilter_const

/--
theorem `isLocalMaxOn_const` / 定理 `isLocalMaxOn_const`

English:
theorem isLocalMaxOn_const
  given: {b : β}
  statement: IsLocalMaxOn (fun _ => b) s a
  proof: isMaxFilter_const

中文:
定理 isLocalMaxOn_const
  条件: {b : β}
  结论: IsLocalMaxOn (fun _ => b) s a
  证明: isMaxFilter_const

Depends on / 依赖: isMaxFilter_const
-/
theorem isLocalMaxOn_const {b : β} : IsLocalMaxOn (fun _ => b) s a :=
  isMaxFilter_const

/--
theorem `isLocalExtrOn_const` / 定理 `isLocalExtrOn_const`

English:
theorem isLocalExtrOn_const
  given: {b : β}
  statement: IsLocalExtrOn (fun _ => b) s a
  proof: isExtrFilter_const

中文:
定理 isLocalExtrOn_const
  条件: {b : β}
  结论: IsLocalExtrOn (fun _ => b) s a
  证明: isExtrFilter_const

Depends on / 依赖: isExtrFilter_const
-/
theorem isLocalExtrOn_const {b : β} : IsLocalExtrOn (fun _ => b) s a :=
  isExtrFilter_const

/--
theorem `isLocalMin_const` / 定理 `isLocalMin_const`

English:
theorem isLocalMin_const
  given: {b : β}
  statement: IsLocalMin (fun _ => b) a
  proof: isMinFilter_const

中文:
定理 isLocalMin_const
  条件: {b : β}
  结论: IsLocalMin (fun _ => b) a
  证明: isMinFilter_const

Depends on / 依赖: isMinFilter_const
-/
theorem isLocalMin_const {b : β} : IsLocalMin (fun _ => b) a :=
  isMinFilter_const

/--
theorem `isLocalMax_const` / 定理 `isLocalMax_const`

English:
theorem isLocalMax_const
  given: {b : β}
  statement: IsLocalMax (fun _ => b) a
  proof: isMaxFilter_const

中文:
定理 isLocalMax_const
  条件: {b : β}
  结论: IsLocalMax (fun _ => b) a
  证明: isMaxFilter_const

Depends on / 依赖: isMaxFilter_const
-/
theorem isLocalMax_const {b : β} : IsLocalMax (fun _ => b) a :=
  isMaxFilter_const

/--
theorem `isLocalExtr_const` / 定理 `isLocalExtr_const`

English:
theorem isLocalExtr_const
  given: {b : β}
  statement: IsLocalExtr (fun _ => b) a
  proof: isExtrFilter_const

中文:
定理 isLocalExtr_const
  条件: {b : β}
  结论: IsLocalExtr (fun _ => b) a
  证明: isExtrFilter_const

Depends on / 依赖: isExtrFilter_const
-/
theorem isLocalExtr_const {b : β} : IsLocalExtr (fun _ => b) a :=
  isExtrFilter_const

/-! ### Composition with (anti)monotone functions -/

nonrec theorem IsLocalMin.comp_mono (hf : IsLocalMin f a) {g : β -> γ} (hg : Monotone g) :
    IsLocalMin (g ∘ f) a :=
  hf.comp_mono hg

nonrec theorem IsLocalMax.comp_mono (hf : IsLocalMax f a) {g : β -> γ} (hg : Monotone g) :
    IsLocalMax (g ∘ f) a :=
  hf.comp_mono hg

nonrec theorem IsLocalExtr.comp_mono (hf : IsLocalExtr f a) {g : β -> γ} (hg : Monotone g) :
    IsLocalExtr (g ∘ f) a :=
  hf.comp_mono hg

nonrec theorem IsLocalMin.comp_antitone (hf : IsLocalMin f a) {g : β -> γ} (hg : Antitone g) :
    IsLocalMax (g ∘ f) a :=
  hf.comp_antitone hg

nonrec theorem IsLocalMax.comp_antitone (hf : IsLocalMax f a) {g : β -> γ} (hg : Antitone g) :
    IsLocalMin (g ∘ f) a :=
  hf.comp_antitone hg

nonrec theorem IsLocalExtr.comp_antitone (hf : IsLocalExtr f a) {g : β -> γ} (hg : Antitone g) :
    IsLocalExtr (g ∘ f) a :=
  hf.comp_antitone hg

nonrec theorem IsLocalMinOn.comp_mono (hf : IsLocalMinOn f s a) {g : β -> γ} (hg : Monotone g) :
    IsLocalMinOn (g ∘ f) s a :=
  hf.comp_mono hg

nonrec theorem IsLocalMaxOn.comp_mono (hf : IsLocalMaxOn f s a) {g : β -> γ} (hg : Monotone g) :
    IsLocalMaxOn (g ∘ f) s a :=
  hf.comp_mono hg

nonrec theorem IsLocalExtrOn.comp_mono (hf : IsLocalExtrOn f s a) {g : β -> γ} (hg : Monotone g) :
    IsLocalExtrOn (g ∘ f) s a :=
  hf.comp_mono hg

nonrec theorem IsLocalMinOn.comp_antitone (hf : IsLocalMinOn f s a) {g : β -> γ} (hg : Antitone g) :
    IsLocalMaxOn (g ∘ f) s a :=
  hf.comp_antitone hg

nonrec theorem IsLocalMaxOn.comp_antitone (hf : IsLocalMaxOn f s a) {g : β -> γ} (hg : Antitone g) :
    IsLocalMinOn (g ∘ f) s a :=
  hf.comp_antitone hg

nonrec theorem IsLocalExtrOn.comp_antitone (hf : IsLocalExtrOn f s a) {g : β -> γ}
    (hg : Antitone g) : IsLocalExtrOn (g ∘ f) s a :=
  hf.comp_antitone hg

open scoped Relator

nonrec theorem IsLocalMin.bicomp_mono [Preorder δ] {op : β -> γ -> δ}
    (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsLocalMin f a) {g : α -> γ}
    (hg : IsLocalMin g a) : IsLocalMin (fun x => op (f x) (g x)) a :=
  hf.bicomp_mono hop hg

nonrec theorem IsLocalMax.bicomp_mono [Preorder δ] {op : β -> γ -> δ}
    (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsLocalMax f a) {g : α -> γ}
    (hg : IsLocalMax g a) : IsLocalMax (fun x => op (f x) (g x)) a :=
  hf.bicomp_mono hop hg

nonrec theorem IsLocalMinOn.bicomp_mono [Preorder δ] {op : β -> γ -> δ}
    (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsLocalMinOn f s a) {g : α -> γ}
    (hg : IsLocalMinOn g s a) : IsLocalMinOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg

nonrec theorem IsLocalMaxOn.bicomp_mono [Preorder δ] {op : β -> γ -> δ}
    (hop : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) op op) (hf : IsLocalMaxOn f s a) {g : α -> γ}
    (hg : IsLocalMaxOn g s a) : IsLocalMaxOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg



/--
theorem `IsLocalMin.comp_continuous` / 定理 `IsLocalMin.comp_continuous`

English:
theorem IsLocalMin.comp_continuous
  statement: [TopologicalSpace δ] {g : δ -> α} {b : δ}
  proof: hg hf

中文:
定理 IsLocalMin.comp_continuous
  结论: [拓扑空间 δ] {g : δ -> α} {b : δ}
  证明: hg hf
-/
theorem IsLocalMin.comp_continuous [TopologicalSpace δ] {g : δ -> α} {b : δ}
    (hf : IsLocalMin f (g b)) (hg : ContinuousAt g b) : IsLocalMin (f ∘ g) b :=
  hg hf

/--
theorem `IsLocalMax.comp_continuous` / 定理 `IsLocalMax.comp_continuous`

English:
theorem IsLocalMax.comp_continuous
  statement: [TopologicalSpace δ] {g : δ -> α} {b : δ}
  proof: hg hf

中文:
定理 IsLocalMax.comp_continuous
  结论: [拓扑空间 δ] {g : δ -> α} {b : δ}
  证明: hg hf
-/
theorem IsLocalMax.comp_continuous [TopologicalSpace δ] {g : δ -> α} {b : δ}
    (hf : IsLocalMax f (g b)) (hg : ContinuousAt g b) : IsLocalMax (f ∘ g) b :=
  hg hf

/--
theorem `IsLocalExtr.comp_continuous` / 定理 `IsLocalExtr.comp_continuous`

English:
theorem IsLocalExtr.comp_continuous
  statement: [TopologicalSpace δ] {g : δ -> α} {b : δ}
  proof: hf.comp_tendsto hg

中文:
定理 IsLocalExtr.comp_continuous
  结论: [拓扑空间 δ] {g : δ -> α} {b : δ}
  证明: hf.comp_tendsto hg

Depends on / 依赖: comp_tendsto, hf.comp_tendsto
-/
theorem IsLocalExtr.comp_continuous [TopologicalSpace δ] {g : δ -> α} {b : δ}
    (hf : IsLocalExtr f (g b)) (hg : ContinuousAt g b) : IsLocalExtr (f ∘ g) b :=
  hf.comp_tendsto hg

/--
theorem `IsLocalMin.comp_continuousOn` / 定理 `IsLocalMin.comp_continuousOn`

English:
theorem IsLocalMin.comp_continuousOn
  statement: [TopologicalSpace δ] {s : Set δ} {g : δ -> α} {b : δ}
  proof: hf.comp_tendsto (hg b hb)

中文:
定理 IsLocalMin.comp_continuousOn
  结论: [拓扑空间 δ] {s : 集合 δ} {g : δ -> α} {b : δ}
  证明: hf.comp_tendsto (hg b hb)

Depends on / 依赖: comp_tendsto, hf.comp_tendsto
-/
theorem IsLocalMin.comp_continuousOn [TopologicalSpace δ] {s : Set δ} {g : δ -> α} {b : δ}
    (hf : IsLocalMin f (g b)) (hg : ContinuousOn g s) (hb : b in s) : IsLocalMinOn (f ∘ g) s b :=
  hf.comp_tendsto (hg b hb)

/--
theorem `IsLocalMax.comp_continuousOn` / 定理 `IsLocalMax.comp_continuousOn`

English:
theorem IsLocalMax.comp_continuousOn
  statement: [TopologicalSpace δ] {s : Set δ} {g : δ -> α} {b : δ}
  proof: hf.comp_tendsto (hg b hb)

中文:
定理 IsLocalMax.comp_continuousOn
  结论: [拓扑空间 δ] {s : 集合 δ} {g : δ -> α} {b : δ}
  证明: hf.comp_tendsto (hg b hb)

Depends on / 依赖: comp_tendsto, hf.comp_tendsto
-/
theorem IsLocalMax.comp_continuousOn [TopologicalSpace δ] {s : Set δ} {g : δ -> α} {b : δ}
    (hf : IsLocalMax f (g b)) (hg : ContinuousOn g s) (hb : b in s) : IsLocalMaxOn (f ∘ g) s b :=
  hf.comp_tendsto (hg b hb)

/--
theorem `IsLocalExtr.comp_continuousOn` / 定理 `IsLocalExtr.comp_continuousOn`

English:
theorem IsLocalExtr.comp_continuousOn
  statement: [TopologicalSpace δ] {s : Set δ} (g : δ -> α) {b : δ}
  proof: hf.elim (fun hf => (hf.comp_continuousOn hg hb).isExtr) fun hf =>
    (IsLocalMax.comp_continuousOn hf hg hb).isExtr

中文:
定理 IsLocalExtr.comp_continuousOn
  结论: [拓扑空间 δ] {s : 集合 δ} (g : δ -> α) {b : δ}
  证明: hf.elim (fun hf => (hf.comp_continuousOn hg hb).isExtr) fun hf =>
    (IsLocalMax.comp_continuousOn hf hg hb).isExtr

Depends on / 依赖: IsLocalMax, IsLocalMax.comp_continuousOn, comp_continuousOn, hf.comp_continuousOn, hf.elim, isExtr
-/
theorem IsLocalExtr.comp_continuousOn [TopologicalSpace δ] {s : Set δ} (g : δ -> α) {b : δ}
    (hf : IsLocalExtr f (g b)) (hg : ContinuousOn g s) (hb : b in s) : IsLocalExtrOn (f ∘ g) s b :=
  hf.elim (fun hf => (hf.comp_continuousOn hg hb).isExtr) fun hf =>
    (IsLocalMax.comp_continuousOn hf hg hb).isExtr

/--
theorem `IsLocalMinOn.comp_continuousOn` / 定理 `IsLocalMinOn.comp_continuousOn`

English:
theorem IsLocalMinOn.comp_continuousOn
  statement: [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ -> α}
  proof: hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))

中文:
定理 IsLocalMinOn.comp_continuousOn
  结论: [拓扑空间 δ] {t : 集合 α} {s : 集合 δ} {g : δ -> α}
  证明: hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.tendsto_nhdsWithin_image, comp_tendsto, hf.comp_tendsto, image_subset_iff, image_subset_iff.mpr, tendsto_nhdsWithin_image, tendsto_nhdsWithin_mono_right
-/
theorem IsLocalMinOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ -> α}
    {b : δ} (hf : IsLocalMinOn f t (g b)) (hst : s subseteq g ⁻¹' t) (hg : ContinuousOn g s) (hb : b in s) :
    IsLocalMinOn (f ∘ g) s b :=
  hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))

/--
theorem `IsLocalMaxOn.comp_continuousOn` / 定理 `IsLocalMaxOn.comp_continuousOn`

English:
theorem IsLocalMaxOn.comp_continuousOn
  statement: [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ -> α}
  proof: hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))

中文:
定理 IsLocalMaxOn.comp_continuousOn
  结论: [拓扑空间 δ] {t : 集合 α} {s : 集合 δ} {g : δ -> α}
  证明: hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.tendsto_nhdsWithin_image, comp_tendsto, hf.comp_tendsto, image_subset_iff, image_subset_iff.mpr, tendsto_nhdsWithin_image, tendsto_nhdsWithin_mono_right
-/
theorem IsLocalMaxOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ -> α}
    {b : δ} (hf : IsLocalMaxOn f t (g b)) (hst : s subseteq g ⁻¹' t) (hg : ContinuousOn g s) (hb : b in s) :
    IsLocalMaxOn (f ∘ g) s b :=
  hf.comp_tendsto
    (tendsto_nhdsWithin_mono_right (image_subset_iff.mpr hst)
      (ContinuousWithinAt.tendsto_nhdsWithin_image (hg b hb)))

/--
theorem `IsLocalExtrOn.comp_continuousOn` / 定理 `IsLocalExtrOn.comp_continuousOn`

English:
theorem IsLocalExtrOn.comp_continuousOn
  statement: [TopologicalSpace δ] {t : Set α} {s : Set δ} (g : δ -> α)
  proof: hf.elim (fun hf => (hf.comp_continuousOn hst hg hb).isExtr) fun hf =>
    (IsLocalMaxOn.comp_continuousOn hf hst hg hb).isExtr

中文:
定理 IsLocalExtrOn.comp_continuousOn
  结论: [拓扑空间 δ] {t : 集合 α} {s : 集合 δ} (g : δ -> α)
  证明: hf.elim (fun hf => (hf.comp_continuousOn hst hg hb).isExtr) fun hf =>
    (IsLocalMaxOn.comp_continuousOn hf hst hg hb).isExtr

Depends on / 依赖: IsLocalMaxOn, IsLocalMaxOn.comp_continuousOn, comp_continuousOn, hf.comp_continuousOn, hf.elim, isExtr
-/
theorem IsLocalExtrOn.comp_continuousOn [TopologicalSpace δ] {t : Set α} {s : Set δ} (g : δ -> α)
    {b : δ} (hf : IsLocalExtrOn f t (g b)) (hst : s subseteq g ⁻¹' t) (hg : ContinuousOn g s)
    (hb : b in s) : IsLocalExtrOn (f ∘ g) s b :=
  hf.elim (fun hf => (hf.comp_continuousOn hst hg hb).isExtr) fun hf =>
    (IsLocalMaxOn.comp_continuousOn hf hst hg hb).isExtr

end Preorder

/-! ### Pointwise addition -/


section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α -> β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.add (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x + g x) a :=
  hf.add hg

nonrec theorem IsLocalMax.add (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x + g x) a :=
  hf.add hg

nonrec theorem IsLocalMinOn.add (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x + g x) s a :=
  hf.add hg

nonrec theorem IsLocalMaxOn.add (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x + g x) s a :=
  hf.add hg

end OrderedAddCommMonoid

/-! ### Pointwise negation and subtraction -/


section OrderedAddCommGroup

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  {f g : α -> β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.neg (hf : IsLocalMin f a) : IsLocalMax (fun x => -f x) a :=
  hf.neg

nonrec theorem IsLocalMax.neg (hf : IsLocalMax f a) : IsLocalMin (fun x => -f x) a :=
  hf.neg

nonrec theorem IsLocalExtr.neg (hf : IsLocalExtr f a) : IsLocalExtr (fun x => -f x) a :=
  hf.neg

nonrec theorem IsLocalMinOn.neg (hf : IsLocalMinOn f s a) : IsLocalMaxOn (fun x => -f x) s a :=
  hf.neg

nonrec theorem IsLocalMaxOn.neg (hf : IsLocalMaxOn f s a) : IsLocalMinOn (fun x => -f x) s a :=
  hf.neg

nonrec theorem IsLocalExtrOn.neg (hf : IsLocalExtrOn f s a) : IsLocalExtrOn (fun x => -f x) s a :=
  hf.neg

nonrec theorem IsLocalMin.sub (hf : IsLocalMin f a) (hg : IsLocalMax g a) :
    IsLocalMin (fun x => f x - g x) a :=
  hf.sub hg

nonrec theorem IsLocalMax.sub (hf : IsLocalMax f a) (hg : IsLocalMin g a) :
    IsLocalMax (fun x => f x - g x) a :=
  hf.sub hg

nonrec theorem IsLocalMinOn.sub (hf : IsLocalMinOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMinOn (fun x => f x - g x) s a :=
  hf.sub hg

nonrec theorem IsLocalMaxOn.sub (hf : IsLocalMaxOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMaxOn (fun x => f x - g x) s a :=
  hf.sub hg

end OrderedAddCommGroup

/-! ### Pointwise `sup`/`inf` -/


section SemilatticeSup

variable [SemilatticeSup β] {f g : α -> β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.sup (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x ⊔ g x) a :=
  hf.sup hg

nonrec theorem IsLocalMax.sup (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x ⊔ g x) a :=
  hf.sup hg

nonrec theorem IsLocalMinOn.sup (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x ⊔ g x) s a :=
  hf.sup hg

nonrec theorem IsLocalMaxOn.sup (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x ⊔ g x) s a :=
  hf.sup hg

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] {f g : α -> β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.inf (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => f x ⊓ g x) a :=
  hf.inf hg

nonrec theorem IsLocalMax.inf (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => f x ⊓ g x) a :=
  hf.inf hg

nonrec theorem IsLocalMinOn.inf (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => f x ⊓ g x) s a :=
  hf.inf hg

nonrec theorem IsLocalMaxOn.inf (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => f x ⊓ g x) s a :=
  hf.inf hg

end SemilatticeInf

/-! ### Pointwise `min`/`max` -/


section LinearOrder

variable [LinearOrder β] {f g : α -> β} {a : α} {s : Set α} {l : Filter α}

nonrec theorem IsLocalMin.min (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => min (f x) (g x)) a :=
  hf.min hg

nonrec theorem IsLocalMax.min (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => min (f x) (g x)) a :=
  hf.min hg

nonrec theorem IsLocalMinOn.min (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => min (f x) (g x)) s a :=
  hf.min hg

nonrec theorem IsLocalMaxOn.min (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => min (f x) (g x)) s a :=
  hf.min hg

nonrec theorem IsLocalMin.max (hf : IsLocalMin f a) (hg : IsLocalMin g a) :
    IsLocalMin (fun x => max (f x) (g x)) a :=
  hf.max hg

nonrec theorem IsLocalMax.max (hf : IsLocalMax f a) (hg : IsLocalMax g a) :
    IsLocalMax (fun x => max (f x) (g x)) a :=
  hf.max hg

nonrec theorem IsLocalMinOn.max (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => max (f x) (g x)) s a :=
  hf.max hg

nonrec theorem IsLocalMaxOn.max (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => max (f x) (g x)) s a :=
  hf.max hg

end LinearOrder

section Eventually

/-! ### Relation with `eventually` comparisons of two functions -/


variable [Preorder β] {s : Set α}

/--
theorem `Filter.EventuallyLE.isLocalMaxOn` / 定理 `Filter.EventuallyLE.isLocalMaxOn`

English:
theorem Filter.EventuallyLE.isLocalMaxOn
  statement: {f g : α -> β} {a : α} (hle : g <=ᶠ[𝓝[s] a] f)
  proof: hle.isMaxFilter hfga h

nonrec theorem IsLocalMaxOn.congr {f g : α -> β} {a : α} (h : IsLocalMaxOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : IsLocalMaxOn g s a :=
h.congr heq heq.eq_of_nhdsWithin hmem

中文:
定理 滤子.EventuallyLE.isLocalMaxOn
  结论: {f g : α -> β} {a : α} (hle : g <=ᶠ[𝓝[s] a] f)
  证明: hle.isMaxFilter hfga h

nonrec theorem IsLocalMaxOn.congr {f g : α -> β} {a : α} (h : IsLocalMaxOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : IsLocalMaxOn g s a :=
h.congr heq heq.eq_of_nhdsWithin hmem

Depends on / 依赖: hle.isMaxFilter, isMaxFilter
-/
theorem Filter.EventuallyLE.isLocalMaxOn {f g : α -> β} {a : α} (hle : g <=ᶠ[𝓝[s] a] f)
    (hfga : f a = g a) (h : IsLocalMaxOn f s a) : IsLocalMaxOn g s a :=
  hle.isMaxFilter hfga h

nonrec theorem IsLocalMaxOn.congr {f g : α -> β} {a : α} (h : IsLocalMaxOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : IsLocalMaxOn g s a :=
h.congr heq heq.eq_of_nhdsWithin hmem

/--
theorem `Filter.EventuallyEq.isLocalMaxOn_iff` / 定理 `Filter.EventuallyEq.isLocalMaxOn_iff`

English:
theorem Filter.EventuallyEq.isLocalMaxOn_iff
  statement: {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
  proof: heq.isMaxFilter_iff heq.eq_of_nhdsWithin hmem

中文:
定理 滤子.EventuallyEq.isLocalMaxOn_iff
  结论: {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
  证明: heq.isMaxFilter_iff heq.eq_of_nhdsWithin hmem

Depends on / 依赖: eq_of_nhdsWithin, heq.eq_of_nhdsWithin, heq.isMaxFilter_iff, isMaxFilter_iff
-/
theorem Filter.EventuallyEq.isLocalMaxOn_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a in s) : IsLocalMaxOn f s a ↔ IsLocalMaxOn g s a :=
heq.isMaxFilter_iff heq.eq_of_nhdsWithin hmem

/--
theorem `Filter.EventuallyLE.isLocalMinOn` / 定理 `Filter.EventuallyLE.isLocalMinOn`

English:
theorem Filter.EventuallyLE.isLocalMinOn
  statement: {f g : α -> β} {a : α} (hle : f <=ᶠ[𝓝[s] a] g)
  proof: hle.isMinFilter hfga h

nonrec theorem IsLocalMinOn.congr {f g : α -> β} {a : α} (h : IsLocalMinOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : IsLocalMinOn g s a :=
h.congr heq heq.eq_of_nhdsWithin hmem

nonrec theorem Filter.EventuallyEq.isLocalMinOn_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a in s) : IsLocalMinOn f s a ↔ IsLocalMinOn g s a :=
heq.isMinFilter_iff heq.eq_of_nhdsWithin hmem

nonrec theorem IsLocalExtrOn.congr {f g : α -> β} {a : α} (h : IsLocalExtrOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : IsLocalExtrOn g s a :=
h.congr heq heq.eq_of_nhdsWithin hmem

中文:
定理 滤子.EventuallyLE.isLocalMinOn
  结论: {f g : α -> β} {a : α} (hle : f <=ᶠ[𝓝[s] a] g)
  证明: hle.isMinFilter hfga h

nonrec theorem IsLocalMinOn.congr {f g : α -> β} {a : α} (h : IsLocalMinOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : IsLocalMinOn g s a :=
h.congr heq heq.eq_of_nhdsWithin hmem

nonrec theorem Filter.EventuallyEq.isLocalMinOn_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a in s) : IsLocalMinOn f s a ↔ IsLocalMinOn g s a :=
heq.isMinFilter_iff heq.eq_of_nhdsWithin hmem

nonrec theorem IsLocalExtrOn.congr {f g : α -> β} {a : α} (h : IsLocalExtrOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : IsLocalExtrOn g s a :=
h.congr heq heq.eq_of_nhdsWithin hmem

Depends on / 依赖: hle.isMinFilter, isMinFilter
-/
theorem Filter.EventuallyLE.isLocalMinOn {f g : α -> β} {a : α} (hle : f <=ᶠ[𝓝[s] a] g)
    (hfga : f a = g a) (h : IsLocalMinOn f s a) : IsLocalMinOn g s a :=
  hle.isMinFilter hfga h

nonrec theorem IsLocalMinOn.congr {f g : α -> β} {a : α} (h : IsLocalMinOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : IsLocalMinOn g s a :=
h.congr heq heq.eq_of_nhdsWithin hmem

nonrec theorem Filter.EventuallyEq.isLocalMinOn_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a in s) : IsLocalMinOn f s a ↔ IsLocalMinOn g s a :=
heq.isMinFilter_iff heq.eq_of_nhdsWithin hmem

nonrec theorem IsLocalExtrOn.congr {f g : α -> β} {a : α} (h : IsLocalExtrOn f s a)
    (heq : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : IsLocalExtrOn g s a :=
h.congr heq heq.eq_of_nhdsWithin hmem

/--
theorem `Filter.EventuallyEq.isLocalExtrOn_iff` / 定理 `Filter.EventuallyEq.isLocalExtrOn_iff`

English:
theorem Filter.EventuallyEq.isLocalExtrOn_iff
  statement: {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
  proof: heq.isExtrFilter_iff heq.eq_of_nhdsWithin hmem

中文:
定理 滤子.EventuallyEq.isLocalExtrOn_iff
  结论: {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
  证明: heq.isExtrFilter_iff heq.eq_of_nhdsWithin hmem

Depends on / 依赖: eq_of_nhdsWithin, heq.eq_of_nhdsWithin, heq.isExtrFilter_iff, isExtrFilter_iff
-/
theorem Filter.EventuallyEq.isLocalExtrOn_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
    (hmem : a in s) : IsLocalExtrOn f s a ↔ IsLocalExtrOn g s a :=
heq.isExtrFilter_iff heq.eq_of_nhdsWithin hmem

/--
theorem `Filter.EventuallyLE.isLocalMax` / 定理 `Filter.EventuallyLE.isLocalMax`

English:
theorem Filter.EventuallyLE.isLocalMax
  statement: {f g : α -> β} {a : α} (hle : g <=ᶠ[𝓝 a] f) (hfga : f a = g a)
  proof: hle.isMaxFilter hfga h

nonrec theorem IsLocalMax.congr {f g : α -> β} {a : α} (h : IsLocalMax f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMax g a :=
  h.congr heq heq.eq_of_nhds

中文:
定理 滤子.EventuallyLE.isLocalMax
  结论: {f g : α -> β} {a : α} (hle : g <=ᶠ[𝓝 a] f) (hfga : f a = g a)
  证明: hle.isMaxFilter hfga h

nonrec theorem IsLocalMax.congr {f g : α -> β} {a : α} (h : IsLocalMax f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMax g a :=
  h.congr heq heq.eq_of_nhds

Depends on / 依赖: hle.isMaxFilter, isMaxFilter
-/
theorem Filter.EventuallyLE.isLocalMax {f g : α -> β} {a : α} (hle : g <=ᶠ[𝓝 a] f) (hfga : f a = g a)
    (h : IsLocalMax f a) : IsLocalMax g a :=
  hle.isMaxFilter hfga h

nonrec theorem IsLocalMax.congr {f g : α -> β} {a : α} (h : IsLocalMax f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMax g a :=
  h.congr heq heq.eq_of_nhds

/--
theorem `Filter.EventuallyEq.isLocalMax_iff` / 定理 `Filter.EventuallyEq.isLocalMax_iff`

English:
theorem Filter.EventuallyEq.isLocalMax_iff
  given: {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a] g)
  proof: heq.isMaxFilter_iff heq.eq_of_nhds

中文:
定理 滤子.EventuallyEq.isLocalMax_iff
  条件: {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a] g)
  证明: heq.isMaxFilter_iff heq.eq_of_nhds

Depends on / 依赖: eq_of_nhds, heq.eq_of_nhds, heq.isMaxFilter_iff, isMaxFilter_iff
-/
theorem Filter.EventuallyEq.isLocalMax_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMax f a ↔ IsLocalMax g a :=
  heq.isMaxFilter_iff heq.eq_of_nhds

/--
theorem `Filter.EventuallyLE.isLocalMin` / 定理 `Filter.EventuallyLE.isLocalMin`

English:
theorem Filter.EventuallyLE.isLocalMin
  statement: {f g : α -> β} {a : α} (hle : f <=ᶠ[𝓝 a] g) (hfga : f a = g a)
  proof: hle.isMinFilter hfga h

nonrec theorem IsLocalMin.congr {f g : α -> β} {a : α} (h : IsLocalMin f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMin g a :=
  h.congr heq heq.eq_of_nhds

中文:
定理 滤子.EventuallyLE.isLocalMin
  结论: {f g : α -> β} {a : α} (hle : f <=ᶠ[𝓝 a] g) (hfga : f a = g a)
  证明: hle.isMinFilter hfga h

nonrec theorem IsLocalMin.congr {f g : α -> β} {a : α} (h : IsLocalMin f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMin g a :=
  h.congr heq heq.eq_of_nhds

Depends on / 依赖: hle.isMinFilter, isMinFilter
-/
theorem Filter.EventuallyLE.isLocalMin {f g : α -> β} {a : α} (hle : f <=ᶠ[𝓝 a] g) (hfga : f a = g a)
    (h : IsLocalMin f a) : IsLocalMin g a :=
  hle.isMinFilter hfga h

nonrec theorem IsLocalMin.congr {f g : α -> β} {a : α} (h : IsLocalMin f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMin g a :=
  h.congr heq heq.eq_of_nhds

/--
theorem `Filter.EventuallyEq.isLocalMin_iff` / 定理 `Filter.EventuallyEq.isLocalMin_iff`

English:
theorem Filter.EventuallyEq.isLocalMin_iff
  given: {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a] g)
  proof: heq.isMinFilter_iff heq.eq_of_nhds

nonrec theorem IsLocalExtr.congr {f g : α -> β} {a : α} (h : IsLocalExtr f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalExtr g a :=
  h.congr heq heq.eq_of_nhds

中文:
定理 滤子.EventuallyEq.isLocalMin_iff
  条件: {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a] g)
  证明: heq.isMinFilter_iff heq.eq_of_nhds

nonrec theorem IsLocalExtr.congr {f g : α -> β} {a : α} (h : IsLocalExtr f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalExtr g a :=
  h.congr heq heq.eq_of_nhds

Depends on / 依赖: eq_of_nhds, heq.eq_of_nhds, heq.isMinFilter_iff, isMinFilter_iff
-/
theorem Filter.EventuallyEq.isLocalMin_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMin f a ↔ IsLocalMin g a :=
  heq.isMinFilter_iff heq.eq_of_nhds

nonrec theorem IsLocalExtr.congr {f g : α -> β} {a : α} (h : IsLocalExtr f a) (heq : f =ᶠ[𝓝 a] g) :
    IsLocalExtr g a :=
  h.congr heq heq.eq_of_nhds

/--
theorem `Filter.EventuallyEq.isLocalExtr_iff` / 定理 `Filter.EventuallyEq.isLocalExtr_iff`

English:
theorem Filter.EventuallyEq.isLocalExtr_iff
  given: {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a] g)
  proof: heq.isExtrFilter_iff heq.eq_of_nhds

中文:
定理 滤子.EventuallyEq.isLocalExtr_iff
  条件: {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a] g)
  证明: heq.isExtrFilter_iff heq.eq_of_nhds

Depends on / 依赖: eq_of_nhds, heq.eq_of_nhds, heq.isExtrFilter_iff, isExtrFilter_iff
-/
theorem Filter.EventuallyEq.isLocalExtr_iff {f g : α -> β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalExtr f a ↔ IsLocalExtr g a :=
  heq.isExtrFilter_iff heq.eq_of_nhds

end Eventually

/--
lemma `isLocalMax_of_mono_anti'` / 引理 `isLocalMax_of_mono_anti'`

English:
lemma isLocalMax_of_mono_anti'
  statement: {α : Type*} [TopologicalSpace α] [LinearOrder α]
  proof: have : b in a := mem_of_mem_nhdsWithin (by simp) ha
  have : b in c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)

中文:
引理 isLocalMax_of_mono_anti'
  结论: {α : 类型} [拓扑空间 α] [线性序 α]
  证明: have : b in a := mem_of_mem_nhdsWithin (by simp) ha
  have : b in c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)

Depends on / 依赖: le_total, mem_of_mem_nhdsWithin, mem_of_superset, nhds_of_Ici_Iic
-/
lemma isLocalMax_of_mono_anti' {α : Type*} [TopologicalSpace α] [LinearOrder α]
    {β : Type*} [Preorder β] {b : α} {f : α -> β}
    {a : Set α} (ha : a in 𝓝[<=] b) {c : Set α} (hc : c in 𝓝[>=] b)
    (h₀ : MonotoneOn f a) (h₁ : AntitoneOn f c) : IsLocalMax f b :=
  have : b in a := mem_of_mem_nhdsWithin (by simp) ha
  have : b in c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)

/--
lemma `isLocalMin_of_anti_mono'` / 引理 `isLocalMin_of_anti_mono'`

English:
lemma isLocalMin_of_anti_mono'
  statement: {α : Type*} [TopologicalSpace α] [LinearOrder α]
  proof: have : b in a := mem_of_mem_nhdsWithin (by simp) ha
  have : b in c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)

中文:
引理 isLocalMin_of_anti_mono'
  结论: {α : 类型} [拓扑空间 α] [线性序 α]
  证明: have : b in a := mem_of_mem_nhdsWithin (by simp) ha
  have : b in c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)

Depends on / 依赖: le_total, mem_of_mem_nhdsWithin, mem_of_superset, nhds_of_Ici_Iic
-/
lemma isLocalMin_of_anti_mono' {α : Type*} [TopologicalSpace α] [LinearOrder α]
    {β : Type*} [Preorder β] {b : α} {f : α -> β}
    {a : Set α} (ha : a in 𝓝[<=] b) {c : Set α} (hc : c in 𝓝[>=] b)
    (h₀ : AntitoneOn f a) (h₁ : MonotoneOn f c) : IsLocalMin f b :=
  have : b in a := mem_of_mem_nhdsWithin (by simp) ha
  have : b in c := mem_of_mem_nhdsWithin (by simp) hc
  mem_of_superset (nhds_of_Ici_Iic ha hc) (fun x _ => by rcases le_total x b <;> aesop)
