/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Locally uniform convergence

We define a sequence of functions `Fₙ` to *converge locally uniformly* to a limiting function `f`
with respect to a filter `p`, spelled `TendstoLocallyUniformly F f p`, if for any `x ∈ s` and any
entourage of the diagonal `u`, there is a neighbourhood `v` of `x` such that `p`-eventually we have
`(f y, Fₙ y) ∈ u` for all `y ∈ v`.

It is important to note that this definition is somewhat non-standard; it is **not** in general
equivalent to "every point has a neighborhood on which the convergence is uniform", which is the
definition more commonly encountered in the literature. The reason is that in our definition the
neighborhood `v` of `x` can depend on the entourage `u`; so our condition is *a priori* weaker than
the usual one, although the two conditions are equivalent if the domain is locally compact. See
`tendstoLocallyUniformlyOn_of_forall_exists_nhds` for the one-way implication; the equivalence
assuming local compactness is part of `tendstoLocallyUniformlyOn_TFAE`.

We adopt this weaker condition because it is more general but appears to be sufficient for
the standard applications of locally-uniform convergence (in particular, for proving that a
locally-uniform limit of continuous functions is continuous).

We also define variants for locally uniform convergence on a subset, called
`TendstoLocallyUniformlyOn F f p s`.

## Tags

Uniform limit, uniform convergence, tends uniformly to
-/

@[expose] public section

noncomputable section

open Topology Uniformity Filter Set Uniform

variable {α β γ ι : Type*} [TopologicalSpace α] [UniformSpace β]
variable {F : ι -> α -> β} {f : α -> β} {s s' : Set α} {x : α} {p : Filter ι}

/--
Definition of `TendstoLocallyUniformlyOn` / `TendstoLocallyUniformlyOn` 的定义

English:
definition TendstoLocallyUniformlyOn
  signature: (F : ι -> α -> β) (f : α -> β) (p : Filter ι) (s : Set α)
  body: forall u in 𝓤 β, forall x in s, exists t in 𝓝[s] x, forallᶠ n in p, forall y in t, (f y, F n y) in u

中文:
定义 TendstoLocallyUniformlyOn
  签名: (F : ι -> α -> β) (f : α -> β) (p : Filter ι) (s : Set α)
  定义体: forall u in 𝓤 β, forall x in s, exists t in 𝓝[s] x, forallᶠ n in p, forall y in t, (f y, F n y) in u
-/
def TendstoLocallyUniformlyOn (F : ι -> α -> β) (f : α -> β) (p : Filter ι) (s : Set α) :=
  forall u in 𝓤 β, forall x in s, exists t in 𝓝[s] x, forallᶠ n in p, forall y in t, (f y, F n y) in u

/--
Definition of `TendstoLocallyUniformly` / `TendstoLocallyUniformly` 的定义

English:
definition TendstoLocallyUniformly
  signature: (F : ι -> α -> β) (f : α -> β) (p : Filter ι)
  body: forall u in 𝓤 β, forall x : α, exists t in 𝓝 x, forallᶠ n in p, forall y in t, (f y, F n y) in u

中文:
定义 TendstoLocallyUniformly
  签名: (F : ι -> α -> β) (f : α -> β) (p : Filter ι)
  定义体: forall u in 𝓤 β, forall x : α, exists t in 𝓝 x, forallᶠ n in p, forall y in t, (f y, F n y) in u
-/
def TendstoLocallyUniformly (F : ι -> α -> β) (f : α -> β) (p : Filter ι) :=
  forall u in 𝓤 β, forall x : α, exists t in 𝓝 x, forallᶠ n in p, forall y in t, (f y, F n y) in u

/--
theorem `tendstoLocallyUniformlyOn_univ` / 定理 `tendstoLocallyUniformlyOn_univ`

English:
theorem tendstoLocallyUniformlyOn_univ
  proof: by
  simp [TendstoLocallyUniformlyOn, TendstoLocallyUniformly, nhdsWithin_univ]

中文:
定理 tendstoLocallyUniformlyOn_univ
  证明: by
  simp [TendstoLocallyUniformlyOn, TendstoLocallyUniformly, nhdsWithin_univ]

Depends on / 依赖: TendstoLocallyUniformly, TendstoLocallyUniformlyOn, nhdsWithin_univ
-/
theorem tendstoLocallyUniformlyOn_univ :
    TendstoLocallyUniformlyOn F f p univ ↔ TendstoLocallyUniformly F f p := by
  simp [TendstoLocallyUniformlyOn, TendstoLocallyUniformly, nhdsWithin_univ]

/--
theorem `tendstoLocallyUniformlyOn_iff_forall_tendsto` / 定理 `tendstoLocallyUniformlyOn_iff_forall_tendsto`

English:
theorem tendstoLocallyUniformlyOn_iff_forall_tendsto
  proof: forall₂_comm.trans forall₄_congr fun _ _ _ _ => by
    simp_rw [mem_map, mem_prod_iff_right, mem_preimage]

nonrec theorem IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto (hs : IsOpen s) :
    TendstoLocallyUniformlyOn F f p s ↔
      forall x in s, Tendsto (fun y : ι × α => (f y.2, F y.1 y.2)) 

中文:
定理 tendstoLocallyUniformlyOn_iff_forall_tendsto
  证明: forall₂_comm.trans forall₄_congr fun _ _ _ _ => by
    simp_rw [mem_map, mem_prod_iff_right, mem_preimage]

nonrec theorem IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto (hs : IsOpen s) :
    TendstoLocallyUniformlyOn F f p s ↔
      forall x in s, Tendsto (fun y : ι × α => (f y.2, F y.1 y.2)) 

Depends on / 依赖: _comm.trans, mem_map, mem_preimage, mem_prod_iff_right, simp_rw
-/
theorem tendstoLocallyUniformlyOn_iff_forall_tendsto :
    TendstoLocallyUniformlyOn F f p s ↔
      forall x in s, Tendsto (fun y : ι × α => (f y.2, F y.1 y.2)) (p ×ˢ 𝓝[s] x) (𝓤 β) :=
forall₂_comm.trans forall₄_congr fun _ _ _ _ => by
    simp_rw [mem_map, mem_prod_iff_right, mem_preimage]

nonrec theorem IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto (hs : IsOpen s) :
    TendstoLocallyUniformlyOn F f p s ↔
      forall x in s, Tendsto (fun y : ι × α => (f y.2, F y.1 y.2)) (p ×ˢ 𝓝 x) (𝓤 β) :=
tendstoLocallyUniformlyOn_iff_forall_tendsto.trans forall₂_congr fun x hx => by
    rw [hs.nhdsWithin_eq hx]

/--
theorem `tendstoLocallyUniformly_iff_forall_tendsto` / 定理 `tendstoLocallyUniformly_iff_forall_tendsto`

English:
theorem tendstoLocallyUniformly_iff_forall_tendsto
  proof: by
  simp [← tendstoLocallyUniformlyOn_univ, isOpen_univ.tendstoLocallyUniformlyOn_iff_forall_tendsto]

中文:
定理 tendstoLocallyUniformly_iff_forall_tendsto
  证明: by
  simp [← tendstoLocallyUniformlyOn_univ, isOpen_univ.tendstoLocallyUniformlyOn_iff_forall_tendsto]

Depends on / 依赖: isOpen_univ, isOpen_univ.tendstoLocallyUniformlyOn_iff_forall_tendsto, tendstoLocallyUniformlyOn_iff_forall_tendsto, tendstoLocallyUniformlyOn_univ
-/
theorem tendstoLocallyUniformly_iff_forall_tendsto :
    TendstoLocallyUniformly F f p ↔
      forall x, Tendsto (fun y : ι × α => (f y.2, F y.1 y.2)) (p ×ˢ 𝓝 x) (𝓤 β) := by
  simp [← tendstoLocallyUniformlyOn_univ, isOpen_univ.tendstoLocallyUniformlyOn_iff_forall_tendsto]

/--
theorem `tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe` / 定理 `tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe`

English:
theorem tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe
  proof: by
  simp only [tendstoLocallyUniformly_iff_forall_tendsto, Subtype.forall', tendsto_map'_iff,
    tendstoLocallyUniformlyOn_iff_forall_tendsto, ← map_nhds_subtype_val, prod_map_right]; rfl

中文:
定理 tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe
  证明: by
  simp only [tendstoLocallyUniformly_iff_forall_tendsto, Subtype.forall', tendsto_map'_iff,
    tendstoLocallyUniformlyOn_iff_forall_tendsto, ← map_nhds_subtype_val, prod_map_right]; rfl

Depends on / 依赖: Subtype, Subtype.forall, _iff, map_nhds_subtype_val, prod_map_right, tendstoLocallyUniformlyOn_iff_forall_tendsto, tendstoLocallyUniformly_iff_forall_tendsto, tendsto_map
-/
theorem tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe :
    TendstoLocallyUniformlyOn F f p s ↔
      TendstoLocallyUniformly (fun i (x : s) => F i x) (f ∘ (↑)) p := by
  simp only [tendstoLocallyUniformly_iff_forall_tendsto, Subtype.forall', tendsto_map'_iff,
    tendstoLocallyUniformlyOn_iff_forall_tendsto, ← map_nhds_subtype_val, prod_map_right]; rfl

/--
theorem `TendstoUniformlyOn.tendstoLocallyUniformlyOn` / 定理 `TendstoUniformlyOn.tendstoLocallyUniformlyOn`

English:
theorem TendstoUniformlyOn.tendstoLocallyUniformlyOn
  given: (h : TendstoUniformlyOn F f p s)
  proof: fun u hu _ _ =>
  ⟨s, self_mem_nhdsWithin, by simpa using h u hu⟩

中文:
定理 TendstoUniformlyOn.tendstoLocallyUniformlyOn
  条件: (h : TendstoUniformlyOn F f p s)
  证明: fun u hu _ _ =>
  ⟨s, self_mem_nhdsWithin, by simpa using h u hu⟩
-/
protected theorem TendstoUniformlyOn.tendstoLocallyUniformlyOn (h : TendstoUniformlyOn F f p s) :
    TendstoLocallyUniformlyOn F f p s := fun u hu _ _ =>
  ⟨s, self_mem_nhdsWithin, by simpa using h u hu⟩

/--
theorem `TendstoUniformly.tendstoLocallyUniformly` / 定理 `TendstoUniformly.tendstoLocallyUniformly`

English:
theorem TendstoUniformly.tendstoLocallyUniformly
  given: (h : TendstoUniformly F f p)
  proof: fun u hu _ => ⟨univ, univ_mem, by simpa using h u hu⟩

中文:
定理 TendstoUniformly.tendstoLocallyUniformly
  条件: (h : TendstoUniformly F f p)
  证明: fun u hu _ => ⟨univ, univ_mem, by simpa using h u hu⟩
-/
protected theorem TendstoUniformly.tendstoLocallyUniformly (h : TendstoUniformly F f p) :
    TendstoLocallyUniformly F f p := fun u hu _ => ⟨univ, univ_mem, by simpa using h u hu⟩

/--
theorem `TendstoLocallyUniformlyOn.mono` / 定理 `TendstoLocallyUniformlyOn.mono`

English:
theorem TendstoLocallyUniformlyOn.mono
  given: (h : TendstoLocallyUniformlyOn F f p s) (h' : s' subseteq s)
  proof: by
  intro u hu x hx
  rcases h u hu x (h' hx) with ⟨t, ht, H⟩
  exact ⟨t, nhdsWithin_mono x h' ht, H.mono fun n => id⟩

中文:
定理 TendstoLocallyUniformlyOn.mono
  条件: (h : TendstoLocallyUniformlyOn F f p s) (h' : s' subseteq s)
  证明: by
  intro u hu x hx
  rcases h u hu x (h' hx) with ⟨t, ht, H⟩
  exact ⟨t, nhdsWithin_mono x h' ht, H.mono fun n => id⟩

Depends on / 依赖: H.mono, nhdsWithin_mono
-/
theorem TendstoLocallyUniformlyOn.mono (h : TendstoLocallyUniformlyOn F f p s) (h' : s' subseteq s) :
    TendstoLocallyUniformlyOn F f p s' := by
  intro u hu x hx
  rcases h u hu x (h' hx) with ⟨t, ht, H⟩
  exact ⟨t, nhdsWithin_mono x h' ht, H.mono fun n => id⟩

/--
theorem `tendstoLocallyUniformlyOn_iUnion` / 定理 `tendstoLocallyUniformlyOn_iUnion`

English:
theorem tendstoLocallyUniformlyOn_iUnion
  statement: {ι' : Sort*} {S : ι' -> Set α} (hS : forall i, IsOpen (S i))
  proof: (isOpen_iUnion hS).tendstoLocallyUniformlyOn_iff_forall_tendsto.2 fun _x hx =>
    let ⟨i, hi⟩ := mem_iUnion.1 hx
    (hS i).tendstoLocallyUniformlyOn_iff_forall_tendsto.1 (h i) _ hi

中文:
定理 tendstoLocallyUniformlyOn_iUnion
  结论: {ι' : Sort*} {S : ι' -> Set α} (hS : 对任意 i, IsOpen (S i))
  证明: (isOpen_iUnion hS).tendstoLocallyUniformlyOn_iff_forall_tendsto.2 fun _x hx =>
    let ⟨i, hi⟩ := mem_iUnion.1 hx
    (hS i).tendstoLocallyUniformlyOn_iff_forall_tendsto.1 (h i) _ hi

Depends on / 依赖: isOpen_iUnion, mem_iUnion, tendstoLocallyUniformlyOn_iff_forall_tendsto
-/
theorem tendstoLocallyUniformlyOn_iUnion {ι' : Sort*} {S : ι' -> Set α} (hS : forall i, IsOpen (S i))
    (h : forall i, TendstoLocallyUniformlyOn F f p (S i)) :
    TendstoLocallyUniformlyOn F f p (⋃ i, S i) :=
  (isOpen_iUnion hS).tendstoLocallyUniformlyOn_iff_forall_tendsto.2 fun _x hx =>
    let ⟨i, hi⟩ := mem_iUnion.1 hx
    (hS i).tendstoLocallyUniformlyOn_iff_forall_tendsto.1 (h i) _ hi

/--
theorem `tendstoLocallyUniformlyOn_biUnion` / 定理 `tendstoLocallyUniformlyOn_biUnion`

English:
theorem tendstoLocallyUniformlyOn_biUnion
  statement: {s : Set γ} {S : γ -> Set α} (hS : forall i in s, IsOpen (S i))
  proof: tendstoLocallyUniformlyOn_iUnion (fun i => isOpen_iUnion (hS i))
    fun i => tendstoLocallyUniformlyOn_iUnion (hS i) (h i)

中文:
定理 tendstoLocallyUniformlyOn_biUnion
  结论: {s : Set γ} {S : γ -> Set α} (hS : 对任意 i in s, IsOpen (S i))
  证明: tendstoLocallyUniformlyOn_iUnion (fun i => isOpen_iUnion (hS i))
    fun i => tendstoLocallyUniformlyOn_iUnion (hS i) (h i)

Depends on / 依赖: isOpen_iUnion, tendstoLocallyUniformlyOn_iUnion
-/
theorem tendstoLocallyUniformlyOn_biUnion {s : Set γ} {S : γ -> Set α} (hS : forall i in s, IsOpen (S i))
    (h : forall i in s, TendstoLocallyUniformlyOn F f p (S i)) :
    TendstoLocallyUniformlyOn F f p (⋃ i in s, S i) :=
  tendstoLocallyUniformlyOn_iUnion (fun i => isOpen_iUnion (hS i))
    fun i => tendstoLocallyUniformlyOn_iUnion (hS i) (h i)

/--
theorem `tendstoLocallyUniformlyOn_sUnion` / 定理 `tendstoLocallyUniformlyOn_sUnion`

English:
theorem tendstoLocallyUniformlyOn_sUnion
  statement: (S : Set (Set α)) (hS : forall s in S, IsOpen s)
  proof: by
  rw [sUnion_eq_biUnion]
  exact tendstoLocallyUniformlyOn_biUnion hS h

中文:
定理 tendstoLocallyUniformlyOn_sUnion
  结论: (S : Set (Set α)) (hS : 对任意 s in S, IsOpen s)
  证明: by
  rw [sUnion_eq_biUnion]
  exact tendstoLocallyUniformlyOn_biUnion hS h

Depends on / 依赖: sUnion_eq_biUnion, tendstoLocallyUniformlyOn_biUnion
-/
theorem tendstoLocallyUniformlyOn_sUnion (S : Set (Set α)) (hS : forall s in S, IsOpen s)
    (h : forall s in S, TendstoLocallyUniformlyOn F f p s) : TendstoLocallyUniformlyOn F f p (⋃₀ S) := by
  rw [sUnion_eq_biUnion]
  exact tendstoLocallyUniformlyOn_biUnion hS h

/--
theorem `TendstoLocallyUniformlyOn.union` / 定理 `TendstoLocallyUniformlyOn.union`

English:
theorem TendstoLocallyUniformlyOn.union
  statement: (hs₁ : IsOpen s) (hs₂ : IsOpen s')
  proof: by
  rw [← sUnion_pair]
  refine tendstoLocallyUniformlyOn_sUnion _ ?_ ?_ <;> simp [*]

中文:
定理 TendstoLocallyUniformlyOn.union
  结论: (hs₁ : IsOpen s) (hs₂ : IsOpen s')
  证明: by
  rw [← sUnion_pair]
  refine tendstoLocallyUniformlyOn_sUnion _ ?_ ?_ <;> simp [*]

Depends on / 依赖: sUnion_pair, tendstoLocallyUniformlyOn_sUnion
-/
theorem TendstoLocallyUniformlyOn.union (hs₁ : IsOpen s) (hs₂ : IsOpen s')
    (h₁ : TendstoLocallyUniformlyOn F f p s) (h₂ : TendstoLocallyUniformlyOn F f p s') :
    TendstoLocallyUniformlyOn F f p (s union s') := by
  rw [← sUnion_pair]
  refine tendstoLocallyUniformlyOn_sUnion _ ?_ ?_ <;> simp [*]

/--
theorem `TendstoLocallyUniformly.tendstoLocallyUniformlyOn` / 定理 `TendstoLocallyUniformly.tendstoLocallyUniformlyOn`

English:
theorem TendstoLocallyUniformly.tendstoLocallyUniformlyOn
  proof: (tendstoLocallyUniformlyOn_univ.mpr h).mono (subset_univ _)

中文:
定理 TendstoLocallyUniformly.tendstoLocallyUniformlyOn
  证明: (tendstoLocallyUniformlyOn_univ.mpr h).mono (subset_univ _)
-/
protected theorem TendstoLocallyUniformly.tendstoLocallyUniformlyOn
    (h : TendstoLocallyUniformly F f p) : TendstoLocallyUniformlyOn F f p s :=
  (tendstoLocallyUniformlyOn_univ.mpr h).mono (subset_univ _)

/--
theorem `tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace` / 定理 `tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace`

English:
theorem tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace
  given: [CompactSpace α]
  proof: by
  refine ⟨fun h V hV => ?_, TendstoUniformly.tendstoLocallyUniformly⟩
  choose U hU using h V hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover' (fun k _ => U k) fun k _ => (hU k).1
  replace hU := fun x : t => (hU x).2
  rw [← eventually_all] at hU
  refine hU.mono fun i hi x => ?_
  spec

中文:
定理 tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace
  条件: [CompactSpace α]
  证明: by
  refine ⟨fun h V hV => ?_, TendstoUniformly.tendstoLocallyUniformly⟩
  choose U hU using h V hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover' (fun k _ => U k) fun k _ => (hU k).1
  replace hU := fun x : t => (hU x).2
  rw [← eventually_all] at hU
  refine hU.mono fun i hi x => ?_
  spec

Depends on / 依赖: SetCoe, SetCoe.exists, TendstoUniformly, TendstoUniformly.tendstoLocallyUniformly, elim_nhds_subcover, eventually_all, exists_and_right, exists_prop, hU.mono, isCompact_univ, isCompact_univ.elim_nhds_subcover, mem_iUnion, mem_univ, replace, specialize, tendstoLocallyUniformly
-/
theorem tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace [CompactSpace α] :
    TendstoLocallyUniformly F f p ↔ TendstoUniformly F f p := by
  refine ⟨fun h V hV => ?_, TendstoUniformly.tendstoLocallyUniformly⟩
  choose U hU using h V hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover' (fun k _ => U k) fun k _ => (hU k).1
  replace hU := fun x : t => (hU x).2
  rw [← eventually_all] at hU
  refine hU.mono fun i hi x => ?_
  specialize ht (mem_univ x)
  simp only [exists_prop, mem_iUnion, SetCoe.exists, exists_and_right] at ht
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := ht
  exact hi ⟨⟨y, hy₁⟩, hy₂⟩ x hy₃

/--
theorem `tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact` / 定理 `tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact`

English:
theorem tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
  given: (hs : IsCompact s)
  proof: by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  refine ⟨fun h => ?_, TendstoUniformlyOn.tendstoLocallyUniformlyOn⟩
  rwa [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe,
    tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace, ←
    tendstoUniformlyOn_iff_te

中文:
定理 tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
  条件: (hs : IsCompact s)
  证明: by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  refine ⟨fun h => ?_, TendstoUniformlyOn.tendstoLocallyUniformlyOn⟩
  rwa [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe,
    tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace, ←
    tendstoUniformlyOn_iff_te

Depends on / 依赖: CompactSpace, TendstoUniformlyOn, TendstoUniformlyOn.tendstoLocallyUniformlyOn, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe, tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace, tendstoUniformlyOn_iff_tendstoUniformly_comp_coe
-/
theorem tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (hs : IsCompact s) :
    TendstoLocallyUniformlyOn F f p s ↔ TendstoUniformlyOn F f p s := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  refine ⟨fun h => ?_, TendstoUniformlyOn.tendstoLocallyUniformlyOn⟩
  rwa [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe,
    tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace, ←
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe] at h

/-!
### Composition
-/

section Comp

/--
theorem `TendstoLocallyUniformlyOn.comp` / 定理 `TendstoLocallyUniformlyOn.comp`

English:
theorem TendstoLocallyUniformlyOn.comp
  statement: [TopologicalSpace γ] {t : Set γ}
  proof: by
  intro u hu x hx
  rcases h u hu (g x) (hg hx) with ⟨a, ha, H⟩
  have : g ⁻¹' a in 𝓝[t] x :=
    (cg x hx).preimage_mem_nhdsWithin' (nhdsWithin_mono (g x) hg.image_subset ha)
  exact ⟨g ⁻¹' a, this, H.mono fun n hn y hy => hn _ hy⟩

中文:
定理 TendstoLocallyUniformlyOn.comp
  结论: [TopologicalSpace γ] {t : Set γ}
  证明: by
  intro u hu x hx
  rcases h u hu (g x) (hg hx) with ⟨a, ha, H⟩
  have : g ⁻¹' a in 𝓝[t] x :=
    (cg x hx).preimage_mem_nhdsWithin' (nhdsWithin_mono (g x) hg.image_subset ha)
  exact ⟨g ⁻¹' a, this, H.mono fun n hn y hy => hn _ hy⟩

Depends on / 依赖: H.mono, hg.image_subset, image_subset, nhdsWithin_mono, preimage_mem_nhdsWithin
-/
theorem TendstoLocallyUniformlyOn.comp [TopologicalSpace γ] {t : Set γ}
    (h : TendstoLocallyUniformlyOn F f p s) (g : γ -> α) (hg : MapsTo g t s)
    (cg : ContinuousOn g t) : TendstoLocallyUniformlyOn (fun n => F n ∘ g) (f ∘ g) p t := by
  intro u hu x hx
  rcases h u hu (g x) (hg hx) with ⟨a, ha, H⟩
  have : g ⁻¹' a in 𝓝[t] x :=
    (cg x hx).preimage_mem_nhdsWithin' (nhdsWithin_mono (g x) hg.image_subset ha)
  exact ⟨g ⁻¹' a, this, H.mono fun n hn y hy => hn _ hy⟩

/--
theorem `TendstoLocallyUniformly.comp` / 定理 `TendstoLocallyUniformly.comp`

English:
theorem TendstoLocallyUniformly.comp
  statement: [TopologicalSpace γ] (h : TendstoLocallyUniformly F f p)
  proof: by
  rw [← tendstoLocallyUniformlyOn_univ] at h ⊢
  rw [← continuousOn_univ] at cg
  exact h.comp _ (mapsTo_univ _ _) cg

中文:
定理 TendstoLocallyUniformly.comp
  结论: [TopologicalSpace γ] (h : TendstoLocallyUniformly F f p)
  证明: by
  rw [← tendstoLocallyUniformlyOn_univ] at h ⊢
  rw [← continuousOn_univ] at cg
  exact h.comp _ (mapsTo_univ _ _) cg

Depends on / 依赖: continuousOn_univ, h.comp, mapsTo_univ, tendstoLocallyUniformlyOn_univ
-/
theorem TendstoLocallyUniformly.comp [TopologicalSpace γ] (h : TendstoLocallyUniformly F f p)
    (g : γ -> α) (cg : Continuous g) : TendstoLocallyUniformly (fun n => F n ∘ g) (f ∘ g) p := by
  rw [← tendstoLocallyUniformlyOn_univ] at h ⊢
  rw [← continuousOn_univ] at cg
  exact h.comp _ (mapsTo_univ _ _) cg

variable [UniformSpace γ] {g : β -> γ}

/--
theorem `UniformContinuousOn.comp_tendstoLocallyUniformlyOn` / 定理 `UniformContinuousOn.comp_tendstoLocallyUniformlyOn`

English:
theorem UniformContinuousOn.comp_tendstoLocallyUniformlyOn
  statement: {t : Set β}
  proof: by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine fun x hx => Tendsto.comp hg (tendsto_inf.mpr ⟨hf x hx, tendsto_principal.mpr ?_⟩)
  filter_upwards [hFs.prod_mk eventually_mem_nhdsWithin] with y hy using ⟨hfs hy.2, hy.1 hy.2⟩

中文:
定理 UniformContinuousOn.comp_tendstoLocallyUniformlyOn
  结论: {t : Set β}
  证明: by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine fun x hx => Tendsto.comp hg (tendsto_inf.mpr ⟨hf x hx, tendsto_principal.mpr ?_⟩)
  filter_upwards [hFs.prod_mk eventually_mem_nhdsWithin] with y hy using ⟨hfs hy.2, hy.1 hy.2⟩

Depends on / 依赖: Tendsto, Tendsto.comp, eventually_mem_nhdsWithin, filter_upwards, hFs.prod_mk, prod_mk, tendstoLocallyUniformlyOn_iff_forall_tendsto, tendsto_inf, tendsto_inf.mpr, tendsto_principal, tendsto_principal.mpr
-/
theorem UniformContinuousOn.comp_tendstoLocallyUniformlyOn {t : Set β}
    (hg : UniformContinuousOn g t) (hf : TendstoLocallyUniformlyOn F f p s)
    (hfs : MapsTo f s t) (hFs : forallᶠ n in p, MapsTo (F n) s t) :
    TendstoLocallyUniformlyOn (g ∘ F ·) (g ∘ f) p s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine fun x hx => Tendsto.comp hg (tendsto_inf.mpr ⟨hf x hx, tendsto_principal.mpr ?_⟩)
  filter_upwards [hFs.prod_mk eventually_mem_nhdsWithin] with y hy using ⟨hfs hy.2, hy.1 hy.2⟩

/--
theorem `UniformContinuousOn.comp_tendstoLocallyUniformly` / 定理 `UniformContinuousOn.comp_tendstoLocallyUniformly`

English:
theorem UniformContinuousOn.comp_tendstoLocallyUniformly
  statement: {t : Set β}
  proof: by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hg.comp_tendstoLocallyUniformlyOn hf <;> simpa [MapsTo]

中文:
定理 UniformContinuousOn.comp_tendstoLocallyUniformly
  结论: {t : Set β}
  证明: by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hg.comp_tendstoLocallyUniformlyOn hf <;> simpa [MapsTo]

Depends on / 依赖: MapsTo, comp_tendstoLocallyUniformlyOn, hg.comp_tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn_univ
-/
theorem UniformContinuousOn.comp_tendstoLocallyUniformly {t : Set β}
    (hg : UniformContinuousOn g t) (hf : TendstoLocallyUniformly F f p)
    (hfs : forall x, f x in t) (hFs : forallᶠ n in p, forall x, F n x in t) :
    TendstoLocallyUniformly (g ∘ F ·) (g ∘ f) p := by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hg.comp_tendstoLocallyUniformlyOn hf <;> simpa [MapsTo]

/--
theorem `UniformContinuous.comp_tendstoLocallyUniformlyOn` / 定理 `UniformContinuous.comp_tendstoLocallyUniformlyOn`

English:
theorem UniformContinuous.comp_tendstoLocallyUniformlyOn
  statement: (hg : UniformContinuous g)
  proof: hg.uniformContinuousOn.comp_tendstoLocallyUniformlyOn hf (mapsTo_univ _ _) .of_forall fun _ =>
    mapsTo_univ _ _

中文:
定理 UniformContinuous.comp_tendstoLocallyUniformlyOn
  结论: (hg : UniformContinuous g)
  证明: hg.uniformContinuousOn.comp_tendstoLocallyUniformlyOn hf (mapsTo_univ _ _) .of_forall fun _ =>
    mapsTo_univ _ _

Depends on / 依赖: comp_tendstoLocallyUniformlyOn, hg.uniformContinuousOn.comp_tendstoLocallyUniformlyOn, mapsTo_univ, of_forall, uniformContinuousOn
-/
theorem UniformContinuous.comp_tendstoLocallyUniformlyOn (hg : UniformContinuous g)
    (hf : TendstoLocallyUniformlyOn F f p s) :
    TendstoLocallyUniformlyOn (g ∘ F ·) (g ∘ f) p s :=
hg.uniformContinuousOn.comp_tendstoLocallyUniformlyOn hf (mapsTo_univ _ _) .of_forall fun _ =>
    mapsTo_univ _ _

/--
theorem `UniformContinuous.comp_tendstoLocallyUniformly` / 定理 `UniformContinuous.comp_tendstoLocallyUniformly`

English:
theorem UniformContinuous.comp_tendstoLocallyUniformly
  statement: (hg : UniformContinuous g)
  proof: (hg.uniformContinuousOn (s := univ)).comp_tendstoLocallyUniformly hf (by simp) (by simp)

中文:
定理 UniformContinuous.comp_tendstoLocallyUniformly
  结论: (hg : UniformContinuous g)
  证明: (hg.uniformContinuousOn (s := univ)).comp_tendstoLocallyUniformly hf (by simp) (by simp)

Depends on / 依赖: comp_tendstoLocallyUniformly, hg.uniformContinuousOn, uniformContinuousOn
-/
theorem UniformContinuous.comp_tendstoLocallyUniformly (hg : UniformContinuous g)
    (hf : TendstoLocallyUniformly F f p) :
    TendstoLocallyUniformly (g ∘ F ·) (g ∘ f) p :=
  (hg.uniformContinuousOn (s := univ)).comp_tendstoLocallyUniformly hf (by simp) (by simp)

end Comp

/--
theorem `TendstoLocallyUniformlyOn.prodMk` / 定理 `TendstoLocallyUniformlyOn.prodMk`

English:
theorem TendstoLocallyUniformlyOn.prodMk
  statement: [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
  proof: by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  rw [uniformity_prod_eq_comap_prod]; rw [tendsto_comap_iff]
  exact (hF x hx).prodMk (hG x hx)

中文:
定理 TendstoLocallyUniformlyOn.prodMk
  结论: [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
  证明: by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  rw [uniformity_prod_eq_comap_prod]; rw [tendsto_comap_iff]
  exact (hF x hx).prodMk (hG x hx)

Depends on / 依赖: prodMk, tendstoLocallyUniformlyOn_iff_forall_tendsto, tendsto_comap_iff, uniformity_prod_eq_comap_prod
-/
theorem TendstoLocallyUniformlyOn.prodMk [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
    (hF : TendstoLocallyUniformlyOn F f p s) (hG : TendstoLocallyUniformlyOn G g p s) :
    TendstoLocallyUniformlyOn (fun n x => (F n x, G n x)) (fun x => (f x, g x)) p s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  rw [uniformity_prod_eq_comap_prod]; rw [tendsto_comap_iff]
  exact (hF x hx).prodMk (hG x hx)

/--
theorem `TendstoLocallyUniformlyOn.piProd` / 定理 `TendstoLocallyUniformlyOn.piProd`

English:
theorem TendstoLocallyUniformlyOn.piProd
  statement: [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
  proof: hF.prodMk hG

中文:
定理 TendstoLocallyUniformlyOn.piProd
  结论: [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
  证明: hF.prodMk hG

Depends on / 依赖: hF.prodMk, prodMk
-/
theorem TendstoLocallyUniformlyOn.piProd [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
    (hF : TendstoLocallyUniformlyOn F f p s) (hG : TendstoLocallyUniformlyOn G g p s) :
    TendstoLocallyUniformlyOn (fun n => Function.prod (F n) (G n)) (Function.prod f g) p s :=
  hF.prodMk hG

/--
theorem `TendstoLocallyUniformly.prodMk` / 定理 `TendstoLocallyUniformly.prodMk`

English:
theorem TendstoLocallyUniformly.prodMk
  statement: [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
  proof: by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  exact hF.prodMk hG

中文:
定理 TendstoLocallyUniformly.prodMk
  结论: [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
  证明: by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  exact hF.prodMk hG

Depends on / 依赖: hF.prodMk, prodMk, tendstoLocallyUniformlyOn_univ
-/
theorem TendstoLocallyUniformly.prodMk [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
    (hF : TendstoLocallyUniformly F f p) (hG : TendstoLocallyUniformly G g p) :
    TendstoLocallyUniformly (fun n x => (F n x, G n x)) (fun x => (f x, g x)) p := by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  exact hF.prodMk hG

/--
theorem `TendstoLocallyUniformly.piProd` / 定理 `TendstoLocallyUniformly.piProd`

English:
theorem TendstoLocallyUniformly.piProd
  statement: [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
  proof: hF.prodMk hG

中文:
定理 TendstoLocallyUniformly.piProd
  结论: [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
  证明: hF.prodMk hG

Depends on / 依赖: hF.prodMk, prodMk
-/
theorem TendstoLocallyUniformly.piProd [UniformSpace γ] {G : ι -> α -> γ} {g : α -> γ}
    (hF : TendstoLocallyUniformly F f p) (hG : TendstoLocallyUniformly G g p) :
    TendstoLocallyUniformly (fun n => Function.prod (F n) (G n)) (Function.prod f g) p :=
  hF.prodMk hG

/--
lemma `tendstoLocallyUniformlyOn_of_forall_exists_nhds` / 引理 `tendstoLocallyUniformlyOn_of_forall_exists_nhds`

English:
lemma tendstoLocallyUniformlyOn_of_forall_exists_nhds
  proof: by
  refine tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr fun x hx => ?_
  obtain ⟨t, ht, htr⟩ := h x hx
  rw [tendstoUniformlyOn_iff_tendsto] at htr
exact htr.mono_left prod_mono_right _ le_principal_iff.mpr ht

中文:
引理 tendstoLocallyUniformlyOn_of_forall_exists_nhds
  证明: by
  refine tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr fun x hx => ?_
  obtain ⟨t, ht, htr⟩ := h x hx
  rw [tendstoUniformlyOn_iff_tendsto] at htr
exact htr.mono_left prod_mono_right _ le_principal_iff.mpr ht

Depends on / 依赖: htr.mono_left, le_principal_iff, le_principal_iff.mpr, mono_left, prod_mono_right, tendstoLocallyUniformlyOn_iff_forall_tendsto, tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr, tendstoUniformlyOn_iff_tendsto
-/
lemma tendstoLocallyUniformlyOn_of_forall_exists_nhds
    (h : forall x in s, exists t in 𝓝[s] x, TendstoUniformlyOn F f p t) :
    TendstoLocallyUniformlyOn F f p s := by
  refine tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr fun x hx => ?_
  obtain ⟨t, ht, htr⟩ := h x hx
  rw [tendstoUniformlyOn_iff_tendsto] at htr
exact htr.mono_left prod_mono_right _ le_principal_iff.mpr ht

/--
lemma `tendstoLocallyUniformly_of_forall_exists_nhds` / 引理 `tendstoLocallyUniformly_of_forall_exists_nhds`

English:
lemma tendstoLocallyUniformly_of_forall_exists_nhds
  proof: tendstoLocallyUniformlyOn_univ.mp
 tendstoLocallyUniformlyOn_of_forall_exists_nhds (by simpa using h)

中文:
引理 tendstoLocallyUniformly_of_forall_exists_nhds
  证明: tendstoLocallyUniformlyOn_univ.mp
 tendstoLocallyUniformlyOn_of_forall_exists_nhds (by simpa using h)

Depends on / 依赖: tendstoLocallyUniformlyOn_of_forall_exists_nhds, tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_univ.mp
-/
lemma tendstoLocallyUniformly_of_forall_exists_nhds
    (h : forall x, exists t in 𝓝 x, TendstoUniformlyOn F f p t) :
    TendstoLocallyUniformly F f p :=
  tendstoLocallyUniformlyOn_univ.mp
 tendstoLocallyUniformlyOn_of_forall_exists_nhds (by simpa using h)

/--
theorem `tendstoLocallyUniformlyOn_TFAE` / 定理 `tendstoLocallyUniformlyOn_TFAE`

English:
theorem tendstoLocallyUniformlyOn_TFAE
  statement: [LocallyCompactSpace α] (G : ι -> α -> β) (g : α -> β)
  proof: by
  tfae_have 1 -> 2
  | h, K, hK1, hK2 =>
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK2).mp (h.mono hK1)
  tfae_have 2 -> 3
  | h, x, hx => by
    obtain ⟨K, ⟨hK1, hK2⟩, hK3⟩ := (compact_basis_nhds x).mem_iff.mp (hs.mem_nhds hx)
    exact ⟨K, nhdsWithin_le_nhds hK1, h K hK3 

中文:
定理 tendstoLocallyUniformlyOn_TFAE
  结论: [LocallyCompactSpace α] (G : ι -> α -> β) (g : α -> β)
  证明: by
  tfae_have 1 -> 2
  | h, K, hK1, hK2 =>
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK2).mp (h.mono hK1)
  tfae_have 2 -> 3
  | h, x, hx => by
    obtain ⟨K, ⟨hK1, hK2⟩, hK3⟩ := (compact_basis_nhds x).mem_iff.mp (hs.mem_nhds hx)
    exact ⟨K, nhdsWithin_le_nhds hK1, h K hK3 

Depends on / 依赖: compact_basis_nhds, h.mono, hs.mem_nhds, mem_iff, mem_iff.mp, mem_nhds, nhdsWithin_le_nhds, tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact, tfae_finish, tfae_have
-/
theorem tendstoLocallyUniformlyOn_TFAE [LocallyCompactSpace α] (G : ι -> α -> β) (g : α -> β)
    (p : Filter ι) (hs : IsOpen s) :
    List.TFAE [
      TendstoLocallyUniformlyOn G g p s,
      forall K, K subseteq s -> IsCompact K -> TendstoUniformlyOn G g p K,
      forall x in s, exists v in 𝓝[s] x, TendstoUniformlyOn G g p v] := by
  tfae_have 1 -> 2
  | h, K, hK1, hK2 =>
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK2).mp (h.mono hK1)
  tfae_have 2 -> 3
  | h, x, hx => by
    obtain ⟨K, ⟨hK1, hK2⟩, hK3⟩ := (compact_basis_nhds x).mem_iff.mp (hs.mem_nhds hx)
    exact ⟨K, nhdsWithin_le_nhds hK1, h K hK3 hK2⟩
  tfae_have 3 -> 1
  | h, u, hu, x, hx => by
    obtain ⟨v, hv1, hv2⟩ := h x hx
    exact ⟨v, hv1, hv2 u hu⟩
  tfae_finish

/--
theorem `tendstoLocallyUniformlyOn_iff_forall_isCompact` / 定理 `tendstoLocallyUniformlyOn_iff_forall_isCompact`

English:
theorem tendstoLocallyUniformlyOn_iff_forall_isCompact
  given: [LocallyCompactSpace α] (hs : IsOpen s)
  proof: (tendstoLocallyUniformlyOn_TFAE F f p hs).out 0 1

中文:
定理 tendstoLocallyUniformlyOn_iff_forall_isCompact
  条件: [LocallyCompactSpace α] (hs : IsOpen s)
  证明: (tendstoLocallyUniformlyOn_TFAE F f p hs).out 0 1

Depends on / 依赖: tendstoLocallyUniformlyOn_TFAE
-/
theorem tendstoLocallyUniformlyOn_iff_forall_isCompact [LocallyCompactSpace α] (hs : IsOpen s) :
    TendstoLocallyUniformlyOn F f p s ↔ forall K, K subseteq s -> IsCompact K -> TendstoUniformlyOn F f p K :=
  (tendstoLocallyUniformlyOn_TFAE F f p hs).out 0 1

/--
lemma `tendstoLocallyUniformly_iff_forall_isCompact` / 引理 `tendstoLocallyUniformly_iff_forall_isCompact`

English:
lemma tendstoLocallyUniformly_iff_forall_isCompact
  given: [LocallyCompactSpace α]
  proof: by
  simp only [← tendstoLocallyUniformlyOn_univ,
    tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ, Set.subset_univ, forall_true_left]

中文:
引理 tendstoLocallyUniformly_iff_forall_isCompact
  条件: [LocallyCompactSpace α]
  证明: by
  simp only [← tendstoLocallyUniformlyOn_univ,
    tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ, Set.subset_univ, forall_true_left]

Depends on / 依赖: Set.subset_univ, forall_true_left, isOpen_univ, subset_univ, tendstoLocallyUniformlyOn_iff_forall_isCompact, tendstoLocallyUniformlyOn_univ
-/
lemma tendstoLocallyUniformly_iff_forall_isCompact [LocallyCompactSpace α] :
    TendstoLocallyUniformly F f p ↔ forall K : Set α, IsCompact K -> TendstoUniformlyOn F f p K := by
  simp only [← tendstoLocallyUniformlyOn_univ,
    tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ, Set.subset_univ, forall_true_left]

/--
theorem `tendstoLocallyUniformlyOn_iff_filter` / 定理 `tendstoLocallyUniformlyOn_iff_filter`

English:
theorem tendstoLocallyUniformlyOn_iff_filter
  proof: by
  simp only [TendstoUniformlyOnFilter, eventually_prod_iff]
  constructor
  · rintro h x hx u hu
    obtain ⟨s, hs1, hs2⟩ := h u hu x hx
    exact ⟨_, hs2, _, eventually_of_mem hs1 fun x => id, fun hi y hy => hi y hy⟩
  · rintro h u hu x hx
    obtain ⟨pa, hpa, pb, hpb, h⟩ := h x hx u hu
    exac

中文:
定理 tendstoLocallyUniformlyOn_iff_filter
  证明: by
  simp only [TendstoUniformlyOnFilter, eventually_prod_iff]
  constructor
  · rintro h x hx u hu
    obtain ⟨s, hs1, hs2⟩ := h u hu x hx
    exact ⟨_, hs2, _, eventually_of_mem hs1 fun x => id, fun hi y hy => hi y hy⟩
  · rintro h u hu x hx
    obtain ⟨pa, hpa, pb, hpb, h⟩ := h x hx u hu
    exac

Depends on / 依赖: TendstoUniformlyOnFilter, eventually_of_mem, eventually_prod_iff
-/
theorem tendstoLocallyUniformlyOn_iff_filter :
    TendstoLocallyUniformlyOn F f p s ↔ forall x in s, TendstoUniformlyOnFilter F f p (𝓝[s] x) := by
  simp only [TendstoUniformlyOnFilter, eventually_prod_iff]
  constructor
  · rintro h x hx u hu
    obtain ⟨s, hs1, hs2⟩ := h u hu x hx
    exact ⟨_, hs2, _, eventually_of_mem hs1 fun x => id, fun hi y hy => hi y hy⟩
  · rintro h u hu x hx
    obtain ⟨pa, hpa, pb, hpb, h⟩ := h x hx u hu
    exact ⟨{a | pb a}, hpb, eventually_of_mem hpa fun i hi y hy => h hi hy⟩

/--
theorem `tendstoLocallyUniformly_iff_filter` / 定理 `tendstoLocallyUniformly_iff_filter`

English:
theorem tendstoLocallyUniformly_iff_filter
  proof: by
  simpa [← tendstoLocallyUniformlyOn_univ, ← nhdsWithin_univ] using
    @tendstoLocallyUniformlyOn_iff_filter _ _ _ _ _ F f univ p

中文:
定理 tendstoLocallyUniformly_iff_filter
  证明: by
  simpa [← tendstoLocallyUniformlyOn_univ, ← nhdsWithin_univ] using
    @tendstoLocallyUniformlyOn_iff_filter _ _ _ _ _ F f univ p

Depends on / 依赖: nhdsWithin_univ, tendstoLocallyUniformlyOn_iff_filter, tendstoLocallyUniformlyOn_univ
-/
theorem tendstoLocallyUniformly_iff_filter :
    TendstoLocallyUniformly F f p ↔ forall x, TendstoUniformlyOnFilter F f p (𝓝 x) := by
  simpa [← tendstoLocallyUniformlyOn_univ, ← nhdsWithin_univ] using
    @tendstoLocallyUniformlyOn_iff_filter _ _ _ _ _ F f univ p

/--
theorem `TendstoLocallyUniformlyOn.tendsto_at` / 定理 `TendstoLocallyUniformlyOn.tendsto_at`

English:
theorem TendstoLocallyUniformlyOn.tendsto_at
  statement: (hf : TendstoLocallyUniformlyOn F f p s) {a : α}
  proof: by
  refine ((tendstoLocallyUniformlyOn_iff_filter.mp hf) a ha).tendsto_at ?_
  simpa only [Filter.principal_singleton] using pure_le_nhdsWithin ha

中文:
定理 TendstoLocallyUniformlyOn.tendsto_at
  结论: (hf : TendstoLocallyUniformlyOn F f p s) {a : α}
  证明: by
  refine ((tendstoLocallyUniformlyOn_iff_filter.mp hf) a ha).tendsto_at ?_
  simpa only [Filter.principal_singleton] using pure_le_nhdsWithin ha

Depends on / 依赖: Filter, Filter.principal_singleton, principal_singleton, pure_le_nhdsWithin, tendstoLocallyUniformlyOn_iff_filter, tendstoLocallyUniformlyOn_iff_filter.mp, tendsto_at
-/
theorem TendstoLocallyUniformlyOn.tendsto_at (hf : TendstoLocallyUniformlyOn F f p s) {a : α}
    (ha : a in s) : Tendsto (fun i => F i a) p (𝓝 (f a)) := by
  refine ((tendstoLocallyUniformlyOn_iff_filter.mp hf) a ha).tendsto_at ?_
  simpa only [Filter.principal_singleton] using pure_le_nhdsWithin ha

/--
theorem `TendstoLocallyUniformlyOn.unique` / 定理 `TendstoLocallyUniformlyOn.unique`

English:
theorem TendstoLocallyUniformlyOn.unique
  statement: [p.NeBot] [T2Space β] {g : α -> β}
  proof: fun _a ha => tendsto_nhds_unique (hf.tendsto_at ha) (hg.tendsto_at ha)

中文:
定理 TendstoLocallyUniformlyOn.unique
  结论: [p.NeBot] [T2Space β] {g : α -> β}
  证明: fun _a ha => tendsto_nhds_unique (hf.tendsto_at ha) (hg.tendsto_at ha)

Depends on / 依赖: hf.tendsto_at, hg.tendsto_at, tendsto_at, tendsto_nhds_unique
-/
theorem TendstoLocallyUniformlyOn.unique [p.NeBot] [T2Space β] {g : α -> β}
    (hf : TendstoLocallyUniformlyOn F f p s) (hg : TendstoLocallyUniformlyOn F g p s) :
    s.EqOn f g := fun _a ha => tendsto_nhds_unique (hf.tendsto_at ha) (hg.tendsto_at ha)

/--
theorem `TendstoLocallyUniformlyOn.congr_inseparable` / 定理 `TendstoLocallyUniformlyOn.congr_inseparable`

English:
theorem TendstoLocallyUniformlyOn.congr_inseparable
  statement: {G : ι -> α -> β}
  proof: by
  have hg : forallᶠ x in p ×ˢ 𝓟 s, Inseparable (F x.1 x.2) (G x.1 x.2) := by
    simpa using eventually_prod_principal_iff.2 hg
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine forall₂_imp (fun x hx hf => ?_) hf
  rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  exact

中文:
定理 TendstoLocallyUniformlyOn.congr_inseparable
  结论: {G : ι -> α -> β}
  证明: by
  have hg : forallᶠ x in p ×ˢ 𝓟 s, Inseparable (F x.1 x.2) (G x.1 x.2) := by
    simpa using eventually_prod_principal_iff.2 hg
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine forall₂_imp (fun x hx hf => ?_) hf
  rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  exact

Depends on / 依赖: Inseparable, Inseparable.rfl.prod, eventually_prod_principal_iff, filter_mono, hg.filter_mono, inf_le_right, mem_open_iff, prod_mono_right, tendstoLocallyUniformlyOn_iff_forall_tendsto, tendsto_right_iff, uniformity_hasBasis_open, uniformity_hasBasis_open.tendsto_right_iff
-/
theorem TendstoLocallyUniformlyOn.congr_inseparable {G : ι -> α -> β}
    (hf : TendstoLocallyUniformlyOn F f p s)
    (hg : forallᶠ n in p, forall x in s, Inseparable (F n x) (G n x)) : TendstoLocallyUniformlyOn G f p s := by
  have hg : forallᶠ x in p ×ˢ 𝓟 s, Inseparable (F x.1 x.2) (G x.1 x.2) := by
    simpa using eventually_prod_principal_iff.2 hg
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine forall₂_imp (fun x hx hf => ?_) hf
  rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  exact fun i hi => (hf i hi).mp ((hg.filter_mono (prod_mono_right p inf_le_right)).mono
    fun x hg hf => ((Inseparable.rfl.prod hg).mem_open_iff hi.2).1 hf)

/--
theorem `TendstoLocallyUniformlyOn.congr` / 定理 `TendstoLocallyUniformlyOn.congr`

English:
theorem TendstoLocallyUniformlyOn.congr
  statement: {G : ι -> α -> β} (hf : TendstoLocallyUniformlyOn F f p s)
  proof: hf.congr_inseparable (.of_forall fun n _ hx => .of_eq (hg n hx))

中文:
定理 TendstoLocallyUniformlyOn.congr
  结论: {G : ι -> α -> β} (hf : TendstoLocallyUniformlyOn F f p s)
  证明: hf.congr_inseparable (.of_forall fun n _ hx => .of_eq (hg n hx))

Depends on / 依赖: congr_inseparable, hf.congr_inseparable, of_eq, of_forall
-/
theorem TendstoLocallyUniformlyOn.congr {G : ι -> α -> β} (hf : TendstoLocallyUniformlyOn F f p s)
    (hg : forall n, s.EqOn (F n) (G n)) : TendstoLocallyUniformlyOn G f p s :=
  hf.congr_inseparable (.of_forall fun n _ hx => .of_eq (hg n hx))

/--
theorem `TendstoLocallyUniformlyOn.congr_inseparable_right` / 定理 `TendstoLocallyUniformlyOn.congr_inseparable_right`

English:
theorem TendstoLocallyUniformlyOn.congr_inseparable_right
  statement: {g : α -> β}
  proof: by
  have hg : forallᶠ x in p ×ˢ 𝓟 s, Inseparable (f x.2) (g x.2) := by
    rw [eventually_prod_principal_iff]
    exact .of_forall fun _ => hg
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine forall₂_imp (fun x hx hf => ?_) hf
  rw [uniformity_hasBasis_open.tendsto_right_iff] at

中文:
定理 TendstoLocallyUniformlyOn.congr_inseparable_right
  结论: {g : α -> β}
  证明: by
  have hg : forallᶠ x in p ×ˢ 𝓟 s, Inseparable (f x.2) (g x.2) := by
    rw [eventually_prod_principal_iff]
    exact .of_forall fun _ => hg
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine forall₂_imp (fun x hx hf => ?_) hf
  rw [uniformity_hasBasis_open.tendsto_right_iff] at

Depends on / 依赖: Inseparable, eventually_prod_principal_iff, filter_mono, hg.filter_mono, hg.prod, inf_le_right, mem_open_iff, of_forall, prod_mono_right, tendstoLocallyUniformlyOn_iff_forall_tendsto, tendsto_right_iff, uniformity_hasBasis_open, uniformity_hasBasis_open.tendsto_right_iff
-/
theorem TendstoLocallyUniformlyOn.congr_inseparable_right {g : α -> β}
    (hf : TendstoLocallyUniformlyOn F f p s)
    (hg : forall x in s, Inseparable (f x) (g x)) : TendstoLocallyUniformlyOn F g p s := by
  have hg : forallᶠ x in p ×ˢ 𝓟 s, Inseparable (f x.2) (g x.2) := by
    rw [eventually_prod_principal_iff]
    exact .of_forall fun _ => hg
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine forall₂_imp (fun x hx hf => ?_) hf
  rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  exact fun i hi => (hf i hi).mp ((hg.filter_mono (prod_mono_right p inf_le_right)).mono
    fun x hg hf => ((hg.prod .rfl).mem_open_iff hi.2).1 hf)

/--
theorem `TendstoLocallyUniformlyOn.congr_right` / 定理 `TendstoLocallyUniformlyOn.congr_right`

English:
theorem TendstoLocallyUniformlyOn.congr_right
  statement: {g : α -> β} (hf : TendstoLocallyUniformlyOn F f p s)
  proof: hf.congr_inseparable_right fun _ hx => .of_eq (hg hx)

中文:
定理 TendstoLocallyUniformlyOn.congr_right
  结论: {g : α -> β} (hf : TendstoLocallyUniformlyOn F f p s)
  证明: hf.congr_inseparable_right fun _ hx => .of_eq (hg hx)

Depends on / 依赖: congr_inseparable_right, hf.congr_inseparable_right, of_eq
-/
theorem TendstoLocallyUniformlyOn.congr_right {g : α -> β} (hf : TendstoLocallyUniformlyOn F f p s)
    (hg : s.EqOn f g) : TendstoLocallyUniformlyOn F g p s :=
  hf.congr_inseparable_right fun _ hx => .of_eq (hg hx)

/--
theorem `TendstoLocallyUniformly.congr_inseparable` / 定理 `TendstoLocallyUniformly.congr_inseparable`

English:
theorem TendstoLocallyUniformly.congr_inseparable
  statement: {G : ι -> α -> β}
  proof: tendstoLocallyUniformlyOn_univ.1
    (hf.tendstoLocallyUniformlyOn.congr_inseparable (by simpa using hg))

中文:
定理 TendstoLocallyUniformly.congr_inseparable
  结论: {G : ι -> α -> β}
  证明: tendstoLocallyUniformlyOn_univ.1
    (hf.tendstoLocallyUniformlyOn.congr_inseparable (by simpa using hg))

Depends on / 依赖: congr_inseparable, hf.tendstoLocallyUniformlyOn.congr_inseparable, tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn_univ
-/
theorem TendstoLocallyUniformly.congr_inseparable {G : ι -> α -> β}
    (hf : TendstoLocallyUniformly F f p)
    (hg : forallᶠ n in p, forall x, Inseparable (F n x) (G n x)) : TendstoLocallyUniformly G f p :=
  tendstoLocallyUniformlyOn_univ.1
    (hf.tendstoLocallyUniformlyOn.congr_inseparable (by simpa using hg))

/--
theorem `TendstoLocallyUniformly.congr` / 定理 `TendstoLocallyUniformly.congr`

English:
theorem TendstoLocallyUniformly.congr
  statement: {G : ι -> α -> β} (hf : TendstoLocallyUniformly F f p)
  proof: hf.congr_inseparable (.of_forall fun n x => .of_eq (hg n x))

中文:
定理 TendstoLocallyUniformly.congr
  结论: {G : ι -> α -> β} (hf : TendstoLocallyUniformly F f p)
  证明: hf.congr_inseparable (.of_forall fun n x => .of_eq (hg n x))

Depends on / 依赖: congr_inseparable, hf.congr_inseparable, of_eq, of_forall
-/
theorem TendstoLocallyUniformly.congr {G : ι -> α -> β} (hf : TendstoLocallyUniformly F f p)
    (hg : forall n x, F n x = G n x) : TendstoLocallyUniformly G f p :=
  hf.congr_inseparable (.of_forall fun n x => .of_eq (hg n x))

/--
theorem `TendstoLocallyUniformly.congr_inseparable_right` / 定理 `TendstoLocallyUniformly.congr_inseparable_right`

English:
theorem TendstoLocallyUniformly.congr_inseparable_right
  statement: {g : α -> β}
  proof: tendstoLocallyUniformlyOn_univ.1
    (hf.tendstoLocallyUniformlyOn.congr_inseparable_right (by simpa using hg))

中文:
定理 TendstoLocallyUniformly.congr_inseparable_right
  结论: {g : α -> β}
  证明: tendstoLocallyUniformlyOn_univ.1
    (hf.tendstoLocallyUniformlyOn.congr_inseparable_right (by simpa using hg))

Depends on / 依赖: congr_inseparable_right, hf.tendstoLocallyUniformlyOn.congr_inseparable_right, tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn_univ
-/
theorem TendstoLocallyUniformly.congr_inseparable_right {g : α -> β}
    (hf : TendstoLocallyUniformly F f p)
    (hg : forall x, Inseparable (f x) (g x)) : TendstoLocallyUniformly F g p :=
  tendstoLocallyUniformlyOn_univ.1
    (hf.tendstoLocallyUniformlyOn.congr_inseparable_right (by simpa using hg))

/--
theorem `TendstoLocallyUniformly.congr_right` / 定理 `TendstoLocallyUniformly.congr_right`

English:
theorem TendstoLocallyUniformly.congr_right
  statement: {g : α -> β} (hf : TendstoLocallyUniformly F f p)
  proof: hf.congr_inseparable_right fun x => .of_eq (hg x)

中文:
定理 TendstoLocallyUniformly.congr_right
  结论: {g : α -> β} (hf : TendstoLocallyUniformly F f p)
  证明: hf.congr_inseparable_right fun x => .of_eq (hg x)

Depends on / 依赖: congr_inseparable_right, hf.congr_inseparable_right, of_eq
-/
theorem TendstoLocallyUniformly.congr_right {g : α -> β} (hf : TendstoLocallyUniformly F f p)
    (hg : forall x, f x = g x) : TendstoLocallyUniformly F g p :=
  hf.congr_inseparable_right fun x => .of_eq (hg x)
