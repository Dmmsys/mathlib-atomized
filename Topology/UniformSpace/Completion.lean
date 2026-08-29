/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Topology.UniformSpace.AbstractCompletion

/-!
# Hausdorff completions of uniform spaces

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `Completion α` and a morphism
(i.e. uniformly continuous map) `(↑) : α → Completion α` which solves the universal
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`.
It means any uniformly continuous `f : α → β` gives rise to a unique morphism
`Completion.extension f : Completion α → β` such that `f = Completion.extension f ∘ (↑)`.
Actually `Completion.extension f` is defined for all maps from `α` to `β` but it has the desired
properties only if `f` is uniformly continuous.

Beware that `(↑)` is not injective if `α` is not Hausdorff. But its image is always
dense. The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, it turns `f : α → β` into a morphism
  `Completion.map f : Completion α → Completion β`
such that
  `(↑) ∘ f = (Completion.map f) ∘ (↑)`
provided `f` is uniformly continuous. This construction is compatible with composition.

In this file we introduce the following concepts:

* `CauchyFilter α` the uniform completion of the uniform space `α` (using Cauchy filters).
  These are not minimal filters.

* `Completion α := Quotient (separationSetoid (CauchyFilter α))` the Hausdorff completion.

## References

This formalization is mostly based on
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
From a slightly different perspective in order to reuse material in `Topology.UniformSpace.Basic`.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped SetRel Uniformity Topology

universe u v w

/--
Definition of `CauchyFilter` / `CauchyFilter` 的定义

English:
definition CauchyFilter
  signature: (α : Type u) [UniformSpace α]
  body: { f : Filter α // Cauchy f }

中文:
定义 CauchyFilter
  签名: (α : 类型u) [一致空间 α]
  定义体: { f : Filter α // Cauchy f }

Depends on / 依赖: Cauchy, Filter
-/
def CauchyFilter (α : Type u) [UniformSpace α] : Type u :=
  { f : Filter α // Cauchy f }

namespace CauchyFilter

section

variable {α : Type u} [UniformSpace α]
variable {β : Type v} {γ : Type w}
variable [UniformSpace β] [UniformSpace γ]

instance (f : CauchyFilter α) : NeBot f.1 := f.2.1

/--
Definition of `gen` / `gen` 的定义

English:
definition gen
  signature: (s : SetRel α α)
  body: { p | s in p.1.val ×ˢ p.2.val }

中文:
定义 gen
  签名: (s : SetRel α α)
  定义体: { p | s in p.1.val ×ˢ p.2.val }
-/
def gen (s : SetRel α α) : SetRel (CauchyFilter α) (CauchyFilter α) :=
  { p | s in p.1.val ×ˢ p.2.val }

/--
theorem `monotone_gen` / 定理 `monotone_gen`

English:
theorem monotone_gen
  statement: Monotone (gen : SetRel α α -> _)
  proof: monotone_ofPred fun p => @Filter.monotone_mem _ (p.1.val ×ˢ p.2.val)

中文:
定理 monotone_gen
  结论: 递增 (gen : SetRel α α -> _)
  证明: monotone_ofPred fun p => @Filter.monotone_mem _ (p.1.val ×ˢ p.2.val)

Depends on / 依赖: Filter, Filter.monotone_mem, monotone_mem, monotone_ofPred
-/
theorem monotone_gen : Monotone (gen : SetRel α α -> _) :=
  monotone_ofPred fun p => @Filter.monotone_mem _ (p.1.val ×ˢ p.2.val)

-- Porting note: this was a calc proof, but I could not make it work
/--
theorem `symm_gen` / 定理 `symm_gen`

English:
theorem symm_gen
  statement: map Prod.swap ((𝓤 α).lift' gen) <= (𝓤 α).lift' gen
  proof: by
  let f := fun s : SetRel α α =>
        { p : CauchyFilter α × CauchyFilter α | s in (p.2.val ×ˢ p.1.val : Filter (α × α)) }
  have h₁ : map Prod.swap ((𝓤 α).lift' gen) = (𝓤 α).lift' f := by
    delta gen
    simp [f, map_lift'_eq, monotone_ofPred, Filter.monotone_mem, Function.comp_def,
      image_swap_eq_preimage_swap]
  have h₂ : (𝓤 α).lift' f <= (𝓤 α).lift' gen :=
    uniformity_lift_le_swap
      (monotone_principal.comp
        (monotone_ofPred fun p => @Filter.monotone_mem _ (p.2.val ×ˢ p.1.val)))
      (by
        have h := fun p : CauchyFilter α × CauchyFilter α => @Filter.prod_comm _ _ p.2.val p.1.val
        simp only [Function.comp, h, mem_map, f]
        exact le_rfl)
  exact h₁.trans_le h₂

中文:
定理 symm_gen
  结论: map 积类型.swap ((𝓤 α).lift' gen) <= (𝓤 α).lift' gen
  证明: by
  let f := fun s : SetRel α α =>
        { p : CauchyFilter α × CauchyFilter α | s in (p.2.val ×ˢ p.1.val : Filter (α × α)) }
  have h₁ : map Prod.swap ((𝓤 α).lift' gen) = (𝓤 α).lift' f := by
    delta gen
    simp [f, map_lift'_eq, monotone_ofPred, Filter.monotone_mem, Function.comp_def,
      image_swap_eq_preimage_swap]
  have h₂ : (𝓤 α).lift' f <= (𝓤 α).lift' gen :=
    uniformity_lift_le_swap
      (monotone_principal.comp
        (monotone_ofPred fun p => @Filter.monotone_mem _ (p.2.val ×ˢ p.1.val)))
      (by
        have h := fun p : CauchyFilter α × CauchyFilter α => @Filter.prod_comm _ _ p.2.val p.1.val
        simp only [Function.comp, h, mem_map, f]
        exact le_rfl)
  exact h₁.trans_le h₂
-/
private theorem symm_gen : map Prod.swap ((𝓤 α).lift' gen) <= (𝓤 α).lift' gen := by
  let f := fun s : SetRel α α =>
        { p : CauchyFilter α × CauchyFilter α | s in (p.2.val ×ˢ p.1.val : Filter (α × α)) }
  have h₁ : map Prod.swap ((𝓤 α).lift' gen) = (𝓤 α).lift' f := by
    delta gen
    simp [f, map_lift'_eq, monotone_ofPred, Filter.monotone_mem, Function.comp_def,
      image_swap_eq_preimage_swap]
  have h₂ : (𝓤 α).lift' f <= (𝓤 α).lift' gen :=
    uniformity_lift_le_swap
      (monotone_principal.comp
        (monotone_ofPred fun p => @Filter.monotone_mem _ (p.2.val ×ˢ p.1.val)))
      (by
        have h := fun p : CauchyFilter α × CauchyFilter α => @Filter.prod_comm _ _ p.2.val p.1.val
        simp only [Function.comp, h, mem_map, f]
        exact le_rfl)
  exact h₁.trans_le h₂

/--
theorem `subset_gen_relComp` / 定理 `subset_gen_relComp`

English:
theorem subset_gen_relComp
  given: {s t : SetRel α α}
  statement: gen s ○ gen t subseteq gen (s ○ t)
  proof: fun ⟨f, g⟩ ⟨h, h₁, h₂⟩ =>
  let ⟨t₁, (ht₁ : t₁ in f.val), t₂, (ht₂ : t₂ in h.val), (h₁ : t₁ ×ˢ t₂ subseteq s)⟩ := mem_prod_iff.mp h₁
  let ⟨t₃, (ht₃ : t₃ in h.val), t₄, (ht₄ : t₄ in g.val), (h₂ : t₃ ×ˢ t₄ subseteq t)⟩ := mem_prod_iff.mp h₂
  have : t₂ inter t₃ in h.val := inter_mem ht₂ ht₃
  let ⟨x, xt₂, xt₃⟩ := h.property.left.nonempty_of_mem this
  (f.val ×ˢ g.val).sets_of_superset (prod_mem_prod ht₁ ht₄)
    fun ⟨a, b⟩ ⟨(ha : a in t₁), (hb : b in t₄)⟩ =>
    ⟨x, h₁ (show (a, x) in t₁ ×ˢ t₂ from ⟨ha, xt₂⟩), h₂ (show (x, b) in t₃ ×ˢ t₄ from ⟨xt₃, hb⟩)⟩

中文:
定理 subset_gen_relComp
  条件: {s t : SetRel α α}
  结论: gen s ○ gen t subseteq gen (s ○ t)
  证明: fun ⟨f, g⟩ ⟨h, h₁, h₂⟩ =>
  let ⟨t₁, (ht₁ : t₁ in f.val), t₂, (ht₂ : t₂ in h.val), (h₁ : t₁ ×ˢ t₂ subseteq s)⟩ := mem_prod_iff.mp h₁
  let ⟨t₃, (ht₃ : t₃ in h.val), t₄, (ht₄ : t₄ in g.val), (h₂ : t₃ ×ˢ t₄ subseteq t)⟩ := mem_prod_iff.mp h₂
  have : t₂ inter t₃ in h.val := inter_mem ht₂ ht₃
  let ⟨x, xt₂, xt₃⟩ := h.property.left.nonempty_of_mem this
  (f.val ×ˢ g.val).sets_of_superset (prod_mem_prod ht₁ ht₄)
    fun ⟨a, b⟩ ⟨(ha : a in t₁), (hb : b in t₄)⟩ =>
    ⟨x, h₁ (show (a, x) in t₁ ×ˢ t₂ from ⟨ha, xt₂⟩), h₂ (show (x, b) in t₃ ×ˢ t₄ from ⟨xt₃, hb⟩)⟩
-/
private theorem subset_gen_relComp {s t : SetRel α α} : gen s ○ gen t subseteq gen (s ○ t) :=
  fun ⟨f, g⟩ ⟨h, h₁, h₂⟩ =>
  let ⟨t₁, (ht₁ : t₁ in f.val), t₂, (ht₂ : t₂ in h.val), (h₁ : t₁ ×ˢ t₂ subseteq s)⟩ := mem_prod_iff.mp h₁
  let ⟨t₃, (ht₃ : t₃ in h.val), t₄, (ht₄ : t₄ in g.val), (h₂ : t₃ ×ˢ t₄ subseteq t)⟩ := mem_prod_iff.mp h₂
  have : t₂ inter t₃ in h.val := inter_mem ht₂ ht₃
  let ⟨x, xt₂, xt₃⟩ := h.property.left.nonempty_of_mem this
  (f.val ×ˢ g.val).sets_of_superset (prod_mem_prod ht₁ ht₄)
    fun ⟨a, b⟩ ⟨(ha : a in t₁), (hb : b in t₄)⟩ =>
    ⟨x, h₁ (show (a, x) in t₁ ×ˢ t₂ from ⟨ha, xt₂⟩), h₂ (show (x, b) in t₃ ×ˢ t₄ from ⟨xt₃, hb⟩)⟩

/--
theorem `comp_gen` / 定理 `comp_gen`

English:
theorem comp_gen
  statement: ((𝓤 α).lift' gen).lift' (fun s => s ○ s) <= (𝓤 α).lift' gen
  proof: calc
        ((𝓤 α).lift' gen).lift' (fun s => s ○ s)
    _ = (𝓤 α).lift' fun s => gen s ○ gen s := by
      rw [lift'_lift'_assoc]
      · exact monotone_gen
      · exact monotone_id.relComp monotone_id
_ <= (𝓤 α).lift' fun s => gen s ○ s := lift'_mono' fun _ _hs => subset_gen_relComp
    _ = ((𝓤 α).lift' fun s : SetRel α α => s ○ s).lift' gen := by
      rw [lift'_lift'_assoc]
      · exact monotone_id.relComp monotone_id
      · exact monotone_gen
    _ <= (𝓤 α).lift' gen := lift'_mono comp_le_uniformity le_rfl

中文:
定理 comp_gen
  结论: ((𝓤 α).lift' gen).lift' (fun s => s ○ s) <= (𝓤 α).lift' gen
  证明: calc
        ((𝓤 α).lift' gen).lift' (fun s => s ○ s)
    _ = (𝓤 α).lift' fun s => gen s ○ gen s := by
      rw [lift'_lift'_assoc]
      · exact monotone_gen
      · exact monotone_id.relComp monotone_id
_ <= (𝓤 α).lift' fun s => gen s ○ s := lift'_mono' fun _ _hs => subset_gen_relComp
    _ = ((𝓤 α).lift' fun s : SetRel α α => s ○ s).lift' gen := by
      rw [lift'_lift'_assoc]
      · exact monotone_id.relComp monotone_id
      · exact monotone_gen
    _ <= (𝓤 α).lift' gen := lift'_mono comp_le_uniformity le_rfl
-/
private theorem comp_gen : ((𝓤 α).lift' gen).lift' (fun s => s ○ s) <= (𝓤 α).lift' gen :=
  calc
        ((𝓤 α).lift' gen).lift' (fun s => s ○ s)
    _ = (𝓤 α).lift' fun s => gen s ○ gen s := by
      rw [lift'_lift'_assoc]
      · exact monotone_gen
      · exact monotone_id.relComp monotone_id
_ <= (𝓤 α).lift' fun s => gen s ○ s := lift'_mono' fun _ _hs => subset_gen_relComp
    _ = ((𝓤 α).lift' fun s : SetRel α α => s ○ s).lift' gen := by
      rw [lift'_lift'_assoc]
      · exact monotone_id.relComp monotone_id
      · exact monotone_gen
    _ <= (𝓤 α).lift' gen := lift'_mono comp_le_uniformity le_rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace (CauchyFilter α)
  body: UniformSpace.ofCore
    { uniformity := (𝓤 α).lift' gen
      refl := principal_le_lift'.2 fun _s hs ⟨a, b⟩ =>
        fun (a_eq_b : a = b) => a_eq_b ▸ a.property.right hs
      symm := by exact symm_gen
      comp := by exact comp_gen }

中文:
实例 :
  签名: 一致空间 (CauchyFilter α)
  定义体: UniformSpace.ofCore
    { uniformity := (𝓤 α).lift' gen
      refl := principal_le_lift'.2 fun _s hs ⟨a, b⟩ =>
        fun (a_eq_b : a = b) => a_eq_b ▸ a.property.right hs
      symm := by exact symm_gen
      comp := by exact comp_gen }

Depends on / 依赖: UniformSpace, UniformSpace.ofCore, a.property.right, a_eq_b, comp_gen, ofCore, principal_le_lift, property, symm_gen, uniformity
-/
instance : UniformSpace (CauchyFilter α) :=
  UniformSpace.ofCore
    { uniformity := (𝓤 α).lift' gen
      refl := principal_le_lift'.2 fun _s hs ⟨a, b⟩ =>
        fun (a_eq_b : a = b) => a_eq_b ▸ a.property.right hs
      symm := by exact symm_gen
      comp := by exact comp_gen }

/--
theorem `mem_uniformity` / 定理 `mem_uniformity`

English:
theorem mem_uniformity
  given: {s : Set (CauchyFilter α × CauchyFilter α)}
  proof: mem_lift'_sets monotone_gen

中文:
定理 mem_uniformity
  条件: {s : 集合 (CauchyFilter α × CauchyFilter α)}
  证明: mem_lift'_sets monotone_gen

Depends on / 依赖: _sets, mem_lift, monotone_gen
-/
theorem mem_uniformity {s : Set (CauchyFilter α × CauchyFilter α)} :
    s in 𝓤 (CauchyFilter α) ↔ exists t in 𝓤 α, gen t subseteq s :=
  mem_lift'_sets monotone_gen

/--
theorem `basis_uniformity` / 定理 `basis_uniformity`

English:
theorem basis_uniformity
  given: {ι : Sort*} {p : ι -> Prop} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s)
  proof: h.lift' monotone_gen

中文:
定理 basis_uniformity
  条件: {ι : 类型层*} {p : ι -> 命题} {s : ι -> SetRel α α} (h : (𝓤 α).有基 p s)
  证明: h.lift' monotone_gen

Depends on / 依赖: h.lift, monotone_gen
-/
theorem basis_uniformity {ι : Sort*} {p : ι -> Prop} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (CauchyFilter α)).HasBasis p (gen ∘ s) :=
  h.lift' monotone_gen

/--
theorem `mem_uniformity'` / 定理 `mem_uniformity'`

English:
theorem mem_uniformity'
  given: {s : Set (CauchyFilter α × CauchyFilter α)}
  proof: by
  refine mem_uniformity.trans (exists_congr (fun t => and_congr_right_iff.mpr (fun _h => ?_)))
  exact ⟨fun h _f _g ht => h ht, fun h _p hp => h _ _ hp⟩

中文:
定理 mem_uniformity'
  条件: {s : 集合 (CauchyFilter α × CauchyFilter α)}
  证明: by
  refine mem_uniformity.trans (exists_congr (fun t => and_congr_right_iff.mpr (fun _h => ?_)))
  exact ⟨fun h _f _g ht => h ht, fun h _p hp => h _ _ hp⟩

Depends on / 依赖: and_congr_right_iff, and_congr_right_iff.mpr, exists_congr, mem_uniformity, mem_uniformity.trans
-/
theorem mem_uniformity' {s : Set (CauchyFilter α × CauchyFilter α)} :
    s in 𝓤 (CauchyFilter α) ↔ exists t in 𝓤 α, forall f g : CauchyFilter α, t in f.1 ×ˢ g.1 -> (f, g) in s := by
  refine mem_uniformity.trans (exists_congr (fun t => and_congr_right_iff.mpr (fun _h => ?_)))
  exact ⟨fun h _f _g ht => h ht, fun h _p hp => h _ _ hp⟩

/--
Definition of `pureCauchy` / `pureCauchy` 的定义

English:
definition pureCauchy
  signature: (a : α)
  body: ⟨pure a, cauchy_pure⟩

中文:
定义 pureCauchy
  签名: (a : α)
  定义体: ⟨pure a, cauchy_pure⟩

Depends on / 依赖: cauchy_pure
-/
def pureCauchy (a : α) : CauchyFilter α :=
  ⟨pure a, cauchy_pure⟩

/--
theorem `isUniformInducing_pureCauchy` / 定理 `isUniformInducing_pureCauchy`

English:
theorem isUniformInducing_pureCauchy
  statement: IsUniformInducing (pureCauchy : α -> CauchyFilter α)
  proof: ⟨have : (preimage fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ∘ gen = id :=
      funext fun s =>
        Set.ext fun ⟨a₁, a₂⟩ => by simp [preimage, gen, pureCauchy]
    calc
      comap (fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ((𝓤 α).lift' gen) =
          (𝓤 α).lift' ((preimage fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ∘ gen) :=
        comap_lift'_eq
      _ = 𝓤 α := by simp [this]
      ⟩

中文:
定理 isUniformInducing_pureCauchy
  结论: 是UniformInducing (pureCauchy : α -> CauchyFilter α)
  证明: ⟨have : (preimage fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ∘ gen = id :=
      funext fun s =>
        Set.ext fun ⟨a₁, a₂⟩ => by simp [preimage, gen, pureCauchy]
    calc
      comap (fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ((𝓤 α).lift' gen) =
          (𝓤 α).lift' ((preimage fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ∘ gen) :=
        comap_lift'_eq
      _ = 𝓤 α := by simp [this]
      ⟩

Depends on / 依赖: Set.ext, comap_lift, preimage, pureCauchy, x.fst, x.snd
-/
theorem isUniformInducing_pureCauchy : IsUniformInducing (pureCauchy : α -> CauchyFilter α) :=
  ⟨have : (preimage fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ∘ gen = id :=
      funext fun s =>
        Set.ext fun ⟨a₁, a₂⟩ => by simp [preimage, gen, pureCauchy]
    calc
      comap (fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ((𝓤 α).lift' gen) =
          (𝓤 α).lift' ((preimage fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ∘ gen) :=
        comap_lift'_eq
      _ = 𝓤 α := by simp [this]
      ⟩

/--
theorem `isUniformEmbedding_pureCauchy` / 定理 `isUniformEmbedding_pureCauchy`

English:
theorem isUniformEmbedding_pureCauchy
  statement: IsUniformEmbedding (pureCauchy : α -> CauchyFilter α) where
  proof: isUniformInducing_pureCauchy
injective _a₁ _a₂ h := pure_injective Subtype.ext_iff.1 h

中文:
定理 isUniformEmbedding_pureCauchy
  结论: 是一致嵌入 (pureCauchy : α -> CauchyFilter α) where
  证明: isUniformInducing_pureCauchy
injective _a₁ _a₂ h := pure_injective Subtype.ext_iff.1 h

Depends on / 依赖: isUniformInducing_pureCauchy
-/
theorem isUniformEmbedding_pureCauchy : IsUniformEmbedding (pureCauchy : α -> CauchyFilter α) where
  __ := isUniformInducing_pureCauchy
injective _a₁ _a₂ h := pure_injective Subtype.ext_iff.1 h

/--
theorem `denseRange_pureCauchy` / 定理 `denseRange_pureCauchy`

English:
theorem denseRange_pureCauchy
  statement: DenseRange (pureCauchy : α -> CauchyFilter α)
  proof: fun f => by
  have h_ex : forall s in 𝓤 (CauchyFilter α), exists y : α, (f, pureCauchy y) in s := fun s hs =>
    let ⟨t'', ht''₁, (ht''₂ : gen t'' subseteq s)⟩ := (mem_lift'_sets monotone_gen).mp hs
    let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁
    have : t' in f.val ×ˢ f.val := f.property.right ht'₁
    let ⟨t, ht, (h : t ×ˢ t subseteq t')⟩ := mem_prod_same_iff.mp this
    let ⟨x, (hx : x in t)⟩ := f.property.left.nonempty_of_mem ht
    have : t'' in f.val ×ˢ pure x :=
      mem_prod_iff.mpr
⟨t, ht, { y : α | (x, y) in t' }, h mk_mem_prod hx hx,
          fun ⟨a, b⟩ ⟨(h₁ : a in t), (h₂ : (x, b) in t')⟩ =>
ht'₂ SetRel.prodMk_mem_comp (@h (a, x) ⟨h₁, hx⟩) h₂⟩
⟨x, ht''₂ by dsimp [gen]; exact this⟩
  simp only [closure_eq_cluster_pts, ClusterPt, nhds_eq_uniformity, lift'_inf_principal_eq,
    Set.inter_comm _ (range pureCauchy), mem_ofPred_eq]
  refine (lift'_neBot_iff ?_).mpr (fun s hs => ?_)
  · exact monotone_const.inter monotone_preimage
  · let ⟨y, hy⟩ := h_ex s hs
    have : pureCauchy y in range pureCauchy inter { y : CauchyFilter α | (f, y) in s } :=
      ⟨mem_range_self y, hy⟩
    exact ⟨_, this⟩

中文:
定理 denseRange_pureCauchy
  结论: DenseRange (pureCauchy : α -> CauchyFilter α)
  证明: fun f => by
  have h_ex : forall s in 𝓤 (CauchyFilter α), exists y : α, (f, pureCauchy y) in s := fun s hs =>
    let ⟨t'', ht''₁, (ht''₂ : gen t'' subseteq s)⟩ := (mem_lift'_sets monotone_gen).mp hs
    let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁
    have : t' in f.val ×ˢ f.val := f.property.right ht'₁
    let ⟨t, ht, (h : t ×ˢ t subseteq t')⟩ := mem_prod_same_iff.mp this
    let ⟨x, (hx : x in t)⟩ := f.property.left.nonempty_of_mem ht
    have : t'' in f.val ×ˢ pure x :=
      mem_prod_iff.mpr
⟨t, ht, { y : α | (x, y) in t' }, h mk_mem_prod hx hx,
          fun ⟨a, b⟩ ⟨(h₁ : a in t), (h₂ : (x, b) in t')⟩ =>
ht'₂ SetRel.prodMk_mem_comp (@h (a, x) ⟨h₁, hx⟩) h₂⟩
⟨x, ht''₂ by dsimp [gen]; exact this⟩
  simp only [closure_eq_cluster_pts, ClusterPt, nhds_eq_uniformity, lift'_inf_principal_eq,
    Set.inter_comm _ (range pureCauchy), mem_ofPred_eq]
  refine (lift'_neBot_iff ?_).mpr (fun s hs => ?_)
  · exact monotone_const.inter monotone_preimage
  · let ⟨y, hy⟩ := h_ex s hs
    have : pureCauchy y in range pureCauchy inter { y : CauchyFilter α | (f, y) in s } :=
      ⟨mem_range_self y, hy⟩
    exact ⟨_, this⟩

Depends on / 依赖: CauchyFilter, _sets, comp_mem_uniformity_sets, f.property.left.nonempty_of_mem, f.property.right, f.val, h_ex, mem_lift, mem_prod_iff, mem_prod_iff.mpr, mem_prod_same_iff, mem_prod_same_iff.mp, monotone_gen, nonempty_of_mem, property, pureCauchy, subseteq
-/
theorem denseRange_pureCauchy : DenseRange (pureCauchy : α -> CauchyFilter α) := fun f => by
  have h_ex : forall s in 𝓤 (CauchyFilter α), exists y : α, (f, pureCauchy y) in s := fun s hs =>
    let ⟨t'', ht''₁, (ht''₂ : gen t'' subseteq s)⟩ := (mem_lift'_sets monotone_gen).mp hs
    let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁
    have : t' in f.val ×ˢ f.val := f.property.right ht'₁
    let ⟨t, ht, (h : t ×ˢ t subseteq t')⟩ := mem_prod_same_iff.mp this
    let ⟨x, (hx : x in t)⟩ := f.property.left.nonempty_of_mem ht
    have : t'' in f.val ×ˢ pure x :=
      mem_prod_iff.mpr
⟨t, ht, { y : α | (x, y) in t' }, h mk_mem_prod hx hx,
          fun ⟨a, b⟩ ⟨(h₁ : a in t), (h₂ : (x, b) in t')⟩ =>
ht'₂ SetRel.prodMk_mem_comp (@h (a, x) ⟨h₁, hx⟩) h₂⟩
⟨x, ht''₂ by dsimp [gen]; exact this⟩
  simp only [closure_eq_cluster_pts, ClusterPt, nhds_eq_uniformity, lift'_inf_principal_eq,
    Set.inter_comm _ (range pureCauchy), mem_ofPred_eq]
  refine (lift'_neBot_iff ?_).mpr (fun s hs => ?_)
  · exact monotone_const.inter monotone_preimage
  · let ⟨y, hy⟩ := h_ex s hs
    have : pureCauchy y in range pureCauchy inter { y : CauchyFilter α | (f, y) in s } :=
      ⟨mem_range_self y, hy⟩
    exact ⟨_, this⟩

/--
theorem `isDenseInducing_pureCauchy` / 定理 `isDenseInducing_pureCauchy`

English:
theorem isDenseInducing_pureCauchy
  statement: IsDenseInducing (pureCauchy : α -> CauchyFilter α)
  proof: isUniformInducing_pureCauchy.isDenseInducing denseRange_pureCauchy

中文:
定理 isDenseInducing_pureCauchy
  结论: 是DenseInducing (pureCauchy : α -> CauchyFilter α)
  证明: isUniformInducing_pureCauchy.isDenseInducing denseRange_pureCauchy

Depends on / 依赖: denseRange_pureCauchy, isDenseInducing, isUniformInducing_pureCauchy, isUniformInducing_pureCauchy.isDenseInducing
-/
theorem isDenseInducing_pureCauchy : IsDenseInducing (pureCauchy : α -> CauchyFilter α) :=
  isUniformInducing_pureCauchy.isDenseInducing denseRange_pureCauchy

/--
theorem `isDenseEmbedding_pureCauchy` / 定理 `isDenseEmbedding_pureCauchy`

English:
theorem isDenseEmbedding_pureCauchy
  statement: IsDenseEmbedding (pureCauchy : α -> CauchyFilter α)
  proof: isUniformEmbedding_pureCauchy.isDenseEmbedding denseRange_pureCauchy

中文:
定理 isDenseEmbedding_pureCauchy
  结论: 是稠密嵌入 (pureCauchy : α -> CauchyFilter α)
  证明: isUniformEmbedding_pureCauchy.isDenseEmbedding denseRange_pureCauchy

Depends on / 依赖: denseRange_pureCauchy, isDenseEmbedding, isUniformEmbedding_pureCauchy, isUniformEmbedding_pureCauchy.isDenseEmbedding
-/
theorem isDenseEmbedding_pureCauchy : IsDenseEmbedding (pureCauchy : α -> CauchyFilter α) :=
  isUniformEmbedding_pureCauchy.isDenseEmbedding denseRange_pureCauchy

/--
theorem `nonempty_cauchyFilter_iff` / 定理 `nonempty_cauchyFilter_iff`

English:
theorem nonempty_cauchyFilter_iff
  statement: Nonempty (CauchyFilter α) ↔ Nonempty α
  proof: by
  constructor <;> rintro ⟨c⟩
  · have := eq_univ_iff_forall.1 isDenseEmbedding_pureCauchy.isDenseInducing.closure_range c
    obtain ⟨_, ⟨_, a, _⟩⟩ := mem_closure_iff.1 this _ isOpen_univ trivial
    exact ⟨a⟩
  · exact ⟨pureCauchy c⟩

中文:
定理 nonempty_cauchyFilter_iff
  结论: 非空 (CauchyFilter α) ↔ 非空 α
  证明: by
  constructor <;> rintro ⟨c⟩
  · have := eq_univ_iff_forall.1 isDenseEmbedding_pureCauchy.isDenseInducing.closure_range c
    obtain ⟨_, ⟨_, a, _⟩⟩ := mem_closure_iff.1 this _ isOpen_univ trivial
    exact ⟨a⟩
  · exact ⟨pureCauchy c⟩

Depends on / 依赖: closure_range, eq_univ_iff_forall, isDenseEmbedding_pureCauchy, isDenseEmbedding_pureCauchy.isDenseInducing.closure_range, isDenseInducing, isOpen_univ, mem_closure_iff, pureCauchy
-/
theorem nonempty_cauchyFilter_iff : Nonempty (CauchyFilter α) ↔ Nonempty α := by
  constructor <;> rintro ⟨c⟩
  · have := eq_univ_iff_forall.1 isDenseEmbedding_pureCauchy.isDenseInducing.closure_range c
    obtain ⟨_, ⟨_, a, _⟩⟩ := mem_closure_iff.1 this _ isOpen_univ trivial
    exact ⟨a⟩
  · exact ⟨pureCauchy c⟩

section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSpace (CauchyFilter α)
  body: completeSpace_extension isUniformInducing_pureCauchy denseRange_pureCauchy fun f hf =>
    let f' : CauchyFilter α := ⟨f, hf⟩
    have : map pureCauchy f <= (𝓤 <| CauchyFilter α).lift' (preimage (Prod.mk f')) :=
      le_lift'.2 fun _ hs =>
        let ⟨t, ht₁, ht₂⟩ := (mem_lift'_sets monotone_gen).mp hs
        let ⟨t', ht', (h : t' ×ˢ t' subseteq t)⟩ := mem_prod_same_iff.mp (hf.right ht₁)
        have : t' subseteq { y : α | (f', pureCauchy y) in gen t } := fun x hx =>
          (f ×ˢ pure x).sets_of_superset (prod_mem_prod ht' hx) h
f.sets_of_superset ht' Subset.trans this (preimage_mono ht₂)
    ⟨f', by simpa [nhds_eq_uniformity]⟩

中文:
实例 :
  签名: 完备空间 (CauchyFilter α)
  定义体: completeSpace_extension isUniformInducing_pureCauchy denseRange_pureCauchy fun f hf =>
    let f' : CauchyFilter α := ⟨f, hf⟩
    have : map pureCauchy f <= (𝓤 <| CauchyFilter α).lift' (preimage (Prod.mk f')) :=
      le_lift'.2 fun _ hs =>
        let ⟨t, ht₁, ht₂⟩ := (mem_lift'_sets monotone_gen).mp hs
        let ⟨t', ht', (h : t' ×ˢ t' subseteq t)⟩ := mem_prod_same_iff.mp (hf.right ht₁)
        have : t' subseteq { y : α | (f', pureCauchy y) in gen t } := fun x hx =>
          (f ×ˢ pure x).sets_of_superset (prod_mem_prod ht' hx) h
f.sets_of_superset ht' Subset.trans this (preimage_mono ht₂)
    ⟨f', by simpa [nhds_eq_uniformity]⟩

Depends on / 依赖: CauchyFilter, Prod.mk, _sets, completeSpace_extension, denseRange_pureCauchy, f.sets, hf.right, isUniformInducing_pureCauchy, le_lift, mem_lift, mem_prod_same_iff, mem_prod_same_iff.mp, monotone_gen, preimage, prod_mem_prod, pureCauchy, sets_of_superset, subseteq
-/
instance : CompleteSpace (CauchyFilter α) :=
  completeSpace_extension isUniformInducing_pureCauchy denseRange_pureCauchy fun f hf =>
    let f' : CauchyFilter α := ⟨f, hf⟩
    have : map pureCauchy f <= (𝓤 <| CauchyFilter α).lift' (preimage (Prod.mk f')) :=
      le_lift'.2 fun _ hs =>
        let ⟨t, ht₁, ht₂⟩ := (mem_lift'_sets monotone_gen).mp hs
        let ⟨t', ht', (h : t' ×ˢ t' subseteq t)⟩ := mem_prod_same_iff.mp (hf.right ht₁)
        have : t' subseteq { y : α | (f', pureCauchy y) in gen t } := fun x hx =>
          (f ×ˢ pure x).sets_of_superset (prod_mem_prod ht' hx) h
f.sets_of_superset ht' Subset.trans this (preimage_mono ht₂)
    ⟨f', by simpa [nhds_eq_uniformity]⟩

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (CauchyFilter α)
  body: ⟨pureCauchy default⟩

中文:
实例 [可居
  签名: α] : 可居 (CauchyFilter α)
  定义体: ⟨pureCauchy default⟩

Depends on / 依赖: pureCauchy
-/
instance [Inhabited α] : Inhabited (CauchyFilter α) :=
  ⟨pureCauchy default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Nonempty α] : Nonempty (CauchyFilter α)
  body: h.recOn fun a => Nonempty.intro CauchyFilter.pureCauchy a

中文:
实例 [h
  签名: : 非空 α] : 非空 (CauchyFilter α)
  定义体: h.recOn fun a => Nonempty.intro CauchyFilter.pureCauchy a

Depends on / 依赖: CauchyFilter, CauchyFilter.pureCauchy, Nonempty, Nonempty.intro, h.recOn, pureCauchy
-/
instance [h : Nonempty α] : Nonempty (CauchyFilter α) :=
h.recOn fun a => Nonempty.intro CauchyFilter.pureCauchy a

section Extend

open scoped Classical in
/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (f : α -> β)
  body: if UniformContinuous f then isDenseInducing_pureCauchy.extend f
  else fun x => f (nonempty_cauchyFilter_iff.1 ⟨x⟩).some

中文:
定义 extend
  签名: (f : α -> β)
  定义体: if UniformContinuous f then isDenseInducing_pureCauchy.extend f
  else fun x => f (nonempty_cauchyFilter_iff.1 ⟨x⟩).some

Depends on / 依赖: UniformContinuous, extend, isDenseInducing_pureCauchy, isDenseInducing_pureCauchy.extend, nonempty_cauchyFilter_iff
-/
def extend (f : α -> β) : CauchyFilter α -> β :=
  if UniformContinuous f then isDenseInducing_pureCauchy.extend f
  else fun x => f (nonempty_cauchyFilter_iff.1 ⟨x⟩).some

section T0Space

variable [T0Space β]

/--
theorem `extend_pureCauchy` / 定理 `extend_pureCauchy`

English:
theorem extend_pureCauchy
  given: {f : α -> β} (hf : UniformContinuous f) (a : α)
  proof: by
  rw [extend]; rw [if_pos hf]
  exact uniformly_extend_of_ind isUniformInducing_pureCauchy denseRange_pureCauchy hf _

中文:
定理 extend_pureCauchy
  条件: {f : α -> β} (hf : 一致连续 f) (a : α)
  证明: by
  rw [extend]; rw [if_pos hf]
  exact uniformly_extend_of_ind isUniformInducing_pureCauchy denseRange_pureCauchy hf _

Depends on / 依赖: denseRange_pureCauchy, extend, if_pos, isUniformInducing_pureCauchy, uniformly_extend_of_ind
-/
theorem extend_pureCauchy {f : α -> β} (hf : UniformContinuous f) (a : α) :
    extend f (pureCauchy a) = f a := by
  rw [extend]; rw [if_pos hf]
  exact uniformly_extend_of_ind isUniformInducing_pureCauchy denseRange_pureCauchy hf _

end T0Space

variable [CompleteSpace β]

@[fun_prop]
/--
theorem `uniformContinuous_extend` / 定理 `uniformContinuous_extend`

English:
theorem uniformContinuous_extend
  given: {f : α -> β}
  statement: UniformContinuous (extend f)
  proof: by
  by_cases hf : UniformContinuous f
  · rw [extend, if_pos hf]
    exact uniformContinuous_uniformly_extend isUniformInducing_pureCauchy denseRange_pureCauchy hf
  · rw [extend, if_neg hf]
    exact uniformContinuous_of_const fun a _b => by congr

中文:
定理 uniformContinuous_extend
  条件: {f : α -> β}
  结论: 一致连续 (extend f)
  证明: by
  by_cases hf : UniformContinuous f
  · rw [extend, if_pos hf]
    exact uniformContinuous_uniformly_extend isUniformInducing_pureCauchy denseRange_pureCauchy hf
  · rw [extend, if_neg hf]
    exact uniformContinuous_of_const fun a _b => by congr

Depends on / 依赖: UniformContinuous, denseRange_pureCauchy, extend, if_neg, if_pos, isUniformInducing_pureCauchy, uniformContinuous_of_const, uniformContinuous_uniformly_extend
-/
theorem uniformContinuous_extend {f : α -> β} : UniformContinuous (extend f) := by
  by_cases hf : UniformContinuous f
  · rw [extend, if_pos hf]
    exact uniformContinuous_uniformly_extend isUniformInducing_pureCauchy denseRange_pureCauchy hf
  · rw [extend, if_neg hf]
    exact uniformContinuous_of_const fun a _b => by congr

end Extend

/--
theorem `inseparable_iff` / 定理 `inseparable_iff`

English:
theorem inseparable_iff
  given: {f g : CauchyFilter α}
  statement: Inseparable f g ↔ f.1 ×ˢ g.1 <= 𝓤 α
  proof: (basis_uniformity (basis_sets _)).inseparable_iff_uniformity

中文:
定理 inseparable_iff
  条件: {f g : CauchyFilter α}
  结论: 不可分 f g ↔ f.1 ×ˢ g.1 <= 𝓤 α
  证明: (basis_uniformity (basis_sets _)).inseparable_iff_uniformity

Depends on / 依赖: basis_sets, basis_uniformity, inseparable_iff_uniformity
-/
theorem inseparable_iff {f g : CauchyFilter α} : Inseparable f g ↔ f.1 ×ˢ g.1 <= 𝓤 α :=
  (basis_uniformity (basis_sets _)).inseparable_iff_uniformity

/--
theorem `inseparable_iff_of_le_nhds` / 定理 `inseparable_iff_of_le_nhds`

English:
theorem inseparable_iff_of_le_nhds
  statement: {f g : CauchyFilter α} {a b : α}
  proof: by
  rw [← tendsto_id'] at ha hb
  rw [inseparable_iff]; rw [(ha.comp tendsto_fst).inseparable_iff_uniformity (hb.comp tendsto_snd)]
  simp only [Function.comp_apply, id_eq, Prod.mk.eta, ← Function.id_def, tendsto_id']

中文:
定理 inseparable_iff_of_le_nhds
  结论: {f g : CauchyFilter α} {a b : α}
  证明: by
  rw [← tendsto_id'] at ha hb
  rw [inseparable_iff]; rw [(ha.comp tendsto_fst).inseparable_iff_uniformity (hb.comp tendsto_snd)]
  simp only [Function.comp_apply, id_eq, Prod.mk.eta, ← Function.id_def, tendsto_id']

Depends on / 依赖: Function, Function.comp_apply, Function.id_def, Prod.mk.eta, comp_apply, ha.comp, hb.comp, id_def, id_eq, inseparable_iff, inseparable_iff_uniformity, tendsto_fst, tendsto_id, tendsto_snd
-/
theorem inseparable_iff_of_le_nhds {f g : CauchyFilter α} {a b : α}
    (ha : f.1 <= 𝓝 a) (hb : g.1 <= 𝓝 b) : Inseparable a b ↔ Inseparable f g := by
  rw [← tendsto_id'] at ha hb
  rw [inseparable_iff]; rw [(ha.comp tendsto_fst).inseparable_iff_uniformity (hb.comp tendsto_snd)]
  simp only [Function.comp_apply, id_eq, Prod.mk.eta, ← Function.id_def, tendsto_id']

/--
theorem `inseparable_lim_iff` / 定理 `inseparable_lim_iff`

English:
theorem inseparable_lim_iff
  given: [CompleteSpace α] {f g : CauchyFilter α}
  proof: f.2.1.nonempty; Inseparable (lim f.1) (lim g.1) ↔ Inseparable f g :=
  inseparable_iff_of_le_nhds f.2.le_nhds_lim g.2.le_nhds_lim

中文:
定理 inseparable_lim_iff
  条件: [完备空间 α] {f g : CauchyFilter α}
  证明: f.2.1.nonempty; Inseparable (lim f.1) (lim g.1) ↔ Inseparable f g :=
  inseparable_iff_of_le_nhds f.2.le_nhds_lim g.2.le_nhds_lim

Depends on / 依赖: Inseparable, nonempty
-/
theorem inseparable_lim_iff [CompleteSpace α] {f g : CauchyFilter α} :
    haveI := f.2.1.nonempty; Inseparable (lim f.1) (lim g.1) ↔ Inseparable f g :=
  inseparable_iff_of_le_nhds f.2.le_nhds_lim g.2.le_nhds_lim

end

/--
theorem `cauchyFilter_eq` / 定理 `cauchyFilter_eq`

English:
theorem cauchyFilter_eq
  statement: {α : Type*} [UniformSpace α] [CompleteSpace α] [T0Space α]
  proof: f.2.1.nonempty; lim f.1 = lim g.1 ↔ Inseparable f g := by
  rw [← inseparable_iff_eq]; rw [inseparable_lim_iff]

中文:
定理 cauchyFilter_eq
  结论: {α : 类型} [一致空间 α] [完备空间 α] [T0空间 α]
  证明: f.2.1.nonempty; lim f.1 = lim g.1 ↔ Inseparable f g := by
  rw [← inseparable_iff_eq]; rw [inseparable_lim_iff]

Depends on / 依赖: Inseparable, inseparable_iff_eq, inseparable_lim_iff, nonempty
-/
theorem cauchyFilter_eq {α : Type*} [UniformSpace α] [CompleteSpace α] [T0Space α]
    {f g : CauchyFilter α} :
    haveI := f.2.1.nonempty; lim f.1 = lim g.1 ↔ Inseparable f g := by
  rw [← inseparable_iff_eq]; rw [inseparable_lim_iff]

section

/--
theorem `separated_pureCauchy_injective` / 定理 `separated_pureCauchy_injective`

English:
theorem separated_pureCauchy_injective
  given: {α : Type*} [UniformSpace α] [T0Space α]
  proof: fun a b h =>
Inseparable.eq (inseparable_iff_of_le_nhds (pure_le_nhds a) (pure_le_nhds b)).2
    SeparationQuotient.mk_eq_mk.1 h

中文:
定理 separated_pureCauchy_injective
  条件: {α : 类型} [一致空间 α] [T0空间 α]
  证明: fun a b h =>
Inseparable.eq (inseparable_iff_of_le_nhds (pure_le_nhds a) (pure_le_nhds b)).2
    SeparationQuotient.mk_eq_mk.1 h
-/
theorem separated_pureCauchy_injective {α : Type*} [UniformSpace α] [T0Space α] :
    Function.Injective fun a : α => SeparationQuotient.mk (pureCauchy a) := fun a b h =>
Inseparable.eq (inseparable_iff_of_le_nhds (pure_le_nhds a) (pure_le_nhds b)).2
    SeparationQuotient.mk_eq_mk.1 h

end

end CauchyFilter

open CauchyFilter Set

namespace UniformSpace

variable (α : Type*) [UniformSpace α]
variable {β : Type*} [UniformSpace β]
variable {γ : Type*} [UniformSpace γ]

/--
Definition of `Completion` / `Completion` 的定义

English:
definition Completion
  body: SeparationQuotient (CauchyFilter α)

中文:
定义 完备化
  定义体: SeparationQuotient (CauchyFilter α)

Depends on / 依赖: CauchyFilter, SeparationQuotient
-/
def Completion := SeparationQuotient (CauchyFilter α)

namespace Completion

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: [Inhabited α]
  body: inferInstanceAs Inhabited (Quotient _)

中文:
实例 inhabited
  签名: [可居 α]
  定义体: inferInstanceAs Inhabited (Quotient _)

Depends on / 依赖: Inhabited, Quotient
-/
instance inhabited [Inhabited α] : Inhabited (Completion α) :=
inferInstanceAs Inhabited (Quotient _)

/--
Instance `uniformSpace` / 实例 `uniformSpace`

English:
instance uniformSpace
  signature: : UniformSpace (Completion α)
  body: fast_instance% SeparationQuotient.instUniformSpace

中文:
实例 uniformSpace
  签名: : 一致空间 (完备化 α)
  定义体: fast_instance% SeparationQuotient.instUniformSpace

Depends on / 依赖: SeparationQuotient, SeparationQuotient.instUniformSpace, fast_instance, instUniformSpace
-/
instance uniformSpace : UniformSpace (Completion α) :=
  fast_instance% SeparationQuotient.instUniformSpace

/--
Instance `completeSpace` / 实例 `completeSpace`

English:
instance completeSpace
  signature: : CompleteSpace (Completion α)
  body: SeparationQuotient.instCompleteSpace

中文:
实例 completeSpace
  签名: : 完备空间 (完备化 α)
  定义体: SeparationQuotient.instCompleteSpace

Depends on / 依赖: SeparationQuotient, SeparationQuotient.instCompleteSpace, instCompleteSpace
-/
instance completeSpace : CompleteSpace (Completion α) :=
  SeparationQuotient.instCompleteSpace

/--
Instance `t0Space` / 实例 `t0Space`

English:
instance t0Space
  signature: : T0Space (Completion α)
  body: SeparationQuotient.instT0Space

中文:
实例 t0Space
  签名: : T0空间 (完备化 α)
  定义体: SeparationQuotient.instT0Space

Depends on / 依赖: SeparationQuotient, SeparationQuotient.instT0Space, instT0Space
-/
instance t0Space : T0Space (Completion α) := SeparationQuotient.instT0Space

variable {α} in
/--
Definition of `coe'` / `coe'` 的定义

English:
definition coe'
  signature: : α -> Completion α
  body: SeparationQuotient.mk ∘ pureCauchy

中文:
定义 coe'
  签名: : α -> 完备化 α
  定义体: SeparationQuotient.mk ∘ pureCauchy
-/
@[coe] def coe' : α -> Completion α := SeparationQuotient.mk ∘ pureCauchy

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe α (Completion α)
  body: ⟨coe'⟩

中文:
实例 :
  签名: Coe α (完备化 α)
  定义体: ⟨coe'⟩
-/
instance : Coe α (Completion α) :=
  ⟨coe'⟩

-- note [use has_coe_t]
/--
theorem `coe_eq` / 定理 `coe_eq`

English:
theorem coe_eq
  statement: ((↑) : α -> Completion α) = SeparationQuotient.mk ∘ pureCauchy
  proof: rfl

中文:
定理 coe_eq
  结论: ((↑) : α -> 完备化 α) = SeparationQuotient.mk ∘ pureCauchy
  证明: rfl
-/
protected theorem coe_eq : ((↑) : α -> Completion α) = SeparationQuotient.mk ∘ pureCauchy := rfl

/--
theorem `isUniformInducing_coe` / 定理 `isUniformInducing_coe`

English:
theorem isUniformInducing_coe
  statement: IsUniformInducing ((↑) : α -> Completion α)
  proof: SeparationQuotient.isUniformInducing_mk.comp isUniformInducing_pureCauchy

中文:
定理 isUniformInducing_coe
  结论: 是UniformInducing ((↑) : α -> 完备化 α)
  证明: SeparationQuotient.isUniformInducing_mk.comp isUniformInducing_pureCauchy

Depends on / 依赖: SeparationQuotient, SeparationQuotient.isUniformInducing_mk.comp, isUniformInducing_mk, isUniformInducing_pureCauchy
-/
theorem isUniformInducing_coe : IsUniformInducing ((↑) : α -> Completion α) :=
  SeparationQuotient.isUniformInducing_mk.comp isUniformInducing_pureCauchy

/--
theorem `comap_coe_eq_uniformity` / 定理 `comap_coe_eq_uniformity`

English:
theorem comap_coe_eq_uniformity
  proof: (isUniformInducing_coe _).1

中文:
定理 comap_coe_eq_uniformity
  证明: (isUniformInducing_coe _).1

Depends on / 依赖: isUniformInducing_coe
-/
theorem comap_coe_eq_uniformity :
    ((𝓤 _).comap fun p : α × α => ((p.1 : Completion α), (p.2 : Completion α))) = 𝓤 α :=
  (isUniformInducing_coe _).1

variable {α} in
/--
theorem `denseRange_coe` / 定理 `denseRange_coe`

English:
theorem denseRange_coe
  statement: DenseRange ((↑) : α -> Completion α)
  proof: SeparationQuotient.surjective_mk.denseRange.comp denseRange_pureCauchy
    SeparationQuotient.continuous_mk

中文:
定理 denseRange_coe
  结论: DenseRange ((↑) : α -> 完备化 α)
  证明: SeparationQuotient.surjective_mk.denseRange.comp denseRange_pureCauchy
    SeparationQuotient.continuous_mk

Depends on / 依赖: SeparationQuotient, SeparationQuotient.continuous_mk, SeparationQuotient.surjective_mk.denseRange.comp, continuous_mk, denseRange, denseRange_pureCauchy, surjective_mk
-/
theorem denseRange_coe : DenseRange ((↑) : α -> Completion α) :=
  SeparationQuotient.surjective_mk.denseRange.comp denseRange_pureCauchy
    SeparationQuotient.continuous_mk

/--
Definition of `cPkg` / `cPkg` 的定义

English:
definition cPkg
  signature: {α : Type*} [UniformSpace α]
  body: Completion α
  coe := (↑)
  uniformStruct := by infer_instance
  complete := by infer_instance
  separation := by infer_instance
  isUniformInducing := Completion.isUniformInducing_coe α
  dense := Completion.denseRange_coe

中文:
定义 cPkg
  签名: {α : 类型} [一致空间 α]
  定义体: Completion α
  coe := (↑)
  uniformStruct := by infer_instance
  complete := by infer_instance
  separation := by infer_instance
  isUniformInducing := Completion.isUniformInducing_coe α
  dense := Completion.denseRange_coe

Depends on / 依赖: Completion
-/
def cPkg {α : Type*} [UniformSpace α] : AbstractCompletion α where
  space := Completion α
  coe := (↑)
  uniformStruct := by infer_instance
  complete := by infer_instance
  separation := by infer_instance
  isUniformInducing := Completion.isUniformInducing_coe α
  dense := Completion.denseRange_coe

/--
Instance `AbstractCompletion.inhabited` / 实例 `AbstractCompletion.inhabited`

English:
instance AbstractCompletion.inhabited
  signature: : Inhabited (AbstractCompletion α)
  body: ⟨cPkg⟩

中文:
实例 AbstractCompletion.inhabited
  签名: : 可居 (AbstractCompletion α)
  定义体: ⟨cPkg⟩
-/
instance AbstractCompletion.inhabited : Inhabited (AbstractCompletion α) :=
  ⟨cPkg⟩

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

/--
theorem `nonempty_completion_iff` / 定理 `nonempty_completion_iff`

English:
theorem nonempty_completion_iff
  statement: Nonempty (Completion α) ↔ Nonempty α
  proof: cPkg.dense.nonempty_iff.symm

@[fun_prop]

中文:
定理 nonempty_completion_iff
  结论: 非空 (完备化 α) ↔ 非空 α
  证明: cPkg.dense.nonempty_iff.symm

@[fun_prop]

Depends on / 依赖: cPkg.dense.nonempty_iff.symm, nonempty_iff
-/
theorem nonempty_completion_iff : Nonempty (Completion α) ↔ Nonempty α :=
  cPkg.dense.nonempty_iff.symm

@[fun_prop]
/--
theorem `uniformContinuous_coe` / 定理 `uniformContinuous_coe`

English:
theorem uniformContinuous_coe
  statement: UniformContinuous ((↑) : α -> Completion α)
  proof: cPkg.uniformContinuous_coe

中文:
定理 uniformContinuous_coe
  结论: 一致连续 ((↑) : α -> 完备化 α)
  证明: cPkg.uniformContinuous_coe

Depends on / 依赖: cPkg.uniformContinuous_coe, uniformContinuous_coe
-/
theorem uniformContinuous_coe : UniformContinuous ((↑) : α -> Completion α) :=
  cPkg.uniformContinuous_coe

/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous ((↑) : α -> Completion α)
  proof: cPkg.continuous_coe

中文:
定理 continuous_coe
  结论: 连续 ((↑) : α -> 完备化 α)
  证明: cPkg.continuous_coe

Depends on / 依赖: cPkg.continuous_coe, continuous_coe
-/
theorem continuous_coe : Continuous ((↑) : α -> Completion α) :=
  cPkg.continuous_coe

/--
theorem `isUniformEmbedding_coe` / 定理 `isUniformEmbedding_coe`

English:
theorem isUniformEmbedding_coe
  given: [T0Space α]
  statement: IsUniformEmbedding ((↑) : α -> Completion α)
  proof: { comap_uniformity := comap_coe_eq_uniformity α
    injective := separated_pureCauchy_injective }

中文:
定理 isUniformEmbedding_coe
  条件: [T0空间 α]
  结论: 是一致嵌入 ((↑) : α -> 完备化 α)
  证明: { comap_uniformity := comap_coe_eq_uniformity α
    injective := separated_pureCauchy_injective }

Depends on / 依赖: comap_coe_eq_uniformity, comap_uniformity, injective, separated_pureCauchy_injective
-/
theorem isUniformEmbedding_coe [T0Space α] : IsUniformEmbedding ((↑) : α -> Completion α) :=
  { comap_uniformity := comap_coe_eq_uniformity α
    injective := separated_pureCauchy_injective }

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  given: [T0Space α]
  statement: Function.Injective ((↑) : α -> Completion α)
  proof: IsUniformEmbedding.injective (isUniformEmbedding_coe _)

中文:
定理 coe_injective
  条件: [T0空间 α]
  结论: 函数.单射 ((↑) : α -> 完备化 α)
  证明: IsUniformEmbedding.injective (isUniformEmbedding_coe _)

Depends on / 依赖: IsUniformEmbedding, IsUniformEmbedding.injective, injective, isUniformEmbedding_coe
-/
theorem coe_injective [T0Space α] : Function.Injective ((↑) : α -> Completion α) :=
  IsUniformEmbedding.injective (isUniformEmbedding_coe _)

variable {α}

@[simp]
/--
lemma `coe_inj` / 引理 `coe_inj`

English:
lemma coe_inj
  given: [T0Space α] {a b : α}
  statement: (a : Completion α) = b ↔ a = b
  proof: (coe_injective _).eq_iff

中文:
引理 coe_inj
  条件: [T0空间 α] {a b : α}
  结论: (a : 完备化 α) = b ↔ a = b
  证明: (coe_injective _).eq_iff

Depends on / 依赖: coe_injective, eq_iff
-/
lemma coe_inj [T0Space α] {a b : α} : (a : Completion α) = b ↔ a = b :=
  (coe_injective _).eq_iff

/--
theorem `isDenseInducing_coe` / 定理 `isDenseInducing_coe`

English:
theorem isDenseInducing_coe
  statement: IsDenseInducing ((↑) : α -> Completion α)
  proof: { (isUniformInducing_coe α).isInducing with dense := denseRange_coe }

中文:
定理 isDenseInducing_coe
  结论: 是DenseInducing ((↑) : α -> 完备化 α)
  证明: { (isUniformInducing_coe α).isInducing with dense := denseRange_coe }

Depends on / 依赖: denseRange_coe, isInducing, isUniformInducing_coe
-/
theorem isDenseInducing_coe : IsDenseInducing ((↑) : α -> Completion α) :=
  { (isUniformInducing_coe α).isInducing with dense := denseRange_coe }

/--
Definition of `UniformCompletion.completeEquivSelf` / `UniformCompletion.completeEquivSelf` 的定义

English:
definition UniformCompletion.completeEquivSelf
  signature: [CompleteSpace α] [T0Space α]
  body: AbstractCompletion.compareEquiv Completion.cPkg AbstractCompletion.ofComplete

中文:
定义 UniformCompletion.completeEquivSelf
  签名: [完备空间 α] [T0空间 α]
  定义体: AbstractCompletion.compareEquiv Completion.cPkg AbstractCompletion.ofComplete

Depends on / 依赖: AbstractCompletion, AbstractCompletion.compareEquiv, AbstractCompletion.ofComplete, Completion, Completion.cPkg, compareEquiv, ofComplete
-/
def UniformCompletion.completeEquivSelf [CompleteSpace α] [T0Space α] : Completion α ≃ᵤ α :=
  AbstractCompletion.compareEquiv Completion.cPkg AbstractCompletion.ofComplete

open TopologicalSpace

/--
Instance `separableSpace_completion` / 实例 `separableSpace_completion`

English:
instance separableSpace_completion
  signature: [SeparableSpace α]
  body: Completion.isDenseInducing_coe.separableSpace

中文:
实例 separableSpace_completion
  签名: [可分空间 α]
  定义体: Completion.isDenseInducing_coe.separableSpace

Depends on / 依赖: Completion, Completion.isDenseInducing_coe.separableSpace, isDenseInducing_coe, separableSpace
-/
instance separableSpace_completion [SeparableSpace α] : SeparableSpace (Completion α) :=
  Completion.isDenseInducing_coe.separableSpace

/--
theorem `isDenseEmbedding_coe` / 定理 `isDenseEmbedding_coe`

English:
theorem isDenseEmbedding_coe
  given: [T0Space α]
  statement: IsDenseEmbedding ((↑) : α -> Completion α)
  proof: { isDenseInducing_coe with injective := separated_pureCauchy_injective }

中文:
定理 isDenseEmbedding_coe
  条件: [T0空间 α]
  结论: 是稠密嵌入 ((↑) : α -> 完备化 α)
  证明: { isDenseInducing_coe with injective := separated_pureCauchy_injective }

Depends on / 依赖: injective, isDenseInducing_coe, separated_pureCauchy_injective
-/
theorem isDenseEmbedding_coe [T0Space α] : IsDenseEmbedding ((↑) : α -> Completion α) :=
  { isDenseInducing_coe with injective := separated_pureCauchy_injective }

/--
theorem `denseRange_coe₂` / 定理 `denseRange_coe₂`

English:
theorem denseRange_coe₂
  proof: denseRange_coe.prodMap denseRange_coe

中文:
定理 denseRange_coe₂
  证明: denseRange_coe.prodMap denseRange_coe

Depends on / 依赖: denseRange_coe, denseRange_coe.prodMap, prodMap
-/
theorem denseRange_coe₂ :
    DenseRange fun x : α × β => ((x.1 : Completion α), (x.2 : Completion β)) :=
  denseRange_coe.prodMap denseRange_coe

/--
theorem `denseRange_coe₃` / 定理 `denseRange_coe₃`

English:
theorem denseRange_coe₃
  proof: denseRange_coe.prodMap denseRange_coe₂

@[elab_as_elim]

中文:
定理 denseRange_coe₃
  证明: denseRange_coe.prodMap denseRange_coe₂

@[elab_as_elim]

Depends on / 依赖: denseRange_coe, denseRange_coe.prodMap, prodMap
-/
theorem denseRange_coe₃ :
    DenseRange fun x : α × β × γ =>
      ((x.1 : Completion α), ((x.2.1 : Completion β), (x.2.2 : Completion γ))) :=
  denseRange_coe.prodMap denseRange_coe₂

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {p : Completion α -> Prop} (a : Completion α) (hp : IsClosed { a | p a })
  proof: isClosed_property denseRange_coe hp ih a

@[elab_as_elim]

中文:
定理 induction_on
  结论: {p : 完备化 α -> 命题} (a : 完备化 α) (hp : 是闭集 { a | p a })
  证明: isClosed_property denseRange_coe hp ih a

@[elab_as_elim]

Depends on / 依赖: denseRange_coe, isClosed_property
-/
theorem induction_on {p : Completion α -> Prop} (a : Completion α) (hp : IsClosed { a | p a })
    (ih : forall a : α, p a) : p a :=
  isClosed_property denseRange_coe hp ih a

@[elab_as_elim]
/--
theorem `induction_on₂` / 定理 `induction_on₂`

English:
theorem induction_on₂
  statement: {p : Completion α -> Completion β -> Prop} (a : Completion α) (b : Completion β)
  proof: have : forall x : Completion α × Completion β, p x.1 x.2 :=
    isClosed_property denseRange_coe₂ hp fun ⟨a, b⟩ => ih a b
  this (a, b)

@[elab_as_elim]

中文:
定理 induction_on₂
  结论: {p : 完备化 α -> 完备化 β -> 命题} (a : 完备化 α) (b : 完备化 β)
  证明: have : forall x : Completion α × Completion β, p x.1 x.2 :=
    isClosed_property denseRange_coe₂ hp fun ⟨a, b⟩ => ih a b
  this (a, b)

@[elab_as_elim]

Depends on / 依赖: Completion, isClosed_property
-/
theorem induction_on₂ {p : Completion α -> Completion β -> Prop} (a : Completion α) (b : Completion β)
    (hp : IsClosed { x : Completion α × Completion β | p x.1 x.2 })
    (ih : forall (a : α) (b : β), p a b) : p a b :=
  have : forall x : Completion α × Completion β, p x.1 x.2 :=
    isClosed_property denseRange_coe₂ hp fun ⟨a, b⟩ => ih a b
  this (a, b)

@[elab_as_elim]
/--
theorem `induction_on₃` / 定理 `induction_on₃`

English:
theorem induction_on₃
  statement: {p : Completion α -> Completion β -> Completion γ -> Prop} (a : Completion α)
  proof: have : forall x : Completion α × Completion β × Completion γ, p x.1 x.2.1 x.2.2 :=
    isClosed_property denseRange_coe₃ hp fun ⟨a, b, c⟩ => ih a b c
  this (a, b, c)

中文:
定理 induction_on₃
  结论: {p : 完备化 α -> 完备化 β -> 完备化 γ -> 命题} (a : 完备化 α)
  证明: have : forall x : Completion α × Completion β × Completion γ, p x.1 x.2.1 x.2.2 :=
    isClosed_property denseRange_coe₃ hp fun ⟨a, b, c⟩ => ih a b c
  this (a, b, c)

Depends on / 依赖: Completion, isClosed_property
-/
theorem induction_on₃ {p : Completion α -> Completion β -> Completion γ -> Prop} (a : Completion α)
    (b : Completion β) (c : Completion γ)
    (hp : IsClosed { x : Completion α × Completion β × Completion γ | p x.1 x.2.1 x.2.2 })
    (ih : forall (a : α) (b : β) (c : γ), p a b c) : p a b c :=
  have : forall x : Completion α × Completion β × Completion γ, p x.1 x.2.1 x.2.2 :=
    isClosed_property denseRange_coe₃ hp fun ⟨a, b, c⟩ => ih a b c
  this (a, b, c)

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : Completion α -> Y}
  proof: cPkg.funext hf hg h

中文:
定理 ext
  结论: {Y : 类型} [拓扑空间 Y] [T2空间 Y] {f g : 完备化 α -> Y}
  证明: cPkg.funext hf hg h

Depends on / 依赖: cPkg.funext
-/
theorem ext {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : Completion α -> Y}
    (hf : Continuous f) (hg : Continuous g) (h : forall a : α, f a = g a) : f = g :=
  cPkg.funext hf hg h

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  statement: {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : Completion α -> Y}
  proof: congr_fun (ext hf hg h) a

中文:
定理 ext'
  结论: {Y : 类型} [拓扑空间 Y] [T2空间 Y] {f g : 完备化 α -> Y}
  证明: congr_fun (ext hf hg h) a

Depends on / 依赖: congr_fun
-/
theorem ext' {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : Completion α -> Y}
    (hf : Continuous f) (hg : Continuous g) (h : forall a : α, f a = g a) (a : Completion α) :
    f a = g a :=
  congr_fun (ext hf hg h) a

section Extension

variable {f : α -> β}

/--
Definition of `extension` / `extension` 的定义

English:
definition extension
  signature: (f : α -> β)
  body: cPkg.extend f

中文:
定义 extension
  签名: (f : α -> β)
  定义体: cPkg.extend f
-/
protected def extension (f : α -> β) : Completion α -> β :=
  cPkg.extend f

section CompleteSpace

variable [CompleteSpace β]

@[fun_prop]
/--
theorem `uniformContinuous_extension` / 定理 `uniformContinuous_extension`

English:
theorem uniformContinuous_extension
  statement: UniformContinuous (Completion.extension f)
  proof: cPkg.uniformContinuous_extend

@[continuity, fun_prop]

中文:
定理 uniformContinuous_extension
  结论: 一致连续 (完备化.extension f)
  证明: cPkg.uniformContinuous_extend

@[continuity, fun_prop]

Depends on / 依赖: cPkg.uniformContinuous_extend, uniformContinuous_extend
-/
theorem uniformContinuous_extension : UniformContinuous (Completion.extension f) :=
  cPkg.uniformContinuous_extend

@[continuity, fun_prop]
/--
theorem `continuous_extension` / 定理 `continuous_extension`

English:
theorem continuous_extension
  statement: Continuous (Completion.extension f)
  proof: cPkg.continuous_extend

中文:
定理 continuous_extension
  结论: 连续 (完备化.extension f)
  证明: cPkg.continuous_extend

Depends on / 依赖: cPkg.continuous_extend, continuous_extend
-/
theorem continuous_extension : Continuous (Completion.extension f) :=
  cPkg.continuous_extend

end CompleteSpace

/--
theorem `extension_coe` / 定理 `extension_coe`

English:
theorem extension_coe
  given: [T0Space β] (hf : UniformContinuous f) (a : α)
  proof: cPkg.extend_coe hf a

中文:
定理 extension_coe
  条件: [T0空间 β] (hf : 一致连续 f) (a : α)
  证明: cPkg.extend_coe hf a

Depends on / 依赖: cPkg.extend_coe, extend_coe
-/
theorem extension_coe [T0Space β] (hf : UniformContinuous f) (a : α) :
    (Completion.extension f) a = f a :=
  cPkg.extend_coe hf a

/--
theorem `inseparable_extension_coe` / 定理 `inseparable_extension_coe`

English:
theorem inseparable_extension_coe
  given: (hf : UniformContinuous f) (x : α)
  proof: cPkg.inseparable_extend_coe hf x

中文:
定理 inseparable_extension_coe
  条件: (hf : 一致连续 f) (x : α)
  证明: cPkg.inseparable_extend_coe hf x

Depends on / 依赖: cPkg.inseparable_extend_coe, inseparable_extend_coe
-/
theorem inseparable_extension_coe (hf : UniformContinuous f) (x : α) :
    Inseparable (Completion.extension f x) (f x) :=
  cPkg.inseparable_extend_coe hf x

/--
lemma `isUniformInducing_extension` / 引理 `isUniformInducing_extension`

English:
lemma isUniformInducing_extension
  given: [CompleteSpace β] (h : IsUniformInducing f)
  proof: cPkg.isUniformInducing_extend h

中文:
引理 isUniformInducing_extension
  条件: [完备空间 β] (h : 是UniformInducing f)
  证明: cPkg.isUniformInducing_extend h

Depends on / 依赖: cPkg.isUniformInducing_extend, isUniformInducing_extend
-/
lemma isUniformInducing_extension [CompleteSpace β] (h : IsUniformInducing f) :
    IsUniformInducing (Completion.extension f) :=
  cPkg.isUniformInducing_extend h

variable [T0Space β] [CompleteSpace β]

/--
theorem `extension_unique` / 定理 `extension_unique`

English:
theorem extension_unique
  statement: (hf : UniformContinuous f) {g : Completion α -> β}
  proof: cPkg.extend_unique hf hg h

@[simp]

中文:
定理 extension_unique
  结论: (hf : 一致连续 f) {g : 完备化 α -> β}
  证明: cPkg.extend_unique hf hg h

@[simp]

Depends on / 依赖: cPkg.extend_unique, extend_unique
-/
theorem extension_unique (hf : UniformContinuous f) {g : Completion α -> β}
    (hg : UniformContinuous g) (h : forall a : α, f a = g (a : Completion α)) :
    Completion.extension f = g :=
  cPkg.extend_unique hf hg h

@[simp]
/--
theorem `extension_comp_coe` / 定理 `extension_comp_coe`

English:
theorem extension_comp_coe
  given: {f : Completion α -> β} (hf : UniformContinuous f)
  proof: cPkg.extend_comp_coe hf

中文:
定理 extension_comp_coe
  条件: {f : 完备化 α -> β} (hf : 一致连续 f)
  证明: cPkg.extend_comp_coe hf

Depends on / 依赖: cPkg.extend_comp_coe, extend_comp_coe
-/
theorem extension_comp_coe {f : Completion α -> β} (hf : UniformContinuous f) :
    Completion.extension (f ∘ (↑)) = f :=
  cPkg.extend_comp_coe hf

end Extension

section Map

variable {f : α -> β}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)
  body: cPkg.map cPkg f

@[fun_prop]

中文:
定义 map
  签名: (f : α -> β)
  定义体: cPkg.map cPkg f

@[fun_prop]
-/
protected def map (f : α -> β) : Completion α -> Completion β :=
  cPkg.map cPkg f

@[fun_prop]
/--
theorem `uniformContinuous_map` / 定理 `uniformContinuous_map`

English:
theorem uniformContinuous_map
  statement: UniformContinuous (Completion.map f)
  proof: cPkg.uniformContinuous_map cPkg f

@[continuity, fun_prop]

中文:
定理 uniformContinuous_map
  结论: 一致连续 (完备化.map f)
  证明: cPkg.uniformContinuous_map cPkg f

@[continuity, fun_prop]

Depends on / 依赖: cPkg.uniformContinuous_map, uniformContinuous_map
-/
theorem uniformContinuous_map : UniformContinuous (Completion.map f) :=
  cPkg.uniformContinuous_map cPkg f

@[continuity, fun_prop]
/--
theorem `continuous_map` / 定理 `continuous_map`

English:
theorem continuous_map
  statement: Continuous (Completion.map f)
  proof: cPkg.continuous_map cPkg f

中文:
定理 continuous_map
  结论: 连续 (完备化.map f)
  证明: cPkg.continuous_map cPkg f

Depends on / 依赖: cPkg.continuous_map, continuous_map
-/
theorem continuous_map : Continuous (Completion.map f) :=
  cPkg.continuous_map cPkg f

/--
theorem `map_coe` / 定理 `map_coe`

English:
theorem map_coe
  given: (hf : UniformContinuous f) (a : α)
  statement: (Completion.map f) a = f a
  proof: cPkg.map_coe cPkg hf a

中文:
定理 map_coe
  条件: (hf : 一致连续 f) (a : α)
  结论: (完备化.map f) a = f a
  证明: cPkg.map_coe cPkg hf a

Depends on / 依赖: cPkg.map_coe, map_coe
-/
theorem map_coe (hf : UniformContinuous f) (a : α) : (Completion.map f) a = f a :=
  cPkg.map_coe cPkg hf a

/--
theorem `map_unique` / 定理 `map_unique`

English:
theorem map_unique
  statement: {f : α -> β} {g : Completion α -> Completion β} (hg : UniformContinuous g)
  proof: cPkg.map_unique cPkg hg h

@[simp]

中文:
定理 map_unique
  结论: {f : α -> β} {g : 完备化 α -> 完备化 β} (hg : 一致连续 g)
  证明: cPkg.map_unique cPkg hg h

@[simp]

Depends on / 依赖: cPkg.map_unique, map_unique
-/
theorem map_unique {f : α -> β} {g : Completion α -> Completion β} (hg : UniformContinuous g)
    (h : forall a : α, ↑(f a) = g a) : Completion.map f = g :=
  cPkg.map_unique cPkg hg h

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: Completion.map (@id α) = id
  proof: cPkg.map_id

中文:
定理 map_id
  结论: 完备化.map (@id α) = id
  证明: cPkg.map_id

Depends on / 依赖: cPkg.map_id, map_id
-/
theorem map_id : Completion.map (@id α) = id :=
  cPkg.map_id

/--
theorem `extension_map` / 定理 `extension_map`

English:
theorem extension_map
  statement: [CompleteSpace γ] [T0Space γ] {f : β -> γ} {g : α -> β}
  proof: Completion.ext (continuous_extension.comp continuous_map) continuous_extension by
    simp [hf, hg, hf.comp hg, map_coe, extension_coe]

中文:
定理 extension_map
  结论: [完备空间 γ] [T0空间 γ] {f : β -> γ} {g : α -> β}
  证明: Completion.ext (continuous_extension.comp continuous_map) continuous_extension by
    simp [hf, hg, hf.comp hg, map_coe, extension_coe]

Depends on / 依赖: Completion, Completion.ext, continuous_extension, continuous_extension.comp, continuous_map, extension_coe, hf.comp, map_coe
-/
theorem extension_map [CompleteSpace γ] [T0Space γ] {f : β -> γ} {g : α -> β}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    Completion.extension f ∘ Completion.map g = Completion.extension (f ∘ g) :=
Completion.ext (continuous_extension.comp continuous_map) continuous_extension by
    simp [hf, hg, hf.comp hg, map_coe, extension_coe]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {g : β -> γ} {f : α -> β} (hg : UniformContinuous g) (hf : UniformContinuous f)
  proof: extension_map ((uniformContinuous_coe _).comp hg) hf

中文:
定理 map_comp
  条件: {g : β -> γ} {f : α -> β} (hg : 一致连续 g) (hf : 一致连续 f)
  证明: extension_map ((uniformContinuous_coe _).comp hg) hf

Depends on / 依赖: extension_map, uniformContinuous_coe
-/
theorem map_comp {g : β -> γ} {f : α -> β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
    Completion.map g ∘ Completion.map f = Completion.map (g ∘ f) :=
  extension_map ((uniformContinuous_coe _).comp hg) hf

/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (e : α ≃ᵤ β)
  body: cPkg.mapEquiv cPkg e

@[simp]

中文:
定义 mapEquiv
  签名: (e : α ≃ᵤ β)
  定义体: cPkg.mapEquiv cPkg e

@[simp]

Depends on / 依赖: cPkg.mapEquiv, mapEquiv
-/
def mapEquiv (e : α ≃ᵤ β) : Completion α ≃ᵤ Completion β := cPkg.mapEquiv cPkg e

@[simp]
/--
theorem `mapEquiv_symm` / 定理 `mapEquiv_symm`

English:
theorem mapEquiv_symm
  given: (e : α ≃ᵤ β)
  statement: (mapEquiv e).symm = mapEquiv e.symm
  proof: cPkg.mapEquiv_symm cPkg e

@[simp]

中文:
定理 mapEquiv_symm
  条件: (e : α ≃ᵤ β)
  结论: (mapEquiv e).symm = mapEquiv e.symm
  证明: cPkg.mapEquiv_symm cPkg e

@[simp]

Depends on / 依赖: cPkg.mapEquiv_symm, mapEquiv_symm
-/
theorem mapEquiv_symm (e : α ≃ᵤ β) : (mapEquiv e).symm = mapEquiv e.symm :=
  cPkg.mapEquiv_symm cPkg e

@[simp]
/--
theorem `mapEquiv_coe` / 定理 `mapEquiv_coe`

English:
theorem mapEquiv_coe
  given: (e : α ≃ᵤ β) (a : α)
  statement: mapEquiv e a = (e a)
  proof: cPkg.mapEquiv_coe cPkg e a

中文:
定理 mapEquiv_coe
  条件: (e : α ≃ᵤ β) (a : α)
  结论: mapEquiv e a = (e a)
  证明: cPkg.mapEquiv_coe cPkg e a

Depends on / 依赖: cPkg.mapEquiv_coe, mapEquiv_coe
-/
theorem mapEquiv_coe (e : α ≃ᵤ β) (a : α) : mapEquiv e a = (e a) := cPkg.mapEquiv_coe cPkg e a

end Map

/- In this section we construct isomorphisms between the completion of a uniform space and the
completion of its separation quotient -/
section SeparationQuotientCompletion

open SeparationQuotient in
/--
Definition of `completionSeparationQuotientEquiv` / `completionSeparationQuotientEquiv` 的定义

English:
definition completionSeparationQuotientEquiv
  signature: (α : Type u) [UniformSpace α]
  body: by
  refine ⟨Completion.extension (lift' ((↑) : α -> Completion α)),
    Completion.map SeparationQuotient.mk, fun a => ?_, fun a => ?_⟩
  · refine induction_on a (isClosed_eq (continuous_map.comp continuous_extension) continuous_id) ?_
    refine SeparationQuotient.surjective_mk.forall.2 fun a => ?_
    rw [extension_coe (uniformContinuous_lift' _)]; rw [lift'_mk (uniformContinuous_coe α)]; rw [map_coe uniformContinuous_mk]
  · refine induction_on a
      (isClosed_eq (continuous_extension.comp continuous_map) continuous_id) fun a => ?_
    rw [map_coe uniformContinuous_mk]; rw [extension_coe (uniformContinuous_lift' _)]; rw [lift'_mk (uniformContinuous_coe _)]

@[fun_prop]

中文:
定义 completionSeparationQuotientEquiv
  签名: (α : 类型u) [一致空间 α]
  定义体: by
  refine ⟨Completion.extension (lift' ((↑) : α -> Completion α)),
    Completion.map SeparationQuotient.mk, fun a => ?_, fun a => ?_⟩
  · refine induction_on a (isClosed_eq (continuous_map.comp continuous_extension) continuous_id) ?_
    refine SeparationQuotient.surjective_mk.forall.2 fun a => ?_
    rw [extension_coe (uniformContinuous_lift' _)]; rw [lift'_mk (uniformContinuous_coe α)]; rw [map_coe uniformContinuous_mk]
  · refine induction_on a
      (isClosed_eq (continuous_extension.comp continuous_map) continuous_id) fun a => ?_
    rw [map_coe uniformContinuous_mk]; rw [extension_coe (uniformContinuous_lift' _)]; rw [lift'_mk (uniformContinuous_coe _)]

@[fun_prop]

Depends on / 依赖: Completion, Completion.extension, Completion.map, SeparationQuotient, SeparationQuotient.mk, SeparationQuotient.surjective_mk.forall, continu, continuous_extension, continuous_extension.comp, continuous_id, continuous_map, continuous_map.comp, extension, extension_coe, induction_on, isClosed_eq, map_coe, surjective_mk, uniformContinuous_coe, uniformContinuous_lift
-/
def completionSeparationQuotientEquiv (α : Type u) [UniformSpace α] :
    Completion (SeparationQuotient α) ≃ Completion α := by
  refine ⟨Completion.extension (lift' ((↑) : α -> Completion α)),
    Completion.map SeparationQuotient.mk, fun a => ?_, fun a => ?_⟩
  · refine induction_on a (isClosed_eq (continuous_map.comp continuous_extension) continuous_id) ?_
    refine SeparationQuotient.surjective_mk.forall.2 fun a => ?_
    rw [extension_coe (uniformContinuous_lift' _)]; rw [lift'_mk (uniformContinuous_coe α)]; rw [map_coe uniformContinuous_mk]
  · refine induction_on a
      (isClosed_eq (continuous_extension.comp continuous_map) continuous_id) fun a => ?_
    rw [map_coe uniformContinuous_mk]; rw [extension_coe (uniformContinuous_lift' _)]; rw [lift'_mk (uniformContinuous_coe _)]

@[fun_prop]
/--
theorem `uniformContinuous_completionSeparationQuotientEquiv` / 定理 `uniformContinuous_completionSeparationQuotientEquiv`

English:
theorem uniformContinuous_completionSeparationQuotientEquiv
  proof: uniformContinuous_extension

@[fun_prop]

中文:
定理 uniformContinuous_completionSeparationQuotientEquiv
  证明: uniformContinuous_extension

@[fun_prop]

Depends on / 依赖: uniformContinuous_extension
-/
theorem uniformContinuous_completionSeparationQuotientEquiv :
    UniformContinuous (completionSeparationQuotientEquiv α) :=
  uniformContinuous_extension

@[fun_prop]
/--
theorem `uniformContinuous_completionSeparationQuotientEquiv_symm` / 定理 `uniformContinuous_completionSeparationQuotientEquiv_symm`

English:
theorem uniformContinuous_completionSeparationQuotientEquiv_symm
  proof: uniformContinuous_map

中文:
定理 uniformContinuous_completionSeparationQuotientEquiv_symm
  证明: uniformContinuous_map

Depends on / 依赖: uniformContinuous_map
-/
theorem uniformContinuous_completionSeparationQuotientEquiv_symm :
    UniformContinuous (completionSeparationQuotientEquiv α).symm :=
  uniformContinuous_map

end SeparationQuotientCompletion

section Extension₂

variable (f : α -> β -> γ)

open Function

/--
Definition of `extension₂` / `extension₂` 的定义

English:
definition extension₂
  signature: (f : α -> β -> γ)
  body: cPkg.extend₂ cPkg f

中文:
定义 extension₂
  签名: (f : α -> β -> γ)
  定义体: cPkg.extend₂ cPkg f
-/
protected def extension₂ (f : α -> β -> γ) : Completion α -> Completion β -> γ :=
  cPkg.extend₂ cPkg f

section T0Space

variable [T0Space γ] {f}

/--
theorem `extension₂_coe_coe` / 定理 `extension₂_coe_coe`

English:
theorem extension₂_coe_coe
  given: (hf : UniformContinuous₂ f) (a : α) (b : β)
  proof: cPkg.extension₂_coe_coe cPkg hf a b

中文:
定理 extension₂_coe_coe
  条件: (hf : UniformContinuous₂ f) (a : α) (b : β)
  证明: cPkg.extension₂_coe_coe cPkg hf a b

Depends on / 依赖: cPkg.extension
-/
theorem extension₂_coe_coe (hf : UniformContinuous₂ f) (a : α) (b : β) :
    Completion.extension₂ f a b = f a b :=
  cPkg.extension₂_coe_coe cPkg hf a b

end T0Space

variable [CompleteSpace γ]

@[fun_prop]
/--
theorem `uniformContinuous_extension₂` / 定理 `uniformContinuous_extension₂`

English:
theorem uniformContinuous_extension₂
  statement: UniformContinuous₂ (Completion.extension₂ f)
  proof: cPkg.uniformContinuous_extension₂ cPkg f

中文:
定理 uniformContinuous_extension₂
  结论: UniformContinuous₂ (完备化.extension₂ f)
  证明: cPkg.uniformContinuous_extension₂ cPkg f

Depends on / 依赖: cPkg.uniformContinuous_extension
-/
theorem uniformContinuous_extension₂ : UniformContinuous₂ (Completion.extension₂ f) :=
  cPkg.uniformContinuous_extension₂ cPkg f

end Extension₂

section Map₂

open Function

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (f : α -> β -> γ)
  body: cPkg.map₂ cPkg cPkg f

@[fun_prop]

中文:
定义 map₂
  签名: (f : α -> β -> γ)
  定义体: cPkg.map₂ cPkg cPkg f

@[fun_prop]
-/
protected def map₂ (f : α -> β -> γ) : Completion α -> Completion β -> Completion γ :=
  cPkg.map₂ cPkg cPkg f

@[fun_prop]
/--
theorem `uniformContinuous_map₂` / 定理 `uniformContinuous_map₂`

English:
theorem uniformContinuous_map₂
  given: (f : α -> β -> γ)
  statement: UniformContinuous₂ (Completion.map₂ f)
  proof: cPkg.uniformContinuous_map₂ cPkg cPkg f

中文:
定理 uniformContinuous_map₂
  条件: (f : α -> β -> γ)
  结论: UniformContinuous₂ (完备化.map₂ f)
  证明: cPkg.uniformContinuous_map₂ cPkg cPkg f

Depends on / 依赖: cPkg.uniformContinuous_map
-/
theorem uniformContinuous_map₂ (f : α -> β -> γ) : UniformContinuous₂ (Completion.map₂ f) :=
  cPkg.uniformContinuous_map₂ cPkg cPkg f

/--
theorem `continuous_map₂` / 定理 `continuous_map₂`

English:
theorem continuous_map₂
  statement: {δ} [TopologicalSpace δ] {f : α -> β -> γ} {a : δ -> Completion α}
  proof: cPkg.continuous_map₂ cPkg cPkg ha hb

中文:
定理 continuous_map₂
  结论: {δ} [拓扑空间 δ] {f : α -> β -> γ} {a : δ -> 完备化 α}
  证明: cPkg.continuous_map₂ cPkg cPkg ha hb

Depends on / 依赖: cPkg.continuous_map
-/
theorem continuous_map₂ {δ} [TopologicalSpace δ] {f : α -> β -> γ} {a : δ -> Completion α}
    {b : δ -> Completion β} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun d : δ => Completion.map₂ f (a d) (b d) :=
  cPkg.continuous_map₂ cPkg cPkg ha hb

/--
theorem `map₂_coe_coe` / 定理 `map₂_coe_coe`

English:
theorem map₂_coe_coe
  given: (a : α) (b : β) (f : α -> β -> γ) (hf : UniformContinuous₂ f)
  proof: cPkg.map₂_coe_coe cPkg cPkg a b f hf

中文:
定理 map₂_coe_coe
  条件: (a : α) (b : β) (f : α -> β -> γ) (hf : UniformContinuous₂ f)
  证明: cPkg.map₂_coe_coe cPkg cPkg a b f hf

Depends on / 依赖: cPkg.map
-/
theorem map₂_coe_coe (a : α) (b : β) (f : α -> β -> γ) (hf : UniformContinuous₂ f) :
    Completion.map₂ f (a : Completion α) (b : Completion β) = f a b :=
  cPkg.map₂_coe_coe cPkg cPkg a b f hf

end Map₂

end Completion

end UniformSpace
