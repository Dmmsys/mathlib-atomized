/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Lift
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The filter of small sets

This file defines the filter of small sets w.r.t. a filter `f`, which is the largest filter
containing all powersets of members of `f`.

`g` converges to `f.smallSets` if for all `s ∈ f`, eventually we have `g x ⊆ s`.

An example usage is that if `f : ι → E → ℝ` is a family of nonnegative functions with integral 1,
then saying that `fun i ↦ support (f i)` tendsto `(𝓝 0).smallSets` is a way of saying that
`f` tends to the Dirac delta distribution.
-/

assert_not_exists Set.Finite

@[expose] public section

open Filter

open Set

variable {α β : Type*} {ι : Sort*}

namespace Filter

variable {l l' la : Filter α} {lb : Filter β}

/--
Definition of `smallSets` / `smallSets` 的定义

English:
definition smallSets
  signature: (l : Filter α)
  body: l.lift' powerset

中文:
定义 smallSets
  签名: (l : 滤子 α)
  定义体: l.lift' powerset

Depends on / 依赖: l.lift, powerset
-/
def smallSets (l : Filter α) : Filter (Set α) :=
  l.lift' powerset

/--
theorem `smallSets_eq_generate` / 定理 `smallSets_eq_generate`

English:
theorem smallSets_eq_generate
  given: {f : Filter α}
  statement: f.smallSets = generate (powerset '' f.sets)
  proof: by
  simp_rw [generate_eq_biInf, smallSets, iInf_image, Filter.lift', Filter.lift, Function.comp_apply,
    Filter.mem_sets]

中文:
定理 smallSets_eq_generate
  条件: {f : 滤子 α}
  结论: f.smallSets = generate (powerset '' f.sets)
  证明: by
  simp_rw [generate_eq_biInf, smallSets, iInf_image, Filter.lift', Filter.lift, Function.comp_apply,
    Filter.mem_sets]

Depends on / 依赖: Filter, Filter.lift, Filter.mem_sets, Function, Function.comp_apply, comp_apply, generate_eq_biInf, iInf_image, mem_sets, simp_rw, smallSets
-/
theorem smallSets_eq_generate {f : Filter α} : f.smallSets = generate (powerset '' f.sets) := by
  simp_rw [generate_eq_biInf, smallSets, iInf_image, Filter.lift', Filter.lift, Function.comp_apply,
    Filter.mem_sets]

-- TODO: get more properties from the adjunction?
-- TODO: is there a general way to get a lower adjoint for the lift of an upper adjoint?
/--
theorem `bind_smallSets_gc` / 定理 `bind_smallSets_gc`

English:
theorem bind_smallSets_gc
  proof: by
  intro L l
  simp_rw [smallSets_eq_generate, le_generate_iff, image_subset_iff]
  rfl

中文:
定理 bind_smallSets_gc
  证明: by
  intro L l
  simp_rw [smallSets_eq_generate, le_generate_iff, image_subset_iff]
  rfl

Depends on / 依赖: image_subset_iff, le_generate_iff, simp_rw, smallSets_eq_generate
-/
theorem bind_smallSets_gc :
    GaloisConnection (fun L : Filter (Set α) => L.bind principal) smallSets := by
  intro L l
  simp_rw [smallSets_eq_generate, le_generate_iff, image_subset_iff]
  rfl

/--
theorem `HasBasis.smallSets` / 定理 `HasBasis.smallSets`

English:
theorem HasBasis.smallSets
  given: {p : ι -> Prop} {s : ι -> Set α} (h : HasBasis l p s)
  proof: h.lift' monotone_powerset

中文:
定理 有基.smallSets
  条件: {p : ι -> 命题} {s : ι -> 集合 α} (h : 有基 l p s)
  证明: h.lift' monotone_powerset
-/
protected theorem HasBasis.smallSets {p : ι -> Prop} {s : ι -> Set α} (h : HasBasis l p s) :
    HasBasis l.smallSets p fun i => 𝒫 s i :=
  h.lift' monotone_powerset

/--
theorem `hasBasis_smallSets` / 定理 `hasBasis_smallSets`

English:
theorem hasBasis_smallSets
  given: (l : Filter α)
  proof: l.basis_sets.smallSets

中文:
定理 hasBasis_smallSets
  条件: (l : 滤子 α)
  证明: l.basis_sets.smallSets

Depends on / 依赖: basis_sets, l.basis_sets.smallSets, smallSets
-/
theorem hasBasis_smallSets (l : Filter α) :
    HasBasis l.smallSets (fun t : Set α => t in l) powerset :=
  l.basis_sets.smallSets

/--
theorem `Eventually.exists_mem_basis_of_smallSets` / 定理 `Eventually.exists_mem_basis_of_smallSets`

English:
theorem Eventually.exists_mem_basis_of_smallSets
  statement: {p : ι -> Prop} {s : ι -> Set α} {P : Set α -> Prop}
  proof: (h₂.smallSets.eventually_iff.mp h₁).imp fun _i ⟨hpi, hi⟩ => ⟨hpi, hi Subset.rfl⟩

中文:
定理 Eventually.存在_mem_basis_of_smallSets
  结论: {p : ι -> 命题} {s : ι -> 集合 α} {P : 集合 α -> 命题}
  证明: (h₂.smallSets.eventually_iff.mp h₁).imp fun _i ⟨hpi, hi⟩ => ⟨hpi, hi Subset.rfl⟩

Depends on / 依赖: Subset, Subset.rfl, eventually_iff, smallSets, smallSets.eventually_iff.mp
-/
theorem Eventually.exists_mem_basis_of_smallSets {p : ι -> Prop} {s : ι -> Set α} {P : Set α -> Prop}
    (h₁ : forallᶠ t in l.smallSets, P t) (h₂ : HasBasis l p s) : exists i, p i ∧ P (s i) :=
  (h₂.smallSets.eventually_iff.mp h₁).imp fun _i ⟨hpi, hi⟩ => ⟨hpi, hi Subset.rfl⟩

/--
theorem `Frequently.smallSets_of_forall_mem_basis` / 定理 `Frequently.smallSets_of_forall_mem_basis`

English:
theorem Frequently.smallSets_of_forall_mem_basis
  statement: {p : ι -> Prop} {s : ι -> Set α} {P : Set α -> Prop}
  proof: h₂.smallSets.frequently_iff.mpr fun _ hi => ⟨_, Subset.rfl, h₁ _ hi⟩

中文:
定理 Frequently.smallSets_of_对任意_mem_basis
  结论: {p : ι -> 命题} {s : ι -> 集合 α} {P : 集合 α -> 命题}
  证明: h₂.smallSets.frequently_iff.mpr fun _ hi => ⟨_, Subset.rfl, h₁ _ hi⟩

Depends on / 依赖: Subset, Subset.rfl, frequently_iff, smallSets, smallSets.frequently_iff.mpr
-/
theorem Frequently.smallSets_of_forall_mem_basis {p : ι -> Prop} {s : ι -> Set α} {P : Set α -> Prop}
    (h₁ : forall i, p i -> P (s i)) (h₂ : HasBasis l p s) : existsᶠ t in l.smallSets, P t :=
  h₂.smallSets.frequently_iff.mpr fun _ hi => ⟨_, Subset.rfl, h₁ _ hi⟩

/--
theorem `Eventually.exists_mem_of_smallSets` / 定理 `Eventually.exists_mem_of_smallSets`

English:
theorem Eventually.exists_mem_of_smallSets
  statement: {p : Set α -> Prop}
  proof: h.exists_mem_basis_of_smallSets l.basis_sets

中文:
定理 Eventually.存在_mem_of_smallSets
  结论: {p : 集合 α -> 命题}
  证明: h.exists_mem_basis_of_smallSets l.basis_sets

Depends on / 依赖: basis_sets, exists_mem_basis_of_smallSets, h.exists_mem_basis_of_smallSets, l.basis_sets
-/
theorem Eventually.exists_mem_of_smallSets {p : Set α -> Prop}
    (h : forallᶠ t in l.smallSets, p t) : exists s in l, p s :=
  h.exists_mem_basis_of_smallSets l.basis_sets

/-! No `Frequently.smallSets_of_forall_mem (h : ∀ s ∈ l, p s) : ∃ᶠ t in l.smallSets, p t` as
`Filter.frequently_smallSets_mem : ∃ᶠ t in l.smallSets, t ∈ l` is preferred. -/

/--
theorem `tendsto_smallSets_iff` / 定理 `tendsto_smallSets_iff`

English:
theorem tendsto_smallSets_iff
  given: {f : α -> Set β}
  proof: (hasBasis_smallSets lb).tendsto_right_iff

中文:
定理 tendsto_smallSets_iff
  条件: {f : α -> 集合 β}
  证明: (hasBasis_smallSets lb).tendsto_right_iff

Depends on / 依赖: hasBasis_smallSets, tendsto_right_iff
-/
theorem tendsto_smallSets_iff {f : α -> Set β} :
    Tendsto f la lb.smallSets ↔ forall t in lb, forallᶠ x in la, f x subseteq t :=
  (hasBasis_smallSets lb).tendsto_right_iff

/--
theorem `eventually_smallSets` / 定理 `eventually_smallSets`

English:
theorem eventually_smallSets
  given: {p : Set α -> Prop}
  proof: eventually_lift'_iff monotone_powerset

中文:
定理 eventually_smallSets
  条件: {p : 集合 α -> 命题}
  证明: eventually_lift'_iff monotone_powerset

Depends on / 依赖: _iff, eventually_lift, monotone_powerset
-/
theorem eventually_smallSets {p : Set α -> Prop} :
    (forallᶠ s in l.smallSets, p s) ↔ exists s in l, forall t, t subseteq s -> p t :=
  eventually_lift'_iff monotone_powerset

/--
theorem `eventually_smallSets'` / 定理 `eventually_smallSets'`

English:
theorem eventually_smallSets'
  given: {p : Set α -> Prop} (hp : forall ⦃s t⦄, s subseteq t -> p t -> p s)
  proof: eventually_smallSets.trans
    exists_congr fun s => Iff.rfl.and ⟨fun H => H s Subset.rfl, fun hs _t ht => hp ht hs⟩

中文:
定理 eventually_smallSets'
  条件: {p : 集合 α -> 命题} (hp : 对任意 ⦃s t⦄, s subseteq t -> p t -> p s)
  证明: eventually_smallSets.trans
    exists_congr fun s => Iff.rfl.and ⟨fun H => H s Subset.rfl, fun hs _t ht => hp ht hs⟩

Depends on / 依赖: Iff.rfl.and, Subset, Subset.rfl, eventually_smallSets, eventually_smallSets.trans, exists_congr
-/
theorem eventually_smallSets' {p : Set α -> Prop} (hp : forall ⦃s t⦄, s subseteq t -> p t -> p s) :
    (forallᶠ s in l.smallSets, p s) ↔ exists s in l, p s :=
eventually_smallSets.trans
    exists_congr fun s => Iff.rfl.and ⟨fun H => H s Subset.rfl, fun hs _t ht => hp ht hs⟩

/--
theorem `HasBasis.eventually_smallSets` / 定理 `HasBasis.eventually_smallSets`

English:
theorem HasBasis.eventually_smallSets
  statement: {α : Type*} {ι : Sort*} {p : ι -> Prop} {l : Filter α}
  proof: by
  rw [l.eventually_smallSets' hq]; rw [hl.exists_iff hq]

中文:
定理 有基.eventually_smallSets
  结论: {α : 类型} {ι : 类型层*} {p : ι -> 命题} {l : 滤子 α}
  证明: by
  rw [l.eventually_smallSets' hq]; rw [hl.exists_iff hq]

Depends on / 依赖: eventually_smallSets, exists_iff, hl.exists_iff, l.eventually_smallSets
-/
theorem HasBasis.eventually_smallSets {α : Type*} {ι : Sort*} {p : ι -> Prop} {l : Filter α}
    {s : ι -> Set α} {q : Set α -> Prop} {hl : l.HasBasis p s}
    (hq : forall ⦃s t : Set α⦄, s subseteq t -> q t -> q s) :
    (forallᶠ s in l.smallSets, q s) ↔ exists i, p i ∧ q (s i) := by
  rw [l.eventually_smallSets' hq]; rw [hl.exists_iff hq]

/--
theorem `frequently_smallSets` / 定理 `frequently_smallSets`

English:
theorem frequently_smallSets
  given: {p : Set α -> Prop}
  proof: l.hasBasis_smallSets.frequently_iff

中文:
定理 frequently_smallSets
  条件: {p : 集合 α -> 命题}
  证明: l.hasBasis_smallSets.frequently_iff

Depends on / 依赖: frequently_iff, hasBasis_smallSets, l.hasBasis_smallSets.frequently_iff
-/
theorem frequently_smallSets {p : Set α -> Prop} :
    (existsᶠ s in l.smallSets, p s) ↔ forall t in l, exists s, s subseteq t ∧ p s :=
  l.hasBasis_smallSets.frequently_iff

/--
theorem `frequently_smallSets_mem` / 定理 `frequently_smallSets_mem`

English:
theorem frequently_smallSets_mem
  given: (l : Filter α)
  statement: existsᶠ s in l.smallSets, s in l
  proof: frequently_smallSets.2 fun t ht => ⟨t, Subset.rfl, ht⟩

中文:
定理 frequently_smallSets_mem
  条件: (l : 滤子 α)
  结论: 存在ᶠ s in l.smallSets, s in l
  证明: frequently_smallSets.2 fun t ht => ⟨t, Subset.rfl, ht⟩

Depends on / 依赖: Subset, Subset.rfl, frequently_smallSets
-/
theorem frequently_smallSets_mem (l : Filter α) : existsᶠ s in l.smallSets, s in l :=
  frequently_smallSets.2 fun t ht => ⟨t, Subset.rfl, ht⟩

/--
theorem `frequently_smallSets'` / 定理 `frequently_smallSets'`

English:
theorem frequently_smallSets'
  statement: {α : Type*} {l : Filter α} {p : Set α -> Prop}
  proof: by
convert! not_iff_not.mpr l.eventually_smallSets' (p := (¬p ·)) (by tauto)
  simp

中文:
定理 frequently_smallSets'
  结论: {α : 类型} {l : 滤子 α} {p : 集合 α -> 命题}
  证明: by
convert! not_iff_not.mpr l.eventually_smallSets' (p := (¬p ·)) (by tauto)
  simp

Depends on / 依赖: convert, eventually_smallSets, l.eventually_smallSets, not_iff_not, not_iff_not.mpr
-/
theorem frequently_smallSets' {α : Type*} {l : Filter α} {p : Set α -> Prop}
    (hp : forall ⦃s t : Set α⦄, s subseteq t -> p s -> p t) :
    (existsᶠ s in l.smallSets, p s) ↔ forall t in l, p t := by
convert! not_iff_not.mpr l.eventually_smallSets' (p := (¬p ·)) (by tauto)
  simp

/--
theorem `HasBasis.frequently_smallSets` / 定理 `HasBasis.frequently_smallSets`

English:
theorem HasBasis.frequently_smallSets
  statement: {α : Type*} {ι : Sort*} {p : ι -> Prop} {l : Filter α}
  proof: by
  rw [Filter.frequently_smallSets' hq]; rw [hl.forall_iff hq]

@[simp]

中文:
定理 有基.frequently_smallSets
  结论: {α : 类型} {ι : 类型层*} {p : ι -> 命题} {l : 滤子 α}
  证明: by
  rw [Filter.frequently_smallSets' hq]; rw [hl.forall_iff hq]

@[simp]

Depends on / 依赖: Filter, Filter.frequently_smallSets, forall_iff, frequently_smallSets, hl.forall_iff
-/
theorem HasBasis.frequently_smallSets {α : Type*} {ι : Sort*} {p : ι -> Prop} {l : Filter α}
    {s : ι -> Set α} {q : Set α -> Prop} {hl : l.HasBasis p s}
    (hq : forall ⦃s t : Set α⦄, s subseteq t -> q s -> q t) :
    (existsᶠ s in l.smallSets, q s) ↔ forall i, p i -> q (s i) := by
  rw [Filter.frequently_smallSets' hq]; rw [hl.forall_iff hq]

@[simp]
/--
lemma `tendsto_image_smallSets` / 引理 `tendsto_image_smallSets`

English:
lemma tendsto_image_smallSets
  given: {f : α -> β}
  proof: by
  rw [tendsto_smallSets_iff]
  refine forall₂_congr fun u hu => ?_
  rw [eventually_smallSets' fun s t hst ht => (image_mono hst).trans ht]
  simp only [image_subset_iff, exists_mem_subset_iff, mem_map]

alias ⟨_, Tendsto.image_smallSets⟩ := tendsto_image_smallSets

中文:
引理 tendsto_image_smallSets
  条件: {f : α -> β}
  证明: by
  rw [tendsto_smallSets_iff]
  refine forall₂_congr fun u hu => ?_
  rw [eventually_smallSets' fun s t hst ht => (image_mono hst).trans ht]
  simp only [image_subset_iff, exists_mem_subset_iff, mem_map]

alias ⟨_, Tendsto.image_smallSets⟩ := tendsto_image_smallSets

Depends on / 依赖: eventually_smallSets, exists_mem_subset_iff, image_mono, image_subset_iff, mem_map, tendsto_smallSets_iff
-/
lemma tendsto_image_smallSets {f : α -> β} :
    Tendsto (f '' ·) la.smallSets lb.smallSets ↔ Tendsto f la lb := by
  rw [tendsto_smallSets_iff]
  refine forall₂_congr fun u hu => ?_
  rw [eventually_smallSets' fun s t hst ht => (image_mono hst).trans ht]
  simp only [image_subset_iff, exists_mem_subset_iff, mem_map]

alias ⟨_, Tendsto.image_smallSets⟩ := tendsto_image_smallSets

/--
theorem `HasAntitoneBasis.tendsto_smallSets` / 定理 `HasAntitoneBasis.tendsto_smallSets`

English:
theorem HasAntitoneBasis.tendsto_smallSets
  statement: {ι} [Preorder ι] {s : ι -> Set α}
  proof: tendsto_smallSets_iff.2 fun _t ht => hl.eventually_subset ht

@[gcongr, mono]

中文:
定理 有AntitoneBasis.tendsto_smallSets
  结论: {ι} [预序 ι] {s : ι -> 集合 α}
  证明: tendsto_smallSets_iff.2 fun _t ht => hl.eventually_subset ht

@[gcongr, mono]

Depends on / 依赖: eventually_subset, hl.eventually_subset, tendsto_smallSets_iff
-/
theorem HasAntitoneBasis.tendsto_smallSets {ι} [Preorder ι] {s : ι -> Set α}
    (hl : l.HasAntitoneBasis s) : Tendsto s atTop l.smallSets :=
  tendsto_smallSets_iff.2 fun _t ht => hl.eventually_subset ht

@[gcongr, mono]
/--
theorem `monotone_smallSets` / 定理 `monotone_smallSets`

English:
theorem monotone_smallSets
  statement: Monotone (@smallSets α)
  proof: monotone_lift' monotone_id monotone_const

@[simp]

中文:
定理 monotone_smallSets
  结论: 递增 (@smallSets α)
  证明: monotone_lift' monotone_id monotone_const

@[simp]

Depends on / 依赖: monotone_const, monotone_id, monotone_lift
-/
theorem monotone_smallSets : Monotone (@smallSets α) :=
  monotone_lift' monotone_id monotone_const

@[simp]
/--
theorem `smallSets_bot` / 定理 `smallSets_bot`

English:
theorem smallSets_bot
  statement: (⊥ : Filter α).smallSets = pure ∅
  proof: by
  rw [smallSets]; rw [lift'_bot]; rw [powerset_empty]; rw [principal_singleton]
  exact monotone_powerset

@[simp]

中文:
定理 smallSets_bot
  结论: (⊥ : 滤子 α).smallSets = pure ∅
  证明: by
  rw [smallSets]; rw [lift'_bot]; rw [powerset_empty]; rw [principal_singleton]
  exact monotone_powerset

@[simp]

Depends on / 依赖: _bot, monotone_powerset, powerset_empty, principal_singleton, smallSets
-/
theorem smallSets_bot : (⊥ : Filter α).smallSets = pure ∅ := by
  rw [smallSets]; rw [lift'_bot]; rw [powerset_empty]; rw [principal_singleton]
  exact monotone_powerset

@[simp]
/--
theorem `smallSets_top` / 定理 `smallSets_top`

English:
theorem smallSets_top
  statement: (⊤ : Filter α).smallSets = ⊤
  proof: by
  rw [smallSets]; rw [lift'_top]; rw [powerset_univ]; rw [principal_univ]

@[simp]

中文:
定理 smallSets_top
  结论: (⊤ : 滤子 α).smallSets = ⊤
  证明: by
  rw [smallSets]; rw [lift'_top]; rw [powerset_univ]; rw [principal_univ]

@[simp]

Depends on / 依赖: _top, powerset_univ, principal_univ, smallSets
-/
theorem smallSets_top : (⊤ : Filter α).smallSets = ⊤ := by
  rw [smallSets]; rw [lift'_top]; rw [powerset_univ]; rw [principal_univ]

@[simp]
/--
theorem `smallSets_principal` / 定理 `smallSets_principal`

English:
theorem smallSets_principal
  given: (s : Set α)
  statement: (𝓟 s).smallSets = 𝓟 (𝒫 s)
  proof: lift'_principal monotone_powerset

中文:
定理 smallSets_principal
  条件: (s : 集合 α)
  结论: (𝓟 s).smallSets = 𝓟 (𝒫 s)
  证明: lift'_principal monotone_powerset

Depends on / 依赖: _principal, monotone_powerset
-/
theorem smallSets_principal (s : Set α) : (𝓟 s).smallSets = 𝓟 (𝒫 s) :=
  lift'_principal monotone_powerset

/--
theorem `smallSets_comap_eq_comap_image` / 定理 `smallSets_comap_eq_comap_image`

English:
theorem smallSets_comap_eq_comap_image
  given: (l : Filter β) (f : α -> β)
  proof: by
  refine (gc_map_comap _).u_comm_of_l_comm (gc_map_comap _) bind_smallSets_gc bind_smallSets_gc ?_
  simp [Function.comp_def, map_bind, bind_map]

中文:
定理 smallSets_comap_eq_comap_image
  条件: (l : 滤子 β) (f : α -> β)
  证明: by
  refine (gc_map_comap _).u_comm_of_l_comm (gc_map_comap _) bind_smallSets_gc bind_smallSets_gc ?_
  simp [Function.comp_def, map_bind, bind_map]

Depends on / 依赖: Function, Function.comp_def, bind_map, bind_smallSets_gc, comp_def, gc_map_comap, map_bind, u_comm_of_l_comm
-/
theorem smallSets_comap_eq_comap_image (l : Filter β) (f : α -> β) :
    (comap f l).smallSets = comap (image f) l.smallSets := by
  refine (gc_map_comap _).u_comm_of_l_comm (gc_map_comap _) bind_smallSets_gc bind_smallSets_gc ?_
  simp [Function.comp_def, map_bind, bind_map]

/--
theorem `smallSets_comap` / 定理 `smallSets_comap`

English:
theorem smallSets_comap
  given: (l : Filter β) (f : α -> β)
  proof: comap_lift'_eq2 monotone_powerset

中文:
定理 smallSets_comap
  条件: (l : 滤子 β) (f : α -> β)
  证明: comap_lift'_eq2 monotone_powerset

Depends on / 依赖: _eq2, comap_lift, monotone_powerset
-/
theorem smallSets_comap (l : Filter β) (f : α -> β) :
    (comap f l).smallSets = l.lift' (powerset ∘ preimage f) :=
  comap_lift'_eq2 monotone_powerset

/--
theorem `comap_smallSets` / 定理 `comap_smallSets`

English:
theorem comap_smallSets
  given: (l : Filter β) (f : α -> Set β)
  proof: comap_lift'_eq

中文:
定理 comap_smallSets
  条件: (l : 滤子 β) (f : α -> 集合 β)
  证明: comap_lift'_eq

Depends on / 依赖: comap_lift
-/
theorem comap_smallSets (l : Filter β) (f : α -> Set β) :
    comap f l.smallSets = l.lift' (preimage f ∘ powerset) :=
  comap_lift'_eq

/--
theorem `smallSets_iInf` / 定理 `smallSets_iInf`

English:
theorem smallSets_iInf
  given: {f : ι -> Filter α}
  statement: (iInf f).smallSets = ⨅ i, (f i).smallSets
  proof: lift'_iInf_of_map_univ (powerset_inter _ _) powerset_univ

中文:
定理 smallSets_iInf
  条件: {f : ι -> 滤子 α}
  结论: (iInf f).smallSets = ⨅ i, (f i).smallSets
  证明: lift'_iInf_of_map_univ (powerset_inter _ _) powerset_univ

Depends on / 依赖: _iInf_of_map_univ, powerset_inter, powerset_univ
-/
theorem smallSets_iInf {f : ι -> Filter α} : (iInf f).smallSets = ⨅ i, (f i).smallSets :=
  lift'_iInf_of_map_univ (powerset_inter _ _) powerset_univ

/--
theorem `smallSets_inf` / 定理 `smallSets_inf`

English:
theorem smallSets_inf
  given: (l₁ l₂ : Filter α)
  statement: (l₁ ⊓ l₂).smallSets = l₁.smallSets ⊓ l₂.smallSets
  proof: lift'_inf _ _ powerset_inter

中文:
定理 smallSets_inf
  条件: (l₁ l₂ : 滤子 α)
  结论: (l₁ ⊓ l₂).smallSets = l₁.smallSets ⊓ l₂.smallSets
  证明: lift'_inf _ _ powerset_inter

Depends on / 依赖: _inf, powerset_inter
-/
theorem smallSets_inf (l₁ l₂ : Filter α) : (l₁ ⊓ l₂).smallSets = l₁.smallSets ⊓ l₂.smallSets :=
  lift'_inf _ _ powerset_inter

/--
Instance `smallSets_neBot` / 实例 `smallSets_neBot`

English:
instance smallSets_neBot
  signature: (l : Filter α)
  body: by
  refine (lift'_neBot_iff ?_).2 fun _ _ => powerset_nonempty
  exact monotone_powerset

中文:
实例 smallSets_neBot
  签名: (l : 滤子 α)
  定义体: by
  refine (lift'_neBot_iff ?_).2 fun _ _ => powerset_nonempty
  exact monotone_powerset

Depends on / 依赖: _neBot_iff, monotone_powerset, powerset_nonempty
-/
instance smallSets_neBot (l : Filter α) : NeBot l.smallSets := by
  refine (lift'_neBot_iff ?_).2 fun _ _ => powerset_nonempty
  exact monotone_powerset

/--
theorem `Tendsto.smallSets_mono` / 定理 `Tendsto.smallSets_mono`

English:
theorem Tendsto.smallSets_mono
  statement: {s t : α -> Set β} (ht : Tendsto t la lb.smallSets)
  proof: by
  rw [tendsto_smallSets_iff] at ht ⊢
  exact fun u hu => (ht u hu).mp (hst.mono fun _ hst ht => hst.trans ht)

中文:
定理 收敛.smallSets_mono
  结论: {s t : α -> 集合 β} (ht : 收敛 t la lb.smallSets)
  证明: by
  rw [tendsto_smallSets_iff] at ht ⊢
  exact fun u hu => (ht u hu).mp (hst.mono fun _ hst ht => hst.trans ht)

Depends on / 依赖: hst.mono, hst.trans, tendsto_smallSets_iff
-/
theorem Tendsto.smallSets_mono {s t : α -> Set β} (ht : Tendsto t la lb.smallSets)
    (hst : forallᶠ x in la, s x subseteq t x) : Tendsto s la lb.smallSets := by
  rw [tendsto_smallSets_iff] at ht ⊢
  exact fun u hu => (ht u hu).mp (hst.mono fun _ hst ht => hst.trans ht)

/--
theorem `Tendsto.of_smallSets` / 定理 `Tendsto.of_smallSets`

English:
theorem Tendsto.of_smallSets
  statement: {s : α -> Set β} {f : α -> β} (hs : Tendsto s la lb.smallSets)
  proof: fun t ht =>
hf.mp (tendsto_smallSets_iff.mp hs t ht).mono fun _ h₁ h₂ => h₁ h₂

@[simp]

中文:
定理 收敛.of_smallSets
  结论: {s : α -> 集合 β} {f : α -> β} (hs : 收敛 s la lb.smallSets)
  证明: fun t ht =>
hf.mp (tendsto_smallSets_iff.mp hs t ht).mono fun _ h₁ h₂ => h₁ h₂

@[simp]
-/
theorem Tendsto.of_smallSets {s : α -> Set β} {f : α -> β} (hs : Tendsto s la lb.smallSets)
    (hf : forallᶠ x in la, f x in s x) : Tendsto f la lb := fun t ht =>
hf.mp (tendsto_smallSets_iff.mp hs t ht).mono fun _ h₁ h₂ => h₁ h₂

@[simp]
/--
theorem `eventually_smallSets_eventually` / 定理 `eventually_smallSets_eventually`

English:
theorem eventually_smallSets_eventually
  given: {p : α -> Prop}
  proof: calc
    _ ↔ exists s in l, forallᶠ x in l', x in s -> p x :=
      eventually_smallSets' fun _ _ hst ht => ht.mono fun _ hx hs => hx (hst hs)
    _ ↔ exists s in l, exists t in l', forall x, x in t -> x in s -> p x := by simp only [eventually_iff_exists_mem]
    _ ↔ forallᶠ x in l ⊓ l', p x := by simp only [eventually_inf, and_comm, mem_inter_iff, ← and_imp]

@[simp]

中文:
定理 eventually_smallSets_eventually
  条件: {p : α -> 命题}
  证明: calc
    _ ↔ exists s in l, forallᶠ x in l', x in s -> p x :=
      eventually_smallSets' fun _ _ hst ht => ht.mono fun _ hx hs => hx (hst hs)
    _ ↔ exists s in l, exists t in l', forall x, x in t -> x in s -> p x := by simp only [eventually_iff_exists_mem]
    _ ↔ forallᶠ x in l ⊓ l', p x := by simp only [eventually_inf, and_comm, mem_inter_iff, ← and_imp]

@[simp]

Depends on / 依赖: and_comm, and_imp, eventually_iff_exists_mem, eventually_inf, eventually_smallSets, ht.mono, mem_inter_iff
-/
theorem eventually_smallSets_eventually {p : α -> Prop} :
    (forallᶠ s in l.smallSets, forallᶠ x in l', x in s -> p x) ↔ forallᶠ x in l ⊓ l', p x :=
  calc
    _ ↔ exists s in l, forallᶠ x in l', x in s -> p x :=
      eventually_smallSets' fun _ _ hst ht => ht.mono fun _ hx hs => hx (hst hs)
    _ ↔ exists s in l, exists t in l', forall x, x in t -> x in s -> p x := by simp only [eventually_iff_exists_mem]
    _ ↔ forallᶠ x in l ⊓ l', p x := by simp only [eventually_inf, and_comm, mem_inter_iff, ← and_imp]

@[simp]
/--
theorem `eventually_smallSets_forall` / 定理 `eventually_smallSets_forall`

English:
theorem eventually_smallSets_forall
  given: {p : α -> Prop}
  proof: by
  simpa only [inf_top_eq, eventually_top] using @eventually_smallSets_eventually α l ⊤ p

alias ⟨Eventually.of_smallSets, Eventually.smallSets⟩ := eventually_smallSets_forall

@[simp]

中文:
定理 eventually_smallSets_对任意
  条件: {p : α -> 命题}
  证明: by
  simpa only [inf_top_eq, eventually_top] using @eventually_smallSets_eventually α l ⊤ p

alias ⟨Eventually.of_smallSets, Eventually.smallSets⟩ := eventually_smallSets_forall

@[simp]

Depends on / 依赖: eventually_smallSets_eventually, eventually_top, inf_top_eq
-/
theorem eventually_smallSets_forall {p : α -> Prop} :
    (forallᶠ s in l.smallSets, forall x in s, p x) ↔ forallᶠ x in l, p x := by
  simpa only [inf_top_eq, eventually_top] using @eventually_smallSets_eventually α l ⊤ p

alias ⟨Eventually.of_smallSets, Eventually.smallSets⟩ := eventually_smallSets_forall

@[simp]
/--
theorem `eventually_smallSets_subset` / 定理 `eventually_smallSets_subset`

English:
theorem eventually_smallSets_subset
  given: {s : Set α}
  statement: (forallᶠ t in l.smallSets, t subseteq s) ↔ s in l
  proof: eventually_smallSets_forall

中文:
定理 eventually_smallSets_subset
  条件: {s : 集合 α}
  结论: (对任意ᶠ t in l.smallSets, t subseteq s) ↔ s in l
  证明: eventually_smallSets_forall

Depends on / 依赖: eventually_smallSets_forall
-/
theorem eventually_smallSets_subset {s : Set α} : (forallᶠ t in l.smallSets, t subseteq s) ↔ s in l :=
  eventually_smallSets_forall

end Filter
