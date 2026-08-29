/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Data.Rel.Cover
public import Mathlib.Topology.Order

/-!
# Uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* uniform continuity (in this file)
* completeness (in `Cauchy.lean`)
* extension of uniform continuous functions to complete spaces (in `IsUniformEmbedding.lean`)
* totally bounded sets (in `Cauchy.lean`)
* totally bounded complete sets are compact (in `Cauchy.lean`)

A uniform structure on a type `X` is a filter `𝓤 X` on `X × X` satisfying some conditions
which makes it reasonable to say that `∀ᶠ (p : X × X) in 𝓤 X, ...` means
"for all p.1 and p.2 in X close enough, ...". Elements of this filter are called entourages
of `X`. The two main examples are:

* If `X` is a metric space, `V ∈ 𝓤 X ↔ ∃ ε > 0, { p | dist p.1 p.2 < ε } ⊆ V`
* If `G` is an additive topological group, `V ∈ 𝓤 G ↔ ∃ U ∈ 𝓝 (0 : G), {p | p.2 - p.1 ∈ U} ⊆ V`

Those examples are generalizations in two different directions of the elementary example where
`X = ℝ` and `V ∈ 𝓤 ℝ ↔ ∃ ε > 0, { p | |p.2 - p.1| < ε } ⊆ V` which features both the topological
group structure on `ℝ` and its metric space structure.

Each uniform structure on `X` induces a topology on `X` characterized by

> `nhds_eq_comap_uniformity : ∀ {x : X}, 𝓝 x = comap (Prod.mk x) (𝓤 X)`

where `Prod.mk x : X → X × X := (fun y ↦ (x, y))` is the partial evaluation of the product
constructor.

The dictionary with metric spaces includes:
* an upper bound for `dist x y` translates into `(x, y) ∈ V` for some `V ∈ 𝓤 X`
* a ball `ball x r` roughly corresponds to `UniformSpace.ball x V := {y | (x, y) ∈ V}`
  for some `V ∈ 𝓤 X`, but the later is more general (it includes in
  particular both open and closed balls for suitable `V`).
  In particular we have:
  `isOpen_iff_ball_subset {s : Set X} : IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 X, ball x V ⊆ s`

The triangle inequality is abstracted to a statement involving the composition of relations in `X`.
First note that the triangle inequality in a metric space is equivalent to
`∀ (x y z : X) (r r' : ℝ), dist x y ≤ r → dist y z ≤ r' → dist x z ≤ r + r'`.
Then, for any `V` and `W` with type `Set (X × X)`, the composition `V ○ W : Set (X × X)` is
defined as `{ p : X × X | ∃ z, (p.1, z) ∈ V ∧ (z, p.2) ∈ W }`.
In the metric space case, if `V = { p | dist p.1 p.2 ≤ r }` and `W = { p | dist p.1 p.2 ≤ r' }`
then the triangle inequality, as reformulated above, says `V ○ W` is contained in
`{p | dist p.1 p.2 ≤ r + r'}` which is the entourage associated to the radius `r + r'`.
In general we have `mem_ball_comp (h : y ∈ ball x V) (h' : z ∈ ball y W) : z ∈ ball x (V ○ W)`.
Note that this discussion does not depend on any axiom imposed on the uniformity filter,
it is simply captured by the definition of composition.

The uniform space axioms ask the filter `𝓤 X` to satisfy the following:
* every `V ∈ 𝓤 X` contains the diagonal `idRel = { p | p.1 = p.2 }`. This abstracts the fact
  that `dist x x ≤ r` for every non-negative radius `r` in the metric space case and also that
  `x - x` belongs to every neighborhood of zero in the topological group case.
* `V ∈ 𝓤 X → Prod.swap '' V ∈ 𝓤 X`. This is tightly related the fact that `dist x y = dist y x`
  in a metric space, and to continuity of negation in the topological group case.
* `∀ V ∈ 𝓤 X, ∃ W ∈ 𝓤 X, W ○ W ⊆ V`. In the metric space case, it corresponds
  to cutting the radius of a ball in half and applying the triangle inequality.
  In the topological group case, it comes from continuity of addition at `(0, 0)`.

These three axioms are stated more abstractly in the definition below, in terms of
operations on filters, without directly manipulating entourages.

## Main definitions

* `UniformSpace X` is a uniform space structure on a type `X`
* `UniformContinuous f` is a predicate saying a function `f : α → β` between uniform spaces
  is uniformly continuous : `∀ r ∈ 𝓤 β, ∀ᶠ (x : α × α) in 𝓤 α, (f x.1, f x.2) ∈ r`

## Notation

Localized in `Uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`.
This file also uses a lot the notation `○` for composition of relations, seen as terms with
type `SetRel X X`. This notation (defined in the file `Mathlib/Data/Rel.lean`) is
localized in `SetRel`.

## Implementation notes

We use the theory of relations as sets developed in `Mathlib/Data/Rel.lean`.
The relevant definition is `SetRel X X := Set (X × X)`, which is the type of elements of
the uniformity filter `𝓤 X : Filter (X × X)`.

The structure `UniformSpace X` bundles a uniform structure on `X`, a topology on `X` and
an assumption saying those are compatible. This may not seem mathematically reasonable at first,
but is in fact an instance of the forgetful inheritance pattern. See Note [forgetful inheritance]
below.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/

@[expose] public section

open Set Filter Topology

universe u v ua ub uc ud

/-!
### Relations, seen as `SetRel α α`
-/

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

open scoped SetRel

/--
lemma `SetRel.mem_filter_prod_comm` / 引理 `SetRel.mem_filter_prod_comm`

English:
lemma SetRel.mem_filter_prod_comm
  given: (R : SetRel α α) {f g : Filter α} [R.IsSymm]
  proof: by
  rw [← R.inv_eq_self]; rw [SetRel.inv]; rw [← mem_map]; rw [← prod_comm]; rw [← SetRel.inv]; rw [R.inv_eq_self]

中文:
引理 SetRel.mem_filter_prod_comm
  条件: (R : SetRel α α) {f g : Filter α} [R.IsSymm]
  证明: by
  rw [← R.inv_eq_self]; rw [SetRel.inv]; rw [← mem_map]; rw [← prod_comm]; rw [← SetRel.inv]; rw [R.inv_eq_self]

Depends on / 依赖: R.inv_eq_self, SetRel, SetRel.inv, inv_eq_self, mem_map, prod_comm
-/
lemma SetRel.mem_filter_prod_comm (R : SetRel α α) {f g : Filter α} [R.IsSymm] :
    R in f ×ˢ g ↔ R in g ×ˢ f := by
  rw [← R.inv_eq_self]; rw [SetRel.inv]; rw [← mem_map]; rw [← prod_comm]; rw [← SetRel.inv]; rw [R.inv_eq_self]

/--
Definition of `UniformSpace.Core` / `UniformSpace.Core` 的定义

English:
structure UniformSpace.Core
  parameters: (α : Type u)
  axioms and operations (4):
    - uniformity : Filter (α × α)
    - refl : 𝓟 SetRel.id <= uniformity
    - symm : Tendsto Prod.swap uniformity uniformity
    - comp : (uniformity.lift' fun s => s ○ s) <= uniformity

中文:
结构 UniformSpace.Core
  参数: (α : 类型u)
  公理与运算 (4 个):
    - uniformity : Filter (α × α)
    - refl : 𝓟 SetRel.id <= uniformity
    - symm : Tendsto Prod.swap uniformity uniformity
    - comp : (uniformity.lift' fun s => s ○ s) <= uniformity

Depends on / 依赖: _sets, c.comp, mem_lift, monotone_id, monotone_id.relComp, relComp
-/
structure UniformSpace.Core (α : Type u) where
  /-- The uniformity filter. Once `UniformSpace` is defined, `𝓤 α` (`_root_.uniformity`) becomes the
  normal form. -/
  uniformity : Filter (α × α)
  /-- Every set in the uniformity filter includes the diagonal. -/
  refl : 𝓟 SetRel.id <= uniformity
  /-- If `s ∈ uniformity`, then `Prod.swap ⁻¹' s ∈ uniformity`. -/
  symm : Tendsto Prod.swap uniformity uniformity
  /-- For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆ u`. -/
  comp : (uniformity.lift' fun s => s ○ s) <= uniformity

/--
theorem `UniformSpace.Core.comp_mem_uniformity_sets` / 定理 `UniformSpace.Core.comp_mem_uniformity_sets`

English:
theorem UniformSpace.Core.comp_mem_uniformity_sets
  statement: {c : Core α} {s : SetRel α α}
  proof: (mem_lift'_sets <| monotone_id.relComp monotone_id).mp c.comp hs

中文:
定理 UniformSpace.Core.comp_mem_uniformity_sets
  结论: {c : Core α} {s : SetRel α α}
  证明: (mem_lift'_sets <| monotone_id.relComp monotone_id).mp c.comp hs
-/
protected theorem UniformSpace.Core.comp_mem_uniformity_sets {c : Core α} {s : SetRel α α}
    (hs : s in c.uniformity) : exists t in c.uniformity, t ○ t subseteq s :=
(mem_lift'_sets <| monotone_id.relComp monotone_id).mp c.comp hs

/--
Definition of `UniformSpace.Core.mk'` / `UniformSpace.Core.mk'` 的定义

English:
definition UniformSpace.Core.mk'
  signature: {α : Type u} (U : Filter (α × α)) (refl : forall r in U, forall (x), (x, x) in r)
  body: U
  refl _r ru := SetRel.id_subset_iff.2 ⟨refl _ ru⟩
  symm
  comp _r ru := let ⟨_s, hs, hsr⟩ := comp _ ru; mem_of_superset (mem_lift' hs) hsr

中文:
定义 UniformSpace.Core.mk'
  签名: {α : 类型u} (U : Filter (α × α)) (refl : 对任意 r in U, 对任意 (x), (x, x) in r)
  定义体: U
  refl _r ru := SetRel.id_subset_iff.2 ⟨refl _ ru⟩
  symm
  comp _r ru := let ⟨_s, hs, hsr⟩ := comp _ ru; mem_of_superset (mem_lift' hs) hsr
-/
def UniformSpace.Core.mk' {α : Type u} (U : Filter (α × α)) (refl : forall r in U, forall (x), (x, x) in r)
    (symm : forall r in U, Prod.swap ⁻¹' r in U) (comp : forall r in U, exists t in U, t ○ t subseteq r) :
    UniformSpace.Core α where
  uniformity := U
  refl _r ru := SetRel.id_subset_iff.2 ⟨refl _ ru⟩
  symm
  comp _r ru := let ⟨_s, hs, hsr⟩ := comp _ ru; mem_of_superset (mem_lift' hs) hsr

/--
Definition of `UniformSpace.Core.mkOfBasis` / `UniformSpace.Core.mkOfBasis` 的定义

English:
definition UniformSpace.Core.mkOfBasis
  signature: {α : Type u} (B : FilterBasis (α × α))
  body: B.filter
  refl := B.hasBasis.ge_iff.mpr fun _r ru => SetRel.id_subset_iff.2 ⟨refl _ ru⟩
  symm := (B.hasBasis.tendsto_iff B.hasBasis).mpr symm
  comp := ((B.hasBasis.lift' (monotone_id.relComp monotone_id)).le_basis_iff B.hasBasis).2 comp

中文:
定义 UniformSpace.Core.mkOfBasis
  签名: {α : 类型u} (B : FilterBasis (α × α))
  定义体: B.filter
  refl := B.hasBasis.ge_iff.mpr fun _r ru => SetRel.id_subset_iff.2 ⟨refl _ ru⟩
  symm := (B.hasBasis.tendsto_iff B.hasBasis).mpr symm
  comp := ((B.hasBasis.lift' (monotone_id.relComp monotone_id)).le_basis_iff B.hasBasis).2 comp

Depends on / 依赖: B.filter, filter
-/
def UniformSpace.Core.mkOfBasis {α : Type u} (B : FilterBasis (α × α))
    (refl : forall r in B, forall (x), (x, x) in r) (symm : forall r in B, exists t in B, t subseteq Prod.swap ⁻¹' r)
    (comp : forall r in B, exists t in B, t ○ t subseteq r) : UniformSpace.Core α where
  uniformity := B.filter
  refl := B.hasBasis.ge_iff.mpr fun _r ru => SetRel.id_subset_iff.2 ⟨refl _ ru⟩
  symm := (B.hasBasis.tendsto_iff B.hasBasis).mpr symm
  comp := ((B.hasBasis.lift' (monotone_id.relComp monotone_id)).le_basis_iff B.hasBasis).2 comp

/-- A uniform space generates a topological space -/
@[instance_reducible]
/--
Definition of `UniformSpace.Core.toTopologicalSpace` / `UniformSpace.Core.toTopologicalSpace` 的定义

English:
definition UniformSpace.Core.toTopologicalSpace
  signature: {α : Type u} (u : UniformSpace.Core α)
  body: .mkOfNhds fun x => .comap (Prod.mk x) u.uniformity

中文:
定义 UniformSpace.Core.toTopologicalSpace
  签名: {α : 类型u} (u : UniformSpace.Core α)
  定义体: .mkOfNhds fun x => .comap (Prod.mk x) u.uniformity

Depends on / 依赖: Prod.mk, mkOfNhds, u.uniformity, uniformity
-/
def UniformSpace.Core.toTopologicalSpace {α : Type u} (u : UniformSpace.Core α) :
    TopologicalSpace α :=
  .mkOfNhds fun x => .comap (Prod.mk x) u.uniformity

/--
theorem `UniformSpace.Core.ext` / 定理 `UniformSpace.Core.ext`

English:
theorem UniformSpace.Core.ext

中文:
定理 UniformSpace.Core.ext
-/
theorem UniformSpace.Core.ext :
    forall {u₁ u₂ : UniformSpace.Core α}, u₁.uniformity = u₂.uniformity -> u₁ = u₂
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

/--
theorem `UniformSpace.Core.nhds_toTopologicalSpace` / 定理 `UniformSpace.Core.nhds_toTopologicalSpace`

English:
theorem UniformSpace.Core.nhds_toTopologicalSpace
  given: {α : Type u} (u : Core α) (x : α)
  proof: by
  apply TopologicalSpace.nhds_mkOfNhds_of_hasBasis (fun _ => (basis_sets _).comap _)
  · exact fun a U hU => u.refl hU rfl
  · intro a U hU
    rcases u.comp_mem_uniformity_sets hU with ⟨V, hV, hVU⟩
    filter_upwards [preimage_mem_comap hV] with b hb
    filter_upwards [preimage_mem_comap hV] wi

中文:
定理 UniformSpace.Core.nhds_toTopologicalSpace
  条件: {α : 类型u} (u : Core α) (x : α)
  证明: by
  apply TopologicalSpace.nhds_mkOfNhds_of_hasBasis (fun _ => (basis_sets _).comap _)
  · exact fun a U hU => u.refl hU rfl
  · intro a U hU
    rcases u.comp_mem_uniformity_sets hU with ⟨V, hV, hVU⟩
    filter_upwards [preimage_mem_comap hV] with b hb
    filter_upwards [preimage_mem_comap hV] wi

Depends on / 依赖: TopologicalSpace, TopologicalSpace.nhds_mkOfNhds_of_hasBasis, basis_sets, comp_mem_uniformity_sets, filter_upwards, nhds_mkOfNhds_of_hasBasis, preimage_mem_comap, u.comp_mem_uniformity_sets, u.refl
-/
theorem UniformSpace.Core.nhds_toTopologicalSpace {α : Type u} (u : Core α) (x : α) :
    @nhds α u.toTopologicalSpace x = comap (Prod.mk x) u.uniformity := by
  apply TopologicalSpace.nhds_mkOfNhds_of_hasBasis (fun _ => (basis_sets _).comap _)
  · exact fun a U hU => u.refl hU rfl
  · intro a U hU
    rcases u.comp_mem_uniformity_sets hU with ⟨V, hV, hVU⟩
    filter_upwards [preimage_mem_comap hV] with b hb
    filter_upwards [preimage_mem_comap hV] with c hc
    exact hVU ⟨b, hb, hc⟩

-- the topological structure is embedded in the uniform structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `α × α` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
@[wikidata Q652446]
/--
Definition of `UniformSpace` / `UniformSpace` 的定义

English:
class UniformSpace
  parameters: (α : Type u)
  extends: TopologicalSpace α
  axioms and operations (4):
    - uniformity : Filter (α × α)
    - symm : Tendsto Prod.swap uniformity uniformity
    - comp : (uniformity.lift' fun s => s ○ s) <= uniformity
    - nhds_eq_comap_uniformity((x : α)) : 𝓝 x = comap (Prod.mk x) uniformity

中文:
类 UniformSpace
  参数: (α : 类型u)
  继承: TopologicalSpace α
  公理与运算 (4 个):
    - uniformity : Filter (α × α)
    - symm : Tendsto Prod.swap uniformity uniformity
    - comp : (uniformity.lift' fun s => s ○ s) <= uniformity
    - nhds_eq_comap_uniformity((x : α)) : 𝓝 x = comap (Prod.mk x) uniformity
-/
class UniformSpace (α : Type u) extends TopologicalSpace α where
  /-- The uniformity filter. -/
  protected uniformity : Filter (α × α)
  /-- If `s ∈ uniformity`, then `Prod.swap ⁻¹' s ∈ uniformity`. -/
  protected symm : Tendsto Prod.swap uniformity uniformity
  /-- For every set `u ∈ uniformity`, there exists `v ∈ uniformity` such that `v ○ v ⊆ u`. -/
  protected comp : (uniformity.lift' fun s => s ○ s) <= uniformity
  /-- The uniformity agrees with the topology: the neighborhoods filter of each point `x`
  is equal to `Filter.comap (Prod.mk x) (𝓤 α)`. -/
  protected nhds_eq_comap_uniformity (x : α) : 𝓝 x = comap (Prod.mk x) uniformity

/--
Definition of `uniformity` / `uniformity` 的定义

English:
definition uniformity
  signature: (α : Type u) [UniformSpace α]
  body: @UniformSpace.uniformity α _

中文:
定义 uniformity
  签名: (α : 类型u) [UniformSpace α]
  定义体: @UniformSpace.uniformity α _

Depends on / 依赖: UniformSpace, UniformSpace.uniformity, uniformity
-/
def uniformity (α : Type u) [UniformSpace α] : Filter (α × α) :=
  @UniformSpace.uniformity α _

/-- Notation for the uniformity filter with respect to a non-standard `UniformSpace` instance. -/
scoped[Uniformity] notation "𝓤[" u "]" => @uniformity _ u

@[inherit_doc]
scoped[Uniformity] notation "𝓤" => uniformity

open scoped Uniformity

/--
Definition of `UniformSpace.ofCoreEq` / `UniformSpace.ofCoreEq` 的定义

English:
abbreviation UniformSpace.ofCoreEq
  signature: {α : Type u} (u : UniformSpace.Core α) (t : TopologicalSpace α)
  body: u
  toTopologicalSpace := t
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_toTopologicalSpace]

中文:
缩写 UniformSpace.ofCoreEq
  签名: {α : 类型u} (u : UniformSpace.Core α) (t : TopologicalSpace α)
  定义体: u
  toTopologicalSpace := t
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_toTopologicalSpace]
-/
abbrev UniformSpace.ofCoreEq {α : Type u} (u : UniformSpace.Core α) (t : TopologicalSpace α)
    (h : t = u.toTopologicalSpace) : UniformSpace α where
  __ := u
  toTopologicalSpace := t
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_toTopologicalSpace]

/--
Definition of `UniformSpace.ofCore` / `UniformSpace.ofCore` 的定义

English:
abbreviation UniformSpace.ofCore
  signature: {α : Type u} (u : UniformSpace.Core α)
  body: .ofCoreEq u _ rfl

中文:
缩写 UniformSpace.ofCore
  签名: {α : 类型u} (u : UniformSpace.Core α)
  定义体: .ofCoreEq u _ rfl

Depends on / 依赖: ofCoreEq
-/
abbrev UniformSpace.ofCore {α : Type u} (u : UniformSpace.Core α) : UniformSpace α :=
  .ofCoreEq u _ rfl

/--
Definition of `UniformSpace.toCore` / `UniformSpace.toCore` 的定义

English:
abbreviation UniformSpace.toCore
  signature: (u : UniformSpace α)
  body: u
  refl := by
    rintro U hU ⟨x, y⟩ (rfl : x = y)
    have : Prod.mk x ⁻¹' U in 𝓝 x := by
      rw [UniformSpace.nhds_eq_comap_uniformity]
      exact preimage_mem_comap hU
    convert! mem_of_mem_nhds this

中文:
缩写 UniformSpace.toCore
  签名: (u : UniformSpace α)
  定义体: u
  refl := by
    rintro U hU ⟨x, y⟩ (rfl : x = y)
    have : Prod.mk x ⁻¹' U in 𝓝 x := by
      rw [UniformSpace.nhds_eq_comap_uniformity]
      exact preimage_mem_comap hU
    convert! mem_of_mem_nhds this
-/
abbrev UniformSpace.toCore (u : UniformSpace α) : UniformSpace.Core α where
  __ := u
  refl := by
    rintro U hU ⟨x, y⟩ (rfl : x = y)
    have : Prod.mk x ⁻¹' U in 𝓝 x := by
      rw [UniformSpace.nhds_eq_comap_uniformity]
      exact preimage_mem_comap hU
    convert! mem_of_mem_nhds this

/--
theorem `UniformSpace.toCore_toTopologicalSpace` / 定理 `UniformSpace.toCore_toTopologicalSpace`

English:
theorem UniformSpace.toCore_toTopologicalSpace
  given: (u : UniformSpace α)
  proof: TopologicalSpace.ext_nhds fun a => by
    rw [u.nhds_eq_comap_uniformity]; rw [u.toCore.nhds_toTopologicalSpace]

中文:
定理 UniformSpace.toCore_toTopologicalSpace
  条件: (u : UniformSpace α)
  证明: TopologicalSpace.ext_nhds fun a => by
    rw [u.nhds_eq_comap_uniformity]; rw [u.toCore.nhds_toTopologicalSpace]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.ext_nhds, ext_nhds, nhds_eq_comap_uniformity, nhds_toTopologicalSpace, toCore, u.nhds_eq_comap_uniformity, u.toCore.nhds_toTopologicalSpace
-/
theorem UniformSpace.toCore_toTopologicalSpace (u : UniformSpace α) :
    u.toCore.toTopologicalSpace = u.toTopologicalSpace :=
  TopologicalSpace.ext_nhds fun a => by
    rw [u.nhds_eq_comap_uniformity]; rw [u.toCore.nhds_toTopologicalSpace]

/--
lemma `UniformSpace.mem_uniformity_ofCore_iff` / 引理 `UniformSpace.mem_uniformity_ofCore_iff`

English:
lemma UniformSpace.mem_uniformity_ofCore_iff
  given: {u : UniformSpace.Core α} {s : SetRel α α}
  proof: Iff.rfl

@[ext (iff := false)]

中文:
引理 UniformSpace.mem_uniformity_ofCore_iff
  条件: {u : UniformSpace.Core α} {s : SetRel α α}
  证明: Iff.rfl

@[ext (iff := false)]

Depends on / 依赖: Iff.rfl
-/
lemma UniformSpace.mem_uniformity_ofCore_iff {u : UniformSpace.Core α} {s : SetRel α α} :
    s in 𝓤[.ofCore u] ↔ s in u.uniformity :=
  Iff.rfl

@[ext (iff := false)]
/--
theorem `UniformSpace.ext` / 定理 `UniformSpace.ext`

English:
theorem UniformSpace.ext
  given: {u₁ u₂ : UniformSpace α} (h : 𝓤[u₁] = 𝓤[u₂])
  statement: u₁ = u₂
  proof: by
  have : u₁.toTopologicalSpace = u₂.toTopologicalSpace := TopologicalSpace.ext_nhds fun x => by
    rw [u₁.nhds_eq_comap_uniformity]; rw [u₂.nhds_eq_comap_uniformity]
    exact congr_arg (comap _) h
  cases u₁; cases u₂; congr

中文:
定理 UniformSpace.ext
  条件: {u₁ u₂ : UniformSpace α} (h : 𝓤[u₁] = 𝓤[u₂])
  结论: u₁ = u₂
  证明: by
  have : u₁.toTopologicalSpace = u₂.toTopologicalSpace := TopologicalSpace.ext_nhds fun x => by
    rw [u₁.nhds_eq_comap_uniformity]; rw [u₂.nhds_eq_comap_uniformity]
    exact congr_arg (comap _) h
  cases u₁; cases u₂; congr
-/
protected theorem UniformSpace.ext {u₁ u₂ : UniformSpace α} (h : 𝓤[u₁] = 𝓤[u₂]) : u₁ = u₂ := by
  have : u₁.toTopologicalSpace = u₂.toTopologicalSpace := TopologicalSpace.ext_nhds fun x => by
    rw [u₁.nhds_eq_comap_uniformity]; rw [u₂.nhds_eq_comap_uniformity]
    exact congr_arg (comap _) h
  cases u₁; cases u₂; congr

/--
theorem `UniformSpace.ext_iff` / 定理 `UniformSpace.ext_iff`

English:
theorem UniformSpace.ext_iff
  given: {u₁ u₂ : UniformSpace α}
  proof: ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩

中文:
定理 UniformSpace.ext_iff
  条件: {u₁ u₂ : UniformSpace α}
  证明: ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩
-/
protected theorem UniformSpace.ext_iff {u₁ u₂ : UniformSpace α} :
    u₁ = u₂ ↔ forall s, s in 𝓤[u₁] ↔ s in 𝓤[u₂] :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩

/--
theorem `UniformSpace.ofCoreEq_toCore` / 定理 `UniformSpace.ofCoreEq_toCore`

English:
theorem UniformSpace.ofCoreEq_toCore
  statement: (u : UniformSpace α) (t : TopologicalSpace α)
  proof: UniformSpace.ext rfl

中文:
定理 UniformSpace.ofCoreEq_toCore
  结论: (u : UniformSpace α) (t : TopologicalSpace α)
  证明: UniformSpace.ext rfl

Depends on / 依赖: UniformSpace, UniformSpace.ext
-/
theorem UniformSpace.ofCoreEq_toCore (u : UniformSpace α) (t : TopologicalSpace α)
    (h : t = u.toCore.toTopologicalSpace) : .ofCoreEq u.toCore t h = u :=
  UniformSpace.ext rfl

/--
Definition of `UniformSpace.replaceTopology` / `UniformSpace.replaceTopology` 的定义

English:
abbreviation UniformSpace.replaceTopology
  signature: {α : Type*} [i : TopologicalSpace α] (u : UniformSpace α)
  body: u
  toTopologicalSpace := i
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_eq_comap_uniformity]

中文:
缩写 UniformSpace.replaceTopology
  签名: {α : 类型} [i : TopologicalSpace α] (u : UniformSpace α)
  定义体: u
  toTopologicalSpace := i
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_eq_comap_uniformity]
-/
abbrev UniformSpace.replaceTopology {α : Type*} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : UniformSpace α where
  __ := u
  toTopologicalSpace := i
  nhds_eq_comap_uniformity x := by rw [h, u.nhds_eq_comap_uniformity]

/--
theorem `UniformSpace.replaceTopology_eq` / 定理 `UniformSpace.replaceTopology_eq`

English:
theorem UniformSpace.replaceTopology_eq
  statement: {α : Type*} [i : TopologicalSpace α] (u : UniformSpace α)
  proof: UniformSpace.ext rfl

中文:
定理 UniformSpace.replaceTopology_eq
  结论: {α : 类型} [i : TopologicalSpace α] (u : UniformSpace α)
  证明: UniformSpace.ext rfl

Depends on / 依赖: UniformSpace, UniformSpace.ext
-/
theorem UniformSpace.replaceTopology_eq {α : Type*} [i : TopologicalSpace α] (u : UniformSpace α)
    (h : i = u.toTopologicalSpace) : u.replaceTopology h = u :=
  UniformSpace.ext rfl

section UniformSpace

variable [UniformSpace α]

/--
theorem `nhds_eq_comap_uniformity` / 定理 `nhds_eq_comap_uniformity`

English:
theorem nhds_eq_comap_uniformity
  given: {x : α}
  statement: 𝓝 x = (𝓤 α).comap (Prod.mk x)
  proof: UniformSpace.nhds_eq_comap_uniformity x

中文:
定理 nhds_eq_comap_uniformity
  条件: {x : α}
  结论: 𝓝 x = (𝓤 α).comap (Prod.mk x)
  证明: UniformSpace.nhds_eq_comap_uniformity x

Depends on / 依赖: UniformSpace, UniformSpace.nhds_eq_comap_uniformity, nhds_eq_comap_uniformity
-/
theorem nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α).comap (Prod.mk x) :=
  UniformSpace.nhds_eq_comap_uniformity x

/--
theorem `isOpen_uniformity` / 定理 `isOpen_uniformity`

English:
theorem isOpen_uniformity
  given: {s : Set α}
  proof: by
  simp only [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap_prodMk]

中文:
定理 isOpen_uniformity
  条件: {s : Set α}
  证明: by
  simp only [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap_prodMk]

Depends on / 依赖: isOpen_iff_mem_nhds, mem_comap_prodMk, nhds_eq_comap_uniformity
-/
theorem isOpen_uniformity {s : Set α} :
    IsOpen s ↔ forall x in s, { p : α × α | p.1 = x -> p.2 in s } in 𝓤 α := by
  simp only [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap_prodMk]

/--
theorem `refl_le_uniformity` / 定理 `refl_le_uniformity`

English:
theorem refl_le_uniformity
  statement: 𝓟 SetRel.id <= 𝓤 α
  proof: (@UniformSpace.toCore α _).refl

中文:
定理 refl_le_uniformity
  结论: 𝓟 SetRel.id <= 𝓤 α
  证明: (@UniformSpace.toCore α _).refl

Depends on / 依赖: UniformSpace, UniformSpace.toCore, toCore
-/
theorem refl_le_uniformity : 𝓟 SetRel.id <= 𝓤 α :=
  (@UniformSpace.toCore α _).refl

/--
Instance `uniformity.neBot` / 实例 `uniformity.neBot`

English:
instance uniformity.neBot
  signature: [Nonempty α]
  body: diagonal_nonempty.principal_neBot.mono refl_le_uniformity

中文:
实例 uniformity.neBot
  签名: [Nonempty α]
  定义体: diagonal_nonempty.principal_neBot.mono refl_le_uniformity

Depends on / 依赖: diagonal_nonempty, diagonal_nonempty.principal_neBot.mono, principal_neBot, refl_le_uniformity
-/
instance uniformity.neBot [Nonempty α] : NeBot (𝓤 α) :=
  diagonal_nonempty.principal_neBot.mono refl_le_uniformity

/--
theorem `refl_mem_uniformity` / 定理 `refl_mem_uniformity`

English:
theorem refl_mem_uniformity
  given: {x : α} {s : SetRel α α} (h : s in 𝓤 α)
  statement: (x, x) in s
  proof: refl_le_uniformity h rfl

中文:
定理 refl_mem_uniformity
  条件: {x : α} {s : SetRel α α} (h : s in 𝓤 α)
  结论: (x, x) in s
  证明: refl_le_uniformity h rfl

Depends on / 依赖: refl_le_uniformity
-/
theorem refl_mem_uniformity {x : α} {s : SetRel α α} (h : s in 𝓤 α) : (x, x) in s :=
  refl_le_uniformity h rfl

/--
theorem `isRefl_of_mem_uniformity` / 定理 `isRefl_of_mem_uniformity`

English:
theorem isRefl_of_mem_uniformity
  given: {s : SetRel α α} (h : s in 𝓤 α)
  statement: s.IsRefl
  proof: ⟨fun _ => refl_mem_uniformity h⟩

中文:
定理 isRefl_of_mem_uniformity
  条件: {s : SetRel α α} (h : s in 𝓤 α)
  结论: s.IsRefl
  证明: ⟨fun _ => refl_mem_uniformity h⟩

Depends on / 依赖: refl_mem_uniformity
-/
theorem isRefl_of_mem_uniformity {s : SetRel α α} (h : s in 𝓤 α) : s.IsRefl :=
  ⟨fun _ => refl_mem_uniformity h⟩

/--
theorem `mem_uniformity_of_eq` / 定理 `mem_uniformity_of_eq`

English:
theorem mem_uniformity_of_eq
  given: {x y : α} {s : SetRel α α} (h : s in 𝓤 α) (hx : x = y)
  statement: (x, y) in s
  proof: refl_le_uniformity h hx

中文:
定理 mem_uniformity_of_eq
  条件: {x y : α} {s : SetRel α α} (h : s in 𝓤 α) (hx : x = y)
  结论: (x, y) in s
  证明: refl_le_uniformity h hx

Depends on / 依赖: refl_le_uniformity
-/
theorem mem_uniformity_of_eq {x y : α} {s : SetRel α α} (h : s in 𝓤 α) (hx : x = y) : (x, y) in s :=
  refl_le_uniformity h hx

/--
theorem `symm_le_uniformity` / 定理 `symm_le_uniformity`

English:
theorem symm_le_uniformity
  statement: map (@Prod.swap α α) (𝓤 _) <= 𝓤 _
  proof: UniformSpace.symm

中文:
定理 symm_le_uniformity
  结论: map (@Prod.swap α α) (𝓤 _) <= 𝓤 _
  证明: UniformSpace.symm

Depends on / 依赖: UniformSpace, UniformSpace.symm
-/
theorem symm_le_uniformity : map (@Prod.swap α α) (𝓤 _) <= 𝓤 _ :=
  UniformSpace.symm

/--
theorem `comp_le_uniformity` / 定理 `comp_le_uniformity`

English:
theorem comp_le_uniformity
  statement: ((𝓤 α).lift' fun s : SetRel α α => s ○ s) <= 𝓤 α
  proof: UniformSpace.comp

中文:
定理 comp_le_uniformity
  结论: ((𝓤 α).lift' fun s : SetRel α α => s ○ s) <= 𝓤 α
  证明: UniformSpace.comp

Depends on / 依赖: UniformSpace, UniformSpace.comp
-/
theorem comp_le_uniformity : ((𝓤 α).lift' fun s : SetRel α α => s ○ s) <= 𝓤 α :=
  UniformSpace.comp

/--
theorem `lift'_comp_uniformity` / 定理 `lift'_comp_uniformity`

English:
theorem lift'_comp_uniformity
  statement: ((𝓤 α).lift' fun s : SetRel α α => s ○ s) = 𝓤 α
  proof: comp_le_uniformity.antisymm le_lift'.2 fun _s hs => mem_of_superset hs
    have := isRefl_of_mem_uniformity hs; SetRel.left_subset_comp

中文:
定理 lift'_comp_uniformity
  结论: ((𝓤 α).lift' fun s : SetRel α α => s ○ s) = 𝓤 α
  证明: comp_le_uniformity.antisymm le_lift'.2 fun _s hs => mem_of_superset hs
    have := isRefl_of_mem_uniformity hs; SetRel.left_subset_comp
-/
theorem lift'_comp_uniformity : ((𝓤 α).lift' fun s : SetRel α α => s ○ s) = 𝓤 α :=
comp_le_uniformity.antisymm le_lift'.2 fun _s hs => mem_of_superset hs
    have := isRefl_of_mem_uniformity hs; SetRel.left_subset_comp

/--
theorem `tendsto_swap_uniformity` / 定理 `tendsto_swap_uniformity`

English:
theorem tendsto_swap_uniformity
  statement: Tendsto (@Prod.swap α α) (𝓤 α) (𝓤 α)
  proof: symm_le_uniformity

中文:
定理 tendsto_swap_uniformity
  结论: Tendsto (@Prod.swap α α) (𝓤 α) (𝓤 α)
  证明: symm_le_uniformity

Depends on / 依赖: symm_le_uniformity
-/
theorem tendsto_swap_uniformity : Tendsto (@Prod.swap α α) (𝓤 α) (𝓤 α) :=
  symm_le_uniformity

/--
theorem `comp_mem_uniformity_sets` / 定理 `comp_mem_uniformity_sets`

English:
theorem comp_mem_uniformity_sets
  given: {s : SetRel α α} (hs : s in 𝓤 α)
  statement: exists t in 𝓤 α, t ○ t subseteq s
  proof: (mem_lift'_sets <| monotone_id.relComp monotone_id).mp comp_le_uniformity hs

中文:
定理 comp_mem_uniformity_sets
  条件: {s : SetRel α α} (hs : s in 𝓤 α)
  结论: 存在 t in 𝓤 α, t ○ t subseteq s
  证明: (mem_lift'_sets <| monotone_id.relComp monotone_id).mp comp_le_uniformity hs

Depends on / 依赖: _sets, comp_le_uniformity, mem_lift, monotone_id, monotone_id.relComp, relComp
-/
theorem comp_mem_uniformity_sets {s : SetRel α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s :=
(mem_lift'_sets <| monotone_id.relComp monotone_id).mp comp_le_uniformity hs

/--
theorem `Filter.Tendsto.uniformity_trans` / 定理 `Filter.Tendsto.uniformity_trans`

English:
theorem Filter.Tendsto.uniformity_trans
  statement: {l : Filter β} {f₁ f₂ f₃ : β -> α}
  proof: by
  refine le_trans (le_lift'.2 fun s hs => mem_map.2 ?_) comp_le_uniformity
  filter_upwards [mem_map.1 (h₁₂ hs), mem_map.1 (h₂₃ hs)] with x hx₁₂ hx₂₃ using ⟨_, hx₁₂, hx₂₃⟩

中文:
定理 Filter.Tendsto.uniformity_trans
  结论: {l : Filter β} {f₁ f₂ f₃ : β -> α}
  证明: by
  refine le_trans (le_lift'.2 fun s hs => mem_map.2 ?_) comp_le_uniformity
  filter_upwards [mem_map.1 (h₁₂ hs), mem_map.1 (h₂₃ hs)] with x hx₁₂ hx₂₃ using ⟨_, hx₁₂, hx₂₃⟩

Depends on / 依赖: comp_le_uniformity, filter_upwards, le_lift, le_trans, mem_map
-/
theorem Filter.Tendsto.uniformity_trans {l : Filter β} {f₁ f₂ f₃ : β -> α}
    (h₁₂ : Tendsto (fun x => (f₁ x, f₂ x)) l (𝓤 α))
    (h₂₃ : Tendsto (fun x => (f₂ x, f₃ x)) l (𝓤 α)) : Tendsto (fun x => (f₁ x, f₃ x)) l (𝓤 α) := by
  refine le_trans (le_lift'.2 fun s hs => mem_map.2 ?_) comp_le_uniformity
  filter_upwards [mem_map.1 (h₁₂ hs), mem_map.1 (h₂₃ hs)] with x hx₁₂ hx₂₃ using ⟨_, hx₁₂, hx₂₃⟩

/--
theorem `Filter.Tendsto.uniformity_symm` / 定理 `Filter.Tendsto.uniformity_symm`

English:
theorem Filter.Tendsto.uniformity_symm
  given: {l : Filter β} {f : β -> α × α} (h : Tendsto f l (𝓤 α))
  proof: tendsto_swap_uniformity.comp h

中文:
定理 Filter.Tendsto.uniformity_symm
  条件: {l : Filter β} {f : β -> α × α} (h : Tendsto f l (𝓤 α))
  证明: tendsto_swap_uniformity.comp h

Depends on / 依赖: tendsto_swap_uniformity, tendsto_swap_uniformity.comp
-/
theorem Filter.Tendsto.uniformity_symm {l : Filter β} {f : β -> α × α} (h : Tendsto f l (𝓤 α)) :
    Tendsto (fun x => ((f x).2, (f x).1)) l (𝓤 α) :=
  tendsto_swap_uniformity.comp h

/--
theorem `tendsto_diag_uniformity` / 定理 `tendsto_diag_uniformity`

English:
theorem tendsto_diag_uniformity
  given: (f : β -> α) (l : Filter β)
  proof: fun _s hs =>
mem_map.2 univ_mem' fun _ => refl_mem_uniformity hs

中文:
定理 tendsto_diag_uniformity
  条件: (f : β -> α) (l : Filter β)
  证明: fun _s hs =>
mem_map.2 univ_mem' fun _ => refl_mem_uniformity hs
-/
theorem tendsto_diag_uniformity (f : β -> α) (l : Filter β) :
    Tendsto (fun x => (f x, f x)) l (𝓤 α) := fun _s hs =>
mem_map.2 univ_mem' fun _ => refl_mem_uniformity hs

/--
theorem `tendsto_const_uniformity` / 定理 `tendsto_const_uniformity`

English:
theorem tendsto_const_uniformity
  given: {a : α} {f : Filter β}
  statement: Tendsto (fun _ => (a, a)) f (𝓤 α)
  proof: tendsto_diag_uniformity (fun _ => a) f

中文:
定理 tendsto_const_uniformity
  条件: {a : α} {f : Filter β}
  结论: Tendsto (fun _ => (a, a)) f (𝓤 α)
  证明: tendsto_diag_uniformity (fun _ => a) f

Depends on / 依赖: tendsto_diag_uniformity
-/
theorem tendsto_const_uniformity {a : α} {f : Filter β} : Tendsto (fun _ => (a, a)) f (𝓤 α) :=
  tendsto_diag_uniformity (fun _ => a) f

/--
theorem `symm_of_uniformity` / 定理 `symm_of_uniformity`

English:
theorem symm_of_uniformity
  given: {s : SetRel α α} (hs : s in 𝓤 α)
  proof: have : preimage Prod.swap s in 𝓤 α := symm_le_uniformity hs
  ⟨s inter preimage Prod.swap s, inter_mem hs this, ⟨fun _ _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩, inter_subset_left⟩

中文:
定理 symm_of_uniformity
  条件: {s : SetRel α α} (hs : s in 𝓤 α)
  证明: have : preimage Prod.swap s in 𝓤 α := symm_le_uniformity hs
  ⟨s inter preimage Prod.swap s, inter_mem hs this, ⟨fun _ _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩, inter_subset_left⟩

Depends on / 依赖: Prod.swap, inter_mem, inter_subset_left, preimage, symm_le_uniformity
-/
theorem symm_of_uniformity {s : SetRel α α} (hs : s in 𝓤 α) :
    exists t in 𝓤 α, SetRel.IsSymm t ∧ t subseteq s :=
  have : preimage Prod.swap s in 𝓤 α := symm_le_uniformity hs
  ⟨s inter preimage Prod.swap s, inter_mem hs this, ⟨fun _ _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩, inter_subset_left⟩

/--
theorem `comp_symm_of_uniformity` / 定理 `comp_symm_of_uniformity`

English:
theorem comp_symm_of_uniformity
  given: {s : SetRel α α} (hs : s in 𝓤 α)
  proof: let ⟨_t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  let ⟨t', ht', _, ht'₂⟩ := symm_of_uniformity ht₁
  ⟨t', ht', SetRel.symm _, Subset.trans (monotone_id.relComp monotone_id ht'₂) ht₂⟩

中文:
定理 comp_symm_of_uniformity
  条件: {s : SetRel α α} (hs : s in 𝓤 α)
  证明: let ⟨_t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  let ⟨t', ht', _, ht'₂⟩ := symm_of_uniformity ht₁
  ⟨t', ht', SetRel.symm _, Subset.trans (monotone_id.relComp monotone_id ht'₂) ht₂⟩

Depends on / 依赖: SetRel, SetRel.symm, Subset, Subset.trans, comp_mem_uniformity_sets, monotone_id, monotone_id.relComp, relComp, symm_of_uniformity
-/
theorem comp_symm_of_uniformity {s : SetRel α α} (hs : s in 𝓤 α) :
    exists t in 𝓤 α, (forall {a b}, (a, b) in t -> (b, a) in t) ∧ t ○ t subseteq s :=
  let ⟨_t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  let ⟨t', ht', _, ht'₂⟩ := symm_of_uniformity ht₁
  ⟨t', ht', SetRel.symm _, Subset.trans (monotone_id.relComp monotone_id ht'₂) ht₂⟩

/--
theorem `uniformity_le_symm` / 定理 `uniformity_le_symm`

English:
theorem uniformity_le_symm
  statement: 𝓤 α <= map Prod.swap (𝓤 α)
  proof: by
  rw [map_swap_eq_comap_swap]; exact tendsto_swap_uniformity.le_comap

中文:
定理 uniformity_le_symm
  结论: 𝓤 α <= map Prod.swap (𝓤 α)
  证明: by
  rw [map_swap_eq_comap_swap]; exact tendsto_swap_uniformity.le_comap

Depends on / 依赖: le_comap, map_swap_eq_comap_swap, tendsto_swap_uniformity, tendsto_swap_uniformity.le_comap
-/
theorem uniformity_le_symm : 𝓤 α <= map Prod.swap (𝓤 α) := by
  rw [map_swap_eq_comap_swap]; exact tendsto_swap_uniformity.le_comap

/--
theorem `uniformity_eq_symm` / 定理 `uniformity_eq_symm`

English:
theorem uniformity_eq_symm
  statement: 𝓤 α = map Prod.swap (𝓤 α)
  proof: le_antisymm uniformity_le_symm symm_le_uniformity

@[simp]

中文:
定理 uniformity_eq_symm
  结论: 𝓤 α = map Prod.swap (𝓤 α)
  证明: le_antisymm uniformity_le_symm symm_le_uniformity

@[simp]

Depends on / 依赖: le_antisymm, symm_le_uniformity, uniformity_le_symm
-/
theorem uniformity_eq_symm : 𝓤 α = map Prod.swap (𝓤 α) :=
  le_antisymm uniformity_le_symm symm_le_uniformity

@[simp]
/--
theorem `comap_swap_uniformity` / 定理 `comap_swap_uniformity`

English:
theorem comap_swap_uniformity
  statement: comap (@Prod.swap α α) (𝓤 α) = 𝓤 α
  proof: (congr_arg _ uniformity_eq_symm).trans comap_map Prod.swap_injective

中文:
定理 comap_swap_uniformity
  结论: comap (@Prod.swap α α) (𝓤 α) = 𝓤 α
  证明: (congr_arg _ uniformity_eq_symm).trans comap_map Prod.swap_injective

Depends on / 依赖: Prod.swap_injective, comap_map, congr_arg, swap_injective, uniformity_eq_symm
-/
theorem comap_swap_uniformity : comap (@Prod.swap α α) (𝓤 α) = 𝓤 α :=
(congr_arg _ uniformity_eq_symm).trans comap_map Prod.swap_injective

/--
theorem `symmetrize_mem_uniformity` / 定理 `symmetrize_mem_uniformity`

English:
theorem symmetrize_mem_uniformity
  given: {V : SetRel α α} (h : V in 𝓤 α)
  statement: SetRel.symmetrize V in 𝓤 α
  proof: by
  apply (𝓤 α).inter_sets h
  rw [← comap_swap_uniformity]
  exact preimage_mem_comap h

中文:
定理 symmetrize_mem_uniformity
  条件: {V : SetRel α α} (h : V in 𝓤 α)
  结论: SetRel.symmetrize V in 𝓤 α
  证明: by
  apply (𝓤 α).inter_sets h
  rw [← comap_swap_uniformity]
  exact preimage_mem_comap h

Depends on / 依赖: comap_swap_uniformity, inter_sets, preimage_mem_comap
-/
theorem symmetrize_mem_uniformity {V : SetRel α α} (h : V in 𝓤 α) : SetRel.symmetrize V in 𝓤 α := by
  apply (𝓤 α).inter_sets h
  rw [← comap_swap_uniformity]
  exact preimage_mem_comap h

/--
theorem `UniformSpace.hasBasis_symmetric` / 定理 `UniformSpace.hasBasis_symmetric`

English:
theorem UniformSpace.hasBasis_symmetric
  proof: hasBasis_self.2 fun t t_in =>
    ⟨SetRel.symmetrize t, symmetrize_mem_uniformity t_in, inferInstance,
      SetRel.symmetrize_subset_self⟩

中文:
定理 UniformSpace.hasBasis_symmetric
  证明: hasBasis_self.2 fun t t_in =>
    ⟨SetRel.symmetrize t, symmetrize_mem_uniformity t_in, inferInstance,
      SetRel.symmetrize_subset_self⟩

Depends on / 依赖: SetRel, SetRel.symmetrize, SetRel.symmetrize_subset_self, hasBasis_self, symmetrize, symmetrize_mem_uniformity, symmetrize_subset_self, t_in
-/
theorem UniformSpace.hasBasis_symmetric :
    (𝓤 α).HasBasis (fun s : SetRel α α => s in 𝓤 α ∧ SetRel.IsSymm s) id :=
  hasBasis_self.2 fun t t_in =>
    ⟨SetRel.symmetrize t, symmetrize_mem_uniformity t_in, inferInstance,
      SetRel.symmetrize_subset_self⟩

/--
theorem `uniformity_lift_le_swap` / 定理 `uniformity_lift_le_swap`

English:
theorem uniformity_lift_le_swap
  statement: {g : SetRel α α -> Filter β} {f : Filter β} (hg : Monotone g)
  proof: calc
    (𝓤 α).lift g <= (Filter.map (@Prod.swap α α) <| 𝓤 α).lift g :=
      lift_mono uniformity_le_symm le_rfl
    _ <= _ := by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h

中文:
定理 uniformity_lift_le_swap
  结论: {g : SetRel α α -> Filter β} {f : Filter β} (hg : Monotone g)
  证明: calc
    (𝓤 α).lift g <= (Filter.map (@Prod.swap α α) <| 𝓤 α).lift g :=
      lift_mono uniformity_le_symm le_rfl
    _ <= _ := by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h

Depends on / 依赖: Filter, Filter.map, Prod.swap, image_swap_eq_preimage_swap, le_rfl, lift_mono, map_lift_eq2, uniformity_le_symm
-/
theorem uniformity_lift_le_swap {g : SetRel α α -> Filter β} {f : Filter β} (hg : Monotone g)
    (h : ((𝓤 α).lift fun s => g (preimage Prod.swap s)) <= f) : (𝓤 α).lift g <= f :=
  calc
    (𝓤 α).lift g <= (Filter.map (@Prod.swap α α) <| 𝓤 α).lift g :=
      lift_mono uniformity_le_symm le_rfl
    _ <= _ := by rw [map_lift_eq2 hg, image_swap_eq_preimage_swap]; exact h

/--
theorem `uniformity_lift_le_comp` / 定理 `uniformity_lift_le_comp`

English:
theorem uniformity_lift_le_comp
  given: {f : SetRel α α -> Filter β} (h : Monotone f)
  proof: calc
    ((𝓤 α).lift fun s => f (s ○ s)) = ((𝓤 α).lift' fun s : SetRel α α => s ○ s).lift f := by
      rw [lift_lift'_assoc]
      · exact monotone_id.relComp monotone_id
      · exact h
    _ <= (𝓤 α).lift f := lift_mono comp_le_uniformity le_rfl

中文:
定理 uniformity_lift_le_comp
  条件: {f : SetRel α α -> Filter β} (h : Monotone f)
  证明: calc
    ((𝓤 α).lift fun s => f (s ○ s)) = ((𝓤 α).lift' fun s : SetRel α α => s ○ s).lift f := by
      rw [lift_lift'_assoc]
      · exact monotone_id.relComp monotone_id
      · exact h
    _ <= (𝓤 α).lift f := lift_mono comp_le_uniformity le_rfl

Depends on / 依赖: SetRel, _assoc, comp_le_uniformity, le_rfl, lift_lift, lift_mono, monotone_id, monotone_id.relComp, relComp
-/
theorem uniformity_lift_le_comp {f : SetRel α α -> Filter β} (h : Monotone f) :
    ((𝓤 α).lift fun s => f (s ○ s)) <= (𝓤 α).lift f :=
  calc
    ((𝓤 α).lift fun s => f (s ○ s)) = ((𝓤 α).lift' fun s : SetRel α α => s ○ s).lift f := by
      rw [lift_lift'_assoc]
      · exact monotone_id.relComp monotone_id
      · exact h
    _ <= (𝓤 α).lift f := lift_mono comp_le_uniformity le_rfl

/--
theorem `comp3_mem_uniformity` / 定理 `comp3_mem_uniformity`

English:
theorem comp3_mem_uniformity
  given: {s : SetRel α α} (hs : s in 𝓤 α)
  statement: exists t in 𝓤 α, t ○ (t ○ t) subseteq s
  proof: let ⟨_t', ht', ht's⟩ := comp_mem_uniformity_sets hs
  let ⟨t, ht, htt'⟩ := comp_mem_uniformity_sets ht'
  have := isRefl_of_mem_uniformity ht
  ⟨t, ht, (SetRel.comp_subset_comp (SetRel.left_subset_comp.trans htt') htt').trans ht's⟩

中文:
定理 comp3_mem_uniformity
  条件: {s : SetRel α α} (hs : s in 𝓤 α)
  结论: 存在 t in 𝓤 α, t ○ (t ○ t) subseteq s
  证明: let ⟨_t', ht', ht's⟩ := comp_mem_uniformity_sets hs
  let ⟨t, ht, htt'⟩ := comp_mem_uniformity_sets ht'
  have := isRefl_of_mem_uniformity ht
  ⟨t, ht, (SetRel.comp_subset_comp (SetRel.left_subset_comp.trans htt') htt').trans ht's⟩

Depends on / 依赖: SetRel, SetRel.comp_subset_comp, SetRel.left_subset_comp.trans, comp_mem_uniformity_sets, comp_subset_comp, isRefl_of_mem_uniformity, left_subset_comp
-/
theorem comp3_mem_uniformity {s : SetRel α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, t ○ (t ○ t) subseteq s :=
  let ⟨_t', ht', ht's⟩ := comp_mem_uniformity_sets hs
  let ⟨t, ht, htt'⟩ := comp_mem_uniformity_sets ht'
  have := isRefl_of_mem_uniformity ht
  ⟨t, ht, (SetRel.comp_subset_comp (SetRel.left_subset_comp.trans htt') htt').trans ht's⟩

/--
theorem `comp_le_uniformity3` / 定理 `comp_le_uniformity3`

English:
theorem comp_le_uniformity3
  statement: ((𝓤 α).lift' fun s : SetRel α α => s ○ (s ○ s)) <= 𝓤 α
  proof: fun _ h =>
  let ⟨_t, htU, ht⟩ := comp3_mem_uniformity h
  mem_of_superset (mem_lift' htU) ht

中文:
定理 comp_le_uniformity3
  结论: ((𝓤 α).lift' fun s : SetRel α α => s ○ (s ○ s)) <= 𝓤 α
  证明: fun _ h =>
  let ⟨_t, htU, ht⟩ := comp3_mem_uniformity h
  mem_of_superset (mem_lift' htU) ht
-/
theorem comp_le_uniformity3 : ((𝓤 α).lift' fun s : SetRel α α => s ○ (s ○ s)) <= 𝓤 α := fun _ h =>
  let ⟨_t, htU, ht⟩ := comp3_mem_uniformity h
  mem_of_superset (mem_lift' htU) ht

/--
theorem `comp_symm_mem_uniformity_sets` / 定理 `comp_symm_mem_uniformity_sets`

English:
theorem comp_symm_mem_uniformity_sets
  given: {s : SetRel α α} (hs : s in 𝓤 α)
  proof: by
  obtain ⟨w, w_in, w_sub⟩ : exists w in 𝓤 α, w ○ w subseteq s := comp_mem_uniformity_sets hs
  use SetRel.symmetrize w, symmetrize_mem_uniformity w_in, inferInstance
  have : SetRel.symmetrize w subseteq w := SetRel.symmetrize_subset_self
  calc SetRel.symmetrize w ○ SetRel.symmetrize w
    _ sub

中文:
定理 comp_symm_mem_uniformity_sets
  条件: {s : SetRel α α} (hs : s in 𝓤 α)
  证明: by
  obtain ⟨w, w_in, w_sub⟩ : exists w in 𝓤 α, w ○ w subseteq s := comp_mem_uniformity_sets hs
  use SetRel.symmetrize w, symmetrize_mem_uniformity w_in, inferInstance
  have : SetRel.symmetrize w subseteq w := SetRel.symmetrize_subset_self
  calc SetRel.symmetrize w ○ SetRel.symmetrize w
    _ sub

Depends on / 依赖: SetRel, SetRel.symmetrize, SetRel.symmetrize_subset_self, comp_mem_uniformity_sets, subseteq, symmetrize, symmetrize_mem_uniformity, symmetrize_subset_self, w_in, w_sub
-/
theorem comp_symm_mem_uniformity_sets {s : SetRel α α} (hs : s in 𝓤 α) :
    exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s := by
  obtain ⟨w, w_in, w_sub⟩ : exists w in 𝓤 α, w ○ w subseteq s := comp_mem_uniformity_sets hs
  use SetRel.symmetrize w, symmetrize_mem_uniformity w_in, inferInstance
  have : SetRel.symmetrize w subseteq w := SetRel.symmetrize_subset_self
  calc SetRel.symmetrize w ○ SetRel.symmetrize w
    _ subseteq w ○ w := by gcongr
    _ subseteq s := w_sub

/--
theorem `subset_comp_self_of_mem_uniformity` / 定理 `subset_comp_self_of_mem_uniformity`

English:
theorem subset_comp_self_of_mem_uniformity
  given: {s : SetRel α α} (h : s in 𝓤 α)
  statement: s subseteq s ○ s
  proof: have := isRefl_of_mem_uniformity h; SetRel.left_subset_comp

中文:
定理 subset_comp_self_of_mem_uniformity
  条件: {s : SetRel α α} (h : s in 𝓤 α)
  结论: s subseteq s ○ s
  证明: have := isRefl_of_mem_uniformity h; SetRel.left_subset_comp

Depends on / 依赖: SetRel, SetRel.left_subset_comp, isRefl_of_mem_uniformity, left_subset_comp
-/
theorem subset_comp_self_of_mem_uniformity {s : SetRel α α} (h : s in 𝓤 α) : s subseteq s ○ s :=
  have := isRefl_of_mem_uniformity h; SetRel.left_subset_comp

/--
theorem `comp_comp_symm_mem_uniformity_sets` / 定理 `comp_comp_symm_mem_uniformity_sets`

English:
theorem comp_comp_symm_mem_uniformity_sets
  given: {s : SetRel α α} (hs : s in 𝓤 α)
  proof: by
  rcases comp_symm_mem_uniformity_sets hs with ⟨w, w_in, _, w_sub⟩
  rcases comp_symm_mem_uniformity_sets w_in with ⟨t, t_in, t_symm, t_sub⟩
  use t, t_in, t_symm
  have : t subseteq t ○ t := subset_comp_self_of_mem_uniformity t_in
  calc
    t ○ t ○ t subseteq w ○ (t ○ t) := by gcongr
    _ subs

中文:
定理 comp_comp_symm_mem_uniformity_sets
  条件: {s : SetRel α α} (hs : s in 𝓤 α)
  证明: by
  rcases comp_symm_mem_uniformity_sets hs with ⟨w, w_in, _, w_sub⟩
  rcases comp_symm_mem_uniformity_sets w_in with ⟨t, t_in, t_symm, t_sub⟩
  use t, t_in, t_symm
  have : t subseteq t ○ t := subset_comp_self_of_mem_uniformity t_in
  calc
    t ○ t ○ t subseteq w ○ (t ○ t) := by gcongr
    _ subs

Depends on / 依赖: comp_symm_mem_uniformity_sets, subset_comp_self_of_mem_uniformity, subseteq, t_in, t_sub, t_symm, w_in, w_sub
-/
theorem comp_comp_symm_mem_uniformity_sets {s : SetRel α α} (hs : s in 𝓤 α) :
    exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t ○ t subseteq s := by
  rcases comp_symm_mem_uniformity_sets hs with ⟨w, w_in, _, w_sub⟩
  rcases comp_symm_mem_uniformity_sets w_in with ⟨t, t_in, t_symm, t_sub⟩
  use t, t_in, t_symm
  have : t subseteq t ○ t := subset_comp_self_of_mem_uniformity t_in
  calc
    t ○ t ○ t subseteq w ○ (t ○ t) := by gcongr
    _ subseteq w ○ w := by gcongr
    _ subseteq s := w_sub

/-!
### Balls in uniform spaces
-/

namespace UniformSpace

/--
Definition of `ball` / `ball` 的定义

English:
definition ball
  signature: (x : β) (V : Set (β × β))
  body: Prod.mk x ⁻¹' V

中文:
定义 ball
  签名: (x : β) (V : Set (β × β))
  定义体: Prod.mk x ⁻¹' V

Depends on / 依赖: Prod.mk
-/
def ball (x : β) (V : Set (β × β)) : Set β := Prod.mk x ⁻¹' V

open UniformSpace (ball)

/--
lemma `mem_ball_self` / 引理 `mem_ball_self`

English:
lemma mem_ball_self
  given: (x : α) {V : SetRel α α}
  statement: V in 𝓤 α -> x in ball x V
  proof: refl_mem_uniformity

中文:
引理 mem_ball_self
  条件: (x : α) {V : SetRel α α}
  结论: V in 𝓤 α -> x in ball x V
  证明: refl_mem_uniformity

Depends on / 依赖: refl_mem_uniformity
-/
lemma mem_ball_self (x : α) {V : SetRel α α} : V in 𝓤 α -> x in ball x V := refl_mem_uniformity

/--
theorem `mem_ball_comp` / 定理 `mem_ball_comp`

English:
theorem mem_ball_comp
  given: {V W : Set (β × β)} {x y z} (h : y in ball x V) (h' : z in ball y W)
  proof: SetRel.prodMk_mem_comp h h'

中文:
定理 mem_ball_comp
  条件: {V W : Set (β × β)} {x y z} (h : y in ball x V) (h' : z in ball y W)
  证明: SetRel.prodMk_mem_comp h h'

Depends on / 依赖: SetRel, SetRel.prodMk_mem_comp, prodMk_mem_comp
-/
theorem mem_ball_comp {V W : Set (β × β)} {x y z} (h : y in ball x V) (h' : z in ball y W) :
    z in ball x (V ○ W) :=
  SetRel.prodMk_mem_comp h h'

/--
theorem `ball_subset_of_comp_subset` / 定理 `ball_subset_of_comp_subset`

English:
theorem ball_subset_of_comp_subset
  given: {V W : Set (β × β)} {x y} (h : x in ball y W) (h' : W ○ W subseteq V)
  proof: fun _z z_in => h' (mem_ball_comp h z_in)

中文:
定理 ball_subset_of_comp_subset
  条件: {V W : Set (β × β)} {x y} (h : x in ball y W) (h' : W ○ W subseteq V)
  证明: fun _z z_in => h' (mem_ball_comp h z_in)

Depends on / 依赖: mem_ball_comp, z_in
-/
theorem ball_subset_of_comp_subset {V W : Set (β × β)} {x y} (h : x in ball y W) (h' : W ○ W subseteq V) :
    ball x W subseteq ball y V := fun _z z_in => h' (mem_ball_comp h z_in)

/--
theorem `ball_mono` / 定理 `ball_mono`

English:
theorem ball_mono
  given: {V W : Set (β × β)} (h : V subseteq W) (x : β)
  statement: ball x V subseteq ball x W
  proof: preimage_mono h

中文:
定理 ball_mono
  条件: {V W : Set (β × β)} (h : V subseteq W) (x : β)
  结论: ball x V subseteq ball x W
  证明: preimage_mono h

Depends on / 依赖: preimage_mono
-/
theorem ball_mono {V W : Set (β × β)} (h : V subseteq W) (x : β) : ball x V subseteq ball x W :=
  preimage_mono h

/--
theorem `ball_inter` / 定理 `ball_inter`

English:
theorem ball_inter
  given: (x : β) (V W : Set (β × β))
  statement: ball x (V inter W) = ball x V inter ball x W
  proof: preimage_inter

中文:
定理 ball_inter
  条件: (x : β) (V W : Set (β × β))
  结论: ball x (V inter W) = ball x V inter ball x W
  证明: preimage_inter

Depends on / 依赖: preimage_inter
-/
theorem ball_inter (x : β) (V W : Set (β × β)) : ball x (V inter W) = ball x V inter ball x W :=
  preimage_inter

/--
theorem `ball_inter_left` / 定理 `ball_inter_left`

English:
theorem ball_inter_left
  given: (x : β) (V W : Set (β × β))
  statement: ball x (V inter W) subseteq ball x V
  proof: ball_mono inter_subset_left x

中文:
定理 ball_inter_left
  条件: (x : β) (V W : Set (β × β))
  结论: ball x (V inter W) subseteq ball x V
  证明: ball_mono inter_subset_left x

Depends on / 依赖: ball_mono, inter_subset_left
-/
theorem ball_inter_left (x : β) (V W : Set (β × β)) : ball x (V inter W) subseteq ball x V :=
  ball_mono inter_subset_left x

/--
theorem `ball_inter_right` / 定理 `ball_inter_right`

English:
theorem ball_inter_right
  given: (x : β) (V W : Set (β × β))
  statement: ball x (V inter W) subseteq ball x W
  proof: ball_mono inter_subset_right x

中文:
定理 ball_inter_right
  条件: (x : β) (V W : Set (β × β))
  结论: ball x (V inter W) subseteq ball x W
  证明: ball_mono inter_subset_right x

Depends on / 依赖: ball_mono, inter_subset_right
-/
theorem ball_inter_right (x : β) (V W : Set (β × β)) : ball x (V inter W) subseteq ball x W :=
  ball_mono inter_subset_right x

/--
theorem `ball_iInter` / 定理 `ball_iInter`

English:
theorem ball_iInter
  given: {x : β} {V : ι -> Set (β × β)}
  statement: ball x (⋂ i, V i) = ⋂ i, ball x (V i)
  proof: preimage_iInter

中文:
定理 ball_iInter
  条件: {x : β} {V : ι -> Set (β × β)}
  结论: ball x (⋂ i, V i) = ⋂ i, ball x (V i)
  证明: preimage_iInter

Depends on / 依赖: preimage_iInter
-/
theorem ball_iInter {x : β} {V : ι -> Set (β × β)} : ball x (⋂ i, V i) = ⋂ i, ball x (V i) :=
  preimage_iInter

/--
theorem `mem_ball_symmetry` / 定理 `mem_ball_symmetry`

English:
theorem mem_ball_symmetry
  given: {V : SetRel β β} [V.IsSymm] {x y}
  statement: x in ball y V ↔ y in ball x V
  proof: V.comm

中文:
定理 mem_ball_symmetry
  条件: {V : SetRel β β} [V.IsSymm] {x y}
  结论: x in ball y V ↔ y in ball x V
  证明: V.comm

Depends on / 依赖: V.comm
-/
theorem mem_ball_symmetry {V : SetRel β β} [V.IsSymm] {x y} : x in ball y V ↔ y in ball x V := V.comm

/--
theorem `ball_eq_of_symmetry` / 定理 `ball_eq_of_symmetry`

English:
theorem ball_eq_of_symmetry
  given: {V : SetRel β β} [V.IsSymm] {x}
  statement: ball x V = { y | (y, x) in V }
  proof: by
  ext y
  rw [mem_ball_symmetry]
  exact Iff.rfl

中文:
定理 ball_eq_of_symmetry
  条件: {V : SetRel β β} [V.IsSymm] {x}
  结论: ball x V = { y | (y, x) in V }
  证明: by
  ext y
  rw [mem_ball_symmetry]
  exact Iff.rfl

Depends on / 依赖: Iff.rfl, mem_ball_symmetry
-/
theorem ball_eq_of_symmetry {V : SetRel β β} [V.IsSymm] {x} : ball x V = { y | (y, x) in V } := by
  ext y
  rw [mem_ball_symmetry]
  exact Iff.rfl

/--
theorem `mem_comp_of_mem_ball` / 定理 `mem_comp_of_mem_ball`

English:
theorem mem_comp_of_mem_ball
  statement: {V W : SetRel β β} {x y z : β} [V.IsSymm] (hx : x in ball z V)
  proof: by
  rw [mem_ball_symmetry] at hx
  exact ⟨z, hx, hy⟩

中文:
定理 mem_comp_of_mem_ball
  结论: {V W : SetRel β β} {x y z : β} [V.IsSymm] (hx : x in ball z V)
  证明: by
  rw [mem_ball_symmetry] at hx
  exact ⟨z, hx, hy⟩

Depends on / 依赖: mem_ball_symmetry
-/
theorem mem_comp_of_mem_ball {V W : SetRel β β} {x y z : β} [V.IsSymm] (hx : x in ball z V)
    (hy : y in ball z W) : (x, y) in V ○ W := by
  rw [mem_ball_symmetry] at hx
  exact ⟨z, hx, hy⟩

/--
theorem `mem_comp_comp` / 定理 `mem_comp_comp`

English:
theorem mem_comp_comp
  given: {V W M : SetRel β β} [W.IsSymm] {p : β × β}
  proof: by
  obtain ⟨x, y⟩ := p
  constructor
  · rintro ⟨z, ⟨w, hpw, hwz⟩, hzy⟩
    exact ⟨(w, z), ⟨hpw, by rwa [mem_ball_symmetry]⟩, hwz⟩
  · rintro ⟨⟨w, z⟩, ⟨w_in, z_in⟩, hwz⟩
    rw [mem_ball_symmetry] at z_in
    exact ⟨z, ⟨w, w_in, hwz⟩, z_in⟩

中文:
定理 mem_comp_comp
  条件: {V W M : SetRel β β} [W.IsSymm] {p : β × β}
  证明: by
  obtain ⟨x, y⟩ := p
  constructor
  · rintro ⟨z, ⟨w, hpw, hwz⟩, hzy⟩
    exact ⟨(w, z), ⟨hpw, by rwa [mem_ball_symmetry]⟩, hwz⟩
  · rintro ⟨⟨w, z⟩, ⟨w_in, z_in⟩, hwz⟩
    rw [mem_ball_symmetry] at z_in
    exact ⟨z, ⟨w, w_in, hwz⟩, z_in⟩

Depends on / 依赖: mem_ball_symmetry, w_in, z_in
-/
theorem mem_comp_comp {V W M : SetRel β β} [W.IsSymm] {p : β × β} :
    p in V ○ M ○ W ↔ (ball p.1 V ×ˢ ball p.2 W inter M).Nonempty := by
  obtain ⟨x, y⟩ := p
  constructor
  · rintro ⟨z, ⟨w, hpw, hwz⟩, hzy⟩
    exact ⟨(w, z), ⟨hpw, by rwa [mem_ball_symmetry]⟩, hwz⟩
  · rintro ⟨⟨w, z⟩, ⟨w_in, z_in⟩, hwz⟩
    rw [mem_ball_symmetry] at z_in
    exact ⟨z, ⟨w, w_in, hwz⟩, z_in⟩

/--
lemma `isCover_iff_subset_iUnion_ball` / 引理 `isCover_iff_subset_iUnion_ball`

English:
lemma isCover_iff_subset_iUnion_ball
  given: {U : SetRel β β} [U.IsSymm] {s N : Set β}
  proof: by
  simp [SetRel.IsCover, subset_def, ball, U.comm]

alias ⟨_root_.SetRel.IsCover.subset_iUnion_ball, _root_.SetRel.IsCover.of_subset_iUnion_ball⟩ :=
  isCover_iff_subset_iUnion_ball

中文:
引理 isCover_iff_subset_iUnion_ball
  条件: {U : SetRel β β} [U.IsSymm] {s N : Set β}
  证明: by
  simp [SetRel.IsCover, subset_def, ball, U.comm]

alias ⟨_root_.SetRel.IsCover.subset_iUnion_ball, _root_.SetRel.IsCover.of_subset_iUnion_ball⟩ :=
  isCover_iff_subset_iUnion_ball

Depends on / 依赖: IsCover, SetRel, SetRel.IsCover, U.comm, subset_def
-/
lemma isCover_iff_subset_iUnion_ball {U : SetRel β β} [U.IsSymm] {s N : Set β} :
    U.IsCover s N ↔ s subseteq ⋃ y in N, ball y U := by
  simp [SetRel.IsCover, subset_def, ball, U.comm]

alias ⟨_root_.SetRel.IsCover.subset_iUnion_ball, _root_.SetRel.IsCover.of_subset_iUnion_ball⟩ :=
  isCover_iff_subset_iUnion_ball

end UniformSpace

/-!
### Neighborhoods in uniform spaces
-/

open UniformSpace

/--
theorem `mem_nhds_uniformity_iff_right` / 定理 `mem_nhds_uniformity_iff_right`

English:
theorem mem_nhds_uniformity_iff_right
  given: {x : α} {s : Set α}
  proof: by
  simp only [nhds_eq_comap_uniformity, mem_comap_prodMk]

中文:
定理 mem_nhds_uniformity_iff_right
  条件: {x : α} {s : Set α}
  证明: by
  simp only [nhds_eq_comap_uniformity, mem_comap_prodMk]

Depends on / 依赖: mem_comap_prodMk, nhds_eq_comap_uniformity
-/
theorem mem_nhds_uniformity_iff_right {x : α} {s : Set α} :
    s in 𝓝 x ↔ { p : α × α | p.1 = x -> p.2 in s } in 𝓤 α := by
  simp only [nhds_eq_comap_uniformity, mem_comap_prodMk]

/--
theorem `mem_nhds_uniformity_iff_left` / 定理 `mem_nhds_uniformity_iff_left`

English:
theorem mem_nhds_uniformity_iff_left
  given: {x : α} {s : Set α}
  proof: by
  rw [uniformity_eq_symm]; rw [mem_nhds_uniformity_iff_right]
  simp only [mem_map, preimage_ofPred_eq, Prod.snd_swap, Prod.fst_swap]

中文:
定理 mem_nhds_uniformity_iff_left
  条件: {x : α} {s : Set α}
  证明: by
  rw [uniformity_eq_symm]; rw [mem_nhds_uniformity_iff_right]
  simp only [mem_map, preimage_ofPred_eq, Prod.snd_swap, Prod.fst_swap]

Depends on / 依赖: Prod.fst_swap, Prod.snd_swap, fst_swap, mem_map, mem_nhds_uniformity_iff_right, preimage_ofPred_eq, snd_swap, uniformity_eq_symm
-/
theorem mem_nhds_uniformity_iff_left {x : α} {s : Set α} :
    s in 𝓝 x ↔ { p : α × α | p.2 = x -> p.1 in s } in 𝓤 α := by
  rw [uniformity_eq_symm]; rw [mem_nhds_uniformity_iff_right]
  simp only [mem_map, preimage_ofPred_eq, Prod.snd_swap, Prod.fst_swap]

/--
theorem `nhdsWithin_eq_comap_uniformity_of_mem` / 定理 `nhdsWithin_eq_comap_uniformity_of_mem`

English:
theorem nhdsWithin_eq_comap_uniformity_of_mem
  given: {x : α} {T : Set α} (hx : x in T) (S : Set α)
  proof: by
  simp [nhdsWithin, nhds_eq_comap_uniformity, hx]

中文:
定理 nhdsWithin_eq_comap_uniformity_of_mem
  条件: {x : α} {T : Set α} (hx : x in T) (S : Set α)
  证明: by
  simp [nhdsWithin, nhds_eq_comap_uniformity, hx]

Depends on / 依赖: nhdsWithin, nhds_eq_comap_uniformity
-/
theorem nhdsWithin_eq_comap_uniformity_of_mem {x : α} {T : Set α} (hx : x in T) (S : Set α) :
    𝓝[S] x = (𝓤 α ⊓ 𝓟 (T ×ˢ S)).comap (Prod.mk x) := by
  simp [nhdsWithin, nhds_eq_comap_uniformity, hx]

/--
theorem `nhdsWithin_eq_comap_uniformity` / 定理 `nhdsWithin_eq_comap_uniformity`

English:
theorem nhdsWithin_eq_comap_uniformity
  given: {x : α} (S : Set α)
  proof: nhdsWithin_eq_comap_uniformity_of_mem (mem_univ _) S

中文:
定理 nhdsWithin_eq_comap_uniformity
  条件: {x : α} (S : Set α)
  证明: nhdsWithin_eq_comap_uniformity_of_mem (mem_univ _) S

Depends on / 依赖: mem_univ, nhdsWithin_eq_comap_uniformity_of_mem
-/
theorem nhdsWithin_eq_comap_uniformity {x : α} (S : Set α) :
    𝓝[S] x = (𝓤 α ⊓ 𝓟 (univ ×ˢ S)).comap (Prod.mk x) :=
  nhdsWithin_eq_comap_uniformity_of_mem (mem_univ _) S

/--
theorem `isOpen_iff_ball_subset` / 定理 `isOpen_iff_ball_subset`

English:
theorem isOpen_iff_ball_subset
  given: {s : Set α}
  statement: IsOpen s ↔ forall x in s, exists V in 𝓤 α, ball x V subseteq s
  proof: by
  simp_rw [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap, ball]

中文:
定理 isOpen_iff_ball_subset
  条件: {s : Set α}
  结论: IsOpen s ↔ 对任意 x in s, 存在 V in 𝓤 α, ball x V subseteq s
  证明: by
  simp_rw [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap, ball]

Depends on / 依赖: isOpen_iff_mem_nhds, mem_comap, nhds_eq_comap_uniformity, simp_rw
-/
theorem isOpen_iff_ball_subset {s : Set α} : IsOpen s ↔ forall x in s, exists V in 𝓤 α, ball x V subseteq s := by
  simp_rw [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity, mem_comap, ball]

/--
theorem `nhds_basis_uniformity'` / 定理 `nhds_basis_uniformity'`

English:
theorem nhds_basis_uniformity'
  statement: {p : ι -> Prop} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s)
  proof: by
  rw [nhds_eq_comap_uniformity]
  exact h.comap (Prod.mk x)

中文:
定理 nhds_basis_uniformity'
  结论: {p : ι -> 命题} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s)
  证明: by
  rw [nhds_eq_comap_uniformity]
  exact h.comap (Prod.mk x)

Depends on / 依赖: Prod.mk, h.comap, nhds_eq_comap_uniformity
-/
theorem nhds_basis_uniformity' {p : ι -> Prop} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => ball x (s i) := by
  rw [nhds_eq_comap_uniformity]
  exact h.comap (Prod.mk x)

/--
theorem `nhds_basis_uniformity` / 定理 `nhds_basis_uniformity`

English:
theorem nhds_basis_uniformity
  statement: {p : ι -> Prop} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s)
  proof: by
  replace h := h.comap Prod.swap
  rw [comap_swap_uniformity] at h
  exact nhds_basis_uniformity' h

中文:
定理 nhds_basis_uniformity
  结论: {p : ι -> 命题} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s)
  证明: by
  replace h := h.comap Prod.swap
  rw [comap_swap_uniformity] at h
  exact nhds_basis_uniformity' h

Depends on / 依赖: Prod.swap, comap_swap_uniformity, h.comap, nhds_basis_uniformity, replace
-/
theorem nhds_basis_uniformity {p : ι -> Prop} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s)
    {x : α} : (𝓝 x).HasBasis p fun i => { y | (y, x) in s i } := by
  replace h := h.comap Prod.swap
  rw [comap_swap_uniformity] at h
  exact nhds_basis_uniformity' h

/--
theorem `nhds_eq_comap_uniformity'` / 定理 `nhds_eq_comap_uniformity'`

English:
theorem nhds_eq_comap_uniformity'
  given: {x : α}
  statement: 𝓝 x = (𝓤 α).comap fun y => (y, x)
  proof: (nhds_basis_uniformity (𝓤 α).basis_sets).eq_of_same_basis (𝓤 α).basis_sets.comap _

中文:
定理 nhds_eq_comap_uniformity'
  条件: {x : α}
  结论: 𝓝 x = (𝓤 α).comap fun y => (y, x)
  证明: (nhds_basis_uniformity (𝓤 α).basis_sets).eq_of_same_basis (𝓤 α).basis_sets.comap _

Depends on / 依赖: basis_sets, basis_sets.comap, eq_of_same_basis, nhds_basis_uniformity
-/
theorem nhds_eq_comap_uniformity' {x : α} : 𝓝 x = (𝓤 α).comap fun y => (y, x) :=
(nhds_basis_uniformity (𝓤 α).basis_sets).eq_of_same_basis (𝓤 α).basis_sets.comap _

/--
theorem `UniformSpace.mem_nhds_iff` / 定理 `UniformSpace.mem_nhds_iff`

English:
theorem UniformSpace.mem_nhds_iff
  given: {x : α} {s : Set α}
  statement: s in 𝓝 x ↔ exists V in 𝓤 α, ball x V subseteq s
  proof: by
  rw [nhds_eq_comap_uniformity]; rw [mem_comap]
  simp_rw [ball]

中文:
定理 UniformSpace.mem_nhds_iff
  条件: {x : α} {s : Set α}
  结论: s in 𝓝 x ↔ 存在 V in 𝓤 α, ball x V subseteq s
  证明: by
  rw [nhds_eq_comap_uniformity]; rw [mem_comap]
  simp_rw [ball]

Depends on / 依赖: mem_comap, nhds_eq_comap_uniformity, simp_rw
-/
theorem UniformSpace.mem_nhds_iff {x : α} {s : Set α} : s in 𝓝 x ↔ exists V in 𝓤 α, ball x V subseteq s := by
  rw [nhds_eq_comap_uniformity]; rw [mem_comap]
  simp_rw [ball]

/--
theorem `UniformSpace.ball_mem_nhds` / 定理 `UniformSpace.ball_mem_nhds`

English:
theorem UniformSpace.ball_mem_nhds
  given: (x : α) ⦃V
  statement: SetRel α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
  proof: by
  rw [UniformSpace.mem_nhds_iff]
  exact ⟨V, V_in, Subset.rfl⟩

中文:
定理 UniformSpace.ball_mem_nhds
  条件: (x : α) ⦃V
  结论: SetRel α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
  证明: by
  rw [UniformSpace.mem_nhds_iff]
  exact ⟨V, V_in, Subset.rfl⟩

Depends on / 依赖: Subset, Subset.rfl, UniformSpace, UniformSpace.mem_nhds_iff, V_in, mem_nhds_iff
-/
theorem UniformSpace.ball_mem_nhds (x : α) ⦃V : SetRel α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x := by
  rw [UniformSpace.mem_nhds_iff]
  exact ⟨V, V_in, Subset.rfl⟩

/--
theorem `UniformSpace.ball_mem_nhdsWithin` / 定理 `UniformSpace.ball_mem_nhdsWithin`

English:
theorem UniformSpace.ball_mem_nhdsWithin
  given: {x : α} {S : Set α} ⦃V
  statement: SetRel α α⦄ (x_in : x in S)
  proof: by
  rw [nhdsWithin_eq_comap_uniformity_of_mem x_in]; rw [mem_comap]
  exact ⟨V, V_in, Subset.rfl⟩

中文:
定理 UniformSpace.ball_mem_nhdsWithin
  条件: {x : α} {S : Set α} ⦃V
  结论: SetRel α α⦄ (x_in : x in S)
  证明: by
  rw [nhdsWithin_eq_comap_uniformity_of_mem x_in]; rw [mem_comap]
  exact ⟨V, V_in, Subset.rfl⟩

Depends on / 依赖: Subset, Subset.rfl, V_in, mem_comap, nhdsWithin_eq_comap_uniformity_of_mem, x_in
-/
theorem UniformSpace.ball_mem_nhdsWithin {x : α} {S : Set α} ⦃V : SetRel α α⦄ (x_in : x in S)
    (V_in : V in 𝓤 α ⊓ 𝓟 (S ×ˢ S)) : ball x V in 𝓝[S] x := by
  rw [nhdsWithin_eq_comap_uniformity_of_mem x_in]; rw [mem_comap]
  exact ⟨V, V_in, Subset.rfl⟩

/--
theorem `UniformSpace.mem_nhds_iff_symm` / 定理 `UniformSpace.mem_nhds_iff_symm`

English:
theorem UniformSpace.mem_nhds_iff_symm
  given: {x : α} {s : Set α}
  proof: by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    use SetRel.symmetrize V, symmetrize_mem_uniformity V_in, inferInstance
    exact Subset.trans (ball_mono SetRel.symmetrize_subset_self x) V_sub
  · rintro ⟨V, V_in, _, V_sub⟩
    exact ⟨V, V_in, V_sub⟩

中文:
定理 UniformSpace.mem_nhds_iff_symm
  条件: {x : α} {s : Set α}
  证明: by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    use SetRel.symmetrize V, symmetrize_mem_uniformity V_in, inferInstance
    exact Subset.trans (ball_mono SetRel.symmetrize_subset_self x) V_sub
  · rintro ⟨V, V_in, _, V_sub⟩
    exact ⟨V, V_in, V_sub⟩

Depends on / 依赖: SetRel, SetRel.symmetrize, SetRel.symmetrize_subset_self, Subset, Subset.trans, UniformSpace, UniformSpace.mem_nhds_iff, V_in, V_sub, ball_mono, mem_nhds_iff, symmetrize, symmetrize_mem_uniformity, symmetrize_subset_self
-/
theorem UniformSpace.mem_nhds_iff_symm {x : α} {s : Set α} :
    s in 𝓝 x ↔ exists V in 𝓤 α, SetRel.IsSymm V ∧ ball x V subseteq s := by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    use SetRel.symmetrize V, symmetrize_mem_uniformity V_in, inferInstance
    exact Subset.trans (ball_mono SetRel.symmetrize_subset_self x) V_sub
  · rintro ⟨V, V_in, _, V_sub⟩
    exact ⟨V, V_in, V_sub⟩

/--
theorem `UniformSpace.hasBasis_nhds` / 定理 `UniformSpace.hasBasis_nhds`

English:
theorem UniformSpace.hasBasis_nhds
  given: (x : α)
  proof: ⟨fun t => by simp [UniformSpace.mem_nhds_iff_symm, and_assoc]⟩

中文:
定理 UniformSpace.hasBasis_nhds
  条件: (x : α)
  证明: ⟨fun t => by simp [UniformSpace.mem_nhds_iff_symm, and_assoc]⟩

Depends on / 依赖: UniformSpace, UniformSpace.mem_nhds_iff_symm, and_assoc, mem_nhds_iff_symm
-/
theorem UniformSpace.hasBasis_nhds (x : α) :
    HasBasis (𝓝 x) (fun s : SetRel α α => s in 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s :=
  ⟨fun t => by simp [UniformSpace.mem_nhds_iff_symm, and_assoc]⟩

open UniformSpace

/--
theorem `UniformSpace.mem_closure_iff_symm_ball` / 定理 `UniformSpace.mem_closure_iff_symm_ball`

English:
theorem UniformSpace.mem_closure_iff_symm_ball
  given: {s : Set α} {x}
  proof: by
  simp [mem_closure_iff_nhds_basis (hasBasis_nhds x), Set.Nonempty]

中文:
定理 UniformSpace.mem_closure_iff_symm_ball
  条件: {s : Set α} {x}
  证明: by
  simp [mem_closure_iff_nhds_basis (hasBasis_nhds x), Set.Nonempty]

Depends on / 依赖: Nonempty, Set.Nonempty, hasBasis_nhds, mem_closure_iff_nhds_basis
-/
theorem UniformSpace.mem_closure_iff_symm_ball {s : Set α} {x} :
    x in closure s ↔ forall {V}, V in 𝓤 α -> SetRel.IsSymm V -> (s inter ball x V).Nonempty := by
  simp [mem_closure_iff_nhds_basis (hasBasis_nhds x), Set.Nonempty]

/--
theorem `UniformSpace.mem_closure_iff_ball` / 定理 `UniformSpace.mem_closure_iff_ball`

English:
theorem UniformSpace.mem_closure_iff_ball
  given: {s : Set α} {x}
  proof: by
  simp [mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (𝓤 α).basis_sets)]

中文:
定理 UniformSpace.mem_closure_iff_ball
  条件: {s : Set α} {x}
  证明: by
  simp [mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (𝓤 α).basis_sets)]

Depends on / 依赖: basis_sets, mem_closure_iff_nhds_basis, nhds_basis_uniformity
-/
theorem UniformSpace.mem_closure_iff_ball {s : Set α} {x} :
    x in closure s ↔ forall {V}, V in 𝓤 α -> (ball x V inter s).Nonempty := by
  simp [mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (𝓤 α).basis_sets)]

/--
theorem `UniformSpace.closure_subset_preimage` / 定理 `UniformSpace.closure_subset_preimage`

English:
theorem UniformSpace.closure_subset_preimage
  proof: by
  intro x hx
  obtain ⟨y, hxy, hy⟩ := mem_closure_iff_ball.mp hx hU
  exact ⟨y, hy, hxy⟩

中文:
定理 UniformSpace.closure_subset_preimage
  证明: by
  intro x hx
  obtain ⟨y, hxy, hy⟩ := mem_closure_iff_ball.mp hx hU
  exact ⟨y, hy, hxy⟩

Depends on / 依赖: mem_closure_iff_ball, mem_closure_iff_ball.mp
-/
theorem UniformSpace.closure_subset_preimage
    {U : SetRel α α} (hU : U in 𝓤 α) (s : Set α) : closure s subseteq U.preimage s := by
  intro x hx
  obtain ⟨y, hxy, hy⟩ := mem_closure_iff_ball.mp hx hU
  exact ⟨y, hy, hxy⟩

/--
theorem `UniformSpace.closure_subset_image` / 定理 `UniformSpace.closure_subset_image`

English:
theorem UniformSpace.closure_subset_image
  proof: closure_subset_preimage (symm_le_uniformity hU) s

中文:
定理 UniformSpace.closure_subset_image
  证明: closure_subset_preimage (symm_le_uniformity hU) s

Depends on / 依赖: closure_subset_preimage, symm_le_uniformity
-/
theorem UniformSpace.closure_subset_image
    {U : SetRel α α} (hU : U in 𝓤 α) (s : Set α) : closure s subseteq U.image s :=
  closure_subset_preimage (symm_le_uniformity hU) s

/--
theorem `nhds_eq_uniformity` / 定理 `nhds_eq_uniformity`

English:
theorem nhds_eq_uniformity
  given: {x : α}
  statement: 𝓝 x = (𝓤 α).lift' (ball x)
  proof: (nhds_basis_uniformity' (𝓤 α).basis_sets).eq_biInf

中文:
定理 nhds_eq_uniformity
  条件: {x : α}
  结论: 𝓝 x = (𝓤 α).lift' (ball x)
  证明: (nhds_basis_uniformity' (𝓤 α).basis_sets).eq_biInf

Depends on / 依赖: basis_sets, eq_biInf, nhds_basis_uniformity
-/
theorem nhds_eq_uniformity {x : α} : 𝓝 x = (𝓤 α).lift' (ball x) :=
  (nhds_basis_uniformity' (𝓤 α).basis_sets).eq_biInf

/--
theorem `nhds_eq_uniformity'` / 定理 `nhds_eq_uniformity'`

English:
theorem nhds_eq_uniformity'
  given: {x : α}
  statement: 𝓝 x = (𝓤 α).lift' fun s => { y | (y, x) in s }
  proof: (nhds_basis_uniformity (𝓤 α).basis_sets).eq_biInf

中文:
定理 nhds_eq_uniformity'
  条件: {x : α}
  结论: 𝓝 x = (𝓤 α).lift' fun s => { y | (y, x) in s }
  证明: (nhds_basis_uniformity (𝓤 α).basis_sets).eq_biInf

Depends on / 依赖: basis_sets, eq_biInf, nhds_basis_uniformity
-/
theorem nhds_eq_uniformity' {x : α} : 𝓝 x = (𝓤 α).lift' fun s => { y | (y, x) in s } :=
  (nhds_basis_uniformity (𝓤 α).basis_sets).eq_biInf

/--
theorem `mem_nhds_left` / 定理 `mem_nhds_left`

English:
theorem mem_nhds_left
  given: (x : α) {s : SetRel α α} (h : s in 𝓤 α)
  statement: { y : α | (x, y) in s } in 𝓝 x
  proof: ball_mem_nhds x h

中文:
定理 mem_nhds_left
  条件: (x : α) {s : SetRel α α} (h : s in 𝓤 α)
  结论: { y : α | (x, y) in s } in 𝓝 x
  证明: ball_mem_nhds x h

Depends on / 依赖: ball_mem_nhds
-/
theorem mem_nhds_left (x : α) {s : SetRel α α} (h : s in 𝓤 α) : { y : α | (x, y) in s } in 𝓝 x :=
  ball_mem_nhds x h

/--
theorem `mem_nhds_right` / 定理 `mem_nhds_right`

English:
theorem mem_nhds_right
  given: (y : α) {s : SetRel α α} (h : s in 𝓤 α)
  statement: { x : α | (x, y) in s } in 𝓝 y
  proof: mem_nhds_left _ (symm_le_uniformity h)

中文:
定理 mem_nhds_right
  条件: (y : α) {s : SetRel α α} (h : s in 𝓤 α)
  结论: { x : α | (x, y) in s } in 𝓝 y
  证明: mem_nhds_left _ (symm_le_uniformity h)

Depends on / 依赖: mem_nhds_left, symm_le_uniformity
-/
theorem mem_nhds_right (y : α) {s : SetRel α α} (h : s in 𝓤 α) : { x : α | (x, y) in s } in 𝓝 y :=
  mem_nhds_left _ (symm_le_uniformity h)

/--
theorem `exists_mem_nhds_ball_subset_of_mem_nhds` / 定理 `exists_mem_nhds_ball_subset_of_mem_nhds`

English:
theorem exists_mem_nhds_ball_subset_of_mem_nhds
  given: {a : α} {U : Set α} (h : U in 𝓝 a)
  proof: let ⟨t, ht, htU⟩ := comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 h)
  ⟨_, mem_nhds_left a ht, t, ht, fun a₁ h₁ a₂ h₂ => @htU (a, a₂) ⟨a₁, h₁, h₂⟩ rfl⟩

中文:
定理 exists_mem_nhds_ball_subset_of_mem_nhds
  条件: {a : α} {U : Set α} (h : U in 𝓝 a)
  证明: let ⟨t, ht, htU⟩ := comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 h)
  ⟨_, mem_nhds_left a ht, t, ht, fun a₁ h₁ a₂ h₂ => @htU (a, a₂) ⟨a₁, h₁, h₂⟩ rfl⟩

Depends on / 依赖: comp_mem_uniformity_sets, mem_nhds_left, mem_nhds_uniformity_iff_right
-/
theorem exists_mem_nhds_ball_subset_of_mem_nhds {a : α} {U : Set α} (h : U in 𝓝 a) :
    exists V in 𝓝 a, exists t in 𝓤 α, forall a' in V, UniformSpace.ball a' t subseteq U :=
  let ⟨t, ht, htU⟩ := comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 h)
  ⟨_, mem_nhds_left a ht, t, ht, fun a₁ h₁ a₂ h₂ => @htU (a, a₂) ⟨a₁, h₁, h₂⟩ rfl⟩

/--
theorem `tendsto_right_nhds_uniformity` / 定理 `tendsto_right_nhds_uniformity`

English:
theorem tendsto_right_nhds_uniformity
  given: {a : α}
  statement: Tendsto (fun a' => (a', a)) (𝓝 a) (𝓤 α)
  proof: fun _ =>
  mem_nhds_right a

中文:
定理 tendsto_right_nhds_uniformity
  条件: {a : α}
  结论: Tendsto (fun a' => (a', a)) (𝓝 a) (𝓤 α)
  证明: fun _ =>
  mem_nhds_right a
-/
theorem tendsto_right_nhds_uniformity {a : α} : Tendsto (fun a' => (a', a)) (𝓝 a) (𝓤 α) := fun _ =>
  mem_nhds_right a

/--
theorem `tendsto_left_nhds_uniformity` / 定理 `tendsto_left_nhds_uniformity`

English:
theorem tendsto_left_nhds_uniformity
  given: {a : α}
  statement: Tendsto (fun a' => (a, a')) (𝓝 a) (𝓤 α)
  proof: fun _ =>
  mem_nhds_left a

中文:
定理 tendsto_left_nhds_uniformity
  条件: {a : α}
  结论: Tendsto (fun a' => (a, a')) (𝓝 a) (𝓤 α)
  证明: fun _ =>
  mem_nhds_left a
-/
theorem tendsto_left_nhds_uniformity {a : α} : Tendsto (fun a' => (a, a')) (𝓝 a) (𝓤 α) := fun _ =>
  mem_nhds_left a

/--
theorem `lift_nhds_left` / 定理 `lift_nhds_left`

English:
theorem lift_nhds_left
  given: {x : α} {g : Set α -> Filter β} (hg : Monotone g)
  proof: by
  rw [nhds_eq_comap_uniformity]; rw [comap_lift_eq2 hg]
  simp_rw [ball, Function.comp_def]

中文:
定理 lift_nhds_left
  条件: {x : α} {g : Set α -> Filter β} (hg : Monotone g)
  证明: by
  rw [nhds_eq_comap_uniformity]; rw [comap_lift_eq2 hg]
  simp_rw [ball, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comap_lift_eq2, comp_def, nhds_eq_comap_uniformity, simp_rw
-/
theorem lift_nhds_left {x : α} {g : Set α -> Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : SetRel α α => g (ball x s) := by
  rw [nhds_eq_comap_uniformity]; rw [comap_lift_eq2 hg]
  simp_rw [ball, Function.comp_def]

/--
theorem `lift_nhds_right` / 定理 `lift_nhds_right`

English:
theorem lift_nhds_right
  given: {x : α} {g : Set α -> Filter β} (hg : Monotone g)
  proof: by
  rw [nhds_eq_comap_uniformity']; rw [comap_lift_eq2 hg]
  simp_rw [Function.comp_def, preimage]

中文:
定理 lift_nhds_right
  条件: {x : α} {g : Set α -> Filter β} (hg : Monotone g)
  证明: by
  rw [nhds_eq_comap_uniformity']; rw [comap_lift_eq2 hg]
  simp_rw [Function.comp_def, preimage]

Depends on / 依赖: Function, Function.comp_def, comap_lift_eq2, comp_def, nhds_eq_comap_uniformity, preimage, simp_rw
-/
theorem lift_nhds_right {x : α} {g : Set α -> Filter β} (hg : Monotone g) :
    (𝓝 x).lift g = (𝓤 α).lift fun s : SetRel α α => g { y | (y, x) in s } := by
  rw [nhds_eq_comap_uniformity']; rw [comap_lift_eq2 hg]
  simp_rw [Function.comp_def, preimage]

/--
theorem `nhds_nhds_eq_uniformity_uniformity_prod` / 定理 `nhds_nhds_eq_uniformity_uniformity_prod`

English:
theorem nhds_nhds_eq_uniformity_uniformity_prod
  given: {a b : α}
  proof: by
  rw [nhds_eq_uniformity']; rw [nhds_eq_uniformity]; rw [prod_lift'_lift']
  exacts [rfl, monotone_preimage, monotone_preimage]

中文:
定理 nhds_nhds_eq_uniformity_uniformity_prod
  条件: {a b : α}
  证明: by
  rw [nhds_eq_uniformity']; rw [nhds_eq_uniformity]; rw [prod_lift'_lift']
  exacts [rfl, monotone_preimage, monotone_preimage]

Depends on / 依赖: _lift, exacts, monotone_preimage, nhds_eq_uniformity, prod_lift
-/
theorem nhds_nhds_eq_uniformity_uniformity_prod {a b : α} :
    𝓝 a ×ˢ 𝓝 b = (𝓤 α).lift fun s : SetRel α α =>
      (𝓤 α).lift' fun t => { y : α | (y, a) in s } ×ˢ { y : α | (b, y) in t } := by
  rw [nhds_eq_uniformity']; rw [nhds_eq_uniformity]; rw [prod_lift'_lift']
  exacts [rfl, monotone_preimage, monotone_preimage]

/--
theorem `Filter.HasBasis.biInter_biUnion_ball` / 定理 `Filter.HasBasis.biInter_biUnion_ball`

English:
theorem Filter.HasBasis.biInter_biUnion_ball
  statement: {p : ι -> Prop} {U : ι -> SetRel α α}
  proof: by
  ext x
  simp [mem_closure_iff_nhds_basis (nhds_basis_uniformity h), ball]

中文:
定理 Filter.HasBasis.biInter_biUnion_ball
  结论: {p : ι -> 命题} {U : ι -> SetRel α α}
  证明: by
  ext x
  simp [mem_closure_iff_nhds_basis (nhds_basis_uniformity h), ball]

Depends on / 依赖: mem_closure_iff_nhds_basis, nhds_basis_uniformity
-/
theorem Filter.HasBasis.biInter_biUnion_ball {p : ι -> Prop} {U : ι -> SetRel α α}
    (h : HasBasis (𝓤 α) p U) (s : Set α) :
    (⋂ (i) (_ : p i), ⋃ x in s, ball x (U i)) = closure s := by
  ext x
  simp [mem_closure_iff_nhds_basis (nhds_basis_uniformity h), ball]

/-! ### Uniform continuity -/

variable [UniformSpace β]

/-- A function `f : α → β` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `α`. -/
@[fun_prop]
/--
Definition of `UniformContinuous` / `UniformContinuous` 的定义

English:
definition UniformContinuous
  signature: (f : α -> β)
  body: Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α) (𝓤 β)

中文:
定义 UniformContinuous
  签名: (f : α -> β)
  定义体: Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α) (𝓤 β)

Depends on / 依赖: Tendsto
-/
def UniformContinuous (f : α -> β) :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α) (𝓤 β)

/-- Notation for uniform continuity with respect to non-standard `UniformSpace` instances. -/
scoped[Uniformity] notation "UniformContinuous[" u₁ ", " u₂ "]" => @UniformContinuous _ _ u₁ u₂

/-- A function `f : α → β` is *uniformly continuous* on `s : Set α` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s ×ˢ s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`. -/
@[fun_prop]
/--
Definition of `UniformContinuousOn` / `UniformContinuousOn` 的定义

English:
definition UniformContinuousOn
  signature: (f : α -> β) (s : Set α)
  body: Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 β)

中文:
定义 UniformContinuousOn
  签名: (f : α -> β) (s : Set α)
  定义体: Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 β)

Depends on / 依赖: Tendsto
-/
def UniformContinuousOn (f : α -> β) (s : Set α) : Prop :=
  Tendsto (fun x : α × α => (f x.1, f x.2)) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 β)

/--
theorem `uniformContinuous_def` / 定理 `uniformContinuous_def`

English:
theorem uniformContinuous_def
  given: {f : α -> β}
  proof: Iff.rfl

中文:
定理 uniformContinuous_def
  条件: {f : α -> β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem uniformContinuous_def {f : α -> β} :
    UniformContinuous f ↔ forall r in 𝓤 β, { x : α × α | (f x.1, f x.2) in r } in 𝓤 α :=
  Iff.rfl

/--
theorem `uniformContinuous_iff_eventually` / 定理 `uniformContinuous_iff_eventually`

English:
theorem uniformContinuous_iff_eventually
  given: {f : α -> β}
  proof: Iff.rfl

中文:
定理 uniformContinuous_iff_eventually
  条件: {f : α -> β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem uniformContinuous_iff_eventually {f : α -> β} :
    UniformContinuous f ↔ forall r in 𝓤 β, forallᶠ x : α × α in 𝓤 α, (f x.1, f x.2) in r :=
  Iff.rfl

/--
theorem `uniformContinuousOn_univ` / 定理 `uniformContinuousOn_univ`

English:
theorem uniformContinuousOn_univ
  given: {f : α -> β}
  proof: by
  rw [UniformContinuousOn]; rw [UniformContinuous]; rw [univ_prod_univ]; rw [principal_univ]; rw [inf_top_eq]

中文:
定理 uniformContinuousOn_univ
  条件: {f : α -> β}
  证明: by
  rw [UniformContinuousOn]; rw [UniformContinuous]; rw [univ_prod_univ]; rw [principal_univ]; rw [inf_top_eq]

Depends on / 依赖: UniformContinuous, UniformContinuousOn, inf_top_eq, principal_univ, univ_prod_univ
-/
theorem uniformContinuousOn_univ {f : α -> β} :
    UniformContinuousOn f univ ↔ UniformContinuous f := by
  rw [UniformContinuousOn]; rw [UniformContinuous]; rw [univ_prod_univ]; rw [principal_univ]; rw [inf_top_eq]

/--
theorem `uniformContinuous_of_const` / 定理 `uniformContinuous_of_const`

English:
theorem uniformContinuous_of_const
  given: {c : α -> β} (h : forall a b, c a = c b)
  proof: have : (fun x : α × α => (c x.fst, c x.snd)) ⁻¹' SetRel.id = univ :=
    eq_univ_iff_forall.2 fun ⟨a, b⟩ => h a b
  le_trans (map_le_iff_le_comap.2 <| by simp [comap_principal, this]) refl_le_uniformity

@[fun_prop]

中文:
定理 uniformContinuous_of_const
  条件: {c : α -> β} (h : 对任意 a b, c a = c b)
  证明: have : (fun x : α × α => (c x.fst, c x.snd)) ⁻¹' SetRel.id = univ :=
    eq_univ_iff_forall.2 fun ⟨a, b⟩ => h a b
  le_trans (map_le_iff_le_comap.2 <| by simp [comap_principal, this]) refl_le_uniformity

@[fun_prop]

Depends on / 依赖: SetRel, SetRel.id, comap_principal, eq_univ_iff_forall, le_trans, map_le_iff_le_comap, refl_le_uniformity, x.fst, x.snd
-/
theorem uniformContinuous_of_const {c : α -> β} (h : forall a b, c a = c b) :
    UniformContinuous c :=
  have : (fun x : α × α => (c x.fst, c x.snd)) ⁻¹' SetRel.id = univ :=
    eq_univ_iff_forall.2 fun ⟨a, b⟩ => h a b
  le_trans (map_le_iff_le_comap.2 <| by simp [comap_principal, this]) refl_le_uniformity

@[fun_prop]
/--
theorem `uniformContinuous_id` / 定理 `uniformContinuous_id`

English:
theorem uniformContinuous_id
  statement: UniformContinuous (@id α)
  proof: tendsto_id

@[fun_prop]

中文:
定理 uniformContinuous_id
  结论: UniformContinuous (@id α)
  证明: tendsto_id

@[fun_prop]

Depends on / 依赖: tendsto_id
-/
theorem uniformContinuous_id : UniformContinuous (@id α) := tendsto_id

@[fun_prop]
/--
theorem `uniformContinuous_const` / 定理 `uniformContinuous_const`

English:
theorem uniformContinuous_const
  given: {b : β}
  statement: UniformContinuous fun _ : α => b
  proof: uniformContinuous_of_const fun _ _ => rfl

@[fun_prop]
nonrec theorem UniformContinuous.comp [UniformSpace γ] {g : β -> γ} {f : α -> β}
    (hg : UniformContinuous g) (hf : UniformContinuous f) : UniformContinuous (g ∘ f) :=
  hg.comp hf

中文:
定理 uniformContinuous_const
  条件: {b : β}
  结论: UniformContinuous fun _ : α => b
  证明: uniformContinuous_of_const fun _ _ => rfl

@[fun_prop]
nonrec theorem UniformContinuous.comp [UniformSpace γ] {g : β -> γ} {f : α -> β}
    (hg : UniformContinuous g) (hf : UniformContinuous f) : UniformContinuous (g ∘ f) :=
  hg.comp hf

Depends on / 依赖: uniformContinuous_of_const
-/
theorem uniformContinuous_const {b : β} : UniformContinuous fun _ : α => b :=
  uniformContinuous_of_const fun _ _ => rfl

@[fun_prop]
nonrec theorem UniformContinuous.comp [UniformSpace γ] {g : β -> γ} {f : α -> β}
    (hg : UniformContinuous g) (hf : UniformContinuous f) : UniformContinuous (g ∘ f) :=
  hg.comp hf

/-- If a function `T` is uniformly continuous in a uniform space `β`,
then its `n`-th iterate `T^[n]` is also uniformly continuous. -/
@[fun_prop]
/--
theorem `UniformContinuous.iterate` / 定理 `UniformContinuous.iterate`

English:
theorem UniformContinuous.iterate
  given: (T : β -> β) (n : Nat) (h : UniformContinuous T)
  proof: by
  induction n with
  | zero => exact uniformContinuous_id
  | succ n hn => exact Function.iterate_succ _ _ ▸ UniformContinuous.comp hn h

中文:
定理 UniformContinuous.iterate
  条件: (T : β -> β) (n : 自然数) (h : UniformContinuous T)
  证明: by
  induction n with
  | zero => exact uniformContinuous_id
  | succ n hn => exact Function.iterate_succ _ _ ▸ UniformContinuous.comp hn h

Depends on / 依赖: Function, Function.iterate_succ, UniformContinuous, UniformContinuous.comp, iterate_succ, uniformContinuous_id
-/
theorem UniformContinuous.iterate (T : β -> β) (n : Nat) (h : UniformContinuous T) :
    UniformContinuous T^[n] := by
  induction n with
  | zero => exact uniformContinuous_id
  | succ n hn => exact Function.iterate_succ _ _ ▸ UniformContinuous.comp hn h

/--
theorem `Filter.HasBasis.uniformContinuous_iff` / 定理 `Filter.HasBasis.uniformContinuous_iff`

English:
theorem Filter.HasBasis.uniformContinuous_iff
  statement: {ι'} {p : ι -> Prop}
  proof: (ha.tendsto_iff hb).trans by simp only [Prod.forall]

中文:
定理 Filter.HasBasis.uniformContinuous_iff
  结论: {ι'} {p : ι -> 命题}
  证明: (ha.tendsto_iff hb).trans by simp only [Prod.forall]

Depends on / 依赖: Prod.forall, ha.tendsto_iff, tendsto_iff
-/
theorem Filter.HasBasis.uniformContinuous_iff {ι'} {p : ι -> Prop}
    {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι' -> Prop} {t : ι' -> Set (β × β)}
    (hb : (𝓤 β).HasBasis q t) {f : α -> β} :
    UniformContinuous f ↔ forall i, q i -> exists j, p j ∧ forall x y, (x, y) in s j -> (f x, f y) in t i :=
(ha.tendsto_iff hb).trans by simp only [Prod.forall]

/--
theorem `Filter.HasBasis.uniformContinuousOn_iff` / 定理 `Filter.HasBasis.uniformContinuousOn_iff`

English:
theorem Filter.HasBasis.uniformContinuousOn_iff
  statement: {ι'} {p : ι -> Prop}
  proof: ((ha.inf_principal (S ×ˢ S)).tendsto_iff hb).trans by
    simp_rw [Prod.forall, Set.inter_comm (s _), forall_mem_comm, mem_inter_iff, mem_prod, and_imp]

中文:
定理 Filter.HasBasis.uniformContinuousOn_iff
  结论: {ι'} {p : ι -> 命题}
  证明: ((ha.inf_principal (S ×ˢ S)).tendsto_iff hb).trans by
    simp_rw [Prod.forall, Set.inter_comm (s _), forall_mem_comm, mem_inter_iff, mem_prod, and_imp]

Depends on / 依赖: Prod.forall, Set.inter_comm, and_imp, forall_mem_comm, ha.inf_principal, inf_principal, inter_comm, mem_inter_iff, mem_prod, simp_rw, tendsto_iff
-/
theorem Filter.HasBasis.uniformContinuousOn_iff {ι'} {p : ι -> Prop}
    {s : ι -> SetRel α α} (ha : (𝓤 α).HasBasis p s) {q : ι' -> Prop} {t : ι' -> Set (β × β)}
    (hb : (𝓤 β).HasBasis q t) {f : α -> β} {S : Set α} :
    UniformContinuousOn f S ↔
      forall i, q i -> exists j, p j ∧ forall x, x in S -> forall y, y in S -> (x, y) in s j -> (f x, f y) in t i :=
((ha.inf_principal (S ×ˢ S)).tendsto_iff hb).trans by
    simp_rw [Prod.forall, Set.inter_comm (s _), forall_mem_comm, mem_inter_iff, mem_prod, and_imp]

/-- A map `f : α → β` between uniform spaces is called *uniform inducing* if the uniformity filter
on `α` is the pullback of the uniformity filter on `β` under `Prod.map f f`. If `α` is a separated
space, then this implies that `f` is injective, hence it is a `IsUniformEmbedding`. -/
@[mk_iff, fun_prop]
/--
Definition of `IsUniformInducing` / `IsUniformInducing` 的定义

English:
structure IsUniformInducing
  parameters: (f : α -> β)
  axioms and operations (1):
    - comap_uniformity : comap (fun x : α × α => (f x.1, f x.2)) (𝓤 β) = 𝓤 α

中文:
结构 IsUniformInducing
  参数: (f : α -> β)
  公理与运算 (1 个):
    - comap_uniformity : comap (fun x : α × α => (f x.1, f x.2)) (𝓤 β) = 𝓤 α
-/
structure IsUniformInducing (f : α -> β) : Prop where
  /-- The uniformity filter on the domain is the pullback of the uniformity filter on the codomain
  under `Prod.map f f`. -/
  comap_uniformity : comap (fun x : α × α => (f x.1, f x.2)) (𝓤 β) = 𝓤 α

/-- A map `f : α → β` between uniform spaces is a *uniform embedding* if it is uniform inducing and
injective. If `α` is a separated space, then the latter assumption follows from the former. -/
@[mk_iff, fun_prop]
/--
Definition of `IsUniformEmbedding` / `IsUniformEmbedding` 的定义

English:
structure IsUniformEmbedding
  parameters: (f : α -> β)
  extends: IsUniformInducing f
  axioms and operations (1):
    - injective : Function.Injective f

中文:
结构 IsUniformEmbedding
  参数: (f : α -> β)
  继承: IsUniformInducing f
  公理与运算 (1 个):
    - injective : Function.Injective f
-/
structure IsUniformEmbedding (f : α -> β) : Prop extends IsUniformInducing f where
  /-- A uniform embedding is injective. -/
  injective : Function.Injective f

/--
lemma `IsUniformEmbedding.isUniformInducing` / 引理 `IsUniformEmbedding.isUniformInducing`

English:
lemma IsUniformEmbedding.isUniformInducing
  given: {f : α -> β} (hf : IsUniformEmbedding f)
  proof: hf.toIsUniformInducing

中文:
引理 IsUniformEmbedding.isUniformInducing
  条件: {f : α -> β} (hf : IsUniformEmbedding f)
  证明: hf.toIsUniformInducing

Depends on / 依赖: hf.toIsUniformInducing, toIsUniformInducing
-/
lemma IsUniformEmbedding.isUniformInducing {f : α -> β} (hf : IsUniformEmbedding f) :
    IsUniformInducing f :=
  hf.toIsUniformInducing

end UniformSpace
