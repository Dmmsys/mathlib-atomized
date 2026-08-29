/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Equicontinuity of a family of functions

Let `X` be a topological space and `α` a `UniformSpace`. A family of functions `F : ι → X → α`
is said to be *equicontinuous at a point `x₀ : X`* when, for any entourage `U` in `α`, there is a
neighborhood `V` of `x₀` such that, for all `x ∈ V`, and *for all `i`*, `F i x` is `U`-close to
`F i x₀`. In other words, one has `∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x, ∀ i, dist x₀ x < δ → dist (F i x₀) (F i x) < ε`.

`F` is said to be *equicontinuous* if it is equicontinuous at each point.

A closely related concept is that of ***uniform*** *equicontinuity* of a family of functions
`F : ι → β → α` between uniform spaces, which means that, for any entourage `U` in `α`, there is an
entourage `V` in `β` such that, if `x` and `y` are `V`-close, then *for all `i`*, `F i x` and
`F i y` are `U`-close. In other words, one has
`∀ U ∈ 𝓤 α, ∀ᶠ xy in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x y, ∀ i, dist x y < δ → dist (F i x₀) (F i x) < ε`.

## Main definitions

* `EquicontinuousAt`: equicontinuity of a family of functions at a point
* `Equicontinuous`: equicontinuity of a family of functions on the whole domain
* `UniformEquicontinuous`: uniform equicontinuity of a family of functions on the whole domain

We also introduce relative versions, namely `EquicontinuousWithinAt`, `EquicontinuousOn` and
`UniformEquicontinuousOn`, akin to `ContinuousWithinAt`, `ContinuousOn` and `UniformContinuousOn`
respectively.

## Main statements

* `equicontinuous_iff_continuous`: equicontinuity can be expressed as a simple continuity
  condition between well-chosen function spaces. This is really useful for building up the theory.
* `Equicontinuous.closure`: if a set of functions is equicontinuous, its closure
  *for the topology of pointwise convergence* is also equicontinuous.

## Notation

Throughout this file, we use :
- `ι`, `κ` for indexing types
- `X`, `Y`, `Z` for topological spaces
- `α`, `β`, `γ` for uniform spaces

## Implementation details

We choose to express equicontinuity as a properties of indexed families of functions rather
than sets of functions for the following reasons:
- it is really easy to express equicontinuity of `H : Set (X → α)` using our setup: it is just
  equicontinuity of the family `(↑) : ↥H → (X → α)`. On the other hand, going the other way around
  would require working with the range of the family, which is always annoying because it
  introduces useless existentials.
- in most applications, one doesn't work with bare functions but with a more specific hom type
  `hom`. Equicontinuity of a set `H : Set hom` would then have to be expressed as equicontinuity
  of `coe_fn '' H`, which is super annoying to work with. This is much simpler with families,
  because equicontinuity of a family `𝓕 : ι → hom` would simply be expressed as equicontinuity
  of `coe_fn ∘ 𝓕`, which doesn't introduce any nasty existentials.

To simplify statements, we do provide abbreviations `Set.EquicontinuousAt`, `Set.Equicontinuous`
and `Set.UniformEquicontinuous` asserting the corresponding fact about the family
`(↑) : ↥H → (X → α)` where `H : Set (X → α)`. Note however that these won't work for sets of hom
types, and in that case one should go back to the family definition rather than using `Set.image`.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]

## Tags

equicontinuity, uniform convergence, ascoli
-/

@[expose] public section


section

open UniformSpace Filter Set Uniformity Topology UniformConvergence Function

variable {ι κ X X' Y α α' β β' γ : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
  [uα : UniformSpace α] [uβ : UniformSpace β] [uγ : UniformSpace γ]

/--
Definition of `EquicontinuousAt` / `EquicontinuousAt` 的定义

English:
definition EquicontinuousAt
  signature: (F : ι -> X -> α) (x₀ : X)
  body: forall U in 𝓤 α, forallᶠ x in 𝓝 x₀, forall i, (F i x₀, F i x) in U

中文:
定义 EquicontinuousAt
  签名: (F : ι -> X -> α) (x₀ : X)
  定义体: forall U in 𝓤 α, forallᶠ x in 𝓝 x₀, forall i, (F i x₀, F i x) in U
-/
def EquicontinuousAt (F : ι -> X -> α) (x₀ : X) : Prop :=
  forall U in 𝓤 α, forallᶠ x in 𝓝 x₀, forall i, (F i x₀, F i x) in U

/--
Definition of `Set.EquicontinuousAt` / `Set.EquicontinuousAt` 的定义

English:
abbreviation Set.EquicontinuousAt
  signature: (H : Set <| X -> α) (x₀ : X)
  body: EquicontinuousAt ((↑) : H -> X -> α) x₀

中文:
缩写 Set.EquicontinuousAt
  签名: (H : Set <| X -> α) (x₀ : X)
  定义体: EquicontinuousAt ((↑) : H -> X -> α) x₀
-/
protected abbrev Set.EquicontinuousAt (H : Set <| X -> α) (x₀ : X) : Prop :=
  EquicontinuousAt ((↑) : H -> X -> α) x₀

/--
Definition of `EquicontinuousWithinAt` / `EquicontinuousWithinAt` 的定义

English:
definition EquicontinuousWithinAt
  signature: (F : ι -> X -> α) (S : Set X) (x₀ : X)
  body: forall U in 𝓤 α, forallᶠ x in 𝓝[S] x₀, forall i, (F i x₀, F i x) in U

中文:
定义 EquicontinuousWithinAt
  签名: (F : ι -> X -> α) (S : Set X) (x₀ : X)
  定义体: forall U in 𝓤 α, forallᶠ x in 𝓝[S] x₀, forall i, (F i x₀, F i x) in U
-/
def EquicontinuousWithinAt (F : ι -> X -> α) (S : Set X) (x₀ : X) : Prop :=
  forall U in 𝓤 α, forallᶠ x in 𝓝[S] x₀, forall i, (F i x₀, F i x) in U

/--
Definition of `Set.EquicontinuousWithinAt` / `Set.EquicontinuousWithinAt` 的定义

English:
abbreviation Set.EquicontinuousWithinAt
  signature: (H : Set <| X -> α) (S : Set X) (x₀ : X)
  body: EquicontinuousWithinAt ((↑) : H -> X -> α) S x₀

中文:
缩写 Set.EquicontinuousWithinAt
  签名: (H : Set <| X -> α) (S : Set X) (x₀ : X)
  定义体: EquicontinuousWithinAt ((↑) : H -> X -> α) S x₀
-/
protected abbrev Set.EquicontinuousWithinAt (H : Set <| X -> α) (S : Set X) (x₀ : X) : Prop :=
  EquicontinuousWithinAt ((↑) : H -> X -> α) S x₀

/--
Definition of `Equicontinuous` / `Equicontinuous` 的定义

English:
definition Equicontinuous
  signature: (F : ι -> X -> α)
  body: forall x₀, EquicontinuousAt F x₀

中文:
定义 Equicontinuous
  签名: (F : ι -> X -> α)
  定义体: forall x₀, EquicontinuousAt F x₀

Depends on / 依赖: EquicontinuousAt
-/
def Equicontinuous (F : ι -> X -> α) : Prop :=
  forall x₀, EquicontinuousAt F x₀

/--
Definition of `Set.Equicontinuous` / `Set.Equicontinuous` 的定义

English:
abbreviation Set.Equicontinuous
  signature: (H : Set <| X -> α)
  body: Equicontinuous ((↑) : H -> X -> α)

中文:
缩写 Set.Equicontinuous
  签名: (H : Set <| X -> α)
  定义体: Equicontinuous ((↑) : H -> X -> α)
-/
protected abbrev Set.Equicontinuous (H : Set <| X -> α) : Prop :=
  Equicontinuous ((↑) : H -> X -> α)

/--
Definition of `EquicontinuousOn` / `EquicontinuousOn` 的定义

English:
definition EquicontinuousOn
  signature: (F : ι -> X -> α) (S : Set X)
  body: forall x₀ in S, EquicontinuousWithinAt F S x₀

中文:
定义 EquicontinuousOn
  签名: (F : ι -> X -> α) (S : Set X)
  定义体: forall x₀ in S, EquicontinuousWithinAt F S x₀

Depends on / 依赖: EquicontinuousWithinAt
-/
def EquicontinuousOn (F : ι -> X -> α) (S : Set X) : Prop :=
  forall x₀ in S, EquicontinuousWithinAt F S x₀

/--
Definition of `Set.EquicontinuousOn` / `Set.EquicontinuousOn` 的定义

English:
abbreviation Set.EquicontinuousOn
  signature: (H : Set <| X -> α) (S : Set X)
  body: EquicontinuousOn ((↑) : H -> X -> α) S

中文:
缩写 Set.EquicontinuousOn
  签名: (H : Set <| X -> α) (S : Set X)
  定义体: EquicontinuousOn ((↑) : H -> X -> α) S
-/
protected abbrev Set.EquicontinuousOn (H : Set <| X -> α) (S : Set X) : Prop :=
  EquicontinuousOn ((↑) : H -> X -> α) S

/--
Definition of `UniformEquicontinuous` / `UniformEquicontinuous` 的定义

English:
definition UniformEquicontinuous
  signature: (F : ι -> β -> α)
  body: forall U in 𝓤 α, forallᶠ xy : β × β in 𝓤 β, forall i, (F i xy.1, F i xy.2) in U

中文:
定义 UniformEquicontinuous
  签名: (F : ι -> β -> α)
  定义体: forall U in 𝓤 α, forallᶠ xy : β × β in 𝓤 β, forall i, (F i xy.1, F i xy.2) in U
-/
def UniformEquicontinuous (F : ι -> β -> α) : Prop :=
  forall U in 𝓤 α, forallᶠ xy : β × β in 𝓤 β, forall i, (F i xy.1, F i xy.2) in U

/--
Definition of `Set.UniformEquicontinuous` / `Set.UniformEquicontinuous` 的定义

English:
abbreviation Set.UniformEquicontinuous
  signature: (H : Set <| β -> α)
  body: UniformEquicontinuous ((↑) : H -> β -> α)

中文:
缩写 Set.UniformEquicontinuous
  签名: (H : Set <| β -> α)
  定义体: UniformEquicontinuous ((↑) : H -> β -> α)
-/
protected abbrev Set.UniformEquicontinuous (H : Set <| β -> α) : Prop :=
  UniformEquicontinuous ((↑) : H -> β -> α)

/--
Definition of `UniformEquicontinuousOn` / `UniformEquicontinuousOn` 的定义

English:
definition UniformEquicontinuousOn
  signature: (F : ι -> β -> α) (S : Set β)
  body: forall U in 𝓤 α, forallᶠ xy : β × β in 𝓤 β ⊓ 𝓟 (S ×ˢ S), forall i, (F i xy.1, F i xy.2) in U

中文:
定义 UniformEquicontinuousOn
  签名: (F : ι -> β -> α) (S : Set β)
  定义体: forall U in 𝓤 α, forallᶠ xy : β × β in 𝓤 β ⊓ 𝓟 (S ×ˢ S), forall i, (F i xy.1, F i xy.2) in U
-/
def UniformEquicontinuousOn (F : ι -> β -> α) (S : Set β) : Prop :=
  forall U in 𝓤 α, forallᶠ xy : β × β in 𝓤 β ⊓ 𝓟 (S ×ˢ S), forall i, (F i xy.1, F i xy.2) in U

/--
Definition of `Set.UniformEquicontinuousOn` / `Set.UniformEquicontinuousOn` 的定义

English:
abbreviation Set.UniformEquicontinuousOn
  signature: (H : Set <| β -> α) (S : Set β)
  body: UniformEquicontinuousOn ((↑) : H -> β -> α) S

中文:
缩写 Set.UniformEquicontinuousOn
  签名: (H : Set <| β -> α) (S : Set β)
  定义体: UniformEquicontinuousOn ((↑) : H -> β -> α) S
-/
protected abbrev Set.UniformEquicontinuousOn (H : Set <| β -> α) (S : Set β) : Prop :=
  UniformEquicontinuousOn ((↑) : H -> β -> α) S

/--
lemma `EquicontinuousAt.equicontinuousWithinAt` / 引理 `EquicontinuousAt.equicontinuousWithinAt`

English:
lemma EquicontinuousAt.equicontinuousWithinAt
  statement: {F : ι -> X -> α} {x₀ : X} (H : EquicontinuousAt F x₀)
  proof: fun U hU => (H U hU).filter_mono inf_le_left

中文:
引理 EquicontinuousAt.equicontinuousWithinAt
  结论: {F : ι -> X -> α} {x₀ : X} (H : EquicontinuousAt F x₀)
  证明: fun U hU => (H U hU).filter_mono inf_le_left

Depends on / 依赖: filter_mono, inf_le_left
-/
lemma EquicontinuousAt.equicontinuousWithinAt {F : ι -> X -> α} {x₀ : X} (H : EquicontinuousAt F x₀)
    (S : Set X) : EquicontinuousWithinAt F S x₀ :=
  fun U hU => (H U hU).filter_mono inf_le_left

/--
lemma `EquicontinuousWithinAt.mono` / 引理 `EquicontinuousWithinAt.mono`

English:
lemma EquicontinuousWithinAt.mono
  statement: {F : ι -> X -> α} {x₀ : X} {S T : Set X}
  proof: fun U hU => (H U hU).filter_mono nhdsWithin_mono x₀ hST

中文:
引理 EquicontinuousWithinAt.mono
  结论: {F : ι -> X -> α} {x₀ : X} {S T : Set X}
  证明: fun U hU => (H U hU).filter_mono nhdsWithin_mono x₀ hST

Depends on / 依赖: filter_mono, nhdsWithin_mono
-/
lemma EquicontinuousWithinAt.mono {F : ι -> X -> α} {x₀ : X} {S T : Set X}
    (H : EquicontinuousWithinAt F T x₀) (hST : S subseteq T) : EquicontinuousWithinAt F S x₀ :=
fun U hU => (H U hU).filter_mono nhdsWithin_mono x₀ hST

/--
lemma `equicontinuousWithinAt_univ` / 引理 `equicontinuousWithinAt_univ`

English:
lemma equicontinuousWithinAt_univ
  given: (F : ι -> X -> α) (x₀ : X)
  proof: by
  rw [EquicontinuousWithinAt]; rw [EquicontinuousAt]; rw [nhdsWithin_univ]

中文:
引理 equicontinuousWithinAt_univ
  条件: (F : ι -> X -> α) (x₀ : X)
  证明: by
  rw [EquicontinuousWithinAt]; rw [EquicontinuousAt]; rw [nhdsWithin_univ]
-/
@[simp] lemma equicontinuousWithinAt_univ (F : ι -> X -> α) (x₀ : X) :
    EquicontinuousWithinAt F univ x₀ ↔ EquicontinuousAt F x₀ := by
  rw [EquicontinuousWithinAt]; rw [EquicontinuousAt]; rw [nhdsWithin_univ]

/--
lemma `equicontinuousAt_restrict_iff` / 引理 `equicontinuousAt_restrict_iff`

English:
lemma equicontinuousAt_restrict_iff
  given: (F : ι -> X -> α) {S : Set X} (x₀ : S)
  proof: by
  simp [EquicontinuousWithinAt, EquicontinuousAt,
    ← eventually_nhds_subtype_iff]

中文:
引理 equicontinuousAt_restrict_iff
  条件: (F : ι -> X -> α) {S : Set X} (x₀ : S)
  证明: by
  simp [EquicontinuousWithinAt, EquicontinuousAt,
    ← eventually_nhds_subtype_iff]

Depends on / 依赖: EquicontinuousAt, EquicontinuousWithinAt, eventually_nhds_subtype_iff
-/
lemma equicontinuousAt_restrict_iff (F : ι -> X -> α) {S : Set X} (x₀ : S) :
    EquicontinuousAt (S.domRestrict ∘ F) x₀ ↔ EquicontinuousWithinAt F S x₀ := by
  simp [EquicontinuousWithinAt, EquicontinuousAt,
    ← eventually_nhds_subtype_iff]

/--
lemma `Equicontinuous.equicontinuousOn` / 引理 `Equicontinuous.equicontinuousOn`

English:
lemma Equicontinuous.equicontinuousOn
  statement: {F : ι -> X -> α} (H : Equicontinuous F)
  proof: fun x _ => (H x).equicontinuousWithinAt S

中文:
引理 Equicontinuous.equicontinuousOn
  结论: {F : ι -> X -> α} (H : Equicontinuous F)
  证明: fun x _ => (H x).equicontinuousWithinAt S

Depends on / 依赖: equicontinuousWithinAt
-/
lemma Equicontinuous.equicontinuousOn {F : ι -> X -> α} (H : Equicontinuous F)
    (S : Set X) : EquicontinuousOn F S :=
  fun x _ => (H x).equicontinuousWithinAt S

/--
lemma `EquicontinuousOn.mono` / 引理 `EquicontinuousOn.mono`

English:
lemma EquicontinuousOn.mono
  statement: {F : ι -> X -> α} {S T : Set X}
  proof: fun x hx => (H x (hST hx)).mono hST

中文:
引理 EquicontinuousOn.mono
  结论: {F : ι -> X -> α} {S T : Set X}
  证明: fun x hx => (H x (hST hx)).mono hST
-/
lemma EquicontinuousOn.mono {F : ι -> X -> α} {S T : Set X}
    (H : EquicontinuousOn F T) (hST : S subseteq T) : EquicontinuousOn F S :=
  fun x hx => (H x (hST hx)).mono hST

/--
lemma `equicontinuousOn_univ` / 引理 `equicontinuousOn_univ`

English:
lemma equicontinuousOn_univ
  given: (F : ι -> X -> α)
  proof: by
  simp [EquicontinuousOn, Equicontinuous]

中文:
引理 equicontinuousOn_univ
  条件: (F : ι -> X -> α)
  证明: by
  simp [EquicontinuousOn, Equicontinuous]

Depends on / 依赖: Equicontinuous, EquicontinuousOn
-/
lemma equicontinuousOn_univ (F : ι -> X -> α) :
    EquicontinuousOn F univ ↔ Equicontinuous F := by
  simp [EquicontinuousOn, Equicontinuous]

/--
lemma `equicontinuous_restrict_iff` / 引理 `equicontinuous_restrict_iff`

English:
lemma equicontinuous_restrict_iff
  given: (F : ι -> X -> α) {S : Set X}
  proof: by
  simp [Equicontinuous, EquicontinuousOn, equicontinuousAt_restrict_iff]

中文:
引理 equicontinuous_restrict_iff
  条件: (F : ι -> X -> α) {S : Set X}
  证明: by
  simp [Equicontinuous, EquicontinuousOn, equicontinuousAt_restrict_iff]

Depends on / 依赖: Equicontinuous, EquicontinuousOn, equicontinuousAt_restrict_iff
-/
lemma equicontinuous_restrict_iff (F : ι -> X -> α) {S : Set X} :
    Equicontinuous (S.domRestrict ∘ F) ↔ EquicontinuousOn F S := by
  simp [Equicontinuous, EquicontinuousOn, equicontinuousAt_restrict_iff]

/--
lemma `UniformEquicontinuous.uniformEquicontinuousOn` / 引理 `UniformEquicontinuous.uniformEquicontinuousOn`

English:
lemma UniformEquicontinuous.uniformEquicontinuousOn
  statement: {F : ι -> β -> α} (H : UniformEquicontinuous F)
  proof: fun U hU => (H U hU).filter_mono inf_le_left

中文:
引理 UniformEquicontinuous.uniformEquicontinuousOn
  结论: {F : ι -> β -> α} (H : UniformEquicontinuous F)
  证明: fun U hU => (H U hU).filter_mono inf_le_left

Depends on / 依赖: filter_mono, inf_le_left
-/
lemma UniformEquicontinuous.uniformEquicontinuousOn {F : ι -> β -> α} (H : UniformEquicontinuous F)
    (S : Set β) : UniformEquicontinuousOn F S :=
  fun U hU => (H U hU).filter_mono inf_le_left

/--
lemma `UniformEquicontinuousOn.mono` / 引理 `UniformEquicontinuousOn.mono`

English:
lemma UniformEquicontinuousOn.mono
  statement: {F : ι -> β -> α} {S T : Set β}
  proof: fun U hU => (H U hU).filter_mono by gcongr

中文:
引理 UniformEquicontinuousOn.mono
  结论: {F : ι -> β -> α} {S T : Set β}
  证明: fun U hU => (H U hU).filter_mono by gcongr

Depends on / 依赖: filter_mono
-/
lemma UniformEquicontinuousOn.mono {F : ι -> β -> α} {S T : Set β}
    (H : UniformEquicontinuousOn F T) (hST : S subseteq T) : UniformEquicontinuousOn F S :=
fun U hU => (H U hU).filter_mono by gcongr

/--
lemma `uniformEquicontinuousOn_univ` / 引理 `uniformEquicontinuousOn_univ`

English:
lemma uniformEquicontinuousOn_univ
  given: (F : ι -> β -> α)
  proof: by
  simp [UniformEquicontinuousOn, UniformEquicontinuous]

中文:
引理 uniformEquicontinuousOn_univ
  条件: (F : ι -> β -> α)
  证明: by
  simp [UniformEquicontinuousOn, UniformEquicontinuous]

Depends on / 依赖: UniformEquicontinuous, UniformEquicontinuousOn
-/
lemma uniformEquicontinuousOn_univ (F : ι -> β -> α) :
    UniformEquicontinuousOn F univ ↔ UniformEquicontinuous F := by
  simp [UniformEquicontinuousOn, UniformEquicontinuous]

/--
lemma `uniformEquicontinuous_restrict_iff` / 引理 `uniformEquicontinuous_restrict_iff`

English:
lemma uniformEquicontinuous_restrict_iff
  given: (F : ι -> β -> α) {S : Set β}
  proof: by
  rw [UniformEquicontinuous]; rw [UniformEquicontinuousOn]
  conv in _ ⊓ _ => rw [← Subtype.range_val (s := S), ← range_prodMap, ← map_comap]
  rfl

中文:
引理 uniformEquicontinuous_restrict_iff
  条件: (F : ι -> β -> α) {S : Set β}
  证明: by
  rw [UniformEquicontinuous]; rw [UniformEquicontinuousOn]
  conv in _ ⊓ _ => rw [← Subtype.range_val (s := S), ← range_prodMap, ← map_comap]
  rfl

Depends on / 依赖: Subtype, Subtype.range_val, UniformEquicontinuous, UniformEquicontinuousOn, map_comap, range_prodMap, range_val
-/
lemma uniformEquicontinuous_restrict_iff (F : ι -> β -> α) {S : Set β} :
    UniformEquicontinuous (S.domRestrict ∘ F) ↔ UniformEquicontinuousOn F S := by
  rw [UniformEquicontinuous]; rw [UniformEquicontinuousOn]
  conv in _ ⊓ _ => rw [← Subtype.range_val (s := S), ← range_prodMap, ← map_comap]
  rfl

/-!
### Empty index type
-/

@[simp]
/--
lemma `equicontinuousAt_empty` / 引理 `equicontinuousAt_empty`

English:
lemma equicontinuousAt_empty
  given: [h : IsEmpty ι] (F : ι -> X -> α) (x₀ : X)
  proof: fun _ _ => Eventually.of_forall (fun _ => h.elim)

@[simp]

中文:
引理 equicontinuousAt_empty
  条件: [h : IsEmpty ι] (F : ι -> X -> α) (x₀ : X)
  证明: fun _ _ => Eventually.of_forall (fun _ => h.elim)

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, h.elim, of_forall
-/
lemma equicontinuousAt_empty [h : IsEmpty ι] (F : ι -> X -> α) (x₀ : X) :
    EquicontinuousAt F x₀ :=
  fun _ _ => Eventually.of_forall (fun _ => h.elim)

@[simp]
/--
lemma `equicontinuousWithinAt_empty` / 引理 `equicontinuousWithinAt_empty`

English:
lemma equicontinuousWithinAt_empty
  given: [h : IsEmpty ι] (F : ι -> X -> α) (S : Set X) (x₀ : X)
  proof: fun _ _ => Eventually.of_forall (fun _ => h.elim)

@[simp]

中文:
引理 equicontinuousWithinAt_empty
  条件: [h : IsEmpty ι] (F : ι -> X -> α) (S : Set X) (x₀ : X)
  证明: fun _ _ => Eventually.of_forall (fun _ => h.elim)

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, h.elim, of_forall
-/
lemma equicontinuousWithinAt_empty [h : IsEmpty ι] (F : ι -> X -> α) (S : Set X) (x₀ : X) :
    EquicontinuousWithinAt F S x₀ :=
  fun _ _ => Eventually.of_forall (fun _ => h.elim)

@[simp]
/--
lemma `equicontinuous_empty` / 引理 `equicontinuous_empty`

English:
lemma equicontinuous_empty
  given: [IsEmpty ι] (F : ι -> X -> α)
  proof: equicontinuousAt_empty F

@[simp]

中文:
引理 equicontinuous_empty
  条件: [IsEmpty ι] (F : ι -> X -> α)
  证明: equicontinuousAt_empty F

@[simp]

Depends on / 依赖: equicontinuousAt_empty
-/
lemma equicontinuous_empty [IsEmpty ι] (F : ι -> X -> α) :
    Equicontinuous F :=
  equicontinuousAt_empty F

@[simp]
/--
lemma `equicontinuousOn_empty` / 引理 `equicontinuousOn_empty`

English:
lemma equicontinuousOn_empty
  given: [IsEmpty ι] (F : ι -> X -> α) (S : Set X)
  proof: fun x₀ _ => equicontinuousWithinAt_empty F S x₀

@[simp]

中文:
引理 equicontinuousOn_empty
  条件: [IsEmpty ι] (F : ι -> X -> α) (S : Set X)
  证明: fun x₀ _ => equicontinuousWithinAt_empty F S x₀

@[simp]

Depends on / 依赖: equicontinuousWithinAt_empty
-/
lemma equicontinuousOn_empty [IsEmpty ι] (F : ι -> X -> α) (S : Set X) :
    EquicontinuousOn F S :=
  fun x₀ _ => equicontinuousWithinAt_empty F S x₀

@[simp]
/--
lemma `uniformEquicontinuous_empty` / 引理 `uniformEquicontinuous_empty`

English:
lemma uniformEquicontinuous_empty
  given: [h : IsEmpty ι] (F : ι -> β -> α)
  proof: fun _ _ => Eventually.of_forall (fun _ => h.elim)

@[simp]

中文:
引理 uniformEquicontinuous_empty
  条件: [h : IsEmpty ι] (F : ι -> β -> α)
  证明: fun _ _ => Eventually.of_forall (fun _ => h.elim)

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, h.elim, of_forall
-/
lemma uniformEquicontinuous_empty [h : IsEmpty ι] (F : ι -> β -> α) :
    UniformEquicontinuous F :=
  fun _ _ => Eventually.of_forall (fun _ => h.elim)

@[simp]
/--
lemma `uniformEquicontinuousOn_empty` / 引理 `uniformEquicontinuousOn_empty`

English:
lemma uniformEquicontinuousOn_empty
  given: [h : IsEmpty ι] (F : ι -> β -> α) (S : Set β)
  proof: fun _ _ => Eventually.of_forall (fun _ => h.elim)

中文:
引理 uniformEquicontinuousOn_empty
  条件: [h : IsEmpty ι] (F : ι -> β -> α) (S : Set β)
  证明: fun _ _ => Eventually.of_forall (fun _ => h.elim)

Depends on / 依赖: Eventually, Eventually.of_forall, h.elim, of_forall
-/
lemma uniformEquicontinuousOn_empty [h : IsEmpty ι] (F : ι -> β -> α) (S : Set β) :
    UniformEquicontinuousOn F S :=
  fun _ _ => Eventually.of_forall (fun _ => h.elim)


/--
theorem `equicontinuousAt_finite` / 定理 `equicontinuousAt_finite`

English:
theorem equicontinuousAt_finite
  given: [Finite ι] {F : ι -> X -> α} {x₀ : X}
  proof: by
  simp [EquicontinuousAt, ContinuousAt, (nhds_basis_uniformity' (𝓤 α).basis_sets).tendsto_right_iff,
    UniformSpace.ball, @forall_comm _ ι]

中文:
定理 equicontinuousAt_finite
  条件: [Finite ι] {F : ι -> X -> α} {x₀ : X}
  证明: by
  simp [EquicontinuousAt, ContinuousAt, (nhds_basis_uniformity' (𝓤 α).basis_sets).tendsto_right_iff,
    UniformSpace.ball, @forall_comm _ ι]

Depends on / 依赖: ContinuousAt, EquicontinuousAt, UniformSpace, UniformSpace.ball, basis_sets, forall_comm, nhds_basis_uniformity, tendsto_right_iff
-/
theorem equicontinuousAt_finite [Finite ι] {F : ι -> X -> α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔ forall i, ContinuousAt (F i) x₀ := by
  simp [EquicontinuousAt, ContinuousAt, (nhds_basis_uniformity' (𝓤 α).basis_sets).tendsto_right_iff,
    UniformSpace.ball, @forall_comm _ ι]

/--
theorem `equicontinuousWithinAt_finite` / 定理 `equicontinuousWithinAt_finite`

English:
theorem equicontinuousWithinAt_finite
  given: [Finite ι] {F : ι -> X -> α} {S : Set X} {x₀ : X}
  proof: by
  simp [EquicontinuousWithinAt, ContinuousWithinAt,
    (nhds_basis_uniformity' (𝓤 α).basis_sets).tendsto_right_iff, UniformSpace.ball,
    @forall_comm _ ι]

中文:
定理 equicontinuousWithinAt_finite
  条件: [Finite ι] {F : ι -> X -> α} {S : Set X} {x₀ : X}
  证明: by
  simp [EquicontinuousWithinAt, ContinuousWithinAt,
    (nhds_basis_uniformity' (𝓤 α).basis_sets).tendsto_right_iff, UniformSpace.ball,
    @forall_comm _ ι]

Depends on / 依赖: ContinuousWithinAt, EquicontinuousWithinAt, UniformSpace, UniformSpace.ball, basis_sets, forall_comm, nhds_basis_uniformity, tendsto_right_iff
-/
theorem equicontinuousWithinAt_finite [Finite ι] {F : ι -> X -> α} {S : Set X} {x₀ : X} :
    EquicontinuousWithinAt F S x₀ ↔ forall i, ContinuousWithinAt (F i) S x₀ := by
  simp [EquicontinuousWithinAt, ContinuousWithinAt,
    (nhds_basis_uniformity' (𝓤 α).basis_sets).tendsto_right_iff, UniformSpace.ball,
    @forall_comm _ ι]

/--
theorem `equicontinuous_finite` / 定理 `equicontinuous_finite`

English:
theorem equicontinuous_finite
  given: [Finite ι] {F : ι -> X -> α}
  proof: by
  simp only [Equicontinuous, equicontinuousAt_finite, continuous_iff_continuousAt, @forall_comm ι]

中文:
定理 equicontinuous_finite
  条件: [Finite ι] {F : ι -> X -> α}
  证明: by
  simp only [Equicontinuous, equicontinuousAt_finite, continuous_iff_continuousAt, @forall_comm ι]

Depends on / 依赖: Equicontinuous, continuous_iff_continuousAt, equicontinuousAt_finite, forall_comm
-/
theorem equicontinuous_finite [Finite ι] {F : ι -> X -> α} :
    Equicontinuous F ↔ forall i, Continuous (F i) := by
  simp only [Equicontinuous, equicontinuousAt_finite, continuous_iff_continuousAt, @forall_comm ι]

/--
theorem `equicontinuousOn_finite` / 定理 `equicontinuousOn_finite`

English:
theorem equicontinuousOn_finite
  given: [Finite ι] {F : ι -> X -> α} {S : Set X}
  proof: by
  simp only [EquicontinuousOn, equicontinuousWithinAt_finite, ContinuousOn, @forall_comm ι]

中文:
定理 equicontinuousOn_finite
  条件: [Finite ι] {F : ι -> X -> α} {S : Set X}
  证明: by
  simp only [EquicontinuousOn, equicontinuousWithinAt_finite, ContinuousOn, @forall_comm ι]

Depends on / 依赖: ContinuousOn, EquicontinuousOn, equicontinuousWithinAt_finite, forall_comm
-/
theorem equicontinuousOn_finite [Finite ι] {F : ι -> X -> α} {S : Set X} :
    EquicontinuousOn F S ↔ forall i, ContinuousOn (F i) S := by
  simp only [EquicontinuousOn, equicontinuousWithinAt_finite, ContinuousOn, @forall_comm ι]

/--
theorem `uniformEquicontinuous_finite` / 定理 `uniformEquicontinuous_finite`

English:
theorem uniformEquicontinuous_finite
  given: [Finite ι] {F : ι -> β -> α}
  proof: by
  simp only [UniformEquicontinuous, eventually_all, @forall_comm _ ι]; rfl

中文:
定理 uniformEquicontinuous_finite
  条件: [Finite ι] {F : ι -> β -> α}
  证明: by
  simp only [UniformEquicontinuous, eventually_all, @forall_comm _ ι]; rfl

Depends on / 依赖: UniformEquicontinuous, eventually_all, forall_comm
-/
theorem uniformEquicontinuous_finite [Finite ι] {F : ι -> β -> α} :
    UniformEquicontinuous F ↔ forall i, UniformContinuous (F i) := by
  simp only [UniformEquicontinuous, eventually_all, @forall_comm _ ι]; rfl

/--
theorem `uniformEquicontinuousOn_finite` / 定理 `uniformEquicontinuousOn_finite`

English:
theorem uniformEquicontinuousOn_finite
  given: [Finite ι] {F : ι -> β -> α} {S : Set β}
  proof: by
  simp only [UniformEquicontinuousOn, eventually_all, @forall_comm _ ι]; rfl

中文:
定理 uniformEquicontinuousOn_finite
  条件: [Finite ι] {F : ι -> β -> α} {S : Set β}
  证明: by
  simp only [UniformEquicontinuousOn, eventually_all, @forall_comm _ ι]; rfl

Depends on / 依赖: UniformEquicontinuousOn, eventually_all, forall_comm
-/
theorem uniformEquicontinuousOn_finite [Finite ι] {F : ι -> β -> α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ forall i, UniformContinuousOn (F i) S := by
  simp only [UniformEquicontinuousOn, eventually_all, @forall_comm _ ι]; rfl


/--
theorem `equicontinuousAt_unique` / 定理 `equicontinuousAt_unique`

English:
theorem equicontinuousAt_unique
  given: [Unique ι] {F : ι -> X -> α} {x : X}
  proof: equicontinuousAt_finite.trans Unique.forall_iff

中文:
定理 equicontinuousAt_unique
  条件: [Unique ι] {F : ι -> X -> α} {x : X}
  证明: equicontinuousAt_finite.trans Unique.forall_iff

Depends on / 依赖: Unique, Unique.forall_iff, equicontinuousAt_finite, equicontinuousAt_finite.trans, forall_iff
-/
theorem equicontinuousAt_unique [Unique ι] {F : ι -> X -> α} {x : X} :
    EquicontinuousAt F x ↔ ContinuousAt (F default) x :=
  equicontinuousAt_finite.trans Unique.forall_iff

/--
theorem `equicontinuousWithinAt_unique` / 定理 `equicontinuousWithinAt_unique`

English:
theorem equicontinuousWithinAt_unique
  given: [Unique ι] {F : ι -> X -> α} {S : Set X} {x : X}
  proof: equicontinuousWithinAt_finite.trans Unique.forall_iff

中文:
定理 equicontinuousWithinAt_unique
  条件: [Unique ι] {F : ι -> X -> α} {S : Set X} {x : X}
  证明: equicontinuousWithinAt_finite.trans Unique.forall_iff

Depends on / 依赖: Unique, Unique.forall_iff, equicontinuousWithinAt_finite, equicontinuousWithinAt_finite.trans, forall_iff
-/
theorem equicontinuousWithinAt_unique [Unique ι] {F : ι -> X -> α} {S : Set X} {x : X} :
    EquicontinuousWithinAt F S x ↔ ContinuousWithinAt (F default) S x :=
  equicontinuousWithinAt_finite.trans Unique.forall_iff

/--
theorem `equicontinuous_unique` / 定理 `equicontinuous_unique`

English:
theorem equicontinuous_unique
  given: [Unique ι] {F : ι -> X -> α}
  proof: equicontinuous_finite.trans Unique.forall_iff

中文:
定理 equicontinuous_unique
  条件: [Unique ι] {F : ι -> X -> α}
  证明: equicontinuous_finite.trans Unique.forall_iff

Depends on / 依赖: Unique, Unique.forall_iff, equicontinuous_finite, equicontinuous_finite.trans, forall_iff
-/
theorem equicontinuous_unique [Unique ι] {F : ι -> X -> α} :
    Equicontinuous F ↔ Continuous (F default) :=
  equicontinuous_finite.trans Unique.forall_iff

/--
theorem `equicontinuousOn_unique` / 定理 `equicontinuousOn_unique`

English:
theorem equicontinuousOn_unique
  given: [Unique ι] {F : ι -> X -> α} {S : Set X}
  proof: equicontinuousOn_finite.trans Unique.forall_iff

中文:
定理 equicontinuousOn_unique
  条件: [Unique ι] {F : ι -> X -> α} {S : Set X}
  证明: equicontinuousOn_finite.trans Unique.forall_iff

Depends on / 依赖: Unique, Unique.forall_iff, equicontinuousOn_finite, equicontinuousOn_finite.trans, forall_iff
-/
theorem equicontinuousOn_unique [Unique ι] {F : ι -> X -> α} {S : Set X} :
    EquicontinuousOn F S ↔ ContinuousOn (F default) S :=
  equicontinuousOn_finite.trans Unique.forall_iff

/--
theorem `uniformEquicontinuous_unique` / 定理 `uniformEquicontinuous_unique`

English:
theorem uniformEquicontinuous_unique
  given: [Unique ι] {F : ι -> β -> α}
  proof: uniformEquicontinuous_finite.trans Unique.forall_iff

中文:
定理 uniformEquicontinuous_unique
  条件: [Unique ι] {F : ι -> β -> α}
  证明: uniformEquicontinuous_finite.trans Unique.forall_iff

Depends on / 依赖: Unique, Unique.forall_iff, forall_iff, uniformEquicontinuous_finite, uniformEquicontinuous_finite.trans
-/
theorem uniformEquicontinuous_unique [Unique ι] {F : ι -> β -> α} :
    UniformEquicontinuous F ↔ UniformContinuous (F default) :=
  uniformEquicontinuous_finite.trans Unique.forall_iff

/--
theorem `uniformEquicontinuousOn_unique` / 定理 `uniformEquicontinuousOn_unique`

English:
theorem uniformEquicontinuousOn_unique
  given: [Unique ι] {F : ι -> β -> α} {S : Set β}
  proof: uniformEquicontinuousOn_finite.trans Unique.forall_iff

中文:
定理 uniformEquicontinuousOn_unique
  条件: [Unique ι] {F : ι -> β -> α} {S : Set β}
  证明: uniformEquicontinuousOn_finite.trans Unique.forall_iff

Depends on / 依赖: Unique, Unique.forall_iff, forall_iff, uniformEquicontinuousOn_finite, uniformEquicontinuousOn_finite.trans
-/
theorem uniformEquicontinuousOn_unique [Unique ι] {F : ι -> β -> α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ UniformContinuousOn (F default) S :=
  uniformEquicontinuousOn_finite.trans Unique.forall_iff

/--
theorem `equicontinuousWithinAt_iff_pair` / 定理 `equicontinuousWithinAt_iff_pair`

English:
theorem equicontinuousWithinAt_iff_pair
  given: {F : ι -> X -> α} {S : Set X} {x₀ : X} (hx₀ : x₀ in S)
  proof: by
  constructor <;> intro H U hU
  · rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
    refine ⟨_, H V hV, fun x hx y hy i => hVU (SetRel.prodMk_mem_comp ?_ (hy i))⟩
    exact SetRel.symm V (hx i)
  · rcases H U hU with ⟨V, hV, hVU⟩
    filter_upwards [hV] using fun x hx i => hVU

中文:
定理 equicontinuousWithinAt_iff_pair
  条件: {F : ι -> X -> α} {S : Set X} {x₀ : X} (hx₀ : x₀ in S)
  证明: by
  constructor <;> intro H U hU
  · rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
    refine ⟨_, H V hV, fun x hx y hy i => hVU (SetRel.prodMk_mem_comp ?_ (hy i))⟩
    exact SetRel.symm V (hx i)
  · rcases H U hU with ⟨V, hV, hVU⟩
    filter_upwards [hV] using fun x hx i => hVU

Depends on / 依赖: SetRel, SetRel.prodMk_mem_comp, SetRel.symm, comp_symm_mem_uniformity_sets, filter_upwards, hVsymm, mem_of_mem_nhdsWithin, prodMk_mem_comp
-/
theorem equicontinuousWithinAt_iff_pair {F : ι -> X -> α} {S : Set X} {x₀ : X} (hx₀ : x₀ in S) :
    EquicontinuousWithinAt F S x₀ ↔
      forall U in 𝓤 α, exists V in 𝓝[S] x₀, forall x in V, forall y in V, forall i, (F i x, F i y) in U := by
  constructor <;> intro H U hU
  · rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
    refine ⟨_, H V hV, fun x hx y hy i => hVU (SetRel.prodMk_mem_comp ?_ (hy i))⟩
    exact SetRel.symm V (hx i)
  · rcases H U hU with ⟨V, hV, hVU⟩
    filter_upwards [hV] using fun x hx i => hVU x₀ (mem_of_mem_nhdsWithin hx₀ hV) x hx i

/--
theorem `equicontinuousAt_iff_pair` / 定理 `equicontinuousAt_iff_pair`

English:
theorem equicontinuousAt_iff_pair
  given: {F : ι -> X -> α} {x₀ : X}
  proof: by
  simp_rw [← equicontinuousWithinAt_univ, equicontinuousWithinAt_iff_pair (mem_univ x₀),
    nhdsWithin_univ]

中文:
定理 equicontinuousAt_iff_pair
  条件: {F : ι -> X -> α} {x₀ : X}
  证明: by
  simp_rw [← equicontinuousWithinAt_univ, equicontinuousWithinAt_iff_pair (mem_univ x₀),
    nhdsWithin_univ]

Depends on / 依赖: equicontinuousWithinAt_iff_pair, equicontinuousWithinAt_univ, mem_univ, nhdsWithin_univ, simp_rw
-/
theorem equicontinuousAt_iff_pair {F : ι -> X -> α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔
      forall U in 𝓤 α, exists V in 𝓝 x₀, forall x in V, forall y in V, forall i, (F i x, F i y) in U := by
  simp_rw [← equicontinuousWithinAt_univ, equicontinuousWithinAt_iff_pair (mem_univ x₀),
    nhdsWithin_univ]

/--
theorem `UniformEquicontinuous.equicontinuous` / 定理 `UniformEquicontinuous.equicontinuous`

English:
theorem UniformEquicontinuous.equicontinuous
  given: {F : ι -> β -> α} (h : UniformEquicontinuous F)
  proof: fun x₀ U hU =>
  mem_of_superset (ball_mem_nhds x₀ (h U hU)) fun _ hx i => hx i

中文:
定理 UniformEquicontinuous.equicontinuous
  条件: {F : ι -> β -> α} (h : UniformEquicontinuous F)
  证明: fun x₀ U hU =>
  mem_of_superset (ball_mem_nhds x₀ (h U hU)) fun _ hx i => hx i
-/
theorem UniformEquicontinuous.equicontinuous {F : ι -> β -> α} (h : UniformEquicontinuous F) :
    Equicontinuous F := fun x₀ U hU =>
  mem_of_superset (ball_mem_nhds x₀ (h U hU)) fun _ hx i => hx i

/--
theorem `UniformEquicontinuousOn.equicontinuousOn` / 定理 `UniformEquicontinuousOn.equicontinuousOn`

English:
theorem UniformEquicontinuousOn.equicontinuousOn
  statement: {F : ι -> β -> α} {S : Set β}
  proof: fun _ hx₀ U hU =>
  mem_of_superset (ball_mem_nhdsWithin hx₀ (h U hU)) fun _ hx i => hx i

中文:
定理 UniformEquicontinuousOn.equicontinuousOn
  结论: {F : ι -> β -> α} {S : Set β}
  证明: fun _ hx₀ U hU =>
  mem_of_superset (ball_mem_nhdsWithin hx₀ (h U hU)) fun _ hx i => hx i
-/
theorem UniformEquicontinuousOn.equicontinuousOn {F : ι -> β -> α} {S : Set β}
    (h : UniformEquicontinuousOn F S) :
    EquicontinuousOn F S := fun _ hx₀ U hU =>
  mem_of_superset (ball_mem_nhdsWithin hx₀ (h U hU)) fun _ hx i => hx i

/--
theorem `EquicontinuousAt.continuousAt` / 定理 `EquicontinuousAt.continuousAt`

English:
theorem EquicontinuousAt.continuousAt
  given: {F : ι -> X -> α} {x₀ : X} (h : EquicontinuousAt F x₀) (i : ι)
  proof: (UniformSpace.hasBasis_nhds _).tendsto_right_iff.2 fun U ⟨hU, _⟩ => (h U hU).mono fun _x hx => hx i

中文:
定理 EquicontinuousAt.continuousAt
  条件: {F : ι -> X -> α} {x₀ : X} (h : EquicontinuousAt F x₀) (i : ι)
  证明: (UniformSpace.hasBasis_nhds _).tendsto_right_iff.2 fun U ⟨hU, _⟩ => (h U hU).mono fun _x hx => hx i

Depends on / 依赖: UniformSpace, UniformSpace.hasBasis_nhds, hasBasis_nhds, tendsto_right_iff
-/
theorem EquicontinuousAt.continuousAt {F : ι -> X -> α} {x₀ : X} (h : EquicontinuousAt F x₀) (i : ι) :
    ContinuousAt (F i) x₀ :=
  (UniformSpace.hasBasis_nhds _).tendsto_right_iff.2 fun U ⟨hU, _⟩ => (h U hU).mono fun _x hx => hx i

/--
theorem `EquicontinuousWithinAt.continuousWithinAt` / 定理 `EquicontinuousWithinAt.continuousWithinAt`

English:
theorem EquicontinuousWithinAt.continuousWithinAt
  statement: {F : ι -> X -> α} {S : Set X} {x₀ : X}
  proof: (UniformSpace.hasBasis_nhds _).tendsto_right_iff.2 fun U ⟨hU, _⟩ => (h U hU).mono fun _x hx => hx i

中文:
定理 EquicontinuousWithinAt.continuousWithinAt
  结论: {F : ι -> X -> α} {S : Set X} {x₀ : X}
  证明: (UniformSpace.hasBasis_nhds _).tendsto_right_iff.2 fun U ⟨hU, _⟩ => (h U hU).mono fun _x hx => hx i

Depends on / 依赖: UniformSpace, UniformSpace.hasBasis_nhds, hasBasis_nhds, tendsto_right_iff
-/
theorem EquicontinuousWithinAt.continuousWithinAt {F : ι -> X -> α} {S : Set X} {x₀ : X}
    (h : EquicontinuousWithinAt F S x₀) (i : ι) :
    ContinuousWithinAt (F i) S x₀ :=
  (UniformSpace.hasBasis_nhds _).tendsto_right_iff.2 fun U ⟨hU, _⟩ => (h U hU).mono fun _x hx => hx i

/--
theorem `Set.EquicontinuousAt.continuousAt_of_mem` / 定理 `Set.EquicontinuousAt.continuousAt_of_mem`

English:
theorem Set.EquicontinuousAt.continuousAt_of_mem
  statement: {H : Set <| X -> α} {x₀ : X}
  proof: h.continuousAt ⟨f, hf⟩

中文:
定理 Set.EquicontinuousAt.continuousAt_of_mem
  结论: {H : Set <| X -> α} {x₀ : X}
  证明: h.continuousAt ⟨f, hf⟩
-/
protected theorem Set.EquicontinuousAt.continuousAt_of_mem {H : Set <| X -> α} {x₀ : X}
    (h : H.EquicontinuousAt x₀) {f : X -> α} (hf : f in H) : ContinuousAt f x₀ :=
  h.continuousAt ⟨f, hf⟩

/--
theorem `Set.EquicontinuousWithinAt.continuousWithinAt_of_mem` / 定理 `Set.EquicontinuousWithinAt.continuousWithinAt_of_mem`

English:
theorem Set.EquicontinuousWithinAt.continuousWithinAt_of_mem
  statement: {H : Set <| X -> α}
  proof: h.continuousWithinAt ⟨f, hf⟩

中文:
定理 Set.EquicontinuousWithinAt.continuousWithinAt_of_mem
  结论: {H : Set <| X -> α}
  证明: h.continuousWithinAt ⟨f, hf⟩
-/
protected theorem Set.EquicontinuousWithinAt.continuousWithinAt_of_mem {H : Set <| X -> α}
    {S : Set X} {x₀ : X} (h : H.EquicontinuousWithinAt S x₀) {f : X -> α} (hf : f in H) :
    ContinuousWithinAt f S x₀ :=
  h.continuousWithinAt ⟨f, hf⟩

/--
theorem `Equicontinuous.continuous` / 定理 `Equicontinuous.continuous`

English:
theorem Equicontinuous.continuous
  given: {F : ι -> X -> α} (h : Equicontinuous F) (i : ι)
  proof: continuous_iff_continuousAt.mpr fun x => (h x).continuousAt i

中文:
定理 Equicontinuous.continuous
  条件: {F : ι -> X -> α} (h : Equicontinuous F) (i : ι)
  证明: continuous_iff_continuousAt.mpr fun x => (h x).continuousAt i

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr
-/
theorem Equicontinuous.continuous {F : ι -> X -> α} (h : Equicontinuous F) (i : ι) :
    Continuous (F i) :=
  continuous_iff_continuousAt.mpr fun x => (h x).continuousAt i

/--
theorem `EquicontinuousOn.continuousOn` / 定理 `EquicontinuousOn.continuousOn`

English:
theorem EquicontinuousOn.continuousOn
  statement: {F : ι -> X -> α} {S : Set X} (h : EquicontinuousOn F S)
  proof: fun x hx => (h x hx).continuousWithinAt i

中文:
定理 EquicontinuousOn.continuousOn
  结论: {F : ι -> X -> α} {S : Set X} (h : EquicontinuousOn F S)
  证明: fun x hx => (h x hx).continuousWithinAt i

Depends on / 依赖: continuousWithinAt
-/
theorem EquicontinuousOn.continuousOn {F : ι -> X -> α} {S : Set X} (h : EquicontinuousOn F S)
    (i : ι) : ContinuousOn (F i) S :=
  fun x hx => (h x hx).continuousWithinAt i

/--
theorem `Set.Equicontinuous.continuous_of_mem` / 定理 `Set.Equicontinuous.continuous_of_mem`

English:
theorem Set.Equicontinuous.continuous_of_mem
  statement: {H : Set <| X -> α} (h : H.Equicontinuous)
  proof: h.continuous ⟨f, hf⟩

中文:
定理 Set.Equicontinuous.continuous_of_mem
  结论: {H : Set <| X -> α} (h : H.Equicontinuous)
  证明: h.continuous ⟨f, hf⟩
-/
protected theorem Set.Equicontinuous.continuous_of_mem {H : Set <| X -> α} (h : H.Equicontinuous)
    {f : X -> α} (hf : f in H) : Continuous f :=
  h.continuous ⟨f, hf⟩

/--
theorem `Set.EquicontinuousOn.continuousOn_of_mem` / 定理 `Set.EquicontinuousOn.continuousOn_of_mem`

English:
theorem Set.EquicontinuousOn.continuousOn_of_mem
  statement: {H : Set <| X -> α} {S : Set X}
  proof: h.continuousOn ⟨f, hf⟩

中文:
定理 Set.EquicontinuousOn.continuousOn_of_mem
  结论: {H : Set <| X -> α} {S : Set X}
  证明: h.continuousOn ⟨f, hf⟩
-/
protected theorem Set.EquicontinuousOn.continuousOn_of_mem {H : Set <| X -> α} {S : Set X}
    (h : H.EquicontinuousOn S) {f : X -> α} (hf : f in H) : ContinuousOn f S :=
  h.continuousOn ⟨f, hf⟩

/--
theorem `UniformEquicontinuous.uniformContinuous` / 定理 `UniformEquicontinuous.uniformContinuous`

English:
theorem UniformEquicontinuous.uniformContinuous
  statement: {F : ι -> β -> α} (h : UniformEquicontinuous F)
  proof: fun U hU =>
  mem_map.mpr (mem_of_superset (h U hU) fun _ hxy => hxy i)

中文:
定理 UniformEquicontinuous.uniformContinuous
  结论: {F : ι -> β -> α} (h : UniformEquicontinuous F)
  证明: fun U hU =>
  mem_map.mpr (mem_of_superset (h U hU) fun _ hxy => hxy i)
-/
theorem UniformEquicontinuous.uniformContinuous {F : ι -> β -> α} (h : UniformEquicontinuous F)
    (i : ι) : UniformContinuous (F i) := fun U hU =>
  mem_map.mpr (mem_of_superset (h U hU) fun _ hxy => hxy i)

/--
theorem `UniformEquicontinuousOn.uniformContinuousOn` / 定理 `UniformEquicontinuousOn.uniformContinuousOn`

English:
theorem UniformEquicontinuousOn.uniformContinuousOn
  statement: {F : ι -> β -> α} {S : Set β}
  proof: fun U hU =>
  mem_map.mpr (mem_of_superset (h U hU) fun _ hxy => hxy i)

中文:
定理 UniformEquicontinuousOn.uniformContinuousOn
  结论: {F : ι -> β -> α} {S : Set β}
  证明: fun U hU =>
  mem_map.mpr (mem_of_superset (h U hU) fun _ hxy => hxy i)
-/
theorem UniformEquicontinuousOn.uniformContinuousOn {F : ι -> β -> α} {S : Set β}
    (h : UniformEquicontinuousOn F S) (i : ι) :
    UniformContinuousOn (F i) S := fun U hU =>
  mem_map.mpr (mem_of_superset (h U hU) fun _ hxy => hxy i)

/--
theorem `Set.UniformEquicontinuous.uniformContinuous_of_mem` / 定理 `Set.UniformEquicontinuous.uniformContinuous_of_mem`

English:
theorem Set.UniformEquicontinuous.uniformContinuous_of_mem
  statement: {H : Set <| β -> α}
  proof: h.uniformContinuous ⟨f, hf⟩

中文:
定理 Set.UniformEquicontinuous.uniformContinuous_of_mem
  结论: {H : Set <| β -> α}
  证明: h.uniformContinuous ⟨f, hf⟩
-/
protected theorem Set.UniformEquicontinuous.uniformContinuous_of_mem {H : Set <| β -> α}
    (h : H.UniformEquicontinuous) {f : β -> α} (hf : f in H) : UniformContinuous f :=
  h.uniformContinuous ⟨f, hf⟩

/--
theorem `Set.UniformEquicontinuousOn.uniformContinuousOn_of_mem` / 定理 `Set.UniformEquicontinuousOn.uniformContinuousOn_of_mem`

English:
theorem Set.UniformEquicontinuousOn.uniformContinuousOn_of_mem
  statement: {H : Set <| β -> α}
  proof: h.uniformContinuousOn ⟨f, hf⟩

中文:
定理 Set.UniformEquicontinuousOn.uniformContinuousOn_of_mem
  结论: {H : Set <| β -> α}
  证明: h.uniformContinuousOn ⟨f, hf⟩
-/
protected theorem Set.UniformEquicontinuousOn.uniformContinuousOn_of_mem {H : Set <| β -> α}
    {S : Set β} (h : H.UniformEquicontinuousOn S) {f : β -> α} (hf : f in H) :
    UniformContinuousOn f S :=
  h.uniformContinuousOn ⟨f, hf⟩

/--
theorem `EquicontinuousAt.comp` / 定理 `EquicontinuousAt.comp`

English:
theorem EquicontinuousAt.comp
  given: {F : ι -> X -> α} {x₀ : X} (h : EquicontinuousAt F x₀) (u : κ -> ι)
  proof: fun U hU => (h U hU).mono fun _ H k => H (u k)

中文:
定理 EquicontinuousAt.comp
  条件: {F : ι -> X -> α} {x₀ : X} (h : EquicontinuousAt F x₀) (u : κ -> ι)
  证明: fun U hU => (h U hU).mono fun _ H k => H (u k)
-/
theorem EquicontinuousAt.comp {F : ι -> X -> α} {x₀ : X} (h : EquicontinuousAt F x₀) (u : κ -> ι) :
    EquicontinuousAt (F ∘ u) x₀ := fun U hU => (h U hU).mono fun _ H k => H (u k)

/--
theorem `EquicontinuousWithinAt.comp` / 定理 `EquicontinuousWithinAt.comp`

English:
theorem EquicontinuousWithinAt.comp
  statement: {F : ι -> X -> α} {S : Set X} {x₀ : X}
  proof: fun U hU => (h U hU).mono fun _ H k => H (u k)

中文:
定理 EquicontinuousWithinAt.comp
  结论: {F : ι -> X -> α} {S : Set X} {x₀ : X}
  证明: fun U hU => (h U hU).mono fun _ H k => H (u k)
-/
theorem EquicontinuousWithinAt.comp {F : ι -> X -> α} {S : Set X} {x₀ : X}
    (h : EquicontinuousWithinAt F S x₀) (u : κ -> ι) :
    EquicontinuousWithinAt (F ∘ u) S x₀ :=
  fun U hU => (h U hU).mono fun _ H k => H (u k)

/--
theorem `Set.EquicontinuousAt.mono` / 定理 `Set.EquicontinuousAt.mono`

English:
theorem Set.EquicontinuousAt.mono
  statement: {H H' : Set <| X -> α} {x₀ : X}
  proof: h.comp (inclusion hH)

中文:
定理 Set.EquicontinuousAt.mono
  结论: {H H' : Set <| X -> α} {x₀ : X}
  证明: h.comp (inclusion hH)
-/
protected theorem Set.EquicontinuousAt.mono {H H' : Set <| X -> α} {x₀ : X}
    (h : H.EquicontinuousAt x₀) (hH : H' subseteq H) : H'.EquicontinuousAt x₀ :=
  h.comp (inclusion hH)

/--
theorem `Set.EquicontinuousWithinAt.mono` / 定理 `Set.EquicontinuousWithinAt.mono`

English:
theorem Set.EquicontinuousWithinAt.mono
  statement: {H H' : Set <| X -> α} {S : Set X} {x₀ : X}
  proof: h.comp (inclusion hH)

中文:
定理 Set.EquicontinuousWithinAt.mono
  结论: {H H' : Set <| X -> α} {S : Set X} {x₀ : X}
  证明: h.comp (inclusion hH)
-/
protected theorem Set.EquicontinuousWithinAt.mono {H H' : Set <| X -> α} {S : Set X} {x₀ : X}
    (h : H.EquicontinuousWithinAt S x₀) (hH : H' subseteq H) : H'.EquicontinuousWithinAt S x₀ :=
  h.comp (inclusion hH)

/--
theorem `Equicontinuous.comp` / 定理 `Equicontinuous.comp`

English:
theorem Equicontinuous.comp
  given: {F : ι -> X -> α} (h : Equicontinuous F) (u : κ -> ι)
  proof: fun x => (h x).comp u

中文:
定理 Equicontinuous.comp
  条件: {F : ι -> X -> α} (h : Equicontinuous F) (u : κ -> ι)
  证明: fun x => (h x).comp u
-/
theorem Equicontinuous.comp {F : ι -> X -> α} (h : Equicontinuous F) (u : κ -> ι) :
    Equicontinuous (F ∘ u) := fun x => (h x).comp u

/--
theorem `EquicontinuousOn.comp` / 定理 `EquicontinuousOn.comp`

English:
theorem EquicontinuousOn.comp
  given: {F : ι -> X -> α} {S : Set X} (h : EquicontinuousOn F S) (u : κ -> ι)
  proof: fun x hx => (h x hx).comp u

中文:
定理 EquicontinuousOn.comp
  条件: {F : ι -> X -> α} {S : Set X} (h : EquicontinuousOn F S) (u : κ -> ι)
  证明: fun x hx => (h x hx).comp u
-/
theorem EquicontinuousOn.comp {F : ι -> X -> α} {S : Set X} (h : EquicontinuousOn F S) (u : κ -> ι) :
    EquicontinuousOn (F ∘ u) S := fun x hx => (h x hx).comp u

/--
theorem `Set.Equicontinuous.mono` / 定理 `Set.Equicontinuous.mono`

English:
theorem Set.Equicontinuous.mono
  statement: {H H' : Set <| X -> α} (h : H.Equicontinuous)
  proof: h.comp (inclusion hH)

中文:
定理 Set.Equicontinuous.mono
  结论: {H H' : Set <| X -> α} (h : H.Equicontinuous)
  证明: h.comp (inclusion hH)
-/
protected theorem Set.Equicontinuous.mono {H H' : Set <| X -> α} (h : H.Equicontinuous)
    (hH : H' subseteq H) : H'.Equicontinuous :=
  h.comp (inclusion hH)

/--
theorem `Set.EquicontinuousOn.mono` / 定理 `Set.EquicontinuousOn.mono`

English:
theorem Set.EquicontinuousOn.mono
  statement: {H H' : Set <| X -> α} {S : Set X}
  proof: h.comp (inclusion hH)

中文:
定理 Set.EquicontinuousOn.mono
  结论: {H H' : Set <| X -> α} {S : Set X}
  证明: h.comp (inclusion hH)
-/
protected theorem Set.EquicontinuousOn.mono {H H' : Set <| X -> α} {S : Set X}
    (h : H.EquicontinuousOn S) (hH : H' subseteq H) : H'.EquicontinuousOn S :=
  h.comp (inclusion hH)

/--
theorem `UniformEquicontinuous.comp` / 定理 `UniformEquicontinuous.comp`

English:
theorem UniformEquicontinuous.comp
  given: {F : ι -> β -> α} (h : UniformEquicontinuous F) (u : κ -> ι)
  proof: fun U hU => (h U hU).mono fun _ H k => H (u k)

中文:
定理 UniformEquicontinuous.comp
  条件: {F : ι -> β -> α} (h : UniformEquicontinuous F) (u : κ -> ι)
  证明: fun U hU => (h U hU).mono fun _ H k => H (u k)
-/
theorem UniformEquicontinuous.comp {F : ι -> β -> α} (h : UniformEquicontinuous F) (u : κ -> ι) :
    UniformEquicontinuous (F ∘ u) := fun U hU => (h U hU).mono fun _ H k => H (u k)

/--
theorem `UniformEquicontinuousOn.comp` / 定理 `UniformEquicontinuousOn.comp`

English:
theorem UniformEquicontinuousOn.comp
  statement: {F : ι -> β -> α} {S : Set β} (h : UniformEquicontinuousOn F S)
  proof: fun U hU => (h U hU).mono fun _ H k => H (u k)

中文:
定理 UniformEquicontinuousOn.comp
  结论: {F : ι -> β -> α} {S : Set β} (h : UniformEquicontinuousOn F S)
  证明: fun U hU => (h U hU).mono fun _ H k => H (u k)
-/
theorem UniformEquicontinuousOn.comp {F : ι -> β -> α} {S : Set β} (h : UniformEquicontinuousOn F S)
    (u : κ -> ι) : UniformEquicontinuousOn (F ∘ u) S :=
  fun U hU => (h U hU).mono fun _ H k => H (u k)

/--
theorem `Set.UniformEquicontinuous.mono` / 定理 `Set.UniformEquicontinuous.mono`

English:
theorem Set.UniformEquicontinuous.mono
  statement: {H H' : Set <| β -> α} (h : H.UniformEquicontinuous)
  proof: h.comp (inclusion hH)

中文:
定理 Set.UniformEquicontinuous.mono
  结论: {H H' : Set <| β -> α} (h : H.UniformEquicontinuous)
  证明: h.comp (inclusion hH)
-/
protected theorem Set.UniformEquicontinuous.mono {H H' : Set <| β -> α} (h : H.UniformEquicontinuous)
    (hH : H' subseteq H) : H'.UniformEquicontinuous :=
  h.comp (inclusion hH)

/--
theorem `Set.UniformEquicontinuousOn.mono` / 定理 `Set.UniformEquicontinuousOn.mono`

English:
theorem Set.UniformEquicontinuousOn.mono
  statement: {H H' : Set <| β -> α} {S : Set β}
  proof: h.comp (inclusion hH)

中文:
定理 Set.UniformEquicontinuousOn.mono
  结论: {H H' : Set <| β -> α} {S : Set β}
  证明: h.comp (inclusion hH)
-/
protected theorem Set.UniformEquicontinuousOn.mono {H H' : Set <| β -> α} {S : Set β}
    (h : H.UniformEquicontinuousOn S) (hH : H' subseteq H) : H'.UniformEquicontinuousOn S :=
  h.comp (inclusion hH)

/--
theorem `equicontinuousAt_iff_range` / 定理 `equicontinuousAt_iff_range`

English:
theorem equicontinuousAt_iff_range
  given: {F : ι -> X -> α} {x₀ : X}
  proof: by
  simp only [EquicontinuousAt, forall_subtype_range_iff]

中文:
定理 equicontinuousAt_iff_range
  条件: {F : ι -> X -> α} {x₀ : X}
  证明: by
  simp only [EquicontinuousAt, forall_subtype_range_iff]

Depends on / 依赖: EquicontinuousAt, forall_subtype_range_iff
-/
theorem equicontinuousAt_iff_range {F : ι -> X -> α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔ EquicontinuousAt ((↑) : range F -> X -> α) x₀ := by
  simp only [EquicontinuousAt, forall_subtype_range_iff]

/--
theorem `equicontinuousWithinAt_iff_range` / 定理 `equicontinuousWithinAt_iff_range`

English:
theorem equicontinuousWithinAt_iff_range
  given: {F : ι -> X -> α} {S : Set X} {x₀ : X}
  proof: by
  simp only [EquicontinuousWithinAt, forall_subtype_range_iff]

中文:
定理 equicontinuousWithinAt_iff_range
  条件: {F : ι -> X -> α} {S : Set X} {x₀ : X}
  证明: by
  simp only [EquicontinuousWithinAt, forall_subtype_range_iff]

Depends on / 依赖: EquicontinuousWithinAt, forall_subtype_range_iff
-/
theorem equicontinuousWithinAt_iff_range {F : ι -> X -> α} {S : Set X} {x₀ : X} :
    EquicontinuousWithinAt F S x₀ ↔ EquicontinuousWithinAt ((↑) : range F -> X -> α) S x₀ := by
  simp only [EquicontinuousWithinAt, forall_subtype_range_iff]

/--
theorem `equicontinuous_iff_range` / 定理 `equicontinuous_iff_range`

English:
theorem equicontinuous_iff_range
  given: {F : ι -> X -> α}
  proof: forall_congr' fun _ => equicontinuousAt_iff_range

中文:
定理 equicontinuous_iff_range
  条件: {F : ι -> X -> α}
  证明: forall_congr' fun _ => equicontinuousAt_iff_range

Depends on / 依赖: equicontinuousAt_iff_range, forall_congr
-/
theorem equicontinuous_iff_range {F : ι -> X -> α} :
    Equicontinuous F ↔ Equicontinuous ((↑) : range F -> X -> α) :=
  forall_congr' fun _ => equicontinuousAt_iff_range

/--
theorem `equicontinuousOn_iff_range` / 定理 `equicontinuousOn_iff_range`

English:
theorem equicontinuousOn_iff_range
  given: {F : ι -> X -> α} {S : Set X}
  proof: forall_congr' fun _ => forall_congr' fun _ => equicontinuousWithinAt_iff_range

中文:
定理 equicontinuousOn_iff_range
  条件: {F : ι -> X -> α} {S : Set X}
  证明: forall_congr' fun _ => forall_congr' fun _ => equicontinuousWithinAt_iff_range

Depends on / 依赖: equicontinuousWithinAt_iff_range, forall_congr
-/
theorem equicontinuousOn_iff_range {F : ι -> X -> α} {S : Set X} :
    EquicontinuousOn F S ↔ EquicontinuousOn ((↑) : range F -> X -> α) S :=
  forall_congr' fun _ => forall_congr' fun _ => equicontinuousWithinAt_iff_range

/--
theorem `uniformEquicontinuous_iff_range` / 定理 `uniformEquicontinuous_iff_range`

English:
theorem uniformEquicontinuous_iff_range
  given: {F : ι -> β -> α}
  proof: ⟨fun h => by rw [← comp_rangeSplitting F]; exact h.comp _, fun h =>
    h.comp (rangeFactorization F)⟩

中文:
定理 uniformEquicontinuous_iff_range
  条件: {F : ι -> β -> α}
  证明: ⟨fun h => by rw [← comp_rangeSplitting F]; exact h.comp _, fun h =>
    h.comp (rangeFactorization F)⟩

Depends on / 依赖: comp_rangeSplitting, h.comp, rangeFactorization
-/
theorem uniformEquicontinuous_iff_range {F : ι -> β -> α} :
    UniformEquicontinuous F ↔ UniformEquicontinuous ((↑) : range F -> β -> α) :=
  ⟨fun h => by rw [← comp_rangeSplitting F]; exact h.comp _, fun h =>
    h.comp (rangeFactorization F)⟩

/--
theorem `uniformEquicontinuousOn_iff_range` / 定理 `uniformEquicontinuousOn_iff_range`

English:
theorem uniformEquicontinuousOn_iff_range
  given: {F : ι -> β -> α} {S : Set β}
  proof: ⟨fun h => by rw [← comp_rangeSplitting F]; exact h.comp _, fun h =>
    h.comp (rangeFactorization F)⟩

中文:
定理 uniformEquicontinuousOn_iff_range
  条件: {F : ι -> β -> α} {S : Set β}
  证明: ⟨fun h => by rw [← comp_rangeSplitting F]; exact h.comp _, fun h =>
    h.comp (rangeFactorization F)⟩

Depends on / 依赖: comp_rangeSplitting, h.comp, rangeFactorization
-/
theorem uniformEquicontinuousOn_iff_range {F : ι -> β -> α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ UniformEquicontinuousOn ((↑) : range F -> β -> α) S :=
  ⟨fun h => by rw [← comp_rangeSplitting F]; exact h.comp _, fun h =>
    h.comp (rangeFactorization F)⟩

section

open UniformFun

/--
theorem `equicontinuousAt_iff_continuousAt` / 定理 `equicontinuousAt_iff_continuousAt`

English:
theorem equicontinuousAt_iff_continuousAt
  given: {F : ι -> X -> α} {x₀ : X}
  proof: by
  rw [ContinuousAt]; rw [(UniformFun.hasBasis_nhds ι α _).tendsto_right_iff]
  rfl

中文:
定理 equicontinuousAt_iff_continuousAt
  条件: {F : ι -> X -> α} {x₀ : X}
  证明: by
  rw [ContinuousAt]; rw [(UniformFun.hasBasis_nhds ι α _).tendsto_right_iff]
  rfl

Depends on / 依赖: ContinuousAt, UniformFun, UniformFun.hasBasis_nhds, hasBasis_nhds, tendsto_right_iff
-/
theorem equicontinuousAt_iff_continuousAt {F : ι -> X -> α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔ ContinuousAt (ofFun ∘ Function.swap F : X -> ι ->ᵤ α) x₀ := by
  rw [ContinuousAt]; rw [(UniformFun.hasBasis_nhds ι α _).tendsto_right_iff]
  rfl

/--
theorem `equicontinuousWithinAt_iff_continuousWithinAt` / 定理 `equicontinuousWithinAt_iff_continuousWithinAt`

English:
theorem equicontinuousWithinAt_iff_continuousWithinAt
  given: {F : ι -> X -> α} {S : Set X} {x₀ : X}
  proof: by
  rw [ContinuousWithinAt]; rw [(UniformFun.hasBasis_nhds ι α _).tendsto_right_iff]
  rfl

中文:
定理 equicontinuousWithinAt_iff_continuousWithinAt
  条件: {F : ι -> X -> α} {S : Set X} {x₀ : X}
  证明: by
  rw [ContinuousWithinAt]; rw [(UniformFun.hasBasis_nhds ι α _).tendsto_right_iff]
  rfl

Depends on / 依赖: ContinuousWithinAt, UniformFun, UniformFun.hasBasis_nhds, hasBasis_nhds, tendsto_right_iff
-/
theorem equicontinuousWithinAt_iff_continuousWithinAt {F : ι -> X -> α} {S : Set X} {x₀ : X} :
    EquicontinuousWithinAt F S x₀ ↔
    ContinuousWithinAt (ofFun ∘ Function.swap F : X -> ι ->ᵤ α) S x₀ := by
  rw [ContinuousWithinAt]; rw [(UniformFun.hasBasis_nhds ι α _).tendsto_right_iff]
  rfl

/--
theorem `equicontinuous_iff_continuous` / 定理 `equicontinuous_iff_continuous`

English:
theorem equicontinuous_iff_continuous
  given: {F : ι -> X -> α}
  proof: by
  simp_rw [Equicontinuous, continuous_iff_continuousAt, equicontinuousAt_iff_continuousAt]

中文:
定理 equicontinuous_iff_continuous
  条件: {F : ι -> X -> α}
  证明: by
  simp_rw [Equicontinuous, continuous_iff_continuousAt, equicontinuousAt_iff_continuousAt]

Depends on / 依赖: Equicontinuous, continuous_iff_continuousAt, equicontinuousAt_iff_continuousAt, simp_rw
-/
theorem equicontinuous_iff_continuous {F : ι -> X -> α} :
    Equicontinuous F ↔ Continuous (ofFun ∘ Function.swap F : X -> ι ->ᵤ α) := by
  simp_rw [Equicontinuous, continuous_iff_continuousAt, equicontinuousAt_iff_continuousAt]

/--
theorem `equicontinuousOn_iff_continuousOn` / 定理 `equicontinuousOn_iff_continuousOn`

English:
theorem equicontinuousOn_iff_continuousOn
  given: {F : ι -> X -> α} {S : Set X}
  proof: by
  simp_rw [EquicontinuousOn, ContinuousOn, equicontinuousWithinAt_iff_continuousWithinAt]

中文:
定理 equicontinuousOn_iff_continuousOn
  条件: {F : ι -> X -> α} {S : Set X}
  证明: by
  simp_rw [EquicontinuousOn, ContinuousOn, equicontinuousWithinAt_iff_continuousWithinAt]

Depends on / 依赖: ContinuousOn, EquicontinuousOn, equicontinuousWithinAt_iff_continuousWithinAt, simp_rw
-/
theorem equicontinuousOn_iff_continuousOn {F : ι -> X -> α} {S : Set X} :
    EquicontinuousOn F S ↔ ContinuousOn (ofFun ∘ Function.swap F : X -> ι ->ᵤ α) S := by
  simp_rw [EquicontinuousOn, ContinuousOn, equicontinuousWithinAt_iff_continuousWithinAt]

/--
theorem `uniformEquicontinuous_iff_uniformContinuous` / 定理 `uniformEquicontinuous_iff_uniformContinuous`

English:
theorem uniformEquicontinuous_iff_uniformContinuous
  given: {F : ι -> β -> α}
  proof: by
  rw [UniformContinuous]; rw [(UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl

中文:
定理 uniformEquicontinuous_iff_uniformContinuous
  条件: {F : ι -> β -> α}
  证明: by
  rw [UniformContinuous]; rw [(UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl

Depends on / 依赖: UniformContinuous, UniformFun, UniformFun.hasBasis_uniformity, hasBasis_uniformity, tendsto_right_iff
-/
theorem uniformEquicontinuous_iff_uniformContinuous {F : ι -> β -> α} :
    UniformEquicontinuous F ↔ UniformContinuous (ofFun ∘ Function.swap F : β -> ι ->ᵤ α) := by
  rw [UniformContinuous]; rw [(UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl

/--
theorem `uniformEquicontinuousOn_iff_uniformContinuousOn` / 定理 `uniformEquicontinuousOn_iff_uniformContinuousOn`

English:
theorem uniformEquicontinuousOn_iff_uniformContinuousOn
  given: {F : ι -> β -> α} {S : Set β}
  proof: by
  rw [UniformContinuousOn]; rw [(UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl

中文:
定理 uniformEquicontinuousOn_iff_uniformContinuousOn
  条件: {F : ι -> β -> α} {S : Set β}
  证明: by
  rw [UniformContinuousOn]; rw [(UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl

Depends on / 依赖: UniformContinuousOn, UniformFun, UniformFun.hasBasis_uniformity, hasBasis_uniformity, tendsto_right_iff
-/
theorem uniformEquicontinuousOn_iff_uniformContinuousOn {F : ι -> β -> α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ UniformContinuousOn (ofFun ∘ Function.swap F : β -> ι ->ᵤ α) S := by
  rw [UniformContinuousOn]; rw [(UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl

/--
theorem `equicontinuousWithinAt_iInf_rng` / 定理 `equicontinuousWithinAt_iInf_rng`

English:
theorem equicontinuousWithinAt_iInf_rng
  statement: {u : κ -> UniformSpace α'} {F : ι -> X -> α'}
  proof: by
  simp +instances only [equicontinuousWithinAt_iff_continuousWithinAt (uα := _), topologicalSpace]
  unfold ContinuousWithinAt
  rw [UniformFun.iInf_eq]; rw [toTopologicalSpace_iInf]; rw [nhds_iInf]; rw [tendsto_iInf]

中文:
定理 equicontinuousWithinAt_iInf_rng
  结论: {u : κ -> UniformSpace α'} {F : ι -> X -> α'}
  证明: by
  simp +instances only [equicontinuousWithinAt_iff_continuousWithinAt (uα := _), topologicalSpace]
  unfold ContinuousWithinAt
  rw [UniformFun.iInf_eq]; rw [toTopologicalSpace_iInf]; rw [nhds_iInf]; rw [tendsto_iInf]
-/
theorem equicontinuousWithinAt_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> X -> α'}
    {S : Set X} {x₀ : X} : EquicontinuousWithinAt (uα := ⨅ k, u k) F S x₀ ↔
      forall k, EquicontinuousWithinAt (uα := u k) F S x₀ := by
  simp +instances only [equicontinuousWithinAt_iff_continuousWithinAt (uα := _), topologicalSpace]
  unfold ContinuousWithinAt
  rw [UniformFun.iInf_eq]; rw [toTopologicalSpace_iInf]; rw [nhds_iInf]; rw [tendsto_iInf]

/--
theorem `equicontinuousAt_iInf_rng` / 定理 `equicontinuousAt_iInf_rng`

English:
theorem equicontinuousAt_iInf_rng
  statement: {u : κ -> UniformSpace α'} {F : ι -> X -> α'}
  proof: by
  simp only [← equicontinuousWithinAt_univ (uα := _), equicontinuousWithinAt_iInf_rng]

中文:
定理 equicontinuousAt_iInf_rng
  结论: {u : κ -> UniformSpace α'} {F : ι -> X -> α'}
  证明: by
  simp only [← equicontinuousWithinAt_univ (uα := _), equicontinuousWithinAt_iInf_rng]

Depends on / 依赖: EquicontinuousAt, equicontinuousWithinAt_iInf_rng, equicontinuousWithinAt_univ
-/
theorem equicontinuousAt_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> X -> α'}
    {x₀ : X} :
    EquicontinuousAt (uα := ⨅ k, u k) F x₀ ↔ forall k, EquicontinuousAt (uα := u k) F x₀ := by
  simp only [← equicontinuousWithinAt_univ (uα := _), equicontinuousWithinAt_iInf_rng]

/--
theorem `equicontinuous_iInf_rng` / 定理 `equicontinuous_iInf_rng`

English:
theorem equicontinuous_iInf_rng
  given: {u : κ -> UniformSpace α'} {F : ι -> X -> α'}
  proof: by
  simp_rw +instances [equicontinuous_iff_continuous (uα := _), UniformFun.topologicalSpace]
  rw [UniformFun.iInf_eq]; rw [toTopologicalSpace_iInf]; rw [continuous_iInf_rng]

中文:
定理 equicontinuous_iInf_rng
  条件: {u : κ -> UniformSpace α'} {F : ι -> X -> α'}
  证明: by
  simp_rw +instances [equicontinuous_iff_continuous (uα := _), UniformFun.topologicalSpace]
  rw [UniformFun.iInf_eq]; rw [toTopologicalSpace_iInf]; rw [continuous_iInf_rng]

Depends on / 依赖: Equicontinuous, UniformFun, UniformFun.iInf_eq, UniformFun.topologicalSpace, continuous_iInf_rng, equicontinuous_iff_continuous, iInf_eq, instances, simp_rw, toTopologicalSpace_iInf, topologicalSpace
-/
theorem equicontinuous_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> X -> α'} :
    Equicontinuous (uα := ⨅ k, u k) F ↔ forall k, Equicontinuous (uα := u k) F := by
  simp_rw +instances [equicontinuous_iff_continuous (uα := _), UniformFun.topologicalSpace]
  rw [UniformFun.iInf_eq]; rw [toTopologicalSpace_iInf]; rw [continuous_iInf_rng]

/--
theorem `equicontinuousOn_iInf_rng` / 定理 `equicontinuousOn_iInf_rng`

English:
theorem equicontinuousOn_iInf_rng
  statement: {u : κ -> UniformSpace α'} {F : ι -> X -> α'}
  proof: by
  simp_rw [EquicontinuousOn, equicontinuousWithinAt_iInf_rng, @forall_comm _ κ]

中文:
定理 equicontinuousOn_iInf_rng
  结论: {u : κ -> UniformSpace α'} {F : ι -> X -> α'}
  证明: by
  simp_rw [EquicontinuousOn, equicontinuousWithinAt_iInf_rng, @forall_comm _ κ]

Depends on / 依赖: EquicontinuousOn, equicontinuousWithinAt_iInf_rng, forall_comm, simp_rw
-/
theorem equicontinuousOn_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> X -> α'}
    {S : Set X} :
    EquicontinuousOn (uα := ⨅ k, u k) F S ↔ forall k, EquicontinuousOn (uα := u k) F S := by
  simp_rw [EquicontinuousOn, equicontinuousWithinAt_iInf_rng, @forall_comm _ κ]

/--
theorem `uniformEquicontinuous_iInf_rng` / 定理 `uniformEquicontinuous_iInf_rng`

English:
theorem uniformEquicontinuous_iInf_rng
  given: {u : κ -> UniformSpace α'} {F : ι -> β -> α'}
  proof: by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uα := _)]
  rw [UniformFun.iInf_eq]; rw [uniformContinuous_iInf_rng]

中文:
定理 uniformEquicontinuous_iInf_rng
  条件: {u : κ -> UniformSpace α'} {F : ι -> β -> α'}
  证明: by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uα := _)]
  rw [UniformFun.iInf_eq]; rw [uniformContinuous_iInf_rng]

Depends on / 依赖: UniformEquicontinuous, UniformFun, UniformFun.iInf_eq, iInf_eq, simp_rw, uniformContinuous_iInf_rng, uniformEquicontinuous_iff_uniformContinuous
-/
theorem uniformEquicontinuous_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> β -> α'} :
    UniformEquicontinuous (uα := ⨅ k, u k) F ↔ forall k, UniformEquicontinuous (uα := u k) F := by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uα := _)]
  rw [UniformFun.iInf_eq]; rw [uniformContinuous_iInf_rng]

/--
theorem `uniformEquicontinuousOn_iInf_rng` / 定理 `uniformEquicontinuousOn_iInf_rng`

English:
theorem uniformEquicontinuousOn_iInf_rng
  statement: {u : κ -> UniformSpace α'} {F : ι -> β -> α'}
  proof: by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uα := _)]
  unfold UniformContinuousOn
  rw [UniformFun.iInf_eq]; rw [iInf_uniformity]; rw [tendsto_iInf]

中文:
定理 uniformEquicontinuousOn_iInf_rng
  结论: {u : κ -> UniformSpace α'} {F : ι -> β -> α'}
  证明: by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uα := _)]
  unfold UniformContinuousOn
  rw [UniformFun.iInf_eq]; rw [iInf_uniformity]; rw [tendsto_iInf]
-/
theorem uniformEquicontinuousOn_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> β -> α'}
    {S : Set β} : UniformEquicontinuousOn (uα := ⨅ k, u k) F S ↔
      forall k, UniformEquicontinuousOn (uα := u k) F S := by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uα := _)]
  unfold UniformContinuousOn
  rw [UniformFun.iInf_eq]; rw [iInf_uniformity]; rw [tendsto_iInf]

/--
theorem `equicontinuousWithinAt_iInf_dom` / 定理 `equicontinuousWithinAt_iInf_dom`

English:
theorem equicontinuousWithinAt_iInf_dom
  statement: {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
  proof: by
  simp only [equicontinuousWithinAt_iff_continuousWithinAt (tX := _)] at hk ⊢
  unfold ContinuousWithinAt nhdsWithin at hk ⊢
  rw [nhds_iInf]
exact hk.mono_left inf_le_inf_right _ iInf_le _ k

中文:
定理 equicontinuousWithinAt_iInf_dom
  结论: {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
  证明: by
  simp only [equicontinuousWithinAt_iff_continuousWithinAt (tX := _)] at hk ⊢
  unfold ContinuousWithinAt nhdsWithin at hk ⊢
  rw [nhds_iInf]
exact hk.mono_left inf_le_inf_right _ iInf_le _ k
-/
theorem equicontinuousWithinAt_iInf_dom {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
    {S : Set X'} {x₀ : X'} {k : κ} (hk : EquicontinuousWithinAt (tX := t k) F S x₀) :
    EquicontinuousWithinAt (tX := ⨅ k, t k) F S x₀ := by
  simp only [equicontinuousWithinAt_iff_continuousWithinAt (tX := _)] at hk ⊢
  unfold ContinuousWithinAt nhdsWithin at hk ⊢
  rw [nhds_iInf]
exact hk.mono_left inf_le_inf_right _ iInf_le _ k

/--
theorem `equicontinuousAt_iInf_dom` / 定理 `equicontinuousAt_iInf_dom`

English:
theorem equicontinuousAt_iInf_dom
  statement: {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
  proof: by
  rw [← equicontinuousWithinAt_univ (tX := _)] at hk ⊢
  exact equicontinuousWithinAt_iInf_dom hk

中文:
定理 equicontinuousAt_iInf_dom
  结论: {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
  证明: by
  rw [← equicontinuousWithinAt_univ (tX := _)] at hk ⊢
  exact equicontinuousWithinAt_iInf_dom hk
-/
theorem equicontinuousAt_iInf_dom {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
    {x₀ : X'} {k : κ} (hk : EquicontinuousAt (tX := t k) F x₀) :
    EquicontinuousAt (tX := ⨅ k, t k) F x₀ := by
  rw [← equicontinuousWithinAt_univ (tX := _)] at hk ⊢
  exact equicontinuousWithinAt_iInf_dom hk

/--
theorem `equicontinuous_iInf_dom` / 定理 `equicontinuous_iInf_dom`

English:
theorem equicontinuous_iInf_dom
  statement: {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
  proof: fun x => equicontinuousAt_iInf_dom (hk x)

中文:
定理 equicontinuous_iInf_dom
  结论: {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
  证明: fun x => equicontinuousAt_iInf_dom (hk x)
-/
theorem equicontinuous_iInf_dom {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
    {k : κ} (hk : Equicontinuous (tX := t k) F) :
    Equicontinuous (tX := ⨅ k, t k) F :=
  fun x => equicontinuousAt_iInf_dom (hk x)

/--
theorem `equicontinuousOn_iInf_dom` / 定理 `equicontinuousOn_iInf_dom`

English:
theorem equicontinuousOn_iInf_dom
  statement: {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
  proof: fun x hx => equicontinuousWithinAt_iInf_dom (hk x hx)

中文:
定理 equicontinuousOn_iInf_dom
  结论: {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
  证明: fun x hx => equicontinuousWithinAt_iInf_dom (hk x hx)
-/
theorem equicontinuousOn_iInf_dom {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α}
    {S : Set X'} {k : κ} (hk : EquicontinuousOn (tX := t k) F S) :
    EquicontinuousOn (tX := ⨅ k, t k) F S :=
  fun x hx => equicontinuousWithinAt_iInf_dom (hk x hx)

/--
theorem `uniformEquicontinuous_iInf_dom` / 定理 `uniformEquicontinuous_iInf_dom`

English:
theorem uniformEquicontinuous_iInf_dom
  statement: {u : κ -> UniformSpace β'} {F : ι -> β' -> α}
  proof: by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uβ := _)] at hk ⊢
  exact uniformContinuous_iInf_dom hk

中文:
定理 uniformEquicontinuous_iInf_dom
  结论: {u : κ -> UniformSpace β'} {F : ι -> β' -> α}
  证明: by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uβ := _)] at hk ⊢
  exact uniformContinuous_iInf_dom hk
-/
theorem uniformEquicontinuous_iInf_dom {u : κ -> UniformSpace β'} {F : ι -> β' -> α}
    {k : κ} (hk : UniformEquicontinuous (uβ := u k) F) :
    UniformEquicontinuous (uβ := ⨅ k, u k) F := by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uβ := _)] at hk ⊢
  exact uniformContinuous_iInf_dom hk

/--
theorem `uniformEquicontinuousOn_iInf_dom` / 定理 `uniformEquicontinuousOn_iInf_dom`

English:
theorem uniformEquicontinuousOn_iInf_dom
  statement: {u : κ -> UniformSpace β'} {F : ι -> β' -> α}
  proof: by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uβ := _)] at hk ⊢
  unfold UniformContinuousOn
  rw [iInf_uniformity]
exact hk.mono_left inf_le_inf_right _ iInf_le _ k

中文:
定理 uniformEquicontinuousOn_iInf_dom
  结论: {u : κ -> UniformSpace β'} {F : ι -> β' -> α}
  证明: by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uβ := _)] at hk ⊢
  unfold UniformContinuousOn
  rw [iInf_uniformity]
exact hk.mono_left inf_le_inf_right _ iInf_le _ k
-/
theorem uniformEquicontinuousOn_iInf_dom {u : κ -> UniformSpace β'} {F : ι -> β' -> α}
    {S : Set β'} {k : κ} (hk : UniformEquicontinuousOn (uβ := u k) F S) :
    UniformEquicontinuousOn (uβ := ⨅ k, u k) F S := by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uβ := _)] at hk ⊢
  unfold UniformContinuousOn
  rw [iInf_uniformity]
exact hk.mono_left inf_le_inf_right _ iInf_le _ k

/--
theorem `Filter.HasBasis.equicontinuousAt_iff_left` / 定理 `Filter.HasBasis.equicontinuousAt_iff_left`

English:
theorem Filter.HasBasis.equicontinuousAt_iff_left
  statement: {p : κ -> Prop} {s : κ -> Set X}
  proof: by
  rw [equicontinuousAt_iff_continuousAt]; rw [ContinuousAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl

中文:
定理 Filter.HasBasis.equicontinuousAt_iff_left
  结论: {p : κ -> 命题} {s : κ -> Set X}
  证明: by
  rw [equicontinuousAt_iff_continuousAt]; rw [ContinuousAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl

Depends on / 依赖: ContinuousAt, UniformFun, UniformFun.hasBasis_nhds, equicontinuousAt_iff_continuousAt, hX.tendsto_iff, hasBasis_nhds, tendsto_iff
-/
theorem Filter.HasBasis.equicontinuousAt_iff_left {p : κ -> Prop} {s : κ -> Set X}
    {F : ι -> X -> α} {x₀ : X} (hX : (𝓝 x₀).HasBasis p s) :
    EquicontinuousAt F x₀ ↔ forall U in 𝓤 α, exists k, p k ∧ forall x in s k, forall i, (F i x₀, F i x) in U := by
  rw [equicontinuousAt_iff_continuousAt]; rw [ContinuousAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl

/--
theorem `Filter.HasBasis.equicontinuousWithinAt_iff_left` / 定理 `Filter.HasBasis.equicontinuousWithinAt_iff_left`

English:
theorem Filter.HasBasis.equicontinuousWithinAt_iff_left
  statement: {p : κ -> Prop} {s : κ -> Set X}
  proof: by
  rw [equicontinuousWithinAt_iff_continuousWithinAt]; rw [ContinuousWithinAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl

中文:
定理 Filter.HasBasis.equicontinuousWithinAt_iff_left
  结论: {p : κ -> 命题} {s : κ -> Set X}
  证明: by
  rw [equicontinuousWithinAt_iff_continuousWithinAt]; rw [ContinuousWithinAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl

Depends on / 依赖: ContinuousWithinAt, UniformFun, UniformFun.hasBasis_nhds, equicontinuousWithinAt_iff_continuousWithinAt, hX.tendsto_iff, hasBasis_nhds, tendsto_iff
-/
theorem Filter.HasBasis.equicontinuousWithinAt_iff_left {p : κ -> Prop} {s : κ -> Set X}
    {F : ι -> X -> α} {S : Set X} {x₀ : X} (hX : (𝓝[S] x₀).HasBasis p s) :
    EquicontinuousWithinAt F S x₀ ↔ forall U in 𝓤 α, exists k, p k ∧ forall x in s k, forall i, (F i x₀, F i x) in U := by
  rw [equicontinuousWithinAt_iff_continuousWithinAt]; rw [ContinuousWithinAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl

/--
theorem `Filter.HasBasis.equicontinuousAt_iff_right` / 定理 `Filter.HasBasis.equicontinuousAt_iff_right`

English:
theorem Filter.HasBasis.equicontinuousAt_iff_right
  statement: {p : κ -> Prop} {s : κ -> Set (α × α)}
  proof: by
  rw [equicontinuousAt_iff_continuousAt]; rw [ContinuousAt]; rw [(UniformFun.hasBasis_nhds_of_basis ι α _ hα).tendsto_right_iff]
  rfl

中文:
定理 Filter.HasBasis.equicontinuousAt_iff_right
  结论: {p : κ -> 命题} {s : κ -> Set (α × α)}
  证明: by
  rw [equicontinuousAt_iff_continuousAt]; rw [ContinuousAt]; rw [(UniformFun.hasBasis_nhds_of_basis ι α _ hα).tendsto_right_iff]
  rfl

Depends on / 依赖: ContinuousAt, UniformFun, UniformFun.hasBasis_nhds_of_basis, equicontinuousAt_iff_continuousAt, hasBasis_nhds_of_basis, tendsto_right_iff
-/
theorem Filter.HasBasis.equicontinuousAt_iff_right {p : κ -> Prop} {s : κ -> Set (α × α)}
    {F : ι -> X -> α} {x₀ : X} (hα : (𝓤 α).HasBasis p s) :
    EquicontinuousAt F x₀ ↔ forall k, p k -> forallᶠ x in 𝓝 x₀, forall i, (F i x₀, F i x) in s k := by
  rw [equicontinuousAt_iff_continuousAt]; rw [ContinuousAt]; rw [(UniformFun.hasBasis_nhds_of_basis ι α _ hα).tendsto_right_iff]
  rfl

/--
theorem `Filter.HasBasis.equicontinuousWithinAt_iff_right` / 定理 `Filter.HasBasis.equicontinuousWithinAt_iff_right`

English:
theorem Filter.HasBasis.equicontinuousWithinAt_iff_right
  statement: {p : κ -> Prop}
  proof: by
  rw [equicontinuousWithinAt_iff_continuousWithinAt]; rw [ContinuousWithinAt]; rw [(UniformFun.hasBasis_nhds_of_basis ι α _ hα).tendsto_right_iff]
  rfl

中文:
定理 Filter.HasBasis.equicontinuousWithinAt_iff_right
  结论: {p : κ -> 命题}
  证明: by
  rw [equicontinuousWithinAt_iff_continuousWithinAt]; rw [ContinuousWithinAt]; rw [(UniformFun.hasBasis_nhds_of_basis ι α _ hα).tendsto_right_iff]
  rfl

Depends on / 依赖: ContinuousWithinAt, UniformFun, UniformFun.hasBasis_nhds_of_basis, equicontinuousWithinAt_iff_continuousWithinAt, hasBasis_nhds_of_basis, tendsto_right_iff
-/
theorem Filter.HasBasis.equicontinuousWithinAt_iff_right {p : κ -> Prop}
    {s : κ -> Set (α × α)} {F : ι -> X -> α} {S : Set X} {x₀ : X} (hα : (𝓤 α).HasBasis p s) :
    EquicontinuousWithinAt F S x₀ ↔ forall k, p k -> forallᶠ x in 𝓝[S] x₀, forall i, (F i x₀, F i x) in s k := by
  rw [equicontinuousWithinAt_iff_continuousWithinAt]; rw [ContinuousWithinAt]; rw [(UniformFun.hasBasis_nhds_of_basis ι α _ hα).tendsto_right_iff]
  rfl

/--
theorem `Filter.HasBasis.equicontinuousAt_iff` / 定理 `Filter.HasBasis.equicontinuousAt_iff`

English:
theorem Filter.HasBasis.equicontinuousAt_iff
  statement: {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop} {s₁ : κ₁ -> Set X}
  proof: by
  rw [equicontinuousAt_iff_continuousAt]; rw [ContinuousAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds_of_basis ι α _ hα)]
  rfl

中文:
定理 Filter.HasBasis.equicontinuousAt_iff
  结论: {κ₁ κ₂ : 类型} {p₁ : κ₁ -> 命题} {s₁ : κ₁ -> Set X}
  证明: by
  rw [equicontinuousAt_iff_continuousAt]; rw [ContinuousAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds_of_basis ι α _ hα)]
  rfl

Depends on / 依赖: ContinuousAt, UniformFun, UniformFun.hasBasis_nhds_of_basis, equicontinuousAt_iff_continuousAt, hX.tendsto_iff, hasBasis_nhds_of_basis, tendsto_iff
-/
theorem Filter.HasBasis.equicontinuousAt_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop} {s₁ : κ₁ -> Set X}
    {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> Set (α × α)} {F : ι -> X -> α} {x₀ : X} (hX : (𝓝 x₀).HasBasis p₁ s₁)
    (hα : (𝓤 α).HasBasis p₂ s₂) :
    EquicontinuousAt F x₀ ↔
      forall k₂, p₂ k₂ -> exists k₁, p₁ k₁ ∧ forall x in s₁ k₁, forall i, (F i x₀, F i x) in s₂ k₂ := by
  rw [equicontinuousAt_iff_continuousAt]; rw [ContinuousAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds_of_basis ι α _ hα)]
  rfl

/--
theorem `Filter.HasBasis.equicontinuousWithinAt_iff` / 定理 `Filter.HasBasis.equicontinuousWithinAt_iff`

English:
theorem Filter.HasBasis.equicontinuousWithinAt_iff
  statement: {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop}
  proof: by
  rw [equicontinuousWithinAt_iff_continuousWithinAt]; rw [ContinuousWithinAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds_of_basis ι α _ hα)]
  rfl

中文:
定理 Filter.HasBasis.equicontinuousWithinAt_iff
  结论: {κ₁ κ₂ : 类型} {p₁ : κ₁ -> 命题}
  证明: by
  rw [equicontinuousWithinAt_iff_continuousWithinAt]; rw [ContinuousWithinAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds_of_basis ι α _ hα)]
  rfl

Depends on / 依赖: ContinuousWithinAt, UniformFun, UniformFun.hasBasis_nhds_of_basis, equicontinuousWithinAt_iff_continuousWithinAt, hX.tendsto_iff, hasBasis_nhds_of_basis, tendsto_iff
-/
theorem Filter.HasBasis.equicontinuousWithinAt_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop}
    {s₁ : κ₁ -> Set X} {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> Set (α × α)} {F : ι -> X -> α} {S : Set X} {x₀ : X}
    (hX : (𝓝[S] x₀).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) :
    EquicontinuousWithinAt F S x₀ ↔
      forall k₂, p₂ k₂ -> exists k₁, p₁ k₁ ∧ forall x in s₁ k₁, forall i, (F i x₀, F i x) in s₂ k₂ := by
  rw [equicontinuousWithinAt_iff_continuousWithinAt]; rw [ContinuousWithinAt]; rw [hX.tendsto_iff (UniformFun.hasBasis_nhds_of_basis ι α _ hα)]
  rfl

/--
theorem `Filter.HasBasis.uniformEquicontinuous_iff_left` / 定理 `Filter.HasBasis.uniformEquicontinuous_iff_left`

English:
theorem Filter.HasBasis.uniformEquicontinuous_iff_left
  statement: {p : κ -> Prop}
  proof: by
  rw [uniformEquicontinuous_iff_uniformContinuous]; rw [UniformContinuous]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity ι α)]
  simp only [Prod.forall]
  rfl

中文:
定理 Filter.HasBasis.uniformEquicontinuous_iff_left
  结论: {p : κ -> 命题}
  证明: by
  rw [uniformEquicontinuous_iff_uniformContinuous]; rw [UniformContinuous]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity ι α)]
  simp only [Prod.forall]
  rfl

Depends on / 依赖: Prod.forall, UniformContinuous, UniformFun, UniformFun.hasBasis_uniformity, hasBasis_uniformity, tendsto_iff, uniformEquicontinuous_iff_uniformContinuous
-/
theorem Filter.HasBasis.uniformEquicontinuous_iff_left {p : κ -> Prop}
    {s : κ -> Set (β × β)} {F : ι -> β -> α} (hβ : (𝓤 β).HasBasis p s) :
    UniformEquicontinuous F ↔
      forall U in 𝓤 α, exists k, p k ∧ forall x y, (x, y) in s k -> forall i, (F i x, F i y) in U := by
  rw [uniformEquicontinuous_iff_uniformContinuous]; rw [UniformContinuous]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity ι α)]
  simp only [Prod.forall]
  rfl

/--
theorem `Filter.HasBasis.uniformEquicontinuousOn_iff_left` / 定理 `Filter.HasBasis.uniformEquicontinuousOn_iff_left`

English:
theorem Filter.HasBasis.uniformEquicontinuousOn_iff_left
  statement: {p : κ -> Prop}
  proof: by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]; rw [UniformContinuousOn]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity ι α)]
  simp only [Prod.forall]
  rfl

中文:
定理 Filter.HasBasis.uniformEquicontinuousOn_iff_left
  结论: {p : κ -> 命题}
  证明: by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]; rw [UniformContinuousOn]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity ι α)]
  simp only [Prod.forall]
  rfl

Depends on / 依赖: Prod.forall, UniformContinuousOn, UniformFun, UniformFun.hasBasis_uniformity, hasBasis_uniformity, tendsto_iff, uniformEquicontinuousOn_iff_uniformContinuousOn
-/
theorem Filter.HasBasis.uniformEquicontinuousOn_iff_left {p : κ -> Prop}
    {s : κ -> Set (β × β)} {F : ι -> β -> α} {S : Set β} (hβ : (𝓤 β ⊓ 𝓟 (S ×ˢ S)).HasBasis p s) :
    UniformEquicontinuousOn F S ↔
      forall U in 𝓤 α, exists k, p k ∧ forall x y, (x, y) in s k -> forall i, (F i x, F i y) in U := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]; rw [UniformContinuousOn]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity ι α)]
  simp only [Prod.forall]
  rfl

/--
theorem `Filter.HasBasis.uniformEquicontinuous_iff_right` / 定理 `Filter.HasBasis.uniformEquicontinuous_iff_right`

English:
theorem Filter.HasBasis.uniformEquicontinuous_iff_right
  statement: {p : κ -> Prop}
  proof: by
  rw [uniformEquicontinuous_iff_uniformContinuous]; rw [UniformContinuous]; rw [(UniformFun.hasBasis_uniformity_of_basis ι α hα).tendsto_right_iff]
  rfl

中文:
定理 Filter.HasBasis.uniformEquicontinuous_iff_right
  结论: {p : κ -> 命题}
  证明: by
  rw [uniformEquicontinuous_iff_uniformContinuous]; rw [UniformContinuous]; rw [(UniformFun.hasBasis_uniformity_of_basis ι α hα).tendsto_right_iff]
  rfl

Depends on / 依赖: UniformContinuous, UniformFun, UniformFun.hasBasis_uniformity_of_basis, hasBasis_uniformity_of_basis, tendsto_right_iff, uniformEquicontinuous_iff_uniformContinuous
-/
theorem Filter.HasBasis.uniformEquicontinuous_iff_right {p : κ -> Prop}
    {s : κ -> Set (α × α)} {F : ι -> β -> α} (hα : (𝓤 α).HasBasis p s) :
    UniformEquicontinuous F ↔ forall k, p k -> forallᶠ xy : β × β in 𝓤 β, forall i, (F i xy.1, F i xy.2) in s k := by
  rw [uniformEquicontinuous_iff_uniformContinuous]; rw [UniformContinuous]; rw [(UniformFun.hasBasis_uniformity_of_basis ι α hα).tendsto_right_iff]
  rfl

/--
theorem `Filter.HasBasis.uniformEquicontinuousOn_iff_right` / 定理 `Filter.HasBasis.uniformEquicontinuousOn_iff_right`

English:
theorem Filter.HasBasis.uniformEquicontinuousOn_iff_right
  statement: {p : κ -> Prop}
  proof: by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]; rw [UniformContinuousOn]; rw [(UniformFun.hasBasis_uniformity_of_basis ι α hα).tendsto_right_iff]
  rfl

中文:
定理 Filter.HasBasis.uniformEquicontinuousOn_iff_right
  结论: {p : κ -> 命题}
  证明: by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]; rw [UniformContinuousOn]; rw [(UniformFun.hasBasis_uniformity_of_basis ι α hα).tendsto_right_iff]
  rfl

Depends on / 依赖: UniformContinuousOn, UniformFun, UniformFun.hasBasis_uniformity_of_basis, hasBasis_uniformity_of_basis, tendsto_right_iff, uniformEquicontinuousOn_iff_uniformContinuousOn
-/
theorem Filter.HasBasis.uniformEquicontinuousOn_iff_right {p : κ -> Prop}
    {s : κ -> Set (α × α)} {F : ι -> β -> α} {S : Set β} (hα : (𝓤 α).HasBasis p s) :
    UniformEquicontinuousOn F S ↔
      forall k, p k -> forallᶠ xy : β × β in 𝓤 β ⊓ 𝓟 (S ×ˢ S), forall i, (F i xy.1, F i xy.2) in s k := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]; rw [UniformContinuousOn]; rw [(UniformFun.hasBasis_uniformity_of_basis ι α hα).tendsto_right_iff]
  rfl

/--
theorem `Filter.HasBasis.uniformEquicontinuous_iff` / 定理 `Filter.HasBasis.uniformEquicontinuous_iff`

English:
theorem Filter.HasBasis.uniformEquicontinuous_iff
  statement: {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop}
  proof: by
  rw [uniformEquicontinuous_iff_uniformContinuous]; rw [UniformContinuous]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity_of_basis ι α hα)]
  simp only [Prod.forall]
  rfl

中文:
定理 Filter.HasBasis.uniformEquicontinuous_iff
  结论: {κ₁ κ₂ : 类型} {p₁ : κ₁ -> 命题}
  证明: by
  rw [uniformEquicontinuous_iff_uniformContinuous]; rw [UniformContinuous]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity_of_basis ι α hα)]
  simp only [Prod.forall]
  rfl

Depends on / 依赖: Prod.forall, UniformContinuous, UniformFun, UniformFun.hasBasis_uniformity_of_basis, hasBasis_uniformity_of_basis, tendsto_iff, uniformEquicontinuous_iff_uniformContinuous
-/
theorem Filter.HasBasis.uniformEquicontinuous_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop}
    {s₁ : κ₁ -> Set (β × β)} {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> Set (α × α)} {F : ι -> β -> α}
    (hβ : (𝓤 β).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) :
    UniformEquicontinuous F ↔
      forall k₂, p₂ k₂ -> exists k₁, p₁ k₁ ∧ forall x y, (x, y) in s₁ k₁ -> forall i, (F i x, F i y) in s₂ k₂ := by
  rw [uniformEquicontinuous_iff_uniformContinuous]; rw [UniformContinuous]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity_of_basis ι α hα)]
  simp only [Prod.forall]
  rfl

/--
theorem `Filter.HasBasis.uniformEquicontinuousOn_iff` / 定理 `Filter.HasBasis.uniformEquicontinuousOn_iff`

English:
theorem Filter.HasBasis.uniformEquicontinuousOn_iff
  statement: {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop}
  proof: by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]; rw [UniformContinuousOn]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity_of_basis ι α hα)]
  simp only [Prod.forall]
  rfl

中文:
定理 Filter.HasBasis.uniformEquicontinuousOn_iff
  结论: {κ₁ κ₂ : 类型} {p₁ : κ₁ -> 命题}
  证明: by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]; rw [UniformContinuousOn]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity_of_basis ι α hα)]
  simp only [Prod.forall]
  rfl

Depends on / 依赖: Prod.forall, UniformContinuousOn, UniformFun, UniformFun.hasBasis_uniformity_of_basis, hasBasis_uniformity_of_basis, tendsto_iff, uniformEquicontinuousOn_iff_uniformContinuousOn
-/
theorem Filter.HasBasis.uniformEquicontinuousOn_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop}
    {s₁ : κ₁ -> Set (β × β)} {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> Set (α × α)} {F : ι -> β -> α}
    {S : Set β} (hβ : (𝓤 β ⊓ 𝓟 (S ×ˢ S)).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) :
    UniformEquicontinuousOn F S ↔
      forall k₂, p₂ k₂ -> exists k₁, p₁ k₁ ∧ forall x y, (x, y) in s₁ k₁ -> forall i, (F i x, F i y) in s₂ k₂ := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]; rw [UniformContinuousOn]; rw [hβ.tendsto_iff (UniformFun.hasBasis_uniformity_of_basis ι α hα)]
  simp only [Prod.forall]
  rfl

/--
theorem `IsUniformInducing.equicontinuousAt_iff` / 定理 `IsUniformInducing.equicontinuousAt_iff`

English:
theorem IsUniformInducing.equicontinuousAt_iff
  statement: {F : ι -> X -> α} {x₀ : X} {u : α -> β}
  proof: by
  have := (UniformFun.postcomp_isUniformInducing (α := ι) hu).isInducing
  rw [equicontinuousAt_iff_continuousAt]; rw [equicontinuousAt_iff_continuousAt]; rw [this.continuousAt_iff]
  rfl

中文:
定理 IsUniformInducing.equicontinuousAt_iff
  结论: {F : ι -> X -> α} {x₀ : X} {u : α -> β}
  证明: by
  have := (UniformFun.postcomp_isUniformInducing (α := ι) hu).isInducing
  rw [equicontinuousAt_iff_continuousAt]; rw [equicontinuousAt_iff_continuousAt]; rw [this.continuousAt_iff]
  rfl

Depends on / 依赖: UniformFun, UniformFun.postcomp_isUniformInducing, continuousAt_iff, equicontinuousAt_iff_continuousAt, isInducing, postcomp_isUniformInducing, this.continuousAt_iff
-/
theorem IsUniformInducing.equicontinuousAt_iff {F : ι -> X -> α} {x₀ : X} {u : α -> β}
    (hu : IsUniformInducing u) : EquicontinuousAt F x₀ ↔ EquicontinuousAt ((u ∘ ·) ∘ F) x₀ := by
  have := (UniformFun.postcomp_isUniformInducing (α := ι) hu).isInducing
  rw [equicontinuousAt_iff_continuousAt]; rw [equicontinuousAt_iff_continuousAt]; rw [this.continuousAt_iff]
  rfl

/--
lemma `IsUniformInducing.equicontinuousWithinAt_iff` / 引理 `IsUniformInducing.equicontinuousWithinAt_iff`

English:
lemma IsUniformInducing.equicontinuousWithinAt_iff
  statement: {F : ι -> X -> α} {S : Set X} {x₀ : X} {u : α -> β}
  proof: by
  have := (UniformFun.postcomp_isUniformInducing (α := ι) hu).isInducing
  simp only [equicontinuousWithinAt_iff_continuousWithinAt, this.continuousWithinAt_iff]
  rfl

中文:
引理 IsUniformInducing.equicontinuousWithinAt_iff
  结论: {F : ι -> X -> α} {S : Set X} {x₀ : X} {u : α -> β}
  证明: by
  have := (UniformFun.postcomp_isUniformInducing (α := ι) hu).isInducing
  simp only [equicontinuousWithinAt_iff_continuousWithinAt, this.continuousWithinAt_iff]
  rfl

Depends on / 依赖: UniformFun, UniformFun.postcomp_isUniformInducing, continuousWithinAt_iff, equicontinuousWithinAt_iff_continuousWithinAt, isInducing, postcomp_isUniformInducing, this.continuousWithinAt_iff
-/
lemma IsUniformInducing.equicontinuousWithinAt_iff {F : ι -> X -> α} {S : Set X} {x₀ : X} {u : α -> β}
    (hu : IsUniformInducing u) : EquicontinuousWithinAt F S x₀ ↔
      EquicontinuousWithinAt ((u ∘ ·) ∘ F) S x₀ := by
  have := (UniformFun.postcomp_isUniformInducing (α := ι) hu).isInducing
  simp only [equicontinuousWithinAt_iff_continuousWithinAt, this.continuousWithinAt_iff]
  rfl

/--
lemma `IsUniformInducing.equicontinuous_iff` / 引理 `IsUniformInducing.equicontinuous_iff`

English:
lemma IsUniformInducing.equicontinuous_iff
  given: {F : ι -> X -> α} {u : α -> β} (hu : IsUniformInducing u)
  proof: by
  congrm forall x, ?_
  rw [hu.equicontinuousAt_iff]

中文:
引理 IsUniformInducing.equicontinuous_iff
  条件: {F : ι -> X -> α} {u : α -> β} (hu : IsUniformInducing u)
  证明: by
  congrm forall x, ?_
  rw [hu.equicontinuousAt_iff]

Depends on / 依赖: congrm, equicontinuousAt_iff, hu.equicontinuousAt_iff
-/
lemma IsUniformInducing.equicontinuous_iff {F : ι -> X -> α} {u : α -> β} (hu : IsUniformInducing u) :
    Equicontinuous F ↔ Equicontinuous ((u ∘ ·) ∘ F) := by
  congrm forall x, ?_
  rw [hu.equicontinuousAt_iff]

/--
theorem `IsUniformInducing.equicontinuousOn_iff` / 定理 `IsUniformInducing.equicontinuousOn_iff`

English:
theorem IsUniformInducing.equicontinuousOn_iff
  statement: {F : ι -> X -> α} {S : Set X} {u : α -> β}
  proof: by
  congrm forall x in S, ?_
  rw [hu.equicontinuousWithinAt_iff]

中文:
定理 IsUniformInducing.equicontinuousOn_iff
  结论: {F : ι -> X -> α} {S : Set X} {u : α -> β}
  证明: by
  congrm forall x in S, ?_
  rw [hu.equicontinuousWithinAt_iff]

Depends on / 依赖: congrm, equicontinuousWithinAt_iff, hu.equicontinuousWithinAt_iff
-/
theorem IsUniformInducing.equicontinuousOn_iff {F : ι -> X -> α} {S : Set X} {u : α -> β}
    (hu : IsUniformInducing u) : EquicontinuousOn F S ↔ EquicontinuousOn ((u ∘ ·) ∘ F) S := by
  congrm forall x in S, ?_
  rw [hu.equicontinuousWithinAt_iff]

/--
theorem `IsUniformInducing.uniformEquicontinuous_iff` / 定理 `IsUniformInducing.uniformEquicontinuous_iff`

English:
theorem IsUniformInducing.uniformEquicontinuous_iff
  statement: {F : ι -> β -> α} {u : α -> γ}
  proof: by
  have := UniformFun.postcomp_isUniformInducing (α := ι) hu
  simp only [uniformEquicontinuous_iff_uniformContinuous, this.uniformContinuous_iff]
  rfl

中文:
定理 IsUniformInducing.uniformEquicontinuous_iff
  结论: {F : ι -> β -> α} {u : α -> γ}
  证明: by
  have := UniformFun.postcomp_isUniformInducing (α := ι) hu
  simp only [uniformEquicontinuous_iff_uniformContinuous, this.uniformContinuous_iff]
  rfl

Depends on / 依赖: UniformFun, UniformFun.postcomp_isUniformInducing, postcomp_isUniformInducing, this.uniformContinuous_iff, uniformContinuous_iff, uniformEquicontinuous_iff_uniformContinuous
-/
theorem IsUniformInducing.uniformEquicontinuous_iff {F : ι -> β -> α} {u : α -> γ}
    (hu : IsUniformInducing u) : UniformEquicontinuous F ↔ UniformEquicontinuous ((u ∘ ·) ∘ F) := by
  have := UniformFun.postcomp_isUniformInducing (α := ι) hu
  simp only [uniformEquicontinuous_iff_uniformContinuous, this.uniformContinuous_iff]
  rfl

/--
theorem `IsUniformInducing.uniformEquicontinuousOn_iff` / 定理 `IsUniformInducing.uniformEquicontinuousOn_iff`

English:
theorem IsUniformInducing.uniformEquicontinuousOn_iff
  statement: {F : ι -> β -> α} {S : Set β} {u : α -> γ}
  proof: by
  have := UniformFun.postcomp_isUniformInducing (α := ι) hu
  simp only [uniformEquicontinuousOn_iff_uniformContinuousOn, this.uniformContinuousOn_iff]
  rfl

中文:
定理 IsUniformInducing.uniformEquicontinuousOn_iff
  结论: {F : ι -> β -> α} {S : Set β} {u : α -> γ}
  证明: by
  have := UniformFun.postcomp_isUniformInducing (α := ι) hu
  simp only [uniformEquicontinuousOn_iff_uniformContinuousOn, this.uniformContinuousOn_iff]
  rfl

Depends on / 依赖: UniformFun, UniformFun.postcomp_isUniformInducing, postcomp_isUniformInducing, this.uniformContinuousOn_iff, uniformContinuousOn_iff, uniformEquicontinuousOn_iff_uniformContinuousOn
-/
theorem IsUniformInducing.uniformEquicontinuousOn_iff {F : ι -> β -> α} {S : Set β} {u : α -> γ}
    (hu : IsUniformInducing u) :
    UniformEquicontinuousOn F S ↔ UniformEquicontinuousOn ((u ∘ ·) ∘ F) S := by
  have := UniformFun.postcomp_isUniformInducing (α := ι) hu
  simp only [uniformEquicontinuousOn_iff_uniformContinuousOn, this.uniformContinuousOn_iff]
  rfl

/--
theorem `EquicontinuousWithinAt.closure'` / 定理 `EquicontinuousWithinAt.closure'`

English:
theorem EquicontinuousWithinAt.closure'
  statement: {A : Set Y} {u : Y -> X -> α} {S : Set X} {x₀ : X}
  proof: by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV, eventually_mem_nhdsWithin] with x hx hxS
  rw [SetCoe.forall] at *
  change A subseteq (fun f => (u f x₀, u f x)) ⁻¹' V at hx
  refine (closure_minimal hx <| hVclosed.preimage <| hu₂.prodMk ?_)

中文:
定理 EquicontinuousWithinAt.closure'
  结论: {A : Set Y} {u : Y -> X -> α} {S : Set X} {x₀ : X}
  证明: by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV, eventually_mem_nhdsWithin] with x hx hxS
  rw [SetCoe.forall] at *
  change A subseteq (fun f => (u f x₀, u f x)) ⁻¹' V at hx
  refine (closure_minimal hx <| hVclosed.preimage <| hu₂.prodMk ?_)

Depends on / 依赖: SetCoe, SetCoe.forall, closure_minimal, continuous_apply, eventually_mem_nhdsWithin, filter_upwards, hVclosed, hVclosed.preimage, mem_uniformity_isClosed, preimage, preimage_mono, prodMk, subseteq
-/
theorem EquicontinuousWithinAt.closure' {A : Set Y} {u : Y -> X -> α} {S : Set X} {x₀ : X}
    (hA : EquicontinuousWithinAt (u ∘ (↑) : A -> X -> α) S x₀) (hu₁ : Continuous (S.domRestrict ∘ u))
    (hu₂ : Continuous (eval x₀ ∘ u)) :
    EquicontinuousWithinAt (u ∘ (↑) : closure A -> X -> α) S x₀ := by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV, eventually_mem_nhdsWithin] with x hx hxS
  rw [SetCoe.forall] at *
  change A subseteq (fun f => (u f x₀, u f x)) ⁻¹' V at hx
  refine (closure_minimal hx <| hVclosed.preimage <| hu₂.prodMk ?_).trans (preimage_mono hVU)
  exact (continuous_apply ⟨x, hxS⟩).comp hu₁

/--
theorem `EquicontinuousAt.closure'` / 定理 `EquicontinuousAt.closure'`

English:
theorem EquicontinuousAt.closure'
  statement: {A : Set Y} {u : Y -> X -> α} {x₀ : X}
  proof: by
  rw [← equicontinuousWithinAt_univ] at hA ⊢
  exact hA.closure' (Pi.continuous_domRestrict _ |>.comp hu) (continuous_apply x₀ |>.comp hu)

中文:
定理 EquicontinuousAt.closure'
  结论: {A : Set Y} {u : Y -> X -> α} {x₀ : X}
  证明: by
  rw [← equicontinuousWithinAt_univ] at hA ⊢
  exact hA.closure' (Pi.continuous_domRestrict _ |>.comp hu) (continuous_apply x₀ |>.comp hu)

Depends on / 依赖: Pi.continuous_domRestrict, closure, continuous_apply, continuous_domRestrict, equicontinuousWithinAt_univ, hA.closure
-/
theorem EquicontinuousAt.closure' {A : Set Y} {u : Y -> X -> α} {x₀ : X}
    (hA : EquicontinuousAt (u ∘ (↑) : A -> X -> α) x₀) (hu : Continuous u) :
    EquicontinuousAt (u ∘ (↑) : closure A -> X -> α) x₀ := by
  rw [← equicontinuousWithinAt_univ] at hA ⊢
  exact hA.closure' (Pi.continuous_domRestrict _ |>.comp hu) (continuous_apply x₀ |>.comp hu)

/--
theorem `Set.EquicontinuousAt.closure` / 定理 `Set.EquicontinuousAt.closure`

English:
theorem Set.EquicontinuousAt.closure
  statement: {A : Set (X -> α)} {x₀ : X}
  proof: hA.closure' (u := id) continuous_id

中文:
定理 Set.EquicontinuousAt.closure
  结论: {A : Set (X -> α)} {x₀ : X}
  证明: hA.closure' (u := id) continuous_id
-/
protected theorem Set.EquicontinuousAt.closure {A : Set (X -> α)} {x₀ : X}
    (hA : A.EquicontinuousAt x₀) : (closure A).EquicontinuousAt x₀ :=
  hA.closure' (u := id) continuous_id

/--
theorem `Set.EquicontinuousWithinAt.closure` / 定理 `Set.EquicontinuousWithinAt.closure`

English:
theorem Set.EquicontinuousWithinAt.closure
  statement: {A : Set (X -> α)} {S : Set X} {x₀ : X}
  proof: hA.closure' (u := id) (Pi.continuous_domRestrict _) (continuous_apply _)

中文:
定理 Set.EquicontinuousWithinAt.closure
  结论: {A : Set (X -> α)} {S : Set X} {x₀ : X}
  证明: hA.closure' (u := id) (Pi.continuous_domRestrict _) (continuous_apply _)
-/
protected theorem Set.EquicontinuousWithinAt.closure {A : Set (X -> α)} {S : Set X} {x₀ : X}
    (hA : A.EquicontinuousWithinAt S x₀) :
    (closure A).EquicontinuousWithinAt S x₀ :=
  hA.closure' (u := id) (Pi.continuous_domRestrict _) (continuous_apply _)

/--
theorem `Equicontinuous.closure'` / 定理 `Equicontinuous.closure'`

English:
theorem Equicontinuous.closure'
  statement: {A : Set Y} {u : Y -> X -> α}
  proof: fun x => (hA x).closure' hu

中文:
定理 Equicontinuous.closure'
  结论: {A : Set Y} {u : Y -> X -> α}
  证明: fun x => (hA x).closure' hu

Depends on / 依赖: closure
-/
theorem Equicontinuous.closure' {A : Set Y} {u : Y -> X -> α}
    (hA : Equicontinuous (u ∘ (↑) : A -> X -> α)) (hu : Continuous u) :
    Equicontinuous (u ∘ (↑) : closure A -> X -> α) := fun x => (hA x).closure' hu

/--
theorem `EquicontinuousOn.closure'` / 定理 `EquicontinuousOn.closure'`

English:
theorem EquicontinuousOn.closure'
  statement: {A : Set Y} {u : Y -> X -> α} {S : Set X}
  proof: fun x hx => (hA x hx).closure' hu .comp hu by exact continuous_apply ⟨x, hx⟩

中文:
定理 EquicontinuousOn.closure'
  结论: {A : Set Y} {u : Y -> X -> α} {S : Set X}
  证明: fun x hx => (hA x hx).closure' hu .comp hu by exact continuous_apply ⟨x, hx⟩

Depends on / 依赖: closure, continuous_apply
-/
theorem EquicontinuousOn.closure' {A : Set Y} {u : Y -> X -> α} {S : Set X}
    (hA : EquicontinuousOn (u ∘ (↑) : A -> X -> α) S) (hu : Continuous (S.domRestrict ∘ u)) :
    EquicontinuousOn (u ∘ (↑) : closure A -> X -> α) S :=
fun x hx => (hA x hx).closure' hu .comp hu by exact continuous_apply ⟨x, hx⟩

/--
theorem `Set.Equicontinuous.closure` / 定理 `Set.Equicontinuous.closure`

English:
theorem Set.Equicontinuous.closure
  given: {A : Set <| X -> α} (hA : A.Equicontinuous)
  proof: fun x => Set.EquicontinuousAt.closure (hA x)

中文:
定理 Set.Equicontinuous.closure
  条件: {A : Set <| X -> α} (hA : A.Equicontinuous)
  证明: fun x => Set.EquicontinuousAt.closure (hA x)
-/
protected theorem Set.Equicontinuous.closure {A : Set <| X -> α} (hA : A.Equicontinuous) :
    (closure A).Equicontinuous := fun x => Set.EquicontinuousAt.closure (hA x)

/--
theorem `Set.EquicontinuousOn.closure` / 定理 `Set.EquicontinuousOn.closure`

English:
theorem Set.EquicontinuousOn.closure
  statement: {A : Set <| X -> α} {S : Set X}
  proof: fun x hx => Set.EquicontinuousWithinAt.closure (hA x hx)

中文:
定理 Set.EquicontinuousOn.closure
  结论: {A : Set <| X -> α} {S : Set X}
  证明: fun x hx => Set.EquicontinuousWithinAt.closure (hA x hx)
-/
protected theorem Set.EquicontinuousOn.closure {A : Set <| X -> α} {S : Set X}
    (hA : A.EquicontinuousOn S) : (closure A).EquicontinuousOn S :=
  fun x hx => Set.EquicontinuousWithinAt.closure (hA x hx)

/--
theorem `UniformEquicontinuousOn.closure'` / 定理 `UniformEquicontinuousOn.closure'`

English:
theorem UniformEquicontinuousOn.closure'
  statement: {A : Set Y} {u : Y -> β -> α} {S : Set β}
  proof: by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV, mem_inf_of_right (mem_principal_self _)]
  rintro ⟨x, y⟩ hxy ⟨hxS, hyS⟩
  rw [SetCoe.forall] at *
  change A subseteq (fun f => (u f x, u f y)) ⁻¹' V at hxy
  refine (closure_minimal hxy <| hVc

中文:
定理 UniformEquicontinuousOn.closure'
  结论: {A : Set Y} {u : Y -> β -> α} {S : Set β}
  证明: by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV, mem_inf_of_right (mem_principal_self _)]
  rintro ⟨x, y⟩ hxy ⟨hxS, hyS⟩
  rw [SetCoe.forall] at *
  change A subseteq (fun f => (u f x, u f y)) ⁻¹' V at hxy
  refine (closure_minimal hxy <| hVc

Depends on / 依赖: SetCoe, SetCoe.forall, closure_minimal, continuous_apply, filter_upwards, hVclosed, hVclosed.preimage, mem_inf_of_right, mem_principal_self, mem_uniformity_isClosed, preimage, preimage_mono, prodMk, subseteq
-/
theorem UniformEquicontinuousOn.closure' {A : Set Y} {u : Y -> β -> α} {S : Set β}
    (hA : UniformEquicontinuousOn (u ∘ (↑) : A -> β -> α) S) (hu : Continuous (S.domRestrict ∘ u)) :
    UniformEquicontinuousOn (u ∘ (↑) : closure A -> β -> α) S := by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV, mem_inf_of_right (mem_principal_self _)]
  rintro ⟨x, y⟩ hxy ⟨hxS, hyS⟩
  rw [SetCoe.forall] at *
  change A subseteq (fun f => (u f x, u f y)) ⁻¹' V at hxy
  refine (closure_minimal hxy <| hVclosed.preimage <| .prodMk ?_ ?_).trans (preimage_mono hVU)
  · exact (continuous_apply ⟨x, hxS⟩).comp hu
  · exact (continuous_apply ⟨y, hyS⟩).comp hu

/--
theorem `UniformEquicontinuous.closure'` / 定理 `UniformEquicontinuous.closure'`

English:
theorem UniformEquicontinuous.closure'
  statement: {A : Set Y} {u : Y -> β -> α}
  proof: by
  rw [← uniformEquicontinuousOn_univ] at hA ⊢
  exact hA.closure' (Pi.continuous_domRestrict _ |>.comp hu)

中文:
定理 UniformEquicontinuous.closure'
  结论: {A : Set Y} {u : Y -> β -> α}
  证明: by
  rw [← uniformEquicontinuousOn_univ] at hA ⊢
  exact hA.closure' (Pi.continuous_domRestrict _ |>.comp hu)

Depends on / 依赖: Pi.continuous_domRestrict, closure, continuous_domRestrict, hA.closure, uniformEquicontinuousOn_univ
-/
theorem UniformEquicontinuous.closure' {A : Set Y} {u : Y -> β -> α}
    (hA : UniformEquicontinuous (u ∘ (↑) : A -> β -> α)) (hu : Continuous u) :
    UniformEquicontinuous (u ∘ (↑) : closure A -> β -> α) := by
  rw [← uniformEquicontinuousOn_univ] at hA ⊢
  exact hA.closure' (Pi.continuous_domRestrict _ |>.comp hu)

/--
theorem `Set.UniformEquicontinuous.closure` / 定理 `Set.UniformEquicontinuous.closure`

English:
theorem Set.UniformEquicontinuous.closure
  statement: {A : Set <| β -> α}
  proof: UniformEquicontinuous.closure' (u := id) hA continuous_id

中文:
定理 Set.UniformEquicontinuous.closure
  结论: {A : Set <| β -> α}
  证明: UniformEquicontinuous.closure' (u := id) hA continuous_id
-/
protected theorem Set.UniformEquicontinuous.closure {A : Set <| β -> α}
    (hA : A.UniformEquicontinuous) : (closure A).UniformEquicontinuous :=
  UniformEquicontinuous.closure' (u := id) hA continuous_id

/--
theorem `Set.UniformEquicontinuousOn.closure` / 定理 `Set.UniformEquicontinuousOn.closure`

English:
theorem Set.UniformEquicontinuousOn.closure
  statement: {A : Set <| β -> α} {S : Set β}
  proof: UniformEquicontinuousOn.closure' (u := id) hA (Pi.continuous_domRestrict _)

中文:
定理 Set.UniformEquicontinuousOn.closure
  结论: {A : Set <| β -> α} {S : Set β}
  证明: UniformEquicontinuousOn.closure' (u := id) hA (Pi.continuous_domRestrict _)
-/
protected theorem Set.UniformEquicontinuousOn.closure {A : Set <| β -> α} {S : Set β}
    (hA : A.UniformEquicontinuousOn S) : (closure A).UniformEquicontinuousOn S :=
  UniformEquicontinuousOn.closure' (u := id) hA (Pi.continuous_domRestrict _)

/-
Implementation note: The following lemma (as well as all the following variations) could
theoretically be deduced from the "closure" statements above. For example, we could do:
```lean
theorem Filter.Tendsto.continuousAt_of_equicontinuousAt {l : Filter ι} [l.NeBot] {F : ι → X → α}
    {f : X → α} {x₀ : X} (h₁ : Tendsto F l (𝓝 f)) (h₂ : EquicontinuousAt F x₀) :
    ContinuousAt f x₀ :=
  (equicontinuousAt_iff_range.mp h₂).closure.continuousAt
    ⟨f, mem_closure_of_tendsto h₁ <| Eventually.of_forall mem_range_self⟩

theorem Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous {l : Filter ι} [l.NeBot]
    {F : ι → β → α} {f : β → α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : UniformEquicontinuous F) :
    UniformContinuous f :=
  (uniformEquicontinuous_iff_range.mp h₂).closure.uniformContinuous
    ⟨f, mem_closure_of_tendsto h₁ <| Eventually.of_forall mem_range_self⟩
```

Unfortunately, the proofs get painful when dealing with the relative case as one needs to change
the ambient topology. So it turns out to be easier to re-do the proof by hand.
-/

/--
theorem `Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt` / 定理 `Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt`

English:
theorem Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt
  statement: {l : Filter ι} [l.NeBot]
  proof: by
  intro U hU; rw [mem_map]
  rcases UniformSpace.mem_nhds_iff.mp hU with ⟨V, hV, hVU⟩
  rcases mem_uniformity_isClosed hV with ⟨W, hW, hWclosed, hWV⟩
  filter_upwards [h₃ W hW, eventually_mem_nhdsWithin] with x hx hxS using
hVU ball_mono hWV (f x₀) hWclosed.mem_of_tendsto (h₂.prodMk_nhds (h₁ x hx

中文:
定理 Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt
  结论: {l : Filter ι} [l.NeBot]
  证明: by
  intro U hU; rw [mem_map]
  rcases UniformSpace.mem_nhds_iff.mp hU with ⟨V, hV, hVU⟩
  rcases mem_uniformity_isClosed hV with ⟨W, hW, hWclosed, hWV⟩
  filter_upwards [h₃ W hW, eventually_mem_nhdsWithin] with x hx hxS using
hVU ball_mono hWV (f x₀) hWclosed.mem_of_tendsto (h₂.prodMk_nhds (h₁ x hx

Depends on / 依赖: Eventually, Eventually.of_forall, UniformSpace, UniformSpace.mem_nhds_iff.mp, ball_mono, eventually_mem_nhdsWithin, filter_upwards, hWclosed, hWclosed.mem_of_tendsto, mem_map, mem_nhds_iff, mem_of_tendsto, mem_uniformity_isClosed, of_forall, prodMk_nhds
-/
theorem Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt {l : Filter ι} [l.NeBot]
    {F : ι -> X -> α} {f : X -> α} {S : Set X} {x₀ : X} (h₁ : forall x in S, Tendsto (F · x) l (𝓝 (f x)))
    (h₂ : Tendsto (F · x₀) l (𝓝 (f x₀))) (h₃ : EquicontinuousWithinAt F S x₀) :
    ContinuousWithinAt f S x₀ := by
  intro U hU; rw [mem_map]
  rcases UniformSpace.mem_nhds_iff.mp hU with ⟨V, hV, hVU⟩
  rcases mem_uniformity_isClosed hV with ⟨W, hW, hWclosed, hWV⟩
  filter_upwards [h₃ W hW, eventually_mem_nhdsWithin] with x hx hxS using
hVU ball_mono hWV (f x₀) hWclosed.mem_of_tendsto (h₂.prodMk_nhds (h₁ x hxS))
    Eventually.of_forall hx

/--
theorem `Filter.Tendsto.continuousAt_of_equicontinuousAt` / 定理 `Filter.Tendsto.continuousAt_of_equicontinuousAt`

English:
theorem Filter.Tendsto.continuousAt_of_equicontinuousAt
  statement: {l : Filter ι} [l.NeBot] {F : ι -> X -> α}
  proof: by
  rw [← continuousWithinAt_univ]; rw [← equicontinuousWithinAt_univ]; rw [tendsto_pi_nhds] at *
  exact continuousWithinAt_of_equicontinuousWithinAt (fun x _ => h₁ x) (h₁ x₀) h₂

中文:
定理 Filter.Tendsto.continuousAt_of_equicontinuousAt
  结论: {l : Filter ι} [l.NeBot] {F : ι -> X -> α}
  证明: by
  rw [← continuousWithinAt_univ]; rw [← equicontinuousWithinAt_univ]; rw [tendsto_pi_nhds] at *
  exact continuousWithinAt_of_equicontinuousWithinAt (fun x _ => h₁ x) (h₁ x₀) h₂
-/
theorem Filter.Tendsto.continuousAt_of_equicontinuousAt {l : Filter ι} [l.NeBot] {F : ι -> X -> α}
    {f : X -> α} {x₀ : X} (h₁ : Tendsto F l (𝓝 f)) (h₂ : EquicontinuousAt F x₀) :
    ContinuousAt f x₀ := by
  rw [← continuousWithinAt_univ]; rw [← equicontinuousWithinAt_univ]; rw [tendsto_pi_nhds] at *
  exact continuousWithinAt_of_equicontinuousWithinAt (fun x _ => h₁ x) (h₁ x₀) h₂

/--
theorem `Filter.Tendsto.continuous_of_equicontinuous` / 定理 `Filter.Tendsto.continuous_of_equicontinuous`

English:
theorem Filter.Tendsto.continuous_of_equicontinuous
  statement: {l : Filter ι} [l.NeBot] {F : ι -> X -> α}
  proof: continuous_iff_continuousAt.mpr fun x => h₁.continuousAt_of_equicontinuousAt (h₂ x)

中文:
定理 Filter.Tendsto.continuous_of_equicontinuous
  结论: {l : Filter ι} [l.NeBot] {F : ι -> X -> α}
  证明: continuous_iff_continuousAt.mpr fun x => h₁.continuousAt_of_equicontinuousAt (h₂ x)

Depends on / 依赖: continuousAt_of_equicontinuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr
-/
theorem Filter.Tendsto.continuous_of_equicontinuous {l : Filter ι} [l.NeBot] {F : ι -> X -> α}
    {f : X -> α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : Equicontinuous F) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x => h₁.continuousAt_of_equicontinuousAt (h₂ x)

/--
theorem `Filter.Tendsto.continuousOn_of_equicontinuousOn` / 定理 `Filter.Tendsto.continuousOn_of_equicontinuousOn`

English:
theorem Filter.Tendsto.continuousOn_of_equicontinuousOn
  statement: {l : Filter ι} [l.NeBot] {F : ι -> X -> α}
  proof: fun x hx => Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt h₁ (h₁ x hx) (h₂ x hx)

中文:
定理 Filter.Tendsto.continuousOn_of_equicontinuousOn
  结论: {l : Filter ι} [l.NeBot] {F : ι -> X -> α}
  证明: fun x hx => Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt h₁ (h₁ x hx) (h₂ x hx)

Depends on / 依赖: Filter, Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt, Tendsto, continuousWithinAt_of_equicontinuousWithinAt
-/
theorem Filter.Tendsto.continuousOn_of_equicontinuousOn {l : Filter ι} [l.NeBot] {F : ι -> X -> α}
    {f : X -> α} {S : Set X} (h₁ : forall x in S, Tendsto (F · x) l (𝓝 (f x)))
    (h₂ : EquicontinuousOn F S) : ContinuousOn f S :=
  fun x hx => Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt h₁ (h₁ x hx) (h₂ x hx)

/--
theorem `Filter.Tendsto.uniformContinuousOn_of_uniformEquicontinuousOn` / 定理 `Filter.Tendsto.uniformContinuousOn_of_uniformEquicontinuousOn`

English:
theorem Filter.Tendsto.uniformContinuousOn_of_uniformEquicontinuousOn
  statement: {l : Filter ι} [l.NeBot]
  proof: by
  intro U hU; rw [mem_map]
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [h₂ V hV, mem_inf_of_right (mem_principal_self _)]
  rintro ⟨x, y⟩ hxy ⟨hxS, hyS⟩
exact hVU hVclosed.mem_of_tendsto ((h₁ x hxS).prodMk_nhds (h₁ y hyS))
    Eventually.of_forall hxy

中文:
定理 Filter.Tendsto.uniformContinuousOn_of_uniformEquicontinuousOn
  结论: {l : Filter ι} [l.NeBot]
  证明: by
  intro U hU; rw [mem_map]
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [h₂ V hV, mem_inf_of_right (mem_principal_self _)]
  rintro ⟨x, y⟩ hxy ⟨hxS, hyS⟩
exact hVU hVclosed.mem_of_tendsto ((h₁ x hxS).prodMk_nhds (h₁ y hyS))
    Eventually.of_forall hxy

Depends on / 依赖: Eventually, Eventually.of_forall, filter_upwards, hVclosed, hVclosed.mem_of_tendsto, mem_inf_of_right, mem_map, mem_of_tendsto, mem_principal_self, mem_uniformity_isClosed, of_forall, prodMk_nhds
-/
theorem Filter.Tendsto.uniformContinuousOn_of_uniformEquicontinuousOn {l : Filter ι} [l.NeBot]
    {F : ι -> β -> α} {f : β -> α} {S : Set β} (h₁ : forall x in S, Tendsto (F · x) l (𝓝 (f x)))
    (h₂ : UniformEquicontinuousOn F S) :
    UniformContinuousOn f S := by
  intro U hU; rw [mem_map]
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [h₂ V hV, mem_inf_of_right (mem_principal_self _)]
  rintro ⟨x, y⟩ hxy ⟨hxS, hyS⟩
exact hVU hVclosed.mem_of_tendsto ((h₁ x hxS).prodMk_nhds (h₁ y hyS))
    Eventually.of_forall hxy

/--
theorem `Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous` / 定理 `Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous`

English:
theorem Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous
  statement: {l : Filter ι} [l.NeBot]
  proof: by
  rw [← uniformContinuousOn_univ]; rw [← uniformEquicontinuousOn_univ]; rw [tendsto_pi_nhds] at *
  exact uniformContinuousOn_of_uniformEquicontinuousOn (fun x _ => h₁ x) h₂

中文:
定理 Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous
  结论: {l : Filter ι} [l.NeBot]
  证明: by
  rw [← uniformContinuousOn_univ]; rw [← uniformEquicontinuousOn_univ]; rw [tendsto_pi_nhds] at *
  exact uniformContinuousOn_of_uniformEquicontinuousOn (fun x _ => h₁ x) h₂
-/
theorem Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous {l : Filter ι} [l.NeBot]
    {F : ι -> β -> α} {f : β -> α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : UniformEquicontinuous F) :
    UniformContinuous f := by
  rw [← uniformContinuousOn_univ]; rw [← uniformEquicontinuousOn_univ]; rw [tendsto_pi_nhds] at *
  exact uniformContinuousOn_of_uniformEquicontinuousOn (fun x _ => h₁ x) h₂

/--
theorem `EquicontinuousAt.tendsto_of_mem_closure` / 定理 `EquicontinuousAt.tendsto_of_mem_closure`

English:
theorem EquicontinuousAt.tendsto_of_mem_closure
  statement: {l : Filter ι} {F : ι -> X -> α} {f : X -> α}
  proof: by
  rw [(nhds_basis_uniformity (𝓤 α).basis_sets).tendsto_right_iff] at hf ⊢
  intro U hU
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVs, hVU⟩
  rw [mem_closure_iff_nhdsWithin_neBot] at hx
  have : forallᶠ y in 𝓝[s] x, y in s ∧ (forall i, (F i x, F i y) in V) ∧ (f y, z) in V :=
even

中文:
定理 EquicontinuousAt.tendsto_of_mem_closure
  结论: {l : Filter ι} {F : ι -> X -> α} {f : X -> α}
  证明: by
  rw [(nhds_basis_uniformity (𝓤 α).basis_sets).tendsto_right_iff] at hf ⊢
  intro U hU
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVs, hVU⟩
  rw [mem_closure_iff_nhdsWithin_neBot] at hx
  have : forallᶠ y in 𝓝[s] x, y in s ∧ (forall i, (F i x, F i y) in V) ∧ (f y, z) in V :=
even

Depends on / 依赖: ball_mem_nhds, basis_sets, comp_comp_symm_mem_uniformity_sets, eventually_mem_nhdsWithin, eventually_mem_nhdsWithin.and, filter_mono, filter_upwards, mem_closure_iff_nhdsWithin_neBot, nhdsWithin_le_nhds, nhds_basis_uniformity, tendsto_right_iff, this.exists
-/
theorem EquicontinuousAt.tendsto_of_mem_closure {l : Filter ι} {F : ι -> X -> α} {f : X -> α}
    {s : Set X} {x : X} {z : α} (hF : EquicontinuousAt F x) (hf : Tendsto f (𝓝[s] x) (𝓝 z))
    (hs : forall y in s, Tendsto (F · y) l (𝓝 (f y))) (hx : x in closure s) :
    Tendsto (F · x) l (𝓝 z) := by
  rw [(nhds_basis_uniformity (𝓤 α).basis_sets).tendsto_right_iff] at hf ⊢
  intro U hU
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVs, hVU⟩
  rw [mem_closure_iff_nhdsWithin_neBot] at hx
  have : forallᶠ y in 𝓝[s] x, y in s ∧ (forall i, (F i x, F i y) in V) ∧ (f y, z) in V :=
eventually_mem_nhdsWithin.and ((hF V hV).filter_mono nhdsWithin_le_nhds).and (hf V hV)
  rcases this.exists with ⟨y, hys, hFy, hfy⟩
  filter_upwards [hs y hys (ball_mem_nhds _ hV)] with i hi
  exact hVU ⟨_, ⟨_, hFy i, mem_ball_symmetry.2 hi⟩, hfy⟩

/--
theorem `Equicontinuous.isClosed_setOfPred_tendsto` / 定理 `Equicontinuous.isClosed_setOfPred_tendsto`

English:
theorem Equicontinuous.isClosed_setOfPred_tendsto
  statement: {l : Filter ι} {F : ι -> X -> α} {f : X -> α}
  proof: closure_subset_iff_isClosed.mp fun x hx =>
    (hF x).tendsto_of_mem_closure (hf.continuousAt.mono_left inf_le_left) (fun _ => id) hx

@[deprecated (since := "2026-07-09")]
alias Equicontinuous.isClosed_setOf_tendsto := Equicontinuous.isClosed_setOfPred_tendsto

中文:
定理 Equicontinuous.isClosed_setOfPred_tendsto
  结论: {l : Filter ι} {F : ι -> X -> α} {f : X -> α}
  证明: closure_subset_iff_isClosed.mp fun x hx =>
    (hF x).tendsto_of_mem_closure (hf.continuousAt.mono_left inf_le_left) (fun _ => id) hx

@[deprecated (since := "2026-07-09")]
alias Equicontinuous.isClosed_setOf_tendsto := Equicontinuous.isClosed_setOfPred_tendsto

Depends on / 依赖: closure_subset_iff_isClosed, closure_subset_iff_isClosed.mp, continuousAt, hf.continuousAt.mono_left, inf_le_left, mono_left, tendsto_of_mem_closure
-/
theorem Equicontinuous.isClosed_setOfPred_tendsto {l : Filter ι} {F : ι -> X -> α} {f : X -> α}
    (hF : Equicontinuous F) (hf : Continuous f) :
    IsClosed {x | Tendsto (F · x) l (𝓝 (f x))} :=
  closure_subset_iff_isClosed.mp fun x hx =>
    (hF x).tendsto_of_mem_closure (hf.continuousAt.mono_left inf_le_left) (fun _ => id) hx

@[deprecated (since := "2026-07-09")]
alias Equicontinuous.isClosed_setOf_tendsto := Equicontinuous.isClosed_setOfPred_tendsto

end

end
