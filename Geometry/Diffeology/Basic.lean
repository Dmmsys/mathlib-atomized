/-
Copyright (c) 2024 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Diffeological spaces

A diffeological space is a concrete sheaf on the site of cartesian spaces ℝⁿ and smooth maps
between them, or equivalently a type `X` with a well-behaved notion of smoothness for functions from
the spaces ℝⁿ to X - see https://ncatlab.org/nlab/show/diffeological+space. In this file we focus on
the latter viewpoint and define some of the basic notions of diffeology, like diffeological spaces
and smooth maps between them.

Concretely, this means that for our purposes a diffeological space is a type `X` together with a set
`plots n` of maps ℝⁿ → X for each n (called plots), such that the following three properties hold:
* Every constant map is a plot.
* For every plot p : ℝⁿ → X and smooth map f : ℝᵐ → ℝⁿ, p ∘ f is a plot.
* Every map p : ℝⁿ → X that is locally smooth is a plot, where by locally smooth we mean that ℝⁿ can
  be covered by open sets U such that p ∘ f is a plot for every smooth f : ℝᵐ → U.

Every normed space, smooth manifold etc. is then naturally a diffeological space by simply taking
the plots to be those maps ℝⁿ → X that are smooth in the traditional sense. A map `f : X → Y`
between diffeological spaces is furthermore called smooth if postcomposition with it sends plots of
`X` to plots of `Y`. This is equivalent to the usual definition of smoothness for maps between e.g.
manifolds, and equivalent to being a plot for maps p : ℝⁿ → X.

In addition to this notion of smoothness, every diffeological space `X` also comes equipped with a
natural diffeology, called the D-topology; it is the finest topology on `X` that makes all plots
continuous, and consists precisely of those sets whose preimages under plots are all open. This
recovers the standard topology of e.g. normed spaces and manifolds, and makes all smooth maps
continuous. We provide this as a definition but not as an instance, for reasons outlined in the
implementation details below.

## Main definitions / results

* `DiffeologicalSpace X`: the type of diffeologies on a type `X`.
* `IsPlot p`: predicate stating that a map p : ℝⁿ → X is a plot, i.e. belongs to the diffeology
  on `X`.
* `DSmooth f`: predicate stating that a map `f : X → Y` between diffeological spaces is smooth in
  the sense that it sends plots to plots. This is the correct notion of morphisms between
  diffeological spaces.
* `dTopology`: the D-topology on a diffeological space, consisting of all sets `U` whose preimage
  `p ⁻¹' u` is open for all plots `p`. This is a definition rather than an instance to avoid
  typeclass diamonds (see below), and meant for use with notation such as
  `Continuous[_, dTopology]`.
* `IsDTopologyCompatible X`: typeclass stating that `X` is equipped with a topology that is equal
  (but not necessarily defeq) to the D-topology.
* `NormedSpace.toDiffeology`: the standard diffeology on any finite-dimensional normed space `X`,
  consisting of all conventionally smooth maps ℝⁿ → X. This is again a definition rather than a
  instance for typeclass diamond reasons; however, we do put this as an instance on `ℝ` and
  `EuclideanSpace ℝ ι` for finite `ι`.
* `IsContDiffCompatible X`: typeclass stating that the diffeology on a normed space `X` is equal to
  the diffeology whose plots are precisely the smooth maps.
* `isPlot_iff_dSmooth`: a map ℝⁿ → X is a plot iff it is smooth.
* `dSmooth_iff_contDiff`: a map between finite-dimensional normed spaces is smooth in the sense of
  `DSmooth` iff it is smooth in the sense of `ContDiff ℝ ∞`.

## Implementation notes

### Choice of test spaces

Instead of defining diffeologies as collections of plots ℝⁿ → X whose domains are the spaces ℝⁿ, we
could have also defined them in terms of maps from some other collection of test spaces; for
example:
* all open balls in the spaces ℝⁿ
* all open subsets of the spaces ℝⁿ
* all finite-dimensional normed spaces, or open balls therein / open subsets thereof
* all finite-dimensional smooth manifolds.

All of these result in equivalent notions of diffeologies and smooth maps; the abstract way to see
this is that the corresponding sites are all dense subsites of the site of finite-dimensional smooth
manifolds, and hence give rise to equivalent sheaf topoi. Which of those sites / collections of test
spaces to use is hence mainly a matter of convenience; we have gone with the cartesian spaces ℝⁿ
mainly for two reasons:
* They are the simplest to work with for practical purposes: maps between subsets are more annoying
  to deal with formally than maps between types, and e.g. smooth manifolds are extremely annoying
  to quantify over, while the cartesian spaces ℝⁿ are indexed simply by the natural numbers ℕ.
* Working with e.g. all finite-dimensional normed spaces instead of this particular choice of
  representatives would lead to an unnecessary universe bump.

One downside of this choice compared to that of all open subsets of ℝⁿ is however that it makes the
sheaf condition / locality condition of diffeologies ("any map that is locally a plot is also
globally a plot") somewhat awkward to state and prove. To mitigate this, we provide
`DiffeologicalSpace.ofPlotsOn` as a way to construct a diffeology from plots whose domains are
subsets of ℝⁿ. See the definition of `NormedSpace.toDiffeology` for an example where this is used.

### D-Topology

While the D-topology is quite well-behaved in some regards, it does unfortunately not always commute
with e.g. products. This means that it can not be registered as an instance - otherwise, there would
be two `TopologicalSpace`-instances on binary products, the product topology of the D-topologies on
the factors and the D-topology of the product diffeology. For emphasis we repeat: in general these
topologies can be mathematically distinct not just non-defeq. We thus instead define a typeclass
`IsDTopologyCompatible X` to express when the topology on `X` does match the D-topology, and also
give the D-topology the short name `dTopology` to enable use of notations such as
`Continuous[_, dTopology]` for continuity with respect to the D-topology.

In order to make it easier to work with diffeological spaces whose natural diffeology does match
the D-topology, we also include the D-topology as part of the data of `DiffeologicalSpace X`.
This allows the diffeologies on e.g. ℝⁿ, manifolds and quotients of diffeological spaces to be
defined in such a way that the D-topology is defeq to the topology that the space already carries.

### Diffeologies on normed spaces

Every normed spaces carries a natural diffeology consisting of all smooth maps from ℝⁿ. While this
"normed space diffeology" does commute with arbitrary products, we can't register it as an instance
because it wouldn't be defeq to the product diffeology on products of normed spaces. We thus only
give it as a definition (`NormedSpace.toDiffeology`) instead of an instance, and instead provide a
typeclass `IsContDiffCompatible X` for talking about normed spaces equipped with the normed space
diffeology.

To make working with finite-dimensional spaces easier, `NormedSpace.toDiffeology` is defined in such
a way that its D-topology is defeq to the topology induced by the norm - however, this currently
comes at the cost of making the definition work only on finite-dimensional spaces. It should be
possible to extend this to all normed spaces though in the future.

## TODO

Much of the basic theory of diffeological spaces has already been formalised at
https://github.com/peabrainiac/lean-orbifolds and just needs to be upstreamed. However, some TODOs
that haven't been formalised at all yet and only depend on the material here are:
* Generalise `NormedSpace.toDiffeology` to infinite-dimensional normed spaces. The hard part of this
  is showing that the D-topology of any normed space is just its usual topology, as is needed to
  make that equality definitional. On paper, this is relatively straightforward:
  for a set U ⊆ X that is not open under the standard normed space topology, take a sequence x_i
  outside of U that converges to a point in U, a smooth map ℝ → X under which a convergent sequence
  in ℝ maps to this sequence (x_i), and use it to conclude that U is not D-open either. However,
  constructing the needed smooth map explicitly is probably a lot of work.
* Generalise `dSmooth_iff_contDiff` to infinite-dimensional normed spaces if possible. There should
  be some references at least for the case of Banach spaces in the literature.

## References

* [Patrick Iglesias-Zemmour, *Diffeology*][zemmour2013diffeology]
* <https://ncatlab.org/nlab/show/diffeological+space>

## Tags
diffeology, diffeological space, smoothness, smooth function
-/

@[expose] public section

noncomputable section

assert_not_exists ChartedSpace

local macro:max "𝔼" noWs n:superscript(term) : term => `(EuclideanSpace Real (Fin $(⟨n.raw[0]⟩)))

open Topology ContDiff

/--
Definition of `DiffeologicalSpace` / `DiffeologicalSpace` 的定义

English:
class DiffeologicalSpace
  parameters: (X : Type*)
  axioms and operations (6):
    - plots((n : Nat)) : Set (𝔼ⁿ -> X)
    - constant_plots({n : Nat} (x : X)) : (fun _ => x) in plots n
    - plot_reparam({n m : Nat} {p : 𝔼ᵐ -> X} {f : 𝔼ⁿ -> 𝔼ᵐ} (hp : p in plots m) (hf : ContDiff Real ∞ f)) : p ∘ f in plots n
    - locality({n : Nat} {p : 𝔼ⁿ -> X} (hp : forall x : 𝔼ⁿ, exists u : Set 𝔼ⁿ, IsOpen u ∧ x in u ∧ forall {m : Nat} {f : 𝔼ᵐ -> 𝔼ⁿ}, (forall x, f x in u) -> ContDiff Real ∞ f -> p ∘ f in plots m)) : p in plots n
    - dTopology : TopologicalSpace X  [default: { IsOpen u := forall ⦃n : Nat⦄, forall p in plots n, IsOpen ]
    - isOpen_iff_preimages_plots({u : Set X}) : dTopology.IsOpen u ↔ forall {n : Nat}, forall p in plots n, IsOpen (p ⁻¹' u)  [default: by rfl]

中文:
类 Diffeological空间
  参数: (X : 类型)
  公理与运算 (6 个):
    - plots((n : 自然数)) : 集合 (𝔼ⁿ -> X)
    - constant_plots({n : 自然数} (x : X)) : (fun _ => x) in plots n
    - plot_reparam({n m : 自然数} {p : 𝔼ᵐ -> X} {f : 𝔼ⁿ -> 𝔼ᵐ} (hp : p in plots m) (hf : 连续可微 实数 ∞ f)) : p ∘ f in plots n
    - locality({n : 自然数} {p : 𝔼ⁿ -> X} (hp : 对任意 x : 𝔼ⁿ, 存在 u : 集合 𝔼ⁿ, 是开集 u ∧ x in u ∧ 对任意 {m : 自然数} {f : 𝔼ᵐ -> 𝔼ⁿ}, (对任意 x, f x in u) -> 连续可微 实数 ∞ f -> p ∘ f in plots m)) : p in plots n
    - dTopology : 拓扑空间 X  [默认: { IsOpen u := forall ⦃n : Nat⦄, forall p in plots n, IsOpen ]
    - isOpen_iff_preimages_plots({u : 集合 X}) : dTopology.是开集 u ↔ 对任意 {n : 自然数}, 对任意 p in plots n, 是开集 (p ⁻¹' u)  [默认: by rfl]
-/
class DiffeologicalSpace (X : Type*) where
  /-- The plots `EuclideanSpace ℝ (Fin n) → X` representing the smooth ways to map
  `EuclideanSpace ℝ (Fin n)` into `X`. This is the main
  piece of data underlying the diffeology. -/
  plots (n : Nat) : Set (𝔼ⁿ -> X)
  /-- Every constant map needs to be a plot. -/
  constant_plots {n : Nat} (x : X) : (fun _ => x) in plots n
  /-- Smooth reparametrisations of plots need to be plots. -/
  plot_reparam {n m : Nat} {p : 𝔼ᵐ -> X} {f : 𝔼ⁿ -> 𝔼ᵐ} (hp : p in plots m) (hf : ContDiff Real ∞ f) :
    p ∘ f in plots n
  /-- Every locally smooth map `EuclideanSpace ℝ (Fin n) → X` is a plot. -/
  locality {n : Nat} {p : 𝔼ⁿ -> X} (hp : forall x : 𝔼ⁿ, exists u : Set 𝔼ⁿ, IsOpen u ∧ x in u ∧
    forall {m : Nat} {f : 𝔼ᵐ -> 𝔼ⁿ}, (forall x, f x in u) -> ContDiff Real ∞ f -> p ∘ f in plots m) : p in plots n
  /-- The D-topology of the diffeology. This is included as part of the data in order to give
  control over what the D-topology is defeq to. See also note [forgetful inheritance]. -/
  dTopology : TopologicalSpace X := {
    IsOpen u := forall ⦃n : Nat⦄, forall p in plots n, IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ _ => isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp =>
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp =>
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu => hs u hu p hp }
  /-- The D-topology consists of exactly those sets whose preimages under plots are all open. -/
  isOpen_iff_preimages_plots {u : Set X} :
    dTopology.IsOpen u ↔ forall {n : Nat}, forall p in plots n, IsOpen (p ⁻¹' u) := by rfl

namespace Diffeology

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

section Defs

alias dTopology := DiffeologicalSpace.dTopology

/-- A map `p : EuclideanSpace ℝ (Fin n) → X` is called a plot iff it is part of the diffeology on
`X`. This is equivalent to `p` being smooth with respect to the standard diffeology on
`EuclideanSpace ℝ (Fin n)`. -/
@[fun_prop]
/--
Definition of `IsPlot` / `IsPlot` 的定义

English:
definition IsPlot
  signature: {n : Nat} (p : 𝔼ⁿ -> X)
  body: p in DiffeologicalSpace.plots n

中文:
定义 IsPlot
  签名: {n : 自然数} (p : 𝔼ⁿ -> X)
  定义体: p in DiffeologicalSpace.plots n

Depends on / 依赖: DiffeologicalSpace, DiffeologicalSpace.plots
-/
def IsPlot {n : Nat} (p : 𝔼ⁿ -> X) : Prop := p in DiffeologicalSpace.plots n

/-- A function between diffeological spaces is smooth iff composition with it preserves
smoothness of plots. -/
@[fun_prop]
/--
Definition of `DSmooth` / `DSmooth` 的定义

English:
definition DSmooth
  signature: (f : X -> Y)
  body: forall (n : Nat) (p : 𝔼ⁿ -> X), IsPlot p -> IsPlot (f ∘ p)

中文:
定义 DSmooth
  签名: (f : X -> Y)
  定义体: forall (n : Nat) (p : 𝔼ⁿ -> X), IsPlot p -> IsPlot (f ∘ p)

Depends on / 依赖: IsPlot
-/
def DSmooth (f : X -> Y) : Prop := forall (n : Nat) (p : 𝔼ⁿ -> X), IsPlot p -> IsPlot (f ∘ p)

end Defs

@[ext]
/--
theorem `_root_.DiffeologicalSpace.ext` / 定理 `_root_.DiffeologicalSpace.ext`

English:
theorem _root_.DiffeologicalSpace.ext
  statement: {X : Type*} {d₁ d₂ : DiffeologicalSpace X}
  proof: by
  obtain ⟨p₁, _, _, _, t₁, h₁⟩ := d₁
  obtain ⟨p₂, _, _, _, t₂, h₂⟩ := d₂
  congr 1; ext s
  exact ((show p₁ = p₂ from h) ▸ @h₁ s).trans (@h₂ s).symm

@[fun_prop]

中文:
定理 _root_.Diffeological空间.ext
  结论: {X : 类型} {d₁ d₂ : Diffeological空间 X}
  证明: by
  obtain ⟨p₁, _, _, _, t₁, h₁⟩ := d₁
  obtain ⟨p₂, _, _, _, t₂, h₂⟩ := d₂
  congr 1; ext s
  exact ((show p₁ = p₂ from h) ▸ @h₁ s).trans (@h₂ s).symm

@[fun_prop]
-/
protected theorem _root_.DiffeologicalSpace.ext {X : Type*} {d₁ d₂ : DiffeologicalSpace X}
    (h : @IsPlot _ d₁ = @IsPlot _ d₂) : d₁ = d₂ := by
  obtain ⟨p₁, _, _, _, t₁, h₁⟩ := d₁
  obtain ⟨p₂, _, _, _, t₂, h₂⟩ := d₂
  congr 1; ext s
  exact ((show p₁ = p₂ from h) ▸ @h₁ s).trans (@h₂ s).symm

@[fun_prop]
/--
lemma `isPlot_const` / 引理 `isPlot_const`

English:
lemma isPlot_const
  given: {n : Nat} {x : X}
  statement: IsPlot (fun _ => x : 𝔼ⁿ -> X)
  proof: DiffeologicalSpace.constant_plots x

中文:
引理 isPlot_const
  条件: {n : 自然数} {x : X}
  结论: IsPlot (fun _ => x : 𝔼ⁿ -> X)
  证明: DiffeologicalSpace.constant_plots x

Depends on / 依赖: DiffeologicalSpace, DiffeologicalSpace.constant_plots, constant_plots
-/
lemma isPlot_const {n : Nat} {x : X} : IsPlot (fun _ => x : 𝔼ⁿ -> X) :=
  DiffeologicalSpace.constant_plots x

/--
lemma `isPlot_reparam` / 引理 `isPlot_reparam`

English:
lemma isPlot_reparam
  given: {n m : Nat} {p : 𝔼ᵐ -> X} {f : 𝔼ⁿ -> 𝔼ᵐ} (hp : IsPlot p) (hf : ContDiff Real ∞ f)
  proof: DiffeologicalSpace.plot_reparam hp hf

中文:
引理 isPlot_reparam
  条件: {n m : 自然数} {p : 𝔼ᵐ -> X} {f : 𝔼ⁿ -> 𝔼ᵐ} (hp : IsPlot p) (hf : 连续可微 实数 ∞ f)
  证明: DiffeologicalSpace.plot_reparam hp hf

Depends on / 依赖: DiffeologicalSpace, DiffeologicalSpace.plot_reparam, plot_reparam
-/
lemma isPlot_reparam {n m : Nat} {p : 𝔼ᵐ -> X} {f : 𝔼ⁿ -> 𝔼ᵐ} (hp : IsPlot p) (hf : ContDiff Real ∞ f) :
    IsPlot (p ∘ f) :=
  DiffeologicalSpace.plot_reparam hp hf

/--
lemma `IsPlot.dSmooth_comp` / 引理 `IsPlot.dSmooth_comp`

English:
lemma IsPlot.dSmooth_comp
  statement: {n : Nat} {p : 𝔼ⁿ -> X} {f : X -> Y}
  proof: hf n p hp

@[fun_prop]

中文:
引理 IsPlot.dSmooth_comp
  结论: {n : 自然数} {p : 𝔼ⁿ -> X} {f : X -> Y}
  证明: hf n p hp

@[fun_prop]
-/
protected lemma IsPlot.dSmooth_comp {n : Nat} {p : 𝔼ⁿ -> X} {f : X -> Y}
    (hp : IsPlot p) (hf : DSmooth f) : IsPlot (f ∘ p) :=
  hf n p hp

@[fun_prop]
/--
lemma `IsPlot.dSmooth_comp'` / 引理 `IsPlot.dSmooth_comp'`

English:
lemma IsPlot.dSmooth_comp'
  statement: {n : Nat} {p : 𝔼ⁿ -> X} {f : X -> Y}
  proof: hf n p hp

中文:
引理 IsPlot.dSmooth_comp'
  结论: {n : 自然数} {p : 𝔼ⁿ -> X} {f : X -> Y}
  证明: hf n p hp
-/
protected lemma IsPlot.dSmooth_comp' {n : Nat} {p : 𝔼ⁿ -> X} {f : X -> Y}
    (hp : IsPlot p) (hf : DSmooth f) : IsPlot fun x => f (p x) :=
  hf n p hp

/--
lemma `isOpen_iff_preimages_plots` / 引理 `isOpen_iff_preimages_plots`

English:
lemma isOpen_iff_preimages_plots
  given: {u : Set X}
  proof: DiffeologicalSpace.isOpen_iff_preimages_plots

中文:
引理 isOpen_iff_preimages_plots
  条件: {u : 集合 X}
  证明: DiffeologicalSpace.isOpen_iff_preimages_plots

Depends on / 依赖: DiffeologicalSpace, DiffeologicalSpace.isOpen_iff_preimages_plots, isOpen_iff_preimages_plots
-/
lemma isOpen_iff_preimages_plots {u : Set X} :
    IsOpen[dTopology] u ↔ forall (n : Nat) (p : 𝔼ⁿ -> X), IsPlot p -> IsOpen (p ⁻¹' u) :=
  DiffeologicalSpace.isOpen_iff_preimages_plots

/--
lemma `IsPlot.continuous` / 引理 `IsPlot.continuous`

English:
lemma IsPlot.continuous
  given: {n : Nat} {p : 𝔼ⁿ -> X} (hp : IsPlot p)
  proof: continuous_def.2 fun _ hu => isOpen_iff_preimages_plots.1 hu n p hp

中文:
引理 IsPlot.continuous
  条件: {n : 自然数} {p : 𝔼ⁿ -> X} (hp : IsPlot p)
  证明: continuous_def.2 fun _ hu => isOpen_iff_preimages_plots.1 hu n p hp
-/
protected lemma IsPlot.continuous {n : Nat} {p : 𝔼ⁿ -> X} (hp : IsPlot p) :
    Continuous[_, dTopology] p :=
  continuous_def.2 fun _ hu => isOpen_iff_preimages_plots.1 hu n p hp

/--
theorem `DSmooth.continuous` / 定理 `DSmooth.continuous`

English:
theorem DSmooth.continuous
  given: {f : X -> Y} (hf : DSmooth f)
  proof: by
  simp_rw [continuous_def, isOpen_iff_preimages_plots (X := X), isOpen_iff_preimages_plots (X := Y)]
  exact fun u hu n p hp => hu n (f ∘ p) (hf n p hp)

中文:
定理 DSmooth.continuous
  条件: {f : X -> Y} (hf : DSmooth f)
  证明: by
  simp_rw [continuous_def, isOpen_iff_preimages_plots (X := X), isOpen_iff_preimages_plots (X := Y)]
  exact fun u hu n p hp => hu n (f ∘ p) (hf n p hp)
-/
protected theorem DSmooth.continuous {f : X -> Y} (hf : DSmooth f) :
    Continuous[dTopology, dTopology] f := by
  simp_rw [continuous_def, isOpen_iff_preimages_plots (X := X), isOpen_iff_preimages_plots (X := Y)]
  exact fun u hu n p hp => hu n (f ∘ p) (hf n p hp)

/--
theorem `dSmooth_iff` / 定理 `dSmooth_iff`

English:
theorem dSmooth_iff
  given: {f : X -> Y}
  proof: Iff.rfl

中文:
定理 dSmooth_iff
  条件: {f : X -> Y}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem dSmooth_iff {f : X -> Y} :
    DSmooth f ↔ forall (n : Nat) (p : 𝔼ⁿ -> X), IsPlot p -> IsPlot (f ∘ p) :=
  Iff.rfl

/--
theorem `dSmooth_id` / 定理 `dSmooth_id`

English:
theorem dSmooth_id
  statement: DSmooth (@id X)
  proof: by simp [DSmooth]

@[fun_prop]

中文:
定理 dSmooth_id
  结论: DSmooth (@id X)
  证明: by simp [DSmooth]

@[fun_prop]

Depends on / 依赖: DSmooth
-/
theorem dSmooth_id : DSmooth (@id X) := by simp [DSmooth]

@[fun_prop]
/--
theorem `dSmooth_id'` / 定理 `dSmooth_id'`

English:
theorem dSmooth_id'
  statement: DSmooth fun x : X => x
  proof: dSmooth_id

中文:
定理 dSmooth_id'
  结论: DSmooth fun x : X => x
  证明: dSmooth_id

Depends on / 依赖: dSmooth_id
-/
theorem dSmooth_id' : DSmooth fun x : X => x := dSmooth_id

/--
theorem `DSmooth.comp` / 定理 `DSmooth.comp`

English:
theorem DSmooth.comp
  given: {f : X -> Y} {g : Y -> Z} (hg : DSmooth g) (hf : DSmooth f)
  proof: fun _ _ hp => hg _ _ (hf _ _ hp)

@[fun_prop]

中文:
定理 DSmooth.comp
  条件: {f : X -> Y} {g : Y -> Z} (hg : DSmooth g) (hf : DSmooth f)
  证明: fun _ _ hp => hg _ _ (hf _ _ hp)

@[fun_prop]
-/
theorem DSmooth.comp {f : X -> Y} {g : Y -> Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (g ∘ f) :=
  fun _ _ hp => hg _ _ (hf _ _ hp)

@[fun_prop]
/--
theorem `DSmooth.comp'` / 定理 `DSmooth.comp'`

English:
theorem DSmooth.comp'
  given: {f : X -> Y} {g : Y -> Z} (hg : DSmooth g) (hf : DSmooth f)
  proof: hg.comp hf

@[fun_prop]

中文:
定理 DSmooth.comp'
  条件: {f : X -> Y} {g : Y -> Z} (hg : DSmooth g) (hf : DSmooth f)
  证明: hg.comp hf

@[fun_prop]

Depends on / 依赖: hg.comp
-/
theorem DSmooth.comp' {f : X -> Y} {g : Y -> Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (fun x => g (f x)) := hg.comp hf

@[fun_prop]
/--
theorem `dSmooth_const` / 定理 `dSmooth_const`

English:
theorem dSmooth_const
  given: {y : Y}
  statement: DSmooth fun _ : X => y
  proof: fun _ _ _ => isPlot_const

中文:
定理 dSmooth_const
  条件: {y : Y}
  结论: DSmooth fun _ : X => y
  证明: fun _ _ _ => isPlot_const

Depends on / 依赖: isPlot_const
-/
theorem dSmooth_const {y : Y} : DSmooth fun _ : X => y :=
  fun _ _ _ => isPlot_const

end Diffeology

namespace DiffeologicalSpace

/-- Replaces the D-topology of a diffeology with another topology equal to it. Useful
to construct diffeologies with better definitional equalities. -/
@[instance_reducible]
/--
Definition of `replaceDTopology` / `replaceDTopology` 的定义

English:
definition replaceDTopology
  signature: {X : Type*} (d : DiffeologicalSpace X)
  body: t
  isOpen_iff_preimages_plots := by intro _; rw [← d.isOpen_iff_preimages_plots, ← h]
  __ := d

中文:
定义 replaceDTopology
  签名: {X : 类型} (d : Diffeological空间 X)
  定义体: t
  isOpen_iff_preimages_plots := by intro _; rw [← d.isOpen_iff_preimages_plots, ← h]
  __ := d
-/
def replaceDTopology {X : Type*} (d : DiffeologicalSpace X)
    (t : TopologicalSpace X) (h : @dTopology _ d = t) : DiffeologicalSpace X where
  dTopology := t
  isOpen_iff_preimages_plots := by intro _; rw [← d.isOpen_iff_preimages_plots, ← h]
  __ := d

/--
lemma `replaceDTopology_eq` / 引理 `replaceDTopology_eq`

English:
lemma replaceDTopology_eq
  statement: {X : Type*} {d : DiffeologicalSpace X}
  proof: by
  ext; rfl

中文:
引理 replaceDTopology_eq
  结论: {X : 类型} {d : Diffeological空间 X}
  证明: by
  ext; rfl
-/
lemma replaceDTopology_eq {X : Type*} {d : DiffeologicalSpace X}
    {t : TopologicalSpace X} {h : @dTopology _ d = t} : d.replaceDTopology t h = d := by
  ext; rfl

/--
Definition of `CorePlotsOn` / `CorePlotsOn` 的定义

English:
structure CorePlotsOn
  parameters: (X : Type*)
  axioms and operations (9):
    - isPlotOn({n : Nat} {u : Set 𝔼ⁿ} (hu : IsOpen u)) : (𝔼ⁿ -> X) -> Prop
    - isPlotOn_congr({n : Nat} {u : Set 𝔼ⁿ} (hu : IsOpen u) {p q : 𝔼ⁿ -> X} (h : Set.EqOn p q u)) : isPlotOn hu p ↔ isPlotOn hu q
    - isPlot({n : Nat}) : (𝔼ⁿ -> X) -> Prop  [default: fun p => isPlotOn isOpen_univ p]
    - isPlotOn_univ({n : Nat} {p : 𝔼ⁿ -> X}) : isPlotOn isOpen_univ p ↔ isPlot p  [default: by simp]
    - isPlot_const({n : Nat} (x : X)) : isPlot fun (_ : 𝔼ⁿ) => x
    - isPlotOn_reparam({n m : Nat} {u : Set 𝔼ⁿ} {v : Set 𝔼ᵐ} {hu : IsOpen u} (hv : IsOpen v) {p : 𝔼ⁿ -> X} {f : 𝔼ᵐ -> 𝔼ⁿ} (h : Set.MapsTo f v u) (hp : isPlotOn hu p) (hf : ContDiffOn Real ∞ f v)) : isPlotOn hv (p ∘ f)
    - locality({n : Nat} {u : Set 𝔼ⁿ} (hu : IsOpen u) {p : 𝔼ⁿ -> X} (hp : forall x in u, exists (v : Set _) (hv : IsOpen v), x in v ∧ isPlotOn hv p)) : isPlotOn hu p
    - dTopology : TopologicalSpace X  [default: { IsOpen u := forall ⦃n : Nat⦄, forall p : 𝔼ⁿ -> X, isPlot p]
    - isOpen_iff_preimages_plots({u : Set X}) : dTopology.IsOpen u ↔ forall {n : Nat}, forall p : 𝔼ⁿ -> X, isPlot p -> IsOpen (p ⁻¹' u)  [default: by rfl]

中文:
结构 余rePlotsOn
  参数: (X : 类型)
  公理与运算 (9 个):
    - isPlotOn({n : 自然数} {u : 集合 𝔼ⁿ} (hu : 是开集 u)) : (𝔼ⁿ -> X) -> 命题
    - isPlotOn_congr({n : 自然数} {u : 集合 𝔼ⁿ} (hu : 是开集 u) {p q : 𝔼ⁿ -> X} (h : 集合.EqOn p q u)) : isPlotOn hu p ↔ isPlotOn hu q
    - isPlot({n : 自然数}) : (𝔼ⁿ -> X) -> 命题  [默认: fun p => isPlotOn isOpen_univ p]
    - isPlotOn_univ({n : 自然数} {p : 𝔼ⁿ -> X}) : isPlotOn isOpen_univ p ↔ isPlot p  [默认: by simp]
    - isPlot_const({n : 自然数} (x : X)) : isPlot fun (_ : 𝔼ⁿ) => x
    - isPlotOn_reparam({n m : 自然数} {u : 集合 𝔼ⁿ} {v : 集合 𝔼ᵐ} {hu : 是开集 u} (hv : 是开集 v) {p : 𝔼ⁿ -> X} {f : 𝔼ᵐ -> 𝔼ⁿ} (h : 集合.映射到 f v u) (hp : isPlotOn hu p) (hf : ContDiffOn 实数 ∞ f v)) : isPlotOn hv (p ∘ f)
    - locality({n : 自然数} {u : 集合 𝔼ⁿ} (hu : 是开集 u) {p : 𝔼ⁿ -> X} (hp : 对任意 x in u, 存在 (v : 集合 _) (hv : 是开集 v), x in v ∧ isPlotOn hv p)) : isPlotOn hu p
    - dTopology : 拓扑空间 X  [默认: { IsOpen u := forall ⦃n : Nat⦄, forall p : 𝔼ⁿ -> X, isPlot p]
    - isOpen_iff_preimages_plots({u : 集合 X}) : dTopology.是开集 u ↔ 对任意 {n : 自然数}, 对任意 p : 𝔼ⁿ -> X, isPlot p -> 是开集 (p ⁻¹' u)  [默认: by rfl]

Depends on / 依赖: isOpen_univ, isPlotOn
-/
structure CorePlotsOn (X : Type*) where
  /-- The predicate determining which maps `u → X` with `u : Set (EuclideanSpace ℝ (Fin n))` open
  are plots. -/
  isPlotOn {n : Nat} {u : Set 𝔼ⁿ} (hu : IsOpen u) : (𝔼ⁿ -> X) -> Prop
  isPlotOn_congr {n : Nat} {u : Set 𝔼ⁿ} (hu : IsOpen u) {p q : 𝔼ⁿ -> X} (h : Set.EqOn p q u) :
    isPlotOn hu p ↔ isPlotOn hu q
  /-- The predicate that the diffeology built from this structure will use. Can be overwritten
  to allow for better definitional equalities. -/
  isPlot {n : Nat} : (𝔼ⁿ -> X) -> Prop := fun p => isPlotOn isOpen_univ p
  isPlotOn_univ {n : Nat} {p : 𝔼ⁿ -> X} :
    isPlotOn isOpen_univ p ↔ isPlot p := by simp
  isPlot_const {n : Nat} (x : X) : isPlot fun (_ : 𝔼ⁿ) => x
  isPlotOn_reparam {n m : Nat} {u : Set 𝔼ⁿ} {v : Set 𝔼ᵐ} {hu : IsOpen u} (hv : IsOpen v)
    {p : 𝔼ⁿ -> X} {f : 𝔼ᵐ -> 𝔼ⁿ} (h : Set.MapsTo f v u) (hp : isPlotOn hu p)
    (hf : ContDiffOn Real ∞ f v) : isPlotOn hv (p ∘ f)
  /-- The locality axiom of diffeologies, phrased in terms of `isPlotOn`. -/
  locality {n : Nat} {u : Set 𝔼ⁿ} (hu : IsOpen u) {p : 𝔼ⁿ -> X}
    (hp : forall x in u, exists (v : Set _) (hv : IsOpen v), x in v ∧ isPlotOn hv p) : isPlotOn hu p
  /-- The D-topology that the diffeology built from this structure will use. Can be overwritten
  to allow for better definitional equalities. -/
  dTopology : TopologicalSpace X := {
    IsOpen u := forall ⦃n : Nat⦄, forall p : 𝔼ⁿ -> X, isPlot p -> IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ _ => isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp =>
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp =>
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu => hs u hu p hp }
  isOpen_iff_preimages_plots {u : Set X} : dTopology.IsOpen u ↔
    forall {n : Nat}, forall p : 𝔼ⁿ -> X, isPlot p -> IsOpen (p ⁻¹' u) := by rfl

/-- Constructs a diffeology from plots defined on open subsets or ℝⁿ rather than ℝⁿ itself,
organised in the form of the auxiliary `CorePlotsOn` structure.
This is more involved in most regards, but also often makes it quite a lot easier to prove
the locality condition. -/
@[instance_reducible]
/--
Definition of `ofCorePlotsOn` / `ofCorePlotsOn` 的定义

English:
definition ofCorePlotsOn
  signature: {X : Type*} (d : DiffeologicalSpace.CorePlotsOn X)
  body: {p | d.isPlot p}
  constant_plots _ := d.isPlot_const _
plot_reparam hp hf := d.isPlotOn_univ.mp
    d.isPlotOn_reparam _ (Set.mapsTo_univ _ _) (d.isPlotOn_univ.mpr hp) hf.contDiffOn
  locality {n p} h := by
refine d.isPlotOn_univ.mp d.locality _ fun x _ => ?_
    let ⟨u, hu, hxu, hu'⟩ := h x
    let ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp hu x hxu
    have h : d.isPlot (p ∘ OpenPartialHomeomorph.univBall x ε) := hu'
      (f := OpenPartialHomeomorph.univBall x ε)
      (fun x' => by
        replace h := (OpenPartialHomeomorph.univBall x ε).map_source (x := x')
        rw [OpenPartialHomeomorph.univBall_target x hε] at h
        aesop)
      OpenPartialHomeomorph.contDiff_univBall
    have h' := d.isPlotOn_reparam (Metric.isOpen_ball) (Set.mapsTo_univ _ _)
      (d.isPlotOn_univ.mpr h) (OpenPartialHomeomorph.contDiffOn_univBall_symm (c := x) (r := ε))
    refine ⟨_, Metric.isOpen_ball, Metric.mem_ball_self hε, (d.isPlotOn_congr _ ?_).mp h'⟩
    rw [Function.comp_assoc]; rw [← OpenPartialHomeomorph.coe_trans]
    apply Set.EqOn.comp_left
    convert! (OpenPartialHomeomorph.symm_trans_self (OpenPartialHomeomorph.univBall x ε)).2
    simp [OpenPartialHomeomorph.univBall_target x hε]
  dTopology := d.dTopology
  isOpen_iff_preimages_plots := d.isOpen_iff_preimages_plots

中文:
定义 ofCorePlotsOn
  签名: {X : 类型} (d : Diffeological空间.余rePlotsOn X)
  定义体: {p | d.isPlot p}
  constant_plots _ := d.isPlot_const _
plot_reparam hp hf := d.isPlotOn_univ.mp
    d.isPlotOn_reparam _ (Set.mapsTo_univ _ _) (d.isPlotOn_univ.mpr hp) hf.contDiffOn
  locality {n p} h := by
refine d.isPlotOn_univ.mp d.locality _ fun x _ => ?_
    let ⟨u, hu, hxu, hu'⟩ := h x
    let ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp hu x hxu
    have h : d.isPlot (p ∘ OpenPartialHomeomorph.univBall x ε) := hu'
      (f := OpenPartialHomeomorph.univBall x ε)
      (fun x' => by
        replace h := (OpenPartialHomeomorph.univBall x ε).map_source (x := x')
        rw [OpenPartialHomeomorph.univBall_target x hε] at h
        aesop)
      OpenPartialHomeomorph.contDiff_univBall
    have h' := d.isPlotOn_reparam (Metric.isOpen_ball) (Set.mapsTo_univ _ _)
      (d.isPlotOn_univ.mpr h) (OpenPartialHomeomorph.contDiffOn_univBall_symm (c := x) (r := ε))
    refine ⟨_, Metric.isOpen_ball, Metric.mem_ball_self hε, (d.isPlotOn_congr _ ?_).mp h'⟩
    rw [Function.comp_assoc]; rw [← OpenPartialHomeomorph.coe_trans]
    apply Set.EqOn.comp_left
    convert! (OpenPartialHomeomorph.symm_trans_self (OpenPartialHomeomorph.univBall x ε)).2
    simp [OpenPartialHomeomorph.univBall_target x hε]
  dTopology := d.dTopology
  isOpen_iff_preimages_plots := d.isOpen_iff_preimages_plots

Depends on / 依赖: d.isPlot, isPlot
-/
def ofCorePlotsOn {X : Type*} (d : DiffeologicalSpace.CorePlotsOn X) :
    DiffeologicalSpace X where
  plots _ := {p | d.isPlot p}
  constant_plots _ := d.isPlot_const _
plot_reparam hp hf := d.isPlotOn_univ.mp
    d.isPlotOn_reparam _ (Set.mapsTo_univ _ _) (d.isPlotOn_univ.mpr hp) hf.contDiffOn
  locality {n p} h := by
refine d.isPlotOn_univ.mp d.locality _ fun x _ => ?_
    let ⟨u, hu, hxu, hu'⟩ := h x
    let ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp hu x hxu
    have h : d.isPlot (p ∘ OpenPartialHomeomorph.univBall x ε) := hu'
      (f := OpenPartialHomeomorph.univBall x ε)
      (fun x' => by
        replace h := (OpenPartialHomeomorph.univBall x ε).map_source (x := x')
        rw [OpenPartialHomeomorph.univBall_target x hε] at h
        aesop)
      OpenPartialHomeomorph.contDiff_univBall
    have h' := d.isPlotOn_reparam (Metric.isOpen_ball) (Set.mapsTo_univ _ _)
      (d.isPlotOn_univ.mpr h) (OpenPartialHomeomorph.contDiffOn_univBall_symm (c := x) (r := ε))
    refine ⟨_, Metric.isOpen_ball, Metric.mem_ball_self hε, (d.isPlotOn_congr _ ?_).mp h'⟩
    rw [Function.comp_assoc]; rw [← OpenPartialHomeomorph.coe_trans]
    apply Set.EqOn.comp_left
    convert! (OpenPartialHomeomorph.symm_trans_self (OpenPartialHomeomorph.univBall x ε)).2
    simp [OpenPartialHomeomorph.univBall_target x hε]
  dTopology := d.dTopology
  isOpen_iff_preimages_plots := d.isOpen_iff_preimages_plots

end DiffeologicalSpace

namespace Diffeology

/--
Definition of `IsDTopologyCompatible` / `IsDTopologyCompatible` 的定义

English:
class IsDTopologyCompatible
  parameters: (X : Type*) [t : TopologicalSpace X] [DiffeologicalSpace X]
  axioms and operations (1):
    - dTop_eq((X)) : dTopology = t

中文:
类 是DTopologyCompatible
  参数: (X : 类型) [t : 拓扑空间 X] [Diffeological空间 X]
  公理与运算 (1 个):
    - dTop_eq((X)) : dTopology = t

Depends on / 依赖: IsDTopologyCompatible, IsDTopologyCompatible.dTop_eq, continuous, convert, dTop_eq, hf.continuous
-/
class IsDTopologyCompatible (X : Type*) [t : TopologicalSpace X] [DiffeologicalSpace X] : Prop where
  dTop_eq (X) : dTopology = t

/--
theorem `DSmooth.continuous'` / 定理 `DSmooth.continuous'`

English:
theorem DSmooth.continuous'
  statement: {X Y : Type*}
  proof: by
  convert! hf.continuous
  · rw [IsDTopologyCompatible.dTop_eq X]
  · rw [IsDTopologyCompatible.dTop_eq Y]

中文:
定理 DSmooth.continuous'
  结论: {X Y : 类型}
  证明: by
  convert! hf.continuous
  · rw [IsDTopologyCompatible.dTop_eq X]
  · rw [IsDTopologyCompatible.dTop_eq Y]
-/
protected theorem DSmooth.continuous' {X Y : Type*}
    [TopologicalSpace X] [DiffeologicalSpace X] [IsDTopologyCompatible X]
    [TopologicalSpace Y] [DiffeologicalSpace Y] [IsDTopologyCompatible Y]
    {f : X -> Y} (hf : DSmooth f) : Continuous f := by
  convert! hf.continuous
  · rw [IsDTopologyCompatible.dTop_eq X]
  · rw [IsDTopologyCompatible.dTop_eq Y]

/--
Definition of `IsContDiffCompatible` / `IsContDiffCompatible` 的定义

English:
class IsContDiffCompatible
  parameters: (X : Type*)
  axioms and operations (1):
    - isPlot_iff({n : Nat} {p : 𝔼ⁿ -> X}) : IsPlot p ↔ ContDiff Real ∞ p

中文:
类 是余ntDiffCompatible
  参数: (X : 类型)
  公理与运算 (1 个):
    - isPlot_iff({n : 自然数} {p : 𝔼ⁿ -> X}) : IsPlot p ↔ 连续可微 实数 ∞ p
-/
class IsContDiffCompatible (X : Type*)
    [NormedAddCommGroup X] [NormedSpace Real X] [DiffeologicalSpace X] : Prop where
  isPlot_iff {n : Nat} {p : 𝔼ⁿ -> X} : IsPlot p ↔ ContDiff Real ∞ p

/-- Diffeology on a finite-dimensional normed space. We make this a definition instead of an
instance because we also want to have product diffeologies as an instance, and having both would
cause instance diamonds on spaces like `Fin n → ℝ`. -/
@[instance_reducible]
/--
Definition of `_root_.NormedSpace.toDiffeology` / `_root_.NormedSpace.toDiffeology` 的定义

English:
definition _root_.NormedSpace.toDiffeology
  signature: (X : Type*)
  body: .ofCorePlotsOn {
    isPlotOn := fun {_ u} _ p => ContDiffOn Real ∞ p u
    isPlotOn_congr := fun _ _ _ h => contDiffOn_congr h
    isPlot := fun p => ContDiff Real ∞ p
    isPlotOn_univ := contDiffOn_univ
    isPlot_const := fun _ => contDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf => hp.comp hf h.subset_preimage
    locality := fun _ _ h => fun x hxu => by
      let ⟨v, hv, hxv, hv'⟩ := h x hxu
      exact ((hv' x hxv).contDiffAt (hv.mem_nhds hxv)).contDiffWithinAt
    dTopology := inferInstance
    isOpen_iff_preimages_plots := fun {u} => by
      refine ⟨fun hu _ _ hp => IsOpen.preimage (hp.continuous) hu, fun h => ?_⟩
      rw [← toEuclidean.preimage_symm_preimage u]
      exact toEuclidean.continuous.isOpen_preimage _ (h _ toEuclidean.symm.contDiff) }

中文:
定义 _root_.赋范空间.toDiffeology
  签名: (X : 类型)
  定义体: .ofCorePlotsOn {
    isPlotOn := fun {_ u} _ p => ContDiffOn Real ∞ p u
    isPlotOn_congr := fun _ _ _ h => contDiffOn_congr h
    isPlot := fun p => ContDiff Real ∞ p
    isPlotOn_univ := contDiffOn_univ
    isPlot_const := fun _ => contDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf => hp.comp hf h.subset_preimage
    locality := fun _ _ h => fun x hxu => by
      let ⟨v, hv, hxv, hv'⟩ := h x hxu
      exact ((hv' x hxv).contDiffAt (hv.mem_nhds hxv)).contDiffWithinAt
    dTopology := inferInstance
    isOpen_iff_preimages_plots := fun {u} => by
      refine ⟨fun hu _ _ hp => IsOpen.preimage (hp.continuous) hu, fun h => ?_⟩
      rw [← toEuclidean.preimage_symm_preimage u]
      exact toEuclidean.continuous.isOpen_preimage _ (h _ toEuclidean.symm.contDiff) }

Depends on / 依赖: ContDiff, ContDiffOn, contDiffAt, contDiffOn_congr, contDiffOn_univ, contDiffWithinAt, contDiff_const, dTopology, h.subset_preimage, hp.comp, hv.mem_nhds, isOpen_iff_preimages_plots, isPlot, isPlotOn, isPlotOn_congr, isPlotOn_reparam, isPlotOn_univ, isPlot_const, locality, mem_nhds
-/
def _root_.NormedSpace.toDiffeology (X : Type*)
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X] :
    DiffeologicalSpace X :=
  .ofCorePlotsOn {
    isPlotOn := fun {_ u} _ p => ContDiffOn Real ∞ p u
    isPlotOn_congr := fun _ _ _ h => contDiffOn_congr h
    isPlot := fun p => ContDiff Real ∞ p
    isPlotOn_univ := contDiffOn_univ
    isPlot_const := fun _ => contDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf => hp.comp hf h.subset_preimage
    locality := fun _ _ h => fun x hxu => by
      let ⟨v, hv, hxv, hv'⟩ := h x hxu
      exact ((hv' x hxv).contDiffAt (hv.mem_nhds hxv)).contDiffWithinAt
    dTopology := inferInstance
    isOpen_iff_preimages_plots := fun {u} => by
      refine ⟨fun hu _ _ hp => IsOpen.preimage (hp.continuous) hu, fun h => ?_⟩
      rw [← toEuclidean.preimage_symm_preimage u]
      exact toEuclidean.continuous.isOpen_preimage _ (h _ toEuclidean.symm.contDiff) }

attribute [local instance] NormedSpace.toDiffeology in
instance {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X] :
    IsContDiffCompatible X :=
  ⟨Iff.rfl⟩

/--
lemma `_root_.NormedSpace.isContDiffCompatible_iff_eq_toDiffeology` / 引理 `_root_.NormedSpace.isContDiffCompatible_iff_eq_toDiffeology`

English:
lemma _root_.NormedSpace.isContDiffCompatible_iff_eq_toDiffeology
  statement: {X : Type*}
  proof: ⟨fun _ => by ext n p; exact IsContDiffCompatible.isPlot_iff, fun h => h ▸ inferInstance⟩

中文:
引理 _root_.赋范空间.isContDiffCompatible_iff_eq_toDiffeology
  结论: {X : 类型}
  证明: ⟨fun _ => by ext n p; exact IsContDiffCompatible.isPlot_iff, fun h => h ▸ inferInstance⟩

Depends on / 依赖: IsContDiffCompatible, IsContDiffCompatible.isPlot_iff, isPlot_iff
-/
lemma _root_.NormedSpace.isContDiffCompatible_iff_eq_toDiffeology {X : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X] [d : DiffeologicalSpace X] :
    IsContDiffCompatible X ↔ d = NormedSpace.toDiffeology X :=
  ⟨fun _ => by ext n p; exact IsContDiffCompatible.isPlot_iff, fun h => h ▸ inferInstance⟩

attribute [local instance] NormedSpace.toDiffeology in
instance {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X] [FiniteDimensional Real X] :
    IsDTopologyCompatible X :=
  ⟨rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiffeologicalSpace Real
  body: NormedSpace.toDiffeology _

中文:
实例 :
  签名: Diffeological空间 实数
  定义体: NormedSpace.toDiffeology _

Depends on / 依赖: NormedSpace, NormedSpace.toDiffeology, toDiffeology
-/
instance : DiffeologicalSpace Real := NormedSpace.toDiffeology _

instance {ι : Type*} [Fintype ι] : DiffeologicalSpace (EuclideanSpace Real ι) :=
  NormedSpace.toDiffeology _

variable {X : Type*} [DiffeologicalSpace X] {n : Nat}

@[fun_prop]
/--
theorem `IsPlot.dSmooth` / 定理 `IsPlot.dSmooth`

English:
theorem IsPlot.dSmooth
  given: {p : 𝔼ⁿ -> X} (hp : IsPlot p)
  statement: DSmooth p
  proof: fun _ _ => isPlot_reparam hp

@[fun_prop]

中文:
定理 IsPlot.dSmooth
  条件: {p : 𝔼ⁿ -> X} (hp : IsPlot p)
  结论: DSmooth p
  证明: fun _ _ => isPlot_reparam hp

@[fun_prop]
-/
protected theorem IsPlot.dSmooth {p : 𝔼ⁿ -> X} (hp : IsPlot p) : DSmooth p :=
  fun _ _ => isPlot_reparam hp

@[fun_prop]
/--
theorem `DSmooth.isPlot` / 定理 `DSmooth.isPlot`

English:
theorem DSmooth.isPlot
  given: {p : 𝔼ⁿ -> X} (hp : DSmooth p)
  statement: IsPlot p
  proof: hp n id contDiff_id (n := ∞)

中文:
定理 DSmooth.isPlot
  条件: {p : 𝔼ⁿ -> X} (hp : DSmooth p)
  结论: IsPlot p
  证明: hp n id contDiff_id (n := ∞)
-/
protected theorem DSmooth.isPlot {p : 𝔼ⁿ -> X} (hp : DSmooth p) : IsPlot p :=
hp n id contDiff_id (n := ∞)

/--
theorem `isPlot_iff_dSmooth` / 定理 `isPlot_iff_dSmooth`

English:
theorem isPlot_iff_dSmooth
  given: {p : 𝔼ⁿ -> X}
  statement: IsPlot p ↔ DSmooth p
  proof: ⟨IsPlot.dSmooth, DSmooth.isPlot⟩

中文:
定理 isPlot_iff_dSmooth
  条件: {p : 𝔼ⁿ -> X}
  结论: IsPlot p ↔ DSmooth p
  证明: ⟨IsPlot.dSmooth, DSmooth.isPlot⟩

Depends on / 依赖: DSmooth, DSmooth.isPlot, IsPlot, IsPlot.dSmooth, dSmooth, isPlot
-/
theorem isPlot_iff_dSmooth {p : 𝔼ⁿ -> X} : IsPlot p ↔ DSmooth p :=
  ⟨IsPlot.dSmooth, DSmooth.isPlot⟩

/--
lemma `isPlot_id` / 引理 `isPlot_id`

English:
lemma isPlot_id
  statement: IsPlot (@id 𝔼ⁿ)
  proof: contDiff_id (n := ∞)

@[fun_prop]

中文:
引理 isPlot_id
  结论: IsPlot (@id 𝔼ⁿ)
  证明: contDiff_id (n := ∞)

@[fun_prop]

Depends on / 依赖: contDiff_id
-/
lemma isPlot_id : IsPlot (@id 𝔼ⁿ) := contDiff_id (n := ∞)

@[fun_prop]
/--
lemma `isPlot_id'` / 引理 `isPlot_id'`

English:
lemma isPlot_id'
  statement: IsPlot fun x : 𝔼ⁿ => x
  proof: isPlot_id

中文:
引理 isPlot_id'
  结论: IsPlot fun x : 𝔼ⁿ => x
  证明: isPlot_id

Depends on / 依赖: isPlot_id
-/
lemma isPlot_id' : IsPlot fun x : 𝔼ⁿ => x := isPlot_id

variable {Y : Type*}
  [NormedAddCommGroup X] [NormedSpace Real X] [IsContDiffCompatible X]
  [NormedAddCommGroup Y] [NormedSpace Real Y] [DiffeologicalSpace Y] [IsContDiffCompatible Y]

/--
theorem `isPlot_iff_contDiff` / 定理 `isPlot_iff_contDiff`

English:
theorem isPlot_iff_contDiff
  given: {p : 𝔼ⁿ -> X}
  statement: IsPlot p ↔ ContDiff Real ∞ p
  proof: IsContDiffCompatible.isPlot_iff

@[fun_prop]

中文:
定理 isPlot_iff_contDiff
  条件: {p : 𝔼ⁿ -> X}
  结论: IsPlot p ↔ 连续可微 实数 ∞ p
  证明: IsContDiffCompatible.isPlot_iff

@[fun_prop]

Depends on / 依赖: IsContDiffCompatible, IsContDiffCompatible.isPlot_iff, isPlot_iff
-/
theorem isPlot_iff_contDiff {p : 𝔼ⁿ -> X} : IsPlot p ↔ ContDiff Real ∞ p :=
  IsContDiffCompatible.isPlot_iff

@[fun_prop]
/--
theorem `_root_.ContDiff.isPlot` / 定理 `_root_.ContDiff.isPlot`

English:
theorem _root_.ContDiff.isPlot
  given: {p : 𝔼ⁿ -> X} (hp : ContDiff Real ∞ p)
  statement: IsPlot p
  proof: isPlot_iff_contDiff.2 hp

@[fun_prop]

中文:
定理 _root_.连续可微.isPlot
  条件: {p : 𝔼ⁿ -> X} (hp : 连续可微 实数 ∞ p)
  结论: IsPlot p
  证明: isPlot_iff_contDiff.2 hp

@[fun_prop]
-/
protected theorem _root_.ContDiff.isPlot {p : 𝔼ⁿ -> X} (hp : ContDiff Real ∞ p) : IsPlot p :=
  isPlot_iff_contDiff.2 hp

@[fun_prop]
/--
theorem `IsPlot.contDiff` / 定理 `IsPlot.contDiff`

English:
theorem IsPlot.contDiff
  given: {p : 𝔼ⁿ -> X} (hp : IsPlot p)
  statement: ContDiff Real ∞ p
  proof: isPlot_iff_contDiff.1 hp

@[fun_prop]

中文:
定理 IsPlot.contDiff
  条件: {p : 𝔼ⁿ -> X} (hp : IsPlot p)
  结论: 连续可微 实数 ∞ p
  证明: isPlot_iff_contDiff.1 hp

@[fun_prop]
-/
protected theorem IsPlot.contDiff {p : 𝔼ⁿ -> X} (hp : IsPlot p) : ContDiff Real ∞ p :=
  isPlot_iff_contDiff.1 hp

@[fun_prop]
/--
theorem `_root_.ContDiff.dSmooth` / 定理 `_root_.ContDiff.dSmooth`

English:
theorem _root_.ContDiff.dSmooth
  given: {f : X -> Y} (hf : ContDiff Real ∞ f)
  statement: DSmooth f
  proof: fun _ _ hp => (hf.comp hp.contDiff).isPlot

@[fun_prop]

中文:
定理 _root_.连续可微.dSmooth
  条件: {f : X -> Y} (hf : 连续可微 实数 ∞ f)
  结论: DSmooth f
  证明: fun _ _ hp => (hf.comp hp.contDiff).isPlot

@[fun_prop]
-/
protected theorem _root_.ContDiff.dSmooth {f : X -> Y} (hf : ContDiff Real ∞ f) : DSmooth f :=
  fun _ _ hp => (hf.comp hp.contDiff).isPlot

@[fun_prop]
/--
theorem `DSmooth.contDiff` / 定理 `DSmooth.contDiff`

English:
theorem DSmooth.contDiff
  given: [FiniteDimensional Real X] {f : X -> Y} (hf : DSmooth f)
  proof: by
  let g := toEuclidean (E := X)
  rw [← Function.comp_id f]; rw [← g.symm_comp_self]
  exact (hf _ _ g.symm.contDiff.isPlot).contDiff.comp g.contDiff

中文:
定理 DSmooth.contDiff
  条件: [有限维 实数 X] {f : X -> Y} (hf : DSmooth f)
  证明: by
  let g := toEuclidean (E := X)
  rw [← Function.comp_id f]; rw [← g.symm_comp_self]
  exact (hf _ _ g.symm.contDiff.isPlot).contDiff.comp g.contDiff
-/
protected theorem DSmooth.contDiff [FiniteDimensional Real X] {f : X -> Y} (hf : DSmooth f) :
    ContDiff Real ∞ f := by
  let g := toEuclidean (E := X)
  rw [← Function.comp_id f]; rw [← g.symm_comp_self]
  exact (hf _ _ g.symm.contDiff.isPlot).contDiff.comp g.contDiff

/--
theorem `dSmooth_iff_contDiff` / 定理 `dSmooth_iff_contDiff`

English:
theorem dSmooth_iff_contDiff
  given: [FiniteDimensional Real X] {f : X -> Y}
  statement: DSmooth f ↔ ContDiff Real ∞ f
  proof: ⟨DSmooth.contDiff, ContDiff.dSmooth⟩

中文:
定理 dSmooth_iff_contDiff
  条件: [有限维 实数 X] {f : X -> Y}
  结论: DSmooth f ↔ 连续可微 实数 ∞ f
  证明: ⟨DSmooth.contDiff, ContDiff.dSmooth⟩

Depends on / 依赖: ContDiff, ContDiff.dSmooth, DSmooth, DSmooth.contDiff, contDiff, dSmooth
-/
theorem dSmooth_iff_contDiff [FiniteDimensional Real X] {f : X -> Y} : DSmooth f ↔ ContDiff Real ∞ f :=
  ⟨DSmooth.contDiff, ContDiff.dSmooth⟩

end Diffeology

section CompleteLattice

namespace DiffeologicalSpace

open Diffeology

variable {X : Type*}

/--
Definition of `toPlots` / `toPlots` 的定义

English:
definition toPlots
  signature: (_ : DiffeologicalSpace X)
  body: {p | IsPlot p.2}

中文:
定义 toPlots
  签名: (_ : Diffeological空间 X)
  定义体: {p | IsPlot p.2}

Depends on / 依赖: IsPlot
-/
def toPlots (_ : DiffeologicalSpace X) : Set ((n : Nat) × (𝔼ⁿ -> X)) :=
  {p | IsPlot p.2}

/--
lemma `injective_toPlots` / 引理 `injective_toPlots`

English:
lemma injective_toPlots
  statement: Function.Injective (@toPlots X)
  proof: fun d d' h => by
  ext n p; exact Set.ext_iff.1 h ⟨n, p⟩

中文:
引理 injective_toPlots
  结论: 函数.单射 (@toPlots X)
  证明: fun d d' h => by
  ext n p; exact Set.ext_iff.1 h ⟨n, p⟩

Depends on / 依赖: Set.ext_iff, ext_iff
-/
lemma injective_toPlots : Function.Injective (@toPlots X) := fun d d' h => by
  ext n p; exact Set.ext_iff.1 h ⟨n, p⟩

/-- The diffeology generated by a set `g` of plots. -/
@[instance_reducible]
/--
Definition of `generateFrom` / `generateFrom` 的定义

English:
definition generateFrom
  signature: (g : Set ((n : Nat) × (𝔼ⁿ -> X)))
  body: {p | forall (d : DiffeologicalSpace X), g subseteq d.toPlots -> ⟨n, p⟩ in d.toPlots}
  constant_plots {n} x := fun _ _ => constant_plots x
  plot_reparam {n m p f} := fun hp hf d hd => @d.plot_reparam n m p f (hp _ hd) hf
  locality {n p} := fun hp d hd => @locality X d n p fun x => by
    let ⟨u, hxu, hu, hu'⟩ := hp x
    exact ⟨u, hxu, hu, fun {m f} hfu hf => (hu' hfu hf) _ hd⟩

中文:
定义 generateFrom
  签名: (g : 集合 ((n : 自然数) × (𝔼ⁿ -> X)))
  定义体: {p | forall (d : DiffeologicalSpace X), g subseteq d.toPlots -> ⟨n, p⟩ in d.toPlots}
  constant_plots {n} x := fun _ _ => constant_plots x
  plot_reparam {n m p f} := fun hp hf d hd => @d.plot_reparam n m p f (hp _ hd) hf
  locality {n p} := fun hp d hd => @locality X d n p fun x => by
    let ⟨u, hxu, hu, hu'⟩ := hp x
    exact ⟨u, hxu, hu, fun {m f} hfu hf => (hu' hfu hf) _ hd⟩

Depends on / 依赖: DiffeologicalSpace, d.toPlots, subseteq, toPlots
-/
def generateFrom (g : Set ((n : Nat) × (𝔼ⁿ -> X))) : DiffeologicalSpace X where
  plots n := {p | forall (d : DiffeologicalSpace X), g subseteq d.toPlots -> ⟨n, p⟩ in d.toPlots}
  constant_plots {n} x := fun _ _ => constant_plots x
  plot_reparam {n m p f} := fun hp hf d hd => @d.plot_reparam n m p f (hp _ hd) hf
  locality {n p} := fun hp d hd => @locality X d n p fun x => by
    let ⟨u, hxu, hu, hu'⟩ := hp x
    exact ⟨u, hxu, hu, fun {m f} hfu hf => (hu' hfu hf) _ hd⟩

/--
lemma `self_subset_toPlots_generateFrom` / 引理 `self_subset_toPlots_generateFrom`

English:
lemma self_subset_toPlots_generateFrom
  given: (g : Set ((n : Nat) × (𝔼ⁿ -> X)))
  proof: fun _ hd _ h => h hd

中文:
引理 self_subset_toPlots_generateFrom
  条件: (g : 集合 ((n : 自然数) × (𝔼ⁿ -> X)))
  证明: fun _ hd _ h => h hd
-/
lemma self_subset_toPlots_generateFrom (g : Set ((n : Nat) × (𝔼ⁿ -> X))) :
    g subseteq (generateFrom g).toPlots :=
  fun _ hd _ h => h hd

/--
lemma `isPlot_generatedFrom_of_mem` / 引理 `isPlot_generatedFrom_of_mem`

English:
lemma isPlot_generatedFrom_of_mem
  statement: {g : Set ((n : Nat) × (𝔼ⁿ -> X))} {n : Nat} {p : 𝔼ⁿ -> X}
  proof: self_subset_toPlots_generateFrom g hp

中文:
引理 isPlot_generatedFrom_of_mem
  结论: {g : 集合 ((n : 自然数) × (𝔼ⁿ -> X))} {n : 自然数} {p : 𝔼ⁿ -> X}
  证明: self_subset_toPlots_generateFrom g hp

Depends on / 依赖: self_subset_toPlots_generateFrom
-/
lemma isPlot_generatedFrom_of_mem {g : Set ((n : Nat) × (𝔼ⁿ -> X))} {n : Nat} {p : 𝔼ⁿ -> X}
    (hp : ⟨n, p⟩ in g) : (@IsPlot _ (generateFrom g)) p :=
  self_subset_toPlots_generateFrom g hp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (DiffeologicalSpace X)
  body: PartialOrder.lift _ injective_toPlots

中文:
实例 :
  签名: 偏序 (Diffeological空间 X)
  定义体: PartialOrder.lift _ injective_toPlots

Depends on / 依赖: PartialOrder, PartialOrder.lift, injective_toPlots
-/
instance : PartialOrder (DiffeologicalSpace X) := PartialOrder.lift _ injective_toPlots

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: {d₁ d₂ : DiffeologicalSpace X}
  statement: d₁ <= d₂ ↔ d₁.toPlots subseteq d₂.toPlots
  proof: Iff.rfl

中文:
引理 le_def
  条件: {d₁ d₂ : Diffeological空间 X}
  结论: d₁ <= d₂ ↔ d₁.toPlots subseteq d₂.toPlots
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_def {d₁ d₂ : DiffeologicalSpace X} : d₁ <= d₂ ↔ d₁.toPlots subseteq d₂.toPlots := Iff.rfl

/--
lemma `le_iff` / 引理 `le_iff`

English:
lemma le_iff
  given: {d₁ d₂ : DiffeologicalSpace X}
  statement: d₁ <= d₂ ↔ forall n, d₁.plots n subseteq d₂.plots n
  proof: le_def.trans ⟨fun h n p h' => (h h' : ⟨n, p⟩ in d₂.toPlots), fun h _ hp => h _ hp⟩

中文:
引理 le_iff
  条件: {d₁ d₂ : Diffeological空间 X}
  结论: d₁ <= d₂ ↔ 对任意 n, d₁.plots n subseteq d₂.plots n
  证明: le_def.trans ⟨fun h n p h' => (h h' : ⟨n, p⟩ in d₂.toPlots), fun h _ hp => h _ hp⟩

Depends on / 依赖: le_def, le_def.trans, toPlots
-/
lemma le_iff {d₁ d₂ : DiffeologicalSpace X} : d₁ <= d₂ ↔ forall n, d₁.plots n subseteq d₂.plots n :=
  le_def.trans ⟨fun h n p h' => (h h' : ⟨n, p⟩ in d₂.toPlots), fun h _ hp => h _ hp⟩

/--
lemma `le_iff'` / 引理 `le_iff'`

English:
lemma le_iff'
  given: {d₁ d₂ : DiffeologicalSpace X}
  statement: d₁ <= d₂ ↔
  proof: le_iff

中文:
引理 le_iff'
  条件: {d₁ d₂ : Diffeological空间 X}
  结论: d₁ <= d₂ ↔
  证明: le_iff

Depends on / 依赖: le_iff
-/
lemma le_iff' {d₁ d₂ : DiffeologicalSpace X} : d₁ <= d₂ ↔
    forall n (p : 𝔼ⁿ -> X), (@IsPlot _ d₁) p -> (@IsPlot _ d₂) p := le_iff

/--
lemma `generateFrom_le_iff_subset_toPlots` / 引理 `generateFrom_le_iff_subset_toPlots`

English:
lemma generateFrom_le_iff_subset_toPlots
  statement: {g : Set ((n : Nat) × (𝔼ⁿ -> X))}
  proof: ⟨fun h => (self_subset_toPlots_generateFrom g).trans h, fun h _ hp => hp _ h⟩

中文:
引理 generateFrom_le_iff_subset_toPlots
  结论: {g : 集合 ((n : 自然数) × (𝔼ⁿ -> X))}
  证明: ⟨fun h => (self_subset_toPlots_generateFrom g).trans h, fun h _ hp => hp _ h⟩

Depends on / 依赖: self_subset_toPlots_generateFrom
-/
lemma generateFrom_le_iff_subset_toPlots {g : Set ((n : Nat) × (𝔼ⁿ -> X))}
    {d : DiffeologicalSpace X} : generateFrom g <= d ↔ g subseteq d.toPlots :=
  ⟨fun h => (self_subset_toPlots_generateFrom g).trans h, fun h _ hp => hp _ h⟩

/--
lemma `generateFrom_le_iff` / 引理 `generateFrom_le_iff`

English:
lemma generateFrom_le_iff
  given: {g : Set ((n : Nat) × (𝔼ⁿ -> X))} {d : DiffeologicalSpace X}
  proof: generateFrom_le_iff_subset_toPlots.trans ⟨fun h _ _ hp => h hp, fun h _ hp => h _ _ hp⟩

中文:
引理 generateFrom_le_iff
  条件: {g : 集合 ((n : 自然数) × (𝔼ⁿ -> X))} {d : Diffeological空间 X}
  证明: generateFrom_le_iff_subset_toPlots.trans ⟨fun h _ _ hp => h hp, fun h _ hp => h _ _ hp⟩

Depends on / 依赖: generateFrom_le_iff_subset_toPlots, generateFrom_le_iff_subset_toPlots.trans
-/
lemma generateFrom_le_iff {g : Set ((n : Nat) × (𝔼ⁿ -> X))} {d : DiffeologicalSpace X} :
    generateFrom g <= d ↔ forall n (p : 𝔼ⁿ -> X), ⟨n, p⟩ in g -> (@IsPlot _ d) p :=
  generateFrom_le_iff_subset_toPlots.trans ⟨fun h _ _ hp => h hp, fun h _ hp => h _ _ hp⟩

/-- The diffeology defined by `g`. Same as `generateFrom g`, except that its set of plots is
definitionally equal to `g`. -/
@[instance_reducible]
/--
Definition of `mkOfClosure` / `mkOfClosure` 的定义

English:
definition mkOfClosure
  signature: (g : Set ((n : Nat) × (𝔼ⁿ -> X))) (hg : (generateFrom g).toPlots = g)
  body: {p | ⟨n, p⟩ in g}
  constant_plots := hg ▸ (generateFrom g).constant_plots
  plot_reparam := hg ▸ (generateFrom g).plot_reparam
  locality := hg ▸ (generateFrom g).locality

@[simp]

中文:
定义 mkOfClosure
  签名: (g : 集合 ((n : 自然数) × (𝔼ⁿ -> X))) (hg : (generateFrom g).toPlots = g)
  定义体: {p | ⟨n, p⟩ in g}
  constant_plots := hg ▸ (generateFrom g).constant_plots
  plot_reparam := hg ▸ (generateFrom g).plot_reparam
  locality := hg ▸ (generateFrom g).locality

@[simp]
-/
protected def mkOfClosure (g : Set ((n : Nat) × (𝔼ⁿ -> X))) (hg : (generateFrom g).toPlots = g) :
    DiffeologicalSpace X where
  plots n := {p | ⟨n, p⟩ in g}
  constant_plots := hg ▸ (generateFrom g).constant_plots
  plot_reparam := hg ▸ (generateFrom g).plot_reparam
  locality := hg ▸ (generateFrom g).locality

@[simp]
/--
lemma `mkOfClosure_eq_generateFrom` / 引理 `mkOfClosure_eq_generateFrom`

English:
lemma mkOfClosure_eq_generateFrom
  statement: {g : Set ((n : Nat) × (𝔼ⁿ -> X))}
  proof: injective_toPlots hg.symm

中文:
引理 mkOfClosure_eq_generateFrom
  结论: {g : 集合 ((n : 自然数) × (𝔼ⁿ -> X))}
  证明: injective_toPlots hg.symm

Depends on / 依赖: hg.symm, injective_toPlots
-/
lemma mkOfClosure_eq_generateFrom {g : Set ((n : Nat) × (𝔼ⁿ -> X))}
    {hg : (generateFrom g).toPlots = g} : DiffeologicalSpace.mkOfClosure g hg = generateFrom g :=
  injective_toPlots hg.symm

/--
theorem `gc_generateFrom` / 定理 `gc_generateFrom`

English:
theorem gc_generateFrom
  given: (X : Type*)
  statement: GaloisConnection generateFrom (@toPlots X)
  proof: @generateFrom_le_iff_subset_toPlots X

中文:
定理 gc_generateFrom
  条件: (X : 类型)
  结论: GaloisConnection generateFrom (@toPlots X)
  证明: @generateFrom_le_iff_subset_toPlots X

Depends on / 依赖: generateFrom_le_iff_subset_toPlots
-/
theorem gc_generateFrom (X : Type*) : GaloisConnection generateFrom (@toPlots X) :=
  @generateFrom_le_iff_subset_toPlots X

/--
Definition of `giGenerateFrom` / `giGenerateFrom` 的定义

English:
definition giGenerateFrom
  signature: (X : Type*)
  body: gc_generateFrom X
  le_l_u := fun _ => le_def.2 (self_subset_toPlots_generateFrom _)
  choice g hg := DiffeologicalSpace.mkOfClosure g (hg.antisymm (self_subset_toPlots_generateFrom g))
  choice_eq _ _ := mkOfClosure_eq_generateFrom

中文:
定义 giGenerateFrom
  签名: (X : 类型)
  定义体: gc_generateFrom X
  le_l_u := fun _ => le_def.2 (self_subset_toPlots_generateFrom _)
  choice g hg := DiffeologicalSpace.mkOfClosure g (hg.antisymm (self_subset_toPlots_generateFrom g))
  choice_eq _ _ := mkOfClosure_eq_generateFrom

Depends on / 依赖: gc_generateFrom
-/
def giGenerateFrom (X : Type*) : GaloisInsertion generateFrom (@toPlots X) where
  gc := gc_generateFrom X
  le_l_u := fun _ => le_def.2 (self_subset_toPlots_generateFrom _)
  choice g hg := DiffeologicalSpace.mkOfClosure g (hg.antisymm (self_subset_toPlots_generateFrom g))
  choice_eq _ _ := mkOfClosure_eq_generateFrom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (DiffeologicalSpace X)
  body: (giGenerateFrom X).liftCompleteLattice

@[gcongr, mono]

中文:
实例 :
  签名: 完备格 (Diffeological空间 X)
  定义体: (giGenerateFrom X).liftCompleteLattice

@[gcongr, mono]

Depends on / 依赖: giGenerateFrom, liftCompleteLattice
-/
instance : CompleteLattice (DiffeologicalSpace X) := (giGenerateFrom X).liftCompleteLattice

@[gcongr, mono]
/--
theorem `generateFrom_mono` / 定理 `generateFrom_mono`

English:
theorem generateFrom_mono
  given: {g₁ g₂ : Set ((n : Nat) × (𝔼ⁿ -> X))} (h : g₁ subseteq g₂)
  proof: (gc_generateFrom _).monotone_l h

中文:
定理 generateFrom_mono
  条件: {g₁ g₂ : 集合 ((n : 自然数) × (𝔼ⁿ -> X))} (h : g₁ subseteq g₂)
  证明: (gc_generateFrom _).monotone_l h

Depends on / 依赖: gc_generateFrom, monotone_l
-/
theorem generateFrom_mono {g₁ g₂ : Set ((n : Nat) × (𝔼ⁿ -> X))} (h : g₁ subseteq g₂) :
    generateFrom g₁ <= generateFrom g₂ :=
  (gc_generateFrom _).monotone_l h

/--
theorem `generateFrom_toPlots` / 定理 `generateFrom_toPlots`

English:
theorem generateFrom_toPlots
  given: (d : DiffeologicalSpace X)
  proof: (giGenerateFrom X).l_u_eq d

中文:
定理 generateFrom_toPlots
  条件: (d : Diffeological空间 X)
  证明: (giGenerateFrom X).l_u_eq d

Depends on / 依赖: giGenerateFrom, l_u_eq
-/
theorem generateFrom_toPlots (d : DiffeologicalSpace X) :
    generateFrom d.toPlots = d :=
  (giGenerateFrom X).l_u_eq d

/--
theorem `leftInverse_generateFrom` / 定理 `leftInverse_generateFrom`

English:
theorem leftInverse_generateFrom
  proof: (giGenerateFrom X).leftInverse_l_u

中文:
定理 leftInverse_generateFrom
  证明: (giGenerateFrom X).leftInverse_l_u

Depends on / 依赖: giGenerateFrom, leftInverse_l_u
-/
theorem leftInverse_generateFrom :
    Function.LeftInverse generateFrom (@toPlots X) :=
  (giGenerateFrom X).leftInverse_l_u

/--
theorem `generateFrom_surjective` / 定理 `generateFrom_surjective`

English:
theorem generateFrom_surjective
  statement: Function.Surjective (@generateFrom X)
  proof: (giGenerateFrom X).l_surjective

中文:
定理 generateFrom_surjective
  结论: 函数.满射 (@generateFrom X)
  证明: (giGenerateFrom X).l_surjective

Depends on / 依赖: giGenerateFrom, l_surjective
-/
theorem generateFrom_surjective : Function.Surjective (@generateFrom X) :=
  (giGenerateFrom X).l_surjective

/--
theorem `generateFrom_union` / 定理 `generateFrom_union`

English:
theorem generateFrom_union
  given: (g₁ g₂ : Set ((n : Nat) × (𝔼ⁿ -> X)))
  proof: (gc_generateFrom X).l_sup

中文:
定理 generateFrom_union
  条件: (g₁ g₂ : 集合 ((n : 自然数) × (𝔼ⁿ -> X)))
  证明: (gc_generateFrom X).l_sup

Depends on / 依赖: gc_generateFrom, l_sup
-/
theorem generateFrom_union (g₁ g₂ : Set ((n : Nat) × (𝔼ⁿ -> X))) :
    generateFrom (g₁ union g₂) = generateFrom g₁ ⊔ generateFrom g₂ :=
  (gc_generateFrom X).l_sup

/--
theorem `generateFrom_iUnion` / 定理 `generateFrom_iUnion`

English:
theorem generateFrom_iUnion
  given: {ι : Type*} {g : ι -> Set ((n : Nat) × (𝔼ⁿ -> X))}
  proof: (gc_generateFrom X).l_iSup

中文:
定理 generateFrom_iUnion
  条件: {ι : 类型} {g : ι -> 集合 ((n : 自然数) × (𝔼ⁿ -> X))}
  证明: (gc_generateFrom X).l_iSup

Depends on / 依赖: gc_generateFrom, l_iSup
-/
theorem generateFrom_iUnion {ι : Type*} {g : ι -> Set ((n : Nat) × (𝔼ⁿ -> X))} :
    generateFrom (⋃ i, g i) = ⨆ i, generateFrom (g i) :=
  (gc_generateFrom X).l_iSup

/--
theorem `generateFrom_sUnion` / 定理 `generateFrom_sUnion`

English:
theorem generateFrom_sUnion
  given: {G : Set (Set ((n : Nat) × (𝔼ⁿ -> X)))}
  proof: (gc_generateFrom X).l_sSup

中文:
定理 generateFrom_sUnion
  条件: {G : 集合 (集合 ((n : 自然数) × (𝔼ⁿ -> X)))}
  证明: (gc_generateFrom X).l_sSup

Depends on / 依赖: gc_generateFrom, l_sSup
-/
theorem generateFrom_sUnion {G : Set (Set ((n : Nat) × (𝔼ⁿ -> X)))} :
    generateFrom (⋃₀ G) = ⨆ s in G, generateFrom s :=
  (gc_generateFrom X).l_sSup

/--
theorem `toPlots_inf` / 定理 `toPlots_inf`

English:
theorem toPlots_inf
  given: (d₁ d₂ : DiffeologicalSpace X)
  proof: rfl

中文:
定理 toPlots_inf
  条件: (d₁ d₂ : Diffeological空间 X)
  证明: rfl
-/
theorem toPlots_inf (d₁ d₂ : DiffeologicalSpace X) :
    (d₁ ⊓ d₂).toPlots = d₁.toPlots inter d₂.toPlots := rfl

/--
theorem `toPlots_iInf` / 定理 `toPlots_iInf`

English:
theorem toPlots_iInf
  given: {ι : Type*} {D : ι -> DiffeologicalSpace X}
  proof: (gc_generateFrom X).u_iInf

中文:
定理 toPlots_iInf
  条件: {ι : 类型} {D : ι -> Diffeological空间 X}
  证明: (gc_generateFrom X).u_iInf

Depends on / 依赖: gc_generateFrom, u_iInf
-/
theorem toPlots_iInf {ι : Type*} {D : ι -> DiffeologicalSpace X} :
    (⨅ i, D i).toPlots = ⋂ i, (D i).toPlots :=
  (gc_generateFrom X).u_iInf

/--
theorem `toPlots_sInf` / 定理 `toPlots_sInf`

English:
theorem toPlots_sInf
  given: {D : Set (DiffeologicalSpace X)}
  statement: (sInf D).toPlots = ⋂ d in D, d.toPlots
  proof: (gc_generateFrom X).u_sInf

中文:
定理 toPlots_sInf
  条件: {D : 集合 (Diffeological空间 X)}
  结论: (sInf D).toPlots = ⋂ d in D, d.toPlots
  证明: (gc_generateFrom X).u_sInf

Depends on / 依赖: gc_generateFrom, u_sInf
-/
theorem toPlots_sInf {D : Set (DiffeologicalSpace X)} : (sInf D).toPlots = ⋂ d in D, d.toPlots :=
  (gc_generateFrom X).u_sInf

/--
theorem `generateFrom_union_toPlots` / 定理 `generateFrom_union_toPlots`

English:
theorem generateFrom_union_toPlots
  given: (d₁ d₂ : DiffeologicalSpace X)
  proof: (giGenerateFrom X).l_sup_u _ _

中文:
定理 generateFrom_union_toPlots
  条件: (d₁ d₂ : Diffeological空间 X)
  证明: (giGenerateFrom X).l_sup_u _ _

Depends on / 依赖: giGenerateFrom, l_sup_u
-/
theorem generateFrom_union_toPlots (d₁ d₂ : DiffeologicalSpace X) :
    generateFrom (d₁.toPlots union d₂.toPlots) = d₁ ⊔ d₂ :=
  (giGenerateFrom X).l_sup_u _ _

/--
theorem `generateFrom_iUnion_toPlots` / 定理 `generateFrom_iUnion_toPlots`

English:
theorem generateFrom_iUnion_toPlots
  given: {ι : Type*} (D : ι -> DiffeologicalSpace X)
  proof: (giGenerateFrom X).l_iSup_u _

中文:
定理 generateFrom_iUnion_toPlots
  条件: {ι : 类型} (D : ι -> Diffeological空间 X)
  证明: (giGenerateFrom X).l_iSup_u _

Depends on / 依赖: giGenerateFrom, l_iSup_u
-/
theorem generateFrom_iUnion_toPlots {ι : Type*} (D : ι -> DiffeologicalSpace X) :
    generateFrom (⋃ i, (D i).toPlots) = ⨆ i, D i :=
  (giGenerateFrom X).l_iSup_u _

/--
theorem `generateFrom_inter_toPlots` / 定理 `generateFrom_inter_toPlots`

English:
theorem generateFrom_inter_toPlots
  given: (d₁ d₂ : DiffeologicalSpace X)
  proof: (giGenerateFrom X).l_inf_u _ _

中文:
定理 generateFrom_inter_toPlots
  条件: (d₁ d₂ : Diffeological空间 X)
  证明: (giGenerateFrom X).l_inf_u _ _

Depends on / 依赖: giGenerateFrom, l_inf_u
-/
theorem generateFrom_inter_toPlots (d₁ d₂ : DiffeologicalSpace X) :
    generateFrom (d₁.toPlots inter d₂.toPlots) = d₁ ⊓ d₂ :=
  (giGenerateFrom X).l_inf_u _ _

/--
theorem `generateFrom_iInter_toPlots` / 定理 `generateFrom_iInter_toPlots`

English:
theorem generateFrom_iInter_toPlots
  given: {ι : Type*} (D : ι -> DiffeologicalSpace X)
  proof: (giGenerateFrom X).l_iInf_u _

中文:
定理 generateFrom_i整数er_toPlots
  条件: {ι : 类型} (D : ι -> Diffeological空间 X)
  证明: (giGenerateFrom X).l_iInf_u _

Depends on / 依赖: giGenerateFrom, l_iInf_u
-/
theorem generateFrom_iInter_toPlots {ι : Type*} (D : ι -> DiffeologicalSpace X) :
    generateFrom (⋂ i, (D i).toPlots) = ⨅ i, D i :=
  (giGenerateFrom X).l_iInf_u _

/--
theorem `generateFrom_iInter_of_generateFrom_eq_self` / 定理 `generateFrom_iInter_of_generateFrom_eq_self`

English:
theorem generateFrom_iInter_of_generateFrom_eq_self
  statement: {ι : Type*}
  proof: (giGenerateFrom X).l_iInf_of_u_l_eq_self G hG

中文:
定理 generateFrom_i整数er_of_generateFrom_eq_self
  结论: {ι : 类型}
  证明: (giGenerateFrom X).l_iInf_of_u_l_eq_self G hG

Depends on / 依赖: giGenerateFrom, l_iInf_of_u_l_eq_self
-/
theorem generateFrom_iInter_of_generateFrom_eq_self {ι : Type*}
    (G : ι -> Set ((n : Nat) × (𝔼ⁿ -> X)))
    (hG : forall i, (generateFrom (G i)).toPlots = G i) :
    generateFrom (⋂ i, G i) = ⨅ i, generateFrom (G i) :=
  (giGenerateFrom X).l_iInf_of_u_l_eq_self G hG

/--
theorem `isPlot_inf_iff` / 定理 `isPlot_inf_iff`

English:
theorem isPlot_inf_iff
  given: {d₁ d₂ : DiffeologicalSpace X} {n : Nat} {p : 𝔼ⁿ -> X}
  proof: Set.ext_iff.1 (toPlots_inf d₁ d₂) ⟨n, p⟩

中文:
定理 isPlot_inf_iff
  条件: {d₁ d₂ : Diffeological空间 X} {n : 自然数} {p : 𝔼ⁿ -> X}
  证明: Set.ext_iff.1 (toPlots_inf d₁ d₂) ⟨n, p⟩

Depends on / 依赖: Set.ext_iff, ext_iff, toPlots_inf
-/
theorem isPlot_inf_iff {d₁ d₂ : DiffeologicalSpace X} {n : Nat} {p : 𝔼ⁿ -> X} :
    (@IsPlot _ (d₁ ⊓ d₂)) p ↔ (@IsPlot _ d₁) p ∧ (@IsPlot _ d₂) p :=
  Set.ext_iff.1 (toPlots_inf d₁ d₂) ⟨n, p⟩

/--
theorem `isPlot_iInf_iff` / 定理 `isPlot_iInf_iff`

English:
theorem isPlot_iInf_iff
  given: {ι : Type*} {D : ι -> DiffeologicalSpace X} {n : Nat} {p : 𝔼ⁿ -> X}
  proof: (Set.ext_iff.1 (toPlots_iInf (D := D)) ⟨n, p⟩).trans Set.mem_iInter

中文:
定理 isPlot_iInf_iff
  条件: {ι : 类型} {D : ι -> Diffeological空间 X} {n : 自然数} {p : 𝔼ⁿ -> X}
  证明: (Set.ext_iff.1 (toPlots_iInf (D := D)) ⟨n, p⟩).trans Set.mem_iInter

Depends on / 依赖: Set.ext_iff, Set.mem_iInter, ext_iff, mem_iInter, toPlots_iInf
-/
theorem isPlot_iInf_iff {ι : Type*} {D : ι -> DiffeologicalSpace X} {n : Nat} {p : 𝔼ⁿ -> X} :
    (@IsPlot _ (⨅ i, D i)) p ↔ forall i, (@IsPlot _ (D i)) p :=
  (Set.ext_iff.1 (toPlots_iInf (D := D)) ⟨n, p⟩).trans Set.mem_iInter

/--
theorem `isPlot_sInf_iff` / 定理 `isPlot_sInf_iff`

English:
theorem isPlot_sInf_iff
  given: {D : Set (DiffeologicalSpace X)} {n : Nat} {p : 𝔼ⁿ -> X}
  proof: (Set.ext_iff.1 (toPlots_sInf (D := D)) ⟨n, p⟩).trans Set.mem_iInter₂

中文:
定理 isPlot_sInf_iff
  条件: {D : 集合 (Diffeological空间 X)} {n : 自然数} {p : 𝔼ⁿ -> X}
  证明: (Set.ext_iff.1 (toPlots_sInf (D := D)) ⟨n, p⟩).trans Set.mem_iInter₂

Depends on / 依赖: Set.ext_iff, Set.mem_iInter, ext_iff, toPlots_sInf
-/
theorem isPlot_sInf_iff {D : Set (DiffeologicalSpace X)} {n : Nat} {p : 𝔼ⁿ -> X} :
    (@IsPlot _ (sInf D)) p ↔ forall d in D, (@IsPlot _ d) p :=
  (Set.ext_iff.1 (toPlots_sInf (D := D)) ⟨n, p⟩).trans Set.mem_iInter₂

end DiffeologicalSpace

end CompleteLattice
