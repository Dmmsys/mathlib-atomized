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

local macro:max "𝔼" noWs n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

open Topology ContDiff

/-- A diffeology on `X`, given by the smooth functions (or "plots") from ℝⁿ to `X`. -/
/-
**DiffeologicalSpace** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：DiffeologicalSpace (X : Type*) where /-- The plots `EuclideanSpace ℝ (Fin 
n) → X` representing the smooth ways to map `EuclideanSpace ℝ (Fin n)` into `X`.
 This is the main piece of data underlying the diffeology. -/ plots (n : Nat) : 
Set (𝔼ⁿ -> X) /-- Every constant map needs to be a plot. -/ constant_plots {n : 
Nat} (x : X) : (fun _ => x) in plots n /-- Smooth reparametrisations of plots ne
ed to be plots. -/ plot_reparam {n m : Nat} {p : 𝔼ᵐ -> X} {f : 𝔼ⁿ -> 𝔼ᵐ} (hp : p
 in plots m) (hf : ContDif
参数：X : Type*；Fin n；Fin n；n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A diffeology on `X`, given by the smooth functions (or "plots") from ℝⁿ to `X`.
-/
class DiffeologicalSpace (X : Type*) where
  /-- The plots `EuclideanSpace ℝ (Fin n) → X` representing the smooth ways to map
  `EuclideanSpace ℝ (Fin n)` into `X`. This is the main
  piece of data underlying the diffeology. -/
  plots (n : ℕ) : Set (𝔼ⁿ → X)
  /-- Every constant map needs to be a plot. -/
  constant_plots {n : ℕ} (x : X) : (fun _ ↦ x) ∈ plots n
  /-- Smooth reparametrisations of plots need to be plots. -/
  plot_reparam {n m : ℕ} {p : 𝔼ᵐ → X} {f : 𝔼ⁿ → 𝔼ᵐ} (hp : p ∈ plots m) (hf : ContDiff ℝ ∞ f) :
    p ∘ f ∈ plots n
  /-- Every locally smooth map `EuclideanSpace ℝ (Fin n) → X` is a plot. -/
  locality {n : ℕ} {p : 𝔼ⁿ → X} (hp : ∀ x : 𝔼ⁿ, ∃ u : Set 𝔼ⁿ, IsOpen u ∧ x ∈ u ∧
    ∀ {m : ℕ} {f : 𝔼ᵐ → 𝔼ⁿ}, (∀ x, f x ∈ u) → ContDiff ℝ ∞ f → p ∘ f ∈ plots m) : p ∈ plots n
  /-- The D-topology of the diffeology. This is included as part of the data in order to give
  control over what the D-topology is defeq to. See also note [forgetful inheritance]. -/
  dTopology : TopologicalSpace X := {
    IsOpen u := ∀ ⦃n : ℕ⦄, ∀ p ∈ plots n, IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ _ ↦ isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp ↦
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp ↦
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu ↦ hs u hu p hp }
  /-- The D-topology consists of exactly those sets whose preimages under plots are all open. -/
  isOpen_iff_preimages_plots {u : Set X} :
    dTopology.IsOpen u ↔ ∀ {n : ℕ}, ∀ p ∈ plots n, IsOpen (p ⁻¹' u) := by rfl

namespace Diffeology

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

section Defs

alias dTopology := DiffeologicalSpace.dTopology

/-- A map `p : EuclideanSpace ℝ (Fin n) → X` is called a plot iff it is part of the diffeology on
`X`. This is equivalent to `p` being smooth with respect to the standard diffeology on
`EuclideanSpace ℝ (Fin n)`. -/
@[fun_prop]
/-
**Diffeology.IsPlot** 是 Mathlib 中的一个定义，位于命名空间 `Diffeology`。
形式化陈述：IsPlot {n : Nat} (p : 𝔼ⁿ -> X) : Prop
参数：p : 𝔼ⁿ -> X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `p : EuclideanSpace ℝ (Fin n) → X` is called a plot iff it is part of the 
diffeology on
`X`. This is equivalent to `p` being smooth with respect to the standard diffeol
ogy on
`EuclideanSpace ℝ (Fin n)`.
-/
def IsPlot {n : ℕ} (p : 𝔼ⁿ → X) : Prop := p ∈ DiffeologicalSpace.plots n

/-- A function between diffeological spaces is smooth iff composition with it preserves
smoothness of plots. -/
@[fun_prop]
/-
**Diffeology.DSmooth** 是 Mathlib 中的一个定义，位于命名空间 `Diffeology`。
形式化陈述：DSmooth (f : X -> Y) : Prop
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function between diffeological spaces is smooth iff composition with it preser
ves
smoothness of plots.
-/
def DSmooth (f : X → Y) : Prop := ∀ (n : ℕ) (p : 𝔼ⁿ → X), IsPlot p → IsPlot (f ∘ p)

end Defs

@[ext]
/-
**Diffeology._root_.DiffeologicalSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.DiffeologicalSpace.ext {X : Type*} {d₁ d₂ : DiffeologicalSpace X}
    (h : @IsPlot _ d₁ = @IsPlot _ d₂) : d₁ = d₂ := by
  obtain ⟨p₁, _, _, _, t₁, h₁⟩ := d₁
  obtain ⟨p₂, _, _, _, t₂, h₂⟩ := d₂
  congr 1; ext s
  exact ((show p₁ = p₂ from h) ▸ @h₁ s).trans (@h₂ s).symm

@[fun_prop]
/-
**Diffeology.isPlot_const** 是 Mathlib 中的一个引理，位于命名空间 `Diffeology`。
形式化陈述：isPlot_const {n : Nat} {x : X} : IsPlot (fun _ => x : 𝔼ⁿ -> X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffeologicalSpace.constant_plots`：∀ {X : Type u_1} [self : Diffeologica
lSpace X] {n : ℕ} (x : X), (fun x_1 => x) ∈ DiffeologicalSpace.plots n
-/
lemma isPlot_const {n : ℕ} {x : X} : IsPlot (fun _ ↦ x : 𝔼ⁿ → X) :=
  DiffeologicalSpace.constant_plots x
/-
**Diffeology.isPlot_reparam** 是 Mathlib 中的一个引理，位于命名空间 `Diffeology`。
形式化陈述：isPlot_reparam {n m : Nat} {p : 𝔼ᵐ -> X} {f : 𝔼ⁿ -> 𝔼ᵐ} (hp : IsPlot p) (h
f : ContDiff Real ∞ f) : IsPlot (p ∘ f)
参数：hp : IsPlot p；hf : ContDiff Real ∞ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `DiffeologicalSpace.plot_reparam`：∀ {X : Type u_1} [self : DiffeologicalS
pace X] {n m : ℕ} {p : EuclideanSpace ℝ (Fin m) → X}   {f : EuclideanSpace ℝ (Fi
n n) → EuclideanSpace…
-/
lemma isPlot_reparam {n m : ℕ} {p : 𝔼ᵐ → X} {f : 𝔼ⁿ → 𝔼ᵐ} (hp : IsPlot p) (hf : ContDiff ℝ ∞ f) :
    IsPlot (p ∘ f) :=
  DiffeologicalSpace.plot_reparam hp hf
/-
**Diffeology.IsPlot.dSmooth_comp** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology.IsPlot`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : DiffeologicalSpace X] [inst_1 : Di
ffeologicalSpace Y] {n : ℕ}   {p : EuclideanSpace ℝ (Fin n) → X} {f : X → Y}, Di
ffeology.IsPlot p → Diffeology.DSmooth f → Diffeology.IsPlot (f ∘ p)
参数：Fin n；f ∘ p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma IsPlot.dSmooth_comp {n : ℕ} {p : 𝔼ⁿ → X} {f : X → Y}
    (hp : IsPlot p) (hf : DSmooth f) : IsPlot (f ∘ p) :=
  hf n p hp

@[fun_prop]
/-
**Diffeology.IsPlot.dSmooth_comp'** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology.IsPlot`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : DiffeologicalSpace X] [inst_1 : Di
ffeologicalSpace Y] {n : ℕ}   {p : EuclideanSpace ℝ (Fin n) → X} {f : X → Y},   
Diffeology.IsPlot p → Diffeology.DSmooth f → Diffeology.IsPlot fun x => f (p x)
参数：Fin n；p x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma IsPlot.dSmooth_comp' {n : ℕ} {p : 𝔼ⁿ → X} {f : X → Y}
    (hp : IsPlot p) (hf : DSmooth f) : IsPlot fun x ↦ f (p x) :=
  hf n p hp
/-
**Diffeology.isOpen_iff_preimages_plots** 是 Mathlib 中的一个引理，位于命名空间 `Diffeology`。
形式化陈述：isOpen_iff_preimages_plots {u : Set X} : IsOpen[dTopology] u ↔ forall (n :
 Nat) (p : 𝔼ⁿ -> X), IsPlot p -> IsOpen (p ⁻¹' u)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffeologicalSpace.isOpen_iff_preimages_plots`：∀ {X : Type u_1} [self : 
DiffeologicalSpace X] {u : Set X},   TopologicalSpace.IsOpen u ↔ ∀ {n : ℕ}, ∀ p 
∈ DiffeologicalSpace.plots n, IsOpe…
-/
lemma isOpen_iff_preimages_plots {u : Set X} :
    IsOpen[dTopology] u ↔ ∀ (n : ℕ) (p : 𝔼ⁿ → X), IsPlot p → IsOpen (p ⁻¹' u) :=
  DiffeologicalSpace.isOpen_iff_preimages_plots
/-
**Diffeology.IsPlot.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology.IsPlot`。
形式化陈述：∀ {X : Type u_1} [inst : DiffeologicalSpace X] {n : ℕ} {p : EuclideanSpace
 ℝ (Fin n) → X},   Diffeology.IsPlot p → Continuous p
参数：Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Diffeology.isOpen_iff_preimages_plots`：isOpen_iff_preimages_plots {u : S
et X} : IsOpen[dTopology] u ↔ forall (n : Nat) (p : 𝔼ⁿ -> X), IsPlot p -> IsOpen
 (p ⁻¹' u)
-/
protected lemma IsPlot.continuous {n : ℕ} {p : 𝔼ⁿ → X} (hp : IsPlot p) :
    Continuous[_, dTopology] p :=
  continuous_def.2 fun _ hu ↦ isOpen_iff_preimages_plots.1 hu n p hp
/-
**Diffeology.DSmooth.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology.DSmooth`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : DiffeologicalSpace X] [inst_1 : Di
ffeologicalSpace Y] {f : X → Y},   Diffeology.DSmooth f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Diffeology.isOpen_iff_preimages_plots`：isOpen_iff_preimages_plots {u : S
et X} : IsOpen[dTopology] u ↔ forall (n : Nat) (p : 𝔼ⁿ -> X), IsPlot p -> IsOpen
 (p ⁻¹' u)
-/
protected theorem DSmooth.continuous {f : X → Y} (hf : DSmooth f) :
    Continuous[dTopology, dTopology] f := by
  simp_rw [continuous_def, isOpen_iff_preimages_plots (X := X), isOpen_iff_preimages_plots (X := Y)]
  exact fun u hu n p hp ↦ hu n (f ∘ p) (hf n p hp)
/-
**Diffeology.dSmooth_iff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology`。
形式化陈述：dSmooth_iff {f : X -> Y} : DSmooth f ↔ forall (n : Nat) (p : 𝔼ⁿ -> X), IsP
lot p -> IsPlot (f ∘ p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dSmooth_iff {f : X → Y} :
    DSmooth f ↔ ∀ (n : ℕ) (p : 𝔼ⁿ → X), IsPlot p → IsPlot (f ∘ p) :=
  Iff.rfl
/-
**Diffeology.dSmooth_id** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology`。
形式化陈述：dSmooth_id : DSmooth (@id X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem dSmooth_id : DSmooth (@id X) := by simp [DSmooth]

@[fun_prop]
/-
**Diffeology.dSmooth_id'** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology`。
形式化陈述：dSmooth_id' : DSmooth fun x : X => x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeology.dSmooth_id`：dSmooth_id : DSmooth (@id X)
-/
theorem dSmooth_id' : DSmooth fun x : X ↦ x := dSmooth_id
/-
**Diffeology.DSmooth.comp** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology.DSmooth`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : DiffeologicalSpace 
X] [inst_1 : DiffeologicalSpace Y]   [inst_2 : DiffeologicalSpace Z] {f : X → Y}
 {g : Y → Z},   Diffeology.DSmooth g → Diffeology.DSmooth f → Diffeology.DSmooth
 (g ∘ f)
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem DSmooth.comp {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (g ∘ f) :=
  fun _ _ hp ↦ hg _ _ (hf _ _ hp)

@[fun_prop]
/-
**Diffeology.DSmooth.comp'** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology.DSmooth`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : DiffeologicalSpace 
X] [inst_1 : DiffeologicalSpace Y]   [inst_2 : DiffeologicalSpace Z] {f : X → Y}
 {g : Y → Z},   Diffeology.DSmooth g → Diffeology.DSmooth f → Diffeology.DSmooth
 fun x => g (f x)
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeology.DSmooth.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} 
[inst : DiffeologicalSpace X] [inst_1 : DiffeologicalSpace Y]   [inst_2 : Diffeo
logicalSpace …
-/
theorem DSmooth.comp' {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (fun x ↦ g (f x)) := hg.comp hf

@[fun_prop]
/-
**Diffeology.dSmooth_const** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology`。
形式化陈述：dSmooth_const {y : Y} : DSmooth fun _ : X => y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Diffeology.isPlot_const`：isPlot_const {n : Nat} {x : X} : IsPlot (fun _ 
=> x : 𝔼ⁿ -> X)
-/
theorem dSmooth_const {y : Y} : DSmooth fun _ : X ↦ y :=
  fun _ _ _ ↦ isPlot_const

end Diffeology

namespace DiffeologicalSpace

/-- Replaces the D-topology of a diffeology with another topology equal to it. Useful
to construct diffeologies with better definitional equalities. -/
@[instance_reducible]
/-
**DiffeologicalSpace.replaceDTopology** 是 Mathlib 中的一个定义，位于命名空间 `DiffeologicalSp
ace`。
形式化陈述：replaceDTopology {X : Type*} (d : DiffeologicalSpace X) (t : TopologicalSp
ace X) (h : @dTopology _ d = t) : DiffeologicalSpace X where dTopology
参数：d : DiffeologicalSpace X；t : TopologicalSpace X；h : @dTopology _ d = t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DiffeologicalSpace.constant_plots`：∀ {X : Type u_1} [self : Diffeologica
lSpace X] {n : ℕ} (x : X), (fun x_1 => x) ∈ DiffeologicalSpace.plots n
· 使用定理 `DiffeologicalSpace.plot_reparam`：∀ {X : Type u_1} [self : DiffeologicalS
pace X] {n m : ℕ} {p : EuclideanSpace ℝ (Fin m) → X}   {f : EuclideanSpace ℝ (Fi
n n) → EuclideanSpace…
· 使用定理 `DiffeologicalSpace.locality`：∀ {X : Type u_1} [self : DiffeologicalSpace
 X] {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → X},   (∀ (x : EuclideanSpace ℝ (Fin 
n)),       ∃ u,  …

--- 原说明 ---
Replaces the D-topology of a diffeology with another topology equal to it. Usefu
l
to construct diffeologies with better definitional equalities.
-/
def replaceDTopology {X : Type*} (d : DiffeologicalSpace X)
    (t : TopologicalSpace X) (h : @dTopology _ d = t) : DiffeologicalSpace X where
  dTopology := t
  isOpen_iff_preimages_plots := by intro _; rw [← d.isOpen_iff_preimages_plots, ← h]
  __ := d
/-
**DiffeologicalSpace.replaceDTopology_eq** 是 Mathlib 中的一个引理，位于命名空间 `Diffeologica
lSpace`。
形式化陈述：replaceDTopology_eq {X : Type*} {d : DiffeologicalSpace X} {t : Topologica
lSpace X} {h : @dTopology _ d = t} : d.replaceDTopology t h = d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffeologicalSpace.ext`：∀ {X : Type u_4} {d₁ d₂ : DiffeologicalSpace X},
 @Diffeology.IsPlot X d₁ = @Diffeology.IsPlot X d₂ → d₁ = d₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma replaceDTopology_eq {X : Type*} {d : DiffeologicalSpace X}
    {t : TopologicalSpace X} {h : @dTopology _ d = t} : d.replaceDTopology t h = d := by
  ext; rfl

/-- A structure with plots specified on open subsets of ℝⁿ rather than ℝⁿ itself. Useful
for constructing diffeologies, as it often makes the locality condition easier to prove. -/
/-
**DiffeologicalSpace.CorePlotsOn** 是 Mathlib 中的一个结构，位于命名空间 `DiffeologicalSpace`。
形式化陈述：CorePlotsOn (X : Type*) where /-- The predicate determining which maps `u 
→ X` with `u : Set (EuclideanSpace ℝ (Fin n))` open are plots. -/ isPlotOn {n : 
Nat} {u : Set 𝔼ⁿ} (hu : IsOpen u) : (𝔼ⁿ -> X) -> Prop isPlotOn_congr {n : Nat} {
u : Set 𝔼ⁿ} (hu : IsOpen u) {p q : 𝔼ⁿ -> X} (h : Set.EqOn p q u) : isPlotOn hu p
 ↔ isPlotOn hu q /-- The predicate that the diffeology built from this structure
 will use. Can be overwritten to allow for better definitional equalities. -/ is
Plot {n : Nat} : (𝔼ⁿ -> X)
参数：X : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure with plots specified on open subsets of ℝⁿ rather than ℝⁿ itself. Us
eful
for constructing diffeologies, as it often makes the locality condition easier t
o prove.
-/
structure CorePlotsOn (X : Type*) where
  /-- The predicate determining which maps `u → X` with `u : Set (EuclideanSpace ℝ (Fin n))` open
  are plots. -/
  isPlotOn {n : ℕ} {u : Set 𝔼ⁿ} (hu : IsOpen u) : (𝔼ⁿ → X) → Prop
  isPlotOn_congr {n : ℕ} {u : Set 𝔼ⁿ} (hu : IsOpen u) {p q : 𝔼ⁿ → X} (h : Set.EqOn p q u) :
    isPlotOn hu p ↔ isPlotOn hu q
  /-- The predicate that the diffeology built from this structure will use. Can be overwritten
  to allow for better definitional equalities. -/
  isPlot {n : ℕ} : (𝔼ⁿ → X) → Prop := fun p ↦ isPlotOn isOpen_univ p
  isPlotOn_univ {n : ℕ} {p : 𝔼ⁿ → X} :
    isPlotOn isOpen_univ p ↔ isPlot p := by simp
  isPlot_const {n : ℕ} (x : X) : isPlot fun (_ : 𝔼ⁿ) ↦ x
  isPlotOn_reparam {n m : ℕ} {u : Set 𝔼ⁿ} {v : Set 𝔼ᵐ} {hu : IsOpen u} (hv : IsOpen v)
    {p : 𝔼ⁿ → X} {f : 𝔼ᵐ → 𝔼ⁿ} (h : Set.MapsTo f v u) (hp : isPlotOn hu p)
    (hf : ContDiffOn ℝ ∞ f v) : isPlotOn hv (p ∘ f)
  /-- The locality axiom of diffeologies, phrased in terms of `isPlotOn`. -/
  locality {n : ℕ} {u : Set 𝔼ⁿ} (hu : IsOpen u) {p : 𝔼ⁿ → X}
    (hp : ∀ x ∈ u, ∃ (v : Set _) (hv : IsOpen v), x ∈ v ∧ isPlotOn hv p) : isPlotOn hu p
  /-- The D-topology that the diffeology built from this structure will use. Can be overwritten
  to allow for better definitional equalities. -/
  dTopology : TopologicalSpace X := {
    IsOpen u := ∀ ⦃n : ℕ⦄, ∀ p : 𝔼ⁿ → X, isPlot p → IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ _ ↦ isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp ↦
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp ↦
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu ↦ hs u hu p hp }
  isOpen_iff_preimages_plots {u : Set X} : dTopology.IsOpen u ↔
    ∀ {n : ℕ}, ∀ p : 𝔼ⁿ → X, isPlot p → IsOpen (p ⁻¹' u) := by rfl

/-- Constructs a diffeology from plots defined on open subsets or ℝⁿ rather than ℝⁿ itself,
organised in the form of the auxiliary `CorePlotsOn` structure.
This is more involved in most regards, but also often makes it quite a lot easier to prove
the locality condition. -/
@[instance_reducible]
/-
**DiffeologicalSpace.ofCorePlotsOn** 是 Mathlib 中的一个定义，位于命名空间 `DiffeologicalSpace
`。
形式化陈述：ofCorePlotsOn {X : Type*} (d : DiffeologicalSpace.CorePlotsOn X) : Diffeol
ogicalSpace X where plots _
参数：d : DiffeologicalSpace.CorePlotsOn X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DiffeologicalSpace.CorePlotsOn.isPlot_const`：∀ {X : Type u_1} (self : Di
ffeologicalSpace.CorePlotsOn X) {n : ℕ} (x : X), self.isPlot fun x_1 => x
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `DiffeologicalSpace.CorePlotsOn.isOpen_iff_preimages_plots`：∀ {X : Type u
_1} (self : DiffeologicalSpace.CorePlotsOn X) {u : Set X},   TopologicalSpace.Is
Open u ↔ ∀ {n : ℕ} (p : EuclideanSpace ℝ (Fin n…

--- 原说明 ---
Constructs a diffeology from plots defined on open subsets or ℝⁿ rather than ℝⁿ 
itself,
organised in the form of the auxiliary `CorePlotsOn` structure.
This is more involved in most regards, but also often makes it quite a lot easie
r to prove
the locality condition.
-/
def ofCorePlotsOn {X : Type*} (d : DiffeologicalSpace.CorePlotsOn X) :
    DiffeologicalSpace X where
  plots _ := {p | d.isPlot p}
  constant_plots _ := d.isPlot_const _
  plot_reparam hp hf := d.isPlotOn_univ.mp <|
    d.isPlotOn_reparam _ (Set.mapsTo_univ _ _) (d.isPlotOn_univ.mpr hp) hf.contDiffOn
  locality {n p} h := by
    refine d.isPlotOn_univ.mp <| d.locality _ fun x _ ↦ ?_
    let ⟨u, hu, hxu, hu'⟩ := h x
    let ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp hu x hxu
    have h : d.isPlot (p ∘ OpenPartialHomeomorph.univBall x ε) := hu'
      (f := OpenPartialHomeomorph.univBall x ε)
      (fun x' ↦ by
        replace h := (OpenPartialHomeomorph.univBall x ε).map_source (x := x')
        rw [OpenPartialHomeomorph.univBall_target x hε] at h
        aesop)
      OpenPartialHomeomorph.contDiff_univBall
    have h' := d.isPlotOn_reparam (Metric.isOpen_ball) (Set.mapsTo_univ _ _)
      (d.isPlotOn_univ.mpr h) (OpenPartialHomeomorph.contDiffOn_univBall_symm (c := x) (r := ε))
    refine ⟨_, Metric.isOpen_ball, Metric.mem_ball_self hε, (d.isPlotOn_congr _ ?_).mp h'⟩
    rw [Function.comp_assoc, ← OpenPartialHomeomorph.coe_trans]
    apply Set.EqOn.comp_left
    convert! (OpenPartialHomeomorph.symm_trans_self (OpenPartialHomeomorph.univBall x ε)).2
    simp [OpenPartialHomeomorph.univBall_target x hε]
  dTopology := d.dTopology
  isOpen_iff_preimages_plots := d.isOpen_iff_preimages_plots

end DiffeologicalSpace

namespace Diffeology

/-- Technical condition saying that the topology on a type agrees with the D-topology.
Necessary because the D-topologies on for example products and subspaces don't agree with
the product and subspace topologies. -/
/-
**Diffeology.IsDTopologyCompatible** 是 Mathlib 中的一个类，位于命名空间 `Diffeology`。
形式化陈述：IsDTopologyCompatible (X : Type*) [t : TopologicalSpace X] [DiffeologicalS
pace X] : Prop where dTop_eq (X) : dTopology = t  /-- A smooth function between 
spaces that are equipped with the D-topology is continuous. -/ protected theorem
 DSmooth.continuous' {X Y : Type*} [TopologicalSpace X] [DiffeologicalSpace X] [
IsDTopologyCompatible X] [TopologicalSpace Y] [DiffeologicalSpace Y] [IsDTopolog
yCompatible Y] {f : X -> Y} (hf : DSmooth f) : Continuous f
参数：X : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Technical condition saying that the topology on a type agrees with the D-topolog
y.
Necessary because the D-topologies on for example products and subspaces don't a
gree with
the product and subspace topologies.
-/
class IsDTopologyCompatible (X : Type*) [t : TopologicalSpace X] [DiffeologicalSpace X] : Prop where
  dTop_eq (X) : dTopology = t

/-- A smooth function between spaces that are equipped with the D-topology is continuous. -/
/-
**Diffeology.DSmooth.continuous'** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology.DSmooth`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Diff
eologicalSpace X]   [Diffeology.IsDTopologyCompatible X] [inst_3 : TopologicalSp
ace Y] [inst_4 : DiffeologicalSpace Y]   [Diffeology.IsDTopologyCompatible Y] {f
 : X → Y}, Diffeology.DSmooth f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Diffeology.IsDTopologyCompatible.dTop_eq`：∀ (X : Type u_1) {t : Topologi
calSpace X} {inst : DiffeologicalSpace X} [self : Diffeology.IsDTopologyCompatib
le X],   Diffeology.dTopology …
· 使用定理 `Diffeology.DSmooth.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : D
iffeologicalSpace X] [inst_1 : DiffeologicalSpace Y] {f : X → Y},   Diffeology.D
Smooth f → Continuo…

--- 原说明 ---
A smooth function between spaces that are equipped with the D-topology is contin
uous.
-/
protected theorem DSmooth.continuous' {X Y : Type*}
    [TopologicalSpace X] [DiffeologicalSpace X] [IsDTopologyCompatible X]
    [TopologicalSpace Y] [DiffeologicalSpace Y] [IsDTopologyCompatible Y]
    {f : X → Y} (hf : DSmooth f) : Continuous f := by
  convert! hf.continuous
  · rw [IsDTopologyCompatible.dTop_eq X]
  · rw [IsDTopologyCompatible.dTop_eq Y]

/-- Technical condition saying that the diffeology on a space is the one coming from
smoothness in the sense of `ContDiff ℝ ∞`. Necessary as a hypothesis for some theorems
because some normed spaces carry a diffeology that is equal but not defeq to the normed space
diffeology (for example the product diffeology in the case of `Fin n → ℝ`), so the information
that these theorems still holds needs to be made available via this typeclass. -/
/-
**Diffeology.IsContDiffCompatible** 是 Mathlib 中的一个归纳类型，位于命名空间 `Diffeology`。
形式化陈述：(X : Type u_1) → [inst : NormedAddCommGroup X] → [NormedSpace ℝ X] → [Diff
eologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Technical condition saying that the diffeology on a space is the one coming from
smoothness in the sense of `ContDiff ℝ ∞`. Necessary as a hypothesis for some th
eorems
because some normed spaces carry a diffeology that is equal but not defeq to the
 normed space
diffeology (for example the product diffeology in the case of `Fin n → ℝ`), so t
he information
that these theorems still holds needs to be made available via this typeclass.
-/
class IsContDiffCompatible (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [DiffeologicalSpace X] : Prop where
  isPlot_iff {n : ℕ} {p : 𝔼ⁿ → X} : IsPlot p ↔ ContDiff ℝ ∞ p

/-- Diffeology on a finite-dimensional normed space. We make this a definition instead of an
instance because we also want to have product diffeologies as an instance, and having both would
cause instance diamonds on spaces like `Fin n → ℝ`. -/
@[instance_reducible]
/-
**Diffeology._root_.NormedSpace.toDiffeology** 是 Mathlib 中的一个定义，位于命名空间 `Diffeolo
gy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Diffeology on a finite-dimensional normed space. We make this a definition inste
ad of an
instance because we also want to have product diffeologies as an instance, and h
aving both would
cause instance diamonds on spaces like `Fin n → ℝ`.
-/
def _root_.NormedSpace.toDiffeology (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    DiffeologicalSpace X :=
  .ofCorePlotsOn {
    isPlotOn := fun {_ u} _ p ↦ ContDiffOn ℝ ∞ p u
    isPlotOn_congr := fun _ _ _ h ↦ contDiffOn_congr h
    isPlot := fun p ↦ ContDiff ℝ ∞ p
    isPlotOn_univ := contDiffOn_univ
    isPlot_const := fun _ ↦ contDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf ↦ hp.comp hf h.subset_preimage
    locality := fun _ _ h ↦ fun x hxu ↦ by
      let ⟨v, hv, hxv, hv'⟩ := h x hxu
      exact ((hv' x hxv).contDiffAt (hv.mem_nhds hxv)).contDiffWithinAt
    dTopology := inferInstance
    isOpen_iff_preimages_plots := fun {u} ↦ by
      refine ⟨fun hu _ _ hp ↦ IsOpen.preimage (hp.continuous) hu, fun h ↦ ?_⟩
      rw [← toEuclidean.preimage_symm_preimage u]
      exact toEuclidean.continuous.isOpen_preimage _ (h _ toEuclidean.symm.contDiff) }

attribute [local instance] NormedSpace.toDiffeology in
/-
**Diffeology.** 是 Mathlib 中的一个实例，位于命名空间 `Diffeology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    IsContDiffCompatible X :=
  ⟨Iff.rfl⟩
/-
**Diffeology._root_.NormedSpace.isContDiffCompatible_iff_eq_toDiffeology** 是 Mat
hlib 中的一个引理，位于命名空间 `Diffeology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NormedSpace.isContDiffCompatible_iff_eq_toDiffeology {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [d : DiffeologicalSpace X] :
    IsContDiffCompatible X ↔ d = NormedSpace.toDiffeology X :=
  ⟨fun _ ↦ by ext n p; exact IsContDiffCompatible.isPlot_iff, fun h ↦ h ▸ inferInstance⟩

attribute [local instance] NormedSpace.toDiffeology in
/-
**Diffeology.** 是 Mathlib 中的一个实例，位于命名空间 `Diffeology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    IsDTopologyCompatible X :=
  ⟨rfl⟩
/-
**Diffeology.** 是 Mathlib 中的一个实例，位于命名空间 `Diffeology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiffeologicalSpace ℝ := NormedSpace.toDiffeology _
/-
**Diffeology.** 是 Mathlib 中的一个实例，位于命名空间 `Diffeology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} [Fintype ι] : DiffeologicalSpace (EuclideanSpace ℝ ι) :=
  NormedSpace.toDiffeology _

variable {X : Type*} [DiffeologicalSpace X] {n : ℕ}

@[fun_prop]
/-
**Diffeology.IsPlot.dSmooth** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology.IsPlot`。
形式化陈述：∀ {X : Type u_1} [inst : DiffeologicalSpace X] {n : ℕ} {p : EuclideanSpace
 ℝ (Fin n) → X},   Diffeology.IsPlot p → Diffeology.DSmooth p
参数：Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Diffeology.isPlot_reparam`：isPlot_reparam {n m : Nat} {p : 𝔼ᵐ -> X} {f :
 𝔼ⁿ -> 𝔼ᵐ} (hp : IsPlot p) (hf : ContDiff Real ∞ f) : IsPlot (p ∘ f)
-/
protected theorem IsPlot.dSmooth {p : 𝔼ⁿ → X} (hp : IsPlot p) : DSmooth p :=
  fun _ _ ↦ isPlot_reparam hp

@[fun_prop]
/-
**Diffeology.DSmooth.isPlot** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology.DSmooth`。
形式化陈述：∀ {X : Type u_1} [inst : DiffeologicalSpace X] {n : ℕ} {p : EuclideanSpace
 ℝ (Fin n) → X},   Diffeology.DSmooth p → Diffeology.IsPlot p
参数：Fin n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
protected theorem DSmooth.isPlot {p : 𝔼ⁿ → X} (hp : DSmooth p) : IsPlot p :=
  hp n id <| contDiff_id (n := ∞)
/-
**Diffeology.isPlot_iff_dSmooth** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology`。
形式化陈述：isPlot_iff_dSmooth {p : 𝔼ⁿ -> X} : IsPlot p ↔ DSmooth p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeology.IsPlot.dSmooth`：∀ {X : Type u_1} [inst : DiffeologicalSpace X
] {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → X},   Diffeology.IsPlot p → Diffeology
.DSmooth p
· 使用定理 `Diffeology.DSmooth.isPlot`：∀ {X : Type u_1} [inst : DiffeologicalSpace X
] {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → X},   Diffeology.DSmooth p → Diffeolog
y.IsPlot p
-/
theorem isPlot_iff_dSmooth {p : 𝔼ⁿ → X} : IsPlot p ↔ DSmooth p :=
  ⟨IsPlot.dSmooth, DSmooth.isPlot⟩
/-
**Diffeology.isPlot_id** 是 Mathlib 中的一个引理，位于命名空间 `Diffeology`。
形式化陈述：isPlot_id : IsPlot (@id 𝔼ⁿ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
lemma isPlot_id : IsPlot (@id 𝔼ⁿ) := contDiff_id (n := ∞)

@[fun_prop]
/-
**Diffeology.isPlot_id'** 是 Mathlib 中的一个引理，位于命名空间 `Diffeology`。
形式化陈述：isPlot_id' : IsPlot fun x : 𝔼ⁿ => x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Diffeology.isPlot_id`：isPlot_id : IsPlot (@id 𝔼ⁿ)
-/
lemma isPlot_id' : IsPlot fun x : 𝔼ⁿ ↦ x := isPlot_id

variable {Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [IsContDiffCompatible X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [DiffeologicalSpace Y] [IsContDiffCompatible Y]
/-
**Diffeology.isPlot_iff_contDiff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology`。
形式化陈述：isPlot_iff_contDiff {p : 𝔼ⁿ -> X} : IsPlot p ↔ ContDiff Real ∞ p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeology.IsContDiffCompatible.isPlot_iff`：∀ {X : Type u_1} {inst : Nor
medAddCommGroup X} {inst_1 : NormedSpace ℝ X} {inst_2 : DiffeologicalSpace X}   
[self : Diffeology.IsContDiffCom…
-/
theorem isPlot_iff_contDiff {p : 𝔼ⁿ → X} : IsPlot p ↔ ContDiff ℝ ∞ p :=
  IsContDiffCompatible.isPlot_iff

@[fun_prop]
/-
**Diffeology._root_.ContDiff.isPlot** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.ContDiff.isPlot {p : 𝔼ⁿ → X} (hp : ContDiff ℝ ∞ p) : IsPlot p :=
  isPlot_iff_contDiff.2 hp

@[fun_prop]
/-
**Diffeology.IsPlot.contDiff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology.IsPlot`。
形式化陈述：∀ {X : Type u_1} [inst : DiffeologicalSpace X] {n : ℕ} [inst_1 : NormedAdd
CommGroup X] [inst_2 : NormedSpace ℝ X]   [Diffeology.IsContDiffCompatible X] {p
 : EuclideanSpace ℝ (Fin n) → X}, Diffeology.IsPlot p → ContDiff ℝ (↑⊤) p
参数：Fin n；↑⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Diffeology.isPlot_iff_contDiff`：isPlot_iff_contDiff {p : 𝔼ⁿ -> X} : IsPl
ot p ↔ ContDiff Real ∞ p
-/
protected theorem IsPlot.contDiff {p : 𝔼ⁿ → X} (hp : IsPlot p) : ContDiff ℝ ∞ p :=
  isPlot_iff_contDiff.1 hp

@[fun_prop]
/-
**Diffeology._root_.ContDiff.dSmooth** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.ContDiff.dSmooth {f : X → Y} (hf : ContDiff ℝ ∞ f) : DSmooth f :=
  fun _ _ hp ↦ (hf.comp hp.contDiff).isPlot

@[fun_prop]
/-
**Diffeology.DSmooth.contDiff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology.DSmooth`。
形式化陈述：∀ {X : Type u_1} [inst : DiffeologicalSpace X] {Y : Type u_2} [inst_1 : No
rmedAddCommGroup X] [inst_2 : NormedSpace ℝ X]   [Diffeology.IsContDiffCompatibl
e X] [inst_4 : NormedAddCommGroup Y] [inst_5 : NormedSpace ℝ Y]   [inst_6 : Diff
eologicalSpace Y] [Diffeology.IsContDiffCompatible Y] [FiniteDimensional ℝ X] {f
 : X → Y},   Diffeology.DSmooth f → ContDiff ℝ (↑⊤) f
参数：↑⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `ContinuousLinearEquiv.symm_comp_self`：symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂
) : (e.symm : M₂ -> M₁) ∘ (e : M₁ -> M₂) = id
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Diffeology.IsPlot.contDiff`：∀ {X : Type u_1} [inst : DiffeologicalSpace 
X] {n : ℕ} [inst_1 : NormedAddCommGroup X] [inst_2 : NormedSpace ℝ X]   [Diffeol
ogy.IsContDiffCo…
· 使用定理 `ContDiff.isPlot`：∀ {X : Type u_1} [inst : DiffeologicalSpace X] {n : ℕ} 
[inst_1 : NormedAddCommGroup X] [inst_2 : NormedSpace ℝ X]   [Diffeology.IsContD
iffCo…
· 使用定理 `ContinuousLinearEquiv.contDiff`：ContinuousLinearEquiv.contDiff (f : E ≃L
[𝕜] F) : ContDiff 𝕜 n f
-/
protected theorem DSmooth.contDiff [FiniteDimensional ℝ X] {f : X → Y} (hf : DSmooth f) :
    ContDiff ℝ ∞ f := by
  let g := toEuclidean (E := X)
  rw [← Function.comp_id f, ← g.symm_comp_self]
  exact (hf _ _ g.symm.contDiff.isPlot).contDiff.comp g.contDiff
/-
**Diffeology.dSmooth_iff_contDiff** 是 Mathlib 中的一个定理，位于命名空间 `Diffeology`。
形式化陈述：dSmooth_iff_contDiff [FiniteDimensional Real X] {f : X -> Y} : DSmooth f ↔
 ContDiff Real ∞ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Diffeology.DSmooth.contDiff`：∀ {X : Type u_1} [inst : DiffeologicalSpace
 X] {Y : Type u_2} [inst_1 : NormedAddCommGroup X] [inst_2 : NormedSpace ℝ X]   
[Diffeology.IsCon…
· 使用定理 `ContDiff.dSmooth`：∀ {X : Type u_1} [inst : DiffeologicalSpace X] {Y : Ty
pe u_2} [inst_1 : NormedAddCommGroup X] [inst_2 : NormedSpace ℝ X]   [Diffeology
.IsCon…
-/
theorem dSmooth_iff_contDiff [FiniteDimensional ℝ X] {f : X → Y} : DSmooth f ↔ ContDiff ℝ ∞ f :=
  ⟨DSmooth.contDiff, ContDiff.dSmooth⟩

end Diffeology

section CompleteLattice

namespace DiffeologicalSpace

open Diffeology

variable {X : Type*}

/-- The plots belonging to a diffeology, as a subset of
`(n : ℕ) × (EuclideanSpace ℝ (Fin n) → X)`. -/
/-
**DiffeologicalSpace.toPlots** 是 Mathlib 中的一个定义，位于命名空间 `DiffeologicalSpace`。
形式化陈述：toPlots (_ : DiffeologicalSpace X) : Set ((n : Nat) × (𝔼ⁿ -> X))
参数：_ : DiffeologicalSpace X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The plots belonging to a diffeology, as a subset of
`(n : ℕ) × (EuclideanSpace ℝ (Fin n) → X)`.
-/
def toPlots (_ : DiffeologicalSpace X) : Set ((n : ℕ) × (𝔼ⁿ → X)) :=
  {p | IsPlot p.2}
/-
**DiffeologicalSpace.injective_toPlots** 是 Mathlib 中的一个引理，位于命名空间 `DiffeologicalS
pace`。
形式化陈述：injective_toPlots : Function.Injective (@toPlots X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiffeologicalSpace.ext`：∀ {X : Type u_4} {d₁ d₂ : DiffeologicalSpace X},
 @Diffeology.IsPlot X d₁ = @Diffeology.IsPlot X d₂ → d₁ = d₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
-/
lemma injective_toPlots : Function.Injective (@toPlots X) := fun d d' h ↦ by
  ext n p; exact Set.ext_iff.1 h ⟨n, p⟩

/-- The diffeology generated by a set `g` of plots. -/
@[instance_reducible]
/-
**DiffeologicalSpace.generateFrom** 是 Mathlib 中的一个定义，位于命名空间 `DiffeologicalSpace`
。
形式化陈述：generateFrom (g : Set ((n : Nat) × (𝔼ⁿ -> X))) : DiffeologicalSpace X wher
e plots n
参数：g : Set ((n : Nat) × (𝔼ⁿ -> X))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diffeology generated by a set `g` of plots.
-/
def generateFrom (g : Set ((n : ℕ) × (𝔼ⁿ → X))) : DiffeologicalSpace X where
  plots n := {p | ∀ (d : DiffeologicalSpace X), g ⊆ d.toPlots → ⟨n, p⟩ ∈ d.toPlots}
  constant_plots {n} x := fun _ _ ↦ constant_plots x
  plot_reparam {n m p f} := fun hp hf d hd ↦ @d.plot_reparam n m p f (hp _ hd) hf
  locality {n p} := fun hp d hd ↦ @locality X d n p fun x ↦ by
    let ⟨u, hxu, hu, hu'⟩ := hp x
    exact ⟨u, hxu, hu, fun {m f} hfu hf ↦ (hu' hfu hf) _ hd⟩
/-
**DiffeologicalSpace.self_subset_toPlots_generateFrom** 是 Mathlib 中的一个引理，位于命名空间 
`DiffeologicalSpace`。
形式化陈述：self_subset_toPlots_generateFrom (g : Set ((n : Nat) × (𝔼ⁿ -> X))) : g sub
seteq (generateFrom g).toPlots
参数：g : Set ((n : Nat) × (𝔼ⁿ -> X))。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma self_subset_toPlots_generateFrom (g : Set ((n : ℕ) × (𝔼ⁿ → X))) :
    g ⊆ (generateFrom g).toPlots :=
  fun _ hd _ h ↦ h hd
/-
**DiffeologicalSpace.isPlot_generatedFrom_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Diff
eologicalSpace`。
形式化陈述：isPlot_generatedFrom_of_mem {g : Set ((n : Nat) × (𝔼ⁿ -> X))} {n : Nat} {p
 : 𝔼ⁿ -> X} (hp : ⟨n, p⟩ in g) : (@IsPlot _ (generateFrom g)) p
参数：(n : Nat) × (𝔼ⁿ -> X)；hp : ⟨n, p⟩ in g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DiffeologicalSpace.self_subset_toPlots_generateFrom`：self_subset_toPlots
_generateFrom (g : Set ((n : Nat) × (𝔼ⁿ -> X))) : g subseteq (generateFrom g).to
Plots
-/
lemma isPlot_generatedFrom_of_mem {g : Set ((n : ℕ) × (𝔼ⁿ → X))} {n : ℕ} {p : 𝔼ⁿ → X}
    (hp : ⟨n, p⟩ ∈ g) : (@IsPlot _ (generateFrom g)) p :=
  self_subset_toPlots_generateFrom g hp
/-
**DiffeologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `DiffeologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (DiffeologicalSpace X) := PartialOrder.lift _ injective_toPlots
/-
**DiffeologicalSpace.le_def** 是 Mathlib 中的一个引理，位于命名空间 `DiffeologicalSpace`。
形式化陈述：le_def {d₁ d₂ : DiffeologicalSpace X} : d₁ <= d₂ ↔ d₁.toPlots subseteq d₂.
toPlots
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def {d₁ d₂ : DiffeologicalSpace X} : d₁ ≤ d₂ ↔ d₁.toPlots ⊆ d₂.toPlots := Iff.rfl
/-
**DiffeologicalSpace.le_iff** 是 Mathlib 中的一个引理，位于命名空间 `DiffeologicalSpace`。
形式化陈述：le_iff {d₁ d₂ : DiffeologicalSpace X} : d₁ <= d₂ ↔ forall n, d₁.plots n su
bseteq d₂.plots n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `DiffeologicalSpace.le_def`：le_def {d₁ d₂ : DiffeologicalSpace X} : d₁ <=
 d₂ ↔ d₁.toPlots subseteq d₂.toPlots
-/
lemma le_iff {d₁ d₂ : DiffeologicalSpace X} : d₁ ≤ d₂ ↔ ∀ n, d₁.plots n ⊆ d₂.plots n :=
  le_def.trans ⟨fun h n p h' ↦ (h h' : ⟨n, p⟩ ∈ d₂.toPlots), fun h _ hp ↦ h _ hp⟩
/-
**DiffeologicalSpace.le_iff'** 是 Mathlib 中的一个引理，位于命名空间 `DiffeologicalSpace`。
形式化陈述：le_iff' {d₁ d₂ : DiffeologicalSpace X} : d₁ <= d₂ ↔ forall n (p : 𝔼ⁿ -> X)
, (@IsPlot _ d₁) p -> (@IsPlot _ d₂) p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DiffeologicalSpace.le_iff`：le_iff {d₁ d₂ : DiffeologicalSpace X} : d₁ <=
 d₂ ↔ forall n, d₁.plots n subseteq d₂.plots n
-/
lemma le_iff' {d₁ d₂ : DiffeologicalSpace X} : d₁ ≤ d₂ ↔
    ∀ n (p : 𝔼ⁿ → X), (@IsPlot _ d₁) p → (@IsPlot _ d₂) p := le_iff
/-
**DiffeologicalSpace.generateFrom_le_iff_subset_toPlots** 是 Mathlib 中的一个引理，位于命名空
间 `DiffeologicalSpace`。
形式化陈述：generateFrom_le_iff_subset_toPlots {g : Set ((n : Nat) × (𝔼ⁿ -> X))} {d : 
DiffeologicalSpace X} : generateFrom g <= d ↔ g subseteq d.toPlots
参数：(n : Nat) × (𝔼ⁿ -> X)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `DiffeologicalSpace.self_subset_toPlots_generateFrom`：self_subset_toPlots
_generateFrom (g : Set ((n : Nat) × (𝔼ⁿ -> X))) : g subseteq (generateFrom g).to
Plots
-/
lemma generateFrom_le_iff_subset_toPlots {g : Set ((n : ℕ) × (𝔼ⁿ → X))}
    {d : DiffeologicalSpace X} : generateFrom g ≤ d ↔ g ⊆ d.toPlots :=
  ⟨fun h ↦ (self_subset_toPlots_generateFrom g).trans h, fun h _ hp ↦ hp _ h⟩

/-- Version of `generateFrom_le_iff_subset_toPlots` that is stated in terms of `IsPlot` instead
of `toPlots`. -/
/-
**DiffeologicalSpace.generateFrom_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Diffeologica
lSpace`。
形式化陈述：generateFrom_le_iff {g : Set ((n : Nat) × (𝔼ⁿ -> X))} {d : DiffeologicalSp
ace X} : generateFrom g <= d ↔ forall n (p : 𝔼ⁿ -> X), ⟨n, p⟩ in g -> (@IsPlot _
 d) p
参数：(n : Nat) × (𝔼ⁿ -> X)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `DiffeologicalSpace.generateFrom_le_iff_subset_toPlots`：generateFrom_le_i
ff_subset_toPlots {g : Set ((n : Nat) × (𝔼ⁿ -> X))} {d : DiffeologicalSpace X} :
 generateFrom g <= d ↔ g subseteq d.toPlots

--- 原说明 ---
Version of `generateFrom_le_iff_subset_toPlots` that is stated in terms of `IsPl
ot` instead
of `toPlots`.
-/
lemma generateFrom_le_iff {g : Set ((n : ℕ) × (𝔼ⁿ → X))} {d : DiffeologicalSpace X} :
    generateFrom g ≤ d ↔ ∀ n (p : 𝔼ⁿ → X), ⟨n, p⟩ ∈ g → (@IsPlot _ d) p :=
  generateFrom_le_iff_subset_toPlots.trans ⟨fun h _ _ hp ↦ h hp, fun h _ hp ↦ h _ _ hp⟩

/-- The diffeology defined by `g`. Same as `generateFrom g`, except that its set of plots is
definitionally equal to `g`. -/
@[instance_reducible]
/-
**DiffeologicalSpace.mkOfClosure** 是 Mathlib 中的一个定义，位于命名空间 `DiffeologicalSpace`。
形式化陈述：{X : Type u_1} →   (g : Set ((n : ℕ) × (EuclideanSpace ℝ (Fin n) → X))) → 
    (DiffeologicalSpace.generateFrom g).toPlots = g → DiffeologicalSpace X
参数：g : Set ((n : ℕ) × (EuclideanSpace ℝ (Fin n) → X))；DiffeologicalSpace.generat
eFrom g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diffeology defined by `g`. Same as `generateFrom g`, except that its set of 
plots is
definitionally equal to `g`.
-/
protected def mkOfClosure (g : Set ((n : ℕ) × (𝔼ⁿ → X))) (hg : (generateFrom g).toPlots = g) :
    DiffeologicalSpace X where
  plots n := {p | ⟨n, p⟩ ∈ g}
  constant_plots := hg ▸ (generateFrom g).constant_plots
  plot_reparam := hg ▸ (generateFrom g).plot_reparam
  locality := hg ▸ (generateFrom g).locality

@[simp]
/-
**DiffeologicalSpace.mkOfClosure_eq_generateFrom** 是 Mathlib 中的一个引理，位于命名空间 `Diff
eologicalSpace`。
形式化陈述：mkOfClosure_eq_generateFrom {g : Set ((n : Nat) × (𝔼ⁿ -> X))} {hg : (gener
ateFrom g).toPlots = g} : DiffeologicalSpace.mkOfClosure g hg = generateFrom g
参数：(n : Nat) × (𝔼ⁿ -> X)；generateFrom g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DiffeologicalSpace.injective_toPlots`：injective_toPlots : Function.Injec
tive (@toPlots X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mkOfClosure_eq_generateFrom {g : Set ((n : ℕ) × (𝔼ⁿ → X))}
    {hg : (generateFrom g).toPlots = g} : DiffeologicalSpace.mkOfClosure g hg = generateFrom g :=
  injective_toPlots hg.symm
/-
**DiffeologicalSpace.gc_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `DiffeologicalSpa
ce`。
形式化陈述：gc_generateFrom (X : Type*) : GaloisConnection generateFrom (@toPlots X)
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DiffeologicalSpace.generateFrom_le_iff_subset_toPlots`：generateFrom_le_i
ff_subset_toPlots {g : Set ((n : Nat) × (𝔼ⁿ -> X))} {d : DiffeologicalSpace X} :
 generateFrom g <= d ↔ g subseteq d.toPlots
-/
theorem gc_generateFrom (X : Type*) : GaloisConnection generateFrom (@toPlots X) :=
  @generateFrom_le_iff_subset_toPlots X

/-- The Galois insertion between `DiffeologicalSpace X` and
`Set ((n : ℕ) × (EuclideanSpace ℝ (Fin n) → X))` whose lower part sends a collection of plots in `X`
to the diffeology they generate, and whose upper part sends a diffeology to its collection of plots.
-/
/-
**DiffeologicalSpace.giGenerateFrom** 是 Mathlib 中的一个定义，位于命名空间 `DiffeologicalSpac
e`。
形式化陈述：giGenerateFrom (X : Type*) : GaloisInsertion generateFrom (@toPlots X) whe
re gc
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DiffeologicalSpace.gc_generateFrom`：gc_generateFrom (X : Type*) : Galois
Connection generateFrom (@toPlots X)

--- 原说明 ---
The Galois insertion between `DiffeologicalSpace X` and
`Set ((n : ℕ) × (EuclideanSpace ℝ (Fin n) → X))` whose lower part sends a collec
tion of plots in `X`
to the diffeology they generate, and whose upper part sends a diffeology to its 
collection of plots.
-/
def giGenerateFrom (X : Type*) : GaloisInsertion generateFrom (@toPlots X) where
  gc := gc_generateFrom X
  le_l_u := fun _ ↦ le_def.2 (self_subset_toPlots_generateFrom _)
  choice g hg := DiffeologicalSpace.mkOfClosure g (hg.antisymm (self_subset_toPlots_generateFrom g))
  choice_eq _ _ := mkOfClosure_eq_generateFrom
/-
**DiffeologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `DiffeologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (DiffeologicalSpace X) := (giGenerateFrom X).liftCompleteLattice

@[gcongr, mono]
/-
**DiffeologicalSpace.generateFrom_mono** 是 Mathlib 中的一个定理，位于命名空间 `DiffeologicalS
pace`。
形式化陈述：generateFrom_mono {g₁ g₂ : Set ((n : Nat) × (𝔼ⁿ -> X))} (h : g₁ subseteq g
₂) : generateFrom g₁ <= generateFrom g₂
参数：(n : Nat) × (𝔼ⁿ -> X)；h : g₁ subseteq g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `DiffeologicalSpace.gc_generateFrom`：gc_generateFrom (X : Type*) : Galois
Connection generateFrom (@toPlots X)
-/
theorem generateFrom_mono {g₁ g₂ : Set ((n : ℕ) × (𝔼ⁿ → X))} (h : g₁ ⊆ g₂) :
    generateFrom g₁ ≤ generateFrom g₂ :=
  (gc_generateFrom _).monotone_l h
/-
**DiffeologicalSpace.generateFrom_toPlots** 是 Mathlib 中的一个定理，位于命名空间 `Diffeologic
alSpace`。
形式化陈述：generateFrom_toPlots (d : DiffeologicalSpace X) : generateFrom d.toPlots =
 d
参数：d : DiffeologicalSpace X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
-/
theorem generateFrom_toPlots (d : DiffeologicalSpace X) :
    generateFrom d.toPlots = d :=
  (giGenerateFrom X).l_u_eq d
/-
**DiffeologicalSpace.leftInverse_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `Diffeol
ogicalSpace`。
形式化陈述：leftInverse_generateFrom : Function.LeftInverse generateFrom (@toPlots X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.leftInverse_l_u`：leftInverse_l_u [Preorder α] [PartialOr
der β] (gi : GaloisInsertion l u) : LeftInverse l u
-/
theorem leftInverse_generateFrom :
    Function.LeftInverse generateFrom (@toPlots X) :=
  (giGenerateFrom X).leftInverse_l_u
/-
**DiffeologicalSpace.generateFrom_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Diffeolo
gicalSpace`。
形式化陈述：generateFrom_surjective : Function.Surjective (@generateFrom X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_surjective`：l_surjective [Preorder α] [PartialOrder β]
 (gi : GaloisInsertion l u) : Surjective l
-/
theorem generateFrom_surjective : Function.Surjective (@generateFrom X) :=
  (giGenerateFrom X).l_surjective
/-
**DiffeologicalSpace.generateFrom_union** 是 Mathlib 中的一个定理，位于命名空间 `Diffeological
Space`。
形式化陈述：generateFrom_union (g₁ g₂ : Set ((n : Nat) × (𝔼ⁿ -> X))) : generateFrom (g
₁ union g₂) = generateFrom g₁ ⊔ generateFrom g₂
参数：g₁ g₂ : Set ((n : Nat) × (𝔼ⁿ -> X))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `DiffeologicalSpace.gc_generateFrom`：gc_generateFrom (X : Type*) : Galois
Connection generateFrom (@toPlots X)
-/
theorem generateFrom_union (g₁ g₂ : Set ((n : ℕ) × (𝔼ⁿ → X))) :
    generateFrom (g₁ ∪ g₂) = generateFrom g₁ ⊔ generateFrom g₂ :=
  (gc_generateFrom X).l_sup
/-
**DiffeologicalSpace.generateFrom_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Diffeologica
lSpace`。
形式化陈述：generateFrom_iUnion {ι : Type*} {g : ι -> Set ((n : Nat) × (𝔼ⁿ -> X))} : g
enerateFrom (⋃ i, g i) = ⨆ i, generateFrom (g i)
参数：(n : Nat) × (𝔼ⁿ -> X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `DiffeologicalSpace.gc_generateFrom`：gc_generateFrom (X : Type*) : Galois
Connection generateFrom (@toPlots X)
-/
theorem generateFrom_iUnion {ι : Type*} {g : ι → Set ((n : ℕ) × (𝔼ⁿ → X))} :
    generateFrom (⋃ i, g i) = ⨆ i, generateFrom (g i) :=
  (gc_generateFrom X).l_iSup
/-
**DiffeologicalSpace.generateFrom_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Diffeologica
lSpace`。
形式化陈述：generateFrom_sUnion {G : Set (Set ((n : Nat) × (𝔼ⁿ -> X)))} : generateFrom
 (⋃₀ G) = ⨆ s in G, generateFrom s
参数：Set ((n : Nat) × (𝔼ⁿ -> X))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用定理 `DiffeologicalSpace.gc_generateFrom`：gc_generateFrom (X : Type*) : Galois
Connection generateFrom (@toPlots X)
-/
theorem generateFrom_sUnion {G : Set (Set ((n : ℕ) × (𝔼ⁿ → X)))} :
    generateFrom (⋃₀ G) = ⨆ s ∈ G, generateFrom s :=
  (gc_generateFrom X).l_sSup
/-
**DiffeologicalSpace.toPlots_inf** 是 Mathlib 中的一个定理，位于命名空间 `DiffeologicalSpace`。
形式化陈述：toPlots_inf (d₁ d₂ : DiffeologicalSpace X) : (d₁ ⊓ d₂).toPlots = d₁.toPlot
s inter d₂.toPlots
参数：d₁ d₂ : DiffeologicalSpace X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPlots_inf (d₁ d₂ : DiffeologicalSpace X) :
    (d₁ ⊓ d₂).toPlots = d₁.toPlots ∩ d₂.toPlots := rfl
/-
**DiffeologicalSpace.toPlots_iInf** 是 Mathlib 中的一个定理，位于命名空间 `DiffeologicalSpace`
。
形式化陈述：toPlots_iInf {ι : Type*} {D : ι -> DiffeologicalSpace X} : (⨅ i, D i).toPl
ots = ⋂ i, (D i).toPlots
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `DiffeologicalSpace.gc_generateFrom`：gc_generateFrom (X : Type*) : Galois
Connection generateFrom (@toPlots X)
-/
theorem toPlots_iInf {ι : Type*} {D : ι → DiffeologicalSpace X} :
    (⨅ i, D i).toPlots = ⋂ i, (D i).toPlots :=
  (gc_generateFrom X).u_iInf
/-
**DiffeologicalSpace.toPlots_sInf** 是 Mathlib 中的一个定理，位于命名空间 `DiffeologicalSpace`
。
形式化陈述：toPlots_sInf {D : Set (DiffeologicalSpace X)} : (sInf D).toPlots = ⋂ d in 
D, d.toPlots
参数：DiffeologicalSpace X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_sInf`：∀ {α : Type u} {β : Type v} [inst : CompleteLat
tice α] [inst_1 : CompleteLattice β] {u : α → β} {l : β → α},   GaloisConnection
 l u → ∀ {s :…
· 使用定理 `DiffeologicalSpace.gc_generateFrom`：gc_generateFrom (X : Type*) : Galois
Connection generateFrom (@toPlots X)
-/
theorem toPlots_sInf {D : Set (DiffeologicalSpace X)} : (sInf D).toPlots = ⋂ d ∈ D, d.toPlots :=
  (gc_generateFrom X).u_sInf
/-
**DiffeologicalSpace.generateFrom_union_toPlots** 是 Mathlib 中的一个定理，位于命名空间 `Diffe
ologicalSpace`。
形式化陈述：generateFrom_union_toPlots (d₁ d₂ : DiffeologicalSpace X) : generateFrom (
d₁.toPlots union d₂.toPlots) = d₁ ⊔ d₂
参数：d₁ d₂ : DiffeologicalSpace X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_sup_u`：l_sup_u [SemilatticeSup α] [SemilatticeSup β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊔ u b) = a ⊔ b
-/
theorem generateFrom_union_toPlots (d₁ d₂ : DiffeologicalSpace X) :
    generateFrom (d₁.toPlots ∪ d₂.toPlots) = d₁ ⊔ d₂ :=
  (giGenerateFrom X).l_sup_u _ _
/-
**DiffeologicalSpace.generateFrom_iUnion_toPlots** 是 Mathlib 中的一个定理，位于命名空间 `Diff
eologicalSpace`。
形式化陈述：generateFrom_iUnion_toPlots {ι : Type*} (D : ι -> DiffeologicalSpace X) : 
generateFrom (⋃ i, (D i).toPlots) = ⨆ i, D i
参数：D : ι -> DiffeologicalSpace X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iSup_u`：l_iSup_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨆ i, u (f i)) = ⨆ i
, f i
-/
theorem generateFrom_iUnion_toPlots {ι : Type*} (D : ι → DiffeologicalSpace X) :
    generateFrom (⋃ i, (D i).toPlots) = ⨆ i, D i :=
  (giGenerateFrom X).l_iSup_u _
/-
**DiffeologicalSpace.generateFrom_inter_toPlots** 是 Mathlib 中的一个定理，位于命名空间 `Diffe
ologicalSpace`。
形式化陈述：generateFrom_inter_toPlots (d₁ d₂ : DiffeologicalSpace X) : generateFrom (
d₁.toPlots inter d₂.toPlots) = d₁ ⊓ d₂
参数：d₁ d₂ : DiffeologicalSpace X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_inf_u`：l_inf_u [SemilatticeInf α] [SemilatticeInf β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊓ u b) = a ⊓ b
-/
theorem generateFrom_inter_toPlots (d₁ d₂ : DiffeologicalSpace X) :
    generateFrom (d₁.toPlots ∩ d₂.toPlots) = d₁ ⊓ d₂ :=
  (giGenerateFrom X).l_inf_u _ _
/-
**DiffeologicalSpace.generateFrom_iInter_toPlots** 是 Mathlib 中的一个定理，位于命名空间 `Diff
eologicalSpace`。
形式化陈述：generateFrom_iInter_toPlots {ι : Type*} (D : ι -> DiffeologicalSpace X) : 
generateFrom (⋂ i, (D i).toPlots) = ⨅ i, D i
参数：D : ι -> DiffeologicalSpace X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iInf_u`：l_iInf_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨅ i, u (f i)) = ⨅ i
, f i
-/
theorem generateFrom_iInter_toPlots {ι : Type*} (D : ι → DiffeologicalSpace X) :
    generateFrom (⋂ i, (D i).toPlots) = ⨅ i, D i :=
  (giGenerateFrom X).l_iInf_u _
/-
**DiffeologicalSpace.generateFrom_iInter_of_generateFrom_eq_self** 是 Mathlib 中的一
个定理，位于命名空间 `DiffeologicalSpace`。
形式化陈述：generateFrom_iInter_of_generateFrom_eq_self {ι : Type*} (G : ι -> Set ((n 
: Nat) × (𝔼ⁿ -> X))) (hG : forall i, (generateFrom (G i)).toPlots = G i) : gener
ateFrom (⋂ i, G i) = ⨅ i, generateFrom (G i)
参数：G : ι -> Set ((n : Nat) × (𝔼ⁿ -> X))；hG : forall i, (generateFrom (G i)).toPl
ots = G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iInf_of_u_l_eq_self`：l_iInf_of_u_l_eq_self [CompleteLa
ttice α] [CompleteLattice β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> α
) (hf : forall i, u (l (f i…
-/
theorem generateFrom_iInter_of_generateFrom_eq_self {ι : Type*}
    (G : ι → Set ((n : ℕ) × (𝔼ⁿ → X)))
    (hG : ∀ i, (generateFrom (G i)).toPlots = G i) :
    generateFrom (⋂ i, G i) = ⨅ i, generateFrom (G i) :=
  (giGenerateFrom X).l_iInf_of_u_l_eq_self G hG
/-
**DiffeologicalSpace.isPlot_inf_iff** 是 Mathlib 中的一个定理，位于命名空间 `DiffeologicalSpac
e`。
形式化陈述：isPlot_inf_iff {d₁ d₂ : DiffeologicalSpace X} {n : Nat} {p : 𝔼ⁿ -> X} : (@
IsPlot _ (d₁ ⊓ d₂)) p ↔ (@IsPlot _ d₁) p ∧ (@IsPlot _ d₂) p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `DiffeologicalSpace.toPlots_inf`：toPlots_inf (d₁ d₂ : DiffeologicalSpace 
X) : (d₁ ⊓ d₂).toPlots = d₁.toPlots inter d₂.toPlots
-/
theorem isPlot_inf_iff {d₁ d₂ : DiffeologicalSpace X} {n : ℕ} {p : 𝔼ⁿ → X} :
    (@IsPlot _ (d₁ ⊓ d₂)) p ↔ (@IsPlot _ d₁) p ∧ (@IsPlot _ d₂) p :=
  Set.ext_iff.1 (toPlots_inf d₁ d₂) ⟨n, p⟩
/-
**DiffeologicalSpace.isPlot_iInf_iff** 是 Mathlib 中的一个定理，位于命名空间 `DiffeologicalSpa
ce`。
形式化陈述：isPlot_iInf_iff {ι : Type*} {D : ι -> DiffeologicalSpace X} {n : Nat} {p :
 𝔼ⁿ -> X} : (@IsPlot _ (⨅ i, D i)) p ↔ forall i, (@IsPlot _ (D i)) p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `DiffeologicalSpace.toPlots_iInf`：toPlots_iInf {ι : Type*} {D : ι -> Diff
eologicalSpace X} : (⨅ i, D i).toPlots = ⋂ i, (D i).toPlots
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
theorem isPlot_iInf_iff {ι : Type*} {D : ι → DiffeologicalSpace X} {n : ℕ} {p : 𝔼ⁿ → X} :
    (@IsPlot _ (⨅ i, D i)) p ↔ ∀ i, (@IsPlot _ (D i)) p :=
  (Set.ext_iff.1 (toPlots_iInf (D := D)) ⟨n, p⟩).trans Set.mem_iInter
/-
**DiffeologicalSpace.isPlot_sInf_iff** 是 Mathlib 中的一个定理，位于命名空间 `DiffeologicalSpa
ce`。
形式化陈述：isPlot_sInf_iff {D : Set (DiffeologicalSpace X)} {n : Nat} {p : 𝔼ⁿ -> X} :
 (@IsPlot _ (sInf D)) p ↔ forall d in D, (@IsPlot _ d) p
参数：DiffeologicalSpace X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `DiffeologicalSpace.toPlots_sInf`：toPlots_sInf {D : Set (DiffeologicalSpa
ce X)} : (sInf D).toPlots = ⋂ d in D, d.toPlots
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem isPlot_sInf_iff {D : Set (DiffeologicalSpace X)} {n : ℕ} {p : 𝔼ⁿ → X} :
    (@IsPlot _ (sInf D)) p ↔ ∀ d ∈ D, (@IsPlot _ d) p :=
  (Set.ext_iff.1 (toPlots_sInf (D := D)) ⟨n, p⟩).trans Set.mem_iInter₂

end DiffeologicalSpace

end CompleteLattice

