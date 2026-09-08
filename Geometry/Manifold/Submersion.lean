/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Samantha Naranjo Guevara
-/
module

public import Mathlib.Geometry.Manifold.LocalSourceTargetProperty
public import Mathlib.Analysis.Normed.Module.Shrink
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Notation

/-! # Smooth submersions

In this file, we define `C^n` submersions between `C^n` manifolds.
As in the case of immersions, the correct definition in the infinite-dimensional setting differs
from the classical finite-dimensional one (which is usually phrased in terms of surjectivity of the
`mfderiv`). Future work will prove that our definition implies the latter, and that both are
equivalent for finite-dimensional manifolds.

Our definition is formulated in terms of local normal forms; i.e., a map `f` is a submersion at `x`
if there exist charts near `x` and `f x` in which `f` looks like the standard projection
`(u, v) ↦ u`. The results in this file follow from abstract results about such local properties.

## Main definitions

* `IsSubmersionAtOfComplement F I J n f x` means a map `f : M → N` between `C^n` manifolds `M` and
  `N` is a submersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `(u, v) ↦ u`, w.r.t. some equivalence
  `E ≃L[𝕜] (E'' × F)`. Differentiability of `f` is not assumed as it follows from this definition.
* `IsSubmersionAt I J n f x` means that `f` is a `C^n` submersion at `x : M` for some choice of a
  complement `F` of the model normed space `E` of `M` in the model normed space `E''` of `N`.
* `IsSubmersionOfComplement F I J n f` means `f : M → N` is a submersion at every point `x : M`,
  w.r.t. the chosen complement `F`.
* `IsSubmersion I J n f` means `f : M → N` is a submersion at every point `x : M`,
  w.r.t. some global choice of complement.

## Main results

* `IsSubmersionAt.congr_of_eventuallyEq`: being a submersion is a local property.
  If `f` and `g` agree near `x` and `f` is a submersion at `x`, then so is `g`.
* `IsSubmersionAtOfComplement.congr_F`, `IsSubmersionOfComplement.congr_F`:
  being a submersion at `x` w.r.t. `F` is stable under
  replacing the complement `F` by an isomorphic copy.
* `isOpen_isSubmersionAtOfComplement` and `isOpen_isSubmersionAt`:
  the set of points where `IsSubmersionAt(OfComplement)` holds is open.
* `IsSubmersionAt.prodMap` and `IsSubmersion.prodMap`: the product of two submersions (at a point)
  is a submersion (at the product point).
* `IsSubmersionAt.contMDiffAt`: if `f` is a submersion at `x`, it is `C^n` at `x`.
* `IsSubmersion.contMDiff`: if `f` is a submersion, it is automatically `C^n`
  in the sense of `ContMDiff`.

## Implementation notes

The implementation strategy is identical to the one for immersions. See the implementation notes in
`Mathlib/Geometry/Manifold/Immersion` for details on:
* `IsSubmersionAt(OfComplement)`,
* universe level issues for complements,
* `small` and `smallEquiv` constructions.

## TODO
* The converse to `IsSubmersionAtOfComplement.congr_F` also holds: any two complements are
  isomorphic, as they are isomorphic to the kernel of the differential `mfderiv I J f x`.
* If `f` is a submersion at `x`, its differential `mfderiv I J f x` admits a continuous right
  inverse, in particular is surjective.
* If `f : M → N` is a map between Banach manifolds, `mfderiv I J f x` having a continuous right
  inverse implies `f` is a submersion at `x`. (This requires the inverse function theorem.)
* `IsSubmersionAt.comp`: if `f : M → N` and `g: N → N'` are maps between Banach manifolds such that
  `f` is a submersion at `x : M` and `g` is a submersion at `f x`, then `g ∘ f` is a submersion
  at `x`.
* `IsSubmersion.comp`: the composition of submersions is a submersion
* If `f : M → N` is a map between finite-dimensional manifolds, `mfderiv I J f x` being surjective
  implies `f` is a submersion at `x`.
* `IsLocalDiffeomorphAt.isSubmersionAt` and `IsLocalDiffeomorph.isSubmersion`:
  a local diffeomorphism (at `x`) is a submersion (at `x`)
* `Diffeomorph.isSubmersion`: in particular, a diffeomorphism is a submersion

## References

* [Alexander Schmeding, *An introduction to infinite-dimensional differential geometry*]
  [schmeding2023]
* Note that Margelef-Roig and Dominguez have a slightly different definition of submersions.

**Please talk** to Michael Rothgang before working on this file, to avoid duplicate work.
The above TODOs are the topic of Samantha Naranjo's master's thesis; it's nicer to coordinate.

-/

public noncomputable section

open scoped Topology ContDiff Manifold
open OpenPartialHomeomorph Function Set

namespace Manifold

universe u
-- We manually name the universe of `E` as `IsSubmersionAt` will use it.

variable {𝕜 E' E'' E''' F F' H H' G G' : Type*} {E : Type u} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M M' N N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}

variable (F I J M N) in
/-- The local property of being a submersion at a point: `f : M → N` is a submersion at `x` if
there exist charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively, such that in these
charts, `f` looks like the projection `(u, v) ↦ u`.
This definition has a fixed parameter `F`, which is a choice of complement of `E''` in the model
normed space `E` of `M`: being a submersion at `x` includes a choice of linear isomorphism
between `E'' × F` and `E`. -/
/-
**Manifold.SubmersionAtProp** 是 Mathlib 中的一个定义，位于命名空间 `Manifold`。
形式化陈述：SubmersionAtProp : (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHom
eomorph N G -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The local property of being a submersion at a point: `f : M → N` is a submersion
 at `x` if
there exist charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
, such that in these
charts, `f` looks like the projection `(u, v) ↦ u`.
This definition has a fixed parameter `F`, which is a choice of complement of `E
''` in the model
normed space `E` of `M`: being a submersion at `x` includes a choice of linear i
somorphism
between `E'' × F` and `E`.
-/
def SubmersionAtProp :
    (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop :=
  fun f domChart codChart ↦ ∃ equiv : E ≃L[𝕜] (E'' × F),
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- Being a submersion at `x` is a local property. -/
/-
**Manifold.isLocalSourceTargetProperty_submmersionAtProp** 是 Mathlib 中的一个引理，位于命名
空间 `Manifold`。
形式化陈述：isLocalSourceTargetProperty_submmersionAtProp : IsLocalSourceTargetPropert
y (SubmersionAtProp F I J M N) where mono_source {f φ ψ s} hs
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.EqOn.trans`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ f₃ : 
α → β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Being a submersion at `x` is a local property.
-/
lemma isLocalSourceTargetProperty_submmersionAtProp :
    IsLocalSourceTargetProperty (SubmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs := fun ⟨equiv, hf⟩ ↦ ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx ↦ ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x ∈ φ.source := by simp_all
    grind

variable (F I J n) in
/-- `f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u, v) ↦ u`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

This definition has a fixed parameter `F`, which is a choice of complement of `E''` in `E`:
being an submersion at `x` includes a choice of linear isomorphism between `E'' × F` and `E`.
While the particular choice of complement is often not important, choosing a complement is useful
in some settings, such as proving that embedded submanifolds are locally given either by an
immersion or a submersion.
Unless you have a particular reason, prefer to use `IsSubmersionAt` instead.
-/
/-
**Manifold.IsSubmersionAtOfComplement** 是 Mathlib 中的一个定义，位于命名空间 `Manifold`。
形式化陈述：IsSubmersionAtOfComplement (f : M -> N) (x : M) : Prop
参数：f : M -> N；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` 
and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u
, v) ↦ u`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ
` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficien
t.

This definition has a fixed parameter `F`, which is a choice of complement of `E
''` in `E`:
being an submersion at `x` includes a choice of linear isomorphism between `E'' 
× F` and `E`.
While the particular choice of complement is often not important, choosing a com
plement is useful
in some settings, such as proving that embedded submanifolds are locally given e
ither by an
immersion or a submersion.
Unless you have a particular reason, prefer to use `IsSubmersionAt` instead.
-/
def IsSubmersionAtOfComplement (f : M → N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp F I J M N)

-- Lift the universe from `E`, to avoid a free universe parameter.

variable (I J n) in
/-- `f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u, v) ↦ u`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

Implicit in this definition is an abstract choice `F` of a complement of `E''` in `E`: being
a submersion at `x` includes a choice of linear isomorphism between `E` and `E'' × F`, which is
where the choice of `F` enters.
If you need stronger control over the complement `F`, use `IsSubmersionAtOfComplement` instead.
-/
/-
**Manifold.IsSubmersionAt** 是 Mathlib 中的一个定义，位于命名空间 `Manifold`。
形式化陈述：IsSubmersionAt (f : M -> N) (x : M) : Prop
参数：f : M -> N；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` 
and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u
, v) ↦ u`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ
` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficien
t.

Implicit in this definition is an abstract choice `F` of a complement of `E''` i
n `E`: being
a submersion at `x` includes a choice of linear isomorphism between `E` and `E''
 × F`, which is
where the choice of `F` enters.
If you need stronger control over the complement `F`, use `IsSubmersionAtOfCompl
ement` instead.
-/
def IsSubmersionAt (f : M → N) (x : M) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionAtOfComplement F I J n f x

variable {f g : M → N} {x : M}

namespace IsSubmersionAtOfComplement

/-
**Manifold.IsSubmersionAtOfComplement.mk_of_charts** 是 Mathlib 中的一个引理，位于命名空间 `Ma
nifold.IsSubmersionAtOfComplement`。
形式化陈述：mk_of_charts (equiv : E ≃L[𝕜] (E'' × F)) (domChart : OpenPartialHomeomorph
 M H) (codChart : OpenPartialHomeomorph N G) (hx : x in domChart.source) (hfx : 
f x in codChart.source) (hdomChart : domChart in IsManifold.maximalAtlas I n M) 
(hcodChart : codChart in IsManifold.maximalAtlas J n N) (hsource : domChart.sour
ce subseteq f ⁻¹' codChart.source) (hwrittenInExtend : EqOn ((codChart.extend J)
 ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv) (domChart.extend I).target) 
: IsSubmersionAtOfCompleme
参数：equiv : E ≃L[𝕜] (E'' × F)；domChart : OpenPartialHomeomorph M H；codChart : Ope
nPartialHomeomorph N G；hx : x in domChart.source；hfx : f x in codChart.source；hd
omChart : domChart in IsManifold.maximalAtlas I n M；hcodChart : codChart in IsMa
nifold.maximalAtlas J n N；hsource : domChart.source subseteq f ⁻¹' codChart.sour
ce；hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) 
(Prod.fst ∘ equiv) (domChart.extend I).target。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_of_charts (equiv : E ≃L[𝕜] (E'' × F)) (domChart : OpenPartialHomeomorph M H)
    (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAtOfComplement F I J n f x := by
  use domChart, codChart
  use equiv

/-- `f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u,v) ↦ u`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
/-
**Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt** 是 Mathlib 中的一个引理，位于命名
空间 `Manifold.IsSubmersionAtOfComplement`。
形式化陈述：mk_of_continuousAt {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : E
 ≃L[𝕜] (E'' × F)) (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartial
Homeomorph N G) (hx : x in domChart.source) (hfx : f x in codChart.source) (hdom
Chart : domChart in IsManifold.maximalAtlas I n M) (hcodChart : codChart in IsMa
nifold.maximalAtlas J n N) (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (
domChart.extend I).symm) (Prod.fst ∘ equiv) (domChart.extend I).target) : IsSubm
ersionAtOfComplement F I J
参数：hf : ContinuousAt f x；equiv : E ≃L[𝕜] (E'' × F)；domChart : OpenPartialHomeomo
rph M H；codChart : OpenPartialHomeomorph N G；hx : x in domChart.source；hfx : f x
 in codChart.source；hdomChart : domChart in IsManifold.maximalAtlas I n M；hcodCh
art : codChart in IsManifold.maximalAtlas J n N；hwrittenInExtend : EqOn ((codCha
rt.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv) (domChart.extend
 I).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.mk_of_continuousAt`：mk_of_continuous
At (hf : ContinuousAt f x) (hP : IsLocalSourceTargetProperty P) (domChart : Open
PartialHomeomorph M H) (codChart : OpenParti…
· 使用引理 `Manifold.isLocalSourceTargetProperty_submmersionAtProp`：isLocalSourceTar
getProperty_submmersionAtProp : IsLocalSourceTargetProperty (SubmersionAtProp F 
I J M N) where mono_source {f φ ψ s} hs

--- 原说明 ---
`f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` 
and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u
,v) ↦ u`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`.
-/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAtOfComplement F I J n f x :=
      LiftSourceTargetPropertyAt.mk_of_continuousAt hf
    isLocalSourceTargetProperty_submmersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

/-- A choice of chart on the domain `M` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like a projection `(u,v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
/-
**Manifold.IsSubmersionAtOfComplement.domChart** 是 Mathlib 中的一个定义，位于命名空间 `Manifo
ld.IsSubmersionAtOfComplement`。
形式化陈述：domChart (h : IsSubmersionAtOfComplement F I J n f x) : OpenPartialHomeomo
rph M H
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of chart on the domain `M` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like a projection `(u,v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given b
y
`h.codChart` and `h.codChart`.
-/
def domChart (h : IsSubmersionAtOfComplement F I J n f x) :
    OpenPartialHomeomorph M H :=
  LiftSourceTargetPropertyAt.domChart h

/-- A choice of chart on the codomain `N` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like a projection `(u, v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
/-
**Manifold.IsSubmersionAtOfComplement.codChart** 是 Mathlib 中的一个定义，位于命名空间 `Manifo
ld.IsSubmersionAtOfComplement`。
形式化陈述：codChart (h : IsSubmersionAtOfComplement F I J n f x) : OpenPartialHomeomo
rph N G
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of chart on the codomain `N` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like a projection `(u, v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given b
y
`h.equiv` and `h.domChart`.
-/
def codChart (h : IsSubmersionAtOfComplement F I J n f x) :
    OpenPartialHomeomorph N G :=
  LiftSourceTargetPropertyAt.codChart h
/-
**Manifold.IsSubmersionAtOfComplement.mem_domChart_source** 是 Mathlib 中的一个引理，位于命
名空间 `Manifold.IsSubmersionAtOfComplement`。
形式化陈述：mem_domChart_source (h : IsSubmersionAtOfComplement F I J n f x) : x in h.
domChart.source
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.mem_domChart_source`：mem_domChart_so
urce (h : LiftSourceTargetPropertyAt I J n f x P) : x in h.domChart.source
-/
lemma mem_domChart_source (h : IsSubmersionAtOfComplement F I J n f x) : x ∈ h.domChart.source :=
  LiftSourceTargetPropertyAt.mem_domChart_source h
/-
**Manifold.IsSubmersionAtOfComplement.mem_codChart_source** 是 Mathlib 中的一个引理，位于命
名空间 `Manifold.IsSubmersionAtOfComplement`。
形式化陈述：mem_codChart_source (h : IsSubmersionAtOfComplement F I J n f x) : f x in 
h.codChart.source
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.mem_codChart_source`：mem_codChart_so
urce (h : LiftSourceTargetPropertyAt I J n f x P) : f x in h.codChart.source
-/
lemma mem_codChart_source (h : IsSubmersionAtOfComplement F I J n f x) : f x ∈ h.codChart.source :=
  LiftSourceTargetPropertyAt.mem_codChart_source h
/-
**Manifold.IsSubmersionAtOfComplement.domChart_mem_maximalAtlas** 是 Mathlib 中的一个
引理，位于命名空间 `Manifold.IsSubmersionAtOfComplement`。
形式化陈述：domChart_mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) : h
.domChart in IsManifold.maximalAtlas I n M
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas`：domChart_
mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) : h.domChart in Is
Manifold.maximalAtlas I n M
-/
lemma domChart_mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h
/-
**Manifold.IsSubmersionAtOfComplement.codChart_mem_maximalAtlas** 是 Mathlib 中的一个
引理，位于命名空间 `Manifold.IsSubmersionAtOfComplement`。
形式化陈述：codChart_mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) : h
.codChart in IsManifold.maximalAtlas J n N
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas`：codChart_
mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) : h.codChart in Is
Manifold.maximalAtlas J n N
-/
lemma codChart_mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) :
    h.codChart ∈ IsManifold.maximalAtlas J n N :=
  LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h
/-
**Manifold.IsSubmersionAtOfComplement.source_subset_preimage_source** 是 Mathlib 
中的一个引理，位于命名空间 `Manifold.IsSubmersionAtOfComplement`。
形式化陈述：source_subset_preimage_source (h : IsSubmersionAtOfComplement F I J n f x)
 : h.domChart.source subseteq f ⁻¹' h.codChart.source
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.source_subset_preimage_source`：sourc
e_subset_preimage_source (h : LiftSourceTargetPropertyAt I J n f x P) : h.domCha
rt.source subseteq f ⁻¹' h.codChart.source
-/
lemma source_subset_preimage_source (h : IsSubmersionAtOfComplement F I J n f x) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source :=
  LiftSourceTargetPropertyAt.source_subset_preimage_source h
/-
**Manifold.IsSubmersionAtOfComplement.mapsto_domChart_source_codChart_source** 是
 Mathlib 中的一个引理，位于命名空间 `Manifold.IsSubmersionAtOfComplement`。
形式化陈述：mapsto_domChart_source_codChart_source (h : IsSubmersionAtOfComplement F I
 J n f x) : MapsTo f h.domChart.source h.codChart.source
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.source_subset_preimage_source`：sourc
e_subset_preimage_source (h : IsSubmersionAtOfComplement F I J n f x) : h.domCha
rt.source subseteq f ⁻¹' h.codChart.source
-/
lemma mapsto_domChart_source_codChart_source (h : IsSubmersionAtOfComplement F I J n f x) :
    MapsTo f h.domChart.source h.codChart.source :=
  h.source_subset_preimage_source

/-- A linear equivalence `E ≃L[𝕜] E'' × F` which belongs to the data of a submersion `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
/-
**Manifold.IsSubmersionAtOfComplement.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.
IsSubmersionAtOfComplement`。
形式化陈述：equiv (h : IsSubmersionAtOfComplement F I J n f x) : E ≃L[𝕜] (E'' × F)
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence `E ≃L[𝕜] E'' × F` which belongs to the data of a submersion
 `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses g
iven by
`h.domChart` and `h.codChart`.
-/
def equiv (h : IsSubmersionAtOfComplement F I J n f x) : E ≃L[𝕜] (E'' × F) :=
  Classical.choose <| LiftSourceTargetPropertyAt.property h
/-
**Manifold.IsSubmersionAtOfComplement.writtenInCharts** 是 Mathlib 中的一个引理，位于命名空间 
`Manifold.IsSubmersionAtOfComplement`。
形式化陈述：writtenInCharts (h : IsSubmersionAtOfComplement F I J n f x) : EqOn ((h.co
dChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (Prod.fst ∘ h.equiv) (h.domCh
art.extend I).target
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.property`：property (h : LiftSourceTa
rgetPropertyAt I J n f x P) : P f h.domChart h.codChart
-/
lemma writtenInCharts (h : IsSubmersionAtOfComplement F I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (Prod.fst ∘ h.equiv)
      (h.domChart.extend I).target :=
  Classical.choose_spec <| LiftSourceTargetPropertyAt.property h
/-
**Manifold.IsSubmersionAtOfComplement.property** 是 Mathlib 中的一个引理，位于命名空间 `Manifo
ld.IsSubmersionAtOfComplement`。
形式化陈述：property (h : IsSubmersionAtOfComplement F I J n f x) : LiftSourceTargetPr
opertyAt I J n f x (SubmersionAtProp F I J M N)
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma property (h : IsSubmersionAtOfComplement F I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp F I J M N) := h

/-- If `f` is a submersion at `x`, it maps its domain chart's target to its codomain chart's target:
`(h.domChart.extend I).target` to `(h.domChart.extend J).target`.

See `target_subset_preimage_target` for a version stated using preimages instead of images.
-/
/-
**Manifold.IsSubmersionAtOfComplement.image_target_subset_target** 是 Mathlib 中的一
个引理，位于命名空间 `Manifold.IsSubmersionAtOfComplement`。
形式化陈述：image_target_subset_target (h : IsSubmersionAtOfComplement F I J n f x) : 
(Prod.fst ∘ h.equiv) '' (h.domChart.extend I).target subseteq (h.codChart.extend
 J).target
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用引理 `Manifold.IsSubmersionAtOfComplement.writtenInCharts`：writtenInCharts (h 
: IsSubmersionAtOfComplement F I J n f x) : EqOn ((h.codChart.extend J) ∘ f ∘ (h
.domChart.extend I).symm) (Prod.fst ∘ h.e…
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `PartialEquiv.symm_image_target_eq_source`：symm_image_target_eq_source : 
e.symm '' e.target = e.source
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Manifold.IsSubmersionAtOfComplement.source_subset_preimage_source`：sourc
e_subset_preimage_source (h : IsSubmersionAtOfComplement F I J n f x) : h.domCha
rt.source subseteq f ⁻¹' h.codChart.source
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If `f` is a submersion at `x`, it maps its domain chart's target to its codomain
 chart's target:
`(h.domChart.extend I).target` to `(h.domChart.extend J).target`.

See `target_subset_preimage_target` for a version stated using preimages instead
 of images.
-/
lemma image_target_subset_target (h : IsSubmersionAtOfComplement F I J n f x) :
    (Prod.fst ∘ h.equiv) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target := by
  rw [← h.writtenInCharts.image_eq, Set.image_comp, Set.image_comp,
    PartialEquiv.symm_image_target_eq_source, OpenPartialHomeomorph.extend_source,
    ← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source ⊆ h.codChart.source := by
    simp [h.source_subset_preimage_source]
  grw [this, OpenPartialHomeomorph.extend_source]

/-- If `f` is a submersion at `x`, its domain chart's target `(h.domChart.extend I).target`
is mapped to its codomain chart's target `(h.domChart.extend J).target`:
see `image_target_subset_target` for a version stated using images. -/
/-
**Manifold.IsSubmersionAtOfComplement.target_subset_preimage_target** 是 Mathlib 
中的一个引理，位于命名空间 `Manifold.IsSubmersionAtOfComplement`。
形式化陈述：target_subset_preimage_target (h : IsSubmersionAtOfComplement F I J n f x)
 : (h.domChart.extend I).target subseteq (Prod.fst ∘ h.equiv) ⁻¹' (h.codChart.ex
tend J).target
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.image_target_subset_target`：image_ta
rget_subset_target (h : IsSubmersionAtOfComplement F I J n f x) : (Prod.fst ∘ h.
equiv) '' (h.domChart.extend I).target subseteq (h.c…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
If `f` is a submersion at `x`, its domain chart's target `(h.domChart.extend I).
target`
is mapped to its codomain chart's target `(h.domChart.extend J).target`:
see `image_target_subset_target` for a version stated using images.
-/
lemma target_subset_preimage_target (h : IsSubmersionAtOfComplement F I J n f x) :
    (h.domChart.extend I).target ⊆ (Prod.fst ∘ h.equiv) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx ↦ h.image_target_subset_target (mem_image_of_mem _ hx)

/-- If `f` is a submersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is a submersion at `x`. -/
/-
**Manifold.IsSubmersionAtOfComplement.congr_of_eventuallyEq** 是 Mathlib 中的一个引理，位
于命名空间 `Manifold.IsSubmersionAtOfComplement`。
形式化陈述：congr_of_eventuallyEq (hf : IsSubmersionAtOfComplement F I J n f x) (hfg :
 f =ᶠ[𝓝 x] g) : IsSubmersionAtOfComplement F I J n g x
参数：hf : IsSubmersionAtOfComplement F I J n f x；hfg : f =ᶠ[𝓝 x] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.congr_of_eventuallyEq`：congr_of_even
tuallyEq (hP : IsLocalSourceTargetProperty P) (hf : LiftSourceTargetPropertyAt I
 J n f x P) (h' : f =ᶠ[nhds x] g) : LiftSourceT…
· 使用引理 `Manifold.isLocalSourceTargetProperty_submmersionAtProp`：isLocalSourceTar
getProperty_submmersionAtProp : IsLocalSourceTargetProperty (SubmersionAtProp F 
I J M N) where mono_source {f φ ψ s} hs
· 使用引理 `Manifold.IsSubmersionAtOfComplement.property`：property (h : IsSubmersion
AtOfComplement F I J n f x) : LiftSourceTargetPropertyAt I J n f x (SubmersionAt
Prop F I J M N)

--- 原说明 ---
If `f` is a submersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is a submersion at `x`.
-/
lemma congr_of_eventuallyEq (hf : IsSubmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAtOfComplement F I J n g x := by
  exact LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_submmersionAtProp hf.property hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is a submersion at `x` if and only if `g` is a submersion at `x`. -/
/-
**Manifold.IsSubmersionAtOfComplement.congr_iff_of_eventuallyEq** 是 Mathlib 中的一个
引理，位于命名空间 `Manifold.IsSubmersionAtOfComplement`。
形式化陈述：congr_iff_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) : IsSubmersionAtOfComplement
 F I J n f x ↔ IsSubmersionAtOfComplement F I J n g x
参数：hfg : f =ᶠ[𝓝 x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq`：congr_iff
_of_eventuallyEq (hP : IsLocalSourceTargetProperty P) (h' : f =ᶠ[nhds x] g) : Li
ftSourceTargetPropertyAt I J n f x P ↔ LiftSourceTa…
· 使用引理 `Manifold.isLocalSourceTargetProperty_submmersionAtProp`：isLocalSourceTar
getProperty_submmersionAtProp : IsLocalSourceTargetProperty (SubmersionAtProp F 
I J M N) where mono_source {f φ ψ s} hs

--- 原说明 ---
If `f = g` on some neighbourhood of `x`,
then `f` is a submersion at `x` if and only if `g` is a submersion at `x`.
-/
lemma congr_iff_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAtOfComplement F I J n f x ↔ IsSubmersionAtOfComplement F I J n g x :=
  LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
    isLocalSourceTargetProperty_submmersionAtProp hfg
/-
**Manifold.IsSubmersionAtOfComplement.small** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.
IsSubmersionAtOfComplement`。
形式化陈述：small (hf : IsSubmersionAtOfComplement F I J n f x) : Small.{u} F
参数：hf : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `ContinuousLinearEquiv.injective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst
 : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [in
st_2 : RingHomInvPair…
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
-/
lemma small (hf : IsSubmersionAtOfComplement F I J n f x) : Small.{u} F :=
  small_of_injective <| hf.equiv.symm.injective.comp (Prod.mk_right_injective 0)

/-- Given a submersion `f` at `x`, this is a choice of complement which lives in the same universe
as the model space for the domain of `f`: this is useful to avoid universe restrictions. -/
/-
**Manifold.IsSubmersionAtOfComplement.smallComplement** 是 Mathlib 中的一个定义，位于命名空间 
`Manifold.IsSubmersionAtOfComplement`。
形式化陈述：smallComplement (hf : IsSubmersionAtOfComplement F I J n f x) : Type u
参数：hf : IsSubmersionAtOfComplement F I J n f x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.small`：small (hf : IsSubmersionAtOfC
omplement F I J n f x) : Small.{u} F

--- 原说明 ---
Given a submersion `f` at `x`, this is a choice of complement which lives in the
 same universe
as the model space for the domain of `f`: this is useful to avoid universe restr
ictions.
-/
def smallComplement (hf : IsSubmersionAtOfComplement F I J n f x) : Type u :=
  haveI := hf.small
  Shrink.{u} F
/-
**Manifold.IsSubmersionAtOfComplement.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsSub
mersionAtOfComplement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hf : IsSubmersionAtOfComplement F I J n f x) : NormedAddCommGroup hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedAddCommGroup (Shrink F)
/-
**Manifold.IsSubmersionAtOfComplement.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsSub
mersionAtOfComplement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hf : IsSubmersionAtOfComplement F I J n f x) : NormedSpace 𝕜 hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedSpace 𝕜 (Shrink F)

/-- Given a submersion `f` at `x` w.r.t. a complement `F`, this construction provides
a continuous linear equivalence from `F` to the small complement of `F`:
mathematically, this is just the identity map; however, this is technically useful as it enables
us to always work with `hf.smallComplement`. -/
/-
**Manifold.IsSubmersionAtOfComplement.smallEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Mani
fold.IsSubmersionAtOfComplement`。
形式化陈述：smallEquiv (hf : IsSubmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smal
lComplement
参数：hf : IsSubmersionAtOfComplement F I J n f x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.small`：small (hf : IsSubmersionAtOfC
omplement F I J n f x) : Small.{u} F
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a submersion `f` at `x` w.r.t. a complement `F`, this construction provide
s
a continuous linear equivalence from `F` to the small complement of `F`:
mathematically, this is just the identity map; however, this is technically usef
ul as it enables
us to always work with `hf.smallComplement`.
-/
def smallEquiv (hf : IsSubmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement :=
  haveI := hf.small
  ((equivShrink F).symm.continuousLinearEquiv 𝕜).symm
/-
**Manifold.IsSubmersionAtOfComplement.trans_F** 是 Mathlib 中的一个引理，位于命名空间 `Manifol
d.IsSubmersionAtOfComplement`。
形式化陈述：trans_F (h : IsSubmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') : Is
SubmersionAtOfComplement F' I J n f x
参数：h : IsSubmersionAtOfComplement F I J n f x；e : F ≃L[𝕜] F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.mem_domChart_source`：mem_domChart_so
urce (h : IsSubmersionAtOfComplement F I J n f x) : x in h.domChart.source
· 使用引理 `Manifold.IsSubmersionAtOfComplement.mem_codChart_source`：mem_codChart_so
urce (h : IsSubmersionAtOfComplement F I J n f x) : f x in h.codChart.source
· 使用引理 `Manifold.IsSubmersionAtOfComplement.domChart_mem_maximalAtlas`：domChart_
mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) : h.domChart in Is
Manifold.maximalAtlas I n M
· 使用引理 `Manifold.IsSubmersionAtOfComplement.codChart_mem_maximalAtlas`：codChart_
mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) : h.codChart in Is
Manifold.maximalAtlas J n N
· 使用引理 `Manifold.IsSubmersionAtOfComplement.source_subset_preimage_source`：sourc
e_subset_preimage_source (h : IsSubmersionAtOfComplement F I J n f x) : h.domCha
rt.source subseteq f ⁻¹' h.codChart.source
· 使用定理 `Set.EqOn.trans`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ f₃ : 
α → β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s
· 使用引理 `Manifold.IsSubmersionAtOfComplement.writtenInCharts`：writtenInCharts (h 
: IsSubmersionAtOfComplement F I J n f x) : EqOn ((h.codChart.extend J) ∘ f ∘ (h
.domChart.extend I).symm) (Prod.fst ∘ h.e…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trans_F (h : IsSubmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') :
    IsSubmersionAtOfComplement F' I J n f x := by
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use h.equiv.trans ((ContinuousLinearEquiv.refl 𝕜 E'').prodCongr e)
  apply Set.EqOn.trans h.writtenInCharts
  intro x hx
  simp

/-- Being a submersion at `x` w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
/-
**Manifold.IsSubmersionAtOfComplement.congr_F** 是 Mathlib 中的一个引理，位于命名空间 `Manifol
d.IsSubmersionAtOfComplement`。
形式化陈述：congr_F (e : F ≃L[𝕜] F') : IsSubmersionAtOfComplement F I J n f x ↔ IsSubm
ersionAtOfComplement F' I J n f x
参数：e : F ≃L[𝕜] F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.trans_F`：trans_F (h : IsSubmersionAt
OfComplement F I J n f x) (e : F ≃L[𝕜] F') : IsSubmersionAtOfComplement F' I J n
 f x

--- 原说明 ---
Being a submersion at `x` w.r.t. `F` is stable under replacing `F` by an isomorp
hic copy.
-/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsSubmersionAtOfComplement F I J n f x ↔ IsSubmersionAtOfComplement F' I J n f x :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/- The set of points where `IsSubmersionAtOfComplement` holds is open. -/
/-
**Manifold.IsSubmersionAtOfComplement._root_.isOpen_isSubmersionAtOfComplement**
 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsSubmersionAtOfComplement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of points where `IsSubmersionAtOfComplement` holds is open.
-/
lemma _root_.isOpen_isSubmersionAtOfComplement :
    IsOpen {x | IsSubmersionAtOfComplement F I J n f x} := by
  exact IsOpen.liftSourceTargetPropertyAt

/-- If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × M' → N × N'` is a submersion at `(x, x')`. -/
/-
**Manifold.IsSubmersionAtOfComplement.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Manifol
d.IsSubmersionAtOfComplement`。
形式化陈述：prodMap {f : M -> N} {g : M' -> N'} {x' : M'} [IsManifold I n M] [IsManifo
ld I' n M'] [IsManifold J n N] [IsManifold J' n N'] (hf : IsSubmersionAtOfComple
ment F I J n f x) (hg : IsSubmersionAtOfComplement F' I' J' n g x') : IsSubmersi
onAtOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x')
参数：hf : IsSubmersionAtOfComplement F I J n f x；hg : IsSubmersionAtOfComplement F
' I' J' n g x'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.prodMap`：prodMap [IsManifold I n M] 
[IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N'] {Q : (M' -> N') -> 
OpenPartialHomeomorph M' H' -> Op…
· 使用引理 `Manifold.IsSubmersionAtOfComplement.property`：property (h : IsSubmersion
AtOfComplement F I J n f x) : LiftSourceTargetPropertyAt I J n f x (SubmersionAt
Prop F I J M N)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OpenPartialHomeomorph.extend_prod`：extend_prod (f' : OpenPartialHomeomor
ph M' H') : (f.prod f').extend (I.prod I') = (f.extend I).prod (f'.extend I')
· 使用定理 `PartialEquiv.prod_target`：prod_target (e : PartialEquiv α β) (e' : Parti
alEquiv γ δ) : (e.prod e').target = e.target ×ˢ e'.target
· 使用引理 `Set.eqOn_prod_iff`：eqOn_prod_iff {a b : α -> γ × δ} : EqOn a b s ↔ EqOn 
(Prod.fst ∘ a) (Prod.fst ∘ b) s ∧ EqOn (Prod.snd ∘ a) (Prod.snd ∘ b) s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.prod_symm`：prod_symm (e : PartialEquiv α β) (e' : PartialEq
uiv γ δ) : (e.prod e').symm = e.symm.prod e'.symm
· 使用定理 `Equiv.prodProdProdComm_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type
 u_11) (δ : Type u_12) (abcd : (α × β) × γ × δ),   (Equiv.prodProdProdComm α β γ
 δ) abcd = ((abcd.…

--- 原说明 ---
If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × M' → N × N'` is a submersion at `(x, x')`.
-/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersionAtOfComplement F I J n f x)
    (hg : IsSubmersionAtOfComplement F' I' J' n g x') :
    IsSubmersionAtOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (equiv₁.prodCongr equiv₂).trans (ContinuousLinearEquiv.prodProdProdComm 𝕜 E'' F E''' F')
  rw [φ₁.extend_prod φ₂, ψ₁.extend_prod, PartialEquiv.prod_target, eqOn_prod_iff]
  exact ⟨fun x ⟨hx, hx'⟩ ↦ by simpa using hfprop hx, fun x ⟨hx, hx'⟩ ↦ by simpa using hgprop hx'⟩

/-- If `f` is a submersion at `x` w.r.t. some complement `F`, it is a submersion at `x`.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being a submersion at `x` requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`. -/
/-
**Manifold.IsSubmersionAtOfComplement.isSubmersionAt** 是 Mathlib 中的一个引理，位于命名空间 `
Manifold.IsSubmersionAtOfComplement`。
形式化陈述：isSubmersionAt (h : IsSubmersionAtOfComplement F I J n f x) : IsSubmersion
At I J n f x
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Manifold.IsSubmersionAtOfComplement.congr_F`：congr_F (e : F ≃L[𝕜] F') : 
IsSubmersionAtOfComplement F I J n f x ↔ IsSubmersionAtOfComplement F' I J n f x

--- 原说明 ---
If `f` is a submersion at `x` w.r.t. some complement `F`, it is a submersion at 
`x`.

Note that the proof contains a small formalisation-related subtlety: `F` can liv
e in any universe,
while being a submersion at `x` requires the existence of a complement in the sa
me universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEqu
iv`.
-/
lemma isSubmersionAt (h : IsSubmersionAtOfComplement F I J n f x) :
    IsSubmersionAt I J n f x := by
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionAtOfComplement.congr_F h.smallEquiv).mp h

/-- If `f` is a `C^n` submersion at `x`, then `f` is `C^n` on its domain chart's source,
in particular on an open neighbourhood of `x`.

Prefer using `IsSubmersionAtOfComplement.contMDiffAt` instead. -/
/-
**Manifold.IsSubmersionAtOfComplement.contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 `Man
ifold.IsSubmersionAtOfComplement`。
形式化陈述：contMDiffOn (h : IsSubmersionAtOfComplement F I J n f x) : ContMDiffOn I J
 n f h.domChart.source
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff`：OpenPartialHomeom
orph.contMDiffOn_writtenInExtend_iff (hφ : φ in maximalAtlas I n M) (hψ : ψ in m
aximalAtlas J n N) (hs : s subseteq φ.sourc…
· 使用引理 `Manifold.IsSubmersionAtOfComplement.domChart_mem_maximalAtlas`：domChart_
mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) : h.domChart in Is
Manifold.maximalAtlas I n M
· 使用引理 `Manifold.IsSubmersionAtOfComplement.codChart_mem_maximalAtlas`：codChart_
mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) : h.codChart in Is
Manifold.maximalAtlas J n N
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Manifold.IsSubmersionAtOfComplement.mapsto_domChart_source_codChart_sour
ce`：mapsto_domChart_source_codChart_source (h : IsSubmersionAtOfComplement F I J
 n f x) : MapsTo f h.domChart.source h.codChart.source
· 使用定理 `OpenPartialHomeomorph.extend_target_eq_image_source`：extend_target_eq_im
age_source : (f.extend I).target = (f.extend I) '' f.source
· 使用定理 `contMDiff_iff_contDiff`：contMDiff_iff_contDiff {f : E -> E'} : ContMDiff
 𝓘(𝕜, E) 𝓘(𝕜, E') n f ↔ ContDiff 𝕜 n f
· 使用定理 `ContDiff.fst`：ContDiff.fst {f : E -> F × G} (hf : ContDiff 𝕜 n f) : Cont
Diff 𝕜 n fun x => (f x).1
· 使用定理 `ContinuousLinearEquiv.contDiff`：ContinuousLinearEquiv.contDiff (f : E ≃L
[𝕜] F) : ContDiff 𝕜 n f
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用引理 `Manifold.IsSubmersionAtOfComplement.writtenInCharts`：writtenInCharts (h 
: IsSubmersionAtOfComplement F I J n f x) : EqOn ((h.codChart.extend J) ∘ f ∘ (h
.domChart.extend I).symm) (Prod.fst ∘ h.e…

--- 原说明 ---
If `f` is a `C^n` submersion at `x`, then `f` is `C^n` on its domain chart's sou
rce,
in particular on an open neighbourhood of `x`.

Prefer using `IsSubmersionAtOfComplement.contMDiffAt` instead.
-/
theorem contMDiffOn (h : IsSubmersionAtOfComplement F I J n f x) :
    ContMDiffOn I J n f h.domChart.source := by
  rw [← contMDiffOn_writtenInExtend_iff h.domChart_mem_maximalAtlas
    h.codChart_mem_maximalAtlas le_rfl h.mapsto_domChart_source_codChart_source,
    ← h.domChart.extend_target_eq_image_source]
  have : CMDiff n (Prod.fst ∘ h.equiv) := by rw [contMDiff_iff_contDiff]; fun_prop
  exact this.contMDiffOn.congr h.writtenInCharts

/-- A `C^n` submersion at `x` is `C^n` at `x`. -/
/-
**Manifold.IsSubmersionAtOfComplement.contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 `Man
ifold.IsSubmersionAtOfComplement`。
形式化陈述：contMDiffAt (h : IsSubmersionAtOfComplement F I J n f x) : CMDiffAt n f x
参数：h : IsSubmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `Manifold.IsSubmersionAtOfComplement.contMDiffOn`：contMDiffOn (h : IsSubm
ersionAtOfComplement F I J n f x) : ContMDiffOn I J n f h.domChart.source
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用引理 `Manifold.IsSubmersionAtOfComplement.mem_domChart_source`：mem_domChart_so
urce (h : IsSubmersionAtOfComplement F I J n f x) : x in h.domChart.source

--- 原说明 ---
A `C^n` submersion at `x` is `C^n` at `x`.
-/
theorem contMDiffAt (h : IsSubmersionAtOfComplement F I J n f x) : CMDiffAt n f x :=
  h.contMDiffOn.contMDiffAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

end IsSubmersionAtOfComplement

namespace IsSubmersionAt

/-
**Manifold.IsSubmersionAt.mk_of_charts** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsSub
mersionAt`。
形式化陈述：mk_of_charts (equiv : E ≃L[𝕜] (E'' × F)) (domChart : OpenPartialHomeomorph
 M H) (codChart : OpenPartialHomeomorph N G) (hx : x in domChart.source) (hfx : 
f x in codChart.source) (hdomChart : domChart in IsManifold.maximalAtlas I n M) 
(hcodChart : codChart in IsManifold.maximalAtlas J n N) (hsource : domChart.sour
ce subseteq f ⁻¹' codChart.source) (hwrittenInExtend : EqOn ((codChart.extend J)
 ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv) (domChart.extend I).target) 
: IsSubmersionAt I J n f x
参数：equiv : E ≃L[𝕜] (E'' × F)；domChart : OpenPartialHomeomorph M H；codChart : Ope
nPartialHomeomorph N G；hx : x in domChart.source；hfx : f x in codChart.source；hd
omChart : domChart in IsManifold.maximalAtlas I n M；hcodChart : codChart in IsMa
nifold.maximalAtlas J n N；hsource : domChart.source subseteq f ⁻¹' codChart.sour
ce；hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) 
(Prod.fst ∘ equiv) (domChart.extend I).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.mk_of_charts`：mk_of_charts (equiv : 
E ≃L[𝕜] (E'' × F)) (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartia
lHomeomorph N G) (hx : x in domChart.s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Manifold.IsSubmersionAtOfComplement.congr_F`：congr_F (e : F ≃L[𝕜] F') : 
IsSubmersionAtOfComplement F I J n f x ↔ IsSubmersionAtOfComplement F' I J n f x
-/
lemma mk_of_charts (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAt I J n f x := by
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

/-- `f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u, v) ↦ u`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
/-
**Manifold.IsSubmersionAt.mk_of_continuousAt** 是 Mathlib 中的一个引理，位于命名空间 `Manifold
.IsSubmersionAt`。
形式化陈述：mk_of_continuousAt {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : E
 ≃L[𝕜] (E'' × F)) (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartial
Homeomorph N G) (hx : x in domChart.source) (hfx : f x in codChart.source) (hdom
Chart : domChart in IsManifold.maximalAtlas I n M) (hcodChart : codChart in IsMa
nifold.maximalAtlas J n N) (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (
domChart.extend I).symm) (Prod.fst ∘ equiv) (domChart.extend I).target) : IsSubm
ersionAt I J n f x
参数：hf : ContinuousAt f x；equiv : E ≃L[𝕜] (E'' × F)；domChart : OpenPartialHomeomo
rph M H；codChart : OpenPartialHomeomorph N G；hx : x in domChart.source；hfx : f x
 in codChart.source；hdomChart : domChart in IsManifold.maximalAtlas I n M；hcodCh
art : codChart in IsManifold.maximalAtlas J n N；hwrittenInExtend : EqOn ((codCha
rt.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv) (domChart.extend
 I).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt`：mk_of_continuous
At {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F)) (dom
Chart : OpenPartialHomeomorph M H) (codChart…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Manifold.IsSubmersionAtOfComplement.congr_F`：congr_F (e : F ≃L[𝕜] F') : 
IsSubmersionAtOfComplement F I J n f x ↔ IsSubmersionAtOfComplement F' I J n f x

--- 原说明 ---
`f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` 
and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u
, v) ↦ u`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`.
-/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAt I J n f x := by
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
/-
**Manifold.IsSubmersionAt.complement** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.IsSubme
rsionAt`。
形式化陈述：complement (h : IsSubmersionAt I J n f x) : Type u
参数：h : IsSubmersionAt I J n f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of complement of the model normed space `E` of `M` in the model normed 
space
`E'` of `N`
-/
def complement (h : IsSubmersionAt I J n f x) : Type u := Classical.choose h
/-
**Manifold.IsSubmersionAt.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsSubmersionAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance (h : IsSubmersionAt I J n f x) : NormedAddCommGroup h.complement :=
  Classical.choose (Classical.choose_spec h)
/-
**Manifold.IsSubmersionAt.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsSubmersionAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance (h : IsSubmersionAt I J n f x) : NormedSpace 𝕜 h.complement :=
  Classical.choose <| Classical.choose_spec <| Classical.choose_spec h
/-
**Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement** 是 Mathlib 中的一个
引理，位于命名空间 `Manifold.IsSubmersionAt`。
形式化陈述：isSubmersionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsS
ubmersionAtOfComplement h.complement I J n f x
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma isSubmersionAtOfComplement_complement (h : IsSubmersionAt I J n f x) :
    IsSubmersionAtOfComplement h.complement I J n f x :=
  Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

/-- A choice of chart on the domain `M` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like a projection `(u, v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
/-
**Manifold.IsSubmersionAt.domChart** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.IsSubmers
ionAt`。
形式化陈述：domChart (h : IsSubmersionAt I J n f x) : OpenPartialHomeomorph M H
参数：h : IsSubmersionAt I J n f x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x

--- 原说明 ---
A choice of chart on the domain `M` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like a projection `(u, v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given b
y
`h.codChart` and `h.codChart`.
-/
def domChart (h : IsSubmersionAt I J n f x) : OpenPartialHomeomorph M H :=
  h.isSubmersionAtOfComplement_complement.domChart

/-- A choice of chart on the co-domain `N` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like a projection `(u, v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
/-
**Manifold.IsSubmersionAt.codChart** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.IsSubmers
ionAt`。
形式化陈述：codChart (h : IsSubmersionAt I J n f x) : OpenPartialHomeomorph N G
参数：h : IsSubmersionAt I J n f x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x

--- 原说明 ---
A choice of chart on the co-domain `N` of a submersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like a projection `(u, v) ↦ u` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given b
y
`h.equiv` and `h.domChart`.
-/
def codChart (h : IsSubmersionAt I J n f x) : OpenPartialHomeomorph N G :=
  h.isSubmersionAtOfComplement_complement.codChart
/-
**Manifold.IsSubmersionAt.mem_domChart_source** 是 Mathlib 中的一个引理，位于命名空间 `Manifol
d.IsSubmersionAt`。
形式化陈述：mem_domChart_source (h : IsSubmersionAt I J n f x) : x in h.domChart.sourc
e
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.mem_domChart_source`：mem_domChart_so
urce (h : IsSubmersionAtOfComplement F I J n f x) : x in h.domChart.source
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x
-/
lemma mem_domChart_source (h : IsSubmersionAt I J n f x) : x ∈ h.domChart.source :=
  h.isSubmersionAtOfComplement_complement.mem_domChart_source
/-
**Manifold.IsSubmersionAt.mem_codChart_source** 是 Mathlib 中的一个引理，位于命名空间 `Manifol
d.IsSubmersionAt`。
形式化陈述：mem_codChart_source (h : IsSubmersionAt I J n f x) : f x in h.codChart.sou
rce
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.mem_codChart_source`：mem_codChart_so
urce (h : IsSubmersionAtOfComplement F I J n f x) : f x in h.codChart.source
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x
-/
lemma mem_codChart_source (h : IsSubmersionAt I J n f x) : f x ∈ h.codChart.source :=
  h.isSubmersionAtOfComplement_complement.mem_codChart_source
/-
**Manifold.IsSubmersionAt.domChart_mem_maximalAtlas** 是 Mathlib 中的一个引理，位于命名空间 `M
anifold.IsSubmersionAt`。
形式化陈述：domChart_mem_maximalAtlas (h : IsSubmersionAt I J n f x) : h.domChart in I
sManifold.maximalAtlas I n M
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.domChart_mem_maximalAtlas`：domChart_
mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) : h.domChart in Is
Manifold.maximalAtlas I n M
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x
-/
lemma domChart_mem_maximalAtlas (h : IsSubmersionAt I J n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  h.isSubmersionAtOfComplement_complement.domChart_mem_maximalAtlas
/-
**Manifold.IsSubmersionAt.codChart_mem_maximalAtlas** 是 Mathlib 中的一个引理，位于命名空间 `M
anifold.IsSubmersionAt`。
形式化陈述：codChart_mem_maximalAtlas (h : IsSubmersionAt I J n f x) : h.codChart in I
sManifold.maximalAtlas J n N
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.codChart_mem_maximalAtlas`：codChart_
mem_maximalAtlas (h : IsSubmersionAtOfComplement F I J n f x) : h.codChart in Is
Manifold.maximalAtlas J n N
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x
-/
lemma codChart_mem_maximalAtlas (h : IsSubmersionAt I J n f x) :
    h.codChart ∈ IsManifold.maximalAtlas J n N :=
  h.isSubmersionAtOfComplement_complement.codChart_mem_maximalAtlas
/-
**Manifold.IsSubmersionAt.source_subset_preimage_source** 是 Mathlib 中的一个引理，位于命名空
间 `Manifold.IsSubmersionAt`。
形式化陈述：source_subset_preimage_source (h : IsSubmersionAt I J n f x) : h.domChart.
source subseteq f ⁻¹' h.codChart.source
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.source_subset_preimage_source`：sourc
e_subset_preimage_source (h : IsSubmersionAtOfComplement F I J n f x) : h.domCha
rt.source subseteq f ⁻¹' h.codChart.source
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x
-/
lemma source_subset_preimage_source (h : IsSubmersionAt I J n f x) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source :=
  h.isSubmersionAtOfComplement_complement.source_subset_preimage_source

/-- A linear equivalence `E ≃L[𝕜] (E'' × F)` which belongs to the data of a submersion `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
/-
**Manifold.IsSubmersionAt.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.IsSubmersion
At`。
形式化陈述：equiv (h : IsSubmersionAt I J n f x) : E ≃L[𝕜] (E'' × h.complement)
参数：h : IsSubmersionAt I J n f x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x

--- 原说明 ---
A linear equivalence `E ≃L[𝕜] (E'' × F)` which belongs to the data of a submersi
on `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses g
iven by
`h.domChart` and `h.codChart`.
-/
def equiv (h : IsSubmersionAt I J n f x) : E ≃L[𝕜] (E'' × h.complement) :=
  h.isSubmersionAtOfComplement_complement.equiv
/-
**Manifold.IsSubmersionAt.writtenInCharts** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.Is
SubmersionAt`。
形式化陈述：writtenInCharts (h : IsSubmersionAt I J n f x) : EqOn ((h.codChart.extend 
J) ∘ f ∘ (h.domChart.extend I).symm) (Prod.fst ∘ h.equiv) (h.domChart.extend I).
target
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.writtenInCharts`：writtenInCharts (h 
: IsSubmersionAtOfComplement F I J n f x) : EqOn ((h.codChart.extend J) ∘ f ∘ (h
.domChart.extend I).symm) (Prod.fst ∘ h.e…
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x
-/
lemma writtenInCharts (h : IsSubmersionAt I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (Prod.fst ∘ h.equiv)
      (h.domChart.extend I).target :=
  h.isSubmersionAtOfComplement_complement.writtenInCharts
/-
**Manifold.IsSubmersionAt.property** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsSubmers
ionAt`。
形式化陈述：property (h : IsSubmersionAt I J n f x) : LiftSourceTargetPropertyAt I J n
 f x (SubmersionAtProp h.complement I J M N)
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.property`：property (h : IsSubmersion
AtOfComplement F I J n f x) : LiftSourceTargetPropertyAt I J n f x (SubmersionAt
Prop F I J M N)
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x
-/
lemma property (h : IsSubmersionAt I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp h.complement I J M N) :=
  h.isSubmersionAtOfComplement_complement.property

/-- If `f` is a submersion at `x`, it maps its domain chart's target to its codomain chart's target:
`(h.domChart.extend I).target` to `(h.domChart.extend J).target`. -/
/-
**Manifold.IsSubmersionAt.image_target_subset_target** 是 Mathlib 中的一个引理，位于命名空间 `
Manifold.IsSubmersionAt`。
形式化陈述：image_target_subset_target (h : IsSubmersionAt I J n f x) : (Prod.fst ∘ h.
equiv) '' (h.domChart.extend I).target subseteq (h.codChart.extend J).target
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.image_target_subset_target`：image_ta
rget_subset_target (h : IsSubmersionAtOfComplement F I J n f x) : (Prod.fst ∘ h.
equiv) '' (h.domChart.extend I).target subseteq (h.c…
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x

--- 原说明 ---
If `f` is a submersion at `x`, it maps its domain chart's target to its codomain
 chart's target:
`(h.domChart.extend I).target` to `(h.domChart.extend J).target`.
-/
lemma image_target_subset_target (h : IsSubmersionAt I J n f x) :
    (Prod.fst ∘ h.equiv) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target :=
  h.isSubmersionAtOfComplement_complement.image_target_subset_target

/-- If `f` is a submersion at `x`, its domain chart's target `(h.domChart.extend I).target`
is mapped to it codomain chart's target `(h.domChart.extend J).target`:
see `image_target_subset_target` for a version stated using images. -/
/-
**Manifold.IsSubmersionAt.target_subset_preimage_target** 是 Mathlib 中的一个引理，位于命名空
间 `Manifold.IsSubmersionAt`。
形式化陈述：target_subset_preimage_target (h : IsSubmersionAt I J n f x) : (h.domChart
.extend I).target subseteq (Prod.fst ∘ h.equiv) ⁻¹' (h.codChart.extend J).target
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAt.image_target_subset_target`：image_target_subset_
target (h : IsSubmersionAt I J n f x) : (Prod.fst ∘ h.equiv) '' (h.domChart.exte
nd I).target subseteq (h.codChart.extend…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
If `f` is a submersion at `x`, its domain chart's target `(h.domChart.extend I).
target`
is mapped to it codomain chart's target `(h.domChart.extend J).target`:
see `image_target_subset_target` for a version stated using images.
-/
lemma target_subset_preimage_target (h : IsSubmersionAt I J n f x) :
    (h.domChart.extend I).target ⊆ (Prod.fst ∘ h.equiv) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx ↦ h.image_target_subset_target (mem_image_of_mem _ hx)

/-- If `f` is a submersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is a submersion at `x`. -/
/-
**Manifold.IsSubmersionAt.congr_of_eventuallyEq** 是 Mathlib 中的一个引理，位于命名空间 `Manif
old.IsSubmersionAt`。
形式化陈述：congr_of_eventuallyEq (hf : IsSubmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) 
: IsSubmersionAt I J n g x
参数：hf : IsSubmersionAt I J n f x；hfg : f =ᶠ[𝓝 x] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.congr_of_eventuallyEq`：congr_of_even
tuallyEq (hf : IsSubmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) : IsS
ubmersionAtOfComplement F I J n g x
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x

--- 原说明 ---
If `f` is a submersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is a submersion at `x`.
-/
lemma congr_of_eventuallyEq (hf : IsSubmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAt I J n g x := by
  use hf.complement, by infer_instance, by infer_instance
  exact hf.isSubmersionAtOfComplement_complement.congr_of_eventuallyEq hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is a submersion at `x` if and only if `g` is a submersion at `x`. -/
/-
**Manifold.IsSubmersionAt.congr_iff** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsSubmer
sionAt`。
形式化陈述：congr_iff (hfg : f =ᶠ[𝓝 x] g) : IsSubmersionAt I J n f x ↔ IsSubmersionAt 
I J n g x
参数：hfg : f =ᶠ[𝓝 x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAt.congr_of_eventuallyEq`：congr_of_eventuallyEq (hf
 : IsSubmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) : IsSubmersionAt I J n g x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If `f = g` on some neighbourhood of `x`,
then `f` is a submersion at `x` if and only if `g` is a submersion at `x`.
-/
lemma congr_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAt I J n f x ↔ IsSubmersionAt I J n g x :=
  ⟨fun h ↦ h.congr_of_eventuallyEq hfg, fun h ↦ h.congr_of_eventuallyEq hfg.symm⟩

/- The set of points where `IsSubmersionAt` holds is open. -/
/-
**Manifold.IsSubmersionAt._root_.isOpen_isSubmersionAt** 是 Mathlib 中的一个引理，位于命名空间
 `Manifold.IsSubmersionAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of points where `IsSubmersionAt` holds is open.
-/
lemma _root_.isOpen_isSubmersionAt :
    IsOpen {x | IsSubmersionAt I J n f x} := by
  rw [isOpen_iff_forall_mem_open]
  exact fun x hx ↦ ⟨{x | IsSubmersionAtOfComplement hx.complement I J n f x },
    fun y hy ↦ hy.isSubmersionAt,
    isOpen_isSubmersionAtOfComplement, by simp [hx.isSubmersionAtOfComplement_complement]⟩

/-- If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × M' → N × N'` is a submersion at `(x, x')`. -/
/-
**Manifold.IsSubmersionAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsSubmersi
onAt`。
形式化陈述：prodMap {f : M -> N} {g : M' -> N'} {x' : M'} [IsManifold I n M] [IsManifo
ld I' n M'] [IsManifold J n N] [IsManifold J' n N'] (hf : IsSubmersionAt I J n f
 x) (hg : IsSubmersionAt I' J' n g x') : IsSubmersionAt (I.prod I') (J.prod J') 
n (Prod.map f g) (x, x')
参数：hf : IsSubmersionAt I J n f x；hg : IsSubmersionAt I' J' n g x'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.isSubmersionAt`：isSubmersionAt (h : 
IsSubmersionAtOfComplement F I J n f x) : IsSubmersionAt I J n f x
· 使用定理 `Manifold.IsSubmersionAtOfComplement.prodMap`：prodMap {f : M -> N} {g : M
' -> N'} {x' : M'} [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [I
sManifold J' n N'] (hf : IsSubmer…
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x

--- 原说明 ---
If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × M' → N × N'` is a submersion at `(x, x')`.
-/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersionAt I J n f x) (hg : IsSubmersionAt I' J' n g x') :
    IsSubmersionAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') :=
  hf.isSubmersionAtOfComplement_complement.prodMap hg.isSubmersionAtOfComplement_complement
    |>.isSubmersionAt

/-- If `f` is a submersion at `x`, then `f` is `C^n` on its domain chart's source,
in particular on an open neighbourhood of `x`.`

Prefer using `IsSubmersionAt.contMDiffAt` instead -/
/-
**Manifold.IsSubmersionAt.contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsSubm
ersionAt`。
形式化陈述：contMDiffOn (h : IsSubmersionAt I J n f x) : CMDiff[h.domChart.source] n f
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsSubmersionAtOfComplement.contMDiffOn`：contMDiffOn (h : IsSubm
ersionAtOfComplement F I J n f x) : ContMDiffOn I J n f h.domChart.source
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x

--- 原说明 ---
If `f` is a submersion at `x`, then `f` is `C^n` on its domain chart's source,
in particular on an open neighbourhood of `x`.`

Prefer using `IsSubmersionAt.contMDiffAt` instead
-/
theorem contMDiffOn (h : IsSubmersionAt I J n f x) : CMDiff[h.domChart.source] n f :=
  h.isSubmersionAtOfComplement_complement.contMDiffOn

/-- A `C^n` submersion at `x` is `C^n` at `x`. -/
/-
**Manifold.IsSubmersionAt.contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsSubm
ersionAt`。
形式化陈述：contMDiffAt (h : IsSubmersionAt I J n f x) : CMDiffAt n f x
参数：h : IsSubmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsSubmersionAtOfComplement.contMDiffAt`：contMDiffAt (h : IsSubm
ersionAtOfComplement F I J n f x) : CMDiffAt n f x
· 使用引理 `Manifold.IsSubmersionAt.isSubmersionAtOfComplement_complement`：isSubmers
ionAtOfComplement_complement (h : IsSubmersionAt I J n f x) : IsSubmersionAtOfCo
mplement h.complement I J n f x

--- 原说明 ---
A `C^n` submersion at `x` is `C^n` at `x`.
-/
theorem contMDiffAt (h : IsSubmersionAt I J n f x) : CMDiffAt n f x :=
  h.isSubmersionAtOfComplement_complement.contMDiffAt

end IsSubmersionAt

variable (F I J n) in
/-- `f : M → N` is a `C^n` submersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `(u, v) ↦ u`.

In other words, `f` is a submersion at each `x ∈ M`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being a submersion at `x` includes a choice of linear isomorphism between `E` and `E'' × F`. -/
/-
**Manifold.IsSubmersionOfComplement** 是 Mathlib 中的一个定义，位于命名空间 `Manifold`。
形式化陈述：IsSubmersionOfComplement (f : M -> N) : Prop
参数：f : M -> N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : M → N` is a `C^n` submersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `(u, v) ↦ u`.

In other words, `f` is a submersion at each `x ∈ M`.

This definition has a fixed parameter `F`, which is a choice of complement of `E
` in `E'`:
being a submersion at `x` includes a choice of linear isomorphism between `E` an
d `E'' × F`.
-/
def IsSubmersionOfComplement (f : M → N) : Prop := ∀ x, IsSubmersionAtOfComplement F I J n f x

variable (I J n) in
/-- `f : M → N` is a `C^n` submersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `(u, v) ↦ u`.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`:
being a submersion includes a choice of linear isomorphism between `E` and `E'' × F`, which is where
the choice of `F` enters. If you need stronger control over the complement `F`,
use `IsSubmersionOfComplement` instead.

Note that our global choice of complement is a bit stronger than asking `f` to be a submersion at
each `x ∈ M` w.r.t. to potentially varying complements: see `isSubmersionAt` for details.
-/
/-
**Manifold.IsSubmersion** 是 Mathlib 中的一个定义，位于命名空间 `Manifold`。
形式化陈述：IsSubmersion (f : M -> N) : Prop
参数：f : M -> N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : M → N` is a `C^n` submersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `(u, v) ↦ u`.

Implicit in this definition is an abstract choice `F` of a complement of `E` in 
`E'`:
being a submersion includes a choice of linear isomorphism between `E` and `E'' 
× F`, which is where
the choice of `F` enters. If you need stronger control over the complement `F`,
use `IsSubmersionOfComplement` instead.

Note that our global choice of complement is a bit stronger than asking `f` to b
e a submersion at
each `x ∈ M` w.r.t. to potentially varying complements: see `isSubmersionAt` for
 details.
-/
def IsSubmersion (f : M → N) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionOfComplement F I J n f

namespace IsSubmersionOfComplement

variable {f g : M → N}

/-- If `f` is a submersion, it is a submersion at each point. -/
/-
**Manifold.IsSubmersionOfComplement.isSubmersionAt** 是 Mathlib 中的一个引理，位于命名空间 `Ma
nifold.IsSubmersionOfComplement`。
形式化陈述：isSubmersionAt (h : IsSubmersionOfComplement F I J n f) (x : M) : IsSubmer
sionAtOfComplement F I J n f x
参数：h : IsSubmersionOfComplement F I J n f；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a submersion, it is a submersion at each point.
-/
lemma isSubmersionAt (h : IsSubmersionOfComplement F I J n f) (x : M) :
    IsSubmersionAtOfComplement F I J n f x := h x
/-
**Manifold.IsSubmersionOfComplement.trans_F** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.
IsSubmersionOfComplement`。
形式化陈述：trans_F (h : IsSubmersionOfComplement F I J n f) (e : F ≃L[𝕜] F') : IsSubm
ersionOfComplement F' I J n f
参数：h : IsSubmersionOfComplement F I J n f；e : F ≃L[𝕜] F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.trans_F`：trans_F (h : IsSubmersionAt
OfComplement F I J n f x) (e : F ≃L[𝕜] F') : IsSubmersionAtOfComplement F' I J n
 f x
-/
lemma trans_F (h : IsSubmersionOfComplement F I J n f) (e : F ≃L[𝕜] F') :
    IsSubmersionOfComplement F' I J n f :=
  fun x ↦ (h x).trans_F e

/-- Being a submersion w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
/-
**Manifold.IsSubmersionOfComplement.congr_F** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.
IsSubmersionOfComplement`。
形式化陈述：congr_F (e : F ≃L[𝕜] F') : IsSubmersionOfComplement F I J n f ↔ IsSubmersi
onOfComplement F' I J n f
参数：e : F ≃L[𝕜] F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionOfComplement.trans_F`：trans_F (h : IsSubmersionOfCo
mplement F I J n f) (e : F ≃L[𝕜] F') : IsSubmersionOfComplement F' I J n f

--- 原说明 ---
Being a submersion w.r.t. `F` is stable under replacing `F` by an isomorphic cop
y.
-/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsSubmersionOfComplement F I J n f ↔ IsSubmersionOfComplement F' I J n f :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/-- If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'` (w.r.t. `F` and `F'`),
respectively, then `f × g: M × M' → N × N'` is a submersion at `(x, x')` w.r.t. `F × F'`. -/
/-
**Manifold.IsSubmersionOfComplement.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.
IsSubmersionOfComplement`。
形式化陈述：prodMap {f : M -> N} {g : M' -> N'} [IsManifold I n M] [IsManifold I' n M'
] [IsManifold J n N] [IsManifold J' n N'] (h : IsSubmersionOfComplement F I J n 
f) (h' : IsSubmersionOfComplement F' I' J' n g) : IsSubmersionOfComplement (F × 
F') (I.prod I') (J.prod J') n (Prod.map f g)
参数：h : IsSubmersionOfComplement F I J n f；h' : IsSubmersionOfComplement F' I' J'
 n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsSubmersionAtOfComplement.prodMap`：prodMap {f : M -> N} {g : M
' -> N'} {x' : M'} [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [I
sManifold J' n N'] (hf : IsSubmer…

--- 原说明 ---
If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'` (w.r.t. `F` and `
F'`),
respectively, then `f × g: M × M' → N × N'` is a submersion at `(x, x')` w.r.t. 
`F × F'`.
-/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (h : IsSubmersionOfComplement F I J n f) (h' : IsSubmersionOfComplement F' I' J' n g) :
    IsSubmersionOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun ⟨x, x'⟩ ↦ (h x).prodMap (h' x')

/-- If `f` is a submersion w.r.t. some complement `F`, it is a submersion.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being a submersion requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`.
-/
/-
**Manifold.IsSubmersionOfComplement.isSubmersion** 是 Mathlib 中的一个引理，位于命名空间 `Mani
fold.IsSubmersionOfComplement`。
形式化陈述：isSubmersion (h : IsSubmersionOfComplement F I J n f) : IsSubmersion I J n
 f
参数：h : IsSubmersionOfComplement F I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Geometry.Manifold.Submersion.0.Manifold.IsSubmersion.eq
_1`：∀ {𝕜 : Type u_1} {E'' : Type u_3} {H : Type u_7} {G : Type u_9} {E : Type u}
 [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGro…
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Manifold.IsSubmersionOfComplement.congr_F`：congr_F (e : F ≃L[𝕜] F') : Is
SubmersionOfComplement F I J n f ↔ IsSubmersionOfComplement F' I J n f

--- 原说明 ---
If `f` is a submersion w.r.t. some complement `F`, it is a submersion.

Note that the proof contains a small formalisation-related subtlety: `F` can liv
e in any universe,
while being a submersion requires the existence of a complement in the same univ
erse as
the model normed space of `N`. This is solved by `smallComplement` and `smallEqu
iv`.
-/
lemma isSubmersion (h : IsSubmersionOfComplement F I J n f) : IsSubmersion I J n f := by
  by_cases! hM : IsEmpty M
  · rw [IsSubmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x ↦ (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionOfComplement.congr_F (h x).smallEquiv).mp h

open IsManifold in
/-- The identity map is a submersion with complement `PUnit`. -/
/-
**Manifold.IsSubmersionOfComplement.id** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsSub
mersionOfComplement`。
形式化陈述：∀ {𝕜 : Type u_1} {H : Type u_7} {E : Type u} [inst : NontriviallyNormedFie
ld 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : Top
ologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_11}   [inst_4 : Topolo
gicalSpace M] [inst_5 : ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M],  
 Manifold.IsSubmersionOfComplement PUnit.{u_15 + 1} I I n id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt`：mk_of_continuous
At {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F)) (dom
Chart : OpenPartialHomeomorph M H) (codChart…
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id

--- 原说明 ---
The identity map is a submersion with complement `PUnit`.
-/
protected lemma id [IsManifold I n M] : IsSubmersionOfComplement PUnit I I n (@id M) := by
  intro x
  apply IsSubmersionAtOfComplement.mk_of_continuousAt (continuousAt_id)
    (ContinuousLinearEquiv.prodUnique 𝕜 E PUnit).symm
    (chartAt H x) (chartAt H x) (mem_chart_source H x) (mem_chart_source H x)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x)
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
  simpa

/-- A `C^n` submersion is `C^n` -/
/-
**Manifold.IsSubmersionOfComplement.contMDiff** 是 Mathlib 中的一个定理，位于命名空间 `Manifol
d.IsSubmersionOfComplement`。
形式化陈述：contMDiff (h : IsSubmersionOfComplement F I J n f) : CMDiff n f
参数：h : IsSubmersionOfComplement F I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsSubmersionAtOfComplement.contMDiffAt`：contMDiffAt (h : IsSubm
ersionAtOfComplement F I J n f x) : CMDiffAt n f x

--- 原说明 ---
A `C^n` submersion is `C^n`
-/
theorem contMDiff (h : IsSubmersionOfComplement F I J n f) : CMDiff n f :=
  fun x ↦ (h x).contMDiffAt

end IsSubmersionOfComplement

namespace IsSubmersion

variable {f g : M → N}

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
/-
**Manifold.IsSubmersion.complement** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.IsSubmers
ion`。
形式化陈述：complement (h : IsSubmersion I J n f) : Type u
参数：h : IsSubmersion I J n f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of complement of the model normed space `E` of `M` in the model normed 
space
`E'` of `N`
-/
def complement (h : IsSubmersion I J n f) : Type u := Classical.choose h
/-
**Manifold.IsSubmersion.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsSubmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance (h : IsSubmersion I J n f) : NormedAddCommGroup h.complement :=
  Classical.choose <| Classical.choose_spec h
/-
**Manifold.IsSubmersion.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsSubmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance (h : IsSubmersion I J n f) : NormedSpace 𝕜 h.complement :=
  Classical.choose <| Classical.choose_spec <| Classical.choose_spec h
/-
**Manifold.IsSubmersion.isSubmersionOfComplement_complement** 是 Mathlib 中的一个引理，位
于命名空间 `Manifold.IsSubmersion`。
形式化陈述：isSubmersionOfComplement_complement (h : IsSubmersion I J n f) : IsSubmers
ionOfComplement h.complement I J n f
参数：h : IsSubmersion I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma isSubmersionOfComplement_complement (h : IsSubmersion I J n f) :
    IsSubmersionOfComplement h.complement I J n f :=
  Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

/-- If `f` is a submersion, it is a submersion at each point. -/
/-
**Manifold.IsSubmersion.isSubmersionAt** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsSub
mersion`。
形式化陈述：isSubmersionAt (h : IsSubmersion I J n f) (x : M) : IsSubmersionAt I J n f
 x
参数：h : IsSubmersion I J n f；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Geometry.Manifold.Submersion.0.Manifold.IsSubmersionAt.
eq_1`：∀ {𝕜 : Type u_1} {E'' : Type u_3} {H : Type u_7} {G : Type u_9} {E : Type 
u} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGro…
· 使用引理 `Manifold.IsSubmersion.isSubmersionOfComplement_complement`：isSubmersionO
fComplement_complement (h : IsSubmersion I J n f) : IsSubmersionOfComplement h.c
omplement I J n f

--- 原说明 ---
If `f` is a submersion, it is a submersion at each point.
-/
lemma isSubmersionAt (h : IsSubmersion I J n f) (x : M) : IsSubmersionAt I J n f x := by
  rw [IsSubmersionAt]
  use h.complement, by infer_instance, by infer_instance
  exact h.isSubmersionOfComplement_complement x

/-- If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × M' → N × N'` is a submersion at `(x, x')`. -/
/-
**Manifold.IsSubmersion.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsSubmersion
`。
形式化陈述：prodMap {f : M -> N} {g : M' -> N'} [IsManifold I n M] [IsManifold I' n M'
] [IsManifold J n N] [IsManifold J' n N'] (hf : IsSubmersion I J n f) (hg : IsSu
bmersion I' J' n g) : IsSubmersion (I.prod I') (J.prod J') n (Prod.map f g)
参数：hf : IsSubmersion I J n f；hg : IsSubmersion I' J' n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsSubmersionOfComplement.isSubmersion`：isSubmersion (h : IsSubm
ersionOfComplement F I J n f) : IsSubmersion I J n f
· 使用定理 `Manifold.IsSubmersionOfComplement.prodMap`：prodMap {f : M -> N} {g : M' 
-> N'} [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J'
 n N'] (h : IsSubmersionOfCompl…
· 使用引理 `Manifold.IsSubmersion.isSubmersionOfComplement_complement`：isSubmersionO
fComplement_complement (h : IsSubmersion I J n f) : IsSubmersionOfComplement h.c
omplement I J n f

--- 原说明 ---
If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × M' → N × N'` is a submersion at `(x, x')`.
-/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersion I J n f) (hg : IsSubmersion I' J' n g) :
    IsSubmersion (I.prod I') (J.prod J') n (Prod.map f g) :=
  (hf.isSubmersionOfComplement_complement.prodMap
    hg.isSubmersionOfComplement_complement ).isSubmersion

/-- The identity map is an submersion. -/
/-
**Manifold.IsSubmersion.id** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsSubmersion`。
形式化陈述：∀ {𝕜 : Type u_1} {H : Type u_7} {E : Type u} [inst : NontriviallyNormedFie
ld 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : Top
ologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_11}   [inst_4 : Topolo
gicalSpace M] [inst_5 : ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M],  
 Manifold.IsSubmersion I I n id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsSubmersionOfComplement.id`：∀ {𝕜 : Type u_1} {H : Type u_7} {E
 : Type u} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 E]…

--- 原说明 ---
The identity map is an submersion.
-/
protected lemma id [IsManifold I n M] : IsSubmersion I I n (@id M) := by
  use PUnit, by infer_instance, by infer_instance
  exact IsSubmersionOfComplement.id

/-- A `C^n` submersion is `C^n` -/
/-
**Manifold.IsSubmersion.contMDiff** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsSubmersi
on`。
形式化陈述：contMDiff (h : IsSubmersion I J n f) : CMDiff n f
参数：h : IsSubmersion I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsSubmersionOfComplement.contMDiff`：contMDiff (h : IsSubmersion
OfComplement F I J n f) : CMDiff n f
· 使用引理 `Manifold.IsSubmersion.isSubmersionOfComplement_complement`：isSubmersionO
fComplement_complement (h : IsSubmersion I J n f) : IsSubmersionOfComplement h.c
omplement I J n f

--- 原说明 ---
A `C^n` submersion is `C^n`
-/
theorem contMDiff (h : IsSubmersion I J n f) : CMDiff n f :=
  h.isSubmersionOfComplement_complement.contMDiff

end IsSubmersion

end Manifold

