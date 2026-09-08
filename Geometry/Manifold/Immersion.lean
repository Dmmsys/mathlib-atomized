/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.LocalSourceTargetProperty
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Analysis.Normed.Module.Shrink  -- shake: keep (NormedAddCommGroup (Shrink ...)), cf. lean#13417
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-! # Smooth immersions

In this file, we define `C^n` immersions between `C^n` manifolds.
The correct definition in the infinite-dimensional setting differs from the standard
finite-dimensional definition (concerning the `mfderiv` being injective): future pull requests will
prove that our definition implies the latter, and that both are equivalent for finite-dimensional
manifolds.

This definition can be conveniently formulated in terms of local properties: `f` is an immersion at
`x` iff there exist suitable charts near `x` and `f x` such that `f` has a nice form w.r.t. these
charts. Most results below can be deduced from more abstract results about such local properties.
This shortens the overall argument, as the definition of submersions has the same general form.

## Main definitions

* `IsImmersionAtOfComplement F I J n f x` means a map `f : M → N` between `C^n` manifolds `M` and
  `N` is an immersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`, w.r.t. some equivalence
  `E' ≃L[𝕜] E × F`. We do not demand that `f` be differentiable (this follows from this definition).
* `IsImmersionAt I J n f x` means that `f` is a `C^n` immersion at `x : M` for some choice of a
  complement `F` of the model normed space `E` of `M` in the model normed space `E'` of `N`.
  In most cases, prefer this definition over `IsImmersionAtOfComplement`.
* `IsImmersionOfComplement F I J n f` means `f : M → N` is an immersion at every point `x : M`,
  w.r.t. the chosen complement `F`.
* `IsImmersion I J n f` means `f : M → N` is an immersion at every point `x : M`,
  w.r.t. some global choice of complement.

## Main results

* `IsImmersionAt.congr_of_eventuallyEq`: being an immersion is a local property.
  If `f` and `g` agree near `x` and `f` is an immersion at `x`, so is `g`
* `IsImmersionAtOfComplement.congr_F`, `IsImmersionOfComplement.congr_F`:
  being an immersion (at `x`) w.r.t. `F` is stable under
  replacing the complement `F` by an isomorphic copy.
* `IsOpen.isImmersionAtOfComplement` and `IsOpen.isImmersionAt`:
  the set of points where `IsImmersionAt(OfComplement)` holds is open.
* `IsImmersionAt.prodMap` and `IsImmersion.prodMap`: the product of two immersions (at a point)
  is an immersion (at the product point).
* `IsImmersion.id`: the identity map is an immersion
* `IsImmersion.of_opens`: the inclusion of an open subset `s → M` of a smooth manifold
  is a smooth immersion
* `ModelWithCorners.isImmersion`: every model with corners is itself an immersion
* `IsImmersionOfComplement.sumInl` and `IsImmersionOfComplement.sumInr`: given `C^n` manifolds
  `M` and `N`, `Sum.inl : M → M ⊕ N` and `Sum.inr : N → M ⊕ N` are `C^n` immersions
* `IsImmersionAt.contMDiffAt`: if f is an immersion at `x`, it is `C^n` at `x`.
* `IsImmersion.contMDiff`: if f is a `C^n` immersion, it is automatically `C^n`
  in the sense of `ContMDiff`.
* `ContMDiffAt.iff_comp_isImmersionAt` and `ContMDiff.iff_comp_isImmersion`: a function `f : M → N`
  is `C^n` (at `x`) if and only if it is continuous (at `x`) and its composition `φ ∘ f` with a
  `C^n` immersion `φ : N → P` (at `f x`) is `C^n`.

## Implementation notes

* In most applications, there is no need to control the choice of complement in the definition of an
  immersion, so `IsImmersion(At)` is perfectly adequate. Such control will be helpful, however,
  when considering the local characterisation of submanifolds: locally, a submanifold is described
  either as the image of an immersion, or the preimage of a submersion --- w.r.t. the same
  complement. Providing a version of the definition that includes complements enables stating this
  equivalence cleanly.
* To avoid a free universe variable in `IsImmersion(At)`, we ask for a complement in the same
  universe as the model normed space for `N`. We provide convenience constructors which do not
  have this restriction to preserve usability.
  This relies on the observation that the equivalence in the definition of immersions allows
  shrinking the universe of the complement: this is implemented in
  `IsImmersion(At)OfComplement.small` and `IsImmersion(At)OfComplement.smallEquiv`.

## TODO
* The converse to `IsImmersionAtOfComplement.congr_F` also holds: any two complements are
  isomorphic, as they are isomorphic to the cokernel of the differential `mfderiv I J f x`.
* If `f` is an immersion at `x`, its differential splits, hence is injective.
* If `f : M → N` is a map between Banach manifolds, `mfderiv I J f x` splitting implies `f` is an
  immersion at `x`. (This requires the inverse function theorem.)
* `IsImmersionAt.comp`: if `f : M → N` and `g: N → N'` are maps between Banach manifolds such that
  `f` is an immersion at `x : M` and `g` is an immersion at `f x`, then `g ∘ f` is an immersion
  at `x`.
* `IsImmersion.comp`: the composition of immersions (between Banach manifolds) is an immersion
* If `f : M → N` is a map between finite-dimensional manifolds, `mfderiv I J f x` being injective
  implies `f` is an immersion at `x`.
* `IsLocalDiffeomorphAt.isImmersionAt` and `IsLocalDiffeomorph.isImmersion`:
  a local diffeomorphism (at `x`) is an immersion (at `x`)
* `Diffeomorph.isImmersion`: in particular, a diffeomorphism is an immersion

## References

* [Juan Margalef-Roig and Enrique Outerelo Dominguez, *Differential topology*][roigdomingues1992]

-/

open scoped Topology ContDiff
open Function Set

public noncomputable section

namespace Manifold

-- We manually name the universe of `E''` as `IsImmersionAt` will use it.
universe u
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E''' : Type*} {E'' : Type u} {F F' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

variable (F I J M N) in
/-- The local property of being an immersion at a point: `f : M → N` is an immersion at `x` if
there exist charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively, such that in these
charts, `f` looks like the inclusion `u ↦ (u, 0)`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in the model
normed space `E'` of `N`: being an immersion at `x` includes a choice of linear isomorphism
between `E × F` and `E'`. -/
/-
**Manifold.ImmersionAtProp** 是 Mathlib 中的一个定义，位于命名空间 `Manifold`。
形式化陈述：ImmersionAtProp : (M -> N) -> OpenPartialHomeomorph M H -> OpenPartialHome
omorph N G -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The local property of being an immersion at a point: `f : M → N` is an immersion
 at `x` if
there exist charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
, such that in these
charts, `f` looks like the inclusion `u ↦ (u, 0)`.

This definition has a fixed parameter `F`, which is a choice of complement of `E
` in the model
normed space `E'` of `N`: being an immersion at `x` includes a choice of linear 
isomorphism
between `E × F` and `E'`.
-/
def ImmersionAtProp : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop :=
  fun f domChart codChart ↦ ∃ equiv : (E × F) ≃L[𝕜] E'',
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- Being an immersion at `x` is a local property. -/
/-
**Manifold.isLocalSourceTargetProperty_immersionAtProp** 是 Mathlib 中的一个引理，位于命名空间
 `Manifold`。
形式化陈述：isLocalSourceTargetProperty_immersionAtProp : IsLocalSourceTargetProperty 
(ImmersionAtProp F I J M N) where mono_source {f φ ψ s} hs
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
Being an immersion at `x` is a local property.
-/
lemma isLocalSourceTargetProperty_immersionAtProp :
    IsLocalSourceTargetProperty (ImmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs := fun ⟨equiv, hf⟩ ↦ ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx ↦ ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x ∈ φ.source := by simp_all
    grind

variable (F I J n) in
/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlases used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`.
While the particular choice of complement is often not important, choosing a complement is useful
in some settings, such as proving that embedded submanifolds are locally given either by an
immersion or a submersion.
Unless you have a particular reason, prefer to use `IsImmersionAt` instead.
-/
/-
**Manifold.IsImmersionAtOfComplement** 是 Mathlib 中的一个定义，位于命名空间 `Manifold`。
形式化陈述：IsImmersionAtOfComplement (f : M -> N) (x : M) : Prop
参数：f : M -> N；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` a
nd `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u 
↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlases used for `M` and `N`, so asking for `φ`
 and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficien
t.

This definition has a fixed parameter `F`, which is a choice of complement of `E
` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F
` and `E'`.
While the particular choice of complement is often not important, choosing a com
plement is useful
in some settings, such as proving that embedded submanifolds are locally given e
ither by an
immersion or a submersion.
Unless you have a particular reason, prefer to use `IsImmersionAt` instead.
-/
def IsImmersionAtOfComplement (f : M → N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N)

-- Lift the universe from `E''`, to avoid a free universe parameter.
variable (I J n) in
/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlases used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`: being an
immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`, which is
where the choice of `F` enters.
If you need stronger control over the complement `F`, use `IsImmersionAtOfComplement` instead.
-/
/-
**Manifold.IsImmersionAt** 是 Mathlib 中的一个定义，位于命名空间 `Manifold`。
形式化陈述：IsImmersionAt (f : M -> N) (x : M) : Prop
参数：f : M -> N；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` a
nd `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u 
↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlases used for `M` and `N`, so asking for `φ`
 and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficien
t.

Implicit in this definition is an abstract choice `F` of a complement of `E` in 
`E'`: being an
immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'
`, which is
where the choice of `F` enters.
If you need stronger control over the complement `F`, use `IsImmersionAtOfComple
ment` instead.
-/
def IsImmersionAt (f : M → N) (x : M) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsImmersionAtOfComplement F I J n f x

variable {f g : M → N} {x : M}

namespace IsImmersionAtOfComplement

/-
**Manifold.IsImmersionAtOfComplement.mk_of_charts** 是 Mathlib 中的一个引理，位于命名空间 `Man
ifold.IsImmersionAtOfComplement`。
形式化陈述：mk_of_charts (equiv : (E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph
 M H) (codChart : OpenPartialHomeomorph N G) (hx : x in domChart.source) (hfx : 
f x in codChart.source) (hdomChart : domChart in IsManifold.maximalAtlas I n M) 
(hcodChart : codChart in IsManifold.maximalAtlas J n N) (hsource : domChart.sour
ce subseteq f ⁻¹' codChart.source) (hwrittenInExtend : EqOn ((codChart.extend J)
 ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0)) (domChart.extend I).target) : 
IsImmersionAtOfComplement 
参数：equiv : (E × F) ≃L[𝕜] E''；domChart : OpenPartialHomeomorph M H；codChart : Ope
nPartialHomeomorph N G；hx : x in domChart.source；hfx : f x in codChart.source；hd
omChart : domChart in IsManifold.maximalAtlas I n M；hcodChart : codChart in IsMa
nifold.maximalAtlas J n N；hsource : domChart.source subseteq f ⁻¹' codChart.sour
ce；hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) 
(equiv ∘ (·, 0)) (domChart.extend I).target。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_of_charts (equiv : (E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph M H)
    (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAtOfComplement F I J n f x := by
  use domChart, codChart
  use equiv

/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
/-
**Manifold.IsImmersionAtOfComplement.mk_of_continuousAt** 是 Mathlib 中的一个引理，位于命名空
间 `Manifold.IsImmersionAtOfComplement`。
形式化陈述：mk_of_continuousAt {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (
E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartial
Homeomorph N G) (hx : x in domChart.source) (hfx : f x in codChart.source) (hdom
Chart : domChart in IsManifold.maximalAtlas I n M) (hcodChart : codChart in IsMa
nifold.maximalAtlas J n N) (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (
domChart.extend I).symm) (equiv ∘ (·, 0)) (domChart.extend I).target) : IsImmers
ionAtOfComplement F I J n 
参数：hf : ContinuousAt f x；equiv : (E × F) ≃L[𝕜] E''；domChart : OpenPartialHomeomo
rph M H；codChart : OpenPartialHomeomorph N G；hx : x in domChart.source；hfx : f x
 in codChart.source；hdomChart : domChart in IsManifold.maximalAtlas I n M；hcodCh
art : codChart in IsManifold.maximalAtlas J n N；hwrittenInExtend : EqOn ((codCha
rt.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0)) (domChart.extend I
).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.mk_of_continuousAt`：mk_of_continuous
At (hf : ContinuousAt f x) (hP : IsLocalSourceTargetProperty P) (domChart : Open
PartialHomeomorph M H) (codChart : OpenParti…
· 使用引理 `Manifold.isLocalSourceTargetProperty_immersionAtProp`：isLocalSourceTarge
tProperty_immersionAtProp : IsLocalSourceTargetProperty (ImmersionAtProp F I J M
 N) where mono_source {f φ ψ s} hs

--- 原说明 ---
`f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` a
nd `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u 
↦ (u, 0)`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`.
-/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAtOfComplement F I J n f x :=
  LiftSourceTargetPropertyAt.mk_of_continuousAt hf isLocalSourceTargetProperty_immersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

/-- A choice of chart on the domain `M` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
/-
**Manifold.IsImmersionAtOfComplement.domChart** 是 Mathlib 中的一个定义，位于命名空间 `Manifol
d.IsImmersionAtOfComplement`。
形式化陈述：domChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomor
ph M H
参数：h : IsImmersionAtOfComplement F I J n f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of chart on the domain `M` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given b
y
`h.codChart` and `h.codChart`.
-/
def domChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph M H :=
  LiftSourceTargetPropertyAt.domChart h

/-- A choice of chart on the co-domain `N` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
/-
**Manifold.IsImmersionAtOfComplement.codChart** 是 Mathlib 中的一个定义，位于命名空间 `Manifol
d.IsImmersionAtOfComplement`。
形式化陈述：codChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomor
ph N G
参数：h : IsImmersionAtOfComplement F I J n f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of chart on the co-domain `N` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given b
y
`h.equiv` and `h.domChart`.
-/
def codChart (h : IsImmersionAtOfComplement F I J n f x) : OpenPartialHomeomorph N G :=
  LiftSourceTargetPropertyAt.codChart h
/-
**Manifold.IsImmersionAtOfComplement.mem_domChart_source** 是 Mathlib 中的一个引理，位于命名
空间 `Manifold.IsImmersionAtOfComplement`。
形式化陈述：mem_domChart_source (h : IsImmersionAtOfComplement F I J n f x) : x in h.d
omChart.source
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.mem_domChart_source`：mem_domChart_so
urce (h : LiftSourceTargetPropertyAt I J n f x P) : x in h.domChart.source
-/
lemma mem_domChart_source (h : IsImmersionAtOfComplement F I J n f x) : x ∈ h.domChart.source :=
  LiftSourceTargetPropertyAt.mem_domChart_source h
/-
**Manifold.IsImmersionAtOfComplement.mem_codChart_source** 是 Mathlib 中的一个引理，位于命名
空间 `Manifold.IsImmersionAtOfComplement`。
形式化陈述：mem_codChart_source (h : IsImmersionAtOfComplement F I J n f x) : f x in h
.codChart.source
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.mem_codChart_source`：mem_codChart_so
urce (h : LiftSourceTargetPropertyAt I J n f x P) : f x in h.codChart.source
-/
lemma mem_codChart_source (h : IsImmersionAtOfComplement F I J n f x) : f x ∈ h.codChart.source :=
  LiftSourceTargetPropertyAt.mem_codChart_source h
/-
**Manifold.IsImmersionAtOfComplement.domChart_mem_maximalAtlas** 是 Mathlib 中的一个引
理，位于命名空间 `Manifold.IsImmersionAtOfComplement`。
形式化陈述：domChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) : h.
domChart in IsManifold.maximalAtlas I n M
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas`：domChart_
mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) : h.domChart in Is
Manifold.maximalAtlas I n M
-/
lemma domChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  LiftSourceTargetPropertyAt.domChart_mem_maximalAtlas h
/-
**Manifold.IsImmersionAtOfComplement.codChart_mem_maximalAtlas** 是 Mathlib 中的一个引
理，位于命名空间 `Manifold.IsImmersionAtOfComplement`。
形式化陈述：codChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) : h.
codChart in IsManifold.maximalAtlas J n N
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas`：codChart_
mem_maximalAtlas (h : LiftSourceTargetPropertyAt I J n f x P) : h.codChart in Is
Manifold.maximalAtlas J n N
-/
lemma codChart_mem_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) :
    h.codChart ∈ IsManifold.maximalAtlas J n N :=
  LiftSourceTargetPropertyAt.codChart_mem_maximalAtlas h
/-
**Manifold.IsImmersionAtOfComplement.source_subset_preimage_source** 是 Mathlib 中
的一个引理，位于命名空间 `Manifold.IsImmersionAtOfComplement`。
形式化陈述：source_subset_preimage_source (h : IsImmersionAtOfComplement F I J n f x) 
: h.domChart.source subseteq f ⁻¹' h.codChart.source
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.source_subset_preimage_source`：sourc
e_subset_preimage_source (h : LiftSourceTargetPropertyAt I J n f x P) : h.domCha
rt.source subseteq f ⁻¹' h.codChart.source
-/
lemma source_subset_preimage_source (h : IsImmersionAtOfComplement F I J n f x) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source :=
  LiftSourceTargetPropertyAt.source_subset_preimage_source h
/-
**Manifold.IsImmersionAtOfComplement.mapsto_domChart_source_codChart_source** 是 
Mathlib 中的一个引理，位于命名空间 `Manifold.IsImmersionAtOfComplement`。
形式化陈述：mapsto_domChart_source_codChart_source (h : IsImmersionAtOfComplement F I 
J n f x) : MapsTo f h.domChart.source h.codChart.source
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.source_subset_preimage_source`：source
_subset_preimage_source (h : IsImmersionAtOfComplement F I J n f x) : h.domChart
.source subseteq f ⁻¹' h.codChart.source
-/
lemma mapsto_domChart_source_codChart_source (h : IsImmersionAtOfComplement F I J n f x) :
    MapsTo f h.domChart.source h.codChart.source :=
  h.source_subset_preimage_source

/-- A linear equivalence `E × F ≃L[𝕜] E''` which belongs to the data of an immersion `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
/-
**Manifold.IsImmersionAtOfComplement.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.I
sImmersionAtOfComplement`。
形式化陈述：equiv (h : IsImmersionAtOfComplement F I J n f x) : (E × F) ≃L[𝕜] E''
参数：h : IsImmersionAtOfComplement F I J n f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence `E × F ≃L[𝕜] E''` which belongs to the data of an immersion
 `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses g
iven by
`h.domChart` and `h.codChart`.
-/
def equiv (h : IsImmersionAtOfComplement F I J n f x) : (E × F) ≃L[𝕜] E'' :=
  Classical.choose <| LiftSourceTargetPropertyAt.property h
/-
**Manifold.IsImmersionAtOfComplement.writtenInCharts** 是 Mathlib 中的一个引理，位于命名空间 `
Manifold.IsImmersionAtOfComplement`。
形式化陈述：writtenInCharts (h : IsImmersionAtOfComplement F I J n f x) : EqOn ((h.cod
Chart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0)) (h.domChart
.extend I).target
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.property`：property (h : LiftSourceTa
rgetPropertyAt I J n f x P) : P f h.domChart h.codChart
-/
lemma writtenInCharts (h : IsImmersionAtOfComplement F I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target :=
  Classical.choose_spec <| LiftSourceTargetPropertyAt.property h
/-
**Manifold.IsImmersionAtOfComplement.property** 是 Mathlib 中的一个引理，位于命名空间 `Manifol
d.IsImmersionAtOfComplement`。
形式化陈述：property (h : IsImmersionAtOfComplement F I J n f x) : LiftSourceTargetPro
pertyAt I J n f x (ImmersionAtProp F I J M N)
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma property (h : IsImmersionAtOfComplement F I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N) := h

/--
If `f` is an immersion at `x`, it maps its domain chart's target `(h.domChart.extend I).target`
to its codomain chart's target `(h.domChart.extend J).target`.

Roig and Domingues' [roigdomingues1992] definition of immersions only asks for this inclusion
between the targets of the local charts: using mathlib's formalisation conventions, that condition
is *slightly* weaker than `source_subset_preimage_source`: the latter implies that
`h.codChart.extend J ∘ f` maps `h.domChart.source` to
`(h.codChart.extend J).target = (h.codChart.extend I) '' h.codChart.source`,
but that does *not* imply `f` maps `h.domChart.source` to `h.codChart.source`;
a priori `f` could map some point `f ∘ h.domChart.extend I x ∉ h.codChart.source` into the target.
Note that this difference only occurs because of our design using junk values;
this is not a mathematically meaningful difference.

At the same time, this condition is fairly weak: it is implied, for instance, by `f` being
continuous at `x` (see `mk_of_continuousAt`), which is easy to ascertain in practice.

See `target_subset_preimage_target` for a version stated using preimages instead of images.
-/
/-
**Manifold.IsImmersionAtOfComplement.map_target_subset_target** 是 Mathlib 中的一个引理
，位于命名空间 `Manifold.IsImmersionAtOfComplement`。
形式化陈述：map_target_subset_target (h : IsImmersionAtOfComplement F I J n f x) : (h.
equiv ∘ (·, 0)) '' (h.domChart.extend I).target subseteq (h.codChart.extend J).t
arget
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用引理 `Manifold.IsImmersionAtOfComplement.writtenInCharts`：writtenInCharts (h :
 IsImmersionAtOfComplement F I J n f x) : EqOn ((h.codChart.extend J) ∘ f ∘ (h.d
omChart.extend I).symm) (h.equiv ∘ (·, 0…
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
· 使用引理 `Manifold.IsImmersionAtOfComplement.source_subset_preimage_source`：source
_subset_preimage_source (h : IsImmersionAtOfComplement F I J n f x) : h.domChart
.source subseteq f ⁻¹' h.codChart.source
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If `f` is an immersion at `x`, it maps its domain chart's target `(h.domChart.ex
tend I).target`
to its codomain chart's target `(h.domChart.extend J).target`.

Roig and Domingues' [roigdomingues1992] definition of immersions only asks for t
his inclusion
between the targets of the local charts: using mathlib's formalisation conventio
ns, that condition
is *slightly* weaker than `source_subset_preimage_source`: the latter implies th
at
`h.codChart.extend J ∘ f` maps `h.domChart.source` to
`(h.codChart.extend J).target = (h.codChart.extend I) '' h.codChart.source`,
but that does *not* imply `f` maps `h.domChart.source` to `h.codChart.source`;
a priori `f` could map some point `f ∘ h.domChart.extend I x ∉ h.codChart.source
` into the target.
Note that this difference only occurs because of our design using junk values;
this is not a mathematically meaningful difference.

At the same time, this condition is fairly weak: it is implied, for instance, by
 `f` being
continuous at `x` (see `mk_of_continuousAt`), which is easy to ascertain in prac
tice.

See `target_subset_preimage_target` for a version stated using preimages instead
 of images.
-/
lemma map_target_subset_target (h : IsImmersionAtOfComplement F I J n f x) :
    (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target := by
  rw [← h.writtenInCharts.image_eq, Set.image_comp, Set.image_comp,
    PartialEquiv.symm_image_target_eq_source, OpenPartialHomeomorph.extend_source,
    ← PartialEquiv.image_source_eq_target]
  have : f '' h.domChart.source ⊆ h.codChart.source := by
    simp [h.source_subset_preimage_source]
  grw [this, OpenPartialHomeomorph.extend_source]

/-- If `f` is an immersion at `x`, its domain chart's target `(h.domChart.extend I).target`
is mapped to its codomain chart's target `(h.domChart.extend J).target`:
see `map_target_subset_target` for a version stated using images. -/
/-
**Manifold.IsImmersionAtOfComplement.target_subset_preimage_target** 是 Mathlib 中
的一个引理，位于命名空间 `Manifold.IsImmersionAtOfComplement`。
形式化陈述：target_subset_preimage_target (h : IsImmersionAtOfComplement F I J n f x) 
: (h.domChart.extend I).target subseteq (h.equiv ∘ (·, 0)) ⁻¹' (h.codChart.exten
d J).target
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.map_target_subset_target`：map_target_
subset_target (h : IsImmersionAtOfComplement F I J n f x) : (h.equiv ∘ (·, 0)) '
' (h.domChart.extend I).target subseteq (h.codCha…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
If `f` is an immersion at `x`, its domain chart's target `(h.domChart.extend I).
target`
is mapped to its codomain chart's target `(h.domChart.extend J).target`:
see `map_target_subset_target` for a version stated using images.
-/
lemma target_subset_preimage_target (h : IsImmersionAtOfComplement F I J n f x) :
    (h.domChart.extend I).target ⊆ (h.equiv ∘ (·, 0)) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx ↦ h.map_target_subset_target (mem_image_of_mem _ hx)

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
/-
**Manifold.IsImmersionAtOfComplement.congr_of_eventuallyEq** 是 Mathlib 中的一个引理，位于
命名空间 `Manifold.IsImmersionAtOfComplement`。
形式化陈述：congr_of_eventuallyEq (hf : IsImmersionAtOfComplement F I J n f x) (hfg : 
f =ᶠ[𝓝 x] g) : IsImmersionAtOfComplement F I J n g x
参数：hf : IsImmersionAtOfComplement F I J n f x；hfg : f =ᶠ[𝓝 x] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.congr_of_eventuallyEq`：congr_of_even
tuallyEq (hP : IsLocalSourceTargetProperty P) (hf : LiftSourceTargetPropertyAt I
 J n f x P) (h' : f =ᶠ[nhds x] g) : LiftSourceT…
· 使用引理 `Manifold.isLocalSourceTargetProperty_immersionAtProp`：isLocalSourceTarge
tProperty_immersionAtProp : IsLocalSourceTargetProperty (ImmersionAtProp F I J M
 N) where mono_source {f φ ψ s} hs
· 使用引理 `Manifold.IsImmersionAtOfComplement.property`：property (h : IsImmersionAt
OfComplement F I J n f x) : LiftSourceTargetPropertyAt I J n f x (ImmersionAtPro
p F I J M N)

--- 原说明 ---
If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`.
-/
lemma congr_of_eventuallyEq (hf : IsImmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n g x :=
  LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_immersionAtProp hf.property hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is an immersion at `x` if and only if `g` is an immersion at `x`. -/
/-
**Manifold.IsImmersionAtOfComplement.congr_iff_of_eventuallyEq** 是 Mathlib 中的一个引
理，位于命名空间 `Manifold.IsImmersionAtOfComplement`。
形式化陈述：congr_iff_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) : IsImmersionAtOfComplement 
F I J n f x ↔ IsImmersionAtOfComplement F I J n g x
参数：hfg : f =ᶠ[𝓝 x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq`：congr_iff
_of_eventuallyEq (hP : IsLocalSourceTargetProperty P) (h' : f =ᶠ[nhds x] g) : Li
ftSourceTargetPropertyAt I J n f x P ↔ LiftSourceTa…
· 使用引理 `Manifold.isLocalSourceTargetProperty_immersionAtProp`：isLocalSourceTarge
tProperty_immersionAtProp : IsLocalSourceTargetProperty (ImmersionAtProp F I J M
 N) where mono_source {f φ ψ s} hs

--- 原说明 ---
If `f = g` on some neighbourhood of `x`,
then `f` is an immersion at `x` if and only if `g` is an immersion at `x`.
-/
lemma congr_iff_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F I J n g x :=
  LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
      isLocalSourceTargetProperty_immersionAtProp hfg
/-
**Manifold.IsImmersionAtOfComplement.small** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.I
sImmersionAtOfComplement`。
形式化陈述：small (hf : IsImmersionAtOfComplement F I J n f x) : Small.{u} F
参数：hf : IsImmersionAtOfComplement F I J n f x。
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
lemma small (hf : IsImmersionAtOfComplement F I J n f x) : Small.{u} F :=
  small_of_injective <| hf.equiv.injective.comp (Prod.mk_right_injective 0)

/-- Given an immersion `f` at `x`, this is a choice of complement which lives in the same universe
as the model space for the co-domain of `f`: this is useful to avoid universe restrictions. -/
/-
**Manifold.IsImmersionAtOfComplement.smallComplement** 是 Mathlib 中的一个定义，位于命名空间 `
Manifold.IsImmersionAtOfComplement`。
形式化陈述：smallComplement (hf : IsImmersionAtOfComplement F I J n f x) : Type u
参数：hf : IsImmersionAtOfComplement F I J n f x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.small`：small (hf : IsImmersionAtOfCom
plement F I J n f x) : Small.{u} F

--- 原说明 ---
Given an immersion `f` at `x`, this is a choice of complement which lives in the
 same universe
as the model space for the co-domain of `f`: this is useful to avoid universe re
strictions.
-/
def smallComplement (hf : IsImmersionAtOfComplement F I J n f x) : Type u :=
  haveI := hf.small
  Shrink.{u} F
/-
**Manifold.IsImmersionAtOfComplement.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsImme
rsionAtOfComplement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedAddCommGroup hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedAddCommGroup (Shrink F)
/-
**Manifold.IsImmersionAtOfComplement.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsImme
rsionAtOfComplement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedSpace 𝕜 hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedSpace 𝕜 (Shrink F)

/-- Given an immersion `f` at `x` w.r.t. a complement `F`, this construction provides
a continuous linear equivalence from `F` to the small complement of `F`:
mathematically, this is just the identity map; however, this is technically useful as it enables
us to always work with `hf.smallComplement`. -/
/-
**Manifold.IsImmersionAtOfComplement.smallEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Manif
old.IsImmersionAtOfComplement`。
形式化陈述：smallEquiv (hf : IsImmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.small
Complement
参数：hf : IsImmersionAtOfComplement F I J n f x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.small`：small (hf : IsImmersionAtOfCom
plement F I J n f x) : Small.{u} F
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given an immersion `f` at `x` w.r.t. a complement `F`, this construction provide
s
a continuous linear equivalence from `F` to the small complement of `F`:
mathematically, this is just the identity map; however, this is technically usef
ul as it enables
us to always work with `hf.smallComplement`.
-/
def smallEquiv (hf : IsImmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement :=
  haveI := hf.small
  ((equivShrink F).symm.continuousLinearEquiv 𝕜).symm
/-
**Manifold.IsImmersionAtOfComplement.trans_F** 是 Mathlib 中的一个引理，位于命名空间 `Manifold
.IsImmersionAtOfComplement`。
形式化陈述：trans_F (h : IsImmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') : IsI
mmersionAtOfComplement F' I J n f x
参数：h : IsImmersionAtOfComplement F I J n f x；e : F ≃L[𝕜] F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.mem_domChart_source`：mem_domChart_sou
rce (h : IsImmersionAtOfComplement F I J n f x) : x in h.domChart.source
· 使用引理 `Manifold.IsImmersionAtOfComplement.mem_codChart_source`：mem_codChart_sou
rce (h : IsImmersionAtOfComplement F I J n f x) : f x in h.codChart.source
· 使用引理 `Manifold.IsImmersionAtOfComplement.domChart_mem_maximalAtlas`：domChart_m
em_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) : h.domChart in IsMa
nifold.maximalAtlas I n M
· 使用引理 `Manifold.IsImmersionAtOfComplement.codChart_mem_maximalAtlas`：codChart_m
em_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) : h.codChart in IsMa
nifold.maximalAtlas J n N
· 使用引理 `Manifold.IsImmersionAtOfComplement.source_subset_preimage_source`：source
_subset_preimage_source (h : IsImmersionAtOfComplement F I J n f x) : h.domChart
.source subseteq f ⁻¹' h.codChart.source
· 使用定理 `Set.EqOn.trans`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ f₃ : 
α → β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s
· 使用引理 `Manifold.IsImmersionAtOfComplement.writtenInCharts`：writtenInCharts (h :
 IsImmersionAtOfComplement F I J n f x) : EqOn ((h.codChart.extend J) ∘ f ∘ (h.d
omChart.extend I).symm) (h.equiv ∘ (·, 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trans_F (h : IsImmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F' I J n f x := by
  refine ⟨h.domChart, h.codChart, h.mem_domChart_source, h.mem_codChart_source,
    h.domChart_mem_maximalAtlas, h.codChart_mem_maximalAtlas, h.source_subset_preimage_source, ?_⟩
  use ((ContinuousLinearEquiv.refl 𝕜 E).prodCongr e.symm).trans h.equiv
  apply Set.EqOn.trans h.writtenInCharts
  intro x hx
  simp

/-- Being an immersion at `x` w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
/-
**Manifold.IsImmersionAtOfComplement.congr_F** 是 Mathlib 中的一个引理，位于命名空间 `Manifold
.IsImmersionAtOfComplement`。
形式化陈述：congr_F (e : F ≃L[𝕜] F') : IsImmersionAtOfComplement F I J n f x ↔ IsImmer
sionAtOfComplement F' I J n f x
参数：e : F ≃L[𝕜] F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.trans_F`：trans_F (h : IsImmersionAtOf
Complement F I J n f x) (e : F ≃L[𝕜] F') : IsImmersionAtOfComplement F' I J n f 
x

--- 原说明 ---
Being an immersion at `x` w.r.t. `F` is stable under replacing `F` by an isomorp
hic copy.
-/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F' I J n f x :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/- The set of points where `IsImmersionAtOfComplement` holds is open. -/
/-
**Manifold.IsImmersionAtOfComplement._root_.IsOpen.isImmersionAtOfComplement** 是
 Mathlib 中的一个引理，位于命名空间 `Manifold.IsImmersionAtOfComplement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of points where `IsImmersionAtOfComplement` holds is open.
-/
lemma _root_.IsOpen.isImmersionAtOfComplement :
    IsOpen {x | IsImmersionAtOfComplement F I J n f x} :=
  IsOpen.liftSourceTargetPropertyAt

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
/-
**Manifold.IsImmersionAtOfComplement.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Manifold
.IsImmersionAtOfComplement`。
形式化陈述：prodMap {f : M -> N} {g : M' -> N'} {x' : M'} [IsManifold I n M] [IsManifo
ld I' n M'] [IsManifold J n N] [IsManifold J' n N'] (hf : IsImmersionAtOfComplem
ent F I J n f x) (hg : IsImmersionAtOfComplement F' I' J' n g x') : IsImmersionA
tOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x')
参数：hf : IsImmersionAtOfComplement F I J n f x；hg : IsImmersionAtOfComplement F' 
I' J' n g x'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.LiftSourceTargetPropertyAt.prodMap`：prodMap [IsManifold I n M] 
[IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N'] {Q : (M' -> N') -> 
OpenPartialHomeomorph M' H' -> Op…
· 使用引理 `Manifold.IsImmersionAtOfComplement.property`：property (h : IsImmersionAt
OfComplement F I J n f x) : LiftSourceTargetPropertyAt I J n f x (ImmersionAtPro
p F I J M N)
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
If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`.
-/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersionAtOfComplement F I J n f x) (hg : IsImmersionAtOfComplement F' I' J' n g x') :
    IsImmersionAtOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' F F').trans (equiv₁.prodCongr equiv₂)
  rw [φ₁.extend_prod φ₂, ψ₁.extend_prod, PartialEquiv.prod_target, eqOn_prod_iff]
  exact ⟨fun x ⟨hx, hx'⟩ ↦ by simpa using hfprop hx, fun x ⟨hx, hx'⟩ ↦ by simpa using hgprop hx'⟩

/-- If `f` is an immersion at `x` w.r.t. some complement `F`, it is an immersion at `x`.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being an immersion at `x` requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`.
-/
/-
**Manifold.IsImmersionAtOfComplement.isImmersionAt** 是 Mathlib 中的一个引理，位于命名空间 `Ma
nifold.IsImmersionAtOfComplement`。
形式化陈述：isImmersionAt (h : IsImmersionAtOfComplement F I J n f x) : IsImmersionAt 
I J n f x
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Manifold.IsImmersionAtOfComplement.congr_F`：congr_F (e : F ≃L[𝕜] F') : I
sImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F' I J n f x

--- 原说明 ---
If `f` is an immersion at `x` w.r.t. some complement `F`, it is an immersion at 
`x`.

Note that the proof contains a small formalisation-related subtlety: `F` can liv
e in any universe,
while being an immersion at `x` requires the existence of a complement in the sa
me universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEqu
iv`.
-/
lemma isImmersionAt (h : IsImmersionAtOfComplement F I J n f x) :
    IsImmersionAt I J n f x := by
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionAtOfComplement.congr_F h.smallEquiv).mp h

open IsManifold in
/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion at every point. -/
/-
**Manifold.IsImmersionAtOfComplement.of_opens** 是 Mathlib 中的一个引理，位于命名空间 `Manifol
d.IsImmersionAtOfComplement`。
形式化陈述：of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) (y : s) : IsImm
ersionAtOfComplement PUnit I I n (Subtype.val : s -> M) y
参数：s : TopologicalSpace.Opens M；y : s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.mk_of_continuousAt`：mk_of_continuousA
t {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'') (domC
hart : OpenPartialHomeomorph M H) (codChart…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
· 使用定理 `TopologicalSpace.Opens.instIsManifoldSubtypeMem`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inclusion of an open subset `s` of a smooth manifold `M` is an immersion at 
every point.
-/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) (y : s) :
    IsImmersionAtOfComplement PUnit I I n (Subtype.val : s → M) y := by
  apply IsImmersionAtOfComplement.mk_of_continuousAt (by fun_prop) (.prodUnique 𝕜 E _)
    (chartAt H y) (chartAt H y.val) (mem_chart_source H y) (mem_chart_source H y.val)
    (chart_mem_maximalAtlas y) (chart_mem_maximalAtlas y.val)
  intro x hx
  suffices I ((chartAt H ↑y) ((chartAt H y).symm (I.symm x))) = x by simpa +contextual
  simp_all

/-- Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`. -/
/-
**Manifold.IsImmersionAtOfComplement._root_.ModelWithCorners.isImmersionAtOfComp
lement** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsImmersionAtOfComplement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`.
-/
protected lemma _root_.ModelWithCorners.isImmersionAtOfComplement {n : ℕ} {x : H} :
    IsImmersionAtOfComplement PUnit I 𝓘(𝕜, E) n I x :=
  Manifold.IsImmersionAtOfComplement.mk_of_continuousAt I.continuousAt
    (.prodUnique _ _ _) (.refl _) (.refl _) (by simp) (by simp)
    (IsManifold.subset_maximalAtlas (by simp)) (IsManifold.subset_maximalAtlas (by simp))
    (by simp [Function.comp_def])

/-- Prefer using `IsImmersionAtOfComplement.continuousAt` instead -/
/-
**Manifold.IsImmersionAtOfComplement.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `Man
ifold.IsImmersionAtOfComplement`。
形式化陈述：continuousOn (h : IsImmersionAtOfComplement F I J n f x) : ContinuousOn f 
h.domChart.source
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.continuousOn_writtenInExtend_iff`：continuousOn_wri
ttenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M -> M'} (hs : s subset
eq f.source) (hmaps : MapsTo g s f'.source) …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Manifold.IsImmersionAtOfComplement.mapsto_domChart_source_codChart_sourc
e`：mapsto_domChart_source_codChart_source (h : IsImmersionAtOfComplement F I J n
 f x) : MapsTo f h.domChart.source h.codChart.source
· 使用定理 `OpenPartialHomeomorph.extend_target_eq_image_source`：extend_target_eq_im
age_source : (f.extend I).target = (f.extend I) '' f.source
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用引理 `Manifold.IsImmersionAtOfComplement.writtenInCharts`：writtenInCharts (h :
 IsImmersionAtOfComplement F I J n f x) : EqOn ((h.codChart.extend J) ∘ f ∘ (h.d
omChart.extend I).symm) (h.equiv ∘ (·, 0…

--- 原说明 ---
Prefer using `IsImmersionAtOfComplement.continuousAt` instead
-/
theorem continuousOn (h : IsImmersionAtOfComplement F I J n f x) :
    ContinuousOn f h.domChart.source := by
  rw [← h.domChart.continuousOn_writtenInExtend_iff le_rfl
      h.mapsto_domChart_source_codChart_source (I' := J) (I := I),
    ← h.domChart.extend_target_eq_image_source]
  have : ContinuousOn (h.equiv ∘ fun x ↦ (x, 0)) (h.domChart.extend I).target := by fun_prop
  exact this.congr h.writtenInCharts

/-- A `C^n` immersion at `x` is continuous at `x`. -/
/-
**Manifold.IsImmersionAtOfComplement.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `Man
ifold.IsImmersionAtOfComplement`。
形式化陈述：continuousAt (h : IsImmersionAtOfComplement F I J n f x) : ContinuousAt f 
x
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `Manifold.IsImmersionAtOfComplement.continuousOn`：continuousOn (h : IsImm
ersionAtOfComplement F I J n f x) : ContinuousOn f h.domChart.source
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用引理 `Manifold.IsImmersionAtOfComplement.mem_domChart_source`：mem_domChart_sou
rce (h : IsImmersionAtOfComplement F I J n f x) : x in h.domChart.source

--- 原说明 ---
A `C^n` immersion at `x` is continuous at `x`.
-/
theorem continuousAt (h : IsImmersionAtOfComplement F I J n f x) : ContinuousAt f x :=
  h.continuousOn.continuousAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

/-- Prefer using `IsImmersionAtOfComplement.contMDiffAt` instead -/
/-
**Manifold.IsImmersionAtOfComplement.contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 `Mani
fold.IsImmersionAtOfComplement`。
形式化陈述：contMDiffOn (h : IsImmersionAtOfComplement F I J n f x) : CMDiff[h.domChar
t.source] n f
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.contMDiffOn_writtenInExtend_iff`：OpenPartialHomeom
orph.contMDiffOn_writtenInExtend_iff (hφ : φ in maximalAtlas I n M) (hψ : ψ in m
aximalAtlas J n N) (hs : s subseteq φ.sourc…
· 使用引理 `Manifold.IsImmersionAtOfComplement.domChart_mem_maximalAtlas`：domChart_m
em_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) : h.domChart in IsMa
nifold.maximalAtlas I n M
· 使用引理 `Manifold.IsImmersionAtOfComplement.codChart_mem_maximalAtlas`：codChart_m
em_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) : h.codChart in IsMa
nifold.maximalAtlas J n N
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `Manifold.IsImmersionAtOfComplement.mapsto_domChart_source_codChart_sourc
e`：mapsto_domChart_source_codChart_source (h : IsImmersionAtOfComplement F I J n
 f x) : MapsTo f h.domChart.source h.codChart.source
· 使用定理 `OpenPartialHomeomorph.extend_target_eq_image_source`：extend_target_eq_im
age_source : (f.extend I).target = (f.extend I) '' f.source
· 使用定理 `contMDiff_iff_contDiff`：contMDiff_iff_contDiff {f : E -> E'} : ContMDiff
 𝓘(𝕜, E) 𝓘(𝕜, E') n f ↔ ContDiff 𝕜 n f
· 使用定理 `ContDiff.fun_comp`：ContDiff.fun_comp {g : F -> G} {f : E -> F} (hg : Con
tDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (fun x => g (f x))
· 使用定理 `ContinuousLinearEquiv.contDiff`：ContinuousLinearEquiv.contDiff (f : E ≃L
[𝕜] F) : ContDiff 𝕜 n f
· 使用定理 `contDiff_prodMk_left`：contDiff_prodMk_left (f₀ : F) : ContDiff 𝕜 n fun e
 : E => (e, f₀)
· 使用定理 `ContMDiffOn.congr`：ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : 
forall y in s, f₁ y = f y) : ContMDiffOn I I' n f₁ s
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用引理 `Manifold.IsImmersionAtOfComplement.writtenInCharts`：writtenInCharts (h :
 IsImmersionAtOfComplement F I J n f x) : EqOn ((h.codChart.extend J) ∘ f ∘ (h.d
omChart.extend I).symm) (h.equiv ∘ (·, 0…

--- 原说明 ---
Prefer using `IsImmersionAtOfComplement.contMDiffAt` instead
-/
theorem contMDiffOn (h : IsImmersionAtOfComplement F I J n f x) :
    CMDiff[h.domChart.source] n f := by
  rw [← h.domChart.contMDiffOn_writtenInExtend_iff h.domChart_mem_maximalAtlas
    h.codChart_mem_maximalAtlas le_rfl h.mapsto_domChart_source_codChart_source,
    ← h.domChart.extend_target_eq_image_source]
  have : CMDiff n (h.equiv ∘ fun x ↦ (x, 0)) := by
    rw [contMDiff_iff_contDiff]; fun_prop
  exact this.contMDiffOn.congr h.writtenInCharts

/-- A `C^n` immersion at `x` is `C^n` at `x`. -/
/-
**Manifold.IsImmersionAtOfComplement.contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 `Mani
fold.IsImmersionAtOfComplement`。
形式化陈述：contMDiffAt (h : IsImmersionAtOfComplement F I J n f x) : CMDiffAt n f x
参数：h : IsImmersionAtOfComplement F I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffOn.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `Manifold.IsImmersionAtOfComplement.contMDiffOn`：contMDiffOn (h : IsImmer
sionAtOfComplement F I J n f x) : CMDiff[h.domChart.source] n f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用引理 `Manifold.IsImmersionAtOfComplement.mem_domChart_source`：mem_domChart_sou
rce (h : IsImmersionAtOfComplement F I J n f x) : x in h.domChart.source

--- 原说明 ---
A `C^n` immersion at `x` is `C^n` at `x`.
-/
theorem contMDiffAt (h : IsImmersionAtOfComplement F I J n f x) : CMDiffAt n f x :=
  h.contMDiffOn.contMDiffAt (h.domChart.open_source.mem_nhds (mem_domChart_source h))

/-- Let `f : M → N` be a function, and suppose `φ : N → N'` is a `C^n` immersion at `f x`, such
that `φ ∘ f` is `C^n` at `x`. Let `x ∈ t ⊆ M` be contained in the slice chart at `f x`.
Then `f` seen in the slice chart at `φ (f x)` and the preferred chart at `x`
is `C^n` at (the image of) `x` within (the image of) `t`. -/
/-
**Manifold.IsImmersionAtOfComplement.aux** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsI
mmersionAtOfComplement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f : M → N` be a function, and suppose `φ : N → N'` is a `C^n` immersion at 
`f x`, such
that `φ ∘ f` is `C^n` at `x`. Let `x ∈ t ⊆ M` be contained in the slice chart at
 `f x`.
Then `f` seen in the slice chart at `φ (f x)` and the preferred chart at `x`
is `C^n` at (the image of) `x` within (the image of) `t`.
-/
private lemma aux {f : M → N} {φ : N → N'}
    (h : IsImmersionAtOfComplement F J J' n φ (f x)) (h' : CMDiffAt n (φ ∘ f) x)
    {t : Set M} (ht : t ⊆ f ⁻¹' h.domChart.source) (hxt : x ∈ t) :
    ContDiffWithinAt 𝕜 n ((h.domChart.extend J) ∘ f ∘ (extChartAt I x).symm)
      ((extChartAt I x).symm ⁻¹' t ∩ range I) ((extChartAt I x) x) := by
  -- Consider the local expressions of `f`, `φ`, `x` and `s'` in the charts we're considering.
  set f' := (h.domChart.extend J) ∘ f ∘ (extChartAt I x).symm
  set φ' := (h.codChart.extend J') ∘ φ ∘ (h.domChart.extend J).symm
  set x' := (extChartAt I x) x
  set s := (extChartAt I x).symm ⁻¹' t ∩ range I
  have hx' : extChartAt I x x ∈ s := ⟨by simp [mem_chart_source H x, hxt], mem_range_self _⟩
  have h'loc : ContDiffWithinAt 𝕜 n ((h.codChart.extend J') ∘ (φ ∘ f) ∘ (extChartAt I x).symm)
      ((extChartAt I x).symm ⁻¹' t ∩ range I) (extChartAt I x x) := by
    replace h' : CMDiffAt[t] n (φ ∘ f) x := h'.contMDiffWithinAt
    rw [contMDiffWithinAt_iff_of_mem_maximalAtlas' h.codChart_mem_maximalAtlas] at h'
    exacts [h'.2, h.mem_codChart_source]
  -- By hypothesis, `φ ∘ f` (read in our charts) is `C^n` at `x'` within `s`.
  have h'' : ContDiffWithinAt 𝕜 n (φ' ∘ f') s x' := by
    apply h'loc.congr_of_mem (fun y hy ↦ ?_) hx'
    simp only [mfld_simps, φ', f']
    rw [h.domChart.left_inv]
    apply ht hy.1
  -- On the other hand, composing `f'` with the inclusion `u ↦ (u, 0)` is also `C^n`
  -- (as a composition of `C^n` functions); this locally equals `φ ∘ f` in coordinates
  -- (since `f` is an immersion).
  set f'' := (h.equiv ∘ fun x ↦ (x, 0)) ∘ f'
  have h''' : ContDiffWithinAt 𝕜 n f'' s x' := by
    refine h''.congr_of_mem (fun y hy ↦ ?_) hx'
    simp only [f'', φ', f']
    nth_rw 2 [comp_apply]
    rw [Function.comp_apply, h.writtenInCharts]
    rw [h.domChart.extend_target_eq_image_source]
    exact ⟨(f ∘ (extChartAt I x).symm) y, ht hy.1, by simp⟩
  -- Composing with a suitable projection to cancel the inclusion, we deduce that `f` is `C^n`.
  have h'''' : ContDiffWithinAt 𝕜 n ((Prod.fst ∘ h.equiv.symm) ∘ f'') s x' :=
    ContDiffWithinAt.comp x' (by fun_prop) h''' (mapsTo_univ _ _)
  exact h''''.congr_of_mem (fun y hy ↦ by simp [f'']) hx'

/-- A function `f : M → N` between `C^n` manifolds is `C^n` at `x` if and only if it is continuous
at `x` and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` at `f x` is `C^n` at `x`. -/
/-
**Manifold.IsImmersionAtOfComplement._root_.ContMDiffAt.iff_comp_isImmersionAtOf
Complement** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsImmersionAtOfComplement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : M → N` between `C^n` manifolds is `C^n` at `x` if and only if it
 is continuous
at `x` and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` at `f x` 
is `C^n` at `x`.
-/
lemma _root_.ContMDiffAt.iff_comp_isImmersionAtOfComplement
    {f : M → N} {φ : N → N'} (hφ : IsImmersionAtOfComplement F J J' n φ (f x)) :
    -- Note: `φ` need not be inducing, so continuity of `φ ∘ f` at `x`
    -- generally does not imply continuity of `f`
    CMDiffAt n f x ↔ ContinuousAt f x ∧ CMDiffAt n (φ ∘ f) x := by
  refine ⟨fun hf ↦ ⟨hf.continuousAt, hφ.contMDiffAt.comp x hf⟩, fun ⟨hf, h'⟩ ↦ ?_⟩
  -- Since `f` is continuous at `x`, some neighbourhood `t` of `x` is mapped
  -- into `hφ.domChart.source` under `f`. By restriction, we may assume `t` is open,
  -- so it suffices to test smoothness on `t`.
  have : hφ.domChart.source ∈ 𝓝 (f x) := hφ.domChart.open_source.mem_nhds hφ.mem_domChart_source
  obtain ⟨t, ht, htopen, hxt⟩ := mem_nhds_iff.mp (hf this)
  suffices CMDiffAt[t] n f x from this.contMDiffAt <| htopen.mem_nhds hxt
  -- We test smoothness of `f` on `t` in the preferred chart at `x` and `hφ.codChart`.
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas'
    hφ.domChart_mem_maximalAtlas hφ.mem_domChart_source]
  refine ⟨hf.continuousWithinAt, ?_⟩
  exact aux hφ h' ht hxt

end IsImmersionAtOfComplement

namespace IsImmersionAt

/-
**Manifold.IsImmersionAt.mk_of_charts** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsImme
rsionAt`。
形式化陈述：mk_of_charts (equiv : (E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph
 M H) (codChart : OpenPartialHomeomorph N G) (hx : x in domChart.source) (hfx : 
f x in codChart.source) (hdomChart : domChart in IsManifold.maximalAtlas I n M) 
(hcodChart : codChart in IsManifold.maximalAtlas J n N) (hsource : domChart.sour
ce subseteq f ⁻¹' codChart.source) (hwrittenInExtend : EqOn ((codChart.extend J)
 ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0)) (domChart.extend I).target) : 
IsImmersionAt I J n f x
参数：equiv : (E × F) ≃L[𝕜] E''；domChart : OpenPartialHomeomorph M H；codChart : Ope
nPartialHomeomorph N G；hx : x in domChart.source；hfx : f x in codChart.source；hd
omChart : domChart in IsManifold.maximalAtlas I n M；hcodChart : codChart in IsMa
nifold.maximalAtlas J n N；hsource : domChart.source subseteq f ⁻¹' codChart.sour
ce；hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) 
(equiv ∘ (·, 0)) (domChart.extend I).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.mk_of_charts`：mk_of_charts (equiv : (
E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartial
Homeomorph N G) (hx : x in domChart.s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Manifold.IsImmersionAtOfComplement.congr_F`：congr_F (e : F ≃L[𝕜] F') : I
sImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F' I J n f x
-/
lemma mk_of_charts (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt I J n f x := by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
/-
**Manifold.IsImmersionAt.mk_of_continuousAt** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.
IsImmersionAt`。
形式化陈述：mk_of_continuousAt {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (
E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartial
Homeomorph N G) (hx : x in domChart.source) (hfx : f x in codChart.source) (hdom
Chart : domChart in IsManifold.maximalAtlas I n M) (hcodChart : codChart in IsMa
nifold.maximalAtlas J n N) (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (
domChart.extend I).symm) (equiv ∘ (·, 0)) (domChart.extend I).target) : IsImmers
ionAt I J n f x
参数：hf : ContinuousAt f x；equiv : (E × F) ≃L[𝕜] E''；domChart : OpenPartialHomeomo
rph M H；codChart : OpenPartialHomeomorph N G；hx : x in domChart.source；hfx : f x
 in codChart.source；hdomChart : domChart in IsManifold.maximalAtlas I n M；hcodCh
art : codChart in IsManifold.maximalAtlas J n N；hwrittenInExtend : EqOn ((codCha
rt.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0)) (domChart.extend I
).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.mk_of_continuousAt`：mk_of_continuousA
t {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'') (domC
hart : OpenPartialHomeomorph M H) (codChart…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Manifold.IsImmersionAtOfComplement.congr_F`：congr_F (e : F ≃L[𝕜] F') : I
sImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F' I J n f x

--- 原说明 ---
`f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` a
nd `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u 
↦ (u, 0)`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`.
-/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt I J n f x := by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
/-
**Manifold.IsImmersionAt.complement** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.IsImmers
ionAt`。
形式化陈述：complement (h : IsImmersionAt I J n f x) : Type u
参数：h : IsImmersionAt I J n f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of complement of the model normed space `E` of `M` in the model normed 
space
`E'` of `N`
-/
def complement (h : IsImmersionAt I J n f x) : Type u := Classical.choose h
/-
**Manifold.IsImmersionAt.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsImmersionAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance (h : IsImmersionAt I J n f x) : NormedAddCommGroup h.complement :=
  Classical.choose <| Classical.choose_spec h
/-
**Manifold.IsImmersionAt.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsImmersionAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance (h : IsImmersionAt I J n f x) : NormedSpace 𝕜 h.complement :=
  Classical.choose <| Classical.choose_spec <| Classical.choose_spec h
/-
**Manifold.IsImmersionAt.isImmersionAtOfComplement_complement** 是 Mathlib 中的一个引理
，位于命名空间 `Manifold.IsImmersionAt`。
形式化陈述：isImmersionAtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImm
ersionAtOfComplement h.complement I J n f x
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma isImmersionAtOfComplement_complement (h : IsImmersionAt I J n f x) :
    IsImmersionAtOfComplement h.complement I J n f x :=
  Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

/-- A choice of chart on the domain `M` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.codChart` and `h.codChart`. -/
/-
**Manifold.IsImmersionAt.domChart** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.IsImmersio
nAt`。
形式化陈述：domChart (h : IsImmersionAt I J n f x) : OpenPartialHomeomorph M H
参数：h : IsImmersionAt I J n f x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x

--- 原说明 ---
A choice of chart on the domain `M` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.codChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given b
y
`h.codChart` and `h.codChart`.
-/
def domChart (h : IsImmersionAt I J n f x) : OpenPartialHomeomorph M H :=
  h.isImmersionAtOfComplement_complement.domChart

/-- A choice of chart on the co-domain `N` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given by
`h.equiv` and `h.domChart`. -/
/-
**Manifold.IsImmersionAt.codChart** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.IsImmersio
nAt`。
形式化陈述：codChart (h : IsImmersionAt I J n f x) : OpenPartialHomeomorph N G
参数：h : IsImmersionAt I J n f x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x

--- 原说明 ---
A choice of chart on the co-domain `N` of an immersion `f` at `x`:
w.r.t. this chart and the data `h.domChart` and `h.equiv`,
`f` will look like an inclusion `u ↦ (u, 0)` in these extended charts.
The particular chart is arbitrary, but this choice matches the witnesses given b
y
`h.equiv` and `h.domChart`.
-/
def codChart (h : IsImmersionAt I J n f x) : OpenPartialHomeomorph N G :=
  h.isImmersionAtOfComplement_complement.codChart
/-
**Manifold.IsImmersionAt.mem_domChart_source** 是 Mathlib 中的一个引理，位于命名空间 `Manifold
.IsImmersionAt`。
形式化陈述：mem_domChart_source (h : IsImmersionAt I J n f x) : x in h.domChart.source
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.mem_domChart_source`：mem_domChart_sou
rce (h : IsImmersionAtOfComplement F I J n f x) : x in h.domChart.source
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x
-/
lemma mem_domChart_source (h : IsImmersionAt I J n f x) : x ∈ h.domChart.source :=
  h.isImmersionAtOfComplement_complement.mem_domChart_source
/-
**Manifold.IsImmersionAt.mem_codChart_source** 是 Mathlib 中的一个引理，位于命名空间 `Manifold
.IsImmersionAt`。
形式化陈述：mem_codChart_source (h : IsImmersionAt I J n f x) : f x in h.codChart.sour
ce
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.mem_codChart_source`：mem_codChart_sou
rce (h : IsImmersionAtOfComplement F I J n f x) : f x in h.codChart.source
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x
-/
lemma mem_codChart_source (h : IsImmersionAt I J n f x) : f x ∈ h.codChart.source :=
  h.isImmersionAtOfComplement_complement.mem_codChart_source
/-
**Manifold.IsImmersionAt.domChart_mem_maximalAtlas** 是 Mathlib 中的一个引理，位于命名空间 `Ma
nifold.IsImmersionAt`。
形式化陈述：domChart_mem_maximalAtlas (h : IsImmersionAt I J n f x) : h.domChart in Is
Manifold.maximalAtlas I n M
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.domChart_mem_maximalAtlas`：domChart_m
em_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) : h.domChart in IsMa
nifold.maximalAtlas I n M
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x
-/
lemma domChart_mem_maximalAtlas (h : IsImmersionAt I J n f x) :
    h.domChart ∈ IsManifold.maximalAtlas I n M :=
  h.isImmersionAtOfComplement_complement.domChart_mem_maximalAtlas
/-
**Manifold.IsImmersionAt.codChart_mem_maximalAtlas** 是 Mathlib 中的一个引理，位于命名空间 `Ma
nifold.IsImmersionAt`。
形式化陈述：codChart_mem_maximalAtlas (h : IsImmersionAt I J n f x) : h.codChart in Is
Manifold.maximalAtlas J n N
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.codChart_mem_maximalAtlas`：codChart_m
em_maximalAtlas (h : IsImmersionAtOfComplement F I J n f x) : h.codChart in IsMa
nifold.maximalAtlas J n N
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x
-/
lemma codChart_mem_maximalAtlas (h : IsImmersionAt I J n f x) :
    h.codChart ∈ IsManifold.maximalAtlas J n N :=
  h.isImmersionAtOfComplement_complement.codChart_mem_maximalAtlas
/-
**Manifold.IsImmersionAt.source_subset_preimage_source** 是 Mathlib 中的一个引理，位于命名空间
 `Manifold.IsImmersionAt`。
形式化陈述：source_subset_preimage_source (h : IsImmersionAt I J n f x) : h.domChart.s
ource subseteq f ⁻¹' h.codChart.source
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.source_subset_preimage_source`：source
_subset_preimage_source (h : IsImmersionAtOfComplement F I J n f x) : h.domChart
.source subseteq f ⁻¹' h.codChart.source
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x
-/
lemma source_subset_preimage_source (h : IsImmersionAt I J n f x) :
    h.domChart.source ⊆ f ⁻¹' h.codChart.source :=
  h.isImmersionAtOfComplement_complement.source_subset_preimage_source

/-- A linear equivalence `E × F ≃L[𝕜] E''` which belongs to the data of an immersion `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses given by
`h.domChart` and `h.codChart`. -/
/-
**Manifold.IsImmersionAt.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.IsImmersionAt
`。
形式化陈述：equiv (h : IsImmersionAt I J n f x) : (E × h.complement) ≃L[𝕜] E''
参数：h : IsImmersionAt I J n f x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x

--- 原说明 ---
A linear equivalence `E × F ≃L[𝕜] E''` which belongs to the data of an immersion
 `f` at `x`:
the particular equivalence is arbitrary, but this choice matches the witnesses g
iven by
`h.domChart` and `h.codChart`.
-/
def equiv (h : IsImmersionAt I J n f x) : (E × h.complement) ≃L[𝕜] E'' :=
  h.isImmersionAtOfComplement_complement.equiv
/-
**Manifold.IsImmersionAt.writtenInCharts** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsI
mmersionAt`。
形式化陈述：writtenInCharts (h : IsImmersionAt I J n f x) : EqOn ((h.codChart.extend J
) ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0)) (h.domChart.extend I).tar
get
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.writtenInCharts`：writtenInCharts (h :
 IsImmersionAtOfComplement F I J n f x) : EqOn ((h.codChart.extend J) ∘ f ∘ (h.d
omChart.extend I).symm) (h.equiv ∘ (·, 0…
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x
-/
lemma writtenInCharts (h : IsImmersionAt I J n f x) :
    EqOn ((h.codChart.extend J) ∘ f ∘ (h.domChart.extend I).symm) (h.equiv ∘ (·, 0))
      (h.domChart.extend I).target :=
  h.isImmersionAtOfComplement_complement.writtenInCharts
/-
**Manifold.IsImmersionAt.property** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsImmersio
nAt`。
形式化陈述：property (h : IsImmersionAt I J n f x) : LiftSourceTargetPropertyAt I J n 
f x (ImmersionAtProp h.complement I J M N)
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.property`：property (h : IsImmersionAt
OfComplement F I J n f x) : LiftSourceTargetPropertyAt I J n f x (ImmersionAtPro
p F I J M N)
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x
-/
lemma property (h : IsImmersionAt I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp h.complement I J M N) :=
  h.isImmersionAtOfComplement_complement.property

/--
If `f` is an immersion at `x`, it maps its domain chart's target to its codomain chart's target:
`(h.domChart.extend I).target` to `(h.domChart.extend J).target`.

Roig and Domingues' [roigdomingues1992] definition of immersions only asks for this inclusion
between the targets of the local charts: using mathlib's formalisation conventions, that condition
is *slightly* weaker than `source_subset_preimage_source`: the latter implies that
`h.codChart.extend J ∘ f` maps `h.domChart.source` to
`(h.codChart.extend J).target = (h.codChart.extend I) '' h.codChart.source`,
but that does *not* imply `f` maps `h.domChart.source` to `h.codChart.source`;
a priori `f` could map some point `f ∘ h.domChart.extend I x ∉ h.codChart.source` into the target.
Note that this difference only occurs because of our design using junk values;
this is not a mathematically meaningful difference.

At the same time, this condition is fairly weak: it is implied, for instance, by `f` being
continuous at `x` (see `mk_of_continuousAt`), which is easy to ascertain in practice.

See `target_subset_preimage_target` for a version stated using preimages instead of images.
-/
/-
**Manifold.IsImmersionAt.map_target_subset_target** 是 Mathlib 中的一个引理，位于命名空间 `Man
ifold.IsImmersionAt`。
形式化陈述：map_target_subset_target (h : IsImmersionAt I J n f x) : (h.equiv ∘ (·, 0)
) '' (h.domChart.extend I).target subseteq (h.codChart.extend J).target
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.map_target_subset_target`：map_target_
subset_target (h : IsImmersionAtOfComplement F I J n f x) : (h.equiv ∘ (·, 0)) '
' (h.domChart.extend I).target subseteq (h.codCha…
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x

--- 原说明 ---
If `f` is an immersion at `x`, it maps its domain chart's target to its codomain
 chart's target:
`(h.domChart.extend I).target` to `(h.domChart.extend J).target`.

Roig and Domingues' [roigdomingues1992] definition of immersions only asks for t
his inclusion
between the targets of the local charts: using mathlib's formalisation conventio
ns, that condition
is *slightly* weaker than `source_subset_preimage_source`: the latter implies th
at
`h.codChart.extend J ∘ f` maps `h.domChart.source` to
`(h.codChart.extend J).target = (h.codChart.extend I) '' h.codChart.source`,
but that does *not* imply `f` maps `h.domChart.source` to `h.codChart.source`;
a priori `f` could map some point `f ∘ h.domChart.extend I x ∉ h.codChart.source
` into the target.
Note that this difference only occurs because of our design using junk values;
this is not a mathematically meaningful difference.

At the same time, this condition is fairly weak: it is implied, for instance, by
 `f` being
continuous at `x` (see `mk_of_continuousAt`), which is easy to ascertain in prac
tice.

See `target_subset_preimage_target` for a version stated using preimages instead
 of images.
-/
lemma map_target_subset_target (h : IsImmersionAt I J n f x) :
    (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).target ⊆ (h.codChart.extend J).target :=
  h.isImmersionAtOfComplement_complement.map_target_subset_target

/-- If `f` is an immersion at `x`, its domain chart's target `(h.domChart.extend I).target`
is mapped to its codomain chart's target `(h.domChart.extend J).target`:
see `map_target_subset_target` for a version stated using images. -/
/-
**Manifold.IsImmersionAt.target_subset_preimage_target** 是 Mathlib 中的一个引理，位于命名空间
 `Manifold.IsImmersionAt`。
形式化陈述：target_subset_preimage_target (h : IsImmersionAt I J n f x) : (h.domChart.
extend I).target subseteq (h.equiv ∘ (·, 0)) ⁻¹' (h.codChart.extend J).target
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAt.map_target_subset_target`：map_target_subset_targe
t (h : IsImmersionAt I J n f x) : (h.equiv ∘ (·, 0)) '' (h.domChart.extend I).ta
rget subseteq (h.codChart.extend J).t…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
If `f` is an immersion at `x`, its domain chart's target `(h.domChart.extend I).
target`
is mapped to its codomain chart's target `(h.domChart.extend J).target`:
see `map_target_subset_target` for a version stated using images.
-/
lemma target_subset_preimage_target (h : IsImmersionAt I J n f x) :
    (h.domChart.extend I).target ⊆ (h.equiv ∘ (·, 0)) ⁻¹' (h.codChart.extend J).target :=
  fun _x hx ↦ h.map_target_subset_target (mem_image_of_mem _ hx)

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
/-
**Manifold.IsImmersionAt.congr_of_eventuallyEq** 是 Mathlib 中的一个引理，位于命名空间 `Manifo
ld.IsImmersionAt`。
形式化陈述：congr_of_eventuallyEq (hf : IsImmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
 IsImmersionAt I J n g x
参数：hf : IsImmersionAt I J n f x；hfg : f =ᶠ[𝓝 x] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.congr_of_eventuallyEq`：congr_of_event
uallyEq (hf : IsImmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) : IsImm
ersionAtOfComplement F I J n g x
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x

--- 原说明 ---
If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`.
-/
lemma congr_of_eventuallyEq (hf : IsImmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt I J n g x := by
  use hf.complement, by infer_instance, by infer_instance
  exact hf.isImmersionAtOfComplement_complement.congr_of_eventuallyEq hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is an immersion at `x` if and only if `g` is an immersion at `x`. -/
/-
**Manifold.IsImmersionAt.congr_iff** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsImmersi
onAt`。
形式化陈述：congr_iff (hfg : f =ᶠ[𝓝 x] g) : IsImmersionAt I J n f x ↔ IsImmersionAt I 
J n g x
参数：hfg : f =ᶠ[𝓝 x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAt.congr_of_eventuallyEq`：congr_of_eventuallyEq (hf 
: IsImmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) : IsImmersionAt I J n g x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
If `f = g` on some neighbourhood of `x`,
then `f` is an immersion at `x` if and only if `g` is an immersion at `x`.
-/
lemma congr_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt I J n f x ↔ IsImmersionAt I J n g x :=
  ⟨fun h ↦ h.congr_of_eventuallyEq hfg, fun h ↦ h.congr_of_eventuallyEq hfg.symm⟩

/- The set of points where `IsImmersionAt` holds is open. -/
/-
**Manifold.IsImmersionAt._root_.IsOpen.isImmersionAt** 是 Mathlib 中的一个引理，位于命名空间 `
Manifold.IsImmersionAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of points where `IsImmersionAt` holds is open.
-/
lemma _root_.IsOpen.isImmersionAt :
    IsOpen {x | IsImmersionAt I J n f x} := by
  rw [isOpen_iff_forall_mem_open]
  exact fun x hx ↦ ⟨{x | IsImmersionAtOfComplement hx.complement I J n f x },
    fun y hy ↦ hy.isImmersionAt, .isImmersionAtOfComplement,
    by simp [hx.isImmersionAtOfComplement_complement]⟩

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
/-
**Manifold.IsImmersionAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsImmersion
At`。
形式化陈述：prodMap {f : M -> N} {g : M' -> N'} {x' : M'} [IsManifold I n M] [IsManifo
ld I' n M'] [IsManifold J n N] [IsManifold J' n N'] (hf : IsImmersionAt I J n f 
x) (hg : IsImmersionAt I' J' n g x') : IsImmersionAt (I.prod I') (J.prod J') n (
Prod.map f g) (x, x')
参数：hf : IsImmersionAt I J n f x；hg : IsImmersionAt I' J' n g x'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.isImmersionAt`：isImmersionAt (h : IsI
mmersionAtOfComplement F I J n f x) : IsImmersionAt I J n f x
· 使用定理 `Manifold.IsImmersionAtOfComplement.prodMap`：prodMap {f : M -> N} {g : M'
 -> N'} {x' : M'} [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [Is
Manifold J' n N'] (hf : IsImmers…
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x

--- 原说明 ---
If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`.
-/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersionAt I J n f x) (hg : IsImmersionAt I' J' n g x') :
    IsImmersionAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') :=
  hf.isImmersionAtOfComplement_complement.prodMap hg.isImmersionAtOfComplement_complement
    |>.isImmersionAt

/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion at every point. -/
/-
**Manifold.IsImmersionAt.of_opens** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsImmersio
nAt`。
形式化陈述：of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) (hx : x in s) :
 IsImmersionAt I I n (Subtype.val : s -> M) ⟨x, hx⟩
参数：s : TopologicalSpace.Opens M；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.of_opens`：of_opens [IsManifold I n M]
 (s : TopologicalSpace.Opens M) (y : s) : IsImmersionAtOfComplement PUnit I I n 
(Subtype.val : s -> M) y

--- 原说明 ---
The inclusion of an open subset `s` of a smooth manifold `M` is an immersion at 
every point.
-/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) (hx : x ∈ s) :
    IsImmersionAt I I n (Subtype.val : s → M) ⟨x, hx⟩ := by
  use PUnit, by infer_instance, by infer_instance
  apply Manifold.IsImmersionAtOfComplement.of_opens

/-- Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`. -/
/-
**Manifold.IsImmersionAt._root_.ModelWithCorners.isImmersionAt** 是 Mathlib 中的一个引
理，位于命名空间 `Manifold.IsImmersionAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`.
-/
protected lemma _root_.ModelWithCorners.isImmersionAt {n : ℕ} {x : H} :
    IsImmersionAt I (modelWithCornersSelf 𝕜 E) n I x := by
  use PUnit, by infer_instance, by infer_instance
  exact I.isImmersionAtOfComplement

/-- Prefer using `IsImmersionAt.continuousAt` instead -/
/-
**Manifold.IsImmersionAt.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsImme
rsionAt`。
形式化陈述：continuousOn (h : IsImmersionAt I J n f x) : ContinuousOn f h.domChart.sou
rce
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsImmersionAtOfComplement.continuousOn`：continuousOn (h : IsImm
ersionAtOfComplement F I J n f x) : ContinuousOn f h.domChart.source
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x

--- 原说明 ---
Prefer using `IsImmersionAt.continuousAt` instead
-/
theorem continuousOn (h : IsImmersionAt I J n f x) : ContinuousOn f h.domChart.source :=
  h.isImmersionAtOfComplement_complement.continuousOn

/-- A `C^n` immersion at `x` is continuous at `x`. -/
/-
**Manifold.IsImmersionAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsImme
rsionAt`。
形式化陈述：continuousAt (h : IsImmersionAt I J n f x) : ContinuousAt f x
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsImmersionAtOfComplement.continuousAt`：continuousAt (h : IsImm
ersionAtOfComplement F I J n f x) : ContinuousAt f x
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x

--- 原说明 ---
A `C^n` immersion at `x` is continuous at `x`.
-/
theorem continuousAt (h : IsImmersionAt I J n f x) : ContinuousAt f x :=
  h.isImmersionAtOfComplement_complement.continuousAt

/-- Prefer using `IsImmersionAt.contMDiffAt` instead -/
/-
**Manifold.IsImmersionAt.contMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsImmer
sionAt`。
形式化陈述：contMDiffOn (h : IsImmersionAt I J n f x) : CMDiff[h.domChart.source] n f
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsImmersionAtOfComplement.contMDiffOn`：contMDiffOn (h : IsImmer
sionAtOfComplement F I J n f x) : CMDiff[h.domChart.source] n f
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x

--- 原说明 ---
Prefer using `IsImmersionAt.contMDiffAt` instead
-/
theorem contMDiffOn (h : IsImmersionAt I J n f x) : CMDiff[h.domChart.source] n f :=
  h.isImmersionAtOfComplement_complement.contMDiffOn

/-- A `C^n` immersion at `x` is `C^n` at `x`. -/
/-
**Manifold.IsImmersionAt.contMDiffAt** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsImmer
sionAt`。
形式化陈述：contMDiffAt (h : IsImmersionAt I J n f x) : CMDiffAt n f x
参数：h : IsImmersionAt I J n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsImmersionAtOfComplement.contMDiffAt`：contMDiffAt (h : IsImmer
sionAtOfComplement F I J n f x) : CMDiffAt n f x
· 使用引理 `Manifold.IsImmersionAt.isImmersionAtOfComplement_complement`：isImmersion
AtOfComplement_complement (h : IsImmersionAt I J n f x) : IsImmersionAtOfComplem
ent h.complement I J n f x

--- 原说明 ---
A `C^n` immersion at `x` is `C^n` at `x`.
-/
theorem contMDiffAt (h : IsImmersionAt I J n f x) : CMDiffAt n f x :=
  h.isImmersionAtOfComplement_complement.contMDiffAt

/-- A function `f : M → N` between `C^n` manifolds is `C^n` at `x` if and only if it is continuous
at `x` and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` at `f x` is `C^n` at `x`. -/
/-
**Manifold.IsImmersionAt._root_.ContMDiffAt.iff_comp_isImmersionAt** 是 Mathlib 中
的一个引理，位于命名空间 `Manifold.IsImmersionAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : M → N` between `C^n` manifolds is `C^n` at `x` if and only if it
 is continuous
at `x` and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` at `f x` 
is `C^n` at `x`.
-/
lemma _root_.ContMDiffAt.iff_comp_isImmersionAt {f : M → N} {φ : N → N'}
    (hφ : IsImmersionAt J J' n φ (f x)) :
    -- Note: `φ` need not be inducing, so continuity of `φ ∘ f` at `x`
    -- generally does not imply continuity of `f`
    CMDiffAt n f x ↔ ContinuousAt f x ∧ CMDiffAt n (φ ∘ f) x := by
  rw [← ContMDiffAt.iff_comp_isImmersionAtOfComplement hφ.isImmersionAtOfComplement_complement]

end IsImmersionAt

variable (F I J n) in
/-- `f : M → N` is a `C^n` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

In other words, `f` is an immersion at each `x ∈ M`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`.
-/
@[expose]
/-
**Manifold.IsImmersionOfComplement** 是 Mathlib 中的一个定义，位于命名空间 `Manifold`。
形式化陈述：IsImmersionOfComplement (f : M -> N) : Prop
参数：f : M -> N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : M → N` is a `C^n` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

In other words, `f` is an immersion at each `x ∈ M`.

This definition has a fixed parameter `F`, which is a choice of complement of `E
` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F
` and `E'`.
-/
def IsImmersionOfComplement (f : M → N) : Prop := ∀ x, IsImmersionAtOfComplement F I J n f x

variable (I J n) in
/-- `f : M → N` is a `C^n` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`:
being an immersion includes a choice of linear isomorphism between `E × F` and `E'`, which is where
the choice of `F` enters. If you need stronger control over the complement `F`,
use `IsImmersionOfComplement` instead.

Note that our global choice of complement is a bit stronger than asking `f` to be an immersion at
each `x ∈ M` w.r.t. potentially varying complements: see `isImmersionAt` for details.
-/
/-
**Manifold.IsImmersion** 是 Mathlib 中的一个定义，位于命名空间 `Manifold`。
形式化陈述：IsImmersion (f : M -> N) : Prop
参数：f : M -> N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : M → N` is a `C^n` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

Implicit in this definition is an abstract choice `F` of a complement of `E` in 
`E'`:
being an immersion includes a choice of linear isomorphism between `E × F` and `
E'`, which is where
the choice of `F` enters. If you need stronger control over the complement `F`,
use `IsImmersionOfComplement` instead.

Note that our global choice of complement is a bit stronger than asking `f` to b
e an immersion at
each `x ∈ M` w.r.t. potentially varying complements: see `isImmersionAt` for det
ails.
-/
def IsImmersion (f : M → N) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F), IsImmersionOfComplement F I J n f

namespace IsImmersionOfComplement

variable {f g : M → N}

/-- If `f` is an immersion, it is an immersion at each point. -/
/-
**Manifold.IsImmersionOfComplement.isImmersionAt** 是 Mathlib 中的一个引理，位于命名空间 `Mani
fold.IsImmersionOfComplement`。
形式化陈述：isImmersionAt (h : IsImmersionOfComplement F I J n f) (x : M) : IsImmersio
nAtOfComplement F I J n f x
参数：h : IsImmersionOfComplement F I J n f；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is an immersion, it is an immersion at each point.
-/
lemma isImmersionAt (h : IsImmersionOfComplement F I J n f) (x : M) :
    IsImmersionAtOfComplement F I J n f x := h x

/-- If `f = g` and `f` is an immersion, so is `g`. -/
/-
**Manifold.IsImmersionOfComplement.congr** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsI
mmersionOfComplement`。
形式化陈述：congr (h : IsImmersionOfComplement F I J n f) (heq : f = g) : IsImmersionO
fComplement F I J n g
参数：h : IsImmersionOfComplement F I J n f；heq : f = g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f = g` and `f` is an immersion, so is `g`.
-/
theorem congr (h : IsImmersionOfComplement F I J n f) (heq : f = g) :
    IsImmersionOfComplement F I J n g :=
  heq ▸ h
/-
**Manifold.IsImmersionOfComplement.trans_F** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.I
sImmersionOfComplement`。
形式化陈述：trans_F (h : IsImmersionOfComplement F I J n f) (e : F ≃L[𝕜] F') : IsImmer
sionOfComplement F' I J n f
参数：h : IsImmersionOfComplement F I J n f；e : F ≃L[𝕜] F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.trans_F`：trans_F (h : IsImmersionAtOf
Complement F I J n f x) (e : F ≃L[𝕜] F') : IsImmersionAtOfComplement F' I J n f 
x
-/
lemma trans_F (h : IsImmersionOfComplement F I J n f) (e : F ≃L[𝕜] F') :
    IsImmersionOfComplement F' I J n f :=
  fun x ↦ (h x).trans_F e

/-- Being an immersion w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
/-
**Manifold.IsImmersionOfComplement.congr_F** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.I
sImmersionOfComplement`。
形式化陈述：congr_F (e : F ≃L[𝕜] F') : IsImmersionOfComplement F I J n f ↔ IsImmersion
OfComplement F' I J n f
参数：e : F ≃L[𝕜] F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionOfComplement.trans_F`：trans_F (h : IsImmersionOfComp
lement F I J n f) (e : F ≃L[𝕜] F') : IsImmersionOfComplement F' I J n f

--- 原说明 ---
Being an immersion w.r.t. `F` is stable under replacing `F` by an isomorphic cop
y.
-/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsImmersionOfComplement F I J n f ↔ IsImmersionOfComplement F' I J n f :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'` (w.r.t. `F` and `F'`),
respectively, then `f × g: M × N → M' × N'` is an immersion at `(x, x')` w.r.t. `F × F'`. -/
/-
**Manifold.IsImmersionOfComplement.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.I
sImmersionOfComplement`。
形式化陈述：prodMap {f : M -> N} {g : M' -> N'} [IsManifold I n M] [IsManifold I' n M'
] [IsManifold J n N] [IsManifold J' n N'] (h : IsImmersionOfComplement F I J n f
) (h' : IsImmersionOfComplement F' I' J' n g) : IsImmersionOfComplement (F × F')
 (I.prod I') (J.prod J') n (Prod.map f g)
参数：h : IsImmersionOfComplement F I J n f；h' : IsImmersionOfComplement F' I' J' n
 g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsImmersionAtOfComplement.prodMap`：prodMap {f : M -> N} {g : M'
 -> N'} {x' : M'} [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [Is
Manifold J' n N'] (hf : IsImmers…

--- 原说明 ---
If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'` (w.r.t. `F` and `F
'`),
respectively, then `f × g: M × N → M' × N'` is an immersion at `(x, x')` w.r.t. 
`F × F'`.
-/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (h : IsImmersionOfComplement F I J n f) (h' : IsImmersionOfComplement F' I' J' n g) :
    IsImmersionOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun ⟨x, x'⟩ ↦ (h x).prodMap (h' x')

/-- If `f` is an immersion w.r.t. some complement `F`, it is an immersion.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being an immersion requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`.
-/
/-
**Manifold.IsImmersionOfComplement.isImmersion** 是 Mathlib 中的一个引理，位于命名空间 `Manifo
ld.IsImmersionOfComplement`。
形式化陈述：isImmersion (h : IsImmersionOfComplement F I J n f) : IsImmersion I J n f
参数：h : IsImmersionOfComplement F I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Geometry.Manifold.Immersion.0.Manifold.IsImmersion.eq_1
`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} {E'' : Type
 u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Manifold.IsImmersionOfComplement.congr_F`：congr_F (e : F ≃L[𝕜] F') : IsI
mmersionOfComplement F I J n f ↔ IsImmersionOfComplement F' I J n f

--- 原说明 ---
If `f` is an immersion w.r.t. some complement `F`, it is an immersion.

Note that the proof contains a small formalisation-related subtlety: `F` can liv
e in any universe,
while being an immersion requires the existence of a complement in the same univ
erse as
the model normed space of `N`. This is solved by `smallComplement` and `smallEqu
iv`.
-/
lemma isImmersion (h : IsImmersionOfComplement F I J n f) : IsImmersion I J n f := by
  by_cases! hM : IsEmpty M
  · rw [IsImmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x ↦ (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionOfComplement.congr_F (h x).smallEquiv).mp h

open IsManifold in
/-- The identity map is an immersion with complement `PUnit`. -/
/-
**Manifold.IsImmersionOfComplement.id** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsImme
rsionOfComplement`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_7} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_11}   [inst_4 : Topo
logicalSpace M] [inst_5 : ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M],
   Manifold.IsImmersionOfComplement PUnit.{u_15 + 1} I I n id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.mk_of_continuousAt`：mk_of_continuousA
t {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'') (domC
hart : OpenPartialHomeomorph M H) (codChart…
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
The identity map is an immersion with complement `PUnit`.
-/
protected lemma id [IsManifold I n M] : IsImmersionOfComplement PUnit I I n (@id M) := by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (continuousAt_id) (.prodUnique 𝕜 E _)
    (chartAt H x) (chartAt H x) (mem_chart_source H x) (mem_chart_source H x)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x)
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
  simpa

/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion. -/
/-
**Manifold.IsImmersionOfComplement.of_opens** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.
IsImmersionOfComplement`。
形式化陈述：of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) : IsImmersionOf
Complement PUnit I I n (Subtype.val : s -> M)
参数：s : TopologicalSpace.Opens M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.of_opens`：of_opens [IsManifold I n M]
 (s : TopologicalSpace.Opens M) (y : s) : IsImmersionAtOfComplement PUnit I I n 
(Subtype.val : s -> M) y

--- 原说明 ---
The inclusion of an open subset `s` of a smooth manifold `M` is an immersion.
-/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsImmersionOfComplement PUnit I I n (Subtype.val : s → M) :=
  fun y ↦ IsImmersionAtOfComplement.of_opens s y

/-- Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`. -/
/-
**Manifold.IsImmersionOfComplement._root_.ModelWithCorners.isImmersionOfCompleme
nt** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsImmersionOfComplement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`.
-/
protected lemma _root_.ModelWithCorners.isImmersionOfComplement {n : ℕ} :
    IsImmersionOfComplement PUnit I (modelWithCornersSelf 𝕜 E) n I :=
  fun _ ↦ I.isImmersionAtOfComplement

/-- Given `C^n` manifolds `M` and `N` over the same model `I`,
`Sum.inl : M → M ⊕ N` is a `C^n` immersion with complement `Unit` -/
/-
**Manifold.IsImmersionOfComplement.sumInl** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.Is
ImmersionOfComplement`。
形式化陈述：sumInl {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold 
I n M] [IsManifold I n M'] : IsImmersionOfComplement Unit I I n (@Sum.inl M M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.mk_of_continuousAt`：mk_of_continuousA
t {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'') (domC
hart : OpenPartialHomeomorph M H) (codChart…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_inl`：continuous_inl : Continuous (@inl X Y)
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
· 使用定理 `sum_chartAt_inl_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…

--- 原说明 ---
Given `C^n` manifolds `M` and `N` over the same model `I`,
`Sum.inl : M → M ⊕ N` is a `C^n` immersion with complement `Unit`
-/
lemma sumInl {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I n M]
    [IsManifold I n M'] : IsImmersionOfComplement Unit I I n (@Sum.inl M M') := by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (equiv := (.prodUnique 𝕜 E _))
    (by fun_prop) _ _ (mem_chart_source H x) (mem_chart_source H (Sum.inl x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (Sum.inl x))
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
  simpa

/-- Given `C^n` manifolds `M` and `N` over the same model `I`,
`Sum.inr : N → M ⊕ N` is a `C^n` immersion with complement `Unit` -/
/-
**Manifold.IsImmersionOfComplement.sumInr** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.Is
ImmersionOfComplement`。
形式化陈述：sumInr {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold 
I n M] [IsManifold I n M'] : IsImmersionOfComplement Unit I I n (@Sum.inr M M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionAtOfComplement.mk_of_continuousAt`：mk_of_continuousA
t {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'') (domC
hart : OpenPartialHomeomorph M H) (codChart…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_inr`：continuous_inr : Continuous (@inr X Y)
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
· 使用定理 `sum_chartAt_inr_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…

--- 原说明 ---
Given `C^n` manifolds `M` and `N` over the same model `I`,
`Sum.inr : N → M ⊕ N` is a `C^n` immersion with complement `Unit`
-/
lemma sumInr {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I n M]
    [IsManifold I n M'] : IsImmersionOfComplement Unit I I n (@Sum.inr M M') := by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt (equiv := (.prodUnique 𝕜 E _))
    (by fun_prop) _ _ (mem_chart_source H x) (mem_chart_source H (Sum.inr x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (Sum.inr x))
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
  simpa

/-- A `C^n` immersion is `C^n`. -/
/-
**Manifold.IsImmersionOfComplement.contMDiff** 是 Mathlib 中的一个定理，位于命名空间 `Manifold
.IsImmersionOfComplement`。
形式化陈述：contMDiff (h : IsImmersionOfComplement F I J n f) : CMDiff n f
参数：h : IsImmersionOfComplement F I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsImmersionAtOfComplement.contMDiffAt`：contMDiffAt (h : IsImmer
sionAtOfComplement F I J n f x) : CMDiffAt n f x

--- 原说明 ---
A `C^n` immersion is `C^n`.
-/
theorem contMDiff (h : IsImmersionOfComplement F I J n f) : CMDiff n f :=
  fun x ↦ (h x).contMDiffAt

/-- A function `f : M → N` between `C^n` manifolds is `C^n` if and only if it is continuous
and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` is `C^n`. -/
/-
**Manifold.IsImmersionOfComplement._root_.ContMDiff.iff_comp_isImmersionOfComple
ment** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsImmersionOfComplement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : M → N` between `C^n` manifolds is `C^n` if and only if it is con
tinuous
and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` is `C^n`.
-/
lemma _root_.ContMDiff.iff_comp_isImmersionOfComplement {f : M → N} {φ : N → N'}
    (hφ : IsImmersionOfComplement F J J' n φ) :
    CMDiff n f ↔ Continuous f ∧ CMDiff n (φ ∘ f) := by
  refine ⟨fun h ↦ ⟨h.continuous, hφ.contMDiff.comp h⟩, fun ⟨h, h'⟩ x ↦ ?_⟩
  rw [ContMDiffAt.iff_comp_isImmersionAtOfComplement (hφ (f x))]
  exact ⟨h.continuousAt, h' x⟩

end IsImmersionOfComplement

namespace IsImmersion

variable {f g : M → N}

/-- A choice of complement of the model normed space `E` of `M` in the model normed space
`E'` of `N` -/
/-
**Manifold.IsImmersion.complement** 是 Mathlib 中的一个定义，位于命名空间 `Manifold.IsImmersio
n`。
形式化陈述：complement (h : IsImmersion I J n f) : Type u
参数：h : IsImmersion I J n f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of complement of the model normed space `E` of `M` in the model normed 
space
`E'` of `N`
-/
def complement (h : IsImmersion I J n f) : Type u := Classical.choose h
/-
**Manifold.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance (h : IsImmersion I J n f) : NormedAddCommGroup h.complement :=
  Classical.choose <| Classical.choose_spec h
/-
**Manifold.IsImmersion.** 是 Mathlib 中的一个实例，位于命名空间 `Manifold.IsImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance (h : IsImmersion I J n f) : NormedSpace 𝕜 h.complement :=
  Classical.choose <| Classical.choose_spec <| Classical.choose_spec h
/-
**Manifold.IsImmersion.isImmersionOfComplement_complement** 是 Mathlib 中的一个引理，位于命
名空间 `Manifold.IsImmersion`。
形式化陈述：isImmersionOfComplement_complement (h : IsImmersion I J n f) : IsImmersion
OfComplement h.complement I J n f
参数：h : IsImmersion I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma isImmersionOfComplement_complement (h : IsImmersion I J n f) :
    IsImmersionOfComplement h.complement I J n f :=
  Classical.choose_spec <| Classical.choose_spec <| Classical.choose_spec h

/-- If `f` is an immersion, it is an immersion at each point.

Note that the converse statement is false in general:
if `f` is an immersion at each `x`, but with the choice of complement possibly depending on `x`,
there need not be a global choice of complement for which `f` is an immersion at each point.
The complement of `f` at `x` is isomorphic to the cokernel of `mfderiv I J f x`, but the `mfderiv`
of `f` at (even nearby) points `x` and `x'` are not directly related. They have the same rank
(the dimension of `E`, as will follow from injectivity), but if `E''` is infinite-dimensional this
is not conclusive. If `E''` is infinite-dimensional, this dimension can indeed change between
different connected components of `M`.
-/
/-
**Manifold.IsImmersion.isImmersionAt** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsImmer
sion`。
形式化陈述：isImmersionAt (h : IsImmersion I J n f) (x : M) : IsImmersionAt I J n f x
参数：h : IsImmersion I J n f；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Geometry.Manifold.Immersion.0.Manifold.IsImmersionAt.eq
_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} {E'' : Ty
pe u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 …
· 使用引理 `Manifold.IsImmersion.isImmersionOfComplement_complement`：isImmersionOfCo
mplement_complement (h : IsImmersion I J n f) : IsImmersionOfComplement h.comple
ment I J n f

--- 原说明 ---
If `f` is an immersion, it is an immersion at each point.

Note that the converse statement is false in general:
if `f` is an immersion at each `x`, but with the choice of complement possibly d
epending on `x`,
there need not be a global choice of complement for which `f` is an immersion at
 each point.
The complement of `f` at `x` is isomorphic to the cokernel of `mfderiv I J f x`,
 but the `mfderiv`
of `f` at (even nearby) points `x` and `x'` are not directly related. They have 
the same rank
(the dimension of `E`, as will follow from injectivity), but if `E''` is infinit
e-dimensional this
is not conclusive. If `E''` is infinite-dimensional, this dimension can indeed c
hange between
different connected components of `M`.
-/
lemma isImmersionAt (h : IsImmersion I J n f) (x : M) : IsImmersionAt I J n f x := by
  rw [IsImmersionAt]
  use h.complement, by infer_instance, by infer_instance
  exact h.isImmersionOfComplement_complement x

/-- If `f = g` and `f` is an immersion, so is `g`. -/
/-
**Manifold.IsImmersion.congr** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsImmersion`。
形式化陈述：congr (h : IsImmersion I J n f) (heq : f = g) : IsImmersion I J n g
参数：h : IsImmersion I J n f；heq : f = g。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f = g` and `f` is an immersion, so is `g`.
-/
theorem congr (h : IsImmersion I J n f) (heq : f = g) : IsImmersion I J n g :=
  heq ▸ h

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
/-
**Manifold.IsImmersion.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsImmersion`。
形式化陈述：prodMap {f : M -> N} {g : M' -> N'} [IsManifold I n M] [IsManifold I' n M'
] [IsManifold J n N] [IsManifold J' n N'] (hf : IsImmersion I J n f) (hg : IsImm
ersion I' J' n g) : IsImmersion (I.prod I') (J.prod J') n (Prod.map f g)
参数：hf : IsImmersion I J n f；hg : IsImmersion I' J' n g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionOfComplement.isImmersion`：isImmersion (h : IsImmersi
onOfComplement F I J n f) : IsImmersion I J n f
· 使用定理 `Manifold.IsImmersionOfComplement.prodMap`：prodMap {f : M -> N} {g : M' -
> N'} [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' 
n N'] (h : IsImmersionOfComple…
· 使用引理 `Manifold.IsImmersion.isImmersionOfComplement_complement`：isImmersionOfCo
mplement_complement (h : IsImmersion I J n f) : IsImmersionOfComplement h.comple
ment I J n f

--- 原说明 ---
If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`.
-/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersion I J n f) (hg : IsImmersion I' J' n g) :
    IsImmersion (I.prod I') (J.prod J') n (Prod.map f g) :=
  (hf.isImmersionOfComplement_complement.prodMap hg.isImmersionOfComplement_complement).isImmersion

open IsManifold in
/-- The identity map is an immersion. -/
/-
**Manifold.IsImmersion.id** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsImmersion`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_7} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_11}   [inst_4 : Topo
logicalSpace M] [inst_5 : ChartedSpace H M] {n : WithTop ℕ∞} [IsManifold I n M],
   Manifold.IsImmersion I I n id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsImmersionOfComplement.id`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
The identity map is an immersion.
-/
protected lemma id [IsManifold I n M] : IsImmersion I I n (@id M) := by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.id

/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion. -/
/-
**Manifold.IsImmersion.of_opens** 是 Mathlib 中的一个引理，位于命名空间 `Manifold.IsImmersion`
。
形式化陈述：of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) : IsImmersion I
 I n (Subtype.val : s -> M)
参数：s : TopologicalSpace.Opens M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Manifold.IsImmersionOfComplement.of_opens`：of_opens [IsManifold I n M] (
s : TopologicalSpace.Opens M) : IsImmersionOfComplement PUnit I I n (Subtype.val
 : s -> M)

--- 原说明 ---
The inclusion of an open subset `s` of a smooth manifold `M` is an immersion.
-/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsImmersion I I n (Subtype.val : s → M) := by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.of_opens s

/-- Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`. -/
/-
**Manifold.IsImmersion._root_.ModelWithCorners.isImmersion** 是 Mathlib 中的一个引理，位于
命名空间 `Manifold.IsImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`.
-/
protected lemma _root_.ModelWithCorners.isImmersion {n : ℕ} :
    IsImmersion I (modelWithCornersSelf 𝕜 E) n I := by
  use PUnit, by infer_instance, by infer_instance
  exact I.isImmersionOfComplement

/-- A `C^n` immersion is `C^n`. -/
/-
**Manifold.IsImmersion.contMDiff** 是 Mathlib 中的一个定理，位于命名空间 `Manifold.IsImmersion
`。
形式化陈述：contMDiff (h : IsImmersion I J n f) : CMDiff n f
参数：h : IsImmersion I J n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Manifold.IsImmersionOfComplement.contMDiff`：contMDiff (h : IsImmersionOf
Complement F I J n f) : CMDiff n f
· 使用引理 `Manifold.IsImmersion.isImmersionOfComplement_complement`：isImmersionOfCo
mplement_complement (h : IsImmersion I J n f) : IsImmersionOfComplement h.comple
ment I J n f

--- 原说明 ---
A `C^n` immersion is `C^n`.
-/
theorem contMDiff
    (h : IsImmersion I J n f) : CMDiff n f :=
  h.isImmersionOfComplement_complement.contMDiff

/-- A function `f : M → N` between `C^n` manifolds is `C^n` if and only if it is continuous
and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` is `C^n`. -/
/-
**Manifold.IsImmersion._root_.ContMDiff.iff_comp_isImmersion** 是 Mathlib 中的一个引理，
位于命名空间 `Manifold.IsImmersion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : M → N` between `C^n` manifolds is `C^n` if and only if it is con
tinuous
and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` is `C^n`.
-/
lemma _root_.ContMDiff.iff_comp_isImmersion {f : M → N} {φ : N → N'} (hφ : IsImmersion J J' n φ) :
    CMDiff n f ↔ Continuous f ∧ CMDiff n (φ ∘ f) := by
  rw [ContMDiff.iff_comp_isImmersionOfComplement hφ.isImmersionOfComplement_complement]

end IsImmersion

end Manifold

