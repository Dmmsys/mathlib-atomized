/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.RCLike.TangentCone
public import Mathlib.Data.Bundle
public import Mathlib.Geometry.Manifold.HasGroupoid
public import Mathlib.Tactic.CrossRefAttribute

/-!
# `C^n` manifolds (possibly with boundary or corners)

A `C^n` manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which the changes of coordinates are `C^n` maps.
We define a model with corners as a map `I : H → E` embedding nicely the topological space `H` in
the vector space `E` (or more precisely as a structure containing all the relevant properties).
Given such a model with corners `I` on `(E, H)`, we define the groupoid of local
homeomorphisms of `H` which are `C^n` when read in `E` (for any regularity `n : ℕ∞ω`).
With this groupoid at hand and the general machinery of charted spaces, we thus get the notion
of `C^n` manifold with respect to any model with corners `I` on `(E, H)`.

Some texts assume manifolds to be Hausdorff and second countable. We (in mathlib) assume neither,
but add these assumptions later as needed. (Quite a few results still do not require them.)

## Main definitions

* `ModelWithCorners 𝕜 E H` :
  a structure containing information on the way a space `H` embeds in a
  model vector space E over the field `𝕜`. This is all that is needed to
  define a `C^n` manifold with model space `H`, and model vector space `E`.
* `modelWithCornersSelf 𝕜 E` :
  trivial model with corners structure on the space `E` embedded in itself by the identity.
* `contDiffGroupoid n I` :
  when `I` is a model with corners on `(𝕜, E, H)`, this is the groupoid of partial homeos of `H`
  which are of class `C^n` over the normed field `𝕜`, when read in `E`.
* `IsManifold I n M` :
  a type class saying that the charted space `M`, modelled on the space `H`, has `C^n` changes of
  coordinates with respect to the model with corners `I` on `(𝕜, E, H)`. This type class is just
  a shortcut for `HasGroupoid M (contDiffGroupoid n I)`.

We define a few constructions of smooth manifolds:
* every empty type is a smooth manifold
* `IsManifold.of_discreteTopology`: a discrete space is a smooth manifold
  (over the trivial model with corners on the trivial space)
* the product of two smooth manifolds
* the disjoint union of two manifolds (over the same charted space)

As specific examples of models with corners, we define (in `Geometry.Manifold.Instances.Real`)
* `modelWithCornersSelf n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace n)` for the model space used to
  define `n`-dimensional real manifolds without boundary
  (with notation `𝓡 n` in the scope `Manifold`)
* `modelWithCornersEuclideanHalfSpace n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n)` for the model space
  used to define `n`-dimensional real manifolds with boundary (with notation `𝓡∂ n` in the locale
  `Manifold`)
* `modelWithCornersEuclideanQuadrant n :
  ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanQuadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

With these definitions at hand, to invoke an `n`-dimensional `C^∞` real manifold without boundary,
one could use

  `variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
   [IsManifold (𝓡 n) ∞ M]`.

However, this is not the recommended way: a theorem proved using this assumption would not apply
for instance to the tangent space of such a manifold, which is modelled on
`(EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n))`
and not on `EuclideanSpace ℝ (Fin (2 * n))`!
In the same way, it would not apply to product manifolds, modelled on
`(EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin m))`.
The right invocation does not focus on one specific construction, but on all constructions sharing
the right properties, like

  `variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {I : ModelWithCorners ℝ E E} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]`

Here, `I.Boundaryless` is a typeclass property ensuring that there is no boundary (this is for
instance the case for `modelWithCornersSelf`, or products of these). Note that one could consider
as a natural assumption to only use the trivial model with corners `modelWithCornersSelf ℝ E`,
but again in product manifolds the natural model with corners will not be this one but the product
one (and they are not defeq as `(fun p : E × F ↦ (p.1, p.2))` is not defeq to the identity).
So, it is important to use the above incantation to maximize the applicability of theorems.

Even better, if the result should apply in a parallel way to smooth manifolds and to analytic
manifolds, the last typeclass should be replaced with `[IsManifold I n M]`
for `n : ℕ∞ω`.

We also define `TangentSpace I (x : M)` as a type synonym of `E`, and `TangentBundle I M` as a
type synonym for `Π (x : M), TangentSpace I x` (in the form of an
abbrev of `Bundle.TotalSpace E (TangentSpace I : M → Type _)`). Apart from basic typeclasses on
`TangentSpace I x`, nothing is proved about them in this file, but it is useful to have them
available as definitions early on to get a clean import structure below. The smooth bundle structure
is defined in `VectorBundle.Tangent`, while the definition is used to talk about manifold
derivatives in `MFDeriv.Basic`, and neither file needs import the other.

## Implementation notes

We want to talk about manifolds modelled on a vector space, but also on manifolds with
boundary, modelled on a half space (or even manifolds with corners). For the latter examples,
we still want to define smooth functions, tangent bundles, and so on. As smooth functions are
well defined on vector spaces or subsets of these, one could take for model space a subtype of a
vector space. With the drawback that the whole vector space itself (which is the most basic
example) is not directly a subtype of itself: the inclusion of `univ : Set E` in `Set E` would
show up in the definition, instead of `id`.

A good abstraction covering both cases is to have a vector
space `E` (with basic example the Euclidean space), a model space `H` (with basic example the upper
half space), and an embedding of `H` into `E` (which can be the identity for `H = E`, or
`Subtype.val` for manifolds with corners). We say that the pair `(E, H)` with their embedding is a
model with corners, and we encompass all the relevant properties (in particular the fact that the
image of `H` in `E` should have unique differentials) in the definition of `ModelWithCorners`.

I have considered using the model with corners `I` as a typeclass argument, possibly `outParam`, to
get lighter notations later on, but it did not turn out right, as on `E × F` there are two natural
model with corners, the trivial (identity) one, and the product one, and they are not defeq and one
needs to indicate to Lean which one we want to use.
This means that when talking on objects on manifolds one will most often need to specify the model
with corners one is using. For instance, the tangent bundle will be `TangentBundle I M` and the
derivative will be `mfderiv I I' f`, instead of the more natural notations `TangentBundle 𝕜 M` and
`mfderiv 𝕜 f` (the field has to be explicit anyway, as some manifolds could be considered both as
real and complex manifolds).
-/

@[expose] public section

open Topology

noncomputable section

universe u v w u' v' w'

namespace PartialEquiv

/- This lemma is here in this file, because in `PartialEquiv.basic` it would
have required to import some topology, and it did not look right. -/
@[fun_prop]
/--
lemma `Continuous.invFun` / 引理 `Continuous.invFun`

English:
lemma Continuous.invFun
  statement: {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
  proof: he

中文:
引理 连续.invFun
  结论: {α β : 类型} [拓扑空间 α] [拓扑空间 β]
  证明: he
-/
lemma Continuous.invFun {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : PartialEquiv α β) (he : Continuous e.symm) : Continuous e.invFun := he

end PartialEquiv

open Set Filter Function PartialEquiv

open scoped Manifold Topology ContDiff

/-! ### Models with corners. -/

open scoped Classical in
/-- A structure containing information on the way a space `H` embeds in a
model vector space `E` over the field `𝕜`. This is all that is needed to
define a `C^n` manifold with model space `H`, and model vector space `E`.

We require that, when the field is `ℝ` or `ℂ`, the range is `ℝ`-convex, as this is what is needed
to do calculus and covers the standard examples of manifolds with boundary. Over other fields,
we require that the range is `univ`, as there is no relevant notion of manifold with boundary there.
-/
@[ext]
/--
Definition of `ModelWithCorners` / `ModelWithCorners` 的定义

English:
structure ModelWithCorners
  parameters: (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
  axioms and operations (5):
    - source_eq : source = univ
    - convex_range' : if h : IsRCLikeNormedField 𝕜 then letI  [default: h.rclike 𝕜 letI : NormedSpace Real E := NormedSpace.restrict]
    - nonempty_interior' : (interior (range toPartialEquiv)).Nonempty
    - continuous_toFun : Continuous toFun  [default: by fun_prop]
    - continuous_invFun : Continuous invFun  [default: by fun_prop]

中文:
结构 带角模型
  参数: (𝕜 : 类型) [NontriviallyNormedField 𝕜] (E : 类型)
  公理与运算 (5 个):
    - source_eq : source = univ
    - convex_range' : if h : 是RCLikeNormedField 𝕜 then letI  [默认: h.rclike 𝕜 letI : NormedSpace Real E := NormedSpace.restrict]
    - nonempty_interior' : (interior (range toPartialEquiv)).非空
    - continuous_toFun : 连续 toFun  [默认: by fun_prop]
    - continuous_invFun : 连续 invFun  [默认: by fun_prop]

Depends on / 依赖: h.rclike, rclike
-/
structure ModelWithCorners (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] extends
    PartialEquiv H E where
  source_eq : source = univ
  /-- To check this condition when the space already has a real normed space structure,
  use `Convex.convex_isRCLikeNormedField` which eliminates the `letI`s below, or the constructor
  `ModelWithCorners.ofConvexRange` -/
  convex_range' :
    if h : IsRCLikeNormedField 𝕜 then
      letI := h.rclike 𝕜
      letI : NormedSpace Real E := NormedSpace.restrictScalars Real 𝕜 E
      Convex Real (range toPartialEquiv)
    else range toPartialEquiv = univ
  nonempty_interior' : (interior (range toPartialEquiv)).Nonempty
  continuous_toFun : Continuous toFun := by fun_prop
  continuous_invFun : Continuous invFun := by fun_prop

/--
lemma `ModelWithCorners.range_eq_target` / 引理 `ModelWithCorners.range_eq_target`

English:
lemma ModelWithCorners.range_eq_target
  statement: {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
  proof: by
  rw [← I.image_source_eq_target]; rw [I.source_eq]; rw [image_univ.symm]

中文:
引理 带角模型.range_eq_target
  结论: {𝕜 E H : 类型} [NontriviallyNormedField 𝕜]
  证明: by
  rw [← I.image_source_eq_target]; rw [I.source_eq]; rw [image_univ.symm]

Depends on / 依赖: I.image_source_eq_target, I.source_eq, image_source_eq_target, image_univ, image_univ.symm, source_eq
-/
lemma ModelWithCorners.range_eq_target {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) :
    range I.toPartialEquiv = I.target := by
  rw [← I.image_source_eq_target]; rw [I.source_eq]; rw [image_univ.symm]

/--
Definition of `ModelWithCorners.ofTargetUniv` / `ModelWithCorners.ofTargetUniv` 的定义

English:
definition ModelWithCorners.ofTargetUniv
  signature: (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  body: φ
  source_eq := hsource
  convex_range' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp only [this, htarget, dite_else_true]
    intro h
    let := h.rclike 𝕜
    let := NormedSpace.restrictScalars Real 𝕜 E
    exact convex_univ
  nonempty_interior' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp [this, htarget]

中文:
定义 带角模型.ofTargetUniv
  签名: (𝕜 : 类型) [NontriviallyNormedField 𝕜]
  定义体: φ
  source_eq := hsource
  convex_range' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp only [this, htarget, dite_else_true]
    intro h
    let := h.rclike 𝕜
    let := NormedSpace.restrictScalars Real 𝕜 E
    exact convex_univ
  nonempty_interior' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp [this, htarget]
-/
def ModelWithCorners.ofTargetUniv (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (φ : PartialEquiv H E) (hsource : φ.source = univ) (htarget : φ.target = univ)
    (hcont : Continuous φ) (hcont_inv : Continuous φ.symm) : ModelWithCorners 𝕜 E H where
  toPartialEquiv := φ
  source_eq := hsource
  convex_range' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp only [this, htarget, dite_else_true]
    intro h
    let := h.rclike 𝕜
    let := NormedSpace.restrictScalars Real 𝕜 E
    exact convex_univ
  nonempty_interior' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp [this, htarget]

attribute [simp, mfld_simps] ModelWithCorners.source_eq

/--
Definition of `modelWithCornersSelf` / `modelWithCornersSelf` 的定义

English:
definition modelWithCornersSelf
  signature: (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
  body: ModelWithCorners.ofTargetUniv 𝕜 (PartialEquiv.refl E) rfl rfl continuous_id continuous_id

@[inherit_doc] scoped[Manifold] notation "𝓘(" 𝕜 ", " E ")" => modelWithCornersSelf 𝕜 E

中文:
定义 modelWithCornersSelf
  签名: (𝕜 : 类型) [NontriviallyNormedField 𝕜] (E : 类型)
  定义体: ModelWithCorners.ofTargetUniv 𝕜 (PartialEquiv.refl E) rfl rfl continuous_id continuous_id

@[inherit_doc] scoped[Manifold] notation "𝓘(" 𝕜 ", " E ")" => modelWithCornersSelf 𝕜 E

Depends on / 依赖: ModelWithCorners, ModelWithCorners.ofTargetUniv, PartialEquiv, PartialEquiv.refl, continuous_id, ofTargetUniv
-/
def modelWithCornersSelf (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : ModelWithCorners 𝕜 E E :=
  ModelWithCorners.ofTargetUniv 𝕜 (PartialEquiv.refl E) rfl rfl continuous_id continuous_id

@[inherit_doc] scoped[Manifold] notation "𝓘(" 𝕜 ", " E ")" => modelWithCornersSelf 𝕜 E

/-- A normed field is a model with corners. -/
scoped[Manifold] notation "𝓘(" 𝕜 ")" => modelWithCornersSelf 𝕜 𝕜

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)

namespace ModelWithCorners

/--
Definition of `toFun'` / `toFun'` 的定义

English:
definition toFun'
  signature: (e : ModelWithCorners 𝕜 E H)
  body: e.toFun

中文:
定义 toFun'
  签名: (e : 带角模型 𝕜 E H)
  定义体: e.toFun
-/
@[coe] def toFun' (e : ModelWithCorners 𝕜 E H) : H -> E := e.toFun

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (ModelWithCorners 𝕜 E H) fun _ => H -> E
  body: ⟨toFun'⟩

中文:
实例 :
  签名: CoeFun (带角模型 𝕜 E H) fun _ => H -> E
  定义体: ⟨toFun'⟩
-/
instance : CoeFun (ModelWithCorners 𝕜 E H) fun _ => H -> E := ⟨toFun'⟩

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : PartialEquiv E H
  body: I.toPartialEquiv.symm

中文:
定义 symm
  签名: : 部分等价 E H
  定义体: I.toPartialEquiv.symm
-/
protected def symm : PartialEquiv E H :=
  I.toPartialEquiv.symm

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
  body: I

中文:
定义 Simps.apply
  签名: (𝕜 : 类型) [NontriviallyNormedField 𝕜] (E : 类型) [赋范交换加群 E]
  定义体: I
-/
def Simps.apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : H -> E :=
  I

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
  body: I.symm

initialize_simps_projections ModelWithCorners (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (𝕜 : 类型) [NontriviallyNormedField 𝕜] (E : 类型) [赋范交换加群 E]
  定义体: I.symm

initialize_simps_projections ModelWithCorners (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : E -> H :=
  I.symm

initialize_simps_projections ModelWithCorners (toFun -> apply, invFun -> symm_apply)

-- Register a few lemmas to make sure that `simp` puts expressions in normal form
@[simp, mfld_simps]
/--
theorem `toPartialEquiv_coe` / 定理 `toPartialEquiv_coe`

English:
theorem toPartialEquiv_coe
  statement: (I.toPartialEquiv : H -> E) = I
  proof: rfl

@[simp, mfld_simps]

中文:
定理 toPartialEquiv_coe
  结论: (I.toPartialEquiv : H -> E) = I
  证明: rfl

@[simp, mfld_simps]
-/
theorem toPartialEquiv_coe : (I.toPartialEquiv : H -> E) = I :=
  rfl

@[simp, mfld_simps]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (e : PartialEquiv H E) (a b c d d')
  proof: rfl

@[simp, mfld_simps]

中文:
定理 mk_coe
  条件: (e : 部分等价 H E) (a b c d d')
  证明: rfl

@[simp, mfld_simps]
-/
theorem mk_coe (e : PartialEquiv H E) (a b c d d') :
    ((ModelWithCorners.mk e a b c d d' : ModelWithCorners 𝕜 E H) : H -> E) = (e : H -> E) :=
  rfl

@[simp, mfld_simps]
/--
theorem `toPartialEquiv_coe_symm` / 定理 `toPartialEquiv_coe_symm`

English:
theorem toPartialEquiv_coe_symm
  statement: (I.toPartialEquiv.symm : E -> H) = I.symm
  proof: rfl

@[simp, mfld_simps]

中文:
定理 toPartialEquiv_coe_symm
  结论: (I.toPartialEquiv.symm : E -> H) = I.symm
  证明: rfl

@[simp, mfld_simps]
-/
theorem toPartialEquiv_coe_symm : (I.toPartialEquiv.symm : E -> H) = I.symm :=
  rfl

@[simp, mfld_simps]
/--
theorem `mk_symm` / 定理 `mk_symm`

English:
theorem mk_symm
  given: (e : PartialEquiv H E) (a b c d d')
  proof: rfl

@[fun_prop]

中文:
定理 mk_symm
  条件: (e : 部分等价 H E) (a b c d d')
  证明: rfl

@[fun_prop]
-/
theorem mk_symm (e : PartialEquiv H E) (a b c d d') :
    (ModelWithCorners.mk e a b c d d' : ModelWithCorners 𝕜 E H).symm = e.symm :=
  rfl

@[fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: Continuous I
  proof: I.continuous_toFun

中文:
定理 continuous
  结论: 连续 I
  证明: I.continuous_toFun
-/
protected theorem continuous : Continuous I :=
  I.continuous_toFun

/--
theorem `continuousAt` / 定理 `continuousAt`

English:
theorem continuousAt
  given: {x}
  statement: ContinuousAt I x
  proof: I.continuous.continuousAt

中文:
定理 continuousAt
  条件: {x}
  结论: ContinuousAt I x
  证明: I.continuous.continuousAt
-/
protected theorem continuousAt {x} : ContinuousAt I x :=
  I.continuous.continuousAt

/--
theorem `continuousWithinAt` / 定理 `continuousWithinAt`

English:
theorem continuousWithinAt
  given: {s x}
  statement: ContinuousWithinAt I s x
  proof: I.continuousAt.continuousWithinAt

@[fun_prop]

中文:
定理 continuousWithinAt
  条件: {s x}
  结论: ContinuousWithinAt I s x
  证明: I.continuousAt.continuousWithinAt

@[fun_prop]
-/
protected theorem continuousWithinAt {s x} : ContinuousWithinAt I s x :=
  I.continuousAt.continuousWithinAt

@[fun_prop]
/--
theorem `continuous_symm` / 定理 `continuous_symm`

English:
theorem continuous_symm
  statement: Continuous I.symm
  proof: I.continuous_invFun

中文:
定理 continuous_symm
  结论: 连续 I.symm
  证明: I.continuous_invFun

Depends on / 依赖: I.continuous_invFun, continuous_invFun
-/
theorem continuous_symm : Continuous I.symm :=
  I.continuous_invFun

/--
theorem `continuousAt_symm` / 定理 `continuousAt_symm`

English:
theorem continuousAt_symm
  given: {x}
  statement: ContinuousAt I.symm x
  proof: I.continuous_symm.continuousAt

中文:
定理 continuousAt_symm
  条件: {x}
  结论: ContinuousAt I.symm x
  证明: I.continuous_symm.continuousAt

Depends on / 依赖: I.continuous_symm.continuousAt, continuousAt, continuous_symm
-/
theorem continuousAt_symm {x} : ContinuousAt I.symm x :=
  I.continuous_symm.continuousAt

/--
theorem `continuousWithinAt_symm` / 定理 `continuousWithinAt_symm`

English:
theorem continuousWithinAt_symm
  given: {s x}
  statement: ContinuousWithinAt I.symm s x
  proof: I.continuous_symm.continuousWithinAt

中文:
定理 continuousWithinAt_symm
  条件: {s x}
  结论: ContinuousWithinAt I.symm s x
  证明: I.continuous_symm.continuousWithinAt

Depends on / 依赖: I.continuous_symm.continuousWithinAt, continuousWithinAt, continuous_symm
-/
theorem continuousWithinAt_symm {s x} : ContinuousWithinAt I.symm s x :=
  I.continuous_symm.continuousWithinAt

/--
theorem `continuousOn_symm` / 定理 `continuousOn_symm`

English:
theorem continuousOn_symm
  given: {s}
  statement: ContinuousOn I.symm s
  proof: I.continuous_symm.continuousOn

@[simp, mfld_simps]

中文:
定理 continuousOn_symm
  条件: {s}
  结论: ContinuousOn I.symm s
  证明: I.continuous_symm.continuousOn

@[simp, mfld_simps]

Depends on / 依赖: I.continuous_symm.continuousOn, continuousOn, continuous_symm
-/
theorem continuousOn_symm {s} : ContinuousOn I.symm s :=
  I.continuous_symm.continuousOn

@[simp, mfld_simps]
/--
theorem `target_eq` / 定理 `target_eq`

English:
theorem target_eq
  statement: I.target = range (I : H -> E)
  proof: by
  rw [← image_univ]; rw [← I.source_eq]
  exact I.image_source_eq_target.symm

中文:
定理 target_eq
  结论: I.target = range (I : H -> E)
  证明: by
  rw [← image_univ]; rw [← I.source_eq]
  exact I.image_source_eq_target.symm

Depends on / 依赖: I.image_source_eq_target.symm, I.source_eq, image_source_eq_target, image_univ, source_eq
-/
theorem target_eq : I.target = range (I : H -> E) := by
  rw [← image_univ]; rw [← I.source_eq]
  exact I.image_source_eq_target.symm

/--
theorem `nonempty_interior` / 定理 `nonempty_interior`

English:
theorem nonempty_interior
  statement: (interior (range I)).Nonempty
  proof: I.nonempty_interior'

中文:
定理 nonempty_interior
  结论: (interior (range I)).非空
  证明: I.nonempty_interior'

Depends on / 依赖: I.nonempty_interior, nonempty_interior
-/
theorem nonempty_interior : (interior (range I)).Nonempty :=
  I.nonempty_interior'

/--
theorem `range_eq_univ_of_not_isRCLikeNormedField` / 定理 `range_eq_univ_of_not_isRCLikeNormedField`

English:
theorem range_eq_univ_of_not_isRCLikeNormedField
  given: (h : ¬ IsRCLikeNormedField 𝕜)
  proof: by
  simpa [h] using I.convex_range'

中文:
定理 range_eq_univ_of_not_isRCLikeNormedField
  条件: (h : ¬ 是RCLikeNormedField 𝕜)
  证明: by
  simpa [h] using I.convex_range'

Depends on / 依赖: I.convex_range, convex_range
-/
theorem range_eq_univ_of_not_isRCLikeNormedField (h : ¬ IsRCLikeNormedField 𝕜) :
    range I = univ := by
  simpa [h] using I.convex_range'

/--
lemma `_root_.Convex.convex_isRCLikeNormedField` / 引理 `_root_.Convex.convex_isRCLikeNormedField`

English:
lemma _root_.Convex.convex_isRCLikeNormedField
  statement: [NormedSpace Real E] [h : IsRCLikeNormedField 𝕜]
  proof: h.rclike
    letI := NormedSpace.restrictScalars Real 𝕜 E
    Convex Real s := by
  let := h.rclike
  let := NormedSpace.restrictScalars Real 𝕜 E
  simp only [Convex, StarConvex] at hs ⊢
  intro u hu v hv a b ha hb hab
  convert! hs hu hv ha hb hab using 2
  · rw [← @algebraMap_smul (R := Real) (A := 𝕜), ← @algebraMap_smul (R := Real) (A := 𝕜)]
  · rw [← @algebraMap_smul (R := Real) (A := 𝕜), ← @algebraMap_smul (R := Real) (A := 𝕜)]

中文:
引理 _root_.凸.convex_isRCLikeNormedField
  结论: [赋范空间 实数 E] [h : 是RCLikeNormedField 𝕜]
  证明: h.rclike
    letI := NormedSpace.restrictScalars Real 𝕜 E
    Convex Real s := by
  let := h.rclike
  let := NormedSpace.restrictScalars Real 𝕜 E
  simp only [Convex, StarConvex] at hs ⊢
  intro u hu v hv a b ha hb hab
  convert! hs hu hv ha hb hab using 2
  · rw [← @algebraMap_smul (R := Real) (A := 𝕜), ← @algebraMap_smul (R := Real) (A := 𝕜)]
  · rw [← @algebraMap_smul (R := Real) (A := 𝕜), ← @algebraMap_smul (R := Real) (A := 𝕜)]

Depends on / 依赖: h.rclike, rclike
-/
lemma _root_.Convex.convex_isRCLikeNormedField [NormedSpace Real E] [h : IsRCLikeNormedField 𝕜]
    {s : Set E} (hs : Convex Real s) :
    letI := h.rclike
    letI := NormedSpace.restrictScalars Real 𝕜 E
    Convex Real s := by
  let := h.rclike
  let := NormedSpace.restrictScalars Real 𝕜 E
  simp only [Convex, StarConvex] at hs ⊢
  intro u hu v hv a b ha hb hab
  convert! hs hu hv ha hb hab using 2
  · rw [← @algebraMap_smul (R := Real) (A := 𝕜), ← @algebraMap_smul (R := Real) (A := 𝕜)]
  · rw [← @algebraMap_smul (R := Real) (A := 𝕜), ← @algebraMap_smul (R := Real) (A := 𝕜)]

/--
Definition of `ofConvexRange` / `ofConvexRange` 的定义

English:
definition ofConvexRange
  body: φ
  source_eq := hsource
  convex_range' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp only [instIsRCLikeNormedField, ↓reduceDIte, this]
    exact htarget.convex_isRCLikeNormedField
  nonempty_interior' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp [this, hint]

中文:
定义 ofConvexRange
  定义体: φ
  source_eq := hsource
  convex_range' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp only [instIsRCLikeNormedField, ↓reduceDIte, this]
    exact htarget.convex_isRCLikeNormedField
  nonempty_interior' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp [this, hint]
-/
def ofConvexRange
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {H : Type*} [TopologicalSpace H]
    (φ : PartialEquiv H E) (hsource : φ.source = univ) (htarget : Convex Real φ.target)
    (hcont : Continuous φ) (hcont_inv : Continuous φ.symm) (hint : (interior φ.target).Nonempty) :
    ModelWithCorners Real E H where
  toPartialEquiv := φ
  source_eq := hsource
  convex_range' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp only [instIsRCLikeNormedField, ↓reduceDIte, this]
    exact htarget.convex_isRCLikeNormedField
  nonempty_interior' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp [this, hint]

/--
theorem `convex_range` / 定理 `convex_range`

English:
theorem convex_range
  given: [NormedSpace Real E]
  statement: Convex Real (range I)
  proof: by
  by_cases h : IsRCLikeNormedField 𝕜
  · let : RCLike 𝕜 := h.rclike
    have W := I.convex_range'
    simp only [h, ↓reduceDIte, toPartialEquiv_coe] at W
    simp only [Convex, StarConvex] at W ⊢
    intro u hu v hv a b ha hb hab
    convert! W hu hv ha hb hab using 2
    · rw [← @algebraMap_smul (R := Real) (A := 𝕜)]
      rfl
    · rw [← @algebraMap_smul (R := Real) (A := 𝕜)]
      rfl
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h, convex_univ]

中文:
定理 convex_range
  条件: [赋范空间 实数 E]
  结论: 凸 实数 (range I)
  证明: by
  by_cases h : IsRCLikeNormedField 𝕜
  · let : RCLike 𝕜 := h.rclike
    have W := I.convex_range'
    simp only [h, ↓reduceDIte, toPartialEquiv_coe] at W
    simp only [Convex, StarConvex] at W ⊢
    intro u hu v hv a b ha hb hab
    convert! W hu hv ha hb hab using 2
    · rw [← @algebraMap_smul (R := Real) (A := 𝕜)]
      rfl
    · rw [← @algebraMap_smul (R := Real) (A := 𝕜)]
      rfl
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h, convex_univ]

Depends on / 依赖: Convex, I.convex_range, IsRCLikeNormedField, RCLike, StarConvex, algebraMap_smul, convert, convex_range, convex_univ, h.rclike, range_eq_univ_of_not_isRCLikeNormedField, rclike, reduceDIte, toPartialEquiv_coe
-/
theorem convex_range [NormedSpace Real E] : Convex Real (range I) := by
  by_cases h : IsRCLikeNormedField 𝕜
  · let : RCLike 𝕜 := h.rclike
    have W := I.convex_range'
    simp only [h, ↓reduceDIte, toPartialEquiv_coe] at W
    simp only [Convex, StarConvex] at W ⊢
    intro u hu v hv a b ha hb hab
    convert! W hu hv ha hb hab using 2
    · rw [← @algebraMap_smul (R := Real) (A := 𝕜)]
      rfl
    · rw [← @algebraMap_smul (R := Real) (A := 𝕜)]
      rfl
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h, convex_univ]

/--
theorem `uniqueDiffOn` / 定理 `uniqueDiffOn`

English:
theorem uniqueDiffOn
  statement: UniqueDiffOn 𝕜 (range I)
  proof: by
  by_cases h : IsRCLikeNormedField 𝕜
  · let := h.rclike 𝕜
    let := NormedSpace.restrictScalars Real 𝕜 E
    apply uniqueDiffOn_convex_of_isRCLikeNormedField _ I.nonempty_interior
    simpa [h] using I.convex_range
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h, uniqueDiffOn_univ]

中文:
定理 uniqueDiffOn
  结论: UniqueDiffOn 𝕜 (range I)
  证明: by
  by_cases h : IsRCLikeNormedField 𝕜
  · let := h.rclike 𝕜
    let := NormedSpace.restrictScalars Real 𝕜 E
    apply uniqueDiffOn_convex_of_isRCLikeNormedField _ I.nonempty_interior
    simpa [h] using I.convex_range
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h, uniqueDiffOn_univ]
-/
protected theorem uniqueDiffOn : UniqueDiffOn 𝕜 (range I) := by
  by_cases h : IsRCLikeNormedField 𝕜
  · let := h.rclike 𝕜
    let := NormedSpace.restrictScalars Real 𝕜 E
    apply uniqueDiffOn_convex_of_isRCLikeNormedField _ I.nonempty_interior
    simpa [h] using I.convex_range
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h, uniqueDiffOn_univ]

/--
theorem `range_subset_closure_interior` / 定理 `range_subset_closure_interior`

English:
theorem range_subset_closure_interior
  statement: range I subseteq closure (interior (range I))
  proof: by
  by_cases h : IsRCLikeNormedField 𝕜
  · let := h.rclike 𝕜
    let := NormedSpace.restrictScalars Real 𝕜 E
    rw [Convex.closure_interior_eq_closure_of_nonempty_interior (𝕜 := Real)]
    · apply subset_closure
    · apply I.convex_range
    · apply I.nonempty_interior
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h]

@[simp, mfld_simps]

中文:
定理 range_subset_closure_interior
  结论: range I subseteq closure (interior (range I))
  证明: by
  by_cases h : IsRCLikeNormedField 𝕜
  · let := h.rclike 𝕜
    let := NormedSpace.restrictScalars Real 𝕜 E
    rw [Convex.closure_interior_eq_closure_of_nonempty_interior (𝕜 := Real)]
    · apply subset_closure
    · apply I.convex_range
    · apply I.nonempty_interior
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h]

@[simp, mfld_simps]

Depends on / 依赖: Convex, Convex.closure_interior_eq_closure_of_nonempty_interior, I.convex_range, I.nonempty_interior, IsRCLikeNormedField, NormedSpace, NormedSpace.restrictScalars, closure_interior_eq_closure_of_nonempty_interior, convex_range, h.rclike, nonempty_interior, range_eq_univ_of_not_isRCLikeNormedField, rclike, restrictScalars, subset_closure
-/
theorem range_subset_closure_interior : range I subseteq closure (interior (range I)) := by
  by_cases h : IsRCLikeNormedField 𝕜
  · let := h.rclike 𝕜
    let := NormedSpace.restrictScalars Real 𝕜 E
    rw [Convex.closure_interior_eq_closure_of_nonempty_interior (𝕜 := Real)]
    · apply subset_closure
    · apply I.convex_range
    · apply I.nonempty_interior
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h]

@[simp, mfld_simps]
/--
theorem `left_inv` / 定理 `left_inv`

English:
theorem left_inv
  given: (x : H)
  statement: I.symm (I x) = x
  proof: by refine I.left_inv' ?_; simp

中文:
定理 left_inv
  条件: (x : H)
  结论: I.symm (I x) = x
  证明: by refine I.left_inv' ?_; simp
-/
protected theorem left_inv (x : H) : I.symm (I x) = x := by refine I.left_inv' ?_; simp

/--
theorem `leftInverse` / 定理 `leftInverse`

English:
theorem leftInverse
  statement: LeftInverse I.symm I
  proof: I.left_inv

中文:
定理 leftInverse
  结论: 左逆 I.symm I
  证明: I.left_inv
-/
protected theorem leftInverse : LeftInverse I.symm I :=
  I.left_inv

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: Injective I
  proof: I.leftInverse.injective

@[simp, mfld_simps]

中文:
定理 injective
  结论: 单射 I
  证明: I.leftInverse.injective

@[simp, mfld_simps]

Depends on / 依赖: I.leftInverse.injective, injective, leftInverse
-/
theorem injective : Injective I :=
  I.leftInverse.injective

@[simp, mfld_simps]
/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  statement: I.symm ∘ I = id
  proof: I.leftInverse.comp_eq_id

中文:
定理 symm_comp_self
  结论: I.symm ∘ I = id
  证明: I.leftInverse.comp_eq_id

Depends on / 依赖: I.leftInverse.comp_eq_id, comp_eq_id, leftInverse
-/
theorem symm_comp_self : I.symm ∘ I = id :=
  I.leftInverse.comp_eq_id

/--
theorem `rightInvOn` / 定理 `rightInvOn`

English:
theorem rightInvOn
  statement: RightInvOn I.symm I (range I)
  proof: I.leftInverse.rightInvOn_range

@[simp, mfld_simps]

中文:
定理 rightInvOn
  结论: RightInvOn I.symm I (range I)
  证明: I.leftInverse.rightInvOn_range

@[simp, mfld_simps]
-/
protected theorem rightInvOn : RightInvOn I.symm I (range I) :=
  I.leftInverse.rightInvOn_range

@[simp, mfld_simps]
/--
theorem `right_inv` / 定理 `right_inv`

English:
theorem right_inv
  given: {x : E} (hx : x in range I)
  statement: I (I.symm x) = x
  proof: I.rightInvOn hx

中文:
定理 right_inv
  条件: {x : E} (hx : x in range I)
  结论: I (I.symm x) = x
  证明: I.rightInvOn hx
-/
protected theorem right_inv {x : E} (hx : x in range I) : I (I.symm x) = x :=
  I.rightInvOn hx

/--
theorem `preimage_image` / 定理 `preimage_image`

English:
theorem preimage_image
  given: (s : Set H)
  statement: I ⁻¹' I '' s = s
  proof: I.injective.preimage_image s

中文:
定理 preimage_image
  条件: (s : 集合 H)
  结论: I ⁻¹' I '' s = s
  证明: I.injective.preimage_image s

Depends on / 依赖: I.injective.preimage_image, injective, preimage_image
-/
theorem preimage_image (s : Set H) : I ⁻¹' I '' s = s :=
  I.injective.preimage_image s

/--
theorem `image_eq` / 定理 `image_eq`

English:
theorem image_eq
  given: (s : Set H)
  statement: I '' s = I.symm ⁻¹' s inter range I
  proof: by
  refine (I.toPartialEquiv.image_eq_target_inter_inv_preimage ?_).trans ?_
  · rw [I.source_eq]; exact subset_univ _
  · rw [inter_comm, I.target_eq, I.toPartialEquiv_coe_symm]

中文:
定理 image_eq
  条件: (s : 集合 H)
  结论: I '' s = I.symm ⁻¹' s inter range I
  证明: by
  refine (I.toPartialEquiv.image_eq_target_inter_inv_preimage ?_).trans ?_
  · rw [I.source_eq]; exact subset_univ _
  · rw [inter_comm, I.target_eq, I.toPartialEquiv_coe_symm]
-/
protected theorem image_eq (s : Set H) : I '' s = I.symm ⁻¹' s inter range I := by
  refine (I.toPartialEquiv.image_eq_target_inter_inv_preimage ?_).trans ?_
  · rw [I.source_eq]; exact subset_univ _
  · rw [inter_comm, I.target_eq, I.toPartialEquiv_coe_symm]

/--
theorem `isClosedEmbedding` / 定理 `isClosedEmbedding`

English:
theorem isClosedEmbedding
  statement: IsClosedEmbedding I
  proof: I.leftInverse.isClosedEmbedding I.continuous_symm I.continuous

中文:
定理 isClosedEmbedding
  结论: 是闭嵌入 I
  证明: I.leftInverse.isClosedEmbedding I.continuous_symm I.continuous

Depends on / 依赖: I.continuous, I.continuous_symm, I.leftInverse.isClosedEmbedding, continuous, continuous_symm, isClosedEmbedding, leftInverse
-/
theorem isClosedEmbedding : IsClosedEmbedding I :=
  I.leftInverse.isClosedEmbedding I.continuous_symm I.continuous

/--
theorem `isClosed_range` / 定理 `isClosed_range`

English:
theorem isClosed_range
  statement: IsClosed (range I)
  proof: I.isClosedEmbedding.isClosed_range

中文:
定理 isClosed_range
  结论: 是闭集 (range I)
  证明: I.isClosedEmbedding.isClosed_range

Depends on / 依赖: I.isClosedEmbedding.isClosed_range, isClosedEmbedding, isClosed_range
-/
theorem isClosed_range : IsClosed (range I) :=
  I.isClosedEmbedding.isClosed_range


/--
theorem `range_eq_closure_interior` / 定理 `range_eq_closure_interior`

English:
theorem range_eq_closure_interior
  statement: range I = closure (interior (range I))
  proof: Subset.antisymm I.range_subset_closure_interior I.isClosed_range.closure_interior_subset

中文:
定理 range_eq_closure_interior
  结论: range I = closure (interior (range I))
  证明: Subset.antisymm I.range_subset_closure_interior I.isClosed_range.closure_interior_subset

Depends on / 依赖: I.isClosed_range.closure_interior_subset, I.range_subset_closure_interior, Subset, Subset.antisymm, antisymm, closure_interior_subset, isClosed_range, range_subset_closure_interior
-/
theorem range_eq_closure_interior : range I = closure (interior (range I)) :=
  Subset.antisymm I.range_subset_closure_interior I.isClosed_range.closure_interior_subset

/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  given: (x : H)
  statement: map I (𝓝 x) = 𝓝[range I] I x
  proof: I.isClosedEmbedding.isEmbedding.map_nhds_eq x

中文:
定理 map_nhds_eq
  条件: (x : H)
  结论: map I (𝓝 x) = 𝓝[range I] I x
  证明: I.isClosedEmbedding.isEmbedding.map_nhds_eq x

Depends on / 依赖: I.isClosedEmbedding.isEmbedding.map_nhds_eq, isClosedEmbedding, isEmbedding, map_nhds_eq
-/
theorem map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[range I] I x :=
  I.isClosedEmbedding.isEmbedding.map_nhds_eq x

/--
theorem `map_nhdsWithin_eq` / 定理 `map_nhdsWithin_eq`

English:
theorem map_nhdsWithin_eq
  given: (s : Set H) (x : H)
  statement: map I (𝓝[s] x) = 𝓝[I '' s] I x
  proof: I.isClosedEmbedding.isEmbedding.map_nhdsWithin_eq s x

中文:
定理 map_nhdsWithin_eq
  条件: (s : 集合 H) (x : H)
  结论: map I (𝓝[s] x) = 𝓝[I '' s] I x
  证明: I.isClosedEmbedding.isEmbedding.map_nhdsWithin_eq s x

Depends on / 依赖: I.isClosedEmbedding.isEmbedding.map_nhdsWithin_eq, isClosedEmbedding, isEmbedding, map_nhdsWithin_eq
-/
theorem map_nhdsWithin_eq (s : Set H) (x : H) : map I (𝓝[s] x) = 𝓝[I '' s] I x :=
  I.isClosedEmbedding.isEmbedding.map_nhdsWithin_eq s x

/--
theorem `image_mem_nhdsWithin` / 定理 `image_mem_nhdsWithin`

English:
theorem image_mem_nhdsWithin
  given: {x : H} {s : Set H} (hs : s in 𝓝 x)
  statement: I '' s in 𝓝[range I] I x
  proof: I.map_nhds_eq x ▸ image_mem_map hs

中文:
定理 image_mem_nhdsWithin
  条件: {x : H} {s : 集合 H} (hs : s in 𝓝 x)
  结论: I '' s in 𝓝[range I] I x
  证明: I.map_nhds_eq x ▸ image_mem_map hs

Depends on / 依赖: I.map_nhds_eq, image_mem_map, map_nhds_eq
-/
theorem image_mem_nhdsWithin {x : H} {s : Set H} (hs : s in 𝓝 x) : I '' s in 𝓝[range I] I x :=
  I.map_nhds_eq x ▸ image_mem_map hs

/--
theorem `symm_map_nhdsWithin_image` / 定理 `symm_map_nhdsWithin_image`

English:
theorem symm_map_nhdsWithin_image
  given: {x : H} {s : Set H}
  statement: map I.symm (𝓝[I '' s] I x) = 𝓝[s] x
  proof: by
  rw [← I.map_nhdsWithin_eq]; rw [map_map]; rw [I.symm_comp_self]; rw [map_id]

中文:
定理 symm_map_nhdsWithin_image
  条件: {x : H} {s : 集合 H}
  结论: map I.symm (𝓝[I '' s] I x) = 𝓝[s] x
  证明: by
  rw [← I.map_nhdsWithin_eq]; rw [map_map]; rw [I.symm_comp_self]; rw [map_id]

Depends on / 依赖: I.map_nhdsWithin_eq, I.symm_comp_self, map_id, map_map, map_nhdsWithin_eq, symm_comp_self
-/
theorem symm_map_nhdsWithin_image {x : H} {s : Set H} : map I.symm (𝓝[I '' s] I x) = 𝓝[s] x := by
  rw [← I.map_nhdsWithin_eq]; rw [map_map]; rw [I.symm_comp_self]; rw [map_id]

/--
theorem `symm_map_nhdsWithin_range` / 定理 `symm_map_nhdsWithin_range`

English:
theorem symm_map_nhdsWithin_range
  given: (x : H)
  statement: map I.symm (𝓝[range I] I x) = 𝓝 x
  proof: by
  rw [← I.map_nhds_eq]; rw [map_map]; rw [I.symm_comp_self]; rw [map_id]

中文:
定理 symm_map_nhdsWithin_range
  条件: (x : H)
  结论: map I.symm (𝓝[range I] I x) = 𝓝 x
  证明: by
  rw [← I.map_nhds_eq]; rw [map_map]; rw [I.symm_comp_self]; rw [map_id]

Depends on / 依赖: I.map_nhds_eq, I.symm_comp_self, map_id, map_map, map_nhds_eq, symm_comp_self
-/
theorem symm_map_nhdsWithin_range (x : H) : map I.symm (𝓝[range I] I x) = 𝓝 x := by
  rw [← I.map_nhds_eq]; rw [map_map]; rw [I.symm_comp_self]; rw [map_id]

/--
theorem `uniqueDiffOn_preimage` / 定理 `uniqueDiffOn_preimage`

English:
theorem uniqueDiffOn_preimage
  given: {s : Set H} (hs : IsOpen s)
  proof: by
  rw [inter_comm]
  exact I.uniqueDiffOn.inter (hs.preimage I.continuous_invFun)

中文:
定理 uniqueDiffOn_preimage
  条件: {s : 集合 H} (hs : 是开集 s)
  证明: by
  rw [inter_comm]
  exact I.uniqueDiffOn.inter (hs.preimage I.continuous_invFun)

Depends on / 依赖: I.continuous_invFun, I.uniqueDiffOn.inter, continuous_invFun, hs.preimage, inter_comm, preimage, uniqueDiffOn
-/
theorem uniqueDiffOn_preimage {s : Set H} (hs : IsOpen s) :
    UniqueDiffOn 𝕜 (I.symm ⁻¹' s inter range I) := by
  rw [inter_comm]
  exact I.uniqueDiffOn.inter (hs.preimage I.continuous_invFun)

/--
theorem `uniqueDiffOn_preimage_source` / 定理 `uniqueDiffOn_preimage_source`

English:
theorem uniqueDiffOn_preimage_source
  statement: {β : Type*} [TopologicalSpace β]
  proof: I.uniqueDiffOn_preimage e.open_source

中文:
定理 uniqueDiffOn_preimage_source
  结论: {β : 类型} [拓扑空间 β]
  证明: I.uniqueDiffOn_preimage e.open_source

Depends on / 依赖: I.uniqueDiffOn_preimage, e.open_source, open_source, uniqueDiffOn_preimage
-/
theorem uniqueDiffOn_preimage_source {β : Type*} [TopologicalSpace β]
    {e : OpenPartialHomeomorph H β} : UniqueDiffOn 𝕜 (I.symm ⁻¹' e.source inter range I) :=
  I.uniqueDiffOn_preimage e.open_source

/--
theorem `uniqueDiffWithinAt_image` / 定理 `uniqueDiffWithinAt_image`

English:
theorem uniqueDiffWithinAt_image
  given: {x : H}
  statement: UniqueDiffWithinAt 𝕜 (range I) (I x)
  proof: I.uniqueDiffOn _ (mem_range_self _)

中文:
定理 uniqueDiffWithinAt_image
  条件: {x : H}
  结论: UniqueDiffWithinAt 𝕜 (range I) (I x)
  证明: I.uniqueDiffOn _ (mem_range_self _)

Depends on / 依赖: I.uniqueDiffOn, mem_range_self, uniqueDiffOn
-/
theorem uniqueDiffWithinAt_image {x : H} : UniqueDiffWithinAt 𝕜 (range I) (I x) :=
  I.uniqueDiffOn _ (mem_range_self _)

/--
theorem `symm_continuousWithinAt_comp_right_iff` / 定理 `symm_continuousWithinAt_comp_right_iff`

English:
theorem symm_continuousWithinAt_comp_right_iff
  statement: {X} [TopologicalSpace X] {f : H -> X} {s : Set H}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.comp I.continuousWithinAt (mapsTo_preimage _ _)
    simp_rw [preimage_inter, preimage_preimage, I.left_inv, preimage_id', preimage_range,
      inter_univ] at this
    rwa [Function.comp_assoc, I.symm_comp_self] at this
  · rw [← I.left_inv x] at h; exact h.comp I.continuousWithinAt_symm inter_subset_left

中文:
定理 symm_continuousWithinAt_comp_right_iff
  结论: {X} [拓扑空间 X] {f : H -> X} {s : 集合 H}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.comp I.continuousWithinAt (mapsTo_preimage _ _)
    simp_rw [preimage_inter, preimage_preimage, I.left_inv, preimage_id', preimage_range,
      inter_univ] at this
    rwa [Function.comp_assoc, I.symm_comp_self] at this
  · rw [← I.left_inv x] at h; exact h.comp I.continuousWithinAt_symm inter_subset_left

Depends on / 依赖: Function, Function.comp_assoc, I.continuousWithinAt, I.continuousWithinAt_symm, I.left_inv, I.symm_comp_self, comp_assoc, continuousWithinAt, continuousWithinAt_symm, h.comp, inter_subset_left, inter_univ, left_inv, mapsTo_preimage, preimage_id, preimage_inter, preimage_preimage, preimage_range, simp_rw, symm_comp_self
-/
theorem symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {f : H -> X} {s : Set H}
    {x : H} :
    ContinuousWithinAt (f ∘ I.symm) (I.symm ⁻¹' s inter range I) (I x) ↔ ContinuousWithinAt f s x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.comp I.continuousWithinAt (mapsTo_preimage _ _)
    simp_rw [preimage_inter, preimage_preimage, I.left_inv, preimage_id', preimage_range,
      inter_univ] at this
    rwa [Function.comp_assoc, I.symm_comp_self] at this
  · rw [← I.left_inv x] at h; exact h.comp I.continuousWithinAt_symm inter_subset_left

/--
theorem `locallyCompactSpace` / 定理 `locallyCompactSpace`

English:
theorem locallyCompactSpace
  given: [LocallyCompactSpace E] (I : ModelWithCorners 𝕜 E H)
  proof: by
  have : forall x : H, (𝓝 x).HasBasis (fun s => s in 𝓝 (I x) ∧ IsCompact s)
      fun s => I.symm '' (s inter range I) := fun x => by
    rw [← I.symm_map_nhdsWithin_range]
    exact ((compact_basis_nhds (I x)).inf_principal _).map _
  refine .of_hasBasis this ?_
  rintro x s ⟨-, hsc⟩
  exact (hsc.inter_right I.isClosed_range).image I.continuous_symm

中文:
定理 locallyCompactSpace
  条件: [局部紧空间 E] (I : 带角模型 𝕜 E H)
  证明: by
  have : forall x : H, (𝓝 x).HasBasis (fun s => s in 𝓝 (I x) ∧ IsCompact s)
      fun s => I.symm '' (s inter range I) := fun x => by
    rw [← I.symm_map_nhdsWithin_range]
    exact ((compact_basis_nhds (I x)).inf_principal _).map _
  refine .of_hasBasis this ?_
  rintro x s ⟨-, hsc⟩
  exact (hsc.inter_right I.isClosed_range).image I.continuous_symm
-/
protected theorem locallyCompactSpace [LocallyCompactSpace E] (I : ModelWithCorners 𝕜 E H) :
    LocallyCompactSpace H := by
  have : forall x : H, (𝓝 x).HasBasis (fun s => s in 𝓝 (I x) ∧ IsCompact s)
      fun s => I.symm '' (s inter range I) := fun x => by
    rw [← I.symm_map_nhdsWithin_range]
    exact ((compact_basis_nhds (I x)).inf_principal _).map _
  refine .of_hasBasis this ?_
  rintro x s ⟨-, hsc⟩
  exact (hsc.inter_right I.isClosed_range).image I.continuous_symm

open TopologicalSpace

/--
theorem `secondCountableTopology` / 定理 `secondCountableTopology`

English:
theorem secondCountableTopology
  given: [SecondCountableTopology E] (I : ModelWithCorners 𝕜 E H)
  proof: I.isClosedEmbedding.isEmbedding.secondCountableTopology

include I in

中文:
定理 secondCountableTopology
  条件: [第二可数拓扑 E] (I : 带角模型 𝕜 E H)
  证明: I.isClosedEmbedding.isEmbedding.secondCountableTopology

include I in
-/
protected theorem secondCountableTopology [SecondCountableTopology E] (I : ModelWithCorners 𝕜 E H) :
    SecondCountableTopology H :=
  I.isClosedEmbedding.isEmbedding.secondCountableTopology

include I in
/--
theorem `t1Space` / 定理 `t1Space`

English:
theorem t1Space
  given: (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  statement: T1Space M
  proof: by
  have : T2Space H := I.isClosedEmbedding.toIsEmbedding.t2Space
  exact ChartedSpace.t1Space H M

中文:
定理 t1Space
  条件: (M : 类型) [拓扑空间 M] [Charted空间 H M]
  结论: T1空间 M
  证明: by
  have : T2Space H := I.isClosedEmbedding.toIsEmbedding.t2Space
  exact ChartedSpace.t1Space H M
-/
protected theorem t1Space (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : T1Space M := by
  have : T2Space H := I.isClosedEmbedding.toIsEmbedding.t2Space
  exact ChartedSpace.t1Space H M

end ModelWithCorners

section

variable (𝕜 E)

/-- In the trivial model with corners, the associated `PartialEquiv` is the identity. -/
@[simp, mfld_simps]
/--
theorem `modelWithCornersSelf_partialEquiv` / 定理 `modelWithCornersSelf_partialEquiv`

English:
theorem modelWithCornersSelf_partialEquiv
  statement: 𝓘(𝕜, E).toPartialEquiv = PartialEquiv.refl E
  proof: rfl

@[simp, mfld_simps]

中文:
定理 modelWithCornersSelf_partialEquiv
  结论: 𝓘(𝕜, E).toPartialEquiv = 部分等价.refl E
  证明: rfl

@[simp, mfld_simps]
-/
theorem modelWithCornersSelf_partialEquiv : 𝓘(𝕜, E).toPartialEquiv = PartialEquiv.refl E :=
  rfl

@[simp, mfld_simps]
/--
theorem `modelWithCornersSelf_coe` / 定理 `modelWithCornersSelf_coe`

English:
theorem modelWithCornersSelf_coe
  statement: (𝓘(𝕜, E) : E -> E) = id
  proof: rfl

@[simp, mfld_simps]

中文:
定理 modelWithCornersSelf_coe
  结论: (𝓘(𝕜, E) : E -> E) = id
  证明: rfl

@[simp, mfld_simps]
-/
theorem modelWithCornersSelf_coe : (𝓘(𝕜, E) : E -> E) = id :=
  rfl

@[simp, mfld_simps]
/--
theorem `modelWithCornersSelf_coe_symm` / 定理 `modelWithCornersSelf_coe_symm`

English:
theorem modelWithCornersSelf_coe_symm
  statement: (𝓘(𝕜, E).symm : E -> E) = id
  proof: rfl

中文:
定理 modelWithCornersSelf_coe_symm
  结论: (𝓘(𝕜, E).symm : E -> E) = id
  证明: rfl

Depends on / 依赖: IsReflexive, IsReflexive.to_isTorsionFree, IsTorsionFree, to_isTorsionFree
-/
theorem modelWithCornersSelf_coe_symm : (𝓘(𝕜, E).symm : E -> E) = id :=
  rfl

end

end

section ModelWithCornersProd

/-- Given two model_with_corners `I` on `(E, H)` and `I'` on `(E', H')`, we define the model with
corners `I.prod I'` on `(E × E', ModelProd H H')`. This appears in particular for the manifold
structure on the tangent bundle to a manifold modelled on `(E, H)`: it will be modelled on
`(E × E, H × E)`. See note [Manifold type tags] for explanation about `ModelProd H H'`
vs `H × H'`. -/
@[simps -isSimp]
/--
Definition of `ModelWithCorners.prod` / `ModelWithCorners.prod` 的定义

English:
definition ModelWithCorners.prod
  signature: {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
  body: { I.toPartialEquiv.prod I'.toPartialEquiv with
    toFun := fun x => (I x.1, I' x.2)
    invFun := fun x => (I.symm x.1, I'.symm x.2)
    source := { x | x.1 in I.source ∧ x.2 in I'.source }
    source_eq := by simp only [ofPred_true, mfld_simps]
    convex_range' := by
      have : range (fun (x : ModelProd H H') => (I x.1, I' x.2)) = range (Prod.map I I') := rfl
      rw [this]; rw [Set.range_prodMap]
      split_ifs with h
      · let := h.rclike
        let := NormedSpace.restrictScalars Real 𝕜 E; let := NormedSpace.restrictScalars Real 𝕜 E'
        exact I.convex_range.prod I'.convex_range
      · simp [range_eq_univ_of_not_isRCLikeNormedField, h]
    nonempty_interior' := by
      have : range (fun (x : ModelProd H H') => (I x.1, I' x.2)) = range (Prod.map I I') := rfl
      simp [this, interior_prod_eq, nonempty_interior]
    continuous_toFun := I.continuous_toFun.prodMap I'.continuous_toFun
    continuous_invFun := I.continuous_invFun.prodMap I'.continuous_invFun }

中文:
定义 带角模型.乘积
  签名: {𝕜 : 类型u} [NontriviallyNormedField 𝕜] {E : 类型v}
  定义体: { I.toPartialEquiv.prod I'.toPartialEquiv with
    toFun := fun x => (I x.1, I' x.2)
    invFun := fun x => (I.symm x.1, I'.symm x.2)
    source := { x | x.1 in I.source ∧ x.2 in I'.source }
    source_eq := by simp only [ofPred_true, mfld_simps]
    convex_range' := by
      have : range (fun (x : ModelProd H H') => (I x.1, I' x.2)) = range (Prod.map I I') := rfl
      rw [this]; rw [Set.range_prodMap]
      split_ifs with h
      · let := h.rclike
        let := NormedSpace.restrictScalars Real 𝕜 E; let := NormedSpace.restrictScalars Real 𝕜 E'
        exact I.convex_range.prod I'.convex_range
      · simp [range_eq_univ_of_not_isRCLikeNormedField, h]
    nonempty_interior' := by
      have : range (fun (x : ModelProd H H') => (I x.1, I' x.2)) = range (Prod.map I I') := rfl
      simp [this, interior_prod_eq, nonempty_interior]
    continuous_toFun := I.continuous_toFun.prodMap I'.continuous_toFun
    continuous_invFun := I.continuous_invFun.prodMap I'.continuous_invFun }

Depends on / 依赖: I.source, I.symm, I.toPartialEquiv.prod, ModelProd, NormedSpace, NormedSpace.restrictScalars, Prod.map, Set.range_prodMap, convex_range, h.rclike, invFun, mfld_simps, ofPred_true, range_prodMap, rclike, restrictScalars, source, source_eq, split_ifs, toPartialEquiv
-/
def ModelWithCorners.prod {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') :
    ModelWithCorners 𝕜 (E × E') (ModelProd H H') :=
  { I.toPartialEquiv.prod I'.toPartialEquiv with
    toFun := fun x => (I x.1, I' x.2)
    invFun := fun x => (I.symm x.1, I'.symm x.2)
    source := { x | x.1 in I.source ∧ x.2 in I'.source }
    source_eq := by simp only [ofPred_true, mfld_simps]
    convex_range' := by
      have : range (fun (x : ModelProd H H') => (I x.1, I' x.2)) = range (Prod.map I I') := rfl
      rw [this]; rw [Set.range_prodMap]
      split_ifs with h
      · let := h.rclike
        let := NormedSpace.restrictScalars Real 𝕜 E; let := NormedSpace.restrictScalars Real 𝕜 E'
        exact I.convex_range.prod I'.convex_range
      · simp [range_eq_univ_of_not_isRCLikeNormedField, h]
    nonempty_interior' := by
      have : range (fun (x : ModelProd H H') => (I x.1, I' x.2)) = range (Prod.map I I') := rfl
      simp [this, interior_prod_eq, nonempty_interior]
    continuous_toFun := I.continuous_toFun.prodMap I'.continuous_toFun
    continuous_invFun := I.continuous_invFun.prodMap I'.continuous_invFun }

/--
Definition of `ModelWithCorners.pi` / `ModelWithCorners.pi` 的定义

English:
definition ModelWithCorners.pi
  signature: {𝕜 : Type u} [NontriviallyNormedField 𝕜] {ι : Type v} [Fintype ι]
  body: PartialEquiv.pi fun i => (I i).toPartialEquiv
  source_eq := by simp only [pi_univ, mfld_simps]
  convex_range' := by
    rw [PartialEquiv.pi_apply]; rw [Set.range_piMap]
    split_ifs with h
    · let := h.rclike
      let := fun i => NormedSpace.restrictScalars Real 𝕜 (E i)
      exact convex_pi fun i _hi => (I i).convex_range
    · simp [range_eq_univ_of_not_isRCLikeNormedField, h]
  nonempty_interior' := by
    rw [PartialEquiv.pi_apply]; rw [Set.range_piMap]
    simp [interior_pi_set finite_univ, univ_pi_nonempty_iff, nonempty_interior]
  continuous_toFun := continuous_pi fun i => (I i).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (I i).continuous_symm.comp (continuous_apply i)

中文:
定义 带角模型.pi
  签名: {𝕜 : 类型u} [NontriviallyNormedField 𝕜] {ι : 类型v} [有限类型 ι]
  定义体: PartialEquiv.pi fun i => (I i).toPartialEquiv
  source_eq := by simp only [pi_univ, mfld_simps]
  convex_range' := by
    rw [PartialEquiv.pi_apply]; rw [Set.range_piMap]
    split_ifs with h
    · let := h.rclike
      let := fun i => NormedSpace.restrictScalars Real 𝕜 (E i)
      exact convex_pi fun i _hi => (I i).convex_range
    · simp [range_eq_univ_of_not_isRCLikeNormedField, h]
  nonempty_interior' := by
    rw [PartialEquiv.pi_apply]; rw [Set.range_piMap]
    simp [interior_pi_set finite_univ, univ_pi_nonempty_iff, nonempty_interior]
  continuous_toFun := continuous_pi fun i => (I i).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (I i).continuous_symm.comp (continuous_apply i)

Depends on / 依赖: PartialEquiv, PartialEquiv.pi, toPartialEquiv
-/
def ModelWithCorners.pi {𝕜 : Type u} [NontriviallyNormedField 𝕜] {ι : Type v} [Fintype ι]
    {E : ι -> Type w} [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)] {H : ι -> Type u'}
    [forall i, TopologicalSpace (H i)] (I : forall i, ModelWithCorners 𝕜 (E i) (H i)) :
    ModelWithCorners 𝕜 (forall i, E i) (ModelPi H) where
  toPartialEquiv := PartialEquiv.pi fun i => (I i).toPartialEquiv
  source_eq := by simp only [pi_univ, mfld_simps]
  convex_range' := by
    rw [PartialEquiv.pi_apply]; rw [Set.range_piMap]
    split_ifs with h
    · let := h.rclike
      let := fun i => NormedSpace.restrictScalars Real 𝕜 (E i)
      exact convex_pi fun i _hi => (I i).convex_range
    · simp [range_eq_univ_of_not_isRCLikeNormedField, h]
  nonempty_interior' := by
    rw [PartialEquiv.pi_apply]; rw [Set.range_piMap]
    simp [interior_pi_set finite_univ, univ_pi_nonempty_iff, nonempty_interior]
  continuous_toFun := continuous_pi fun i => (I i).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (I i).continuous_symm.comp (continuous_apply i)

/--
Definition of `ModelWithCorners.tangent` / `ModelWithCorners.tangent` 的定义

English:
abbreviation ModelWithCorners.tangent
  signature: {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
  body: I.prod 𝓘(𝕜, E)

中文:
缩写 带角模型.tangent
  签名: {𝕜 : 类型u} [NontriviallyNormedField 𝕜] {E : 类型v}
  定义体: I.prod 𝓘(𝕜, E)

Depends on / 依赖: I.prod
-/
abbrev ModelWithCorners.tangent {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : ModelWithCorners 𝕜 (E × E) (ModelProd H E) :=
  I.prod 𝓘(𝕜, E)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H'] {G : Type*}
  [TopologicalSpace G] {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 F G}

@[simp, mfld_simps]
/--
theorem `modelWithCorners_prod_toPartialEquiv` / 定理 `modelWithCorners_prod_toPartialEquiv`

English:
theorem modelWithCorners_prod_toPartialEquiv
  proof: rfl

@[simp, mfld_simps]

中文:
定理 modelWithCorners_prod_toPartialEquiv
  证明: rfl

@[simp, mfld_simps]
-/
theorem modelWithCorners_prod_toPartialEquiv :
    (I.prod J).toPartialEquiv = I.toPartialEquiv.prod J.toPartialEquiv :=
  rfl

@[simp, mfld_simps]
/--
theorem `modelWithCorners_prod_coe` / 定理 `modelWithCorners_prod_coe`

English:
theorem modelWithCorners_prod_coe
  given: (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
  proof: rfl

@[simp, mfld_simps]

中文:
定理 modelWithCorners_prod_coe
  条件: (I : 带角模型 𝕜 E H) (I' : 带角模型 𝕜 E' H')
  证明: rfl

@[simp, mfld_simps]
-/
theorem modelWithCorners_prod_coe (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') :
    (I.prod I' : _ × _ -> _ × _) = Prod.map I I' :=
  rfl

@[simp, mfld_simps]
/--
theorem `modelWithCorners_prod_coe_symm` / 定理 `modelWithCorners_prod_coe_symm`

English:
theorem modelWithCorners_prod_coe_symm
  statement: (I : ModelWithCorners 𝕜 E H)
  proof: rfl

中文:
定理 modelWithCorners_prod_coe_symm
  结论: (I : 带角模型 𝕜 E H)
  证明: rfl
-/
theorem modelWithCorners_prod_coe_symm (I : ModelWithCorners 𝕜 E H)
    (I' : ModelWithCorners 𝕜 E' H') :
    ((I.prod I').symm : _ × _ -> _ × _) = Prod.map I.symm I'.symm :=
  rfl

/--
theorem `modelWithCornersSelf_prod` / 定理 `modelWithCornersSelf_prod`

English:
theorem modelWithCornersSelf_prod
  statement: 𝓘(𝕜, E × F) = 𝓘(𝕜, E).prod 𝓘(𝕜, F)
  proof: by ext1 <;> simp

中文:
定理 modelWithCornersSelf_prod
  结论: 𝓘(𝕜, E × F) = 𝓘(𝕜, E).乘积 𝓘(𝕜, F)
  证明: by ext1 <;> simp
-/
theorem modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜, E).prod 𝓘(𝕜, F) := by ext1 <;> simp

/--
theorem `ModelWithCorners.range_prod` / 定理 `ModelWithCorners.range_prod`

English:
theorem ModelWithCorners.range_prod
  statement: range (I.prod J) = range I ×ˢ range J
  proof: by
  simp_rw [← ModelWithCorners.target_eq]; rfl

中文:
定理 带角模型.range_prod
  结论: range (I.乘积 J) = range I ×ˢ range J
  证明: by
  simp_rw [← ModelWithCorners.target_eq]; rfl

Depends on / 依赖: ModelWithCorners, ModelWithCorners.target_eq, simp_rw, target_eq
-/
theorem ModelWithCorners.range_prod : range (I.prod J) = range I ×ˢ range J := by
  simp_rw [← ModelWithCorners.target_eq]; rfl

end ModelWithCornersProd

section Boundaryless

/--
Definition of `ModelWithCorners.Boundaryless` / `ModelWithCorners.Boundaryless` 的定义

English:
class ModelWithCorners.Boundaryless
  parameters: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  axioms and operations (1):
    - range_eq_univ : range I = univ

中文:
类 带角模型.无边界
  参数: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {E : 类型}
  公理与运算 (1 个):
    - range_eq_univ : range I = univ
-/
class ModelWithCorners.Boundaryless {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : Prop where
  range_eq_univ : range I = univ

/--
theorem `ModelWithCorners.range_eq_univ` / 定理 `ModelWithCorners.range_eq_univ`

English:
theorem ModelWithCorners.range_eq_univ
  statement: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  proof: ModelWithCorners.Boundaryless.range_eq_univ

中文:
定理 带角模型.range_eq_univ
  结论: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {E : 类型}
  证明: ModelWithCorners.Boundaryless.range_eq_univ

Depends on / 依赖: Boundaryless, ModelWithCorners, ModelWithCorners.Boundaryless.range_eq_univ, range_eq_univ
-/
theorem ModelWithCorners.range_eq_univ {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] :
    range I = univ := ModelWithCorners.Boundaryless.range_eq_univ

/-- If `I` is a `ModelWithCorners.Boundaryless` model, then it is a homeomorphism. -/
@[simps +simpRhs]
/--
Definition of `ModelWithCorners.toHomeomorph` / `ModelWithCorners.toHomeomorph` 的定义

English:
definition ModelWithCorners.toHomeomorph
  signature: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  body: I
  left_inv := I.left_inv
right_inv _ := I.right_inv I.range_eq_univ.symm ▸ mem_univ _

中文:
定义 带角模型.toHomeomorph
  签名: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {E : 类型}
  定义体: I
  left_inv := I.left_inv
right_inv _ := I.right_inv I.range_eq_univ.symm ▸ mem_univ _
-/
def ModelWithCorners.toHomeomorph {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] : H ≃ₜ E where
  __ := I
  left_inv := I.left_inv
right_inv _ := I.right_inv I.range_eq_univ.symm ▸ mem_univ _

/--
Instance `modelWithCornersSelf_boundaryless` / 实例 `modelWithCornersSelf_boundaryless`

English:
instance modelWithCornersSelf_boundaryless
  signature: (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
  body: ⟨by simp⟩

中文:
实例 modelWithCornersSelf_boundaryless
  签名: (𝕜 : 类型) [NontriviallyNormedField 𝕜] (E : 类型)
  定义体: ⟨by simp⟩
-/
instance modelWithCornersSelf_boundaryless (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : (modelWithCornersSelf 𝕜 E).Boundaryless :=
  ⟨by simp⟩

/--
Instance `ModelWithCorners.range_eq_univ_prod` / 实例 `ModelWithCorners.range_eq_univ_prod`

English:
instance ModelWithCorners.range_eq_univ_prod
  signature: {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
  body: by
  constructor
  dsimp
  rw [Set.range_prodMap]; rw [ModelWithCorners.Boundaryless.range_eq_univ]; rw [ModelWithCorners.Boundaryless.range_eq_univ]; rw [univ_prod_univ]

中文:
实例 带角模型.range_eq_univ_prod
  签名: {𝕜 : 类型u} [NontriviallyNormedField 𝕜] {E : 类型v}
  定义体: by
  constructor
  dsimp
  rw [Set.range_prodMap]; rw [ModelWithCorners.Boundaryless.range_eq_univ]; rw [ModelWithCorners.Boundaryless.range_eq_univ]; rw [univ_prod_univ]

Depends on / 依赖: Boundaryless, ModelWithCorners, ModelWithCorners.Boundaryless.range_eq_univ, Set.range_prodMap, range_eq_univ, range_prodMap, univ_prod_univ
-/
instance ModelWithCorners.range_eq_univ_prod {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] {E' : Type v'} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
    [I'.Boundaryless] : (I.prod I').Boundaryless := by
  constructor
  dsimp
  rw [Set.range_prodMap]; rw [ModelWithCorners.Boundaryless.range_eq_univ]; rw [ModelWithCorners.Boundaryless.range_eq_univ]; rw [univ_prod_univ]

end Boundaryless

section contDiffGroupoid

/-! ### `C^n` functions on models with corners -/


variable {m n : Nat∞ω} {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]

variable (n I) in
/--
Definition of `contDiffPregroupoid` / `contDiffPregroupoid` 的定义

English:
definition contDiffPregroupoid
  signature: : Pregroupoid H where
  body: ContDiffOn 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s inter range I)
  comp {f g u v} hf hg _ _ _ := by
    have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
    simp only [this]
    refine hg.comp (hf.mono fun x ⟨hx1, hx2⟩ => ⟨hx1.1, hx2⟩) ?_
    rintro x ⟨hx1, _⟩
    simp only [mfld_simps] at hx1 ⊢
    exact hx1.2
  id_mem := by
    apply ContDiffOn.congr contDiff_id.contDiffOn
    rintro x ⟨_, hx2⟩
    rcases mem_range.1 hx2 with ⟨y, hy⟩
    rw [← hy]
    simp only [mfld_simps]
  locality {f u} _ H := by
    apply contDiffOn_of_locally_contDiffOn
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rcases H x hy1 with ⟨v, v_open, xv, hv⟩
    have : I.symm ⁻¹' (u inter v) inter range I = I.symm ⁻¹' u inter range I inter I.symm ⁻¹' v := by
      rw [preimage_inter]; rw [inter_assoc]; rw [inter_assoc]
      congr 1
      rw [inter_comm]
    rw [this] at hv
    exact ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by simpa, hv⟩
  congr {f g u} _ fg hf := by
    apply hf.congr
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rw [fg _ hy1]

中文:
定义 contDiffPregroupoid
  签名: : Pregroupoid H where
  定义体: ContDiffOn 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s inter range I)
  comp {f g u v} hf hg _ _ _ := by
    have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
    simp only [this]
    refine hg.comp (hf.mono fun x ⟨hx1, hx2⟩ => ⟨hx1.1, hx2⟩) ?_
    rintro x ⟨hx1, _⟩
    simp only [mfld_simps] at hx1 ⊢
    exact hx1.2
  id_mem := by
    apply ContDiffOn.congr contDiff_id.contDiffOn
    rintro x ⟨_, hx2⟩
    rcases mem_range.1 hx2 with ⟨y, hy⟩
    rw [← hy]
    simp only [mfld_simps]
  locality {f u} _ H := by
    apply contDiffOn_of_locally_contDiffOn
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rcases H x hy1 with ⟨v, v_open, xv, hv⟩
    have : I.symm ⁻¹' (u inter v) inter range I = I.symm ⁻¹' u inter range I inter I.symm ⁻¹' v := by
      rw [preimage_inter]; rw [inter_assoc]; rw [inter_assoc]
      congr 1
      rw [inter_comm]
    rw [this] at hv
    exact ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by simpa, hv⟩
  congr {f g u} _ fg hf := by
    apply hf.congr
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rw [fg _ hy1]

Depends on / 依赖: ContDiffOn, I.symm
-/
def contDiffPregroupoid : Pregroupoid H where
  property f s := ContDiffOn 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s inter range I)
  comp {f g u v} hf hg _ _ _ := by
    have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
    simp only [this]
    refine hg.comp (hf.mono fun x ⟨hx1, hx2⟩ => ⟨hx1.1, hx2⟩) ?_
    rintro x ⟨hx1, _⟩
    simp only [mfld_simps] at hx1 ⊢
    exact hx1.2
  id_mem := by
    apply ContDiffOn.congr contDiff_id.contDiffOn
    rintro x ⟨_, hx2⟩
    rcases mem_range.1 hx2 with ⟨y, hy⟩
    rw [← hy]
    simp only [mfld_simps]
  locality {f u} _ H := by
    apply contDiffOn_of_locally_contDiffOn
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rcases H x hy1 with ⟨v, v_open, xv, hv⟩
    have : I.symm ⁻¹' (u inter v) inter range I = I.symm ⁻¹' u inter range I inter I.symm ⁻¹' v := by
      rw [preimage_inter]; rw [inter_assoc]; rw [inter_assoc]
      congr 1
      rw [inter_comm]
    rw [this] at hv
    exact ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by simpa, hv⟩
  congr {f g u} _ fg hf := by
    apply hf.congr
    rintro y ⟨hy1, hy2⟩
    rcases mem_range.1 hy2 with ⟨x, hx⟩
    rw [← hx] at hy1 ⊢
    simp only [mfld_simps] at hy1 ⊢
    rw [fg _ hy1]

variable (n I) in
/--
Definition of `contDiffGroupoid` / `contDiffGroupoid` 的定义

English:
definition contDiffGroupoid
  signature: : StructureGroupoid H
  body: Pregroupoid.groupoid (contDiffPregroupoid n I)

中文:
定义 contDiffGroupoid
  签名: : StructureGroupoid H
  定义体: Pregroupoid.groupoid (contDiffPregroupoid n I)

Depends on / 依赖: Pregroupoid, Pregroupoid.groupoid, contDiffPregroupoid, groupoid
-/
def contDiffGroupoid : StructureGroupoid H :=
  Pregroupoid.groupoid (contDiffPregroupoid n I)

/--
theorem `contDiffGroupoid_le` / 定理 `contDiffGroupoid_le`

English:
theorem contDiffGroupoid_le
  given: (h : m <= n)
  statement: contDiffGroupoid n I <= contDiffGroupoid m I
  proof: by
  rw [contDiffGroupoid]; rw [contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  exact ContDiffOn.of_le hfs h

中文:
定理 contDiffGroupoid_le
  条件: (h : m <= n)
  结论: contDiffGroupoid n I <= contDiffGroupoid m I
  证明: by
  rw [contDiffGroupoid]; rw [contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  exact ContDiffOn.of_le hfs h

Depends on / 依赖: ContDiffOn, ContDiffOn.of_le, contDiffGroupoid, groupoid_of_pregroupoid_le, of_le
-/
theorem contDiffGroupoid_le (h : m <= n) : contDiffGroupoid n I <= contDiffGroupoid m I := by
  rw [contDiffGroupoid]; rw [contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  exact ContDiffOn.of_le hfs h

/--
theorem `contDiffGroupoid_zero_eq` / 定理 `contDiffGroupoid_zero_eq`

English:
theorem contDiffGroupoid_zero_eq
  statement: contDiffGroupoid 0 I = continuousGroupoid H
  proof: by
  apply le_antisymm le_top
  intro u _
  -- we have to check that every open partial homeomorphism belongs to `contDiffGroupoid 0 I`,
  -- by unfolding its definition
  change u in contDiffGroupoid 0 I
  rw [contDiffGroupoid]; rw [mem_groupoid_of_pregroupoid]; rw [contDiffPregroupoid]
  simp only [contDiffOn_zero]
  constructor
  · refine I.continuous.comp_continuousOn (u.continuousOn.comp I.continuousOn_symm ?_)
    exact (mapsTo_preimage _ _).mono_left inter_subset_left
  · refine I.continuous.comp_continuousOn (u.symm.continuousOn.comp I.continuousOn_symm ?_)
    exact (mapsTo_preimage _ _).mono_left inter_subset_left

中文:
定理 contDiffGroupoid_zero_eq
  结论: contDiffGroupoid 0 I = continuousGroupoid H
  证明: by
  apply le_antisymm le_top
  intro u _
  -- we have to check that every open partial homeomorphism belongs to `contDiffGroupoid 0 I`,
  -- by unfolding its definition
  change u in contDiffGroupoid 0 I
  rw [contDiffGroupoid]; rw [mem_groupoid_of_pregroupoid]; rw [contDiffPregroupoid]
  simp only [contDiffOn_zero]
  constructor
  · refine I.continuous.comp_continuousOn (u.continuousOn.comp I.continuousOn_symm ?_)
    exact (mapsTo_preimage _ _).mono_left inter_subset_left
  · refine I.continuous.comp_continuousOn (u.symm.continuousOn.comp I.continuousOn_symm ?_)
    exact (mapsTo_preimage _ _).mono_left inter_subset_left

Depends on / 依赖: le_antisymm, le_top
-/
theorem contDiffGroupoid_zero_eq : contDiffGroupoid 0 I = continuousGroupoid H := by
  apply le_antisymm le_top
  intro u _
  -- we have to check that every open partial homeomorphism belongs to `contDiffGroupoid 0 I`,
  -- by unfolding its definition
  change u in contDiffGroupoid 0 I
  rw [contDiffGroupoid]; rw [mem_groupoid_of_pregroupoid]; rw [contDiffPregroupoid]
  simp only [contDiffOn_zero]
  constructor
  · refine I.continuous.comp_continuousOn (u.continuousOn.comp I.continuousOn_symm ?_)
    exact (mapsTo_preimage _ _).mono_left inter_subset_left
  · refine I.continuous.comp_continuousOn (u.symm.continuousOn.comp I.continuousOn_symm ?_)
    exact (mapsTo_preimage _ _).mono_left inter_subset_left

-- FIXME: does this generalise to other groupoids? The argument is not specific
-- to C^n functions, but uses something about the groupoid's property that is not easy to abstract.
/--
lemma `ContDiffGroupoid.mem_of_source_eq_empty` / 引理 `ContDiffGroupoid.mem_of_source_eq_empty`

English:
lemma ContDiffGroupoid.mem_of_source_eq_empty
  statement: (f : OpenPartialHomeomorph H H)
  proof: by
  constructor
  · intro x ⟨hx, _⟩
    rw [mem_preimage] at hx
    simp_all only [mem_empty_iff_false]
  · intro x ⟨hx, _⟩
    have : f.target = ∅ := by simp [← f.image_source_eq_target, hf]
    simp_all

include I in

中文:
引理 ContDiffGroupoid.mem_of_source_eq_empty
  结论: (f : OpenPartialHomeomorph H H)
  证明: by
  constructor
  · intro x ⟨hx, _⟩
    rw [mem_preimage] at hx
    simp_all only [mem_empty_iff_false]
  · intro x ⟨hx, _⟩
    have : f.target = ∅ := by simp [← f.image_source_eq_target, hf]
    simp_all

include I in

Depends on / 依赖: f.image_source_eq_target, f.target, image_source_eq_target, mem_empty_iff_false, mem_preimage, target
-/
lemma ContDiffGroupoid.mem_of_source_eq_empty (f : OpenPartialHomeomorph H H)
    (hf : f.source = ∅) : f in contDiffGroupoid n I := by
  constructor
  · intro x ⟨hx, _⟩
    rw [mem_preimage] at hx
    simp_all only [mem_empty_iff_false]
  · intro x ⟨hx, _⟩
    have : f.target = ∅ := by simp [← f.image_source_eq_target, hf]
    simp_all

include I in
/--
lemma `ContinuousGroupoid.mem_of_source_eq_empty` / 引理 `ContinuousGroupoid.mem_of_source_eq_empty`

English:
lemma ContinuousGroupoid.mem_of_source_eq_empty
  statement: (f : OpenPartialHomeomorph H H)
  proof: by
  rw [← contDiffGroupoid_zero_eq (I := I)]
  exact ContDiffGroupoid.mem_of_source_eq_empty f hf

中文:
引理 ContinuousGroupoid.mem_of_source_eq_empty
  结论: (f : OpenPartialHomeomorph H H)
  证明: by
  rw [← contDiffGroupoid_zero_eq (I := I)]
  exact ContDiffGroupoid.mem_of_source_eq_empty f hf

Depends on / 依赖: ContDiffGroupoid, ContDiffGroupoid.mem_of_source_eq_empty, contDiffGroupoid_zero_eq, mem_of_source_eq_empty
-/
lemma ContinuousGroupoid.mem_of_source_eq_empty (f : OpenPartialHomeomorph H H)
    (hf : f.source = ∅) : f in continuousGroupoid H := by
  rw [← contDiffGroupoid_zero_eq (I := I)]
  exact ContDiffGroupoid.mem_of_source_eq_empty f hf

/--
theorem `ofSet_mem_contDiffGroupoid` / 定理 `ofSet_mem_contDiffGroupoid`

English:
theorem ofSet_mem_contDiffGroupoid
  given: {s : Set H} (hs : IsOpen s)
  proof: by
  rw [contDiffGroupoid]; rw [mem_groupoid_of_pregroupoid]
  suffices h : ContDiffOn 𝕜 n (I ∘ I.symm) (I.symm ⁻¹' s inter range I) by
    simp [h, contDiffPregroupoid]
  have : ContDiffOn 𝕜 n id (univ : Set E) := contDiff_id.contDiffOn
  exact this.congr_mono (fun x hx => I.right_inv hx.2) (subset_univ _)

中文:
定理 ofSet_mem_contDiffGroupoid
  条件: {s : 集合 H} (hs : 是开集 s)
  证明: by
  rw [contDiffGroupoid]; rw [mem_groupoid_of_pregroupoid]
  suffices h : ContDiffOn 𝕜 n (I ∘ I.symm) (I.symm ⁻¹' s inter range I) by
    simp [h, contDiffPregroupoid]
  have : ContDiffOn 𝕜 n id (univ : Set E) := contDiff_id.contDiffOn
  exact this.congr_mono (fun x hx => I.right_inv hx.2) (subset_univ _)

Depends on / 依赖: ContDiffOn, I.right_inv, I.symm, congr_mono, contDiffGroupoid, contDiffOn, contDiffPregroupoid, contDiff_id, contDiff_id.contDiffOn, mem_groupoid_of_pregroupoid, right_inv, subset_univ, this.congr_mono
-/
theorem ofSet_mem_contDiffGroupoid {s : Set H} (hs : IsOpen s) :
    OpenPartialHomeomorph.ofSet s hs in contDiffGroupoid n I := by
  rw [contDiffGroupoid]; rw [mem_groupoid_of_pregroupoid]
  suffices h : ContDiffOn 𝕜 n (I ∘ I.symm) (I.symm ⁻¹' s inter range I) by
    simp [h, contDiffPregroupoid]
  have : ContDiffOn 𝕜 n id (univ : Set E) := contDiff_id.contDiffOn
  exact this.congr_mono (fun x hx => I.right_inv hx.2) (subset_univ _)

/--
theorem `symm_trans_mem_contDiffGroupoid` / 定理 `symm_trans_mem_contDiffGroupoid`

English:
theorem symm_trans_mem_contDiffGroupoid
  given: (e : OpenPartialHomeomorph M H)
  proof: haveI : e.symm.trans e ≈ OpenPartialHomeomorph.ofSet e.target e.open_target :=
    OpenPartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_contDiffGroupoid e.open_target) this

中文:
定理 symm_trans_mem_contDiffGroupoid
  条件: (e : OpenPartialHomeomorph M H)
  证明: haveI : e.symm.trans e ≈ OpenPartialHomeomorph.ofSet e.target e.open_target :=
    OpenPartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_contDiffGroupoid e.open_target) this

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.ofSet, OpenPartialHomeomorph.symm_trans_self, StructureGroupoid, StructureGroupoid.mem_of_eqOnSource, e.open_target, e.symm.trans, e.target, mem_of_eqOnSource, ofSet_mem_contDiffGroupoid, open_target, symm_trans_self, target
-/
theorem symm_trans_mem_contDiffGroupoid (e : OpenPartialHomeomorph M H) :
    e.symm.trans e in contDiffGroupoid n I :=
  haveI : e.symm.trans e ≈ OpenPartialHomeomorph.ofSet e.target e.open_target :=
    OpenPartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_contDiffGroupoid e.open_target) this

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']

set_option backward.isDefEq.respectTransparency false in
/--
theorem `contDiffGroupoid_prod` / 定理 `contDiffGroupoid_prod`

English:
theorem contDiffGroupoid_prod
  statement: {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  proof: by
  obtain ⟨he, he_symm⟩ := he
  obtain ⟨he', he'_symm⟩ := he'
  constructor <;> simp only [OpenPartialHomeomorph.prod_toPartialHomeomorph,
    contDiffPregroupoid]
  · have h3 := ContDiffOn.prodMap he he'
    rw [← I.image_eq]; rw [← I'.image_eq]; rw [prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3
  · have h3 := ContDiffOn.prodMap he_symm he'_symm
    rw [← I.image_eq]; rw [← I'.image_eq]; rw [prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3

中文:
定理 contDiffGroupoid_prod
  结论: {I : 带角模型 𝕜 E H} {I' : 带角模型 𝕜 E' H'}
  证明: by
  obtain ⟨he, he_symm⟩ := he
  obtain ⟨he', he'_symm⟩ := he'
  constructor <;> simp only [OpenPartialHomeomorph.prod_toPartialHomeomorph,
    contDiffPregroupoid]
  · have h3 := ContDiffOn.prodMap he he'
    rw [← I.image_eq]; rw [← I'.image_eq]; rw [prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3
  · have h3 := ContDiffOn.prodMap he_symm he'_symm
    rw [← I.image_eq]; rw [← I'.image_eq]; rw [prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3

Depends on / 依赖: ContDiffOn, ContDiffOn.prodMap, I.image_eq, I.prod, OpenPartialHomeomorph, OpenPartialHomeomorph.prod_toPartialHomeomorph, _symm, contDiffPregroupoid, he_symm, image_eq, prodMap, prod_image_image_eq, prod_toPartialHomeomorph
-/
theorem contDiffGroupoid_prod {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    {e : OpenPartialHomeomorph H H} {e' : OpenPartialHomeomorph H' H'}
    (he : e in contDiffGroupoid n I) (he' : e' in contDiffGroupoid n I') :
    e.prod e' in contDiffGroupoid n (I.prod I') := by
  obtain ⟨he, he_symm⟩ := he
  obtain ⟨he', he'_symm⟩ := he'
  constructor <;> simp only [OpenPartialHomeomorph.prod_toPartialHomeomorph,
    contDiffPregroupoid]
  · have h3 := ContDiffOn.prodMap he he'
    rw [← I.image_eq]; rw [← I'.image_eq]; rw [prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3
  · have h3 := ContDiffOn.prodMap he_symm he'_symm
    rw [← I.image_eq]; rw [← I'.image_eq]; rw [prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ClosedUnderRestriction (contDiffGroupoid n I)
  body: (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      apply (contDiffGroupoid n I).mem_of_eqOnSource' _ _ _ hes
      exact ofSet_mem_contDiffGroupoid hs)

中文:
实例 :
  签名: ClosedUnderRestriction (contDiffGroupoid n I)
  定义体: (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      apply (contDiffGroupoid n I).mem_of_eqOnSource' _ _ _ hes
      exact ofSet_mem_contDiffGroupoid hs)

Depends on / 依赖: StructureGroupoid, StructureGroupoid.le_iff, closedUnderRestriction_iff_id_le, contDiffGroupoid, le_iff, mem_of_eqOnSource, ofSet_mem_contDiffGroupoid
-/
instance : ClosedUnderRestriction (contDiffGroupoid n I) :=
  (closedUnderRestriction_iff_id_le _).mpr
    (by
      rw [StructureGroupoid.le_iff]
      rintro e ⟨s, hs, hes⟩
      apply (contDiffGroupoid n I).mem_of_eqOnSource' _ _ _ hes
      exact ofSet_mem_contDiffGroupoid hs)

end contDiffGroupoid

section IsManifold

/-! ### `C^n` manifolds (possibly with boundary or corners) -/

/--
Definition of `IsManifold` / `IsManifold` 的定义

English:
class IsManifold
  parameters: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  extends: HasGroupoid M (contDiffGroupoid n I)
  (no additional axioms)

中文:
类 是流形
  参数: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {E : 类型}
  继承: 有群胚 M (contDiffGroupoid n I)
  (无附加公理)
-/
class IsManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : Nat∞ω) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] : Prop
    extends HasGroupoid M (contDiffGroupoid n I)

/--
theorem `IsManifold.mk'` / 定理 `IsManifold.mk'`

English:
theorem IsManifold.mk'
  statement: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  proof: { gr with }

中文:
定理 是流形.mk'
  结论: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {E : 类型}
  证明: { gr with }
-/
theorem IsManifold.mk' {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : Nat∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [gr : HasGroupoid M (contDiffGroupoid n I)] : IsManifold I n M :=
  { gr with }

/--
theorem `isManifold_of_contDiffOn` / 定理 `isManifold_of_contDiffOn`

English:
theorem isManifold_of_contDiffOn
  statement: {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  proof: by
    have : HasGroupoid M (contDiffGroupoid n I) := hasGroupoid_of_pregroupoid _ (h _ _)
    apply StructureGroupoid.compatible

中文:
定理 isManifold_of_contDiffOn
  结论: {𝕜 : 类型} [NontriviallyNormedField 𝕜]
  证明: by
    have : HasGroupoid M (contDiffGroupoid n I) := hasGroupoid_of_pregroupoid _ (h _ _)
    apply StructureGroupoid.compatible

Depends on / 依赖: HasGroupoid, StructureGroupoid, StructureGroupoid.compatible, compatible, contDiffGroupoid, hasGroupoid_of_pregroupoid
-/
theorem isManifold_of_contDiffOn {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : Nat∞ω) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    (h : forall e e' : OpenPartialHomeomorph M H, e in atlas H M -> e' in atlas H M ->
      ContDiffOn 𝕜 n (I ∘ e.symm ≫ₕ e' ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source inter range I)) :
    IsManifold I n M where
  compatible := by
    have : HasGroupoid M (contDiffGroupoid n I) := hasGroupoid_of_pregroupoid _ (h _ _)
    apply StructureGroupoid.compatible

/--
Instance `instIsManifoldModelSpace` / 实例 `instIsManifoldModelSpace`

English:
instance instIsManifoldModelSpace
  signature: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  body: { hasGroupoid_model_space _ _ with }

中文:
实例 instIsManifoldModelSpace
  签名: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {E : 类型}
  定义体: { hasGroupoid_model_space _ _ with }

Depends on / 依赖: hasGroupoid_model_space
-/
instance instIsManifoldModelSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {n : Nat∞ω} : IsManifold I n H :=
  { hasGroupoid_model_space _ _ with }

end IsManifold

namespace IsManifold

/- We restate in the namespace `IsManifold` some lemmas that hold for general
charted space with a structure groupoid, avoiding the need to specify the groupoid
`contDiffGroupoid n I` explicitly. -/
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {n : Nat∞ω} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/--
theorem `of_le` / 定理 `of_le`

English:
theorem of_le
  statement: {m n : Nat∞ω} (hmn : m <= n)
  proof: by
  have : HasGroupoid M (contDiffGroupoid m I) :=
    hasGroupoid_of_le (G₁ := contDiffGroupoid n I) (by infer_instance)
      (contDiffGroupoid_le hmn)
  exact mk' I m M

中文:
定理 of_le
  结论: {m n : 自然数∞ω} (hmn : m <= n)
  证明: by
  have : HasGroupoid M (contDiffGroupoid m I) :=
    hasGroupoid_of_le (G₁ := contDiffGroupoid n I) (by infer_instance)
      (contDiffGroupoid_le hmn)
  exact mk' I m M
-/
protected theorem of_le {m n : Nat∞ω} (hmn : m <= n)
    [IsManifold I n M] : IsManifold I m M := by
  have : HasGroupoid M (contDiffGroupoid m I) :=
    hasGroupoid_of_le (G₁ := contDiffGroupoid n I) (by infer_instance)
      (contDiffGroupoid_le hmn)
  exact mk' I m M

/--
Definition of `_root_.ENat.LEInfty` / `_root_.ENat.LEInfty` 的定义

English:
class _root_.ENat.LEInfty
  parameters: (m : Nat∞ω)
  axioms and operations (1):
    - out : m <= ∞

中文:
类 _root_.E自然数.LEInfty
  参数: (m : 自然数∞ω)
  公理与运算 (1 个):
    - out : m <= ∞
-/
class _root_.ENat.LEInfty (m : Nat∞ω) where
  out : m <= ∞

open ENat

instance (n : Nat∞) : LEInfty (n : Nat∞ω) := ⟨mod_cast le_top⟩

instance (n : Nat) : LEInfty (n : Nat∞ω) := ⟨mod_cast le_top⟩

instance (n : Nat) [n.AtLeastTwo] : LEInfty (no_index (OfNat.ofNat n) : Nat∞ω) :=
  inferInstanceAs (LEInfty (n : Nat∞ω))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LEInfty (1 : Nat∞ω)
  body: inferInstanceAs (LEInfty ((1 : Nat) : Nat∞ω))

中文:
实例 :
  签名: LEInfty (1 : 自然数∞ω)
  定义体: inferInstanceAs (LEInfty ((1 : Nat) : Nat∞ω))

Depends on / 依赖: LEInfty
-/
instance : LEInfty (1 : Nat∞ω) := inferInstanceAs (LEInfty ((1 : Nat) : Nat∞ω))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LEInfty (0 : Nat∞ω)
  body: inferInstanceAs (LEInfty ((0 : Nat) : Nat∞ω))

中文:
实例 :
  签名: LEInfty (0 : 自然数∞ω)
  定义体: inferInstanceAs (LEInfty ((0 : Nat) : Nat∞ω))

Depends on / 依赖: LEInfty
-/
instance : LEInfty (0 : Nat∞ω) := inferInstanceAs (LEInfty ((0 : Nat) : Nat∞ω))

instance {a : Nat∞ω} [IsManifold I ∞ M] [h : LEInfty a] :
    IsManifold I a M :=
  IsManifold.of_le h.out

instance {a : Nat∞ω} [IsManifold I ω M] :
    IsManifold I a M :=
  IsManifold.of_le le_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsManifold I 0 M
  body: by
  suffices HasGroupoid M (contDiffGroupoid 0 I) from mk' I 0 M
  constructor
  intro e e' he he'
  rw [contDiffGroupoid_zero_eq]
  trivial

中文:
实例 :
  签名: 是流形 I 0 M
  定义体: by
  suffices HasGroupoid M (contDiffGroupoid 0 I) from mk' I 0 M
  constructor
  intro e e' he he'
  rw [contDiffGroupoid_zero_eq]
  trivial

Depends on / 依赖: HasGroupoid, contDiffGroupoid, contDiffGroupoid_zero_eq
-/
instance : IsManifold I 0 M := by
  suffices HasGroupoid M (contDiffGroupoid 0 I) from mk' I 0 M
  constructor
  intro e e' he he'
  rw [contDiffGroupoid_zero_eq]
  trivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsManifold
  signature: I 2 M] :
  body: IsManifold.of_le one_le_two

中文:
实例 [是流形
  签名: I 2 M] :
  定义体: IsManifold.of_le one_le_two

Depends on / 依赖: IsManifold, IsManifold.of_le, of_le, one_le_two
-/
instance [IsManifold I 2 M] :
    IsManifold I 1 M :=
  IsManifold.of_le one_le_two

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsManifold
  signature: I 3 M] : IsManifold I 2 M
  body: IsManifold.of_le (n := 3) (by norm_cast)

中文:
实例 [是流形
  签名: I 3 M] : 是流形 I 2 M
  定义体: IsManifold.of_le (n := 3) (by norm_cast)

Depends on / 依赖: IsManifold, IsManifold.of_le, of_le
-/
instance [IsManifold I 3 M] : IsManifold I 2 M := IsManifold.of_le (n := 3) (by norm_cast)

variable (I n M) in
/--
Definition of `maximalAtlas` / `maximalAtlas` 的定义

English:
definition maximalAtlas
  body: (contDiffGroupoid n I).maximalAtlas M

中文:
定义 maximalAtlas
  定义体: (contDiffGroupoid n I).maximalAtlas M

Depends on / 依赖: contDiffGroupoid, maximalAtlas
-/
def maximalAtlas :=
  (contDiffGroupoid n I).maximalAtlas M

/--
lemma `mem_maximalAtlas_iff` / 引理 `mem_maximalAtlas_iff`

English:
lemma mem_maximalAtlas_iff
  given: {e : OpenPartialHomeomorph M H}
  proof: by
  rfl

中文:
引理 mem_maximalAtlas_iff
  条件: {e : OpenPartialHomeomorph M H}
  证明: by
  rfl
-/
lemma mem_maximalAtlas_iff {e : OpenPartialHomeomorph M H} :
    e in maximalAtlas I n M ↔ e in (contDiffGroupoid n I).maximalAtlas M := by
  rfl

/--
theorem `subset_maximalAtlas` / 定理 `subset_maximalAtlas`

English:
theorem subset_maximalAtlas
  given: [IsManifold I n M]
  statement: atlas H M subseteq maximalAtlas I n M
  proof: StructureGroupoid.subset_maximalAtlas _

中文:
定理 subset_maximalAtlas
  条件: [是流形 I n M]
  结论: atlas H M subseteq maximalAtlas I n M
  证明: StructureGroupoid.subset_maximalAtlas _

Depends on / 依赖: StructureGroupoid, StructureGroupoid.subset_maximalAtlas, subset_maximalAtlas
-/
theorem subset_maximalAtlas [IsManifold I n M] : atlas H M subseteq maximalAtlas I n M :=
  StructureGroupoid.subset_maximalAtlas _

/--
theorem `chart_mem_maximalAtlas` / 定理 `chart_mem_maximalAtlas`

English:
theorem chart_mem_maximalAtlas
  given: [IsManifold I n M] (x : M)
  proof: StructureGroupoid.chart_mem_maximalAtlas _ x

中文:
定理 chart_mem_maximalAtlas
  条件: [是流形 I n M] (x : M)
  证明: StructureGroupoid.chart_mem_maximalAtlas _ x

Depends on / 依赖: StructureGroupoid, StructureGroupoid.chart_mem_maximalAtlas, chart_mem_maximalAtlas
-/
theorem chart_mem_maximalAtlas [IsManifold I n M] (x : M) :
    chartAt H x in maximalAtlas I n M :=
  StructureGroupoid.chart_mem_maximalAtlas _ x

/--
theorem `compatible_of_mem_maximalAtlas` / 定理 `compatible_of_mem_maximalAtlas`

English:
theorem compatible_of_mem_maximalAtlas
  statement: {e e' : OpenPartialHomeomorph M H}
  proof: StructureGroupoid.compatible_of_mem_maximalAtlas he he'

中文:
定理 compatible_of_mem_maximalAtlas
  结论: {e e' : OpenPartialHomeomorph M H}
  证明: StructureGroupoid.compatible_of_mem_maximalAtlas he he'

Depends on / 依赖: StructureGroupoid, StructureGroupoid.compatible_of_mem_maximalAtlas, compatible_of_mem_maximalAtlas
-/
theorem compatible_of_mem_maximalAtlas {e e' : OpenPartialHomeomorph M H}
    (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) :
    e.symm.trans e' in contDiffGroupoid n I :=
  StructureGroupoid.compatible_of_mem_maximalAtlas he he'

/--
lemma `maximalAtlas_subset_of_le` / 引理 `maximalAtlas_subset_of_le`

English:
lemma maximalAtlas_subset_of_le
  given: {m n : Nat∞ω} (h : m <= n)
  proof: StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le h)

中文:
引理 maximalAtlas_subset_of_le
  条件: {m n : 自然数∞ω} (h : m <= n)
  证明: StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le h)

Depends on / 依赖: StructureGroupoid, StructureGroupoid.maximalAtlas_mono, contDiffGroupoid_le, maximalAtlas_mono
-/
lemma maximalAtlas_subset_of_le {m n : Nat∞ω} (h : m <= n) :
    maximalAtlas I n M subseteq maximalAtlas I m M :=
  StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le h)

variable (n) in
/--
Instance `empty` / 实例 `empty`

English:
instance empty
  signature: [IsEmpty M]
  body: by
  apply isManifold_of_contDiffOn
  intro e e' _ _ x hx
  set t := I.symm ⁻¹' (e.symm ≫ₕ e').source inter range I
  -- Since `M` is empty, the condition about compatibility of transition maps is vacuous.
  have : (e.symm ≫ₕ e').source = ∅ := calc (e.symm ≫ₕ e').source
    _ = (e.symm.source) inter e.symm ⁻¹' e'.source := by rw [← OpenPartialHomeomorph.trans_source]
    _ = (e.symm.source) inter e.symm ⁻¹' ∅ := by rw [eq_empty_of_isEmpty (e'.source)]
    _ = (e.symm.source) inter ∅ := by rw [preimage_empty]
    _ = ∅ := inter_empty e.symm.source
  have : t = ∅ := calc t
    _ = I.symm ⁻¹' (e.symm ≫ₕ e').source inter range I := by
      rw [← Subtype.preimage_val_eq_preimage_val_iff]
    _ = ∅ inter range I := by rw [this, preimage_empty]
    _ = ∅ := empty_inter (range I)
  apply (this ▸ hx).elim

中文:
实例 empty
  签名: [是空 M]
  定义体: by
  apply isManifold_of_contDiffOn
  intro e e' _ _ x hx
  set t := I.symm ⁻¹' (e.symm ≫ₕ e').source inter range I
  -- Since `M` is empty, the condition about compatibility of transition maps is vacuous.
  have : (e.symm ≫ₕ e').source = ∅ := calc (e.symm ≫ₕ e').source
    _ = (e.symm.source) inter e.symm ⁻¹' e'.source := by rw [← OpenPartialHomeomorph.trans_source]
    _ = (e.symm.source) inter e.symm ⁻¹' ∅ := by rw [eq_empty_of_isEmpty (e'.source)]
    _ = (e.symm.source) inter ∅ := by rw [preimage_empty]
    _ = ∅ := inter_empty e.symm.source
  have : t = ∅ := calc t
    _ = I.symm ⁻¹' (e.symm ≫ₕ e').source inter range I := by
      rw [← Subtype.preimage_val_eq_preimage_val_iff]
    _ = ∅ inter range I := by rw [this, preimage_empty]
    _ = ∅ := empty_inter (range I)
  apply (this ▸ hx).elim

Depends on / 依赖: I.symm, e.symm, isManifold_of_contDiffOn, source
-/
instance empty [IsEmpty M] : IsManifold I n M := by
  apply isManifold_of_contDiffOn
  intro e e' _ _ x hx
  set t := I.symm ⁻¹' (e.symm ≫ₕ e').source inter range I
  -- Since `M` is empty, the condition about compatibility of transition maps is vacuous.
  have : (e.symm ≫ₕ e').source = ∅ := calc (e.symm ≫ₕ e').source
    _ = (e.symm.source) inter e.symm ⁻¹' e'.source := by rw [← OpenPartialHomeomorph.trans_source]
    _ = (e.symm.source) inter e.symm ⁻¹' ∅ := by rw [eq_empty_of_isEmpty (e'.source)]
    _ = (e.symm.source) inter ∅ := by rw [preimage_empty]
    _ = ∅ := inter_empty e.symm.source
  have : t = ∅ := calc t
    _ = I.symm ⁻¹' (e.symm ≫ₕ e').source inter range I := by
      rw [← Subtype.preimage_val_eq_preimage_val_iff]
    _ = ∅ inter range I := by rw [this, preimage_empty]
    _ = ∅ := empty_inter (range I)
  apply (this ▸ hx).elim

attribute [local instance] ChartedSpace.ofDiscreteTopology in
variable (n) in
/--
theorem `of_discreteTopology` / 定理 `of_discreteTopology`

English:
theorem of_discreteTopology
  given: [DiscreteTopology M] [Unique E]
  proof: by
  apply isManifold_of_contDiffOn _ _ _ (fun _ _ _ _ => contDiff_of_subsingleton.contDiffOn)

中文:
定理 of_discreteTopology
  条件: [离散拓扑 M] [唯一 E]
  证明: by
  apply isManifold_of_contDiffOn _ _ _ (fun _ _ _ _ => contDiff_of_subsingleton.contDiffOn)

Depends on / 依赖: contDiffOn, contDiff_of_subsingleton, contDiff_of_subsingleton.contDiffOn, isManifold_of_contDiffOn
-/
theorem of_discreteTopology [DiscreteTopology M] [Unique E] :
    IsManifold (modelWithCornersSelf 𝕜 E) n M := by
  apply isManifold_of_contDiffOn _ _ _ (fun _ _ _ _ => contDiff_of_subsingleton.contDiffOn)

attribute [local instance] ChartedSpace.ofDiscreteTopology in
example [Unique E] : IsManifold (𝓘(𝕜, E)) n (Fin 2) := of_discreteTopology _

/--
Instance `prod` / 实例 `prod`

English:
instance prod
  signature: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  body: by
    rintro f g ⟨f1, hf1, f2, hf2, rfl⟩ ⟨g1, hg1, g2, hg2, rfl⟩
    rw [OpenPartialHomeomorph.prod_symm]; rw [OpenPartialHomeomorph.prod_trans]
    have h1 := (contDiffGroupoid n I).compatible hf1 hg1
    have h2 := (contDiffGroupoid n I').compatible hf2 hg2
    exact contDiffGroupoid_prod h1 h2

中文:
实例 乘积
  签名: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {E : 类型} [赋范交换加群 E]
  定义体: by
    rintro f g ⟨f1, hf1, f2, hf2, rfl⟩ ⟨g1, hg1, g2, hg2, rfl⟩
    rw [OpenPartialHomeomorph.prod_symm]; rw [OpenPartialHomeomorph.prod_trans]
    have h1 := (contDiffGroupoid n I).compatible hf1 hg1
    have h2 := (contDiffGroupoid n I').compatible hf2 hg2
    exact contDiffGroupoid_prod h1 h2

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_trans, compatible, contDiffGroupoid, contDiffGroupoid_prod, prod_symm, prod_trans
-/
instance prod {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
    [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I n M] (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold I' n M'] :
    IsManifold (I.prod I') n (M × M') where
  compatible := by
    rintro f g ⟨f1, hf1, f2, hf2, rfl⟩ ⟨g1, hg1, g2, hg2, rfl⟩
    rw [OpenPartialHomeomorph.prod_symm]; rw [OpenPartialHomeomorph.prod_trans]
    have h1 := (contDiffGroupoid n I).compatible hf1 hg1
    have h2 := (contDiffGroupoid n I').compatible hf2 hg2
    exact contDiffGroupoid_prod h1 h2

section

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {n : Nat∞ω}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/--
lemma `mem_maximalAtlas_prod` / 引理 `mem_maximalAtlas_prod`

English:
lemma mem_maximalAtlas_prod
  statement: [IsManifold I n M] [IsManifold I' n M']
  proof: by
  simp only [mem_maximalAtlas_iff]
  rintro e'' ⟨f, hf, f', hf', rfl⟩
  rw [OpenPartialHomeomorph.prod_symm_trans_prod]; rw [OpenPartialHomeomorph.prod_symm_trans_prod]
  constructor <;>
    apply contDiffGroupoid_prod <;> grind [compatible_of_mem_maximalAtlas, subset_maximalAtlas]

中文:
引理 mem_maximalAtlas_prod
  结论: [是流形 I n M] [是流形 I' n M']
  证明: by
  simp only [mem_maximalAtlas_iff]
  rintro e'' ⟨f, hf, f', hf', rfl⟩
  rw [OpenPartialHomeomorph.prod_symm_trans_prod]; rw [OpenPartialHomeomorph.prod_symm_trans_prod]
  constructor <;>
    apply contDiffGroupoid_prod <;> grind [compatible_of_mem_maximalAtlas, subset_maximalAtlas]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.prod_symm_trans_prod, compatible_of_mem_maximalAtlas, contDiffGroupoid_prod, mem_maximalAtlas_iff, prod_symm_trans_prod, subset_maximalAtlas
-/
lemma mem_maximalAtlas_prod [IsManifold I n M] [IsManifold I' n M']
    {e : OpenPartialHomeomorph M H} (he : e in maximalAtlas I n M)
    {e' : OpenPartialHomeomorph M' H'} (he' : e' in maximalAtlas I' n M') :
    e.prod e' in maximalAtlas (I.prod I') n (M × M') := by
  simp only [mem_maximalAtlas_iff]
  rintro e'' ⟨f, hf, f', hf', rfl⟩
  rw [OpenPartialHomeomorph.prod_symm_trans_prod]; rw [OpenPartialHomeomorph.prod_symm_trans_prod]
  constructor <;>
    apply contDiffGroupoid_prod <;> grind [compatible_of_mem_maximalAtlas, subset_maximalAtlas]

end

section DisjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  [hM : IsManifold I n M] [hM' : IsManifold I n M']

/--
Instance `disjointUnion` / 实例 `disjointUnion`

English:
instance disjointUnion
  signature: : IsManifold I n (M oplus M') where
  body: by
    obtain (h | h) := isEmpty_or_nonempty H
    · exact ContDiffGroupoid.mem_of_source_eq_empty _ (eq_empty_of_isEmpty _)
    obtain (⟨f, hf, hef⟩ | ⟨f, hf, hef⟩) := ChartedSpace.mem_atlas_sum he
    · obtain (⟨f', hf', he'f'⟩ | ⟨f', hf', he'f'⟩) := ChartedSpace.mem_atlas_sum he'
      · rw [hef, he'f', f.lift_openEmbedding_trans f' IsOpenEmbedding.inl]
        exact hM.compatible hf hf'
      · rw [hef, he'f']
        apply ContDiffGroupoid.mem_of_source_eq_empty
        ext x
        exact ⟨fun ⟨hx₁, hx₂⟩ => by simp_all, fun hx => hx.elim⟩
    · -- Analogous argument to the first case: is there a way to deduplicate?
      obtain (⟨f', hf', he'f'⟩ | ⟨f', hf', he'f'⟩) := ChartedSpace.mem_atlas_sum he'
      · rw [hef, he'f']
        apply ContDiffGroupoid.mem_of_source_eq_empty
        ext x
        exact ⟨fun ⟨hx₁, hx₂⟩ => by simp_all, fun hx => hx.elim⟩
      · rw [hef, he'f', f.lift_openEmbedding_trans f' IsOpenEmbedding.inr]
        exact hM'.compatible hf hf'

中文:
实例 disjointUnion
  签名: : 是流形 I n (M oplus M') where
  定义体: by
    obtain (h | h) := isEmpty_or_nonempty H
    · exact ContDiffGroupoid.mem_of_source_eq_empty _ (eq_empty_of_isEmpty _)
    obtain (⟨f, hf, hef⟩ | ⟨f, hf, hef⟩) := ChartedSpace.mem_atlas_sum he
    · obtain (⟨f', hf', he'f'⟩ | ⟨f', hf', he'f'⟩) := ChartedSpace.mem_atlas_sum he'
      · rw [hef, he'f', f.lift_openEmbedding_trans f' IsOpenEmbedding.inl]
        exact hM.compatible hf hf'
      · rw [hef, he'f']
        apply ContDiffGroupoid.mem_of_source_eq_empty
        ext x
        exact ⟨fun ⟨hx₁, hx₂⟩ => by simp_all, fun hx => hx.elim⟩
    · -- Analogous argument to the first case: is there a way to deduplicate?
      obtain (⟨f', hf', he'f'⟩ | ⟨f', hf', he'f'⟩) := ChartedSpace.mem_atlas_sum he'
      · rw [hef, he'f']
        apply ContDiffGroupoid.mem_of_source_eq_empty
        ext x
        exact ⟨fun ⟨hx₁, hx₂⟩ => by simp_all, fun hx => hx.elim⟩
      · rw [hef, he'f', f.lift_openEmbedding_trans f' IsOpenEmbedding.inr]
        exact hM'.compatible hf hf'

Depends on / 依赖: ChartedSpace, ChartedSpace.mem_atlas_sum, ContDiffGroupoid, ContDiffGroupoid.mem_of_source_eq_empty, IsOpenEmbedding, IsOpenEmbedding.inl, compatible, eq_empty_of_isEmpty, f.lift_openEmbedding_trans, hM.compatible, hx.elim, isEmpty_or_nonempty, lift_openEmbedding_trans, mem_atlas_sum, mem_of_source_eq_empty
-/
instance disjointUnion : IsManifold I n (M oplus M') where
  compatible {e} e' he he' := by
    obtain (h | h) := isEmpty_or_nonempty H
    · exact ContDiffGroupoid.mem_of_source_eq_empty _ (eq_empty_of_isEmpty _)
    obtain (⟨f, hf, hef⟩ | ⟨f, hf, hef⟩) := ChartedSpace.mem_atlas_sum he
    · obtain (⟨f', hf', he'f'⟩ | ⟨f', hf', he'f'⟩) := ChartedSpace.mem_atlas_sum he'
      · rw [hef, he'f', f.lift_openEmbedding_trans f' IsOpenEmbedding.inl]
        exact hM.compatible hf hf'
      · rw [hef, he'f']
        apply ContDiffGroupoid.mem_of_source_eq_empty
        ext x
        exact ⟨fun ⟨hx₁, hx₂⟩ => by simp_all, fun hx => hx.elim⟩
    · -- Analogous argument to the first case: is there a way to deduplicate?
      obtain (⟨f', hf', he'f'⟩ | ⟨f', hf', he'f'⟩) := ChartedSpace.mem_atlas_sum he'
      · rw [hef, he'f']
        apply ContDiffGroupoid.mem_of_source_eq_empty
        ext x
        exact ⟨fun ⟨hx₁, hx₂⟩ => by simp_all, fun hx => hx.elim⟩
      · rw [hef, he'f', f.lift_openEmbedding_trans f' IsOpenEmbedding.inr]
        exact hM'.compatible hf hf'

end DisjointUnion

end IsManifold

/--
theorem `OpenPartialHomeomorph.isManifold_singleton` / 定理 `OpenPartialHomeomorph.isManifold_singleton`

English:
theorem OpenPartialHomeomorph.isManifold_singleton
  proof: @IsManifold.mk' _ _ _ _ _ _ _ _ _ _ _ (id _)
    e.singleton_hasGroupoid h (contDiffGroupoid n I)

中文:
定理 OpenPartialHomeomorph.isManifold_singleton
  证明: @IsManifold.mk' _ _ _ _ _ _ _ _ _ _ _ (id _)
    e.singleton_hasGroupoid h (contDiffGroupoid n I)

Depends on / 依赖: IsManifold, IsManifold.mk, contDiffGroupoid, e.singleton_hasGroupoid, singleton_hasGroupoid
-/
theorem OpenPartialHomeomorph.isManifold_singleton
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : Nat∞ω}
    {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M H) (h : e.source = Set.univ) :
    @IsManifold 𝕜 _ E _ _ H _ I n M _ (e.singletonChartedSpace h) :=
@IsManifold.mk' _ _ _ _ _ _ _ _ _ _ _ (id _)
    e.singleton_hasGroupoid h (contDiffGroupoid n I)

/--
theorem `Topology.IsOpenEmbedding.isManifold_singleton` / 定理 `Topology.IsOpenEmbedding.isManifold_singleton`

English:
theorem Topology.IsOpenEmbedding.isManifold_singleton
  statement: {𝕜 E H : Type*}
  proof: (h.toOpenPartialHomeomorph f).isManifold_singleton (by simp)

中文:
定理 拓扑.是开嵌入.isManifold_singleton
  结论: {𝕜 E H : 类型}
  证明: (h.toOpenPartialHomeomorph f).isManifold_singleton (by simp)

Depends on / 依赖: h.toOpenPartialHomeomorph, isManifold_singleton, toOpenPartialHomeomorph
-/
theorem Topology.IsOpenEmbedding.isManifold_singleton {𝕜 E H : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {n : Nat∞ω}
    {M : Type*} [TopologicalSpace M] [Nonempty M] {f : M -> H} (h : IsOpenEmbedding f) :
    @IsManifold 𝕜 _ E _ _ H _ I n M _ h.singletonChartedSpace :=
  (h.toOpenPartialHomeomorph f).isManifold_singleton (by simp)

namespace TopologicalSpace.Opens

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : Nat∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  (s : Opens M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsManifold I n s
  body: { s.instHasGroupoid (contDiffGroupoid n I) with }

中文:
实例 :
  签名: 是流形 I n s
  定义体: { s.instHasGroupoid (contDiffGroupoid n I) with }

Depends on / 依赖: contDiffGroupoid, instHasGroupoid, s.instHasGroupoid
-/
instance : IsManifold I n s :=
  { s.instHasGroupoid (contDiffGroupoid n I) with }

end TopologicalSpace.Opens

section TangentSpace

/- We define the tangent space to `M` modelled on `I : ModelWithCorners 𝕜 E H` as a type synonym
for `E`. This is enough to define linear maps between tangent spaces, for instance derivatives,
but the interesting part is to define a manifold structure on the whole tangent bundle, which
requires that `M` is a `C^n` manifold. The definition is put here to avoid importing
all the smooth bundle structure when defining manifold derivatives. -/

set_option linter.unusedVariables false in
/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangentBundleCore I M).toFiberBundleCore.fiber x`, but we use `E` to help the kernel.

The definition of `TangentSpace` is not reducible so that type class inference
does not pick wrong instances.
-/
@[nolint unusedArguments, wikidata Q909601]
/--
Definition of `TangentSpace` / `TangentSpace` 的定义

English:
definition TangentSpace
  signature: {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  body: E
deriving
  TopologicalSpace, AddCommGroup, IsTopologicalAddGroup, Module 𝕜,
  ContinuousSMul 𝕜,
  -- the following instance derives from the previous one, but through an instance with priority 100
  -- which takes a long time to be found. We register a shortcut instance instead
  ContinuousConstSMul 𝕜

中文:
定义 TangentSpace
  签名: {𝕜 : 类型} [NontriviallyNormedField 𝕜]
  定义体: E
deriving
  TopologicalSpace, AddCommGroup, IsTopologicalAddGroup, Module 𝕜,
  ContinuousSMul 𝕜,
  -- the following instance derives from the previous one, but through an instance with priority 100
  -- which takes a long time to be found. We register a shortcut instance instead
  ContinuousConstSMul 𝕜
-/
def TangentSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (_x : M) : Type u := E
deriving
  TopologicalSpace, AddCommGroup, IsTopologicalAddGroup, Module 𝕜,
  ContinuousSMul 𝕜,
  -- the following instance derives from the previous one, but through an instance with priority 100
  -- which takes a long time to be found. We register a shortcut instance instead
  ContinuousConstSMul 𝕜

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `NormedSpace.fromTangentSpace` / `NormedSpace.fromTangentSpace` 的定义

English:
definition NormedSpace.fromTangentSpace
  signature: (v : E)
  body: v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp

中文:
定义 赋范空间.fromTangentSpace
  签名: (v : E)
  定义体: v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp
-/
def NormedSpace.fromTangentSpace (v : E) : TangentSpace 𝓘(𝕜, E) v ≃L[𝕜] E where
  toFun v := v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (TangentSpace I x)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (TangentSpace I x)
  定义体: ⟨0⟩
-/
instance : Inhabited (TangentSpace I x) := ⟨0⟩

variable (M) in
-- is empty if the base manifold is empty
/-- The tangent bundle to a manifold, as a Sigma type. Defined in terms of
`Bundle.TotalSpace` to be able to put a suitable topology on it. -/
@[wikidata Q746550]
/--
Definition of `TangentBundle` / `TangentBundle` 的定义

English:
abbreviation TangentBundle
  body: Bundle.TotalSpace E (TangentSpace I : M -> Type _)

中文:
缩写 切丛
  定义体: Bundle.TotalSpace E (TangentSpace I : M -> Type _)

Depends on / 依赖: Bundle, Bundle.TotalSpace, TangentSpace, TotalSpace
-/
abbrev TangentBundle := Bundle.TotalSpace E (TangentSpace I : M -> Type _)

end TangentSpace

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

deriving instance PathConnectedSpace for TangentSpace I x

end Real
