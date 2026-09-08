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
/-
**PartialEquiv.Continuous.invFun** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.Continu
ous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] (e : PartialEquiv α β),   Continuous ↑e.symm → Continuous e.invF
un
参数：e : PartialEquiv α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma is here in this file, because in `PartialEquiv.basic` it would
have required to import some topology, and it did not look right.
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
/-
**ModelWithCorners** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：ModelWithCorners (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [Norm
edAddCommGroup E] [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] extends Par
tialEquiv H E where source_eq : source = univ /-- To check this condition when t
he space already has a real normed space structure, use `Convex.convex_isRCLikeN
ormedField` which eliminates the `letI`s below, or the constructor `ModelWithCor
ners.ofConvexRange` -/ convex_range' : if h : IsRCLikeNormedField 𝕜 then letI
参数：𝕜 : Type*；E : Type*；H : Type*。
继承自：PartialEquiv H E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure containing information on the way a space `H` embeds in a
model vector space `E` over the field `𝕜`. This is all that is needed to
define a `C^n` manifold with model space `H`, and model vector space `E`.

We require that, when the field is `ℝ` or `ℂ`, the range is `ℝ`-convex, as this 
is what is needed
to do calculus and covers the standard examples of manifolds with boundary. Over
 other fields,
we require that the range is `univ`, as there is no relevant notion of manifold 
with boundary there.
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
      letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
      Convex ℝ (range toPartialEquiv)
    else range toPartialEquiv = univ
  nonempty_interior' : (interior (range toPartialEquiv)).Nonempty
  continuous_toFun : Continuous toFun := by fun_prop
  continuous_invFun : Continuous invFun := by fun_prop
/-
**ModelWithCorners.range_eq_target** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModelWithCorners.range_eq_target {𝕜 E H : Type*} [NontriviallyNormedField 
𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithC
orners 𝕜 E H) : range I.toPartialEquiv = I.target
参数：I : ModelWithCorners 𝕜 E H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
lemma ModelWithCorners.range_eq_target {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) :
    range I.toPartialEquiv = I.target := by
  rw [← I.image_source_eq_target, I.source_eq, image_univ.symm]

/-- If a model with corners has full range, the `convex_range'` condition is satisfied. -/
/-
**ModelWithCorners.ofTargetUniv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ModelWithCorners.ofTargetUniv (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E :
 Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H
] (φ : PartialEquiv H E) (hsource : φ.source = univ) (htarget : φ.target = univ)
 (hcont : Continuous φ) (hcont_inv : Continuous φ.symm) : ModelWithCorners 𝕜 E H
 where toPartialEquiv
参数：𝕜 : Type*；φ : PartialEquiv H E；hsource : φ.source = univ；htarget : φ.target =
 univ；hcont : Continuous φ；hcont_inv : Continuous φ.symm。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a model with corners has full range, the `convex_range'` condition is satisfi
ed.
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
    let := NormedSpace.restrictScalars ℝ 𝕜 E
    exact convex_univ
  nonempty_interior' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp [this, htarget]

attribute [simp, mfld_simps] ModelWithCorners.source_eq

/-- A vector space is a model with corners, denoted as `𝓘(𝕜, E)` within the `Manifold` namespace. -/
/-
**modelWithCornersSelf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：modelWithCornersSelf (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [
NormedAddCommGroup E] [NormedSpace 𝕜 E] : ModelWithCorners 𝕜 E E
参数：𝕜 : Type*；E : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vector space is a model with corners, denoted as `𝓘(𝕜, E)` within the `Manifol
d` namespace.
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

/-- Coercion of a model with corners to a function. We don't use `e.toFun` because it is actually
`e.toPartialEquiv.toFun`, so `simp` will apply lemmas about `toPartialEquiv`. While we may want to
switch to this behavior later, doing it mid-port will break a lot of proofs. -/
/-
**ModelWithCorners.toFun'** 是 Mathlib 中的一个定义，位于命名空间 `ModelWithCorners`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
{H : Type u_3} → [inst_3 : TopologicalSpace H] → ModelWithCorners 𝕜 E H → H → E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of a model with corners to a function. We don't use `e.toFun` because i
t is actually
`e.toPartialEquiv.toFun`, so `simp` will apply lemmas about `toPartialEquiv`. Wh
ile we may want to
switch to this behavior later, doing it mid-port will break a lot of proofs.
-/
@[coe] def toFun' (e : ModelWithCorners 𝕜 E H) : H → E := e.toFun
/-
**ModelWithCorners.** 是 Mathlib 中的一个实例，位于命名空间 `ModelWithCorners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of a model with corners to a function. We don't use `e.toFun` because i
t is actually
`e.toPartialEquiv.toFun`, so `simp` will apply lemmas about `toPartialEquiv`. Wh
ile we may want to
switch to this behavior later, doing it mid-port will break a lot of proofs.
-/
instance : CoeFun (ModelWithCorners 𝕜 E H) fun _ => H → E := ⟨toFun'⟩

/-- The inverse to a model with corners, only registered as a `PartialEquiv`. -/
/-
**ModelWithCorners.symm** 是 Mathlib 中的一个定义，位于命名空间 `ModelWithCorners`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} → [inst_3 : TopologicalSpace H] → ModelWithCorners 𝕜 E 
H → PartialEquiv E H
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse to a model with corners, only registered as a `PartialEquiv`.
-/
protected def symm : PartialEquiv E H :=
  I.toPartialEquiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
/-
**ModelWithCorners.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `ModelWithCorners.Simps
`。
形式化陈述：(𝕜 : Type u_4) →   [inst : NontriviallyNormedField 𝕜] →     (E : Type u_5)
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
(H : Type u_6) → [inst_3 : TopologicalSpace H] → ModelWithCorners 𝕜 E H → H → E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
because it is a composition of multiple projections.
-/
def Simps.apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : H → E :=
  I

/-- See Note [custom simps projection] -/
/-
**ModelWithCorners.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `ModelWithCorners.
Simps`。
形式化陈述：(𝕜 : Type u_4) →   [inst : NontriviallyNormedField 𝕜] →     (E : Type u_5)
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
(H : Type u_6) → [inst_3 : TopologicalSpace H] → ModelWithCorners 𝕜 E H → E → H
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type*) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : E → H :=
  I.symm

initialize_simps_projections ModelWithCorners (toFun → apply, invFun → symm_apply)

-- Register a few lemmas to make sure that `simp` puts expressions in normal form
@[simp, mfld_simps]
/-
**ModelWithCorners.toPartialEquiv_coe** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorner
s`。
形式化陈述：toPartialEquiv_coe : (I.toPartialEquiv : H -> E) = I
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPartialEquiv_coe : (I.toPartialEquiv : H → E) = I :=
  rfl

@[simp, mfld_simps]
/-
**ModelWithCorners.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：mk_coe (e : PartialEquiv H E) (a b c d d') : ((ModelWithCorners.mk e a b c
 d d' : ModelWithCorners 𝕜 E H) : H -> E) = (e : H -> E)
参数：e : PartialEquiv H E；a b c d d'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe (e : PartialEquiv H E) (a b c d d') :
    ((ModelWithCorners.mk e a b c d d' : ModelWithCorners 𝕜 E H) : H → E) = (e : H → E) :=
  rfl

@[simp, mfld_simps]
/-
**ModelWithCorners.toPartialEquiv_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithC
orners`。
形式化陈述：toPartialEquiv_coe_symm : (I.toPartialEquiv.symm : E -> H) = I.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPartialEquiv_coe_symm : (I.toPartialEquiv.symm : E → H) = I.symm :=
  rfl

@[simp, mfld_simps]
/-
**ModelWithCorners.mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：mk_symm (e : PartialEquiv H E) (a b c d d') : (ModelWithCorners.mk e a b c
 d d' : ModelWithCorners 𝕜 E H).symm = e.symm
参数：e : PartialEquiv H E；a b c d d'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_symm (e : PartialEquiv H E) (a b c d d') :
    (ModelWithCorners.mk e a b c d d' : ModelWithCorners 𝕜 E H).symm = e.symm :=
  rfl

@[fun_prop]
/-
**ModelWithCorners.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H), Continuous ↑I
参数：I : ModelWithCorners 𝕜 E H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.continuous_toFun`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
-/
protected theorem continuous : Continuous I :=
  I.continuous_toFun
/-
**ModelWithCorners.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H) {x : H},   ContinuousAt (↑I) x
参数：I : ModelWithCorners 𝕜 E H；↑I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ModelWithCorners.continuous`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
-/
protected theorem continuousAt {x} : ContinuousAt I x :=
  I.continuous.continuousAt
/-
**ModelWithCorners.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorner
s`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H) {s : Set H}   {x : H}, Continuou
sWithinAt (↑I) s x
参数：I : ModelWithCorners 𝕜 E H；↑I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ModelWithCorners.continuousAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
-/
protected theorem continuousWithinAt {s x} : ContinuousWithinAt I s x :=
  I.continuousAt.continuousWithinAt

@[fun_prop]
/-
**ModelWithCorners.continuous_symm** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：continuous_symm : Continuous I.symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.continuous_invFun`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {H : Type u_…
-/
theorem continuous_symm : Continuous I.symm :=
  I.continuous_invFun
/-
**ModelWithCorners.continuousAt_symm** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners
`。
形式化陈述：continuousAt_symm {x} : ContinuousAt I.symm x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
-/
theorem continuousAt_symm {x} : ContinuousAt I.symm x :=
  I.continuous_symm.continuousAt
/-
**ModelWithCorners.continuousWithinAt_symm** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithC
orners`。
形式化陈述：continuousWithinAt_symm {s x} : ContinuousWithinAt I.symm s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
-/
theorem continuousWithinAt_symm {s x} : ContinuousWithinAt I.symm s x :=
  I.continuous_symm.continuousWithinAt
/-
**ModelWithCorners.continuousOn_symm** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners
`。
形式化陈述：continuousOn_symm {s} : ContinuousOn I.symm s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
-/
theorem continuousOn_symm {s} : ContinuousOn I.symm s :=
  I.continuous_symm.continuousOn

@[simp, mfld_simps]
/-
**ModelWithCorners.target_eq** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：target_eq : I.target = range (I : H -> E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
-/
theorem target_eq : I.target = range (I : H → E) := by
  rw [← image_univ, ← I.source_eq]
  exact I.image_source_eq_target.symm
/-
**ModelWithCorners.nonempty_interior** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners
`。
形式化陈述：nonempty_interior : (interior (range I)).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.nonempty_interior'`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
-/
theorem nonempty_interior : (interior (range I)).Nonempty :=
  I.nonempty_interior'
/-
**ModelWithCorners.range_eq_univ_of_not_isRCLikeNormedField** 是 Mathlib 中的一个定理，位
于命名空间 `ModelWithCorners`。
形式化陈述：range_eq_univ_of_not_isRCLikeNormedField (h : ¬ IsRCLikeNormedField 𝕜) : r
ange I = univ
参数：h : ¬ IsRCLikeNormedField 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ModelWithCorners.convex_range'`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
-/
theorem range_eq_univ_of_not_isRCLikeNormedField (h : ¬ IsRCLikeNormedField 𝕜) :
    range I = univ := by
  simpa [h] using I.convex_range'

/-- If a set is `ℝ`-convex for some normed space structure, then it is `ℝ`-convex for the
normed space structure coming from an `IsRCLikeNormedField 𝕜`. Useful when constructing model
spaces to avoid diamond issues when populating the field `convex_range'`. -/
/-
**ModelWithCorners._root_.Convex.convex_isRCLikeNormedField** 是 Mathlib 中的一个引理，位
于命名空间 `ModelWithCorners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a set is `ℝ`-convex for some normed space structure, then it is `ℝ`-convex fo
r the
normed space structure coming from an `IsRCLikeNormedField 𝕜`. Useful when const
ructing model
spaces to avoid diamond issues when populating the field `convex_range'`.
-/
lemma _root_.Convex.convex_isRCLikeNormedField [NormedSpace ℝ E] [h : IsRCLikeNormedField 𝕜]
    {s : Set E} (hs : Convex ℝ s) :
    letI := h.rclike
    letI := NormedSpace.restrictScalars ℝ 𝕜 E
    Convex ℝ s := by
  let := h.rclike
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  simp only [Convex, StarConvex] at hs ⊢
  intro u hu v hv a b ha hb hab
  convert! hs hu hv ha hb hab using 2
  · rw [← @algebraMap_smul (R := ℝ) (A := 𝕜), ← @algebraMap_smul (R := ℝ) (A := 𝕜)]
  · rw [← @algebraMap_smul (R := ℝ) (A := 𝕜), ← @algebraMap_smul (R := ℝ) (A := 𝕜)]

/-- Construct a model with corners over `ℝ` from a continuous partial equiv with convex range. -/
/-
**ModelWithCorners.ofConvexRange** 是 Mathlib 中的一个定义，位于命名空间 `ModelWithCorners`。
形式化陈述：ofConvexRange {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {H :
 Type*} [TopologicalSpace H] (φ : PartialEquiv H E) (hsource : φ.source = univ) 
(htarget : Convex Real φ.target) (hcont : Continuous φ) (hcont_inv : Continuous 
φ.symm) (hint : (interior φ.target).Nonempty) : ModelWithCorners Real E H where 
toPartialEquiv
参数：φ : PartialEquiv H E；hsource : φ.source = univ；htarget : Convex Real φ.target
；hcont : Continuous φ；hcont_inv : Continuous φ.symm；hint : (interior φ.target).N
onempty。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a model with corners over `ℝ` from a continuous partial equiv with con
vex range.
-/
def ofConvexRange
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    (φ : PartialEquiv H E) (hsource : φ.source = univ) (htarget : Convex ℝ φ.target)
    (hcont : Continuous φ) (hcont_inv : Continuous φ.symm) (hint : (interior φ.target).Nonempty) :
    ModelWithCorners ℝ E H where
  toPartialEquiv := φ
  source_eq := hsource
  convex_range' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp only [instIsRCLikeNormedField, ↓reduceDIte, this]
    exact htarget.convex_isRCLikeNormedField
  nonempty_interior' := by
    have : range φ = φ.target := by rw [← φ.image_source_eq_target, hsource, image_univ.symm]
    simp [this, hint]
/-
**ModelWithCorners.convex_range** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：convex_range [NormedSpace Real E] : Convex Real (range I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.convex_range'`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.range_eq_univ_of_not_isRCLikeNormedField`：range_eq_univ
_of_not_isRCLikeNormedField (h : ¬ IsRCLikeNormedField 𝕜) : range I = univ
-/
theorem convex_range [NormedSpace ℝ E] : Convex ℝ (range I) := by
  by_cases h : IsRCLikeNormedField 𝕜
  · let : RCLike 𝕜 := h.rclike
    have W := I.convex_range'
    simp only [h, ↓reduceDIte, toPartialEquiv_coe] at W
    simp only [Convex, StarConvex] at W ⊢
    intro u hu v hv a b ha hb hab
    convert! W hu hv ha hb hab using 2
    · rw [← @algebraMap_smul (R := ℝ) (A := 𝕜)]
      rfl
    · rw [← @algebraMap_smul (R := ℝ) (A := 𝕜)]
      rfl
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h, convex_univ]
/-
**ModelWithCorners.uniqueDiffOn** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H),   UniqueDiffOn 𝕜 (Set.range ↑I)
参数：I : ModelWithCorners 𝕜 E H；Set.range ↑I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniqueDiffOn_convex_of_isRCLikeNormedField`：uniqueDiffOn_convex_of_isRCL
ikeNormedField (conv : Convex Real s) (hs : (interior s).Nonempty) : UniqueDiffO
n 𝕜 s
· 使用定理 `ModelWithCorners.convex_range`：convex_range [NormedSpace Real E] : Conve
x Real (range I)
· 使用定理 `ModelWithCorners.nonempty_interior`：nonempty_interior : (interior (range
 I)).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.range_eq_univ_of_not_isRCLikeNormedField`：range_eq_univ
_of_not_isRCLikeNormedField (h : ¬ IsRCLikeNormedField 𝕜) : range I = univ
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
protected theorem uniqueDiffOn : UniqueDiffOn 𝕜 (range I) := by
  by_cases h : IsRCLikeNormedField 𝕜
  · let := h.rclike 𝕜
    let := NormedSpace.restrictScalars ℝ 𝕜 E
    apply uniqueDiffOn_convex_of_isRCLikeNormedField _ I.nonempty_interior
    simpa [h] using I.convex_range
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h, uniqueDiffOn_univ]
/-
**ModelWithCorners.range_subset_closure_interior** 是 Mathlib 中的一个定理，位于命名空间 `Mode
lWithCorners`。
形式化陈述：range_subset_closure_interior : range I subseteq closure (interior (range 
I))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convex.closure_interior_eq_closure_of_nonempty_interior`：Convex.closure_
interior_eq_closure_of_nonempty_interior {s : Set E} (hs : Convex 𝕜 s) (hs' : (i
nterior s).Nonempty) : closure (interior s) =…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ModelWithCorners.convex_range`：convex_range [NormedSpace Real E] : Conve
x Real (range I)
· 使用定理 `ModelWithCorners.nonempty_interior`：nonempty_interior : (interior (range
 I)).Nonempty
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.range_eq_univ_of_not_isRCLikeNormedField`：range_eq_univ
_of_not_isRCLikeNormedField (h : ¬ IsRCLikeNormedField 𝕜) : range I = univ
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem range_subset_closure_interior : range I ⊆ closure (interior (range I)) := by
  by_cases h : IsRCLikeNormedField 𝕜
  · let := h.rclike 𝕜
    let := NormedSpace.restrictScalars ℝ 𝕜 E
    rw [Convex.closure_interior_eq_closure_of_nonempty_interior (𝕜 := ℝ)]
    · apply subset_closure
    · apply I.convex_range
    · apply I.nonempty_interior
  · simp [range_eq_univ_of_not_isRCLikeNormedField I h]

@[simp, mfld_simps]
/-
**ModelWithCorners.left_inv** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H) (x : H),   ↑I.symm (↑I x) = x
参数：I : ModelWithCorners 𝕜 E H；x : H；↑I x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.left_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : PartialE
quiv α β) ⦃x : α⦄, x ∈ self.source → self.invFun (↑self x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
-/
protected theorem left_inv (x : H) : I.symm (I x) = x := by refine I.left_inv' ?_; simp
/-
**ModelWithCorners.leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H),   Function.LeftInverse ↑I.symm 
↑I
参数：I : ModelWithCorners 𝕜 E H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
-/
protected theorem leftInverse : LeftInverse I.symm I :=
  I.left_inv
/-
**ModelWithCorners.injective** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：injective : Injective I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `ModelWithCorners.leftInverse`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {H : Type u_…
-/
theorem injective : Injective I :=
  I.leftInverse.injective

@[simp, mfld_simps]
/-
**ModelWithCorners.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：symm_comp_self : I.symm ∘ I = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → f ∘ g = id
· 使用定理 `ModelWithCorners.leftInverse`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {H : Type u_…
-/
theorem symm_comp_self : I.symm ∘ I = id :=
  I.leftInverse.comp_eq_id
/-
**ModelWithCorners.rightInvOn** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H),   Set.RightInvOn (↑I.symm) (↑I)
 (Set.range ↑I)
参数：I : ModelWithCorners 𝕜 E H；↑I.symm；↑I；Set.range ↑I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.rightInvOn_range`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {g : β → α}, Function.LeftInverse f g → Set.RightInvOn f g (Set.range
 g)
· 使用定理 `ModelWithCorners.leftInverse`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {H : Type u_…
-/
protected theorem rightInvOn : RightInvOn I.symm I (range I) :=
  I.leftInverse.rightInvOn_range

@[simp, mfld_simps]
/-
**ModelWithCorners.right_inv** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H) {x : E},   x ∈ Set.range ↑I → ↑I
 (↑I.symm x) = x
参数：I : ModelWithCorners 𝕜 E H；↑I.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.rightInvOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
-/
protected theorem right_inv {x : E} (hx : x ∈ range I) : I (I.symm x) = x :=
  I.rightInvOn hx
/-
**ModelWithCorners.preimage_image** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：preimage_image (s : Set H) : I ⁻¹' I '' s = s
参数：s : Set H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `ModelWithCorners.injective`：injective : Injective I
-/
theorem preimage_image (s : Set H) : I ⁻¹' I '' s = s :=
  I.injective.preimage_image s
/-
**ModelWithCorners.image_eq** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H) (s : Set H),   ↑I '' s = ↑I.symm
 ⁻¹' s ∩ Set.range ↑I
参数：I : ModelWithCorners 𝕜 E H；s : Set H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PartialEquiv.image_eq_target_inter_inv_preimage`：image_eq_target_inter_i
nv_preimage {s : Set α} (h : s subseteq e.source) : e '' s = e.target inter e.sy
mm ⁻¹' s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `ModelWithCorners.toPartialEquiv_coe_symm`：toPartialEquiv_coe_symm : (I.t
oPartialEquiv.symm : E -> H) = I.symm
-/
protected theorem image_eq (s : Set H) : I '' s = I.symm ⁻¹' s ∩ range I := by
  refine (I.toPartialEquiv.image_eq_target_inter_inv_preimage ?_).trans ?_
  · rw [I.source_eq]; exact subset_univ _
  · rw [inter_comm, I.target_eq, I.toPartialEquiv_coe_symm]
/-
**ModelWithCorners.isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners
`。
形式化陈述：isClosedEmbedding : IsClosedEmbedding I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.isClosedEmbedding`：Function.LeftInverse.isClosedEmb
edding [T2Space X] {f : X -> Y} {g : Y -> X} (h : Function.LeftInverse f g) (hf 
: Continuous f) (hg : Contin…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ModelWithCorners.leftInverse`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {H : Type u_…
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
· 使用定理 `ModelWithCorners.continuous`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
-/
theorem isClosedEmbedding : IsClosedEmbedding I :=
  I.leftInverse.isClosedEmbedding I.continuous_symm I.continuous
/-
**ModelWithCorners.isClosed_range** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：isClosed_range : IsClosed (range I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `ModelWithCorners.isClosedEmbedding`：isClosedEmbedding : IsClosedEmbeddin
g I
-/
theorem isClosed_range : IsClosed (range I) :=
  I.isClosedEmbedding.isClosed_range
/-
**ModelWithCorners.range_eq_closure_interior** 是 Mathlib 中的一个定理，位于命名空间 `ModelWit
hCorners`。
形式化陈述：range_eq_closure_interior : range I = closure (interior (range I))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `ModelWithCorners.range_subset_closure_interior`：range_subset_closure_int
erior : range I subseteq closure (interior (range I))
· 使用定理 `IsClosed.closure_interior_subset`：IsClosed.closure_interior_subset {s : 
Set X} (s_closed : IsClosed s) : closure (interior s) subseteq s
· 使用定理 `ModelWithCorners.isClosed_range`：isClosed_range : IsClosed (range I)
-/
theorem range_eq_closure_interior : range I = closure (interior (range I)) :=
  Subset.antisymm I.range_subset_closure_interior I.isClosed_range.closure_interior_subset
/-
**ModelWithCorners.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[range I] I x
参数：x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEm
bedding f → ∀ (x : X),…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `ModelWithCorners.isClosedEmbedding`：isClosedEmbedding : IsClosedEmbeddin
g I
-/
theorem map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[range I] I x :=
  I.isClosedEmbedding.isEmbedding.map_nhds_eq x
/-
**ModelWithCorners.map_nhdsWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners
`。
形式化陈述：map_nhdsWithin_eq (s : Set H) (x : H) : map I (𝓝[s] x) = 𝓝[I '' s] I x
参数：s : Set H；x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `ModelWithCorners.isClosedEmbedding`：isClosedEmbedding : IsClosedEmbeddin
g I
-/
theorem map_nhdsWithin_eq (s : Set H) (x : H) : map I (𝓝[s] x) = 𝓝[I '' s] I x :=
  I.isClosedEmbedding.isEmbedding.map_nhdsWithin_eq s x
/-
**ModelWithCorners.image_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorn
ers`。
形式化陈述：image_mem_nhdsWithin {x : H} {s : Set H} (hs : s in 𝓝 x) : I '' s in 𝓝[ran
ge I] I x
参数：hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `ModelWithCorners.map_nhds_eq`：map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[rang
e I] I x
-/
theorem image_mem_nhdsWithin {x : H} {s : Set H} (hs : s ∈ 𝓝 x) : I '' s ∈ 𝓝[range I] I x :=
  I.map_nhds_eq x ▸ image_mem_map hs
/-
**ModelWithCorners.symm_map_nhdsWithin_image** 是 Mathlib 中的一个定理，位于命名空间 `ModelWit
hCorners`。
形式化陈述：symm_map_nhdsWithin_image {x : H} {s : Set H} : map I.symm (𝓝[I '' s] I x)
 = 𝓝[s] x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.map_nhdsWithin_eq`：map_nhdsWithin_eq (s : Set H) (x : H
) : map I (𝓝[s] x) = 𝓝[I '' s] I x
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `ModelWithCorners.symm_comp_self`：symm_comp_self : I.symm ∘ I = id
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
-/
theorem symm_map_nhdsWithin_image {x : H} {s : Set H} : map I.symm (𝓝[I '' s] I x) = 𝓝[s] x := by
  rw [← I.map_nhdsWithin_eq, map_map, I.symm_comp_self, map_id]
/-
**ModelWithCorners.symm_map_nhdsWithin_range** 是 Mathlib 中的一个定理，位于命名空间 `ModelWit
hCorners`。
形式化陈述：symm_map_nhdsWithin_range (x : H) : map I.symm (𝓝[range I] I x) = 𝓝 x
参数：x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.map_nhds_eq`：map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[rang
e I] I x
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `ModelWithCorners.symm_comp_self`：symm_comp_self : I.symm ∘ I = id
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
-/
theorem symm_map_nhdsWithin_range (x : H) : map I.symm (𝓝[range I] I x) = 𝓝 x := by
  rw [← I.map_nhds_eq, map_map, I.symm_comp_self, map_id]
/-
**ModelWithCorners.uniqueDiffOn_preimage** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCor
ners`。
形式化陈述：uniqueDiffOn_preimage {s : Set H} (hs : IsOpen s) : UniqueDiffOn 𝕜 (I.symm
 ⁻¹' s inter range I)
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `UniqueDiffOn.inter`：UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsO
pen t) : UniqueDiffOn 𝕜 (s inter t)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ModelWithCorners.uniqueDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ModelWithCorners.continuous_invFun`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {H : Type u_…
-/
theorem uniqueDiffOn_preimage {s : Set H} (hs : IsOpen s) :
    UniqueDiffOn 𝕜 (I.symm ⁻¹' s ∩ range I) := by
  rw [inter_comm]
  exact I.uniqueDiffOn.inter (hs.preimage I.continuous_invFun)
/-
**ModelWithCorners.uniqueDiffOn_preimage_source** 是 Mathlib 中的一个定理，位于命名空间 `Model
WithCorners`。
形式化陈述：uniqueDiffOn_preimage_source {β : Type*} [TopologicalSpace β] {e : OpenPar
tialHomeomorph H β} : UniqueDiffOn 𝕜 (I.symm ⁻¹' e.source inter range I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.uniqueDiffOn_preimage`：uniqueDiffOn_preimage {s : Set H
} (hs : IsOpen s) : UniqueDiffOn 𝕜 (I.symm ⁻¹' s inter range I)
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem uniqueDiffOn_preimage_source {β : Type*} [TopologicalSpace β]
    {e : OpenPartialHomeomorph H β} : UniqueDiffOn 𝕜 (I.symm ⁻¹' e.source ∩ range I) :=
  I.uniqueDiffOn_preimage e.open_source
/-
**ModelWithCorners.uniqueDiffWithinAt_image** 是 Mathlib 中的一个定理，位于命名空间 `ModelWith
Corners`。
形式化陈述：uniqueDiffWithinAt_image {x : H} : UniqueDiffWithinAt 𝕜 (range I) (I x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.uniqueDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem uniqueDiffWithinAt_image {x : H} : UniqueDiffWithinAt 𝕜 (range I) (I x) :=
  I.uniqueDiffOn _ (mem_range_self _)
/-
**ModelWithCorners.symm_continuousWithinAt_comp_right_iff** 是 Mathlib 中的一个定理，位于命
名空间 `ModelWithCorners`。
形式化陈述：symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {f : H -> 
X} {s : Set H} {x : H} : ContinuousWithinAt (f ∘ I.symm) (I.symm ⁻¹' s inter ran
ge I) (I x) ↔ ContinuousWithinAt f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `ModelWithCorners.continuousWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.symm_comp_self`：symm_comp_self : I.symm ∘ I = id
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.continuousWithinAt_symm`：continuousWithinAt_symm {s x} 
: ContinuousWithinAt I.symm s x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {f : H → X} {s : Set H}
    {x : H} :
    ContinuousWithinAt (f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x) ↔ ContinuousWithinAt f s x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h.comp I.continuousWithinAt (mapsTo_preimage _ _)
    simp_rw [preimage_inter, preimage_preimage, I.left_inv, preimage_id', preimage_range,
      inter_univ] at this
    rwa [Function.comp_assoc, I.symm_comp_self] at this
  · rw [← I.left_inv x] at h; exact h.comp I.continuousWithinAt_symm inter_subset_left
/-
**ModelWithCorners.locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorne
rs`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] [LocallyCompactSpace E]   (I : ModelWithCorners 𝕜 E H), Local
lyCompactSpace H
参数：I : ModelWithCorners 𝕜 E H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.symm_map_nhdsWithin_range`：symm_map_nhdsWithin_range (x
 : H) : map I.symm (𝓝[range I] I x) = 𝓝 x
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
· 使用定理 `compact_basis_nhds`：compact_basis_nhds [LocallyCompactSpace X] (x : X) :
 (𝓝 x).HasBasis (fun s => s in 𝓝 x ∧ IsCompact s) fun s => s
· 使用定理 `LocallyCompactSpace.of_hasBasis`：LocallyCompactSpace.of_hasBasis {ι : X 
-> Type*} {p : forall x, ι x -> Prop} {s : forall x, ι x -> Set X} (h : forall x
, (𝓝 x).HasBasis (p x…
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `ModelWithCorners.isClosed_range`：isClosed_range : IsClosed (range I)
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
-/
protected theorem locallyCompactSpace [LocallyCompactSpace E] (I : ModelWithCorners 𝕜 E H) :
    LocallyCompactSpace H := by
  have : ∀ x : H, (𝓝 x).HasBasis (fun s => s ∈ 𝓝 (I x) ∧ IsCompact s)
      fun s => I.symm '' (s ∩ range I) := fun x ↦ by
    rw [← I.symm_map_nhdsWithin_range]
    exact ((compact_basis_nhds (I x)).inf_principal _).map _
  refine .of_hasBasis this ?_
  rintro x s ⟨-, hsc⟩
  exact (hsc.inter_right I.isClosed_range).image I.continuous_symm

open TopologicalSpace
/-
**ModelWithCorners.secondCountableTopology** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithC
orners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] [SecondCountableTopology E]   (I : ModelWithCorners 𝕜 E H), S
econdCountableTopology H
参数：I : ModelWithCorners 𝕜 E H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.secondCountableTopology`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace α] {f : α → β} [inst_1 : TopologicalSpace β]   [S
econdCountableTopology β], Topolog…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `ModelWithCorners.isClosedEmbedding`：isClosedEmbedding : IsClosedEmbeddin
g I
-/
protected theorem secondCountableTopology [SecondCountableTopology E] (I : ModelWithCorners 𝕜 E H) :
    SecondCountableTopology H :=
  I.isClosedEmbedding.isEmbedding.secondCountableTopology

include I in
/-- Every manifold is a Fréchet space (T1 space) -- regardless of whether it is
Hausdorff. -/
/-
**ModelWithCorners.t1Space** 是 Mathlib 中的一个定理，位于命名空间 `ModelWithCorners`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type u_4)   [inst : Topolog
icalSpace M] [ChartedSpace H M], T1Space M
参数：I : ModelWithCorners 𝕜 E H；M : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t2Space`：Topology.IsEmbedding.t2Space [TopologicalS
pace Y] [T2Space Y] {f : X -> Y} (hf : IsEmbedding f) : T2Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `ModelWithCorners.isClosedEmbedding`：isClosedEmbedding : IsClosedEmbeddin
g I
· 使用定理 `ChartedSpace.t1Space`：ChartedSpace.t1Space [T1Space H] : T1Space M
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X

--- 原说明 ---
Every manifold is a Fréchet space (T1 space) -- regardless of whether it is
Hausdorff.
-/
protected theorem t1Space (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : T1Space M := by
  have : T2Space H := I.isClosedEmbedding.toIsEmbedding.t2Space
  exact ChartedSpace.t1Space H M

end ModelWithCorners

section

variable (𝕜 E)

/-- In the trivial model with corners, the associated `PartialEquiv` is the identity. -/
@[simp, mfld_simps]
/-
**modelWithCornersSelf_partialEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：modelWithCornersSelf_partialEquiv : 𝓘(𝕜, E).toPartialEquiv = PartialEquiv.
refl E
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the trivial model with corners, the associated `PartialEquiv` is the identity
.
-/
theorem modelWithCornersSelf_partialEquiv : 𝓘(𝕜, E).toPartialEquiv = PartialEquiv.refl E :=
  rfl

@[simp, mfld_simps]
/-
**modelWithCornersSelf_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：modelWithCornersSelf_coe : (𝓘(𝕜, E) : E -> E) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem modelWithCornersSelf_coe : (𝓘(𝕜, E) : E → E) = id :=
  rfl

@[simp, mfld_simps]
/-
**modelWithCornersSelf_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：modelWithCornersSelf_coe_symm : (𝓘(𝕜, E).symm : E -> E) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem modelWithCornersSelf_coe_symm : (𝓘(𝕜, E).symm : E → E) = id :=
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
/-
**ModelWithCorners.prod** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ModelWithCorners.prod {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v
} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H] (I 
: ModelWithCorners 𝕜 E H) {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace 𝕜 
E'] {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') : Model
WithCorners 𝕜 (E × E') (ModelProd H H')
参数：I : ModelWithCorners 𝕜 E H；I' : ModelWithCorners 𝕜 E' H'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two model_with_corners `I` on `(E, H)` and `I'` on `(E', H')`, we define t
he model with
corners `I.prod I'` on `(E × E', ModelProd H H')`. This appears in particular fo
r the manifold
structure on the tangent bundle to a manifold modelled on `(E, H)`: it will be m
odelled on
`(E × E, H × E)`. See note [Manifold type tags] for explanation about `ModelProd
 H H'`
vs `H × H'`.
-/
def ModelWithCorners.prod {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') :
    ModelWithCorners 𝕜 (E × E') (ModelProd H H') :=
  { I.toPartialEquiv.prod I'.toPartialEquiv with
    toFun := fun x => (I x.1, I' x.2)
    invFun := fun x => (I.symm x.1, I'.symm x.2)
    source := { x | x.1 ∈ I.source ∧ x.2 ∈ I'.source }
    source_eq := by simp only [ofPred_true, mfld_simps]
    convex_range' := by
      have : range (fun (x : ModelProd H H') ↦ (I x.1, I' x.2)) = range (Prod.map I I') := rfl
      rw [this, Set.range_prodMap]
      split_ifs with h
      · let := h.rclike
        let := NormedSpace.restrictScalars ℝ 𝕜 E; let := NormedSpace.restrictScalars ℝ 𝕜 E'
        exact I.convex_range.prod I'.convex_range
      · simp [range_eq_univ_of_not_isRCLikeNormedField, h]
    nonempty_interior' := by
      have : range (fun (x : ModelProd H H') ↦ (I x.1, I' x.2)) = range (Prod.map I I') := rfl
      simp [this, interior_prod_eq, nonempty_interior]
    continuous_toFun := I.continuous_toFun.prodMap I'.continuous_toFun
    continuous_invFun := I.continuous_invFun.prodMap I'.continuous_invFun }

/-- Given a finite family of `ModelWithCorners` `I i` on `(E i, H i)`, we define the model with
corners `pi I` on `(Π i, E i, ModelPi H)`. See note [Manifold type tags] for explanation about
`ModelPi H`. -/
/-
**ModelWithCorners.pi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ModelWithCorners.pi {𝕜 : Type u} [NontriviallyNormedField 𝕜] {ι : Type v} 
[Fintype ι] {E : ι -> Type w} [forall i, NormedAddCommGroup (E i)] [forall i, No
rmedSpace 𝕜 (E i)] {H : ι -> Type u'} [forall i, TopologicalSpace (H i)] (I : fo
rall i, ModelWithCorners 𝕜 (E i) (H i)) : ModelWithCorners 𝕜 (forall i, E i) (Mo
delPi H) where toPartialEquiv
参数：E i；E i；H i；I : forall i, ModelWithCorners 𝕜 (E i) (H i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite family of `ModelWithCorners` `I i` on `(E i, H i)`, we define the
 model with
corners `pi I` on `(Π i, E i, ModelPi H)`. See note [Manifold type tags] for exp
lanation about
`ModelPi H`.
-/
def ModelWithCorners.pi {𝕜 : Type u} [NontriviallyNormedField 𝕜] {ι : Type v} [Fintype ι]
    {E : ι → Type w} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {H : ι → Type u'}
    [∀ i, TopologicalSpace (H i)] (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) :
    ModelWithCorners 𝕜 (∀ i, E i) (ModelPi H) where
  toPartialEquiv := PartialEquiv.pi fun i => (I i).toPartialEquiv
  source_eq := by simp only [pi_univ, mfld_simps]
  convex_range' := by
    rw [PartialEquiv.pi_apply, Set.range_piMap]
    split_ifs with h
    · let := h.rclike
      let := fun i ↦ NormedSpace.restrictScalars ℝ 𝕜 (E i)
      exact convex_pi fun i _hi ↦ (I i).convex_range
    · simp [range_eq_univ_of_not_isRCLikeNormedField, h]
  nonempty_interior' := by
    rw [PartialEquiv.pi_apply, Set.range_piMap]
    simp [interior_pi_set finite_univ, univ_pi_nonempty_iff, nonempty_interior]
  continuous_toFun := continuous_pi fun i => (I i).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (I i).continuous_symm.comp (continuous_apply i)

/-- Special case of product model with corners, which is trivial on the second factor. This shows up
as the model to tangent bundles. -/
/-
**ModelWithCorners.tangent** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ModelWithCorners.tangent {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Typ
e v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H] 
(I : ModelWithCorners 𝕜 E H) : ModelWithCorners 𝕜 (E × E) (ModelProd H E)
参数：I : ModelWithCorners 𝕜 E H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Special case of product model with corners, which is trivial on the second facto
r. This shows up
as the model to tangent bundles.
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
/-
**modelWithCorners_prod_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：modelWithCorners_prod_toPartialEquiv : (I.prod J).toPartialEquiv = I.toPar
tialEquiv.prod J.toPartialEquiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem modelWithCorners_prod_toPartialEquiv :
    (I.prod J).toPartialEquiv = I.toPartialEquiv.prod J.toPartialEquiv :=
  rfl

@[simp, mfld_simps]
/-
**modelWithCorners_prod_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：modelWithCorners_prod_coe (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorn
ers 𝕜 E' H') : (I.prod I' : _ × _ -> _ × _) = Prod.map I I'
参数：I : ModelWithCorners 𝕜 E H；I' : ModelWithCorners 𝕜 E' H'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem modelWithCorners_prod_coe (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') :
    (I.prod I' : _ × _ → _ × _) = Prod.map I I' :=
  rfl

@[simp, mfld_simps]
/-
**modelWithCorners_prod_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：modelWithCorners_prod_coe_symm (I : ModelWithCorners 𝕜 E H) (I' : ModelWit
hCorners 𝕜 E' H') : ((I.prod I').symm : _ × _ -> _ × _) = Prod.map I.symm I'.sym
m
参数：I : ModelWithCorners 𝕜 E H；I' : ModelWithCorners 𝕜 E' H'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem modelWithCorners_prod_coe_symm (I : ModelWithCorners 𝕜 E H)
    (I' : ModelWithCorners 𝕜 E' H') :
    ((I.prod I').symm : _ × _ → _ × _) = Prod.map I.symm I'.symm :=
  rfl

/-- This lemma should be erased, or at least burn in hell, as it uses bad defeq: the left model
with corners is for `E times F`, the right one for `ModelProd E F`, and there's a good reason
we are distinguishing them. -/
/-
**modelWithCornersSelf_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜, E).prod 𝓘(𝕜, F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.ext`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedField 𝕜
} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_2 : NormedSpace 𝕜 E} {H
 : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.refl_prod_refl`：refl_prod_refl : (PartialEquiv.refl α).prod
 (PartialEquiv.refl β) = PartialEquiv.refl (α × β)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This lemma should be erased, or at least burn in hell, as it uses bad defeq: the
 left model
with corners is for `E times F`, the right one for `ModelProd E F`, and there's 
a good reason
we are distinguishing them.
-/
theorem modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜, E).prod 𝓘(𝕜, F) := by ext1 <;> simp
/-
**ModelWithCorners.range_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModelWithCorners.range_prod : range (I.prod J) = range I ×ˢ range J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ModelWithCorners.range_prod : range (I.prod J) = range I ×ˢ range J := by
  simp_rw [← ModelWithCorners.target_eq]; rfl

end ModelWithCornersProd

section Boundaryless

/-- Property ensuring that the model with corners `I` defines manifolds without boundary. This
differs from the more general `BoundarylessManifold`, which requires every point on the manifold
to be an interior point. -/
/-
**ModelWithCorners.Boundaryless** 是 Mathlib 中的一个归纳类型，位于命名空间 `ModelWithCorners`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
{H : Type u_3} → [inst_3 : TopologicalSpace H] → ModelWithCorners 𝕜 E H → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Property ensuring that the model with corners `I` defines manifolds without boun
dary. This
differs from the more general `BoundarylessManifold`, which requires every point
 on the manifold
to be an interior point.
-/
class ModelWithCorners.Boundaryless {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : Prop where
  range_eq_univ : range I = univ
/-
**ModelWithCorners.range_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModelWithCorners.range_eq_univ {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E 
: Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace 
H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] : range I = univ
参数：I : ModelWithCorners 𝕜 E H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.Boundaryless.range_eq_univ`：∀ {𝕜 : Type u_1} {inst : No
ntriviallyNormedField 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_
2 : NormedSpace 𝕜 E} {H : Type u_…
-/
theorem ModelWithCorners.range_eq_univ {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] :
    range I = univ := ModelWithCorners.Boundaryless.range_eq_univ

/-- If `I` is a `ModelWithCorners.Boundaryless` model, then it is a homeomorphism. -/
@[simps +simpRhs]
/-
**ModelWithCorners.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ModelWithCorners.toHomeomorph {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E :
 Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H
] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] : H ≃ₜ E where __
参数：I : ModelWithCorners 𝕜 E H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `ModelWithCorners.continuous_toFun`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `ModelWithCorners.continuous_invFun`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
If `I` is a `ModelWithCorners.Boundaryless` model, then it is a homeomorphism.
-/
def ModelWithCorners.toHomeomorph {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] : H ≃ₜ E where
  __ := I
  left_inv := I.left_inv
  right_inv _ := I.right_inv <| I.range_eq_univ.symm ▸ mem_univ _

/-- The trivial model with corners has no boundary -/
/-
**modelWithCornersSelf_boundaryless** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：modelWithCornersSelf_boundaryless (𝕜 : Type*) [NontriviallyNormedField 𝕜] 
(E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] : (modelWithCornersSelf 𝕜 E
).Boundaryless
参数：𝕜 : Type*；E : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The trivial model with corners has no boundary
-/
instance modelWithCornersSelf_boundaryless (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : (modelWithCornersSelf 𝕜 E).Boundaryless :=
  ⟨by simp⟩

/-- If two model with corners are boundaryless, their product also is -/
/-
**ModelWithCorners.range_eq_univ_prod** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ModelWithCorners.range_eq_univ_prod {𝕜 : Type u} [NontriviallyNormedField 
𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [Topologic
alSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] {E' : Type v'} [NormedA
ddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type w'} [TopologicalSpace H'] (I' : Mo
delWithCorners 𝕜 E' H') [I'.Boundaryless] : (I.prod I').Boundaryless
参数：I : ModelWithCorners 𝕜 E H；I' : ModelWithCorners 𝕜 E' H'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
· 使用定理 `ModelWithCorners.Boundaryless.range_eq_univ`：∀ {𝕜 : Type u_1} {inst : No
ntriviallyNormedField 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_
2 : NormedSpace 𝕜 E} {H : Type u_…
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ

--- 原说明 ---
If two model with corners are boundaryless, their product also is
-/
instance ModelWithCorners.range_eq_univ_prod {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] {E' : Type v'} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
    [I'.Boundaryless] : (I.prod I').Boundaryless := by
  constructor
  dsimp
  rw [Set.range_prodMap, ModelWithCorners.Boundaryless.range_eq_univ,
    ModelWithCorners.Boundaryless.range_eq_univ, univ_prod_univ]

end Boundaryless

section contDiffGroupoid

/-! ### `C^n` functions on models with corners -/


variable {m n : ℕ∞ω} {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]

variable (n I) in
/-- Given a model with corners `(E, H)`, we define the pregroupoid of `C^n` transformations of `H`
as the maps that are `C^n` when read in `E` through `I`. -/
/-
**contDiffPregroupoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：contDiffPregroupoid : Pregroupoid H where property f s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a model with corners `(E, H)`, we define the pregroupoid of `C^n` transfor
mations of `H`
as the maps that are `C^n` when read in `E` through `I`.
-/
def contDiffPregroupoid : Pregroupoid H where
  property f s := ContDiffOn 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
  comp {f g u v} hf hg _ _ _ := by
    have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm := by ext x; simp
    simp only [this]
    refine hg.comp (hf.mono fun x ⟨hx1, hx2⟩ ↦ ⟨hx1.1, hx2⟩) ?_
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
    have : I.symm ⁻¹' (u ∩ v) ∩ range I = I.symm ⁻¹' u ∩ range I ∩ I.symm ⁻¹' v := by
      rw [preimage_inter, inter_assoc, inter_assoc]
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
/-- Given a model with corners `(E, H)`, we define the groupoid of invertible `C^n` transformations
of `H` as the invertible maps that are `C^n` when read in `E` through `I`. -/
/-
**contDiffGroupoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：contDiffGroupoid : StructureGroupoid H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a model with corners `(E, H)`, we define the groupoid of invertible `C^n` 
transformations
of `H` as the invertible maps that are `C^n` when read in `E` through `I`.
-/
def contDiffGroupoid : StructureGroupoid H :=
  Pregroupoid.groupoid (contDiffPregroupoid n I)

/-- Inclusion of the groupoid of `C^n` local diffeos in the groupoid of `C^m` local diffeos when
`m ≤ n` -/
/-
**contDiffGroupoid_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffGroupoid_le (h : m <= n) : contDiffGroupoid n I <= contDiffGroupoi
d m I
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffGroupoid.eq_1`：∀ (n : WithTop ℕ∞) {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace …
· 使用定理 `groupoid_of_pregroupoid_le`：groupoid_of_pregroupoid_le (PG₁ PG₂ : Pregro
upoid H) (h : forall f s, PG₁.property f s -> PG₂.property f s) : PG₁.groupoid <
= PG₂.groupoid
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s

--- 原说明 ---
Inclusion of the groupoid of `C^n` local diffeos in the groupoid of `C^m` local 
diffeos when
`m ≤ n`
-/
theorem contDiffGroupoid_le (h : m ≤ n) : contDiffGroupoid n I ≤ contDiffGroupoid m I := by
  rw [contDiffGroupoid, contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  exact ContDiffOn.of_le hfs h

/-- The groupoid of `0`-times continuously differentiable maps is just the groupoid of all
open partial homeomorphisms -/
/-
**contDiffGroupoid_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffGroupoid_zero_eq : contDiffGroupoid 0 I = continuousGroupoid H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffGroupoid.eq_1`：∀ (n : WithTop ℕ∞) {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace …
· 使用定理 `mem_groupoid_of_pregroupoid`：mem_groupoid_of_pregroupoid {PG : Pregroupo
id H} {e : OpenPartialHomeomorph H H} : e in PG.groupoid ↔ PG.property e e.sourc
e ∧ PG.property e…
· 使用定理 `contDiffPregroupoid.eq_1`：∀ (n : WithTop ℕ∞) {𝕜 : Type u_1} [inst : Nont
riviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `ModelWithCorners.continuous`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `OpenPartialHomeomorph.continuousOn`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y), ContinuousOn (↑…
· 使用定理 `ModelWithCorners.continuousOn_symm`：continuousOn_symm {s} : ContinuousOn
 I.symm s
· 使用定理 `Set.MapsTo.mono_left`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t
 : Set β} {f : α → β}, Set.MapsTo f s₁ t → s₂ ⊆ s₁ → Set.MapsTo f s₂ t
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s

--- 原说明 ---
The groupoid of `0`-times continuously differentiable maps is just the groupoid 
of all
open partial homeomorphisms
-/
theorem contDiffGroupoid_zero_eq : contDiffGroupoid 0 I = continuousGroupoid H := by
  apply le_antisymm le_top
  intro u _
  -- we have to check that every open partial homeomorphism belongs to `contDiffGroupoid 0 I`,
  -- by unfolding its definition
  change u ∈ contDiffGroupoid 0 I
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  simp only [contDiffOn_zero]
  constructor
  · refine I.continuous.comp_continuousOn (u.continuousOn.comp I.continuousOn_symm ?_)
    exact (mapsTo_preimage _ _).mono_left inter_subset_left
  · refine I.continuous.comp_continuousOn (u.symm.continuousOn.comp I.continuousOn_symm ?_)
    exact (mapsTo_preimage _ _).mono_left inter_subset_left

-- FIXME: does this generalise to other groupoids? The argument is not specific
-- to C^n functions, but uses something about the groupoid's property that is not easy to abstract.
/-- Any change of coordinates with empty source belongs to `contDiffGroupoid`. -/
/-
**ContDiffGroupoid.mem_of_source_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContDiffGroupoid.mem_of_source_eq_empty (f : OpenPartialHomeomorph H H) (h
f : f.source = ∅) : f in contDiffGroupoid n I
参数：f : OpenPartialHomeomorph H H；hf : f.source = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.image_source_eq_target`：image_source_eq_target : e
 '' e.source = e.target
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Any change of coordinates with empty source belongs to `contDiffGroupoid`.
-/
lemma ContDiffGroupoid.mem_of_source_eq_empty (f : OpenPartialHomeomorph H H)
    (hf : f.source = ∅) : f ∈ contDiffGroupoid n I := by
  constructor
  · intro x ⟨hx, _⟩
    rw [mem_preimage] at hx
    simp_all only [mem_empty_iff_false]
  · intro x ⟨hx, _⟩
    have : f.target = ∅ := by simp [← f.image_source_eq_target, hf]
    simp_all

include I in
/-- Any change of coordinates with empty source belongs to `continuousGroupoid`. -/
/-
**ContinuousGroupoid.mem_of_source_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousGroupoid.mem_of_source_eq_empty (f : OpenPartialHomeomorph H H) 
(hf : f.source = ∅) : f in continuousGroupoid H
参数：f : OpenPartialHomeomorph H H；hf : f.source = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffGroupoid_zero_eq`：contDiffGroupoid_zero_eq : contDiffGroupoid 0 
I = continuousGroupoid H
· 使用引理 `ContDiffGroupoid.mem_of_source_eq_empty`：ContDiffGroupoid.mem_of_source_
eq_empty (f : OpenPartialHomeomorph H H) (hf : f.source = ∅) : f in contDiffGrou
poid n I

--- 原说明 ---
Any change of coordinates with empty source belongs to `continuousGroupoid`.
-/
lemma ContinuousGroupoid.mem_of_source_eq_empty (f : OpenPartialHomeomorph H H)
    (hf : f.source = ∅) : f ∈ continuousGroupoid H := by
  rw [← contDiffGroupoid_zero_eq (I := I)]
  exact ContDiffGroupoid.mem_of_source_eq_empty f hf

/-- An identity open partial homeomorphism belongs to the `C^n` groupoid. -/
/-
**ofSet_mem_contDiffGroupoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofSet_mem_contDiffGroupoid {s : Set H} (hs : IsOpen s) : OpenPartialHomeom
orph.ofSet s hs in contDiffGroupoid n I
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffGroupoid.eq_1`：∀ (n : WithTop ℕ∞) {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace …
· 使用定理 `mem_groupoid_of_pregroupoid`：mem_groupoid_of_pregroupoid {PG : Pregroupo
id H} {e : OpenPartialHomeomorph H H} : e in PG.groupoid ↔ PG.property e e.sourc
e ∧ PG.property e…
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `ContDiffOn.congr_mono`：ContDiffOn.congr_mono (hf : ContDiffOn 𝕜 n f s) (
h₁ : forall x in s₁, f₁ x = f x) (hs : s₁ subseteq s) : ContDiffOn 𝕜 n f₁ s₁
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.ofSet_apply`：∀ {X : Type u_1} [inst : TopologicalS
pace X] (s : Set X) (hs : IsOpen s), ↑(OpenPartialHomeomorph.ofSet s hs) = id
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
An identity open partial homeomorphism belongs to the `C^n` groupoid.
-/
theorem ofSet_mem_contDiffGroupoid {s : Set H} (hs : IsOpen s) :
    OpenPartialHomeomorph.ofSet s hs ∈ contDiffGroupoid n I := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  suffices h : ContDiffOn 𝕜 n (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I) by
    simp [h, contDiffPregroupoid]
  have : ContDiffOn 𝕜 n id (univ : Set E) := contDiff_id.contDiffOn
  exact this.congr_mono (fun x hx => I.right_inv hx.2) (subset_univ _)

/-- The composition of an open partial homeomorphism from `H` to `M` and its inverse belongs to
the `C^n` groupoid. -/
/-
**symm_trans_mem_contDiffGroupoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symm_trans_mem_contDiffGroupoid (e : OpenPartialHomeomorph M H) : e.symm.t
rans e in contDiffGroupoid n I
参数：e : OpenPartialHomeomorph M H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.mem_of_eqOnSource`：StructureGroupoid.mem_of_eqOnSource
 (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H} (he : e in G) (h :
 e' ≈ e) : e' in G
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `ofSet_mem_contDiffGroupoid`：ofSet_mem_contDiffGroupoid {s : Set H} (hs :
 IsOpen s) : OpenPartialHomeomorph.ofSet s hs in contDiffGroupoid n I
· 使用定理 `OpenPartialHomeomorph.symm_trans_self`：symm_trans_self : e.symm.trans e 
≈ OpenPartialHomeomorph.ofSet e.target e.open_target

--- 原说明 ---
The composition of an open partial homeomorphism from `H` to `M` and its inverse
 belongs to
the `C^n` groupoid.
-/
theorem symm_trans_mem_contDiffGroupoid (e : OpenPartialHomeomorph M H) :
    e.symm.trans e ∈ contDiffGroupoid n I :=
  haveI : e.symm.trans e ≈ OpenPartialHomeomorph.ofSet e.target e.open_target :=
    OpenPartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_contDiffGroupoid e.open_target) this

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']

set_option backward.isDefEq.respectTransparency false in
/-- The product of two `C^n` open partial homeomorphisms is `C^n`. -/
/-
**contDiffGroupoid_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffGroupoid_prod {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 
𝕜 E' H'} {e : OpenPartialHomeomorph H H} {e' : OpenPartialHomeomorph H' H'} (he 
: e in contDiffGroupoid n I) (he' : e' in contDiffGroupoid n I') : e.prod e' in 
contDiffGroupoid n (I.prod I')
参数：he : e in contDiffGroupoid n I；he' : e' in contDiffGroupoid n I'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
· 使用定理 `ContDiffOn.prodMap`：ContDiffOn.prodMap {E' : Type*} [NormedAddCommGroup 
E'] [NormedSpace 𝕜 E'] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {
s : Set …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.image_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `Set.prod_image_image_eq`：prod_image_image_eq {m₁ : α -> γ} {m₂ : β -> δ}
 : (m₁ '' s) ×ˢ (m₂ '' t) = (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t

--- 原说明 ---
The product of two `C^n` open partial homeomorphisms is `C^n`.
-/
theorem contDiffGroupoid_prod {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    {e : OpenPartialHomeomorph H H} {e' : OpenPartialHomeomorph H' H'}
    (he : e ∈ contDiffGroupoid n I) (he' : e' ∈ contDiffGroupoid n I') :
    e.prod e' ∈ contDiffGroupoid n (I.prod I') := by
  obtain ⟨he, he_symm⟩ := he
  obtain ⟨he', he'_symm⟩ := he'
  constructor <;> simp only [OpenPartialHomeomorph.prod_toPartialHomeomorph,
    contDiffPregroupoid]
  · have h3 := ContDiffOn.prodMap he he'
    rw [← I.image_eq, ← I'.image_eq, prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3
  · have h3 := ContDiffOn.prodMap he_symm he'_symm
    rw [← I.image_eq, ← I'.image_eq, prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3

/-- The `C^n` groupoid is closed under restriction. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `C^n` groupoid is closed under restriction.
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

/-- Typeclass defining manifolds with respect to a model with corners, over a
field `𝕜`. This definition includes the model with corners `I` (which might allow boundary, corners,
or not, so this class covers both manifolds with boundary and manifolds without boundary), and
a smoothness parameter `n : ℕ∞ω` (where `n = 0` means topological manifold, `n = ∞` means
smooth manifold and `n = ω` means analytic manifold). -/
/-
**IsManifold** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     ModelWithCorners 𝕜 E H →                 WithTop ℕ∞ → (M : Type u_4) → [ins
t : TopologicalSpace M] → [ChartedSpace H M] → Prop
参数：M : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass defining manifolds with respect to a model with corners, over a
field `𝕜`. This definition includes the model with corners `I` (which might allo
w boundary, corners,
or not, so this class covers both manifolds with boundary and manifolds without 
boundary), and
a smoothness parameter `n : ℕ∞ω` (where `n = 0` means topological manifold, `n =
 ∞` means
smooth manifold and `n = ω` means analytic manifold).
-/
class IsManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] : Prop
    extends HasGroupoid M (contDiffGroupoid n I)

/-- Building a `C^n` manifold from a `HasGroupoid` assumption. -/
/-
**IsManifold.mk'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsManifold.mk' {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [Normed
AddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWit
hCorners 𝕜 E H) (n : Nat∞ω) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] 
[gr : HasGroupoid M (contDiffGroupoid n I)] : IsManifold I n M
参数：I : ModelWithCorners 𝕜 E H；n : Nat∞ω；M : Type*；contDiffGroupoid n I。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Building a `C^n` manifold from a `HasGroupoid` assumption.
-/
theorem IsManifold.mk' {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [gr : HasGroupoid M (contDiffGroupoid n I)] : IsManifold I n M :=
  { gr with }
/-
**isManifold_of_contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isManifold_of_contDiffOn {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type
*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I 
: ModelWithCorners 𝕜 E H) (n : Nat∞ω) (M : Type*) [TopologicalSpace M] [ChartedS
pace H M] (h : forall e e' : OpenPartialHomeomorph M H, e in atlas H M -> e' in 
atlas H M -> ContDiffOn 𝕜 n (I ∘ e.symm ≫ₕ e' ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e
').source inter range I)) : IsManifold I n M where compatible
参数：I : ModelWithCorners 𝕜 E H；n : Nat∞ω；M : Type*；h : forall e e' : OpenPartialH
omeomorph M H, e in atlas H M -> e' in atlas H M -> ContDiffOn 𝕜 n (I ∘ e.symm ≫
ₕ e' ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source inter range I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasGroupoid_of_pregroupoid`：hasGroupoid_of_pregroupoid (PG : Pregroupoid
 H) (h : forall {e e' : OpenPartialHomeomorph M H}, e in atlas H M -> e' in atla
s H M -> PG.prop…
· 使用定理 `StructureGroupoid.compatible`：StructureGroupoid.compatible {H : Type*} [
TopologicalSpace H] (G : StructureGroupoid H) {M : Type*} [TopologicalSpace M] [
ChartedSpace H M] …
-/
theorem isManifold_of_contDiffOn {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    (h : ∀ e e' : OpenPartialHomeomorph M H, e ∈ atlas H M → e' ∈ atlas H M →
      ContDiffOn 𝕜 n (I ∘ e.symm ≫ₕ e' ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I)) :
    IsManifold I n M where
  compatible := by
    have : HasGroupoid M (contDiffGroupoid n I) := hasGroupoid_of_pregroupoid _ (h _ _)
    apply StructureGroupoid.compatible

/-- For any model with corners, the model space is a `C^n` manifold -/
/-
**instIsManifoldModelSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instIsManifoldModelSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type
*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I 
: ModelWithCorners 𝕜 E H} {n : Nat∞ω} : IsManifold I n H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any model with corners, the model space is a `C^n` manifold
-/
instance instIsManifoldModelSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} : IsManifold I n H :=
  { hasGroupoid_model_space _ _ with }

end IsManifold

namespace IsManifold

/- We restate in the namespace `IsManifold` some lemmas that hold for general
charted space with a structure groupoid, avoiding the need to specify the groupoid
`contDiffGroupoid n I` explicitly. -/
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {n : ℕ∞ω} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-
**IsManifold.of_le** 是 Mathlib 中的一个定理，位于命名空间 `IsManifold`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {m n : WithTop ℕ∞},   m ≤ n → ∀ [IsMa
nifold I n M], IsManifold I m M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasGroupoid_of_le`：hasGroupoid_of_le {G₁ G₂ : StructureGroupoid H} (h : 
HasGroupoid M G₁) (hle : G₁ <= G₂) : HasGroupoid M G₂
· 使用定理 `IsManifold.toHasGroupoid`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFie
ld 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_2 : NormedSpace 𝕜 E
} {H : Type u_…
· 使用定理 `contDiffGroupoid_le`：contDiffGroupoid_le (h : m <= n) : contDiffGroupoid
 n I <= contDiffGroupoid m I
· 使用定理 `IsManifold.mk'`：IsManifold.mk' {𝕜 : Type*} [NontriviallyNormedField 𝕜] {
E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpac
e H]…
-/
protected theorem of_le {m n : ℕ∞ω} (hmn : m ≤ n)
    [IsManifold I n M] : IsManifold I m M := by
  have : HasGroupoid M (contDiffGroupoid m I) :=
    hasGroupoid_of_le (G₁ := contDiffGroupoid n I) (by infer_instance)
      (contDiffGroupoid_le hmn)
  exact mk' I m M

/-- A typeclass registering that a smoothness exponent is smaller than `∞`. Used to deduce that
some manifolds are `C^n` when they are `C^∞`. -/
/-
**IsManifold._root_.ENat.LEInfty** 是 Mathlib 中的一个类，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass registering that a smoothness exponent is smaller than `∞`. Used to 
deduce that
some manifolds are `C^n` when they are `C^∞`.
-/
class _root_.ENat.LEInfty (m : ℕ∞ω) where
  out : m ≤ ∞

open ENat
/-
**IsManifold.** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ∞) : LEInfty (n : ℕ∞ω) := ⟨mod_cast le_top⟩
/-
**IsManifold.** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : LEInfty (n : ℕ∞ω) := ⟨mod_cast le_top⟩
/-
**IsManifold.** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) [n.AtLeastTwo] : LEInfty (no_index (OfNat.ofNat n) : ℕ∞ω) :=
  inferInstanceAs (LEInfty (n : ℕ∞ω))
/-
**IsManifold.** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LEInfty (1 : ℕ∞ω) := inferInstanceAs (LEInfty ((1 : ℕ) : ℕ∞ω))
/-
**IsManifold.** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LEInfty (0 : ℕ∞ω) := inferInstanceAs (LEInfty ((0 : ℕ) : ℕ∞ω))
/-
**IsManifold.** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : ℕ∞ω} [IsManifold I ∞ M] [h : LEInfty a] :
    IsManifold I a M :=
  IsManifold.of_le h.out
/-
**IsManifold.** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : ℕ∞ω} [IsManifold I ω M] :
    IsManifold I a M :=
  IsManifold.of_le le_top
/-
**IsManifold.** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsManifold I 0 M := by
  suffices HasGroupoid M (contDiffGroupoid 0 I) from mk' I 0 M
  constructor
  intro e e' he he'
  rw [contDiffGroupoid_zero_eq]
  trivial
/-
**IsManifold.** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsManifold I 2 M] :
    IsManifold I 1 M :=
  IsManifold.of_le one_le_two
/-
**IsManifold.** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsManifold I 3 M] : IsManifold I 2 M := IsManifold.of_le (n := 3) (by norm_cast)

variable (I n M) in
/-- The maximal atlas of `M` for the `C^n` manifold with corners structure corresponding to the
model with corners `I`. -/
/-
**IsManifold.maximalAtlas** 是 Mathlib 中的一个定义，位于命名空间 `IsManifold`。
形式化陈述：maximalAtlas
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal atlas of `M` for the `C^n` manifold with corners structure correspon
ding to the
model with corners `I`.
-/
def maximalAtlas :=
  (contDiffGroupoid n I).maximalAtlas M
/-
**IsManifold.mem_maximalAtlas_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsManifold`。
形式化陈述：mem_maximalAtlas_iff {e : OpenPartialHomeomorph M H} : e in maximalAtlas I
 n M ↔ e in (contDiffGroupoid n I).maximalAtlas M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_maximalAtlas_iff {e : OpenPartialHomeomorph M H} :
    e ∈ maximalAtlas I n M ↔ e ∈ (contDiffGroupoid n I).maximalAtlas M := by
  rfl
/-
**IsManifold.subset_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 `IsManifold`。
形式化陈述：subset_maximalAtlas [IsManifold I n M] : atlas H M subseteq maximalAtlas I
 n M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.subset_maximalAtlas`：StructureGroupoid.subset_maximalA
tlas [HasGroupoid M G] : atlas H M subseteq G.maximalAtlas M
· 使用定理 `IsManifold.toHasGroupoid`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFie
ld 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_2 : NormedSpace 𝕜 E
} {H : Type u_…
-/
theorem subset_maximalAtlas [IsManifold I n M] : atlas H M ⊆ maximalAtlas I n M :=
  StructureGroupoid.subset_maximalAtlas _
/-
**IsManifold.chart_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 `IsManifold`。
形式化陈述：chart_mem_maximalAtlas [IsManifold I n M] (x : M) : chartAt H x in maximal
Atlas I n M
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.chart_mem_maximalAtlas`：StructureGroupoid.chart_mem_ma
ximalAtlas [HasGroupoid M G] (x : M) : chartAt H x in G.maximalAtlas M
· 使用定理 `IsManifold.toHasGroupoid`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFie
ld 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_2 : NormedSpace 𝕜 E
} {H : Type u_…
-/
theorem chart_mem_maximalAtlas [IsManifold I n M] (x : M) :
    chartAt H x ∈ maximalAtlas I n M :=
  StructureGroupoid.chart_mem_maximalAtlas _ x
/-
**IsManifold.compatible_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 `IsManifol
d`。
形式化陈述：compatible_of_mem_maximalAtlas {e e' : OpenPartialHomeomorph M H} (he : e 
in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) : e.symm.trans e' in con
tDiffGroupoid n I
参数：he : e in maximalAtlas I n M；he' : e' in maximalAtlas I n M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.compatible_of_mem_maximalAtlas`：StructureGroupoid.comp
atible_of_mem_maximalAtlas {e e' : OpenPartialHomeomorph M H} (he : e in G.maxim
alAtlas M) (he' : e' in G.maximalAtlas…
-/
theorem compatible_of_mem_maximalAtlas {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ maximalAtlas I n M) (he' : e' ∈ maximalAtlas I n M) :
    e.symm.trans e' ∈ contDiffGroupoid n I :=
  StructureGroupoid.compatible_of_mem_maximalAtlas he he'
/-
**IsManifold.maximalAtlas_subset_of_le** 是 Mathlib 中的一个引理，位于命名空间 `IsManifold`。
形式化陈述：maximalAtlas_subset_of_le {m n : Nat∞ω} (h : m <= n) : maximalAtlas I n M 
subseteq maximalAtlas I m M
参数：h : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.maximalAtlas_mono`：StructureGroupoid.maximalAtlas_mono
 {G G' : StructureGroupoid H} (h : G <= G') : G.maximalAtlas M subseteq G'.maxim
alAtlas M
· 使用定理 `contDiffGroupoid_le`：contDiffGroupoid_le (h : m <= n) : contDiffGroupoid
 n I <= contDiffGroupoid m I
-/
lemma maximalAtlas_subset_of_le {m n : ℕ∞ω} (h : m ≤ n) :
    maximalAtlas I n M ⊆ maximalAtlas I m M :=
  StructureGroupoid.maximalAtlas_mono (contDiffGroupoid_le h)

variable (n) in
/-- The empty set is a `C^n` manifold w.r.t. any charted space and model. -/
/-
**IsManifold.empty** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
形式化陈述：empty [IsEmpty M] : IsManifold I n M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isManifold_of_contDiffOn`：isManifold_of_contDiffOn {𝕜 : Type*} [Nontrivi
allyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Typ
e*} [Topologic…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.trans_source`：trans_source : (e.trans e').source =
 e.source inter e ⁻¹' e'.source
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `Set.preimage_empty`：preimage_empty : f ⁻¹' ∅ = ∅
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `Subtype.preimage_val_eq_preimage_val_iff`：preimage_val_eq_preimage_val_i
ff (s t u : Set α) : (Subtype.val : s -> α) ⁻¹' t = Subtype.val ⁻¹' u ↔ s inter 
t = s inter u
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅

--- 原说明 ---
The empty set is a `C^n` manifold w.r.t. any charted space and model.
-/
instance empty [IsEmpty M] : IsManifold I n M := by
  apply isManifold_of_contDiffOn
  intro e e' _ _ x hx
  set t := I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I
  -- Since `M` is empty, the condition about compatibility of transition maps is vacuous.
  have : (e.symm ≫ₕ e').source = ∅ := calc (e.symm ≫ₕ e').source
    _ = (e.symm.source) ∩ e.symm ⁻¹' e'.source := by rw [← OpenPartialHomeomorph.trans_source]
    _ = (e.symm.source) ∩ e.symm ⁻¹' ∅ := by rw [eq_empty_of_isEmpty (e'.source)]
    _ = (e.symm.source) ∩ ∅ := by rw [preimage_empty]
    _ = ∅ := inter_empty e.symm.source
  have : t = ∅ := calc t
    _ = I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I := by
      rw [← Subtype.preimage_val_eq_preimage_val_iff]
    _ = ∅ ∩ range I := by rw [this, preimage_empty]
    _ = ∅ := empty_inter (range I)
  apply (this ▸ hx).elim

attribute [local instance] ChartedSpace.ofDiscreteTopology in
variable (n) in
/-- A discrete space `M` is a smooth manifold over the trivial model on a trivial normed space. -/
/-
**IsManifold.of_discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 `IsManifold`。
形式化陈述：of_discreteTopology [DiscreteTopology M] [Unique E] : IsManifold (modelWit
hCornersSelf 𝕜 E) n M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isManifold_of_contDiffOn`：isManifold_of_contDiffOn {𝕜 : Type*} [Nontrivi
allyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Typ
e*} [Topologic…
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `contDiff_of_subsingleton`：contDiff_of_subsingleton [Subsingleton F] : Co
ntDiff 𝕜 n f
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
A discrete space `M` is a smooth manifold over the trivial model on a trivial no
rmed space.
-/
theorem of_discreteTopology [DiscreteTopology M] [Unique E] :
    IsManifold (modelWithCornersSelf 𝕜 E) n M := by
  apply isManifold_of_contDiffOn _ _ _ (fun _ _ _ _ ↦ contDiff_of_subsingleton.contDiffOn)

attribute [local instance] ChartedSpace.ofDiscreteTopology in
/-
**IsManifold.** 是 Mathlib 中的一个示例，位于命名空间 `IsManifold`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Unique E] : IsManifold (𝓘(𝕜, E)) n (Fin 2) := of_discreteTopology _

/-- The product of two `C^n` manifolds is naturally a `C^n` manifold. -/
/-
**IsManifold.prod** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
形式化陈述：prod {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGro
up E] [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] 
{H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [Topo
logicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} (M : Type*) [TopologicalSpace M
] [ChartedSpace H M] [IsManifold I n M] (M' : Type*) [TopologicalSpace M'] [Char
tedSpace H' M'] [IsManifold I' n M'] : IsManifold (I.prod I') n (M × M') where c
ompatible
参数：M : Type*；M' : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.prod_symm`：prod_symm (eX : OpenPartialHomeomorph X
 X') (eY : OpenPartialHomeomorph Y Y') : (eX.prod eY).symm = eX.symm.prod eY.sym
m
· 使用定理 `OpenPartialHomeomorph.prod_trans`：prod_trans (e : OpenPartialHomeomorph 
X Y) (f : OpenPartialHomeomorph Y Z) (e' : OpenPartialHomeomorph X' Y') (f' : Op
enPartialHomeomorph Y'…
· 使用定理 `StructureGroupoid.compatible`：StructureGroupoid.compatible {H : Type*} [
TopologicalSpace H] (G : StructureGroupoid H) {M : Type*} [TopologicalSpace M] [
ChartedSpace H M] …
· 使用定理 `IsManifold.toHasGroupoid`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFie
ld 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_2 : NormedSpace 𝕜 E
} {H : Type u_…
· 使用定理 `contDiffGroupoid_prod`：contDiffGroupoid_prod {I : ModelWithCorners 𝕜 E H
} {I' : ModelWithCorners 𝕜 E' H'} {e : OpenPartialHomeomorph H H} {e' : OpenPart
ialHomeomor…

--- 原说明 ---
The product of two `C^n` manifolds is naturally a `C^n` manifold.
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
    rw [OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_trans]
    have h1 := (contDiffGroupoid n I).compatible hf1 hg1
    have h2 := (contDiffGroupoid n I').compatible hf2 hg2
    exact contDiffGroupoid_prod h1 h2

section

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-
**IsManifold.mem_maximalAtlas_prod** 是 Mathlib 中的一个引理，位于命名空间 `IsManifold`。
形式化陈述：mem_maximalAtlas_prod [IsManifold I n M] [IsManifold I' n M'] {e : OpenPar
tialHomeomorph M H} (he : e in maximalAtlas I n M) {e' : OpenPartialHomeomorph M
' H'} (he' : e' in maximalAtlas I' n M') : e.prod e' in maximalAtlas (I.prod I')
 n (M × M')
参数：he : e in maximalAtlas I n M；he' : e' in maximalAtlas I' n M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.prod_symm_trans_prod`：prod_symm_trans_prod (e f : 
OpenPartialHomeomorph X Y) (e' f' : OpenPartialHomeomorph X' Y') : (e.prod e').s
ymm.trans (f.prod f') = (e.symm.…
· 使用定理 `contDiffGroupoid_prod`：contDiffGroupoid_prod {I : ModelWithCorners 𝕜 E H
} {I' : ModelWithCorners 𝕜 E' H'} {e : OpenPartialHomeomorph H H} {e' : OpenPart
ialHomeomor…
-/
lemma mem_maximalAtlas_prod [IsManifold I n M] [IsManifold I' n M']
    {e : OpenPartialHomeomorph M H} (he : e ∈ maximalAtlas I n M)
    {e' : OpenPartialHomeomorph M' H'} (he' : e' ∈ maximalAtlas I' n M') :
    e.prod e' ∈ maximalAtlas (I.prod I') n (M × M') := by
  simp only [mem_maximalAtlas_iff]
  rintro e'' ⟨f, hf, f', hf', rfl⟩
  rw [OpenPartialHomeomorph.prod_symm_trans_prod,
    OpenPartialHomeomorph.prod_symm_trans_prod]
  constructor <;>
    apply contDiffGroupoid_prod <;> grind [compatible_of_mem_maximalAtlas, subset_maximalAtlas]

end

section DisjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  [hM : IsManifold I n M] [hM' : IsManifold I n M']

/-- The disjoint union of two `C^n` manifolds modelled on `(E, H)`
is a `C^n` manifold modelled on `(E, H)`. -/
/-
**IsManifold.disjointUnion** 是 Mathlib 中的一个实例，位于命名空间 `IsManifold`。
形式化陈述：disjointUnion : IsManifold I n (M oplus M') where compatible {e} e' he he'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用引理 `ContDiffGroupoid.mem_of_source_eq_empty`：ContDiffGroupoid.mem_of_source_
eq_empty (f : OpenPartialHomeomorph H H) (hf : f.source = ∅) : f in contDiffGrou
poid n I
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
· 使用引理 `ChartedSpace.mem_atlas_sum`：ChartedSpace.mem_atlas_sum [h : Nonempty H] 
{e : OpenPartialHomeomorph (M oplus M') H} (he : e in atlas H (M oplus M')) : (e
xists f : OpenPa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OpenPartialHomeomorph.lift_openEmbedding_trans`：lift_openEmbedding_trans
 (e e' : OpenPartialHomeomorph X Z) (hf : IsOpenEmbedding f) : (e.lift_openEmbed
ding hf).symm.trans (e'.lift_openEmb…
· 使用定理 `HasGroupoid.compatible`：∀ {H : Type u_5} {inst : TopologicalSpace H} {M 
: Type u_6} {inst_1 : TopologicalSpace M} {inst_2 : ChartedSpace H M}   {G : Str
uctureGroupo…
· 使用定理 `IsManifold.toHasGroupoid`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFie
ld 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_2 : NormedSpace 𝕜 E
} {H : Type u_…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False

--- 原说明 ---
The disjoint union of two `C^n` manifolds modelled on `(E, H)`
is a `C^n` manifold modelled on `(E, H)`.
-/
instance disjointUnion : IsManifold I n (M ⊕ M') where
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
        exact ⟨fun ⟨hx₁, hx₂⟩ ↦ by simp_all, fun hx ↦ hx.elim⟩
    · -- Analogous argument to the first case: is there a way to deduplicate?
      obtain (⟨f', hf', he'f'⟩ | ⟨f', hf', he'f'⟩) := ChartedSpace.mem_atlas_sum he'
      · rw [hef, he'f']
        apply ContDiffGroupoid.mem_of_source_eq_empty
        ext x
        exact ⟨fun ⟨hx₁, hx₂⟩ ↦ by simp_all, fun hx ↦ hx.elim⟩
      · rw [hef, he'f', f.lift_openEmbedding_trans f' IsOpenEmbedding.inr]
        exact hM'.compatible hf hf'

end DisjointUnion

end IsManifold

/-
**OpenPartialHomeomorph.isManifold_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.isManifold_singleton {𝕜 : Type*} [NontriviallyNormed
Field 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [Topol
ogicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : Nat∞ω} {M : Type*} [Topological
Space M] (e : OpenPartialHomeomorph M H) (h : e.source = Set.univ) : @IsManifold
 𝕜 _ E _ _ H _ I n M _ (e.singletonChartedSpace h)
参数：e : OpenPartialHomeomorph M H；h : e.source = Set.univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsManifold.mk'`：IsManifold.mk' {𝕜 : Type*} [NontriviallyNormedField 𝕜] {
E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpac
e H]…
· 使用定理 `OpenPartialHomeomorph.singleton_hasGroupoid`：singleton_hasGroupoid (h : 
e.source = Set.univ) (G : StructureGroupoid H) [ClosedUnderRestriction G] : @Has
Groupoid _ _ _ _ (e.singletonChar…
· 使用定理 `instClosedUnderRestrictionContDiffGroupoid`：∀ {n : WithTop ℕ∞} {𝕜 : Type
 u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommG
roup E]   [inst_2 : NormedSpace …
-/
theorem OpenPartialHomeomorph.isManifold_singleton
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] (e : OpenPartialHomeomorph M H) (h : e.source = Set.univ) :
    @IsManifold 𝕜 _ E _ _ H _ I n M _ (e.singletonChartedSpace h) :=
  @IsManifold.mk' _ _ _ _ _ _ _ _ _ _ _ (id _) <|
    e.singleton_hasGroupoid h (contDiffGroupoid n I)
/-
**Topology.IsOpenEmbedding.isManifold_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.isManifold_singleton {𝕜 E H : Type*} [Nontriviall
yNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I
 : ModelWithCorners 𝕜 E H} {n : Nat∞ω} {M : Type*} [TopologicalSpace M] [Nonempt
y M] {f : M -> H} (h : IsOpenEmbedding f) : @IsManifold 𝕜 _ E _ _ H _ I n M _ h.
singletonChartedSpace
参数：h : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.isManifold_singleton`：OpenPartialHomeomorph.isMani
fold_singleton {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCom
mGroup E] [NormedSpace 𝕜 E] {H :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source`：∀ {X : Type u_1
} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : 
X → Y)   (h : Topology.IsOpenEmbedding f) [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Topology.IsOpenEmbedding.isManifold_singleton {𝕜 E H : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [Nonempty M] {f : M → H} (h : IsOpenEmbedding f) :
    @IsManifold 𝕜 _ E _ _ H _ I n M _ h.singletonChartedSpace :=
  (h.toOpenPartialHomeomorph f).isManifold_singleton (by simp)

namespace TopologicalSpace.Opens

open TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  (s : Opens M)

/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**TangentSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TangentSpace {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type u} [NormedA
ddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWith
Corners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (_x : M) : Ty
pe u
参数：I : ModelWithCorners 𝕜 E H；_x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tangent space at a point of the manifold `M`. It is just `E`. We could use i
nstead
`(tangentBundleCore I M).toFiberBundleCore.fiber x`, but we use `E` to help the 
kernel.

The definition of `TangentSpace` is not reducible so that type class inference
does not pick wrong instances.
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
/-- Identifying the tangent space at a normed space with the normed space itself.
This canonical identification (which, in mathlib, is implemented using an abuse of definitional
equality) is very prevalent in a number of places: this device allows making it explicit. -/
/-
**NormedSpace.fromTangentSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NormedSpace.fromTangentSpace (v : E) : TangentSpace 𝓘(𝕜, E) v ≃L[𝕜] E wher
e toFun v
参数：v : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identifying the tangent space at a normed space with the normed space itself.
This canonical identification (which, in mathlib, is implemented using an abuse 
of definitional
equality) is very prevalent in a number of places: this device allows making it 
explicit.
-/
def NormedSpace.fromTangentSpace (v : E) : TangentSpace 𝓘(𝕜, E) v ≃L[𝕜] E where
  toFun v := v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (TangentSpace I x) := ⟨0⟩

variable (M) in
-- is empty if the base manifold is empty
/-- The tangent bundle to a manifold, as a Sigma type. Defined in terms of
`Bundle.TotalSpace` to be able to put a suitable topology on it. -/
@[wikidata Q746550]
/-
**TangentBundle** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TangentBundle
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tangent bundle to a manifold, as a Sigma type. Defined in terms of
`Bundle.TotalSpace` to be able to put a suitable topology on it.
-/
abbrev TangentBundle := Bundle.TotalSpace E (TangentSpace I : M → Type _)

end TangentSpace

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

deriving instance PathConnectedSpace for TangentSpace I x

end Real

