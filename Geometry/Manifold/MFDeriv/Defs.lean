/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.LocalInvariantProperties

/-!
# The derivative of functions between manifolds

Let `M` and `M'` be two manifolds over a field `𝕜` (with respective models with
corners `I` on `(E, H)` and `I'` on `(E', H')`), and let `f : M → M'`. We define the
derivative of the function at a point, within a set or along the whole space, mimicking the API
for (Fréchet) derivatives. It is denoted by `mfderiv I I' f x`, where "m" stands for "manifold" and
"f" for "Fréchet" (as in the usual derivative `fderiv 𝕜 f x`).

## Main definitions

* `UniqueMDiffOn I s` : predicate saying that, at each point of the set `s`, a function can have
  at most one derivative. This technical condition is important when we define
  `mfderivWithin` below, as otherwise there is an arbitrary choice in the derivative,
  and many properties will fail (for instance the chain rule). This is analogous to
  `UniqueDiffOn 𝕜 s` in a vector space.

Let `f` be a map between manifolds. The following definitions follow the `fderiv` API.

* `mfderiv I I' f x` : the derivative of `f` at `x`, as a continuous linear map from the tangent
  space at `x` to the tangent space at `f x`. If the map is not differentiable, this is `0`.
* `mfderivWithin I I' f s x` : the derivative of `f` at `x` within `s`, as a continuous linear map
  from the tangent space at `x` to the tangent space at `f x`. If the map is not differentiable
  within `s`, this is `0`.
* `MDifferentiableAt I I' f x` : Prop expressing whether `f` is differentiable at `x`.
* `MDifferentiableWithinAt I I' f s x` : Prop expressing whether `f` is differentiable within `s`
  at `x`.
* `HasMFDerivAt I I' f s x f'` : Prop expressing whether `f` has `f'` as a derivative at `x`.
* `HasMFDerivWithinAt I I' f s x f'` : Prop expressing whether `f` has `f'` as a derivative
  within `s` at `x`.
* `MDifferentiableOn I I' f s` : Prop expressing that `f` is differentiable on the set `s`.
* `MDifferentiable I I' f` : Prop expressing that `f` is differentiable everywhere.
* `tangentMap I I' f` : the derivative of `f`, as a map from the tangent bundle of `M` to the
  tangent bundle of `M'`.

Various related results are proven in separate files: see
- `Basic.lean` for basic properties of the `mfderiv`, mimicking the API of the Fréchet derivative,
- `FDeriv.lean` for the equivalence of the manifold notions with the usual Fréchet derivative
  for functions between vector spaces,
- `SpecificFunctions.lean` for results on the differential of the identity, constant functions,
  products and arithmetic operators (like addition or scalar multiplication),
- `Atlas.lean` for differentiability of charts, models with corners and extended charts,
- `UniqueDifferential.lean` for various properties of unique differentiability sets in manifolds.

## Implementation notes

The tangent bundle is constructed using the machinery of topological fiber bundles, for which one
can define bundled morphisms and construct canonically maps from the total space of one bundle to
the total space of another one. One could use this mechanism to construct directly the derivative
of a smooth map. However, we want to define the derivative of any map (and let it be zero if the map
is not differentiable) to avoid proof arguments everywhere. This means we have to go back to the
details of the definition of the total space of a fiber bundle constructed from core, to cook up a
suitable definition of the derivative. It is the following: at each point, we have a preferred chart
(used to identify the fiber above the point with the model vector space in fiber bundles). Then one
should read the function using these preferred charts at `x` and `f x`, and take the derivative
of `f` in these charts.

Due to the fact that we are working in a model with corners, with an additional embedding `I` of the
model space `H` in the model vector space `E`, the charts taking values in `E` are not the original
charts of the manifold, but those ones composed with `I`, called extended charts. We define
`writtenInExtChartAt I I' x f` for the function `f` written in the preferred extended charts. Then
the manifold derivative of `f`, at `x`, is just the usual derivative of
`writtenInExtChartAt I I' x f`, at the point `(extChartAt I x) x`.

There is a subtlety with respect to continuity: if the function is not continuous, then the image
of a small open set around `x` will not be contained in the source of the preferred chart around
`f x`, which means that when reading `f` in the chart one is losing some information. To avoid this,
we include continuity in the definition of differentiability (which is reasonable since with any
definition, differentiability implies continuity).

*Warning*: the derivative (even within a subset) is a linear map on the whole tangent space. Suppose
that one is given a smooth submanifold `N`, and a function which is smooth on `N` (i.e., its
restriction to the subtype `N` is smooth). Then, in the whole manifold `M`, the property
`MDifferentiableOn I I' f N` holds. However, `mfderivWithin I I' f N` is not uniquely defined
(what values would one choose for vectors that are transverse to `N`?), which can create issues down
the road. The problem here is that knowing the value of `f` along `N` does not determine the
differential of `f` in all directions. This is in contrast to the case where `N` would be an open
subset, or a submanifold with boundary of maximal dimension, where this issue does not appear.
The predicate `UniqueMDiffOn I N` indicates that the derivative along `N` is unique if it exists,
and is an assumption in most statements requiring a form of uniqueness.

On a vector space, the manifold derivative and the usual derivative are equal. This means in
particular that they live on the same space, i.e., the tangent space is defeq to the original vector
space. To get this property is a motivation for our definition of the tangent space as a single
copy of the vector space, instead of more usual definitions such as the space of derivations, or
the space of equivalence classes of smooth curves in the manifold.

## Tags
derivative, manifold
-/

@[expose] public section

noncomputable section

open scoped Topology ContDiff
open Set ChartedSpace

section DerivativesDefinitions

/-!
### Derivative of maps between manifolds

The derivative of a map `f` between manifolds `M` and `M'` at `x` is a bounded linear
map from the tangent space to `M` at `x`, to the tangent space to `M'` at `f x`. Since we defined
the tangent space using one specific chart, the formula for the derivative is written in terms of
this specific chart.

We use the names `MDifferentiable` and `mfderiv`, where the prefix letter `m` means "manifold".
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M']

variable (I I') in
/--
Definition of `DifferentiableWithinAtProp` / `DifferentiableWithinAtProp` 的定义

English:
definition DifferentiableWithinAtProp
  signature: (f : H -> H') (s : Set H) (x : H)
  body: DifferentiableWithinAt 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s inter Set.range I) (I x)

中文:
定义 DifferentiableWithinAtProp
  签名: (f : H -> H') (s : 集合 H) (x : H)
  定义体: DifferentiableWithinAt 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s inter Set.range I) (I x)

Depends on / 依赖: DifferentiableWithinAt, I.symm, LinearEquiv, LinearEquiv.ext, Set.range, mapRange_id
-/
def DifferentiableWithinAtProp (f : H -> H') (s : Set H) (x : H) : Prop :=
  DifferentiableWithinAt 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s inter Set.range I) (I x)

open scoped Manifold

/--
theorem `differentiableWithinAtProp_self_source` / 定理 `differentiableWithinAtProp_self_source`

English:
theorem differentiableWithinAtProp_self_source
  given: {f : E -> H'} {s : Set E} {x : E}
  proof: by
  simp_rw [DifferentiableWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]

中文:
定理 differentiableWithinAtProp_self_source
  条件: {f : E -> H'} {s : 集合 E} {x : E}
  证明: by
  simp_rw [DifferentiableWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]

Depends on / 依赖: CompTriple, CompTriple.comp_eq, DifferentiableWithinAtProp, LinearEquiv, LinearEquiv.ext, comp_eq, f.map_zero, f.trans, id_eq, inter_univ, mapRange_comp, map_zero, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, preimage_id_eq, range_id, simp_rw
-/
theorem differentiableWithinAtProp_self_source {f : E -> H'} {s : Set E} {x : E} :
    DifferentiableWithinAtProp 𝓘(𝕜, E) I' f s x ↔ DifferentiableWithinAt 𝕜 (I' ∘ f) s x := by
  simp_rw [DifferentiableWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]

/--
theorem `DifferentiableWithinAtProp_self` / 定理 `DifferentiableWithinAtProp_self`

English:
theorem DifferentiableWithinAtProp_self
  given: {f : E -> E'} {s : Set E} {x : E}
  proof: differentiableWithinAtProp_self_source

中文:
定理 DifferentiableWithinAtProp_self
  条件: {f : E -> E'} {s : 集合 E} {x : E}
  证明: differentiableWithinAtProp_self_source

Depends on / 依赖: LinearEquiv, LinearEquiv.ext, differentiableWithinAtProp_self_source
-/
theorem DifferentiableWithinAtProp_self {f : E -> E'} {s : Set E} {x : E} :
    DifferentiableWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E') f s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  differentiableWithinAtProp_self_source

/--
theorem `differentiableWithinAtProp_self_target` / 定理 `differentiableWithinAtProp_self_target`

English:
theorem differentiableWithinAtProp_self_target
  given: {f : H -> E'} {s : Set H} {x : H}
  proof: Iff.rfl

中文:
定理 differentiableWithinAtProp_self_target
  条件: {f : H -> E'} {s : 集合 H} {x : H}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem differentiableWithinAtProp_self_target {f : H -> E'} {s : Set H} {x : H} :
    DifferentiableWithinAtProp I 𝓘(𝕜, E') f s x ↔
      DifferentiableWithinAt 𝕜 (f ∘ I.symm) (I.symm ⁻¹' s inter range I) (I x) :=
  Iff.rfl

/--
theorem `differentiableWithinAt_localInvariantProp` / 定理 `differentiableWithinAt_localInvariantProp`

English:
theorem differentiableWithinAt_localInvariantProp
  proof: { is_local := by
      intro s x u f u_open xu
      have : I.symm ⁻¹' (s inter u) inter Set.range I = I.symm ⁻¹' s inter Set.range I inter I.symm ⁻¹' u := by
        simp only [Set.inter_right_comm, Set.preimage_inter]
      rw [DifferentiableWithinAtProp]; rw [DifferentiableWithinAtProp]; rw [this]
      symm
      apply differentiableWithinAt_inter
      have : u in 𝓝 (I.symm (I x)) := by
        rw [ModelWithCorners.left_inv]
        exact u_open.mem_nhds xu
      apply I.continuous_symm.continuousAt this
    right_invariance' := by
      intro s x f e he hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
      rw [this] at h
      have : I (e x) in I.symm ⁻¹' e.target inter Set.range I := by simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he).2.contDiffWithinAt this
      convert! (h.comp' _ (this.differentiableWithinAt one_ne_zero)).mono_of_mem_nhdsWithin _
        using 1
      · ext y; simp only [mfld_simps]
      refine
        mem_nhdsWithin.mpr
          ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
            simp_rw [Set.mem_preimage, I.left_inv, e.mapsTo hx], ?_⟩
      mfld_set_tac
    congr_of_forall := by
      intro s x f g h hx hf
      apply hf.congr
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [h, hy, mfld_simps]
      · simp only [hx, mfld_simps]
    left_invariance' := by
      intro s x f e' he' hs hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have A : (I' ∘ f ∘ I.symm) (I x) in I'.symm ⁻¹' e'.source inter Set.range I' := by
        simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he').1.contDiffWithinAt A
      convert! (this.differentiableWithinAt one_ne_zero).comp _ h _
      · ext y; simp only [mfld_simps]
      · intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1 }

中文:
定理 differentiableWithinAt_localInvariantProp
  证明: { is_local := by
      intro s x u f u_open xu
      have : I.symm ⁻¹' (s inter u) inter Set.range I = I.symm ⁻¹' s inter Set.range I inter I.symm ⁻¹' u := by
        simp only [Set.inter_right_comm, Set.preimage_inter]
      rw [DifferentiableWithinAtProp]; rw [DifferentiableWithinAtProp]; rw [this]
      symm
      apply differentiableWithinAt_inter
      have : u in 𝓝 (I.symm (I x)) := by
        rw [ModelWithCorners.left_inv]
        exact u_open.mem_nhds xu
      apply I.continuous_symm.continuousAt this
    right_invariance' := by
      intro s x f e he hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
      rw [this] at h
      have : I (e x) in I.symm ⁻¹' e.target inter Set.range I := by simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he).2.contDiffWithinAt this
      convert! (h.comp' _ (this.differentiableWithinAt one_ne_zero)).mono_of_mem_nhdsWithin _
        using 1
      · ext y; simp only [mfld_simps]
      refine
        mem_nhdsWithin.mpr
          ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
            simp_rw [Set.mem_preimage, I.left_inv, e.mapsTo hx], ?_⟩
      mfld_set_tac
    congr_of_forall := by
      intro s x f g h hx hf
      apply hf.congr
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [h, hy, mfld_simps]
      · simp only [hx, mfld_simps]
    left_invariance' := by
      intro s x f e' he' hs hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have A : (I' ∘ f ∘ I.symm) (I x) in I'.symm ⁻¹' e'.source inter Set.range I' := by
        simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he').1.contDiffWithinAt A
      convert! (this.differentiableWithinAt one_ne_zero).comp _ h _
      · ext y; simp only [mfld_simps]
      · intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1 }

Depends on / 依赖: DifferentiableWithinAtProp, I.continuous_symm.continuousAt, I.symm, ModelWithCorners, ModelWithCorners.left_inv, Set.inter_right_comm, Set.preimage_inter, Set.range, continuousAt, continuous_symm, differentiableWithinAt_inter, inter_right_comm, is_local, left_inv, mem_nhds, preimage_inter, right_invariance, u_open, u_open.mem_nhds
-/
theorem differentiableWithinAt_localInvariantProp :
    (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
      (DifferentiableWithinAtProp I I') :=
  { is_local := by
      intro s x u f u_open xu
      have : I.symm ⁻¹' (s inter u) inter Set.range I = I.symm ⁻¹' s inter Set.range I inter I.symm ⁻¹' u := by
        simp only [Set.inter_right_comm, Set.preimage_inter]
      rw [DifferentiableWithinAtProp]; rw [DifferentiableWithinAtProp]; rw [this]
      symm
      apply differentiableWithinAt_inter
      have : u in 𝓝 (I.symm (I x)) := by
        rw [ModelWithCorners.left_inv]
        exact u_open.mem_nhds xu
      apply I.continuous_symm.continuousAt this
    right_invariance' := by
      intro s x f e he hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
      rw [this] at h
      have : I (e x) in I.symm ⁻¹' e.target inter Set.range I := by simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he).2.contDiffWithinAt this
      convert! (h.comp' _ (this.differentiableWithinAt one_ne_zero)).mono_of_mem_nhdsWithin _
        using 1
      · ext y; simp only [mfld_simps]
      refine
        mem_nhdsWithin.mpr
          ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
            simp_rw [Set.mem_preimage, I.left_inv, e.mapsTo hx], ?_⟩
      mfld_set_tac
    congr_of_forall := by
      intro s x f g h hx hf
      apply hf.congr
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [h, hy, mfld_simps]
      · simp only [hx, mfld_simps]
    left_invariance' := by
      intro s x f e' he' hs hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have A : (I' ∘ f ∘ I.symm) (I x) in I'.symm ⁻¹' e'.source inter Set.range I' := by
        simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he').1.contDiffWithinAt A
      convert! (this.differentiableWithinAt one_ne_zero).comp _ h _
      · ext y; simp only [mfld_simps]
      · intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1 }

variable (I) in
/--
Definition of `UniqueMDiffWithinAt` / `UniqueMDiffWithinAt` 的定义

English:
definition UniqueMDiffWithinAt
  signature: (s : Set M) (x : M)
  body: UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s inter range I) ((extChartAt I x) x)

中文:
定义 UniqueMDiffWithinAt
  签名: (s : 集合 M) (x : M)
  定义体: UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s inter range I) ((extChartAt I x) x)

Depends on / 依赖: UniqueDiffWithinAt, extChartAt
-/
def UniqueMDiffWithinAt (s : Set M) (x : M) :=
  UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s inter range I) ((extChartAt I x) x)

variable (I) in
/--
Definition of `UniqueMDiffOn` / `UniqueMDiffOn` 的定义

English:
definition UniqueMDiffOn
  signature: (s : Set M)
  body: forall x in s, UniqueMDiffWithinAt I s x

中文:
定义 UniqueMDiffOn
  签名: (s : 集合 M)
  定义体: forall x in s, UniqueMDiffWithinAt I s x

Depends on / 依赖: UniqueMDiffWithinAt
-/
def UniqueMDiffOn (s : Set M) :=
  forall x in s, UniqueMDiffWithinAt I s x

variable (I I') in
/--
Definition of `MDifferentiableWithinAt` / `MDifferentiableWithinAt` 的定义

English:
definition MDifferentiableWithinAt
  signature: (f : M -> M') (s : Set M) (x : M)
  body: LiftPropWithinAt (DifferentiableWithinAtProp I I') f s x

中文:
定义 MDifferentiableWithinAt
  签名: (f : M -> M') (s : 集合 M) (x : M)
  定义体: LiftPropWithinAt (DifferentiableWithinAtProp I I') f s x

Depends on / 依赖: DifferentiableWithinAtProp, LiftPropWithinAt
-/
def MDifferentiableWithinAt (f : M -> M') (s : Set M) (x : M) :=
  LiftPropWithinAt (DifferentiableWithinAtProp I I') f s x

/--
theorem `mdifferentiableWithinAt_iff'` / 定理 `mdifferentiableWithinAt_iff'`

English:
theorem mdifferentiableWithinAt_iff'
  given: (f : M -> M') (s : Set M) (x : M)
  proof: by
  rw [MDifferentiableWithinAt]; rw [liftPropWithinAt_iff']; rfl

中文:
定理 mdifferentiableWithinAt_iff'
  条件: (f : M -> M') (s : 集合 M) (x : M)
  证明: by
  rw [MDifferentiableWithinAt]; rw [liftPropWithinAt_iff']; rfl

Depends on / 依赖: MDifferentiableWithinAt, liftPropWithinAt_iff
-/
theorem mdifferentiableWithinAt_iff' (f : M -> M') (s : Set M) (x : M) :
    MDifferentiableWithinAt I I' f s x ↔ ContinuousWithinAt f s x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
      ((extChartAt I x).symm ⁻¹' s inter range I) ((extChartAt I x) x) := by
  rw [MDifferentiableWithinAt]; rw [liftPropWithinAt_iff']; rfl

/--
theorem `MDifferentiableWithinAt.continuousWithinAt` / 定理 `MDifferentiableWithinAt.continuousWithinAt`

English:
theorem MDifferentiableWithinAt.continuousWithinAt
  statement: {f : M -> M'} {s : Set M} {x : M}
  proof: .1 .1 hf mdifferentiableWithinAt_iff' ..

中文:
定理 MDifferentiableWithinAt.continuousWithinAt
  结论: {f : M -> M'} {s : 集合 M} {x : M}
  证明: .1 .1 hf mdifferentiableWithinAt_iff' ..

Depends on / 依赖: mdifferentiableWithinAt_iff
-/
theorem MDifferentiableWithinAt.continuousWithinAt {f : M -> M'} {s : Set M} {x : M}
    (hf : MDifferentiableWithinAt I I' f s x) :
    ContinuousWithinAt f s x :=
.1 .1 hf mdifferentiableWithinAt_iff' ..

/--
theorem `MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt` / 定理 `MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt`

English:
theorem MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt
  proof: .2 .1 hf mdifferentiableWithinAt_iff' ..

中文:
定理 MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt
  证明: .2 .1 hf mdifferentiableWithinAt_iff' ..

Depends on / 依赖: mdifferentiableWithinAt_iff
-/
theorem MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt
    {f : M -> M'} {s : Set M} {x : M} (hf : MDifferentiableWithinAt I I' f s x) :
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
      ((extChartAt I x).symm ⁻¹' s inter range I) ((extChartAt I x) x) :=
.2 .1 hf mdifferentiableWithinAt_iff' ..

variable (I I') in
/--
Definition of `MDifferentiableAt` / `MDifferentiableAt` 的定义

English:
definition MDifferentiableAt
  signature: (f : M -> M') (x : M)
  body: LiftPropAt (DifferentiableWithinAtProp I I') f x

中文:
定义 MDifferentiableAt
  签名: (f : M -> M') (x : M)
  定义体: LiftPropAt (DifferentiableWithinAtProp I I') f x

Depends on / 依赖: DifferentiableWithinAtProp, LiftPropAt
-/
def MDifferentiableAt (f : M -> M') (x : M) :=
  LiftPropAt (DifferentiableWithinAtProp I I') f x

/--
theorem `mdifferentiableAt_iff` / 定理 `mdifferentiableAt_iff`

English:
theorem mdifferentiableAt_iff
  given: (f : M -> M') (x : M)
  proof: by
  rw [MDifferentiableAt]; rw [liftPropAt_iff]
  congrm _ ∧ ?_
  simp [DifferentiableWithinAtProp, Set.univ_inter, Function.comp_assoc]

中文:
定理 mdifferentiableAt_iff
  条件: (f : M -> M') (x : M)
  证明: by
  rw [MDifferentiableAt]; rw [liftPropAt_iff]
  congrm _ ∧ ?_
  simp [DifferentiableWithinAtProp, Set.univ_inter, Function.comp_assoc]

Depends on / 依赖: DifferentiableWithinAtProp, Function, Function.comp_assoc, MDifferentiableAt, Set.univ_inter, comp_assoc, congrm, liftPropAt_iff, univ_inter
-/
theorem mdifferentiableAt_iff (f : M -> M') (x : M) :
    MDifferentiableAt I I' f x ↔ ContinuousAt f x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x) := by
  rw [MDifferentiableAt]; rw [liftPropAt_iff]
  congrm _ ∧ ?_
  simp [DifferentiableWithinAtProp, Set.univ_inter, Function.comp_assoc]

/--
theorem `MDifferentiableAt.continuousAt` / 定理 `MDifferentiableAt.continuousAt`

English:
theorem MDifferentiableAt.continuousAt
  given: {f : M -> M'} {x : M} (hf : MDifferentiableAt I I' f x)
  proof: .1 .1 hf mdifferentiableAt_iff ..

中文:
定理 MDifferentiableAt.continuousAt
  条件: {f : M -> M'} {x : M} (hf : MDifferentiableAt I I' f x)
  证明: .1 .1 hf mdifferentiableAt_iff ..

Depends on / 依赖: mdifferentiableAt_iff
-/
theorem MDifferentiableAt.continuousAt {f : M -> M'} {x : M} (hf : MDifferentiableAt I I' f x) :
    ContinuousAt f x :=
.1 .1 hf mdifferentiableAt_iff ..

/--
theorem `MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt` / 定理 `MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt`

English:
theorem MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt
  statement: {f : M -> M'} {x : M}
  proof: .2 .1 hf mdifferentiableAt_iff ..

中文:
定理 MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt
  结论: {f : M -> M'} {x : M}
  证明: .2 .1 hf mdifferentiableAt_iff ..

Depends on / 依赖: mdifferentiableAt_iff
-/
theorem MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt {f : M -> M'} {x : M}
    (hf : MDifferentiableAt I I' f x) :
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x) :=
.2 .1 hf mdifferentiableAt_iff ..

variable (I I') in
/--
Definition of `MDifferentiableOn` / `MDifferentiableOn` 的定义

English:
definition MDifferentiableOn
  signature: (f : M -> M') (s : Set M)
  body: forall x in s, MDifferentiableWithinAt I I' f s x

中文:
定义 MDifferentiableOn
  签名: (f : M -> M') (s : 集合 M)
  定义体: forall x in s, MDifferentiableWithinAt I I' f s x

Depends on / 依赖: MDifferentiableWithinAt
-/
def MDifferentiableOn (f : M -> M') (s : Set M) :=
  forall x in s, MDifferentiableWithinAt I I' f s x

variable (I I') in
/--
Definition of `MDifferentiable` / `MDifferentiable` 的定义

English:
definition MDifferentiable
  signature: (f : M -> M')
  body: forall x, MDifferentiableAt I I' f x

中文:
定义 MDifferentiable
  签名: (f : M -> M')
  定义体: forall x, MDifferentiableAt I I' f x

Depends on / 依赖: MDifferentiableAt
-/
def MDifferentiable (f : M -> M') :=
  forall x, MDifferentiableAt I I' f x

variable (I I') in
/--
Definition of `OpenPartialHomeomorph.MDifferentiable` / `OpenPartialHomeomorph.MDifferentiable` 的定义

English:
definition OpenPartialHomeomorph.MDifferentiable
  signature: (f : OpenPartialHomeomorph M M')
  body: MDifferentiableOn I I' f f.source ∧ MDifferentiableOn I' I f.symm f.target

中文:
定义 OpenPartialHomeomorph.MDifferentiable
  签名: (f : OpenPartialHomeomorph M M')
  定义体: MDifferentiableOn I I' f f.source ∧ MDifferentiableOn I' I f.symm f.target

Depends on / 依赖: MDifferentiableOn, f.source, f.symm, f.target, source, target
-/
def OpenPartialHomeomorph.MDifferentiable (f : OpenPartialHomeomorph M M') :=
  MDifferentiableOn I I' f f.source ∧ MDifferentiableOn I' I f.symm f.target

variable (I I') in
/--
Definition of `HasMFDerivWithinAt` / `HasMFDerivWithinAt` 的定义

English:
definition HasMFDerivWithinAt
  signature: (f : M -> M') (s : Set M) (x : M)
  body: ContinuousWithinAt f s x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E -> E') f'
      ((extChartAt I x).symm ⁻¹' s inter range I) ((extChartAt I x) x)

中文:
定义 HasMFDerivWithinAt
  签名: (f : M -> M') (s : 集合 M) (x : M)
  定义体: ContinuousWithinAt f s x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E -> E') f'
      ((extChartAt I x).symm ⁻¹' s inter range I) ((extChartAt I x) x)

Depends on / 依赖: ContinuousWithinAt, HasFDerivWithinAt, extChartAt, writtenInExtChartAt
-/
def HasMFDerivWithinAt (f : M -> M') (s : Set M) (x : M)
    (f' : TangentSpace I x ->L[𝕜] TangentSpace I' (f x)) :=
  ContinuousWithinAt f s x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E -> E') f'
      ((extChartAt I x).symm ⁻¹' s inter range I) ((extChartAt I x) x)

variable (I I') in
/--
Definition of `HasMFDerivAt` / `HasMFDerivAt` 的定义

English:
definition HasMFDerivAt
  signature: (f : M -> M') (x : M) (f' : TangentSpace I x ->L[𝕜] TangentSpace I' (f x))
  body: ContinuousAt f x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E -> E') f' (range I) ((extChartAt I x) x)

中文:
定义 HasMFDerivAt
  签名: (f : M -> M') (x : M) (f' : TangentSpace I x ->L[𝕜] TangentSpace I' (f x))
  定义体: ContinuousAt f x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E -> E') f' (range I) ((extChartAt I x) x)

Depends on / 依赖: ContinuousAt, HasFDerivWithinAt, extChartAt, writtenInExtChartAt
-/
def HasMFDerivAt (f : M -> M') (x : M) (f' : TangentSpace I x ->L[𝕜] TangentSpace I' (f x)) :=
  ContinuousAt f x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E -> E') f' (range I) ((extChartAt I x) x)

open scoped Classical in
variable (I I') in
/--
Definition of `mfderivWithin` / `mfderivWithin` 的定义

English:
definition mfderivWithin
  signature: (f : M -> M') (s : Set M) (x : M)
  body: if MDifferentiableWithinAt I I' f s x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s inter range I)
        ((extChartAt I x) x) :
      _)
  else 0

中文:
定义 mfderivWithin
  签名: (f : M -> M') (s : 集合 M) (x : M)
  定义体: if MDifferentiableWithinAt I I' f s x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s inter range I)
        ((extChartAt I x) x) :
      _)
  else 0

Depends on / 依赖: MDifferentiableWithinAt, extChartAt, fderivWithin, writtenInExtChartAt
-/
def mfderivWithin (f : M -> M') (s : Set M) (x : M) : TangentSpace I x ->L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableWithinAt I I' f s x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s inter range I)
        ((extChartAt I x) x) :
      _)
  else 0

open scoped Classical in
variable (I I') in
/--
Definition of `mfderiv` / `mfderiv` 的定义

English:
definition mfderiv
  signature: (f : M -> M') (x : M)
  body: if MDifferentiableAt I I' f x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f : E -> E') (range I) ((extChartAt I x) x) :)
  else 0

中文:
定义 mfderiv
  签名: (f : M -> M') (x : M)
  定义体: if MDifferentiableAt I I' f x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f : E -> E') (range I) ((extChartAt I x) x) :)
  else 0

Depends on / 依赖: MDifferentiableAt, extChartAt, fderivWithin, writtenInExtChartAt
-/
def mfderiv (f : M -> M') (x : M) : TangentSpace I x ->L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableAt I I' f x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f : E -> E') (range I) ((extChartAt I x) x) :)
  else 0

variable (I I') in
/--
Definition of `tangentMapWithin` / `tangentMapWithin` 的定义

English:
definition tangentMapWithin
  signature: (f : M -> M') (s : Set M)
  body: fun p =>
  ⟨f p.1, (mfderivWithin I I' f s p.1 : TangentSpace I p.1 -> TangentSpace I' (f p.1)) p.2⟩

中文:
定义 tangentMapWithin
  签名: (f : M -> M') (s : 集合 M)
  定义体: fun p =>
  ⟨f p.1, (mfderivWithin I I' f s p.1 : TangentSpace I p.1 -> TangentSpace I' (f p.1)) p.2⟩
-/
def tangentMapWithin (f : M -> M') (s : Set M) : TangentBundle I M -> TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderivWithin I I' f s p.1 : TangentSpace I p.1 -> TangentSpace I' (f p.1)) p.2⟩

variable (I I') in
/--
Definition of `tangentMap` / `tangentMap` 的定义

English:
definition tangentMap
  signature: (f : M -> M')
  body: fun p =>
  ⟨f p.1, (mfderiv I I' f p.1 : TangentSpace I p.1 -> TangentSpace I' (f p.1)) p.2⟩

中文:
定义 tangentMap
  签名: (f : M -> M')
  定义体: fun p =>
  ⟨f p.1, (mfderiv I I' f p.1 : TangentSpace I p.1 -> TangentSpace I' (f p.1)) p.2⟩
-/
def tangentMap (f : M -> M') : TangentBundle I M -> TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderiv I I' f p.1 : TangentSpace I p.1 -> TangentSpace I' (f p.1)) p.2⟩

end DerivativesDefinitions
