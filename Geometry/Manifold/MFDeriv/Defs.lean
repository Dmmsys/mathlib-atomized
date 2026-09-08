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
/-- Property in the model space of a model with corners of being differentiable within a set at a
point, when read in the model vector space. This property will be lifted to manifolds to define
differentiable functions between manifolds. -/
/-
**DifferentiableWithinAtProp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DifferentiableWithinAtProp (f : H -> H') (s : Set H) (x : H) : Prop
参数：f : H -> H'；s : Set H；x : H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Property in the model space of a model with corners of being differentiable with
in a set at a
point, when read in the model vector space. This property will be lifted to mani
folds to define
differentiable functions between manifolds.
-/
def DifferentiableWithinAtProp (f : H → H') (s : Set H) (x : H) : Prop :=
  DifferentiableWithinAt 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ Set.range I) (I x)

open scoped Manifold
/-
**differentiableWithinAtProp_self_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAtProp_self_source {f : E -> H'} {s : Set E} {x : E} :
 DifferentiableWithinAtProp 𝓘(𝕜, E) I' f s x ↔ DifferentiableWithinAt 𝕜 (I' ∘ f)
 s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableWithinAtProp_self_source {f : E → H'} {s : Set E} {x : E} :
    DifferentiableWithinAtProp 𝓘(𝕜, E) I' f s x ↔ DifferentiableWithinAt 𝕜 (I' ∘ f) s x := by
  simp_rw [DifferentiableWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]
/-
**DifferentiableWithinAtProp_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAtProp_self {f : E -> E'} {s : Set E} {x : E} : Differ
entiableWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E') f s x ↔ DifferentiableWithinAt 𝕜 f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAtProp_self_source`：differentiableWithinAtProp_self_
source {f : E -> H'} {s : Set E} {x : E} : DifferentiableWithinAtProp 𝓘(𝕜, E) I'
 f s x ↔ DifferentiableWithi…
-/
theorem DifferentiableWithinAtProp_self {f : E → E'} {s : Set E} {x : E} :
    DifferentiableWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E') f s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  differentiableWithinAtProp_self_source
/-
**differentiableWithinAtProp_self_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAtProp_self_target {f : H -> E'} {s : Set H} {x : H} :
 DifferentiableWithinAtProp I 𝓘(𝕜, E') f s x ↔ DifferentiableWithinAt 𝕜 (f ∘ I.s
ymm) (I.symm ⁻¹' s inter range I) (I x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem differentiableWithinAtProp_self_target {f : H → E'} {s : Set H} {x : H} :
    DifferentiableWithinAtProp I 𝓘(𝕜, E') f s x ↔
      DifferentiableWithinAt 𝕜 (f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x) :=
  Iff.rfl

/-- Being differentiable in the model space is a local property, invariant under smooth maps.
Therefore, it will lift nicely to manifolds. -/
/-
**differentiableWithinAt_localInvariantProp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_localInvariantProp : (contDiffGroupoid 1 I).LocalIn
variantProp (contDiffGroupoid 1 I') (DifferentiableWithinAtProp I I')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_right_comm`：inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ inter s₂ 
inter s₃ = s₁ inter s₃ inter s₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableWithinAtProp.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `differentiableWithinAt_inter`：differentiableWithinAt_inter (ht : t in 𝓝 
x) : DifferentiableWithinAt 𝕜 f (s inter t) x ↔ DifferentiableWithinAt 𝕜 f s x
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ContDiffOn.contDiffWithinAt`：ContDiffOn.contDiffWithinAt (h : ContDiffOn
 𝕜 n f s) (hx : x in s) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_groupoid_of_pregroupoid`：mem_groupoid_of_pregroupoid {PG : Pregroupo
id H} {e : OpenPartialHomeomorph H H} : e in PG.groupoid ↔ PG.property e e.sourc
e ∧ PG.property e…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DifferentiableWithinAt.mono_of_mem_nhdsWithin`：DifferentiableWithinAt.mo
no_of_mem_nhdsWithin (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E} (hst : s i
n 𝓝[t] x) : DifferentiableWithinAt …
· 使用定理 `DifferentiableWithinAt.comp'`：DifferentiableWithinAt.comp' {g : F -> G} 
{t : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithin
At 𝕜 f s x) : Diff…
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Being differentiable in the model space is a local property, invariant under smo
oth maps.
Therefore, it will lift nicely to manifolds.
-/
theorem differentiableWithinAt_localInvariantProp :
    (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
      (DifferentiableWithinAtProp I I') :=
  { is_local := by
      intro s x u f u_open xu
      have : I.symm ⁻¹' (s ∩ u) ∩ Set.range I = I.symm ⁻¹' s ∩ Set.range I ∩ I.symm ⁻¹' u := by
        simp only [Set.inter_right_comm, Set.preimage_inter]
      rw [DifferentiableWithinAtProp, DifferentiableWithinAtProp, this]
      symm
      apply differentiableWithinAt_inter
      have : u ∈ 𝓝 (I.symm (I x)) := by
        rw [ModelWithCorners.left_inv]
        exact u_open.mem_nhds xu
      apply I.continuous_symm.continuousAt this
    right_invariance' := by
      intro s x f e he hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
      rw [this] at h
      have : I (e x) ∈ I.symm ⁻¹' e.target ∩ Set.range I := by simp only [hx, mfld_simps]
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
      have A : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ Set.range I' := by
        simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he').1.contDiffWithinAt A
      convert! (this.differentiableWithinAt one_ne_zero).comp _ h _
      · ext y; simp only [mfld_simps]
      · intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1 }

variable (I) in
/-- Predicate ensuring that, at a point and within a set, a function can have at most one
derivative. This is expressed using the preferred chart at the considered point. -/
/-
**UniqueMDiffWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniqueMDiffWithinAt (s : Set M) (x : M)
参数：s : Set M；x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate ensuring that, at a point and within a set, a function can have at mos
t one
derivative. This is expressed using the preferred chart at the considered point.
-/
def UniqueMDiffWithinAt (s : Set M) (x : M) :=
  UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)

variable (I) in
/-- Predicate ensuring that, at all points of a set, a function can have at most one derivative. -/
/-
**UniqueMDiffOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniqueMDiffOn (s : Set M)
参数：s : Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate ensuring that, at all points of a set, a function can have at most one
 derivative.
-/
def UniqueMDiffOn (s : Set M) :=
  ∀ x ∈ s, UniqueMDiffWithinAt I s x

variable (I I') in
/-- `MDifferentiableWithinAt I I' f s x` indicates that the function `f` between manifolds
has a derivative at the point `x` within the set `s`.
This is a generalization of `DifferentiableWithinAt` to manifolds.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differentiable, while
this would not mean anything relevant. -/
/-
**MDifferentiableWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt (f : M -> M') (s : Set M) (x : M)
参数：f : M -> M'；s : Set M；x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MDifferentiableWithinAt I I' f s x` indicates that the function `f` between man
ifolds
has a derivative at the point `x` within the set `s`.
This is a generalization of `DifferentiableWithinAt` to manifolds.

We require continuity in the definition, as otherwise points close to `x` in `s`
 could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything t
o the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differe
ntiable, while
this would not mean anything relevant.
-/
def MDifferentiableWithinAt (f : M → M') (s : Set M) (x : M) :=
  LiftPropWithinAt (DifferentiableWithinAtProp I I') f s x
/-
**mdifferentiableWithinAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_iff' (f : M -> M') (s : Set M) (x : M) : MDifferen
tiableWithinAt I I' f s x ↔ ContinuousWithinAt f s x ∧ DifferentiableWithinAt 𝕜 
(writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s inter range I) ((ext
ChartAt I x) x)
参数：f : M -> M'；s : Set M；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MDifferentiableWithinAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {H : Type u_…
· 使用定理 `ChartedSpace.liftPropWithinAt_iff'`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mdifferentiableWithinAt_iff' (f : M → M') (s : Set M) (x : M) :
    MDifferentiableWithinAt I I' f s x ↔ ContinuousWithinAt f s x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x) := by
  rw [MDifferentiableWithinAt, liftPropWithinAt_iff']; rfl
/-
**MDifferentiableWithinAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.continuousWithinAt {f : M -> M'} {s : Set M} {x : 
M} (hf : MDifferentiableWithinAt I I' f s x) : ContinuousWithinAt f s x
参数：hf : MDifferentiableWithinAt I I' f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableWithinAt_iff'`：mdifferentiableWithinAt_iff' (f : M -> M')
 (s : Set M) (x : M) : MDifferentiableWithinAt I I' f s x ↔ ContinuousWithinAt f
 s x ∧ Differentia…
-/
theorem MDifferentiableWithinAt.continuousWithinAt {f : M → M'} {s : Set M} {x : M}
    (hf : MDifferentiableWithinAt I I' f s x) :
    ContinuousWithinAt f s x :=
  mdifferentiableWithinAt_iff' .. |>.1 hf |>.1
/-
**MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt** 是 Mathlib
 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt {f : M 
-> M'} {s : Set M} {x : M} (hf : MDifferentiableWithinAt I I' f s x) : Different
iableWithinAt 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s inte
r range I) ((extChartAt I x) x)
参数：hf : MDifferentiableWithinAt I I' f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableWithinAt_iff'`：mdifferentiableWithinAt_iff' (f : M -> M')
 (s : Set M) (x : M) : MDifferentiableWithinAt I I' f s x ↔ ContinuousWithinAt f
 s x ∧ Differentia…
-/
theorem MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt
    {f : M → M'} {s : Set M} {x : M} (hf : MDifferentiableWithinAt I I' f s x) :
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x) :=
  mdifferentiableWithinAt_iff' .. |>.1 hf |>.2

variable (I I') in
/-- `MDifferentiableAt I I' f x` indicates that the function `f` between manifolds
has a derivative at the point `x`.
This is a generalization of `DifferentiableAt` to manifolds.

We require continuity in the definition, as otherwise points close to `x` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differentiable, while
this would not mean anything relevant. -/
/-
**MDifferentiableAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MDifferentiableAt (f : M -> M') (x : M)
参数：f : M -> M'；x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MDifferentiableAt I I' f x` indicates that the function `f` between manifolds
has a derivative at the point `x`.
This is a generalization of `DifferentiableAt` to manifolds.

We require continuity in the definition, as otherwise points close to `x` could 
be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything t
o the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differe
ntiable, while
this would not mean anything relevant.
-/
def MDifferentiableAt (f : M → M') (x : M) :=
  LiftPropAt (DifferentiableWithinAtProp I I') f x
/-
**mdifferentiableAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_iff (f : M -> M') (x : M) : MDifferentiableAt I I' f x ↔
 ContinuousAt f x ∧ DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (ran
ge I) ((extChartAt I x) x)
参数：f : M -> M'；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MDifferentiableAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{H : Type u_…
· 使用定理 `ChartedSpace.liftPropAt_iff`：liftPropAt_iff {P : (H -> H') -> Set H -> H
 -> Prop} {f : M -> M'} {x : M} : LiftPropAt P f x ↔ ContinuousAt f x ∧ P (chart
At H' (f x) ∘ f ∘…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mdifferentiableAt_iff (f : M → M') (x : M) :
    MDifferentiableAt I I' f x ↔ ContinuousAt f x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x) := by
  rw [MDifferentiableAt, liftPropAt_iff]
  congrm _ ∧ ?_
  simp [DifferentiableWithinAtProp, Set.univ_inter, Function.comp_assoc]
/-
**MDifferentiableAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.continuousAt {f : M -> M'} {x : M} (hf : MDifferentiable
At I I' f x) : ContinuousAt f x
参数：hf : MDifferentiableAt I I' f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableAt_iff`：mdifferentiableAt_iff (f : M -> M') (x : M) : MDi
fferentiableAt I I' f x ↔ ContinuousAt f x ∧ DifferentiableWithinAt 𝕜 (writtenIn
ExtChartAt …
-/
theorem MDifferentiableAt.continuousAt {f : M → M'} {x : M} (hf : MDifferentiableAt I I' f x) :
    ContinuousAt f x :=
  mdifferentiableAt_iff .. |>.1 hf |>.1
/-
**MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt {f : M -> M'}
 {x : M} (hf : MDifferentiableAt I I' f x) : DifferentiableWithinAt 𝕜 (writtenIn
ExtChartAt I I' x f) (range I) ((extChartAt I x) x)
参数：hf : MDifferentiableAt I I' f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableAt_iff`：mdifferentiableAt_iff (f : M -> M') (x : M) : MDi
fferentiableAt I I' f x ↔ ContinuousAt f x ∧ DifferentiableWithinAt 𝕜 (writtenIn
ExtChartAt …
-/
theorem MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt {f : M → M'} {x : M}
    (hf : MDifferentiableAt I I' f x) :
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x) :=
  mdifferentiableAt_iff .. |>.1 hf |>.2

variable (I I') in
/-- `MDifferentiableOn I I' f s` indicates that the function `f` between manifolds
has a derivative within `s` at all points of `s`.
This is a generalization of `DifferentiableOn` to manifolds. -/
/-
**MDifferentiableOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MDifferentiableOn (f : M -> M') (s : Set M)
参数：f : M -> M'；s : Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MDifferentiableOn I I' f s` indicates that the function `f` between manifolds
has a derivative within `s` at all points of `s`.
This is a generalization of `DifferentiableOn` to manifolds.
-/
def MDifferentiableOn (f : M → M') (s : Set M) :=
  ∀ x ∈ s, MDifferentiableWithinAt I I' f s x

variable (I I') in
/-- `MDifferentiable I I' f` indicates that the function `f` between manifolds
has a derivative everywhere.
This is a generalization of `Differentiable` to manifolds. -/
/-
**MDifferentiable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MDifferentiable (f : M -> M')
参数：f : M -> M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MDifferentiable I I' f` indicates that the function `f` between manifolds
has a derivative everywhere.
This is a generalization of `Differentiable` to manifolds.
-/
def MDifferentiable (f : M → M') :=
  ∀ x, MDifferentiableAt I I' f x

variable (I I') in
/-- Prop registering if an open partial homeomorphism is a local diffeomorphism on its source -/
/-
**OpenPartialHomeomorph.MDifferentiable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.MDifferentiable (f : OpenPartialHomeomorph M M')
参数：f : OpenPartialHomeomorph M M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prop registering if an open partial homeomorphism is a local diffeomorphism on i
ts source
-/
def OpenPartialHomeomorph.MDifferentiable (f : OpenPartialHomeomorph M M') :=
  MDifferentiableOn I I' f f.source ∧ MDifferentiableOn I' I f.symm f.target

variable (I I') in
/-- `HasMFDerivWithinAt I I' f s x f'` indicates that the function `f` between manifolds
has, at the point `x` and within the set `s`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

This is a generalization of `HasFDerivWithinAt` to manifolds (as indicated by the prefix `m`).
The order of arguments is changed as the type of the derivative `f'` depends on the choice of `x`.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differentiable, while
this would not mean anything relevant. -/
/-
**HasMFDerivWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt (f : M -> M') (s : Set M) (x : M) (f' : TangentSpace I 
x ->L[𝕜] TangentSpace I' (f x))
参数：f : M -> M'；s : Set M；x : M；f' : TangentSpace I x ->L[𝕜] TangentSpace I' (f x
)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasMFDerivWithinAt I I' f s x f'` indicates that the function `f` between manif
olds
has, at the point `x` and within the set `s`, the derivative `f'`. Here, `f'` is
 a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

This is a generalization of `HasFDerivWithinAt` to manifolds (as indicated by th
e prefix `m`).
The order of arguments is changed as the type of the derivative `f'` depends on 
the choice of `x`.

We require continuity in the definition, as otherwise points close to `x` in `s`
 could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything t
o the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differe
ntiable, while
this would not mean anything relevant.
-/
def HasMFDerivWithinAt (f : M → M') (s : Set M) (x : M)
    (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousWithinAt f s x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E → E') f'
      ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)

variable (I I') in
/-- `HasMFDerivAt I I' f x f'` indicates that the function `f` between manifolds
has, at the point `x`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differentiable, while
this would not mean anything relevant. -/
/-
**HasMFDerivAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasMFDerivAt (f : M -> M') (x : M) (f' : TangentSpace I x ->L[𝕜] TangentSp
ace I' (f x))
参数：f : M -> M'；x : M；f' : TangentSpace I x ->L[𝕜] TangentSpace I' (f x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasMFDerivAt I I' f x f'` indicates that the function `f` between manifolds
has, at the point `x`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

We require continuity in the definition, as otherwise points close to `x` in `s`
 could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything t
o the image points,
and in particular by coincidence `writtenInExtChartAt I I' x f` could be differe
ntiable, while
this would not mean anything relevant.
-/
def HasMFDerivAt (f : M → M') (x : M) (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousAt f x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E → E') f' (range I) ((extChartAt I x) x)

open scoped Classical in
variable (I I') in
/-- `mfderivWithin I I' f s x`, given a function `f` between two manifolds,
is the derivative of `f` at `x` within `s`,
as a continuous linear map from the tangent space at `x` to the tangent space at `f x`. -/
/-
**mfderivWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mfderivWithin (f : M -> M') (s : Set M) (x : M) : TangentSpace I x ->L[𝕜] 
TangentSpace I' (f x)
参数：f : M -> M'；s : Set M；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mfderivWithin I I' f s x`, given a function `f` between two manifolds,
is the derivative of `f` at `x` within `s`,
as a continuous linear map from the tangent space at `x` to the tangent space at
 `f x`.
-/
def mfderivWithin (f : M → M') (s : Set M) (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableWithinAt I I' f s x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) :
      _)
  else 0

open scoped Classical in
variable (I I') in
/-- `mfderiv I I' f x`, given a function `f` between two manifolds, is the derivative of `f` at `x`,
as a continuous linear map from the tangent space at `x` to the tangent space at `f x`. -/
/-
**mfderiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mfderiv (f : M -> M') (x : M) : TangentSpace I x ->L[𝕜] TangentSpace I' (f
 x)
参数：f : M -> M'；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mfderiv I I' f x`, given a function `f` between two manifolds, is the derivativ
e of `f` at `x`,
as a continuous linear map from the tangent space at `x` to the tangent space at
 `f x`.
-/
def mfderiv (f : M → M') (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableAt I I' f x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f : E → E') (range I) ((extChartAt I x) x) :)
  else 0

variable (I I') in
/-- `tangentMapWithin I I' f s` is the derivative of `f : M → M'` within a set `s`,
as a map between the tangent bundles `TM` and `TM'`. -/
/-
**tangentMapWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tangentMapWithin (f : M -> M') (s : Set M) : TangentBundle I M -> TangentB
undle I' M'
参数：f : M -> M'；s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`tangentMapWithin I I' f s` is the derivative of `f : M → M'` within a set `s`,
as a map between the tangent bundles `TM` and `TM'`.
-/
def tangentMapWithin (f : M → M') (s : Set M) : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderivWithin I I' f s p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩

variable (I I') in
/-- `tangentMap I I' f` is the derivative of `f : M → M'` as a map between the tangent bundles
`TM` and `TM'`. -/
/-
**tangentMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tangentMap (f : M -> M') : TangentBundle I M -> TangentBundle I' M'
参数：f : M -> M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`tangentMap I I' f` is the derivative of `f : M → M'` as a map between the tange
nt bundles
`TM` and `TM'`.
-/
def tangentMap (f : M → M') : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderiv I I' f p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩

end DerivativesDefinitions

