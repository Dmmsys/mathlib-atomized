/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM

/-!
# Distributions

Let `E` be a real **finite-dimensional normed space**, `Ω` an open subset of `E`,
and `F` a real **locally convex topological vector space**.

An **`F`-valued distribution on `Ω`** is a continuous `ℝ`-linear map `T : 𝓓(Ω, ℝ) →L[ℝ] F`,
defined on the space `𝓓(Ω, ℝ)` of real-valued test functions, and taking values in `F`.
In particular, if `𝕜` is an `RCLike` field, `𝓓'(Ω, 𝕜)` is the usual notion of real or complex
distribution on `Ω`.

We denote the space of `F`-valued distributions on `Ω` by `𝓓'(Ω, F)`. Topologically,
it is defined as `𝓓(Ω, ℝ) →L_c[ℝ] F`, meaning that we endow it with the topology of uniform
convergence on compact subsets of `𝓓(Ω, ℝ)`. In this particular case, this happens to coincide
with the topology of `𝓓(Ω, ℝ) →L[ℝ] F`, namely that of uniform convergence on bounded subsets.
See the implementation notes below for more details.

Right now, this file contains very few mathematical statements.
The theory will be expanded in future PRs.

## Main Declarations

* `𝓓'^{n}(Ω, F) = Distribution Ω F n` is the space of `F`-valued distributions on `Ω` with
  order at most `n`. See the implementation notes below for more information about the parameter
  `n : ℕ∞`; in most cases you want to use the space `𝓓'(Ω, F) = Distribution Ω F ⊤`.
* `Distribution.mapCLM`: any continuous linear map `A : F →L[ℝ] G` induces a continuous linear
  map `𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, G)`. On locally integrable functions, this corresponds to applying `A`
  pointwise.

## Notation

In the `Distributions` scope, we introduce the following notations:
* `𝓓'^{n}(Ω, F)`: the space of `F`-valued distributions on the open set `Ω` with order at most
  `n : ℕ∞`.
* `𝓓'(Ω, F)`: the space of `F`-valued distributions on the open set `Ω`, i.e `𝓓'^{⊤}(Ω, F)`.

Note that the parameter `n` here lives in `ℕ∞`, unlike the parameter for `ContDiff` which lives
in `WithTop ℕ∞` (to incorporate analytic functions). This means that we can't use the notation
`∞` introduced for `ContDiff` for our regularity, because it denotes an element of `WithTop ℕ∞`.
We could introduce another notation `∞` for `⊤ : ℕ∞`, but we believe it would be confusing.

## Implementation Notes

### `abbrev` or `def`

At this point in time, it is not clear whether we should enforce a separation between the API
for `𝓓'(Ω, F)` and the more generic API about `𝓓(Ω, ℝ) →L_c[ℝ] F`.
For now, we have made the "default" choice to implement `Distribution` as an `abbrev`, which means
that we get a lot of instances for free, but also that there is no such separation of APIs.

If this happens to be a bad decision, which will become clear while developing the theory,
do not hesitate to refactor to a `def` instead.

### Vector-valued distributions

The theory of vector-valued distributions is not as well-known as its scalar-valued analog. The
definition we choose is studied in
[L. Schwartz, *Théorie des distributions à valeurs vectorielles*][schwartz1957].

Let us give two examples of how we plan to use this level of generality:
* In the short term, this will allow us to define the *Fréchet derivative* of a distribution,
  as a continuous linear map `𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, E →L[ℝ] F)`. Note that, even if `F = ℝ`,
  the derivative is naturally vector-valued.
* On a longer timescale, we should aim to prove the
  [Schwartz Kernel Theorem](https://en.wikipedia.org/wiki/Schwartz_kernel_theorem), which is
  formulated nicely in terms of vector-valued distributions. Indeed, it says precisely that one
  can (algebraically, at least) identify the spaces `𝓓'(Ω₁ ×ˢ Ω₂, ℝ)` and `𝓓'(Ω₁, 𝓓'(Ω₂, ℝ))`.

### Choice of scalar field

In the literature, it is common to define complex-valued distributions as continuous `ℂ`-linear
forms `T : 𝓓(Ω, ℂ) →L[ℂ] ℂ`. We use `𝓓(Ω, ℝ) →L[ℝ] ℂ` instead, that is, we only ever test
against *real-valued* test functions.

This makes no difference mathematically, since `𝓓(Ω, ℂ)` is the complexification of `𝓓(Ω, ℝ)`,
hence there is a topological isomorphism between `𝓓(Ω, ℝ) →L[ℝ] F` and `𝓓(Ω, ℂ) →L[ℂ] F`
whenever `F` is a complex vector space.

We choose this definition because it avoids adding a base field as an extra parameter.
Instead, we use the generality of vector-valued distributions to our advantage: a complex-valued
distribution is nothing more than a distribution taking values in the real vector-space `ℂ`.

### Order of distributions

Based on established practice in the literature, a natural way to express the order of a
distribution would be to introduce a predicate `Distribution.HasOrderAtMost` on the space of all
distributions. Here though, we define a separate space `𝓓'^{n}(Ω, F)` whose elements are precisely
distributions of order at most `n`.

This is not incompatible with the predicate approach: in fact, we think that such a predicate
should eventually become the primary interface for the order of a distribution. However, we believe
that being able to talk about the space `𝓓'^{n}(Ω, F)` is also quite important, for the following
reasons:
* if `T : 𝓓'(Ω,F)` is a distribution whose order is at most `n`, it is natural to test it against
  a `C^n` test function (especially if `n = 0`). This means that we naturally want to consider its
  extension `T'` as an element of `𝓓'^{n}(Ω, F)`.
* it is often quite easy to keep track of the regularities while *defining* an operation on
  distributions (e. g. differentiation). On the other hand, once you have defined an operation on
  `𝓓'^(Ω, F)`, it can be quite painful to study its relation to order *a posteriori*.

Note that the topology on `𝓓'^{n}(Ω, F)` has no reason to be the subspace topology coming from
`𝓓'(Ω, F)`.

### Choice of topology

Our choice of the compact convergence topology on `𝓓'^{n}(Ω, F)` follows
[L. Schwartz, *Théorie des distributions à valeurs vectorielles*, §2, p. 49][schwartz1957].

Note that, since `𝓓(Ω, ℝ)` is a Montel space, the topology on `𝓓'(Ω, F)` is also that of
bounded convergence. Hence, our definition also agrees with
[L. Schwartz, *Théorie des distributions*, Chapitre III, §3][schwartz1950].

When `n` is finite, however, `𝓓^{n}(Ω, ℝ)` is no longer a Montel space
(see [L. Schwartz, *Théorie des distributions*, Chapitre III, §2, p. 71][schwartz1950]), hence
these two topologies have no reason to be the same. Schwartz uses compact convergence as a default
(see [L. Schwartz, *Théorie des distributions à valeurs vectorielles*, §2, p. 50][schwartz1957]),
which we follow here.

Finally, note that a **sequence** of distributions converges in `𝓓'(Ω, F)` if and only if it
converges pointwise
(see [L. Schwartz, *Théorie des distributions*, Chapitre III, §3, Théorème XIII][schwartz1950]).
Due to this fact, some texts endow `𝓓'(Ω, F)` with the pointwise convergence topology. While this
gives the same converging sequences as the topology of bounded/compact convergence, this is no
longer true for general filters.

## References

* [L. Schwartz, *Théorie des distributions*][schwartz1950]
* [L. Schwartz, *Théorie des distributions à valeurs vectorielles*][schwartz1957]

-/

@[expose] public section

open Set TopologicalSpace
open scoped Distributions CompactConvergenceCLM

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {Ω : Opens E}
  {F : Type*} [AddCommGroup F] [Module Real F] [TopologicalSpace F]
  {F' : Type*} [AddCommGroup F'] [Module Real F'] [TopologicalSpace F']
  {n k : Nat∞}

-- TODO: def or abbrev?
variable (Ω F n) in
/--
Definition of `Distribution` / `Distribution` 的定义

English:
abbreviation Distribution
  body: 𝓓^{n}(Ω, Real) ->L_c[Real] F

中文:
缩写 分布
  定义体: 𝓓^{n}(Ω, Real) ->L_c[Real] F
-/
abbrev Distribution := 𝓓^{n}(Ω, Real) ->L_c[Real] F

/-- We denote `𝓓'^{n}(Ω, F)` the space of `F`-valued distributions on `Ω` with order at most
`n : ℕ∞`. Note that using `𝓓'` is a bit abusive since this is no longer a dual space unless
`F = 𝕜`. -/
scoped[Distributions] notation "𝓓'^{" n "}(" Ω ", " F ")" => Distribution Ω F n

/-- We denote `𝓓'(Ω, F)` the space of `F`-valued distributions on `Ω`. Note that using `𝓓'`
is a bit abusive since this is no longer a dual space unless `F = 𝕜`. -/
scoped[Distributions] notation "𝓓'(" Ω ", " F ")" => Distribution Ω F ⊤

variable [IsTopologicalAddGroup F] [ContinuousSMul Real F]
variable [IsTopologicalAddGroup F'] [ContinuousSMul Real F']

namespace Distribution

section mapCLM
-- TODO: generalize this section to `𝕜` linear maps (or even semilinear maps)
-- by generalizing `ContinuousLinearMap.postcompCompactConvergenceCLM`

/--
Definition of `mapCLM` / `mapCLM` 的定义

English:
definition mapCLM
  signature: (A : F ->L[Real] F')
  body: A.postcompCompactConvergenceCLM _

@[simp]

中文:
定义 mapCLM
  签名: (A : F ->L[实数] F')
  定义体: A.postcompCompactConvergenceCLM _

@[simp]

Depends on / 依赖: A.postcompCompactConvergenceCLM, postcompCompactConvergenceCLM
-/
noncomputable def mapCLM (A : F ->L[Real] F') : 𝓓'^{n}(Ω, F) ->L[Real] 𝓓'^{n}(Ω, F') :=
  A.postcompCompactConvergenceCLM _

@[simp]
/--
lemma `mapCLM_apply` / 引理 `mapCLM_apply`

English:
lemma mapCLM_apply
  given: {A : F ->L[Real] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, Real)}
  proof: rfl

中文:
引理 mapCLM_apply
  条件: {A : F ->L[实数] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, 实数)}
  证明: rfl
-/
lemma mapCLM_apply {A : F ->L[Real] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, Real)} :
    mapCLM A T f = A (T f) := rfl

end mapCLM

section DiracDelta

/-- The Dirac delta distribution. This is zero if `x` does not belong to `Ω`. -/
@[wikidata Q209675]
/--
Definition of `delta` / `delta` 的定义

English:
definition delta
  signature: (x : E)
  body: f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const _

@[simp]

中文:
定义 delta
  签名: (x : E)
  定义体: f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const _

@[simp]
-/
noncomputable def delta (x : E) : 𝓓'^{n}(Ω, Real) where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const _

@[simp]
/--
theorem `delta_apply` / 定理 `delta_apply`

English:
theorem delta_apply
  given: (x : E) (f : 𝓓^{n}(Ω, Real))
  statement: delta x f = f x
  proof: by
  rfl

@[simp]

中文:
定理 delta_apply
  条件: (x : E) (f : 𝓓^{n}(Ω, 实数))
  结论: delta x f = f x
  证明: by
  rfl

@[simp]
-/
theorem delta_apply (x : E) (f : 𝓓^{n}(Ω, Real)) : delta x f = f x := by
  rfl

@[simp]
/--
theorem `delta_eq_zero_of_notMem` / 定理 `delta_eq_zero_of_notMem`

English:
theorem delta_eq_zero_of_notMem
  given: (x : E) (hx : x ∉ Ω)
  statement: (delta x : 𝓓'^{n}(Ω, Real)) = 0
  proof: by
  ext f
  change f x = 0
  have hx_support : x ∉ tsupport f := by
    intro hx_mem
    exact hx (f.tsupport_subset hx_mem)
  exact image_eq_zero_of_notMem_tsupport hx_support

中文:
定理 delta_eq_zero_of_notMem
  条件: (x : E) (hx : x ∉ Ω)
  结论: (delta x : 𝓓'^{n}(Ω, 实数)) = 0
  证明: by
  ext f
  change f x = 0
  have hx_support : x ∉ tsupport f := by
    intro hx_mem
    exact hx (f.tsupport_subset hx_mem)
  exact image_eq_zero_of_notMem_tsupport hx_support

Depends on / 依赖: f.tsupport_subset, hx_mem, hx_support, image_eq_zero_of_notMem_tsupport, tsupport, tsupport_subset
-/
theorem delta_eq_zero_of_notMem (x : E) (hx : x ∉ Ω) : (delta x : 𝓓'^{n}(Ω, Real)) = 0 := by
  ext f
  change f x = 0
  have hx_support : x ∉ tsupport f := by
    intro hx_mem
    exact hx (f.tsupport_subset hx_mem)
  exact image_eq_zero_of_notMem_tsupport hx_support

end DiracDelta

section LineDerivCLM
-- TODO: generalize this section to `𝕜` linearity
-- by generalizing `ContinuousLinearMap.precompCompactConvergenceCLM`

/--
Definition of `lineDerivCLM` / `lineDerivCLM` 的定义

English:
definition lineDerivCLM
  signature: (v : E)
  body: - (TestFunction.lineDerivCLM Real v).precompCompactConvergenceCLM _

中文:
定义 lineDerivCLM
  签名: (v : E)
  定义体: - (TestFunction.lineDerivCLM Real v).precompCompactConvergenceCLM _

Depends on / 依赖: TestFunction, TestFunction.lineDerivCLM, lineDerivCLM, precompCompactConvergenceCLM
-/
noncomputable def lineDerivCLM (v : E) :
    𝓓'^{k}(Ω, F) ->L[Real] 𝓓'^{n}(Ω, F) :=
  - (TestFunction.lineDerivCLM Real v).precompCompactConvergenceCLM _

/--
lemma `lineDerivCLM_apply` / 引理 `lineDerivCLM_apply`

English:
lemma lineDerivCLM_apply
  given: {v : E} {T : 𝓓'^{k}(Ω, F)} {f : 𝓓^{n}(Ω, Real)}
  proof: rfl

中文:
引理 lineDerivCLM_apply
  条件: {v : E} {T : 𝓓'^{k}(Ω, F)} {f : 𝓓^{n}(Ω, 实数)}
  证明: rfl
-/
lemma lineDerivCLM_apply {v : E} {T : 𝓓'^{k}(Ω, F)} {f : 𝓓^{n}(Ω, Real)} :
    lineDerivCLM v T f = - T (TestFunction.lineDerivCLM Real v f) :=
  rfl

/--
lemma `lineDerivCLM_add` / 引理 `lineDerivCLM_add`

English:
lemma lineDerivCLM_add
  given: {v₁ v₂ : E}
  proof: by
  ext T f
  simp [lineDerivCLM_apply, TestFunction.lineDerivCLM_add, neg_add, -neg_add_rev]

中文:
引理 lineDerivCLM_add
  条件: {v₁ v₂ : E}
  证明: by
  ext T f
  simp [lineDerivCLM_apply, TestFunction.lineDerivCLM_add, neg_add, -neg_add_rev]

Depends on / 依赖: TestFunction, TestFunction.lineDerivCLM_add, lineDerivCLM_add, lineDerivCLM_apply, neg_add, neg_add_rev
-/
lemma lineDerivCLM_add {v₁ v₂ : E} :
    (lineDerivCLM (v₁ + v₂) : 𝓓'^{k}(Ω, F) ->L[Real] 𝓓'^{n}(Ω, F)) =
      lineDerivCLM v₁ + lineDerivCLM v₂ := by
  ext T f
  simp [lineDerivCLM_apply, TestFunction.lineDerivCLM_add, neg_add, -neg_add_rev]

/--
lemma `lineDerivCLM_smul` / 引理 `lineDerivCLM_smul`

English:
lemma lineDerivCLM_smul
  given: {c : Real} {v : E}
  proof: by
  ext T f
  simp [lineDerivCLM_apply, TestFunction.lineDerivCLM_smul]

中文:
引理 lineDerivCLM_smul
  条件: {c : 实数} {v : E}
  证明: by
  ext T f
  simp [lineDerivCLM_apply, TestFunction.lineDerivCLM_smul]

Depends on / 依赖: TestFunction, TestFunction.lineDerivCLM_smul, lineDerivCLM_apply, lineDerivCLM_smul
-/
lemma lineDerivCLM_smul {c : Real} {v : E} :
    (lineDerivCLM (c • v) : 𝓓'^{k}(Ω, F) ->L[Real] 𝓓'^{n}(Ω, F)) =
      c • lineDerivCLM v := by
  ext T f
  simp [lineDerivCLM_apply, TestFunction.lineDerivCLM_smul]

open LineDeriv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F)
  body: lineDerivCLM v

中文:
实例 :
  签名: LineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F)
  定义体: lineDerivCLM v

Depends on / 依赖: lineDerivCLM
-/
noncomputable instance : LineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp v := lineDerivCLM v

variable (𝕜) in
/--
lemma `lineDerivOp_eq_lineDerivCLM` / 引理 `lineDerivOp_eq_lineDerivCLM`

English:
lemma lineDerivOp_eq_lineDerivCLM
  given: {v : E} {T : 𝓓'(Ω, F)}
  proof: rfl

@[simp]

中文:
引理 lineDerivOp_eq_lineDerivCLM
  条件: {v : E} {T : 𝓓'(Ω, F)}
  证明: rfl

@[simp]
-/
lemma lineDerivOp_eq_lineDerivCLM {v : E} {T : 𝓓'(Ω, F)} :
    ∂_{v} T = lineDerivCLM v T :=
  rfl

@[simp]
/--
theorem `lineDerivOp_apply_apply` / 定理 `lineDerivOp_apply_apply`

English:
theorem lineDerivOp_apply_apply
  given: (f : 𝓓'(Ω, F)) (g : 𝓓(Ω, Real)) (m : E)
  proof: by
  rw [map_neg]; rfl

中文:
定理 lineDerivOp_apply_apply
  条件: (f : 𝓓'(Ω, F)) (g : 𝓓(Ω, 实数)) (m : E)
  证明: by
  rw [map_neg]; rfl

Depends on / 依赖: map_neg
-/
theorem lineDerivOp_apply_apply (f : 𝓓'(Ω, F)) (g : 𝓓(Ω, Real)) (m : E) :
    ∂_{m} f g = f (- ∂_{m} g) := by
  rw [map_neg]; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivAdd E 𝓓'(Ω, F) 𝓓'(Ω, F)
  body: map_add (lineDerivCLM v)
  lineDerivOp_left_add _ _ T := congr($lineDerivCLM_add T)

中文:
实例 :
  签名: LineDerivAdd E 𝓓'(Ω, F) 𝓓'(Ω, F)
  定义体: map_add (lineDerivCLM v)
  lineDerivOp_left_add _ _ T := congr($lineDerivCLM_add T)

Depends on / 依赖: lineDerivCLM, map_add
-/
noncomputable instance : LineDerivAdd E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp_add v := map_add (lineDerivCLM v)
  lineDerivOp_left_add _ _ T := congr($lineDerivCLM_add T)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivSMul Real E 𝓓'(Ω, F) 𝓓'(Ω, F)
  body: map_smul (lineDerivCLM v)

中文:
实例 :
  签名: LineDerivSMul 实数 E 𝓓'(Ω, F) 𝓓'(Ω, F)
  定义体: map_smul (lineDerivCLM v)

Depends on / 依赖: lineDerivCLM, map_smul
-/
noncomputable instance : LineDerivSMul Real E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp_smul v := map_smul (lineDerivCLM v)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivLeftSMul Real E 𝓓'(Ω, F) 𝓓'(Ω, F)
  body: congr($lineDerivCLM_smul T)

中文:
实例 :
  签名: LineDerivLeftSMul 实数 E 𝓓'(Ω, F) 𝓓'(Ω, F)
  定义体: congr($lineDerivCLM_smul T)

Depends on / 依赖: lineDerivCLM_smul
-/
noncomputable instance : LineDerivLeftSMul Real E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp_left_smul _ _ T := congr($lineDerivCLM_smul T)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousLineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F)
  body: (lineDerivCLM v).continuous

中文:
实例 :
  签名: 余ntinuousLineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F)
  定义体: (lineDerivCLM v).continuous

Depends on / 依赖: continuous, lineDerivCLM
-/
noncomputable instance : ContinuousLineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  continuous_lineDerivOp v := (lineDerivCLM v).continuous

/--
lemma `lineDerivOpCLM_eq_lineDerivCLM` / 引理 `lineDerivOpCLM_eq_lineDerivCLM`

English:
lemma lineDerivOpCLM_eq_lineDerivCLM
  given: {v : E}
  proof: rfl

中文:
引理 lineDerivOpCLM_eq_lineDerivCLM
  条件: {v : E}
  证明: rfl
-/
lemma lineDerivOpCLM_eq_lineDerivCLM {v : E} :
    lineDerivOpCLM Real 𝓓'(Ω, F) v = lineDerivCLM v :=
  rfl

end LineDerivCLM

end Distribution
