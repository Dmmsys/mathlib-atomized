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
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {F' : Type*} [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  {n k : ℕ∞}

-- TODO: def or abbrev?
variable (Ω F n) in
/-- `𝓓'^{n}(Ω, F) = Distribution Ω F n` is the space of `F`-valued distributions on `Ω` with
order at most `n`.

In most cases you want to use the space `𝓓'(Ω, F) = Distribution Ω F ⊤`. -/
/-
**Distribution** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Distribution
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`𝓓'^{n}(Ω, F) = Distribution Ω F n` is the space of `F`-valued distributions on 
`Ω` with
order at most `n`.

In most cases you want to use the space `𝓓'(Ω, F) = Distribution Ω F ⊤`.
-/
abbrev Distribution := 𝓓^{n}(Ω, ℝ) →L_c[ℝ] F

/-- We denote `𝓓'^{n}(Ω, F)` the space of `F`-valued distributions on `Ω` with order at most
`n : ℕ∞`. Note that using `𝓓'` is a bit abusive since this is no longer a dual space unless
`F = 𝕜`. -/
scoped[Distributions] notation "𝓓'^{" n "}(" Ω ", " F ")" => Distribution Ω F n

/-- We denote `𝓓'(Ω, F)` the space of `F`-valued distributions on `Ω`. Note that using `𝓓'`
is a bit abusive since this is no longer a dual space unless `F = 𝕜`. -/
scoped[Distributions] notation "𝓓'(" Ω ", " F ")" => Distribution Ω F ⊤

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
variable [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F']

namespace Distribution

section mapCLM
-- TODO: generalize this section to `𝕜` linear maps (or even semilinear maps)
-- by generalizing `ContinuousLinearMap.postcompCompactConvergenceCLM`

/-- Any continuous linear map `A : F →L[ℝ] G` induces a continuous linear map
`𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, G)`. On locally integrable functions, this corresponds to applying `A`
pointwise. -/
/-
**Distribution.mapCLM** 是 Mathlib 中的一个定义，位于命名空间 `Distribution`。
形式化陈述：mapCLM (A : F ->L[Real] F') : 𝓓'^{n}(Ω, F) ->L[Real] 𝓓'^{n}(Ω, F')
参数：A : F ->L[Real] F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any continuous linear map `A : F →L[ℝ] G` induces a continuous linear map
`𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, G)`. On locally integrable functions, this corresponds to 
applying `A`
pointwise.
-/
noncomputable def mapCLM (A : F →L[ℝ] F') : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F') :=
  A.postcompCompactConvergenceCLM _

@[simp]
/-
**Distribution.mapCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `Distribution`。
形式化陈述：mapCLM_apply {A : F ->L[Real] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, Real)} 
: mapCLM A T f = A (T f)
参数：Ω, F；Ω, Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
lemma mapCLM_apply {A : F →L[ℝ] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} :
    mapCLM A T f = A (T f) := rfl

end mapCLM

section DiracDelta

/-- The Dirac delta distribution. This is zero if `x` does not belong to `Ω`. -/
@[wikidata Q209675]
/-
**Distribution.delta** 是 Mathlib 中的一个定义，位于命名空间 `Distribution`。
形式化陈述：delta (x : E) : 𝓓'^{n}(Ω, Real) where toFun f
参数：x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Dirac delta distribution. This is zero if `x` does not belong to `Ω`.
-/
noncomputable def delta (x : E) : 𝓓'^{n}(Ω, ℝ) where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const _

@[simp]
/-
**Distribution.delta_apply** 是 Mathlib 中的一个定理，位于命名空间 `Distribution`。
形式化陈述：delta_apply (x : E) (f : 𝓓^{n}(Ω, Real)) : delta x f = f x
参数：x : E；f : 𝓓^{n}(Ω, Real)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem delta_apply (x : E) (f : 𝓓^{n}(Ω, ℝ)) : delta x f = f x := by
  rfl

@[simp]
/-
**Distribution.delta_eq_zero_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Distribution`。
形式化陈述：delta_eq_zero_of_notMem (x : E) (hx : x ∉ Ω) : (delta x : 𝓓'^{n}(Ω, Real))
 = 0
参数：x : E；hx : x ∉ Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TestFunction.tsupport_subset`：∀ {E : Type u_3} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4}   
[inst_2 : NormedAd…
· 使用定理 `image_eq_zero_of_notMem_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst 
: Zero α] [inst_1 : TopologicalSpace X] {f : X → α} {x : X},   x ∉ tsupport f → 
f x = 0
-/
theorem delta_eq_zero_of_notMem (x : E) (hx : x ∉ Ω) : (delta x : 𝓓'^{n}(Ω, ℝ)) = 0 := by
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

/-- `lineDerivCLM 𝕜 v` is the continuous `𝕜`-linear-map sending a distribution
`T : 𝓓'^{k}_{K}(E, F)` to its derivative along the vector `v`, which is a
distribution in `𝓓^{n}_{K}(E, F)`. Because differentiating increases the order, this only makes
sense if `k + 1 ≤ n`, otherwise we define it as the zero map.

The parameters `n` and `k` are implicit as they can often be inferred from context, or
specified by a type ascription. For `n = k = ⊤`, we also provide instances of the `LineDeriv`
notation typeclass. -/
/-
**Distribution.lineDerivCLM** 是 Mathlib 中的一个定义，位于命名空间 `Distribution`。
形式化陈述：lineDerivCLM (v : E) : 𝓓'^{k}(Ω, F) ->L[Real] 𝓓'^{n}(Ω, F)
参数：v : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lineDerivCLM 𝕜 v` is the continuous `𝕜`-linear-map sending a distribution
`T : 𝓓'^{k}_{K}(E, F)` to its derivative along the vector `v`, which is a
distribution in `𝓓^{n}_{K}(E, F)`. Because differentiating increases the order, 
this only makes
sense if `k + 1 ≤ n`, otherwise we define it as the zero map.

The parameters `n` and `k` are implicit as they can often be inferred from conte
xt, or
specified by a type ascription. For `n = k = ⊤`, we also provide instances of th
e `LineDeriv`
notation typeclass.
-/
noncomputable def lineDerivCLM (v : E) :
    𝓓'^{k}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F) :=
  - (TestFunction.lineDerivCLM ℝ v).precompCompactConvergenceCLM _
/-
**Distribution.lineDerivCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `Distribution`。
形式化陈述：lineDerivCLM_apply {v : E} {T : 𝓓'^{k}(Ω, F)} {f : 𝓓^{n}(Ω, Real)} : lineD
erivCLM v T f = - T (TestFunction.lineDerivCLM Real v f)
参数：Ω, F；Ω, Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
lemma lineDerivCLM_apply {v : E} {T : 𝓓'^{k}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} :
    lineDerivCLM v T f = - T (TestFunction.lineDerivCLM ℝ v f) :=
  rfl
/-
**Distribution.lineDerivCLM_add** 是 Mathlib 中的一个引理，位于命名空间 `Distribution`。
形式化陈述：lineDerivCLM_add {v₁ v₂ : E} : (lineDerivCLM (v₁ + v₂) : 𝓓'^{k}(Ω, F) ->L[
Real] 𝓓'^{n}(Ω, F)) = lineDerivCLM v₁ + lineDerivCLM v₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TestFunction.instIsTopologicalAddGroup`：∀ {E : Type u_3} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Ty
pe u_4}   [inst_2 : NormedAd…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `TestFunction.lineDerivCLM_add`：lineDerivCLM_add {v₁ v₂ : E} : (lineDeriv
CLM 𝕜 (v₁ + v₂) : 𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{k}(Ω, F)) = lineDerivCLM 𝕜 v₁ + lineDeri
vCLM 𝕜 v₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `UniformConvergenceCLM.instIsAddApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} 
[inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3}
   (F : Type u_4) [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lineDerivCLM_add {v₁ v₂ : E} :
    (lineDerivCLM (v₁ + v₂) : 𝓓'^{k}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F)) =
      lineDerivCLM v₁ + lineDerivCLM v₂ := by
  ext T f
  simp [lineDerivCLM_apply, TestFunction.lineDerivCLM_add, neg_add, -neg_add_rev]
/-
**Distribution.lineDerivCLM_smul** 是 Mathlib 中的一个引理，位于命名空间 `Distribution`。
形式化陈述：lineDerivCLM_smul {c : Real} {v : E} : (lineDerivCLM (c • v) : 𝓓'^{k}(Ω, F
) ->L[Real] 𝓓'^{n}(Ω, F)) = c • lineDerivCLM v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `TestFunction.instIsScalarTower`：∀ {E : Type u_3} [inst : NormedAddCommGr
oup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type u_4} 
  [inst_2 : NormedAd…
· 使用定理 `TestFunction.instContinuousSMulReal`：∀ {E : Type u_3} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type 
u_4}   [inst_2 : NormedAd…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `TestFunction.lineDerivCLM_smul`：lineDerivCLM_smul {c : Real} {v : E} : (
lineDerivCLM 𝕜 (c • v) : 𝓓^{n}(Ω, F) ->L[𝕜] 𝓓^{k}(Ω, F)) = c • lineDerivCLM 𝕜 v
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `UniformConvergenceCLM.instIsSMulApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lineDerivCLM_smul {c : ℝ} {v : E} :
    (lineDerivCLM (c • v) : 𝓓'^{k}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F)) =
      c • lineDerivCLM v := by
  ext T f
  simp [lineDerivCLM_apply, TestFunction.lineDerivCLM_smul]

open LineDeriv

/-- Note: we cannot express the full generality of `lineDerivCLM` purely in terms of this typeclass,
because (by design) the target type `𝓓^{k}_{K}(E, F)` is not determined by the input type
`𝓓^{n}_{K}(E, F)`. -/
/-
**Distribution.** 是 Mathlib 中的一个实例，位于命名空间 `Distribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note: we cannot express the full generality of `lineDerivCLM` purely in terms of
 this typeclass,
because (by design) the target type `𝓓^{k}_{K}(E, F)` is not determined by the i
nput type
`𝓓^{n}_{K}(E, F)`.
-/
noncomputable instance : LineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp v := lineDerivCLM v

variable (𝕜) in
/-
**Distribution.lineDerivOp_eq_lineDerivCLM** 是 Mathlib 中的一个引理，位于命名空间 `Distributi
on`。
形式化陈述：lineDerivOp_eq_lineDerivCLM {v : E} {T : 𝓓'(Ω, F)} : ∂_{v} T = lineDerivCL
M v T
参数：Ω, F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lineDerivOp_eq_lineDerivCLM {v : E} {T : 𝓓'(Ω, F)} :
    ∂_{v} T = lineDerivCLM v T :=
  rfl

@[simp]
/-
**Distribution.lineDerivOp_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Distribution`。
形式化陈述：lineDerivOp_apply_apply (f : 𝓓'(Ω, F)) (g : 𝓓(Ω, Real)) (m : E) : ∂_{m} f 
g = f (- ∂_{m} g)
参数：f : 𝓓'(Ω, F)；g : 𝓓(Ω, Real)；m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem lineDerivOp_apply_apply (f : 𝓓'(Ω, F)) (g : 𝓓(Ω, ℝ)) (m : E) :
    ∂_{m} f g = f (- ∂_{m} g) := by
  rw [map_neg]; rfl
/-
**Distribution.** 是 Mathlib 中的一个实例，位于命名空间 `Distribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LineDerivAdd E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp_add v := map_add (lineDerivCLM v)
  lineDerivOp_left_add _ _ T := congr($lineDerivCLM_add T)
/-
**Distribution.** 是 Mathlib 中的一个实例，位于命名空间 `Distribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LineDerivSMul ℝ E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp_smul v := map_smul (lineDerivCLM v)
/-
**Distribution.** 是 Mathlib 中的一个实例，位于命名空间 `Distribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LineDerivLeftSMul ℝ E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp_left_smul _ _ T := congr($lineDerivCLM_smul T)
/-
**Distribution.** 是 Mathlib 中的一个实例，位于命名空间 `Distribution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ContinuousLineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  continuous_lineDerivOp v := (lineDerivCLM v).continuous
/-
**Distribution.lineDerivOpCLM_eq_lineDerivCLM** 是 Mathlib 中的一个引理，位于命名空间 `Distrib
ution`。
形式化陈述：lineDerivOpCLM_eq_lineDerivCLM {v : E} : lineDerivOpCLM Real 𝓓'(Ω, F) v = 
lineDerivCLM v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Distribution.instLineDerivAddTopENat`：∀ {E : Type u_1} [inst : NormedAdd
CommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F : Type
 u_2}   [inst_2 : AddCommG…
· 使用定理 `Distribution.instLineDerivSMulRealTopENat`：∀ {E : Type u_1} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F :
 Type u_2}   [inst_2 : AddCommG…
· 使用定理 `Distribution.instContinuousLineDerivTopENat`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {Ω : TopologicalSpace.Opens E} {F
 : Type u_2}   [inst_2 : AddCommG…
-/
lemma lineDerivOpCLM_eq_lineDerivCLM {v : E} :
    lineDerivOpCLM ℝ 𝓓'(Ω, F) v = lineDerivCLM v :=
  rfl

end LineDerivCLM

end Distribution

