/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Luigi Massacci
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuously differentiable functions supported in a given compact set

This file develops the basic theory of bundled `n`-times continuously differentiable functions
with support contained in a given compact set.

Given `n : ℕ∞` and a compact subset `K` of a normed space `E`, we consider the type of bundled
functions `f : E → F` (where `F` is a normed vector space) such that:

- `f` is `n`-times continuously differentiable: `ContDiff ℝ n f`.
- `f` vanishes outside of a compact set: `EqOn f 0 Kᶜ`.

The main reason this exists as a bundled type is to be endowed with its natural locally convex
topology (namely, uniform convergence of `f` and its derivatives up to order `n`).
Taking the locally convex inductive limit of these as `K` varies yields the natural topology on test
functions, used to define distributions. While most of distribution theory cares only about `C^∞`
functions, we also want to endow the space of `C^n` test functions with its natural topology.
Indeed, distributions of order less than `n` are precisely those which extend continuously to this
larger space of test functions.

## Main definitions

- `ContDiffMapSupportedIn E F n K`: the type of bundled `n`-times continuously differentiable
  functions `E → F` which vanish outside of `K`.
- `ContDiffMapSupportedIn.iteratedFDerivLM`: wrapper, as a `𝕜`-linear map, for
  `iteratedFDeriv` from `ContDiffMapSupportedIn E F n K` to
  `ContDiffMapSupportedIn E (E [×i]→L[ℝ] F) k K`.
- `ContDiffMapSupportedIn.topologicalSpace`, `ContDiffMapSupportedIn.uniformSpace`: the topology
  and uniform structures on `𝓓^{n}_{K}(E, F)`, given by uniform convergence of the functions and
  all their derivatives up to order `n`.

## Main statements

- `ContDiffMapSupportedIn.isTopologicalAddGroup`, `ContDiffMapSupportedIn.continuousSMul` and
  `ContDiffMapSupportedIn.instLocallyConvexSpace`: `𝓓^{n}_{K}(E, F)` is a locally convex
  topological vector space.

## Notation

In the `Distributions` scope, we introduce the following notations:
- `𝓓^{n}_{K}(E, F)`: the space of `n`-times continuously differentiable functions `E → F`
  which vanish outside of `K`.
- `𝓓_{K}(E, F)`: the space of smooth (infinitely differentiable) functions `E → F`
  which vanish outside of `K`, i.e. `𝓓^{⊤}_{K}(E, F)`.
- `N[𝕜; F]_{K, n, i}` (or simply `N[𝕜]_{K, n, i}`): the `𝕜`-seminorm on `𝓓^{n}_{K}(E, F)`
  given by the sup-norm of the `i`-th derivative.
- `N[𝕜; F]_{K, i}` (or simply `N[𝕜]_{K, i}`): the `𝕜`-seminorm on `𝓓_{K}(E, F)`
  given by the sup-norm of the `i`-th derivative.

## Implementation details

* The technical choice of spelling `EqOn f 0 Kᶜ` in the definition, as opposed to `tsupport f ⊆ K`
  is to make rewriting `f x` to `0` easier when `x ∉ K`.
* Having the parameter `n` (instead of just using smooth functions) is useful because
  it allows us to track the regularity of our operations, which will tell us how the order
  of a distribution behaves under the transpose of said operation. For example, the fact
  that differentiation of test functions *decreases* regularity by (at most) one will imply that
  differentiation of distributions *increases* their order by (at most) one. This comes
  with the downside of many regularity parameters; we considered specializing all the
  definitions to the (most common) smooth case, but we believe it is better to wait and see
  what is more practical to use later on.
* In `iteratedFDerivLM`, we define the `i`-th iterated differentiation operator as
  a map from `𝓓^{n}_{K}` to `𝓓^{k}_{K}` without imposing relations on `n`, `k` and `i`. Of course
  this is defined as `0` if `k + i > n`. This creates some verbosity as all of these variables are
  explicit, but it allows the most flexibility while avoiding DTT hell.

## Tags

distributions
-/

@[expose] public section

open TopologicalSpace Set Function UniformSpace WithSeminorms
open scoped BoundedContinuousFunction Topology NNReal ContDiff

variable (𝕜 E F F' : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] [NormedSpace 𝕜 F] [SMulCommClass Real 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace Real F'] [NormedSpace 𝕜 F'] [SMulCommClass Real 𝕜 F']
  {n n₁ n₂ k : Nat∞} {K K₁ K₂ : Compacts E}

/--
Definition of `ContDiffMapSupportedIn` / `ContDiffMapSupportedIn` 的定义

English:
structure ContDiffMapSupportedIn
  parameters: (n : Nat∞) (K : Compacts E)
  axioms and operations (3):
    - toFun : E -> F
    - contDiff' : ContDiff Real n toFun
    - zero_on_compl' : EqOn toFun 0 Kᶜ

中文:
结构 余ntDiffMapSupportedIn
  参数: (n : 自然数∞) (K : 余mpacts E)
  公理与运算 (3 个):
    - toFun : E -> F
    - contDiff' : 连续可微 实数 n toFun
    - zero_on_compl' : EqOn toFun 0 Kᶜ
-/
structure ContDiffMapSupportedIn (n : Nat∞) (K : Compacts E) : Type _ where
  /-- The underlying function. Use coercion instead. -/
  protected toFun : E -> F
  protected contDiff' : ContDiff Real n toFun
  protected zero_on_compl' : EqOn toFun 0 Kᶜ

/-- Notation for the space of bundled `n`-times continuously differentiable
functions with support in a compact set `K`. -/
scoped[Distributions] notation "𝓓^{" n "}_{" K "}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F n K

/-- Notation for the space of bundled smooth (infinitely differentiable)
functions with support in a compact set `K`. -/
scoped[Distributions] notation "𝓓_{" K "}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F ⊤ K

open Distributions

/--
Definition of `ContDiffMapSupportedInClass` / `ContDiffMapSupportedInClass` 的定义

English:
class ContDiffMapSupportedInClass
  parameters: (B : Type*) (E F : outParam <| Type*)
  extends: FunLike B E F
  axioms and operations (2):
    - map_contDiff((f : B)) : ContDiff Real n f
    - map_zero_on_compl((f : B)) : EqOn f 0 Kᶜ

中文:
类 余ntDiffMapSupportedIn类
  参数: (B : 类型) (E F : outParam <| 类型)
  继承: 函数状 B E F
  公理与运算 (2 个):
    - map_contDiff((f : B)) : 连续可微 实数 n f
    - map_zero_on_compl((f : B)) : EqOn f 0 Kᶜ
-/
class ContDiffMapSupportedInClass (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F]
    (n : outParam Nat∞) (K : outParam <| Compacts E)
    extends FunLike B E F where
  map_contDiff (f : B) : ContDiff Real n f
  map_zero_on_compl (f : B) : EqOn f 0 Kᶜ

open ContDiffMapSupportedInClass

namespace ContDiffMapSupportedInClass

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F]
    (n : outParam Nat∞) (K : outParam <| Compacts E)
    [ContDiffMapSupportedInClass B E F n K] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F]
    (n : outParam Nat∞) (K : outParam <| Compacts E)
    [ContDiffMapSupportedInClass B E F n K] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    have := HasCompactSupport.intro K.isCompact (map_zero_on_compl f)
    rcases (map_continuous f).bounded_above_of_compact_support this with ⟨C, hC⟩
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)

end ContDiffMapSupportedInClass

namespace ContDiffMapSupportedIn

/--
Instance `toContDiffMapSupportedInClass` / 实例 `toContDiffMapSupportedInClass`

English:
instance toContDiffMapSupportedInClass
  signature: :
  body: f.toFun
  coe_injective f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_zero_on_compl f := f.zero_on_compl'

中文:
实例 toContDiffMapSupportedInClass
  签名: :
  定义体: f.toFun
  coe_injective f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_zero_on_compl f := f.zero_on_compl'

Depends on / 依赖: f.toFun
-/
instance toContDiffMapSupportedInClass :
    ContDiffMapSupportedInClass 𝓓^{n}_{K}(E, F) E F n K where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_zero_on_compl f := f.zero_on_compl'

variable {E F F'}

/--
theorem `contDiff` / 定理 `contDiff`

English:
theorem contDiff
  given: (f : 𝓓^{n}_{K}(E, F))
  statement: ContDiff Real n f
  proof: map_contDiff f

中文:
定理 contDiff
  条件: (f : 𝓓^{n}_{K}(E, F))
  结论: 连续可微 实数 n f
  证明: map_contDiff f
-/
protected theorem contDiff (f : 𝓓^{n}_{K}(E, F)) : ContDiff Real n f := map_contDiff f
/--
theorem `zero_on_compl` / 定理 `zero_on_compl`

English:
theorem zero_on_compl
  given: (f : 𝓓^{n}_{K}(E, F))
  statement: EqOn f 0 Kᶜ
  proof: map_zero_on_compl f

中文:
定理 zero_on_compl
  条件: (f : 𝓓^{n}_{K}(E, F))
  结论: EqOn f 0 Kᶜ
  证明: map_zero_on_compl f
-/
protected theorem zero_on_compl (f : 𝓓^{n}_{K}(E, F)) : EqOn f 0 Kᶜ := map_zero_on_compl f
/--
theorem `compact_supp` / 定理 `compact_supp`

English:
theorem compact_supp
  given: (f : 𝓓^{n}_{K}(E, F))
  statement: HasCompactSupport f
  proof: .intro K.isCompact (map_zero_on_compl f)

@[simp]

中文:
定理 compact_supp
  条件: (f : 𝓓^{n}_{K}(E, F))
  结论: HasCompactSupport f
  证明: .intro K.isCompact (map_zero_on_compl f)

@[simp]
-/
protected theorem compact_supp (f : 𝓓^{n}_{K}(E, F)) : HasCompactSupport f :=
  .intro K.isCompact (map_zero_on_compl f)

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : 𝓓^{n}_{K}(E, F)}
  statement: f.toFun = (f : E -> F)
  proof: rfl

中文:
定理 toFun_eq_coe
  条件: {f : 𝓓^{n}_{K}(E, F)}
  结论: f.toFun = (f : E -> F)
  证明: rfl
-/
theorem toFun_eq_coe {f : 𝓓^{n}_{K}(E, F)} : f.toFun = (f : E -> F) :=
  rfl

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (f : 𝓓^{n}_{K}(E, F))
  body: f

initialize_simps_projections ContDiffMapSupportedIn (toFun -> coe, as_prefix coe)

@[ext]

中文:
定义 Simps.coe
  签名: (f : 𝓓^{n}_{K}(E, F))
  定义体: f

initialize_simps_projections ContDiffMapSupportedIn (toFun -> coe, as_prefix coe)

@[ext]
-/
def Simps.coe (f : 𝓓^{n}_{K}(E, F)) : E -> F := f

initialize_simps_projections ContDiffMapSupportedIn (toFun -> coe, as_prefix coe)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : 𝓓^{n}_{K}(E, F)} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : 𝓓^{n}_{K}(E, F)} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : 𝓓^{n}_{K}(E, F)} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : 𝓓^{n}_{K}(E, F)) (f' : E -> F) (h : f' = f)
  body: f'
  contDiff' := h.symm ▸ f.contDiff
  zero_on_compl' := h.symm ▸ f.zero_on_compl

@[simp]

中文:
定义 copy
  签名: (f : 𝓓^{n}_{K}(E, F)) (f' : E -> F) (h : f' = f)
  定义体: f'
  contDiff' := h.symm ▸ f.contDiff
  zero_on_compl' := h.symm ▸ f.zero_on_compl

@[simp]
-/
protected def copy (f : 𝓓^{n}_{K}(E, F)) (f' : E -> F) (h : f' = f) : 𝓓^{n}_{K}(E, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  zero_on_compl' := h.symm ▸ f.zero_on_compl

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : 𝓓^{n}_{K}(E, F)) (f' : E -> F) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : 𝓓^{n}_{K}(E, F)) (f' : E -> F) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : 𝓓^{n}_{K}(E, F)) (f' : E -> F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : 𝓓^{n}_{K}(E, F)) (f' : E -> F) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

@[simp]

中文:
定理 copy_eq
  条件: (f : 𝓓^{n}_{K}(E, F)) (f' : E -> F) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : 𝓓^{n}_{K}(E, F)) (f' : E -> F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/--
theorem `coe_toBoundedContinuousFunction` / 定理 `coe_toBoundedContinuousFunction`

English:
theorem coe_toBoundedContinuousFunction
  given: (f : 𝓓^{n}_{K}(E, F))
  proof: rfl

中文:
定理 coe_toBoundedContinuousFunction
  条件: (f : 𝓓^{n}_{K}(E, F))
  证明: rfl
-/
theorem coe_toBoundedContinuousFunction (f : 𝓓^{n}_{K}(E, F)) :
    (f : BoundedContinuousFunction E F) = (f : E -> F) := rfl

section AddCommGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero 𝓓^{n}_{K}(E, F)
  body: .mk 0 contDiff_zero_fun fun _ _ => rfl

中文:
实例 :
  签名: 零 𝓓^{n}_{K}(E, F)
  定义体: .mk 0 contDiff_zero_fun fun _ _ => rfl

Depends on / 依赖: contDiff_zero_fun
-/
instance : Zero 𝓓^{n}_{K}(E, F) where
  zero := .mk 0 contDiff_zero_fun fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply 𝓓^{n}_{K}(E, F) E F
  body: rfl

@[deprecated (since := "2026-06-15")] alias coe_zero := FunLike.coe_zero

中文:
实例 :
  签名: 是ZeroApply 𝓓^{n}_{K}(E, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-15")] alias coe_zero := FunLike.coe_zero
-/
instance : IsZeroApply 𝓓^{n}_{K}(E, F) E F where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_zero := FunLike.coe_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add 𝓓^{n}_{K}(E, F)
  body: .mk (f + g) (f.contDiff.add g.contDiff) by
    rw [← add_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

中文:
实例 :
  签名: 加法 𝓓^{n}_{K}(E, F)
  定义体: .mk (f + g) (f.contDiff.add g.contDiff) by
    rw [← add_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

Depends on / 依赖: add_zero, contDiff, f.contDiff.add, f.zero_on_compl.comp_left, g.contDiff, g.zero_on_compl, zero_on_compl
-/
instance : Add 𝓓^{n}_{K}(E, F) where
add f g := .mk (f + g) (f.contDiff.add g.contDiff) by
    rw [← add_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply 𝓓^{n}_{K}(E, F) E F
  body: rfl

@[deprecated (since := "2026-06-15")] alias coe_add := FunLike.coe_add

中文:
实例 :
  签名: 是加法Apply 𝓓^{n}_{K}(E, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-15")] alias coe_add := FunLike.coe_add
-/
instance : IsAddApply 𝓓^{n}_{K}(E, F) E F where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_add := FunLike.coe_add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg 𝓓^{n}_{K}(E, F)
  body: .mk (-f) (f.contDiff.neg) by
    rw [← neg_zero]
    exact f.zero_on_compl.comp_left

中文:
实例 :
  签名: 取负 𝓓^{n}_{K}(E, F)
  定义体: .mk (-f) (f.contDiff.neg) by
    rw [← neg_zero]
    exact f.zero_on_compl.comp_left

Depends on / 依赖: comp_left, contDiff, f.contDiff.neg, f.zero_on_compl.comp_left, neg_zero, zero_on_compl
-/
instance : Neg 𝓓^{n}_{K}(E, F) where
neg f := .mk (-f) (f.contDiff.neg) by
    rw [← neg_zero]
    exact f.zero_on_compl.comp_left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNegApply 𝓓^{n}_{K}(E, F) E F
  body: rfl

@[deprecated (since := "2026-06-15")] alias coe_neg := FunLike.coe_neg

中文:
实例 :
  签名: 是NegApply 𝓓^{n}_{K}(E, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-15")] alias coe_neg := FunLike.coe_neg
-/
instance : IsNegApply 𝓓^{n}_{K}(E, F) E F where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_neg := FunLike.coe_neg

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub 𝓓^{n}_{K}(E, F) where
  body: .mk (f - g) (f.contDiff.sub g.contDiff) by
    rw [← sub_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

中文:
实例 instSub
  签名: : 减法 𝓓^{n}_{K}(E, F) where
  定义体: .mk (f - g) (f.contDiff.sub g.contDiff) by
    rw [← sub_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

Depends on / 依赖: contDiff, f.contDiff.sub, f.zero_on_compl.comp_left, g.contDiff, g.zero_on_compl, sub_zero, zero_on_compl
-/
instance instSub : Sub 𝓓^{n}_{K}(E, F) where
sub f g := .mk (f - g) (f.contDiff.sub g.contDiff) by
    rw [← sub_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSubApply 𝓓^{n}_{K}(E, F) E F
  body: rfl

@[deprecated (since := "2026-06-15")] alias coe_sub := FunLike.coe_sub

中文:
实例 :
  签名: 是SubApply 𝓓^{n}_{K}(E, F) E F
  定义体: rfl

@[deprecated (since := "2026-06-15")] alias coe_sub := FunLike.coe_sub
-/
instance : IsSubApply 𝓓^{n}_{K}(E, F) E F where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_sub := FunLike.coe_sub

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: {R} [Semiring R] [Module R F] [SMulCommClass Real R F] [ContinuousConstSMul R F]
  body: .mk (c • (f : E -> F)) (f.contDiff.const_smul c) by
    rw [← smul_zero c]
    exact f.zero_on_compl.comp_left

中文:
实例 instSMul
  签名: {R} [半环 R] [模 R F] [标量交换类 实数 R F] [连续常数标量乘法 R F]
  定义体: .mk (c • (f : E -> F)) (f.contDiff.const_smul c) by
    rw [← smul_zero c]
    exact f.zero_on_compl.comp_left

Depends on / 依赖: comp_left, const_smul, contDiff, f.contDiff.const_smul, f.zero_on_compl.comp_left, smul_zero, zero_on_compl
-/
instance instSMul {R} [Semiring R] [Module R F] [SMulCommClass Real R F] [ContinuousConstSMul R F] :
    SMul R 𝓓^{n}_{K}(E, F) where
smul c f := .mk (c • (f : E -> F)) (f.contDiff.const_smul c) by
    rw [← smul_zero c]
    exact f.zero_on_compl.comp_left

instance {R} [Semiring R] [Module R F] [SMulCommClass Real R F] [ContinuousConstSMul R F] :
    IsSMulApply R 𝓓^{n}_{K}(E, F) E F where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_smul := FunLike.coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup 𝓓^{n}_{K}(E, F)
  body: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-15")] alias coeHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coe_coeHom := FunLike.coe_coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coeHom_injective := FunLike.coeAddMonoidHom_injective

中文:
实例 :
  签名: 加法交换群 𝓓^{n}_{K}(E, F)
  定义体: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-15")] alias coeHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coe_coeHom := FunLike.coe_coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coeHom_injective := FunLike.coeAddMonoidHom_injective

Depends on / 依赖: FunLike, FunLike.addCommGroup, addCommGroup, fast_instance
-/
instance : AddCommGroup 𝓓^{n}_{K}(E, F) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-15")] alias coeHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coe_coeHom := FunLike.coe_coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coeHom_injective := FunLike.coeAddMonoidHom_injective

end AddCommGroup

section Module

instance {R} [Semiring R] [Module R F] [SMulCommClass Real R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}_{K}(E, F) := fast_instance% FunLike.module

end Module

/--
theorem `support_subset` / 定理 `support_subset`

English:
theorem support_subset
  given: (f : 𝓓^{n}_{K}(E, F))
  statement: support f subseteq K
  proof: support_subset_iff'.mpr f.zero_on_compl

中文:
定理 support_subset
  条件: (f : 𝓓^{n}_{K}(E, F))
  结论: support f subseteq K
  证明: support_subset_iff'.mpr f.zero_on_compl
-/
protected theorem support_subset (f : 𝓓^{n}_{K}(E, F)) : support f subseteq K :=
  support_subset_iff'.mpr f.zero_on_compl

/--
theorem `tsupport_subset` / 定理 `tsupport_subset`

English:
theorem tsupport_subset
  given: (f : 𝓓^{n}_{K}(E, F))
  statement: tsupport f subseteq K
  proof: closure_minimal f.support_subset K.isCompact.isClosed

中文:
定理 tsupport_subset
  条件: (f : 𝓓^{n}_{K}(E, F))
  结论: tsupport f subseteq K
  证明: closure_minimal f.support_subset K.isCompact.isClosed
-/
protected theorem tsupport_subset (f : 𝓓^{n}_{K}(E, F)) : tsupport f subseteq K :=
  closure_minimal f.support_subset K.isCompact.isClosed

/--
theorem `hasCompactSupport` / 定理 `hasCompactSupport`

English:
theorem hasCompactSupport
  given: (f : 𝓓^{n}_{K}(E, F))
  statement: HasCompactSupport f
  proof: HasCompactSupport.intro K.isCompact f.zero_on_compl

@[fun_prop]

中文:
定理 hasCompactSupport
  条件: (f : 𝓓^{n}_{K}(E, F))
  结论: HasCompactSupport f
  证明: HasCompactSupport.intro K.isCompact f.zero_on_compl

@[fun_prop]
-/
protected theorem hasCompactSupport (f : 𝓓^{n}_{K}(E, F)) : HasCompactSupport f :=
  HasCompactSupport.intro K.isCompact f.zero_on_compl

@[fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (f : 𝓓^{n}_{K}(E, F))
  statement: Continuous f
  proof: f.contDiff.continuous

中文:
定理 continuous
  条件: (f : 𝓓^{n}_{K}(E, F))
  结论: 连续 f
  证明: f.contDiff.continuous
-/
protected theorem continuous (f : 𝓓^{n}_{K}(E, F)) : Continuous f :=
  f.contDiff.continuous

/-- Inclusion of unbundled `n`-times continuously differentiable function with support included
in a compact `K` into the space `𝓓^{n}_{K}`. -/
@[simps]
/--
Definition of `of_support_subset` / `of_support_subset` 的定义

English:
definition of_support_subset
  signature: {f : E -> F} (hf : ContDiff Real n f) (hsupp : support f subseteq K)
  body: f
  contDiff' := hf
  zero_on_compl' := support_subset_iff'.mp hsupp

中文:
定义 of_support_subset
  签名: {f : E -> F} (hf : 连续可微 实数 n f) (hsupp : support f subseteq K)
  定义体: f
  contDiff' := hf
  zero_on_compl' := support_subset_iff'.mp hsupp
-/
protected def of_support_subset {f : E -> F} (hf : ContDiff Real n f) (hsupp : support f subseteq K) :
    𝓓^{n}_{K}(E, F) where
  toFun := f
  contDiff' := hf
  zero_on_compl' := support_subset_iff'.mp hsupp

/--
theorem `bounded_iteratedFDeriv` / 定理 `bounded_iteratedFDeriv`

English:
theorem bounded_iteratedFDeriv
  given: (f : 𝓓^{n}_{K}(E, F)) {i : Nat} (hi : i <= n)
  proof: Continuous.bounded_above_of_compact_support
    (f.contDiff.continuous_iteratedFDeriv <| (WithTop.le_coe rfl).mpr hi)
    (f.hasCompactSupport.iteratedFDeriv i)

中文:
定理 bounded_iteratedFDeriv
  条件: (f : 𝓓^{n}_{K}(E, F)) {i : 自然数} (hi : i <= n)
  证明: Continuous.bounded_above_of_compact_support
    (f.contDiff.continuous_iteratedFDeriv <| (WithTop.le_coe rfl).mpr hi)
    (f.hasCompactSupport.iteratedFDeriv i)
-/
protected theorem bounded_iteratedFDeriv (f : 𝓓^{n}_{K}(E, F)) {i : Nat} (hi : i <= n) :
    exists C, forall x, ‖iteratedFDeriv Real i f x‖ <= C :=
  Continuous.bounded_above_of_compact_support
    (f.contDiff.continuous_iteratedFDeriv <| (WithTop.le_coe rfl).mpr hi)
    (f.hasCompactSupport.iteratedFDeriv i)

/--
theorem `iteratedFDeriv_zero_on_compl` / 定理 `iteratedFDeriv_zero_on_compl`

English:
theorem iteratedFDeriv_zero_on_compl
  given: (f : 𝓓^{n}_{K}(E, F)) {i : Nat}
  proof: by
  intro x (hx : x ∉ K)
  contrapose! hx
  exact f.tsupport_subset (support_iteratedFDeriv_subset i hx)

中文:
定理 iteratedFDeriv_zero_on_compl
  条件: (f : 𝓓^{n}_{K}(E, F)) {i : 自然数}
  证明: by
  intro x (hx : x ∉ K)
  contrapose! hx
  exact f.tsupport_subset (support_iteratedFDeriv_subset i hx)
-/
protected theorem iteratedFDeriv_zero_on_compl (f : 𝓓^{n}_{K}(E, F)) {i : Nat} :
    EqOn (iteratedFDeriv Real i f) 0 Kᶜ := by
  intro x (hx : x ∉ K)
  contrapose! hx
  exact f.tsupport_subset (support_iteratedFDeriv_subset i hx)

/--
Definition of `toBoundedContinuousFunctionLM` / `toBoundedContinuousFunctionLM` 的定义

English:
definition toBoundedContinuousFunctionLM
  signature: : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] E ->ᵇ F where
  body: f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

中文:
定义 toBoundedContinuousFunctionLM
  签名: : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] E ->ᵇ F where
  定义体: f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
-/
noncomputable def toBoundedContinuousFunctionLM : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] E ->ᵇ F where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/--
lemma `toBoundedContinuousFunctionLM_apply` / 引理 `toBoundedContinuousFunctionLM_apply`

English:
lemma toBoundedContinuousFunctionLM_apply
  given: (f : 𝓓^{n}_{K}(E, F))
  proof: rfl

中文:
引理 toBoundedContinuousFunctionLM_apply
  条件: (f : 𝓓^{n}_{K}(E, F))
  证明: rfl
-/
lemma toBoundedContinuousFunctionLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    toBoundedContinuousFunctionLM 𝕜 f = f :=
  rfl

/--
lemma `toBoundedContinuousFunctionLM_eq_of_scalars` / 引理 `toBoundedContinuousFunctionLM_eq_of_scalars`

English:
lemma toBoundedContinuousFunctionLM_eq_of_scalars
  statement: (𝕜' : Type*) [NontriviallyNormedField 𝕜']
  proof: rfl

中文:
引理 toBoundedContinuousFunctionLM_eq_of_scalars
  结论: (𝕜' : 类型) [NontriviallyNormedField 𝕜']
  证明: rfl
-/
lemma toBoundedContinuousFunctionLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] :
    (toBoundedContinuousFunctionLM 𝕜 : 𝓓^{n}_{K}(E, F) -> _) = toBoundedContinuousFunctionLM 𝕜' :=
  rfl

variable {𝕜} in
-- Note: generalizing this to a semilinear setting would require a semilinear version of
-- `CompatibleSMul`.
/--
Definition of `postcompLM` / `postcompLM` 的定义

English:
definition postcompLM
  signature: [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F')
  body: ⟨T ∘ f, T.restrictScalars Real
    fun x hx => by simp [f.zero_on_compl hx]⟩
  map_add' f g := by ext x; exact map_add T (f x) (g x)
  map_smul' c f := by ext x; exact map_smul T c (f x)

@[simp]

中文:
定义 postcompLM
  签名: [线性映射.余mpatibleSMul F F' 实数 𝕜] (T : F ->L[𝕜] F')
  定义体: ⟨T ∘ f, T.restrictScalars Real
    fun x hx => by simp [f.zero_on_compl hx]⟩
  map_add' f g := by ext x; exact map_add T (f x) (g x)
  map_smul' c f := by ext x; exact map_smul T c (f x)

@[simp]

Depends on / 依赖: T.restrictScalars, restrictScalars
-/
noncomputable def postcompLM [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F') :
    𝓓^{n}_{K}(E, F) ->ₗ[𝕜] 𝓓^{n}_{K}(E, F') where
.contDiff.comp f.contDiff, toFun f := ⟨T ∘ f, T.restrictScalars Real
    fun x hx => by simp [f.zero_on_compl hx]⟩
  map_add' f g := by ext x; exact map_add T (f x) (g x)
  map_smul' c f := by ext x; exact map_smul T c (f x)

@[simp]
/--
lemma `postcompLM_apply` / 引理 `postcompLM_apply`

English:
lemma postcompLM_apply
  statement: [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F')
  proof: rfl

中文:
引理 postcompLM_apply
  结论: [线性映射.余mpatibleSMul F F' 实数 𝕜] (T : F ->L[𝕜] F')
  证明: rfl
-/
lemma postcompLM_apply [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F')
    (f : 𝓓^{n}_{K}(E, F)) :
    postcompLM T f = T ∘ f :=
  rfl

open scoped Classical in
/--
Definition of `monoLM` / `monoLM` 的定义

English:
definition monoLM
  signature: :
  body: if h : n₂ <= n₁ ∧ K₁ <= K₂ then
      .of_support_subset (f.contDiff.of_le (mod_cast h.1)) (f.support_subset.trans h.2)
    else 0
  map_add' f g := by split_ifs <;> ext <;> simp
  map_smul' c f := by split_ifs <;> ext <;> simp

中文:
定义 monoLM
  签名: :
  定义体: if h : n₂ <= n₁ ∧ K₁ <= K₂ then
      .of_support_subset (f.contDiff.of_le (mod_cast h.1)) (f.support_subset.trans h.2)
    else 0
  map_add' f g := by split_ifs <;> ext <;> simp
  map_smul' c f := by split_ifs <;> ext <;> simp

Depends on / 依赖: contDiff, f.contDiff.of_le, f.support_subset.trans, map_add, map_smul, mod_cast, of_le, of_support_subset, split_ifs, support_subset
-/
noncomputable def monoLM :
    𝓓^{n₁}_{K₁}(E, F) ->ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F) where
  toFun f :=
    if h : n₂ <= n₁ ∧ K₁ <= K₂ then
      .of_support_subset (f.contDiff.of_le (mod_cast h.1)) (f.support_subset.trans h.2)
    else 0
  map_add' f g := by split_ifs <;> ext <;> simp
  map_smul' c f := by split_ifs <;> ext <;> simp

open scoped Classical in
@[simp]
/--
lemma `monoLM_apply` / 引理 `monoLM_apply`

English:
lemma monoLM_apply
  given: (f : 𝓓^{n₁}_{K₁}(E, F))
  proof: by
  rw [monoLM]
  split_ifs <;> rfl

中文:
引理 monoLM_apply
  条件: (f : 𝓓^{n₁}_{K₁}(E, F))
  证明: by
  rw [monoLM]
  split_ifs <;> rfl

Depends on / 依赖: monoLM, split_ifs
-/
lemma monoLM_apply (f : 𝓓^{n₁}_{K₁}(E, F)) :
    ((monoLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F)) : E -> F) = if n₂ <= n₁ ∧ K₁ <= K₂ then f else 0 := by
  rw [monoLM]
  split_ifs <;> rfl

/--
lemma `monoLM_eq_zero` / 引理 `monoLM_eq_zero`

English:
lemma monoLM_eq_zero
  given: (H : ¬ (n₂ <= n₁ ∧ K₁ <= K₂))
  proof: by
  ext; simp [H]

中文:
引理 monoLM_eq_zero
  条件: (H : ¬ (n₂ <= n₁ ∧ K₁ <= K₂))
  证明: by
  ext; simp [H]
-/
lemma monoLM_eq_zero (H : ¬ (n₂ <= n₁ ∧ K₁ <= K₂)) :
    (monoLM 𝕜 : 𝓓^{n₁}_{K₁}(E, F) ->ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F)) = 0 := by
  ext; simp [H]

/--
lemma `monoLM_eq_of_scalars` / 引理 `monoLM_eq_of_scalars`

English:
lemma monoLM_eq_of_scalars
  statement: (𝕜' : Type*)
  proof: rfl

中文:
引理 monoLM_eq_of_scalars
  结论: (𝕜' : 类型)
  证明: rfl
-/
lemma monoLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] :
    (monoLM 𝕜 : 𝓓^{n₁}_{K₁}(E, F) -> 𝓓^{n₂}_{K₂}(E, F)) = monoLM 𝕜' :=
  rfl

variable (n k) in
/--
Definition of `fderivLM` / `fderivLM` 的定义

English:
definition fderivLM
  signature: :
  body: if hk : k + 1 <= n then
      .of_support_subset
        (f.contDiff.fderiv_right <| mod_cast hk)
        ((support_fderiv_subset Real).trans f.tsupport_subset)
    else 0
  map_add' f g := by
    split_ifs with hk
    · have hk' : 0 < (n : Nat∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_l

中文:
定义 fderivLM
  签名: :
  定义体: if hk : k + 1 <= n then
      .of_support_subset
        (f.contDiff.fderiv_right <| mod_cast hk)
        ((support_fderiv_subset Real).trans f.tsupport_subset)
    else 0
  map_add' f g := by
    split_ifs with hk
    · have hk' : 0 < (n : Nat∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_l

Depends on / 依赖: FunLike, FunLike.coe_add, add_pos_of_right, coe_add, contDiff, differentiable, differentiableAt, f.contDiff.differentiable, f.contDiff.fderiv_right, f.tsupport_subset, fderiv_add, fderiv_right, g.contDiff.differentiable, map_add, map_smul, mod_cast, of_support_subset, split_ifs, support_fderiv_subset, trans_le
-/
noncomputable def fderivLM :
    𝓓^{n}_{K}(E, F) ->ₗ[𝕜] 𝓓^{k}_{K}(E, E ->L[Real] F) where
  toFun f :=
    if hk : k + 1 <= n then
      .of_support_subset
        (f.contDiff.fderiv_right <| mod_cast hk)
        ((support_fderiv_subset Real).trans f.tsupport_subset)
    else 0
  map_add' f g := by
    split_ifs with hk
    · have hk' : 0 < (n : Nat∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_le hk
      ext
      simp [fderiv_add (f.contDiff.differentiable hk'.ne').differentiableAt
                       (g.contDiff.differentiable hk'.ne').differentiableAt, FunLike.coe_add]
    · simp
  map_smul' c f := by
    split_ifs with hk
    · have hk' : 0 < (n : Nat∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_le hk
      ext
      simp [fderiv_const_smul (f.contDiff.differentiable hk'.ne').differentiableAt,
        FunLike.coe_smul]
    · simp

@[simp]
/--
lemma `fderivLM_apply` / 引理 `fderivLM_apply`

English:
lemma fderivLM_apply
  given: (f : 𝓓^{n}_{K}(E, F))
  proof: by
  rw [fderivLM]
  split_ifs <;> rfl

中文:
引理 fderivLM_apply
  条件: (f : 𝓓^{n}_{K}(E, F))
  证明: by
  rw [fderivLM]
  split_ifs <;> rfl

Depends on / 依赖: fderivLM, split_ifs
-/
lemma fderivLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    fderivLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0 := by
  rw [fderivLM]
  split_ifs <;> rfl

/--
lemma `fderivLM_apply_of_le` / 引理 `fderivLM_apply_of_le`

English:
lemma fderivLM_apply_of_le
  given: (f : 𝓓^{n}_{K}(E, F)) (hk : k + 1 <= n)
  proof: by
  simp [hk]

中文:
引理 fderivLM_apply_of_le
  条件: (f : 𝓓^{n}_{K}(E, F)) (hk : k + 1 <= n)
  证明: by
  simp [hk]
-/
lemma fderivLM_apply_of_le (f : 𝓓^{n}_{K}(E, F)) (hk : k + 1 <= n) :
    fderivLM 𝕜 n k f = fderiv Real f := by
  simp [hk]

/--
lemma `fderivLM_apply_of_gt` / 引理 `fderivLM_apply_of_gt`

English:
lemma fderivLM_apply_of_gt
  given: (f : 𝓓^{n}_{K}(E, F)) (hk : n < k + 1)
  proof: by
  ext : 1
  simp [not_le_of_gt hk]

中文:
引理 fderivLM_apply_of_gt
  条件: (f : 𝓓^{n}_{K}(E, F)) (hk : n < k + 1)
  证明: by
  ext : 1
  simp [not_le_of_gt hk]

Depends on / 依赖: not_le_of_gt
-/
lemma fderivLM_apply_of_gt (f : 𝓓^{n}_{K}(E, F)) (hk : n < k + 1) :
    fderivLM 𝕜 n k f = 0 := by
  ext : 1
  simp [not_le_of_gt hk]

/--
lemma `fderivLM_eq_of_scalars` / 引理 `fderivLM_eq_of_scalars`

English:
lemma fderivLM_eq_of_scalars
  statement: (𝕜' : Type*) [NontriviallyNormedField 𝕜']
  proof: rfl

中文:
引理 fderivLM_eq_of_scalars
  结论: (𝕜' : 类型) [NontriviallyNormedField 𝕜']
  证明: rfl
-/
lemma fderivLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] :
    (fderivLM 𝕜 n k : 𝓓^{n}_{K}(E, F) -> _) = fderivLM 𝕜' n k :=
  rfl

variable (n k) in
/--
Definition of `iteratedFDerivLM` / `iteratedFDerivLM` 的定义

English:
definition iteratedFDerivLM
  signature: (i : Nat)
  body: if hi : k + i <= n then
      .of_support_subset
        (f.contDiff.iteratedFDeriv_right <| mod_cast hi)
        ((support_iteratedFDeriv_subset i).trans f.tsupport_subset)
    else 0
  map_add' f g := by
    split_ifs with hi
    · have hi' : (i : Nat∞ω) <= n := mod_cast (le_of_add_le_right hi)
  

中文:
定义 iteratedFDerivLM
  签名: (i : 自然数)
  定义体: if hi : k + i <= n then
      .of_support_subset
        (f.contDiff.iteratedFDeriv_right <| mod_cast hi)
        ((support_iteratedFDeriv_subset i).trans f.tsupport_subset)
    else 0
  map_add' f g := by
    split_ifs with hi
    · have hi' : (i : Nat∞ω) <= n := mod_cast (le_of_add_le_right hi)
  

Depends on / 依赖: FunLike, FunLike.coe_add, coe_add, contDiff, f.contDiff.iteratedFDeriv_right, f.contDiff.of_le, f.tsupport_subset, g.contDiff.of_le, iteratedFDeriv_add, iteratedFDeriv_const_smu, iteratedFDeriv_right, le_of_add_le_right, map_add, map_smul, mod_cast, of_le, of_support_subset, split_ifs, support_iteratedFDeriv_subset, tsupport_subset
-/
noncomputable def iteratedFDerivLM (i : Nat) :
    𝓓^{n}_{K}(E, F) ->ₗ[𝕜] 𝓓^{k}_{K}(E, E [×i]->L[Real] F) where
  /-
  Note: it is tempting to define this as some linear map if `k + i ≤ n`,
  and the zero map otherwise. However, we would lose the definitional equality between
  `iteratedFDerivLM 𝕜 n k i f` and `iteratedFDerivLM ℝ n k i f`.

  This is caused by the fact that the equality `f (if p then x else y) = if p then f x else f y`
  is not definitional.
  -/
  toFun f :=
    if hi : k + i <= n then
      .of_support_subset
        (f.contDiff.iteratedFDeriv_right <| mod_cast hi)
        ((support_iteratedFDeriv_subset i).trans f.tsupport_subset)
    else 0
  map_add' f g := by
    split_ifs with hi
    · have hi' : (i : Nat∞ω) <= n := mod_cast (le_of_add_le_right hi)
      ext
      simp [iteratedFDeriv_add (f.contDiff.of_le hi') (g.contDiff.of_le hi'), FunLike.coe_add]
    · simp
  map_smul' c f := by
    split_ifs with hi
    · have hi' : (i : Nat∞ω) <= n := mod_cast (le_of_add_le_right hi)
      ext
      simp [iteratedFDeriv_const_smul_apply (f.contDiff.of_le hi').contDiffAt, FunLike.coe_smul]
    · simp

@[simp]
/--
lemma `iteratedFDerivLM_apply` / 引理 `iteratedFDerivLM_apply`

English:
lemma iteratedFDerivLM_apply
  given: {i : Nat} (f : 𝓓^{n}_{K}(E, F))
  proof: by
  rw [ContDiffMapSupportedIn.iteratedFDerivLM]
  split_ifs <;> rfl

中文:
引理 iteratedFDerivLM_apply
  条件: {i : 自然数} (f : 𝓓^{n}_{K}(E, F))
  证明: by
  rw [ContDiffMapSupportedIn.iteratedFDerivLM]
  split_ifs <;> rfl

Depends on / 依赖: ContDiffMapSupportedIn, ContDiffMapSupportedIn.iteratedFDerivLM, iteratedFDerivLM, split_ifs
-/
lemma iteratedFDerivLM_apply {i : Nat} (f : 𝓓^{n}_{K}(E, F)) :
    iteratedFDerivLM 𝕜 n k i f = if k + i <= n then iteratedFDeriv Real i f else 0 := by
  rw [ContDiffMapSupportedIn.iteratedFDerivLM]
  split_ifs <;> rfl

/--
lemma `iteratedFDerivLM_apply_of_le` / 引理 `iteratedFDerivLM_apply_of_le`

English:
lemma iteratedFDerivLM_apply_of_le
  given: {i : Nat} (f : 𝓓^{n}_{K}(E, F)) (hin : k + i <= n)
  proof: by
  simp [hin]

中文:
引理 iteratedFDerivLM_apply_of_le
  条件: {i : 自然数} (f : 𝓓^{n}_{K}(E, F)) (hin : k + i <= n)
  证明: by
  simp [hin]
-/
lemma iteratedFDerivLM_apply_of_le {i : Nat} (f : 𝓓^{n}_{K}(E, F)) (hin : k + i <= n) :
    iteratedFDerivLM 𝕜 n k i f = iteratedFDeriv Real i f := by
  simp [hin]

/--
lemma `iteratedFDerivLM_apply_of_gt` / 引理 `iteratedFDerivLM_apply_of_gt`

English:
lemma iteratedFDerivLM_apply_of_gt
  given: {i : Nat} (f : 𝓓^{n}_{K}(E, F)) (hin : n < k + i)
  proof: by
  ext : 1
  simp [not_le_of_gt hin]

中文:
引理 iteratedFDerivLM_apply_of_gt
  条件: {i : 自然数} (f : 𝓓^{n}_{K}(E, F)) (hin : n < k + i)
  证明: by
  ext : 1
  simp [not_le_of_gt hin]

Depends on / 依赖: not_le_of_gt
-/
lemma iteratedFDerivLM_apply_of_gt {i : Nat} (f : 𝓓^{n}_{K}(E, F)) (hin : n < k + i) :
    iteratedFDerivLM 𝕜 n k i f = 0 := by
  ext : 1
  simp [not_le_of_gt hin]

/--
lemma `iteratedFDerivLM_eq_of_scalars` / 引理 `iteratedFDerivLM_eq_of_scalars`

English:
lemma iteratedFDerivLM_eq_of_scalars
  statement: {i : Nat} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
  proof: rfl

中文:
引理 iteratedFDerivLM_eq_of_scalars
  结论: {i : 自然数} (𝕜' : 类型) [NontriviallyNormedField 𝕜']
  证明: rfl
-/
lemma iteratedFDerivLM_eq_of_scalars {i : Nat} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] :
    (iteratedFDerivLM 𝕜 n k i : 𝓓^{n}_{K}(E, F) -> _)
      = iteratedFDerivLM 𝕜' n k i :=
  rfl

variable (n) in
/--
Definition of `structureMapLM` / `structureMapLM` 的定义

English:
definition structureMapLM
  signature: (i : Nat)
  body: toBoundedContinuousFunctionLM 𝕜 ∘ₗ iteratedFDerivLM 𝕜 n 0 i

中文:
定义 structureMapLM
  签名: (i : 自然数)
  定义体: toBoundedContinuousFunctionLM 𝕜 ∘ₗ iteratedFDerivLM 𝕜 n 0 i

Depends on / 依赖: iteratedFDerivLM, toBoundedContinuousFunctionLM
-/
noncomputable def structureMapLM (i : Nat) :
    𝓓^{n}_{K}(E, F) ->ₗ[𝕜] E ->ᵇ (E [×i]->L[Real] F) :=
  toBoundedContinuousFunctionLM 𝕜 ∘ₗ iteratedFDerivLM 𝕜 n 0 i

/--
lemma `structureMapLM_eq` / 引理 `structureMapLM_eq`

English:
lemma structureMapLM_eq
  given: {i : Nat}
  proof: rfl

中文:
引理 structureMapLM_eq
  条件: {i : 自然数}
  证明: rfl
-/
lemma structureMapLM_eq {i : Nat} :
    (structureMapLM 𝕜 n i : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] E ->ᵇ (E [×i]->L[Real] F)) =
      (toBoundedContinuousFunctionLM 𝕜 : 𝓓^{0}_{K}(E, E [×i]->L[Real] F) ->ₗ[𝕜] E ->ᵇ (E [×i]->L[Real] F)) ∘ₗ
      (iteratedFDerivLM 𝕜 n 0 i : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] 𝓓^{0}_{K}(E, E [×i]->L[Real] F)) :=
  rfl

/--
lemma `structureMapLM_apply` / 引理 `structureMapLM_apply`

English:
lemma structureMapLM_apply
  given: {i : Nat} (f : 𝓓^{n}_{K}(E, F))
  proof: by
  simp [structureMapLM]

中文:
引理 structureMapLM_apply
  条件: {i : 自然数} (f : 𝓓^{n}_{K}(E, F))
  证明: by
  simp [structureMapLM]

Depends on / 依赖: structureMapLM
-/
lemma structureMapLM_apply {i : Nat} (f : 𝓓^{n}_{K}(E, F)) :
    structureMapLM 𝕜 n i f = if i <= n then iteratedFDeriv Real i f else 0 := by
  simp [structureMapLM]

/--
lemma `structureMapLM_top_apply` / 引理 `structureMapLM_top_apply`

English:
lemma structureMapLM_top_apply
  given: {i : Nat} (f : 𝓓_{K}(E, F))
  proof: by
  simp [structureMapLM_eq]

中文:
引理 structureMapLM_top_apply
  条件: {i : 自然数} (f : 𝓓_{K}(E, F))
  证明: by
  simp [structureMapLM_eq]

Depends on / 依赖: structureMapLM_eq
-/
lemma structureMapLM_top_apply {i : Nat} (f : 𝓓_{K}(E, F)) :
    structureMapLM 𝕜 ⊤ i f = iteratedFDeriv Real i f := by
  simp [structureMapLM_eq]

/--
lemma `structureMapLM_eq_of_scalars` / 引理 `structureMapLM_eq_of_scalars`

English:
lemma structureMapLM_eq_of_scalars
  statement: {i : Nat} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
  proof: rfl

中文:
引理 structureMapLM_eq_of_scalars
  结论: {i : 自然数} (𝕜' : 类型) [NontriviallyNormedField 𝕜']
  证明: rfl
-/
lemma structureMapLM_eq_of_scalars {i : Nat} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] :
    (structureMapLM 𝕜 n i : 𝓓^{n}_{K}(E, F) -> _) = structureMapLM 𝕜' n i :=
  rfl

/--
lemma `structureMapLM_zero_apply` / 引理 `structureMapLM_zero_apply`

English:
lemma structureMapLM_zero_apply
  given: {f : 𝓓^{n}_{K}(E, F)} {x : E}
  proof: by
  ext
  simp [structureMapLM_apply, iteratedFDeriv_zero_eq_comp]

中文:
引理 structureMapLM_zero_apply
  条件: {f : 𝓓^{n}_{K}(E, F)} {x : E}
  证明: by
  ext
  simp [structureMapLM_apply, iteratedFDeriv_zero_eq_comp]

Depends on / 依赖: iteratedFDeriv_zero_eq_comp, structureMapLM_apply
-/
lemma structureMapLM_zero_apply {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    structureMapLM 𝕜 n 0 f x = ContinuousMultilinearMap.uncurry0 Real E (f x) := by
  ext
  simp [structureMapLM_apply, iteratedFDeriv_zero_eq_comp]

/--
lemma `structureMapLM_zero_injective` / 引理 `structureMapLM_zero_injective`

English:
lemma structureMapLM_zero_injective
  proof: by
  intro f g hfg
  simpa [BoundedContinuousFunction.ext_iff, ContinuousMultilinearMap.ext_iff,
    structureMapLM_zero_apply, ContDiffMapSupportedIn.ext_iff] using hfg

中文:
引理 structureMapLM_zero_injective
  证明: by
  intro f g hfg
  simpa [BoundedContinuousFunction.ext_iff, ContinuousMultilinearMap.ext_iff,
    structureMapLM_zero_apply, ContDiffMapSupportedIn.ext_iff] using hfg

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.ext_iff, ContDiffMapSupportedIn, ContDiffMapSupportedIn.ext_iff, ContinuousMultilinearMap, ContinuousMultilinearMap.ext_iff, ext_iff, structureMapLM_zero_apply
-/
lemma structureMapLM_zero_injective :
    Injective (structureMapLM 𝕜 n 0 : 𝓓^{n}_{K}(E, F) -> E ->ᵇ E [×0]->L[Real] F) := by
  intro f g hfg
  simpa [BoundedContinuousFunction.ext_iff, ContinuousMultilinearMap.ext_iff,
    structureMapLM_zero_apply, ContDiffMapSupportedIn.ext_iff] using hfg

section Topology

/--
Instance `topologicalSpace` / 实例 `topologicalSpace`

English:
instance topologicalSpace
  signature: : TopologicalSpace 𝓓^{n}_{K}(E, F)
  body: ⨅ (i : Nat), induced (structureMapLM Real n i) inferInstance

中文:
实例 topologicalSpace
  签名: : 拓扑空间 𝓓^{n}_{K}(E, F)
  定义体: ⨅ (i : Nat), induced (structureMapLM Real n i) inferInstance

Depends on / 依赖: induced, structureMapLM
-/
noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}_{K}(E, F) :=
  ⨅ (i : Nat), induced (structureMapLM Real n i) inferInstance

/--
Instance `uniformSpace` / 实例 `uniformSpace`

English:
instance uniformSpace
  signature: : UniformSpace 𝓓^{n}_{K}(E, F)
  body: .replaceTopology
  (⨅ (i : Nat), UniformSpace.comap (structureMapLM Real n i) inferInstance)
  toTopologicalSpace_iInf.symm

中文:
实例 uniformSpace
  签名: : 一致空间 𝓓^{n}_{K}(E, F)
  定义体: .replaceTopology
  (⨅ (i : Nat), UniformSpace.comap (structureMapLM Real n i) inferInstance)
  toTopologicalSpace_iInf.symm

Depends on / 依赖: replaceTopology
-/
noncomputable instance uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F) := .replaceTopology
  (⨅ (i : Nat), UniformSpace.comap (structureMapLM Real n i) inferInstance)
  toTopologicalSpace_iInf.symm

/--
theorem `uniformSpace_eq_iInf` / 定理 `uniformSpace_eq_iInf`

English:
theorem uniformSpace_eq_iInf
  statement: (uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F)) =
  proof: UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm

中文:
定理 uniformSpace_eq_iInf
  结论: (uniformSpace : 一致空间 𝓓^{n}_{K}(E, F)) =
  证明: UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm
-/
protected theorem uniformSpace_eq_iInf : (uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F)) =
    ⨅ (i : Nat), UniformSpace.comap (structureMapLM Real n i) inferInstance :=
  UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm

/--
Instance `isTopologicalAddGroup` / 实例 `isTopologicalAddGroup`

English:
instance isTopologicalAddGroup
  signature: : IsTopologicalAddGroup 𝓓^{n}_{K}(E, F)
  body: topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _

中文:
实例 isTopologicalAddGroup
  签名: : 是拓扑加群 𝓓^{n}_{K}(E, F)
  定义体: topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _

Depends on / 依赖: topologicalAddGroup_iInf, topologicalAddGroup_induced
-/
instance isTopologicalAddGroup : IsTopologicalAddGroup 𝓓^{n}_{K}(E, F) :=
  topologicalAddGroup_iInf fun _ => topologicalAddGroup_induced _

/--
Instance `isUniformAddGroup` / 实例 `isUniformAddGroup`

English:
instance isUniformAddGroup
  signature: : IsUniformAddGroup 𝓓^{n}_{K}(E, F)
  body: by
  rw [ContDiffMapSupportedIn.uniformSpace_eq_iInf]
  exact isUniformAddGroup_iInf fun _ => IsUniformAddGroup.comap _

中文:
实例 isUniformAddGroup
  签名: : 是UniformAdd群 𝓓^{n}_{K}(E, F)
  定义体: by
  rw [ContDiffMapSupportedIn.uniformSpace_eq_iInf]
  exact isUniformAddGroup_iInf fun _ => IsUniformAddGroup.comap _

Depends on / 依赖: ContDiffMapSupportedIn, ContDiffMapSupportedIn.uniformSpace_eq_iInf, IsUniformAddGroup, IsUniformAddGroup.comap, isUniformAddGroup_iInf, uniformSpace_eq_iInf
-/
instance isUniformAddGroup : IsUniformAddGroup 𝓓^{n}_{K}(E, F) := by
  rw [ContDiffMapSupportedIn.uniformSpace_eq_iInf]
  exact isUniformAddGroup_iInf fun _ => IsUniformAddGroup.comap _

/--
Instance `continuousSMul` / 实例 `continuousSMul`

English:
instance continuousSMul
  signature: : ContinuousSMul 𝕜 𝓓^{n}_{K}(E, F)
  body: continuousSMul_iInf fun i => continuousSMul_induced (structureMapLM 𝕜 n i)

中文:
实例 continuousSMul
  签名: : 连续标量乘法 𝕜 𝓓^{n}_{K}(E, F)
  定义体: continuousSMul_iInf fun i => continuousSMul_induced (structureMapLM 𝕜 n i)

Depends on / 依赖: continuousSMul_iInf, continuousSMul_induced, structureMapLM
-/
instance continuousSMul : ContinuousSMul 𝕜 𝓓^{n}_{K}(E, F) :=
  continuousSMul_iInf fun i => continuousSMul_induced (structureMapLM 𝕜 n i)

/--
Instance `locallyConvexSpace` / 实例 `locallyConvexSpace`

English:
instance locallyConvexSpace
  signature: : LocallyConvexSpace Real 𝓓^{n}_{K}(E, F)
  body: LocallyConvexSpace.iInf fun _ => LocallyConvexSpace.induced _

中文:
实例 locallyConvexSpace
  签名: : LocallyConvex空间 实数 𝓓^{n}_{K}(E, F)
  定义体: LocallyConvexSpace.iInf fun _ => LocallyConvexSpace.induced _

Depends on / 依赖: LocallyConvexSpace, LocallyConvexSpace.iInf, LocallyConvexSpace.induced, induced
-/
instance locallyConvexSpace : LocallyConvexSpace Real 𝓓^{n}_{K}(E, F) :=
  LocallyConvexSpace.iInf fun _ => LocallyConvexSpace.induced _

variable (n) in
/--
Definition of `structureMapCLM` / `structureMapCLM` 的定义

English:
definition structureMapCLM
  signature: (i : Nat)
  body: structureMapLM 𝕜 n i
  cont := continuous_iInf_dom continuous_induced_dom

@[simp]

中文:
定义 structureMapCLM
  签名: (i : 自然数)
  定义体: structureMapLM 𝕜 n i
  cont := continuous_iInf_dom continuous_induced_dom

@[simp]

Depends on / 依赖: structureMapLM
-/
noncomputable def structureMapCLM (i : Nat) :
    𝓓^{n}_{K}(E, F) ->L[𝕜] E ->ᵇ (E [×i]->L[Real] F) where
  toLinearMap := structureMapLM 𝕜 n i
  cont := continuous_iInf_dom continuous_induced_dom

@[simp]
/--
lemma `structureMapCLM_apply` / 引理 `structureMapCLM_apply`

English:
lemma structureMapCLM_apply
  given: {i : Nat} (f : 𝓓^{n}_{K}(E, F))
  proof: by
  simp [structureMapCLM, structureMapLM_apply]

中文:
引理 structureMapCLM_apply
  条件: {i : 自然数} (f : 𝓓^{n}_{K}(E, F))
  证明: by
  simp [structureMapCLM, structureMapLM_apply]

Depends on / 依赖: structureMapCLM, structureMapLM_apply
-/
lemma structureMapCLM_apply {i : Nat} (f : 𝓓^{n}_{K}(E, F)) :
    structureMapCLM 𝕜 n i f = if i <= n then iteratedFDeriv Real i f else 0 := by
  simp [structureMapCLM, structureMapLM_apply]

/--
lemma `structureMapCLM_top_apply` / 引理 `structureMapCLM_top_apply`

English:
lemma structureMapCLM_top_apply
  given: {i : Nat} (f : 𝓓_{K}(E, F))
  proof: by
  simp [structureMapCLM, structureMapLM_top_apply]

中文:
引理 structureMapCLM_top_apply
  条件: {i : 自然数} (f : 𝓓_{K}(E, F))
  证明: by
  simp [structureMapCLM, structureMapLM_top_apply]

Depends on / 依赖: structureMapCLM, structureMapLM_top_apply
-/
lemma structureMapCLM_top_apply {i : Nat} (f : 𝓓_{K}(E, F)) :
    structureMapCLM 𝕜 ⊤ i f = iteratedFDeriv Real i f := by
  simp [structureMapCLM, structureMapLM_top_apply]

/--
lemma `structureMapCLM_eq_of_scalars` / 引理 `structureMapCLM_eq_of_scalars`

English:
lemma structureMapCLM_eq_of_scalars
  statement: {i : Nat} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
  proof: rfl

中文:
引理 structureMapCLM_eq_of_scalars
  结论: {i : 自然数} (𝕜' : 类型) [NontriviallyNormedField 𝕜']
  证明: rfl
-/
lemma structureMapCLM_eq_of_scalars {i : Nat} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] :
    (structureMapCLM 𝕜 n i : 𝓓^{n}_{K}(E, F) -> _) = structureMapCLM 𝕜' n i :=
  rfl

/--
lemma `structureMapCLM_zero_apply` / 引理 `structureMapCLM_zero_apply`

English:
lemma structureMapCLM_zero_apply
  given: {f : 𝓓^{n}_{K}(E, F)} {x : E}
  proof: structureMapLM_zero_apply 𝕜

中文:
引理 structureMapCLM_zero_apply
  条件: {f : 𝓓^{n}_{K}(E, F)} {x : E}
  证明: structureMapLM_zero_apply 𝕜

Depends on / 依赖: structureMapLM_zero_apply
-/
lemma structureMapCLM_zero_apply {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    structureMapCLM 𝕜 n 0 f x = ContinuousMultilinearMap.uncurry0 Real E (f x) :=
  structureMapLM_zero_apply 𝕜

/--
lemma `structureMapCLM_zero_injective` / 引理 `structureMapCLM_zero_injective`

English:
lemma structureMapCLM_zero_injective
  proof: structureMapLM_zero_injective 𝕜

中文:
引理 structureMapCLM_zero_injective
  证明: structureMapLM_zero_injective 𝕜

Depends on / 依赖: structureMapLM_zero_injective
-/
lemma structureMapCLM_zero_injective :
    Injective (structureMapCLM 𝕜 n 0 : 𝓓^{n}_{K}(E, F) -> E ->ᵇ E [×0]->L[Real] F) :=
  structureMapLM_zero_injective 𝕜

/--
lemma `isUniformEmbedding_pi_structureMapCLM` / 引理 `isUniformEmbedding_pi_structureMapCLM`

English:
lemma isUniformEmbedding_pi_structureMapCLM
  proof: structureMapCLM_zero_injective 𝕜 (congr($hfg 0))
  toIsUniformInducing := by
    simp_rw [isUniformInducing_iff_uniformSpace, ContDiffMapSupportedIn.uniformSpace_eq_iInf,
      Pi.uniformSpace_eq, comap_iInf, ← comap_comap]
    rfl

中文:
引理 isUniformEmbedding_pi_structureMapCLM
  证明: structureMapCLM_zero_injective 𝕜 (congr($hfg 0))
  toIsUniformInducing := by
    simp_rw [isUniformInducing_iff_uniformSpace, ContDiffMapSupportedIn.uniformSpace_eq_iInf,
      Pi.uniformSpace_eq, comap_iInf, ← comap_comap]
    rfl

Depends on / 依赖: structureMapCLM_zero_injective
-/
lemma isUniformEmbedding_pi_structureMapCLM :
    IsUniformEmbedding (ContinuousLinearMap.pi (structureMapCLM 𝕜 n) :
      𝓓^{n}_{K}(E, F) ->L[𝕜] Π i, E ->ᵇ (E [×i]->L[Real] F)) where
  injective f g hfg := structureMapCLM_zero_injective 𝕜 (congr($hfg 0))
  toIsUniformInducing := by
    simp_rw [isUniformInducing_iff_uniformSpace, ContDiffMapSupportedIn.uniformSpace_eq_iInf,
      Pi.uniformSpace_eq, comap_iInf, ← comap_comap]
    rfl

-- Note: if needed, we could allow an extra parameter `𝕜` in case the user wants to use
-- `structureMapCLM 𝕜 n i`.
/--
theorem `continuous_iff_comp` / 定理 `continuous_iff_comp`

English:
theorem continuous_iff_comp
  given: {X} [TopologicalSpace X] (φ : X -> 𝓓^{n}_{K}(E, F))
  proof: by
  simp [continuous_iInf_rng, continuous_induced_rng, structureMapCLM]

中文:
定理 continuous_iff_comp
  条件: {X} [拓扑空间 X] (φ : X -> 𝓓^{n}_{K}(E, F))
  证明: by
  simp [continuous_iInf_rng, continuous_induced_rng, structureMapCLM]

Depends on / 依赖: continuous_iInf_rng, continuous_induced_rng, structureMapCLM
-/
theorem continuous_iff_comp {X} [TopologicalSpace X] (φ : X -> 𝓓^{n}_{K}(E, F)) :
    Continuous φ ↔ forall i, Continuous (structureMapCLM Real n i ∘ φ) := by
  simp [continuous_iInf_rng, continuous_induced_rng, structureMapCLM]

-- Note: if needed, we could allow an extra parameter `𝕜` in case the user wants to use
-- `structureMapCLM 𝕜 n i`.
/--
theorem `continuous_iff_comp_order_le` / 定理 `continuous_iff_comp_order_le`

English:
theorem continuous_iff_comp_order_le
  given: {X : Type*} [TopologicalSpace X] (φ : X -> 𝓓^{n}_{K}(E, F))
  proof: by
  rw [continuous_iff_comp]
  congrm (forall i, ?_)
  by_cases hin : i <= n <;> simp only [hin, true_imp_iff, false_imp_iff, iff_true]
  refine continuous_zero.congr fun x => ?_
  ext t : 1
  simp [hin, structureMapCLM_apply]

中文:
定理 continuous_iff_comp_order_le
  条件: {X : 类型} [拓扑空间 X] (φ : X -> 𝓓^{n}_{K}(E, F))
  证明: by
  rw [continuous_iff_comp]
  congrm (forall i, ?_)
  by_cases hin : i <= n <;> simp only [hin, true_imp_iff, false_imp_iff, iff_true]
  refine continuous_zero.congr fun x => ?_
  ext t : 1
  simp [hin, structureMapCLM_apply]

Depends on / 依赖: congrm, continuous_iff_comp, continuous_zero, continuous_zero.congr, false_imp_iff, iff_true, structureMapCLM_apply, true_imp_iff
-/
theorem continuous_iff_comp_order_le {X : Type*} [TopologicalSpace X] (φ : X -> 𝓓^{n}_{K}(E, F)) :
    Continuous φ ↔ forall (i : Nat), i <= n -> Continuous (structureMapCLM Real n i ∘ φ) := by
  rw [continuous_iff_comp]
  congrm (forall i, ?_)
  by_cases hin : i <= n <;> simp only [hin, true_imp_iff, false_imp_iff, iff_true]
  refine continuous_zero.congr fun x => ?_
  ext t : 1
  simp [hin, structureMapCLM_apply]

variable (E F n K)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def seminorm (i : Nat)
  body: (normSeminorm 𝕜 (E ->ᵇ (E [×i]->L[Real] F))).comp (structureMapLM 𝕜 n i)

中文:
定义 noncomputable
  签名: def seminorm (i : 自然数)
  定义体: (normSeminorm 𝕜 (E ->ᵇ (E [×i]->L[Real] F))).comp (structureMapLM 𝕜 n i)
-/
protected noncomputable def seminorm (i : Nat) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (normSeminorm 𝕜 (E ->ᵇ (E [×i]->L[Real] F))).comp (structureMapLM 𝕜 n i)

-- Note: If these end up conflicting with other seminorms (e.g `SchwartzMap.seminorm`),
-- we may want to put them in a more specific scope.
@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "]_{" K ", " n ", " i "}" =>
  ContDiffMapSupportedIn.seminorm 𝕜 _ _ n K i

@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "]_{" K ", " i "}" =>
  ContDiffMapSupportedIn.seminorm 𝕜 _ _ ⊤ K i

@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "; " F "]_{" K ", " n ", " i "}" =>
  ContDiffMapSupportedIn.seminorm 𝕜 _ F n K i

@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "; " F "]_{" K ", " i "}" =>
  ContDiffMapSupportedIn.seminorm 𝕜 _ F ⊤ K i

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def supSeminorm (i : Nat)
  body: (Finset.Iic i).sup (ContDiffMapSupportedIn.seminorm 𝕜 E F n K)

中文:
定义 noncomputable
  签名: def supSeminorm (i : 自然数)
  定义体: (Finset.Iic i).sup (ContDiffMapSupportedIn.seminorm 𝕜 E F n K)
-/
protected noncomputable def supSeminorm (i : Nat) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (Finset.Iic i).sup (ContDiffMapSupportedIn.seminorm 𝕜 E F n K)

/--
theorem `withSeminorms` / 定理 `withSeminorms`

English:
theorem withSeminorms
  proof: by
  let p : SeminormFamily 𝕜 𝓓^{n}_{K}(E, F) ((_ : Nat) × Fin 1) :=
    SeminormFamily.sigma fun i _ =>
      (normSeminorm 𝕜 (E ->ᵇ (E [×i]->L[Real] F))).comp (structureMapLM 𝕜 n i)
  have : WithSeminorms p :=
    withSeminorms_iInf fun i => LinearMap.withSeminorms_induced (norm_withSeminorms _ _)

中文:
定理 withSeminorms
  证明: by
  let p : SeminormFamily 𝕜 𝓓^{n}_{K}(E, F) ((_ : Nat) × Fin 1) :=
    SeminormFamily.sigma fun i _ =>
      (normSeminorm 𝕜 (E ->ᵇ (E [×i]->L[Real] F))).comp (structureMapLM 𝕜 n i)
  have : WithSeminorms p :=
    withSeminorms_iInf fun i => LinearMap.withSeminorms_induced (norm_withSeminorms _ _)
-/
protected theorem withSeminorms :
    WithSeminorms (ContDiffMapSupportedIn.seminorm 𝕜 E F n K) := by
  let p : SeminormFamily 𝕜 𝓓^{n}_{K}(E, F) ((_ : Nat) × Fin 1) :=
    SeminormFamily.sigma fun i _ =>
      (normSeminorm 𝕜 (E ->ᵇ (E [×i]->L[Real] F))).comp (structureMapLM 𝕜 n i)
  have : WithSeminorms p :=
    withSeminorms_iInf fun i => LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
  exact this.congr_equiv (Equiv.sigmaUnique _ _).symm

/--
theorem `withSeminorms'` / 定理 `withSeminorms'`

English:
theorem withSeminorms'
  proof: (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K).partial_sups

中文:
定理 withSeminorms'
  证明: (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K).partial_sups
-/
protected theorem withSeminorms' :
    WithSeminorms (ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K) :=
  (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K).partial_sups

variable {E F n K}

/--
theorem `seminorm_apply` / 定理 `seminorm_apply`

English:
theorem seminorm_apply
  given: (i : Nat) (f : 𝓓^{n}_{K}(E, F))
  proof: rfl

中文:
定理 seminorm_apply
  条件: (i : 自然数) (f : 𝓓^{n}_{K}(E, F))
  证明: rfl
-/
protected theorem seminorm_apply (i : Nat) (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} f = ‖structureMapCLM 𝕜 n i f‖ :=
  rfl

/--
theorem `seminorm_eq_bot_of_gt` / 定理 `seminorm_eq_bot_of_gt`

English:
theorem seminorm_eq_bot_of_gt
  given: {i : Nat} (hin : n < i)
  proof: by
  have : ¬(i <= n) := by simpa using hin
  ext f
  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.ext_iff,
    structureMapCLM_apply, this]

中文:
定理 seminorm_eq_bot_of_gt
  条件: {i : 自然数} (hin : n < i)
  证明: by
  have : ¬(i <= n) := by simpa using hin
  ext f
  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.ext_iff,
    structureMapCLM_apply, this]
-/
protected theorem seminorm_eq_bot_of_gt {i : Nat} (hin : n < i) :
    N[𝕜; F]_{K, n, i} = ⊥ := by
  have : ¬(i <= n) := by simpa using hin
  ext f
  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.ext_iff,
    structureMapCLM_apply, this]

/--
theorem `seminorm_le_iff` / 定理 `seminorm_le_iff`

English:
theorem seminorm_le_iff
  given: {C : Real} (hC : 0 <= C) (i : Nat) (f : 𝓓^{n}_{K}(E, F))
  proof: by
  have : (forall x, ‖iteratedFDeriv Real i f x‖ <= C) ↔ (forall x in K, ‖iteratedFDeriv Real i f x‖ <= C) := by
    congrm forall x, ?_
    by_cases hx : x in K
    · simp [hx]
    · simp [hx, f.iteratedFDeriv_zero_on_compl hx, hC]
  by_cases hi : i <= n
  · simp [hi, forall_const, ContDiffMapSup

中文:
定理 seminorm_le_iff
  条件: {C : 实数} (hC : 0 <= C) (i : 自然数) (f : 𝓓^{n}_{K}(E, F))
  证明: by
  have : (forall x, ‖iteratedFDeriv Real i f x‖ <= C) ↔ (forall x in K, ‖iteratedFDeriv Real i f x‖ <= C) := by
    congrm forall x, ?_
    by_cases hx : x in K
    · simp [hx]
    · simp [hx, f.iteratedFDeriv_zero_on_compl hx, hC]
  by_cases hi : i <= n
  · simp [hi, forall_const, ContDiffMapSup
-/
protected theorem seminorm_le_iff {C : Real} (hC : 0 <= C) (i : Nat) (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} f <= C ↔ (i <= n -> forall x in K, ‖iteratedFDeriv Real i f x‖ <= C) := by
  have : (forall x, ‖iteratedFDeriv Real i f x‖ <= C) ↔ (forall x in K, ‖iteratedFDeriv Real i f x‖ <= C) := by
    congrm forall x, ?_
    by_cases hx : x in K
    · simp [hx]
    · simp [hx, f.iteratedFDeriv_zero_on_compl hx, hC]
  by_cases hi : i <= n
  · simp [hi, forall_const, ContDiffMapSupportedIn.seminorm_apply, structureMapCLM_apply,
      BoundedContinuousFunction.norm_le hC, this]
  · push Not at hi
    simp [hi, ContDiffMapSupportedIn.seminorm_eq_bot_of_gt _ hi, hC]

/--
theorem `seminorm_top_le_iff` / 定理 `seminorm_top_le_iff`

English:
theorem seminorm_top_le_iff
  given: {C : Real} (hC : 0 <= C) (i : Nat) (f : 𝓓_{K}(E, F))
  proof: by
  simp_rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 hC, le_top, forall_const]

中文:
定理 seminorm_top_le_iff
  条件: {C : 实数} (hC : 0 <= C) (i : 自然数) (f : 𝓓_{K}(E, F))
  证明: by
  simp_rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 hC, le_top, forall_const]
-/
protected theorem seminorm_top_le_iff {C : Real} (hC : 0 <= C) (i : Nat) (f : 𝓓_{K}(E, F)) :
    N[𝕜]_{K, i} f <= C ↔ forall x in K, ‖iteratedFDeriv Real i f x‖ <= C := by
  simp_rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 hC, le_top, forall_const]

/--
theorem `norm_iteratedFDeriv_apply_le_seminorm` / 定理 `norm_iteratedFDeriv_apply_le_seminorm`

English:
theorem norm_iteratedFDeriv_apply_le_seminorm
  statement: {i : Nat} (hin : i <= n)
  proof: calc
      ‖iteratedFDeriv Real i f x‖
  _ = ‖structureMapLM Real n i f x‖ := by simp [structureMapLM_apply, hin]
  _ <= ‖structureMapLM Real n i f‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
  _ = N[𝕜]_{K, n, i} f := rfl

中文:
定理 norm_iteratedFDeriv_apply_le_seminorm
  结论: {i : 自然数} (hin : i <= n)
  证明: calc
      ‖iteratedFDeriv Real i f x‖
  _ = ‖structureMapLM Real n i f x‖ := by simp [structureMapLM_apply, hin]
  _ <= ‖structureMapLM Real n i f‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
  _ = N[𝕜]_{K, n, i} f := rfl

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_coe_le_norm, iteratedFDeriv, norm_coe_le_norm, structureMapLM, structureMapLM_apply
-/
theorem norm_iteratedFDeriv_apply_le_seminorm {i : Nat} (hin : i <= n)
    {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    ‖iteratedFDeriv Real i f x‖ <= N[𝕜]_{K, n, i} f :=
  calc
      ‖iteratedFDeriv Real i f x‖
  _ = ‖structureMapLM Real n i f x‖ := by simp [structureMapLM_apply, hin]
  _ <= ‖structureMapLM Real n i f‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
  _ = N[𝕜]_{K, n, i} f := rfl

/--
theorem `norm_iteratedFDeriv_apply_le_seminorm_top` / 定理 `norm_iteratedFDeriv_apply_le_seminorm_top`

English:
theorem norm_iteratedFDeriv_apply_le_seminorm_top
  statement: {i : Nat}
  proof: norm_iteratedFDeriv_apply_le_seminorm 𝕜 (mod_cast le_top)

中文:
定理 norm_iteratedFDeriv_apply_le_seminorm_top
  结论: {i : 自然数}
  证明: norm_iteratedFDeriv_apply_le_seminorm 𝕜 (mod_cast le_top)

Depends on / 依赖: le_top, mod_cast, norm_iteratedFDeriv_apply_le_seminorm
-/
theorem norm_iteratedFDeriv_apply_le_seminorm_top {i : Nat}
    {f : 𝓓_{K}(E, F)} {x : E} :
    ‖iteratedFDeriv Real i f x‖ <= N[𝕜]_{K, i} f :=
  norm_iteratedFDeriv_apply_le_seminorm 𝕜 (mod_cast le_top)

/--
theorem `norm_apply_le_seminorm` / 定理 `norm_apply_le_seminorm`

English:
theorem norm_apply_le_seminorm
  given: {f : 𝓓^{n}_{K}(E, F)} {x : E}
  proof: by
  rw [← norm_iteratedFDeriv_zero (𝕜 := Real) (f := f) (x := x)]
  exact norm_iteratedFDeriv_apply_le_seminorm 𝕜 zero_le

中文:
定理 norm_apply_le_seminorm
  条件: {f : 𝓓^{n}_{K}(E, F)} {x : E}
  证明: by
  rw [← norm_iteratedFDeriv_zero (𝕜 := Real) (f := f) (x := x)]
  exact norm_iteratedFDeriv_apply_le_seminorm 𝕜 zero_le

Depends on / 依赖: norm_iteratedFDeriv_apply_le_seminorm, norm_iteratedFDeriv_zero, zero_le
-/
theorem norm_apply_le_seminorm {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    ‖f x‖ <= N[𝕜]_{K, n, 0} f := by
  rw [← norm_iteratedFDeriv_zero (𝕜 := Real) (f := f) (x := x)]
  exact norm_iteratedFDeriv_apply_le_seminorm 𝕜 zero_le

/--
theorem `norm_toBoundedContinuousFunction` / 定理 `norm_toBoundedContinuousFunction`

English:
theorem norm_toBoundedContinuousFunction
  given: (f : 𝓓^{n}_{K}(E, F))
  proof: by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm,
    ContDiffMapSupportedIn.seminorm_apply, structureMapCLM_apply]

中文:
定理 norm_toBoundedContinuousFunction
  条件: (f : 𝓓^{n}_{K}(E, F))
  证明: by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm,
    ContDiffMapSupportedIn.seminorm_apply, structureMapCLM_apply]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_eq_iSup_norm, ContDiffMapSupportedIn, ContDiffMapSupportedIn.seminorm_apply, norm_eq_iSup_norm, seminorm_apply, structureMapCLM_apply
-/
theorem norm_toBoundedContinuousFunction (f : 𝓓^{n}_{K}(E, F)) :
    ‖(f : E ->ᵇ F)‖ = N[𝕜]_{K, n, 0} f := by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm,
    ContDiffMapSupportedIn.seminorm_apply, structureMapCLM_apply]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mkCLM (A : 𝓓^{n₁}_{K₁}(E, F) -> E -> F')
  body: letI Φ : 𝓓^{n₁}_{K₁}(E, F) ->ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F') :=
    { toFun f := ⟨A f, hsmooth f, hsupp f⟩
      map_add' f g := ext (hadd f g)
      map_smul' c f := ext (hsmul c f) }
  { toLinearMap := Φ
    cont := show Continuous Φ by
      refine continuous_of_isBounded (ContDiffMapSupportedIn.withSemi

中文:
定义 noncomputable
  签名: def mkCLM (A : 𝓓^{n₁}_{K₁}(E, F) -> E -> F')
  定义体: letI Φ : 𝓓^{n₁}_{K₁}(E, F) ->ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F') :=
    { toFun f := ⟨A f, hsmooth f, hsupp f⟩
      map_add' f g := ext (hadd f g)
      map_smul' c f := ext (hsmul c f) }
  { toLinearMap := Φ
    cont := show Continuous Φ by
      refine continuous_of_isBounded (ContDiffMapSupportedIn.withSemi
-/
protected noncomputable def mkCLM (A : 𝓓^{n₁}_{K₁}(E, F) -> E -> F')
    (hadd : forall f g x, A (f + g) x = A f x + A g x)
    (hsmul : forall (c : 𝕜) f x, A (c • f) x = c • A f x)
    (hsmooth : forall f, ContDiff Real n₂ (A f))
    (hsupp : forall f, EqOn (A f) 0 K₂ᶜ)
    (hbound : forall i : Nat, i <= n₂ -> exists (s : Finset Nat) (C : Real), 0 <= C ∧ forall f, forall x in K₂,
      ‖iteratedFDeriv Real i (A f) x‖ <= C * (s.sup fun j => N[𝕜]_{K₁, n₁, j}) f) :
    𝓓^{n₁}_{K₁}(E, F) ->L[𝕜] 𝓓^{n₂}_{K₂}(E, F') :=
  letI Φ : 𝓓^{n₁}_{K₁}(E, F) ->ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F') :=
    { toFun f := ⟨A f, hsmooth f, hsupp f⟩
      map_add' f g := ext (hadd f g)
      map_smul' c f := ext (hsmul c f) }
  { toLinearMap := Φ
    cont := show Continuous Φ by
      refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i => ?_)
      by_cases hi : i <= n₂
      · obtain ⟨s, C, hC, h⟩ := hbound i hi
        exact ⟨s, C, fun f => ((Φ f).seminorm_le_iff 𝕜 (mul_nonneg hC (apply_nonneg _ _)) i).2
          fun _ x hx => h f x hx⟩
      · exact ⟨∅, 0, fun f => by
          simp [ContDiffMapSupportedIn.seminorm_eq_bot_of_gt 𝕜 (not_le.1 hi)]⟩ }

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def mkCLMtoNormedSpace {G : Type*} [NormedAddCommGroup G]
  body: letI Φ : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] G := ⟨⟨A, hadd⟩, hsmul⟩
  { toLinearMap := Φ
    cont := show Continuous Φ by
      obtain ⟨s, C, hC, h⟩ := hbound
      exact continuous_normedSpace_rng G (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K)
        Φ ⟨s, ⟨C, hC⟩, h⟩ }

中文:
定义 noncomputable
  签名: def mkCLMtoNormedSpace {G : 类型} [赋范交换加群 G]
  定义体: letI Φ : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] G := ⟨⟨A, hadd⟩, hsmul⟩
  { toLinearMap := Φ
    cont := show Continuous Φ by
      obtain ⟨s, C, hC, h⟩ := hbound
      exact continuous_normedSpace_rng G (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K)
        Φ ⟨s, ⟨C, hC⟩, h⟩ }
-/
protected noncomputable def mkCLMtoNormedSpace {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (A : 𝓓^{n}_{K}(E, F) -> G)
    (hadd : forall f g, A (f + g) = A f + A g)
    (hsmul : forall (c : 𝕜) f, A (c • f) = c • A f)
    (hbound : exists (s : Finset Nat) (C : Real), 0 <= C ∧ forall f,
      ‖A f‖ <= C * (s.sup fun i => N[𝕜]_{K, n, i}) f) :
    𝓓^{n}_{K}(E, F) ->L[𝕜] G :=
  letI Φ : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] G := ⟨⟨A, hadd⟩, hsmul⟩
  { toLinearMap := Φ
    cont := show Continuous Φ by
      obtain ⟨s, C, hC, h⟩ := hbound
      exact continuous_normedSpace_rng G (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K)
        Φ ⟨s, ⟨C, hC⟩, h⟩ }

/--
Definition of `toBoundedContinuousFunctionCLM` / `toBoundedContinuousFunctionCLM` 的定义

English:
definition toBoundedContinuousFunctionCLM
  signature: : 𝓓^{n}_{K}(E, F) ->L[𝕜] E ->ᵇ F where
  body: toBoundedContinuousFunctionLM 𝕜
  cont := show Continuous (toBoundedContinuousFunctionLM 𝕜) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (norm_withSeminorms 𝕜 _) _ (fun _ => ⟨{0}, 1, fun f => ?_⟩)
    simp [norm_toBoundedContinuousFunction 𝕜 f]

@[simp]

中文:
定义 toBoundedContinuousFunctionCLM
  签名: : 𝓓^{n}_{K}(E, F) ->L[𝕜] E ->ᵇ F where
  定义体: toBoundedContinuousFunctionLM 𝕜
  cont := show Continuous (toBoundedContinuousFunctionLM 𝕜) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (norm_withSeminorms 𝕜 _) _ (fun _ => ⟨{0}, 1, fun f => ?_⟩)
    simp [norm_toBoundedContinuousFunction 𝕜 f]

@[simp]

Depends on / 依赖: toBoundedContinuousFunctionLM
-/
noncomputable def toBoundedContinuousFunctionCLM : 𝓓^{n}_{K}(E, F) ->L[𝕜] E ->ᵇ F where
  toLinearMap := toBoundedContinuousFunctionLM 𝕜
  cont := show Continuous (toBoundedContinuousFunctionLM 𝕜) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (norm_withSeminorms 𝕜 _) _ (fun _ => ⟨{0}, 1, fun f => ?_⟩)
    simp [norm_toBoundedContinuousFunction 𝕜 f]

@[simp]
/--
lemma `toBoundedContinuousFunctionCLM_apply` / 引理 `toBoundedContinuousFunctionCLM_apply`

English:
lemma toBoundedContinuousFunctionCLM_apply
  given: (f : 𝓓^{n}_{K}(E, F))
  proof: rfl

中文:
引理 toBoundedContinuousFunctionCLM_apply
  条件: (f : 𝓓^{n}_{K}(E, F))
  证明: rfl
-/
lemma toBoundedContinuousFunctionCLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    toBoundedContinuousFunctionCLM 𝕜 f = f :=
  rfl

/--
lemma `toBoundedContinuousFunctionCLM_eq_of_scalars` / 引理 `toBoundedContinuousFunctionCLM_eq_of_scalars`

English:
lemma toBoundedContinuousFunctionCLM_eq_of_scalars
  statement: (𝕜' : Type*) [NontriviallyNormedField 𝕜']
  proof: rfl

中文:
引理 toBoundedContinuousFunctionCLM_eq_of_scalars
  结论: (𝕜' : 类型) [NontriviallyNormedField 𝕜']
  证明: rfl

Depends on / 依赖: SeminormedGroup, seminormedGroup
-/
lemma toBoundedContinuousFunctionCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] :
    (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n}_{K}(E, F) -> _) = toBoundedContinuousFunctionCLM 𝕜' :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousEval 𝓓^{n}_{K}(E, F) E F
  body: ContinuousEval.of_continuous_forget
    (toBoundedContinuousFunctionCLM Real).continuous

中文:
实例 :
  签名: 余ntinuousEval 𝓓^{n}_{K}(E, F) E F
  定义体: ContinuousEval.of_continuous_forget
    (toBoundedContinuousFunctionCLM Real).continuous

Depends on / 依赖: ContinuousEval, ContinuousEval.of_continuous_forget, SeminormedCommGroup, continuous, of_continuous_forget, seminormedCommGroup, toBoundedContinuousFunctionCLM
-/
instance : ContinuousEval 𝓓^{n}_{K}(E, F) E F :=
  ContinuousEval.of_continuous_forget
    (toBoundedContinuousFunctionCLM Real).continuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T3Space 𝓓^{n}_{K}(E, F)
  body: have : Injective (toBoundedContinuousFunctionCLM Real : 𝓓^{n}_{K}(E, F) ->L[Real] E ->ᵇ F) :=
    fun _ _ hfg => ext fun x => congr(($hfg : E -> F) x)
  have : T2Space 𝓓^{n}_{K}(E, F) := .of_injective_continuous this
    (toBoundedContinuousFunctionCLM Real).continuous
  inferInstance

中文:
实例 :
  签名: T3空间 𝓓^{n}_{K}(E, F)
  定义体: have : Injective (toBoundedContinuousFunctionCLM Real : 𝓓^{n}_{K}(E, F) ->L[Real] E ->ᵇ F) :=
    fun _ _ hfg => ext fun x => congr(($hfg : E -> F) x)
  have : T2Space 𝓓^{n}_{K}(E, F) := .of_injective_continuous this
    (toBoundedContinuousFunctionCLM Real).continuous
  inferInstance

Depends on / 依赖: Injective, NormedGroup, T2Space, continuous, normedGroup, of_injective_continuous, toBoundedContinuousFunctionCLM
-/
instance : T3Space 𝓓^{n}_{K}(E, F) :=
  have : Injective (toBoundedContinuousFunctionCLM Real : 𝓓^{n}_{K}(E, F) ->L[Real] E ->ᵇ F) :=
    fun _ _ hfg => ext fun x => congr(($hfg : E -> F) x)
  have : T2Space 𝓓^{n}_{K}(E, F) := .of_injective_continuous this
    (toBoundedContinuousFunctionCLM Real).continuous
  inferInstance

/--
theorem `seminorm_postcompLM_le` / 定理 `seminorm_postcompLM_le`

English:
theorem seminorm_postcompLM_le
  statement: [LinearMap.CompatibleSMul F F' Real 𝕜] {i : Nat} (T : F ->L[𝕜] F')
  proof: by
  set T' := T.restrictScalars Real
  change N[Real]_{K, n, i} (postcompLM T' f) <= ‖T'‖ * N[Real]_{K, n, i} f
  rw [ContDiffMapSupportedIn.seminorm_le_iff Real (by positivity)]
  intro hi x hx
  rw [postcompLM_apply]
  calc
      ‖iteratedFDeriv Real i (T' ∘ f) x‖
  _ = ‖T'.compContinuousMultilin

中文:
定理 seminorm_postcompLM_le
  结论: [线性映射.余mpatibleSMul F F' 实数 𝕜] {i : 自然数} (T : F ->L[𝕜] F')
  证明: by
  set T' := T.restrictScalars Real
  change N[Real]_{K, n, i} (postcompLM T' f) <= ‖T'‖ * N[Real]_{K, n, i} f
  rw [ContDiffMapSupportedIn.seminorm_le_iff Real (by positivity)]
  intro hi x hx
  rw [postcompLM_apply]
  calc
      ‖iteratedFDeriv Real i (T' ∘ f) x‖
  _ = ‖T'.compContinuousMultilin

Depends on / 依赖: ContDiffMapSupportedIn, ContDiffMapSupportedIn.seminorm_le_iff, NormedCommGroup, T.restrictScalars, compContinuousMultilinearMap, contDiff, contDiffAt, f.contDiff.contDiffAt, iteratedFDeriv, iteratedFDeriv_comp_left, mod_cast, norm_compContinuousMultilinearMap_le, normedCommGroup, postcompLM, postcompLM_apply, restrictScalars, seminorm_le_iff
-/
theorem seminorm_postcompLM_le [LinearMap.CompatibleSMul F F' Real 𝕜] {i : Nat} (T : F ->L[𝕜] F')
    (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} (postcompLM T f) <= ‖T‖ * N[𝕜]_{K, n, i} f := by
  set T' := T.restrictScalars Real
  change N[Real]_{K, n, i} (postcompLM T' f) <= ‖T'‖ * N[Real]_{K, n, i} f
  rw [ContDiffMapSupportedIn.seminorm_le_iff Real (by positivity)]
  intro hi x hx
  rw [postcompLM_apply]
  calc
      ‖iteratedFDeriv Real i (T' ∘ f) x‖
  _ = ‖T'.compContinuousMultilinearMap (iteratedFDeriv Real i f x)‖ := by
        rw [T'.iteratedFDeriv_comp_left f.contDiff.contDiffAt (mod_cast hi)]
  _ <= ‖T'‖ * ‖iteratedFDeriv Real i f x‖ := T'.norm_compContinuousMultilinearMap_le _
  _ <= ‖T'‖ * N[Real]_{K, n, i} f := by grw [norm_iteratedFDeriv_apply_le_seminorm Real hi]

variable {𝕜} in
-- Note: generalizing this to a semilinear setting would require a semilinear version of
-- `CompatibleSMul`.
/--
Definition of `postcompCLM` / `postcompCLM` 的定义

English:
definition postcompCLM
  signature: [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F')
  body: postcompLM T
  cont := show Continuous (postcompLM T) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i => ⟨{i}, ‖T‖, fun f => ?_⟩)
    simpa using seminorm_postcompLM_le 𝕜 T f

@[simp]

中文:
定义 postcompCLM
  签名: [线性映射.余mpatibleSMul F F' 实数 𝕜] (T : F ->L[𝕜] F')
  定义体: postcompLM T
  cont := show Continuous (postcompLM T) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i => ⟨{i}, ‖T‖, fun f => ?_⟩)
    simpa using seminorm_postcompLM_le 𝕜 T f

@[simp]

Depends on / 依赖: postcompLM
-/
noncomputable def postcompCLM [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F') :
    𝓓^{n}_{K}(E, F) ->L[𝕜] 𝓓^{n}_{K}(E, F') where
  toLinearMap := postcompLM T
  cont := show Continuous (postcompLM T) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i => ⟨{i}, ‖T‖, fun f => ?_⟩)
    simpa using seminorm_postcompLM_le 𝕜 T f

@[simp]
/--
lemma `postcompCLM_apply` / 引理 `postcompCLM_apply`

English:
lemma postcompCLM_apply
  statement: [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F')
  proof: rfl

中文:
引理 postcompCLM_apply
  结论: [线性映射.余mpatibleSMul F F' 实数 𝕜] (T : F ->L[𝕜] F')
  证明: rfl
-/
lemma postcompCLM_apply [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F')
    (f : 𝓓^{n}_{K}(E, F)) :
    postcompCLM T f = T ∘ f :=
  rfl

/--
theorem `seminorm_monoLM_le` / 定理 `seminorm_monoLM_le`

English:
theorem seminorm_monoLM_le
  given: {i : Nat} (f : 𝓓^{n₁}_{K₁}(E, F))
  proof: by
  by_cases H : n₂ <= n₁ ∧ K₁ <= K₂
  · simp (discharger := positivity) only [ContDiffMapSupportedIn.seminorm_le_iff, monoLM_apply, H,
      and_self, ↓reduceIte]
    intro hik _ _
    exact norm_iteratedFDeriv_apply_le_seminorm _ (hik.trans (mod_cast H.1))
  · simp [monoLM_eq_zero, H]

中文:
定理 seminorm_monoLM_le
  条件: {i : 自然数} (f : 𝓓^{n₁}_{K₁}(E, F))
  证明: by
  by_cases H : n₂ <= n₁ ∧ K₁ <= K₂
  · simp (discharger := positivity) only [ContDiffMapSupportedIn.seminorm_le_iff, monoLM_apply, H,
      and_self, ↓reduceIte]
    intro hik _ _
    exact norm_iteratedFDeriv_apply_le_seminorm _ (hik.trans (mod_cast H.1))
  · simp [monoLM_eq_zero, H]

Depends on / 依赖: ContDiffMapSupportedIn, ContDiffMapSupportedIn.seminorm_le_iff, and_self, discharger, hik.trans, mod_cast, monoLM_apply, monoLM_eq_zero, norm_iteratedFDeriv_apply_le_seminorm, reduceIte, seminorm_le_iff
-/
theorem seminorm_monoLM_le {i : Nat} (f : 𝓓^{n₁}_{K₁}(E, F)) :
    N[𝕜]_{K₂, n₂, i} (monoLM 𝕜 f) <= N[𝕜]_{K₁, n₁, i} f := by
  by_cases H : n₂ <= n₁ ∧ K₁ <= K₂
  · simp (discharger := positivity) only [ContDiffMapSupportedIn.seminorm_le_iff, monoLM_apply, H,
      and_self, ↓reduceIte]
    intro hik _ _
    exact norm_iteratedFDeriv_apply_le_seminorm _ (hik.trans (mod_cast H.1))
  · simp [monoLM_eq_zero, H]

/--
theorem `seminorm_monoLM_eq` / 定理 `seminorm_monoLM_eq`

English:
theorem seminorm_monoLM_eq
  given: {i : Nat} (h₁ : n₁ = n₂) (h₂ : K₁ <= K₂) (f : 𝓓^{n₁}_{K₁}(E, F))
  proof: by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm, ContDiffMapSupportedIn.seminorm_apply,
    structureMapCLM_apply, h₁, h₂]

中文:
定理 seminorm_monoLM_eq
  条件: {i : 自然数} (h₁ : n₁ = n₂) (h₂ : K₁ <= K₂) (f : 𝓓^{n₁}_{K₁}(E, F))
  证明: by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm, ContDiffMapSupportedIn.seminorm_apply,
    structureMapCLM_apply, h₁, h₂]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_eq_iSup_norm, ContDiffMapSupportedIn, ContDiffMapSupportedIn.seminorm_apply, norm_eq_iSup_norm, seminorm_apply, structureMapCLM_apply
-/
theorem seminorm_monoLM_eq {i : Nat} (h₁ : n₁ = n₂) (h₂ : K₁ <= K₂) (f : 𝓓^{n₁}_{K₁}(E, F)) :
    N[𝕜]_{K₂, n₂, i} (monoLM 𝕜 f) = N[𝕜]_{K₁, n₁, i} f := by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm, ContDiffMapSupportedIn.seminorm_apply,
    structureMapCLM_apply, h₁, h₂]

/--
Definition of `monoCLM` / `monoCLM` 的定义

English:
definition monoCLM
  signature: :
  body: monoLM 𝕜
  cont := show Continuous (monoLM 𝕜) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
      (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _) _ (fun i => ⟨{i}, 1, fun f => ?_⟩)
    simpa using seminorm_monoLM_le 𝕜 f

中文:
定义 monoCLM
  签名: :
  定义体: monoLM 𝕜
  cont := show Continuous (monoLM 𝕜) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
      (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _) _ (fun i => ⟨{i}, 1, fun f => ?_⟩)
    simpa using seminorm_monoLM_le 𝕜 f

Depends on / 依赖: monoLM
-/
noncomputable def monoCLM :
    𝓓^{n₁}_{K₁}(E, F) ->L[𝕜] 𝓓^{n₂}_{K₂}(E, F) where
  toLinearMap := monoLM 𝕜
  cont := show Continuous (monoLM 𝕜) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
      (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _) _ (fun i => ⟨{i}, 1, fun f => ?_⟩)
    simpa using seminorm_monoLM_le 𝕜 f

open scoped Classical in
@[simp]
/--
lemma `monoCLM_apply` / 引理 `monoCLM_apply`

English:
lemma monoCLM_apply
  given: (f : 𝓓^{n₁}_{K₁}(E, F))
  proof: monoLM_apply 𝕜 f

中文:
引理 monoCLM_apply
  条件: (f : 𝓓^{n₁}_{K₁}(E, F))
  证明: monoLM_apply 𝕜 f

Depends on / 依赖: monoLM_apply
-/
lemma monoCLM_apply (f : 𝓓^{n₁}_{K₁}(E, F)) :
    ((monoCLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F)) : E -> F) = if n₂ <= n₁ ∧ K₁ <= K₂ then f else 0 :=
  monoLM_apply 𝕜 f

/--
lemma `monoCLM_eq_zero` / 引理 `monoCLM_eq_zero`

English:
lemma monoCLM_eq_zero
  given: (H : ¬ (n₂ <= n₁ ∧ K₁ <= K₂))
  proof: by
  ext; simp [H]

中文:
引理 monoCLM_eq_zero
  条件: (H : ¬ (n₂ <= n₁ ∧ K₁ <= K₂))
  证明: by
  ext; simp [H]
-/
lemma monoCLM_eq_zero (H : ¬ (n₂ <= n₁ ∧ K₁ <= K₂)) :
    (monoCLM 𝕜 : 𝓓^{n₁}_{K₁}(E, F) ->L[𝕜] 𝓓^{n₂}_{K₂}(E, F)) = 0 := by
  ext; simp [H]

/--
lemma `monoCLM_eq_of_scalars` / 引理 `monoCLM_eq_of_scalars`

English:
lemma monoCLM_eq_of_scalars
  statement: (𝕜' : Type*)
  proof: rfl

中文:
引理 monoCLM_eq_of_scalars
  结论: (𝕜' : 类型)
  证明: rfl
-/
lemma monoCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] :
    (monoCLM 𝕜 : 𝓓^{n₁}_{K₁}(E, F) -> 𝓓^{n₂}_{K₂}(E, F)) = monoCLM 𝕜' :=
  rfl

/--
theorem `seminorm_fderivLM_le` / 定理 `seminorm_fderivLM_le`

English:
theorem seminorm_fderivLM_le
  given: {i : Nat} (f : 𝓓^{n}_{K}(E, F))
  proof: by
  by_cases! hk : k + 1 <= n
  · rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 (apply_nonneg ..)]
    intro hi x hx
    have hi' : i + 1 <= n := (add_le_add_left hi 1).trans hk
    simpa [hk, norm_iteratedFDeriv_fderiv] using
      norm_iteratedFDeriv_apply_le_seminorm 𝕜 hi'
  · simp [fderivLM_appl

中文:
定理 seminorm_fderivLM_le
  条件: {i : 自然数} (f : 𝓓^{n}_{K}(E, F))
  证明: by
  by_cases! hk : k + 1 <= n
  · rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 (apply_nonneg ..)]
    intro hi x hx
    have hi' : i + 1 <= n := (add_le_add_left hi 1).trans hk
    simpa [hk, norm_iteratedFDeriv_fderiv] using
      norm_iteratedFDeriv_apply_le_seminorm 𝕜 hi'
  · simp [fderivLM_appl

Depends on / 依赖: ContDiffMapSupportedIn, ContDiffMapSupportedIn.seminorm_le_iff, add_le_add_left, apply_nonneg, fderivLM_apply_of_gt, norm_iteratedFDeriv_apply_le_seminorm, norm_iteratedFDeriv_fderiv, seminorm_le_iff
-/
theorem seminorm_fderivLM_le {i : Nat} (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, k, i} (fderivLM 𝕜 n k f) <= N[𝕜]_{K, n, i + 1} f := by
  by_cases! hk : k + 1 <= n
  · rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 (apply_nonneg ..)]
    intro hi x hx
    have hi' : i + 1 <= n := (add_le_add_left hi 1).trans hk
    simpa [hk, norm_iteratedFDeriv_fderiv] using
      norm_iteratedFDeriv_apply_le_seminorm 𝕜 hi'
  · simp [fderivLM_apply_of_gt 𝕜 f hk]

/--
theorem `seminorm_fderivLM_top` / 定理 `seminorm_fderivLM_top`

English:
theorem seminorm_fderivLM_top
  given: {i : Nat} (f : 𝓓_{K}(E, F))
  proof: by
  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.norm_eq_iSup_norm,
    norm_iteratedFDeriv_fderiv]

中文:
定理 seminorm_fderivLM_top
  条件: {i : 自然数} (f : 𝓓_{K}(E, F))
  证明: by
  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.norm_eq_iSup_norm,
    norm_iteratedFDeriv_fderiv]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_eq_iSup_norm, ContDiffMapSupportedIn, ContDiffMapSupportedIn.seminorm_apply, norm_eq_iSup_norm, norm_iteratedFDeriv_fderiv, seminorm_apply
-/
theorem seminorm_fderivLM_top {i : Nat} (f : 𝓓_{K}(E, F)) :
    N[𝕜]_{K, i} (fderivLM 𝕜 ⊤ ⊤ f) = N[𝕜]_{K, i + 1} f := by
  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.norm_eq_iSup_norm,
    norm_iteratedFDeriv_fderiv]

variable (n k) in
/--
Definition of `fderivCLM` / `fderivCLM` 的定义

English:
definition fderivCLM
  signature: :
  body: fderivLM 𝕜 n k
  cont := show Continuous (fderivLM 𝕜 n k) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (fun i => ⟨{i+1}, 1, fun f => ?_⟩)
    simpa using seminorm_fderivLM_le 𝕜 f

@[simp]

中文:
定义 fderivCLM
  签名: :
  定义体: fderivLM 𝕜 n k
  cont := show Continuous (fderivLM 𝕜 n k) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (fun i => ⟨{i+1}, 1, fun f => ?_⟩)
    simpa using seminorm_fderivLM_le 𝕜 f

@[simp]

Depends on / 依赖: fderivLM
-/
noncomputable def fderivCLM :
    𝓓^{n}_{K}(E, F) ->L[𝕜] 𝓓^{k}_{K}(E, E ->L[Real] F) where
  toLinearMap := fderivLM 𝕜 n k
  cont := show Continuous (fderivLM 𝕜 n k) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (fun i => ⟨{i+1}, 1, fun f => ?_⟩)
    simpa using seminorm_fderivLM_le 𝕜 f

@[simp]
/--
lemma `fderivCLM_apply` / 引理 `fderivCLM_apply`

English:
lemma fderivCLM_apply
  given: (f : 𝓓^{n}_{K}(E, F))
  proof: fderivLM_apply 𝕜 f

中文:
引理 fderivCLM_apply
  条件: (f : 𝓓^{n}_{K}(E, F))
  证明: fderivLM_apply 𝕜 f

Depends on / 依赖: fderivLM_apply
-/
lemma fderivCLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    fderivCLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0 :=
  fderivLM_apply 𝕜 f

/--
lemma `fderivCLM_apply_of_le` / 引理 `fderivCLM_apply_of_le`

English:
lemma fderivCLM_apply_of_le
  given: (f : 𝓓^{n}_{K}(E, F)) (hk : k + 1 <= n)
  proof: fderivLM_apply_of_le 𝕜 f hk

中文:
引理 fderivCLM_apply_of_le
  条件: (f : 𝓓^{n}_{K}(E, F)) (hk : k + 1 <= n)
  证明: fderivLM_apply_of_le 𝕜 f hk

Depends on / 依赖: fderivLM_apply_of_le
-/
lemma fderivCLM_apply_of_le (f : 𝓓^{n}_{K}(E, F)) (hk : k + 1 <= n) :
    fderivCLM 𝕜 n k f = fderiv Real f :=
  fderivLM_apply_of_le 𝕜 f hk

/--
lemma `fderivCLM_apply_of_gt` / 引理 `fderivCLM_apply_of_gt`

English:
lemma fderivCLM_apply_of_gt
  given: (f : 𝓓^{n}_{K}(E, F)) (hk : n < k + 1)
  proof: fderivLM_apply_of_gt 𝕜 f hk

中文:
引理 fderivCLM_apply_of_gt
  条件: (f : 𝓓^{n}_{K}(E, F)) (hk : n < k + 1)
  证明: fderivLM_apply_of_gt 𝕜 f hk

Depends on / 依赖: fderivLM_apply_of_gt
-/
lemma fderivCLM_apply_of_gt (f : 𝓓^{n}_{K}(E, F)) (hk : n < k + 1) :
    fderivCLM 𝕜 n k f = 0 :=
  fderivLM_apply_of_gt 𝕜 f hk

/--
lemma `fderivCLM_eq_of_scalars` / 引理 `fderivCLM_eq_of_scalars`

English:
lemma fderivCLM_eq_of_scalars
  statement: (𝕜' : Type*) [NontriviallyNormedField 𝕜']
  proof: rfl

中文:
引理 fderivCLM_eq_of_scalars
  结论: (𝕜' : 类型) [NontriviallyNormedField 𝕜']
  证明: rfl
-/
lemma fderivCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] :
    (fderivCLM 𝕜 n k : 𝓓^{n}_{K}(E, F) -> _) = fderivCLM 𝕜' n k :=
  rfl

end Topology

section Integral

open MeasureTheory

variable {𝕜} {m : MeasurableSpace E} [OpensMeasurableSpace E] {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedSpace Real F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]

@[fun_prop]
/--
theorem `stronglyMeasurable` / 定理 `stronglyMeasurable`

English:
theorem stronglyMeasurable
  given: (f : 𝓓^{n}_{K}(E, F))
  proof: by
  exact f.continuous.stronglyMeasurable_of_hasCompactSupport f.hasCompactSupport

@[fun_prop]

中文:
定理 stronglyMeasurable
  条件: (f : 𝓓^{n}_{K}(E, F))
  证明: by
  exact f.continuous.stronglyMeasurable_of_hasCompactSupport f.hasCompactSupport

@[fun_prop]
-/
protected theorem stronglyMeasurable (f : 𝓓^{n}_{K}(E, F)) :
    StronglyMeasurable f := by
  exact f.continuous.stronglyMeasurable_of_hasCompactSupport f.hasCompactSupport

@[fun_prop]
/--
theorem `aestronglyMeasurable` / 定理 `aestronglyMeasurable`

English:
theorem aestronglyMeasurable
  given: {μ : Measure E} (f : 𝓓^{n}_{K}(E, F))
  proof: f.stronglyMeasurable.aestronglyMeasurable

中文:
定理 aestronglyMeasurable
  条件: {μ : 测度 E} (f : 𝓓^{n}_{K}(E, F))
  证明: f.stronglyMeasurable.aestronglyMeasurable
-/
protected theorem aestronglyMeasurable {μ : Measure E} (f : 𝓓^{n}_{K}(E, F)) :
    AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

/--
theorem `memLp_top` / 定理 `memLp_top`

English:
theorem memLp_top
  given: {μ : Measure E} (f : 𝓓^{n}_{K}(E, F))
  proof: f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport μ

中文:
定理 memLp_top
  条件: {μ : 测度 E} (f : 𝓓^{n}_{K}(E, F))
  证明: f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport μ
-/
protected theorem memLp_top {μ : Measure E} (f : 𝓓^{n}_{K}(E, F)) :
    MemLp f ⊤ μ :=
  f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport μ

/--
theorem `integrable` / 定理 `integrable`

English:
theorem integrable
  statement: {μ : Measure E} [μ_finite : IsFiniteMeasure (μ.restrict K)]
  proof: by
  rw [← integrableOn_iff_integrable_of_support_subset f.support_subset]
  exact f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

中文:
定理 integrable
  结论: {μ : 测度 E} [μ_finite : 是有限测度 (μ.restrict K)]
  证明: by
  rw [← integrableOn_iff_integrable_of_support_subset f.support_subset]
  exact f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
-/
protected theorem integrable {μ : Measure E} [μ_finite : IsFiniteMeasure (μ.restrict K)]
    (f : 𝓓^{n}_{K}(E, F)) :
    Integrable f μ := by
  rw [← integrableOn_iff_integrable_of_support_subset f.support_subset]
  exact f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

/--
theorem `integrable_bilin` / 定理 `integrable_bilin`

English:
theorem integrable_bilin
  statement: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {μ : Measure E} {φ : E -> F₂}
  proof: by
  suffices IntegrableOn (fun x => B (f x) (φ x)) K μ by
    rwa [integrableOn_iff_integrable_of_support_subset] at this
    refine subset_trans ?_ f.support_subset
    exact fun x hx hfx => hx (by simp [hfx])
  rw [IntegrableOn]; rw [← memLp_one_iff_integrable] at hφ ⊢
  exact B.memLp_of_bilin 1 

中文:
定理 integrable_bilin
  结论: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {μ : 测度 E} {φ : E -> F₂}
  证明: by
  suffices IntegrableOn (fun x => B (f x) (φ x)) K μ by
    rwa [integrableOn_iff_integrable_of_support_subset] at this
    refine subset_trans ?_ f.support_subset
    exact fun x hx hfx => hx (by simp [hfx])
  rw [IntegrableOn]; rw [← memLp_one_iff_integrable] at hφ ⊢
  exact B.memLp_of_bilin 1 
-/
protected theorem integrable_bilin (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {μ : Measure E} {φ : E -> F₂}
    (hφ : IntegrableOn φ K μ) (f : 𝓓^{n}_{K}(E, F₁)) :
    Integrable (fun x => B (f x) (φ x)) μ := by
  suffices IntegrableOn (fun x => B (f x) (φ x)) K μ by
    rwa [integrableOn_iff_integrable_of_support_subset] at this
    refine subset_trans ?_ f.support_subset
    exact fun x hx hfx => hx (by simp [hfx])
  rw [IntegrableOn]; rw [← memLp_one_iff_integrable] at hφ ⊢
  exact B.memLp_of_bilin 1 f.memLp_top hφ

variable [SMulCommClass Real 𝕜 F₁] [NormedSpace Real F₃] [SMulCommClass Real 𝕜 F₃]

-- TODO: semilinearize
/--
Definition of `integralAgainstBilinLM` / `integralAgainstBilinLM` 的定义

English:
definition integralAgainstBilinLM
  signature: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : Measure E) (φ : E -> F₂)
  body: open scoped Classical in
    if IntegrableOn φ K μ then ∫ x, B (f x) (φ x) ∂μ else 0
  map_add' f g := by
    split_ifs with hφ
    · simp_rw [add_apply, map_add, add_apply,
        integral_add (f.integrable_bilin B hφ) (g.integrable_bilin B hφ)]
    · simp
  map_smul' c f := by
    split_ifs with 

中文:
定义 integralAgainstBilinLM
  签名: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : 测度 E) (φ : E -> F₂)
  定义体: open scoped Classical in
    if IntegrableOn φ K μ then ∫ x, B (f x) (φ x) ∂μ else 0
  map_add' f g := by
    split_ifs with hφ
    · simp_rw [add_apply, map_add, add_apply,
        integral_add (f.integrable_bilin B hφ) (g.integrable_bilin B hφ)]
    · simp
  map_smul' c f := by
    split_ifs with 

Depends on / 依赖: Classical, scoped
-/
noncomputable def integralAgainstBilinLM (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : Measure E) (φ : E -> F₂) :
    𝓓^{n}_{K}(E, F₁) ->ₗ[𝕜] F₃ where
  toFun f := open scoped Classical in
    if IntegrableOn φ K μ then ∫ x, B (f x) (φ x) ∂μ else 0
  map_add' f g := by
    split_ifs with hφ
    · simp_rw [add_apply, map_add, add_apply,
        integral_add (f.integrable_bilin B hφ) (g.integrable_bilin B hφ)]
    · simp
  map_smul' c f := by
    split_ifs with hφ
    · simp_rw [smul_apply, map_smul, smul_apply, integral_smul c, RingHom.id_apply]
    · simp

@[simp]
/--
lemma `integralAgainstBilinLM_apply` / 引理 `integralAgainstBilinLM_apply`

English:
lemma integralAgainstBilinLM_apply
  statement: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
  proof: by
  rfl

中文:
引理 integralAgainstBilinLM_apply
  结论: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : 测度 E} {φ : E -> F₂}
  证明: by
  rfl
-/
lemma integralAgainstBilinLM_apply {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
    {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinLM B μ φ f = open scoped Classical in
      if IntegrableOn φ K μ then ∫ x, B (f x) (φ x) ∂μ else 0 := by
  rfl

/--
lemma `integralAgainstBilinLM_eq_integral` / 引理 `integralAgainstBilinLM_eq_integral`

English:
lemma integralAgainstBilinLM_eq_integral
  statement: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
  proof: by
  simp [hφ]

中文:
引理 integralAgainstBilinLM_eq_integral
  结论: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : 测度 E} {φ : E -> F₂}
  证明: by
  simp [hφ]
-/
lemma integralAgainstBilinLM_eq_integral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
    (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinLM B μ φ f = ∫ x, B (f x) (φ x) ∂μ := by
  simp [hφ]

/--
lemma `integralAgainstBilinLM_eq_setIntegral` / 引理 `integralAgainstBilinLM_eq_setIntegral`

English:
lemma integralAgainstBilinLM_eq_setIntegral
  statement: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
  proof: by
  rw [integralAgainstBilinLM_eq_integral hφ]; rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [f.zero_on_compl hx]; rw [Pi.zero_apply]; rw [map_zero]; rw [zero_apply]

中文:
引理 integralAgainstBilinLM_eq_set整数egral
  结论: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : 测度 E} {φ : E -> F₂}
  证明: by
  rw [integralAgainstBilinLM_eq_integral hφ]; rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [f.zero_on_compl hx]; rw [Pi.zero_apply]; rw [map_zero]; rw [zero_apply]

Depends on / 依赖: Pi.zero_apply, f.zero_on_compl, integralAgainstBilinLM_eq_integral, map_zero, setIntegral_eq_integral_of_forall_compl_eq_zero, zero_apply, zero_on_compl
-/
lemma integralAgainstBilinLM_eq_setIntegral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
    (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinLM B μ φ f = ∫ x in K, B (f x) (φ x) ∂μ := by
  rw [integralAgainstBilinLM_eq_integral hφ]; rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [f.zero_on_compl hx]; rw [Pi.zero_apply]; rw [map_zero]; rw [zero_apply]

/--
lemma `norm_integralAgainstBilinLM_le` / 引理 `norm_integralAgainstBilinLM_le`

English:
lemma norm_integralAgainstBilinLM_le
  statement: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
  proof: by
  by_cases hφ : IntegrableOn φ K μ
  · have h : forallᵐ x ∂(μ.restrict K), ‖B (f x) (φ x)‖ <= ‖φ x‖ * ‖B‖ * N[𝕜]_{K, n, 0} f := by
      filter_upwards [] with x
      grw [ContinuousLinearMap.le_opNorm, ContinuousLinearMap.le_opNorm, norm_apply_le_seminorm 𝕜,
        mul_comm, mul_assoc]
    rw 

中文:
引理 norm_integralAgainstBilinLM_le
  结论: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : 测度 E} {φ : E -> F₂}
  证明: by
  by_cases hφ : IntegrableOn φ K μ
  · have h : forallᵐ x ∂(μ.restrict K), ‖B (f x) (φ x)‖ <= ‖φ x‖ * ‖B‖ * N[𝕜]_{K, n, 0} f := by
      filter_upwards [] with x
      grw [ContinuousLinearMap.le_opNorm, ContinuousLinearMap.le_opNorm, norm_apply_le_seminorm 𝕜,
        mul_comm, mul_assoc]
    rw 

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.le_opNorm, IntegrableOn, filter_upwards, integralAgainstBilinLM, integralAgainstBilinLM_eq_setIntegral, integral_mul_const, le_opNorm, le_trans, mul_assoc, mul_comm, mul_const, norm.mul_const, norm_apply_le_seminorm, norm_integral_le_of_norm_le, reduceIte, restrict
-/
lemma norm_integralAgainstBilinLM_le {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
    {f : 𝓓^{n}_{K}(E, F₁)} :
    ‖integralAgainstBilinLM B μ φ f‖ <=
      (∫ x in K, ‖φ x‖ ∂μ) * ‖B‖ * N[𝕜]_{K, n, 0} f := by
  by_cases hφ : IntegrableOn φ K μ
  · have h : forallᵐ x ∂(μ.restrict K), ‖B (f x) (φ x)‖ <= ‖φ x‖ * ‖B‖ * N[𝕜]_{K, n, 0} f := by
      filter_upwards [] with x
      grw [ContinuousLinearMap.le_opNorm, ContinuousLinearMap.le_opNorm, norm_apply_le_seminorm 𝕜,
        mul_comm, mul_assoc]
    rw [integralAgainstBilinLM_eq_setIntegral hφ]
    apply le_trans (norm_integral_le_of_norm_le ((hφ.norm.mul_const _).mul_const _) h)
    rw [integral_mul_const]; rw [integral_mul_const]
  · simp only [integralAgainstBilinLM, hφ, ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk, norm_zero]
    positivity

-- TODO: semilinearize
/--
Definition of `integralAgainstBilinCLM` / `integralAgainstBilinCLM` 的定义

English:
definition integralAgainstBilinCLM
  signature: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : Measure E) (φ : E -> F₂)
  body: ContDiffMapSupportedIn.mkCLMtoNormedSpace 𝕜 (integralAgainstBilinLM B μ φ)
    (integralAgainstBilinLM B μ φ).map_add (integralAgainstBilinLM B μ φ).map_smul
    ⟨{0}, (∫ x in K, ‖φ x‖ ∂μ) * ‖B‖, by positivity,
      fun f => by simpa using! norm_integralAgainstBilinLM_le⟩

@[simp]

中文:
定义 integralAgainstBilinCLM
  签名: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : 测度 E) (φ : E -> F₂)
  定义体: ContDiffMapSupportedIn.mkCLMtoNormedSpace 𝕜 (integralAgainstBilinLM B μ φ)
    (integralAgainstBilinLM B μ φ).map_add (integralAgainstBilinLM B μ φ).map_smul
    ⟨{0}, (∫ x in K, ‖φ x‖ ∂μ) * ‖B‖, by positivity,
      fun f => by simpa using! norm_integralAgainstBilinLM_le⟩

@[simp]

Depends on / 依赖: ContDiffMapSupportedIn, ContDiffMapSupportedIn.mkCLMtoNormedSpace, integralAgainstBilinLM, map_add, map_smul, mkCLMtoNormedSpace, norm_integralAgainstBilinLM_le
-/
noncomputable def integralAgainstBilinCLM (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : Measure E) (φ : E -> F₂) :
    𝓓^{n}_{K}(E, F₁) ->L[𝕜] F₃ :=
  ContDiffMapSupportedIn.mkCLMtoNormedSpace 𝕜 (integralAgainstBilinLM B μ φ)
    (integralAgainstBilinLM B μ φ).map_add (integralAgainstBilinLM B μ φ).map_smul
    ⟨{0}, (∫ x in K, ‖φ x‖ ∂μ) * ‖B‖, by positivity,
      fun f => by simpa using! norm_integralAgainstBilinLM_le⟩

@[simp]
/--
lemma `integralAgainstBilinCLM_apply` / 引理 `integralAgainstBilinCLM_apply`

English:
lemma integralAgainstBilinCLM_apply
  statement: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
  proof: integralAgainstBilinLM_apply

中文:
引理 integralAgainstBilinCLM_apply
  结论: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : 测度 E} {φ : E -> F₂}
  证明: integralAgainstBilinLM_apply

Depends on / 依赖: integralAgainstBilinLM_apply
-/
lemma integralAgainstBilinCLM_apply {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
    {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinCLM B μ φ f = open scoped Classical in
      if IntegrableOn φ K μ then ∫ x, B (f x) (φ x) ∂μ else 0 :=
  integralAgainstBilinLM_apply

/--
lemma `integralAgainstBilinCLM_eq_integral` / 引理 `integralAgainstBilinCLM_eq_integral`

English:
lemma integralAgainstBilinCLM_eq_integral
  statement: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
  proof: integralAgainstBilinLM_eq_integral hφ

中文:
引理 integralAgainstBilinCLM_eq_integral
  结论: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : 测度 E} {φ : E -> F₂}
  证明: integralAgainstBilinLM_eq_integral hφ

Depends on / 依赖: integralAgainstBilinLM_eq_integral
-/
lemma integralAgainstBilinCLM_eq_integral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
    (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinCLM B μ φ f = ∫ x, B (f x) (φ x) ∂μ :=
  integralAgainstBilinLM_eq_integral hφ

/--
lemma `integralAgainstBilinCLM_eq_setIntegral` / 引理 `integralAgainstBilinCLM_eq_setIntegral`

English:
lemma integralAgainstBilinCLM_eq_setIntegral
  statement: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
  proof: integralAgainstBilinLM_eq_setIntegral hφ

中文:
引理 integralAgainstBilinCLM_eq_set整数egral
  结论: {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : 测度 E} {φ : E -> F₂}
  证明: integralAgainstBilinLM_eq_setIntegral hφ

Depends on / 依赖: integralAgainstBilinLM_eq_setIntegral
-/
lemma integralAgainstBilinCLM_eq_setIntegral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
    (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinCLM B μ φ f = ∫ x in K, B (f x) (φ x) ∂μ :=
  integralAgainstBilinLM_eq_setIntegral hφ

end Integral

section Multiplication

section bilin

open ContDiffMapSupportedIn

variable {F₁ F₂ F₃ G : Type*} [NormedAlgebra Real 𝕜]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedSpace Real F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedSpace Real F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [NormedSpace Real F₃]

open ContinuousLinearMap Finset

variable {𝕜}
/--
Definition of `bilinLeftCLM` / `bilinLeftCLM` 的定义

English:
definition bilinLeftCLM
  signature: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {g : E -> F₂} (hg : ContDiff Real n g)
  body: ContDiffMapSupportedIn.mkCLM 𝕜 (fun φ x => B (φ x) (g x)) ?hadd ?hsmul (fun φ => ?hsmooth)
    (fun φ x hx => ?hsupp) (fun k hk => ?hbound)

中文:
定义 bilinLeftCLM
  签名: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {g : E -> F₂} (hg : 连续可微 实数 n g)
  定义体: ContDiffMapSupportedIn.mkCLM 𝕜 (fun φ x => B (φ x) (g x)) ?hadd ?hsmul (fun φ => ?hsmooth)
    (fun φ x hx => ?hsupp) (fun k hk => ?hbound)

Depends on / 依赖: ContDiffMapSupportedIn, ContDiffMapSupportedIn.mkCLM, hbound, hsmooth
-/
noncomputable def bilinLeftCLM (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {g : E -> F₂} (hg : ContDiff Real n g) :
    𝓓^{n}_{K}(E, F₁) ->L[𝕜] 𝓓^{n}_{K}(E, F₃) :=
  ContDiffMapSupportedIn.mkCLM 𝕜 (fun φ x => B (φ x) (g x)) ?hadd ?hsmul (fun φ => ?hsmooth)
    (fun φ x hx => ?hsupp) (fun k hk => ?hbound)
where finally
  case hadd | hsmul => intros; simp
  case hsmooth =>
    exact (B.bilinearRestrictScalars Real).isBoundedBilinearMap.contDiff.comp (φ.contDiff.prodMk hg)
  case hsupp => simp only [φ.zero_on_compl hx, Pi.zero_apply, map_zero, zero_apply]
  case hbound =>
    have hcont : Continuous fun x => (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
        (fun i => ‖iteratedFDeriv Real i g x‖) :=
      Continuous.finset_sup'_apply Finset.nonempty_range_add_one fun i hi =>
        (hg.continuous_iteratedFDeriv (WithTop.coe_le_coe.2
          (le_trans (WithTop.coe_le_coe.2 (mem_range_succ_iff.mp hi)) hk))).norm
    obtain ⟨C₀, hC₀⟩ := K.isCompact.exists_bound_of_continuousOn hcont.continuousOn
    have hgC₀ : forall i <= k, forall x in K, ‖iteratedFDeriv Real i g x‖ <= ‖C₀‖ := fun i hi x hx =>
      (Finset.le_sup' _ (Finset.mem_range_succ_iff.2 hi)).trans
        ((Real.le_norm_self _).trans ((hC₀ x hx).trans (Real.le_norm_self C₀)))
    refine ⟨Finset.Iic k, ‖B‖ * 2 ^ k * ‖C₀‖, by positivity, fun φ x hx => ?_⟩
    calc
      ‖iteratedFDeriv Real k (fun y => B (φ y) (g y)) x‖
        <= ‖B‖ * ∑ i in Finset.range (k + 1), (k.choose i : Real) * ‖iteratedFDeriv Real i φ x‖ *
            ‖iteratedFDeriv Real (k - i) g x‖ := by
          simpa using (B.bilinearRestrictScalars Real).norm_iteratedFDeriv_le_of_bilinear
            φ.contDiff hg x (mod_cast hk)
      _ <= ‖B‖ * ∑ i in Finset.range (k + 1), (k.choose i : Real) *
            ((Finset.Iic k).sup fun m => N[𝕜]_{K, n, m}) φ * ‖C₀‖ := by
          gcongr with i hi
          · exact (norm_iteratedFDeriv_apply_le_seminorm 𝕜
              ((WithTop.coe_le_coe.2 (mem_range_succ_iff.mp hi)).trans hk)).trans
              (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 (mem_range_succ_iff.mp hi)))
          · exact hgC₀ (k - i) (Nat.sub_le k i) x hx
      _ = ‖B‖ * 2 ^ k * ‖C₀‖ * ((Finset.Iic k).sup fun m => N[𝕜]_{K, n, m}) φ := by
          simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring

@[simp]
/--
theorem `bilinLeftCLM_apply` / 定理 `bilinLeftCLM_apply`

English:
theorem bilinLeftCLM_apply
  statement: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {g : E -> F₂} (hg : ContDiff Real n g)
  proof: rfl

中文:
定理 bilinLeftCLM_apply
  结论: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {g : E -> F₂} (hg : 连续可微 实数 n g)
  证明: rfl
-/
theorem bilinLeftCLM_apply (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {g : E -> F₂} (hg : ContDiff Real n g)
    (φ : 𝓓^{n}_{K}(E, F₁)) : bilinLeftCLM B hg φ = fun x => B (φ x) (g x) := rfl

end bilin

end Multiplication

end ContDiffMapSupportedIn
