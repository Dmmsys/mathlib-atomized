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
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [SMulCommClass ℝ 𝕜 F']
  {n n₁ n₂ k : ℕ∞} {K K₁ K₂ : Compacts E}

/-- The type of bundled `n`-times continuously differentiable maps which vanish outside of a fixed
compact set `K`. -/
/-
**ContDiffMapSupportedIn** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_2) →   (F : Type u_3) →     [inst : NormedAddCommGroup E] →   
    [NormedSpace ℝ E] →         [inst_2 : NormedAddCommGroup F] → [NormedSpace ℝ
 F] → ℕ∞ → TopologicalSpace.Compacts E → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of bundled `n`-times continuously differentiable maps which vanish outs
ide of a fixed
compact set `K`.
-/
structure ContDiffMapSupportedIn (n : ℕ∞) (K : Compacts E) : Type _ where
  /-- The underlying function. Use coercion instead. -/
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
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

/-- `ContDiffMapSupportedInClass B E F n K` states that `B` is a type of bundled `n`-times
continuously differentiable functions with support in the compact set `K`. -/
/-
**ContDiffMapSupportedInClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 →   (E : outParam (Type u_6)) →     (F : outParam (Type u_7)) →  
     [inst : NormedAddCommGroup E] →         [inst_1 : NormedAddCommGroup F] →  
         [NormedSpace ℝ E] →             [NormedSpace ℝ F] → outParam ℕ∞ → outPa
ram (TopologicalSpace.Compacts E) → Type (max (max u_5 u_6) u_7)
参数：E : outParam (Type u_6)；F : outParam (Type u_7)；TopologicalSpace.Compacts E；m
ax (max u_5 u_6) u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContDiffMapSupportedInClass B E F n K` states that `B` is a type of bundled `n`
-times
continuously differentiable functions with support in the compact set `K`.
-/
class ContDiffMapSupportedInClass (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  map_zero_on_compl (f : B) : EqOn f 0 Kᶜ

open ContDiffMapSupportedInClass

namespace ContDiffMapSupportedInClass

/-
**ContDiffMapSupportedInClass.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn
Class`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    [ContDiffMapSupportedInClass B E F n K] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous
/-
**ContDiffMapSupportedInClass.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn
Class`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    [ContDiffMapSupportedInClass B E F n K] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    have := HasCompactSupport.intro K.isCompact (map_zero_on_compl f)
    rcases (map_continuous f).bounded_above_of_compact_support this with ⟨C, hC⟩
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)

end ContDiffMapSupportedInClass

namespace ContDiffMapSupportedIn

/-
**ContDiffMapSupportedIn.toContDiffMapSupportedInClass** 是 Mathlib 中的一个实例，位于命名空间
 `ContDiffMapSupportedIn`。
形式化陈述：toContDiffMapSupportedInClass : ContDiffMapSupportedInClass 𝓓^{n}_{K}(E, F
) E F n K where coe f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffMapSupportedIn.contDiff'`：∀ {E : Type u_2} {F : Type u_3} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup 
F]   [inst_3 : NormedS…
· 使用定理 `ContDiffMapSupportedIn.zero_on_compl'`：∀ {E : Type u_2} {F : Type u_3} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommG
roup F]   [inst_3 : NormedS…
-/
instance toContDiffMapSupportedInClass :
    ContDiffMapSupportedInClass 𝓓^{n}_{K}(E, F) E F n K where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_zero_on_compl f := f.zero_on_compl'

variable {E F F'}
/-
**ContDiffMapSupportedIn.contDiff** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSupporte
dIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} (f : ContDiffMapSupportedIn E F n K),   C
ontDiff ℝ ↑n ⇑f
参数：f : ContDiffMapSupportedIn E F n K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffMapSupportedInClass.map_contDiff`：∀ {B : Type u_5} {E : outParam
 (Type u_6)} {F : outParam (Type u_7)} {inst : NormedAddCommGroup E}   {inst_1 :
 NormedAddCommGroup F} {inst_2…
-/
protected theorem contDiff (f : 𝓓^{n}_{K}(E, F)) : ContDiff ℝ n f := map_contDiff f
/-
**ContDiffMapSupportedIn.zero_on_compl** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSup
portedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} (f : ContDiffMapSupportedIn E F n K),   S
et.EqOn (⇑f) 0 (↑K)ᶜ
参数：f : ContDiffMapSupportedIn E F n K；⇑f；↑K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffMapSupportedInClass.map_zero_on_compl`：∀ {B : Type u_5} {E : out
Param (Type u_6)} {F : outParam (Type u_7)} {inst : NormedAddCommGroup E}   {ins
t_1 : NormedAddCommGroup F} {inst_2…
-/
protected theorem zero_on_compl (f : 𝓓^{n}_{K}(E, F)) : EqOn f 0 Kᶜ := map_zero_on_compl f
/-
**ContDiffMapSupportedIn.compact_supp** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSupp
ortedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} (f : ContDiffMapSupportedIn E F n K),   H
asCompactSupport ⇑f
参数：f : ContDiffMapSupportedIn E F n K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactSupport.intro`：∀ {α : Type u_2} {β : Type u_4} [inst : Topolog
icalSpace α] [inst_1 : Zero β] {f : α → β} {K : Set α} [R1Space α],   IsCompact 
K → (∀ x ∉ K,…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
· 使用定理 `ContDiffMapSupportedInClass.map_zero_on_compl`：∀ {B : Type u_5} {E : out
Param (Type u_6)} {F : outParam (Type u_7)} {inst : NormedAddCommGroup E}   {ins
t_1 : NormedAddCommGroup F} {inst_2…
-/
protected theorem compact_supp (f : 𝓓^{n}_{K}(E, F)) : HasCompactSupport f :=
  .intro K.isCompact (map_zero_on_compl f)

@[simp]
/-
**ContDiffMapSupportedIn.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSupp
ortedIn`。
形式化陈述：toFun_eq_coe {f : 𝓓^{n}_{K}(E, F)} : f.toFun = (f : E -> F)
参数：E, F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : 𝓓^{n}_{K}(E, F)} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
/-
**ContDiffMapSupportedIn.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSupport
edIn.Simps`。
形式化陈述：{E : Type u_2} →   {F : Type u_3} →     [inst : NormedAddCommGroup E] →   
    [inst_1 : NormedSpace ℝ E] →         [inst_2 : NormedAddCommGroup F] →      
     [inst_3 : NormedSpace ℝ F] →             {n : ℕ∞} → {K : TopologicalSpace.C
ompacts E} → ContDiffMapSupportedIn E F n K → E → F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See note [custom simps projection].
-/
def Simps.coe (f : 𝓓^{n}_{K}(E, F)) : E → F := f

initialize_simps_projections ContDiffMapSupportedIn (toFun → coe, as_prefix coe)

@[ext]
/-
**ContDiffMapSupportedIn.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：ext {f g : 𝓓^{n}_{K}(E, F)} (h : forall a, f a = g a) : f = g
参数：E, F；h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : 𝓓^{n}_{K}(E, F)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `ContDiffMapSupportedIn` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**ContDiffMapSupportedIn.copy** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSupportedIn`
。
形式化陈述：{E : Type u_2} →   {F : Type u_3} →     [inst : NormedAddCommGroup E] →   
    [inst_1 : NormedSpace ℝ E] →         [inst_2 : NormedAddCommGroup F] →      
     [inst_3 : NormedSpace ℝ F] →             {n : ℕ∞} →               {K : Topo
logicalSpace.Compacts E} →                 (f : ContDiffMapSupportedIn E F n K) 
→ (f' : E → F) → f' = ⇑f → ContDiffMapSupportedIn E F n K
参数：f : ContDiffMapSupportedIn E F n K；f' : E → F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `ContDiffMapSupportedIn` with a new `toFun` equal to the old one. Usef
ul to fix
definitional equalities.
-/
protected def copy (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : 𝓓^{n}_{K}(E, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  zero_on_compl' := h.symm ▸ f.zero_on_compl

@[simp]
/-
**ContDiffMapSupportedIn.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSupporte
dIn`。
形式化陈述：coe_copy (f : 𝓓^{n}_{K}(E, F)) (f' : E -> F) (h : f' = f) : ⇑(f.copy f' h)
 = f'
参数：f : 𝓓^{n}_{K}(E, F)；f' : E -> F；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**ContDiffMapSupportedIn.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSupported
In`。
形式化陈述：copy_eq (f : 𝓓^{n}_{K}(E, F)) (f' : E -> F) (h : f' = f) : f.copy f' h = f
参数：f : 𝓓^{n}_{K}(E, F)；f' : E -> F；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/-
**ContDiffMapSupportedIn.coe_toBoundedContinuousFunction** 是 Mathlib 中的一个定理，位于命名
空间 `ContDiffMapSupportedIn`。
形式化陈述：coe_toBoundedContinuousFunction (f : 𝓓^{n}_{K}(E, F)) : (f : BoundedContin
uousFunction E F) = (f : E -> F)
参数：f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffMapSupportedInClass.instBoundedContinuousMapClass`：∀ (B : Type u
_5) (E : outParam (Type u_6)) (F : outParam (Type u_7)) [inst : NormedAddCommGro
up E]   [inst_1 : NormedAddCommGroup F] [inst_2…
· 使用定理 `BoundedContinuousMapClass.map_bounded`：∀ {F : Type u_2} {α : outParam (T
ype u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst_1 : Pseu
doMetricSpace β} {inst_2 : …
-/
theorem coe_toBoundedContinuousFunction (f : 𝓓^{n}_{K}(E, F)) :
    (f : BoundedContinuousFunction E F) = (f : E → F) := rfl

section AddCommGroup

/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero 𝓓^{n}_{K}(E, F) where
  zero := .mk 0 contDiff_zero_fun fun _ _ ↦ rfl
/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply 𝓓^{n}_{K}(E, F) E F where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_zero := FunLike.coe_zero
/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add 𝓓^{n}_{K}(E, F) where
  add f g := .mk (f + g) (f.contDiff.add g.contDiff) <| by
    rw [← add_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl
/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply 𝓓^{n}_{K}(E, F) E F where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_add := FunLike.coe_add
/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg 𝓓^{n}_{K}(E, F) where
  neg f := .mk (-f) (f.contDiff.neg) <| by
    rw [← neg_zero]
    exact f.zero_on_compl.comp_left
/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNegApply 𝓓^{n}_{K}(E, F) E F where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_neg := FunLike.coe_neg
/-
**ContDiffMapSupportedIn.instSub** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupported
In`。
形式化陈述：instSub : Sub 𝓓^{n}_{K}(E, F) where sub f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub 𝓓^{n}_{K}(E, F) where
  sub f g := .mk (f - g) (f.contDiff.sub g.contDiff) <| by
    rw [← sub_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl
/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSubApply 𝓓^{n}_{K}(E, F) E F where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_sub := FunLike.coe_sub
/-
**ContDiffMapSupportedIn.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupporte
dIn`。
形式化陈述：instSMul {R} [Semiring R] [Module R F] [SMulCommClass Real R F] [Continuou
sConstSMul R F] : SMul R 𝓓^{n}_{K}(E, F) where smul c f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    SMul R 𝓓^{n}_{K}(E, F) where
  smul c f := .mk (c • (f : E → F)) (f.contDiff.const_smul c) <| by
    rw [← smul_zero c]
    exact f.zero_on_compl.comp_left
/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    IsSMulApply R 𝓓^{n}_{K}(E, F) E F where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_smul := FunLike.coe_smul
/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup 𝓓^{n}_{K}(E, F) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-15")] alias coeHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coe_coeHom := FunLike.coe_coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coeHom_injective := FunLike.coeAddMonoidHom_injective

end AddCommGroup

section Module

/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}_{K}(E, F) := fast_instance% FunLike.module

end Module

/-
**ContDiffMapSupportedIn.support_subset** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSu
pportedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} (f : ContDiffMapSupportedIn E F n K),   F
unction.support ⇑f ⊆ ↑K
参数：f : ContDiffMapSupportedIn E F n K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `ContDiffMapSupportedIn.zero_on_compl`：∀ {E : Type u_2} {F : Type u_3} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
-/
protected theorem support_subset (f : 𝓓^{n}_{K}(E, F)) : support f ⊆ K :=
  support_subset_iff'.mpr f.zero_on_compl
/-
**ContDiffMapSupportedIn.tsupport_subset** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapS
upportedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} (f : ContDiffMapSupportedIn E F n K),   t
support ⇑f ⊆ ↑K
参数：f : ContDiffMapSupportedIn E F n K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `ContDiffMapSupportedIn.support_subset`：∀ {E : Type u_2} {F : Type u_3} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommG
roup F]   [inst_3 : NormedS…
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
-/
protected theorem tsupport_subset (f : 𝓓^{n}_{K}(E, F)) : tsupport f ⊆ K :=
  closure_minimal f.support_subset K.isCompact.isClosed
/-
**ContDiffMapSupportedIn.hasCompactSupport** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMa
pSupportedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} (f : ContDiffMapSupportedIn E F n K),   H
asCompactSupport ⇑f
参数：f : ContDiffMapSupportedIn E F n K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactSupport.intro`：∀ {α : Type u_2} {β : Type u_4} [inst : Topolog
icalSpace α] [inst_1 : Zero β] {f : α → β} {K : Set α} [R1Space α],   IsCompact 
K → (∀ x ∉ K,…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
· 使用定理 `ContDiffMapSupportedIn.zero_on_compl`：∀ {E : Type u_2} {F : Type u_3} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
-/
protected theorem hasCompactSupport (f : 𝓓^{n}_{K}(E, F)) : HasCompactSupport f :=
  HasCompactSupport.intro K.isCompact f.zero_on_compl

@[fun_prop]
/-
**ContDiffMapSupportedIn.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSuppor
tedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} (f : ContDiffMapSupportedIn E F n K),   C
ontinuous ⇑f
参数：f : ContDiffMapSupportedIn E F n K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `ContDiffMapSupportedIn.contDiff`：∀ {E : Type u_2} {F : Type u_3} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F
]   [inst_3 : NormedS…
-/
protected theorem continuous (f : 𝓓^{n}_{K}(E, F)) : Continuous f :=
  f.contDiff.continuous

/-- Inclusion of unbundled `n`-times continuously differentiable function with support included
in a compact `K` into the space `𝓓^{n}_{K}`. -/
@[simps]
/-
**ContDiffMapSupportedIn.of_support_subset** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMa
pSupportedIn`。
形式化陈述：{E : Type u_2} →   {F : Type u_3} →     [inst : NormedAddCommGroup E] →   
    [inst_1 : NormedSpace ℝ E] →         [inst_2 : NormedAddCommGroup F] →      
     [inst_3 : NormedSpace ℝ F] →             {n : ℕ∞} →               {K : Topo
logicalSpace.Compacts E} →                 {f : E → F} → ContDiff ℝ (↑n) f → Fun
ction.support f ⊆ ↑K → ContDiffMapSupportedIn E F n K
参数：↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inclusion of unbundled `n`-times continuously differentiable function with suppo
rt included
in a compact `K` into the space `𝓓^{n}_{K}`.
-/
protected def of_support_subset {f : E → F} (hf : ContDiff ℝ n f) (hsupp : support f ⊆ K) :
    𝓓^{n}_{K}(E, F) where
  toFun := f
  contDiff' := hf
  zero_on_compl' := support_subset_iff'.mp hsupp
/-
**ContDiffMapSupportedIn.bounded_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 `ContD
iffMapSupportedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} (f : ContDiffMapSupportedIn E F n K) {i :
 ℕ},   ↑i ≤ n → ∃ C, ∀ (x : E), ‖iteratedFDeriv ℝ i (⇑f) x‖ ≤ C
参数：f : ContDiffMapSupportedIn E F n K；x : E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Continuous.bounded_above_of_compact_support`：Continuous.bounded_above_of
_compact_support (hf : Continuous f) (h : HasCompactSupport f) : exists C, foral
l x, ‖f x‖ <= C
· 使用定理 `ContDiff.continuous_iteratedFDeriv`：ContDiff.continuous_iteratedFDeriv {
m : Nat} (hm : m <= n) (hf : ContDiff 𝕜 n f) : Continuous fun x => iteratedFDeri
v 𝕜 m f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α] {o : Option α},
 b ∈ o → (o ≤ ↑a ↔ b ≤ a)
· 使用定理 `ContDiffMapSupportedIn.contDiff`：∀ {E : Type u_2} {F : Type u_3} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F
]   [inst_3 : NormedS…
· 使用定理 `HasCompactSupport.iteratedFDeriv`：HasCompactSupport.iteratedFDeriv (hf :
 HasCompactSupport f) (n : Nat) : HasCompactSupport (iteratedFDeriv 𝕜 n f)
· 使用定理 `ContDiffMapSupportedIn.hasCompactSupport`：∀ {E : Type u_2} {F : Type u_3
} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCo
mmGroup F]   [inst_3 : NormedS…
-/
protected theorem bounded_iteratedFDeriv (f : 𝓓^{n}_{K}(E, F)) {i : ℕ} (hi : i ≤ n) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C :=
  Continuous.bounded_above_of_compact_support
    (f.contDiff.continuous_iteratedFDeriv <| (WithTop.le_coe rfl).mpr hi)
    (f.hasCompactSupport.iteratedFDeriv i)
/-
**ContDiffMapSupportedIn.iteratedFDeriv_zero_on_compl** 是 Mathlib 中的一个定理，位于命名空间 
`ContDiffMapSupportedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} (f : ContDiffMapSupportedIn E F n K) {i :
 ℕ},   Set.EqOn (iteratedFDeriv ℝ i ⇑f) 0 (↑K)ᶜ
参数：f : ContDiffMapSupportedIn E F n K；iteratedFDeriv ℝ i ⇑f；↑K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `ContDiffMapSupportedIn.tsupport_subset`：∀ {E : Type u_2} {F : Type u_3} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
· 使用定理 `support_iteratedFDeriv_subset`：support_iteratedFDeriv_subset (n : Nat) :
 support (iteratedFDeriv 𝕜 n f) subseteq tsupport f
-/
protected theorem iteratedFDeriv_zero_on_compl (f : 𝓓^{n}_{K}(E, F)) {i : ℕ} :
    EqOn (iteratedFDeriv ℝ i f) 0 Kᶜ := by
  intro x (hx : x ∉ K)
  contrapose! hx
  exact f.tsupport_subset (support_iteratedFDeriv_subset i hx)

/-- Inclusion of `𝓓^{n}_{K}(E, F)` into the space `E →ᵇ F` of bounded continuous maps
as a `𝕜`-linear map.

This is subsumed by `toBoundedContinuousFunctionCLM`, which also bundles the continuity. -/
/-
**ContDiffMapSupportedIn.toBoundedContinuousFunctionLM** 是 Mathlib 中的一个定义，位于命名空间
 `ContDiffMapSupportedIn`。
形式化陈述：toBoundedContinuousFunctionLM : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] E ->ᵇ F where toFun
 f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inclusion of `𝓓^{n}_{K}(E, F)` into the space `E →ᵇ F` of bounded continuous map
s
as a `𝕜`-linear map.

This is subsumed by `toBoundedContinuousFunctionCLM`, which also bundles the con
tinuity.
-/
noncomputable def toBoundedContinuousFunctionLM : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ F where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/-
**ContDiffMapSupportedIn.toBoundedContinuousFunctionLM_apply** 是 Mathlib 中的一个引理，
位于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：toBoundedContinuousFunctionLM_apply (f : 𝓓^{n}_{K}(E, F)) : toBoundedConti
nuousFunctionLM 𝕜 f = f
参数：f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma toBoundedContinuousFunctionLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    toBoundedContinuousFunctionLM 𝕜 f = f :=
  rfl
/-
**ContDiffMapSupportedIn.toBoundedContinuousFunctionLM_eq_of_scalars** 是 Mathlib
 中的一个引理，位于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：toBoundedContinuousFunctionLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNorm
edField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] : (toBoundedContinuousF
unctionLM 𝕜 : 𝓓^{n}_{K}(E, F) -> _) = toBoundedContinuousFunctionLM 𝕜'
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma toBoundedContinuousFunctionLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (toBoundedContinuousFunctionLM 𝕜 : 𝓓^{n}_{K}(E, F) → _) = toBoundedContinuousFunctionLM 𝕜' :=
  rfl

variable {𝕜} in
-- Note: generalizing this to a semilinear setting would require a semilinear version of
-- `CompatibleSMul`.
/-- Given `T : F →L[𝕜] F'`, `postcompLM T` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)`
to `T ∘ f` as an element of `𝓓^{n}_{K}(E, F')`.

This is subsumed by `postcompCLM T`, which also bundles the continuity. -/
/-
**ContDiffMapSupportedIn.postcompLM** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSuppor
tedIn`。
形式化陈述：postcompLM [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F') : 𝓓^{n
}_{K}(E, F) ->ₗ[𝕜] 𝓓^{n}_{K}(E, F') where .contDiff.comp f.contDiff, toFun f
参数：T : F ->L[𝕜] F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `T : F →L[𝕜] F'`, `postcompLM T` is the `𝕜`-linear-map sending `f : 𝓓^{n}_
{K}(E, F)`
to `T ∘ f` as an element of `𝓓^{n}_{K}(E, F')`.

This is subsumed by `postcompCLM T`, which also bundles the continuity.
-/
noncomputable def postcompLM [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F') :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n}_{K}(E, F') where
  toFun f := ⟨T ∘ f, T.restrictScalars ℝ |>.contDiff.comp f.contDiff,
    fun x hx ↦ by simp [f.zero_on_compl hx]⟩
  map_add' f g := by ext x; exact map_add T (f x) (g x)
  map_smul' c f := by ext x; exact map_smul T c (f x)

@[simp]
/-
**ContDiffMapSupportedIn.postcompLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContDiffMap
SupportedIn`。
形式化陈述：postcompLM_apply [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F') 
(f : 𝓓^{n}_{K}(E, F)) : postcompLM T f = T ∘ f
参数：T : F ->L[𝕜] F'；f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma postcompLM_apply [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F')
    (f : 𝓓^{n}_{K}(E, F)) :
    postcompLM T f = T ∘ f :=
  rfl

open scoped Classical in
/-- If `n₁ ≥ n₂` and `K₁ ⊆ K₂`, `monoLM 𝕜` is the `𝕜`-linear inclusion of
`𝓓^{n₁}_{K₁}(E, F)` inside `𝓓^{n₂}_{K₂}(E, F)`. Otherwise, this is the zero map.

This is in fact continuous (see `monoCLM`). Furthermore:
* it is a topological embedding when `n₁ = n₂` and `K₁ ⊆ K₂` (not in Mathlib as of March 2026).
* it maps bounded sets to compact sets when `n₁ ≥ n₂ + 1` and `K₁ ⊆ K₂` (not in Mathlib as of
March 2026).

The parameters `n₁, n₂, K₁, K₂` are implicit as they can often be inferred from context, or
specified by a type ascription.
-/
/-
**ContDiffMapSupportedIn.monoLM** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSupportedI
n`。
形式化陈述：monoLM : 𝓓^{n₁}_{K₁}(E, F) ->ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `n₁ ≥ n₂` and `K₁ ⊆ K₂`, `monoLM 𝕜` is the `𝕜`-linear inclusion of
`𝓓^{n₁}_{K₁}(E, F)` inside `𝓓^{n₂}_{K₂}(E, F)`. Otherwise, this is the zero map.

This is in fact continuous (see `monoCLM`). Furthermore:
* it is a topological embedding when `n₁ = n₂` and `K₁ ⊆ K₂` (not in Mathlib as 
of March 2026).
* it maps bounded sets to compact sets when `n₁ ≥ n₂ + 1` and `K₁ ⊆ K₂` (not in 
Mathlib as of
March 2026).

The parameters `n₁, n₂, K₁, K₂` are implicit as they can often be inferred from 
context, or
specified by a type ascription.
-/
noncomputable def monoLM :
    𝓓^{n₁}_{K₁}(E, F) →ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F) where
  toFun f :=
    if h : n₂ ≤ n₁ ∧ K₁ ≤ K₂ then
      .of_support_subset (f.contDiff.of_le (mod_cast h.1)) (f.support_subset.trans h.2)
    else 0
  map_add' f g := by split_ifs <;> ext <;> simp
  map_smul' c f := by split_ifs <;> ext <;> simp

open scoped Classical in
@[simp]
/-
**ContDiffMapSupportedIn.monoLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContDiffMapSupp
ortedIn`。
形式化陈述：monoLM_apply (f : 𝓓^{n₁}_{K₁}(E, F)) : ((monoLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F)) :
 E -> F) = if n₂ <= n₁ ∧ K₁ <= K₂ then f else 0
参数：f : 𝓓^{n₁}_{K₁}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffMapSupportedIn.monoLM.eq_1`：∀ (𝕜 : Type u_1) {E : Type u_2} {F :
 Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace ℝ …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma monoLM_apply (f : 𝓓^{n₁}_{K₁}(E, F)) :
    ((monoLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F)) : E → F) = if n₂ ≤ n₁ ∧ K₁ ≤ K₂ then f else 0 := by
  rw [monoLM]
  split_ifs <;> rfl
/-
**ContDiffMapSupportedIn.monoLM_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `ContDiffMapSu
pportedIn`。
形式化陈述：monoLM_eq_zero (H : ¬ (n₂ <= n₁ ∧ K₁ <= K₂)) : (monoLM 𝕜 : 𝓓^{n₁}_{K₁}(E, 
F) ->ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F)) = 0
参数：H : ¬ (n₂ <= n₁ ∧ K₁ <= K₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffMapSupportedIn.ext`：ext {f g : 𝓓^{n}_{K}(E, F)} (h : forall a, f
 a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.monoLM_apply`：monoLM_apply (f : 𝓓^{n₁}_{K₁}(E, F)
) : ((monoLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F)) : E -> F) = if n₂ <= n₁ ∧ K₁ <= K₂ then f 
else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContDiffMapSupportedIn.instIsZeroApply`：∀ {E : Type u_2} {F : Type u_3} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma monoLM_eq_zero (H : ¬ (n₂ ≤ n₁ ∧ K₁ ≤ K₂)) :
    (monoLM 𝕜 : 𝓓^{n₁}_{K₁}(E, F) →ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F)) = 0 := by
  ext; simp [H]
/-
**ContDiffMapSupportedIn.monoLM_eq_of_scalars** 是 Mathlib 中的一个引理，位于命名空间 `ContDif
fMapSupportedIn`。
形式化陈述：monoLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedSpac
e 𝕜' F] [SMulCommClass Real 𝕜' F] : (monoLM 𝕜 : 𝓓^{n₁}_{K₁}(E, F) -> 𝓓^{n₂}_{K₂}
(E, F)) = monoLM 𝕜'
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma monoLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (monoLM 𝕜 : 𝓓^{n₁}_{K₁}(E, F) → 𝓓^{n₂}_{K₂}(E, F)) = monoLM 𝕜' :=
  rfl

variable (n k) in
/-- `fderivLM 𝕜 n k` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its derivative as an element of `𝓓^{k}_{K}(E, E →L[ℝ] F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the zero map.

This is subsumed by `fderivCLM`, which also bundles the continuity. -/
/-
**ContDiffMapSupportedIn.fderivLM** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSupporte
dIn`。
形式化陈述：fderivLM : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] 𝓓^{k}_{K}(E, E ->L[Real] F) where toFun 
f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fderivLM 𝕜 n k` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its derivative as an element of `𝓓^{k}_{K}(E, E →L[ℝ] F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the
 zero map.

This is subsumed by `fderivCLM`, which also bundles the continuity.
-/
noncomputable def fderivLM :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{k}_{K}(E, E →L[ℝ] F) where
  toFun f :=
    if hk : k + 1 ≤ n then
      .of_support_subset
        (f.contDiff.fderiv_right <| mod_cast hk)
        ((support_fderiv_subset ℝ).trans f.tsupport_subset)
    else 0
  map_add' f g := by
    split_ifs with hk
    · have hk' : 0 < (n : ℕ∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_le hk
      ext
      simp [fderiv_add (f.contDiff.differentiable hk'.ne').differentiableAt
                       (g.contDiff.differentiable hk'.ne').differentiableAt, FunLike.coe_add]
    · simp
  map_smul' c f := by
    split_ifs with hk
    · have hk' : 0 < (n : ℕ∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_le hk
      ext
      simp [fderiv_const_smul (f.contDiff.differentiable hk'.ne').differentiableAt,
        FunLike.coe_smul]
    · simp

@[simp]
/-
**ContDiffMapSupportedIn.fderivLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContDiffMapSu
pportedIn`。
形式化陈述：fderivLM_apply (f : 𝓓^{n}_{K}(E, F)) : fderivLM 𝕜 n k f = if k + 1 <= n th
en fderiv Real f else 0
参数：f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffMapSupportedIn.fderivLM.eq_1`：∀ (𝕜 : Type u_1) {E : Type u_2} {F
 : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E] 
  [inst_2 : NormedSpace ℝ …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma fderivLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    fderivLM 𝕜 n k f = if k + 1 ≤ n then fderiv ℝ f else 0 := by
  rw [fderivLM]
  split_ifs <;> rfl
/-
**ContDiffMapSupportedIn.fderivLM_apply_of_le** 是 Mathlib 中的一个引理，位于命名空间 `ContDif
fMapSupportedIn`。
形式化陈述：fderivLM_apply_of_le (f : 𝓓^{n}_{K}(E, F)) (hk : k + 1 <= n) : fderivLM 𝕜 
n k f = fderiv Real f
参数：f : 𝓓^{n}_{K}(E, F)；hk : k + 1 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContDiffMapSupportedIn.fderivLM_apply`：fderivLM_apply (f : 𝓓^{n}_{K}(E, 
F)) : fderivLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderivLM_apply_of_le (f : 𝓓^{n}_{K}(E, F)) (hk : k + 1 ≤ n) :
    fderivLM 𝕜 n k f = fderiv ℝ f := by
  simp [hk]
/-
**ContDiffMapSupportedIn.fderivLM_apply_of_gt** 是 Mathlib 中的一个引理，位于命名空间 `ContDif
fMapSupportedIn`。
形式化陈述：fderivLM_apply_of_gt (f : 𝓓^{n}_{K}(E, F)) (hk : n < k + 1) : fderivLM 𝕜 n
 k f = 0
参数：f : 𝓓^{n}_{K}(E, F)；hk : n < k + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffMapSupportedIn.ext`：ext {f g : 𝓓^{n}_{K}(E, F)} (h : forall a, f
 a = g a) : f = g
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.fderivLM_apply`：fderivLM_apply (f : 𝓓^{n}_{K}(E, 
F)) : fderivLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContDiffMapSupportedIn.instIsZeroApply`：∀ {E : Type u_2} {F : Type u_3} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderivLM_apply_of_gt (f : 𝓓^{n}_{K}(E, F)) (hk : n < k + 1) :
    fderivLM 𝕜 n k f = 0 := by
  ext : 1
  simp [not_le_of_gt hk]
/-
**ContDiffMapSupportedIn.fderivLM_eq_of_scalars** 是 Mathlib 中的一个引理，位于命名空间 `ContD
iffMapSupportedIn`。
形式化陈述：fderivLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedSp
ace 𝕜' F] [SMulCommClass Real 𝕜' F] : (fderivLM 𝕜 n k : 𝓓^{n}_{K}(E, F) -> _) = 
fderivLM 𝕜' n k
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
-/
lemma fderivLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (fderivLM 𝕜 n k : 𝓓^{n}_{K}(E, F) → _) = fderivLM 𝕜' n k :=
  rfl

variable (n k) in
/-- `iteratedFDerivLM 𝕜 n k i` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its `i`-th iterated derivative as an element of `𝓓^{k}_{K}(E, E [×i]→L[ℝ] F)`.
This only makes mathematical sense if `k + i ≤ n`, otherwise we define it as the zero map.

This is subsumed by `iteratedFDerivCLM` (not yet in Mathlib), which also bundles the
continuity. -/
/-
**ContDiffMapSupportedIn.iteratedFDerivLM** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMap
SupportedIn`。
形式化陈述：iteratedFDerivLM (i : Nat) : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] 𝓓^{k}_{K}(E, E [×i]->L
[Real] F) where /- Note: it is tempting to define this as some linear map if `k 
+ i ≤ n`, and the zero map otherwise. However, we would lose the definitional eq
uality between `iteratedFDerivLM 𝕜 n k i f` and `iteratedFDerivLM ℝ n k i f`.  T
his is caused by the fact that the equality `f (if p then x else y) = if p then 
f x else f y` is not definitional. -/ toFun f
参数：i : Nat。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`iteratedFDerivLM 𝕜 n k i` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` t
o
its `i`-th iterated derivative as an element of `𝓓^{k}_{K}(E, E [×i]→L[ℝ] F)`.
This only makes mathematical sense if `k + i ≤ n`, otherwise we define it as the
 zero map.

This is subsumed by `iteratedFDerivCLM` (not yet in Mathlib), which also bundles
 the
continuity.
-/
noncomputable def iteratedFDerivLM (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{k}_{K}(E, E [×i]→L[ℝ] F) where
  /-
  Note: it is tempting to define this as some linear map if `k + i ≤ n`,
  and the zero map otherwise. However, we would lose the definitional equality between
  `iteratedFDerivLM 𝕜 n k i f` and `iteratedFDerivLM ℝ n k i f`.

  This is caused by the fact that the equality `f (if p then x else y) = if p then f x else f y`
  is not definitional.
  -/
  toFun f :=
    if hi : k + i ≤ n then
      .of_support_subset
        (f.contDiff.iteratedFDeriv_right <| mod_cast hi)
        ((support_iteratedFDeriv_subset i).trans f.tsupport_subset)
    else 0
  map_add' f g := by
    split_ifs with hi
    · have hi' : (i : ℕ∞ω) ≤ n := mod_cast (le_of_add_le_right hi)
      ext
      simp [iteratedFDeriv_add (f.contDiff.of_le hi') (g.contDiff.of_le hi'), FunLike.coe_add]
    · simp
  map_smul' c f := by
    split_ifs with hi
    · have hi' : (i : ℕ∞ω) ≤ n := mod_cast (le_of_add_le_right hi)
      ext
      simp [iteratedFDeriv_const_smul_apply (f.contDiff.of_le hi').contDiffAt, FunLike.coe_smul]
    · simp

@[simp]
/-
**ContDiffMapSupportedIn.iteratedFDerivLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContD
iffMapSupportedIn`。
形式化陈述：iteratedFDerivLM_apply {i : Nat} (f : 𝓓^{n}_{K}(E, F)) : iteratedFDerivLM 
𝕜 n k i f = if k + i <= n then iteratedFDeriv Real i f else 0
参数：f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffMapSupportedIn.iteratedFDerivLM.eq_1`：∀ (𝕜 : Type u_1) {E : Type
 u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommG
roup E]   [inst_2 : NormedSpace ℝ …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma iteratedFDerivLM_apply {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) :
    iteratedFDerivLM 𝕜 n k i f = if k + i ≤ n then iteratedFDeriv ℝ i f else 0 := by
  rw [ContDiffMapSupportedIn.iteratedFDerivLM]
  split_ifs <;> rfl
/-
**ContDiffMapSupportedIn.iteratedFDerivLM_apply_of_le** 是 Mathlib 中的一个引理，位于命名空间 
`ContDiffMapSupportedIn`。
形式化陈述：iteratedFDerivLM_apply_of_le {i : Nat} (f : 𝓓^{n}_{K}(E, F)) (hin : k + i 
<= n) : iteratedFDerivLM 𝕜 n k i f = iteratedFDeriv Real i f
参数：f : 𝓓^{n}_{K}(E, F)；hin : k + i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContDiffMapSupportedIn.iteratedFDerivLM_apply`：iteratedFDerivLM_apply {i
 : Nat} (f : 𝓓^{n}_{K}(E, F)) : iteratedFDerivLM 𝕜 n k i f = if k + i <= n then 
iteratedFDeriv Real i f else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iteratedFDerivLM_apply_of_le {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) (hin : k + i ≤ n) :
    iteratedFDerivLM 𝕜 n k i f = iteratedFDeriv ℝ i f := by
  simp [hin]
/-
**ContDiffMapSupportedIn.iteratedFDerivLM_apply_of_gt** 是 Mathlib 中的一个引理，位于命名空间 
`ContDiffMapSupportedIn`。
形式化陈述：iteratedFDerivLM_apply_of_gt {i : Nat} (f : 𝓓^{n}_{K}(E, F)) (hin : n < k 
+ i) : iteratedFDerivLM 𝕜 n k i f = 0
参数：f : 𝓓^{n}_{K}(E, F)；hin : n < k + i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffMapSupportedIn.ext`：ext {f g : 𝓓^{n}_{K}(E, F)} (h : forall a, f
 a = g a) : f = g
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.iteratedFDerivLM_apply`：iteratedFDerivLM_apply {i
 : Nat} (f : 𝓓^{n}_{K}(E, F)) : iteratedFDerivLM 𝕜 n k i f = if k + i <= n then 
iteratedFDeriv Real i f else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContDiffMapSupportedIn.instIsZeroApply`：∀ {E : Type u_2} {F : Type u_3} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iteratedFDerivLM_apply_of_gt {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) (hin : n < k + i) :
    iteratedFDerivLM 𝕜 n k i f = 0 := by
  ext : 1
  simp [not_le_of_gt hin]
/-
**ContDiffMapSupportedIn.iteratedFDerivLM_eq_of_scalars** 是 Mathlib 中的一个引理，位于命名空
间 `ContDiffMapSupportedIn`。
形式化陈述：iteratedFDerivLM_eq_of_scalars {i : Nat} (𝕜' : Type*) [NontriviallyNormedF
ield 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] : (iteratedFDerivLM 𝕜 n k 
i : 𝓓^{n}_{K}(E, F) -> _) = iteratedFDerivLM 𝕜' n k i
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
-/
lemma iteratedFDerivLM_eq_of_scalars {i : ℕ} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (iteratedFDerivLM 𝕜 n k i : 𝓓^{n}_{K}(E, F) → _)
      = iteratedFDerivLM 𝕜' n k i :=
  rfl

variable (n) in
/-- `structureMapLM 𝕜 n i` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to its
`i`-th iterated derivative as an element of `E →ᵇ (E [×i]→L[ℝ] F)`. In other words, it
is the composition of `toBoundedContinuousFunctionLM 𝕜` and `iteratedFDerivLM 𝕜 n 0 i`.
This only makes mathematical sense if `i ≤ n`, otherwise we define it as the zero map.

We call these "structure maps" because they define the topology on `𝓓^{n}_{K}(E, F)`.

This is subsumed by `structureMapCLM`, which also bundles the
continuity. -/
/-
**ContDiffMapSupportedIn.structureMapLM** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSu
pportedIn`。
形式化陈述：structureMapLM (i : Nat) : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] E ->ᵇ (E [×i]->L[Real] F
)
参数：i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`structureMapLM 𝕜 n i` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to it
s
`i`-th iterated derivative as an element of `E →ᵇ (E [×i]→L[ℝ] F)`. In other wor
ds, it
is the composition of `toBoundedContinuousFunctionLM 𝕜` and `iteratedFDerivLM 𝕜 
n 0 i`.
This only makes mathematical sense if `i ≤ n`, otherwise we define it as the zer
o map.

We call these "structure maps" because they define the topology on `𝓓^{n}_{K}(E,
 F)`.

This is subsumed by `structureMapCLM`, which also bundles the
continuity.
-/
noncomputable def structureMapLM (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F) :=
  toBoundedContinuousFunctionLM 𝕜 ∘ₗ iteratedFDerivLM 𝕜 n 0 i
/-
**ContDiffMapSupportedIn.structureMapLM_eq** 是 Mathlib 中的一个引理，位于命名空间 `ContDiffMa
pSupportedIn`。
形式化陈述：structureMapLM_eq {i : Nat} : (structureMapLM 𝕜 n i : 𝓓^{n}_{K}(E, F) ->ₗ[
𝕜] E ->ᵇ (E [×i]->L[Real] F)) = (toBoundedContinuousFunctionLM 𝕜 : 𝓓^{0}_{K}(E, 
E [×i]->L[Real] F) ->ₗ[𝕜] E ->ᵇ (E [×i]->L[Real] F)) ∘ₗ (iteratedFDerivLM 𝕜 n 0 
i : 𝓓^{n}_{K}(E, F) ->ₗ[𝕜] 𝓓^{0}_{K}(E, E [×i]->L[Real] F))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
-/
lemma structureMapLM_eq {i : ℕ} :
    (structureMapLM 𝕜 n i : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F)) =
      (toBoundedContinuousFunctionLM 𝕜 : 𝓓^{0}_{K}(E, E [×i]→L[ℝ] F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F)) ∘ₗ
      (iteratedFDerivLM 𝕜 n 0 i : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{0}_{K}(E, E [×i]→L[ℝ] F)) :=
  rfl
/-
**ContDiffMapSupportedIn.structureMapLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContDif
fMapSupportedIn`。
形式化陈述：structureMapLM_apply {i : Nat} (f : 𝓓^{n}_{K}(E, F)) : structureMapLM 𝕜 n 
i f = if i <= n then iteratedFDeriv Real i f else 0
参数：f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffMapSupportedInClass.instBoundedContinuousMapClass`：∀ (B : Type u
_5) (E : outParam (Type u_6)) (F : outParam (Type u_7)) [inst : NormedAddCommGro
up E]   [inst_1 : NormedAddCommGroup F] [inst_2…
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用引理 `ContDiffMapSupportedIn.iteratedFDerivLM_apply`：iteratedFDerivLM_apply {i
 : Nat} (f : 𝓓^{n}_{K}(E, F)) : iteratedFDerivLM 𝕜 n k i f = if k + i <= n then 
iteratedFDeriv Real i f else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `BoundedContinuousMapClass.map_bounded`：∀ {F : Type u_2} {α : outParam (T
ype u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst_1 : Pseu
doMetricSpace β} {inst_2 : …
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `BoundedContinuousFunction.mk.congr_simp`：∀ {α : Type u} {β : Type v} [in
st : TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (toContinuousMap toCon
tinuousMap_1 : C(α, β)) (e_to…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma structureMapLM_apply {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) :
    structureMapLM 𝕜 n i f = if i ≤ n then iteratedFDeriv ℝ i f else 0 := by
  simp [structureMapLM]
/-
**ContDiffMapSupportedIn.structureMapLM_top_apply** 是 Mathlib 中的一个引理，位于命名空间 `Con
tDiffMapSupportedIn`。
形式化陈述：structureMapLM_top_apply {i : Nat} (f : 𝓓_{K}(E, F)) : structureMapLM 𝕜 ⊤ 
i f = iteratedFDeriv Real i f
参数：f : 𝓓_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `ContDiffMapSupportedInClass.instBoundedContinuousMapClass`：∀ (B : Type u
_5) (E : outParam (Type u_6)) (F : outParam (Type u_7)) [inst : NormedAddCommGro
up E]   [inst_1 : NormedAddCommGroup F] [inst_2…
· 使用引理 `ContDiffMapSupportedIn.iteratedFDerivLM_apply`：iteratedFDerivLM_apply {i
 : Nat} (f : 𝓓^{n}_{K}(E, F)) : iteratedFDerivLM 𝕜 n k i f = if k + i <= n then 
iteratedFDeriv Real i f else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `BoundedContinuousMapClass.map_bounded`：∀ {F : Type u_2} {α : outParam (T
ype u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst_1 : Pseu
doMetricSpace β} {inst_2 : …
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `BoundedContinuousFunction.mk.congr_simp`：∀ {α : Type u} {β : Type v} [in
st : TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (toContinuousMap toCon
tinuousMap_1 : C(α, β)) (e_to…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma structureMapLM_top_apply {i : ℕ} (f : 𝓓_{K}(E, F)) :
    structureMapLM 𝕜 ⊤ i f = iteratedFDeriv ℝ i f := by
  simp [structureMapLM_eq]
/-
**ContDiffMapSupportedIn.structureMapLM_eq_of_scalars** 是 Mathlib 中的一个引理，位于命名空间 
`ContDiffMapSupportedIn`。
形式化陈述：structureMapLM_eq_of_scalars {i : Nat} (𝕜' : Type*) [NontriviallyNormedFie
ld 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] : (structureMapLM 𝕜 n i : 𝓓^
{n}_{K}(E, F) -> _) = structureMapLM 𝕜' n i
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
-/
lemma structureMapLM_eq_of_scalars {i : ℕ} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (structureMapLM 𝕜 n i : 𝓓^{n}_{K}(E, F) → _) = structureMapLM 𝕜' n i :=
  rfl
/-
**ContDiffMapSupportedIn.structureMapLM_zero_apply** 是 Mathlib 中的一个引理，位于命名空间 `Co
ntDiffMapSupportedIn`。
形式化陈述：structureMapLM_zero_apply {f : 𝓓^{n}_{K}(E, F)} {x : E} : structureMapLM 𝕜
 n 0 f x = ContinuousMultilinearMap.uncurry0 Real E (f x)
参数：E, F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.structureMapLM_apply`：structureMapLM_apply {i : N
at} (f : 𝓓^{n}_{K}(E, F)) : structureMapLM 𝕜 n i f = if i <= n then iteratedFDer
iv Real i f else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma structureMapLM_zero_apply {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    structureMapLM 𝕜 n 0 f x = ContinuousMultilinearMap.uncurry0 ℝ E (f x) := by
  ext
  simp [structureMapLM_apply, iteratedFDeriv_zero_eq_comp]
/-
**ContDiffMapSupportedIn.structureMapLM_zero_injective** 是 Mathlib 中的一个引理，位于命名空间
 `ContDiffMapSupportedIn`。
形式化陈述：structureMapLM_zero_injective : Injective (structureMapLM 𝕜 n 0 : 𝓓^{n}_{K
}(E, F) -> E ->ᵇ E [×0]->L[Real] F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContDiffMapSupportedIn.structureMapLM_zero_apply`：structureMapLM_zero_ap
ply {f : 𝓓^{n}_{K}(E, F)} {x : E} : structureMapLM 𝕜 n 0 f x = ContinuousMultili
nearMap.uncurry0 Real E (f x)
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
-/
lemma structureMapLM_zero_injective :
    Injective (structureMapLM 𝕜 n 0 : 𝓓^{n}_{K}(E, F) → E →ᵇ E [×0]→L[ℝ] F) := by
  intro f g hfg
  simpa [BoundedContinuousFunction.ext_iff, ContinuousMultilinearMap.ext_iff,
    structureMapLM_zero_apply, ContDiffMapSupportedIn.ext_iff] using hfg

section Topology

/-
**ContDiffMapSupportedIn.topologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMap
SupportedIn`。
形式化陈述：topologicalSpace : TopologicalSpace 𝓓^{n}_{K}(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}_{K}(E, F) :=
  ⨅ (i : ℕ), induced (structureMapLM ℝ n i) inferInstance
/-
**ContDiffMapSupportedIn.uniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupp
ortedIn`。
形式化陈述：uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F) := .replaceTopology
  (⨅ (i : ℕ), UniformSpace.comap (structureMapLM ℝ n i) inferInstance)
  toTopologicalSpace_iInf.symm
/-
**ContDiffMapSupportedIn.uniformSpace_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ContDif
fMapSupportedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E},   ContDiffMapSupportedIn.uniformSpace = 
    ⨅ i, UniformSpace.comap (⇑(ContDiffMapSupportedIn.structureMapLM ℝ n i)) inf
erInstance
参数：⇑(ContDiffMapSupportedIn.structureMapLM ℝ n i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.replaceTopology_eq`：UniformSpace.replaceTopology_eq {α : Ty
pe*} [i : TopologicalSpace α] (u : UniformSpace α) (h : i = u.toTopologicalSpace
) : u.replaceTopology…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniformSpace.toTopologicalSpace_iInf`：toTopologicalSpace_iInf {ι : Sort*
} {u : ι -> UniformSpace α} : (iInf u).toTopologicalSpace = ⨅ i, (u i).toTopolog
icalSpace
-/
protected theorem uniformSpace_eq_iInf : (uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F)) =
    ⨅ (i : ℕ), UniformSpace.comap (structureMapLM ℝ n i) inferInstance :=
  UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm
/-
**ContDiffMapSupportedIn.isTopologicalAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `ContDi
ffMapSupportedIn`。
形式化陈述：isTopologicalAddGroup : IsTopologicalAddGroup 𝓓^{n}_{K}(E, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `topologicalAddGroup_iInf`：∀ {G : Type w} {ι : Sort u_1} [inst : AddGroup
 G] {ts' : ι → TopologicalSpace G},   (∀ (i : ι), IsTopologicalAddGroup G) → IsT
opologicalAddG…
· 使用定理 `topologicalAddGroup_induced`：∀ {G : Type w} {H : Type x} [inst : Topolog
icalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {F : Type u_1}   [i
nst_3 : AddGroup …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
instance isTopologicalAddGroup : IsTopologicalAddGroup 𝓓^{n}_{K}(E, F) :=
  topologicalAddGroup_iInf fun _ ↦ topologicalAddGroup_induced _
/-
**ContDiffMapSupportedIn.isUniformAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMa
pSupportedIn`。
形式化陈述：isUniformAddGroup : IsUniformAddGroup 𝓓^{n}_{K}(E, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffMapSupportedIn.uniformSpace_eq_iInf`：∀ {E : Type u_2} {F : Type 
u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAd
dCommGroup F]   [inst_3 : NormedS…
· 使用定理 `isUniformAddGroup_iInf`：∀ {G : Type u_1} [inst : AddGroup G] {ι : Sort u
_4} {us' : ι → UniformSpace G},   (∀ (i : ι), IsUniformAddGroup G) → IsUniformAd
dGroup G
· 使用定理 `IsUniformAddGroup.comap`：∀ {G : Type u_1} {H : Type u_2} {hom : Type u_3
} [inst : AddGroup G] [inst_1 : AddGroup H] {u : UniformSpace H}   [IsUniformAdd
Group H] [ins…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
instance isUniformAddGroup : IsUniformAddGroup 𝓓^{n}_{K}(E, F) := by
  rw [ContDiffMapSupportedIn.uniformSpace_eq_iInf]
  exact isUniformAddGroup_iInf fun _ ↦ IsUniformAddGroup.comap _
/-
**ContDiffMapSupportedIn.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSu
pportedIn`。
形式化陈述：continuousSMul : ContinuousSMul 𝕜 𝓓^{n}_{K}(E, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousSMul_iInf`：continuousSMul_iInf {ts' : ι -> TopologicalSpace X}
 (h : forall i, @ContinuousSMul M X _ _ (ts' i)) : @ContinuousSMul M X _ _ (⨅ i,
 ts' i)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `continuousSMul_induced`：continuousSMul_induced : @ContinuousSMul R M₁ _ 
u (t.induced f)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
instance continuousSMul : ContinuousSMul 𝕜 𝓓^{n}_{K}(E, F) :=
  continuousSMul_iInf fun i ↦ continuousSMul_induced (structureMapLM 𝕜 n i)
/-
**ContDiffMapSupportedIn.locallyConvexSpace** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffM
apSupportedIn`。
形式化陈述：locallyConvexSpace : LocallyConvexSpace Real 𝓓^{n}_{K}(E, F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyConvexSpace.iInf`：∀ {ι : Sort u_1} {𝕜 : Type u_2} {E : Type u_3} 
[inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst
_3 : _root_.M…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `LocallyConvexSpace.induced`：∀ {𝕜 : Type u_2} {E : Type u_3} {F : Type u_
4} [inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [i
nst_3 : _root_.M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
-/
instance locallyConvexSpace : LocallyConvexSpace ℝ 𝓓^{n}_{K}(E, F) :=
  LocallyConvexSpace.iInf fun _ ↦ LocallyConvexSpace.induced _

variable (n) in
/-- `structureMapCLM 𝕜 n i` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to its
`i`-th iterated derivative as an element of `E →ᵇ (E [×i]→L[ℝ] F)`.
This only makes mathematical sense if `i ≤ n`, otherwise we define it as the zero map.

We call these "structure maps" because they define the topology on `𝓓^{n}_{K}(E, F)`. -/
/-
**ContDiffMapSupportedIn.structureMapCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapS
upportedIn`。
形式化陈述：structureMapCLM (i : Nat) : 𝓓^{n}_{K}(E, F) ->L[𝕜] E ->ᵇ (E [×i]->L[Real] 
F) where toLinearMap
参数：i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`structureMapCLM 𝕜 n i` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(
E, F)` to its
`i`-th iterated derivative as an element of `E →ᵇ (E [×i]→L[ℝ] F)`.
This only makes mathematical sense if `i ≤ n`, otherwise we define it as the zer
o map.

We call these "structure maps" because they define the topology on `𝓓^{n}_{K}(E,
 F)`.
-/
noncomputable def structureMapCLM (i : ℕ) :
    𝓓^{n}_{K}(E, F) →L[𝕜] E →ᵇ (E [×i]→L[ℝ] F) where
  toLinearMap := structureMapLM 𝕜 n i
  cont := continuous_iInf_dom continuous_induced_dom

@[simp]
/-
**ContDiffMapSupportedIn.structureMapCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContDi
ffMapSupportedIn`。
形式化陈述：structureMapCLM_apply {i : Nat} (f : 𝓓^{n}_{K}(E, F)) : structureMapCLM 𝕜 
n i f = if i <= n then iteratedFDeriv Real i f else 0
参数：f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContDiffMapSupportedIn.structureMapLM_apply`：structureMapLM_apply {i : N
at} (f : 𝓓^{n}_{K}(E, F)) : structureMapLM 𝕜 n i f = if i <= n then iteratedFDer
iv Real i f else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma structureMapCLM_apply {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) :
    structureMapCLM 𝕜 n i f = if i ≤ n then iteratedFDeriv ℝ i f else 0 := by
  simp [structureMapCLM, structureMapLM_apply]
/-
**ContDiffMapSupportedIn.structureMapCLM_top_apply** 是 Mathlib 中的一个引理，位于命名空间 `Co
ntDiffMapSupportedIn`。
形式化陈述：structureMapCLM_top_apply {i : Nat} (f : 𝓓_{K}(E, F)) : structureMapCLM 𝕜 
⊤ i f = iteratedFDeriv Real i f
参数：f : 𝓓_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContDiffMapSupportedIn.structureMapLM_top_apply`：structureMapLM_top_appl
y {i : Nat} (f : 𝓓_{K}(E, F)) : structureMapLM 𝕜 ⊤ i f = iteratedFDeriv Real i f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma structureMapCLM_top_apply {i : ℕ} (f : 𝓓_{K}(E, F)) :
    structureMapCLM 𝕜 ⊤ i f = iteratedFDeriv ℝ i f := by
  simp [structureMapCLM, structureMapLM_top_apply]
/-
**ContDiffMapSupportedIn.structureMapCLM_eq_of_scalars** 是 Mathlib 中的一个引理，位于命名空间
 `ContDiffMapSupportedIn`。
形式化陈述：structureMapCLM_eq_of_scalars {i : Nat} (𝕜' : Type*) [NontriviallyNormedFi
eld 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] : (structureMapCLM 𝕜 n i : 
𝓓^{n}_{K}(E, F) -> _) = structureMapCLM 𝕜' n i
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
-/
lemma structureMapCLM_eq_of_scalars {i : ℕ} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (structureMapCLM 𝕜 n i : 𝓓^{n}_{K}(E, F) → _) = structureMapCLM 𝕜' n i :=
  rfl
/-
**ContDiffMapSupportedIn.structureMapCLM_zero_apply** 是 Mathlib 中的一个引理，位于命名空间 `C
ontDiffMapSupportedIn`。
形式化陈述：structureMapCLM_zero_apply {f : 𝓓^{n}_{K}(E, F)} {x : E} : structureMapCLM
 𝕜 n 0 f x = ContinuousMultilinearMap.uncurry0 Real E (f x)
参数：E, F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffMapSupportedIn.structureMapLM_zero_apply`：structureMapLM_zero_ap
ply {f : 𝓓^{n}_{K}(E, F)} {x : E} : structureMapLM 𝕜 n 0 f x = ContinuousMultili
nearMap.uncurry0 Real E (f x)
-/
lemma structureMapCLM_zero_apply {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    structureMapCLM 𝕜 n 0 f x = ContinuousMultilinearMap.uncurry0 ℝ E (f x) :=
  structureMapLM_zero_apply 𝕜
/-
**ContDiffMapSupportedIn.structureMapCLM_zero_injective** 是 Mathlib 中的一个引理，位于命名空
间 `ContDiffMapSupportedIn`。
形式化陈述：structureMapCLM_zero_injective : Injective (structureMapCLM 𝕜 n 0 : 𝓓^{n}_
{K}(E, F) -> E ->ᵇ E [×0]->L[Real] F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffMapSupportedIn.structureMapLM_zero_injective`：structureMapLM_zer
o_injective : Injective (structureMapLM 𝕜 n 0 : 𝓓^{n}_{K}(E, F) -> E ->ᵇ E [×0]-
>L[Real] F)
-/
lemma structureMapCLM_zero_injective :
    Injective (structureMapCLM 𝕜 n 0 : 𝓓^{n}_{K}(E, F) → E →ᵇ E [×0]→L[ℝ] F) :=
  structureMapLM_zero_injective 𝕜
/-
**ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM** 是 Mathlib 中的一个引
理，位于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：isUniformEmbedding_pi_structureMapCLM : IsUniformEmbedding (ContinuousLine
arMap.pi (structureMapCLM 𝕜 n) : 𝓓^{n}_{K}(E, F) ->L[𝕜] Π i, E ->ᵇ (E [×i]->L[Re
al] F)) where injective f g hfg
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffMapSupportedIn.uniformSpace_eq_iInf`：∀ {E : Type u_2} {F : Type 
u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAd
dCommGroup F]   [inst_3 : NormedS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Pi.uniformSpace_eq`：Pi.uniformSpace_eq : Pi.uniformSpace α = ⨅ i, Unifor
mSpace.comap (eval i) (U i)
· 使用定理 `UniformSpace.comap_iInf`：UniformSpace.comap_iInf {ι α γ} {u : ι -> Unifo
rmSpace γ} {f : α -> γ} : (⨅ i, u i).comap f = ⨅ i, (u i).comap f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ContDiffMapSupportedIn.structureMapCLM_zero_injective`：structureMapCLM_z
ero_injective : Injective (structureMapCLM 𝕜 n 0 : 𝓓^{n}_{K}(E, F) -> E ->ᵇ E [×
0]->L[Real] F)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma isUniformEmbedding_pi_structureMapCLM :
    IsUniformEmbedding (ContinuousLinearMap.pi (structureMapCLM 𝕜 n) :
      𝓓^{n}_{K}(E, F) →L[𝕜] Π i, E →ᵇ (E [×i]→L[ℝ] F)) where
  injective f g hfg := structureMapCLM_zero_injective 𝕜 (congr($hfg 0))
  toIsUniformInducing := by
    simp_rw [isUniformInducing_iff_uniformSpace, ContDiffMapSupportedIn.uniformSpace_eq_iInf,
      Pi.uniformSpace_eq, comap_iInf, ← comap_comap]
    rfl

/-- The **universal property** of the topology on `𝓓^{n}_{K}(E, F)`: a map to `𝓓^{n}_{K}(E, F)`
is continuous if and only if its composition with each structure map
`structureMapCLM ℝ n i : 𝓓^{n}_{K}(E, F) → (E →ᵇ (E [×i]→L[ℝ] F))` is continuous.

Since `structureMapCLM ℝ n i` is zero whenever `i > n`, it suffices to check it for `i ≤ n`,
as proven by `continuous_iff_comp_order_le`. -/
-- Note: if needed, we could allow an extra parameter `𝕜` in case the user wants to use
-- `structureMapCLM 𝕜 n i`.
/-
**ContDiffMapSupportedIn.continuous_iff_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContDiff
MapSupportedIn`。
形式化陈述：continuous_iff_comp {X} [TopologicalSpace X] (φ : X -> 𝓓^{n}_{K}(E, F)) : 
Continuous φ ↔ forall i, Continuous (structureMapCLM Real n i ∘ φ)
参数：φ : X -> 𝓓^{n}_{K}(E, F)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_iff_comp {X} [TopologicalSpace X] (φ : X → 𝓓^{n}_{K}(E, F)) :
    Continuous φ ↔ ∀ i, Continuous (structureMapCLM ℝ n i ∘ φ) := by
  simp [continuous_iInf_rng, continuous_induced_rng, structureMapCLM]

/-- The **universal property** of the topology on `𝓓^{n}_{K}(E, F)`: a map to `𝓓^{n}_{K}(E, F)`
is continuous if and only if its composition with the structure map
`structureMapCLM ℝ n i : 𝓓^{n}_{K}(E, F) → (E →ᵇ (E [×i]→L[ℝ] F))` is continuous for each
`i ≤ n`. -/
-- Note: if needed, we could allow an extra parameter `𝕜` in case the user wants to use
-- `structureMapCLM 𝕜 n i`.
/-
**ContDiffMapSupportedIn.continuous_iff_comp_order_le** 是 Mathlib 中的一个定理，位于命名空间 
`ContDiffMapSupportedIn`。
形式化陈述：continuous_iff_comp_order_le {X : Type*} [TopologicalSpace X] (φ : X -> 𝓓^
{n}_{K}(E, F)) : Continuous φ ↔ forall (i : Nat), i <= n -> Continuous (structur
eMapCLM Real n i ∘ φ)
参数：φ : X -> 𝓓^{n}_{K}(E, F)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffMapSupportedIn.continuous_iff_comp`：continuous_iff_comp {X} [Top
ologicalSpace X] (φ : X -> 𝓓^{n}_{K}(E, F)) : Continuous φ ↔ forall i, Continuou
s (structureMapCLM Real n i ∘ φ)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Continuous.congr`：Continuous.congr {g : X -> Y} (h : Continuous f) (h' :
 forall x, f x = g x) : Continuous g
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.structureMapCLM_apply`：structureMapCLM_apply {i :
 Nat} (f : 𝓓^{n}_{K}(E, F)) : structureMapCLM 𝕜 n i f = if i <= n then iteratedF
Deriv Real i f else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem continuous_iff_comp_order_le {X : Type*} [TopologicalSpace X] (φ : X → 𝓓^{n}_{K}(E, F)) :
    Continuous φ ↔ ∀ (i : ℕ), i ≤ n → Continuous (structureMapCLM ℝ n i ∘ φ) := by
  rw [continuous_iff_comp]
  congrm (∀ i, ?_)
  by_cases hin : i ≤ n <;> simp only [hin, true_imp_iff, false_imp_iff, iff_true]
  refine continuous_zero.congr fun x ↦ ?_
  ext t : 1
  simp [hin, structureMapCLM_apply]

variable (E F n K)

/-- The seminorms on the space `𝓓^{n}_{K}(E, F)` given by the sup norm of the iterated derivatives.
In the scope `Distributions.Seminorm`, we denote them by `N[𝕜; F]_{K, n, i}`
(or `N[𝕜]_{K, n, i}`), or simply by `N[𝕜; F]_{K, i}` (or `N[𝕜; F]_{K, i}`) when `n = ∞`. -/
/-
**ContDiffMapSupportedIn.seminorm** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSupporte
dIn`。
形式化陈述：(𝕜 : Type u_1) →   (E : Type u_2) →     (F : Type u_3) →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : NormedAddCommGroup E] →           [i
nst_2 : NormedSpace ℝ E] →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace ℝ F] →                 [inst_5 : NormedSpace 𝕜 F] →
                   [inst_6 : SMulCommClass ℝ 𝕜 F] →                     (n : ℕ∞)
 → (K : TopologicalSpace.Compacts E) → ℕ → Seminorm 𝕜 (ContDiffMapSupportedIn E 
F n K)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The seminorms on the space `𝓓^{n}_{K}(E, F)` given by the sup norm of the iterat
ed derivatives.
In the scope `Distributions.Seminorm`, we denote them by `N[𝕜; F]_{K, n, i}`
(or `N[𝕜]_{K, n, i}`), or simply by `N[𝕜; F]_{K, i}` (or `N[𝕜; F]_{K, i}`) when 
`n = ∞`.
-/
protected noncomputable def seminorm (i : ℕ) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[ℝ] F))).comp (structureMapLM 𝕜 n i)

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

/-- The seminorms on the space `𝓓^{n}_{K}(E, F)` given by sup of the
`ContDiffMapSupportedIn.seminorm k`for `k ≤ i`. -/
/-
**ContDiffMapSupportedIn.supSeminorm** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSuppo
rtedIn`。
形式化陈述：(𝕜 : Type u_1) →   (E : Type u_2) →     (F : Type u_3) →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : NormedAddCommGroup E] →           [i
nst_2 : NormedSpace ℝ E] →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace ℝ F] →                 [inst_5 : NormedSpace 𝕜 F] →
                   [inst_6 : SMulCommClass ℝ 𝕜 F] →                     (n : ℕ∞)
 → (K : TopologicalSpace.Compacts E) → ℕ → Seminorm 𝕜 (ContDiffMapSupportedIn E 
F n K)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The seminorms on the space `𝓓^{n}_{K}(E, F)` given by sup of the
`ContDiffMapSupportedIn.seminorm k`for `k ≤ i`.
-/
protected noncomputable def supSeminorm (i : ℕ) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (Finset.Iic i).sup (ContDiffMapSupportedIn.seminorm 𝕜 E F n K)
/-
**ContDiffMapSupportedIn.withSeminorms** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSup
portedIn`。
形式化陈述：∀ (𝕜 : Type u_1) (E : Type u_2) (F : Type u_3) [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace ℝ F] [inst_5 : NormedSpace 𝕜 F]   [in
st_6 : SMulCommClass ℝ 𝕜 F] (n : ℕ∞) (K : TopologicalSpace.Compacts E),   WithSe
minorms (ContDiffMapSupportedIn.seminorm 𝕜 E F n K)
参数：𝕜 : Type u_1；E : Type u_2；F : Type u_3；n : ℕ∞；K : TopologicalSpace.Compacts E
；ContDiffMapSupportedIn.seminorm 𝕜 E F n K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `withSeminorms_iInf`：withSeminorms_iInf {κ : ι -> Type*} {p : (i : ι) -> 
SeminormFamily 𝕜 E (κ i)} {t : ι -> TopologicalSpace E} (hp : forall i, WithSemi
norms (t…
· 使用定理 `LinearMap.withSeminorms_induced`：LinearMap.withSeminorms_induced {q : Se
minormFamily 𝕜₂ F ι} (hq : WithSeminorms q) (f : E ->ₛₗ[σ₁₂] F) : WithSeminorms 
(topology
· 使用定理 `norm_withSeminorms`：norm_withSeminorms (𝕜 E) [NormedField 𝕜] [Seminormed
AddCommGroup E] [NormedSpace 𝕜 E] : WithSeminorms fun _ : Fin 1 => normSeminorm 
𝕜 E
· 使用定理 `WithSeminorms.congr_equiv`：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_9
} {ι' : Type u_10} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : 
_root_.Module 𝕜…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
protected theorem withSeminorms :
    WithSeminorms (ContDiffMapSupportedIn.seminorm 𝕜 E F n K) := by
  let p : SeminormFamily 𝕜 𝓓^{n}_{K}(E, F) ((_ : ℕ) × Fin 1) :=
    SeminormFamily.sigma fun i _ ↦
      (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[ℝ] F))).comp (structureMapLM 𝕜 n i)
  have : WithSeminorms p :=
    withSeminorms_iInf fun i ↦ LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
  exact this.congr_equiv (Equiv.sigmaUnique _ _).symm
/-
**ContDiffMapSupportedIn.withSeminorms'** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSu
pportedIn`。
形式化陈述：∀ (𝕜 : Type u_1) (E : Type u_2) (F : Type u_3) [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace ℝ F] [inst_5 : NormedSpace 𝕜 F]   [in
st_6 : SMulCommClass ℝ 𝕜 F] (n : ℕ∞) (K : TopologicalSpace.Compacts E),   WithSe
minorms (ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K)
参数：𝕜 : Type u_1；E : Type u_2；F : Type u_3；n : ℕ∞；K : TopologicalSpace.Compacts E
；ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.partial_sups`：∀ {𝕜 : Type u_2} {E : Type u_6} {ι : Type u_
9} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Pre…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffMapSupportedIn.withSeminorms`：∀ (𝕜 : Type u_1) (E : Type u_2) (F
 : Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E] 
  [inst_2 : NormedSpace ℝ …
-/
protected theorem withSeminorms' :
    WithSeminorms (ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K) :=
  (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K).partial_sups

variable {E F n K}
/-
**ContDiffMapSupportedIn.seminorm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSu
pportedIn`。
形式化陈述：∀ (𝕜 : Type u_1) {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace ℝ F] [inst_5 : NormedSpace 𝕜 F]   [in
st_6 : SMulCommClass ℝ 𝕜 F] {n : ℕ∞} {K : TopologicalSpace.Compacts E} (i : ℕ)  
 (f : ContDiffMapSupportedIn E F n K),   (ContDiffMapSupportedIn.seminorm 𝕜 E F 
n K i) f = ‖(ContDiffMapSupportedIn.structureMapCLM 𝕜 n i) f‖
参数：𝕜 : Type u_1；i : ℕ；f : ContDiffMapSupportedIn E F n K；ContDiffMapSupportedIn.
seminorm 𝕜 E F n K i；ContDiffMapSupportedIn.structureMapCLM 𝕜 n i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
protected theorem seminorm_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} f = ‖structureMapCLM 𝕜 n i f‖ :=
  rfl
/-
**ContDiffMapSupportedIn.seminorm_eq_bot_of_gt** 是 Mathlib 中的一个定理，位于命名空间 `ContDi
ffMapSupportedIn`。
形式化陈述：∀ (𝕜 : Type u_1) {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace ℝ F] [inst_5 : NormedSpace 𝕜 F]   [in
st_6 : SMulCommClass ℝ 𝕜 F] {n : ℕ∞} {K : TopologicalSpace.Compacts E} {i : ℕ}, 
  n < ↑i → ContDiffMapSupportedIn.seminorm 𝕜 E F n K i = ⊥
参数：𝕜 : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.structureMapCLM_apply`：structureMapCLM_apply {i :
 Nat} (f : 𝓓^{n}_{K}(E, F)) : structureMapCLM 𝕜 n i f = if i <= n then iteratedF
Deriv Real i f else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem seminorm_eq_bot_of_gt {i : ℕ} (hin : n < i) :
    N[𝕜; F]_{K, n, i} = ⊥ := by
  have : ¬(i ≤ n) := by simpa using hin
  ext f
  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.ext_iff,
    structureMapCLM_apply, this]
/-
**ContDiffMapSupportedIn.seminorm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapS
upportedIn`。
形式化陈述：∀ (𝕜 : Type u_1) {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace ℝ F] [inst_5 : NormedSpace 𝕜 F]   [in
st_6 : SMulCommClass ℝ 𝕜 F] {n : ℕ∞} {K : TopologicalSpace.Compacts E} {C : ℝ}, 
  0 ≤ C →     ∀ (i : ℕ) (f : ContDiffMapSupportedIn E F n K),       (ContDiffMap
SupportedIn.seminorm 𝕜 E F n K i) f ≤ C ↔ ↑i ≤ n → ∀ x ∈ K, ‖iteratedFDeriv ℝ i 
(⇑f) x‖ ≤ C
参数：𝕜 : Type u_1；i : ℕ；f : ContDiffMapSupportedIn E F n K；ContDiffMapSupportedIn.
seminorm 𝕜 E F n K i；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContDiffMapSupportedIn.iteratedFDeriv_zero_on_compl`：∀ {E : Type u_2} {F
 : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : 
NormedAddCommGroup F]   [inst_3 : NormedS…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.structureMapCLM_apply`：structureMapCLM_apply {i :
 Nat} (f : 𝓓^{n}_{K}(E, F)) : structureMapCLM 𝕜 n i f = if i <= n then iteratedF
Deriv Real i f else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ContDiffMapSupportedIn.seminorm_eq_bot_of_gt`：∀ (𝕜 : Type u_1) {E : Type
 u_2} {F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommG
roup E]   [inst_2 : NormedSpace ℝ …
-/
protected theorem seminorm_le_iff {C : ℝ} (hC : 0 ≤ C) (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} f ≤ C ↔ (i ≤ n → ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C) := by
  have : (∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C) ↔ (∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C) := by
    congrm ∀ x, ?_
    by_cases hx : x ∈ K
    · simp [hx]
    · simp [hx, f.iteratedFDeriv_zero_on_compl hx, hC]
  by_cases hi : i ≤ n
  · simp [hi, forall_const, ContDiffMapSupportedIn.seminorm_apply, structureMapCLM_apply,
      BoundedContinuousFunction.norm_le hC, this]
  · push Not at hi
    simp [hi, ContDiffMapSupportedIn.seminorm_eq_bot_of_gt _ hi, hC]
/-
**ContDiffMapSupportedIn.seminorm_top_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContDiff
MapSupportedIn`。
形式化陈述：∀ (𝕜 : Type u_1) {E : Type u_2} {F : Type u_3} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace ℝ F] [inst_5 : NormedSpace 𝕜 F]   [in
st_6 : SMulCommClass ℝ 𝕜 F] {K : TopologicalSpace.Compacts E} {C : ℝ},   0 ≤ C →
     ∀ (i : ℕ) (f : ContDiffMapSupportedIn E F ⊤ K),       (ContDiffMapSupported
In.seminorm 𝕜 E F ⊤ K i) f ≤ C ↔ ∀ x ∈ K, ‖iteratedFDeriv ℝ i (⇑f) x‖ ≤ C
参数：𝕜 : Type u_1；i : ℕ；f : ContDiffMapSupportedIn E F ⊤ K；ContDiffMapSupportedIn.
seminorm 𝕜 E F ⊤ K i；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffMapSupportedIn.seminorm_le_iff`：∀ (𝕜 : Type u_1) {E : Type u_2} 
{F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E
]   [inst_2 : NormedSpace ℝ …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem seminorm_top_le_iff {C : ℝ} (hC : 0 ≤ C) (i : ℕ) (f : 𝓓_{K}(E, F)) :
    N[𝕜]_{K, i} f ≤ C ↔ ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  simp_rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 hC, le_top, forall_const]
/-
**ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm** 是 Mathlib 中的一个定
理，位于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：norm_iteratedFDeriv_apply_le_seminorm {i : Nat} (hin : i <= n) {f : 𝓓^{n}_
{K}(E, F)} {x : E} : ‖iteratedFDeriv Real i f x‖ <= N[𝕜]_{K, n, i} f
参数：hin : i <= n；E, F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.structureMapLM_apply`：structureMapLM_apply {i : N
at} (f : 𝓓^{n}_{K}(E, F)) : structureMapLM 𝕜 n i f = if i <= n then iteratedFDer
iv Real i f else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
-/
theorem norm_iteratedFDeriv_apply_le_seminorm {i : ℕ} (hin : i ≤ n)
    {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    ‖iteratedFDeriv ℝ i f x‖ ≤ N[𝕜]_{K, n, i} f :=
  calc
      ‖iteratedFDeriv ℝ i f x‖
  _ = ‖structureMapLM ℝ n i f x‖ := by simp [structureMapLM_apply, hin]
  _ ≤ ‖structureMapLM ℝ n i f‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
  _ = N[𝕜]_{K, n, i} f := rfl
/-
**ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top** 是 Mathlib 中
的一个定理，位于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：norm_iteratedFDeriv_apply_le_seminorm_top {i : Nat} {f : 𝓓_{K}(E, F)} {x :
 E} : ‖iteratedFDeriv Real i f x‖ <= N[𝕜]_{K, i} f
参数：E, F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm`：norm_itera
tedFDeriv_apply_le_seminorm {i : Nat} (hin : i <= n) {f : 𝓓^{n}_{K}(E, F)} {x : 
E} : ‖iteratedFDeriv Real i f x‖ <= N[𝕜]_{K, n, i}…
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem norm_iteratedFDeriv_apply_le_seminorm_top {i : ℕ}
    {f : 𝓓_{K}(E, F)} {x : E} :
    ‖iteratedFDeriv ℝ i f x‖ ≤ N[𝕜]_{K, i} f :=
  norm_iteratedFDeriv_apply_le_seminorm 𝕜 (mod_cast le_top)
/-
**ContDiffMapSupportedIn.norm_apply_le_seminorm** 是 Mathlib 中的一个定理，位于命名空间 `ContD
iffMapSupportedIn`。
形式化陈述：norm_apply_le_seminorm {f : 𝓓^{n}_{K}(E, F)} {x : E} : ‖f x‖ <= N[𝕜]_{K, n
, 0} f
参数：E, F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_iteratedFDeriv_zero`：norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0
 f x‖ = ‖f x‖
· 使用定理 `ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm`：norm_itera
tedFDeriv_apply_le_seminorm {i : Nat} (hin : i <= n) {f : 𝓓^{n}_{K}(E, F)} {x : 
E} : ‖iteratedFDeriv Real i f x‖ <= N[𝕜]_{K, n, i}…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
theorem norm_apply_le_seminorm {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    ‖f x‖ ≤ N[𝕜]_{K, n, 0} f := by
  rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := f) (x := x)]
  exact norm_iteratedFDeriv_apply_le_seminorm 𝕜 zero_le
/-
**ContDiffMapSupportedIn.norm_toBoundedContinuousFunction** 是 Mathlib 中的一个定理，位于命
名空间 `ContDiffMapSupportedIn`。
形式化陈述：norm_toBoundedContinuousFunction (f : 𝓓^{n}_{K}(E, F)) : ‖(f : E ->ᵇ F)‖ =
 N[𝕜]_{K, n, 0} f
参数：f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContDiffMapSupportedInClass.instBoundedContinuousMapClass`：∀ (B : Type u
_5) (E : outParam (Type u_6)) (F : outParam (Type u_7)) [inst : NormedAddCommGro
up E]   [inst_1 : NormedAddCommGroup F] [inst_2…
· 使用定理 `BoundedContinuousMapClass.map_bounded`：∀ {F : Type u_2} {α : outParam (T
ype u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst_1 : Pseu
doMetricSpace β} {inst_2 : …
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.norm_eq_iSup_norm`：norm_eq_iSup_norm : ‖f‖ = ⨆
 x : α, ‖f x‖
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.structureMapCLM_apply`：structureMapCLM_apply {i :
 Nat} (f : 𝓓^{n}_{K}(E, F)) : structureMapCLM 𝕜 n i f = if i <= n then iteratedF
Deriv Real i f else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `norm_iteratedFDeriv_zero`：norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0
 f x‖ = ‖f x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_toBoundedContinuousFunction (f : 𝓓^{n}_{K}(E, F)) :
    ‖(f : E →ᵇ F)‖ = N[𝕜]_{K, n, 0} f := by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm,
    ContDiffMapSupportedIn.seminorm_apply, structureMapCLM_apply]

/-- Define a continuous `𝕜`-linear map from `𝓓^{n₁}_{K₁}(E, F)` to `𝓓^{n₂}_{K₂}(E, F')`. -/
/-
**ContDiffMapSupportedIn.mkCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSupportedIn
`。
形式化陈述：(𝕜 : Type u_1) →   {E : Type u_2} →     {F : Type u_3} →       {F' : Type 
u_4} →         [inst : NontriviallyNormedField 𝕜] →           [inst_1 : NormedAd
dCommGroup E] →             [inst_2 : NormedSpace ℝ E] →               [inst_3 :
 NormedAddCommGroup F] →                 [inst_4 : NormedSpace ℝ F] →           
        [inst_5 : NormedSpace 𝕜 F] →                     [inst_6 : SMulCommClass
 ℝ 𝕜 F] →                       [inst_7 : NormedAddCommGroup F'] →              
           [inst_8 : NormedSpace ℝ F'] →                           [inst_9 : Nor
medSpace 𝕜 F'] →                             [inst_10 : SMulCommClass ℝ 𝕜 F'] → 
                              {n₁ n₂ : ℕ∞} →                                 {K₁
 K₂ : TopologicalSpace.Compacts E} →                                   (A : Cont
DiffMapSupportedIn E F n₁ K₁ → E → F') →                                     (∀ 
(f g : ContDiffMapSupportedIn E F n₁ K₁) (x : E), A (f + g) x = A f x + A g x) →
                                       (∀ (c : 𝕜) (f : ContDiffMapSupportedIn E 
F n₁ K₁) (x : E),                                           A (c • f) x = c • A 
f x) →                                         (∀ (f : ContDiffMapSupportedIn E 
F n₁ K₁), ContDiff ℝ (↑n₂) (A f)) →                                           (∀
 (f : ContDiffMapSupportedIn E F n₁ K₁), Set.EqOn (A f) 0 (↑K₂)ᶜ) →             
                                (∀ (i : ℕ),                                     
            ↑i ≤ n₂ →                                                   ∃ s C,  
                                                   0 ≤ C ∧                      
                                 ∀ (f : ContDiffMapSupportedIn E F n₁ K₁),      
                                                   ∀ x ∈ K₂,                    
                                       ‖iteratedFDeriv ℝ i (A f) x‖ ≤           
                                                  C *                           
                                    (s.sup fun j =>                             
                                      ContDiffMapSupportedIn.seminorm 𝕜 E F n₁ K
₁ j)                                                                 f) →       
                                        ContDiffMapSupportedIn E F n₁ K₁ →L[𝕜] C
ontDiffMapSupportedIn E F' n₂ K₂
参数：f g : ContDiffMapSupportedIn E F n₁ K₁；x : E；f + g；c : 𝕜；f : ContDiffMapSuppo
rtedIn E F n₁ K₁；x : E；c • f；f : ContDiffMapSupportedIn E F n₁ K₁；↑n₂；A f；f : Co
ntDiffMapSupportedIn E F n₁ K₁；A f；↑K₂；i : ℕ；f : ContDiffMapSupportedIn E F n₁ K
₁；A f；s.sup fun j =>                                                            
       ContDiffMapSupportedIn.seminorm 𝕜 E F n₁ K₁ j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a continuous `𝕜`-linear map from `𝓓^{n₁}_{K₁}(E, F)` to `𝓓^{n₂}_{K₂}(E, F
')`.
-/
protected noncomputable def mkCLM (A : 𝓓^{n₁}_{K₁}(E, F) → E → F')
    (hadd : ∀ f g x, A (f + g) x = A f x + A g x)
    (hsmul : ∀ (c : 𝕜) f x, A (c • f) x = c • A f x)
    (hsmooth : ∀ f, ContDiff ℝ n₂ (A f))
    (hsupp : ∀ f, EqOn (A f) 0 K₂ᶜ)
    (hbound : ∀ i : ℕ, i ≤ n₂ → ∃ (s : Finset ℕ) (C : ℝ), 0 ≤ C ∧ ∀ f, ∀ x ∈ K₂,
      ‖iteratedFDeriv ℝ i (A f) x‖ ≤ C * (s.sup fun j ↦ N[𝕜]_{K₁, n₁, j}) f) :
    𝓓^{n₁}_{K₁}(E, F) →L[𝕜] 𝓓^{n₂}_{K₂}(E, F') :=
  letI Φ : 𝓓^{n₁}_{K₁}(E, F) →ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F') :=
    { toFun f := ⟨A f, hsmooth f, hsupp f⟩
      map_add' f g := ext (hadd f g)
      map_smul' c f := ext (hsmul c f) }
  { toLinearMap := Φ
    cont := show Continuous Φ by
      refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      by_cases hi : i ≤ n₂
      · obtain ⟨s, C, hC, h⟩ := hbound i hi
        exact ⟨s, C, fun f ↦ ((Φ f).seminorm_le_iff 𝕜 (mul_nonneg hC (apply_nonneg _ _)) i).2
          fun _ x hx ↦ h f x hx⟩
      · exact ⟨∅, 0, fun f ↦ by
          simp [ContDiffMapSupportedIn.seminorm_eq_bot_of_gt 𝕜 (not_le.1 hi)]⟩ }

/-- Define a continous `𝕜`-linear map fom `𝓓^{n}_{K}(E, F)` to a normed space. -/
/-
**ContDiffMapSupportedIn.mkCLMtoNormedSpace** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffM
apSupportedIn`。
形式化陈述：(𝕜 : Type u_1) →   {E : Type u_2} →     {F : Type u_3} →       [inst : Non
triviallyNormedField 𝕜] →         [inst_1 : NormedAddCommGroup E] →           [i
nst_2 : NormedSpace ℝ E] →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace ℝ F] →                 [inst_5 : NormedSpace 𝕜 F] →
                   [inst_6 : SMulCommClass ℝ 𝕜 F] →                     {n : ℕ∞}
 →                       {K : TopologicalSpace.Compacts E} →                    
     {G : Type u_5} →                           [inst_7 : NormedAddCommGroup G] 
→                             [inst_8 : NormedSpace 𝕜 G] →                      
         (A : ContDiffMapSupportedIn E F n K → G) →                             
    (∀ (f g : ContDiffMapSupportedIn E F n K), A (f + g) = A f + A g) →         
                          (∀ (c : 𝕜) (f : ContDiffMapSupportedIn E F n K), A (c 
• f) = c • A f) →                                     (∃ s C,                   
                      0 ≤ C ∧                                           ∀ (f : C
ontDiffMapSupportedIn E F n K),                                             ‖A f
‖ ≤                                               C * (s.sup fun i => ContDiffMa
pSupportedIn.seminorm 𝕜 E F n K i) f) →                                       Co
ntDiffMapSupportedIn E F n K →L[𝕜] G
参数：f g : ContDiffMapSupportedIn E F n K；f + g；c : 𝕜；f : ContDiffMapSupportedIn E
 F n K；c • f；f : ContDiffMapSupportedIn E F n K；s.sup fun i => ContDiffMapSuppor
tedIn.seminorm 𝕜 E F n K i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a continous `𝕜`-linear map fom `𝓓^{n}_{K}(E, F)` to a normed space.
-/
protected noncomputable def mkCLMtoNormedSpace {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (A : 𝓓^{n}_{K}(E, F) → G)
    (hadd : ∀ f g, A (f + g) = A f + A g)
    (hsmul : ∀ (c : 𝕜) f, A (c • f) = c • A f)
    (hbound : ∃ (s : Finset ℕ) (C : ℝ), 0 ≤ C ∧ ∀ f,
      ‖A f‖ ≤ C * (s.sup fun i ↦ N[𝕜]_{K, n, i}) f) :
    𝓓^{n}_{K}(E, F) →L[𝕜] G :=
  letI Φ : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] G := ⟨⟨A, hadd⟩, hsmul⟩
  { toLinearMap := Φ
    cont := show Continuous Φ by
      obtain ⟨s, C, hC, h⟩ := hbound
      exact continuous_normedSpace_rng G (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K)
        Φ ⟨s, ⟨C, hC⟩, h⟩ }

/-- The inclusion of the space `𝓓^{n}_{K}(E, F)` into the space `E →ᵇ F` of bounded continuous
functions as a continuous `𝕜`-linear map. -/
/-
**ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM** 是 Mathlib 中的一个定义，位于命名空
间 `ContDiffMapSupportedIn`。
形式化陈述：toBoundedContinuousFunctionCLM : 𝓓^{n}_{K}(E, F) ->L[𝕜] E ->ᵇ F where toLi
nearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the space `𝓓^{n}_{K}(E, F)` into the space `E →ᵇ F` of bounded 
continuous
functions as a continuous `𝕜`-linear map.
-/
noncomputable def toBoundedContinuousFunctionCLM : 𝓓^{n}_{K}(E, F) →L[𝕜] E →ᵇ F where
  toLinearMap := toBoundedContinuousFunctionLM 𝕜
  cont := show Continuous (toBoundedContinuousFunctionLM 𝕜) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (norm_withSeminorms 𝕜 _) _ (fun _ ↦ ⟨{0}, 1, fun f ↦ ?_⟩)
    simp [norm_toBoundedContinuousFunction 𝕜 f]

@[simp]
/-
**ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM_apply** 是 Mathlib 中的一个引理
，位于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：toBoundedContinuousFunctionCLM_apply (f : 𝓓^{n}_{K}(E, F)) : toBoundedCont
inuousFunctionCLM 𝕜 f = f
参数：f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma toBoundedContinuousFunctionCLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    toBoundedContinuousFunctionCLM 𝕜 f = f :=
  rfl
/-
**ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM_eq_of_scalars** 是 Mathli
b 中的一个引理，位于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：toBoundedContinuousFunctionCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNor
medField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass Real 𝕜' F] : (toBoundedContinuous
FunctionCLM 𝕜 : 𝓓^{n}_{K}(E, F) -> _) = toBoundedContinuousFunctionCLM 𝕜'
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma toBoundedContinuousFunctionCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n}_{K}(E, F) → _) = toBoundedContinuousFunctionCLM 𝕜' :=
  rfl
/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousEval 𝓓^{n}_{K}(E, F) E F :=
  ContinuousEval.of_continuous_forget
    (toBoundedContinuousFunctionCLM ℝ).continuous
/-
**ContDiffMapSupportedIn.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffMapSupportedIn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T3Space 𝓓^{n}_{K}(E, F) :=
  have : Injective (toBoundedContinuousFunctionCLM ℝ : 𝓓^{n}_{K}(E, F) →L[ℝ] E →ᵇ F) :=
    fun _ _ hfg ↦ ext fun x ↦ congr(($hfg : E → F) x)
  have : T2Space 𝓓^{n}_{K}(E, F) := .of_injective_continuous this
    (toBoundedContinuousFunctionCLM ℝ).continuous
  inferInstance
/-
**ContDiffMapSupportedIn.seminorm_postcompLM_le** 是 Mathlib 中的一个定理，位于命名空间 `ContD
iffMapSupportedIn`。
形式化陈述：seminorm_postcompLM_le [LinearMap.CompatibleSMul F F' Real 𝕜] {i : Nat} (T
 : F ->L[𝕜] F') (f : 𝓓^{n}_{K}(E, F)) : N[𝕜]_{K, n, i} (postcompLM T f) <= ‖T‖ *
 N[𝕜]_{K, n, i} f
参数：T : F ->L[𝕜] F'；f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffMapSupportedIn.seminorm_le_iff`：∀ (𝕜 : Type u_1) {E : Type u_2} 
{F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E
]   [inst_2 : NormedSpace ℝ …
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用引理 `ContDiffMapSupportedIn.postcompLM_apply`：postcompLM_apply [LinearMap.Com
patibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F') (f : 𝓓^{n}_{K}(E, F)) : postcompLM T 
f = T ∘ f
· 使用定理 `ContinuousLinearMap.iteratedFDeriv_comp_left`：ContinuousLinearMap.iterat
edFDeriv_comp_left {f : E -> F} (g : F ->L[𝕜] G) (hf : ContDiffAt 𝕜 n f x) {i : 
Nat} (hi : i <= n) : iteratedFDeri…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `ContDiffMapSupportedIn.contDiff`：∀ {E : Type u_2} {F : Type u_3} [inst :
 NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F
]   [inst_3 : NormedS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.norm_compContinuousMultilinearMap_le`：norm_compConti
nuousMultilinearMap_le (g : G ->L[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E G) : 
‖g.compContinuousMultilinearMap f‖ <= ‖g‖ * ‖f…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm`：norm_itera
tedFDeriv_apply_le_seminorm {i : Nat} (hin : i <= n) {f : 𝓓^{n}_{K}(E, F)} {x : 
E} : ‖iteratedFDeriv Real i f x‖ <= N[𝕜]_{K, n, i}…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem seminorm_postcompLM_le [LinearMap.CompatibleSMul F F' ℝ 𝕜] {i : ℕ} (T : F →L[𝕜] F')
    (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} (postcompLM T f) ≤ ‖T‖ * N[𝕜]_{K, n, i} f := by
  set T' := T.restrictScalars ℝ
  change N[ℝ]_{K, n, i} (postcompLM T' f) ≤ ‖T'‖ * N[ℝ]_{K, n, i} f
  rw [ContDiffMapSupportedIn.seminorm_le_iff ℝ (by positivity)]
  intro hi x hx
  rw [postcompLM_apply]
  calc
      ‖iteratedFDeriv ℝ i (T' ∘ f) x‖
  _ = ‖T'.compContinuousMultilinearMap (iteratedFDeriv ℝ i f x)‖ := by
        rw [T'.iteratedFDeriv_comp_left f.contDiff.contDiffAt (mod_cast hi)]
  _ ≤ ‖T'‖ * ‖iteratedFDeriv ℝ i f x‖ := T'.norm_compContinuousMultilinearMap_le _
  _ ≤ ‖T'‖ * N[ℝ]_{K, n, i} f := by grw [norm_iteratedFDeriv_apply_le_seminorm ℝ hi]

variable {𝕜} in
-- Note: generalizing this to a semilinear setting would require a semilinear version of
-- `CompatibleSMul`.
/-- Given `T : F →L[𝕜] F'`, `postcompCLM T` is the continuous `𝕜`-linear-map sending
`f : 𝓓^{n}_{K}(E, F)` to `T ∘ f` as an element of `𝓓^{n}_{K}(E, F')`. -/
/-
**ContDiffMapSupportedIn.postcompCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSuppo
rtedIn`。
形式化陈述：postcompCLM [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F') : 𝓓^{
n}_{K}(E, F) ->L[𝕜] 𝓓^{n}_{K}(E, F') where toLinearMap
参数：T : F ->L[𝕜] F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `T : F →L[𝕜] F'`, `postcompCLM T` is the continuous `𝕜`-linear-map sending
`f : 𝓓^{n}_{K}(E, F)` to `T ∘ f` as an element of `𝓓^{n}_{K}(E, F')`.
-/
noncomputable def postcompCLM [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F') :
    𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{n}_{K}(E, F') where
  toLinearMap := postcompLM T
  cont := show Continuous (postcompLM T) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ⟨{i}, ‖T‖, fun f ↦ ?_⟩)
    simpa using seminorm_postcompLM_le 𝕜 T f

@[simp]
/-
**ContDiffMapSupportedIn.postcompCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContDiffMa
pSupportedIn`。
形式化陈述：postcompCLM_apply [LinearMap.CompatibleSMul F F' Real 𝕜] (T : F ->L[𝕜] F')
 (f : 𝓓^{n}_{K}(E, F)) : postcompCLM T f = T ∘ f
参数：T : F ->L[𝕜] F'；f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma postcompCLM_apply [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F')
    (f : 𝓓^{n}_{K}(E, F)) :
    postcompCLM T f = T ∘ f :=
  rfl
/-
**ContDiffMapSupportedIn.seminorm_monoLM_le** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffM
apSupportedIn`。
形式化陈述：seminorm_monoLM_le {i : Nat} (f : 𝓓^{n₁}_{K₁}(E, F)) : N[𝕜]_{K₂, n₂, i} (m
onoLM 𝕜 f) <= N[𝕜]_{K₁, n₁, i} f
参数：f : 𝓓^{n₁}_{K₁}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContDiffMapSupportedIn.monoLM_apply`：monoLM_apply (f : 𝓓^{n₁}_{K₁}(E, F)
) : ((monoLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F)) : E -> F) = if n₂ <= n₁ ∧ K₁ <= K₂ then f 
else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm`：norm_itera
tedFDeriv_apply_le_seminorm {i : Nat} (hin : i <= n) {f : 𝓓^{n}_{K}(E, F)} {x : 
E} : ‖iteratedFDeriv Real i f x‖ <= N[𝕜]_{K, n, i}…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `ContDiffMapSupportedIn.monoLM_eq_zero`：monoLM_eq_zero (H : ¬ (n₂ <= n₁ ∧
 K₁ <= K₂)) : (monoLM 𝕜 : 𝓓^{n₁}_{K₁}(E, F) ->ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F)) = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
-/
theorem seminorm_monoLM_le {i : ℕ} (f : 𝓓^{n₁}_{K₁}(E, F)) :
    N[𝕜]_{K₂, n₂, i} (monoLM 𝕜 f) ≤ N[𝕜]_{K₁, n₁, i} f := by
  by_cases H : n₂ ≤ n₁ ∧ K₁ ≤ K₂
  · simp (discharger := positivity) only [ContDiffMapSupportedIn.seminorm_le_iff, monoLM_apply, H,
      and_self, ↓reduceIte]
    intro hik _ _
    exact norm_iteratedFDeriv_apply_le_seminorm _ (hik.trans (mod_cast H.1))
  · simp [monoLM_eq_zero, H]
/-
**ContDiffMapSupportedIn.seminorm_monoLM_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffM
apSupportedIn`。
形式化陈述：seminorm_monoLM_eq {i : Nat} (h₁ : n₁ = n₂) (h₂ : K₁ <= K₂) (f : 𝓓^{n₁}_{K
₁}(E, F)) : N[𝕜]_{K₂, n₂, i} (monoLM 𝕜 f) = N[𝕜]_{K₁, n₁, i} f
参数：h₁ : n₁ = n₂；h₂ : K₁ <= K₂；f : 𝓓^{n₁}_{K₁}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `BoundedContinuousFunction.norm_eq_iSup_norm`：norm_eq_iSup_norm : ‖f‖ = ⨆
 x : α, ‖f x‖
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.structureMapCLM_apply`：structureMapCLM_apply {i :
 Nat} (f : 𝓓^{n}_{K}(E, F)) : structureMapCLM 𝕜 n i f = if i <= n then iteratedF
Deriv Real i f else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ContDiffMapSupportedIn.monoLM_apply`：monoLM_apply (f : 𝓓^{n₁}_{K₁}(E, F)
) : ((monoLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F)) : E -> F) = if n₂ <= n₁ ∧ K₁ <= K₂ then f 
else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem seminorm_monoLM_eq {i : ℕ} (h₁ : n₁ = n₂) (h₂ : K₁ ≤ K₂) (f : 𝓓^{n₁}_{K₁}(E, F)) :
    N[𝕜]_{K₂, n₂, i} (monoLM 𝕜 f) = N[𝕜]_{K₁, n₁, i} f := by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm, ContDiffMapSupportedIn.seminorm_apply,
    structureMapCLM_apply, h₁, h₂]

/-- If `n₁ ≥ n₂` and `K₁ ⊆ K₂`, `monoCLM 𝕜` is the continuous `𝕜`-linear inclusion of
`𝓓^{n₁}_{K₁}(E, F)` inside `𝓓^{n₂}_{K₂}(E, F)`. Otherwise, this is the zero map.

Furthermore:
* it is a topological embedding when `n₁ = n₂` and `K₁ ⊆ K₂` (not in Mathlib as of March 2026).
* it maps bounded sets to compact sets when `n₁ ≥ n₂ + 1` and `K₁ ⊆ K₂` (not in Mathlib as of
March 2026).

The parameters `n₁, n₂, K₁, K₂` are implicit as they can often be inferred from context, or
specified by a type ascription.
-/
/-
**ContDiffMapSupportedIn.monoCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSupported
In`。
形式化陈述：monoCLM : 𝓓^{n₁}_{K₁}(E, F) ->L[𝕜] 𝓓^{n₂}_{K₂}(E, F) where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `n₁ ≥ n₂` and `K₁ ⊆ K₂`, `monoCLM 𝕜` is the continuous `𝕜`-linear inclusion o
f
`𝓓^{n₁}_{K₁}(E, F)` inside `𝓓^{n₂}_{K₂}(E, F)`. Otherwise, this is the zero map.

Furthermore:
* it is a topological embedding when `n₁ = n₂` and `K₁ ⊆ K₂` (not in Mathlib as 
of March 2026).
* it maps bounded sets to compact sets when `n₁ ≥ n₂ + 1` and `K₁ ⊆ K₂` (not in 
Mathlib as of
March 2026).

The parameters `n₁, n₂, K₁, K₂` are implicit as they can often be inferred from 
context, or
specified by a type ascription.
-/
noncomputable def monoCLM :
    𝓓^{n₁}_{K₁}(E, F) →L[𝕜] 𝓓^{n₂}_{K₂}(E, F) where
  toLinearMap := monoLM 𝕜
  cont := show Continuous (monoLM 𝕜) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
      (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _) _ (fun i ↦ ⟨{i}, 1, fun f ↦ ?_⟩)
    simpa using seminorm_monoLM_le 𝕜 f

open scoped Classical in
@[simp]
/-
**ContDiffMapSupportedIn.monoCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContDiffMapSup
portedIn`。
形式化陈述：monoCLM_apply (f : 𝓓^{n₁}_{K₁}(E, F)) : ((monoCLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F))
 : E -> F) = if n₂ <= n₁ ∧ K₁ <= K₂ then f else 0
参数：f : 𝓓^{n₁}_{K₁}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffMapSupportedIn.monoLM_apply`：monoLM_apply (f : 𝓓^{n₁}_{K₁}(E, F)
) : ((monoLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F)) : E -> F) = if n₂ <= n₁ ∧ K₁ <= K₂ then f 
else 0
-/
lemma monoCLM_apply (f : 𝓓^{n₁}_{K₁}(E, F)) :
    ((monoCLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F)) : E → F) = if n₂ ≤ n₁ ∧ K₁ ≤ K₂ then f else 0 :=
  monoLM_apply 𝕜 f
/-
**ContDiffMapSupportedIn.monoCLM_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `ContDiffMapS
upportedIn`。
形式化陈述：monoCLM_eq_zero (H : ¬ (n₂ <= n₁ ∧ K₁ <= K₂)) : (monoCLM 𝕜 : 𝓓^{n₁}_{K₁}(E
, F) ->L[𝕜] 𝓓^{n₂}_{K₂}(E, F)) = 0
参数：H : ¬ (n₂ <= n₁ ∧ K₁ <= K₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffMapSupportedIn.ext`：ext {f g : 𝓓^{n}_{K}(E, F)} (h : forall a, f
 a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.monoCLM_apply`：monoCLM_apply (f : 𝓓^{n₁}_{K₁}(E, 
F)) : ((monoCLM 𝕜 f : 𝓓^{n₂}_{K₂}(E, F)) : E -> F) = if n₂ <= n₁ ∧ K₁ <= K₂ then
 f else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContDiffMapSupportedIn.instIsZeroApply`：∀ {E : Type u_2} {F : Type u_3} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma monoCLM_eq_zero (H : ¬ (n₂ ≤ n₁ ∧ K₁ ≤ K₂)) :
    (monoCLM 𝕜 : 𝓓^{n₁}_{K₁}(E, F) →L[𝕜] 𝓓^{n₂}_{K₂}(E, F)) = 0 := by
  ext; simp [H]
/-
**ContDiffMapSupportedIn.monoCLM_eq_of_scalars** 是 Mathlib 中的一个引理，位于命名空间 `ContDi
ffMapSupportedIn`。
形式化陈述：monoCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedSpa
ce 𝕜' F] [SMulCommClass Real 𝕜' F] : (monoCLM 𝕜 : 𝓓^{n₁}_{K₁}(E, F) -> 𝓓^{n₂}_{K
₂}(E, F)) = monoCLM 𝕜'
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma monoCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (monoCLM 𝕜 : 𝓓^{n₁}_{K₁}(E, F) → 𝓓^{n₂}_{K₂}(E, F)) = monoCLM 𝕜' :=
  rfl
/-
**ContDiffMapSupportedIn.seminorm_fderivLM_le** 是 Mathlib 中的一个定理，位于命名空间 `ContDif
fMapSupportedIn`。
形式化陈述：seminorm_fderivLM_le {i : Nat} (f : 𝓓^{n}_{K}(E, F)) : N[𝕜]_{K, k, i} (fde
rivLM 𝕜 n k f) <= N[𝕜]_{K, n, i + 1} f
参数：f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffMapSupportedIn.seminorm_le_iff`：∀ (𝕜 : Type u_1) {E : Type u_2} 
{F : Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E
]   [inst_2 : NormedSpace ℝ …
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ContDiffMapSupportedIn.fderivLM_apply`：fderivLM_apply (f : 𝓓^{n}_{K}(E, 
F)) : fderivLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `norm_iteratedFDeriv_fderiv`：norm_iteratedFDeriv_fderiv {n : Nat} : ‖iter
atedFDeriv 𝕜 n (fderiv 𝕜 f) x‖ = ‖iteratedFDeriv 𝕜 (n + 1) f x‖
· 使用定理 `ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm`：norm_itera
tedFDeriv_apply_le_seminorm {i : Nat} (hin : i <= n) {f : 𝓓^{n}_{K}(E, F)} {x : 
E} : ‖iteratedFDeriv Real i f x‖ <= N[𝕜]_{K, n, i}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `ContDiffMapSupportedIn.fderivLM_apply_of_gt`：fderivLM_apply_of_gt (f : 𝓓
^{n}_{K}(E, F)) (hk : n < k + 1) : fderivLM 𝕜 n k f = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
-/
theorem seminorm_fderivLM_le {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, k, i} (fderivLM 𝕜 n k f) ≤ N[𝕜]_{K, n, i + 1} f := by
  by_cases! hk : k + 1 ≤ n
  · rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 (apply_nonneg ..)]
    intro hi x hx
    have hi' : i + 1 ≤ n := (add_le_add_left hi 1).trans hk
    simpa [hk, norm_iteratedFDeriv_fderiv] using
      norm_iteratedFDeriv_apply_le_seminorm 𝕜 hi'
  · simp [fderivLM_apply_of_gt 𝕜 f hk]
/-
**ContDiffMapSupportedIn.seminorm_fderivLM_top** 是 Mathlib 中的一个定理，位于命名空间 `ContDi
ffMapSupportedIn`。
形式化陈述：seminorm_fderivLM_top {i : Nat} (f : 𝓓_{K}(E, F)) : N[𝕜]_{K, i} (fderivLM 
𝕜 ⊤ ⊤ f) = N[𝕜]_{K, i + 1} f
参数：f : 𝓓_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `BoundedContinuousFunction.norm_eq_iSup_norm`：norm_eq_iSup_norm : ‖f‖ = ⨆
 x : α, ‖f x‖
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ContDiffMapSupportedIn.structureMapCLM_apply`：structureMapCLM_apply {i :
 Nat} (f : 𝓓^{n}_{K}(E, F)) : structureMapCLM 𝕜 n i f = if i <= n then iteratedF
Deriv Real i f else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ContDiffMapSupportedIn.fderivLM_apply`：fderivLM_apply (f : 𝓓^{n}_{K}(E, 
F)) : fderivLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `norm_iteratedFDeriv_fderiv`：norm_iteratedFDeriv_fderiv {n : Nat} : ‖iter
atedFDeriv 𝕜 n (fderiv 𝕜 f) x‖ = ‖iteratedFDeriv 𝕜 (n + 1) f x‖
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem seminorm_fderivLM_top {i : ℕ} (f : 𝓓_{K}(E, F)) :
    N[𝕜]_{K, i} (fderivLM 𝕜 ⊤ ⊤ f) = N[𝕜]_{K, i + 1} f := by
  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.norm_eq_iSup_norm,
    norm_iteratedFDeriv_fderiv]

variable (n k) in
/-- `fderivCLM 𝕜 n k` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its derivative as an element of `𝓓^{k}_{K}(E, E →L[ℝ] F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the zero map. -/
/-
**ContDiffMapSupportedIn.fderivCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSupport
edIn`。
形式化陈述：fderivCLM : 𝓓^{n}_{K}(E, F) ->L[𝕜] 𝓓^{k}_{K}(E, E ->L[Real] F) where toLin
earMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fderivCLM 𝕜 n k` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)`
 to
its derivative as an element of `𝓓^{k}_{K}(E, E →L[ℝ] F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the
 zero map.
-/
noncomputable def fderivCLM :
    𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{k}_{K}(E, E →L[ℝ] F) where
  toLinearMap := fderivLM 𝕜 n k
  cont := show Continuous (fderivLM 𝕜 n k) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (fun i ↦ ⟨{i+1}, 1, fun f ↦ ?_⟩)
    simpa using seminorm_fderivLM_le 𝕜 f

@[simp]
/-
**ContDiffMapSupportedIn.fderivCLM_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContDiffMapS
upportedIn`。
形式化陈述：fderivCLM_apply (f : 𝓓^{n}_{K}(E, F)) : fderivCLM 𝕜 n k f = if k + 1 <= n 
then fderiv Real f else 0
参数：f : 𝓓^{n}_{K}(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffMapSupportedIn.fderivLM_apply`：fderivLM_apply (f : 𝓓^{n}_{K}(E, 
F)) : fderivLM 𝕜 n k f = if k + 1 <= n then fderiv Real f else 0
-/
lemma fderivCLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    fderivCLM 𝕜 n k f = if k + 1 ≤ n then fderiv ℝ f else 0 :=
  fderivLM_apply 𝕜 f
/-
**ContDiffMapSupportedIn.fderivCLM_apply_of_le** 是 Mathlib 中的一个引理，位于命名空间 `ContDi
ffMapSupportedIn`。
形式化陈述：fderivCLM_apply_of_le (f : 𝓓^{n}_{K}(E, F)) (hk : k + 1 <= n) : fderivCLM 
𝕜 n k f = fderiv Real f
参数：f : 𝓓^{n}_{K}(E, F)；hk : k + 1 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffMapSupportedIn.fderivLM_apply_of_le`：fderivLM_apply_of_le (f : 𝓓
^{n}_{K}(E, F)) (hk : k + 1 <= n) : fderivLM 𝕜 n k f = fderiv Real f
-/
lemma fderivCLM_apply_of_le (f : 𝓓^{n}_{K}(E, F)) (hk : k + 1 ≤ n) :
    fderivCLM 𝕜 n k f = fderiv ℝ f :=
  fderivLM_apply_of_le 𝕜 f hk
/-
**ContDiffMapSupportedIn.fderivCLM_apply_of_gt** 是 Mathlib 中的一个引理，位于命名空间 `ContDi
ffMapSupportedIn`。
形式化陈述：fderivCLM_apply_of_gt (f : 𝓓^{n}_{K}(E, F)) (hk : n < k + 1) : fderivCLM 𝕜
 n k f = 0
参数：f : 𝓓^{n}_{K}(E, F)；hk : n < k + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffMapSupportedIn.fderivLM_apply_of_gt`：fderivLM_apply_of_gt (f : 𝓓
^{n}_{K}(E, F)) (hk : n < k + 1) : fderivLM 𝕜 n k f = 0
-/
lemma fderivCLM_apply_of_gt (f : 𝓓^{n}_{K}(E, F)) (hk : n < k + 1) :
    fderivCLM 𝕜 n k f = 0 :=
  fderivLM_apply_of_gt 𝕜 f hk
/-
**ContDiffMapSupportedIn.fderivCLM_eq_of_scalars** 是 Mathlib 中的一个引理，位于命名空间 `Cont
DiffMapSupportedIn`。
形式化陈述：fderivCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedS
pace 𝕜' F] [SMulCommClass Real 𝕜' F] : (fderivCLM 𝕜 n k : 𝓓^{n}_{K}(E, F) -> _) 
= fderivCLM 𝕜' n k
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
-/
lemma fderivCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (fderivCLM 𝕜 n k : 𝓓^{n}_{K}(E, F) → _) = fderivCLM 𝕜' n k :=
  rfl

end Topology

section Integral

open MeasureTheory

variable {𝕜} {m : MeasurableSpace E} [OpensMeasurableSpace E] {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]

@[fun_prop]
/-
**ContDiffMapSupportedIn.stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffM
apSupportedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} {m : MeasurableSpace E} [OpensMeasurableS
pace E]   (f : ContDiffMapSupportedIn E F n K), MeasureTheory.StronglyMeasurable
 ⇑f
参数：f : ContDiffMapSupportedIn E F n K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.stronglyMeasurable_of_hasCompactSupport`：∀ {α : Type u_1} {β 
: Type u_2} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace α] [OpensMeasu
rableSpace α]   [inst_3 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContDiffMapSupportedIn.continuous`：∀ {E : Type u_2} {F : Type u_3} [inst
 : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup
 F]   [inst_3 : NormedS…
· 使用定理 `ContDiffMapSupportedIn.hasCompactSupport`：∀ {E : Type u_2} {F : Type u_3
} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCo
mmGroup F]   [inst_3 : NormedS…
-/
protected theorem stronglyMeasurable (f : 𝓓^{n}_{K}(E, F)) :
    StronglyMeasurable f := by
  exact f.continuous.stronglyMeasurable_of_hasCompactSupport f.hasCompactSupport

@[fun_prop]
/-
**ContDiffMapSupportedIn.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `ContDif
fMapSupportedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} {m : MeasurableSpace E} [OpensMeasurableS
pace E]   {μ : MeasureTheory.Measure E} (f : ContDiffMapSupportedIn E F n K), Me
asureTheory.AEStronglyMeasurable (⇑f) μ
参数：f : ContDiffMapSupportedIn E F n K；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `ContDiffMapSupportedIn.stronglyMeasurable`：∀ {E : Type u_2} {F : Type u_
3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddC
ommGroup F]   [inst_3 : NormedS…
-/
protected theorem aestronglyMeasurable {μ : Measure E} (f : 𝓓^{n}_{K}(E, F)) :
    AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable
/-
**ContDiffMapSupportedIn.memLp_top** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSupport
edIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} {m : MeasurableSpace E} [OpensMeasurableS
pace E]   {μ : MeasureTheory.Measure E} (f : ContDiffMapSupportedIn E F n K), Me
asureTheory.MemLp ⇑f ⊤ μ
参数：f : ContDiffMapSupportedIn E F n K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.memLp_top_of_hasCompactSupport`：∀ {E : Type u_4} [inst : Norm
edAddCommGroup E] {X : Type u_7} [inst_1 : TopologicalSpace X] [inst_2 : Measura
bleSpace X]   [OpensMeasurableS…
· 使用定理 `ContDiffMapSupportedIn.continuous`：∀ {E : Type u_2} {F : Type u_3} [inst
 : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup
 F]   [inst_3 : NormedS…
· 使用定理 `ContDiffMapSupportedIn.hasCompactSupport`：∀ {E : Type u_2} {F : Type u_3
} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCo
mmGroup F]   [inst_3 : NormedS…
-/
protected theorem memLp_top {μ : Measure E} (f : 𝓓^{n}_{K}(E, F)) :
    MemLp f ⊤ μ :=
  f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport μ
/-
**ContDiffMapSupportedIn.integrable** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMapSuppor
tedIn`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {n :
 ℕ∞} {K : TopologicalSpace.Compacts E} {m : MeasurableSpace E} [OpensMeasurableS
pace E]   {μ : MeasureTheory.Measure E} [μ_finite : MeasureTheory.IsFiniteMeasur
e (μ.restrict ↑K)]   (f : ContDiffMapSupportedIn E F n K), MeasureTheory.Integra
ble (⇑f) μ
参数：μ.restrict ↑K；f : ContDiffMapSupportedIn E F n K；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrableOn_iff_integrable_of_support_subset`：integrableO
n_iff_integrable_of_support_subset {f : α -> ε'} (h1s : support f subseteq s) : 
IntegrableOn f s μ ↔ Integrable f μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContDiffMapSupportedIn.support_subset`：∀ {E : Type u_2} {F : Type u_3} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommG
roup F]   [inst_3 : NormedS…
· 使用定理 `Continuous.integrable_of_hasCompactSupport`：Continuous.integrable_of_has
CompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) : Integrable f μ
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `ContDiffMapSupportedIn.continuous`：∀ {E : Type u_2} {F : Type u_3} [inst
 : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup
 F]   [inst_3 : NormedS…
· 使用定理 `ContDiffMapSupportedIn.hasCompactSupport`：∀ {E : Type u_2} {F : Type u_3
} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCo
mmGroup F]   [inst_3 : NormedS…
-/
protected theorem integrable {μ : Measure E} [μ_finite : IsFiniteMeasure (μ.restrict K)]
    (f : 𝓓^{n}_{K}(E, F)) :
    Integrable f μ := by
  rw [← integrableOn_iff_integrable_of_support_subset f.support_subset]
  exact f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
/-
**ContDiffMapSupportedIn.integrable_bilin** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffMap
SupportedIn`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace ℝ E] {n : ℕ∞} {K : TopologicalS
pace.Compacts E} {m : MeasurableSpace E} [OpensMeasurableSpace E]   {F₁ : Type u
_5} {F₂ : Type u_6} {F₃ : Type u_7} [inst_4 : NormedAddCommGroup F₁] [inst_5 : N
ormedSpace 𝕜 F₁]   [inst_6 : NormedSpace ℝ F₁] [inst_7 : NormedAddCommGroup F₂] 
[inst_8 : NormedSpace 𝕜 F₂]   [inst_9 : NormedAddCommGroup F₃] [inst_10 : Normed
Space 𝕜 F₃] (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {μ : MeasureTheory.Measure E}   {φ : E → 
F₂},   MeasureTheory.IntegrableOn φ (↑K) μ →     ∀ (f : ContDiffMapSupportedIn E
 F₁ n K), MeasureTheory.Integrable (fun x => (B (f x)) (φ x)) μ
参数：B : F₁ →L[𝕜] F₂ →L[𝕜] F₃；↑K；f : ContDiffMapSupportedIn E F₁ n K；fun x => (B (
f x)) (φ x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `ContinuousLinearMap.memLp_of_bilin`：memLp_of_bilin {f : α -> E} {g : α -
> F} (hf : MemLp f p μ) (hg : MemLp g q μ) : MemLp (fun x => B (f x) (g x)) r μ
· 使用定理 `ContDiffMapSupportedIn.memLp_top`：∀ {E : Type u_2} {F : Type u_3} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup 
F]   [inst_3 : NormedS…
· 使用定理 `MeasureTheory.integrableOn_iff_integrable_of_support_subset`：integrableO
n_iff_integrable_of_support_subset {f : α -> ε'} (h1s : support f subseteq s) : 
IntegrableOn f s μ ↔ Integrable f μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContDiffMapSupportedIn.support_subset`：∀ {E : Type u_2} {F : Type u_3} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommG
roup F]   [inst_3 : NormedS…
-/
protected theorem integrable_bilin (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {μ : Measure E} {φ : E → F₂}
    (hφ : IntegrableOn φ K μ) (f : 𝓓^{n}_{K}(E, F₁)) :
    Integrable (fun x ↦ B (f x) (φ x)) μ := by
  suffices IntegrableOn (fun x ↦ B (f x) (φ x)) K μ by
    rwa [integrableOn_iff_integrable_of_support_subset] at this
    refine subset_trans ?_ f.support_subset
    exact fun x hx hfx ↦ hx (by simp [hfx])
  rw [IntegrableOn, ← memLp_one_iff_integrable] at hφ ⊢
  exact B.memLp_of_bilin 1 f.memLp_top hφ

variable [SMulCommClass ℝ 𝕜 F₁] [NormedSpace ℝ F₃] [SMulCommClass ℝ 𝕜 F₃]

-- TODO: semilinearize
/-- Given a continuous `𝕜`-bilinear map `B : F₁ →L[𝕜] F₂ →L[𝕜] F₃`, a measure `μ` on `E`,
and a function `φ : E → F₂` which is `μ`-integrable on `K`, this is the `𝕜`-linear map
`f ↦ ∫ x, B (f x) (φ x) ∂μ` from `𝓓^{n}_{K}(E, F₁)` to `F₃`. Otherwise, this is the zero map.

You should probably use `integralAgainstBilinCLM`, which bundles the continuity. -/
/-
**ContDiffMapSupportedIn.integralAgainstBilinLM** 是 Mathlib 中的一个定义，位于命名空间 `ContD
iffMapSupportedIn`。
形式化陈述：integralAgainstBilinLM (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : Measure E) (φ : E
 -> F₂) : 𝓓^{n}_{K}(E, F₁) ->ₗ[𝕜] F₃ where toFun f
参数：B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃；μ : Measure E；φ : E -> F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous `𝕜`-bilinear map `B : F₁ →L[𝕜] F₂ →L[𝕜] F₃`, a measure `μ` on
 `E`,
and a function `φ : E → F₂` which is `μ`-integrable on `K`, this is the `𝕜`-line
ar map
`f ↦ ∫ x, B (f x) (φ x) ∂μ` from `𝓓^{n}_{K}(E, F₁)` to `F₃`. Otherwise, this is 
the zero map.

You should probably use `integralAgainstBilinCLM`, which bundles the continuity.
-/
noncomputable def integralAgainstBilinLM (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (μ : Measure E) (φ : E → F₂) :
    𝓓^{n}_{K}(E, F₁) →ₗ[𝕜] F₃ where
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
/-
**ContDiffMapSupportedIn.integralAgainstBilinLM_apply** 是 Mathlib 中的一个引理，位于命名空间 
`ContDiffMapSupportedIn`。
形式化陈述：integralAgainstBilinLM_apply {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} 
{φ : E -> F₂} {f : 𝓓^{n}_{K}(E, F₁)} : integralAgainstBilinLM B μ φ f = open sco
ped Classical in if IntegrableOn φ K μ then ∫ x, B (f x) (φ x) ∂μ else 0
参数：E, F₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma integralAgainstBilinLM_apply {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinLM B μ φ f = open scoped Classical in
      if IntegrableOn φ K μ then ∫ x, B (f x) (φ x) ∂μ else 0 := by
  rfl
/-
**ContDiffMapSupportedIn.integralAgainstBilinLM_eq_integral** 是 Mathlib 中的一个引理，位
于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：integralAgainstBilinLM_eq_integral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measu
re E} {φ : E -> F₂} (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} : integralA
gainstBilinLM B μ φ f = ∫ x, B (f x) (φ x) ∂μ
参数：hφ : IntegrableOn φ K μ；E, F₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContDiffMapSupportedIn.integralAgainstBilinLM_apply`：integralAgainstBili
nLM_apply {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂} {f : 𝓓^{n}_
{K}(E, F₁)} : integralAgainstBilinLM B μ …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integralAgainstBilinLM_eq_integral {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinLM B μ φ f = ∫ x, B (f x) (φ x) ∂μ := by
  simp [hφ]
/-
**ContDiffMapSupportedIn.integralAgainstBilinLM_eq_setIntegral** 是 Mathlib 中的一个引
理，位于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：integralAgainstBilinLM_eq_setIntegral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Me
asure E} {φ : E -> F₂} (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} : integr
alAgainstBilinLM B μ φ f = ∫ x in K, B (f x) (φ x) ∂μ
参数：hφ : IntegrableOn φ K μ；E, F₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContDiffMapSupportedIn.integralAgainstBilinLM_eq_integral`：integralAgain
stBilinLM_eq_integral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
 (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁…
· 使用定理 `MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero`：setIntegr
al_eq_integral_of_forall_compl_eq_zero (h : forall x, x ∉ s -> f x = 0) : ∫ x in
 s, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `ContDiffMapSupportedIn.zero_on_compl`：∀ {E : Type u_2} {F : Type u_3} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
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
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
lemma integralAgainstBilinLM_eq_setIntegral {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinLM B μ φ f = ∫ x in K, B (f x) (φ x) ∂μ := by
  rw [integralAgainstBilinLM_eq_integral hφ, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [f.zero_on_compl hx, Pi.zero_apply, map_zero, zero_apply]
/-
**ContDiffMapSupportedIn.norm_integralAgainstBilinLM_le** 是 Mathlib 中的一个引理，位于命名空
间 `ContDiffMapSupportedIn`。
形式化陈述：norm_integralAgainstBilinLM_le {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E
} {φ : E -> F₂} {f : 𝓓^{n}_{K}(E, F₁)} : ‖integralAgainstBilinLM B μ φ f‖ <= (∫ 
x in K, ‖φ x‖ ∂μ) * ‖B‖ * N[𝕜]_{K, n, 0} f
参数：E, F₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ContDiffMapSupportedIn.norm_apply_le_seminorm`：norm_apply_le_seminorm {f
 : 𝓓^{n}_{K}(E, F)} {x : E} : ‖f x‖ <= N[𝕜]_{K, n, 0} f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `ContDiffMapSupportedIn.integralAgainstBilinLM_eq_setIntegral`：integralAg
ainstBilinLM_eq_setIntegral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E 
-> F₂} (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E,…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.norm_integral_le_of_norm_le`：norm_integral_le_of_norm_le {
f : α -> G} {g : α -> Real} (hg : Integrable g μ) (h : forallᵐ x ∂μ, ‖f x‖ <= g 
x) : ‖∫ x, f x ∂μ‖ <= ∫ x, g x …
· 使用定理 `MeasureTheory.Integrable.mul_const`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `MeasureTheory.integral_mul_const`：integral_mul_const {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, f a * r ∂μ = (∫ a, f a ∂μ) * r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
（共 42 条，此处仅展示前 30 条）
-/
lemma norm_integralAgainstBilinLM_le {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    {f : 𝓓^{n}_{K}(E, F₁)} :
    ‖integralAgainstBilinLM B μ φ f‖ ≤
      (∫ x in K, ‖φ x‖ ∂μ) * ‖B‖ * N[𝕜]_{K, n, 0} f := by
  by_cases hφ : IntegrableOn φ K μ
  · have h : ∀ᵐ x ∂(μ.restrict K), ‖B (f x) (φ x)‖ ≤ ‖φ x‖ * ‖B‖ * N[𝕜]_{K, n, 0} f := by
      filter_upwards [] with x
      grw [ContinuousLinearMap.le_opNorm, ContinuousLinearMap.le_opNorm, norm_apply_le_seminorm 𝕜,
        mul_comm, mul_assoc]
    rw [integralAgainstBilinLM_eq_setIntegral hφ]
    apply le_trans (norm_integral_le_of_norm_le ((hφ.norm.mul_const _).mul_const _) h)
    rw [integral_mul_const, integral_mul_const]
  · simp only [integralAgainstBilinLM, hφ, ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk, norm_zero]
    positivity

-- TODO: semilinearize
/-- Given a continuous `𝕜`-bilinear map `B : F₁ →L[𝕜] F₂ →L[𝕜] F₃`, a measure `μ` on `E`,
and a function `φ : E → F₂` which is integrable on `K`, this is the *continuous* `𝕜`-linear map
`f ↦ ∫ x, B (f x) (φ x) ∂μ` from `𝓓^{n}_{K}(E, F₁)` to `F₃`. Otherwise, this is the zero map. -/
/-
**ContDiffMapSupportedIn.integralAgainstBilinCLM** 是 Mathlib 中的一个定义，位于命名空间 `Cont
DiffMapSupportedIn`。
形式化陈述：integralAgainstBilinCLM (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (μ : Measure E) (φ : 
E -> F₂) : 𝓓^{n}_{K}(E, F₁) ->L[𝕜] F₃
参数：B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃；μ : Measure E；φ : E -> F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous `𝕜`-bilinear map `B : F₁ →L[𝕜] F₂ →L[𝕜] F₃`, a measure `μ` on
 `E`,
and a function `φ : E → F₂` which is integrable on `K`, this is the *continuous*
 `𝕜`-linear map
`f ↦ ∫ x, B (f x) (φ x) ∂μ` from `𝓓^{n}_{K}(E, F₁)` to `F₃`. Otherwise, this is 
the zero map.
-/
noncomputable def integralAgainstBilinCLM (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (μ : Measure E) (φ : E → F₂) :
    𝓓^{n}_{K}(E, F₁) →L[𝕜] F₃ :=
  ContDiffMapSupportedIn.mkCLMtoNormedSpace 𝕜 (integralAgainstBilinLM B μ φ)
    (integralAgainstBilinLM B μ φ).map_add (integralAgainstBilinLM B μ φ).map_smul
    ⟨{0}, (∫ x in K, ‖φ x‖ ∂μ) * ‖B‖, by positivity,
      fun f ↦ by simpa using! norm_integralAgainstBilinLM_le⟩

@[simp]
/-
**ContDiffMapSupportedIn.integralAgainstBilinCLM_apply** 是 Mathlib 中的一个引理，位于命名空间
 `ContDiffMapSupportedIn`。
形式化陈述：integralAgainstBilinCLM_apply {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E}
 {φ : E -> F₂} {f : 𝓓^{n}_{K}(E, F₁)} : integralAgainstBilinCLM B μ φ f = open s
coped Classical in if IntegrableOn φ K μ then ∫ x, B (f x) (φ x) ∂μ else 0
参数：E, F₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `ContDiffMapSupportedIn.integralAgainstBilinLM_apply`：integralAgainstBili
nLM_apply {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂} {f : 𝓓^{n}_
{K}(E, F₁)} : integralAgainstBilinLM B μ …
-/
lemma integralAgainstBilinCLM_apply {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinCLM B μ φ f = open scoped Classical in
      if IntegrableOn φ K μ then ∫ x, B (f x) (φ x) ∂μ else 0 :=
  integralAgainstBilinLM_apply
/-
**ContDiffMapSupportedIn.integralAgainstBilinCLM_eq_integral** 是 Mathlib 中的一个引理，
位于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：integralAgainstBilinCLM_eq_integral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Meas
ure E} {φ : E -> F₂} (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} : integral
AgainstBilinCLM B μ φ f = ∫ x, B (f x) (φ x) ∂μ
参数：hφ : IntegrableOn φ K μ；E, F₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `ContDiffMapSupportedIn.integralAgainstBilinLM_eq_integral`：integralAgain
stBilinLM_eq_integral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E -> F₂}
 (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁…
-/
lemma integralAgainstBilinCLM_eq_integral {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinCLM B μ φ f = ∫ x, B (f x) (φ x) ∂μ :=
  integralAgainstBilinLM_eq_integral hφ
/-
**ContDiffMapSupportedIn.integralAgainstBilinCLM_eq_setIntegral** 是 Mathlib 中的一个
引理，位于命名空间 `ContDiffMapSupportedIn`。
形式化陈述：integralAgainstBilinCLM_eq_setIntegral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : M
easure E} {φ : E -> F₂} (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} : integ
ralAgainstBilinCLM B μ φ f = ∫ x in K, B (f x) (φ x) ∂μ
参数：hφ : IntegrableOn φ K μ；E, F₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `ContDiffMapSupportedIn.integralAgainstBilinLM_eq_setIntegral`：integralAg
ainstBilinLM_eq_setIntegral {B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃} {μ : Measure E} {φ : E 
-> F₂} (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E,…
-/
lemma integralAgainstBilinCLM_eq_setIntegral {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : IntegrableOn φ K μ) {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinCLM B μ φ f = ∫ x in K, B (f x) (φ x) ∂μ :=
  integralAgainstBilinLM_eq_setIntegral hφ

end Integral

section Multiplication

section bilin

open ContDiffMapSupportedIn

variable {F₁ F₂ F₃ G : Type*} [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [NormedSpace ℝ F₃]

open ContinuousLinearMap Finset

variable {𝕜}
/-- The map `f ↦ (x ↦ B (f x) (g x))` as a continuous `𝕜`-linear map on 𝓓^{n}_{K}(E, F₁),
where `B` is a continuous `𝕜`-linear map and `g` is a C^n function.

TODO: Introduce a type of bundled C^k functions. -/
/-
**ContDiffMapSupportedIn.bilinLeftCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffMapSupp
ortedIn`。
形式化陈述：bilinLeftCLM (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {g : E -> F₂} (hg : ContDiff Rea
l n g) : 𝓓^{n}_{K}(E, F₁) ->L[𝕜] 𝓓^{n}_{K}(E, F₃)
参数：B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃；hg : ContDiff Real n g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `f ↦ (x ↦ B (f x) (g x))` as a continuous `𝕜`-linear map on 𝓓^{n}_{K}(E,
 F₁),
where `B` is a continuous `𝕜`-linear map and `g` is a C^n function.

TODO: Introduce a type of bundled C^k functions.
-/
noncomputable def bilinLeftCLM (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {g : E → F₂} (hg : ContDiff ℝ n g) :
    𝓓^{n}_{K}(E, F₁) →L[𝕜] 𝓓^{n}_{K}(E, F₃) :=
  ContDiffMapSupportedIn.mkCLM 𝕜 (fun φ x ↦ B (φ x) (g x)) ?hadd ?hsmul (fun φ ↦ ?hsmooth)
    (fun φ x hx ↦ ?hsupp) (fun k hk ↦ ?hbound)
where finally
  case hadd | hsmul => intros; simp
  case hsmooth =>
    exact (B.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp (φ.contDiff.prodMk hg)
  case hsupp => simp only [φ.zero_on_compl hx, Pi.zero_apply, map_zero, zero_apply]
  case hbound =>
    have hcont : Continuous fun x ↦ (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
        (fun i ↦ ‖iteratedFDeriv ℝ i g x‖) :=
      Continuous.finset_sup'_apply Finset.nonempty_range_add_one fun i hi ↦
        (hg.continuous_iteratedFDeriv (WithTop.coe_le_coe.2
          (le_trans (WithTop.coe_le_coe.2 (mem_range_succ_iff.mp hi)) hk))).norm
    obtain ⟨C₀, hC₀⟩ := K.isCompact.exists_bound_of_continuousOn hcont.continuousOn
    have hgC₀ : ∀ i ≤ k, ∀ x ∈ K, ‖iteratedFDeriv ℝ i g x‖ ≤ ‖C₀‖ := fun i hi x hx ↦
      (Finset.le_sup' _ (Finset.mem_range_succ_iff.2 hi)).trans
        ((Real.le_norm_self _).trans ((hC₀ x hx).trans (Real.le_norm_self C₀)))
    refine ⟨Finset.Iic k, ‖B‖ * 2 ^ k * ‖C₀‖, by positivity, fun φ x hx ↦ ?_⟩
    calc
      ‖iteratedFDeriv ℝ k (fun y ↦ B (φ y) (g y)) x‖
        ≤ ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ x‖ *
            ‖iteratedFDeriv ℝ (k - i) g x‖ := by
          simpa using (B.bilinearRestrictScalars ℝ).norm_iteratedFDeriv_le_of_bilinear
            φ.contDiff hg x (mod_cast hk)
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            ((Finset.Iic k).sup fun m ↦ N[𝕜]_{K, n, m}) φ * ‖C₀‖ := by
          gcongr with i hi
          · exact (norm_iteratedFDeriv_apply_le_seminorm 𝕜
              ((WithTop.coe_le_coe.2 (mem_range_succ_iff.mp hi)).trans hk)).trans
              (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 (mem_range_succ_iff.mp hi)))
          · exact hgC₀ (k - i) (Nat.sub_le k i) x hx
      _ = ‖B‖ * 2 ^ k * ‖C₀‖ * ((Finset.Iic k).sup fun m ↦ N[𝕜]_{K, n, m}) φ := by
          simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring

@[simp]
/-
**ContDiffMapSupportedIn.bilinLeftCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffM
apSupportedIn`。
形式化陈述：bilinLeftCLM_apply (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {g : E -> F₂} (hg : ContDi
ff Real n g) (φ : 𝓓^{n}_{K}(E, F₁)) : bilinLeftCLM B hg φ = fun x => B (φ x) (g 
x)
参数：B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃；hg : ContDiff Real n g；φ : 𝓓^{n}_{K}(E, F₁)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
-/
theorem bilinLeftCLM_apply (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {g : E → F₂} (hg : ContDiff ℝ n g)
    (φ : 𝓓^{n}_{K}(E, F₁)) : bilinLeftCLM B hg φ = fun x => B (φ x) (g x) := rfl

end bilin

end Multiplication

end ContDiffMapSupportedIn

