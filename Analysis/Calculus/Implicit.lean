/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Module.Complemented

/-!
# Implicit function theorem

We prove three versions of the implicit function theorem. First we define a structure
`ImplicitFunctionData` that holds arguments for the most general version of the implicit function
theorem, see `ImplicitFunctionData.implicitFunction` and
`ImplicitFunctionData.hasStrictFDerivAt_implicitFunction`. This version allows a user to choose a
specific implicit function but provides only a little convenience over the inverse function theorem.

Then we define `HasStrictFDerivAt.implicitFunctionDataOfComplemented`: implicit function defined by
`f (g z y) = z`, where `f : E → F` is a function strictly differentiable at `a` such that its
derivative `f'` is surjective and has a `complemented` kernel.

Finally, if the codomain of `f` is a finite-dimensional space, then we can automatically prove
that the kernel of `f'` is complemented, hence the only assumptions are `HasStrictFDerivAt`
and `f'.range = ⊤`. This version is named `HasStrictFDerivAt.implicitFunction`.

For the version where the implicit equation is defined by a $C^n$ function `f : E × F → G` with an
invertible derivative `∂f/∂y`, see `ContDiffAt.implicitFunction`.

## TODO

* Add a version for `f : 𝕜 × 𝕜 → 𝕜` proving `HasStrictDerivAt` and `deriv φ = ...`.
* Prove that in a real vector space the implicit function has the same smoothness as the original
  one.
* If the original function is differentiable in a neighborhood, then the implicit function is
  differentiable in a neighborhood as well. Current setup only proves differentiability at one
  point for the implicit function constructed in this file (as opposed to an unspecified implicit
  function). One of the ways to overcome this difficulty is to use uniqueness of the implicit
  function in the general version of the theorem. Another way is to prove that *any* implicit
  function satisfying some predicate is strictly differentiable.

## Tags

implicit function, inverse function
-/

public section

noncomputable section

open scoped Topology

open Filter

open ContinuousLinearMap (fst snd smulRight ker_prod)

open ContinuousLinearEquiv (ofBijective)

open LinearMap (ker range)

/-!
### General version

Consider two functions `f : E → F` and `g : E → G` and a point `a` such that

* both functions are strictly differentiable at `a`;
* the derivatives are surjective;
* the kernels of the derivatives are complementary subspaces of `E`.

Note that the map `x ↦ (f x, g x)` has a bijective derivative, hence it is an open partial
homeomorphism between `E` and `F × G`. We use this fact to define a function `φ : F → G → E`
(see `ImplicitFunctionData.implicitFunction`) such that for `(y, z)` close enough to `(f a, g a)`
we have `f (φ y z) = y` and `g (φ y z) = z`. We also prove a formula for `∂φ / ∂z`.

Though this statement is almost symmetric with respect to `F`, `G`, we interpret it in the following
way. Consider a family of surfaces `{x | f x = y}`, `y ∈ 𝓝 (f a)`. Each of these surfaces is
parametrized by `φ y`.

There are many ways to choose a (differentiable) function `φ` such that `f (φ y z) = y` but the
extra condition `g (φ y z) = z` allows a user to select one of these functions. If we imagine
that the level surfaces `f = const` form a local horizontal foliation, then the choice of
`g` fixes a transverse foliation `g = const`, and `φ` is the inverse function of the projection
of `{x | f x = y}` along this transverse foliation.

This version of the theorem is used to prove the other versions and can be used if a user
needs to have a complete control over the choice of the implicit function.
-/


/-- Data for the general version of the implicit function theorem. It holds two functions
`f : E → F` and `g : E → G` (named `leftFun` and `rightFun`) and a point `a` (named `pt`) such that

* both functions are strictly differentiable at `a`;
* the derivatives are surjective;
* the kernels of the derivatives are complementary subspaces of `E`. -/
/-
**ImplicitFunctionData** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_1) →   [inst : NontriviallyNormedField 𝕜] →     (E : Type u_2)
 →       [inst_1 : NormedAddCommGroup E] →         [NormedSpace 𝕜 E] →          
 [CompleteSpace E] →             (F : Type u_3) →               [inst_4 : Normed
AddCommGroup F] →                 [NormedSpace 𝕜 F] →                   [Complet
eSpace F] →                     (G : Type u_4) →                       [inst_7 :
 NormedAddCommGroup G] →                         [NormedSpace 𝕜 G] → [CompleteSp
ace G] → Type (max (max u_2 u_3) u_4)
参数：max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Data for the general version of the implicit function theorem. It holds two func
tions
`f : E → F` and `g : E → G` (named `leftFun` and `rightFun`) and a point `a` (na
med `pt`) such that

* both functions are strictly differentiable at `a`;
* the derivatives are surjective;
* the kernels of the derivatives are complementary subspaces of `E`.
-/
structure ImplicitFunctionData (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] (F : Type*) [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [CompleteSpace G] where
  /-- Left function -/
  leftFun : E → F
  /-- Derivative of the left function -/
  leftDeriv : E →L[𝕜] F
  /-- Right function -/
  rightFun : E → G
  /-- Derivative of the right function -/
  rightDeriv : E →L[𝕜] G
  /-- The point at which `leftFun` and `rightFun` are strictly differentiable -/
  pt : E
  hasStrictFDerivAt_leftFun : HasStrictFDerivAt leftFun leftDeriv pt
  hasStrictFDerivAt_rightFun : HasStrictFDerivAt rightFun rightDeriv pt
  range_leftDeriv : leftDeriv.range = ⊤
  range_rightDeriv : rightDeriv.range = ⊤
  isCompl_ker : IsCompl leftDeriv.ker rightDeriv.ker

namespace ImplicitFunctionData

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  (φ : ImplicitFunctionData 𝕜 E F G)

/-- The function given by `x ↦ (leftFun x, rightFun x)`. -/
/-
**ImplicitFunctionData.prodFun** 是 Mathlib 中的一个定义，位于命名空间 `ImplicitFunctionData`。
形式化陈述：prodFun (x : E) : F × G
参数：x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function given by `x ↦ (leftFun x, rightFun x)`.
-/
def prodFun (x : E) : F × G :=
  (φ.leftFun x, φ.rightFun x)

@[simp]
/-
**ImplicitFunctionData.prodFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `ImplicitFunction
Data`。
形式化陈述：prodFun_apply (x : E) : φ.prodFun x = (φ.leftFun x, φ.rightFun x)
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodFun_apply (x : E) : φ.prodFun x = (φ.leftFun x, φ.rightFun x) := by
  rfl
/-
**ImplicitFunctionData.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ImplicitFunc
tionData`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : CompleteSpace E]
 {F : Type u_3} [inst_4 : NormedAddCommGroup F]   [inst_5 : NormedSpace 𝕜 F] [in
st_6 : CompleteSpace F] {G : Type u_4} [inst_7 : NormedAddCommGroup G]   [inst_8
 : NormedSpace 𝕜 G] [inst_9 : CompleteSpace G] (φ : ImplicitFunctionData 𝕜 E F G
),   HasStrictFDerivAt φ.prodFun (↑(φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ
.rightDeriv ⋯ ⋯ ⋯)) φ.pt
参数：φ : ImplicitFunctionData 𝕜 E F G；↑(φ.leftDeriv.equivProdOfSurjectiveOfIsCompl
 φ.rightDeriv ⋯ ⋯ ⋯)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt_leftFun`：∀ {𝕜 : Type u_1} [inst :
 NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [in
st_2 : NormedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt_rightFun`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] [inst_3 : Co…
-/
protected theorem hasStrictFDerivAt :
    HasStrictFDerivAt φ.prodFun
      (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv φ.range_rightDeriv
          φ.isCompl_ker :
        E →L[𝕜] F × G)
      φ.pt :=
  φ.hasStrictFDerivAt_leftFun.prodMk φ.hasStrictFDerivAt_rightFun
/-
**ImplicitFunctionData.isInvertible_fderiv_prodFun** 是 Mathlib 中的一个定理，位于命名空间 `Im
plicitFunctionData`。
形式化陈述：isInvertible_fderiv_prodFun : (fderiv 𝕜 φ.prodFun φ.pt).IsInvertible
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ContinuousLinearMap.isInvertible_equiv`：∀ {R : Type u_1} {M : Type u_2} 
{M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace M₂]   [in
st_2 : Semiring R] [inst_3 :…
-/
theorem isInvertible_fderiv_prodFun : (fderiv 𝕜 φ.prodFun φ.pt).IsInvertible := by
  rw [φ.hasStrictFDerivAt.hasFDerivAt.fderiv]
  exact ContinuousLinearMap.isInvertible_equiv

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `x ↦ (f x, g x)` defines an open partial homeomorphism between
`E` and `F × G`. In particular, `{x | f x = f a}` is locally homeomorphic to `G`. -/
/-
**ImplicitFunctionData.toOpenPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Implic
itFunctionData`。
形式化陈述：toOpenPartialHomeomorph : OpenPartialHomeomorph E (F × G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…

--- 原说明 ---
Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly 
differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these de
rivatives are
complementary subspaces of `E`, then `x ↦ (f x, g x)` defines an open partial ho
meomorphism between
`E` and `F × G`. In particular, `{x | f x = f a}` is locally homeomorphic to `G`
.
-/
def toOpenPartialHomeomorph : OpenPartialHomeomorph E (F × G) :=
  φ.hasStrictFDerivAt.toOpenPartialHomeomorph _

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `implicitFunction` is the unique (germ of a) map
`φ : F → G → E` such that `f (φ y z) = y` and `g (φ y z) = z`. -/
/-
**ImplicitFunctionData.implicitFunction** 是 Mathlib 中的一个定义，位于命名空间 `ImplicitFunct
ionData`。
形式化陈述：implicitFunction : F -> G -> E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly 
differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these de
rivatives are
complementary subspaces of `E`, then `implicitFunction` is the unique (germ of a
) map
`φ : F → G → E` such that `f (φ y z) = y` and `g (φ y z) = z`.
-/
def implicitFunction : F → G → E :=
  Function.curry <| φ.toOpenPartialHomeomorph.symm
/-
**ImplicitFunctionData.implicitFunction_def** 是 Mathlib 中的一个定理，位于命名空间 `ImplicitF
unctionData`。
形式化陈述：implicitFunction_def : implicitFunction φ = Function.curry (φ.hasStrictFDe
rivAt.toOpenPartialHomeomorph _).symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem implicitFunction_def :
    implicitFunction φ = Function.curry (φ.hasStrictFDerivAt.toOpenPartialHomeomorph _).symm := by
  rfl
/-
**ImplicitFunctionData.implicitFunction_apply** 是 Mathlib 中的一个引理，位于命名空间 `Implici
tFunctionData`。
形式化陈述：implicitFunction_apply {x : F} {y : G} : φ.implicitFunction x y = φ.toOpen
PartialHomeomorph.symm (x, y)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma implicitFunction_apply {x : F} {y : G} :
    φ.implicitFunction x y = φ.toOpenPartialHomeomorph.symm (x, y) := by
  rfl

@[simp]
/-
**ImplicitFunctionData.toOpenPartialHomeomorph_coe** 是 Mathlib 中的一个定理，位于命名空间 `Im
plicitFunctionData`。
形式化陈述：toOpenPartialHomeomorph_coe : ⇑φ.toOpenPartialHomeomorph = φ.prodFun
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpenPartialHomeomorph_coe : ⇑φ.toOpenPartialHomeomorph = φ.prodFun := by
  rfl
/-
**ImplicitFunctionData.toOpenPartialHomeomorph_apply** 是 Mathlib 中的一个定理，位于命名空间 `
ImplicitFunctionData`。
形式化陈述：toOpenPartialHomeomorph_apply (x : E) : φ.toOpenPartialHomeomorph x = (φ.l
eftFun x, φ.rightFun x)
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpenPartialHomeomorph_apply (x : E) :
    φ.toOpenPartialHomeomorph x = (φ.leftFun x, φ.rightFun x) := by
  rfl
/-
**ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source** 是 Mathlib 中的一个定理，
位于命名空间 `ImplicitFunctionData`。
形式化陈述：pt_mem_toOpenPartialHomeomorph_source : φ.pt in φ.toOpenPartialHomeomorph.
source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source`：mem_toOpenPartialH
omeomorph_source (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : a in (hf.toOpe
nPartialHomeomorph f).source
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…
-/
theorem pt_mem_toOpenPartialHomeomorph_source : φ.pt ∈ φ.toOpenPartialHomeomorph.source :=
  φ.hasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
/-
**ImplicitFunctionData.map_pt_mem_toOpenPartialHomeomorph_target** 是 Mathlib 中的一
个定理，位于命名空间 `ImplicitFunctionData`。
形式化陈述：map_pt_mem_toOpenPartialHomeomorph_target : (φ.leftFun φ.pt, φ.rightFun φ.
pt) in φ.toOpenPartialHomeomorph.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用定理 `ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source`：pt_mem_toOpe
nPartialHomeomorph_source : φ.pt in φ.toOpenPartialHomeomorph.source
-/
theorem map_pt_mem_toOpenPartialHomeomorph_target :
    (φ.leftFun φ.pt, φ.rightFun φ.pt) ∈ φ.toOpenPartialHomeomorph.target :=
  φ.toOpenPartialHomeomorph.map_source <| φ.pt_mem_toOpenPartialHomeomorph_source
/-
**ImplicitFunctionData.prodFun_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 `Impli
citFunctionData`。
形式化陈述：prodFun_implicitFunction : forallᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.prod
Fun (φ.implicitFunction p.1 p.2) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `HasStrictFDerivAt.eventually_right_inverse`：eventually_right_inverse (hf
 : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : forallᶠ y in 𝓝 (f a), f (hf.localI
nverse f f' a y) = y
-/
theorem prodFun_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.prodFun (φ.implicitFunction p.1 p.2) = p :=
  φ.hasStrictFDerivAt.eventually_right_inverse.mono fun ⟨_, _⟩ h => h

@[deprecated (since := "2026-01-27")]
alias prod_map_implicitFunction := prodFun_implicitFunction
/-
**ImplicitFunctionData.leftFun_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 `Impli
citFunctionData`。
形式化陈述：leftFun_implicitFunction : forallᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.left
Fun (φ.implicitFunction p.1 p.2) = p.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ImplicitFunctionData.prodFun_implicitFunction`：prodFun_implicitFunction 
: forallᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.prodFun (φ.implicitFunction p.1 p.2
) = p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem leftFun_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.leftFun (φ.implicitFunction p.1 p.2) = p.1 :=
  φ.prodFun_implicitFunction.mono fun _ => congr_arg Prod.fst

@[deprecated (since := "2026-01-27")]
alias left_map_implicitFunction := leftFun_implicitFunction
/-
**ImplicitFunctionData.rightFun_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 `Impl
icitFunctionData`。
形式化陈述：rightFun_implicitFunction : forallᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.rig
htFun (φ.implicitFunction p.1 p.2) = p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ImplicitFunctionData.prodFun_implicitFunction`：prodFun_implicitFunction 
: forallᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.prodFun (φ.implicitFunction p.1 p.2
) = p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem rightFun_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.rightFun (φ.implicitFunction p.1 p.2) = p.2 :=
  φ.prodFun_implicitFunction.mono fun _ => congr_arg Prod.snd

@[deprecated (since := "2026-01-27")]
alias right_map_implicitFunction := rightFun_implicitFunction
/-
**ImplicitFunctionData.implicitFunction_apply_image** 是 Mathlib 中的一个定理，位于命名空间 `I
mplicitFunctionData`。
形式化陈述：implicitFunction_apply_image : forallᶠ x in 𝓝 φ.pt, φ.implicitFunction (φ.
leftFun x) (φ.rightFun x) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.eventually_left_inverse`：eventually_left_inverse (hf :
 HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : forallᶠ x in 𝓝 a, hf.localInverse f 
f' a (f x) = x
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…
-/
theorem implicitFunction_apply_image :
    ∀ᶠ x in 𝓝 φ.pt, φ.implicitFunction (φ.leftFun x) (φ.rightFun x) = x :=
  φ.hasStrictFDerivAt.eventually_left_inverse
/-
**ImplicitFunctionData.leftFun_implicitFunction_eq_leftFun** 是 Mathlib 中的一个定理，位于
命名空间 `ImplicitFunctionData`。
形式化陈述：leftFun_implicitFunction_eq_leftFun : forallᶠ x in 𝓝 φ.pt, φ.leftFun (φ.im
plicitFunction (φ.leftFun φ.pt) (φ.rightFun x)) = φ.leftFun φ.pt
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.prod_inr_nhds`：Filter.Eventually.prod_inr_nhds {p : Y 
-> Prop} {y : Y} (h : forallᶠ x in 𝓝 y, p x) (x : X) : forallᶠ x in 𝓝 (x, y), p 
(x : X × Y).2
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `Filter.Eventually.curry_nhds`：Filter.Eventually.curry_nhds {p : X × Y ->
 Prop} {x : X} {y : Y} (h : forallᶠ x in 𝓝 (x, y), p x) : forallᶠ x' in 𝓝 x, for
allᶠ y' in 𝓝 y, p …
· 使用定理 `ImplicitFunctionData.leftFun_implicitFunction`：leftFun_implicitFunction 
: forallᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.leftFun (φ.implicitFunction p.1 p.2
) = p.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasStrictFDerivAt.map_nhds_eq_of_equiv`：map_nhds_eq_of_equiv (hf : HasSt
rictFDerivAt f (f' : E ->L[𝕜] F) a) : map f (𝓝 a) = 𝓝 (f a)
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.prodFun_apply`：prodFun_apply (x : E) : φ.prodFun x 
= (φ.leftFun x, φ.rightFun x)
-/
theorem leftFun_implicitFunction_eq_leftFun : ∀ᶠ x in 𝓝 φ.pt,
    φ.leftFun (φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x)) = φ.leftFun φ.pt := by
  have := φ.leftFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this
/-
**ImplicitFunctionData.rightFun_implicitFunction_eq_rightFun** 是 Mathlib 中的一个定理，
位于命名空间 `ImplicitFunctionData`。
形式化陈述：rightFun_implicitFunction_eq_rightFun : forallᶠ x in 𝓝 φ.pt, φ.rightFun (φ
.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x)) = φ.rightFun x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.prod_inr_nhds`：Filter.Eventually.prod_inr_nhds {p : Y 
-> Prop} {y : Y} (h : forallᶠ x in 𝓝 y, p x) (x : X) : forallᶠ x in 𝓝 (x, y), p 
(x : X × Y).2
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `Filter.Eventually.curry_nhds`：Filter.Eventually.curry_nhds {p : X × Y ->
 Prop} {x : X} {y : Y} (h : forallᶠ x in 𝓝 (x, y), p x) : forallᶠ x' in 𝓝 x, for
allᶠ y' in 𝓝 y, p …
· 使用定理 `ImplicitFunctionData.rightFun_implicitFunction`：rightFun_implicitFunctio
n : forallᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.rightFun (φ.implicitFunction p.1 
p.2) = p.2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasStrictFDerivAt.map_nhds_eq_of_equiv`：map_nhds_eq_of_equiv (hf : HasSt
rictFDerivAt f (f' : E ->L[𝕜] F) a) : map f (𝓝 a) = 𝓝 (f a)
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.prodFun_apply`：prodFun_apply (x : E) : φ.prodFun x 
= (φ.leftFun x, φ.rightFun x)
-/
theorem rightFun_implicitFunction_eq_rightFun : ∀ᶠ x in 𝓝 φ.pt,
    φ.rightFun (φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x)) = φ.rightFun x := by
  have := φ.rightFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this
/-
**ImplicitFunctionData.leftFun_eq_iff_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间
 `ImplicitFunctionData`。
形式化陈述：leftFun_eq_iff_implicitFunction : forallᶠ x in 𝓝 φ.pt, φ.leftFun x = φ.lef
tFun φ.pt ↔ φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x) = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ImplicitFunctionData.leftFun_implicitFunction_eq_leftFun`：leftFun_implic
itFunction_eq_leftFun : forallᶠ x in 𝓝 φ.pt, φ.leftFun (φ.implicitFunction (φ.le
ftFun φ.pt) (φ.rightFun x)) = φ.leftFun φ.pt
· 使用定理 `ImplicitFunctionData.implicitFunction_apply_image`：implicitFunction_appl
y_image : forallᶠ x in 𝓝 φ.pt, φ.implicitFunction (φ.leftFun x) (φ.rightFun x) =
 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem leftFun_eq_iff_implicitFunction : ∀ᶠ x in 𝓝 φ.pt,
    φ.leftFun x = φ.leftFun φ.pt ↔ φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x) = x := by
  filter_upwards [φ.implicitFunction_apply_image, φ.leftFun_implicitFunction_eq_leftFun] with x _ _
  constructor <;> exact fun h => by rwa [← h]
/-
**ImplicitFunctionData.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `ImplicitFunctionDa
ta`。
形式化陈述：map_nhds_eq : map φ.leftFun (𝓝 φ.pt) = 𝓝 (φ.leftFun φ.pt)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `HasStrictFDerivAt.map_nhds_eq_of_equiv`：map_nhds_eq_of_equiv (hf : HasSt
rictFDerivAt f (f' : E ->L[𝕜] F) a) : map f (𝓝 a) = 𝓝 (f a)
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `map_fst_nhds`：map_fst_nhds (x : X × Y) : map Prod.fst (𝓝 x) = 𝓝 x.1
-/
theorem map_nhds_eq : map φ.leftFun (𝓝 φ.pt) = 𝓝 (φ.leftFun φ.pt) :=
  show map (Prod.fst ∘ φ.prodFun) (𝓝 φ.pt) = 𝓝 (φ.prodFun φ.pt).1 by
    rw [← map_map, φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, map_fst_nhds]

/-- The implicit function is strictly differentiable. -/
/-
**ImplicitFunctionData.hasStrictFDerivAt_implicitFunction_fderiv** 是 Mathlib 中的一
个定理，位于命名空间 `ImplicitFunctionData`。
形式化陈述：hasStrictFDerivAt_implicitFunction_fderiv : HasStrictFDerivAt (φ.implicitF
unction (φ.leftFun φ.pt)) (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rig
htFun φ.pt)) (φ.rightFun φ.pt)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `HasStrictFDerivAt.to_localInverse`：to_localInverse (hf : HasStrictFDeriv
At f (f' : E ->L[𝕜] F) a) : HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm 
: F ->L[𝕜] E) (f a)
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `hasStrictFDerivAt_const`：hasStrictFDerivAt_const (c : F) (x : E) : HasSt
rictFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x
· 使用定理 `hasStrictFDerivAt_id`：hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt i
d (.id 𝕜 E) x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…

--- 原说明 ---
The implicit function is strictly differentiable.
-/
theorem hasStrictFDerivAt_implicitFunction_fderiv :
    HasStrictFDerivAt (φ.implicitFunction (φ.leftFun φ.pt))
      (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt)) (φ.rightFun φ.pt) := by
  have := φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
    ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _))
  convert! this
  exact this.hasFDerivAt.fderiv
/-
**ImplicitFunctionData.differentiableAt_implicitFunction** 是 Mathlib 中的一个定理，位于命名
空间 `ImplicitFunctionData`。
形式化陈述：differentiableAt_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) : Dif
ferentiableAt 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt)
参数：φ : ImplicitFunctionData 𝕜 E F G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt_implicitFunction_fderiv`：hasStric
tFDerivAt_implicitFunction_fderiv : HasStrictFDerivAt (φ.implicitFunction (φ.lef
tFun φ.pt)) (fderiv 𝕜 (φ.implicitFunction (φ.leftFun…
-/
theorem differentiableAt_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) :
    DifferentiableAt 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) :=
  φ.hasStrictFDerivAt_implicitFunction_fderiv.hasFDerivAt.differentiableAt
/-
**ImplicitFunctionData.fderiv_implicitFunction_apply_eq_iff** 是 Mathlib 中的一个定理，位
于命名空间 `ImplicitFunctionData`。
形式化陈述：fderiv_implicitFunction_apply_eq_iff (φ : ImplicitFunctionData 𝕜 E F G) {x
 : G} {y : E} : fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt)
 x = y ↔ φ.leftDeriv y = 0 ∧ φ.rightDeriv y = x
参数：φ : ImplicitFunctionData 𝕜 E F G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `HasStrictFDerivAt.to_localInverse`：to_localInverse (hf : HasStrictFDeriv
At f (f' : E ->L[𝕜] F) a) : HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm 
: F ->L[𝕜] E) (f a)
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `hasStrictFDerivAt_const`：hasStrictFDerivAt_const (c : F) (x : E) : HasSt
rictFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x
· 使用定理 `hasStrictFDerivAt_id`：hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt i
d (.id 𝕜 E) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fderiv_implicitFunction_apply_eq_iff (φ : ImplicitFunctionData 𝕜 E F G) {x : G} {y : E} :
    fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x = y ↔
      φ.leftDeriv y = 0 ∧ φ.rightDeriv y = x := by
  unfold implicitFunction Function.curry toOpenPartialHomeomorph
  simp only [← HasStrictFDerivAt.localInverse_def]
  rw [φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
    ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _)) |>.hasFDerivAt |>.fderiv]
  simp [ContinuousLinearEquiv.symm_apply_eq, @eq_comm _ (φ.leftDeriv _),
    @eq_comm _ (φ.rightDeriv _)]

@[simp]
/-
**ImplicitFunctionData.leftDeriv_fderiv_implicitFunction** 是 Mathlib 中的一个定理，位于命名
空间 `ImplicitFunctionData`。
形式化陈述：leftDeriv_fderiv_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) (x : 
G) : φ.leftDeriv (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.p
t) x) = 0
参数：φ : ImplicitFunctionData 𝕜 E F G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ImplicitFunctionData.fderiv_implicitFunction_apply_eq_iff`：fderiv_implic
itFunction_apply_eq_iff (φ : ImplicitFunctionData 𝕜 E F G) {x : G} {y : E} : fde
riv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.…
-/
theorem leftDeriv_fderiv_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) (x : G) :
    φ.leftDeriv (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x) = 0 := by
  exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl |>.left

@[simp]
/-
**ImplicitFunctionData.rightDeriv_fderiv_implicitFunction** 是 Mathlib 中的一个定理，位于命
名空间 `ImplicitFunctionData`。
形式化陈述：rightDeriv_fderiv_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) (x :
 G) : φ.rightDeriv (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ
.pt) x) = x
参数：φ : ImplicitFunctionData 𝕜 E F G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ImplicitFunctionData.fderiv_implicitFunction_apply_eq_iff`：fderiv_implic
itFunction_apply_eq_iff (φ : ImplicitFunctionData 𝕜 E F G) {x : G} {y : E} : fde
riv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.…
-/
theorem rightDeriv_fderiv_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) (x : G) :
    φ.rightDeriv (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x) = x := by
  exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl |>.right
/-
**ImplicitFunctionData.hasStrictFDerivAt_implicitFunction** 是 Mathlib 中的一个定理，位于命
名空间 `ImplicitFunctionData`。
形式化陈述：hasStrictFDerivAt_implicitFunction (g'inv : G ->L[𝕜] E) (hg'inv : φ.rightD
eriv.comp g'inv = ContinuousLinearMap.id 𝕜 G) (hg'invf : φ.leftDeriv.comp g'inv 
= 0) : HasStrictFDerivAt (φ.implicitFunction (φ.leftFun φ.pt)) g'inv (φ.rightFun
 φ.pt)
参数：g'inv : G ->L[𝕜] E；hg'inv : φ.rightDeriv.comp g'inv = ContinuousLinearMap.id 
𝕜 G；hg'invf : φ.leftDeriv.comp g'inv = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ImplicitFunctionData.fderiv_implicitFunction_apply_eq_iff`：fderiv_implic
itFunction_apply_eq_iff (φ : ImplicitFunctionData 𝕜 E F G) {x : G} {y : E} : fde
riv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt_implicitFunction_fderiv`：hasStric
tFDerivAt_implicitFunction_fderiv : HasStrictFDerivAt (φ.implicitFunction (φ.lef
tFun φ.pt)) (fderiv 𝕜 (φ.implicitFunction (φ.leftFun…
-/
theorem hasStrictFDerivAt_implicitFunction (g'inv : G →L[𝕜] E)
    (hg'inv : φ.rightDeriv.comp g'inv = ContinuousLinearMap.id 𝕜 G)
    (hg'invf : φ.leftDeriv.comp g'inv = 0) :
    HasStrictFDerivAt (φ.implicitFunction (φ.leftFun φ.pt)) g'inv (φ.rightFun φ.pt) := by
  convert! φ.hasStrictFDerivAt_implicitFunction_fderiv
  ext1 x
  rw [eq_comm, fderiv_implicitFunction_apply_eq_iff]
  simp_all [DFunLike.ext_iff]

@[deprecated (since := "2026-01-27")]
alias implicitFunction_hasStrictFDerivAt := hasStrictFDerivAt_implicitFunction
/-
**ImplicitFunctionData.map_implicitFunction_nhdsWithin_preimage** 是 Mathlib 中的一个
定理，位于命名空间 `ImplicitFunctionData`。
形式化陈述：map_implicitFunction_nhdsWithin_preimage (φ : ImplicitFunctionData 𝕜 E F G
) (s : Set E) : (𝓝[φ.implicitFunction (φ.leftFun φ.pt) ⁻¹' s] (φ.rightFun φ.pt))
.map (φ.implicitFunction (φ.leftFun φ.pt)) = 𝓝[s inter φ.leftFun ⁻¹' {φ.leftFun 
φ.pt}] φ.pt
参数：φ : ImplicitFunctionData 𝕜 E F G；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用引理 `Topology.IsInducing.map_nhdsWithin_eq`：Topology.IsInducing.map_nhdsWithi
n_eq {f : α -> β} (hf : IsInducing f) (s : Set α) (x : α) : map f (𝓝[s] x) = 𝓝[f
 '' s] f x
· 使用引理 `isInducing_prodMkRight`：isInducing_prodMkRight (x : X) : IsInducing (Pro
d.mk x : Y -> X × Y)
· 使用定理 `Set.singleton_prod`：singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t
· 使用定理 `OpenPartialHomeomorph.map_nhdsWithin_eq`：map_nhdsWithin_eq {x} (hx : x i
n e.source) (s : Set X) : map e (𝓝[s] x) = 𝓝[e '' (e.source inter s)] e x
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
· 使用定理 `ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source`：pt_mem_toOpe
nPartialHomeomorph_source : φ.pt in φ.toOpenPartialHomeomorph.source
· 使用定理 `ImplicitFunctionData.prodFun_apply`：prodFun_apply (x : E) : φ.prodFun x 
= (φ.leftFun x, φ.rightFun x)
· 使用定理 `ImplicitFunctionData.toOpenPartialHomeomorph_coe`：toOpenPartialHomeomorp
h_coe : ⇑φ.toOpenPartialHomeomorph = φ.prodFun
· 使用定理 `OpenPartialHomeomorph.leftInvOn`：∀ {X : Type u_1} {Y : Type u_3} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph 
X Y), Set.LeftInvOn (…
· 使用定理 `OpenPartialHomeomorph.image_source_inter_eq'`：image_source_inter_eq' (s 
: Set X) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OpenPartialHomeomorph.nhdsWithin_source_inter`：nhdsWithin_source_inter {
x} (hx : x in e.source) (s : Set X) : 𝓝[e.source inter s] x = 𝓝[s] x
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem map_implicitFunction_nhdsWithin_preimage (φ : ImplicitFunctionData 𝕜 E F G)
    (s : Set E) :
    (𝓝[φ.implicitFunction (φ.leftFun φ.pt) ⁻¹' s] (φ.rightFun φ.pt)).map
      (φ.implicitFunction (φ.leftFun φ.pt)) = 𝓝[s ∩ φ.leftFun ⁻¹' {φ.leftFun φ.pt}] φ.pt := by
  have H : φ.implicitFunction (φ.leftFun φ.pt) =
      φ.toOpenPartialHomeomorph.symm ∘ (φ.leftFun φ.pt, ·) := rfl
  rw [H, ← Filter.map_map, (isInducing_prodMkRight _).map_nhdsWithin_eq, ← Set.singleton_prod,
    OpenPartialHomeomorph.map_nhdsWithin_eq, ← prodFun_apply, ← toOpenPartialHomeomorph_coe,
    φ.toOpenPartialHomeomorph.leftInvOn φ.pt_mem_toOpenPartialHomeomorph_source,
    OpenPartialHomeomorph.image_source_inter_eq']
  · conv_rhs =>
      rw [← φ.toOpenPartialHomeomorph.nhdsWithin_source_inter
        φ.pt_mem_toOpenPartialHomeomorph_source]
    congr 1
    ext x
    suffices x ∈ φ.toOpenPartialHomeomorph.source → φ.leftFun x = φ.leftFun φ.pt →
        (φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, φ.rightFun x) ∈ s ↔ x ∈ s) by
      simpa [@and_comm (_ = _)]
    intro hxs hx_eq
    rw [← hx_eq, ← prodFun_apply, ← toOpenPartialHomeomorph_coe,
      φ.toOpenPartialHomeomorph.leftInvOn hxs]
  · exact φ.toOpenPartialHomeomorph.mapsTo φ.pt_mem_toOpenPartialHomeomorph_source
/-
**ImplicitFunctionData.eventuallyEq_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 `
ImplicitFunctionData`。
形式化陈述：eventuallyEq_implicitFunction {ψ : F -> G -> E} (h : forallᶠ x in 𝓝 φ.pt, 
ψ (φ.leftFun x) (φ.rightFun x) = x) : Function.uncurry ψ =ᶠ[𝓝 (φ.prodFun φ.pt)] 
Function.uncurry φ.implicitFunction
参数：h : forallᶠ x in 𝓝 φ.pt, ψ (φ.leftFun x) (φ.rightFun x) = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.localInverse_unique`：localInverse_unique (hf : HasStri
ctFDerivAt f (f' : E ->L[𝕜] F) a) {g : F -> E} (hg : forallᶠ x in 𝓝 a, g (f x) =
 x) : forallᶠ y in 𝓝 (f a),…
· 使用定理 `ImplicitFunctionData.range_leftDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.range_rightDeriv`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.isCompl_ker`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] [inst_3 : Co…
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] [inst_3 : Co…
-/
theorem eventuallyEq_implicitFunction {ψ : F → G → E}
    (h : ∀ᶠ x in 𝓝 φ.pt, ψ (φ.leftFun x) (φ.rightFun x) = x) :
    Function.uncurry ψ =ᶠ[𝓝 (φ.prodFun φ.pt)] Function.uncurry φ.implicitFunction :=
  HasStrictFDerivAt.localInverse_unique _ h

end ImplicitFunctionData

namespace HasStrictFDerivAt

section Complemented

/-!
### Case of a complemented kernel

In this section we prove the following version of the implicit function theorem. Consider a map
`f : E → F` and a point `a : E` such that `f` is strictly differentiable at `a`, its derivative `f'`
is surjective and the kernel of `f'` is a complemented subspace of `E` (i.e., it has a closed
complementary subspace). Then there exists a function `φ : F → ker f' → E` such that for `(y, z)`
close to `(f a, 0)` we have `f (φ y z) = y` and the derivative of `φ (f a)` at zero is the
embedding `ker f' → E`.

Note that a map with these properties is not unique. E.g., different choices of a subspace
complementary to `ker f'` lead to different maps `φ`.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {f : E → F} {f' : E →L[𝕜] F} {a : E}

section Defs

variable (f f')

/-- Data used to apply the generic implicit function theorem to the case of a strictly
differentiable map such that its derivative is surjective and has a complemented kernel. -/
@[simp]
/-
**HasStrictFDerivAt.implicitFunctionDataOfComplemented** 是 Mathlib 中的一个定义，位于命名空间
 `HasStrictFDerivAt`。
形式化陈述：implicitFunctionDataOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : 
f'.range = ⊤) (hker : f'.ker.ClosedComplemented) : ImplicitFunctionData 𝕜 E F f'
.ker where leftFun
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Data used to apply the generic implicit function theorem to the case of a strict
ly
differentiable map such that its derivative is surjective and has a complemented
 kernel.
-/
def implicitFunctionDataOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) : ImplicitFunctionData 𝕜 E F f'.ker where
  leftFun := f
  leftDeriv := f'
  rightFun x := Classical.choose hker (x - a)
  rightDeriv := Classical.choose hker
  pt := a
  hasStrictFDerivAt_leftFun := hf
  hasStrictFDerivAt_rightFun :=
    (Classical.choose hker).hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
  range_leftDeriv := hf'
  range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
  isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hker)

/-- An open partial homeomorphism between `E` and `F × f'.ker` sending level surfaces of `f`
to vertical subspaces. -/
/-
**HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented** 是 Mathlib 中的
一个定义，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：implicitToOpenPartialHomeomorphOfComplemented (hf : HasStrictFDerivAt f f'
 a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) : OpenPartialHomeomo
rph E (F × f'.ker)
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open partial homeomorphism between `E` and `F × f'.ker` sending level surface
s of `f`
to vertical subspaces.
-/
def implicitToOpenPartialHomeomorphOfComplemented (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    OpenPartialHomeomorph E (F × f'.ker) :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).toOpenPartialHomeomorph

/-- Implicit function `g` defined by `f (g z y) = z`. -/
/-
**HasStrictFDerivAt.implicitFunctionOfComplemented** 是 Mathlib 中的一个定义，位于命名空间 `Ha
sStrictFDerivAt`。
形式化陈述：implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.r
ange = ⊤) (hker : f'.ker.ClosedComplemented) : F -> f'.ker -> E
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implicit function `g` defined by `f (g z y) = z`.
-/
def implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) : F → f'.ker → E :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction

end Defs

@[simp]
/-
**HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_fst** 是 Mathli
b 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：implicitToOpenPartialHomeomorphOfComplemented_fst (hf : HasStrictFDerivAt 
f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (x : E) : (hf.im
plicitToOpenPartialHomeomorphOfComplemented f f' hf' hker x).fst = f x
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem implicitToOpenPartialHomeomorphOfComplemented_fst (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (x : E) :
    (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker x).fst = f x := by
  rfl
/-
**HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply** 是 Math
lib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：implicitToOpenPartialHomeomorphOfComplemented_apply (hf : HasStrictFDerivA
t f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (y : E) : hf.i
mplicitToOpenPartialHomeomorphOfComplemented f f' hf' hker y = (f y, Classical.c
hoose hker (y - a))
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted；y : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem implicitToOpenPartialHomeomorphOfComplemented_apply (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (y : E) :
    hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker y =
      (f y, Classical.choose hker (y - a)) := by
  rfl

@[simp]
/-
**HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply_ker** 是 
Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：implicitToOpenPartialHomeomorphOfComplemented_apply_ker (hf : HasStrictFDe
rivAt f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (y : f'.ke
r) : hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker (y + a) = (f
 (y + a), y)
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted；y : f'.ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply`：i
mplicitToOpenPartialHomeomorphOfComplemented_apply (hf : HasStrictFDerivAt f f' 
a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) …
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem implicitToOpenPartialHomeomorphOfComplemented_apply_ker (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (y : f'.ker) :
    hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker (y + a) = (f (y + a), y) := by
  simp only [implicitToOpenPartialHomeomorphOfComplemented_apply, add_sub_cancel_right,
    Classical.choose_spec hker]

@[simp]
/-
**HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_self** 是 Mathl
ib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：implicitToOpenPartialHomeomorphOfComplemented_self (hf : HasStrictFDerivAt
 f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) : hf.implicitTo
OpenPartialHomeomorphOfComplemented f f' hf' hker a = (f a, 0)
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply`：i
mplicitToOpenPartialHomeomorphOfComplemented_apply (hf : HasStrictFDerivAt f f' 
a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) …
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem implicitToOpenPartialHomeomorphOfComplemented_self (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker a = (f a, 0) := by
  simp [hf.implicitToOpenPartialHomeomorphOfComplemented_apply]
/-
**HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorphOfComplemented_source** 是
 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：mem_implicitToOpenPartialHomeomorphOfComplemented_source (hf : HasStrictFD
erivAt f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) : a in (h
f.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).source
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source`：pt_mem_toOpe
nPartialHomeomorph_source : φ.pt in φ.toOpenPartialHomeomorph.source
-/
theorem mem_implicitToOpenPartialHomeomorphOfComplemented_source (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    a ∈ (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).source :=
  ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _
/-
**HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorphOfComplemented_target** 是
 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：mem_implicitToOpenPartialHomeomorphOfComplemented_target (hf : HasStrictFD
erivAt f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) : (f a, (
0 : f'.ker)) in (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker)
.target
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_self`：im
plicitToOpenPartialHomeomorphOfComplemented_self (hf : HasStrictFDerivAt f f' a)
 (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :…
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用定理 `HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorphOfComplemented_sour
ce`：mem_implicitToOpenPartialHomeomorphOfComplemented_source (hf : HasStrictFDer
ivAt f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemen…
-/
theorem mem_implicitToOpenPartialHomeomorphOfComplemented_target (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    (f a, (0 : f'.ker)) ∈
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).target := by
  simpa only [implicitToOpenPartialHomeomorphOfComplemented_self] using
    (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).map_source <|
      hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker

/-- `HasStrictFDerivAt.implicitFunctionOfComplemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
/-
**HasStrictFDerivAt.map_implicitFunctionOfComplemented_eq** 是 Mathlib 中的一个定理，位于命
名空间 `HasStrictFDerivAt`。
形式化陈述：map_implicitFunctionOfComplemented_eq (hf : HasStrictFDerivAt f f' a) (hf'
 : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) : forallᶠ p : F × f'.ker in 
𝓝 (f a, 0), f (hf.implicitFunctionOfComplemented f f' hf' hker p.1 p.2) = p.1
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse`：eventually_right_inverse
 {x} (hx : x in e.target) : forallᶠ y in 𝓝 x, e (e.symm y) = y
· 使用定理 `HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorphOfComplemented_targ
et`：mem_implicitToOpenPartialHomeomorphOfComplemented_target (hf : HasStrictFDer
ivAt f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemen…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
`HasStrictFDerivAt.implicitFunctionOfComplemented` sends `(z, y)` to a point in 
`f ⁻¹' z`.
-/
theorem map_implicitFunctionOfComplemented_eq (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    ∀ᶠ p : F × f'.ker in 𝓝 (f a, 0),
      f (hf.implicitFunctionOfComplemented f f' hf' hker p.1 p.2) = p.1 :=
  ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).eventually_right_inverse <|
        hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker).mono
    fun ⟨_, _⟩ h => congr_arg Prod.fst h

/-- Any point in some neighborhood of `a` can be represented as
`HasStrictFDerivAt.implicitFunctionOfComplemented` of some point. -/
/-
**HasStrictFDerivAt.eq_implicitFunctionOfComplemented** 是 Mathlib 中的一个定理，位于命名空间 
`HasStrictFDerivAt`。
形式化陈述：eq_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f
'.range = ⊤) (hker : f'.ker.ClosedComplemented) : forallᶠ x in 𝓝 a, hf.implicitF
unctionOfComplemented f f' hf' hker (f x) (hf.implicitToOpenPartialHomeomorphOfC
omplemented f f' hf' hker x).snd = x
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ImplicitFunctionData.implicitFunction_apply_image`：implicitFunction_appl
y_image : forallᶠ x in 𝓝 φ.pt, φ.implicitFunction (φ.leftFun x) (φ.rightFun x) =
 x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
Any point in some neighborhood of `a` can be represented as
`HasStrictFDerivAt.implicitFunctionOfComplemented` of some point.
-/
theorem eq_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    ∀ᶠ x in 𝓝 a, hf.implicitFunctionOfComplemented f f' hf' hker (f x)
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker x).snd = x :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction_apply_image

@[simp]
/-
**HasStrictFDerivAt.implicitFunctionOfComplemented_apply_image** 是 Mathlib 中的一个定
理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：implicitFunctionOfComplemented_apply_image (hf : HasStrictFDerivAt f f' a)
 (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) : hf.implicitFunctionOf
Complemented f f' hf' hker (f a) 0 = a
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_self`：im
plicitToOpenPartialHomeomorphOfComplemented_self (hf : HasStrictFDerivAt f f' a)
 (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorphOfComplemented_sour
ce`：mem_implicitToOpenPartialHomeomorphOfComplemented_source (hf : HasStrictFDer
ivAt f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemen…
-/
theorem implicitFunctionOfComplemented_apply_image (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    hf.implicitFunctionOfComplemented f f' hf' hker (f a) 0 = a := by
  simpa only [implicitToOpenPartialHomeomorphOfComplemented_self] using!
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).left_inv
      (hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker)

set_option backward.isDefEq.respectTransparency.types false in
/-
**HasStrictFDerivAt.to_implicitFunctionOfComplemented** 是 Mathlib 中的一个定理，位于命名空间 
`HasStrictFDerivAt`。
形式化陈述：to_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f
'.range = ⊤) (hker : f'.ker.ClosedComplemented) : HasStrictFDerivAt (hf.implicit
FunctionOfComplemented f f' hf' hker (f a)) f'.ker.subtypeL 0
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；hker : f'.ker.ClosedCompleme
nted。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ImplicitFunctionData.mk.congr_simp`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] [inst_3 : Co…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ImplicitFunctionData.hasStrictFDerivAt_implicitFunction`：hasStrictFDeriv
At_implicitFunction (g'inv : G ->L[𝕜] E) (hg'inv : φ.rightDeriv.comp g'inv = Con
tinuousLinearMap.id 𝕜 G) (hg'invf : φ.leftDer…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `ContinuousLinearMap.apply_val_ker`：apply_val_ker (f : M₁ ->SL[σ₁₂] M₂) (
x : f.ker) : f x = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
theorem to_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    HasStrictFDerivAt (hf.implicitFunctionOfComplemented f f' hf' hker (f a))
      f'.ker.subtypeL 0 := by
  convert!
    (implicitFunctionDataOfComplemented f f' hf hf' hker).hasStrictFDerivAt_implicitFunction
      f'.ker.subtypeL _ _
  swap
  · ext
    simp only [Classical.choose_spec hker, implicitFunctionDataOfComplemented,
      ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.coe_subtype,
      ContinuousLinearMap.id_apply]
  swap
  · ext
    simp only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.coe_subtype,
      ContinuousLinearMap.apply_val_ker, zero_apply]
  simp only [implicitFunctionDataOfComplemented, map_sub, sub_self]

end Complemented

/-!
### Finite-dimensional case

In this section we prove the following version of the implicit function theorem. Consider a map
`f : E → F` from a Banach normed space to a finite-dimensional space.
Take a point `a : E` such that `f` is strictly differentiable at `a` and its derivative `f'`
is surjective. Then there exists a function `φ : F → ker f' → E` such that for `(y, z)`
close to `(f a, 0)` we have `f (φ y z) = y` and the derivative of `φ (f a)` at zero is the
embedding `ker f' → E`.

This version deduces that `ker f'` is a complemented subspace from the fact that `F` is a finite
dimensional space, then applies the previous version.

Note that a map with these properties is not unique. E.g., different choices of a subspace
complementary to `ker f'` lead to different maps `φ`.
-/

section FiniteDimensional

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] (f : E → F) (f' : E →L[𝕜] F) {a : E}

/-- Given a map `f : E → F` to a finite-dimensional space with a surjective derivative `f'`,
returns an open partial homeomorphism between `E` and `F × ker f'`. -/
/-
**HasStrictFDerivAt.implicitToOpenPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `H
asStrictFDerivAt`。
形式化陈述：implicitToOpenPartialHomeomorph (hf : HasStrictFDerivAt f f' a) (hf' : f'.
range = ⊤) : OpenPartialHomeomorph E (F × f'.ker)
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a map `f : E → F` to a finite-dimensional space with a surjective derivati
ve `f'`,
returns an open partial homeomorphism between `E` and `F × ker f'`.
-/
def implicitToOpenPartialHomeomorph (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    OpenPartialHomeomorph E (F × f'.ker) :=
  have := FiniteDimensional.complete 𝕜 F
  hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf'
    f'.ker_closedComplemented_of_finiteDimensional_range

/-- Implicit function `g` defined by `f (g z y) = z`. -/
/-
**HasStrictFDerivAt.implicitFunction** 是 Mathlib 中的一个定义，位于命名空间 `HasStrictFDerivA
t`。
形式化陈述：implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) : F 
-> f'.ker -> E
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implicit function `g` defined by `f (g z y) = z`.
-/
def implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) : F → f'.ker → E :=
  Function.curry <| (hf.implicitToOpenPartialHomeomorph f f' hf').symm

variable {f f'}

@[simp]
/-
**HasStrictFDerivAt.implicitToOpenPartialHomeomorph_fst** 是 Mathlib 中的一个定理，位于命名空
间 `HasStrictFDerivAt`。
形式化陈述：implicitToOpenPartialHomeomorph_fst (hf : HasStrictFDerivAt f f' a) (hf' :
 f'.range = ⊤) (x : E) : (hf.implicitToOpenPartialHomeomorph f f' hf' x).fst = f
 x
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem implicitToOpenPartialHomeomorph_fst (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (x : E) : (hf.implicitToOpenPartialHomeomorph f f' hf' x).fst = f x := by
  rfl

@[simp]
/-
**HasStrictFDerivAt.implicitToOpenPartialHomeomorph_apply_ker** 是 Mathlib 中的一个定理
，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：implicitToOpenPartialHomeomorph_apply_ker (hf : HasStrictFDerivAt f f' a) 
(hf' : f'.range = ⊤) (y : f'.ker) : hf.implicitToOpenPartialHomeomorph f f' hf' 
(y + a) = (f (y + a), y)
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；y : f'.ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply_ke
r`：implicitToOpenPartialHomeomorphOfComplemented_apply_ker (hf : HasStrictFDeriv
At f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplement…
-/
theorem implicitToOpenPartialHomeomorph_apply_ker (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (y : f'.ker) :
    hf.implicitToOpenPartialHomeomorph f f' hf' (y + a) = (f (y + a), y) :=
  have := FiniteDimensional.complete 𝕜 F
  implicitToOpenPartialHomeomorphOfComplemented_apply_ker ..

@[simp]
/-
**HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self** 是 Mathlib 中的一个定理，位于命名
空间 `HasStrictFDerivAt`。
形式化陈述：implicitToOpenPartialHomeomorph_self (hf : HasStrictFDerivAt f f' a) (hf' 
: f'.range = ⊤) : hf.implicitToOpenPartialHomeomorph f f' hf' a = (f a, 0)
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_self`：im
plicitToOpenPartialHomeomorphOfComplemented_self (hf : HasStrictFDerivAt f f' a)
 (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :…
-/
theorem implicitToOpenPartialHomeomorph_self (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    hf.implicitToOpenPartialHomeomorph f f' hf' a = (f a, 0) :=
  have := FiniteDimensional.complete 𝕜 F
  implicitToOpenPartialHomeomorphOfComplemented_self ..
/-
**HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_source** 是 Mathlib 中的一个定
理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：mem_implicitToOpenPartialHomeomorph_source (hf : HasStrictFDerivAt f f' a)
 (hf' : f'.range = ⊤) : a in (hf.implicitToOpenPartialHomeomorph f f' hf').sourc
e
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source`：pt_mem_toOpe
nPartialHomeomorph_source : φ.pt in φ.toOpenPartialHomeomorph.source
-/
theorem mem_implicitToOpenPartialHomeomorph_source (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) : a ∈ (hf.implicitToOpenPartialHomeomorph f f' hf').source :=
  have := FiniteDimensional.complete 𝕜 F
  ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _
/-
**HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_target** 是 Mathlib 中的一个定
理，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：mem_implicitToOpenPartialHomeomorph_target (hf : HasStrictFDerivAt f f' a)
 (hf' : f'.range = ⊤) : (f a, (0 : f'.ker)) in (hf.implicitToOpenPartialHomeomor
ph f f' hf').target
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorphOfComplemented_targ
et`：mem_implicitToOpenPartialHomeomorphOfComplemented_target (hf : HasStrictFDer
ivAt f f' a) (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemen…
-/
theorem mem_implicitToOpenPartialHomeomorph_target (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) :
    (f a, (0 : f'.ker)) ∈ (hf.implicitToOpenPartialHomeomorph f f' hf').target :=
  have := FiniteDimensional.complete 𝕜 F
  mem_implicitToOpenPartialHomeomorphOfComplemented_target ..
/-
**HasStrictFDerivAt.tendsto_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 `HasStric
tFDerivAt`。
形式化陈述：tendsto_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range =
 ⊤) {α : Type*} {l : Filter α} {g₁ : α -> F} {g₂ : α -> f'.ker} (h₁ : Tendsto g₁
 l (𝓝 <| f a)) (h₂ : Tendsto g₂ l (𝓝 0)) : Tendsto (fun t => hf.implicitFunction
 f f' hf' (g₁ t) (g₂ t)) l (𝓝 a)
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤；h₁ : Tendsto g₁ l (𝓝 <| f a)
；h₂ : Tendsto g₂ l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `OpenPartialHomeomorph.tendsto_symm`：tendsto_symm {x} (hx : x in e.source
) : Tendsto e.symm (𝓝 (e x)) (𝓝 x)
· 使用定理 `HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_source`：mem_implic
itToOpenPartialHomeomorph_source (hf : HasStrictFDerivAt f f' a) (hf' : f'.range
 = ⊤) : a in (hf.implicitToOpenPartialHomeomorph f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self`：implicitToOpenPa
rtialHomeomorph_self (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) : hf.i
mplicitToOpenPartialHomeomorph f f' hf' a = …
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem tendsto_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) {α : Type*}
    {l : Filter α} {g₁ : α → F} {g₂ : α → f'.ker} (h₁ : Tendsto g₁ l (𝓝 <| f a))
    (h₂ : Tendsto g₂ l (𝓝 0)) :
    Tendsto (fun t => hf.implicitFunction f f' hf' (g₁ t) (g₂ t)) l (𝓝 a) := by
  refine ((hf.implicitToOpenPartialHomeomorph f f' hf').tendsto_symm
    (hf.mem_implicitToOpenPartialHomeomorph_source hf')).comp ?_
  rw [implicitToOpenPartialHomeomorph_self]
  exact h₁.prodMk_nhds h₂

alias _root_.Filter.Tendsto.implicitFunction := tendsto_implicitFunction

/-- `HasStrictFDerivAt.implicitFunction` sends `(z, y)` to a point in `f ⁻¹' z`. -/
/-
**HasStrictFDerivAt.map_implicitFunction_eq** 是 Mathlib 中的一个定理，位于命名空间 `HasStrict
FDerivAt`。
形式化陈述：map_implicitFunction_eq (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = 
⊤) : forallᶠ p : F × f'.ker in 𝓝 (f a, 0), f (hf.implicitFunction f f' hf' p.1 p
.2) = p.1
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.map_implicitFunctionOfComplemented_eq`：map_implicitFun
ctionOfComplemented_eq (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (hke
r : f'.ker.ClosedComplemented) : forallᶠ p : …

--- 原说明 ---
`HasStrictFDerivAt.implicitFunction` sends `(z, y)` to a point in `f ⁻¹' z`.
-/
theorem map_implicitFunction_eq (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    ∀ᶠ p : F × f'.ker in 𝓝 (f a, 0), f (hf.implicitFunction f f' hf' p.1 p.2) = p.1 :=
  have := FiniteDimensional.complete 𝕜 F
  map_implicitFunctionOfComplemented_eq ..

@[simp]
/-
**HasStrictFDerivAt.implicitFunction_apply_image** 是 Mathlib 中的一个定理，位于命名空间 `HasS
trictFDerivAt`。
形式化陈述：implicitFunction_apply_image (hf : HasStrictFDerivAt f f' a) (hf' : f'.ran
ge = ⊤) : hf.implicitFunction f f' hf' (f a) 0 = a
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.implicitFunctionOfComplemented_apply_image`：implicitFu
nctionOfComplemented_apply_image (hf : HasStrictFDerivAt f f' a) (hf' : f'.range
 = ⊤) (hker : f'.ker.ClosedComplemented) : hf.impl…
-/
theorem implicitFunction_apply_image (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    hf.implicitFunction f f' hf' (f a) 0 = a := by
  have := FiniteDimensional.complete 𝕜 F
  apply implicitFunctionOfComplemented_apply_image

/-- Any point in some neighborhood of `a` can be represented as `HasStrictFDerivAt.implicitFunction`
of some point. -/
/-
**HasStrictFDerivAt.eq_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDer
ivAt`。
形式化陈述：eq_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
 forallᶠ x in 𝓝 a, hf.implicitFunction f f' hf' (f x) (hf.implicitToOpenPartialH
omeomorph f f' hf' x).snd = x
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.eq_implicitFunctionOfComplemented`：eq_implicitFunction
OfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (hker : f'.k
er.ClosedComplemented) : forallᶠ x in 𝓝 a…

--- 原说明 ---
Any point in some neighborhood of `a` can be represented as `HasStrictFDerivAt.i
mplicitFunction`
of some point.
-/
theorem eq_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    ∀ᶠ x in 𝓝 a,
      hf.implicitFunction f f' hf' (f x) (hf.implicitToOpenPartialHomeomorph f f' hf' x).snd = x :=
  have := FiniteDimensional.complete 𝕜 F
  eq_implicitFunctionOfComplemented ..
/-
**HasStrictFDerivAt.to_implicitFunction** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDer
ivAt`。
形式化陈述：to_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
 HasStrictFDerivAt (hf.implicitFunction f f' hf' (f a)) f'.ker.subtypeL 0
参数：hf : HasStrictFDerivAt f f' a；hf' : f'.range = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.to_implicitFunctionOfComplemented`：to_implicitFunction
OfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) (hker : f'.k
er.ClosedComplemented) : HasStrictFDerivA…
-/
theorem to_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    HasStrictFDerivAt (hf.implicitFunction f f' hf' (f a)) f'.ker.subtypeL 0 :=
  have := FiniteDimensional.complete 𝕜 F
  to_implicitFunctionOfComplemented ..

end FiniteDimensional

end HasStrictFDerivAt

end

