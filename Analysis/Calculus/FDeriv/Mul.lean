/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Multiplicative operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* multiplication of a function by a scalar function
* product of finitely many scalar functions
* taking the pointwise multiplicative inverse (i.e. `Inv.inv` or `Ring.inverse`) of a function
-/

public section

open scoped Ring
open Asymptotics ContinuousLinearMap Topology

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f : E → F}
variable {f' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}

section SMul

/-! ### Derivative of the product of a scalar-valued function and a vector-valued function

If `c` is a differentiable scalar-valued function and `f` is a differentiable vector-valued
function, then `fun x ↦ c x • f x` is differentiable as well. Lemmas in this section work for
functions `c` taking values in the base field, as well as in a normed algebra over the base
field: e.g., they work for `c : E → ℂ` and `f : E → F` provided that `F` is a complex
normed vector space.
-/


variable {𝕜' : Type*} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]

variable {c : E → 𝕜'} {c' : E →L[𝕜] 𝕜'}

@[to_fun (attr := fun_prop)]
/-
**HasStrictFDerivAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDer
ivAt f f' x) : HasStrictFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x
参数：hc : HasStrictFDerivAt c c' x；hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `isBoundedBilinearMap_smul`：isBoundedBilinearMap_smul {E : Type*} [Semino
rmedAddCommGroup E] [Module 𝕜 E] [Module A E] [IsBoundedSMul A E] [IsScalarTower
 𝕜 A E] : IsBou…
· 使用定理 `IsBoundedBilinearMap.hasStrictFDerivAt`：IsBoundedBilinearMap.hasStrictFD
erivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasStrictFDerivAt b (h.deriv
 p) p
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x :=
  (isBoundedBilinearMap_smul.hasStrictFDerivAt (c x, f x)).comp x <| hc.prodMk hf

@[to_fun (attr := fun_prop)]
/-
**HasFDerivWithinAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.smul (hc : HasFDerivWithinAt c c' s x) (hf : HasFDerivWi
thinAt f f' s x) : HasFDerivWithinAt (c • f) (c x • f' + c'.smulRight (f x)) s x
参数：hc : HasFDerivWithinAt c c' s x；hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `isBoundedBilinearMap_smul`：isBoundedBilinearMap_smul {E : Type*} [Semino
rmedAddCommGroup E] [Module 𝕜 E] [Module A E] [IsBoundedSMul A E] [IsScalarTower
 𝕜 A E] : IsBou…
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasFDerivWithinAt.smul
    (hc : HasFDerivWithinAt c c' s x) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (c • f) (c x • f' + c'.smulRight (f x)) s x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp_hasFDerivWithinAt x <|
    hc.prodMk hf

@[to_fun (attr := fun_prop)]
/-
**HasFDerivAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x) : Has
FDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x
参数：hc : HasFDerivAt c c' x；hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `isBoundedBilinearMap_smul`：isBoundedBilinearMap_smul {E : Type*} [Semino
rmedAddCommGroup E] [Module 𝕜 E] [Module A E] [IsBoundedSMul A E] [IsScalarTower
 𝕜 A E] : IsBou…
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
-/
theorem HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp x <| hc.prodMk hf

@[to_fun (attr := fun_prop)]
/-
**DifferentiableWithinAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.smul (hc : DifferentiableWithinAt 𝕜 c s x) (hf : Di
fferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (c • f) s x
参数：hc : DifferentiableWithinAt 𝕜 c s x；hf : DifferentiableWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.smul`：HasFDerivWithinAt.smul (hc : HasFDerivWithinAt c
 c' s x) (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithinAt (c • f) (c x • f'
 + c'.smulRi…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (c • f) s x :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
/-
**DifferentiableAt.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt
 𝕜 f x) : DifferentiableAt 𝕜 (c • f) x
参数：hc : DifferentiableAt 𝕜 c x；hf : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.smul`：HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFD
erivAt f f' x) : HasFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (c • f) x :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]
/-
**DifferentiableOn.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn
 𝕜 f s) : DifferentiableOn 𝕜 (c • f) s
参数：hc : DifferentiableOn 𝕜 c s；hf : DifferentiableOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.smul`：DifferentiableWithinAt.smul (hc : Different
iableWithinAt 𝕜 c s x) (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWit
hinAt 𝕜 (c • f) s…
-/
theorem DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (c • f) s := fun x hx => (hc x hx).smul (hf x hx)

@[to_fun (attr := simp, fun_prop)]
/-
**Differentiable.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.smul (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f) : 
Differentiable 𝕜 (c • f)
参数：hc : Differentiable 𝕜 c；hf : Differentiable 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.smul`：DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c 
x) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (c • f) x
-/
theorem Differentiable.smul (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (c • f) := fun x => (hc x).smul (hf x)
/-
**fderivWithin_fun_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_fun_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : Differentiabl
eWithinAt 𝕜 c s x) (hf : DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 (fun y
 => c y • f y) s x = c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smulRig
ht (f x)
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；hf : Diffe
rentiableWithinAt 𝕜 f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.smul`：HasFDerivWithinAt.smul (hc : HasFDerivWithinAt c
 c' s x) (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithinAt (c • f) (c x • f'
 + c'.smulRi…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_fun_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (fun y => c y • f y) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smulRight (f x) :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs
/-
**fderivWithin_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWit
hinAt 𝕜 c s x) (hf : DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 (c • f) s 
x = c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smulRight (f x)
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；hf : Diffe
rentiableWithinAt 𝕜 f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.smul`：HasFDerivWithinAt.smul (hc : HasFDerivWithinAt c
 c' s x) (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithinAt (c • f) (c x • f'
 + c'.smulRi…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (c • f) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smulRight (f x) :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs
/-
**fderiv_fun_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_fun_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x
) : fderiv 𝕜 (fun y => c y • f y) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smulRi
ght (f x)
参数：hc : DifferentiableAt 𝕜 c x；hf : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.smul`：HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFD
erivAt f f' x) : HasFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_fun_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y => c y • f y) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smulRight (f x) :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv
/-
**fderiv_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) : 
fderiv 𝕜 (c • f) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smulRight (f x)
参数：hc : DifferentiableAt 𝕜 c x；hf : DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.smul`：HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFD
erivAt f f' x) : HasFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (c • f) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smulRight (f x) :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv

@[fun_prop]
/-
**HasStrictFDerivAt.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.smul_const (hc : HasStrictFDerivAt c c' x) (f : F) : Has
StrictFDerivAt (fun y => c y • f) (c'.smulRight f) x
参数：hc : HasStrictFDerivAt c c' x；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasStrictFDerivAt.smul`：HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c
 c' x) (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivAt (c • f) (c x • f' + c
'.smulRight …
· 使用定理 `hasStrictFDerivAt_const`：hasStrictFDerivAt_const (c : F) (x : E) : HasSt
rictFDerivAt (fun _ => c) (0 : E ->L[𝕜] F) x
-/
theorem HasStrictFDerivAt.smul_const (hc : HasStrictFDerivAt c c' x) (f : F) :
    HasStrictFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
  simpa only [smul_zero, zero_add] using! hc.smul (hasStrictFDerivAt_const f x)

@[fun_prop]
/-
**HasFDerivWithinAt.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.smul_const (hc : HasFDerivWithinAt c c' s x) (f : F) : H
asFDerivWithinAt (fun y => c y • f) (c'.smulRight f) s x
参数：hc : HasFDerivWithinAt c c' s x；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasFDerivWithinAt.smul`：HasFDerivWithinAt.smul (hc : HasFDerivWithinAt c
 c' s x) (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithinAt (c • f) (c x • f'
 + c'.smulRi…
· 使用定理 `hasFDerivWithinAt_const`：hasFDerivWithinAt_const (c : F) (x : E) (s : Se
t E) : HasFDerivWithinAt (fun _ => c) (0 : E ->L[𝕜] F) s x
-/
theorem HasFDerivWithinAt.smul_const (hc : HasFDerivWithinAt c c' s x) (f : F) :
    HasFDerivWithinAt (fun y => c y • f) (c'.smulRight f) s x := by
  simpa only [smul_zero, zero_add] using! hc.smul (hasFDerivWithinAt_const f x s)

@[fun_prop]
/-
**HasFDerivAt.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.smul_const (hc : HasFDerivAt c c' x) (f : F) : HasFDerivAt (fu
n y => c y • f) (c'.smulRight f) x
参数：hc : HasFDerivAt c c' x；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasFDerivAt.smul`：HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFD
erivAt f f' x) : HasFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x
· 使用定理 `hasFDerivAt_const`：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun 
_ => c) (0 : E ->L[𝕜] F) x
-/
theorem HasFDerivAt.smul_const (hc : HasFDerivAt c c' x) (f : F) :
    HasFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
  simpa only [smul_zero, zero_add] using! hc.smul (hasFDerivAt_const f x)

@[fun_prop]
/-
**DifferentiableWithinAt.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f
 : F) : DifferentiableWithinAt 𝕜 (fun y => c y • f) s x
参数：hc : DifferentiableWithinAt 𝕜 c s x；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.smul_const`：HasFDerivWithinAt.smul_const (hc : HasFDer
ivWithinAt c c' s x) (f : F) : HasFDerivWithinAt (fun y => c y • f) (c'.smulRigh
t f) s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    DifferentiableWithinAt 𝕜 (fun y => c y • f) s x :=
  (hc.hasFDerivWithinAt.smul_const f).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableAt.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) : Differ
entiableAt 𝕜 (fun y => c y • f) x
参数：hc : DifferentiableAt 𝕜 c x；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.smul_const`：HasFDerivAt.smul_const (hc : HasFDerivAt c c' x)
 (f : F) : HasFDerivAt (fun y => c y • f) (c'.smulRight f) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    DifferentiableAt 𝕜 (fun y => c y • f) x :=
  (hc.hasFDerivAt.smul_const f).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.smul_const (hc : DifferentiableOn 𝕜 c s) (f : F) : Differ
entiableOn 𝕜 (fun y => c y • f) s
参数：hc : DifferentiableOn 𝕜 c s；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.smul_const`：DifferentiableWithinAt.smul_const (hc
 : DifferentiableWithinAt 𝕜 c s x) (f : F) : DifferentiableWithinAt 𝕜 (fun y => 
c y • f) s x
-/
theorem DifferentiableOn.smul_const (hc : DifferentiableOn 𝕜 c s) (f : F) :
    DifferentiableOn 𝕜 (fun y => c y • f) s := fun x hx => (hc x hx).smul_const f

@[fun_prop]
/-
**Differentiable.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.smul_const (hc : Differentiable 𝕜 c) (f : F) : Differentiab
le 𝕜 fun y => c y • f
参数：hc : Differentiable 𝕜 c；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.smul_const`：DifferentiableAt.smul_const (hc : Different
iableAt 𝕜 c x) (f : F) : DifferentiableAt 𝕜 (fun y => c y • f) x
-/
theorem Differentiable.smul_const (hc : Differentiable 𝕜 c) (f : F) :
    Differentiable 𝕜 fun y => c y • f := fun x => (hc x).smul_const f
/-
**fderivWithin_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : Differentia
bleWithinAt 𝕜 c s x) (f : F) : fderivWithin 𝕜 (fun y => c y • f) s x = (fderivWi
thin 𝕜 c s x).smulRight f
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.smul_const`：HasFDerivWithinAt.smul_const (hc : HasFDer
ivWithinAt c c' s x) (f : F) : HasFDerivWithinAt (fun y => c y • f) (c'.smulRigh
t f) s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    fderivWithin 𝕜 (fun y => c y • f) s x = (fderivWithin 𝕜 c s x).smulRight f :=
  (hc.hasFDerivWithinAt.smul_const f).fderivWithin hxs
/-
**fderiv_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) : fderiv 𝕜 (fun y 
=> c y • f) x = (fderiv 𝕜 c x).smulRight f
参数：hc : DifferentiableAt 𝕜 c x；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.smul_const`：HasFDerivAt.smul_const (hc : HasFDerivAt c c' x)
 (f : F) : HasFDerivAt (fun y => c y • f) (c'.smulRight f) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    fderiv 𝕜 (fun y => c y • f) x = (fderiv 𝕜 c x).smulRight f :=
  (hc.hasFDerivAt.smul_const f).fderiv

end SMul

section Mul

/-! ### Derivative of the product of two functions -/

open scoped RightActions


variable {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸] [NormedAlgebra 𝕜 𝔸']
  {a b : E → 𝔸} {a' b' : E →L[𝕜] 𝔸} {c d : E → 𝔸'} {c' d' : E →L[𝕜] 𝔸'}

@[to_fun (attr := fun_prop)]
/-
**HasStrictFDerivAt.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x) (hb : HasSt
rictFDerivAt b b' x) : HasStrictFDerivAt (a * b) (a x • b' + a' <• b x) x
参数：ha : HasStrictFDerivAt a a' x；hb : HasStrictFDerivAt b b' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
· 使用定理 `IsBoundedBilinearMap.hasStrictFDerivAt`：IsBoundedBilinearMap.hasStrictFD
erivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasStrictFDerivAt b (h.deriv
 p) p
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFDerivAt a a' x)
    (hb : HasStrictFDerivAt b b' x) :
    HasStrictFDerivAt (a * b) (a x • b' + a' <• b x) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasStrictFDerivAt (a x, b x)).comp x
    (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
/-
**HasStrictFDerivAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDeri
vAt d d' x) : HasStrictFDerivAt (c * d) (c x • d' + d x • c') x
参数：hc : HasStrictFDerivAt c c' x；hd : HasStrictFDerivAt d d' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasStrictFDerivAt.mul'`：HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFD
erivAt a a' x) (hb : HasStrictFDerivAt b b' x) : HasStrictFDerivAt (a * b) (a x 
• b' + a' <•…
-/
theorem HasStrictFDerivAt.mul (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (c * d) (c x • d' + d x • c') x := by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
/-
**HasFDerivWithinAt.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a a' s x) (hb : HasFDerivWi
thinAt b b' s x) : HasFDerivWithinAt (a * b) (a x • b' + a' <• b x) s x
参数：ha : HasFDerivWithinAt a a' s x；hb : HasFDerivWithinAt b b' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a a' s x) (hb : HasFDerivWithinAt b b' s x) :
    HasFDerivWithinAt (a * b) (a x • b' + a' <• b x) s x := by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp_hasFDerivWithinAt x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
/-
**HasFDerivWithinAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.mul (hc : HasFDerivWithinAt c c' s x) (hd : HasFDerivWit
hinAt d d' s x) : HasFDerivWithinAt (c * d) (c x • d' + d x • c') s x
参数：hc : HasFDerivWithinAt c c' s x；hd : HasFDerivWithinAt d d' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasFDerivWithinAt.mul'`：HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a
 a' s x) (hb : HasFDerivWithinAt b b' s x) : HasFDerivWithinAt (a * b) (a x • b'
 + a' <• b x…
-/
theorem HasFDerivWithinAt.mul (hc : HasFDerivWithinAt c c' s x) (hd : HasFDerivWithinAt d d' s x) :
    HasFDerivWithinAt (c * d) (c x • d' + d x • c') s x := by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
/-
**HasFDerivAt.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) : Has
FDerivAt (a * b) (a x • b' + a' <• b x) x
参数：ha : HasFDerivAt a a' x；hb : HasFDerivAt b b' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
-/
theorem HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x) :
    HasFDerivAt (a * b) (a x • b' + a' <• b x) x := by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp x (ha.prodMk hb)

@[to_fun (attr := fun_prop)]
/-
**HasFDerivAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.mul (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) : HasF
DerivAt (c * d) (c x • d' + d x • c') x
参数：hc : HasFDerivAt c c' x；hd : HasFDerivAt d d' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasFDerivAt.mul'`：HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFD
erivAt b b' x) : HasFDerivAt (a * b) (a x • b' + a' <• b x) x
-/
theorem HasFDerivAt.mul (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
    HasFDerivAt (c * d) (c x • d' + d x • c') x := by
  convert! hc.mul' hd
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
/-
**DifferentiableWithinAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.mul (ha : DifferentiableWithinAt 𝕜 a s x) (hb : Dif
ferentiableWithinAt 𝕜 b s x) : DifferentiableWithinAt 𝕜 (a * b) s x
参数：ha : DifferentiableWithinAt 𝕜 a s x；hb : DifferentiableWithinAt 𝕜 b s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasFDerivWithinAt.mul'`：HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a
 a' s x) (hb : HasFDerivWithinAt b b' s x) : HasFDerivWithinAt (a * b) (a x • b'
 + a' <• b x…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.mul (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) : DifferentiableWithinAt 𝕜 (a * b) s x :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
/-
**DifferentiableAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 
𝕜 b x) : DifferentiableAt 𝕜 (a * b) x
参数：ha : DifferentiableAt 𝕜 a x；hb : DifferentiableAt 𝕜 b x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasFDerivAt.mul'`：HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFD
erivAt b b' x) : HasFDerivAt (a * b) (a x • b' + a' <• b x) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    DifferentiableAt 𝕜 (a * b) x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]
/-
**DifferentiableOn.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 
𝕜 b s) : DifferentiableOn 𝕜 (a * b) s
参数：ha : DifferentiableOn 𝕜 a s；hb : DifferentiableOn 𝕜 b s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mul`：DifferentiableWithinAt.mul (ha : Differentia
bleWithinAt 𝕜 a s x) (hb : DifferentiableWithinAt 𝕜 b s x) : DifferentiableWithi
nAt 𝕜 (a * b) s …
-/
theorem DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 𝕜 b s) :
    DifferentiableOn 𝕜 (a * b) s := fun x hx => (ha x hx).mul (hb x hx)

@[to_fun (attr := simp, fun_prop)]
/-
**Differentiable.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.mul (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b) : D
ifferentiable 𝕜 (a * b)
参数：ha : Differentiable 𝕜 a；hb : Differentiable 𝕜 b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.mul`：DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x)
 (hb : DifferentiableAt 𝕜 b x) : DifferentiableAt 𝕜 (a * b) x
-/
theorem Differentiable.mul (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b) :
    Differentiable 𝕜 (a * b) := fun x => (ha x).mul (hb x)
/-
**fderivWithin_fun_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_fun_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : Differentiabl
eWithinAt 𝕜 a s x) (hb : DifferentiableWithinAt 𝕜 b s x) : fderivWithin 𝕜 (fun y
 => a y * b y) s x = a x • fderivWithin 𝕜 b s x + fderivWithin 𝕜 a s x <• b x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；ha : DifferentiableWithinAt 𝕜 a s x；hb : Diffe
rentiableWithinAt 𝕜 b s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `HasFDerivWithinAt.mul'`：HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a
 a' s x) (hb : HasFDerivWithinAt b b' s x) : HasFDerivWithinAt (a * b) (a x • b'
 + a' <• b x…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_fun_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) :
    fderivWithin 𝕜 (fun y => a y * b y) s x =
      a x • fderivWithin 𝕜 b s x + fderivWithin 𝕜 a s x <• b x :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs
/-
**fderivWithin_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWit
hinAt 𝕜 a s x) (hb : DifferentiableWithinAt 𝕜 b s x) : fderivWithin 𝕜 (a * b) s 
x = a x • fderivWithin 𝕜 b s x + fderivWithin 𝕜 a s x <• b x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；ha : DifferentiableWithinAt 𝕜 a s x；hb : Diffe
rentiableWithinAt 𝕜 b s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `HasFDerivWithinAt.mul'`：HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a
 a' s x) (hb : HasFDerivWithinAt b b' s x) : HasFDerivWithinAt (a * b) (a x • b'
 + a' <• b x…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) :
    fderivWithin 𝕜 (a * b) s x =
      a x • fderivWithin 𝕜 b s x + fderivWithin 𝕜 a s x <• b x :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs
/-
**fderivWithin_fun_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_fun_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : Differentiable
WithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x) : fderivWithin 𝕜 (fun y 
=> c y * d y) s x = c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；hd : Diffe
rentiableWithinAt 𝕜 d s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `HasFDerivWithinAt.mul`：HasFDerivWithinAt.mul (hc : HasFDerivWithinAt c c
' s x) (hd : HasFDerivWithinAt d d' s x) : HasFDerivWithinAt (c * d) (c x • d' +
 d x • c') …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_fun_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => c y * d y) s x =
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs
/-
**fderivWithin_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWith
inAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x) : fderivWithin 𝕜 (c * d) s x
 = c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；hd : Diffe
rentiableWithinAt 𝕜 d s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `HasFDerivWithinAt.mul`：HasFDerivWithinAt.mul (hc : HasFDerivWithinAt c c
' s x) (hd : HasFDerivWithinAt d d' s x) : HasFDerivWithinAt (c * d) (c x • d' +
 d x • c') …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (c * d) s x =
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs
/-
**fderiv_fun_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_fun_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x
) : fderiv 𝕜 (fun y => a y * b y) x = a x • fderiv 𝕜 b x + fderiv 𝕜 a x <• b x
参数：ha : DifferentiableAt 𝕜 a x；hb : DifferentiableAt 𝕜 b x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `HasFDerivAt.mul'`：HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFD
erivAt b b' x) : HasFDerivAt (a * b) (a x • b' + a' <• b x) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_fun_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (fun y => a y * b y) x = a x • fderiv 𝕜 b x + fderiv 𝕜 a x <• b x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv
/-
**fderiv_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) : 
fderiv 𝕜 (a * b) x = a x • fderiv 𝕜 b x + fderiv 𝕜 a x <• b x
参数：ha : DifferentiableAt 𝕜 a x；hb : DifferentiableAt 𝕜 b x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `HasFDerivAt.mul'`：HasFDerivAt.mul' (ha : HasFDerivAt a a' x) (hb : HasFD
erivAt b b' x) : HasFDerivAt (a * b) (a x • b' + a' <• b x) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (a * b) x = a x • fderiv 𝕜 b x + fderiv 𝕜 a x <• b x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv
/-
**fderiv_fun_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
 : fderiv 𝕜 (fun y => c y * d y) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x
参数：hc : DifferentiableAt 𝕜 c x；hd : DifferentiableAt 𝕜 d x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `HasFDerivAt.mul`：HasFDerivAt.mul (hc : HasFDerivAt c c' x) (hd : HasFDer
ivAt d d' x) : HasFDerivAt (c * d) (c x • d' + d x • c') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => c y * d y) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv
/-
**fderiv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) : f
deriv 𝕜 (c * d) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x
参数：hc : DifferentiableAt 𝕜 c x；hd : DifferentiableAt 𝕜 d x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `HasFDerivAt.mul`：HasFDerivAt.mul (hc : HasFDerivAt c c' x) (hd : HasFDer
ivAt d d' x) : HasFDerivAt (c * d) (c x • d' + d x • c') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (c * d) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv

@[fun_prop]
/-
**HasStrictFDerivAt.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.mul_const' (ha : HasStrictFDerivAt a a' x) (b : 𝔸) : Has
StrictFDerivAt (fun y => a y * b) (a' <• b) x
参数：ha : HasStrictFDerivAt a a' x；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
theorem HasStrictFDerivAt.mul_const' (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
    HasStrictFDerivAt (fun y => a y * b) (a' <• b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasStrictFDerivAt.comp x ha

@[fun_prop]
/-
**HasStrictFDerivAt.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.mul_const (hc : HasStrictFDerivAt c c' x) (d : 𝔸') : Has
StrictFDerivAt (fun y => c y * d) (d • c') x
参数：hc : HasStrictFDerivAt c c' x；d : 𝔸'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasStrictFDerivAt.mul_const'`：HasStrictFDerivAt.mul_const' (ha : HasStri
ctFDerivAt a a' x) (b : 𝔸) : HasStrictFDerivAt (fun y => a y * b) (a' <• b) x
-/
theorem HasStrictFDerivAt.mul_const (hc : HasStrictFDerivAt c c' x) (d : 𝔸') :
    HasStrictFDerivAt (fun y => c y * d) (d • c') x := by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]
/-
**HasFDerivWithinAt.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.mul_const' (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) : H
asFDerivWithinAt (fun y => a y * b) (a' <• b) s x
参数：ha : HasFDerivWithinAt a a' s x；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem HasFDerivWithinAt.mul_const' (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) :
    HasFDerivWithinAt (fun y => a y * b) (a' <• b) s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAt.comp_hasFDerivWithinAt x ha

@[fun_prop]
/-
**HasFDerivWithinAt.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.mul_const (hc : HasFDerivWithinAt c c' s x) (d : 𝔸') : H
asFDerivWithinAt (fun y => c y * d) (d • c') s x
参数：hc : HasFDerivWithinAt c c' s x；d : 𝔸'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasFDerivWithinAt.mul_const'`：HasFDerivWithinAt.mul_const' (ha : HasFDer
ivWithinAt a a' s x) (b : 𝔸) : HasFDerivWithinAt (fun y => a y * b) (a' <• b) s 
x
-/
theorem HasFDerivWithinAt.mul_const (hc : HasFDerivWithinAt c c' s x) (d : 𝔸') :
    HasFDerivWithinAt (fun y => c y * d) (d • c') s x := by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]
/-
**HasFDerivAt.mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.mul_const' (ha : HasFDerivAt a a' x) (b : 𝔸) : HasFDerivAt (fu
n y => a y * b) (a' <• b) x
参数：ha : HasFDerivAt a a' x；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem HasFDerivAt.mul_const' (ha : HasFDerivAt a a' x) (b : 𝔸) :
    HasFDerivAt (fun y => a y * b) (a' <• b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAt.comp x ha

@[fun_prop]
/-
**HasFDerivAt.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.mul_const (hc : HasFDerivAt c c' x) (d : 𝔸') : HasFDerivAt (fu
n y => c y * d) (d • c') x
参数：hc : HasFDerivAt c c' x；d : 𝔸'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasFDerivAt.mul_const'`：HasFDerivAt.mul_const' (ha : HasFDerivAt a a' x)
 (b : 𝔸) : HasFDerivAt (fun y => a y * b) (a' <• b) x
-/
theorem HasFDerivAt.mul_const (hc : HasFDerivAt c c' x) (d : 𝔸') :
    HasFDerivAt (fun y => c y * d) (d • c') x := by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]
/-
**DifferentiableWithinAt.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.mul_const (ha : DifferentiableWithinAt 𝕜 a s x) (b 
: 𝔸) : DifferentiableWithinAt 𝕜 (fun y => a y * b) s x
参数：ha : DifferentiableWithinAt 𝕜 a s x；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasFDerivWithinAt.mul_const'`：HasFDerivWithinAt.mul_const' (ha : HasFDer
ivWithinAt a a' s x) (b : 𝔸) : HasFDerivWithinAt (fun y => a y * b) (a' <• b) s 
x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.mul_const (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => a y * b) s x :=
  (ha.hasFDerivWithinAt.mul_const' b).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableAt.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.mul_const (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) : Differe
ntiableAt 𝕜 (fun y => a y * b) x
参数：ha : DifferentiableAt 𝕜 a x；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasFDerivAt.mul_const'`：HasFDerivAt.mul_const' (ha : HasFDerivAt a a' x)
 (b : 𝔸) : HasFDerivAt (fun y => a y * b) (a' <• b) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.mul_const (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => a y * b) x :=
  (ha.hasFDerivAt.mul_const' b).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.mul_const (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) : Differe
ntiableOn 𝕜 (fun y => a y * b) s
参数：ha : DifferentiableOn 𝕜 a s；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mul_const`：DifferentiableWithinAt.mul_const (ha :
 DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) : DifferentiableWithinAt 𝕜 (fun y => a 
y * b) s x
-/
theorem DifferentiableOn.mul_const (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => a y * b) s := fun x hx => (ha x hx).mul_const b

@[fun_prop]
/-
**Differentiable.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.mul_const (ha : Differentiable 𝕜 a) (b : 𝔸) : Differentiabl
e 𝕜 fun y => a y * b
参数：ha : Differentiable 𝕜 a；b : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.mul_const`：DifferentiableAt.mul_const (ha : Differentia
bleAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => a y * b) x
-/
theorem Differentiable.mul_const (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => a y * b := fun x => (ha x).mul_const b
/-
**fderivWithin_mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_mul_const' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : Differentia
bleWithinAt 𝕜 a s x) (b : 𝔸) : fderivWithin 𝕜 (fun y => a y * b) s x = fderivWit
hin 𝕜 a s x <• b
参数：hxs : UniqueDiffWithinAt 𝕜 s x；ha : DifferentiableWithinAt 𝕜 a s x；b : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.mul_const'`：HasFDerivWithinAt.mul_const' (ha : HasFDer
ivWithinAt a a' s x) (b : 𝔸) : HasFDerivWithinAt (fun y => a y * b) (a' <• b) s 
x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_mul_const' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => a y * b) s x = fderivWithin 𝕜 a s x <• b :=
  (ha.hasFDerivWithinAt.mul_const' b).fderivWithin hxs
/-
**fderivWithin_mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : Differentiab
leWithinAt 𝕜 c s x) (d : 𝔸') : fderivWithin 𝕜 (fun y => c y * d) s x = d • fderi
vWithin 𝕜 c s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；d : 𝔸'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.mul_const`：HasFDerivWithinAt.mul_const (hc : HasFDeriv
WithinAt c c' s x) (d : 𝔸') : HasFDerivWithinAt (fun y => c y * d) (d • c') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸') :
    fderivWithin 𝕜 (fun y => c y * d) s x = d • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul_const d).fderivWithin hxs
/-
**fderiv_mul_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_mul_const' (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) : fderiv 𝕜 (fun y 
=> a y * b) x = fderiv 𝕜 a x <• b
参数：ha : DifferentiableAt 𝕜 a x；b : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.mul_const'`：HasFDerivAt.mul_const' (ha : HasFDerivAt a a' x)
 (b : 𝔸) : HasFDerivAt (fun y => a y * b) (a' <• b) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_mul_const' (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => a y * b) x = fderiv 𝕜 a x <• b :=
  (ha.hasFDerivAt.mul_const' b).fderiv
/-
**fderiv_mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸') : fderiv 𝕜 (fun y 
=> c y * d) x = d • fderiv 𝕜 c x
参数：hc : DifferentiableAt 𝕜 c x；d : 𝔸'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.mul_const`：HasFDerivAt.mul_const (hc : HasFDerivAt c c' x) (
d : 𝔸') : HasFDerivAt (fun y => c y * d) (d • c') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸') :
    fderiv 𝕜 (fun y => c y * d) x = d • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul_const d).fderiv

@[fun_prop]
/-
**HasStrictFDerivAt.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.const_mul (ha : HasStrictFDerivAt a a' x) (b : 𝔸) : HasS
trictFDerivAt (fun y => b * a y) (b • a') x
参数：ha : HasStrictFDerivAt a a' x；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
theorem HasStrictFDerivAt.const_mul (ha : HasStrictFDerivAt a a' x) (b : 𝔸) :
    HasStrictFDerivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasStrictFDerivAt.comp x ha

@[fun_prop]
/-
**HasFDerivWithinAt.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.const_mul (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) : Ha
sFDerivWithinAt (fun y => b * a y) (b • a') s x
参数：ha : HasFDerivWithinAt a a' s x；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem HasFDerivWithinAt.const_mul (ha : HasFDerivWithinAt a a' s x) (b : 𝔸) :
    HasFDerivWithinAt (fun y => b * a y) (b • a') s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAt.comp_hasFDerivWithinAt x ha

@[fun_prop]
/-
**HasFDerivAt.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.const_mul (ha : HasFDerivAt a a' x) (b : 𝔸) : HasFDerivAt (fun
 y => b * a y) (b • a') x
参数：ha : HasFDerivAt a a' x；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem HasFDerivAt.const_mul (ha : HasFDerivAt a a' x) (b : 𝔸) :
    HasFDerivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAt.comp x ha

@[fun_prop]
/-
**DifferentiableWithinAt.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.const_mul (ha : DifferentiableWithinAt 𝕜 a s x) (b 
: 𝔸) : DifferentiableWithinAt 𝕜 (fun y => b * a y) s x
参数：ha : DifferentiableWithinAt 𝕜 a s x；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasFDerivWithinAt.const_mul`：HasFDerivWithinAt.const_mul (ha : HasFDeriv
WithinAt a a' s x) (b : 𝔸) : HasFDerivWithinAt (fun y => b * a y) (b • a') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.const_mul (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => b * a y) s x :=
  (ha.hasFDerivWithinAt.const_mul b).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableAt.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) : Differe
ntiableAt 𝕜 (fun y => b * a y) x
参数：ha : DifferentiableAt 𝕜 a x；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `HasFDerivAt.const_mul`：HasFDerivAt.const_mul (ha : HasFDerivAt a a' x) (
b : 𝔸) : HasFDerivAt (fun y => b * a y) (b • a') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => b * a y) x :=
  (ha.hasFDerivAt.const_mul b).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.const_mul (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) : Differe
ntiableOn 𝕜 (fun y => b * a y) s
参数：ha : DifferentiableOn 𝕜 a s；b : 𝔸。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.const_mul`：DifferentiableWithinAt.const_mul (ha :
 DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) : DifferentiableWithinAt 𝕜 (fun y => b 
* a y) s x
-/
theorem DifferentiableOn.const_mul (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => b * a y) s := fun x hx => (ha x hx).const_mul b

@[fun_prop]
/-
**Differentiable.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.const_mul (ha : Differentiable 𝕜 a) (b : 𝔸) : Differentiabl
e 𝕜 fun y => b * a y
参数：ha : Differentiable 𝕜 a；b : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.const_mul`：DifferentiableAt.const_mul (ha : Differentia
bleAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => b * a y) x
-/
theorem Differentiable.const_mul (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => b * a y := fun x => (ha x).const_mul b
/-
**fderivWithin_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : Differentiab
leWithinAt 𝕜 a s x) (b : 𝔸) : fderivWithin 𝕜 (fun y => b * a y) s x = b • fderiv
Within 𝕜 a s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；ha : DifferentiableWithinAt 𝕜 a s x；b : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.const_mul`：HasFDerivWithinAt.const_mul (ha : HasFDeriv
WithinAt a a' s x) (b : 𝔸) : HasFDerivWithinAt (fun y => b * a y) (b • a') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => b * a y) s x = b • fderivWithin 𝕜 a s x :=
  (ha.hasFDerivWithinAt.const_mul b).fderivWithin hxs
/-
**fderiv_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) : fderiv 𝕜 (fun y =
> b * a y) x = b • fderiv 𝕜 a x
参数：ha : DifferentiableAt 𝕜 a x；b : 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.const_mul`：HasFDerivAt.const_mul (ha : HasFDerivAt a a' x) (
b : 𝔸) : HasFDerivAt (fun y => b * a y) (b • a') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => b * a y) x = b • fderiv 𝕜 a x :=
  (ha.hasFDerivAt.const_mul b).fderiv

end Mul

section Prod
open scoped RightActions

/-! ### Derivative of a finite product of functions -/

variable {ι : Type*} {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸]
  [NormedAlgebra 𝕜 𝔸'] {u : Finset ι} {f : ι → E → 𝔸} {f' : ι → E →L[𝕜] 𝔸} {g : ι → E → 𝔸'}
  {g' : ι → E →L[𝕜] 𝔸'}

@[fun_prop]
/-
**hasStrictFDerivAt_list_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_list_prod' [Finite ι] {l : List ι} {x : ι -> 𝔸} : HasStr
ictFDerivAt (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `HasStrictFDerivAt.congr_fderiv`：HasStrictFDerivAt.congr_fderiv (h : HasS
trictFDerivAt f f' x) (h' : f' = g') : HasStrictFDerivAt f g' x
· 使用定理 `HasStrictFDerivAt.mul'`：HasStrictFDerivAt.mul' {x : E} (ha : HasStrictFD
erivAt a a' x) (hb : HasStrictFDerivAt b b' x) : HasStrictFDerivAt (a * b) (a x 
• b' + a' <•…
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `List.map_take`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.take i l) = List.take i (List.map f l)
· 使用定理 `List.map_drop`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.drop i l) = List.drop i (List.map f l)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
（共 41 条，此处仅展示前 30 条）
-/
theorem hasStrictFDerivAt_list_prod' [Finite ι] {l : List ι} {x : ι → 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.map x).prod)
      (∑ i : Fin l.length, ((l.take i).map x).prod •
        proj l[i] <• ((l.drop (.succ i)).map x).prod) x := by
  have := Fintype.ofFinite ι
  induction l with
  | nil => simp [hasStrictFDerivAt_const]
  | cons a l IH =>
    simp only [List.map_cons, List.prod_cons, ← proj_apply (R := 𝕜) (φ := fun _ : ι ↦ 𝔸) a]
    exact .congr_fderiv (.mul' (ContinuousLinearMap.hasStrictFDerivAt _) IH)
      (by ext; simp [Fin.sum_univ_succ, Finset.mul_sum, mul_assoc, add_comm])

@[fun_prop]
/-
**hasStrictFDerivAt_list_prod_finRange'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_list_prod_finRange' {n : Nat} {x : Fin n -> 𝔸} : HasStri
ctFDerivAt (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.congr_fderiv`：HasStrictFDerivAt.congr_fderiv (h : HasS
trictFDerivAt f f' x) (h' : f' = g') : HasStrictFDerivAt f g' x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `hasStrictFDerivAt_list_prod'`：hasStrictFDerivAt_list_prod' [Finite ι] {l
 : List ι} {x : ι -> 𝔸} : HasStrictFDerivAt (𝕜
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e : ι
 ≃ κ),…
· 使用定理 `List.length_finRange`：∀ {n : ℕ}, (List.finRange n).length = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.map_take`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.take i l) = List.take i (List.map f l)
· 使用定理 `List.map_drop`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.drop i l) = List.drop i (List.map f l)
· 使用定理 `List.getElem_finRange`：∀ {n i : ℕ} (h : i < (List.finRange n).length), (
List.finRange n)[i] = Fin.cast ⋯ ⟨i, h⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasStrictFDerivAt_list_prod_finRange' {n : ℕ} {x : Fin n → 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ ((List.finRange n).map x).prod)
      (∑ i : Fin n, (((List.finRange n).take i).map x).prod •
        proj i <• (((List.finRange n).drop (.succ i)).map x).prod) x :=
  hasStrictFDerivAt_list_prod'.congr_fderiv <|
    Finset.sum_equiv (finCongr List.length_finRange) (by simp) (by simp)

@[fun_prop]
/-
**hasStrictFDerivAt_list_prod_attach'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_list_prod_attach' {l : List ι} {x : {i // i in l} -> 𝔸} 
: HasStrictFDerivAt (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.congr_fderiv`：HasStrictFDerivAt.congr_fderiv (h : HasS
trictFDerivAt f f' x) (h' : f' = g') : HasStrictFDerivAt f g' x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_attach`：∀ {α : Type u_1} {l : List α}, l.attach.length = l.l
ength
· 使用定理 `hasStrictFDerivAt_list_prod'`：hasStrictFDerivAt_list_prod' [Finite ι] {l
 : List ι} {x : ι -> 𝔸} : HasStrictFDerivAt (𝕜
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finset.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e : ι
 ≃ κ),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
· 使用定理 `List.map_take`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.take i l) = List.take i (List.map f l)
· 使用定理 `List.map_drop`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.drop i l) = List.drop i (List.map f l)
· 使用定理 `List.getElem_attach`：∀ {α : Type u_1} {xs : List α} {i : ℕ} (h : i < xs.
attach.length), xs.attach[i] = ⟨xs[i], ⋯⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasStrictFDerivAt_list_prod_attach' {l : List ι} {x : {i // i ∈ l} → 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.attach.map x).prod)
      (∑ i : Fin l.length, ((l.attach.take i).map x).prod •
        proj l.attach[i.cast List.length_attach.symm] <•
          ((l.attach.drop (.succ i)).map x).prod) x := by
  classical exact hasStrictFDerivAt_list_prod'.congr_fderiv <| Eq.symm <|
    Finset.sum_equiv (finCongr List.length_attach.symm) (by simp) (by simp)

@[fun_prop]
/-
**hasFDerivAt_list_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_list_prod' [Finite ι] {l : List ι} {x : ι -> 𝔸'} : HasFDerivAt
 (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `hasStrictFDerivAt_list_prod'`：hasStrictFDerivAt_list_prod' [Finite ι] {l
 : List ι} {x : ι -> 𝔸} : HasStrictFDerivAt (𝕜
-/
theorem hasFDerivAt_list_prod' [Finite ι] {l : List ι} {x : ι → 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.map x).prod)
      (∑ i : Fin l.length, ((l.take i).map x).prod •
        proj l[i] <• ((l.drop (.succ i)).map x).prod) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_list_prod'.hasFDerivAt

@[fun_prop]
/-
**hasFDerivAt_list_prod_finRange'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_list_prod_finRange' {n : Nat} {x : Fin n -> 𝔸} : HasFDerivAt (
𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `hasStrictFDerivAt_list_prod_finRange'`：hasStrictFDerivAt_list_prod_finRa
nge' {n : Nat} {x : Fin n -> 𝔸} : HasStrictFDerivAt (𝕜
-/
theorem hasFDerivAt_list_prod_finRange' {n : ℕ} {x : Fin n → 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ ((List.finRange n).map x).prod)
      (∑ i : Fin n, (((List.finRange n).take i).map x).prod •
        proj i <• (((List.finRange n).drop (.succ i)).map x).prod) x :=
  hasStrictFDerivAt_list_prod_finRange'.hasFDerivAt

@[fun_prop]
/-
**hasFDerivAt_list_prod_attach'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_list_prod_attach' {l : List ι} {x : {i // i in l} -> 𝔸} : HasF
DerivAt (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_attach`：∀ {α : Type u_1} {l : List α}, l.attach.length = l.l
ength
· 使用定理 `hasStrictFDerivAt_list_prod_attach'`：hasStrictFDerivAt_list_prod_attach'
 {l : List ι} {x : {i // i in l} -> 𝔸} : HasStrictFDerivAt (𝕜
-/
theorem hasFDerivAt_list_prod_attach' {l : List ι} {x : {i // i ∈ l} → 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.attach.map x).prod)
      (∑ i : Fin l.length, ((l.attach.take i).map x).prod •
        (proj l.attach[i.cast List.length_attach.symm]) <•
          ((l.attach.drop (.succ i)).map x).prod) x := by
  exact hasStrictFDerivAt_list_prod_attach'.hasFDerivAt

/--
Auxiliary lemma for `hasStrictFDerivAt_multiset_prod`.

For `NormedCommRing 𝔸'`, can rewrite as `Multiset` using `Multiset.prod_coe`.
-/
@[fun_prop]
/-
**hasStrictFDerivAt_list_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_list_prod [DecidableEq ι] [Finite ι] {l : List ι} {x : ι
 -> 𝔸'} : HasStrictFDerivAt (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.congr_fderiv`：HasStrictFDerivAt.congr_fderiv (h : HasS
trictFDerivAt f f' x) (h' : f' = g') : HasStrictFDerivAt f g' x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `hasStrictFDerivAt_list_prod'`：hasStrictFDerivAt_list_prod' [Finite ι] {l
 : List ι} {x : ι -> 𝔸} : HasStrictFDerivAt (𝕜
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_get_finRange`：∀ {α : Type u_1} (l : List α), List.map l.get (Li
st.finRange l.length) = l
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.Perm.prod_eq`：∀ {M : Type u_4} [inst : CommMonoid M] {l₁ l₂ : List 
M}, l₁.Perm l₂ → l₁.prod = l₂.prod
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `List.erase_getElem`：erase_getElem [BEq ι] [LawfulBEq ι] {l : List ι} {i 
: Nat} (hi : i < l.length) : Perm (l.erase l[i]) (l.eraseIdx i)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.eraseIdx_eq_take_drop_succ`：∀ {α : Type u_1} (l : List α) (i : ℕ), 
l.eraseIdx i = List.take i l ++ List.drop (i + 1) l
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `List.sum_toFinset`：∀ {ι : Type u_1} {M : Type u_5} [inst : DecidableEq ι
] [inst_1 : AddCommMonoid M] (f : ι → M) {l : List ι},   l.Nodup → l.toFinset.su
m f = (…
· 使用定理 `List.nodup_finRange`：∀ (n : ℕ), (List.finRange n).Nodup
· 使用定理 `List.toFinset_finRange`：∀ (n : ℕ), (List.finRange n).toFinset = Finset.u
niv
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `hasStrictFDerivAt_multiset_prod`.

For `NormedCommRing 𝔸'`, can rewrite as `Multiset` using `Multiset.prod_coe`.
-/
theorem hasStrictFDerivAt_list_prod [DecidableEq ι] [Finite ι] {l : List ι} {x : ι → 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.map x).prod)
      (l.map fun i ↦ ((l.erase i).map x).prod • proj i).sum x := by
  have := Fintype.ofFinite ι
  refine hasStrictFDerivAt_list_prod'.congr_fderiv ?_
  conv_rhs => arg 1; arg 2; rw [← List.map_get_finRange l]
  simp only [List.map_map, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange,
    Function.comp_def, ((List.erase_getElem _).map _).prod_eq, List.eraseIdx_eq_take_drop_succ,
    List.map_append, List.prod_append, List.get_eq_getElem, Fin.getElem_fin, Nat.succ_eq_add_one]
  exact Finset.sum_congr rfl fun i _ ↦ by
    ext; simp only [smul_apply, op_smul_eq_smul, smul_eq_mul]; ring

@[fun_prop]
/-
**hasStrictFDerivAt_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_multiset_prod [DecidableEq ι] [Finite ι] {u : Multiset ι
} {x : ι -> 𝔸'} : HasStrictFDerivAt (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `hasStrictFDerivAt_list_prod`：hasStrictFDerivAt_list_prod [DecidableEq ι]
 [Finite ι] {l : List ι} {x : ι -> 𝔸'} : HasStrictFDerivAt (𝕜
-/
theorem hasStrictFDerivAt_multiset_prod [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι → 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (u.map x).prod)
      (u.map (fun i ↦ ((u.erase i).map x).prod • proj i)).sum x :=
  have := Fintype.ofFinite ι
  u.inductionOn fun l ↦ by simpa using hasStrictFDerivAt_list_prod

@[fun_prop]
/-
**hasFDerivAt_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_multiset_prod [DecidableEq ι] [Finite ι] {u : Multiset ι} {x :
 ι -> 𝔸'} : HasFDerivAt (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `hasStrictFDerivAt_multiset_prod`：hasStrictFDerivAt_multiset_prod [Decida
bleEq ι] [Finite ι] {u : Multiset ι} {x : ι -> 𝔸'} : HasStrictFDerivAt (𝕜
-/
theorem hasFDerivAt_multiset_prod [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι → 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ (u.map x).prod)
      (Multiset.sum (u.map (fun i ↦ ((u.erase i).map x).prod • proj i))) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_multiset_prod.hasFDerivAt
/-
**hasStrictFDerivAt_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_finsetProd [DecidableEq ι] [Finite ι] {x : ι -> 𝔸'} : Ha
sStrictFDerivAt (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `hasStrictFDerivAt_multiset_prod`：hasStrictFDerivAt_multiset_prod [Decida
bleEq ι] [Finite ι] {u : Multiset ι} {x : ι -> 𝔸'} : HasStrictFDerivAt (𝕜
-/
theorem hasStrictFDerivAt_finsetProd [DecidableEq ι] [Finite ι] {x : ι → 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (∏ i ∈ u, · i) (∑ i ∈ u, (∏ j ∈ u.erase i, x j) • proj i) x := by
  simp only [Finset.sum_eq_multiset_sum, Finset.prod_eq_multiset_prod]
  exact hasStrictFDerivAt_multiset_prod

@[deprecated (since := "2026-04-08")]
alias hasStrictFDerivAt_finset_prod := hasStrictFDerivAt_finsetProd
/-
**hasFDerivAt_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_finsetProd [DecidableEq ι] [Finite ι] {x : ι -> 𝔸'} : HasFDeri
vAt (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `hasStrictFDerivAt_finsetProd`：hasStrictFDerivAt_finsetProd [DecidableEq 
ι] [Finite ι] {x : ι -> 𝔸'} : HasStrictFDerivAt (𝕜
-/
theorem hasFDerivAt_finsetProd [DecidableEq ι] [Finite ι] {x : ι → 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (∏ i ∈ u, · i) (∑ i ∈ u, (∏ j ∈ u.erase i, x j) • proj i) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_finsetProd.hasFDerivAt

@[deprecated (since := "2026-04-08")] alias hasFDerivAt_finset_prod := hasFDerivAt_finsetProd

section Comp

@[fun_prop]
/-
**HasStrictFDerivAt.list_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.list_prod' {l : List ι} {x : E} (h : forall i in l, HasS
trictFDerivAt (f i ·) (f' i) x) : HasStrictFDerivAt (fun x => (l.map (f · x)).pr
od) (∑ i : Fin l.length, ((l.take i).map (f · x)).prod • f' l[i] <• ((l.drop (.s
ucc i)).map (f · x)).prod) x
参数：h : forall i in l, HasStrictFDerivAt (f i ·) (f' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.get_eq_getElem`：get_eq_getElem? (l : List α) (i : Fin l.length) : l
.get i = l[i]?.get (by simp)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_get_finRange`：∀ {α : Type u_1} (l : List α), List.map l.get (Li
st.finRange l.length) = l
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `HasStrictFDerivAt.congr_fderiv`：HasStrictFDerivAt.congr_fderiv (h : HasS
trictFDerivAt f f' x) (h' : f' = g') : HasStrictFDerivAt f g' x
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `hasStrictFDerivAt_list_prod_finRange'`：hasStrictFDerivAt_list_prod_finRa
nge' {n : Nat} {x : Fin n -> 𝔸} : HasStrictFDerivAt (𝕜
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasStrictFDerivAt_pi`：hasStrictFDerivAt_pi : HasStrictFDerivAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') x ↔ forall i, HasStrictFDerivAt (φ i) (φ' 
i) x
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `List.map_take`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.take i l) = List.take i (List.map f l)
· 使用定理 `List.map_drop`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.drop i l) = List.drop i (List.map f l)
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 34 条，此处仅展示前 30 条）
-/
theorem HasStrictFDerivAt.list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, HasStrictFDerivAt (f i ·) (f' i) x) :
    HasStrictFDerivAt (fun x ↦ (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  -- After https://github.com/leanprover-community/mathlib4/issues/19108, we have to be optimistic with `:)`s; otherwise Lean decides it need to find
  -- `NormedAddCommGroup (List 𝔸)` which is nonsense.
  refine .congr_fderiv (hasStrictFDerivAt_list_prod_finRange'.comp x
    (hasStrictFDerivAt_pi.mpr fun i ↦ h (l.get i) (List.getElem_mem ..)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]

/--
Unlike `HasFDerivAt.finsetProd`, supports non-commutative multiply and duplicate elements.
-/
@[fun_prop]
/-
**HasFDerivAt.list_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.list_prod' {l : List ι} {x : E} (h : forall i in l, HasFDerivA
t (f i ·) (f' i) x) : HasFDerivAt (fun x => (l.map (f · x)).prod) (∑ i : Fin l.l
ength, ((l.take i).map (f · x)).prod • f' l[i] <• ((l.drop (.succ i)).map (f · x
)).prod) x
参数：h : forall i in l, HasFDerivAt (f i ·) (f' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.get_eq_getElem`：get_eq_getElem? (l : List α) (i : Fin l.length) : l
.get i = l[i]?.get (by simp)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_get_finRange`：∀ {α : Type u_1} (l : List α), List.map l.get (Li
st.finRange l.length) = l
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `HasFDerivAt.congr_fderiv`：HasFDerivAt.congr_fderiv (h : HasFDerivAt f f'
 x) (h' : f' = g') : HasFDerivAt f g' x
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `hasFDerivAt_list_prod_finRange'`：hasFDerivAt_list_prod_finRange' {n : Na
t} {x : Fin n -> 𝔸} : HasFDerivAt (𝕜
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivAt_pi`：hasFDerivAt_pi : HasFDerivAt (fun x i => φ i x) (Continu
ousLinearMap.pi φ') x ↔ forall i, HasFDerivAt (φ i) (φ' i) x
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `List.map_take`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.take i l) = List.take i (List.map f l)
· 使用定理 `List.map_drop`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.drop i l) = List.drop i (List.map f l)
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Unlike `HasFDerivAt.finsetProd`, supports non-commutative multiply and duplicate
 elements.
-/
theorem HasFDerivAt.list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, HasFDerivAt (f i ·) (f' i) x) :
    HasFDerivAt (fun x ↦ (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp x
    (hasFDerivAt_pi.mpr fun i ↦ h (l.get i) (l.get_mem i)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]

@[fun_prop]
/-
**HasFDerivWithinAt.list_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.list_prod' {l : List ι} {x : E} (h : forall i in l, HasF
DerivWithinAt (f i ·) (f' i) s x) : HasFDerivWithinAt (fun x => (l.map (f · x)).
prod) (∑ i : Fin l.length, ((l.take i).map (f · x)).prod • f' l[i] <• ((l.drop (
.succ i)).map (f · x)).prod) s x
参数：h : forall i in l, HasFDerivWithinAt (f i ·) (f' i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `List.get_eq_getElem`：get_eq_getElem? (l : List α) (i : Fin l.length) : l
.get i = l[i]?.get (by simp)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_get_finRange`：∀ {α : Type u_1} (l : List α), List.map l.get (Li
st.finRange l.length) = l
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `HasFDerivWithinAt.congr_fderiv`：HasFDerivWithinAt.congr_fderiv (h : HasF
DerivWithinAt f f' s x) (h' : f' = g') : HasFDerivWithinAt f g' s x
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `hasFDerivAt_list_prod_finRange'`：hasFDerivAt_list_prod_finRange' {n : Na
t} {x : Fin n -> 𝔸} : HasFDerivAt (𝕜
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_pi`：hasFDerivWithinAt_pi : HasFDerivWithinAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') s x ↔ forall i, HasFDerivWithinAt (φ i) (φ
' i) s x
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `List.map_take`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.take i l) = List.take i (List.map f l)
· 使用定理 `List.map_drop`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
{i : ℕ},   List.map f (List.drop i l) = List.drop i (List.map f l)
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 34 条，此处仅展示前 30 条）
-/
theorem HasFDerivWithinAt.list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, HasFDerivWithinAt (f i ·) (f' i) s x) :
    HasFDerivWithinAt (fun x ↦ (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) s x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  refine .congr_fderiv (hasFDerivAt_list_prod_finRange'.comp_hasFDerivWithinAt x
    (hasFDerivWithinAt_pi.mpr fun i ↦ h (l.get i) (l.get_mem i)) :) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]
/-
**fderiv_list_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_list_prod' {l : List ι} {x : E} (h : forall i in l, DifferentiableA
t 𝕜 (f i ·) x) : fderiv 𝕜 (fun x => (l.map (f · x)).prod) x = ∑ i : Fin l.length
, ((l.take i).map (f · x)).prod • (fderiv 𝕜 (fun x => f l[i] x) x) <• ((l.drop (
.succ i)).map (f · x)).prod
参数：h : forall i in l, DifferentiableAt 𝕜 (f i ·) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `HasFDerivAt.list_prod'`：HasFDerivAt.list_prod' {l : List ι} {x : E} (h :
 forall i in l, HasFDerivAt (f i ·) (f' i) x) : HasFDerivAt (fun x => (l.map (f 
· x)).prod) …
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, DifferentiableAt 𝕜 (f i ·) x) :
    fderiv 𝕜 (fun x ↦ (l.map (f · x)).prod) x =
      ∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        (fderiv 𝕜 (fun x ↦ f l[i] x) x) <• ((l.drop (.succ i)).map (f · x)).prod :=
  (HasFDerivAt.list_prod' fun i hi ↦ (h i hi).hasFDerivAt).fderiv
/-
**fderivWithin_list_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_list_prod' {l : List ι} {x : E} (hxs : UniqueDiffWithinAt 𝕜 s
 x) (h : forall i in l, DifferentiableWithinAt 𝕜 (f i ·) s x) : fderivWithin 𝕜 (
fun x => (l.map (f · x)).prod) s x = ∑ i : Fin l.length, ((l.take i).map (f · x)
).prod • (fderivWithin 𝕜 (fun x => f l[i] x) s x) <• ((l.drop (.succ i)).map (f 
· x)).prod
参数：hxs : UniqueDiffWithinAt 𝕜 s x；h : forall i in l, DifferentiableWithinAt 𝕜 (f
 i ·) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `HasFDerivWithinAt.list_prod'`：HasFDerivWithinAt.list_prod' {l : List ι} 
{x : E} (h : forall i in l, HasFDerivWithinAt (f i ·) (f' i) s x) : HasFDerivWit
hinAt (fun x => (l…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_list_prod' {l : List ι} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 s x) (h : ∀ i ∈ l, DifferentiableWithinAt 𝕜 (f i ·) s x) :
    fderivWithin 𝕜 (fun x ↦ (l.map (f · x)).prod) s x =
      ∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        (fderivWithin 𝕜 (fun x ↦ f l[i] x) s x) <• ((l.drop (.succ i)).map (f · x)).prod :=
  (HasFDerivWithinAt.list_prod' fun i hi ↦ (h i hi).hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]
/-
**HasStrictFDerivAt.multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E} (
h : forall i in u, HasStrictFDerivAt (g i ·) (g' i) x) : HasStrictFDerivAt (fun 
x => (u.map (g · x)).prod) (u.map fun i => ((u.erase i).map (g · x)).prod • g' i
).sum x
参数：h : forall i in u, HasStrictFDerivAt (g i ·) (g' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.attach_map_val`：attach_map_val (s : Multiset α) : s.attach.map 
Subtype.val = s
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `HasStrictFDerivAt.congr_fderiv`：HasStrictFDerivAt.congr_fderiv (h : HasS
trictFDerivAt f f' x) (h' : f' = g') : HasStrictFDerivAt f g' x
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `hasStrictFDerivAt_multiset_prod`：hasStrictFDerivAt_multiset_prod [Decida
bleEq ι] [Finite ι] {u : Multiset ι} {x : ι -> 𝔸'} : HasStrictFDerivAt (𝕜
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasStrictFDerivAt_pi`：hasStrictFDerivAt_pi : HasStrictFDerivAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') x ↔ forall i, HasStrictFDerivAt (φ i) (φ' 
i) x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用引理 `Multiset.erase_attach_map`：erase_attach_map (s : Multiset α) (f : α -> β
) (x : {x // x in s}) : (s.attach.erase x).map (fun j : {x // x in s} => f j) = 
(s.erase x).map…
· 使用定理 `Finset.sum_multiset_map_count`：∀ {ι : Type u_1} [inst : DecidableEq ι] (
s : Multiset ι) {M : Type u_5} [inst_1 : AddCommMonoid M] (f : ι → M),   (Multis
et.map f s).sum = ∑…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Multiset.count_attach`：count_attach (a : {x // x in s}) : s.attach.count
 a = s.count ↑a
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
（共 35 条，此处仅展示前 30 条）
-/
theorem HasStrictFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasStrictFDerivAt (g i ·) (g' i) x) :
    HasStrictFDerivAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasStrictFDerivAt_multiset_prod.comp x <|
      hasStrictFDerivAt_pi.mpr fun i ↦ h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

/--
Unlike `HasFDerivAt.finsetProd`, supports duplicate elements.
-/
@[fun_prop]
/-
**HasFDerivAt.multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E} (h : fo
rall i in u, HasFDerivAt (g i ·) (g' i) x) : HasFDerivAt (fun x => (u.map (g · x
)).prod) (u.map fun i => ((u.erase i).map (g · x)).prod • g' i).sum x
参数：h : forall i in u, HasFDerivAt (g i ·) (g' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.attach_map_val`：attach_map_val (s : Multiset α) : s.attach.map 
Subtype.val = s
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `HasFDerivAt.congr_fderiv`：HasFDerivAt.congr_fderiv (h : HasFDerivAt f f'
 x) (h' : f' = g') : HasFDerivAt f g' x
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `hasFDerivAt_multiset_prod`：hasFDerivAt_multiset_prod [DecidableEq ι] [Fi
nite ι] {u : Multiset ι} {x : ι -> 𝔸'} : HasFDerivAt (𝕜
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivAt_pi`：hasFDerivAt_pi : HasFDerivAt (fun x i => φ i x) (Continu
ousLinearMap.pi φ') x ↔ forall i, HasFDerivAt (φ i) (φ' i) x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用引理 `Multiset.erase_attach_map`：erase_attach_map (s : Multiset α) (f : α -> β
) (x : {x // x in s}) : (s.attach.erase x).map (fun j : {x // x in s} => f j) = 
(s.erase x).map…
· 使用定理 `Finset.sum_multiset_map_count`：∀ {ι : Type u_1} [inst : DecidableEq ι] (
s : Multiset ι) {M : Type u_5} [inst_1 : AddCommMonoid M] (f : ι → M),   (Multis
et.map f s).sum = ∑…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Multiset.count_attach`：count_attach (a : {x // x in s}) : s.attach.count
 a = s.count ↑a
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Unlike `HasFDerivAt.finsetProd`, supports duplicate elements.
-/
theorem HasFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasFDerivAt (g i ·) (g' i) x) :
    HasFDerivAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp x <| hasFDerivAt_pi.mpr fun i ↦ h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

@[fun_prop]
/-
**HasFDerivWithinAt.multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E} (
h : forall i in u, HasFDerivWithinAt (g i ·) (g' i) s x) : HasFDerivWithinAt (fu
n x => (u.map (g · x)).prod) (u.map fun i => ((u.erase i).map (g · x)).prod • g'
 i).sum s x
参数：h : forall i in u, HasFDerivWithinAt (g i ·) (g' i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.attach_map_val`：attach_map_val (s : Multiset α) : s.attach.map 
Subtype.val = s
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `HasFDerivWithinAt.congr_fderiv`：HasFDerivWithinAt.congr_fderiv (h : HasF
DerivWithinAt f f' s x) (h' : f' = g') : HasFDerivWithinAt f g' s x
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `hasFDerivAt_multiset_prod`：hasFDerivAt_multiset_prod [DecidableEq ι] [Fi
nite ι] {u : Multiset ι} {x : ι -> 𝔸'} : HasFDerivAt (𝕜
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_pi`：hasFDerivWithinAt_pi : HasFDerivWithinAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') s x ↔ forall i, HasFDerivWithinAt (φ i) (φ
' i) s x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用引理 `Multiset.erase_attach_map`：erase_attach_map (s : Multiset α) (f : α -> β
) (x : {x // x in s}) : (s.attach.erase x).map (fun j : {x // x in s} => f j) = 
(s.erase x).map…
· 使用定理 `Finset.sum_multiset_map_count`：∀ {ι : Type u_1} [inst : DecidableEq ι] (
s : Multiset ι) {M : Type u_5} [inst_1 : AddCommMonoid M] (f : ι → M),   (Multis
et.map f s).sum = ∑…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Multiset.count_attach`：count_attach (a : {x // x in s}) : s.attach.count
 a = s.count ↑a
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
（共 35 条，此处仅展示前 30 条）
-/
theorem HasFDerivWithinAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasFDerivWithinAt (g i ·) (g' i) s x) :
    HasFDerivWithinAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum s x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasFDerivAt_multiset_prod.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i ↦ h (Subtype.val i) i.prop :)
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])
/-
**fderiv_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E} (h : forall 
i in u, DifferentiableAt 𝕜 (g i ·) x) : fderiv 𝕜 (fun x => (u.map (g · x)).prod)
 x = (u.map fun i => ((u.erase i).map (g · x)).prod • fderiv 𝕜 (g i) x).sum
参数：h : forall i in u, DifferentiableAt 𝕜 (g i ·) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `HasFDerivAt.multiset_prod`：HasFDerivAt.multiset_prod [DecidableEq ι] {u 
: Multiset ι} {x : E} (h : forall i in u, HasFDerivAt (g i ·) (g' i) x) : HasFDe
rivAt (fun x =>…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, DifferentiableAt 𝕜 (g i ·) x) :
    fderiv 𝕜 (fun x ↦ (u.map (g · x)).prod) x =
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • fderiv 𝕜 (g i) x).sum :=
  (HasFDerivAt.multiset_prod fun i hi ↦ (h i hi).hasFDerivAt).fderiv
/-
**fderivWithin_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E} (hxs :
 UniqueDiffWithinAt 𝕜 s x) (h : forall i in u, DifferentiableWithinAt 𝕜 (g i ·) 
s x) : fderivWithin 𝕜 (fun x => (u.map (g · x)).prod) s x = (u.map fun i => ((u.
erase i).map (g · x)).prod • fderivWithin 𝕜 (g i) s x).sum
参数：hxs : UniqueDiffWithinAt 𝕜 s x；h : forall i in u, DifferentiableWithinAt 𝕜 (g
 i ·) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `HasFDerivWithinAt.multiset_prod`：HasFDerivWithinAt.multiset_prod [Decida
bleEq ι] {u : Multiset ι} {x : E} (h : forall i in u, HasFDerivWithinAt (g i ·) 
(g' i) s x) : HasFDer…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 s x) (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (g i ·) s x) :
    fderivWithin 𝕜 (fun x ↦ (u.map (g · x)).prod) s x =
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • fderivWithin 𝕜 (g i) s x).sum :=
  (HasFDerivWithinAt.multiset_prod fun i hi ↦ (h i hi).hasFDerivWithinAt).fderivWithin hxs
/-
**HasStrictFDerivAt.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.finsetProd [DecidableEq ι] {x : E} (hg : forall i in u, 
HasStrictFDerivAt (g i) (g' i) x) : HasStrictFDerivAt (∏ i in u, g i ·) (∑ i in 
u, (∏ j in u.erase i, g j x) • g' i) x
参数：hg : forall i in u, HasStrictFDerivAt (g i) (g' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `HasStrictFDerivAt.congr_fderiv`：HasStrictFDerivAt.congr_fderiv (h : HasS
trictFDerivAt f f' x) (h' : f' = g') : HasStrictFDerivAt f g' x
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `hasStrictFDerivAt_finsetProd`：hasStrictFDerivAt_finsetProd [DecidableEq 
ι] [Finite ι] {x : ι -> 𝔸'} : HasStrictFDerivAt (𝕜
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasStrictFDerivAt_pi`：hasStrictFDerivAt_pi : HasStrictFDerivAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') x ↔ forall i, HasStrictFDerivAt (φ i) (φ' 
i) x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_erase_attach`：prod_erase_attach [DecidableEq ι] {s : Finset 
ι} (f : ι -> M) (i : ↑s) : ∏ j in s.attach.erase i, f ↑j = ∏ j in s.erase ↑i, f 
j
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
（共 31 条，此处仅展示前 30 条）
-/
theorem HasStrictFDerivAt.finsetProd [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt (∏ i ∈ u, g i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, g j x) • g' i) x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasStrictFDerivAt_finsetProd.comp x <| hasStrictFDerivAt_pi.mpr fun i ↦ hg i i.prop)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")]
alias HasStrictFDerivAt.finset_prod := HasStrictFDerivAt.finsetProd
/-
**HasFDerivAt.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.finsetProd [DecidableEq ι] {x : E} (hg : forall i in u, HasFDe
rivAt (g i) (g' i) x) : HasFDerivAt (∏ i in u, g i ·) (∑ i in u, (∏ j in u.erase
 i, g j x) • g' i) x
参数：hg : forall i in u, HasFDerivAt (g i) (g' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `HasFDerivAt.congr_fderiv`：HasFDerivAt.congr_fderiv (h : HasFDerivAt f f'
 x) (h' : f' = g') : HasFDerivAt f g' x
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `hasFDerivAt_finsetProd`：hasFDerivAt_finsetProd [DecidableEq ι] [Finite ι
] {x : ι -> 𝔸'} : HasFDerivAt (𝕜
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivAt_pi`：hasFDerivAt_pi : HasFDerivAt (fun x i => φ i x) (Continu
ousLinearMap.pi φ') x ↔ forall i, HasFDerivAt (φ i) (φ' i) x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_erase_attach`：prod_erase_attach [DecidableEq ι] {s : Finset 
ι} (f : ι -> M) (i : ↑s) : ∏ j in s.attach.erase i, f ↑j = ∏ j in s.erase ↑i, f 
j
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
（共 31 条，此处仅展示前 30 条）
-/
theorem HasFDerivAt.finsetProd [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (∏ i ∈ u, g i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, g j x) • g' i) x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finsetProd.comp x <| hasFDerivAt_pi.mpr fun i ↦ hg (Subtype.val i) i.prop :)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")] alias HasFDerivAt.finset_prod := HasFDerivAt.finsetProd
/-
**HasFDerivWithinAt.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.finsetProd [DecidableEq ι] {x : E} (hg : forall i in u, 
HasFDerivWithinAt (g i) (g' i) s x) : HasFDerivWithinAt (∏ i in u, g i ·) (∑ i i
n u, (∏ j in u.erase i, g j x) • g' i) s x
参数：hg : forall i in u, HasFDerivWithinAt (g i) (g' i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `HasFDerivWithinAt.congr_fderiv`：HasFDerivWithinAt.congr_fderiv (h : HasF
DerivWithinAt f f' s x) (h' : f' = g') : HasFDerivWithinAt f g' s x
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `hasFDerivAt_finsetProd`：hasFDerivAt_finsetProd [DecidableEq ι] [Finite ι
] {x : ι -> 𝔸'} : HasFDerivAt (𝕜
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_pi`：hasFDerivWithinAt_pi : HasFDerivWithinAt (fun x i 
=> φ i x) (ContinuousLinearMap.pi φ') s x ↔ forall i, HasFDerivWithinAt (φ i) (φ
' i) s x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_erase_attach`：prod_erase_attach [DecidableEq ι] {s : Finset 
ι} (f : ι -> M) (i : ↑s) : ∏ j in s.attach.erase i, f ↑j = ∏ j in s.erase ↑i, f 
j
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
（共 31 条，此处仅展示前 30 条）
-/
theorem HasFDerivWithinAt.finsetProd [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (∏ i ∈ u, g i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, g j x) • g' i) s x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasFDerivAt_finsetProd.comp_hasFDerivWithinAt x <|
      hasFDerivWithinAt_pi.mpr fun i ↦ hg (Subtype.val i) i.prop :)
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")]
alias HasFDerivWithinAt.finset_prod := HasFDerivWithinAt.finsetProd
/-
**fderiv_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_finsetProd [DecidableEq ι] {x : E} (hg : forall i in u, Differentia
bleAt 𝕜 (g i) x) : fderiv 𝕜 (∏ i in u, g i ·) x = ∑ i in u, (∏ j in u.erase i, (
g j x)) • fderiv 𝕜 (g i) x
参数：hg : forall i in u, DifferentiableAt 𝕜 (g i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `HasFDerivAt.finsetProd`：HasFDerivAt.finsetProd [DecidableEq ι] {x : E} (
hg : forall i in u, HasFDerivAt (g i) (g' i) x) : HasFDerivAt (∏ i in u, g i ·) 
(∑ i in u, (…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_finsetProd [DecidableEq ι] {x : E} (hg : ∀ i ∈ u, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (∏ i ∈ u, g i ·) x = ∑ i ∈ u, (∏ j ∈ u.erase i, (g j x)) • fderiv 𝕜 (g i) x :=
  (HasFDerivAt.finsetProd fun i hi ↦ (hg i hi).hasFDerivAt).fderiv

@[deprecated (since := "2026-04-08")] alias fderiv_finset_prod := fderiv_finsetProd
/-
**fderivWithin_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_finsetProd [DecidableEq ι] {x : E} (hxs : UniqueDiffWithinAt 
𝕜 s x) (hg : forall i in u, DifferentiableWithinAt 𝕜 (g i) s x) : fderivWithin 𝕜
 (∏ i in u, g i ·) s x = ∑ i in u, (∏ j in u.erase i, (g j x)) • fderivWithin 𝕜 
(g i) s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hg : forall i in u, DifferentiableWithinAt 𝕜 (
g i) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `HasFDerivWithinAt.finsetProd`：HasFDerivWithinAt.finsetProd [DecidableEq 
ι] {x : E} (hg : forall i in u, HasFDerivWithinAt (g i) (g' i) s x) : HasFDerivW
ithinAt (∏ i in u,…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_finsetProd [DecidableEq ι] {x : E} (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hg : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (g i) s x) :
    fderivWithin 𝕜 (∏ i ∈ u, g i ·) s x =
      ∑ i ∈ u, (∏ j ∈ u.erase i, (g j x)) • fderivWithin 𝕜 (g i) s x :=
  (HasFDerivWithinAt.finsetProd fun i hi ↦ (hg i hi).hasFDerivWithinAt).fderivWithin hxs

@[deprecated (since := "2026-04-08")] alias fderivWithin_finset_prod := fderivWithin_finsetProd

end Comp

end Prod

section AlgebraInverse

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ring

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`.

TODO (low prio): prove a version without assumption `[HasSummableGeomSeries R]` but within the set
of units. -/
@[fun_prop]
/-
**hasFDerivAt_ringInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_ringInverse (x : Rˣ) : HasFDerivAt Ring.inverse (-mulLeftRight
 𝕜 R ↑x⁻¹ ↑x⁻¹) x
参数：x : Rˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `NormedRing.inverse_add_norm_diff_second_order`：inverse_add_norm_diff_sec
ond_order (x : Rˣ) : (fun t : R => (↑x + t)⁻¹ʳ - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =O[𝓝 0]
 fun t => ‖t‖ ^ 2
· 使用定理 `Asymptotics.isLittleO_norm_pow_id`：isLittleO_norm_pow_id {n : Nat} (h : 
1 < n) : (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => x
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ring.inverse_invertible`：Ring.inverse_invertible (x : α) [Invertible x] 
: x⁻¹ʳ = ⅟x
· 使用定理 `invOf_units`：invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟(u 
: α) = ↑u⁻¹
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b

--- 原说明 ---
At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of 
the inversion
operation is the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`.

TODO (low prio): prove a version without assumption `[HasSummableGeomSeries R]` 
but within the set
of units.
-/
theorem hasFDerivAt_ringInverse (x : Rˣ) :
    HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x := by
  have : (fun t : R => Ring.inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] id :=
    (inverse_add_norm_diff_second_order x).trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  simpa [hasFDerivAt_iff_isLittleO_nhds_zero] using! this

@[fun_prop]
/-
**differentiableAt_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_inverse {x : R} (hx : IsUnit x) : DifferentiableAt 𝕜 (@Ri
ng.inverse R _) x
参数：hx : IsUnit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `hasFDerivAt_ringInverse`：hasFDerivAt_ringInverse (x : Rˣ) : HasFDerivAt 
Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
-/
theorem differentiableAt_inverse {x : R} (hx : IsUnit x) :
    DifferentiableAt 𝕜 (@Ring.inverse R _) x :=
  let ⟨u, hu⟩ := hx; hu ▸ (hasFDerivAt_ringInverse u).differentiableAt

@[fun_prop]
/-
**differentiableWithinAt_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_inverse {x : R} (hx : IsUnit x) (s : Set R) : Diffe
rentiableWithinAt 𝕜 (@Ring.inverse R _) s x
参数：hx : IsUnit x；s : Set R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_inverse`：differentiableAt_inverse {x : R} (hx : IsUnit 
x) : DifferentiableAt 𝕜 (@Ring.inverse R _) x
-/
theorem differentiableWithinAt_inverse {x : R} (hx : IsUnit x) (s : Set R) :
    DifferentiableWithinAt 𝕜 (@Ring.inverse R _) s x :=
  (differentiableAt_inverse hx).differentiableWithinAt

@[fun_prop]
/-
**differentiableOn_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_inverse : DifferentiableOn 𝕜 (@Ring.inverse R _) {x | IsU
nit x}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAt_inverse`：differentiableWithinAt_inverse {x : R} (
hx : IsUnit x) (s : Set R) : DifferentiableWithinAt 𝕜 (@Ring.inverse R _) s x
-/
theorem differentiableOn_inverse : DifferentiableOn 𝕜 (@Ring.inverse R _) {x | IsUnit x} :=
  fun _x hx => differentiableWithinAt_inverse hx _
/-
**fderiv_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_inverse (x : Rˣ) : fderiv 𝕜 (@Ring.inverse R _) x = -mulLeftRight 𝕜
 R ↑x⁻¹ ↑x⁻¹
参数：x : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `hasFDerivAt_ringInverse`：hasFDerivAt_ringInverse (x : Rˣ) : HasFDerivAt 
Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
-/
theorem fderiv_inverse (x : Rˣ) : fderiv 𝕜 (@Ring.inverse R _) x = -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹ :=
  (hasFDerivAt_ringInverse x).fderiv
/-
**hasStrictFDerivAt_ringInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_ringInverse (x : Rˣ) : HasStrictFDerivAt Ring.inverse (-
mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
参数：x : Rˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `fderiv_inverse`：fderiv_inverse (x : Rˣ) : fderiv 𝕜 (@Ring.inverse R _) x
 = -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹
· 使用定理 `AnalyticAt.hasStrictFDerivAt`：AnalyticAt.hasStrictFDerivAt (h : Analytic
At 𝕜 f x) : HasStrictFDerivAt f (fderiv 𝕜 f x) x
· 使用引理 `analyticAt_inverse`：analyticAt_inverse [HasSummableGeomSeries A] (z : Aˣ
) : AnalyticAt 𝕜 Ring.inverse (z : A)
-/
theorem hasStrictFDerivAt_ringInverse (x : Rˣ) :
    HasStrictFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x := by
  convert! (analyticAt_inverse (𝕜 := 𝕜) x).hasStrictFDerivAt
  exact (fderiv_inverse x).symm

variable {h : E → R} {z : E} {S : Set E}

@[fun_prop]
/-
**DifferentiableWithinAt.inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.inverse (hf : DifferentiableWithinAt 𝕜 h S z) (hz :
 IsUnit (h z)) : DifferentiableWithinAt 𝕜 (fun x => (h x)⁻¹ʳ) S z
参数：hf : DifferentiableWithinAt 𝕜 h S z；hz : IsUnit (h z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `differentiableAt_inverse`：differentiableAt_inverse {x : R} (hx : IsUnit 
x) : DifferentiableAt 𝕜 (@Ring.inverse R _) x
-/
theorem DifferentiableWithinAt.inverse (hf : DifferentiableWithinAt 𝕜 h S z) (hz : IsUnit (h z)) :
    DifferentiableWithinAt 𝕜 (fun x => (h x)⁻¹ʳ) S z :=
  (differentiableAt_inverse hz).comp_differentiableWithinAt z hf

@[simp, fun_prop]
/-
**DifferentiableAt.inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.inverse (hf : DifferentiableAt 𝕜 h z) (hz : IsUnit (h z))
 : DifferentiableAt 𝕜 (fun x => (h x)⁻¹ʳ) z
参数：hf : DifferentiableAt 𝕜 h z；hz : IsUnit (h z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `differentiableAt_inverse`：differentiableAt_inverse {x : R} (hx : IsUnit 
x) : DifferentiableAt 𝕜 (@Ring.inverse R _) x
-/
theorem DifferentiableAt.inverse (hf : DifferentiableAt 𝕜 h z) (hz : IsUnit (h z)) :
    DifferentiableAt 𝕜 (fun x => (h x)⁻¹ʳ) z :=
  (differentiableAt_inverse hz).comp z hf

@[fun_prop]
/-
**DifferentiableOn.inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.inverse (hf : DifferentiableOn 𝕜 h S) (hz : forall x in S
, IsUnit (h x)) : DifferentiableOn 𝕜 (fun x => (h x)⁻¹ʳ) S
参数：hf : DifferentiableOn 𝕜 h S；hz : forall x in S, IsUnit (h x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.inverse`：DifferentiableWithinAt.inverse (hf : Dif
ferentiableWithinAt 𝕜 h S z) (hz : IsUnit (h z)) : DifferentiableWithinAt 𝕜 (fun
 x => (h x)⁻¹ʳ) S z
-/
theorem DifferentiableOn.inverse (hf : DifferentiableOn 𝕜 h S) (hz : ∀ x ∈ S, IsUnit (h x)) :
    DifferentiableOn 𝕜 (fun x => (h x)⁻¹ʳ) S := fun x h => (hf x h).inverse (hz x h)

@[simp, fun_prop]
/-
**Differentiable.inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.inverse (hf : Differentiable 𝕜 h) (hz : forall x, IsUnit (h
 x)) : Differentiable 𝕜 fun x => (h x)⁻¹ʳ
参数：hf : Differentiable 𝕜 h；hz : forall x, IsUnit (h x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.inverse`：DifferentiableAt.inverse (hf : DifferentiableA
t 𝕜 h z) (hz : IsUnit (h z)) : DifferentiableAt 𝕜 (fun x => (h x)⁻¹ʳ) z
-/
theorem Differentiable.inverse (hf : Differentiable 𝕜 h) (hz : ∀ x, IsUnit (h x)) :
    Differentiable 𝕜 fun x => (h x)⁻¹ʳ := fun x => (hf x).inverse (hz x)

end AlgebraInverse

/-! ### Derivative of the inverse in a division ring

Note that some lemmas are primed as they are expressed without commutativity, whereas their
counterparts in commutative fields involve simpler expressions, and are given in
`Mathlib/Analysis/Calculus/Deriv/Inv.lean`.
-/

section DivisionRingInverse

variable {R : Type*} [NormedDivisionRing R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Ring

/-- At an invertible element `x` of a normed division algebra `R`, the inversion is strictly
differentiable, with derivative the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`. For a nicer formula in
the commutative case, see `hasStrictFDerivAt_inv`. -/
/-
**hasStrictFDerivAt_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_inv' {x : R} (hx : x != 0) : HasStrictFDerivAt Inv.inv (
-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `hasStrictFDerivAt_ringInverse`：hasStrictFDerivAt_ringInverse (x : Rˣ) : 
HasStrictFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K

--- 原说明 ---
At an invertible element `x` of a normed division algebra `R`, the inversion is 
strictly
differentiable, with derivative the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`. For a 
nicer formula in
the commutative case, see `hasStrictFDerivAt_inv`.
-/
theorem hasStrictFDerivAt_inv' {x : R} (hx : x ≠ 0) :
    HasStrictFDerivAt Inv.inv (-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x := by
  simpa using hasStrictFDerivAt_ringInverse (Units.mk0 _ hx)

/-- At an invertible element `x` of a normed division algebra `R`, the Fréchet derivative of the
inversion operation is the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`. For a nicer formula in the
commutative case, see `hasFDerivAt_inv`. -/
@[fun_prop]
/-
**hasFDerivAt_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_inv' {x : R} (hx : x != 0) : HasFDerivAt Inv.inv (-mulLeftRigh
t 𝕜 R x⁻¹ x⁻¹) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `hasFDerivAt_ringInverse`：hasFDerivAt_ringInverse (x : Rˣ) : HasFDerivAt 
Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K

--- 原说明 ---
At an invertible element `x` of a normed division algebra `R`, the Fréchet deriv
ative of the
inversion operation is the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`. For a nicer for
mula in the
commutative case, see `hasFDerivAt_inv`.
-/
theorem hasFDerivAt_inv' {x : R} (hx : x ≠ 0) :
    HasFDerivAt Inv.inv (-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x := by
  simpa using hasFDerivAt_ringInverse (Units.mk0 _ hx)

@[fun_prop]
/-
**differentiableAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_inv {x : R} (hx : x != 0) : DifferentiableAt 𝕜 Inv.inv x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `hasFDerivAt_inv'`：hasFDerivAt_inv' {x : R} (hx : x != 0) : HasFDerivAt I
nv.inv (-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x
-/
theorem differentiableAt_inv {x : R} (hx : x ≠ 0) : DifferentiableAt 𝕜 Inv.inv x :=
  (hasFDerivAt_inv' hx).differentiableAt

@[fun_prop]
/-
**differentiableWithinAt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_inv {x : R} (hx : x != 0) (s : Set R) : Differentia
bleWithinAt 𝕜 (fun x => x⁻¹) s x
参数：hx : x != 0；s : Set R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_inv`：differentiableAt_inv {x : R} (hx : x != 0) : Diffe
rentiableAt 𝕜 Inv.inv x
-/
theorem differentiableWithinAt_inv {x : R} (hx : x ≠ 0) (s : Set R) :
    DifferentiableWithinAt 𝕜 (fun x => x⁻¹) s x :=
  (differentiableAt_inv hx).differentiableWithinAt

@[fun_prop]
/-
**differentiableOn_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_inv : DifferentiableOn 𝕜 (fun x : R => x⁻¹) {x | x != 0}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `differentiableWithinAt_inv`：differentiableWithinAt_inv {x : R} (hx : x !
= 0) (s : Set R) : DifferentiableWithinAt 𝕜 (fun x => x⁻¹) s x
-/
theorem differentiableOn_inv : DifferentiableOn 𝕜 (fun x : R => x⁻¹) {x | x ≠ 0} := fun _x hx =>
  differentiableWithinAt_inv hx _

/-- Non-commutative version of `fderiv_inv` -/
/-
**fderiv_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_inv' {x : R} (hx : x != 0) : fderiv 𝕜 Inv.inv x = -mulLeftRight 𝕜 R
 x⁻¹ x⁻¹
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `hasFDerivAt_inv'`：hasFDerivAt_inv' {x : R} (hx : x != 0) : HasFDerivAt I
nv.inv (-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x

--- 原说明 ---
Non-commutative version of `fderiv_inv`
-/
theorem fderiv_inv' {x : R} (hx : x ≠ 0) : fderiv 𝕜 Inv.inv x = -mulLeftRight 𝕜 R x⁻¹ x⁻¹ :=
  (hasFDerivAt_inv' hx).fderiv

/-- Non-commutative version of `fderivWithin_inv` -/
/-
**fderivWithin_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_inv' {s : Set R} {x : R} (hx : x != 0) (hxs : UniqueDiffWithi
nAt 𝕜 s x) : fderivWithin 𝕜 (fun x => x⁻¹) s x = -mulLeftRight 𝕜 R x⁻¹ x⁻¹
参数：hx : x != 0；hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `differentiableAt_inv`：differentiableAt_inv {x : R} (hx : x != 0) : Diffe
rentiableAt 𝕜 Inv.inv x
· 使用定理 `fderiv_inv'`：fderiv_inv' {x : R} (hx : x != 0) : fderiv 𝕜 Inv.inv x = -m
ulLeftRight 𝕜 R x⁻¹ x⁻¹

--- 原说明 ---
Non-commutative version of `fderivWithin_inv`
-/
theorem fderivWithin_inv' {s : Set R} {x : R} (hx : x ≠ 0) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x => x⁻¹) s x = -mulLeftRight 𝕜 R x⁻¹ x⁻¹ := by
  rw [DifferentiableAt.fderivWithin (differentiableAt_inv hx) hxs]
  exact fderiv_inv' hx

variable {h : E → R} {z : E} {S : Set E}

@[to_fun (attr := fun_prop)]
/-
**DifferentiableWithinAt.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.inv (hf : DifferentiableWithinAt 𝕜 h S z) (hz : h z
 != 0) : DifferentiableWithinAt 𝕜 (h⁻¹) S z
参数：hf : DifferentiableWithinAt 𝕜 h S z；hz : h z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `differentiableAt_inv`：differentiableAt_inv {x : R} (hx : x != 0) : Diffe
rentiableAt 𝕜 Inv.inv x
-/
theorem DifferentiableWithinAt.inv (hf : DifferentiableWithinAt 𝕜 h S z) (hz : h z ≠ 0) :
    DifferentiableWithinAt 𝕜 (h⁻¹) S z :=
  (differentiableAt_inv hz).comp_differentiableWithinAt z hf

@[to_fun (attr := simp, fun_prop)]
/-
**DifferentiableAt.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.inv (hf : DifferentiableAt 𝕜 h z) (hz : h z != 0) : Diffe
rentiableAt 𝕜 (h⁻¹) z
参数：hf : DifferentiableAt 𝕜 h z；hz : h z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `differentiableAt_inv`：differentiableAt_inv {x : R} (hx : x != 0) : Diffe
rentiableAt 𝕜 Inv.inv x
-/
theorem DifferentiableAt.inv (hf : DifferentiableAt 𝕜 h z) (hz : h z ≠ 0) :
    DifferentiableAt 𝕜 (h⁻¹) z :=
  (differentiableAt_inv hz).comp z hf

@[to_fun (attr := fun_prop)]
/-
**DifferentiableOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.inv (hf : DifferentiableOn 𝕜 h S) (hz : forall x in S, h 
x != 0) : DifferentiableOn 𝕜 (h⁻¹) S
参数：hf : DifferentiableOn 𝕜 h S；hz : forall x in S, h x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.inv`：DifferentiableWithinAt.inv (hf : Differentia
bleWithinAt 𝕜 h S z) (hz : h z != 0) : DifferentiableWithinAt 𝕜 (h⁻¹) S z
-/
theorem DifferentiableOn.inv (hf : DifferentiableOn 𝕜 h S) (hz : ∀ x ∈ S, h x ≠ 0) :
    DifferentiableOn 𝕜 (h⁻¹) S := fun x h => (hf x h).inv (hz x h)

@[to_fun (attr := simp, fun_prop)]
/-
**Differentiable.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.inv (hf : Differentiable 𝕜 h) (hz : forall x, h x != 0) : D
ifferentiable 𝕜 (h⁻¹)
参数：hf : Differentiable 𝕜 h；hz : forall x, h x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.inv`：DifferentiableAt.inv (hf : DifferentiableAt 𝕜 h z)
 (hz : h z != 0) : DifferentiableAt 𝕜 (h⁻¹) z
-/
theorem Differentiable.inv (hf : Differentiable 𝕜 h) (hz : ∀ x, h x ≠ 0) :
    Differentiable 𝕜 (h⁻¹) := fun x => (hf x).inv (hz x)

end DivisionRingInverse

end

