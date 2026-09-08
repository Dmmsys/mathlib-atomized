/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Multiplicative operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* composition of continuous linear maps
* application of continuous (multi)linear maps to a constant
-/

public section


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

section CLMCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {c : E → G →L[𝕜] H}
  {c' : E →L[𝕜] G →L[𝕜] H} {d : E → F →L[𝕜] G} {d' : E →L[𝕜] F →L[𝕜] G} {u : E → G} {u' : E →L[𝕜] G}

@[fun_prop]
/-
**HasStrictFDerivAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.clm_comp (hc : HasStrictFDerivAt c c' x) (hd : HasStrict
FDerivAt d d' x) : HasStrictFDerivAt (fun y => (c y).comp (d y)) ((compL 𝕜 F G H
 (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x
参数：hc : HasStrictFDerivAt c c' x；hd : HasStrictFDerivAt d d' x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `isBoundedBilinearMap_comp`：isBoundedBilinearMap_comp : IsBoundedBilinear
Map 𝕜 fun p : (F ->L[𝕜] G) × (E ->L[𝕜] F) => p.1.comp p.2
· 使用定理 `IsBoundedBilinearMap.hasStrictFDerivAt`：IsBoundedBilinearMap.hasStrictFD
erivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasStrictFDerivAt b (h.deriv
 p) p
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasStrictFDerivAt.clm_comp (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x) :
    HasStrictFDerivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
  (isBoundedBilinearMap_comp.hasStrictFDerivAt (c x, d x)).comp x (hc.prodMk hd)

@[fun_prop]
/-
**HasFDerivWithinAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.clm_comp (hc : HasFDerivWithinAt c c' s x) (hd : HasFDer
ivWithinAt d d' s x) : HasFDerivWithinAt (fun y => (c y).comp (d y)) ((compL 𝕜 F
 G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') s x
参数：hc : HasFDerivWithinAt c c' s x；hd : HasFDerivWithinAt d d' s x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `isBoundedBilinearMap_comp`：isBoundedBilinearMap_comp : IsBoundedBilinear
Map 𝕜 fun p : (F ->L[𝕜] G) × (E ->L[𝕜] F) => p.1.comp p.2
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasFDerivWithinAt.clm_comp (hc : HasFDerivWithinAt c c' s x)
    (hd : HasFDerivWithinAt d d' s x) :
    HasFDerivWithinAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') s x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_comp.hasFDerivAt (c x, d x)).comp_hasFDerivWithinAt x (hc.prodMk hd)

@[fun_prop]
/-
**HasFDerivAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.clm_comp (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
 HasFDerivAt (fun y => (c y).comp (d y)) ((compL 𝕜 F G H (c x)).comp d' + ((comp
L 𝕜 F G H).flip (d x)).comp c') x
参数：hc : HasFDerivAt c c' x；hd : HasFDerivAt d d' x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `isBoundedBilinearMap_comp`：isBoundedBilinearMap_comp : IsBoundedBilinear
Map 𝕜 fun p : (F ->L[𝕜] G) × (E ->L[𝕜] F) => p.1.comp p.2
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
-/
theorem HasFDerivAt.clm_comp (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
    HasFDerivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_comp.hasFDerivAt (c x, d x)).comp x <| hc.prodMk hd

@[fun_prop]
/-
**DifferentiableWithinAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.clm_comp (hc : DifferentiableWithinAt 𝕜 c s x) (hd 
: DifferentiableWithinAt 𝕜 d s x) : DifferentiableWithinAt 𝕜 (fun y => (c y).com
p (d y)) s x
参数：hc : DifferentiableWithinAt 𝕜 c s x；hd : DifferentiableWithinAt 𝕜 d s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivWithinAt.clm_comp`：HasFDerivWithinAt.clm_comp (hc : HasFDerivWi
thinAt c c' s x) (hd : HasFDerivWithinAt d d' s x) : HasFDerivWithinAt (fun y =>
 (c y).comp (d y…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.clm_comp (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    DifferentiableWithinAt 𝕜 (fun y => (c y).comp (d y)) s x :=
  (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : Differentiab
leAt 𝕜 d x) : DifferentiableAt 𝕜 (fun y => (c y).comp (d y)) x
参数：hc : DifferentiableAt 𝕜 c x；hd : DifferentiableAt 𝕜 d x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivAt.clm_comp`：HasFDerivAt.clm_comp (hc : HasFDerivAt c c' x) (hd
 : HasFDerivAt d d' x) : HasFDerivAt (fun y => (c y).comp (d y)) ((compL 𝕜 F G H
 (c x)).co…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    DifferentiableAt 𝕜 (fun y => (c y).comp (d y)) x :=
  (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.clm_comp (hc : DifferentiableOn 𝕜 c s) (hd : Differentiab
leOn 𝕜 d s) : DifferentiableOn 𝕜 (fun y => (c y).comp (d y)) s
参数：hc : DifferentiableOn 𝕜 c s；hd : DifferentiableOn 𝕜 d s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableWithinAt.clm_comp`：DifferentiableWithinAt.clm_comp (hc : D
ifferentiableWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x) : Different
iableWithinAt 𝕜 (fun …
-/
theorem DifferentiableOn.clm_comp (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s) :
    DifferentiableOn 𝕜 (fun y => (c y).comp (d y)) s := fun x hx => (hc x hx).clm_comp (hd x hx)

@[fun_prop]
/-
**Differentiable.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.clm_comp (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d
) : Differentiable 𝕜 fun y => (c y).comp (d y)
参数：hc : Differentiable 𝕜 c；hd : Differentiable 𝕜 d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableAt.clm_comp`：DifferentiableAt.clm_comp (hc : Differentiabl
eAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) : DifferentiableAt 𝕜 (fun y => (c y).co
mp (d y)) x
-/
theorem Differentiable.clm_comp (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) :
    Differentiable 𝕜 fun y => (c y).comp (d y) := fun x => (hc x).clm_comp (hd x)
/-
**fderivWithin_clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_clm_comp (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : Differentiabl
eWithinAt 𝕜 c s x) (hd : DifferentiableWithinAt 𝕜 d s x) : fderivWithin 𝕜 (fun y
 => (c y).comp (d y)) s x = (compL 𝕜 F G H (c x)).comp (fderivWithin 𝕜 d s x) + 
((compL 𝕜 F G H).flip (d x)).comp (fderivWithin 𝕜 c s x)
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；hd : Diffe
rentiableWithinAt 𝕜 d s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.clm_comp`：HasFDerivWithinAt.clm_comp (hc : HasFDerivWi
thinAt c c' s x) (hd : HasFDerivWithinAt d d' s x) : HasFDerivWithinAt (fun y =>
 (c y).comp (d y…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_clm_comp (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => (c y).comp (d y)) s x =
      (compL 𝕜 F G H (c x)).comp (fderivWithin 𝕜 d s x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderivWithin 𝕜 c s x) :=
  (hc.hasFDerivWithinAt.clm_comp hd.hasFDerivWithinAt).fderivWithin hxs
/-
**fderiv_clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x
) : fderiv 𝕜 (fun y => (c y).comp (d y)) x = (compL 𝕜 F G H (c x)).comp (fderiv 
𝕜 d x) + ((compL 𝕜 F G H).flip (d x)).comp (fderiv 𝕜 c x)
参数：hc : DifferentiableAt 𝕜 c x；hd : DifferentiableAt 𝕜 d x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.clm_comp`：HasFDerivAt.clm_comp (hc : HasFDerivAt c c' x) (hd
 : HasFDerivAt d d' x) : HasFDerivAt (fun y => (c y).comp (d y)) ((compL 𝕜 F G H
 (c x)).co…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => (c y).comp (d y)) x =
      (compL 𝕜 F G H (c x)).comp (fderiv 𝕜 d x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderiv 𝕜 c x) :=
  (hc.hasFDerivAt.clm_comp hd.hasFDerivAt).fderiv

@[fun_prop]
/-
**HasStrictFDerivAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.clm_apply (hc : HasStrictFDerivAt c c' x) (hu : HasStric
tFDerivAt u u' x) : HasStrictFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'
.flip (u x)) x
参数：hc : HasStrictFDerivAt c c' x；hu : HasStrictFDerivAt u u' x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
· 使用定理 `IsBoundedBilinearMap.hasStrictFDerivAt`：IsBoundedBilinearMap.hasStrictFD
erivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasStrictFDerivAt b (h.deriv
 p) p
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasStrictFDerivAt.clm_apply (hc : HasStrictFDerivAt c c' x)
    (hu : HasStrictFDerivAt u u' x) :
    HasStrictFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
  (isBoundedBilinearMap_apply.hasStrictFDerivAt (c x, u x)).comp x (hc.prodMk hu)

@[fun_prop]
/-
**HasFDerivWithinAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.clm_apply (hc : HasFDerivWithinAt c c' s x) (hu : HasFDe
rivWithinAt u u' s x) : HasFDerivWithinAt (fun y => (c y) (u y)) ((c x).comp u' 
+ c'.flip (u x)) s x
参数：hc : HasFDerivWithinAt c c' s x；hu : HasFDerivWithinAt u u' s x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasFDerivWithinAt.clm_apply (hc : HasFDerivWithinAt c c' s x)
    (hu : HasFDerivWithinAt u u' s x) :
    HasFDerivWithinAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) s x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_apply.hasFDerivAt (c x, u x)).comp_hasFDerivWithinAt x
    (hc.prodMk hu)

@[fun_prop]
/-
**HasFDerivAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.clm_apply (hc : HasFDerivAt c c' x) (hu : HasFDerivAt u u' x) 
: HasFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x
参数：hc : HasFDerivAt c c' x；hu : HasFDerivAt u u' x。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
· 使用定理 `IsBoundedBilinearMap.hasFDerivAt`：IsBoundedBilinearMap.hasFDerivAt (h : 
IsBoundedBilinearMap 𝕜 b) (p : E × F) : HasFDerivAt b (h.deriv p) p
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
-/
theorem HasFDerivAt.clm_apply (hc : HasFDerivAt c c' x) (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_apply.hasFDerivAt (c x, u x)).comp x (hc.prodMk hu)

@[fun_prop]
/-
**DifferentiableWithinAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.clm_apply (hc : DifferentiableWithinAt 𝕜 c s x) (hu
 : DifferentiableWithinAt 𝕜 u s x) : DifferentiableWithinAt 𝕜 (fun y => (c y) (u
 y)) s x
参数：hc : DifferentiableWithinAt 𝕜 c s x；hu : DifferentiableWithinAt 𝕜 u s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivWithinAt.clm_apply`：HasFDerivWithinAt.clm_apply (hc : HasFDeriv
WithinAt c c' s x) (hu : HasFDerivWithinAt u u' s x) : HasFDerivWithinAt (fun y 
=> (c y) (u y)) (…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.clm_apply (hc : DifferentiableWithinAt 𝕜 c s x)
    (hu : DifferentiableWithinAt 𝕜 u s x) : DifferentiableWithinAt 𝕜 (fun y => (c y) (u y)) s x :=
  (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : Differentia
bleAt 𝕜 u x) : DifferentiableAt 𝕜 (fun y => (c y) (u y)) x
参数：hc : DifferentiableAt 𝕜 c x；hu : DifferentiableAt 𝕜 u x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivAt.clm_apply`：HasFDerivAt.clm_apply (hc : HasFDerivAt c c' x) (
hu : HasFDerivAt u u' x) : HasFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c
'.flip (u x…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    DifferentiableAt 𝕜 (fun y => (c y) (u y)) x :=
  (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.clm_apply (hc : DifferentiableOn 𝕜 c s) (hu : Differentia
bleOn 𝕜 u s) : DifferentiableOn 𝕜 (fun y => (c y) (u y)) s
参数：hc : DifferentiableOn 𝕜 c s；hu : DifferentiableOn 𝕜 u s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableWithinAt.clm_apply`：DifferentiableWithinAt.clm_apply (hc :
 DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s x) : Differe
ntiableWithinAt 𝕜 (fun…
-/
theorem DifferentiableOn.clm_apply (hc : DifferentiableOn 𝕜 c s) (hu : DifferentiableOn 𝕜 u s) :
    DifferentiableOn 𝕜 (fun y => (c y) (u y)) s := fun x hx => (hc x hx).clm_apply (hu x hx)

@[fun_prop]
/-
**Differentiable.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.clm_apply (hc : Differentiable 𝕜 c) (hu : Differentiable 𝕜 
u) : Differentiable 𝕜 fun y => (c y) (u y)
参数：hc : Differentiable 𝕜 c；hu : Differentiable 𝕜 u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableAt.clm_apply`：DifferentiableAt.clm_apply (hc : Differentia
bleAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) : DifferentiableAt 𝕜 (fun y => (c y) 
(u y)) x
-/
theorem Differentiable.clm_apply (hc : Differentiable 𝕜 c) (hu : Differentiable 𝕜 u) :
    Differentiable 𝕜 fun y => (c y) (u y) := fun x => (hc x).clm_apply (hu x)
/-
**fderivWithin_clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_clm_apply (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : Differentiab
leWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s x) : fderivWithin 𝕜 (fun 
y => (c y) (u y)) s x = (c x).comp (fderivWithin 𝕜 u s x) + (fderivWithin 𝕜 c s 
x).flip (u x)
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；hu : Diffe
rentiableWithinAt 𝕜 u s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.clm_apply`：HasFDerivWithinAt.clm_apply (hc : HasFDeriv
WithinAt c c' s x) (hu : HasFDerivWithinAt u u' s x) : HasFDerivWithinAt (fun y 
=> (c y) (u y)) (…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_clm_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s x) :
    fderivWithin 𝕜 (fun y => (c y) (u y)) s x =
      (c x).comp (fderivWithin 𝕜 u s x) + (fderivWithin 𝕜 c s x).flip (u x) :=
  (hc.hasFDerivWithinAt.clm_apply hu.hasFDerivWithinAt).fderivWithin hxs
/-
**fderiv_clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u 
x) : fderiv 𝕜 (fun y => (c y) (u y)) x = (c x).comp (fderiv 𝕜 u x) + (fderiv 𝕜 c
 x).flip (u x)
参数：hc : DifferentiableAt 𝕜 c x；hu : DifferentiableAt 𝕜 u x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.clm_apply`：HasFDerivAt.clm_apply (hc : HasFDerivAt c c' x) (
hu : HasFDerivAt u u' x) : HasFDerivAt (fun y => (c y) (u y)) ((c x).comp u' + c
'.flip (u x…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    fderiv 𝕜 (fun y => (c y) (u y)) x = (c x).comp (fderiv 𝕜 u x) + (fderiv 𝕜 c x).flip (u x) :=
  (hc.hasFDerivAt.clm_apply hu.hasFDerivAt).fderiv

end CLMCompApply

section ContinuousMultilinearApplyConst

/-! ### Derivative of the application of continuous multilinear maps to a constant -/

variable {ι : Type*}
  {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {c : E → ContinuousMultilinearMap 𝕜 M H}
  {c' : E →L[𝕜] ContinuousMultilinearMap 𝕜 M H}

section fintype

variable [Fintype ι]

@[fun_prop]
/-
**HasStrictFDerivAt.continuousMultilinear_apply_const** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：HasStrictFDerivAt.continuousMultilinear_apply_const (hc : HasStrictFDerivA
t c c' x) (u : forall i, M i) : HasStrictFDerivAt (fun y => (c y) u) (c'.flipMul
tilinear u) x
参数：hc : HasStrictFDerivAt c c' x；u : forall i, M i。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
theorem HasStrictFDerivAt.continuousMultilinear_apply_const (hc : HasStrictFDerivAt c c' x)
    (u : ∀ i, M i) : HasStrictFDerivAt (fun y ↦ (c y) u) (c'.flipMultilinear u) x :=
  (ContinuousMultilinearMap.apply 𝕜 M H u).hasStrictFDerivAt.comp x hc

@[fun_prop]
/-
**HasFDerivWithinAt.continuousMultilinear_apply_const** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：HasFDerivWithinAt.continuousMultilinear_apply_const (hc : HasFDerivWithinA
t c c' s x) (u : forall i, M i) : HasFDerivWithinAt (fun y => (c y) u) (c'.flipM
ultilinear u) s x
参数：hc : HasFDerivWithinAt c c' s x；u : forall i, M i。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem HasFDerivWithinAt.continuousMultilinear_apply_const (hc : HasFDerivWithinAt c c' s x)
    (u : ∀ i, M i) :
    HasFDerivWithinAt (fun y ↦ (c y) u) (c'.flipMultilinear u) s x :=
  (ContinuousMultilinearMap.apply 𝕜 M H u).hasFDerivAt.comp_hasFDerivWithinAt x hc

@[fun_prop]
/-
**HasFDerivAt.continuousMultilinear_apply_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.continuousMultilinear_apply_const (hc : HasFDerivAt c c' x) (u
 : forall i, M i) : HasFDerivAt (fun y => (c y) u) (c'.flipMultilinear u) x
参数：hc : HasFDerivAt c c' x；u : forall i, M i。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem HasFDerivAt.continuousMultilinear_apply_const (hc : HasFDerivAt c c' x) (u : ∀ i, M i) :
    HasFDerivAt (fun y ↦ (c y) u) (c'.flipMultilinear u) x :=
  (ContinuousMultilinearMap.apply 𝕜 M H u).hasFDerivAt.comp x hc
/-
**fderivWithin_continuousMultilinear_apply_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_continuousMultilinear_apply_const (hxs : UniqueDiffWithinAt 𝕜
 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (u : forall i, M i) : fderivWithin 𝕜
 (fun y => (c y) u) s x = ((fderivWithin 𝕜 c s x).flipMultilinear u)
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；u : forall
 i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.continuousMultilinear_apply_const`：HasFDerivWithinAt.c
ontinuousMultilinear_apply_const (hc : HasFDerivWithinAt c c' s x) (u : forall i
, M i) : HasFDerivWithinAt (fun y => (c y…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_continuousMultilinear_apply_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ∀ i, M i) :
    fderivWithin 𝕜 (fun y ↦ (c y) u) s x = ((fderivWithin 𝕜 c s x).flipMultilinear u) :=
  (hc.hasFDerivWithinAt.continuousMultilinear_apply_const u).fderivWithin hxs
/-
**fderiv_continuousMultilinear_apply_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_continuousMultilinear_apply_const (hc : DifferentiableAt 𝕜 c x) (u 
: forall i, M i) : (fderiv 𝕜 (fun y => (c y) u) x) = (fderiv 𝕜 c x).flipMultilin
ear u
参数：hc : DifferentiableAt 𝕜 c x；u : forall i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.continuousMultilinear_apply_const`：HasFDerivAt.continuousMul
tilinear_apply_const (hc : HasFDerivAt c c' x) (u : forall i, M i) : HasFDerivAt
 (fun y => (c y) u) (c'.flipMultili…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_continuousMultilinear_apply_const (hc : DifferentiableAt 𝕜 c x) (u : ∀ i, M i) :
    (fderiv 𝕜 (fun y ↦ (c y) u) x) = (fderiv 𝕜 c x).flipMultilinear u :=
  (hc.hasFDerivAt.continuousMultilinear_apply_const u).fderiv

end fintype

section finite

variable [Finite ι]

@[fun_prop]
/-
**DifferentiableWithinAt.continuousMultilinear_apply_const** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：DifferentiableWithinAt.continuousMultilinear_apply_const (hc : Differentia
bleWithinAt 𝕜 c s x) (u : forall i, M i) : DifferentiableWithinAt 𝕜 (fun y => (c
 y) u) s x
参数：hc : DifferentiableWithinAt 𝕜 c s x；u : forall i, M i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivWithinAt.continuousMultilinear_apply_const`：HasFDerivWithinAt.c
ontinuousMultilinear_apply_const (hc : HasFDerivWithinAt c c' s x) (u : forall i
, M i) : HasFDerivWithinAt (fun y => (c y…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.continuousMultilinear_apply_const
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ∀ i, M i) :
    DifferentiableWithinAt 𝕜 (fun y ↦ (c y) u) s x :=
  have := Fintype.ofFinite ι
  (hc.hasFDerivWithinAt.continuousMultilinear_apply_const u).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableAt.continuousMultilinear_apply_const** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：DifferentiableAt.continuousMultilinear_apply_const (hc : DifferentiableAt 
𝕜 c x) (u : forall i, M i) : DifferentiableAt 𝕜 (fun y => (c y) u) x
参数：hc : DifferentiableAt 𝕜 c x；u : forall i, M i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivAt.continuousMultilinear_apply_const`：HasFDerivAt.continuousMul
tilinear_apply_const (hc : HasFDerivAt c c' x) (u : forall i, M i) : HasFDerivAt
 (fun y => (c y) u) (c'.flipMultili…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.continuousMultilinear_apply_const (hc : DifferentiableAt 𝕜 c x)
    (u : ∀ i, M i) :
    DifferentiableAt 𝕜 (fun y ↦ (c y) u) x :=
  have := Fintype.ofFinite ι
  (hc.hasFDerivAt.continuousMultilinear_apply_const u).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.continuousMultilinear_apply_const** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：DifferentiableOn.continuousMultilinear_apply_const (hc : DifferentiableOn 
𝕜 c s) (u : forall i, M i) : DifferentiableOn 𝕜 (fun y => (c y) u) s
参数：hc : DifferentiableOn 𝕜 c s；u : forall i, M i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableWithinAt.continuousMultilinear_apply_const`：Differentiable
WithinAt.continuousMultilinear_apply_const (hc : DifferentiableWithinAt 𝕜 c s x)
 (u : forall i, M i) : DifferentiableWithinAt …
-/
theorem DifferentiableOn.continuousMultilinear_apply_const (hc : DifferentiableOn 𝕜 c s)
    (u : ∀ i, M i) : DifferentiableOn 𝕜 (fun y ↦ (c y) u) s :=
  fun x hx ↦ (hc x hx).continuousMultilinear_apply_const u

@[fun_prop]
/-
**Differentiable.continuousMultilinear_apply_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.continuousMultilinear_apply_const (hc : Differentiable 𝕜 c)
 (u : forall i, M i) : Differentiable 𝕜 fun y => (c y) u
参数：hc : Differentiable 𝕜 c；u : forall i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableAt.continuousMultilinear_apply_const`：DifferentiableAt.con
tinuousMultilinear_apply_const (hc : DifferentiableAt 𝕜 c x) (u : forall i, M i)
 : DifferentiableAt 𝕜 (fun y => (c y) u)…
-/
theorem Differentiable.continuousMultilinear_apply_const (hc : Differentiable 𝕜 c) (u : ∀ i, M i) :
    Differentiable 𝕜 fun y ↦ (c y) u := fun x ↦ (hc x).continuousMultilinear_apply_const u

/-- Application of a `ContinuousMultilinearMap` to a constant commutes with `fderivWithin`. -/
/-
**fderivWithin_continuousMultilinear_apply_const_apply** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：fderivWithin_continuousMultilinear_apply_const_apply (hxs : UniqueDiffWith
inAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (u : forall i, M i) (m : E) : 
(fderivWithin 𝕜 (fun y => (c y) u) s x) m = (fderivWithin 𝕜 c s x) m u
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；u : forall
 i, M i；m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `fderivWithin_continuousMultilinear_apply_const`：fderivWithin_continuousM
ultilinear_apply_const (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWith
inAt 𝕜 c s x) (u : forall i, M i) : …
· 使用定理 `ContinuousLinearMap.flipMultilinear_apply_apply`：∀ {𝕜 : Type u} {ι : Typ
e v} {E : ι → Type wE} {G : Type wG} {G' : Type wG'} [inst : NontriviallyNormedF
ield 𝕜]   [inst_1 : (i : ι) → Seminor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Application of a `ContinuousMultilinearMap` to a constant commutes with `fderivW
ithin`.
-/
theorem fderivWithin_continuousMultilinear_apply_const_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ∀ i, M i) (m : E) :
    (fderivWithin 𝕜 (fun y ↦ (c y) u) s x) m = (fderivWithin 𝕜 c s x) m u := by
  have := Fintype.ofFinite ι
  simp [fderivWithin_continuousMultilinear_apply_const hxs hc]

/-- Application of a `ContinuousMultilinearMap` to a constant commutes with `fderiv`. -/
/-
**fderiv_continuousMultilinear_apply_const_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_continuousMultilinear_apply_const_apply (hc : DifferentiableAt 𝕜 c 
x) (u : forall i, M i) (m : E) : (fderiv 𝕜 (fun y => (c y) u) x) m = (fderiv 𝕜 c
 x) m u
参数：hc : DifferentiableAt 𝕜 c x；u : forall i, M i；m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `fderiv_continuousMultilinear_apply_const`：fderiv_continuousMultilinear_a
pply_const (hc : DifferentiableAt 𝕜 c x) (u : forall i, M i) : (fderiv 𝕜 (fun y 
=> (c y) u) x) = (fderiv 𝕜 c x…
· 使用定理 `ContinuousLinearMap.flipMultilinear_apply_apply`：∀ {𝕜 : Type u} {ι : Typ
e v} {E : ι → Type wE} {G : Type wG} {G' : Type wG'} [inst : NontriviallyNormedF
ield 𝕜]   [inst_1 : (i : ι) → Seminor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Application of a `ContinuousMultilinearMap` to a constant commutes with `fderiv`
.
-/
theorem fderiv_continuousMultilinear_apply_const_apply (hc : DifferentiableAt 𝕜 c x)
    (u : ∀ i, M i) (m : E) :
    (fderiv 𝕜 (fun y ↦ (c y) u) x) m = (fderiv 𝕜 c x) m u := by
  have := Fintype.ofFinite ι
  simp [fderiv_continuousMultilinear_apply_const hc]

end finite

end ContinuousMultilinearApplyConst

section ContinuousAlternatingMapApplyConst

/-!
### Derivative of the application of continuous alternating maps to a constant

Given a differentiable family of continuous alternating maps `c : E → F [⋀^ι]→L[𝕜] G`
and a tuple of vectors `u : ι → F`,
the derivative of `c x u` as a function of `x` is given by `fun m ↦ c' m u`,
where `c'` is the derivative of `c` at `x`.
-/

variable {ι : Type*} {c : E → F [⋀^ι]→L[𝕜] G} {c' : E →L[𝕜] (F [⋀^ι]→L[𝕜] G)}

section fintype

variable [Fintype ι]

@[fun_prop]
/-
**HasStrictFDerivAt.continuousAlternatingMap_apply_const** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：HasStrictFDerivAt.continuousAlternatingMap_apply_const (hc : HasStrictFDer
ivAt c c' x) (u : ι -> F) : HasStrictFDerivAt (c · u) (c'.flipAlternating u) x
参数：hc : HasStrictFDerivAt c c' x；u : ι -> F。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
theorem HasStrictFDerivAt.continuousAlternatingMap_apply_const (hc : HasStrictFDerivAt c c' x)
    (u : ι → F) : HasStrictFDerivAt (c · u) (c'.flipAlternating u) x :=
  (ContinuousAlternatingMap.apply 𝕜 F G u).hasStrictFDerivAt.comp x hc

@[fun_prop]
/-
**HasFDerivWithinAt.continuousAlternatingMap_apply_const** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：HasFDerivWithinAt.continuousAlternatingMap_apply_const (hc : HasFDerivWith
inAt c c' s x) (u : ι -> F) : HasFDerivWithinAt (c · u) (c'.flipAlternating u) s
 x
参数：hc : HasFDerivWithinAt c c' s x；u : ι -> F。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem HasFDerivWithinAt.continuousAlternatingMap_apply_const (hc : HasFDerivWithinAt c c' s x)
    (u : ι → F) :
    HasFDerivWithinAt (c · u) (c'.flipAlternating u) s x :=
  (ContinuousAlternatingMap.apply 𝕜 F G u).hasFDerivAt.comp_hasFDerivWithinAt x hc

@[fun_prop]
/-
**HasFDerivAt.continuousAlternatingMap_apply_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.continuousAlternatingMap_apply_const (hc : HasFDerivAt c c' x)
 (u : ι -> F) : HasFDerivAt (fun y => (c y) u) (c'.flipAlternating u) x
参数：hc : HasFDerivAt c c' x；u : ι -> F。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem HasFDerivAt.continuousAlternatingMap_apply_const (hc : HasFDerivAt c c' x) (u : ι → F) :
    HasFDerivAt (fun y ↦ (c y) u) (c'.flipAlternating u) x :=
  (ContinuousAlternatingMap.apply 𝕜 F G u).hasFDerivAt.comp x hc
/-
**fderivWithin_continuousAlternatingMap_apply_const** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：fderivWithin_continuousAlternatingMap_apply_const (hxs : UniqueDiffWithinA
t 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (u : ι -> F) : fderivWithin 𝕜 (fu
n y => (c y) u) s x = ((fderivWithin 𝕜 c s x).flipAlternating u)
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；u : ι -> F
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.continuousAlternatingMap_apply_const`：HasFDerivWithinA
t.continuousAlternatingMap_apply_const (hc : HasFDerivWithinAt c c' s x) (u : ι 
-> F) : HasFDerivWithinAt (c · u) (c'.flipAl…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_continuousAlternatingMap_apply_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ι → F) :
    fderivWithin 𝕜 (fun y ↦ (c y) u) s x = ((fderivWithin 𝕜 c s x).flipAlternating u) :=
  (hc.hasFDerivWithinAt.continuousAlternatingMap_apply_const u).fderivWithin hxs
/-
**fderiv_continuousAlternatingMap_apply_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_continuousAlternatingMap_apply_const (hc : DifferentiableAt 𝕜 c x) 
(u : ι -> F) : (fderiv 𝕜 (fun y => (c y) u) x) = (fderiv 𝕜 c x).flipAlternating 
u
参数：hc : DifferentiableAt 𝕜 c x；u : ι -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.continuousAlternatingMap_apply_const`：HasFDerivAt.continuous
AlternatingMap_apply_const (hc : HasFDerivAt c c' x) (u : ι -> F) : HasFDerivAt 
(fun y => (c y) u) (c'.flipAlternating…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_continuousAlternatingMap_apply_const (hc : DifferentiableAt 𝕜 c x) (u : ι → F) :
    (fderiv 𝕜 (fun y ↦ (c y) u) x) = (fderiv 𝕜 c x).flipAlternating u :=
  (hc.hasFDerivAt.continuousAlternatingMap_apply_const u).fderiv

end fintype

section finite

variable [Finite ι]

@[fun_prop]
/-
**DifferentiableWithinAt.continuousAlternatingMap_apply_const** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.continuousAlternatingMap_apply_const (hc : Differen
tiableWithinAt 𝕜 c s x) (u : ι -> F) : DifferentiableWithinAt 𝕜 (fun y => (c y) 
u) s x
参数：hc : DifferentiableWithinAt 𝕜 c s x；u : ι -> F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivWithinAt.continuousAlternatingMap_apply_const`：HasFDerivWithinA
t.continuousAlternatingMap_apply_const (hc : HasFDerivWithinAt c c' s x) (u : ι 
-> F) : HasFDerivWithinAt (c · u) (c'.flipAl…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.continuousAlternatingMap_apply_const
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ι → F) :
    DifferentiableWithinAt 𝕜 (fun y ↦ (c y) u) s x :=
  have := Fintype.ofFinite ι
  (hc.hasFDerivWithinAt.continuousAlternatingMap_apply_const u).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableAt.continuousAlternatingMap_apply_const** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：DifferentiableAt.continuousAlternatingMap_apply_const (hc : Differentiable
At 𝕜 c x) (u : ι -> F) : DifferentiableAt 𝕜 (fun y => (c y) u) x
参数：hc : DifferentiableAt 𝕜 c x；u : ι -> F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `HasFDerivAt.continuousAlternatingMap_apply_const`：HasFDerivAt.continuous
AlternatingMap_apply_const (hc : HasFDerivAt c c' x) (u : ι -> F) : HasFDerivAt 
(fun y => (c y) u) (c'.flipAlternating…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.continuousAlternatingMap_apply_const (hc : DifferentiableAt 𝕜 c x)
    (u : ι → F) :
    DifferentiableAt 𝕜 (fun y ↦ (c y) u) x :=
  have := Fintype.ofFinite ι
  (hc.hasFDerivAt.continuousAlternatingMap_apply_const u).differentiableAt

/-- Application of a `ContinuousAlternatingMap` to a constant commutes with `fderivWithin`. -/
/-
**fderivWithin_continuousAlternatingMap_apply_const_apply** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：fderivWithin_continuousAlternatingMap_apply_const_apply (hxs : UniqueDiffW
ithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (u : ι -> F) (m : E) : (fde
rivWithin 𝕜 (fun y => (c y) u) s x) m = (fderivWithin 𝕜 c s x) m u
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hc : DifferentiableWithinAt 𝕜 c s x；u : ι -> F
；m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `fderivWithin_continuousAlternatingMap_apply_const`：fderivWithin_continuo
usAlternatingMap_apply_const (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : Differentiab
leWithinAt 𝕜 c s x) (u : ι -> F) : fder…
· 使用定理 `ContinuousLinearMap.flipAlternating_apply_apply`：∀ {𝕜 : Type u} {E : Typ
e wE} {F : Type wF} {G : Type wG} {ι : Type v} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : SeminormedAddCommGroup …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Application of a `ContinuousAlternatingMap` to a constant commutes with `fderivW
ithin`.
-/
theorem fderivWithin_continuousAlternatingMap_apply_const_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (u : ι → F) (m : E) :
    (fderivWithin 𝕜 (fun y ↦ (c y) u) s x) m = (fderivWithin 𝕜 c s x) m u := by
  have := Fintype.ofFinite ι
  simp [fderivWithin_continuousAlternatingMap_apply_const hxs hc]

/-- Application of a `ContinuousAlternatingMap` to a constant commutes with `fderiv`. -/
/-
**fderiv_continuousAlternatingMap_apply_const_apply** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：fderiv_continuousAlternatingMap_apply_const_apply (hc : DifferentiableAt 𝕜
 c x) (u : ι -> F) (m : E) : (fderiv 𝕜 (fun y => (c y) u) x) m = (fderiv 𝕜 c x) 
m u
参数：hc : DifferentiableAt 𝕜 c x；u : ι -> F；m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `fderiv_continuousAlternatingMap_apply_const`：fderiv_continuousAlternatin
gMap_apply_const (hc : DifferentiableAt 𝕜 c x) (u : ι -> F) : (fderiv 𝕜 (fun y =
> (c y) u) x) = (fderiv 𝕜 c x).fl…
· 使用定理 `ContinuousLinearMap.flipAlternating_apply_apply`：∀ {𝕜 : Type u} {E : Typ
e wE} {F : Type wF} {G : Type wG} {ι : Type v} [inst : NontriviallyNormedField 𝕜
]   [inst_1 : SeminormedAddCommGroup …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Application of a `ContinuousAlternatingMap` to a constant commutes with `fderiv`
.
-/
theorem fderiv_continuousAlternatingMap_apply_const_apply (hc : DifferentiableAt 𝕜 c x)
    (u : ι → F) (m : E) :
    (fderiv 𝕜 (fun y ↦ (c y) u) x) m = (fderiv 𝕜 c x) m u := by
  have := Fintype.ofFinite ι
  simp [fderiv_continuousAlternatingMap_apply_const hc]

@[fun_prop]
/-
**DifferentiableOn.continuousAlternatingMap_apply_const** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：DifferentiableOn.continuousAlternatingMap_apply_const (hc : Differentiable
On 𝕜 c s) (u : ι -> F) : DifferentiableOn 𝕜 (fun y => (c y) u) s
参数：hc : DifferentiableOn 𝕜 c s；u : ι -> F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableWithinAt.continuousAlternatingMap_apply_const`：Differentia
bleWithinAt.continuousAlternatingMap_apply_const (hc : DifferentiableWithinAt 𝕜 
c s x) (u : ι -> F) : DifferentiableWithinAt 𝕜 (f…
-/
theorem DifferentiableOn.continuousAlternatingMap_apply_const (hc : DifferentiableOn 𝕜 c s)
    (u : ι → F) : DifferentiableOn 𝕜 (fun y ↦ (c y) u) s :=
  fun x hx ↦ (hc x hx).continuousAlternatingMap_apply_const u

@[fun_prop]
/-
**Differentiable.continuousAlternatingMap_apply_const** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Differentiable.continuousAlternatingMap_apply_const (hc : Differentiable 𝕜
 c) (u : ι -> F) : Differentiable 𝕜 fun y => (c y) u
参数：hc : Differentiable 𝕜 c；u : ι -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DifferentiableAt.continuousAlternatingMap_apply_const`：DifferentiableAt.
continuousAlternatingMap_apply_const (hc : DifferentiableAt 𝕜 c x) (u : ι -> F) 
: DifferentiableAt 𝕜 (fun y => (c y) u) x
-/
theorem Differentiable.continuousAlternatingMap_apply_const (hc : Differentiable 𝕜 c) (u : ι → F) :
    Differentiable 𝕜 fun y ↦ (c y) u := fun x ↦ (hc x).continuousAlternatingMap_apply_const u

end finite

end ContinuousAlternatingMapApplyConst

end

