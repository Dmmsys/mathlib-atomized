/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The derivative of the scalar restriction of a linear map

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
the scalar restriction of a linear map.
-/

public section


open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is differentiable over `ℂ`, then it is differentiable over `ℝ`. In this paragraph,
we give variants of this statement, in the general situation where `ℂ` and `ℝ` are replaced
respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra over `𝕜`.
-/


variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
variable [IsScalarTower 𝕜 𝕜' E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
variable [IsScalarTower 𝕜 𝕜' F]
variable {f : E → F} {f' : E →L[𝕜'] F} {s : Set E} {x : E}

/-
**HasFDerivAtFilter.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.restrictScalars {L} (h : HasFDerivAtFilter f f' L) : Has
FDerivAtFilter f (f'.restrictScalars 𝕜) L
参数：h : HasFDerivAtFilter f f' L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.of_isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Typ…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `HasFDerivAtFilter.isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Typ…
-/
theorem HasFDerivAtFilter.restrictScalars {L} (h : HasFDerivAtFilter f f' L) :
    HasFDerivAtFilter f (f'.restrictScalars 𝕜) L :=
  .of_isLittleO h.isLittleO

@[fun_prop]
/-
**HasStrictFDerivAt.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.restrictScalars (h : HasStrictFDerivAt f f' x) : HasStri
ctFDerivAt f (f'.restrictScalars 𝕜) x
参数：h : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.restrictScalars`：HasFDerivAtFilter.restrictScalars {L}
 (h : HasFDerivAtFilter f f' L) : HasFDerivAtFilter f (f'.restrictScalars 𝕜) L
-/
theorem HasStrictFDerivAt.restrictScalars (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt f (f'.restrictScalars 𝕜) x :=
  HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]
/-
**HasFDerivAt.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.restrictScalars (h : HasFDerivAt f f' x) : HasFDerivAt f (f'.r
estrictScalars 𝕜) x
参数：h : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.restrictScalars`：HasFDerivAtFilter.restrictScalars {L}
 (h : HasFDerivAtFilter f f' L) : HasFDerivAtFilter f (f'.restrictScalars 𝕜) L
-/
theorem HasFDerivAt.restrictScalars (h : HasFDerivAt f f' x) :
    HasFDerivAt f (f'.restrictScalars 𝕜) x :=
  HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]
/-
**HasFDerivWithinAt.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.restrictScalars (h : HasFDerivWithinAt f f' s x) : HasFD
erivWithinAt f (f'.restrictScalars 𝕜) s x
参数：h : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.restrictScalars`：HasFDerivAtFilter.restrictScalars {L}
 (h : HasFDerivAtFilter f f' L) : HasFDerivAtFilter f (f'.restrictScalars 𝕜) L
-/
theorem HasFDerivWithinAt.restrictScalars (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt f (f'.restrictScalars 𝕜) s x :=
  HasFDerivAtFilter.restrictScalars 𝕜 h

@[fun_prop]
/-
**DifferentiableAt.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.restrictScalars (h : DifferentiableAt 𝕜' f x) : Different
iableAt 𝕜 f x
参数：h : DifferentiableAt 𝕜' f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `HasFDerivAt.restrictScalars`：HasFDerivAt.restrictScalars (h : HasFDerivA
t f f' x) : HasFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.restrictScalars (h : DifferentiableAt 𝕜' f x) : DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt.restrictScalars 𝕜).differentiableAt

@[fun_prop]
/-
**DifferentiableWithinAt.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.restrictScalars (h : DifferentiableWithinAt 𝕜' f s 
x) : DifferentiableWithinAt 𝕜 f s x
参数：h : DifferentiableWithinAt 𝕜' f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `HasFDerivWithinAt.restrictScalars`：HasFDerivWithinAt.restrictScalars (h 
: HasFDerivWithinAt f f' s x) : HasFDerivWithinAt f (f'.restrictScalars 𝕜) s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.restrictScalars (h : DifferentiableWithinAt 𝕜' f s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  (h.hasFDerivWithinAt.restrictScalars 𝕜).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableOn.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.restrictScalars (h : DifferentiableOn 𝕜' f s) : Different
iableOn 𝕜 f s
参数：h : DifferentiableOn 𝕜' f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.restrictScalars`：DifferentiableWithinAt.restrictS
calars (h : DifferentiableWithinAt 𝕜' f s x) : DifferentiableWithinAt 𝕜 f s x
-/
theorem DifferentiableOn.restrictScalars (h : DifferentiableOn 𝕜' f s) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x hx).restrictScalars 𝕜

@[fun_prop]
/-
**Differentiable.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.restrictScalars (h : Differentiable 𝕜' f) : Differentiable 
𝕜 f
参数：h : Differentiable 𝕜' f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.restrictScalars`：DifferentiableAt.restrictScalars (h : 
DifferentiableAt 𝕜' f x) : DifferentiableAt 𝕜 f x
-/
theorem Differentiable.restrictScalars (h : Differentiable 𝕜' f) : Differentiable 𝕜 f := fun x =>
  (h x).restrictScalars 𝕜

@[fun_prop]
/-
**HasFDerivWithinAt.of_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.of_restrictScalars {g' : E ->L[𝕜] F} (h : HasFDerivWithi
nAt f g' s x) (H : f'.restrictScalars 𝕜 = g') : HasFDerivWithinAt f f' s x
参数：h : HasFDerivWithinAt f g' s x；H : f'.restrictScalars 𝕜 = g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `HasFDerivWithinAt.of_isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Typ…
· 使用定理 `HasFDerivWithinAt.isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Typ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem HasFDerivWithinAt.of_restrictScalars {g' : E →L[𝕜] F} (h : HasFDerivWithinAt f g' s x)
    (H : f'.restrictScalars 𝕜 = g') : HasFDerivWithinAt f f' s x := by
  rw [← H] at h
  exact .of_isLittleO h.isLittleO

@[fun_prop]
/-
**hasFDerivAt_of_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_of_restrictScalars {g' : E ->L[𝕜] F} (h : HasFDerivAt f g' x) 
(H : f'.restrictScalars 𝕜 = g') : HasFDerivAt f f' x
参数：h : HasFDerivAt f g' x；H : f'.restrictScalars 𝕜 = g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `HasFDerivAt.of_isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {F : Typ…
· 使用定理 `HasFDerivAt.isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Typ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem hasFDerivAt_of_restrictScalars {g' : E →L[𝕜] F} (h : HasFDerivAt f g' x)
    (H : f'.restrictScalars 𝕜 = g') : HasFDerivAt f f' x := by
  rw [← H] at h
  exact .of_isLittleO h.isLittleO
/-
**DifferentiableAt.fderiv_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.fderiv_restrictScalars (h : DifferentiableAt 𝕜' f x) : fd
eriv 𝕜 f x = (fderiv 𝕜' f x).restrictScalars 𝕜
参数：h : DifferentiableAt 𝕜' f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
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
· 使用定理 `HasFDerivAt.restrictScalars`：HasFDerivAt.restrictScalars (h : HasFDerivA
t f f' x) : HasFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.fderiv_restrictScalars (h : DifferentiableAt 𝕜' f x) :
    fderiv 𝕜 f x = (fderiv 𝕜' f x).restrictScalars 𝕜 :=
  (h.hasFDerivAt.restrictScalars 𝕜).fderiv
/-
**DifferentiableWithinAt.restrictScalars_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：DifferentiableWithinAt.restrictScalars_fderivWithin (hf : DifferentiableWi
thinAt 𝕜' f s x) (hs : UniqueDiffWithinAt 𝕜 s x) : (fderivWithin 𝕜' f s x).restr
ictScalars 𝕜 = fderivWithin 𝕜 f s x
参数：hf : DifferentiableWithinAt 𝕜' f s x；hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
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
· 使用定理 `HasFDerivWithinAt.restrictScalars`：HasFDerivWithinAt.restrictScalars (h 
: HasFDerivWithinAt f f' s x) : HasFDerivWithinAt f (f'.restrictScalars 𝕜) s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.restrictScalars_fderivWithin (hf : DifferentiableWithinAt 𝕜' f s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    (fderivWithin 𝕜' f s x).restrictScalars 𝕜 = fderivWithin 𝕜 f s x :=
  ((hf.hasFDerivWithinAt.restrictScalars 𝕜).fderivWithin hs).symm
/-
**differentiableWithinAt_iff_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_iff_restrictScalars (hf : DifferentiableWithinAt 𝕜 
f s x) (hs : UniqueDiffWithinAt 𝕜 s x) : DifferentiableWithinAt 𝕜' f s x ↔ exist
s g' : E ->L[𝕜'] F, g'.restrictScalars 𝕜 = fderivWithin 𝕜 f s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `UniqueDiffWithinAt.eq`：UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s
 x) (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt f f₁' s x) : f' = 
f₁'
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
· 使用定理 `HasFDerivWithinAt.restrictScalars`：HasFDerivWithinAt.restrictScalars (h 
: HasFDerivWithinAt f f' s x) : HasFDerivWithinAt f (f'.restrictScalars 𝕜) s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `HasFDerivWithinAt.of_restrictScalars`：HasFDerivWithinAt.of_restrictScala
rs {g' : E ->L[𝕜] F} (h : HasFDerivWithinAt f g' s x) (H : f'.restrictScalars 𝕜 
= g') : HasFDerivWithinAt …
-/
theorem differentiableWithinAt_iff_restrictScalars (hf : DifferentiableWithinAt 𝕜 f s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) : DifferentiableWithinAt 𝕜' f s x ↔
      ∃ g' : E →L[𝕜'] F, g'.restrictScalars 𝕜 = fderivWithin 𝕜 f s x := by
  constructor
  · rintro ⟨g', hg'⟩
    exact ⟨g', hs.eq (hg'.restrictScalars 𝕜) hf.hasFDerivWithinAt⟩
  · rintro ⟨f', hf'⟩
    exact ⟨f', hf.hasFDerivWithinAt.of_restrictScalars 𝕜 hf'⟩
/-
**differentiableAt_iff_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_iff_restrictScalars (hf : DifferentiableAt 𝕜 f x) : Diffe
rentiableAt 𝕜' f x ↔ exists g' : E ->L[𝕜'] F, g'.restrictScalars 𝕜 = fderiv 𝕜 f 
x
参数：hf : DifferentiableAt 𝕜 f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `differentiableWithinAt_iff_restrictScalars`：differentiableWithinAt_iff_r
estrictScalars (hf : DifferentiableWithinAt 𝕜 f s x) (hs : UniqueDiffWithinAt 𝕜 
s x) : DifferentiableWithinAt 𝕜'…
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem differentiableAt_iff_restrictScalars (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜' f x ↔ ∃ g' : E →L[𝕜'] F, g'.restrictScalars 𝕜 = fderiv 𝕜 f x := by
  rw [← differentiableWithinAt_univ, ← fderivWithin_univ]
  exact
    differentiableWithinAt_iff_restrictScalars 𝕜 hf.differentiableWithinAt uniqueDiffWithinAt_univ

end RestrictScalars

