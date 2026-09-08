/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The derivative of bounded linear maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
bounded linear maps.
-/

public section

open Asymptotics

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable (f : E →L[𝕜] F)
variable {x : E}
variable {s : Set E}
variable {L : Filter (E × E)}

/-!
### Bundled continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `ContinuousLinearMap`, and denoted `E →L[𝕜] F`, works for topological vector spaces),
and the unbundled version (with a predicate `IsBoundedLinearMap`, requires normed spaces).
This section deals with the first form, see below for the unbundled version
-/

/-
**ContinuousLinearMap.hasFDerivAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] (f : E →L[𝕜] F) {L : Filter (E × E)},   HasFDerivAtFilter 
(⇑f) f L
参数：f : E →L[𝕜] F；E × E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleOTVS.congr_left`：∀ {α : Type u_1} {𝕜 : Type u_3} {E 
: Type u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCom
mGroup E] [inst_2 : Topol…
· 使用定理 `Asymptotics.IsLittleOTVS.zero`：∀ {α : Type u_1} {𝕜 : Type u_3} {E : Type
 u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : AddCommGroup
 E] [inst_2 : Topol…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.map_sub`：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type
 u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [inst_3 
: AddCommGroup M]…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Bundled continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `ContinuousLinearMap`, and denoted `E →L[𝕜] F`, works for topological vec
tor spaces),
and the unbundled version (with a predicate `IsBoundedLinearMap`, requires norme
d spaces).
This section deals with the first form, see below for the unbundled version
-/
protected theorem hasFDerivAtFilter : HasFDerivAtFilter f f L :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun x => by
    simp only [f.map_sub, sub_self, Pi.zero_apply]

@[fun_prop]
/-
**ContinuousLinearMap.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] (f : E →L[𝕜] F) {x : E}, HasStrictFDerivAt (⇑f) f x
参数：f : E →L[𝕜] F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasFDerivAtFilter`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem hasStrictFDerivAt : HasStrictFDerivAt f f x :=
  f.hasFDerivAtFilter

@[fun_prop]
/-
**ContinuousLinearMap.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] (f : E →L[𝕜] F) {x : E} {s : Set E},   HasFDerivWithinAt (
⇑f) f s x
参数：f : E →L[𝕜] F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasFDerivAtFilter`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem hasFDerivWithinAt : HasFDerivWithinAt f f s x :=
  f.hasFDerivAtFilter

@[fun_prop]
/-
**ContinuousLinearMap.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] (f : E →L[𝕜] F) {x : E}, HasFDerivAt (⇑f) f x
参数：f : E →L[𝕜] F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasFDerivAtFilter`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem hasFDerivAt : HasFDerivAt f f x :=
  f.hasFDerivAtFilter

@[simp, fun_prop]
/-
**ContinuousLinearMap.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] (f : E →L[𝕜] F) {x : E}, DifferentiableAt 𝕜 (⇑f) x
参数：f : E →L[𝕜] F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
protected theorem differentiableAt : DifferentiableAt 𝕜 f x :=
  f.hasFDerivAt.differentiableAt

@[fun_prop]
/-
**ContinuousLinearMap.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] (f : E →L[𝕜] F) {x : E} {s : Set E},   DifferentiableWithi
nAt 𝕜 (⇑f) s x
参数：f : E →L[𝕜] F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `ContinuousLinearMap.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Mo
dule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 f s x :=
  f.differentiableAt.differentiableWithinAt

@[simp, fun_prop]
/-
**ContinuousLinearMap.differentiable** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] (f : E →L[𝕜] F), Differentiable 𝕜 ⇑f
参数：f : E →L[𝕜] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Mo
dule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem differentiable : Differentiable 𝕜 f := fun _ =>
  f.differentiableAt

@[fun_prop]
/-
**ContinuousLinearMap.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] (f : E →L[𝕜] F) {s : Set E}, DifferentiableOn 𝕜 (⇑f) s
参数：f : E →L[𝕜] F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
-/
protected theorem differentiableOn : DifferentiableOn 𝕜 f s :=
  f.differentiable.differentiableOn

variable [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]

@[simp]
/-
**ContinuousLinearMap.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] (f : E →L[𝕜] F) {x : E} [ContinuousAdd E]   [ContinuousSMu
l 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F], fderiv 𝕜 (⇑f) x = f
参数：f : E →L[𝕜] F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
protected theorem fderiv : fderiv 𝕜 f x = f :=
  f.hasFDerivAt.fderiv
/-
**ContinuousLinearMap.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
{F : Type u_3} [inst_4 : AddCommGroup F]   [inst_5 : _root_.Module 𝕜 F] [inst_6 
: TopologicalSpace F] (f : E →L[𝕜] F) {x : E} {s : Set E} [ContinuousAdd E]   [C
ontinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F],   UniqueD
iffWithinAt 𝕜 s x → fderivWithin 𝕜 (⇑f) s x = f
参数：f : E →L[𝕜] F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `ContinuousLinearMap.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Mo
dule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `ContinuousLinearMap.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] 
[inst_3 : Topolo…
-/
protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 f s x = f := by
  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
  exact f.fderiv

end ContinuousLinearMap

/-! ### Unbundled continuous linear maps -/

namespace IsBoundedLinearMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F}
variable {x : E}
variable {s : Set E}
variable {L : Filter (E × E)}

/-
**IsBoundedLinearMap.hasFDerivAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinea
rMap`。
形式化陈述：hasFDerivAtFilter (h : IsBoundedLinearMap 𝕜 f) : HasFDerivAtFilter f h.toC
ontinuousLinearMap L
参数：h : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasFDerivAtFilter`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
theorem hasFDerivAtFilter (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAtFilter f h.toContinuousLinearMap L :=
  h.toContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]
/-
**IsBoundedLinearMap.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinea
rMap`。
形式化陈述：hasFDerivWithinAt (h : IsBoundedLinearMap 𝕜 f) : HasFDerivWithinAt f h.toC
ontinuousLinearMap s x
参数：h : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.hasFDerivAtFilter`：hasFDerivAtFilter (h : IsBoundedLi
nearMap 𝕜 f) : HasFDerivAtFilter f h.toContinuousLinearMap L
-/
theorem hasFDerivWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivWithinAt f h.toContinuousLinearMap s x :=
  h.hasFDerivAtFilter

@[fun_prop]
/-
**IsBoundedLinearMap.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：hasFDerivAt (h : IsBoundedLinearMap 𝕜 f) : HasFDerivAt f h.toContinuousLin
earMap x
参数：h : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.hasFDerivAtFilter`：hasFDerivAtFilter (h : IsBoundedLi
nearMap 𝕜 f) : HasFDerivAtFilter f h.toContinuousLinearMap L
-/
theorem hasFDerivAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAt f h.toContinuousLinearMap x :=
  h.hasFDerivAtFilter

@[fun_prop]
/-
**IsBoundedLinearMap.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinear
Map`。
形式化陈述：differentiableAt (h : IsBoundedLinearMap 𝕜 f) : DifferentiableAt 𝕜 f x
参数：h : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsBoundedLinearMap.hasFDerivAt`：hasFDerivAt (h : IsBoundedLinearMap 𝕜 f)
 : HasFDerivAt f h.toContinuousLinearMap x
-/
theorem differentiableAt (h : IsBoundedLinearMap 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt

@[fun_prop]
/-
**IsBoundedLinearMap.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `IsBounded
LinearMap`。
形式化陈述：differentiableWithinAt (h : IsBoundedLinearMap 𝕜 f) : DifferentiableWithin
At 𝕜 f s x
参数：h : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsBoundedLinearMap.differentiableAt`：differentiableAt (h : IsBoundedLine
arMap 𝕜 f) : DifferentiableAt 𝕜 f x
-/
theorem differentiableWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.differentiableAt.differentiableWithinAt
/-
**IsBoundedLinearMap.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {x : E} (h : IsBou
ndedLinearMap 𝕜 f), fderiv 𝕜 f x = IsBoundedLinearMap.toContinuousLinearMap f h
参数：h : IsBoundedLinearMap 𝕜 f。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedLinearMap.hasFDerivAt`：hasFDerivAt (h : IsBoundedLinearMap 𝕜 f)
 : HasFDerivAt f h.toContinuousLinearMap x
-/
protected theorem fderiv (h : IsBoundedLinearMap 𝕜 f) :
    fderiv 𝕜 f x = h.toContinuousLinearMap :=
  HasFDerivAt.fderiv h.hasFDerivAt
/-
**IsBoundedLinearMap.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`
。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {x : E} {s : Set E
} (h : IsBoundedLinearMap 𝕜 f),   UniqueDiffWithinAt 𝕜 s x → fderivWithin 𝕜 f s 
x = IsBoundedLinearMap.toContinuousLinearMap f h
参数：h : IsBoundedLinearMap 𝕜 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
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
· 使用定理 `IsBoundedLinearMap.differentiableAt`：differentiableAt (h : IsBoundedLine
arMap 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `IsBoundedLinearMap.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type u_…
-/
protected theorem fderivWithin (h : IsBoundedLinearMap 𝕜 f)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = h.toContinuousLinearMap := by
  rw [DifferentiableAt.fderivWithin h.differentiableAt hxs]
  exact h.fderiv

@[fun_prop]
/-
**IsBoundedLinearMap.differentiable** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMa
p`。
形式化陈述：differentiable (h : IsBoundedLinearMap 𝕜 f) : Differentiable 𝕜 f
参数：h : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.differentiableAt`：differentiableAt (h : IsBoundedLine
arMap 𝕜 f) : DifferentiableAt 𝕜 f x
-/
theorem differentiable (h : IsBoundedLinearMap 𝕜 f) : Differentiable 𝕜 f :=
  fun _ => h.differentiableAt

@[fun_prop]
/-
**IsBoundedLinearMap.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinear
Map`。
形式化陈述：differentiableOn (h : IsBoundedLinearMap 𝕜 f) : DifferentiableOn 𝕜 f s
参数：h : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `IsBoundedLinearMap.differentiable`：differentiable (h : IsBoundedLinearMa
p 𝕜 f) : Differentiable 𝕜 f
-/
theorem differentiableOn (h : IsBoundedLinearMap 𝕜 f) : DifferentiableOn 𝕜 f s :=
  h.differentiable.differentiableOn

end IsBoundedLinearMap

