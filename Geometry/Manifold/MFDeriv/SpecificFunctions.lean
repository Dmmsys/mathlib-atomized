/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.Notation

/-!
# Differentiability of specific functions

In this file, we establish differentiability results for
- continuous linear maps and continuous linear equivalences
- the identity
- constant functions
- products
- arithmetic operations (such as addition and scalar multiplication).

-/

public section

noncomputable section

open scoped Manifold
open Bundle Set Topology

section SpecificFunctions

/-! ### Differentiability of specific functions -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a charted space `M''` over the pair `(E'', H'')`.
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*}
  [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a charted space `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  -- F₁, F₂, F₃, F₄ are normed spaces
  {F₁ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]

namespace ContinuousLinearMap

variable (f : E →L[𝕜] E') {s : Set E} {x : E}

/-
**ContinuousLinearMap.hasMFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E →L[𝕜] E') {s : Set E
} {x : E}, HasMFDerivAt[s] (⇑f) x f
参数：f : E →L[𝕜] E'；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.hasMFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {E' : Type u…
· 使用定理 `ContinuousLinearMap.hasFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem hasMFDerivWithinAt : HasMFDerivAt[s] f x f :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt
/-
**ContinuousLinearMap.hasMFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E →L[𝕜] E') {x : E}, H
asMFDerivAt% (⇑f) x f
参数：f : E →L[𝕜] E'；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasMFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {E' : Type u…
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
protected theorem hasMFDerivAt : HasMFDerivAt% f x f :=
  f.hasFDerivAt.hasMFDerivAt
/-
**ContinuousLinearMap.mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E →L[𝕜] E') {s : Set E
} {x : E}, MDiffAt[s] ⇑f x
参数：f : E →L[𝕜] E'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mdifferentiableWithinAt`：∀ {𝕜 : Type u_1} [inst :
 NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [in
st_2 : NormedSpace 𝕜 E] {E' : Type u…
· 使用定理 `ContinuousLinearMap.differentiableWithinAt`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] [inst_3 : Topolo…
-/
protected theorem mdifferentiableWithinAt : MDiffAt[s] f x :=
  f.differentiableWithinAt.mdifferentiableWithinAt
/-
**ContinuousLinearMap.mdifferentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E →L[𝕜] E') {s : Set E
}, MDiff[s] ⇑f
参数：f : E →L[𝕜] E'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.mdifferentiableOn`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {E' : Type u…
· 使用定理 `ContinuousLinearMap.differentiableOn`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Mo
dule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem mdifferentiableOn : MDiff[s] f :=
  f.differentiableOn.mdifferentiableOn
/-
**ContinuousLinearMap.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E →L[𝕜] E') {x : E}, M
DiffAt ⇑f x
参数：f : E →L[𝕜] E'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.mdifferentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {E' : Type u…
· 使用定理 `ContinuousLinearMap.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Mo
dule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem mdifferentiableAt : MDiffAt f x :=
  f.differentiableAt.mdifferentiableAt
/-
**ContinuousLinearMap.mdifferentiable** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E →L[𝕜] E'), MDiff ⇑f
参数：f : E →L[𝕜] E'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.mdifferentiable`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {E' : Type u…
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
-/
protected theorem mdifferentiable : MDiff f :=
  f.differentiable.mdifferentiable
/-
**ContinuousLinearMap.mfderiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：mfderiv_eq : mfderiv% f x = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用定理 `ContinuousLinearMap.hasMFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {E' : Type u…
-/
theorem mfderiv_eq : mfderiv% f x = f :=
  f.hasMFDerivAt.mfderiv
/-
**ContinuousLinearMap.mfderivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：mfderivWithin_eq (hs : UniqueMDiffAt[s] x) : mfderiv[s] f x = f
参数：hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `ContinuousLinearMap.hasMFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {E' : Type u…
-/
theorem mfderivWithin_eq (hs : UniqueMDiffAt[s] x) : mfderiv[s] f x = f :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] E') {s : Set E} {x : E}

/-
**ContinuousLinearEquiv.hasMFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E ≃L[𝕜] E') {s : Set E
} {x : E}, HasMFDerivAt[s] (⇑f) x ↑f
参数：f : E ≃L[𝕜] E'；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.hasMFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {E' : Type u…
· 使用定理 `ContinuousLinearEquiv.hasFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem hasMFDerivWithinAt : HasMFDerivAt[s] f x (f : E →L[𝕜] E') :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt
/-
**ContinuousLinearEquiv.hasMFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E ≃L[𝕜] E') {x : E}, H
asMFDerivAt% (⇑f) x ↑f
参数：f : E ≃L[𝕜] E'；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.hasMFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {E' : Type u…
· 使用定理 `ContinuousLinearEquiv.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
-/
protected theorem hasMFDerivAt : HasMFDerivAt% f x (f : E →L[𝕜] E') :=
  f.hasFDerivAt.hasMFDerivAt
/-
**ContinuousLinearEquiv.mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E ≃L[𝕜] E') {s : Set E
} {x : E}, MDiffAt[s] ⇑f x
参数：f : E ≃L[𝕜] E'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.mdifferentiableWithinAt`：∀ {𝕜 : Type u_1} [inst :
 NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [in
st_2 : NormedSpace 𝕜 E] {E' : Type u…
· 使用定理 `ContinuousLinearEquiv.differentiableWithinAt`：∀ {𝕜 : Type u_1} [inst : N
ontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem mdifferentiableWithinAt : MDiffAt[s] f x :=
  f.differentiableWithinAt.mdifferentiableWithinAt
/-
**ContinuousLinearEquiv.mdifferentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E ≃L[𝕜] E') {s : Set E
}, MDiff[s] ⇑f
参数：f : E ≃L[𝕜] E'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.mdifferentiableOn`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {E' : Type u…
· 使用定理 `ContinuousLinearEquiv.differentiableOn`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem mdifferentiableOn : MDiff[s] f :=
  f.differentiableOn.mdifferentiableOn
/-
**ContinuousLinearEquiv.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E ≃L[𝕜] E') {x : E}, M
DiffAt ⇑f x
参数：f : E ≃L[𝕜] E'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.mdifferentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {E' : Type u…
· 使用定理 `ContinuousLinearEquiv.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem mdifferentiableAt : MDiffAt f x :=
  f.differentiableAt.mdifferentiableAt
/-
**ContinuousLinearEquiv.mdifferentiable** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' : Type u_5} [inst_3 : 
NormedAddCommGroup E'] [inst_4 : NormedSpace 𝕜 E']   (f : E ≃L[𝕜] E'), MDiff ⇑f
参数：f : E ≃L[𝕜] E'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.mdifferentiable`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {E' : Type u…
· 使用定理 `ContinuousLinearEquiv.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
protected theorem mdifferentiable : MDiff f :=
  f.differentiable.mdifferentiable
/-
**ContinuousLinearEquiv.mfderiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEq
uiv`。
形式化陈述：mfderiv_eq : mfderiv% f x = (f : E ->L[𝕜] E')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用定理 `ContinuousLinearEquiv.hasMFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {E' : Type u…
-/
theorem mfderiv_eq : mfderiv% f x = (f : E →L[𝕜] E') :=
  f.hasMFDerivAt.mfderiv
/-
**ContinuousLinearEquiv.mfderivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：mfderivWithin_eq (hs : UniqueMDiffAt[s] x) : mfderiv[s] f x = (f : E ->L[𝕜
] E')
参数：hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `ContinuousLinearEquiv.hasMFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] {E' : Type u…
-/
theorem mfderivWithin_eq (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] f x = (f : E →L[𝕜] E') :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearEquiv

variable {s : Set M} {x : M}

section id

/-! #### Identity -/

/-
**hasMFDerivAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivAt_id (x : M) : HasMFDerivAt% (@id M) x (ContinuousLinearMap.id 
𝕜 (TangentSpace% x))
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFDerivWithinAt.congr_of_eventuallyEq`：HasFDerivWithinAt.congr_of_even
tuallyEq (h : HasFDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : HasFDerivWithinAt f₁ f' …
· 使用定理 `hasFDerivWithinAt_id`：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDer
ivWithinAt id (.id 𝕜 E) s x
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x

--- 原说明 ---
#### Identity
-/
theorem hasMFDerivAt_id (x : M) :
    HasMFDerivAt% (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace% x)) := by
  refine ⟨continuousAt_id, ?_⟩
  have : ∀ᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = y := by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _) this
  simp only [mfld_simps]
/-
**hasMFDerivWithinAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_id (s : Set M) (x : M) : HasMFDerivAt[s] (@id M) x (Con
tinuousLinearMap.id 𝕜 (TangentSpace% x))
参数：s : Set M；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
· 使用定理 `hasMFDerivAt_id`：hasMFDerivAt_id (x : M) : HasMFDerivAt% (@id M) x (Cont
inuousLinearMap.id 𝕜 (TangentSpace% x))
-/
theorem hasMFDerivWithinAt_id (s : Set M) (x : M) :
    HasMFDerivAt[s] (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace% x)) :=
  (hasMFDerivAt_id x).hasMFDerivWithinAt
/-
**mdifferentiableAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_id : MDiffAt (@id M) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `hasMFDerivAt_id`：hasMFDerivAt_id (x : M) : HasMFDerivAt% (@id M) x (Cont
inuousLinearMap.id 𝕜 (TangentSpace% x))
-/
theorem mdifferentiableAt_id : MDiffAt (@id M) x :=
  (hasMFDerivAt_id x).mdifferentiableAt
/-
**mdifferentiableWithinAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_id : MDiffAt[s] (@id M) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `mdifferentiableAt_id`：mdifferentiableAt_id : MDiffAt (@id M) x
-/
theorem mdifferentiableWithinAt_id : MDiffAt[s] (@id M) x :=
  mdifferentiableAt_id.mdifferentiableWithinAt
/-
**mdifferentiable_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_id : MDiff (@id M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableAt_id`：mdifferentiableAt_id : MDiffAt (@id M) x
-/
theorem mdifferentiable_id : MDiff (@id M) := fun _ ↦ mdifferentiableAt_id
/-
**mdifferentiableOn_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_id : MDiff[s] (@id M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.mdifferentiableOn`：MDifferentiable.mdifferentiableOn (h 
: MDiff f) : MDiff[s] f
· 使用定理 `mdifferentiable_id`：mdifferentiable_id : MDiff (@id M)
-/
theorem mdifferentiableOn_id : MDiff[s] (@id M) :=
  mdifferentiable_id.mdifferentiableOn

@[simp, mfld_simps]
/-
**mfderiv_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% 
x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用定理 `hasMFDerivAt_id`：hasMFDerivAt_id (x : M) : HasMFDerivAt% (@id M) x (Cont
inuousLinearMap.id 𝕜 (TangentSpace% x))
-/
theorem mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x) :=
  (hasMFDerivAt_id x).mfderiv
/-
**mfderivWithin_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_id (hxs : UniqueMDiffAt[s] x) : mfderiv[s] (@id M) x = Conti
nuousLinearMap.id 𝕜 (TangentSpace% x)
参数：hxs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MDifferentiable.mfderivWithin`：MDifferentiable.mfderivWithin (h : MDiffA
t f x) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] f x = mfderiv% f x
· 使用定理 `mdifferentiableAt_id`：mdifferentiableAt_id : MDiffAt (@id M) x
· 使用定理 `mfderiv_id`：mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (
TangentSpace% x)
-/
theorem mfderivWithin_id (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_id hxs]
  exact mfderiv_id

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
/-
**tangentMap_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMap_id : tangentMap% (@id M) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_id`：mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (
TangentSpace% x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tangentMap_id : tangentMap% (@id M) = id := by ext1 ⟨x, v⟩; simp [tangentMap]
/-
**tangentMapWithin_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMapWithin_id {p : TangentBundle I M} (hs : UniqueMDiffAt[s] p.proj)
 : tangentMap[s] (id : M -> M) p = p
参数：hs : UniqueMDiffAt[s] p.proj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin_id`：mfderivWithin_id (hxs : UniqueMDiffAt[s] x) : mfderiv[
s] (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x)
-/
theorem tangentMapWithin_id {p : TangentBundle I M} (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (id : M → M) p = p := by
  simp only [tangentMapWithin, id]
  rw [mfderivWithin_id]
  · rcases p with ⟨⟩; rfl
  · exact hs

end id

section Const

/-! #### Constants -/


variable {c : M'}

set_option backward.isDefEq.respectTransparency false in
/-
**hasMFDerivAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivAt_const (c : M') (x : M) : HasMFDerivAt% (fun _ : M => c) x (0 
: TangentSpace% x ->L[𝕜] TangentSpace% c)
参数：c : M'；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem hasMFDerivAt_const (c : M') (x : M) :
    HasMFDerivAt% (fun _ : M ↦ c) x (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  ⟨by fun_prop, by simp [Function.comp_def, hasFDerivWithinAt_const]⟩
/-
**hasMFDerivWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_const (c : M') (s : Set M) (x : M) : HasMFDerivAt[s] (f
un _ : M => c) x (0 : TangentSpace% x ->L[𝕜] TangentSpace% c)
参数：c : M'；s : Set M；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
· 使用定理 `hasMFDerivAt_const`：hasMFDerivAt_const (c : M') (x : M) : HasMFDerivAt% 
(fun _ : M => c) x (0 : TangentSpace% x ->L[𝕜] TangentSpace% c)
-/
theorem hasMFDerivWithinAt_const (c : M') (s : Set M) (x : M) :
    HasMFDerivAt[s] (fun _ : M ↦ c) x (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  (hasMFDerivAt_const c x).hasMFDerivWithinAt
/-
**mdifferentiableAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_const : MDiffAt (fun _ : M => c) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `hasMFDerivAt_const`：hasMFDerivAt_const (c : M') (x : M) : HasMFDerivAt% 
(fun _ : M => c) x (0 : TangentSpace% x ->L[𝕜] TangentSpace% c)
-/
theorem mdifferentiableAt_const : MDiffAt (fun _ : M ↦ c) x :=
  (hasMFDerivAt_const c x).mdifferentiableAt
/-
**mdifferentiableWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_const : MDiffAt[s] (fun _ : M => c) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `mdifferentiableAt_const`：mdifferentiableAt_const : MDiffAt (fun _ : M =>
 c) x
-/
theorem mdifferentiableWithinAt_const : MDiffAt[s] (fun _ : M ↦ c) x :=
  mdifferentiableAt_const.mdifferentiableWithinAt
/-
**mdifferentiable_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_const : MDiff fun _ : M => c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableAt_const`：mdifferentiableAt_const : MDiffAt (fun _ : M =>
 c) x
-/
theorem mdifferentiable_const : MDiff fun _ : M ↦ c := fun _ ↦ mdifferentiableAt_const
/-
**mdifferentiableOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_const : MDiff[s] (fun _ : M => c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.mdifferentiableOn`：MDifferentiable.mdifferentiableOn (h 
: MDiff f) : MDiff[s] f
· 使用定理 `mdifferentiable_const`：mdifferentiable_const : MDiff fun _ : M => c
-/
theorem mdifferentiableOn_const : MDiff[s] (fun _ : M ↦ c) :=
  mdifferentiable_const.mdifferentiableOn

@[simp, mfld_simps]
/-
**mfderiv_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_const : mfderiv% (fun _ : M => c) x = (0 : TangentSpace% x ->L[𝕜] 
TangentSpace% c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用定理 `hasMFDerivAt_const`：hasMFDerivAt_const (c : M') (x : M) : HasMFDerivAt% 
(fun _ : M => c) x (0 : TangentSpace% x ->L[𝕜] TangentSpace% c)
-/
theorem mfderiv_const :
    mfderiv% (fun _ : M ↦ c) x = (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  (hasMFDerivAt_const c x).mfderiv
/-
**mfderivWithin_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_const : mfderiv[s] (fun _ : M => c) x = (0 : TangentSpace% x
 ->L[𝕜] TangentSpace% c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin_eq_zero`：HasMFDerivWithinAt.mfderivWith
in_eq_zero (h : HasMFDerivWithinAt I I' f s x 0) : mfderiv[s] f x = 0
· 使用定理 `hasMFDerivWithinAt_const`：hasMFDerivWithinAt_const (c : M') (s : Set M) 
(x : M) : HasMFDerivAt[s] (fun _ : M => c) x (0 : TangentSpace% x ->L[𝕜] Tangent
Space% c)
-/
theorem mfderivWithin_const :
    mfderiv[s] (fun _ : M ↦ c) x = (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  (hasMFDerivWithinAt_const _ _ _).mfderivWithin_eq_zero

end Const

section Prod

/-! ### Operations on the product of two manifolds -/

/-
**MDifferentiableWithinAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.prodMk {f : M -> M'} {g : M -> M''} (hf : MDiffAt[
s] f x) (hg : MDiffAt[s] g x) : MDiffAt[s] (fun x => (f x, g x)) x
参数：hf : MDiffAt[s] f x；hg : MDiffAt[s] g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `DifferentiableWithinAt.prodMk`：DifferentiableWithinAt.prodMk (hf₁ : Diff
erentiableWithinAt 𝕜 f₁ s x) (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) : Different
iableWithinAt 𝕜 (fu…
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…

--- 原说明 ---
### Operations on the product of two manifolds
-/
theorem MDifferentiableWithinAt.prodMk {f : M → M'} {g : M → M''}
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
    MDiffAt[s] (fun x ↦ (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/-- If `f` and `g` have derivatives `df` and `dg` within `s` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg` within `s`. -/
/-
**HasMFDerivWithinAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.prodMk {f : M -> M'} {g : M -> M''} {df : TangentSpace%
 x ->L[𝕜] TangentSpace% (f x)} (hf : HasMFDerivAt[s] f x df) {dg : TangentSpace%
 x ->L[𝕜] TangentSpace% (g x)} (hg : HasMFDerivAt[s] g x dg) : HasMFDerivAt[s] (
fun y => (f y, g y)) x (df.prod dg)
参数：f x；hf : HasMFDerivAt[s] f x df；g x；hg : HasMFDerivAt[s] g x dg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `f` and `g` have derivatives `df` and `dg` within `s` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg` within `s`.
-/
theorem HasMFDerivWithinAt.prodMk {f : M → M'} {g : M → M''}
    {df : TangentSpace% x →L[𝕜] TangentSpace% (f x)} (hf : HasMFDerivAt[s] f x df)
    {dg : TangentSpace% x →L[𝕜] TangentSpace% (g x)} (hg : HasMFDerivAt[s] g x dg) :
    HasMFDerivAt[s] (fun y ↦ (f y, g y)) x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩
/-
**mfderivWithin_prodMk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderivWithin_prodMk {f : M -> M'} {g : M -> M''} (hf : MDiffAt[s] f x) (h
g : MDiffAt[s] g x) (hs : UniqueMDiffAt[s] x) : mfderiv[s] (fun x => (f x, g x))
 x = (mfderiv[s] f x).prod (mfderiv[s] g x)
参数：hf : MDiffAt[s] f x；hg : MDiffAt[s] g x；hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `HasMFDerivWithinAt.prodMk`：HasMFDerivWithinAt.prodMk {f : M -> M'} {g : 
M -> M''} {df : TangentSpace% x ->L[𝕜] TangentSpace% (f x)} (hf : HasMFDerivAt[s
] f x df) {dg :…
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
lemma mfderivWithin_prodMk {f : M → M'} {g : M → M''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
    (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] (fun x ↦ (f x, g x)) x = (mfderiv[s] f x).prod (mfderiv[s] g x) :=
  (hf.hasMFDerivWithinAt.prodMk hg.hasMFDerivWithinAt).mfderivWithin hs
/-
**mfderiv_prodMk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderiv_prodMk {f : M -> M'} {g : M -> M''} (hf : MDiffAt f x) (hg : MDiff
At g x) : mfderiv% (fun x => (f x, g x)) x = (mfderiv% f x).prod (mfderiv% g x)
参数：hf : MDiffAt f x；hg : MDiffAt g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `mfderivWithin_prodMk`：mfderivWithin_prodMk {f : M -> M'} {g : M -> M''} 
(hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) (hs : UniqueMDiffAt[s] x) : mfderiv[
s] (fun x …
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
-/
lemma mfderiv_prodMk {f : M → M'} {g : M → M''} (hf : MDiffAt f x) (hg : MDiffAt g x) :
    mfderiv% (fun x ↦ (f x, g x)) x = (mfderiv% f x).prod (mfderiv% g x) := by
  simp_rw [← mfderivWithin_univ]
  exact mfderivWithin_prodMk hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I)
/-
**MDifferentiableAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.prodMk {f : M -> M'} {g : M -> M''} (hf : MDiffAt f x) (
hg : MDiffAt g x) : MDiffAt (fun x => (f x, g x)) x
参数：hf : MDiffAt f x；hg : MDiffAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `DifferentiableWithinAt.prodMk`：DifferentiableWithinAt.prodMk (hf₁ : Diff
erentiableWithinAt 𝕜 f₁ s x) (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) : Different
iableWithinAt 𝕜 (fu…
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
-/
theorem MDifferentiableAt.prodMk {f : M → M'} {g : M → M''} (hf : MDiffAt f x) (hg : MDiffAt g x) :
    MDiffAt (fun x ↦ (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/-- If `f` and `g` have derivatives `df` and `dg` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg`. -/
/-
**HasMFDerivAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.prodMk {f : M -> M'} {g : M -> M''} {df : TangentSpace% x ->L
[𝕜] TangentSpace% (f x)} (hf : HasMFDerivAt% f x df) {dg : TangentSpace% x ->L[𝕜
] TangentSpace% (g x)} (hg : HasMFDerivAt% g x dg) : HasMFDerivAt% (fun y => (f 
y, g y)) x (df.prod dg)
参数：f x；hf : HasMFDerivAt% f x df；g x；hg : HasMFDerivAt% g x dg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `f` and `g` have derivatives `df` and `dg` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg`.
-/
theorem HasMFDerivAt.prodMk {f : M → M'} {g : M → M''}
    {df : TangentSpace% x →L[𝕜] TangentSpace% (f x)} (hf : HasMFDerivAt% f x df)
    {dg : TangentSpace% x →L[𝕜] TangentSpace% (g x)} (hg : HasMFDerivAt% g x dg) :
    HasMFDerivAt% (fun y ↦ (f y, g y)) x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩
/-
**MDifferentiableWithinAt.prodMk_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.prodMk_space {f : M -> E'} {g : M -> E''} (hf : MD
iffAt[s] f x) (hg : MDiffAt[s] g x) : MDifferentiableWithinAt I 𝓘(𝕜, E' × E'') (
fun x => (f x, g x)) s x
参数：hf : MDiffAt[s] f x；hg : MDiffAt[s] g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `DifferentiableWithinAt.prodMk`：DifferentiableWithinAt.prodMk (hf₁ : Diff
erentiableWithinAt 𝕜 f₁ s x) (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) : Different
iableWithinAt 𝕜 (fu…
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
-/
theorem MDifferentiableWithinAt.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
    MDifferentiableWithinAt I 𝓘(𝕜, E' × E'') (fun x ↦ (f x, g x)) s x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩
/-
**MDifferentiableAt.prodMk_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.prodMk_space {f : M -> E'} {g : M -> E''} (hf : MDiffAt 
f x) (hg : MDiffAt g x) : MDifferentiableAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x
)) x
参数：hf : MDiffAt f x；hg : MDiffAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `DifferentiableWithinAt.prodMk`：DifferentiableWithinAt.prodMk (hf₁ : Diff
erentiableWithinAt 𝕜 f₁ s x) (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) : Different
iableWithinAt 𝕜 (fu…
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
-/
theorem MDifferentiableAt.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    MDifferentiableAt I 𝓘(𝕜, E' × E'') (fun x ↦ (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩
/-
**MDifferentiableOn.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.prodMk {f : M -> M'} {g : M -> M''} (hf : MDiff[s] f) (h
g : MDiff[s] g) : MDiff[s] (fun x => (f x, g x))
参数：hf : MDiff[s] f；hg : MDiff[s] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.prodMk`：MDifferentiableWithinAt.prodMk {f : M ->
 M'} {g : M -> M''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) : MDiffAt[s] (fu
n x => (f x, g x)) x
-/
theorem MDifferentiableOn.prodMk {f : M → M'} {g : M → M''} (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDiff[s] (fun x ↦ (f x, g x)) := fun x hx ↦ (hf x hx).prodMk (hg x hx)
/-
**MDifferentiable.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.prodMk {f : M -> M'} {g : M -> M''} (hf : MDiff f) (hg : M
Diff g) : MDiff fun x => (f x, g x)
参数：hf : MDiff f；hg : MDiff g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.prodMk`：MDifferentiableAt.prodMk {f : M -> M'} {g : M 
-> M''} (hf : MDiffAt f x) (hg : MDiffAt g x) : MDiffAt (fun x => (f x, g x)) x
-/
theorem MDifferentiable.prodMk {f : M → M'} {g : M → M''} (hf : MDiff f) (hg : MDiff g) :
    MDiff fun x ↦ (f x, g x) := fun x ↦ (hf x).prodMk (hg x)
/-
**MDifferentiableOn.prodMk_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.prodMk_space {f : M -> E'} {g : M -> E''} (hf : MDiff[s]
 f) (hg : MDiff[s] g) : MDifferentiableOn I 𝓘(𝕜, E' × E'') (fun x => (f x, g x))
 s
参数：hf : MDiff[s] f；hg : MDiff[s] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.prodMk_space`：MDifferentiableWithinAt.prodMk_spa
ce {f : M -> E'} {g : M -> E''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) : MD
ifferentiableWithinAt I 𝓘(…
-/
theorem MDifferentiableOn.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDifferentiableOn I 𝓘(𝕜, E' × E'') (fun x ↦ (f x, g x)) s :=
  fun x hx ↦ (hf x hx).prodMk_space (hg x hx)
/-
**MDifferentiable.prodMk_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.prodMk_space {f : M -> E'} {g : M -> E''} (hf : MDiff f) (
hg : MDiff g) : MDifferentiable I 𝓘(𝕜, E' × E'') fun x => (f x, g x)
参数：hf : MDiff f；hg : MDiff g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.prodMk_space`：MDifferentiableAt.prodMk_space {f : M ->
 E'} {g : M -> E''} (hf : MDiffAt f x) (hg : MDiffAt g x) : MDifferentiableAt I 
𝓘(𝕜, E' × E'') (fun …
-/
theorem MDifferentiable.prodMk_space {f : M → E'} {g : M → E''} (hf : MDiff f) (hg : MDiff g) :
    MDifferentiable I 𝓘(𝕜, E' × E'') fun x ↦ (f x, g x) :=
fun x ↦ (hf x).prodMk_space (hg x)
/-
**hasMFDerivAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivAt_fst (x : M × M') : HasMFDerivAt% (@Prod.fst M M') x (Continuo
usLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2))
参数：x : M × M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_prod`：extChartAt_prod (x : M × M') : extChartAt (I.prod I') x
 = (extChartAt I x.1).prod (extChartAt I' x.2)
· 使用定理 `HasFDerivWithinAt.congr_of_eventuallyEq`：HasFDerivWithinAt.congr_of_even
tuallyEq (h : HasFDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : HasFDerivWithinAt f₁ f' …
· 使用定理 `hasFDerivWithinAt_fst`：hasFDerivWithinAt_fst {s : Set (E × F)} : HasFDer
ivWithinAt (@Prod.fst E F) (fst 𝕜 E F) s p
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem hasMFDerivAt_fst (x : M × M') :
    HasMFDerivAt% (@Prod.fst M M') x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) := by
  refine ⟨continuous_fst.continuousAt, ?_⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I x.1 ∘ Prod.fst ∘ (extChartAt (I.prod I') x).symm) y = y.1 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I x.1).right_inv hy.1
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_fst this
  -- Porting note: next line was `simp only [mfld_simps]`
  exact (extChartAt I x.1).right_inv <| (extChartAt I x.1).map_source (mem_extChartAt_source _)
/-
**hasMFDerivWithinAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_fst (s : Set (M × M')) (x : M × M') : HasMFDerivAt[s] (
@Prod.fst M M') x (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% 
x.2))
参数：s : Set (M × M')；x : M × M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
· 使用定理 `hasMFDerivAt_fst`：hasMFDerivAt_fst (x : M × M') : HasMFDerivAt% (@Prod.f
st M M') x (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2))
-/
theorem hasMFDerivWithinAt_fst (s : Set (M × M')) (x : M × M') :
    HasMFDerivAt[s] (@Prod.fst M M') x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) :=
  (hasMFDerivAt_fst x).hasMFDerivWithinAt
/-
**mdifferentiableAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Prod.fst M M') x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `hasMFDerivAt_fst`：hasMFDerivAt_fst (x : M × M') : HasMFDerivAt% (@Prod.f
st M M') x (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2))
-/
theorem mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Prod.fst M M') x :=
  (hasMFDerivAt_fst x).mdifferentiableAt
/-
**mdifferentiableWithinAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_fst {s : Set (M × M')} {x : M × M'} : MDiffAt[s] (
@Prod.fst M M') x
参数：M × M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `mdifferentiableAt_fst`：mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Pr
od.fst M M') x
-/
theorem mdifferentiableWithinAt_fst {s : Set (M × M')} {x : M × M'} :
    MDiffAt[s] (@Prod.fst M M') x :=
  mdifferentiableAt_fst.mdifferentiableWithinAt
/-
**mdifferentiable_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_fst : MDiff (@Prod.fst M M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableAt_fst`：mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Pr
od.fst M M') x
-/
theorem mdifferentiable_fst : MDiff (@Prod.fst M M') := fun _ ↦ mdifferentiableAt_fst
/-
**mdifferentiableOn_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_fst {s : Set (M × M')} : MDiff[s] (@Prod.fst M M')
参数：M × M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.mdifferentiableOn`：MDifferentiable.mdifferentiableOn (h 
: MDiff f) : MDiff[s] f
· 使用定理 `mdifferentiable_fst`：mdifferentiable_fst : MDiff (@Prod.fst M M')
-/
theorem mdifferentiableOn_fst {s : Set (M × M')} : MDiff[s] (@Prod.fst M M') :=
  mdifferentiable_fst.mdifferentiableOn

@[simp, mfld_simps]
/-
**mfderiv_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_fst {x : M × M'} : mfderiv% (@Prod.fst M M') x = ContinuousLinearM
ap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用定理 `hasMFDerivAt_fst`：hasMFDerivAt_fst (x : M × M') : HasMFDerivAt% (@Prod.f
st M M') x (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2))
-/
theorem mfderiv_fst {x : M × M'} :
    mfderiv% (@Prod.fst M M') x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) :=
  (hasMFDerivAt_fst x).mfderiv
/-
**mfderivWithin_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_fst {s : Set (M × M')} {x : M × M'} (hxs : UniqueMDiffAt[s] 
x) : mfderiv[s] (@Prod.fst M M') x = ContinuousLinearMap.fst 𝕜 (TangentSpace% x.
1) (TangentSpace% x.2)
参数：M × M'；hxs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MDifferentiable.mfderivWithin`：MDifferentiable.mfderivWithin (h : MDiffA
t f x) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] f x = mfderiv% f x
· 使用定理 `mdifferentiableAt_fst`：mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Pr
od.fst M M') x
· 使用定理 `mfderiv_fst`：mfderiv_fst {x : M × M'} : mfderiv% (@Prod.fst M M') x = Co
ntinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)
-/
theorem mfderivWithin_fst {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@Prod.fst M M') x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_fst hxs]; exact mfderiv_fst

@[simp, mfld_simps]
/-
**tangentMap_prodFst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMap_prodFst {p : TangentBundle (I.prod I') (M × M')} : tangentMap% 
(@Prod.fst M M') p = ⟨p.proj.1, p.2.1⟩
参数：I.prod I'；M × M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_fst`：mfderiv_fst {x : M × M'} : mfderiv% (@Prod.fst M M') x = Co
ntinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)
-/
theorem tangentMap_prodFst {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap% (@Prod.fst M M') p = ⟨p.proj.1, p.2.1⟩ := by
  simp [tangentMap]; rfl
/-
**tangentMapWithin_prodFst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMapWithin_prodFst {s : Set (M × M')} {p : TangentBundle (I.prod I')
 (M × M')} (hs : UniqueMDiffAt[s] p.proj) : tangentMap[s] (@Prod.fst M M') p = ⟨
p.proj.1, p.2.1⟩
参数：M × M'；I.prod I'；M × M'；hs : UniqueMDiffAt[s] p.proj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin_fst`：mfderivWithin_fst {s : Set (M × M')} {x : M × M'} (hx
s : UniqueMDiffAt[s] x) : mfderiv[s] (@Prod.fst M M') x = ContinuousLinearMap.fs
t 𝕜 (Ta…
-/
theorem tangentMapWithin_prodFst {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (@Prod.fst M M') p = ⟨p.proj.1, p.2.1⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_fst]
  · rcases p with ⟨⟩; rfl
  · exact hs
/-
**hasMFDerivAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivAt_snd (x : M × M') : HasMFDerivAt% (@Prod.snd M M') x (Continuo
usLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2))
参数：x : M × M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_prod`：extChartAt_prod (x : M × M') : extChartAt (I.prod I') x
 = (extChartAt I x.1).prod (extChartAt I' x.2)
· 使用定理 `HasFDerivWithinAt.congr_of_eventuallyEq`：HasFDerivWithinAt.congr_of_even
tuallyEq (h : HasFDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : HasFDerivWithinAt f₁ f' …
· 使用定理 `hasFDerivWithinAt_snd`：hasFDerivWithinAt_snd {s : Set (E × F)} : HasFDer
ivWithinAt (@Prod.snd E F) (snd 𝕜 E F) s p
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem hasMFDerivAt_snd (x : M × M') :
    HasMFDerivAt% (@Prod.snd M M') x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) := by
  refine ⟨continuous_snd.continuousAt, ?_⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I' x.2 ∘ Prod.snd ∘ (extChartAt (I.prod I') x).symm) y = y.2 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I' x.2).right_inv hy.2
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_snd this
  -- Porting note: the next line was `simp only [mfld_simps]`
  exact (extChartAt I' x.2).right_inv <| (extChartAt I' x.2).map_source (mem_extChartAt_source _)
/-
**hasMFDerivWithinAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_snd (s : Set (M × M')) (x : M × M') : HasMFDerivAt[s] (
@Prod.snd M M') x (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% 
x.2))
参数：s : Set (M × M')；x : M × M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
· 使用定理 `hasMFDerivAt_snd`：hasMFDerivAt_snd (x : M × M') : HasMFDerivAt% (@Prod.s
nd M M') x (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2))
-/
theorem hasMFDerivWithinAt_snd (s : Set (M × M')) (x : M × M') :
    HasMFDerivAt[s] (@Prod.snd M M') x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) :=
  (hasMFDerivAt_snd x).hasMFDerivWithinAt
/-
**mdifferentiableAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Prod.snd M M') x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `hasMFDerivAt_snd`：hasMFDerivAt_snd (x : M × M') : HasMFDerivAt% (@Prod.s
nd M M') x (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2))
-/
theorem mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Prod.snd M M') x :=
  (hasMFDerivAt_snd x).mdifferentiableAt
/-
**mdifferentiableWithinAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_snd {s : Set (M × M')} {x : M × M'} : MDiffAt[s] (
@Prod.snd M M') x
参数：M × M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `mdifferentiableAt_snd`：mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Pr
od.snd M M') x
-/
theorem mdifferentiableWithinAt_snd {s : Set (M × M')} {x : M × M'} :
    MDiffAt[s] (@Prod.snd M M') x := mdifferentiableAt_snd.mdifferentiableWithinAt
/-
**mdifferentiable_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_snd : MDiff (@Prod.snd M M')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableAt_snd`：mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Pr
od.snd M M') x
-/
theorem mdifferentiable_snd : MDiff (@Prod.snd M M') := fun _ ↦ mdifferentiableAt_snd
/-
**mdifferentiableOn_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_snd {s : Set (M × M')} : MDiff[s] (@Prod.snd M M')
参数：M × M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.mdifferentiableOn`：MDifferentiable.mdifferentiableOn (h 
: MDiff f) : MDiff[s] f
· 使用定理 `mdifferentiable_snd`：mdifferentiable_snd : MDiff (@Prod.snd M M')
-/
theorem mdifferentiableOn_snd {s : Set (M × M')} : MDiff[s] (@Prod.snd M M') :=
  mdifferentiable_snd.mdifferentiableOn

@[simp, mfld_simps]
/-
**mfderiv_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_snd {x : M × M'} : mfderiv% (@Prod.snd M M') x = ContinuousLinearM
ap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用定理 `hasMFDerivAt_snd`：hasMFDerivAt_snd (x : M × M') : HasMFDerivAt% (@Prod.s
nd M M') x (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2))
-/
theorem mfderiv_snd {x : M × M'} :
    mfderiv% (@Prod.snd M M') x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) :=
  (hasMFDerivAt_snd x).mfderiv
/-
**mfderivWithin_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_snd {s : Set (M × M')} {x : M × M'} (hxs : UniqueMDiffAt[s] 
x) : mfderiv[s] (@Prod.snd M M') x = ContinuousLinearMap.snd 𝕜 (TangentSpace% x.
1) (TangentSpace% x.2)
参数：M × M'；hxs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MDifferentiable.mfderivWithin`：MDifferentiable.mfderivWithin (h : MDiffA
t f x) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] f x = mfderiv% f x
· 使用定理 `mdifferentiableAt_snd`：mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Pr
od.snd M M') x
· 使用定理 `mfderiv_snd`：mfderiv_snd {x : M × M'} : mfderiv% (@Prod.snd M M') x = Co
ntinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)
-/
theorem mfderivWithin_snd {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@Prod.snd M M') x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_snd hxs]; exact mfderiv_snd
/-
**MDifferentiableWithinAt.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.fst {f : N -> M × M'} {s : Set N} {x : N} (hf : MD
iffAt[s] f x) : MDiffAt[s] (fun x => (f x).1) x
参数：hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp_mdifferentiableWithinAt`：MDifferentiableAt.comp_m
differentiableWithinAt (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s]
 (g ∘ f) x
· 使用定理 `mdifferentiableAt_fst`：mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Pr
od.fst M M') x
-/
theorem MDifferentiableWithinAt.fst {f : N → M × M'} {s : Set N} {x : N}
    (hf : MDiffAt[s] f x) : MDiffAt[s] (fun x ↦ (f x).1) x :=
  mdifferentiableAt_fst.comp_mdifferentiableWithinAt x hf
/-
**MDifferentiableAt.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.fst {f : N -> M × M'} {x : N} (hf : MDiffAt f x) : MDiff
At (fun x => (f x).1) x
参数：hf : MDiffAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp`：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (h
f : MDiffAt f x) : MDiffAt (g ∘ f) x
· 使用定理 `mdifferentiableAt_fst`：mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Pr
od.fst M M') x
-/
theorem MDifferentiableAt.fst {f : N → M × M'} {x : N} (hf : MDiffAt f x) :
    MDiffAt (fun x ↦ (f x).1) x :=
  mdifferentiableAt_fst.comp x hf
/-
**MDifferentiable.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.fst {f : N -> M × M'} (hf : MDiff f) : MDiff fun x => (f x
).1
参数：hf : MDiff f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.comp`：MDifferentiable.comp (hg : MDiff g) (hf : MDiff f)
 : MDiff (g ∘ f)
· 使用定理 `mdifferentiable_fst`：mdifferentiable_fst : MDiff (@Prod.fst M M')
-/
theorem MDifferentiable.fst {f : N → M × M'} (hf : MDiff f) : MDiff fun x ↦ (f x).1 :=
  mdifferentiable_fst.comp hf
/-
**MDifferentiableWithinAt.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.snd {f : N -> M × M'} {s : Set N} {x : N} (hf : MD
iffAt[s] f x) : MDiffAt[s] (fun x => (f x).2) x
参数：hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp_mdifferentiableWithinAt`：MDifferentiableAt.comp_m
differentiableWithinAt (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s]
 (g ∘ f) x
· 使用定理 `mdifferentiableAt_snd`：mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Pr
od.snd M M') x
-/
theorem MDifferentiableWithinAt.snd {f : N → M × M'} {s : Set N} {x : N} (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x ↦ (f x).2) x :=
  mdifferentiableAt_snd.comp_mdifferentiableWithinAt x hf
/-
**MDifferentiableAt.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.snd {f : N -> M × M'} {x : N} (hf : MDiffAt f x) : MDiff
At (fun x => (f x).2) x
参数：hf : MDiffAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp`：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (h
f : MDiffAt f x) : MDiffAt (g ∘ f) x
· 使用定理 `mdifferentiableAt_snd`：mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Pr
od.snd M M') x
-/
theorem MDifferentiableAt.snd {f : N → M × M'} {x : N} (hf : MDiffAt f x) :
    MDiffAt (fun x ↦ (f x).2) x :=
  mdifferentiableAt_snd.comp x hf
/-
**MDifferentiable.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.snd {f : N -> M × M'} (hf : MDiff f) : MDiff fun x => (f x
).2
参数：hf : MDiff f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.comp`：MDifferentiable.comp (hg : MDiff g) (hf : MDiff f)
 : MDiff (g ∘ f)
· 使用定理 `mdifferentiable_snd`：mdifferentiable_snd : MDiff (@Prod.snd M M')
-/
theorem MDifferentiable.snd {f : N → M × M'} (hf : MDiff f) : MDiff fun x ↦ (f x).2 :=
  mdifferentiable_snd.comp hf
/-
**mdifferentiableWithinAt_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_prod_iff (f : M -> M' × N') : MDiffAt[s] f x ↔ MDi
ffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.snd ∘ f) x
参数：f : M -> M' × N'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.fst`：MDifferentiableWithinAt.fst {f : N -> M × M
'} {s : Set N} {x : N} (hf : MDiffAt[s] f x) : MDiffAt[s] (fun x => (f x).1) x
· 使用定理 `MDifferentiableWithinAt.snd`：MDifferentiableWithinAt.snd {f : N -> M × M
'} {s : Set N} {x : N} (hf : MDiffAt[s] f x) : MDiffAt[s] (fun x => (f x).2) x
· 使用定理 `MDifferentiableWithinAt.prodMk`：MDifferentiableWithinAt.prodMk {f : M ->
 M'} {g : M -> M''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) : MDiffAt[s] (fu
n x => (f x, g x)) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mdifferentiableWithinAt_prod_iff (f : M → M' × N') :
    MDiffAt[s] f x ↔ MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.snd ∘ f) x :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩
/-
**mdifferentiableWithinAt_prod_module_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_prod_module_iff (f : M -> F₁ × F₂) : MDifferentiab
leWithinAt I 𝓘(𝕜, F₁ × F₂) f s x ↔ MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Pro
d.snd ∘ f) x
参数：f : M -> F₁ × F₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modelWithCornersSelf_prod`：modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜
, E).prod 𝓘(𝕜, F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `chartedSpaceSelf_prod`：chartedSpaceSelf_prod : prodChartedSpace H H H' H
' = chartedSpaceSelf (H × H')
· 使用定理 `mdifferentiableWithinAt_prod_iff`：mdifferentiableWithinAt_prod_iff (f : 
M -> M' × N') : MDiffAt[s] f x ↔ MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.
snd ∘ f) x
-/
theorem mdifferentiableWithinAt_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableWithinAt I 𝓘(𝕜, F₁ × F₂) f s x ↔
      MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableWithinAt_prod_iff f
/-
**mdifferentiableAt_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_prod_iff (f : M -> M' × N') : MDiffAt f x ↔ MDiffAt (Pro
d.fst ∘ f) x ∧ MDiffAt (Prod.snd ∘ f) x
参数：f : M -> M' × N'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_prod_iff`：mdifferentiableWithinAt_prod_iff (f : 
M -> M' × N') : MDiffAt[s] f x ↔ MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.
snd ∘ f) x
-/
theorem mdifferentiableAt_prod_iff (f : M → M' × N') :
    MDiffAt f x ↔ MDiffAt (Prod.fst ∘ f) x ∧ MDiffAt (Prod.snd ∘ f) x := by
  simp_rw [← mdifferentiableWithinAt_univ]; exact mdifferentiableWithinAt_prod_iff f
/-
**mdifferentiableAt_prod_module_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_prod_module_iff (f : M -> F₁ × F₂) : MDifferentiableAt I
 𝓘(𝕜, F₁ × F₂) f x ↔ MDiffAt (Prod.fst ∘ f) x ∧ MDiffAt (Prod.snd ∘ f) x
参数：f : M -> F₁ × F₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modelWithCornersSelf_prod`：modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜
, E).prod 𝓘(𝕜, F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `chartedSpaceSelf_prod`：chartedSpaceSelf_prod : prodChartedSpace H H H' H
' = chartedSpaceSelf (H × H')
· 使用定理 `mdifferentiableAt_prod_iff`：mdifferentiableAt_prod_iff (f : M -> M' × N'
) : MDiffAt f x ↔ MDiffAt (Prod.fst ∘ f) x ∧ MDiffAt (Prod.snd ∘ f) x
-/
theorem mdifferentiableAt_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableAt I 𝓘(𝕜, F₁ × F₂) f x ↔
      MDiffAt (Prod.fst ∘ f) x ∧ MDiffAt (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableAt_prod_iff f
/-
**mdifferentiableOn_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_prod_iff (f : M -> M' × N') : MDiff[s] f ↔ MDiff[s] (Pro
d.fst ∘ f) ∧ MDiff[s] (Prod.snd ∘ f)
参数：f : M -> M' × N'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableWithinAt_prod_iff`：mdifferentiableWithinAt_prod_iff (f : 
M -> M' × N') : MDiffAt[s] f x ↔ MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.
snd ∘ f) x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem mdifferentiableOn_prod_iff (f : M → M' × N') :
    MDiff[s] f ↔ MDiff[s] (Prod.fst ∘ f) ∧ MDiff[s] (Prod.snd ∘ f) :=
  ⟨fun h ↦ ⟨fun x hx ↦ ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).1,
      fun x hx ↦ ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).2⟩,
    fun h x hx ↦ (mdifferentiableWithinAt_prod_iff f).2 ⟨h.1 x hx, h.2 x hx⟩⟩
/-
**mdifferentiableOn_prod_module_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_prod_module_iff (f : M -> F₁ × F₂) : MDifferentiableOn I
 𝓘(𝕜, F₁ × F₂) f s ↔ MDiff[s] (Prod.fst ∘ f) ∧ MDiff[s] (Prod.snd ∘ f)
参数：f : M -> F₁ × F₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modelWithCornersSelf_prod`：modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜
, E).prod 𝓘(𝕜, F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `chartedSpaceSelf_prod`：chartedSpaceSelf_prod : prodChartedSpace H H H' H
' = chartedSpaceSelf (H × H')
· 使用定理 `mdifferentiableOn_prod_iff`：mdifferentiableOn_prod_iff (f : M -> M' × N'
) : MDiff[s] f ↔ MDiff[s] (Prod.fst ∘ f) ∧ MDiff[s] (Prod.snd ∘ f)
-/
theorem mdifferentiableOn_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableOn I 𝓘(𝕜, F₁ × F₂) f s ↔ MDiff[s] (Prod.fst ∘ f) ∧ MDiff[s] (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableOn_prod_iff f
/-
**mdifferentiable_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_prod_iff (f : M -> M' × N') : MDiff f ↔ MDiff (Prod.fst ∘ 
f) ∧ MDiff (Prod.snd ∘ f)
参数：f : M -> M' × N'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.fst`：MDifferentiable.fst {f : N -> M × M'} (hf : MDiff f
) : MDiff fun x => (f x).1
· 使用定理 `MDifferentiable.snd`：MDifferentiable.snd {f : N -> M × M'} (hf : MDiff f
) : MDiff fun x => (f x).2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MDifferentiable.prodMk`：MDifferentiable.prodMk {f : M -> M'} {g : M -> M
''} (hf : MDiff f) (hg : MDiff g) : MDiff fun x => (f x, g x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mdifferentiable_prod_iff (f : M → M' × N') :
    MDiff f ↔ MDiff (Prod.fst ∘ f) ∧ MDiff (Prod.snd ∘ f) :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ by convert! h.1.prodMk h.2⟩
/-
**mdifferentiable_prod_module_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_prod_module_iff (f : M -> F₁ × F₂) : MDifferentiable I 𝓘(𝕜
, F₁ × F₂) f ↔ MDiff (Prod.fst ∘ f) ∧ MDiff (Prod.snd ∘ f)
参数：f : M -> F₁ × F₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `modelWithCornersSelf_prod`：modelWithCornersSelf_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜
, E).prod 𝓘(𝕜, F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `chartedSpaceSelf_prod`：chartedSpaceSelf_prod : prodChartedSpace H H H' H
' = chartedSpaceSelf (H × H')
· 使用定理 `mdifferentiable_prod_iff`：mdifferentiable_prod_iff (f : M -> M' × N') : 
MDiff f ↔ MDiff (Prod.fst ∘ f) ∧ MDiff (Prod.snd ∘ f)
-/
theorem mdifferentiable_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiable I 𝓘(𝕜, F₁ × F₂) f ↔ MDiff (Prod.fst ∘ f) ∧ MDiff (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiable_prod_iff f


section prodMap

variable {f : M → M'} {g : N → N'} {r : Set N} {y : N}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
/-
**MDifferentiableWithinAt.prodMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.prodMap' {p : M × N} (hf : MDiffAt[s] f p.1) (hg :
 MDiffAt[r] g p.2) : MDiffAt[s ×ˢ r] (Prod.map f g) p
参数：hf : MDiffAt[s] f p.1；hg : MDiffAt[r] g p.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.prodMk`：MDifferentiableWithinAt.prodMk {f : M ->
 M'} {g : M -> M''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) : MDiffAt[s] (fu
n x => (f x, g x)) x
· 使用定理 `MDifferentiableWithinAt.comp`：MDifferentiableWithinAt.comp (hg : MDiffAt
[u] g (f x)) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) : MDifferentiableWit
hinAt I I'' (g ∘ f…
· 使用定理 `mdifferentiableWithinAt_fst`：mdifferentiableWithinAt_fst {s : Set (M × M
')} {x : M × M'} : MDiffAt[s] (@Prod.fst M M') x
· 使用定理 `Set.prod_subset_preimage_fst`：prod_subset_preimage_fst (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.fst ⁻¹' s
· 使用定理 `mdifferentiableWithinAt_snd`：mdifferentiableWithinAt_snd {s : Set (M × M
')} {x : M × M'} : MDiffAt[s] (@Prod.snd M M') x
· 使用定理 `Set.prod_subset_preimage_snd`：prod_subset_preimage_snd (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.snd ⁻¹' t

--- 原说明 ---
The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point.
-/
theorem MDifferentiableWithinAt.prodMap' {p : M × N}
    (hf : MDiffAt[s] f p.1) (hg : MDiffAt[r] g p.2) :
    MDiffAt[s ×ˢ r] (Prod.map f g) p :=
  (hf.comp p mdifferentiableWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk <|
    hg.comp p mdifferentiableWithinAt_snd (prod_subset_preimage_snd _ _)
/-
**MDifferentiableWithinAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.prodMap (hf : MDiffAt[s] f x) (hg : MDiffAt[r] g y
) : MDiffAt[s ×ˢ r] (Prod.map f g) (x, y)
参数：hf : MDiffAt[s] f x；hg : MDiffAt[r] g y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.prodMap'`：MDifferentiableWithinAt.prodMap' {p : 
M × N} (hf : MDiffAt[s] f p.1) (hg : MDiffAt[r] g p.2) : MDiffAt[s ×ˢ r] (Prod.m
ap f g) p
-/
theorem MDifferentiableWithinAt.prodMap (hf : MDiffAt[s] f x) (hg : MDiffAt[r] g y) :
    MDiffAt[s ×ˢ r] (Prod.map f g) (x, y) :=
  hf.prodMap' hg
/-
**MDifferentiableAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.prodMap (hf : MDiffAt f x) (hg : MDiffAt g y) : MDiffAt 
(Prod.map f g) (x, y)
参数：hf : MDiffAt f x；hg : MDiffAt g y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `MDifferentiableWithinAt.prodMap`：MDifferentiableWithinAt.prodMap (hf : M
DiffAt[s] f x) (hg : MDiffAt[r] g y) : MDiffAt[s ×ˢ r] (Prod.map f g) (x, y)
-/
theorem MDifferentiableAt.prodMap (hf : MDiffAt f x) (hg : MDiffAt g y) :
    MDiffAt (Prod.map f g) (x, y) := by
  rw [← mdifferentiableWithinAt_univ] at *
  convert! hf.prodMap hg
  exact univ_prod_univ.symm

/-- Variant of `MDifferentiableAt.prod_map` in which the point in the product is given as `p`
instead of a pair `(x, y)`. -/
/-
**MDifferentiableAt.prodMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.prodMap' {p : M × N} (hf : MDiffAt f p.1) (hg : MDiffAt 
g p.2) : MDiffAt (Prod.map f g) p
参数：hf : MDiffAt f p.1；hg : MDiffAt g p.2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.prodMap`：MDifferentiableAt.prodMap (hf : MDiffAt f x) 
(hg : MDiffAt g y) : MDiffAt (Prod.map f g) (x, y)

--- 原说明 ---
Variant of `MDifferentiableAt.prod_map` in which the point in the product is giv
en as `p`
instead of a pair `(x, y)`.
-/
theorem MDifferentiableAt.prodMap' {p : M × N}
    (hf : MDiffAt f p.1) (hg : MDiffAt g p.2) : MDiffAt (Prod.map f g) p :=
  hf.prodMap hg
/-
**MDifferentiableOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.prodMap (hf : MDiff[s] f) (hg : MDiff[r] g) : MDiff[s ×ˢ
 r] (Prod.map f g)
参数：hf : MDiff[s] f；hg : MDiff[r] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableOn.prodMk`：MDifferentiableOn.prodMk {f : M -> M'} {g : M 
-> M''} (hf : MDiff[s] f) (hg : MDiff[s] g) : MDiff[s] (fun x => (f x, g x))
· 使用定理 `MDifferentiableOn.comp`：MDifferentiableOn.comp (hg : MDiff[u] g) (hf : M
Diff[s] f) (st : s subseteq f ⁻¹' u) : MDiff[s] (g ∘ f)
· 使用定理 `mdifferentiableOn_fst`：mdifferentiableOn_fst {s : Set (M × M')} : MDiff[
s] (@Prod.fst M M')
· 使用定理 `Set.prod_subset_preimage_fst`：prod_subset_preimage_fst (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.fst ⁻¹' s
· 使用定理 `mdifferentiableOn_snd`：mdifferentiableOn_snd {s : Set (M × M')} : MDiff[
s] (@Prod.snd M M')
· 使用定理 `Set.prod_subset_preimage_snd`：prod_subset_preimage_snd (s : Set α) (t : 
Set β) : s ×ˢ t subseteq Prod.snd ⁻¹' t
-/
theorem MDifferentiableOn.prodMap (hf : MDiff[s] f) (hg : MDiff[r] g) :
    MDiff[s ×ˢ r] (Prod.map f g) :=
  (hf.comp mdifferentiableOn_fst (prod_subset_preimage_fst _ _)).prodMk <|
    hg.comp mdifferentiableOn_snd (prod_subset_preimage_snd _ _)
/-
**MDifferentiable.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.prodMap (hf : MDiff f) (hg : MDiff g) : MDiff (Prod.map f 
g)
参数：hf : MDiff f；hg : MDiff g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.prodMap'`：MDifferentiableAt.prodMap' {p : M × N} (hf :
 MDiffAt f p.1) (hg : MDiffAt g p.2) : MDiffAt (Prod.map f g) p
-/
theorem MDifferentiable.prodMap (hf : MDiff f) (hg : MDiff g) : MDiff (Prod.map f g) := fun p ↦
  (hf p.1).prodMap' (hg p.2)
/-
**HasMFDerivWithinAt.prodMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.prodMap {s : Set <| M × M'} {p : M × M'} {f : M -> N} {
g : M' -> N'} {df : TangentSpace% p.1 ->L[𝕜] TangentSpace% (f p.1)} (hf : HasMFD
erivAt[Prod.fst '' s] f p.1 df) {dg : TangentSpace% p.2 ->L[𝕜] TangentSpace% (g 
p.2)} (hg : HasMFDerivAt[Prod.snd '' s] g p.2 dg) : HasMFDerivAt[s] (Prod.map f 
g) p (df.prodMap dg)
参数：f p.1；hf : HasMFDerivAt[Prod.fst '' s] f p.1 df；g p.2；hg : HasMFDerivAt[Prod.
snd '' s] g p.2 dg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `ContinuousWithinAt.prodMap`：ContinuousWithinAt.prodMap {f : α -> γ} {g :
 β -> δ} {s : Set α} {t : Set β} {x : α} {y : β} (hf : ContinuousWithinAt f s x)
 (hg : Continuou…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
· 使用定理 `PartialEquiv.prod_symm`：prod_symm (e : PartialEquiv α β) (e' : PartialEq
uiv γ δ) : (e.prod e').symm = e.symm.prod e'.symm
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `writtenInExtChartAt_prod`：writtenInExtChartAt_prod {f : M -> N} {g : M' 
-> N'} {x : M} {x' : M'} : (writtenInExtChartAt (I.prod I') (J.prod J') (x, x') 
(Prod.map f g)…
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `HasFDerivWithinAt.prodMap`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type u_…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.fst_image_prod_subset`：fst_image_prod_subset (s : Set α) (t : Set β)
 : Prod.fst '' s ×ˢ t subseteq s
· 使用定理 `Set.snd_image_prod_subset`：snd_image_prod_subset (s : Set α) (t : Set β)
 : Prod.snd '' s ×ˢ t subseteq t
-/
lemma HasMFDerivWithinAt.prodMap {s : Set <| M × M'} {p : M × M'} {f : M → N} {g : M' → N'}
    {df : TangentSpace% p.1 →L[𝕜] TangentSpace% (f p.1)}
    (hf : HasMFDerivAt[Prod.fst '' s] f p.1 df)
    {dg : TangentSpace% p.2 →L[𝕜] TangentSpace% (g p.2)}
    (hg : HasMFDerivAt[Prod.snd '' s] g p.2 dg) :
    HasMFDerivAt[s] (Prod.map f g) p (df.prodMap dg) := by
  refine ⟨hf.1.prodMap hg.1 |>.mono (by grind), ?_⟩
  have better : ((extChartAt (I.prod I') p).symm ⁻¹' s ∩ range ↑(I.prod I')) ⊆
      ((extChartAt I p.1).symm ⁻¹' (Prod.fst '' s) ∩ range I) ×ˢ
        ((extChartAt I' p.2).symm ⁻¹' (Prod.snd '' s) ∩ range I') := by
    simp only [mfld_simps]
    rw [range_prodMap, I.toPartialEquiv.prod_symm, (chartAt H p.1).toPartialEquiv.prod_symm]
    intro p₀ ⟨hp₀, ⟨hp₁₁, hp₁₂⟩⟩
    exact ⟨⟨by simp_all; grind, by assumption⟩, ⟨by simp_all; grind, by assumption⟩⟩
  rw [writtenInExtChartAt_prod]
  apply HasFDerivWithinAt.mono ?_ better
  apply HasFDerivWithinAt.prodMap
  exacts [hf.2.mono (fst_image_prod_subset ..), hg.2.mono (snd_image_prod_subset ..)]

set_option backward.isDefEq.respectTransparency false in
/-
**HasMFDerivAt.prodMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.prodMap {p : M × M'} {f : M -> N} {g : M' -> N'} {df : Tangen
tSpace% p.1 ->L[𝕜] TangentSpace% (f p.1)} (hf : HasMFDerivAt% f p.1 df) {dg : Ta
ngentSpace% p.2 ->L[𝕜] TangentSpace% (g p.2)} (hg : HasMFDerivAt% g p.2 dg) : Ha
sMFDerivAt% (Prod.map f g) p ((mfderiv% f p.1).prodMap (mfderiv% g p.2))
参数：f p.1；hf : HasMFDerivAt% f p.1 df；g p.2；hg : HasMFDerivAt% g p.2 dg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用引理 `HasMFDerivWithinAt.prodMap`：HasMFDerivWithinAt.prodMap {s : Set <| M × M
'} {p : M × M'} {f : M -> N} {g : M' -> N'} {df : TangentSpace% p.1 ->L[𝕜] Tange
ntSpace% (f p.1)…
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
-/
lemma HasMFDerivAt.prodMap {p : M × M'} {f : M → N} {g : M' → N'}
    {df : TangentSpace% p.1 →L[𝕜] TangentSpace% (f p.1)} (hf : HasMFDerivAt% f p.1 df)
    {dg : TangentSpace% p.2 →L[𝕜] TangentSpace% (g p.2)} (hg : HasMFDerivAt% g p.2 dg) :
    HasMFDerivAt% (Prod.map f g) p
      ((mfderiv% f p.1).prodMap (mfderiv% g p.2)) := by
  simp_rw [← hasMFDerivWithinAt_univ, ← mfderivWithin_univ, ← univ_prod_univ]
  convert! hf.hasMFDerivWithinAt.prodMap hg.hasMFDerivWithinAt
  · rw [mfderivWithin_univ]; exact hf.mfderiv
  · rw [mfderivWithin_univ]; exact hg.mfderiv

-- Note: this lemma does not apply easily to an arbitrary subset `s ⊆ M × M'` as
-- unique differentiability on `(Prod.fst '' s)` and `(Prod.snd '' s)` does not imply
-- unique differentiability on `s`: a priori, `(Prod.fst '' s) × (Prod.fst '' s)`
-- could be a strict superset of `s`.
/-
**mfderivWithin_prodMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderivWithin_prodMap {p : M × M'} {t : Set M'} {f : M -> N} {g : M' -> N'
} (hf : MDiffAt[s] f p.1) (hg : MDiffAt[t] g p.2) (hs : UniqueMDiffAt[s] p.1) (h
t : UniqueMDiffAt[t] p.2) : mfderiv[s ×ˢ t] (Prod.map f g) p = (mfderiv[s] f p.1
).prodMap (mfderiv[t] g p.2)
参数：hf : MDiffAt[s] f p.1；hg : MDiffAt[t] g p.2；hs : UniqueMDiffAt[s] p.1；ht : Un
iqueMDiffAt[t] p.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mono`：HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f 
x f') (hst : s subseteq t) : HasMFDerivAt[s] f x f'
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用引理 `HasMFDerivWithinAt.prodMap`：HasMFDerivWithinAt.prodMap {s : Set <| M × M
'} {p : M × M'} {f : M -> N} {g : M' -> N'} {df : TangentSpace% p.1 ->L[𝕜] Tange
ntSpace% (f p.1)…
· 使用定理 `UniqueMDiffWithinAt.prod`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {H : Type u_…
-/
lemma mfderivWithin_prodMap {p : M × M'} {t : Set M'} {f : M → N} {g : M' → N'}
    (hf : MDiffAt[s] f p.1) (hg : MDiffAt[t] g p.2)
    (hs : UniqueMDiffAt[s] p.1) (ht : UniqueMDiffAt[t] p.2) :
    mfderiv[s ×ˢ t] (Prod.map f g) p = (mfderiv[s] f p.1).prodMap (mfderiv[t] g p.2) := by
  have hf' : HasMFDerivAt[Prod.fst '' s ×ˢ t] f p.1 (mfderiv[s] f p.1) :=
    hf.hasMFDerivWithinAt.mono (by grind)
  have hg' : HasMFDerivAt[Prod.snd '' s ×ˢ t] g p.2 (mfderiv[t] g p.2) :=
    hg.hasMFDerivWithinAt.mono (by grind)
  exact (hf'.prodMap hg').mfderivWithin (hs.prod ht)
/-
**mfderiv_prodMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderiv_prodMap {p : M × M'} {f : M -> N} {g : M' -> N'} (hf : MDiffAt f p
.1) (hg : MDiffAt g p.2) : mfderiv% (Prod.map f g) p = (mfderiv% f p.1).prodMap 
(mfderiv% g p.2)
参数：hf : MDiffAt f p.1；hg : MDiffAt g p.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `mfderivWithin_prodMap`：mfderivWithin_prodMap {p : M × M'} {t : Set M'} {
f : M -> N} {g : M' -> N'} (hf : MDiffAt[s] f p.1) (hg : MDiffAt[t] g p.2) (hs :
 UniqueMDif…
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
-/
lemma mfderiv_prodMap {p : M × M'} {f : M → N} {g : M' → N'}
    (hf : MDiffAt f p.1) (hg : MDiffAt g p.2) :
    mfderiv% (Prod.map f g) p = (mfderiv% f p.1).prodMap (mfderiv% g p.2) := by
  simp_rw [← mfderivWithin_univ, ← univ_prod_univ]
  exact mfderivWithin_prodMap hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I) (uniqueMDiffWithinAt_univ I')

end prodMap

@[simp, mfld_simps]
/-
**tangentMap_prodSnd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMap_prodSnd {p : TangentBundle (I.prod I') (M × M')} : tangentMap% 
(@Prod.snd M M') p = ⟨p.proj.2, p.2.2⟩
参数：I.prod I'；M × M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_snd`：mfderiv_snd {x : M × M'} : mfderiv% (@Prod.snd M M') x = Co
ntinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)
-/
theorem tangentMap_prodSnd {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap% (@Prod.snd M M') p = ⟨p.proj.2, p.2.2⟩ := by
  simp [tangentMap]; rfl
/-
**tangentMapWithin_prodSnd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMapWithin_prodSnd {s : Set (M × M')} {p : TangentBundle (I.prod I')
 (M × M')} (hs : UniqueMDiffAt[s] p.proj) : tangentMap[s] (@Prod.snd M M') p = ⟨
p.proj.2, p.2.2⟩
参数：M × M'；I.prod I'；M × M'；hs : UniqueMDiffAt[s] p.proj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin_snd`：mfderivWithin_snd {s : Set (M × M')} {x : M × M'} (hx
s : UniqueMDiffAt[s] x) : mfderiv[s] (@Prod.snd M M') x = ContinuousLinearMap.sn
d 𝕜 (Ta…
-/
theorem tangentMapWithin_prodSnd {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (@Prod.snd M M') p = ⟨p.proj.2, p.2.2⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_snd hs]
  rcases p with ⟨⟩; rfl

-- Kept as an alias for discoverability.
alias MDifferentiableAt.mfderiv_prod := mfderiv_prodMk

set_option backward.isDefEq.respectTransparency false in
/-
**mfderiv_prod_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_prod_left {x₀ : M} {y₀ : M'} : mfderiv% (fun (x : M) => (x, y₀)) x
₀ = ContinuousLinearMap.inl 𝕜 (TangentSpace% x₀) (TangentSpace% y₀)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MDifferentiableAt.mfderiv_prod`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `mdifferentiableAt_id`：mdifferentiableAt_id : MDiffAt (@id M) x
· 使用定理 `mdifferentiableAt_const`：mdifferentiableAt_const : MDiffAt (fun _ : M =>
 c) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_id`：mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (
TangentSpace% x)
· 使用定理 `mfderiv_const`：mfderiv_const : mfderiv% (fun _ : M => c) x = (0 : Tangen
tSpace% x ->L[𝕜] TangentSpace% c)
· 使用定理 `ContinuousLinearMap.inl.eq_1`：∀ (R : Type u_1) [inst : Semiring R] (M₁ :
 Type u_2) [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 
: _root_.Module R …
-/
theorem mfderiv_prod_left {x₀ : M} {y₀ : M'} :
    mfderiv% (fun (x : M) ↦ (x, y₀)) x₀ =
      ContinuousLinearMap.inl 𝕜 (TangentSpace% x₀) (TangentSpace% y₀) := by
  refine (mdifferentiableAt_id.mfderiv_prod mdifferentiableAt_const).trans ?_
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inl]

-- TODO: better error when the type of x is left open
/-
**tangentMap_prod_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMap_prod_left {p : TangentBundle I M} {y₀ : M'} : tangentMap% (fun 
(x : M) => (x, y₀)) p = ⟨(p.1, y₀), (p.2, 0)⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_prod_left`：mfderiv_prod_left {x₀ : M} {y₀ : M'} : mfderiv% (fun 
(x : M) => (x, y₀)) x₀ = ContinuousLinearMap.inl 𝕜 (TangentSpace% x₀) (TangentSp
ace% y₀…
-/
theorem tangentMap_prod_left {p : TangentBundle I M} {y₀ : M'} :
    tangentMap% (fun (x : M) ↦ (x, y₀)) p = ⟨(p.1, y₀), (p.2, 0)⟩ := by
  simp only [tangentMap, mfderiv_prod_left]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**mfderiv_prod_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_prod_right {x₀ : M} {y₀ : M'} : mfderiv% (fun (y : M') => (x₀, y))
 y₀ = ContinuousLinearMap.inr 𝕜 (TangentSpace% x₀) (TangentSpace% y₀)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MDifferentiableAt.mfderiv_prod`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `mdifferentiableAt_const`：mdifferentiableAt_const : MDiffAt (fun _ : M =>
 c) x
· 使用定理 `mdifferentiableAt_id`：mdifferentiableAt_id : MDiffAt (@id M) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_id`：mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (
TangentSpace% x)
· 使用定理 `mfderiv_const`：mfderiv_const : mfderiv% (fun _ : M => c) x = (0 : Tangen
tSpace% x ->L[𝕜] TangentSpace% c)
· 使用定理 `ContinuousLinearMap.inr.eq_1`：∀ (R : Type u_1) [inst : Semiring R] (M₁ :
 Type u_2) [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 
: _root_.Module R …
-/
theorem mfderiv_prod_right {x₀ : M} {y₀ : M'} :
    mfderiv% (fun (y : M') ↦ (x₀, y)) y₀ =
      ContinuousLinearMap.inr 𝕜 (TangentSpace% x₀) (TangentSpace% y₀) := by
  refine (mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_id).trans ?_
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inr]
/-
**tangentMap_prod_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMap_prod_right {p : TangentBundle I' M'} {x₀ : M} : tangentMap% (fu
n (y : M') => (x₀, y)) p = ⟨(x₀, p.1), (0, p.2)⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_prod_right`：mfderiv_prod_right {x₀ : M} {y₀ : M'} : mfderiv% (fu
n (y : M') => (x₀, y)) y₀ = ContinuousLinearMap.inr 𝕜 (TangentSpace% x₀) (Tangen
tSpace% …
-/
theorem tangentMap_prod_right {p : TangentBundle I' M'} {x₀ : M} :
    tangentMap% (fun (y : M') ↦ (x₀, y)) p = ⟨(x₀, p.1), (0, p.2)⟩ := by
  simp only [tangentMap, mfderiv_prod_right]
  rfl

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. -/
/-
**mfderiv_prod_eq_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_prod_eq_add {f : M × M' -> M''} {p : M × M'} (hf : MDiffAt f p) : 
mfderiv% f p = mfderiv% (fun z : M × M' => f (z.1, p.2)) p + mfderiv% (fun z : M
 × M' => f (p.1, z.2)) p
参数：hf : MDiffAt f p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_comp_of_eq`：mfderiv_comp_of_eq {x : M} {y : M'} (hg : MDiffAt g 
y) (hf : MDiffAt f x) (hy : f x = y) : mfderiv% (g ∘ f) x = (mfderiv% g (f x)).c
omp (mfd…
· 使用定理 `MDifferentiableAt.prodMk`：MDifferentiableAt.prodMk {f : M -> M'} {g : M 
-> M''} (hf : MDiffAt f x) (hg : MDiffAt g x) : MDiffAt (fun x => (f x, g x)) x
· 使用定理 `mdifferentiableAt_fst`：mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Pr
od.fst M M') x
· 使用定理 `mdifferentiableAt_const`：mdifferentiableAt_const : MDiffAt (fun _ : M =>
 c) x
· 使用定理 `mdifferentiableAt_snd`：mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Pr
od.snd M M') x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.comp_add`：comp_add [ContinuousAdd M₂] [ContinuousAdd
 M₃] (g : M₂ ->SL[σ₂₃] M₃) (f₁ f₂ : M₁ ->SL[σ₁₂] M₂) : g ∘SL (f₁ + f₂) = g ∘SL f
₁ + g ∘SL f₂
· 使用定理 `MDifferentiableAt.mfderiv_prod`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `mfderiv_fst`：mfderiv_fst {x : M × M'} : mfderiv% (@Prod.fst M M') x = Co
ntinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)
· 使用定理 `mfderiv_snd`：mfderiv_snd {x : M × M'} : mfderiv% (@Prod.snd M M') x = Co
ntinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)
· 使用定理 `mfderiv_const`：mfderiv_const : mfderiv% (fun _ : M => c) x = (0 : Tangen
tSpace% x ->L[𝕜] TangentSpace% c)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `ContinuousLinearMap.coprod_inl_inr`：coprod_inl_inr : ContinuousLinearMap
.coprod (.inl R M N) (.inr R M N) = .id R (M × N)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f

--- 原说明 ---
The total derivative of a function in two variables is the sum of the partial de
rivatives.
  Note that to state this (without casts) we need to be able to see through the 
definition of
  `TangentSpace`.
-/
theorem mfderiv_prod_eq_add {f : M × M' → M''} {p : M × M'}
    (hf : MDiffAt f p) :
    mfderiv% f p =
        mfderiv% (fun z : M × M' ↦ f (z.1, p.2)) p +
        mfderiv% (fun z : M × M' ↦ f (p.1, z.2)) p := by
  erw [mfderiv_comp_of_eq hf (mdifferentiableAt_fst.prodMk mdifferentiableAt_const) rfl,
    mfderiv_comp_of_eq hf (mdifferentiableAt_const.prodMk mdifferentiableAt_snd) rfl,
    ← ContinuousLinearMap.comp_add,
    mdifferentiableAt_fst.mfderiv_prod mdifferentiableAt_const,
    mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_snd, mfderiv_fst,
    mfderiv_snd, mfderiv_const, mfderiv_const]
  symm
  convert! ContinuousLinearMap.comp_id <| mfderiv% f (p.1, p.2)
  exact ContinuousLinearMap.coprod_inl_inr

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. Version in terms of the one-variable derivatives. -/
/-
**mfderiv_prod_eq_add_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_prod_eq_add_comp {f : M × M' -> M''} {p : M × M'} (hf : MDiffAt f 
p) : mfderiv% f p = (mfderiv% (fun z : M => f (z, p.2)) p.1) ∘L (id (ContinuousL
inearMap.fst 𝕜 E E') : (TangentSpace% p) ->L[𝕜] (TangentSpace% p.1)) + (mfderiv%
 (fun z : M' => f (p.1, z)) p.2) ∘L (id (ContinuousLinearMap.snd 𝕜 E E') : (Tang
entSpace% p) ->L[𝕜] (TangentSpace% p.2))
参数：hf : MDiffAt f p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_prod_eq_add`：mfderiv_prod_eq_add {f : M × M' -> M''} {p : M × M'
} (hf : MDiffAt f p) : mfderiv% f p = mfderiv% (fun z : M × M' => f (z.1, p.2)) 
p + mfder…
· 使用定理 `mfderiv_comp`：mfderiv_comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : m
fderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x)
· 使用定理 `MDifferentiableAt.comp`：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (h
f : MDiffAt f x) : MDiffAt (g ∘ f) x
· 使用定理 `MDifferentiableAt.prodMk`：MDifferentiableAt.prodMk {f : M -> M'} {g : M 
-> M''} (hf : MDiffAt f x) (hg : MDiffAt g x) : MDiffAt (fun x => (f x, g x)) x
· 使用定理 `mdifferentiableAt_id`：mdifferentiableAt_id : MDiffAt (@id M) x
· 使用定理 `mdifferentiableAt_const`：mdifferentiableAt_const : MDiffAt (fun _ : M =>
 c) x
· 使用定理 `mdifferentiableAt_fst`：mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Pr
od.fst M M') x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `mfderiv_fst`：mfderiv_fst {x : M × M'} : mfderiv% (@Prod.fst M M') x = Co
ntinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)
· 使用定理 `mdifferentiableAt_snd`：mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Pr
od.snd M M') x
· 使用定理 `mfderiv_snd`：mfderiv_snd {x : M × M'} : mfderiv% (@Prod.snd M M') x = Co
ntinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)

--- 原说明 ---
The total derivative of a function in two variables is the sum of the partial de
rivatives.
  Note that to state this (without casts) we need to be able to see through the 
definition of
  `TangentSpace`. Version in terms of the one-variable derivatives.
-/
theorem mfderiv_prod_eq_add_comp {f : M × M' → M''} {p : M × M'} (hf : MDiffAt f p) :
    mfderiv% f p =
        (mfderiv% (fun z : M ↦ f (z, p.2)) p.1) ∘L (id (ContinuousLinearMap.fst 𝕜 E E') :
          (TangentSpace% p) →L[𝕜] (TangentSpace% p.1)) +
        (mfderiv% (fun z : M' ↦ f (p.1, z)) p.2) ∘L (id (ContinuousLinearMap.snd 𝕜 E E') :
          (TangentSpace% p) →L[𝕜] (TangentSpace% p.2)) := by
  rw [mfderiv_prod_eq_add hf]
  congr
  · have : (fun z : M × M' ↦ f (z.1, p.2)) = (fun z : M ↦ f (z, p.2)) ∘ Prod.fst := rfl
    rw [this, mfderiv_comp (I' := I)]
    · simp only [mfderiv_fst]
      rfl
    · exact hf.comp _ (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    · exact mdifferentiableAt_fst
  · have : (fun z : M × M' ↦ f (p.1, z.2)) = (fun z : M' ↦ f (p.1, z)) ∘ Prod.snd := rfl
    rw [this, mfderiv_comp (I' := I')]
    · simp only [mfderiv_snd]
      rfl
    · exact hf.comp _ (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    · exact mdifferentiableAt_snd

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. Version in terms of the one-variable derivatives. -/
/-
**mfderiv_prod_eq_add_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_prod_eq_add_apply {f : M × M' -> M''} {p : M × M'} {v : TangentSpa
ce% p} (hf : MDiffAt f p) : mfderiv% f p v = mfderiv% (fun z : M => f (z, p.2)) 
p.1 v.1 + mfderiv% (fun z : M' => f (p.1, z)) p.2 v.2
参数：hf : MDiffAt f p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_prod_eq_add_comp`：mfderiv_prod_eq_add_comp {f : M × M' -> M''} {
p : M × M'} (hf : MDiffAt f p) : mfderiv% f p = (mfderiv% (fun z : M => f (z, p.
2)) p.1) ∘L (i…

--- 原说明 ---
The total derivative of a function in two variables is the sum of the partial de
rivatives.
  Note that to state this (without casts) we need to be able to see through the 
definition of
  `TangentSpace`. Version in terms of the one-variable derivatives.
-/
theorem mfderiv_prod_eq_add_apply {f : M × M' → M''} {p : M × M'} {v : TangentSpace% p}
    (hf : MDiffAt f p) :
    mfderiv% f p v =
      mfderiv% (fun z : M ↦ f (z, p.2)) p.1 v.1 + mfderiv% (fun z : M' ↦ f (p.1, z)) p.2 v.2 := by
  rw [mfderiv_prod_eq_add_comp hf]
  rfl

end Prod

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {p : M ⊕ M'}

/-- In extended charts at `p`, `Sum.swap` looks like the identity near `p`. -/
/-
**writtenInExtChartAt_sumSwap_eventuallyEq_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_sumSwap_eventuallyEq_id : writtenInExtChartAt I I p Su
m.swap =ᶠ[𝓝[range I] (I <| chartAt H p p)] id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ChartedSpace.sum_chartAt_inr`：ChartedSpace.sum_chartAt_inr (x' : M') : h
aveI : Nonempty H
· 使用引理 `ChartedSpace.sum_chartAt_inl`：ChartedSpace.sum_chartAt_inl (x : M) : hav
eI : Nonempty H
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `Filter.inter_mem_iff`：inter_mem_iff {s t : Set α} : s inter t in f ↔ s i
n f ∧ t in f
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin`：ContinuousWithinAt.preimage_
mem_nhdsWithin {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝 (f x)) : 
f ⁻¹' t in 𝓝[s] x
· 使用定理 `ModelWithCorners.continuousWithinAt_symm`：continuousWithinAt_symm {s x} 
: ContinuousWithinAt I.symm s x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sum_chartAt_inl_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `sum_chartAt_inr_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…

--- 原说明 ---
In extended charts at `p`, `Sum.swap` looks like the identity near `p`.
-/
lemma writtenInExtChartAt_sumSwap_eventuallyEq_id :
    writtenInExtChartAt I I p Sum.swap =ᶠ[𝓝[range I] (I <| chartAt H p p)] id := by
  cases p with
    | inl x =>
      let t := I.symm ⁻¹' (chartAt H x).target ∩ range I
      have : EqOn (writtenInExtChartAt I I (Sum.inl x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inl,
          ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr]
        dsimp
        rw [Sum.inr_injective.extend_apply, (chartAt H x).right_inv (by grind)]
        exact I.right_inv (by grind)
      apply Filter.eventually_of_mem ?_ this
      rw [Filter.inter_mem_iff]
      refine ⟨I.continuousWithinAt_symm.preimage_mem_nhdsWithin ?_, self_mem_nhdsWithin⟩
      exact (chartAt H x).open_target.mem_nhds (by simp)
    | inr x =>
      let t := I.symm ⁻¹' (chartAt H x).target ∩ range I
      have : EqOn (writtenInExtChartAt I I (Sum.inr x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inr,
          ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr]
        dsimp
        rw [Sum.inl_injective.extend_apply, (chartAt H x).right_inv (by grind)]
        exact I.right_inv (by grind)
      apply Filter.eventually_of_mem ?_ this
      rw [Filter.inter_mem_iff]
      refine ⟨I.continuousWithinAt_symm.preimage_mem_nhdsWithin ?_, self_mem_nhdsWithin⟩
      exact (chartAt H x).open_target.mem_nhds (by simp)
/-
**hasMFDerivAt_sumSwap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivAt_sumSwap : HasMFDerivAt% (@Sum.swap M M') p (ContinuousLinearM
ap.id 𝕜 (TangentSpace% p))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用引理 `continuous_sum_swap`：continuous_sum_swap : Continuous (@Sum.swap X Y)
· 使用定理 `HasFDerivWithinAt.congr_of_eventuallyEq`：HasFDerivWithinAt.congr_of_even
tuallyEq (h : HasFDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : HasFDerivWithinAt f₁ f' …
· 使用定理 `hasFDerivWithinAt_id`：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDer
ivWithinAt id (.id 𝕜 E) s x
· 使用引理 `writtenInExtChartAt_sumSwap_eventuallyEq_id`：writtenInExtChartAt_sumSwap
_eventuallyEq_id : writtenInExtChartAt I I p Sum.swap =ᶠ[𝓝[range I] (I <| chartA
t H p p)] id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sum_chartAt_inr_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…
· 使用定理 `sum_chartAt_inl_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem hasMFDerivAt_sumSwap :
    HasMFDerivAt% (@Sum.swap M M') p (ContinuousLinearMap.id 𝕜 (TangentSpace% p)) := by
  refine ⟨by fun_prop, ?_⟩
  apply (hasFDerivWithinAt_id _ (range I)).congr_of_eventuallyEq
  · exact writtenInExtChartAt_sumSwap_eventuallyEq_id
  · simp only [mfld_simps]
    cases p <;> simp

@[simp]
/-
**mfderivWithin_sumSwap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_sumSwap {s : Set (M oplus M')} (hs : UniqueMDiffAt[s] p) : m
fderiv[s] (@Sum.swap M M') p = ContinuousLinearMap.id 𝕜 (TangentSpace% p)
参数：M oplus M'；hs : UniqueMDiffAt[s] p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
· 使用定理 `hasMFDerivAt_sumSwap`：hasMFDerivAt_sumSwap : HasMFDerivAt% (@Sum.swap M 
M') p (ContinuousLinearMap.id 𝕜 (TangentSpace% p))
-/
theorem mfderivWithin_sumSwap {s : Set (M ⊕ M')} (hs : UniqueMDiffAt[s] p) :
    mfderiv[s] (@Sum.swap M M') p = ContinuousLinearMap.id 𝕜 (TangentSpace% p) :=
  hasMFDerivAt_sumSwap.hasMFDerivWithinAt.mfderivWithin hs

@[simp]
/-
**mfderiv_sumSwap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_sumSwap : mfderiv% (@Sum.swap M M') p = ContinuousLinearMap.id 𝕜 (
TangentSpace% p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `mfderivWithin_sumSwap`：mfderivWithin_sumSwap {s : Set (M oplus M')} (hs 
: UniqueMDiffAt[s] p) : mfderiv[s] (@Sum.swap M M') p = ContinuousLinearMap.id 𝕜
 (TangentSp…
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
-/
theorem mfderiv_sumSwap :
    mfderiv% (@Sum.swap M M') p = ContinuousLinearMap.id 𝕜 (TangentSpace% p) := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumSwap (uniqueMDiffWithinAt_univ I))

variable {f : M → N} (g : M' → N') {q : M} {q' : M'}
/-
**writtenInExtChartAt_sumInl_eventuallyEq_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_sumInl_eventuallyEq_id : (writtenInExtChartAt I I q (@
Sum.inl M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q q)] id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.image_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用引理 `OpenPartialHomeomorph.extend_image_target_mem_nhds`：extend_image_target_
mem_nhds {x : M} (hx : x in f.source) : I '' f.target in 𝓝[range I] (f.extend I)
 x
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用引理 `ChartedSpace.sum_chartAt_inl`：ChartedSpace.sum_chartAt_inl (x : M) : hav
eI : Nonempty H
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma writtenInExtChartAt_sumInl_eventuallyEq_id :
    (writtenInExtChartAt I I q (@Sum.inl M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q q)] id := by
  have hmem : I.symm ⁻¹'
      (chartAt H q).target ∩ Set.range I ∈ 𝓝[Set.range I] (extChartAt I q q) := by
    rw [← I.image_eq (chartAt H q).target]
    exact (chartAt H q).extend_image_target_mem_nhds (mem_chart_source H q)
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
  simp [writtenInExtChartAt, extChartAt, ChartedSpace.sum_chartAt_inl,
    Sum.inl_injective.extend_apply <| chartAt H q,
    (chartAt H q).right_inv (by simpa [Set.mem_preimage, I.left_inv] using hyT)]
/-
**writtenInExtChartAt_sumInr_eventuallyEq_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_sumInr_eventuallyEq_id : (writtenInExtChartAt I I q' (
@Sum.inr M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q' q')] id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.image_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用引理 `OpenPartialHomeomorph.extend_image_target_mem_nhds`：extend_image_target_
mem_nhds {x : M} (hx : x in f.source) : I '' f.target in 𝓝[range I] (f.extend I)
 x
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `nonempty_of_chartedSpace`：nonempty_of_chartedSpace {H : Type*} {M : Type
*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : Nonemp
ty H
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
· 使用引理 `ChartedSpace.sum_chartAt_inr`：ChartedSpace.sum_chartAt_inr (x' : M') : h
aveI : Nonempty H
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma writtenInExtChartAt_sumInr_eventuallyEq_id :
    (writtenInExtChartAt I I q' (@Sum.inr M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q' q')] id := by
  have hmem : I.symm ⁻¹'
      (chartAt H q').target ∩ Set.range I ∈ 𝓝[Set.range I] (extChartAt I q' q') := by
    rw [← I.image_eq (chartAt H q').target]
    exact (chartAt H q').extend_image_target_mem_nhds (mem_chart_source H q')
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
  simp [writtenInExtChartAt, extChartAt, ChartedSpace.sum_chartAt_inr,
    Sum.inr_injective.extend_apply <| chartAt H q',
    (chartAt H q').right_inv (by simpa [Set.mem_preimage, I.left_inv] using hyT)]
/-
**hasMFDerivWithinAt_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_inl : HasMFDerivAt[s] (@Sum.inl M M') q (ContinuousLine
arMap.id 𝕜 (TangentSpace% q))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `continuous_inl`：continuous_inl : Continuous (@inl X Y)
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用引理 `writtenInExtChartAt_sumInl_eventuallyEq_id`：writtenInExtChartAt_sumInl_e
ventuallyEq_id : (writtenInExtChartAt I I q (@Sum.inl M M')) =ᶠ[𝓝[Set.range I] (
extChartAt I q q)] id
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `HasFDerivWithinAt.congr_of_eventuallyEq`：HasFDerivWithinAt.congr_of_even
tuallyEq (h : HasFDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : HasFDerivWithinAt f₁ f' …
· 使用定理 `hasFDerivWithinAt_id`：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDer
ivWithinAt id (.id 𝕜 E) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `sum_chartAt_inl_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasMFDerivWithinAt_inl :
    HasMFDerivAt[s] (@Sum.inl M M') q (ContinuousLinearMap.id 𝕜 (TangentSpace% q)) := by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q (@Sum.inl M M'))
      =ᶠ[𝓝[(extChartAt I q).symm ⁻¹' s ∩ Set.range I] (extChartAt I q q)] id :=
    writtenInExtChartAt_sumInl_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy ↦ hy.2))
  exact (hasFDerivWithinAt_id (extChartAt I q q) _).congr_of_eventuallyEq this
    (by simp [writtenInExtChartAt, extChartAt])

set_option backward.isDefEq.respectTransparency false in
/-
**hasMFDerivAt_inl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivAt_inl : HasMFDerivAt% (@Sum.inl M M') q (ContinuousLinearMap.id
 𝕜 (TangentSpace% p))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasMFDerivWithinAt_inl`：hasMFDerivWithinAt_inl : HasMFDerivAt[s] (@Sum.i
nl M M') q (ContinuousLinearMap.id 𝕜 (TangentSpace% q))
-/
theorem hasMFDerivAt_inl :
    HasMFDerivAt% (@Sum.inl M M') q (ContinuousLinearMap.id 𝕜 (TangentSpace% p)) := by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inl (s := Set.univ)
/-
**hasMFDerivWithinAt_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_inr {t : Set M'} : HasMFDerivAt[t] (@Sum.inr M M') q' (
ContinuousLinearMap.id 𝕜 (TangentSpace% q'))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `continuous_inr`：continuous_inr : Continuous (@inr X Y)
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用引理 `writtenInExtChartAt_sumInr_eventuallyEq_id`：writtenInExtChartAt_sumInr_e
ventuallyEq_id : (writtenInExtChartAt I I q' (@Sum.inr M M')) =ᶠ[𝓝[Set.range I] 
(extChartAt I q' q')] id
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `HasFDerivWithinAt.congr_of_eventuallyEq`：HasFDerivWithinAt.congr_of_even
tuallyEq (h : HasFDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : HasFDerivWithinAt f₁ f' …
· 使用定理 `hasFDerivWithinAt_id`：hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDer
ivWithinAt id (.id 𝕜 E) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `sum_chartAt_inr_apply`：∀ {H : Type u} {M : Type u_2} {M' : Type u_3} [in
st : TopologicalSpace H] [inst_1 : TopologicalSpace M]   [inst_2 : TopologicalSp
ace M'] [cm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasMFDerivWithinAt_inr {t : Set M'} :
    HasMFDerivAt[t] (@Sum.inr M M') q' (ContinuousLinearMap.id 𝕜 (TangentSpace% q')) := by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q' (@Sum.inr M M'))
      =ᶠ[𝓝[(extChartAt I q').symm ⁻¹' t ∩ Set.range I] (extChartAt I q' q')] id :=
    writtenInExtChartAt_sumInr_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy ↦ hy.2))
  exact (hasFDerivWithinAt_id (extChartAt I q' q') _).congr_of_eventuallyEq this
    (by simp [writtenInExtChartAt, extChartAt])

set_option backward.isDefEq.respectTransparency false in
/-
**hasMFDerivAt_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivAt_inr : HasMFDerivAt% (@Sum.inr M M') q' (ContinuousLinearMap.i
d 𝕜 (TangentSpace% p))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasMFDerivWithinAt_inr`：hasMFDerivWithinAt_inr {t : Set M'} : HasMFDeriv
At[t] (@Sum.inr M M') q' (ContinuousLinearMap.id 𝕜 (TangentSpace% q'))
-/
theorem hasMFDerivAt_inr :
    HasMFDerivAt% (@Sum.inr M M') q' (ContinuousLinearMap.id 𝕜 (TangentSpace% p)) := by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inr (t := Set.univ)
/-
**mfderivWithin_sumInl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_sumInl (hU : UniqueMDiffAt[s] q) : mfderiv[s] (@Sum.inl M M'
) q = ContinuousLinearMap.id 𝕜 (TangentSpace% p)
参数：hU : UniqueMDiffAt[s] q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `hasMFDerivWithinAt_inl`：hasMFDerivWithinAt_inl : HasMFDerivAt[s] (@Sum.i
nl M M') q (ContinuousLinearMap.id 𝕜 (TangentSpace% q))
-/
theorem mfderivWithin_sumInl (hU : UniqueMDiffAt[s] q) :
    mfderiv[s] (@Sum.inl M M') q = ContinuousLinearMap.id 𝕜 (TangentSpace% p) :=
  hasMFDerivWithinAt_inl.mfderivWithin hU
/-
**mfderiv_sumInl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_sumInl : mfderiv% (@Sum.inl M M') q = ContinuousLinearMap.id 𝕜 (Ta
ngentSpace% p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `mfderivWithin_sumInl`：mfderivWithin_sumInl (hU : UniqueMDiffAt[s] q) : m
fderiv[s] (@Sum.inl M M') q = ContinuousLinearMap.id 𝕜 (TangentSpace% p)
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
-/
theorem mfderiv_sumInl :
    mfderiv% (@Sum.inl M M') q = ContinuousLinearMap.id 𝕜 (TangentSpace% p) := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInl (uniqueMDiffWithinAt_univ I))
/-
**mfderivWithin_sumInr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_sumInr {t : Set M'} (hU : UniqueMDiffAt[t] q') : mfderiv[t] 
(@Sum.inr M M') q' = ContinuousLinearMap.id 𝕜 (TangentSpace% q')
参数：hU : UniqueMDiffAt[t] q'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `hasMFDerivWithinAt_inr`：hasMFDerivWithinAt_inr {t : Set M'} : HasMFDeriv
At[t] (@Sum.inr M M') q' (ContinuousLinearMap.id 𝕜 (TangentSpace% q'))
-/
theorem mfderivWithin_sumInr {t : Set M'} (hU : UniqueMDiffAt[t] q') :
    mfderiv[t] (@Sum.inr M M') q' = ContinuousLinearMap.id 𝕜 (TangentSpace% q') :=
  hasMFDerivWithinAt_inr.mfderivWithin hU
/-
**mfderiv_sumInr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_sumInr : mfderiv% (@Sum.inr M M') q' = ContinuousLinearMap.id 𝕜 (T
angentSpace% q')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `mfderivWithin_sumInr`：mfderivWithin_sumInr {t : Set M'} (hU : UniqueMDif
fAt[t] q') : mfderiv[t] (@Sum.inr M M') q' = ContinuousLinearMap.id 𝕜 (TangentSp
ace% q')
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
-/
theorem mfderiv_sumInr :
    mfderiv% (@Sum.inr M M') q' = ContinuousLinearMap.id 𝕜 (TangentSpace% q') := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInr (uniqueMDiffWithinAt_univ I))

end disjointUnion

section Arithmetic

/-! #### Arithmetic

Note that in the `HasMFDerivAt` lemmas there is an abuse of the defeq between `E'` and
`TangentSpace 𝓘(𝕜, E') (f z)` (similarly for `g',F',p',q'`). In general this defeq is not
canonical, but in this case (the tangent space of a vector space) it is canonical.
-/

section Group

variable {z : M} {f g : M → E'} {f' g' : TangentSpace% z →L[𝕜] E'}

/-
**HasMFDerivWithinAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.add {s : Set M} (hf : HasMFDerivAt[s] f z f') (hg : Has
MFDerivAt[s] g z g') : HasMFDerivAt[s] (f + g) z (f' + g')
参数：hf : HasMFDerivAt[s] f z f'；hg : HasMFDerivAt[s] g z g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousWithinAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [in
st_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {
f g : X → M}…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.add`：HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f
' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f + g) (f' + g') s
 x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivWithinAt.add {s : Set M}
    (hf : HasMFDerivAt[s] f z f') (hg : HasMFDerivAt[s] g z g') :
    HasMFDerivAt[s] (f + g) z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩
/-
**HasMFDerivAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.add (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g') :
 HasMFDerivAt% (f + g) z (f' + g')
参数：hf : HasMFDerivAt% f z f'；hg : HasMFDerivAt% g z g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 :
 Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : 
X → M}…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.add`：HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f
' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f + g) (f' + g') s
 x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivAt.add (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g') :
    HasMFDerivAt% (f + g) z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩
/-
**MDifferentiableWithinAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.add {s : Set M} (hf : MDiffAt[s] f z) (hg : MDiffA
t[s] g z) : MDiffAt[s] (f + g) z
参数：hf : MDiffAt[s] f z；hg : MDiffAt[s] g z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasMFDerivWithinAt.add`：HasMFDerivWithinAt.add {s : Set M} (hf : HasMFDe
rivAt[s] f z f') (hg : HasMFDerivAt[s] g z g') : HasMFDerivAt[s] (f + g) z (f' +
 g')
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem MDifferentiableWithinAt.add {s : Set M} (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) :
    MDiffAt[s] (f + g) z :=
  (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mdifferentiableWithinAt
/-
**MDifferentiableAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.add (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f +
 g) z
参数：hf : MDiffAt f z；hg : MDiffAt g z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasMFDerivAt.add`：HasMFDerivAt.add (hf : HasMFDerivAt% f z f') (hg : Has
MFDerivAt% g z g') : HasMFDerivAt% (f + g) z (f' + g')
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem MDifferentiableAt.add (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f + g) z :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mdifferentiableAt
/-
**MDifferentiableOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.add {s : Set M} (hf : MDiff[s] f) (hg : MDiff[s] g) : MD
iff[s] (f + g)
参数：hf : MDiff[s] f；hg : MDiff[s] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.add`：MDifferentiableWithinAt.add {s : Set M} (hf
 : MDiffAt[s] f z) (hg : MDiffAt[s] g z) : MDiffAt[s] (f + g) z
-/
theorem MDifferentiableOn.add {s : Set M} (hf : MDiff[s] f) (hg : MDiff[s] g) : MDiff[s] (f + g) :=
  fun x hx ↦ (hf x hx).add (hg x hx)
/-
**MDifferentiable.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.add (hf : MDiff f) (hg : MDiff g) : MDiff (f + g)
参数：hf : MDiff f；hg : MDiff g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.add`：MDifferentiableAt.add (hf : MDiffAt f z) (hg : MD
iffAt g z) : MDiffAt (f + g) z
-/
theorem MDifferentiable.add (hf : MDiff f) (hg : MDiff g) : MDiff (f + g) :=
  fun x ↦ (hf x).add (hg x)

-- TODO: this lemma (and others below) uses the identification of tangent spaces silently
-- Deprecate all these lemmas in favour of a version using `mvfderiv(Within)`
-- Porting note: forcing types using `by exact`
/-
**mfderiv_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_add (hf : MDiffAt f z) (hg : MDiffAt g z) : (mfderiv% (f + g) z : 
TangentSpace% z ->L[𝕜] E') = (by exact mfderiv% f z) + (by exact mfderiv% g z)
参数：hf : MDiffAt f z；hg : MDiffAt g z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasMFDerivAt.add`：HasMFDerivAt.add (hf : HasMFDerivAt% f z f') (hg : Has
MFDerivAt% g z g') : HasMFDerivAt% (f + g) z (f' + g')
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem mfderiv_add (hf : MDiffAt f z) (hg : MDiffAt g z) :
    (mfderiv% (f + g) z : TangentSpace% z →L[𝕜] E') =
      (by exact mfderiv% f z) + (by exact mfderiv% g z) :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv
/-
**mfderivWithin_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_add (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) (hs : Unique
MDiffAt[s] z) : (mfderiv[s] (f + g) z : TangentSpace% z ->L[𝕜] E') = (by exact m
fderiv[s] f z) + (by exact mfderiv[s] g z)
参数：hf : MDiffAt[s] f z；hg : MDiffAt[s] g z；hs : UniqueMDiffAt[s] z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasMFDerivWithinAt.add`：HasMFDerivWithinAt.add {s : Set M} (hf : HasMFDe
rivAt[s] f z f') (hg : HasMFDerivAt[s] g z g') : HasMFDerivAt[s] (f + g) z (f' +
 g')
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem mfderivWithin_add (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
    (hs : UniqueMDiffAt[s] z) :
    (mfderiv[s] (f + g) z : TangentSpace% z →L[𝕜] E') =
      (by exact mfderiv[s] f z) + (by exact mfderiv[s] g z) :=
  (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mfderivWithin hs

section sum
variable {ι : Type} {t : Finset ι} {f : ι → M → E'} {f' : ι → TangentSpace% z →L[𝕜] E'}

/-
**HasMFDerivWithinAt.sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.sum (hf : forall i in t, HasMFDerivAt[s] (f i) z (f' i)
) : HasMFDerivAt[s] (∑ i in t, f i) z (∑ i in t, f' i)
参数：hf : forall i in t, HasMFDerivAt[s] (f i) z (f' i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `hasMFDerivWithinAt_const`：hasMFDerivWithinAt_const (c : M') (s : Set M) 
(x : M) : HasMFDerivAt[s] (fun _ : M => c) x (0 : TangentSpace% x ->L[𝕜] Tangent
Space% c)
-/
lemma HasMFDerivWithinAt.sum (hf : ∀ i ∈ t, HasMFDerivAt[s] (f i) z (f' i)) :
    HasMFDerivAt[s] (∑ i ∈ t, f i) z (∑ i ∈ t, f' i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i s hi IH => grind [HasMFDerivWithinAt.add]

set_option backward.isDefEq.respectTransparency false in
/-
**HasMFDerivAt.sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.sum (hf : forall i in t, HasMFDerivAt% (f i) z (f' i)) : HasM
FDerivAt% (∑ i in t, f i) z (∑ i in t, f' i)
参数：hf : forall i in t, HasMFDerivAt% (f i) z (f' i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `HasMFDerivWithinAt.sum`：HasMFDerivWithinAt.sum (hf : forall i in t, HasM
FDerivAt[s] (f i) z (f' i)) : HasMFDerivAt[s] (∑ i in t, f i) z (∑ i in t, f' i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
lemma HasMFDerivAt.sum (hf : ∀ i ∈ t, HasMFDerivAt% (f i) z (f' i)) :
    HasMFDerivAt% (∑ i ∈ t, f i) z (∑ i ∈ t, f' i) := by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.sum hf
/-
**MDifferentiableWithinAt.sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.sum (hf : forall i in t, MDiffAt[s] (f i) z) : MDi
ffAt[s] (∑ i in t, f i) z
参数：hf : forall i in t, MDiffAt[s] (f i) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `HasMFDerivWithinAt.sum`：HasMFDerivWithinAt.sum (hf : forall i in t, HasM
FDerivAt[s] (f i) z (f' i)) : HasMFDerivAt[s] (∑ i in t, f i) z (∑ i in t, f' i)
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
lemma MDifferentiableWithinAt.sum
    (hf : ∀ i ∈ t, MDiffAt[s] (f i) z) : MDiffAt[s] (∑ i ∈ t, f i) z :=
  (HasMFDerivWithinAt.sum fun i hi ↦ (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt
/-
**MDifferentiableAt.sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.sum (hf : forall i in t, MDiffAt (f i) z) : MDiffAt (∑ i
 in t, f i) z
参数：hf : forall i in t, MDiffAt (f i) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.sum`：MDifferentiableWithinAt.sum (hf : forall i 
in t, MDiffAt[s] (f i) z) : MDiffAt[s] (∑ i in t, f i) z
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
lemma MDifferentiableAt.sum (hf : ∀ i ∈ t, MDiffAt (f i) z) : MDiffAt (∑ i ∈ t, f i) z := by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact .sum hf
/-
**MDifferentiableOn.sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.sum (hf : forall i in t, MDiff[s] (f i)) : MDiff[s] (∑ i
 in t, f i)
参数：hf : forall i in t, MDiff[s] (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.sum`：MDifferentiableWithinAt.sum (hf : forall i 
in t, MDiffAt[s] (f i) z) : MDiffAt[s] (∑ i in t, f i) z
-/
lemma MDifferentiableOn.sum (hf : ∀ i ∈ t, MDiff[s] (f i)) : MDiff[s] (∑ i ∈ t, f i) :=
  fun z hz ↦ .sum fun i hi ↦ hf i hi z hz
/-
**MDifferentiable.sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiable.sum (hf : forall i in t, MDiff (f i)) : MDiff (∑ i in t, f
 i)
参数：hf : forall i in t, MDiff (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableAt.sum`：MDifferentiableAt.sum (hf : forall i in t, MDiffA
t (f i) z) : MDiffAt (∑ i in t, f i) z
-/
lemma MDifferentiable.sum (hf : ∀ i ∈ t, MDiff (f i)) : MDiff (∑ i ∈ t, f i) :=
  fun z ↦ .sum fun i hi ↦ hf i hi z

end sum

/-
**HasMFDerivWithinAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.const_smul (hf : HasMFDerivAt[s] f z f') (a : 𝕜) : HasM
FDerivAt[s] (a • f) z (a • f')
参数：hf : HasMFDerivAt[s] f z f'；a : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousWithinAt.const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α] 
  [inst_3 : Topolog…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.const_smul`：HasFDerivWithinAt.const_smul (h : HasFDeri
vWithinAt f f' s x) (c : R) : HasFDerivWithinAt (c • f) (c • f') s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivWithinAt.const_smul (hf : HasMFDerivAt[s] f z f') (a : 𝕜) :
    HasMFDerivAt[s] (a • f) z (a • f') :=
  ⟨hf.1.const_smul a, hf.2.const_smul a⟩
/-
**HasMFDerivAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.const_smul (hf : HasMFDerivAt% f z f') (s : 𝕜) : HasMFDerivAt
% (s • f) z (s • f')
参数：hf : HasMFDerivAt% f z f'；s : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousAt.const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3} 
[inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   [ins
t_3 : Topolog…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.const_smul`：HasFDerivWithinAt.const_smul (h : HasFDeri
vWithinAt f f' s x) (c : R) : HasFDerivWithinAt (c • f) (c • f') s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivAt.const_smul (hf : HasMFDerivAt% f z f') (s : 𝕜) :
    HasMFDerivAt% (s • f) z (s • f') :=
  ⟨hf.1.const_smul s, hf.2.const_smul s⟩
/-
**MDifferentiableWithinAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.const_smul (hf : MDiffAt[s] f z) (a : 𝕜) : MDiffAt
[s] (a • f) z
参数：hf : MDiffAt[s] f z；a : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasMFDerivWithinAt.const_smul`：HasMFDerivWithinAt.const_smul (hf : HasMF
DerivAt[s] f z f') (a : 𝕜) : HasMFDerivAt[s] (a • f) z (a • f')
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem MDifferentiableWithinAt.const_smul (hf : MDiffAt[s] f z) (a : 𝕜) : MDiffAt[s] (a • f) z :=
  (hf.hasMFDerivWithinAt.const_smul a).mdifferentiableWithinAt
/-
**MDifferentiableAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.const_smul (hf : MDiffAt f z) (s : 𝕜) : MDiffAt (s • f) 
z
参数：hf : MDiffAt f z；s : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasMFDerivAt.const_smul`：HasMFDerivAt.const_smul (hf : HasMFDerivAt% f z
 f') (s : 𝕜) : HasMFDerivAt% (s • f) z (s • f')
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem MDifferentiableAt.const_smul (hf : MDiffAt f z) (s : 𝕜) : MDiffAt (s • f) z :=
  (hf.hasMFDerivAt.const_smul s).mdifferentiableAt
/-
**MDifferentiableOn.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.const_smul (a : 𝕜) (hf : MDiff[s] f) : MDiff[s] (a • f)
参数：a : 𝕜；hf : MDiff[s] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.const_smul`：MDifferentiableWithinAt.const_smul (
hf : MDiffAt[s] f z) (a : 𝕜) : MDiffAt[s] (a • f) z
-/
theorem MDifferentiableOn.const_smul (a : 𝕜) (hf : MDiff[s] f) : MDiff[s] (a • f) :=
  fun x hx ↦ (hf x hx).const_smul a
/-
**MDifferentiable.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.const_smul (s : 𝕜) (hf : MDiff f) : MDiff (s • f)
参数：s : 𝕜；hf : MDiff f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.const_smul`：MDifferentiableAt.const_smul (hf : MDiffAt
 f z) (s : 𝕜) : MDiffAt (s • f) z
-/
theorem MDifferentiable.const_smul (s : 𝕜) (hf : MDiff f) : MDiff (s • f) :=
  fun x ↦ (hf x).const_smul s
/-
**const_smul_mfderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：const_smul_mfderiv (hf : MDiffAt f z) (s : 𝕜) : mfderiv% (s • f) z = s • m
fderiv% f z
参数：hf : MDiffAt f z；s : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasMFDerivAt.const_smul`：HasMFDerivAt.const_smul (hf : HasMFDerivAt% f z
 f') (s : 𝕜) : HasMFDerivAt% (s • f) z (s • f')
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem const_smul_mfderiv (hf : MDiffAt f z) (s : 𝕜) : mfderiv% (s • f) z = s • mfderiv% f z :=
  (hf.hasMFDerivAt.const_smul s).mfderiv
/-
**HasMFDerivWithinAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.neg {s : Set M} (hf : HasMFDerivAt[s] f z f') : HasMFDe
rivAt[s] (-f) z (-f')
参数：hf : HasMFDerivAt[s] f z f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousWithinAt.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {
f : X → G} {…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.neg`：HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f'
 s x) : HasFDerivWithinAt (-f) (-f') s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivWithinAt.neg {s : Set M} (hf : HasMFDerivAt[s] f z f') :
    HasMFDerivAt[s] (-f) z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩
/-
**HasMFDerivAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.neg (hf : HasMFDerivAt% f z f') : HasMFDerivAt% (-f) z (-f')
参数：hf : HasMFDerivAt% f z f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAt.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.neg`：HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f'
 s x) : HasFDerivWithinAt (-f) (-f') s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivAt.neg (hf : HasMFDerivAt% f z f') : HasMFDerivAt% (-f) z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩

set_option backward.isDefEq.respectTransparency false in
/-
**hasMFDerivAt_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivAt_neg : HasMFDerivAt% (-f) z (-f') ↔ HasMFDerivAt% f z f'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `HasMFDerivAt.neg`：HasMFDerivAt.neg (hf : HasMFDerivAt% f z f') : HasMFDe
rivAt% (-f) z (-f')
-/
theorem hasMFDerivAt_neg : HasMFDerivAt% (-f) z (-f') ↔ HasMFDerivAt% f z f' :=
  ⟨fun hf ↦ by convert! hf.neg <;> rw [neg_neg], fun hf ↦ hf.neg⟩
/-
**MDifferentiableWithinAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.neg {s : Set M} (hf : MDiffAt[s] f z) : MDiffAt[s]
 (-f) z
参数：hf : MDiffAt[s] f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasMFDerivWithinAt.neg`：HasMFDerivWithinAt.neg {s : Set M} (hf : HasMFDe
rivAt[s] f z f') : HasMFDerivAt[s] (-f) z (-f')
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem MDifferentiableWithinAt.neg {s : Set M} (hf : MDiffAt[s] f z) : MDiffAt[s] (-f) z :=
  (hf.hasMFDerivWithinAt.neg).mdifferentiableWithinAt
/-
**MDifferentiableAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.neg (hf : MDiffAt f z) : MDiffAt (-f) z
参数：hf : MDiffAt f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasMFDerivAt.neg`：HasMFDerivAt.neg (hf : HasMFDerivAt% f z f') : HasMFDe
rivAt% (-f) z (-f')
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem MDifferentiableAt.neg (hf : MDiffAt f z) : MDiffAt (-f) z :=
  hf.hasMFDerivAt.neg.mdifferentiableAt
/-
**MDifferentiableOn.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.neg {s : Set M} (hf : MDiff[s] f) : MDiff[s] (-f)
参数：hf : MDiff[s] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.neg`：MDifferentiableWithinAt.neg {s : Set M} (hf
 : MDiffAt[s] f z) : MDiffAt[s] (-f) z
-/
theorem MDifferentiableOn.neg {s : Set M} (hf : MDiff[s] f) : MDiff[s] (-f) :=
  fun x hx ↦ (hf x hx).neg
/-
**mdifferentiableWithinAt_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_neg : MDiffAt[s] (-f) z ↔ MDiffAt[s] f z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MDifferentiableWithinAt.neg`：MDifferentiableWithinAt.neg {s : Set M} (hf
 : MDiffAt[s] f z) : MDiffAt[s] (-f) z
-/
theorem mdifferentiableWithinAt_neg : MDiffAt[s] (-f) z ↔ MDiffAt[s] f z :=
  ⟨fun hf ↦ by convert hf.neg; rw [neg_neg], fun hf ↦ hf.neg⟩
/-
**mdifferentiableAt_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_neg : MDiffAt (-f) z ↔ MDiffAt f z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MDifferentiableAt.neg`：MDifferentiableAt.neg (hf : MDiffAt f z) : MDiffA
t (-f) z
-/
theorem mdifferentiableAt_neg : MDiffAt (-f) z ↔ MDiffAt f z :=
  ⟨fun hf ↦ by convert! hf.neg; rw [neg_neg], fun hf ↦ hf.neg⟩
/-
**MDifferentiable.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.neg (hf : MDiff f) : MDiff (-f)
参数：hf : MDiff f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.neg`：MDifferentiableAt.neg (hf : MDiffAt f z) : MDiffA
t (-f) z
-/
theorem MDifferentiable.neg (hf : MDiff f) : MDiff (-f) := fun x ↦ (hf x).neg

set_option backward.isDefEq.respectTransparency false in
/-
**mfderivWithin_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_neg (hs : UniqueMDiffAt[s] x) : mfderiv[s] (-f) x = -mfderiv
[s] f x
参数：hs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasMFDerivWithinAt.neg`：HasMFDerivWithinAt.neg {s : Set M} (hf : HasMFDe
rivAt[s] f z f') : HasMFDerivAt[s] (-f) z (-f')
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableWithinAt_neg`：mdifferentiableWithinAt_neg : MDiffAt[s] (-
f) z ↔ MDiffAt[s] f z
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem mfderivWithin_neg (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] (-f) x = -mfderiv[s] f x := by
  simp_rw [mfderivWithin]
  by_cases hf : MDiffAt[s] f x
  · exact hf.hasMFDerivWithinAt.neg.mfderivWithin hs
  · rw [if_neg hf]; rw [← mdifferentiableWithinAt_neg] at hf; rw [if_neg hf, neg_zero]
/-
**mfderiv_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_neg : mfderiv% (-f) x = -mfderiv% f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `mfderivWithin_neg`：mfderivWithin_neg (hs : UniqueMDiffAt[s] x) : mfderiv
[s] (-f) x = -mfderiv[s] f x
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
-/
theorem mfderiv_neg : mfderiv% (-f) x = -mfderiv% f x := by
  rw [← mfderivWithin_univ, mfderivWithin_neg (uniqueMDiffWithinAt_univ I), mfderivWithin_univ]
/-
**HasMFDerivWithinAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.sub (hf : HasMFDerivAt[s] f z f') (hg : HasMFDerivAt[s]
 g z g') : HasMFDerivAt[s] (f - g) z (f' - g')
参数：hf : HasMFDerivAt[s] f z f'；hg : HasMFDerivAt[s] g z g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousWithinAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {
f g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.sub`：HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f
' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f - g) (f' - g') s
 x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivWithinAt.sub (hf : HasMFDerivAt[s] f z f') (hg : HasMFDerivAt[s] g z g') :
    HasMFDerivAt[s] (f - g) z (f' - g') :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
/-
**HasMFDerivAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.sub (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g') :
 HasMFDerivAt% (f - g) z (f' - g')
参数：hf : HasMFDerivAt% f z f'；hg : HasMFDerivAt% g z g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.sub`：HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f
' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f - g) (f' - g') s
 x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivAt.sub (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g') :
    HasMFDerivAt% (f - g) z (f' - g') :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
/-
**MDifferentiableWithinAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.sub (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) : 
MDiffAt[s] (f - g) z
参数：hf : MDiffAt[s] f z；hg : MDiffAt[s] g z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasMFDerivWithinAt.sub`：HasMFDerivWithinAt.sub (hf : HasMFDerivAt[s] f z
 f') (hg : HasMFDerivAt[s] g z g') : HasMFDerivAt[s] (f - g) z (f' - g')
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem MDifferentiableWithinAt.sub (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) :
    MDiffAt[s] (f - g) z :=
  (hf.hasMFDerivWithinAt.sub hg.hasMFDerivWithinAt).mdifferentiableWithinAt
/-
**MDifferentiableAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.sub (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f -
 g) z
参数：hf : MDiffAt f z；hg : MDiffAt g z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasMFDerivAt.sub`：HasMFDerivAt.sub (hf : HasMFDerivAt% f z f') (hg : Has
MFDerivAt% g z g') : HasMFDerivAt% (f - g) z (f' - g')
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem MDifferentiableAt.sub (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f - g) z :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mdifferentiableAt
/-
**MDifferentiableOn.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.sub (hf : MDiff[s] f) (hg : MDiff[s] g) : MDiff[s] (f - 
g)
参数：hf : MDiff[s] f；hg : MDiff[s] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.sub`：MDifferentiableWithinAt.sub (hf : MDiffAt[s
] f z) (hg : MDiffAt[s] g z) : MDiffAt[s] (f - g) z
-/
theorem MDifferentiableOn.sub (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDiff[s] (f - g) :=
  fun x hx ↦ (hf x hx).sub (hg x hx)
/-
**MDifferentiable.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.sub (hf : MDiff f) (hg : MDiff g) : MDiff (f - g)
参数：hf : MDiff f；hg : MDiff g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.sub`：MDifferentiableAt.sub (hf : MDiffAt f z) (hg : MD
iffAt g z) : MDiffAt (f - g) z
-/
theorem MDifferentiable.sub (hf : MDiff f) (hg : MDiff g) : MDiff (f - g) :=
  fun x ↦ (hf x).sub (hg x)
/-
**mfderivWithin_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_sub (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) (hs : Unique
MDiffAt[s] z) : (mfderiv[s] (f - g) z : TangentSpace% z ->L[𝕜] E') = (by exact m
fderiv[s] f z) - (by exact mfderiv[s] g z)
参数：hf : MDiffAt[s] f z；hg : MDiffAt[s] g z；hs : UniqueMDiffAt[s] z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasMFDerivWithinAt.sub`：HasMFDerivWithinAt.sub (hf : HasMFDerivAt[s] f z
 f') (hg : HasMFDerivAt[s] g z g') : HasMFDerivAt[s] (f - g) z (f' - g')
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem mfderivWithin_sub (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
    (hs : UniqueMDiffAt[s] z) :
    (mfderiv[s] (f - g) z : TangentSpace% z →L[𝕜] E') =
      (by exact mfderiv[s] f z) - (by exact mfderiv[s] g z) :=
  (hf.hasMFDerivWithinAt.sub hg.hasMFDerivWithinAt).mfderivWithin hs
/-
**mfderiv_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_sub (hf : MDiffAt f z) (hg : MDiffAt g z) : (mfderiv% (f - g) z : 
TangentSpace% z ->L[𝕜] E') = (by exact mfderiv% f z) - (by exact mfderiv% g z)
参数：hf : MDiffAt f z；hg : MDiffAt g z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasMFDerivAt.sub`：HasMFDerivAt.sub (hf : HasMFDerivAt% f z f') (hg : Has
MFDerivAt% g z g') : HasMFDerivAt% (f - g) z (f' - g')
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem mfderiv_sub (hf : MDiffAt f z) (hg : MDiffAt g z) :
    (mfderiv% (f - g) z : TangentSpace% z →L[𝕜] E') =
      (by exact mfderiv% f z) - (by exact mfderiv% g z) :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv

end Group

section AlgebraOverRing
open scoped RightActions

variable {z : M} {F' : Type*} [NormedRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace% z →L[𝕜] F'}

/-
**HasMFDerivWithinAt.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hq 
: HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') : HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q
) s z (p z • q' + p' <• q z : E ->L[𝕜] F')
参数：hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p'；hq : HasMFDerivWithinAt I 𝓘(𝕜, F'
) q s z q'。
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
· 使用定理 `ContinuousWithinAt.mul`：ContinuousWithinAt.mul (hf : ContinuousWithinAt 
f s x) (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (f * g) s x
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HasFDerivWithinAt.mul'`：HasFDerivWithinAt.mul' (ha : HasFDerivWithinAt a
 a' s x) (hb : HasFDerivWithinAt b b' s x) : HasFDerivWithinAt (a * b) (a x • b'
 + a' <• b x…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + p' <• q z : E →L[𝕜] F') :=
  ⟨hp.1.mul hq.1, by simpa only [mfld_simps] using! hp.2.mul' hq.2⟩
/-
**HasMFDerivAt.mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.mul' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hq : HasMFDerivAt
 I 𝓘(𝕜, F') q z q') : HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + p' <• q z : 
E ->L[𝕜] F')
参数：hp : HasMFDerivAt I 𝓘(𝕜, F') p z p'；hq : HasMFDerivAt I 𝓘(𝕜, F') q z q'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
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
· 使用定理 `hasMFDerivWithinAt_univ`：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f 
x f' ↔ HasMFDerivAt% f x f'
· 使用定理 `HasMFDerivWithinAt.mul'`：HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinA
t I 𝓘(𝕜, F') p s z p') (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') : HasMFDeri
vWithinAt I 𝓘…
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
-/
theorem HasMFDerivAt.mul' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + p' <• q z : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt
/-
**MDifferentiableWithinAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.mul (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z
) (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) : MDifferentiableWithinAt I 𝓘(
𝕜, F') (p * q) s z
参数：hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z；hq : MDifferentiableWithinAt I 
𝓘(𝕜, F') q s z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
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
· 使用定理 `HasMFDerivWithinAt.mul'`：HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinA
t I 𝓘(𝕜, F') p s z p') (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') : HasMFDeri
vWithinAt I 𝓘…
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem MDifferentiableWithinAt.mul (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (p * q) s z :=
  (hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt).mdifferentiableWithinAt
/-
**MDifferentiableAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (hq : MDiffe
rentiableAt I 𝓘(𝕜, F') q z) : MDifferentiableAt I 𝓘(𝕜, F') (p * q) z
参数：hp : MDifferentiableAt I 𝓘(𝕜, F') p z；hq : MDifferentiableAt I 𝓘(𝕜, F') q z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
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
· 使用定理 `HasMFDerivAt.mul'`：HasMFDerivAt.mul' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p
') (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') : HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p 
z • q' …
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) : MDifferentiableAt I 𝓘(𝕜, F') (p * q) z :=
  (hp.hasMFDerivAt.mul' hq.hasMFDerivAt).mdifferentiableAt
/-
**MDifferentiableOn.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.mul (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (hq : MDiffe
rentiableOn I 𝓘(𝕜, F') q s) : MDifferentiableOn I 𝓘(𝕜, F') (p * q) s
参数：hp : MDifferentiableOn I 𝓘(𝕜, F') p s；hq : MDifferentiableOn I 𝓘(𝕜, F') q s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mul`：MDifferentiableWithinAt.mul (hp : MDifferen
tiableWithinAt I 𝓘(𝕜, F') p s z) (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z)
 : MDifferentiabl…
-/
theorem MDifferentiableOn.mul (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) : MDifferentiableOn I 𝓘(𝕜, F') (p * q) s :=
  fun x hx ↦ (hp x hx).mul <| hq x hx
/-
**MDifferentiable.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.mul (hp : MDifferentiable I 𝓘(𝕜, F') p) (hq : MDifferentia
ble I 𝓘(𝕜, F') q) : MDifferentiable I 𝓘(𝕜, F') (p * q)
参数：hp : MDifferentiable I 𝓘(𝕜, F') p；hq : MDifferentiable I 𝓘(𝕜, F') q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mul`：MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘
(𝕜, F') p z) (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) : MDifferentiableAt I 𝓘(𝕜, 
F') (p * q)…
-/
theorem MDifferentiable.mul (hp : MDifferentiable I 𝓘(𝕜, F') p)
    (hq : MDifferentiable I 𝓘(𝕜, F') q) : MDifferentiable I 𝓘(𝕜, F') (p * q) :=
  fun x ↦ (hp x).mul (hq x)
/-
**MDifferentiableWithinAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.pow (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z
) (n : Nat) : MDifferentiableWithinAt I 𝓘(𝕜, F') (p ^ n) s z
参数：hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mdifferentiableWithinAt_const`：mdifferentiableWithinAt_const : MDiffAt[s
] (fun _ : M => c) x
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `MDifferentiableWithinAt.mul`：MDifferentiableWithinAt.mul (hp : MDifferen
tiableWithinAt I 𝓘(𝕜, F') p s z) (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z)
 : MDifferentiabl…
-/
theorem MDifferentiableWithinAt.pow (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (n : ℕ) : MDifferentiableWithinAt I 𝓘(𝕜, F') (p ^ n) s z := by
  induction n with
  | zero => simpa [pow_zero] using! mdifferentiableWithinAt_const
  | succ n hn => simpa [pow_succ] using! hn.mul hp
/-
**MDifferentiableAt.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.pow (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (n : Nat) : 
MDifferentiableAt I 𝓘(𝕜, F') (p ^ n) z
参数：hp : MDifferentiableAt I 𝓘(𝕜, F') p z；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用定理 `MDifferentiableWithinAt.pow`：MDifferentiableWithinAt.pow (hp : MDifferen
tiableWithinAt I 𝓘(𝕜, F') p s z) (n : Nat) : MDifferentiableWithinAt I 𝓘(𝕜, F') 
(p ^ n) s z
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
-/
theorem MDifferentiableAt.pow (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (n : ℕ) :
    MDifferentiableAt I 𝓘(𝕜, F') (p ^ n) z :=
  mdifferentiableWithinAt_univ.mp (hp.mdifferentiableWithinAt.pow n)
/-
**MDifferentiableOn.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.pow (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (n : Nat) : 
MDifferentiableOn I 𝓘(𝕜, F') (p ^ n) s
参数：hp : MDifferentiableOn I 𝓘(𝕜, F') p s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.pow`：MDifferentiableWithinAt.pow (hp : MDifferen
tiableWithinAt I 𝓘(𝕜, F') p s z) (n : Nat) : MDifferentiableWithinAt I 𝓘(𝕜, F') 
(p ^ n) s z
-/
theorem MDifferentiableOn.pow (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (n : ℕ) :
    MDifferentiableOn I 𝓘(𝕜, F') (p ^ n) s := fun x hx ↦ (hp x hx).pow n
/-
**MDifferentiable.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.pow (hp : MDifferentiable I 𝓘(𝕜, F') p) (n : Nat) : MDiffe
rentiable I 𝓘(𝕜, F') (p ^ n)
参数：hp : MDifferentiable I 𝓘(𝕜, F') p；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.pow`：MDifferentiableAt.pow (hp : MDifferentiableAt I 𝓘
(𝕜, F') p z) (n : Nat) : MDifferentiableAt I 𝓘(𝕜, F') (p ^ n) z
-/
theorem MDifferentiable.pow (hp : MDifferentiable I 𝓘(𝕜, F') p) (n : ℕ) :
    MDifferentiable I 𝓘(𝕜, F') (p ^ n) := fun x ↦ (hp x).pow n

end AlgebraOverRing

section AlgebraOverCommRing

variable {z : M} {F' : Type*} [NormedCommRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace% z →L[𝕜] F'}

set_option backward.isDefEq.respectTransparency false in
/-
**HasMFDerivWithinAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.mul (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hq :
 HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') : HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q)
 s z (p z • q' + q z • p' : E ->L[𝕜] F')
参数：hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p'；hq : HasMFDerivWithinAt I 𝓘(𝕜, F'
) q s z q'。
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
· 使用定理 `HasMFDerivWithinAt.mul'`：HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinA
t I 𝓘(𝕜, F') p s z p') (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') : HasMFDeri
vWithinAt I 𝓘…
-/
theorem HasMFDerivWithinAt.mul (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + q z • p' : E →L[𝕜] F') := by
  convert! hp.mul' hq; ext _; apply mul_comm
/-
**HasMFDerivAt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.mul (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hq : HasMFDerivAt 
I 𝓘(𝕜, F') q z q') : HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + q z • p' : E 
->L[𝕜] F')
参数：hp : HasMFDerivAt I 𝓘(𝕜, F') p z p'；hq : HasMFDerivAt I 𝓘(𝕜, F') q z q'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
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
· 使用定理 `hasMFDerivWithinAt_univ`：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f 
x f' ↔ HasMFDerivAt% f x f'
· 使用定理 `HasMFDerivWithinAt.mul`：HasMFDerivWithinAt.mul (hp : HasMFDerivWithinAt 
I 𝓘(𝕜, F') p s z p') (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') : HasMFDerivW
ithinAt I 𝓘(…
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
-/
theorem HasMFDerivAt.mul (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + q z • p' : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul hq.hasMFDerivWithinAt

section prod
variable {ι : Type} {t : Finset ι} {f : ι → M → F'} {f' : ι → TangentSpace% z →L[𝕜] F'}

set_option backward.isDefEq.respectTransparency false in
/-
**HasMFDerivWithinAt.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.prod [DecidableEq ι] (hf : forall i in t, HasMFDerivWit
hinAt I 𝓘(𝕜, F') (f i) s z (f' i)) : HasMFDerivWithinAt I 𝓘(𝕜, F') (∏ i in t, f 
i) s z (∑ i in t, (∏ j in t.erase i, f j z) • (f' i))
参数：hf : forall i in t, HasMFDerivWithinAt I 𝓘(𝕜, F') (f i) s z (f' i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `hasMFDerivWithinAt_const`：hasMFDerivWithinAt_const (c : M') (s : Set M) 
(x : M) : HasMFDerivAt[s] (fun _ : M => c) x (0 : TangentSpace% x ->L[𝕜] Tangent
Space% c)
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.erase_insert_of_ne`：erase_insert_of_ne {a b : α} {s : Finset α} (
h : a != b) : (insert a s).erase b = insert a (s.erase b)
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 34 条，此处仅展示前 30 条）
-/
lemma HasMFDerivWithinAt.prod [DecidableEq ι]
    (hf : ∀ i ∈ t, HasMFDerivWithinAt I 𝓘(𝕜, F') (f i) s z (f' i)) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) s z
      (∑ i ∈ t, (∏ j ∈ t.erase i, f j z) • (f' i)) := by
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i t hi IH =>
    rw [t.sum_insert hi, t.erase_insert hi, t.prod_insert hi, add_comm]
    rw [t.forall_mem_insert] at hf
    convert! hf.1.mul (IH hf.2) using 2
    · simp only [t.smul_sum, ← mul_smul]
      refine t.sum_congr rfl (fun j hj ↦ ?_)
      rw [t.erase_insert_of_ne (by grind), Finset.prod_insert (by grind)]
    · simp

set_option backward.isDefEq.respectTransparency false in
/-
**HasMFDerivAt.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.prod [DecidableEq ι] (hf : forall i in t, HasMFDerivAt I 𝓘(𝕜,
 F') (f i) z (f' i)) : HasMFDerivAt I 𝓘(𝕜, F') (∏ i in t, f i) z (∑ i in t, (∏ j
 in t.erase i, f j z) • (f' i))
参数：hf : forall i in t, HasMFDerivAt I 𝓘(𝕜, F') (f i) z (f' i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
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
· 使用引理 `HasMFDerivWithinAt.prod`：HasMFDerivWithinAt.prod [DecidableEq ι] (hf : f
orall i in t, HasMFDerivWithinAt I 𝓘(𝕜, F') (f i) s z (f' i)) : HasMFDerivWithin
At I 𝓘(𝕜, F')…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
lemma HasMFDerivAt.prod [DecidableEq ι]
    (hf : ∀ i ∈ t, HasMFDerivAt I 𝓘(𝕜, F') (f i) z (f' i)) :
    HasMFDerivAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) z (∑ i ∈ t, (∏ j ∈ t.erase i, f j z) • (f' i)) := by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.prod hf
/-
**MDifferentiableWithinAt.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.prod (hf : forall i in t, MDifferentiableWithinAt 
I 𝓘(𝕜, F') (f i) s z) : MDifferentiableWithinAt I 𝓘(𝕜, F') (∏ i in t, f i) s z
参数：hf : forall i in t, MDifferentiableWithinAt I 𝓘(𝕜, F') (f i) s z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
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
· 使用引理 `HasMFDerivWithinAt.prod`：HasMFDerivWithinAt.prod [DecidableEq ι] (hf : f
orall i in t, HasMFDerivWithinAt I 𝓘(𝕜, F') (f i) s z (f' i)) : HasMFDerivWithin
At I 𝓘(𝕜, F')…
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
lemma MDifferentiableWithinAt.prod
    (hf : ∀ i ∈ t, MDifferentiableWithinAt I 𝓘(𝕜, F') (f i) s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) s z := by
  -- `by classical exact` to avoid needing a `DecidableEq` argument
  classical exact (HasMFDerivWithinAt.prod
    fun i hi ↦ (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt
/-
**MDifferentiableAt.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.prod (hf : forall i in t, MDifferentiableAt I 𝓘(𝕜, F') (
f i) z) : MDifferentiableAt I 𝓘(𝕜, F') (∏ i in t, f i) z
参数：hf : forall i in t, MDifferentiableAt I 𝓘(𝕜, F') (f i) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.prod`：MDifferentiableWithinAt.prod (hf : forall 
i in t, MDifferentiableWithinAt I 𝓘(𝕜, F') (f i) s z) : MDifferentiableWithinAt 
I 𝓘(𝕜, F') (∏ i in…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
lemma MDifferentiableAt.prod (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, F') (f i) z) :
    MDifferentiableAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) z := by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact MDifferentiableWithinAt.prod hf
/-
**MDifferentiableOn.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.prod (hf : forall i in t, MDifferentiableOn I 𝓘(𝕜, F') (
f i) s) : MDifferentiableOn I 𝓘(𝕜, F') (∏ i in t, f i) s
参数：hf : forall i in t, MDifferentiableOn I 𝓘(𝕜, F') (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.prod`：MDifferentiableWithinAt.prod (hf : forall 
i in t, MDifferentiableWithinAt I 𝓘(𝕜, F') (f i) s z) : MDifferentiableWithinAt 
I 𝓘(𝕜, F') (∏ i in…
-/
lemma MDifferentiableOn.prod (hf : ∀ i ∈ t, MDifferentiableOn I 𝓘(𝕜, F') (f i) s) :
    MDifferentiableOn I 𝓘(𝕜, F') (∏ i ∈ t, f i) s :=
  fun z hz ↦ .prod fun i hi ↦ hf i hi z hz
/-
**MDifferentiable.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiable.prod (hf : forall i in t, MDifferentiable I 𝓘(𝕜, F') (f i)
) : MDifferentiable I 𝓘(𝕜, F') (∏ i in t, f i)
参数：hf : forall i in t, MDifferentiable I 𝓘(𝕜, F') (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableAt.prod`：MDifferentiableAt.prod (hf : forall i in t, MDif
ferentiableAt I 𝓘(𝕜, F') (f i) z) : MDifferentiableAt I 𝓘(𝕜, F') (∏ i in t, f i)
 z
-/
lemma MDifferentiable.prod (hf : ∀ i ∈ t, MDifferentiable I 𝓘(𝕜, F') (f i)) :
    MDifferentiable I 𝓘(𝕜, F') (∏ i ∈ t, f i) :=
  fun z ↦ .prod fun i hi ↦ hf i hi z

end prod

end AlgebraOverCommRing

section DivisionRing
open scoped RightActions

variable {z : M} {F' : Type*} [NormedDivisionRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace% z →L[𝕜] F'}

/-
**HasMFDerivWithinAt.inv'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.inv' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hp_
ne : p z != 0) : HasMFDerivWithinAt I 𝓘(𝕜, F') (p⁻¹) s z (-((p z)⁻¹ •> p' <• (p 
z)⁻¹) : E ->L[𝕜] F')
参数：hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p'；hp_ne : p z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.comp_hasMFDerivWithinAt`：HasMFDerivAt.comp_hasMFDerivWithin
At (hg : HasMFDerivAt% g (f x) g') (hf : HasMFDerivAt[s] f x f') : HasMFDerivAt[
s] (g ∘ f) x (g'.comp f')
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
· 使用定理 `HasFDerivAt.hasMFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {E' : Type u…
· 使用定理 `hasFDerivAt_inv'`：hasFDerivAt_inv' {x : R} (hx : x != 0) : HasFDerivAt I
nv.inv (-mulLeftRight 𝕜 R x⁻¹ x⁻¹) x
-/
lemma HasMFDerivWithinAt.inv' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hp_ne : p z ≠ 0) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p⁻¹) s z (-((p z)⁻¹ •> p' <• (p z)⁻¹) : E →L[𝕜] F') :=
  (hasFDerivAt_inv' hp_ne).hasMFDerivAt.comp_hasMFDerivWithinAt (hf := hp)
/-
**HasMFDerivAt.inv'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.inv' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hp_ne : p z != 0)
 : HasMFDerivAt I 𝓘(𝕜, F') (p⁻¹) z (-((p z)⁻¹ •> p' <• (p z)⁻¹) : E ->L[𝕜] F')
参数：hp : HasMFDerivAt I 𝓘(𝕜, F') p z p'；hp_ne : p z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `hasMFDerivWithinAt_univ`：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f 
x f' ↔ HasMFDerivAt% f x f'
· 使用引理 `HasMFDerivWithinAt.inv'`：HasMFDerivWithinAt.inv' (hp : HasMFDerivWithinA
t I 𝓘(𝕜, F') p s z p') (hp_ne : p z != 0) : HasMFDerivWithinAt I 𝓘(𝕜, F') (p⁻¹) 
s z (-((p z)⁻…
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
-/
lemma HasMFDerivAt.inv' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hp_ne : p z ≠ 0) :
    HasMFDerivAt I 𝓘(𝕜, F') (p⁻¹) z (-((p z)⁻¹ •> p' <• (p z)⁻¹) : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.inv' hp_ne
/-
**MDifferentiableWithinAt.inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.inv (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z
) (hp_ne : p z != 0) : MDifferentiableWithinAt I 𝓘(𝕜, F') p⁻¹ s z
参数：hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z；hp_ne : p z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `HasMFDerivWithinAt.inv'`：HasMFDerivWithinAt.inv' (hp : HasMFDerivWithinA
t I 𝓘(𝕜, F') p s z p') (hp_ne : p z != 0) : HasMFDerivWithinAt I 𝓘(𝕜, F') (p⁻¹) 
s z (-((p z)⁻…
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
lemma MDifferentiableWithinAt.inv (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hp_ne : p z ≠ 0) : MDifferentiableWithinAt I 𝓘(𝕜, F') p⁻¹ s z :=
  (hp.hasMFDerivWithinAt.inv' hp_ne).mdifferentiableWithinAt
/-
**MDifferentiableAt.inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.inv (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (hp_ne : p z
 != 0) : MDifferentiableAt I 𝓘(𝕜, F') p⁻¹ z
参数：hp : MDifferentiableAt I 𝓘(𝕜, F') p z；hp_ne : p z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用引理 `MDifferentiableWithinAt.inv`：MDifferentiableWithinAt.inv (hp : MDifferen
tiableWithinAt I 𝓘(𝕜, F') p s z) (hp_ne : p z != 0) : MDifferentiableWithinAt I 
𝓘(𝕜, F') p⁻¹ s z
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
-/
lemma MDifferentiableAt.inv (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (hp_ne : p z ≠ 0) :
    MDifferentiableAt I 𝓘(𝕜, F') p⁻¹ z :=
  mdifferentiableWithinAt_univ.mp <| hp.mdifferentiableWithinAt.inv hp_ne
/-
**MDifferentiableOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.inv (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (hp_ne : for
all z in s, p z != 0) : MDifferentiableOn I 𝓘(𝕜, F') p⁻¹ s
参数：hp : MDifferentiableOn I 𝓘(𝕜, F') p s；hp_ne : forall z in s, p z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableWithinAt.inv`：MDifferentiableWithinAt.inv (hp : MDifferen
tiableWithinAt I 𝓘(𝕜, F') p s z) (hp_ne : p z != 0) : MDifferentiableWithinAt I 
𝓘(𝕜, F') p⁻¹ s z
-/
theorem MDifferentiableOn.inv (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (hp_ne : ∀ z ∈ s, p z ≠ 0) :
    MDifferentiableOn I 𝓘(𝕜, F') p⁻¹ s :=
  fun x hx ↦ (hp x hx).inv (hp_ne x hx)
/-
**MDifferentiable.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.inv (hp : MDifferentiable I 𝓘(𝕜, F') p) (hp_ne : forall z,
 p z != 0) : MDifferentiable I 𝓘(𝕜, F') p⁻¹
参数：hp : MDifferentiable I 𝓘(𝕜, F') p；hp_ne : forall z, p z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MDifferentiableAt.inv`：MDifferentiableAt.inv (hp : MDifferentiableAt I 𝓘
(𝕜, F') p z) (hp_ne : p z != 0) : MDifferentiableAt I 𝓘(𝕜, F') p⁻¹ z
-/
theorem MDifferentiable.inv (hp : MDifferentiable I 𝓘(𝕜, F') p) (hp_ne : ∀ z, p z ≠ 0) :
    MDifferentiable I 𝓘(𝕜, F') p⁻¹ :=
  fun x ↦ (hp x).inv (hp_ne x)
/-
**MDifferentiableWithinAt.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.div (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z
) (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) (hq_ne : q z != 0) : MDifferen
tiableWithinAt I 𝓘(𝕜, F') (p / q) s z
参数：hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z；hq : MDifferentiableWithinAt I 
𝓘(𝕜, F') q s z；hq_ne : q z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MDifferentiableWithinAt.mul`：MDifferentiableWithinAt.mul (hp : MDifferen
tiableWithinAt I 𝓘(𝕜, F') p s z) (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z)
 : MDifferentiabl…
· 使用引理 `MDifferentiableWithinAt.inv`：MDifferentiableWithinAt.inv (hp : MDifferen
tiableWithinAt I 𝓘(𝕜, F') p s z) (hp_ne : p z != 0) : MDifferentiableWithinAt I 
𝓘(𝕜, F') p⁻¹ s z
-/
lemma MDifferentiableWithinAt.div (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) (hq_ne : q z ≠ 0) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (p / q) s z := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)
/-
**MDifferentiableAt.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.div (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (hq : MDiffe
rentiableAt I 𝓘(𝕜, F') q z) (hq_ne : q z != 0) : MDifferentiableAt I 𝓘(𝕜, F') (p
 / q) z
参数：hp : MDifferentiableAt I 𝓘(𝕜, F') p z；hq : MDifferentiableAt I 𝓘(𝕜, F') q z；h
q_ne : q z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MDifferentiableAt.mul`：MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘
(𝕜, F') p z) (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) : MDifferentiableAt I 𝓘(𝕜, 
F') (p * q)…
· 使用引理 `MDifferentiableAt.inv`：MDifferentiableAt.inv (hp : MDifferentiableAt I 𝓘
(𝕜, F') p z) (hp_ne : p z != 0) : MDifferentiableAt I 𝓘(𝕜, F') p⁻¹ z
-/
lemma MDifferentiableAt.div (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) (hq_ne : q z ≠ 0) :
    MDifferentiableAt I 𝓘(𝕜, F') (p / q) z := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)
/-
**MDifferentiableOn.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.div (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (hq : MDiffe
rentiableOn I 𝓘(𝕜, F') q s) (hq_ne : forall z in s, q z != 0) : MDifferentiableO
n I 𝓘(𝕜, F') (p / q) s
参数：hp : MDifferentiableOn I 𝓘(𝕜, F') p s；hq : MDifferentiableOn I 𝓘(𝕜, F') q s；h
q_ne : forall z in s, q z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MDifferentiableOn.mul`：MDifferentiableOn.mul (hp : MDifferentiableOn I 𝓘
(𝕜, F') p s) (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) : MDifferentiableOn I 𝓘(𝕜, 
F') (p * q)…
· 使用定理 `MDifferentiableOn.inv`：MDifferentiableOn.inv (hp : MDifferentiableOn I 𝓘
(𝕜, F') p s) (hp_ne : forall z in s, p z != 0) : MDifferentiableOn I 𝓘(𝕜, F') p⁻
¹ s
-/
lemma MDifferentiableOn.div (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) (hq_ne : ∀ z ∈ s, q z ≠ 0) :
    MDifferentiableOn I 𝓘(𝕜, F') (p / q) s := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)
/-
**MDifferentiable.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiable.div (hp : MDifferentiable I 𝓘(𝕜, F') p) (hq : MDifferentia
ble I 𝓘(𝕜, F') q) (hq_ne : forall z, q z != 0) : MDifferentiable I 𝓘(𝕜, F') (p /
 q)
参数：hp : MDifferentiable I 𝓘(𝕜, F') p；hq : MDifferentiable I 𝓘(𝕜, F') q；hq_ne : f
orall z, q z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MDifferentiable.mul`：MDifferentiable.mul (hp : MDifferentiable I 𝓘(𝕜, F'
) p) (hq : MDifferentiable I 𝓘(𝕜, F') q) : MDifferentiable I 𝓘(𝕜, F') (p * q)
· 使用定理 `MDifferentiable.inv`：MDifferentiable.inv (hp : MDifferentiable I 𝓘(𝕜, F'
) p) (hp_ne : forall z, p z != 0) : MDifferentiable I 𝓘(𝕜, F') p⁻¹
-/
lemma MDifferentiable.div (hp : MDifferentiable I 𝓘(𝕜, F') p)
    (hq : MDifferentiable I 𝓘(𝕜, F') q) (hq_ne : ∀ z, q z ≠ 0) :
    MDifferentiable I 𝓘(𝕜, F') (p / q) := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

end DivisionRing

section Field

variable {z : M} {F' : Type*} [NormedField F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace% z →L[𝕜] F'}

set_option backward.isDefEq.respectTransparency.types false in
/-
**HasMFDerivWithinAt.inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.inv (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hp_n
e : p z != 0) : HasMFDerivWithinAt I 𝓘(𝕜, F') (p⁻¹) s z (-(p z ^ 2)⁻¹ • p' : E -
>L[𝕜] F')
参数：hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p'；hp_ne : p z != 0。
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
（共 56 条，此处仅展示前 30 条）
-/
lemma HasMFDerivWithinAt.inv (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hp_ne : p z ≠ 0) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p⁻¹) s z (-(p z ^ 2)⁻¹ • p' : E →L[𝕜] F') := by
  convert! hp.inv' hp_ne
  ext
  simp
  ring_nf
/-
**HasMFDerivAt.inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.inv (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hp_ne : p z != 0) 
: HasMFDerivAt I 𝓘(𝕜, F') (p⁻¹) z (-(p z ^ 2)⁻¹ • p' : E ->L[𝕜] F')
参数：hp : HasMFDerivAt I 𝓘(𝕜, F') p z p'；hp_ne : p z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `hasMFDerivWithinAt_univ`：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f 
x f' ↔ HasMFDerivAt% f x f'
· 使用引理 `HasMFDerivWithinAt.inv`：HasMFDerivWithinAt.inv (hp : HasMFDerivWithinAt 
I 𝓘(𝕜, F') p s z p') (hp_ne : p z != 0) : HasMFDerivWithinAt I 𝓘(𝕜, F') (p⁻¹) s 
z (-(p z ^ 2…
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
-/
lemma HasMFDerivAt.inv (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hp_ne : p z ≠ 0) :
    HasMFDerivAt I 𝓘(𝕜, F') (p⁻¹) z (-(p z ^ 2)⁻¹ • p' : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.inv hp_ne

set_option backward.isDefEq.respectTransparency.types false in
/-
**HasMFDerivWithinAt.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.div (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hq :
 HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') (hq_ne : q z != 0) : HasMFDerivWithinAt
 I 𝓘(𝕜, F') (p / q) s z ((1 / q z) • p' - (p z / q z ^ 2) • q' : E ->L[𝕜] F')
参数：hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p'；hq : HasMFDerivWithinAt I 𝓘(𝕜, F'
) q s z q'；hq_ne : q z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 69 条，此处仅展示前 30 条）
-/
lemma HasMFDerivWithinAt.div (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') (hq_ne : q z ≠ 0) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p / q) s z
      ((1 / q z) • p' - (p z / q z ^ 2) • q' : E →L[𝕜] F') := by
  convert! hp.mul (hq.inv hq_ne) using 1
  · simp [div_eq_mul_inv]
  · ext
    simp [div_eq_mul_inv]
    ring
/-
**HasMFDerivAt.div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.div (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hq : HasMFDerivAt 
I 𝓘(𝕜, F') q z q') (hq_ne : q z != 0) : HasMFDerivAt I 𝓘(𝕜, F') (p / q) z ((1 / 
q z) • p' - (p z / q z ^ 2) • q' : E ->L[𝕜] F')
参数：hp : HasMFDerivAt I 𝓘(𝕜, F') p z p'；hq : HasMFDerivAt I 𝓘(𝕜, F') q z q'；hq_ne
 : q z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `hasMFDerivWithinAt_univ`：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f 
x f' ↔ HasMFDerivAt% f x f'
· 使用引理 `HasMFDerivWithinAt.div`：HasMFDerivWithinAt.div (hp : HasMFDerivWithinAt 
I 𝓘(𝕜, F') p s z p') (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') (hq_ne : q z 
!= 0) : HasM…
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
-/
lemma HasMFDerivAt.div (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') (hq_ne : q z ≠ 0) :
    HasMFDerivAt I 𝓘(𝕜, F') (p / q) z
      ((1 / q z) • p' - (p z / q z ^ 2) • q' : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.div hq.hasMFDerivWithinAt hq_ne

end Field

end Arithmetic

end SpecificFunctions

