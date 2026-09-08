/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# The derivative of a linear equivalence

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
continuous linear equivalences.

We also prove the usual formula for the derivative of the inverse function, assuming it exists.
The inverse function theorem is in `Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`.
-/

public section

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f : E → F} {f' : E →L[𝕜] F} {x : E} {s : Set E} {c : F}

namespace ContinuousLinearEquiv

/-! ### Differentiability of linear equivs, and invariance of differentiability -/


variable (iso : E ≃L[𝕜] F)

@[fun_prop]
/-
**ContinuousLinearEquiv.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   (iso : E ≃L[𝕜] F), Has
StrictFDerivAt (⇑iso) (↑iso) x
参数：iso : E ≃L[𝕜] F；⇑iso；↑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem hasStrictFDerivAt : HasStrictFDerivAt iso (iso : E →L[𝕜] F) x :=
  iso.toContinuousLinearMap.hasStrictFDerivAt

@[fun_prop]
/-
**ContinuousLinearEquiv.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   {s : Set E} (iso : E ≃
L[𝕜] F), HasFDerivWithinAt (⇑iso) (↑iso) s x
参数：iso : E ≃L[𝕜] F；⇑iso；↑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem hasFDerivWithinAt : HasFDerivWithinAt iso (iso : E →L[𝕜] F) s x :=
  iso.toContinuousLinearMap.hasFDerivWithinAt

@[fun_prop]
/-
**ContinuousLinearEquiv.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearE
quiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   (iso : E ≃L[𝕜] F), Has
FDerivAt (⇑iso) (↑iso) x
参数：iso : E ≃L[𝕜] F；⇑iso；↑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.hasFDerivAtFilter`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
-/
protected theorem hasFDerivAt : HasFDerivAt iso (iso : E →L[𝕜] F) x :=
  iso.toContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]
/-
**ContinuousLinearEquiv.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   (iso : E ≃L[𝕜] F), Dif
ferentiableAt 𝕜 (⇑iso) x
参数：iso : E ≃L[𝕜] F；⇑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `ContinuousLinearEquiv.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
-/
protected theorem differentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.hasFDerivAt.differentiableAt

@[fun_prop]
/-
**ContinuousLinearEquiv.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   {s : Set E} (iso : E ≃
L[𝕜] F), DifferentiableWithinAt 𝕜 (⇑iso) s x
参数：iso : E ≃L[𝕜] F；⇑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `ContinuousLinearEquiv.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.differentiableAt.differentiableWithinAt
/-
**ContinuousLinearEquiv.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv`
。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   (iso : E ≃L[𝕜] F), fde
riv 𝕜 (⇑iso) x = ↑iso
参数：iso : E ≃L[𝕜] F；⇑iso。
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
· 使用定理 `ContinuousLinearEquiv.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
-/
protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.hasFDerivAt.fderiv
/-
**ContinuousLinearEquiv.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Equiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   {s : Set E} (iso : E ≃
L[𝕜] F), UniqueDiffWithinAt 𝕜 s x → fderivWithin 𝕜 (⇑iso) s x = ↑iso
参数：iso : E ≃L[𝕜] F；⇑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module
 𝕜 E] [inst_3 : Topolo…
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
-/
protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  iso.toContinuousLinearMap.fderivWithin hxs

@[fun_prop]
/-
**ContinuousLinearEquiv.differentiable** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   (iso : E ≃L[𝕜] F), Differentia
ble 𝕜 ⇑iso
参数：iso : E ≃L[𝕜] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem differentiable : Differentiable 𝕜 iso := fun _ => iso.differentiableAt

@[fun_prop]
/-
**ContinuousLinearEquiv.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {s : Set E}   (iso : E ≃L[𝕜] F),
 DifferentiableOn 𝕜 (⇑iso) s
参数：iso : E ≃L[𝕜] F；⇑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `ContinuousLinearEquiv.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
protected theorem differentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.differentiable.differentiableOn
/-
**ContinuousLinearEquiv.comp_differentiableWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearEquiv`。
形式化陈述：comp_differentiableWithinAt_iff {f : G -> E} {s : Set G} {x : G} : Differe
ntiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `ContinuousLinearEquiv.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.symm_comp_self`：symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂
) : (e.symm : M₂ -> M₁) ∘ (e : M₁ -> M₂) = id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
-/
theorem comp_differentiableWithinAt_iff {f : G → E} {s : Set G} {x : G} :
    DifferentiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  refine ⟨fun H => ?_, fun H => iso.differentiable.differentiableAt.comp_differentiableWithinAt x H⟩
  have : DifferentiableWithinAt 𝕜 (iso.symm ∘ iso ∘ f) s x :=
    iso.symm.differentiable.differentiableAt.comp_differentiableWithinAt x H
  rwa [← Function.comp_assoc iso.symm iso f, iso.symm_comp_self] at this
/-
**ContinuousLinearEquiv.comp_differentiableAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearEquiv`。
形式化陈述：comp_differentiableAt_iff {f : G -> E} {x : G} : DifferentiableAt 𝕜 (iso ∘
 f) x ↔ DifferentiableAt 𝕜 f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `ContinuousLinearEquiv.comp_differentiableWithinAt_iff`：comp_differentiab
leWithinAt_iff {f : G -> E} {s : Set G} {x : G} : DifferentiableWithinAt 𝕜 (iso 
∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comp_differentiableAt_iff {f : G → E} {x : G} :
    DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x := by
  rw [← differentiableWithinAt_univ, ← differentiableWithinAt_univ,
    iso.comp_differentiableWithinAt_iff]
/-
**ContinuousLinearEquiv.comp_differentiableOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearEquiv`。
形式化陈述：comp_differentiableOn_iff {f : G -> E} {s : Set G} : DifferentiableOn 𝕜 (i
so ∘ f) s ↔ DifferentiableOn 𝕜 f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableOn.eq_1`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst
_3 : Topolo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ContinuousLinearEquiv.comp_differentiableWithinAt_iff`：comp_differentiab
leWithinAt_iff {f : G -> E} {s : Set G} {x : G} : DifferentiableWithinAt 𝕜 (iso 
∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_differentiableOn_iff {f : G → E} {s : Set G} :
    DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s := by
  rw [DifferentiableOn, DifferentiableOn]
  simp only [iso.comp_differentiableWithinAt_iff]
/-
**ContinuousLinearEquiv.comp_differentiable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearEquiv`。
形式化陈述：comp_differentiable_iff {f : G -> E} : Differentiable 𝕜 (iso ∘ f) ↔ Differ
entiable 𝕜 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `differentiableOn_univ`：differentiableOn_univ : DifferentiableOn 𝕜 f univ
 ↔ Differentiable 𝕜 f
· 使用定理 `ContinuousLinearEquiv.comp_differentiableOn_iff`：comp_differentiableOn_i
ff {f : G -> E} {s : Set G} : DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 
𝕜 f s
-/
theorem comp_differentiable_iff {f : G → E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f := by
  rw [← differentiableOn_univ, ← differentiableOn_univ]
  exact iso.comp_differentiableOn_iff
/-
**ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearEquiv`。
形式化陈述：comp_hasFDerivWithinAt_iff {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜]
 E} : HasFDerivWithinAt (iso ∘ f) ((iso : E ->L[𝕜] F).comp f') s x ↔ HasFDerivWi
thinAt f f' s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearEquiv.coe_symm_comp_coe`：coe_symm_comp_coe (e : M₁ ≃SL[σ
₁₂] M₂) : (e.symm : M₂ ->SL[σ₂₁] M₁).comp (e : M₁ ->SL[σ₁₂] M₂) = ContinuousLine
arMap.id R₁ M₁
· 使用定理 `ContinuousLinearMap.id_comp`：id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘
SL f = f
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `ContinuousLinearEquiv.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
-/
theorem comp_hasFDerivWithinAt_iff {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivWithinAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') s x ↔ HasFDerivWithinAt f f' s x := by
  refine ⟨fun H => ?_, fun H => iso.hasFDerivAt.comp_hasFDerivWithinAt x H⟩
  simpa [Function.comp_def, ← ContinuousLinearMap.comp_assoc]
    using iso.symm.hasFDerivAt.comp_hasFDerivWithinAt x H
/-
**ContinuousLinearEquiv.comp_hasStrictFDerivAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearEquiv`。
形式化陈述：comp_hasStrictFDerivAt_iff {f : G -> E} {x : G} {f' : G ->L[𝕜] E} : HasStr
ictFDerivAt (iso ∘ f) ((iso : E ->L[𝕜] F).comp f') x ↔ HasStrictFDerivAt f f' x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `ContinuousLinearEquiv.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] {F : Type u_…
-/
theorem comp_hasStrictFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasStrictFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasStrictFDerivAt f f' x := by
  refine ⟨fun H => ?_, fun H => iso.hasStrictFDerivAt.comp x H⟩
  convert! iso.symm.hasStrictFDerivAt.comp x H using 1 <;>
    ext z <;> apply (iso.symm_apply_apply _).symm
/-
**ContinuousLinearEquiv.comp_hasFDerivAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearEquiv`。
形式化陈述：comp_hasFDerivAt_iff {f : G -> E} {x : G} {f' : G ->L[𝕜] E} : HasFDerivAt 
(iso ∘ f) ((iso : E ->L[𝕜] F).comp f') x ↔ HasFDerivAt f f' x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff`：comp_hasFDerivWithinAt
_iff {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] E} : HasFDerivWithinAt (iso
 ∘ f) ((iso : E ->L[𝕜] F).comp f') s x…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_hasFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasFDerivAt f f' x := by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff]
/-
**ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearEquiv`。
形式化陈述：comp_hasFDerivWithinAt_iff' {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜
] F} : HasFDerivWithinAt (iso ∘ f) f' s x ↔ HasFDerivWithinAt f ((iso.symm : F -
>L[𝕜] E).comp f') s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff`：comp_hasFDerivWithinAt
_iff {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] E} : HasFDerivWithinAt (iso
 ∘ f) ((iso : E ->L[𝕜] F).comp f') s x…
· 使用定理 `ContinuousLinearMap.comp_assoc`：comp_assoc {R₄ : Type*} [Semiring R₄] [M
odule R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₃₄ : R₃ ->+* R₄} [RingHomCo
mpTriple σ₁₃ σ₃₄ σ₁₄…
· 使用定理 `ContinuousLinearEquiv.coe_comp_coe_symm`：coe_comp_coe_symm (e : M₁ ≃SL[σ
₁₂] M₂) : (e : M₁ ->SL[σ₁₂] M₂).comp (e.symm : M₂ ->SL[σ₂₁] M₁) = ContinuousLine
arMap.id R₂ M₂
· 使用定理 `ContinuousLinearMap.id_comp`：id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘
SL f = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comp_hasFDerivWithinAt_iff' {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivWithinAt (iso ∘ f) f' s x ↔
      HasFDerivWithinAt f ((iso.symm : F →L[𝕜] E).comp f') s x := by
  rw [← iso.comp_hasFDerivWithinAt_iff, ← ContinuousLinearMap.comp_assoc, iso.coe_comp_coe_symm,
    ContinuousLinearMap.id_comp]
/-
**ContinuousLinearEquiv.comp_hasFDerivAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearEquiv`。
形式化陈述：comp_hasFDerivAt_iff' {f : G -> E} {x : G} {f' : G ->L[𝕜] F} : HasFDerivAt
 (iso ∘ f) f' x ↔ HasFDerivAt f ((iso.symm : F ->L[𝕜] E).comp f') x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff'`：comp_hasFDerivWithinA
t_iff' {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] F} : HasFDerivWithinAt (i
so ∘ f) f' s x ↔ HasFDerivWithinAt f ((…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_hasFDerivAt_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivAt (iso ∘ f) f' x ↔ HasFDerivAt f ((iso.symm : F →L[𝕜] E).comp f') x := by
  simp_rw [← hasFDerivWithinAt_univ, iso.comp_hasFDerivWithinAt_iff']
/-
**ContinuousLinearEquiv.comp_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：comp_fderivWithin {f : G -> E} {s : Set G} {x : G} (hxs : UniqueDiffWithin
At 𝕜 s x) : fderivWithin 𝕜 (iso ∘ f) s x = (iso : E ->L[𝕜] F).comp (fderivWithin
 𝕜 f s x)
参数：hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_comp_fderivWithin`：fderiv_comp_fderivWithin {g : F -> G} (hg : Di
fferentiableAt 𝕜 g (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDif
fWithinAt 𝕜 s …
· 使用定理 `ContinuousLinearEquiv.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `ContinuousLinearEquiv.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {F : Type u_…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearEquiv.comp_differentiableWithinAt_iff`：comp_differentiab
leWithinAt_iff {f : G -> E} {s : Set G} {x : G} : DifferentiableWithinAt 𝕜 (iso 
∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0
· 使用定理 `ContinuousLinearMap.comp_zero`：comp_zero (g : M₂ ->SL[σ₂₃] M₃) : g ∘SL (
0 : M₁ ->SL[σ₁₂] M₂) = 0
-/
theorem comp_fderivWithin {f : G → E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderivWithin 𝕜 f s x) := by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · rw [fderiv_comp_fderivWithin x iso.differentiableAt h hxs, iso.fderiv]
  · have : ¬DifferentiableWithinAt 𝕜 (iso ∘ f) s x := mt iso.comp_differentiableWithinAt_iff.1 h
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this, ContinuousLinearMap.comp_zero]
/-
**ContinuousLinearEquiv.comp_fderiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearE
quiv`。
形式化陈述：comp_fderiv {f : G -> E} {x : G} : fderiv 𝕜 (iso ∘ f) x = (iso : E ->L[𝕜] 
F).comp (fderiv 𝕜 f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `ContinuousLinearEquiv.comp_fderivWithin`：comp_fderivWithin {f : G -> E} 
{s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (iso ∘ f) 
s x = (iso : E ->L[𝕜] F).comp…
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem comp_fderiv {f : G → E} {x : G} :
    fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) := by
  rw [← fderivWithin_univ, ← fderivWithin_univ]
  exact iso.comp_fderivWithin uniqueDiffWithinAt_univ
/-
**ContinuousLinearEquiv._root_.fderivWithin_continuousLinearEquiv_comp** 是 Mathl
ib 中的一个引理，位于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.fderivWithin_continuousLinearEquiv_comp (L : G ≃L[𝕜] G') (f : E → (F →L[𝕜] G))
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x ↦ (L : G →L[𝕜] G').comp (f x)) s x =
      (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L)) ∘L (fderivWithin 𝕜 f s x) := by
  change fderivWithin 𝕜 (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L) ∘ f) s x = _
  rw [ContinuousLinearEquiv.comp_fderivWithin _ hs]
/-
**ContinuousLinearEquiv._root_.fderiv_continuousLinearEquiv_comp** 是 Mathlib 中的一
个引理，位于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.fderiv_continuousLinearEquiv_comp (L : G ≃L[𝕜] G') (f : E → (F →L[𝕜] G)) (x : E) :
    fderiv 𝕜 (fun x ↦ (L : G →L[𝕜] G').comp (f x)) x =
      (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L)) ∘L (fderiv 𝕜 f x) := by
  change fderiv 𝕜 (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L) ∘ f) x = _
  rw [ContinuousLinearEquiv.comp_fderiv]
/-
**ContinuousLinearEquiv._root_.fderiv_continuousLinearEquiv_comp'** 是 Mathlib 中的
一个引理，位于命名空间 `ContinuousLinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.fderiv_continuousLinearEquiv_comp' (L : G ≃L[𝕜] G') (f : E → (F →L[𝕜] G)) :
    fderiv 𝕜 (fun x ↦ (L : G →L[𝕜] G').comp (f x)) =
      fun x ↦ (((ContinuousLinearEquiv.refl 𝕜 F).arrowCongr L)) ∘L (fderiv 𝕜 f x) := by
  ext x : 1
  exact fderiv_continuousLinearEquiv_comp L f x
/-
**ContinuousLinearEquiv.comp_right_differentiableWithinAt_iff** 是 Mathlib 中的一个定理
，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：comp_right_differentiableWithinAt_iff {f : F -> G} {s : Set F} {x : E} : D
ifferentiableWithinAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x ↔ DifferentiableWithinAt 𝕜 f s (
iso x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.comp`：DifferentiableWithinAt.comp {g : F -> G} {t
 : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt
 𝕜 f s x) (h : Ma…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `ContinuousLinearEquiv.differentiableWithinAt`：∀ {𝕜 : Type u_1} [inst : N
ontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `ContinuousLinearEquiv.self_comp_symm`：self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂
) : (e : M₁ -> M₂) ∘ (e.symm : M₂ -> M₁) = id
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
-/
theorem comp_right_differentiableWithinAt_iff {f : F → G} {s : Set F} {x : E} :
    DifferentiableWithinAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x ↔ DifferentiableWithinAt 𝕜 f s (iso x) := by
  refine ⟨fun H => ?_, fun H => H.comp x iso.differentiableWithinAt (mapsTo_preimage _ s)⟩
  have : DifferentiableWithinAt 𝕜 ((f ∘ iso) ∘ iso.symm) s (iso x) := by
    rw [← iso.symm_apply_apply x] at H
    apply H.comp (iso x) iso.symm.differentiableWithinAt
    intro y hy
    simpa only [mem_preimage, apply_symm_apply] using hy
  rwa [Function.comp_assoc, iso.self_comp_symm] at this
/-
**ContinuousLinearEquiv.comp_right_differentiableAt_iff** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearEquiv`。
形式化陈述：comp_right_differentiableAt_iff {f : F -> G} {x : E} : DifferentiableAt 𝕜 
(f ∘ iso) x ↔ DifferentiableAt 𝕜 f (iso x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_right_differentiableWithinAt_iff`：comp_right_
differentiableWithinAt_iff {f : F -> G} {s : Set F} {x : E} : DifferentiableWith
inAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x ↔ DifferentiableWi…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_right_differentiableAt_iff {f : F → G} {x : E} :
    DifferentiableAt 𝕜 (f ∘ iso) x ↔ DifferentiableAt 𝕜 f (iso x) := by
  simp only [← differentiableWithinAt_univ, ← iso.comp_right_differentiableWithinAt_iff,
    preimage_univ]
/-
**ContinuousLinearEquiv.comp_right_differentiableOn_iff** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearEquiv`。
形式化陈述：comp_right_differentiableOn_iff {f : F -> G} {s : Set F} : DifferentiableO
n 𝕜 (f ∘ iso) (iso ⁻¹' s) ↔ DifferentiableOn 𝕜 f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `ContinuousLinearEquiv.comp_right_differentiableWithinAt_iff`：comp_right_
differentiableWithinAt_iff {f : F -> G} {s : Set F} {x : E} : DifferentiableWith
inAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x ↔ DifferentiableWi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem comp_right_differentiableOn_iff {f : F → G} {s : Set F} :
    DifferentiableOn 𝕜 (f ∘ iso) (iso ⁻¹' s) ↔ DifferentiableOn 𝕜 f s := by
  refine ⟨fun H y hy => ?_, fun H y hy => iso.comp_right_differentiableWithinAt_iff.2 (H _ hy)⟩
  rw [← iso.apply_symm_apply y, ← comp_right_differentiableWithinAt_iff]
  apply H
  simpa only [mem_preimage, apply_symm_apply] using hy
/-
**ContinuousLinearEquiv.comp_right_differentiable_iff** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearEquiv`。
形式化陈述：comp_right_differentiable_iff {f : F -> G} : Differentiable 𝕜 (f ∘ iso) ↔ 
Differentiable 𝕜 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_right_differentiableOn_iff`：comp_right_differ
entiableOn_iff {f : F -> G} {s : Set F} : DifferentiableOn 𝕜 (f ∘ iso) (iso ⁻¹' 
s) ↔ DifferentiableOn 𝕜 f s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_right_differentiable_iff {f : F → G} :
    Differentiable 𝕜 (f ∘ iso) ↔ Differentiable 𝕜 f := by
  simp only [← differentiableOn_univ, ← iso.comp_right_differentiableOn_iff, preimage_univ]
/-
**ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousLinearEquiv`。
形式化陈述：comp_right_hasFDerivWithinAt_iff {f : F -> G} {s : Set F} {x : E} {f' : F 
->L[𝕜] G} : HasFDerivWithinAt (f ∘ iso) (f'.comp (iso : E ->L[𝕜] F)) (iso ⁻¹' s)
 x ↔ HasFDerivWithinAt f f' s (iso x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `ContinuousLinearEquiv.self_comp_symm`：self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂
) : (e : M₁ -> M₂) ∘ (e.symm : M₂ -> M₁) = id
· 使用定理 `ContinuousLinearMap.comp_assoc`：comp_assoc {R₄ : Type*} [Semiring R₄] [M
odule R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₃₄ : R₃ ->+* R₄} [RingHomCo
mpTriple σ₁₃ σ₃₄ σ₁₄…
· 使用定理 `ContinuousLinearEquiv.coe_comp_coe_symm`：coe_comp_coe_symm (e : M₁ ≃SL[σ
₁₂] M₂) : (e : M₁ ->SL[σ₁₂] M₂).comp (e.symm : M₂ ->SL[σ₂₁] M₁) = ContinuousLine
arMap.id R₂ M₂
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f
· 使用定理 `HasFDerivWithinAt.comp`：HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[
𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt 
f f' s x) (h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `ContinuousLinearEquiv.hasFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
-/
theorem comp_right_hasFDerivWithinAt_iff {f : F → G} {s : Set F} {x : E} {f' : F →L[𝕜] G} :
    HasFDerivWithinAt (f ∘ iso) (f'.comp (iso : E →L[𝕜] F)) (iso ⁻¹' s) x ↔
      HasFDerivWithinAt f f' s (iso x) := by
  refine ⟨fun H => ?_, fun H => H.comp x iso.hasFDerivWithinAt (mapsTo_preimage _ s)⟩
  rw [← iso.symm_apply_apply x] at H
  have A : f = (f ∘ iso) ∘ iso.symm := by
    rw [Function.comp_assoc, iso.self_comp_symm]
    rfl
  have B : f' = (f'.comp (iso : E →L[𝕜] F)).comp (iso.symm : F →L[𝕜] E) := by
    rw [ContinuousLinearMap.comp_assoc, iso.coe_comp_coe_symm, ContinuousLinearMap.comp_id]
  rw [A, B]
  apply H.comp (iso x) iso.symm.hasFDerivWithinAt
  intro y hy
  simpa only [mem_preimage, apply_symm_apply] using hy
/-
**ContinuousLinearEquiv.comp_right_hasFDerivAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearEquiv`。
形式化陈述：comp_right_hasFDerivAt_iff {f : F -> G} {x : E} {f' : F ->L[𝕜] G} : HasFDe
rivAt (f ∘ iso) (f'.comp (iso : E ->L[𝕜] F)) x ↔ HasFDerivAt f f' (iso x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_right_hasFDerivAt_iff {f : F → G} {x : E} {f' : F →L[𝕜] G} :
    HasFDerivAt (f ∘ iso) (f'.comp (iso : E →L[𝕜] F)) x ↔ HasFDerivAt f f' (iso x) := by
  simp only [← hasFDerivWithinAt_univ, ← comp_right_hasFDerivWithinAt_iff, preimage_univ]
/-
**ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff'** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearEquiv`。
形式化陈述：comp_right_hasFDerivWithinAt_iff' {f : F -> G} {s : Set F} {x : E} {f' : E
 ->L[𝕜] G} : HasFDerivWithinAt (f ∘ iso) f' (iso ⁻¹' s) x ↔ HasFDerivWithinAt f 
(f'.comp (iso.symm : F ->L[𝕜] E)) s (iso x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff`：comp_right_hasFD
erivWithinAt_iff {f : F -> G} {s : Set F} {x : E} {f' : F ->L[𝕜] G} : HasFDerivW
ithinAt (f ∘ iso) (f'.comp (iso : E ->L[𝕜] F…
· 使用定理 `ContinuousLinearMap.comp_assoc`：comp_assoc {R₄ : Type*} [Semiring R₄] [M
odule R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₃₄ : R₃ ->+* R₄} [RingHomCo
mpTriple σ₁₃ σ₃₄ σ₁₄…
· 使用定理 `ContinuousLinearEquiv.coe_symm_comp_coe`：coe_symm_comp_coe (e : M₁ ≃SL[σ
₁₂] M₂) : (e.symm : M₂ ->SL[σ₂₁] M₁).comp (e : M₁ ->SL[σ₁₂] M₂) = ContinuousLine
arMap.id R₁ M₁
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comp_right_hasFDerivWithinAt_iff' {f : F → G} {s : Set F} {x : E} {f' : E →L[𝕜] G} :
    HasFDerivWithinAt (f ∘ iso) f' (iso ⁻¹' s) x ↔
      HasFDerivWithinAt f (f'.comp (iso.symm : F →L[𝕜] E)) s (iso x) := by
  rw [← iso.comp_right_hasFDerivWithinAt_iff, ContinuousLinearMap.comp_assoc,
    iso.coe_symm_comp_coe, ContinuousLinearMap.comp_id]
/-
**ContinuousLinearEquiv.comp_right_hasFDerivAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearEquiv`。
形式化陈述：comp_right_hasFDerivAt_iff' {f : F -> G} {x : E} {f' : E ->L[𝕜] G} : HasFD
erivAt (f ∘ iso) f' x ↔ HasFDerivAt f (f'.comp (iso.symm : F ->L[𝕜] E)) (iso x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff'`：comp_right_hasF
DerivWithinAt_iff' {f : F -> G} {s : Set F} {x : E} {f' : E ->L[𝕜] G} : HasFDeri
vWithinAt (f ∘ iso) f' (iso ⁻¹' s) x ↔ HasFDe…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_right_hasFDerivAt_iff' {f : F → G} {x : E} {f' : E →L[𝕜] G} :
    HasFDerivAt (f ∘ iso) f' x ↔ HasFDerivAt f (f'.comp (iso.symm : F →L[𝕜] E)) (iso x) := by
  simp only [← hasFDerivWithinAt_univ, ← iso.comp_right_hasFDerivWithinAt_iff', preimage_univ]
/-
**ContinuousLinearEquiv.comp_right_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearEquiv`。
形式化陈述：comp_right_fderivWithin {f : F -> G} {s : Set F} {x : E} (hxs : UniqueDiff
WithinAt 𝕜 (iso ⁻¹' s) x) : fderivWithin 𝕜 (f ∘ iso) (iso ⁻¹' s) x = (fderivWith
in 𝕜 f s (iso x)).comp (iso : E ->L[𝕜] F)
参数：hxs : UniqueDiffWithinAt 𝕜 (iso ⁻¹' s) x。
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff`：comp_right_hasFD
erivWithinAt_iff {f : F -> G} {s : Set F} {x : E} {f' : F ->L[𝕜] G} : HasFDerivW
ithinAt (f ∘ iso) (f'.comp (iso : E ->L[𝕜] F…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearEquiv.comp_right_differentiableWithinAt_iff`：comp_right_
differentiableWithinAt_iff {f : F -> G} {s : Set F} {x : E} : DifferentiableWith
inAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x ↔ DifferentiableWi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0
· 使用定理 `ContinuousLinearMap.zero_comp`：zero_comp (f : M₁ ->SL[σ₁₂] M₂) : (0 : M₂
 ->SL[σ₂₃] M₃) ∘SL f = 0
-/
theorem comp_right_fderivWithin {f : F → G} {s : Set F} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 (iso ⁻¹' s) x) :
    fderivWithin 𝕜 (f ∘ iso) (iso ⁻¹' s) x =
      (fderivWithin 𝕜 f s (iso x)).comp (iso : E →L[𝕜] F) := by
  by_cases h : DifferentiableWithinAt 𝕜 f s (iso x)
  · exact (iso.comp_right_hasFDerivWithinAt_iff.2 h.hasFDerivWithinAt).fderivWithin hxs
  · have : ¬DifferentiableWithinAt 𝕜 (f ∘ iso) (iso ⁻¹' s) x := by
      intro h'
      exact h (iso.comp_right_differentiableWithinAt_iff.1 h')
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this, ContinuousLinearMap.zero_comp]
/-
**ContinuousLinearEquiv.comp_right_fderiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearEquiv`。
形式化陈述：comp_right_fderiv {f : F -> G} {x : E} : fderiv 𝕜 (f ∘ iso) x = (fderiv 𝕜 
f (iso x)).comp (iso : E ->L[𝕜] F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `ContinuousLinearEquiv.comp_right_fderivWithin`：comp_right_fderivWithin {
f : F -> G} {s : Set F} {x : E} (hxs : UniqueDiffWithinAt 𝕜 (iso ⁻¹' s) x) : fde
rivWithin 𝕜 (f ∘ iso) (iso ⁻¹' s) x…
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
theorem comp_right_fderiv {f : F → G} {x : E} :
    fderiv 𝕜 (f ∘ iso) x = (fderiv 𝕜 f (iso x)).comp (iso : E →L[𝕜] F) := by
  rw [← fderivWithin_univ, ← fderivWithin_univ, ← iso.comp_right_fderivWithin, preimage_univ]
  exact uniqueDiffWithinAt_univ

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

/-! ### Differentiability of linear isometry equivs, and invariance of differentiability -/


variable (iso : E ≃ₗᵢ[𝕜] F)

@[fun_prop]
/-
**LinearIsometryEquiv.hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometr
yEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   (iso : E ≃ₗᵢ[𝕜] F), Ha
sStrictFDerivAt (⇑iso) (↑↑iso) x
参数：iso : E ≃ₗᵢ[𝕜] F；⇑iso；↑↑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem hasStrictFDerivAt : HasStrictFDerivAt iso (iso : E →L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).hasStrictFDerivAt

@[fun_prop]
/-
**LinearIsometryEquiv.hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometr
yEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   {s : Set E} (iso : E ≃
ₗᵢ[𝕜] F), HasFDerivWithinAt (⇑iso) (↑↑iso) s x
参数：iso : E ≃ₗᵢ[𝕜] F；⇑iso；↑↑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.hasFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem hasFDerivWithinAt : HasFDerivWithinAt iso (iso : E →L[𝕜] F) s x :=
  (iso : E ≃L[𝕜] F).hasFDerivWithinAt

@[fun_prop]
/-
**LinearIsometryEquiv.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   (iso : E ≃ₗᵢ[𝕜] F), Ha
sFDerivAt (⇑iso) (↑↑iso) x
参数：iso : E ≃ₗᵢ[𝕜] F；⇑iso；↑↑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
-/
protected theorem hasFDerivAt : HasFDerivAt iso (iso : E →L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).hasFDerivAt

@[fun_prop]
/-
**LinearIsometryEquiv.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   (iso : E ≃ₗᵢ[𝕜] F), Di
fferentiableAt 𝕜 (⇑iso) x
参数：iso : E ≃ₗᵢ[𝕜] F；⇑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `LinearIsometryEquiv.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Type u_…
-/
protected theorem differentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.hasFDerivAt.differentiableAt

@[fun_prop]
/-
**LinearIsometryEquiv.differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `LinearIs
ometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   {s : Set E} (iso : E ≃
ₗᵢ[𝕜] F), DifferentiableWithinAt 𝕜 (⇑iso) s x
参数：iso : E ≃ₗᵢ[𝕜] F；⇑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `LinearIsometryEquiv.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.differentiableAt.differentiableWithinAt
/-
**LinearIsometryEquiv.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   (iso : E ≃ₗᵢ[𝕜] F), fd
eriv 𝕜 (⇑iso) x = ↑↑iso
参数：iso : E ≃ₗᵢ[𝕜] F；⇑iso。
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
· 使用定理 `LinearIsometryEquiv.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Type u_…
-/
protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.hasFDerivAt.fderiv
/-
**LinearIsometryEquiv.fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqui
v`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {x : E}   {s : Set E} (iso : E ≃
ₗᵢ[𝕜] F), UniqueDiffWithinAt 𝕜 s x → fderivWithin 𝕜 (⇑iso) s x = ↑↑iso
参数：iso : E ≃ₗᵢ[𝕜] F；⇑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.fderivWithin`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Type u_…
-/
protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  (iso : E ≃L[𝕜] F).fderivWithin hxs

@[fun_prop]
/-
**LinearIsometryEquiv.differentiable** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEq
uiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   (iso : E ≃ₗᵢ[𝕜] F), Differenti
able 𝕜 ⇑iso
参数：iso : E ≃ₗᵢ[𝕜] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
protected theorem differentiable : Differentiable 𝕜 iso := fun _ => iso.differentiableAt

@[fun_prop]
/-
**LinearIsometryEquiv.differentiableOn** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {s : Set E}   (iso : E ≃ₗᵢ[𝕜] F)
, DifferentiableOn 𝕜 (⇑iso) s
参数：iso : E ≃ₗᵢ[𝕜] F；⇑iso。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `LinearIsometryEquiv.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Type u_…
-/
protected theorem differentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.differentiable.differentiableOn
/-
**LinearIsometryEquiv.comp_differentiableWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 
`LinearIsometryEquiv`。
形式化陈述：comp_differentiableWithinAt_iff {f : G -> E} {s : Set G} {x : G} : Differe
ntiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_differentiableWithinAt_iff`：comp_differentiab
leWithinAt_iff {f : G -> E} {s : Set G} {x : G} : DifferentiableWithinAt 𝕜 (iso 
∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x
-/
theorem comp_differentiableWithinAt_iff {f : G → E} {s : Set G} {x : G} :
    DifferentiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  (iso : E ≃L[𝕜] F).comp_differentiableWithinAt_iff
/-
**LinearIsometryEquiv.comp_differentiableAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rIsometryEquiv`。
形式化陈述：comp_differentiableAt_iff {f : G -> E} {x : G} : DifferentiableAt 𝕜 (iso ∘
 f) x ↔ DifferentiableAt 𝕜 f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_differentiableAt_iff`：comp_differentiableAt_i
ff {f : G -> E} {x : G} : DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f 
x
-/
theorem comp_differentiableAt_iff {f : G → E} {x : G} :
    DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x :=
  (iso : E ≃L[𝕜] F).comp_differentiableAt_iff
/-
**LinearIsometryEquiv.comp_differentiableOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rIsometryEquiv`。
形式化陈述：comp_differentiableOn_iff {f : G -> E} {s : Set G} : DifferentiableOn 𝕜 (i
so ∘ f) s ↔ DifferentiableOn 𝕜 f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_differentiableOn_iff`：comp_differentiableOn_i
ff {f : G -> E} {s : Set G} : DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 
𝕜 f s
-/
theorem comp_differentiableOn_iff {f : G → E} {s : Set G} :
    DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s :=
  (iso : E ≃L[𝕜] F).comp_differentiableOn_iff
/-
**LinearIsometryEquiv.comp_differentiable_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearI
sometryEquiv`。
形式化陈述：comp_differentiable_iff {f : G -> E} : Differentiable 𝕜 (iso ∘ f) ↔ Differ
entiable 𝕜 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_differentiable_iff`：comp_differentiable_iff {
f : G -> E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f
-/
theorem comp_differentiable_iff {f : G → E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f :=
  (iso : E ≃L[𝕜] F).comp_differentiable_iff
/-
**LinearIsometryEquiv.comp_hasFDerivWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Line
arIsometryEquiv`。
形式化陈述：comp_hasFDerivWithinAt_iff {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜]
 E} : HasFDerivWithinAt (iso ∘ f) ((iso : E ->L[𝕜] F).comp f') s x ↔ HasFDerivWi
thinAt f f' s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff`：comp_hasFDerivWithinAt
_iff {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] E} : HasFDerivWithinAt (iso
 ∘ f) ((iso : E ->L[𝕜] F).comp f') s x…
-/
theorem comp_hasFDerivWithinAt_iff {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivWithinAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') s x ↔ HasFDerivWithinAt f f' s x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff
/-
**LinearIsometryEquiv.comp_hasStrictFDerivAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Line
arIsometryEquiv`。
形式化陈述：comp_hasStrictFDerivAt_iff {f : G -> E} {x : G} {f' : G ->L[𝕜] E} : HasStr
ictFDerivAt (iso ∘ f) ((iso : E ->L[𝕜] F).comp f') x ↔ HasStrictFDerivAt f f' x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_hasStrictFDerivAt_iff`：comp_hasStrictFDerivAt
_iff {f : G -> E} {x : G} {f' : G ->L[𝕜] E} : HasStrictFDerivAt (iso ∘ f) ((iso 
: E ->L[𝕜] F).comp f') x ↔ HasStrictFD…
-/
theorem comp_hasStrictFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasStrictFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasStrictFDerivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_hasStrictFDerivAt_iff
/-
**LinearIsometryEquiv.comp_hasFDerivAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsom
etryEquiv`。
形式化陈述：comp_hasFDerivAt_iff {f : G -> E} {x : G} {f' : G ->L[𝕜] E} : HasFDerivAt 
(iso ∘ f) ((iso : E ->L[𝕜] F).comp f') x ↔ HasFDerivAt f f' x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_hasFDerivAt_iff`：comp_hasFDerivAt_iff {f : G 
-> E} {x : G} {f' : G ->L[𝕜] E} : HasFDerivAt (iso ∘ f) ((iso : E ->L[𝕜] F).comp
 f') x ↔ HasFDerivAt f f' x
-/
theorem comp_hasFDerivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasFDerivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasFDerivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff
/-
**LinearIsometryEquiv.comp_hasFDerivWithinAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earIsometryEquiv`。
形式化陈述：comp_hasFDerivWithinAt_iff' {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜
] F} : HasFDerivWithinAt (iso ∘ f) f' s x ↔ HasFDerivWithinAt f ((iso.symm : F -
>L[𝕜] E).comp f') s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff'`：comp_hasFDerivWithinA
t_iff' {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] F} : HasFDerivWithinAt (i
so ∘ f) f' s x ↔ HasFDerivWithinAt f ((…
-/
theorem comp_hasFDerivWithinAt_iff' {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivWithinAt (iso ∘ f) f' s x ↔ HasFDerivWithinAt f ((iso.symm : F →L[𝕜] E).comp f') s x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivWithinAt_iff'
/-
**LinearIsometryEquiv.comp_hasFDerivAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 `LinearIso
metryEquiv`。
形式化陈述：comp_hasFDerivAt_iff' {f : G -> E} {x : G} {f' : G ->L[𝕜] F} : HasFDerivAt
 (iso ∘ f) f' x ↔ HasFDerivAt f ((iso.symm : F ->L[𝕜] E).comp f') x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_hasFDerivAt_iff'`：comp_hasFDerivAt_iff' {f : 
G -> E} {x : G} {f' : G ->L[𝕜] F} : HasFDerivAt (iso ∘ f) f' x ↔ HasFDerivAt f (
(iso.symm : F ->L[𝕜] E).comp f') …
-/
theorem comp_hasFDerivAt_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
    HasFDerivAt (iso ∘ f) f' x ↔ HasFDerivAt f ((iso.symm : F →L[𝕜] E).comp f') x :=
  (iso : E ≃L[𝕜] F).comp_hasFDerivAt_iff'
/-
**LinearIsometryEquiv.comp_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometr
yEquiv`。
形式化陈述：comp_fderivWithin {f : G -> E} {s : Set G} {x : G} (hxs : UniqueDiffWithin
At 𝕜 s x) : fderivWithin 𝕜 (iso ∘ f) s x = (iso : E ->L[𝕜] F).comp (fderivWithin
 𝕜 f s x)
参数：hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_fderivWithin`：comp_fderivWithin {f : G -> E} 
{s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (iso ∘ f) 
s x = (iso : E ->L[𝕜] F).comp…
-/
theorem comp_fderivWithin {f : G → E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderivWithin 𝕜 f s x) :=
  (iso : E ≃L[𝕜] F).comp_fderivWithin hxs
/-
**LinearIsometryEquiv.comp_fderiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEquiv
`。
形式化陈述：comp_fderiv {f : G -> E} {x : G} : fderiv 𝕜 (iso ∘ f) x = (iso : E ->L[𝕜] 
F).comp (fderiv 𝕜 f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.comp_fderiv`：comp_fderiv {f : G -> E} {x : G} : fd
eriv 𝕜 (iso ∘ f) x = (iso : E ->L[𝕜] F).comp (fderiv 𝕜 f x)
-/
theorem comp_fderiv {f : G → E} {x : G} :
    fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) :=
  (iso : E ≃L[𝕜] F).comp_fderiv
/-
**LinearIsometryEquiv.comp_fderiv'** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometryEqui
v`。
形式化陈述：comp_fderiv' {f : G -> E} : fderiv 𝕜 (iso ∘ f) = fun x => (iso : E ->L[𝕜] 
F).comp (fderiv 𝕜 f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearIsometryEquiv.comp_fderiv`：comp_fderiv {f : G -> E} {x : G} : fder
iv 𝕜 (iso ∘ f) x = (iso : E ->L[𝕜] F).comp (fderiv 𝕜 f x)
-/
theorem comp_fderiv' {f : G → E} :
    fderiv 𝕜 (iso ∘ f) = fun x ↦ (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) := by
  ext x : 1
  exact LinearIsometryEquiv.comp_fderiv iso

end LinearIsometryEquiv

/-
**HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE (h : HasFDerivWithinAt f f' s 
x) (hf' : exists C, AntilipschitzWith C f') : Tendsto f (𝓝[s \ {x}] x) (𝓝[!=] f 
x)
参数：h : HasFDerivWithinAt f f' s x；hf' : exists C, AntilipschitzWith C f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dist_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], dist 0 = norm
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
· 使用定理 `AntilipschitzWith.le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst : P
seudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   A
ntilipschitzWith K …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `HasFDerivWithinAt.isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Typ…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Asymptotics.IsBigO.eq_zero_imp`：∀ {α : Type u_1} {E'' : Type u_9} {F'' :
 Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F'']   
{f'' : α → E''} {g''…
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsEquivalent.isBigO_symm`：∀ {α : Type u_1} {β : Type u_2} [i
nst : NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquiva
lent l u v → v =O[l] u
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
（共 39 条，此处仅展示前 30 条）
-/
theorem HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE (h : HasFDerivWithinAt f f' s x)
    (hf' : ∃ C, AntilipschitzWith C f') : Tendsto f (𝓝[s \ {x}] x) (𝓝[≠] f x) := by
  replace hf' : ∃ C, ∀ z, ‖z‖ ≤ C * ‖f' z‖ := by
    obtain ⟨C, hC⟩ := hf'
    exact ⟨C, fun x ↦ by simpa using hC.le_mul_dist 0 x⟩
  have A : (fun z ↦ z - x) =O[𝓝[s] x] fun z ↦ f' (z - x) :=
    isBigO_iff.mpr <| hf'.imp fun C hC ↦ Eventually.of_forall fun z ↦ hC (z - x)
  have : (fun z ↦ f z - f x) ~[𝓝[s] x] fun z ↦ f' (z - x) := h.isLittleO.trans_isBigO A
  have : ∀ᶠ (x_1 : E) in 𝓝[s] x, x_1 ∈ ({x}ᶜ : Set E) → f x_1 ∈ ({f x}ᶜ : Set F) := by
    simpa [sub_eq_zero, not_imp_not] using (A.trans this.isBigO_symm).eq_zero_imp
  apply le_inf ((map_mono (nhdsWithin_mono x sdiff_subset)).trans h.continuousWithinAt)
  rwa [le_principal_iff, ← eventually_mem_set, eventually_map, sdiff_eq, nhdsWithin_inter',
    eventually_inf_principal]
/-
**HasFDerivWithinAt.eventually_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.eventually_ne (h : HasFDerivWithinAt f f' s x) (hf' : ex
ists C, AntilipschitzWith C f') : forallᶠ z in 𝓝[s \ {x}] x, f z != c
参数：h : HasFDerivWithinAt f f' s x；hf' : exists C, AntilipschitzWith C f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE`：HasFDerivWithinAt.tendsto_n
hdsWithin_nhdsNE (h : HasFDerivWithinAt f f' s x) (hf' : exists C, Antilipschitz
With C f') : Tendsto f (𝓝[s \ {x}…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `eventually_ne_nhdsWithin`：eventually_ne_nhdsWithin [T1Space X] {a b : X}
 {s : Set X} (h : a != b) : forallᶠ x in 𝓝[s] a, x != b
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem HasFDerivWithinAt.eventually_ne (h : HasFDerivWithinAt f f' s x)
    (hf' : ∃ C, AntilipschitzWith C f') : ∀ᶠ z in 𝓝[s \ {x}] x, f z ≠ c := by
  rw [← eventually_map (m := f) (P := fun z ↦ z ≠ c)]
  apply Eventually.filter_mono (h.tendsto_nhdsWithin_nhdsNE hf')
  rcases eq_or_ne (f x) c with rfl | hc
  · exact eventually_mem_nhdsWithin
  · exact eventually_ne_nhdsWithin hc
/-
**HasFDerivWithinAt.eventually_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.eventually_notMem (h : HasFDerivWithinAt f f' s x) (hf' 
: exists C, AntilipschitzWith C f') (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) : for
allᶠ z in 𝓝[s \ {x}] x, f z ∉ t
参数：h : HasFDerivWithinAt f f' s x；hf' : exists C, AntilipschitzWith C f'；t : Set
 F；ht : ¬ AccPt (f x) (𝓟 t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE`：HasFDerivWithinAt.tendsto_n
hdsWithin_nhdsNE (h : HasFDerivWithinAt f f' s x) (hf' : exists C, Antilipschitz
With C f') : Tendsto f (𝓝[s \ {x}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.not_frequently`：not_frequently {p : α -> Prop} {f : Filter α} : (
¬existsᶠ x in f, p x) ↔ forallᶠ x in f, ¬p x
· 使用定理 `accPt_iff_frequently_nhdsNE`：accPt_iff_frequently_nhdsNE {X : Type*} [To
pologicalSpace X] {x : X} {C : Set X} : AccPt x (𝓟 C) ↔ existsᶠ (y : X) in 𝓝[!=]
 x, y in C
-/
theorem HasFDerivWithinAt.eventually_notMem (h : HasFDerivWithinAt f f' s x)
    (hf' : ∃ C, AntilipschitzWith C f') (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) :
    ∀ᶠ z in 𝓝[s \ {x}] x, f z ∉ t := by
  rw [accPt_iff_frequently_nhdsNE, not_frequently] at ht
  exact eventually_map.mp (ht.filter_mono (h.tendsto_nhdsWithin_nhdsNE hf'))
/-
**HasFDerivAt.tendsto_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.tendsto_nhdsNE (h : HasFDerivAt f f' x) (hf' : exists C, Antil
ipschitzWith C f') : Tendsto f (𝓝[!=] x) (𝓝[!=] f x)
参数：h : HasFDerivAt f f' x；hf' : exists C, AntilipschitzWith C f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `HasFDerivWithinAt.tendsto_nhdsWithin_nhdsNE`：HasFDerivWithinAt.tendsto_n
hdsWithin_nhdsNE (h : HasFDerivWithinAt f f' s x) (hf' : exists C, Antilipschitz
With C f') : Tendsto f (𝓝[s \ {x}…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
-/
theorem HasFDerivAt.tendsto_nhdsNE (h : HasFDerivAt f f' x)
    (hf' : ∃ C, AntilipschitzWith C f') : Tendsto f (𝓝[≠] x) (𝓝[≠] f x) := by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).tendsto_nhdsWithin_nhdsNE hf'
/-
**HasFDerivAt.eventually_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.eventually_ne (h : HasFDerivAt f f' x) (hf' : exists C, Antili
pschitzWith C f') : forallᶠ z in 𝓝[!=] x, f z != c
参数：h : HasFDerivAt f f' x；hf' : exists C, AntilipschitzWith C f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `HasFDerivWithinAt.eventually_ne`：HasFDerivWithinAt.eventually_ne (h : Ha
sFDerivWithinAt f f' s x) (hf' : exists C, AntilipschitzWith C f') : forallᶠ z i
n 𝓝[s \ {x}] x, f z !…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
-/
theorem HasFDerivAt.eventually_ne (h : HasFDerivAt f f' x) (hf' : ∃ C, AntilipschitzWith C f') :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ c := by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).eventually_ne hf'
/-
**HasFDerivAt.eventually_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.eventually_notMem (h : HasFDerivAt f f' x) (hf' : exists C, An
tilipschitzWith C f') (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) : forallᶠ z in 𝓝[!=
] x, f z ∉ t
参数：h : HasFDerivAt f f' x；hf' : exists C, AntilipschitzWith C f'；t : Set F；ht : 
¬ AccPt (f x) (𝓟 t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `HasFDerivWithinAt.eventually_notMem`：HasFDerivWithinAt.eventually_notMem
 (h : HasFDerivWithinAt f f' s x) (hf' : exists C, AntilipschitzWith C f') (t : 
Set F) (ht : ¬ AccPt (f x…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasFDerivWithinAt_univ`：hasFDerivWithinAt_univ : HasFDerivWithinAt f f' 
univ x ↔ HasFDerivAt f f' x
-/
theorem HasFDerivAt.eventually_notMem (h : HasFDerivAt f f' x) (hf' : ∃ C, AntilipschitzWith C f')
    (t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) : ∀ᶠ z in 𝓝[≠] x, f z ∉ t := by
  simpa only [compl_eq_univ_sdiff] using (hasFDerivWithinAt_univ.2 h).eventually_notMem hf' t ht

end

section

/-
  In the special case of a normed space over the reals,
  we can use scalar multiplication in the `tendsto` characterization
  of the Fréchet derivative.
-/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : E → F} {f' : E →L[ℝ] F} {x : E}

/-
**has_fderiv_at_filter_real_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：has_fderiv_at_filter_real_equiv {L : Filter E} : Tendsto (fun x' : E => ‖x
' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) L (𝓝 0) ↔ Tendsto (fun x' : E => ‖x' - x‖
⁻¹ • (f x' - f x - f' (x' - x))) L (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_iff_norm_sub_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [inst
 : SeminormedAddCommGroup E] {f : α → E} {a : Filter α} {b : E},   Filter.Tendst
o f a (nhds b) ↔ Filter…
· 使用定理 `Filter.tendsto_congr`：tendsto_congr {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂
 : Filter β} (h : forall x, f₁ x = f₂ x) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem has_fderiv_at_filter_real_equiv {L : Filter E} :
    Tendsto (fun x' : E => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) L (𝓝 0) ↔
      Tendsto (fun x' : E => ‖x' - x‖⁻¹ • (f x' - f x - f' (x' - x))) L (𝓝 0) := by
  symm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_congr fun x' => ?_
  simp [norm_smul]
/-
**HasFDerivAt.lim_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.lim_real (hf : HasFDerivAt f f' x) (v : E) : Tendsto (fun c : 
Real => c • (f (x + c⁻¹ • v) - f x)) atTop (𝓝 (f' v))
参数：hf : HasFDerivAt f f' x；v : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.lim`：HasFDerivAt.lim [ContinuousAdd E] [ContinuousSMul 𝕜 E] 
[ContinuousAdd F] [ContinuousSMul 𝕜 F] (hf : HasFDerivAt f f' x) (v : E) {α : Ty
pe*} …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_atTop_atTop`：tendsto_atTop_atTop : Tendsto f atTop atTop 
↔ forall b : β, exists i : α, forall a : α, i <= a -> b <= f a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem HasFDerivAt.lim_real (hf : HasFDerivAt f f' x) (v : E) :
    Tendsto (fun c : ℝ => c • (f (x + c⁻¹ • v) - f x)) atTop (𝓝 (f' v)) := by
  apply hf.lim v
  rw [tendsto_atTop_atTop]
  exact fun b => ⟨b, fun a ha => le_trans ha (le_abs_self _)⟩

end

open scoped Pointwise

section TangentCone

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {s : Set E}
  {f' : E →L[𝕜] F} {x : E}

/-- The image of a tangent cone under the differential of a map is included in the tangent cone to
the image. -/
/-
**HasFDerivWithinAt.mapsTo_tangent_cone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.mapsTo_tangent_cone (h : HasFDerivWithinAt f f' s x) : M
apsTo f' (tangentConeAt 𝕜 s x) (tangentConeAt 𝕜 (f '' s) (f x))
参数：h : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_fun_of_mem_tangentConeAt`：exists_fun_of_mem_tangentConeAt (h : y 
in tangentConeAt R s x) : exists (α : Type (max u v)) (l : Filter α) (_hl : l.Ne
Bot) (c : α -> R) (d …
· 使用定理 `mem_tangentConeAt_of_seq`：mem_tangentConeAt_of_seq {α : Type*} (l : Filt
er α) [l.NeBot] (c : α -> R) (d : α -> E) (hd₀ : Tendsto d l (𝓝 0)) (hds : foral
lᶠ n in l, x +…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_sub_nhds_zero_iff`：∀ {G : Type w} [inst : AddGroup G] [inst_1 : 
TopologicalSpace G] [IsTopologicalAddGroup G] {α : Type u_1} {l : Filter α}   {x
 : G} {u : α → …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFDerivWithinAt.lim`：HasFDerivWithinAt.lim (h : HasFDerivWithinAt f f'
 s x) {α : Type*} {l : Filter α} {c : α -> 𝕜} {d : α -> E} {v : E} (dlim : Tends
to d l (𝓝 0…

--- 原说明 ---
The image of a tangent cone under the differential of a map is included in the t
angent cone to
the image.
-/
theorem HasFDerivWithinAt.mapsTo_tangent_cone (h : HasFDerivWithinAt f f' s x) :
    MapsTo f' (tangentConeAt 𝕜 s x) (tangentConeAt 𝕜 (f '' s) (f x)) := by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  apply mem_tangentConeAt_of_seq l c (fun n ↦ f (x + d n) - f x)
  · rw [tendsto_sub_nhds_zero_iff]
    refine h.continuousWithinAt.tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, hds⟩
    simpa using tendsto_const_nhds.add hd₀
  · exact hds.mono fun n hn ↦ ⟨x + d n, hn, by simp⟩
  · exact h.lim hd₀ hds hcd

/-- If a set has the unique differentiability property at a point x, then the image of this set
under a map with onto derivative has also the unique differentiability property at the image point.
-/
/-
**HasFDerivWithinAt.uniqueDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.uniqueDiffWithinAt (h : HasFDerivWithinAt f f' s x) (hs 
: UniqueDiffWithinAt 𝕜 s x) (h' : DenseRange f') : UniqueDiffWithinAt 𝕜 (f '' s)
 (f x)
参数：h : HasFDerivWithinAt f f' s x；hs : UniqueDiffWithinAt 𝕜 s x；h' : DenseRange 
f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.dense_of_mapsTo`：DenseRange.dense_of_mapsTo {f : X -> Y} (hf'
 : DenseRange f) (hf : Continuous f) (hs : Dense s) {t : Set Y} (ht : MapsTo f s
 t) : Dense t
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `UniqueDiffWithinAt.dense_tangentConeAt`：∀ {R : Type u} {E : Type v} [ins
t : Semiring R] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   [inst_3
 : TopologicalSpace E] {s : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.MapsTo.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂
 t₂
· 使用定理 `HasFDerivWithinAt.mapsTo_tangent_cone`：HasFDerivWithinAt.mapsTo_tangent_
cone (h : HasFDerivWithinAt f f' s x) : MapsTo f' (tangentConeAt 𝕜 s x) (tangent
ConeAt 𝕜 (f '' s) (f x))
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `ContinuousWithinAt.mem_closure_image`：ContinuousWithinAt.mem_closure_ima
ge (h : ContinuousWithinAt f s x) (hx : x in closure s) : f x in closure (f '' s
)
· 使用定理 `HasFDerivWithinAt.continuousWithinAt`：HasFDerivWithinAt.continuousWithin
At (h : HasFDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `UniqueDiffWithinAt.mem_closure`：∀ {R : Type u} {E : Type v} [inst : Semi
ring R] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   [inst_3 : Topol
ogicalSpace E] {s : …

--- 原说明 ---
If a set has the unique differentiability property at a point x, then the image 
of this set
under a map with onto derivative has also the unique differentiability property 
at the image point.
-/
theorem HasFDerivWithinAt.uniqueDiffWithinAt (h : HasFDerivWithinAt f f' s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) (h' : DenseRange f') : UniqueDiffWithinAt 𝕜 (f '' s) (f x) := by
  refine ⟨h'.dense_of_mapsTo f'.continuous hs.1 ?_, h.continuousWithinAt.mem_closure_image hs.2⟩
  change
    Submodule.span 𝕜 (tangentConeAt 𝕜 s x) ≤
      (Submodule.span 𝕜 (tangentConeAt 𝕜 (f '' s) (f x))).comap f'.toLinearMap
  rw [Submodule.span_le]
  exact h.mapsTo_tangent_cone.mono Subset.rfl Submodule.subset_span
/-
**UniqueDiffOn.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffOn.image {f' : E -> E ->L[𝕜] F} (hs : UniqueDiffOn 𝕜 s) (hf' : f
orall x in s, HasFDerivWithinAt f (f' x) s x) (hd : forall x in s, DenseRange (f
' x)) : UniqueDiffOn 𝕜 (f '' s)
参数：hs : UniqueDiffOn 𝕜 s；hf' : forall x in s, HasFDerivWithinAt f (f' x) s x；hd 
: forall x in s, DenseRange (f' x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `HasFDerivWithinAt.uniqueDiffWithinAt`：HasFDerivWithinAt.uniqueDiffWithin
At (h : HasFDerivWithinAt f f' s x) (hs : UniqueDiffWithinAt 𝕜 s x) (h' : DenseR
ange f') : UniqueDiffWithi…
-/
theorem UniqueDiffOn.image {f' : E → E →L[𝕜] F} (hs : UniqueDiffOn 𝕜 s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hd : ∀ x ∈ s, DenseRange (f' x)) :
    UniqueDiffOn 𝕜 (f '' s) :=
  forall_mem_image.2 fun x hx => (hf' x hx).uniqueDiffWithinAt (hs x hx) (hd x hx)
/-
**HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv (e' : E ≃L[𝕜
] F) (h : HasFDerivWithinAt f (e' : E ->L[𝕜] F) s x) (hs : UniqueDiffWithinAt 𝕜 
s x) : UniqueDiffWithinAt 𝕜 (f '' s) (f x)
参数：e' : E ≃L[𝕜] F；h : HasFDerivWithinAt f (e' : E ->L[𝕜] F) s x；hs : UniqueDiffW
ithinAt 𝕜 s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.uniqueDiffWithinAt`：HasFDerivWithinAt.uniqueDiffWithin
At (h : HasFDerivWithinAt f f' s x) (hs : UniqueDiffWithinAt 𝕜 s x) (h' : DenseR
ange f') : UniqueDiffWithi…
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `ContinuousLinearEquiv.surjective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
-/
theorem HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv (e' : E ≃L[𝕜] F)
    (h : HasFDerivWithinAt f (e' : E →L[𝕜] F) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜 (f '' s) (f x) :=
  h.uniqueDiffWithinAt hs e'.surjective.denseRange
/-
**ContinuousLinearEquiv.uniqueDiffOn_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.uniqueDiffOn_image (e : E ≃L[𝕜] F) (h : UniqueDiffOn
 𝕜 s) : UniqueDiffOn 𝕜 (e '' s)
参数：e : E ≃L[𝕜] F；h : UniqueDiffOn 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffOn.image`：UniqueDiffOn.image {f' : E -> E ->L[𝕜] F} (hs : Uniq
ueDiffOn 𝕜 s) (hf' : forall x in s, HasFDerivWithinAt f (f' x) s x) (hd : forall
 x in s,…
· 使用定理 `ContinuousLinearEquiv.hasFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `ContinuousLinearEquiv.surjective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
-/
theorem ContinuousLinearEquiv.uniqueDiffOn_image (e : E ≃L[𝕜] F) (h : UniqueDiffOn 𝕜 s) :
    UniqueDiffOn 𝕜 (e '' s) :=
  h.image (fun _ _ => e.hasFDerivWithinAt) fun _ _ => e.surjective.denseRange

@[simp]
/-
**ContinuousLinearEquiv.uniqueDiffOn_image_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.uniqueDiffOn_image_iff (e : E ≃L[𝕜] F) : UniqueDiffO
n 𝕜 (e '' s) ↔ UniqueDiffOn 𝕜 s
参数：e : E ≃L[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.uniqueDiffOn_image`：ContinuousLinearEquiv.uniqueDi
ffOn_image (e : E ≃L[𝕜] F) (h : UniqueDiffOn 𝕜 s) : UniqueDiffOn 𝕜 (e '' s)
· 使用定理 `ContinuousLinearEquiv.symm_image_image`：symm_image_image (e : M₁ ≃SL[σ₁₂
] M₂) (s : Set M₁) : e.symm '' e '' s = s
-/
theorem ContinuousLinearEquiv.uniqueDiffOn_image_iff (e : E ≃L[𝕜] F) :
    UniqueDiffOn 𝕜 (e '' s) ↔ UniqueDiffOn 𝕜 s :=
  ⟨fun h => e.symm_image_image s ▸ e.symm.uniqueDiffOn_image h, e.uniqueDiffOn_image⟩

@[simp]
/-
**ContinuousLinearEquiv.uniqueDiffOn_preimage_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.uniqueDiffOn_preimage_iff (e : F ≃L[𝕜] E) : UniqueDi
ffOn 𝕜 (e ⁻¹' s) ↔ UniqueDiffOn 𝕜 s
参数：e : F ≃L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.image_symm_eq_preimage`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `ContinuousLinearEquiv.uniqueDiffOn_image_iff`：ContinuousLinearEquiv.uniq
ueDiffOn_image_iff (e : E ≃L[𝕜] F) : UniqueDiffOn 𝕜 (e '' s) ↔ UniqueDiffOn 𝕜 s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ContinuousLinearEquiv.uniqueDiffOn_preimage_iff (e : F ≃L[𝕜] E) :
    UniqueDiffOn 𝕜 (e ⁻¹' s) ↔ UniqueDiffOn 𝕜 s := by
  rw [← e.image_symm_eq_preimage, e.symm.uniqueDiffOn_image_iff]
/-
**UniqueDiffWithinAt.smul** 是 Mathlib 中的一个定理，位于命名空间 `UniqueDiffWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {s : Set E} {x : E},   Uni
queDiffWithinAt 𝕜 s x →     ∀ {G : Type u_4} [inst_3 : GroupWithZero G] [inst_4 
: DistribMulAction G E] [ContinuousConstSMul G E]       [SMulCommClass G 𝕜 E] {c
 : G}, c ≠ 0 → UniqueDiffWithinAt 𝕜 (c • s) (c • x)
参数：c • s；c • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv`：HasFDeriv
WithinAt.uniqueDiffWithinAt_of_continuousLinearEquiv (e' : E ≃L[𝕜] F) (h : HasFD
erivWithinAt f (e' : E ->L[𝕜] F) s x) (hs : UniqueD…
· 使用定理 `ContinuousLinearEquiv.hasFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontri
viallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : 
NormedSpace 𝕜 E] {F : Type u_…
-/
protected theorem UniqueDiffWithinAt.smul (h : UniqueDiffWithinAt 𝕜 s x)
    {G : Type*} [GroupWithZero G] [DistribMulAction G E] [ContinuousConstSMul G E]
    [SMulCommClass G 𝕜 E] {c : G} (hc : c ≠ 0) :
    UniqueDiffWithinAt 𝕜 (c • s) (c • x) :=
  (ContinuousLinearEquiv.smulLeft <| Units.mk0 c hc).hasFDerivWithinAt
    |>.uniqueDiffWithinAt_of_continuousLinearEquiv _ h
/-
**UniqueDiffWithinAt.smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `UniqueDiffWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {s : Set E} {x : E} {G : T
ype u_4} [inst_3 : GroupWithZero G]   [inst_4 : DistribMulAction G E] [Continuou
sConstSMul G E] [SMulCommClass G 𝕜 E] {c : G},   c ≠ 0 → (UniqueDiffWithinAt 𝕜 (
c • s) (c • x) ↔ UniqueDiffWithinAt 𝕜 s x)
参数：UniqueDiffWithinAt 𝕜 (c • s) (c • x) ↔ UniqueDiffWithinAt 𝕜 s x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `UniqueDiffWithinAt.smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {s : Set E} …
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
protected theorem UniqueDiffWithinAt.smul_iff
    {G : Type*} [GroupWithZero G] [DistribMulAction G E] [ContinuousConstSMul G E]
    [SMulCommClass G 𝕜 E] {c : G} (hc : c ≠ 0) :
    UniqueDiffWithinAt 𝕜 (c • s) (c • x) ↔ UniqueDiffWithinAt 𝕜 s x :=
  ⟨fun h ↦ by simpa [hc] using h.smul (inv_ne_zero hc), (.smul · hc)⟩

end TangentCone

section SMulLeft

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {s : Set E}
  {f' : E →L[𝕜] F} {x : E}

/-
**hasFDerivWithinAt_comp_smul_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_comp_smul_smul_iff {c : 𝕜} : HasFDerivWithinAt (f <| c •
 ·) (c • f') s x ↔ HasFDerivWithinAt f f' (c • s) (c • x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `HasFDerivWithinAt.of_subsingleton`：HasFDerivWithinAt.of_subsingleton [T1
Space E] (h : s.Subsingleton) : HasFDerivWithinAt f f' s x
· 使用引理 `Set.subsingleton_zero_smul_set`：subsingleton_zero_smul_set (s : Set β) :
 ((0 : α) • s).Subsingleton
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousLinearEquiv.smulLeft_apply_apply`：∀ {R₁ : Type u_1} [inst : Se
miring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoi
d M₁]   [inst_3 : _root_.Module …
· 使用定理 `ContinuousLinearMap.map_smul_of_tower`：map_smul_of_tower {R S : Type*} [
Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂] [Module S M₂] [LinearMap.Compa
tibleSMul M₁ M₂ R S] (f : M…
· 使用定理 `LinearMap.CompatibleSMul.units`：∀ {M : Type u_8} {M₂ : Type u_10} [inst 
: AddCommGroup M] [inst_1 : AddCommGroup M₂] {R : Type u_14} {S : Type u_15}   [
inst_2 : Monoid R] […
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
（共 35 条，此处仅展示前 30 条）
-/
theorem hasFDerivWithinAt_comp_smul_smul_iff {c : 𝕜} :
    HasFDerivWithinAt (f <| c • ·) (c • f') s x ↔ HasFDerivWithinAt f f' (c • s) (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hasFDerivWithinAt_const, HasFDerivWithinAt.of_subsingleton (subsingleton_zero_smul_set _)]
  · lift c to 𝕜ˣ using IsUnit.mk0 c hc
    have A : f'.comp ((ContinuousLinearEquiv.smulLeft c : E ≃L[𝕜] E) : E →L[𝕜] E) = c • f' := by
      ext; simp
    rw [← Units.smul_def c x, ← ContinuousLinearEquiv.smulLeft_apply_apply (R₁ := 𝕜),
      ← ContinuousLinearEquiv.comp_right_hasFDerivWithinAt_iff, A]
    simp [Function.comp_def, ← Units.smul_def, ← preimage_smul_inv, preimage_preimage]
/-
**hasFDerivWithinAt_comp_smul_iff_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_comp_smul_iff_smul {c : 𝕜} (hc : c != 0) : HasFDerivWith
inAt (f <| c • ·) f' s x ↔ HasFDerivWithinAt (c • f) f' (c • s) (c • x)
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ContinuousLinearEquiv.comp_hasFDerivWithinAt_iff`：comp_hasFDerivWithinAt
_iff {f : G -> E} {s : Set G} {x : G} {f' : G ->L[𝕜] E} : HasFDerivWithinAt (iso
 ∘ f) ((iso : E ->L[𝕜] F).comp f') s x…
-/
theorem hasFDerivWithinAt_comp_smul_iff_smul {c : 𝕜} (hc : c ≠ 0) :
    HasFDerivWithinAt (f <| c • ·) f' s x ↔ HasFDerivWithinAt (c • f) f' (c • s) (c • x) := by
  simp only [← hasFDerivWithinAt_comp_smul_smul_iff, Pi.smul_apply]
  lift c to 𝕜ˣ using IsUnit.mk0 c hc
  exact (ContinuousLinearEquiv.smulLeft c).comp_hasFDerivWithinAt_iff.symm

set_option backward.isDefEq.respectTransparency false in
/-
**fderivWithin_comp_smul_eq_fderivWithin_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_comp_smul_eq_fderivWithin_smul (c : 𝕜) : fderivWithin 𝕜 (f <|
 c • ·) s x = fderivWithin 𝕜 (c • f) (c • s) (c • x)
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_fun_const`：fderivWithin_fun_const (c : F) : fderivWithin 𝕜 
(fun _ => c) s = 0
· 使用定理 `fderivWithin_zero`：fderivWithin_zero : fderivWithin 𝕜 (0 : E -> F) s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `hasFDerivWithinAt_comp_smul_iff_smul`：hasFDerivWithinAt_comp_smul_iff_sm
ul {c : 𝕜} (hc : c != 0) : HasFDerivWithinAt (f <| c • ·) f' s x ↔ HasFDerivWith
inAt (c • f) f' (c • s) (c…
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
-/
theorem fderivWithin_comp_smul_eq_fderivWithin_smul (c : 𝕜) :
    fderivWithin 𝕜 (f <| c • ·) s x = fderivWithin 𝕜 (c • f) (c • s) (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · classical
    simp only [fderivWithin, DifferentiableWithinAt, hasFDerivWithinAt_comp_smul_iff_smul hc]
/-
**fderivWithin_comp_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_comp_smul (c : 𝕜) (hs : UniqueDiffWithinAt 𝕜 s x) : fderivWit
hin 𝕜 (f <| c • ·) s x = c • fderivWithin 𝕜 f (c • s) (c • x)
参数：c : 𝕜；hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_fun_const`：fderivWithin_fun_const (c : F) : fderivWithin 𝕜 
(fun _ => c) s = 0
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderivWithin_comp_smul_eq_fderivWithin_smul`：fderivWithin_comp_smul_eq_f
derivWithin_smul (c : 𝕜) : fderivWithin 𝕜 (f <| c • ·) s x = fderivWithin 𝕜 (c •
 f) (c • s) (c • x)
· 使用引理 `fderivWithin_const_smul_field`：fderivWithin_const_smul_field (c : R) (hs
 : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f
 s x
· 使用定理 `UniqueDiffWithinAt.smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {s : Set E} …
-/
theorem fderivWithin_comp_smul (c : 𝕜) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (f <| c • ·) s x = c • fderivWithin 𝕜 f (c • s) (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [fderivWithin_comp_smul_eq_fderivWithin_smul, fderivWithin_const_smul_field]
    exact hs.smul hc
/-
**fderiv_comp_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_comp_smul (c : 𝕜) : fderiv 𝕜 (f <| c • ·) x = c • fderiv 𝕜 f (c • x
)
参数：c : 𝕜。
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
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `fderivWithin_comp_smul`：fderivWithin_comp_smul (c : 𝕜) (hs : UniqueDiffW
ithinAt 𝕜 s x) : fderivWithin 𝕜 (f <| c • ·) s x = c • fderivWithin 𝕜 f (c • s) 
(c • x)
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.smul_set_univ₀`：smul_set_univ₀ (ha : a != 0) : a • (univ : Set β) = 
univ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem fderiv_comp_smul (c : 𝕜) : fderiv 𝕜 (f <| c • ·) x = c • fderiv 𝕜 f (c • x) := by
  rw [← fderivWithin_univ, fderivWithin_comp_smul _ uniqueDiffWithinAt_univ]
  rcases eq_or_ne c 0 with rfl | hc <;> simp [smul_set_univ₀, *]
/-
**fderivWithin_comp_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_comp_neg {f : 𝕜 -> F} {s : Set 𝕜} {x : 𝕜} : fderivWithin 𝕜 (f
un a => f (-a)) s x = -fderivWithin 𝕜 f (-s) (-x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_comp_smul_eq_fderivWithin_smul`：fderivWithin_comp_smul_eq_f
derivWithin_smul (c : 𝕜) : fderivWithin 𝕜 (f <| c • ·) s x = fderivWithin 𝕜 (c •
 f) (c • s) (c • x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `Set.neg_smul_set`：neg_smul_set : -a • t = -(a • t)
· 使用引理 `fderivWithin_neg'`：fderivWithin_neg' {s : Set 𝕜} {f : 𝕜 -> F} {x : 𝕜} : 
fderivWithin 𝕜 (-f) s x = -fderivWithin 𝕜 f s x
-/
theorem fderivWithin_comp_neg {f : 𝕜 → F} {s : Set 𝕜} {x : 𝕜} :
    fderivWithin 𝕜 (fun a => f (-a)) s x = -fderivWithin 𝕜 f (-s) (-x) := by
  have t1 := fderivWithin_comp_smul_eq_fderivWithin_smul (-1 : 𝕜) (f := f) (s := s) (x := x)
  simp only [neg_smul, one_smul, Set.neg_smul_set] at t1
  exact t1.trans fderivWithin_neg'

end SMulLeft

