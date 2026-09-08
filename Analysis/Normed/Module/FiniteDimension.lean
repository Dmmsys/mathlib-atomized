/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Normed.Group.Lemmas
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Logic.Encodable.Pi
public import Mathlib.Topology.Algebra.AffineSubspace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Dual.Lemmas


/-!
# Finite-dimensional normed spaces over complete fields

Over a complete nontrivially normed field, in finite dimension, all norms are equivalent and all
linear maps are continuous. Moreover, a finite-dimensional subspace is always complete and closed.

## Main results:

* `FiniteDimensional.complete` : a finite-dimensional space over a complete field is complete. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution.
* `Submodule.closed_of_finiteDimensional` : a finite-dimensional subspace over a complete field is
  closed
* `FiniteDimensional.proper` : a finite-dimensional space over a proper field is proper. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution. It is however registered as an instance for `𝕜 = ℝ` and `𝕜 = ℂ`. As properness
  implies completeness, there is no need to also register `FiniteDimensional.complete` on `ℝ` or
  `ℂ`.
* `FiniteDimensional.of_isCompact_closedBall`: Riesz' theorem: if the closed unit ball is
  compact, then the space is finite-dimensional.

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'` to `E` are continuous thanks to
`LinearMap.continuous_of_finiteDimensional`. This gives the desired norm equivalence.
-/

@[expose] public section

universe u v w x

noncomputable section

open Asymptotics Filter Module Metric Module NNReal Set TopologicalSpace Topology

namespace LinearIsometry

open LinearMap

variable {F E₁ : Type*} [SeminormedAddCommGroup F] [NormedAddCommGroup E₁]
variable {R₁ : Type*} [Field R₁] [Module R₁ E₁] [Module R₁ F] [FiniteDimensional R₁ E₁]
  [FiniteDimensional R₁ F]

/-- A linear isometry between finite-dimensional spaces of equal dimension can be upgraded
to a linear isometry equivalence. -/
/-
**LinearIsometry.toLinearIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry
`。
形式化陈述：toLinearIsometryEquiv (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁
 F) : E₁ ≃ₗᵢ[R₁] F where toLinearEquiv
参数：li : E₁ ->ₗᵢ[R₁] F；h : finrank R₁ E₁ = finrank R₁ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear isometry between finite-dimensional spaces of equal dimension can be up
graded
to a linear isometry equivalence.
-/
def toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    E₁ ≃ₗᵢ[R₁] F where
  toLinearEquiv := li.toLinearMap.linearEquivOfInjective li.injective h
  norm_map' := li.norm_map'

@[simp]
/-
**LinearIsometry.coe_toLinearIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsom
etry`。
形式化陈述：coe_toLinearIsometryEquiv (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finran
k R₁ F) : (li.toLinearIsometryEquiv h : E₁ -> F) = li
参数：li : E₁ ->ₗᵢ[R₁] F；h : finrank R₁ E₁ = finrank R₁ F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    (li.toLinearIsometryEquiv h : E₁ → F) = li :=
  rfl

@[simp]
/-
**LinearIsometry.toLinearIsometryEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearIs
ometry`。
形式化陈述：toLinearIsometryEquiv_apply (li : E₁ ->ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finr
ank R₁ F) (x : E₁) : (li.toLinearIsometryEquiv h) x = li x
参数：li : E₁ ->ₗᵢ[R₁] F；h : finrank R₁ E₁ = finrank R₁ F；x : E₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearIsometryEquiv_apply (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
    (x : E₁) : (li.toLinearIsometryEquiv h) x = li x :=
  rfl

end LinearIsometry

namespace AffineIsometry

open AffineMap

variable {𝕜 : Type*} {V₁ V₂ : Type*} {P₁ P₂ : Type*} [NormedField 𝕜] [NormedAddCommGroup V₁]
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₁] [NormedSpace 𝕜 V₂] [MetricSpace P₁]
  [PseudoMetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]

variable [FiniteDimensional 𝕜 V₁] [FiniteDimensional 𝕜 V₂]

/-- An affine isometry between finite-dimensional spaces of equal dimension can be upgraded
to an affine isometry equivalence. -/
/-
**AffineIsometry.toAffineIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AffineIsometry
`。
形式化陈述：toAffineIsometryEquiv [Inhabited P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V
₁ = finrank 𝕜 V₂) : P₁ ≃ᵃⁱ[𝕜] P₂
参数：li : P₁ ->ᵃⁱ[𝕜] P₂；h : finrank 𝕜 V₁ = finrank 𝕜 V₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine isometry between finite-dimensional spaces of equal dimension can be u
pgraded
to an affine isometry equivalence.
-/
def toAffineIsometryEquiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
    P₁ ≃ᵃⁱ[𝕜] P₂ :=
  AffineIsometryEquiv.mk' li (li.linearIsometry.toLinearIsometryEquiv h)
    (Inhabited.default (α := P₁)) fun p => by simp

@[simp]
/-
**AffineIsometry.coe_toAffineIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AffineIsom
etry`。
形式化陈述：coe_toAffineIsometryEquiv [Inhabited P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂) (h : finrank
 𝕜 V₁ = finrank 𝕜 V₂) : (li.toAffineIsometryEquiv h : P₁ -> P₂) = li
参数：li : P₁ ->ᵃⁱ[𝕜] P₂；h : finrank 𝕜 V₁ = finrank 𝕜 V₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAffineIsometryEquiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂)
    (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) : (li.toAffineIsometryEquiv h : P₁ → P₂) = li :=
  rfl

@[simp]
/-
**AffineIsometry.toAffineIsometryEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineIs
ometry`。
形式化陈述：toAffineIsometryEquiv_apply [Inhabited P₁] (li : P₁ ->ᵃⁱ[𝕜] P₂) (h : finra
nk 𝕜 V₁ = finrank 𝕜 V₂) (x : P₁) : (li.toAffineIsometryEquiv h) x = li x
参数：li : P₁ ->ᵃⁱ[𝕜] P₂；h : finrank 𝕜 V₁ = finrank 𝕜 V₂；x : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineIsometryEquiv_apply [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂)
    (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) (x : P₁) : (li.toAffineIsometryEquiv h) x = li x :=
  rfl

end AffineIsometry

section CompleteField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜]

section Affine

variable {PE PF : Type*} [MetricSpace PE] [NormedAddTorsor E PE] [MetricSpace PF]
  [NormedAddTorsor F PF] [FiniteDimensional 𝕜 E]

/-
**AffineMap.continuous_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.continuous_of_finiteDimensional (f : PE ->ᵃ[𝕜] PF) : Continuous 
f
参数：f : PE ->ᵃ[𝕜] PF。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineMap.continuous_linear_iff`：continuous_linear_iff {f : P ->ᵃ[R] Q} 
: Continuous f.linear ↔ Continuous f
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
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
theorem AffineMap.continuous_of_finiteDimensional (f : PE →ᵃ[𝕜] PF) : Continuous f :=
  AffineMap.continuous_linear_iff.1 f.linear.continuous_of_finiteDimensional
/-
**AffineEquiv.continuous_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineEquiv.continuous_of_finiteDimensional (f : PE ≃ᵃ[𝕜] PF) : Continuous
 f
参数：f : PE ≃ᵃ[𝕜] PF。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.continuous_of_finiteDimensional`：AffineMap.continuous_of_finit
eDimensional (f : PE ->ᵃ[𝕜] PF) : Continuous f
-/
theorem AffineEquiv.continuous_of_finiteDimensional (f : PE ≃ᵃ[𝕜] PF) : Continuous f :=
  f.toAffineMap.continuous_of_finiteDimensional

/-- Reinterpret an affine equivalence as a continuous affine equivalence in finite dimension. -/
/-
**AffineEquiv.toContinuousAffineEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AffineEquiv.toContinuousAffineEquiv : (PE ≃ᵃ[𝕜] PF) ≃ (PE ≃ᴬ[𝕜] PF) where 
toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.continuous_of_finiteDimensional`：AffineEquiv.continuous_of_f
initeDimensional (f : PE ≃ᵃ[𝕜] PF) : Continuous f

--- 原说明 ---
Reinterpret an affine equivalence as a continuous affine equivalence in finite d
imension.
-/
def AffineEquiv.toContinuousAffineEquiv : (PE ≃ᵃ[𝕜] PF) ≃ (PE ≃ᴬ[𝕜] PF) where
  toFun f :=
    haveI := f.linear.finiteDimensional
    ⟨f, f.continuous_of_finiteDimensional, f.symm.continuous_of_finiteDimensional⟩
  invFun f := f.toAffineEquiv
  left_inv _ := rfl
  right_inv _ := ContinuousAffineEquiv.toAffineEquiv_injective rfl

@[simp]
/-
**AffineEquiv.coe_toContinuousAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineEquiv.coe_toContinuousAffineEquiv (f : PE ≃ᵃ[𝕜] PF) : ⇑(toContinuous
AffineEquiv f) = f
参数：f : PE ≃ᵃ[𝕜] PF。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AffineEquiv.coe_toContinuousAffineEquiv (f : PE ≃ᵃ[𝕜] PF) :
    ⇑(toContinuousAffineEquiv f) = f := rfl

@[simp]
/-
**AffineEquiv.toAffineEquiv_toContinuousAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：AffineEquiv.toAffineEquiv_toContinuousAffineEquiv (f : PE ≃ᵃ[𝕜] PF) : (toC
ontinuousAffineEquiv f).toAffineEquiv = f
参数：f : PE ≃ᵃ[𝕜] PF。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AffineEquiv.toAffineEquiv_toContinuousAffineEquiv (f : PE ≃ᵃ[𝕜] PF) :
    (toContinuousAffineEquiv f).toAffineEquiv = f := rfl

@[simp]
/-
**AffineEquiv.toContinuousAffineEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineEquiv.toContinuousAffineEquiv_symm_apply (f : PE ≃ᴬ[𝕜] PF) : toConti
nuousAffineEquiv.symm f = f.toAffineEquiv
参数：f : PE ≃ᴬ[𝕜] PF。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem AffineEquiv.toContinuousAffineEquiv_symm_apply (f : PE ≃ᴬ[𝕜] PF) :
    toContinuousAffineEquiv.symm f = f.toAffineEquiv := rfl

/-- Reinterpret an affine equivalence as a homeomorphism. -/
/-
**AffineEquiv.toHomeomorphOfFiniteDimensional** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AffineEquiv.toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) : PE ≃ₜ PF
参数：f : PE ≃ᵃ[𝕜] PF。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an affine equivalence as a homeomorphism.
-/
def AffineEquiv.toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) : PE ≃ₜ PF :=
  (toContinuousAffineEquiv f).toHomeomorph

@[simp]
/-
**AffineEquiv.coe_toHomeomorphOfFiniteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineEquiv.coe_toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) : ⇑f.toH
omeomorphOfFiniteDimensional = f
参数：f : PE ≃ᵃ[𝕜] PF。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional = f :=
  rfl

@[simp]
/-
**AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm (f : PE ≃ᵃ[𝕜] PF) : ⇑
f.toHomeomorphOfFiniteDimensional.symm = f.symm
参数：f : PE ≃ᵃ[𝕜] PF。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional.symm = f.symm :=
  rfl

attribute [deprecated AffineEquiv.toContinuousAffineEquiv (since := "2026-05-11")]
  AffineEquiv.toHomeomorphOfFiniteDimensional

/-- An affine map from a finite-dimensional space is automatically Lipschitz. -/
/-
**AffineMap.lipschitzWith_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.lipschitzWith_of_finiteDimensional (f : PE ->ᵃ[𝕜] PF) : exists K
 : Real>=0, LipschitzWith K f
参数：f : PE ->ᵃ[𝕜] PF。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddTorsor.dist_eq_norm'`：∀ {V : outParam (Type u_1)} {P : Type u_2
} {inst : SeminormedAddCommGroup V} {inst_1 : PseudoMetricSpace P}   [self : Nor
medAddTorsor V P] (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖

--- 原说明 ---
An affine map from a finite-dimensional space is automatically Lipschitz.
-/
theorem AffineMap.lipschitzWith_of_finiteDimensional (f : PE →ᵃ[𝕜] PF) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  let fL : E →L[𝕜] F := f.linear.toContinuousLinearMap
  refine ⟨‖fL‖₊, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  rw [NormedAddTorsor.dist_eq_norm', NormedAddTorsor.dist_eq_norm', ← f.linearMap_vsub]
  exact fL.le_opNorm _

end Affine

/-
**ContinuousLinearMap.continuous_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.continuous_det : Continuous fun f : E ->L[𝕜] E => f.de
t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.det_eq_det_toMatrix_of_finset`：det_eq_det_toMatrix_of_finset [
DecidableEq M] {s : Finset M} (b : Basis s A M) (f : M ->ₗ[A] M) : LinearMap.det
 f = Matrix.det (LinearMap.to…
· 使用定理 `Continuous.matrix_det`：Continuous.matrix_det [Fintype n] [DecidableEq n]
 [CommRing R] [IsTopologicalRing R] {A : X -> Matrix n n R} (hA : Continuous A) 
: Continuou…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instIsTopologicalAddGroupMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Ty
pe u_8} [inst : TopologicalSpace R] [inst_1 : AddGroup R]   [IsTopologicalAddGro
up R], IsTopologicalA…
· 使用定理 `instContinuousSMulMatrix`：∀ {α : Type u_2} {m : Type u_4} {n : Type u_5}
 {R : Type u_8} [inst : TopologicalSpace R] [inst_1 : TopologicalSpace α]   [ins
t_2 : SMul α R…
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `LinearMap.det_def`：∀ {M : Type u_7} [inst : AddCommGroup M] {A : Type u_
8} [inst_1 : CommRing A] [inst_2 : _root_.Module A M],   LinearMap.det = if H : 
∃ s, No…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 31 条，此处仅展示前 30 条）
-/
theorem ContinuousLinearMap.continuous_det : Continuous fun f : E →L[𝕜] E => f.det := by
  change Continuous fun f : E →L[𝕜] E => LinearMap.det (f : E →ₗ[𝕜] E)
  -- TODO: this could be easier with `det_cases`
  by_cases h : ∃ s : Finset E, Nonempty (Basis (↥s) 𝕜 E)
  · rcases h with ⟨s, ⟨b⟩⟩
    have : FiniteDimensional 𝕜 E := b.finiteDimensional_of_finite
    classical
    simp_rw [LinearMap.det_eq_det_toMatrix_of_finset b]
    refine Continuous.matrix_det ?_
    exact
      ((LinearMap.toMatrix b b).toLinearMap.comp
          (ContinuousLinearMap.coeLM 𝕜)).continuous_of_finiteDimensional
  · rw [LinearMap.det]
    simpa only [h, MonoidHom.one_apply, dif_neg, not_false_iff] using continuous_const

/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `C * K` where `C` only depends on `E'`. We record a working value for this constant `C`
as `lipschitzExtensionConstant E'`. -/
irreducible_def lipschitzExtensionConstant (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] : ℝ≥0 :=
  let A := (Basis.ofVectorSpace ℝ E').equivFun.toContinuousLinearEquiv
  max (‖A.symm.toContinuousLinearMap‖₊ * ‖A.toContinuousLinearMap‖₊) 1

/-
**lipschitzExtensionConstant_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzExtensionConstant_pos (E' : Type*) [NormedAddCommGroup E'] [Norme
dSpace Real E'] [FiniteDimensional Real E'] : 0 < lipschitzExtensionConstant E'
参数：E' : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lipschitzExtensionConstant_def`：∀ (E' : Type u_1) [inst : NormedAddCommG
roup E'] [inst_1 : NormedSpace ℝ E'] [inst_2 : FiniteDimensional ℝ E'],   lipsch
itzExtensionConstant…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem lipschitzExtensionConstant_pos (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] : 0 < lipschitzExtensionConstant E' := by
  rw [lipschitzExtensionConstant]
  exact zero_lt_one.trans_le (le_max_right _ _)

/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `lipschitzExtensionConstant E' * K`. -/
/-
**LipschitzOnWith.extend_finite_dimension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.extend_finite_dimension {α : Type*} [PseudoMetricSpace α] 
{E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E'] [FiniteDimensional Re
al E'] {s : Set α} {f : α -> E'} {K : Real>=0} (hf : LipschitzOnWith K f s) : ex
ists g : α -> E', LipschitzWith (lipschitzExtensionConstant E' * K) g ∧ EqOn f g
 s
参数：hf : LipschitzOnWith K f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ContinuousLinearEquiv.lipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : Nontrivia
llyNormedField 𝕜₂] [i…
· 使用定理 `LipschitzWith.comp_lipschitzOnWith`：comp_lipschitzOnWith {Kf Kg : Real>=
0} {f : β -> γ} {g : α -> β} {s : Set α} (hf : LipschitzWith Kf f) (hg : Lipschi
tzOnWith Kg g s) : Lipsc…
· 使用定理 `LipschitzOnWith.extend_pi`：LipschitzOnWith.extend_pi [Fintype ι] {f : α 
-> ι -> Real} {s : Set α} {K : Real>=0} (hf : LipschitzOnWith K f s) : exists g 
: α -> ι -> Rea…
· 使用定理 `LipschitzWith.weaken`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzWit
h K f → ∀ …
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lipschitzExtensionConstant_def`：∀ (E' : Type u_1) [inst : NormedAddCommG
roup E'] [inst_1 : NormedSpace ℝ E'] [inst_2 : FiniteDimensional ℝ E'],   lipsch
itzExtensionConstant…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimens
ional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, wit
h a slightly worse
constant `lipschitzExtensionConstant E' * K`.
-/
theorem LipschitzOnWith.extend_finite_dimension {α : Type*} [PseudoMetricSpace α] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {s : Set α} {f : α → E'}
    {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ g : α → E', LipschitzWith (lipschitzExtensionConstant E' * K) g ∧ EqOn f g s := by
  /- This result is already known for spaces `ι → ℝ`. We use a continuous linear equiv between
    `E'` and such a space to transfer the result to `E'`. -/
  let ι : Type _ := Basis.ofVectorSpaceIndex ℝ E'
  let A := (Basis.ofVectorSpace ℝ E').equivFun.toContinuousLinearEquiv
  have LA : LipschitzWith ‖A.toContinuousLinearMap‖₊ A := by apply A.lipschitz
  have L : LipschitzOnWith (‖A.toContinuousLinearMap‖₊ * K) (A ∘ f) s :=
    LA.comp_lipschitzOnWith hf
  obtain ⟨g, hg, gs⟩ :
    ∃ g : α → ι → ℝ, LipschitzWith (‖A.toContinuousLinearMap‖₊ * K) g ∧ EqOn (A ∘ f) g s :=
    L.extend_pi
  refine ⟨A.symm ∘ g, ?_, ?_⟩
  · have LAsymm : LipschitzWith ‖A.symm.toContinuousLinearMap‖₊ A.symm := by
      apply A.symm.lipschitz
    apply (LAsymm.comp hg).weaken
    rw [lipschitzExtensionConstant, ← mul_assoc]
    exact mul_le_mul' (le_max_left _ _) le_rfl
  · intro x hx
    have : A (f x) = g x := gs hx
    simp only [(· ∘ ·), ← this, A.symm_apply_apply]
/-
**LinearMap.exists_antilipschitzWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.exists_antilipschitzWith [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F
) (hf : LinearMap.ker f = ⊥) : exists K > 0, AntilipschitzWith K f
参数：f : E ->ₗ[𝕜] F；hf : LinearMap.ker f = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `AntilipschitzWith.of_subsingleton`：of_subsingleton [Subsingleton α] {K :
 Real>=0} : AntilipschitzWith K f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `ContinuousLinearEquiv.nnnorm_symm_pos`：nnnorm_symm_pos [RingHomIsometric
 σ₁₂] [Nontrivial E] (e : E ≃SL[σ₁₂] F) : 0 < ‖(e.symm : F ->SL[σ₂₁] E)‖₊
· 使用定理 `ContinuousLinearEquiv.antilipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E
 : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddC
ommGroup F] [inst_2 : Non…
-/
theorem LinearMap.exists_antilipschitzWith [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F)
    (hf : LinearMap.ker f = ⊥) : ∃ K > 0, AntilipschitzWith K f := by
  cases subsingleton_or_nontrivial E
  · exact ⟨1, zero_lt_one, AntilipschitzWith.of_subsingleton⟩
  · rw [LinearMap.ker_eq_bot] at hf
    let e : E ≃L[𝕜] LinearMap.range f := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv
    exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩

open Function in
/-- A `LinearMap` on a finite-dimensional space over a complete field
  is injective iff it is anti-Lipschitz. -/
/-
**LinearMap.injective_iff_antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.injective_iff_antilipschitz [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜
] F) : Injective f ↔ exists K > 0, AntilipschitzWith K f
参数：f : E ->ₗ[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearMap.exists_antilipschitzWith`：LinearMap.exists_antilipschitzWith [
FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F) (hf : LinearMap.ker f = ⊥) : exists K > 
0, AntilipschitzWith K f
· 使用定理 `AntilipschitzWith.injective`：∀ {α : Type u_4} {β : Type u_5} [inst : EMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Antilip
schitzWith K f → …

--- 原说明 ---
A `LinearMap` on a finite-dimensional space over a complete field
  is injective iff it is anti-Lipschitz.
-/
theorem LinearMap.injective_iff_antilipschitz [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F) :
    Injective f ↔ ∃ K > 0, AntilipschitzWith K f := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    exact f.exists_antilipschitzWith
  · rintro ⟨K, -, H⟩
    exact H.injective

/-- An injective affine map from a finite-dimensional space is automatically anti-Lipschitz. -/
/-
**AffineMap.antilipschitzWith_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.antilipschitzWith_of_finiteDimensional {PE PF : Type*} [MetricSp
ace PE] [NormedAddTorsor E PE] [MetricSpace PF] [NormedAddTorsor F PF] [FiniteDi
mensional 𝕜 E] {f : PE ->ᵃ[𝕜] PF} (hf : Function.Injective f) : exists K : Real>
=0, AntilipschitzWith K f
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.injective_iff_antilipschitz`：LinearMap.injective_iff_antilipsc
hitz [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F) : Injective f ↔ exists K > 0, Anti
lipschitzWith K f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AffineMap.linear_injective_iff`：linear_injective_iff (f : P1 ->ᵃ[k] P2) 
: Function.Injective f.linear ↔ Function.Injective f
· 使用定理 `AntilipschitzWith.of_le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst 
: PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β}, 
  (∀ (x y : α), dist x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `ZeroHomClass.bound_of_antilipschitz`：∀ {𝓕 : Type u_1} {E : Type u_2} {F 
: Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [ins
t_2 : FunLike 𝓕 E F] [Zer…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…

--- 原说明 ---
An injective affine map from a finite-dimensional space is automatically anti-Li
pschitz.
-/
theorem AffineMap.antilipschitzWith_of_finiteDimensional {PE PF : Type*} [MetricSpace PE]
    [NormedAddTorsor E PE] [MetricSpace PF] [NormedAddTorsor F PF] [FiniteDimensional 𝕜 E]
    {f : PE →ᵃ[𝕜] PF} (hf : Function.Injective f) :
    ∃ K : ℝ≥0, AntilipschitzWith K f := by
  obtain ⟨K, -, hK⟩ := f.linear.injective_iff_antilipschitz.mp (f.linear_injective_iff.mpr hf)
  refine ⟨K, AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_⟩
  rw [dist_eq_norm_vsub E, dist_eq_norm_vsub F, ← f.linearMap_vsub]
  exact ZeroHomClass.bound_of_antilipschitz f.linear hK (x -ᵥ y)

open Function in
/-- The set of injective continuous linear maps `E → F` is open,
  if `E` is finite-dimensional over a complete field. -/
/-
**ContinuousLinearMap.isOpen_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.isOpen_injective [FiniteDimensional 𝕜 E] : IsOpen { L 
: E ->L[𝕜] F | Injective L }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_eventually`：isOpen_iff_eventually : IsOpen s ↔ forall x, x in
 s -> forallᶠ y in 𝓝 x, y in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.injective_iff_antilipschitz`：LinearMap.injective_iff_antilipsc
hitz [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F) : Injective f ↔ exists K > 0, Anti
lipschitzWith K f
· 使用定理 `eventually_nnnorm_sub_lt`：eventually_nnnorm_sub_lt (x₀ : E) {ε : Real>=0
} (ε_pos : 0 < ε) : forallᶠ x in 𝓝 x₀, ‖x - x₀‖₊ < ε
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `AntilipschitzWith.add_sub_lipschitzWith`：∀ {α : Type u_4} {E : Type u_5}
 [inst : SeminormedAddCommGroup E] [inst_1 : PseudoEMetricSpace α] {Kf Kg : NNRe
al}   {f g : α → E}, Antilips…
· 使用定理 `ContinuousLinearMap.lipschitz`：lipschitz (f : E ->SL[σ₁₂] F) : Lipschitz
With ‖f‖₊ f

--- 原说明 ---
The set of injective continuous linear maps `E → F` is open,
  if `E` is finite-dimensional over a complete field.
-/
theorem ContinuousLinearMap.isOpen_injective [FiniteDimensional 𝕜 E] :
    IsOpen { L : E →L[𝕜] F | Injective L } := by
  rw [isOpen_iff_eventually]
  rintro φ₀ hφ₀
  rcases φ₀.injective_iff_antilipschitz.mp hφ₀ with ⟨K, K_pos, H⟩
  have : ∀ᶠ φ in 𝓝 φ₀, ‖φ - φ₀‖₊ < K⁻¹ := eventually_nnnorm_sub_lt _ <| inv_pos_of_pos K_pos
  filter_upwards [this] with φ hφ
  apply φ.injective_iff_antilipschitz.mpr
  exact ⟨(K⁻¹ - ‖φ - φ₀‖₊)⁻¹, inv_pos_of_pos (tsub_pos_of_lt hφ),
    H.add_sub_lipschitzWith (φ - φ₀).lipschitz hφ⟩

open ContinuousLinearMap

/-- Continuous linear equivalence between continuous linear functions `𝕜ⁿ → E` and `Eⁿ`.
The spaces `𝕜ⁿ` and `Eⁿ` are represented as `ι → 𝕜` and `ι → E`, respectively,
where `ι` is a finite type. -/
/-
**ContinuousLinearEquiv.piRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.piRing (ι : Type*) [Fintype ι] [DecidableEq ι] : ((ι
 -> 𝕜) ->L[𝕜] E) ≃L[𝕜] ι -> E
参数：ι : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear equivalence between continuous linear functions `𝕜ⁿ → E` and `
Eⁿ`.
The spaces `𝕜ⁿ` and `Eⁿ` are represented as `ι → 𝕜` and `ι → E`, respectively,
where `ι` is a finite type.
-/
def ContinuousLinearEquiv.piRing (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ((ι → 𝕜) →L[𝕜] E) ≃L[𝕜] ι → E :=
  { LinearMap.toContinuousLinearMap.symm.trans (LinearEquiv.piRing 𝕜 E ι 𝕜) with
    continuous_invFun := by
      simp_rw [LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
      refine AddMonoidHomClass.continuous_of_bound
        (LinearMap.toContinuousLinearMap.toLinearMap.comp
            (LinearEquiv.piRing 𝕜 E ι 𝕜).symm.toLinearMap)
        (Fintype.card ι : ℝ) fun g ↦ ?_
      rw [← nsmul_eq_mul]
      refine opNorm_le_bound _ (nsmul_nonneg (norm_nonneg g) (Fintype.card ι)) fun t ↦ ?_
      simp_rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
        LinearMap.coe_toContinuousLinearMap', LinearEquiv.piRing_symm_apply]
      apply le_trans (norm_sum_le _ _)
      rw [smul_mul_assoc]
      refine Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ ?_
      rw [norm_smul, mul_comm]
      gcongr <;> apply norm_le_pi_norm }
/-
**LinearIndependent.eventually** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndependent`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {E : Type v} [inst_1 : N
ormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [CompleteSpace 𝕜] {ι : Type u_
1} [Finite ι] {f : ι → E},   LinearIndependent 𝕜 f → ∀ᶠ (g : ι → E) in nhds f, L
inearIndependent 𝕜 g
参数：g : ι → E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.exists_antilipschitzWith`：LinearMap.exists_antilipschitzWith [
FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F) (hf : LinearMap.ker f = ⊥) : exists K > 
0, AntilipschitzWith K f
· 使用定理 `tendsto_finsetSum`：∀ {ι : Type u_1} {α : Type u_2} {M : Type u_3} [inst 
: TopologicalSpace M] [inst_1 : AddCommMonoid M] [ContinuousAdd M]   {f : ι → α 
→ M} {x…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 50 条，此处仅展示前 30 条）
-/
protected theorem LinearIndependent.eventually {ι} [Finite ι] {f : ι → E}
    (hf : LinearIndependent 𝕜 f) : ∀ᶠ g in 𝓝 f, LinearIndependent 𝕜 g := by
  cases nonempty_fintype ι
  classical
  simp only [Fintype.linearIndependent_iff'] at hf ⊢
  rcases LinearMap.exists_antilipschitzWith _ hf with ⟨K, K0, hK⟩
  have : Tendsto (fun g : ι → E => ∑ i, ‖g i - f i‖) (𝓝 f) (𝓝 <| ∑ i, ‖f i - f i‖) :=
    tendsto_finsetSum _ fun i _ =>
      Tendsto.norm <| ((continuous_apply i).tendsto _).sub tendsto_const_nhds
  simp only [sub_self, norm_zero, Finset.sum_const_zero] at this
  refine (this.eventually (gt_mem_nhds <| inv_pos.2 K0)).mono fun g hg => ?_
  replace hg : ∑ i, ‖g i - f i‖₊ < K⁻¹ := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    exact hg
  rw [LinearMap.ker_eq_bot]
  refine (hK.add_sub_lipschitzWith (LipschitzWith.of_dist_le_mul fun v u => ?_) hg).injective
  simp only [dist_eq_norm, LinearMap.lsum_apply, Pi.sub_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smulRight_apply, LinearMap.id_apply, ←
    Finset.sum_sub_distrib, ← smul_sub, ← sub_smul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_smul, mul_comm]
  gcongr
  exact norm_le_pi_norm (v - u) i
/-
**isOpen_setOfPred_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_setOfPred_linearIndependent {ι : Type*} [Finite ι] : IsOpen { f : ι
 -> E | LinearIndependent 𝕜 f }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `LinearIndependent.eventually`：∀ {𝕜 : Type u} [inst : NontriviallyNormedF
ield 𝕜] {E : Type v} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] [CompleteSpace 𝕜…
-/
theorem isOpen_setOfPred_linearIndependent {ι : Type*} [Finite ι] :
    IsOpen { f : ι → E | LinearIndependent 𝕜 f } :=
  isOpen_iff_mem_nhds.2 fun _ => LinearIndependent.eventually

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_linearIndependent := isOpen_setOfPred_linearIndependent
/-
**isOpen_setOfPred_nat_le_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_setOfPred_nat_le_rank (n : Nat) : IsOpen { f : E ->L[𝕜] F | ↑n <= (
f : E ->ₗ[𝕜] F).rank }
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `isOpen_setOfPred_linearIndependent`：isOpen_setOfPred_linearIndependent {
ι : Type*} [Finite ι] : IsOpen { f : ι -> E | LinearIndependent 𝕜 f }
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem isOpen_setOfPred_nat_le_rank (n : ℕ) :
    IsOpen { f : E →L[𝕜] F | ↑n ≤ (f : E →ₗ[𝕜] F).rank } := by
  simp only [LinearMap.le_rank_iff_exists_linearIndependent_finset, ofPred_exists, ← exists_prop]
  refine isOpen_biUnion fun t _ => ?_
  have : Continuous fun f : E →L[𝕜] F => fun x : (t : Set E) => f x :=
    continuous_pi fun x => (ContinuousLinearMap.apply 𝕜 F (x : E)).continuous
  exact isOpen_setOfPred_linearIndependent.preimage this

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_nat_le_rank := isOpen_setOfPred_nat_le_rank
/-
**isOpen_setOfPred_affineIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_setOfPred_affineIndependent {ι : Type*} [Finite ι] : IsOpen {p : ι 
-> E | AffineIndependent 𝕜 p}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.instOfFiniteOfDiscreteTopology`：∀ {Y : Type u_2} [Fin
ite Y] [inst : UniformSpace Y] [DiscreteTopology Y], DiscreteUniformity Y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instT1SpaceForall`：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i : ι) →
 TopologicalSpace (X i)] [∀ (i : ι), T1Space (X i)],   T1Space ((i : ι) → X i)
· 使用定理 `T4Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T4
Space X], T1Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `affineIndependent_iff_linearIndependent_vsub`：affineIndependent_iff_line
arIndependent_vsub (p : ι -> P) (i1 : ι) : AffineIndependent k p ↔ LinearIndepen
dent k fun i : { x // x != i1 } =>…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.vsub`：∀ {V : Type u_1} {P : Type u_2} {α : Type u_3} [inst : 
AddGroup V] [inst_1 : TopologicalSpace V]   [inst_2 : AddTorsor V P] [inst_3 : T
opolo…
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `isOpen_setOfPred_linearIndependent`：isOpen_setOfPred_linearIndependent {
ι : Type*} [Finite ι] : IsOpen { f : ι -> E | LinearIndependent 𝕜 f }
-/
theorem isOpen_setOfPred_affineIndependent {ι : Type*} [Finite ι] :
    IsOpen {p : ι → E | AffineIndependent 𝕜 p} := by
  classical
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i₀⟩⟩
  · exact isOpen_discrete _
  · simp_rw [affineIndependent_iff_linearIndependent_vsub 𝕜 _ i₀]
    let ι' := { x // x ≠ i₀ }
    cases nonempty_fintype ι
    have : Fintype ι' := Subtype.fintype _
    convert_to!
      IsOpen ((fun (p : ι → E) (i : ι') ↦ p i -ᵥ p i₀) ⁻¹' {p : ι' → E | LinearIndependent 𝕜 p})
    exact isOpen_setOfPred_linearIndependent.preimage (by fun_prop)

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_affineIndependent := isOpen_setOfPred_affineIndependent

namespace Module.Basis

set_option backward.isDefEq.respectTransparency false in
/-
**Module.Basis.opNNNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：opNNNorm_le {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E ->L[𝕜] F} (M 
: Real>=0) (hu : forall i, ‖u (v i)‖₊ <= M) : ‖u‖₊ <= Fintype.card ι • ‖v.equivF
unL.toContinuousLinearMap‖₊ * M
参数：v : Basis ι 𝕜 E；M : Real>=0；hu : forall i, ‖u (v i)‖₊ <= M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNNNorm_le_bound`：opNNNorm_le_bound (f : E ->SL[σ₁₂
] F) (M : Real>=0) (hM : forall x, ‖f x‖₊ <= M * ‖x‖₊) : ‖f‖₊ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.sum_equivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6
} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : Finty…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `nnnorm_sum_le`：∀ {ι : Type u_3} {E : Type u_5} [inst : SeminormedAddComm
Group E] (s : Finset ι) (f : ι → E),   ‖∑ a ∈ s, f a‖₊ ≤ ∑ a ∈ s, ‖f a‖₊
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Pi.sum_nnnorm_apply_le_nnnorm`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst
 : Fintype ι] [inst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i
), ∑ i, ‖f i‖₊ ≤ Fi…
· 使用定理 `nsmul_le_nsmul_right`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pr
eorder M] [AddLeftMono M] [AddRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), i • a
 ≤ i • b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 34 条，此处仅展示前 30 条）
-/
theorem opNNNorm_le {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E →L[𝕜] F} (M : ℝ≥0)
    (hu : ∀ i, ‖u (v i)‖₊ ≤ M) : ‖u‖₊ ≤ Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖₊ * M :=
  u.opNNNorm_le_bound _ fun e => by
    set φ := v.equivFunL.toContinuousLinearMap
    calc
      ‖u e‖₊ = ‖u (∑ i, v.equivFun e i • v i)‖₊ := by rw [v.sum_equivFun]
      _ = ‖∑ i, v.equivFun e i • (u <| v i)‖₊ := by simp only [equivFun_apply, map_sum, map_smul]
      _ ≤ ∑ i, ‖v.equivFun e i • (u <| v i)‖₊ := nnnorm_sum_le _ _
      _ = ∑ i, ‖v.equivFun e i‖₊ * ‖u (v i)‖₊ := by simp only [nnnorm_smul]
      _ ≤ ∑ i, ‖v.equivFun e i‖₊ * M := by gcongr; apply hu
      _ = (∑ i, ‖v.equivFun e i‖₊) * M := by rw [Finset.sum_mul]
      _ ≤ Fintype.card ι • (‖φ‖₊ * ‖e‖₊) * M := by
        gcongr
        calc
          ∑ i, ‖v.equivFun e i‖₊ ≤ Fintype.card ι • ‖φ e‖₊ := Pi.sum_nnnorm_apply_le_nnnorm _
          _ ≤ Fintype.card ι • (‖φ‖₊ * ‖e‖₊) := nsmul_le_nsmul_right (φ.le_opNNNorm e) _
      _ = Fintype.card ι • ‖φ‖₊ * M * ‖e‖₊ := by simp only [smul_mul_assoc, mul_right_comm]
/-
**Module.Basis.opNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：opNorm_le {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E ->L[𝕜] F} {M : 
Real} (hM : 0 <= M) (hu : forall i, ‖u (v i)‖ <= M) : ‖u‖ <= Fintype.card ι • ‖v
.equivFunL.toContinuousLinearMap‖ * M
参数：v : Basis ι 𝕜 E；hM : 0 <= M；hu : forall i, ‖u (v i)‖ <= M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `Module.Basis.opNNNorm_le`：opNNNorm_le {ι : Type*} [Fintype ι] (v : Basis
 ι 𝕜 E) {u : E ->L[𝕜] F} (M : Real>=0) (hu : forall i, ‖u (v i)‖₊ <= M) : ‖u‖₊ <
= Fintype.card…
-/
theorem opNorm_le {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E →L[𝕜] F} {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ i, ‖u (v i)‖ ≤ M) :
    ‖u‖ ≤ Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖ * M := by
  simpa using! NNReal.coe_le_coe.mpr (v.opNNNorm_le ⟨M, hM⟩ hu)

/-- A weaker version of `Basis.opNNNorm_le` that abstracts away the value of `C`. -/
/-
**Module.Basis.exists_opNNNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：exists_opNNNorm_le {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E) : exists C > (
0 : Real>=0), forall {u : E ->L[𝕜] F} (M : Real>=0), (forall i, ‖u (v i)‖₊ <= M)
 -> ‖u‖₊ <= C * M
参数：v : Basis ι 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Basis.opNNNorm_le`：opNNNorm_le {ι : Type*} [Fintype ι] (v : Basis
 ι 𝕜 E) {u : E ->L[𝕜] F} (M : Real>=0) (hu : forall i, ‖u (v i)‖₊ <= M) : ‖u‖₊ <
= Fintype.card…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
A weaker version of `Basis.opNNNorm_le` that abstracts away the value of `C`.
-/
theorem exists_opNNNorm_le {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E) :
    ∃ C > (0 : ℝ≥0), ∀ {u : E →L[𝕜] F} (M : ℝ≥0), (∀ i, ‖u (v i)‖₊ ≤ M) → ‖u‖₊ ≤ C * M := by
  cases nonempty_fintype ι
  exact
    ⟨max (Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖₊) 1,
      zero_lt_one.trans_le (le_max_right _ _), fun {u} M hu =>
      (v.opNNNorm_le M hu).trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le⟩

/-- A weaker version of `Basis.opNorm_le` that abstracts away the value of `C`. -/
/-
**Module.Basis.exists_opNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：exists_opNorm_le {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E) : exists C > (0 
: Real), forall {u : E ->L[𝕜] F} {M : Real}, 0 <= M -> (forall i, ‖u (v i)‖ <= M
) -> ‖u‖ <= C * M
参数：v : Basis ι 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.exists_opNNNorm_le`：exists_opNNNorm_le {ι : Type*} [Finite 
ι] (v : Basis ι 𝕜 E) : exists C > (0 : Real>=0), forall {u : E ->L[𝕜] F} (M : Re
al>=0), (forall i, ‖u…

--- 原说明 ---
A weaker version of `Basis.opNorm_le` that abstracts away the value of `C`.
-/
theorem exists_opNorm_le {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E) :
    ∃ C > (0 : ℝ), ∀ {u : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ‖u (v i)‖ ≤ M) → ‖u‖ ≤ C * M := by
  obtain ⟨C, hC, h⟩ := v.exists_opNNNorm_le (F := F)
  refine ⟨C, hC, ?_⟩
  intro u M hM H
  simpa using! h ⟨M, hM⟩ H

end Module.Basis

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FiniteDimensional 𝕜 E] [SecondCountableTopology F] :
    SecondCountableTopology (E →L[𝕜] F) := by
  let d := Module.finrank 𝕜 E
  let e₁ : E ≃L[𝕜] Fin d → 𝕜 :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm
  let e₂ : (E →L[𝕜] F) ≃L[𝕜] Fin d → F :=
    (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  exact e₂.toHomeomorph.secondCountableTopology
/-
**AffineSubspace.closed_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineSubspace.closed_of_finiteDimensional {P : Type*} [MetricSpace P] [No
rmedAddTorsor E P] (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] : 
IsClosed (s : Set P)
参数：s : AffineSubspace 𝕜 P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.isClosed_direction_iff`：isClosed_direction_iff [T1Space V
] (s : AffineSubspace R P) : IsClosed (s.direction : Set V) ↔ IsClosed (s : Set 
P)
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Submodule.closed_of_finiteDimensional`：Submodule.closed_of_finiteDimensi
onal [T2Space E] (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsClosed (s : Set
 E)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem AffineSubspace.closed_of_finiteDimensional {P : Type*} [MetricSpace P]
    [NormedAddTorsor E P] (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] :
    IsClosed (s : Set P) :=
  s.isClosed_direction_iff.mp s.direction.closed_of_finiteDimensional

section Riesz

/-- In an infinite-dimensional space, given a finite number of points, one may find a point
with norm at most `R` which is at distance at least `1` of all these points. -/
/-
**exists_norm_le_le_norm_sub_of_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_norm_le_le_norm_sub_of_finset {c : 𝕜} (hc : 1 < ‖c‖) {R : Real} (hR
 : ‖c‖ < R) (h : ¬FiniteDimensional 𝕜 E) (s : Finset E) : exists x : E, ‖x‖ <= R
 ∧ forall y in s, 1 <= ‖y - x‖
参数：hc : 1 < ‖c‖；hR : ‖c‖ < R；h : ¬FiniteDimensional 𝕜 E；s : Finset E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `Submodule.closed_of_finiteDimensional`：Submodule.closed_of_finiteDimensi
onal [T2Space E] (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsClosed (s : Set
 E)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `riesz_lemma_of_norm_lt`：riesz_lemma_of_norm_lt {c : 𝕜} (hc : 1 < ‖c‖) {R
 : Real} (hR : ‖c‖ < R) {F : Subspace 𝕜 E} (hFc : IsClosed (F : Set E)) (hF : ex
ists x : E, …
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s

--- 原说明 ---
In an infinite-dimensional space, given a finite number of points, one may find 
a point
with norm at most `R` which is at distance at least `1` of all these points.
-/
theorem exists_norm_le_le_norm_sub_of_finset {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R)
    (h : ¬FiniteDimensional 𝕜 E) (s : Finset E) : ∃ x : E, ‖x‖ ≤ R ∧ ∀ y ∈ s, 1 ≤ ‖y - x‖ := by
  let F := Submodule.span 𝕜 (s : Set E)
  have hF : F.FG := ⟨s, rfl⟩
  have : FiniteDimensional 𝕜 F := .of_fg hF
  have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finiteDimensional _
  have : ∃ x, x ∉ F := by
    contrapose! h
    have : (⊤ : Submodule 𝕜 E) = F := by
      ext x
      simp [h]
    rw [← this] at hF
    exact .of_fg_top hF
  obtain ⟨x, xR, hx⟩ : ∃ x : E, ‖x‖ ≤ R ∧ ∀ y : E, y ∈ F → 1 ≤ ‖x - y‖ :=
    riesz_lemma_of_norm_lt hc hR Fclosed this
  have hx' : ∀ y : E, y ∈ F → 1 ≤ ‖y - x‖ := by
    intro y hy
    rw [← norm_neg]
    simpa using hx y hy
  exact ⟨x, xR, fun y hy => hx' _ (Submodule.subset_span hy)⟩

/-- In an infinite-dimensional normed space, there exists a sequence of points which are all
bounded by `R` and at distance at least `1`. For a version not assuming `c` and `R`, see
`exists_seq_norm_le_one_le_norm_sub`. -/
/-
**exists_seq_norm_le_one_le_norm_sub'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_norm_le_one_le_norm_sub' {c : 𝕜} (hc : 1 < ‖c‖) {R : Real} (hR 
: ‖c‖ < R) (h : ¬FiniteDimensional 𝕜 E) : exists f : Nat -> E, (forall n, ‖f n‖ 
<= R) ∧ Pairwise fun m n => 1 <= ‖f m - f n‖
参数：hc : 1 < ‖c‖；hR : ‖c‖ < R；h : ¬FiniteDimensional 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `exists_seq_of_forall_finset_exists'`：exists_seq_of_forall_finset_exists'
 {α : Type*} (P : α -> Prop) (r : α -> α -> Prop) [Std.Symm r] (h : forall s : F
inset α, (forall x in s, …
· 使用定理 `exists_norm_le_le_norm_sub_of_finset`：exists_norm_le_le_norm_sub_of_fins
et {c : 𝕜} (hc : 1 < ‖c‖) {R : Real} (hR : ‖c‖ < R) (h : ¬FiniteDimensional 𝕜 E)
 (s : Finset E) : exists x…

--- 原说明 ---
In an infinite-dimensional normed space, there exists a sequence of points which
 are all
bounded by `R` and at distance at least `1`. For a version not assuming `c` and 
`R`, see
`exists_seq_norm_le_one_le_norm_sub`.
-/
theorem exists_seq_norm_le_one_le_norm_sub' {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R)
    (h : ¬FiniteDimensional 𝕜 E) :
    ∃ f : ℕ → E, (∀ n, ‖f n‖ ≤ R) ∧ Pairwise fun m n => 1 ≤ ‖f m - f n‖ := by
  have : Std.Symm fun x y : E => 1 ≤ ‖x - y‖ := by
    constructor
    intro x y hxy
    rw [← norm_neg]
    simpa
  apply
    exists_seq_of_forall_finset_exists' (fun x : E => ‖x‖ ≤ R) fun (x : E) (y : E) => 1 ≤ ‖x - y‖
  rintro s -
  exact exists_norm_le_le_norm_sub_of_finset hc hR h s
/-
**exists_seq_norm_le_one_le_norm_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_norm_le_one_le_norm_sub (h : ¬FiniteDimensional 𝕜 E) : exists (
R : Real) (f : Nat -> E), 1 < R ∧ (forall n, ‖f n‖ <= R) ∧ Pairwise fun m n => 1
 <= ‖f m - f n‖
参数：h : ¬FiniteDimensional 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 40 条，此处仅展示前 30 条）
-/
theorem exists_seq_norm_le_one_le_norm_sub (h : ¬FiniteDimensional 𝕜 E) :
    ∃ (R : ℝ) (f : ℕ → E), 1 < R ∧ (∀ n, ‖f n‖ ≤ R) ∧ Pairwise fun m n => 1 ≤ ‖f m - f n‖ := by
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, 1 < ‖c‖ := NormedField.exists_one_lt_norm 𝕜
  have A : ‖c‖ < ‖c‖ + 1 := by linarith
  rcases exists_seq_norm_le_one_le_norm_sub' hc A h with ⟨f, hf⟩
  exact ⟨‖c‖ + 1, f, hc.trans A, hf.1, hf.2⟩

variable (𝕜)

/-- **Riesz's theorem**: if a closed ball with center zero of positive radius is compact in a vector
space, then the space is finite-dimensional. -/
/-
**FiniteDimensional.of_isCompact_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.of_isCompact_closedBall {V : Type*} [NormedAddCommGroup 
V] [Module 𝕜 V] [ContinuousSMul 𝕜 V] {r : Real} (rpos : 0 < r) {c : V} (h : IsCo
mpact (Metric.closedBall c r)) : FiniteDimensional 𝕜 V
参数：rpos : 0 < r；h : IsCompact (Metric.closedBall c r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_isCompact_closedBall₀`：FiniteDimensional.of_isCompa
ct_closedBall₀ {V : Type*} [NormedAddCommGroup V] [Module 𝕜 V] [ContinuousSMul 𝕜
 V] {r : Real} (rpos : 0 < r) (h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Metric.vadd_closedBall`：∀ {G : Type v} {X : Type w} [inst : PseudoMetric
Space X] [inst_1 : AddGroup G] [inst_2 : AddAction G X]   [IsIsometricVAdd G X] 
(c : G) (x :…
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `IsCompact.vadd`：∀ {α : Type u_4} {β : Type u_5} [inst : VAdd α β] [inst_
1 : TopologicalSpace β] [ContinuousConstVAdd α β] (a : α)   {s : Set β}, IsCompa
ct s…
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
**Riesz's theorem**: if a closed ball with center zero of positive radius is com
pact in a vector
space, then the space is finite-dimensional.
-/
theorem FiniteDimensional.of_isCompact_closedBall₀ {V : Type*} [NormedAddCommGroup V] [Module 𝕜 V]
    [ContinuousSMul 𝕜 V] {r : ℝ} (rpos : 0 < r) (h : IsCompact (Metric.closedBall (0 : V) r)) :
    FiniteDimensional 𝕜 V :=
  .of_totallyBounded_nhds_zero 𝕜 (Metric.closedBall_mem_nhds 0 rpos) h.totallyBounded

/-- **Riesz's theorem**: if a closed ball of positive radius is compact in a vector space, then the
space is finite-dimensional. -/
/-
**FiniteDimensional.of_isCompact_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.of_isCompact_closedBall {V : Type*} [NormedAddCommGroup 
V] [Module 𝕜 V] [ContinuousSMul 𝕜 V] {r : Real} (rpos : 0 < r) {c : V} (h : IsCo
mpact (Metric.closedBall c r)) : FiniteDimensional 𝕜 V
参数：rpos : 0 < r；h : IsCompact (Metric.closedBall c r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_isCompact_closedBall₀`：FiniteDimensional.of_isCompa
ct_closedBall₀ {V : Type*} [NormedAddCommGroup V] [Module 𝕜 V] [ContinuousSMul 𝕜
 V] {r : Real} (rpos : 0 < r) (h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Metric.vadd_closedBall`：∀ {G : Type v} {X : Type w} [inst : PseudoMetric
Space X] [inst_1 : AddGroup G] [inst_2 : AddAction G X]   [IsIsometricVAdd G X] 
(c : G) (x :…
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `IsCompact.vadd`：∀ {α : Type u_4} {β : Type u_5} [inst : VAdd α β] [inst_
1 : TopologicalSpace β] [ContinuousConstVAdd α β] (a : α)   {s : Set β}, IsCompa
ct s…
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
**Riesz's theorem**: if a closed ball of positive radius is compact in a vector 
space, then the
space is finite-dimensional.
-/
theorem FiniteDimensional.of_isCompact_closedBall {V : Type*} [NormedAddCommGroup V] [Module 𝕜 V]
    [ContinuousSMul 𝕜 V] {r : ℝ} (rpos : 0 < r) {c : V} (h : IsCompact (Metric.closedBall c r)) :
    FiniteDimensional 𝕜 V :=
  .of_isCompact_closedBall₀ 𝕜 rpos <| by simpa using h.vadd (-c)

/-- A locally compact normed vector space is proper. -/
/-
**ProperSpace.of_locallyCompactSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ProperSpace.of_locallyCompactSpace (𝕜 : Type*) [NontriviallyNormedField 𝕜]
 {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E
] : ProperSpace E
参数：𝕜 : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.exists_isCompact_closedBall`：exists_isCompact_closedBall [WeaklyL
ocallyCompactSpace α] (x : α) : exists r, 0 < r ∧ IsCompact (closedBall x r)
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `smul_closedBall'`：smul_closedBall' {c : 𝕜} (hc : c != 0) (x : E) (r : Re
al) : c • closedBall x r = closedBall (c • x) (‖c‖ * r)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `IsCompact.smul`：IsCompact.smul {α β} [SMul α β] [TopologicalSpace β] [Co
ntinuousConstSMul α β] (a : α) {s : Set β} (hs : IsCompact s) : IsCompact (a • s
)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Filter.Tendsto.atTop_mul_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `tendsto_pow_atTop_atTop_of_one_lt`：tendsto_pow_atTop_atTop_of_one_lt [Se
miring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean
 α] {r : α} (h : 1 < r)…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `ProperSpace.of_seq_closedBall`：ProperSpace.of_seq_closedBall {β : Type*}
 {l : Filter β} [NeBot l] {x : α} {r : β -> Real} (hr : Tendsto r l atTop) (hc :
 forallᶠ i in l, Is…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
A locally compact normed vector space is proper.
-/
lemma ProperSpace.of_locallyCompactSpace (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E] : ProperSpace E := by
  rcases exists_isCompact_closedBall (0 : E) with ⟨r, rpos, hr⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have hC : ∀ n, IsCompact (closedBall (0 : E) (‖c‖ ^ n * r)) := fun n ↦ by
    have : c ^ n ≠ 0 := pow_ne_zero _ <| fun h ↦ by simp [h, zero_le_one.not_gt] at hc
    simpa [_root_.smul_closedBall' this] using hr.smul (c ^ n)
  have hTop : Tendsto (fun n ↦ ‖c‖ ^ n * r) atTop atTop :=
    Tendsto.atTop_mul_const rpos (tendsto_pow_atTop_atTop_of_one_lt hc)
  exact .of_seq_closedBall hTop (Eventually.of_forall hC)
/-
**ProperSpace.of_locallyCompact_module** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ProperSpace.of_locallyCompact_module (V : Type*) [AddCommGroup V] [Topolog
icalSpace V] [IsTopologicalAddGroup V] [T2Space V] [Nontrivial V] [LocallyCompac
tSpace V] [Module 𝕜 V] [ContinuousSMul 𝕜 V] : ProperSpace 𝕜
参数：V : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `isClosedEmbedding_smul_left`：isClosedEmbedding_smul_left [T2Space E] {c 
: E} (hc : c != 0) : IsClosedEmbedding fun x : 𝕜 => x • c
· 使用定理 `Topology.IsClosedEmbedding.locallyCompactSpace`：∀ {X : Type u_1} {Y : Ty
pe u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompac
tSpace Y]   {f : X → Y}, Topology.Is…
· 使用引理 `ProperSpace.of_locallyCompactSpace`：ProperSpace.of_locallyCompactSpace (
𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E] [N
ormedSpace 𝕜 E] [Locally…
-/
lemma ProperSpace.of_locallyCompact_module (V : Type*) [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [T2Space V] [Nontrivial V] [LocallyCompactSpace V] [Module 𝕜 V]
    [ContinuousSMul 𝕜 V] : ProperSpace 𝕜 :=
  have : LocallyCompactSpace 𝕜 := by
    obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
    let L : 𝕜 → V := fun t ↦ t • v
    have : IsClosedEmbedding L := isClosedEmbedding_smul_left hv
    apply IsClosedEmbedding.locallyCompactSpace this
  .of_locallyCompactSpace 𝕜

end Riesz

open ContinuousLinearMap

/-- A family of continuous linear maps is continuous within `s` at `x` iff all its applications
are. -/
/-
**continuousWithinAt_clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimen
sional 𝕜 E] {f : X -> E ->L[𝕜] F} {s : Set X} {x : X} : ContinuousWithinAt f s x
 ↔ forall y, ContinuousWithinAt (fun q => f q y) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_fin_fun`：Module.finrank_fin_fun {n : Nat} : finrank R (Fi
n n -> R) = n
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.continuousWithinAt_iff`：Topology.IsInducing.continuo
usWithinAt_iff {f : α -> β} {g : β -> γ} (hg : IsInducing g) {s : Set α} {x : α}
 : ContinuousWithinAt f s x ↔ Co…
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousWithinAt_pi`：continuousWithinAt_pi {ι : Type*} {X : ι -> Type*
} [forall i, TopologicalSpace (X i)] {f : α -> forall i, X i} {s : Set α} {x : α
} : Continu…

--- 原说明 ---
A family of continuous linear maps is continuous within `s` at `x` iff all its a
pplications
are.
-/
theorem continuousWithinAt_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X → E →L[𝕜] F} {s : Set X} {x : X} :
    ContinuousWithinAt f s x ↔ ∀ y, ContinuousWithinAt (fun q ↦ f q y) s x := by
  refine ⟨fun h y ↦ (apply 𝕜 F y).continuous.continuousAt.comp_continuousWithinAt h, fun h ↦ ?_⟩
  let e : (E →L[𝕜] F) ≃L[𝕜] Fin (finrank 𝕜 E) → F :=
    ((ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm).arrowCongr
      (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing _)
  rw [e.toHomeomorph.isInducing.continuousWithinAt_iff]
  exact continuousWithinAt_pi.mpr fun i ↦ h _

/-- A family of continuous linear maps is continuous on `s` iff all its applications are. -/
/-
**continuousOn_clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional
 𝕜 E] {f : X -> E ->L[𝕜] F} {s : Set X} : ContinuousOn f s ↔ forall y, Continuou
sOn (fun x => f x y) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b

--- 原说明 ---
A family of continuous linear maps is continuous on `s` iff all its applications
 are.
-/
theorem continuousOn_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X → E →L[𝕜] F} {s : Set X} :
    ContinuousOn f s ↔ ∀ y, ContinuousOn (fun x ↦ f x y) s := by
  simp_rw [ContinuousOn, continuousWithinAt_clm_apply, imp_forall_iff]
  exact forall_comm

/-- A family of continuous linear maps is continuous at a point iff all its applications are. -/
/-
**continuousAt_clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional
 𝕜 E] {f : X -> E ->L[𝕜] F} {x : X} : ContinuousAt f x ↔ forall y, ContinuousAt 
(fun q => f q y) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A family of continuous linear maps is continuous at a point iff all its applicat
ions are.
-/
theorem continuousAt_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X → E →L[𝕜] F} {x : X} :
    ContinuousAt f x ↔ ∀ y, ContinuousAt (fun q ↦ f q y) x := by
  simp_rw [← continuousWithinAt_univ, continuousWithinAt_clm_apply]
/-
**continuous_clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜
 E] {f : X -> E ->L[𝕜] F} : Continuous f ↔ forall y, Continuous (f · y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X → E →L[𝕜] F} : Continuous f ↔ ∀ y, Continuous (f · y) := by
  simp_rw [← continuousOn_univ, continuousOn_clm_apply]

end CompleteField

section LocallyCompactField

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜] (E : Type v) [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [LocallyCompactSpace 𝕜]

/-- Any finite-dimensional vector space over a locally compact field is proper.
We do not register this as an instance to avoid an instance loop when trying to prove the
properness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
/-
**FiniteDimensional.proper** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.proper [FiniteDimensional 𝕜 E] : ProperSpace E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProperSpace.of_locallyCompactSpace`：ProperSpace.of_locallyCompactSpace (
𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E] [N
ormedSpace 𝕜 E] [Locally…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_fin_fun`：Module.finrank_fin_fun {n : Nat} : finrank R (Fi
n n -> R) = n
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `AntilipschitzWith.properSpace`：∀ {β : Type u_2} [inst : PseudoMetricSpac
e β] {α : Type u_4} [inst_1 : MetricSpace α] {K : NNReal} {f : α → β}   [ProperS
pace α], Antilipsch…
· 使用定理 `ContinuousLinearEquiv.antilipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E
 : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddC
ommGroup F] [inst_2 : Non…
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `ContinuousLinearEquiv.surjective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…

--- 原说明 ---
Any finite-dimensional vector space over a locally compact field is proper.
We do not register this as an instance to avoid an instance loop when trying to 
prove the
properness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare th
e instance
explicitly when needed.
-/
theorem FiniteDimensional.proper [FiniteDimensional 𝕜 E] : ProperSpace E := by
  have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  exact e.symm.antilipschitz.properSpace e.symm.continuous e.symm.surjective

end LocallyCompactField

/-- Over the real numbers, we can register the previous statement as an instance as it will not
cause problems in instance resolution since the properness of `ℝ` is already known. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Over the real numbers, we can register the previous statement as an instance as 
it will not
cause problems in instance resolution since the properness of `ℝ` is already kno
wn.
-/
instance (priority := 900) FiniteDimensional.proper_real (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : ProperSpace E :=
  FiniteDimensional.proper ℝ E

/-- A submodule of a locally compact space over a complete field is also locally compact (and even
proper). -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule of a locally compact space over a complete field is also locally com
pact (and even
proper).
-/
instance {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E] (S : Submodule 𝕜 E) :
    ProperSpace S := by
  nontriviality E
  have : ProperSpace 𝕜 := .of_locallyCompact_module 𝕜 E
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  exact FiniteDimensional.proper 𝕜 S

/-- If `E` is a finite-dimensional normed real vector space, `x : E`, and `s` is a neighborhood of
`x` that is not equal to the whole space, then there exists a point `y ∈ frontier s` at distance
`Metric.infDist x sᶜ` from `x`. See also
`IsCompact.exists_mem_frontier_infDist_compl_eq_dist`. -/
/-
**exists_mem_frontier_infDist_compl_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_mem_frontier_infDist_compl_eq_dist {E : Type*} [NormedAddCommGroup 
E] [NormedSpace Real E] [FiniteDimensional Real E] {x : E} {s : Set E} (hx : x i
n s) (hs : s != univ) : exists y in frontier s, Metric.infDist x sᶜ = dist x y
参数：hx : x in s；hs : s != univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.exists_mem_closure_infDist_eq_dist`：exists_mem_closure_infDist_eq
_dist [ProperSpace α] (hne : s.Nonempty) (x : α) : exists y in closure s, infDis
t x s = dist x y
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_compl`：nonempty_compl : sᶜ.Nonempty ↔ s != univ
· 使用定理 `Metric.closedBall_infDist_compl_subset_closure`：Metric.closedBall_infDis
t_compl_subset_closure {x : F} {s : Set F} (hx : x in s) : closedBall x (infDist
 x sᶜ) subseteq closure s
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ

--- 原说明 ---
If `E` is a finite-dimensional normed real vector space, `x : E`, and `s` is a n
eighborhood of
`x` that is not equal to the whole space, then there exists a point `y ∈ frontie
r s` at distance
`Metric.infDist x sᶜ` from `x`. See also
`IsCompact.exists_mem_frontier_infDist_compl_eq_dist`.
-/
theorem exists_mem_frontier_infDist_compl_eq_dist {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {x : E} {s : Set E} (hx : x ∈ s) (hs : s ≠ univ) :
    ∃ y ∈ frontier s, Metric.infDist x sᶜ = dist x y := by
  rcases Metric.exists_mem_closure_infDist_eq_dist (nonempty_compl.2 hs) x with ⟨y, hys, hyd⟩
  rw [closure_compl] at hys
  refine ⟨y, ⟨Metric.closedBall_infDist_compl_subset_closure hx <|
    Metric.mem_closedBall.2 <| ge_of_eq ?_, hys⟩, hyd⟩
  rwa [dist_comm]

/-- If `K` is a compact set in a nontrivial real normed space and `x ∈ K`, then there exists a point
`y` of the boundary of `K` at distance `Metric.infDist x Kᶜ` from `x`. See also
`exists_mem_frontier_infDist_compl_eq_dist`. -/
nonrec theorem IsCompact.exists_mem_frontier_infDist_compl_eq_dist {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] {x : E} {K : Set E} (hK : IsCompact K)
    (hx : x ∈ K) :
    ∃ y ∈ frontier K, Metric.infDist x Kᶜ = dist x y := by
  obtain hx' | hx' : x ∈ interior K ∪ frontier K := by
    rw [← closure_eq_interior_union_frontier]
    exact subset_closure hx
  · rw [mem_interior_iff_mem_nhds, Metric.nhds_basis_closedBall.mem_iff] at hx'
    rcases hx' with ⟨r, hr₀, hrK⟩
    have : FiniteDimensional ℝ E :=
      .of_isCompact_closedBall ℝ hr₀
        (hK.of_isClosed_subset Metric.isClosed_closedBall hrK)
    exact exists_mem_frontier_infDist_compl_eq_dist hx hK.ne_univ
  · refine ⟨x, hx', ?_⟩
    rw [frontier_eq_closure_inter_closure] at hx'
    rw [Metric.infDist_zero_of_mem_closure hx'.2, dist_self]

/-- In a finite-dimensional vector space over `ℝ`, the series `∑ x, ‖f x‖` is unconditionally
summable if and only if the series `∑ x, f x` is unconditionally summable. One implication holds in
any complete normed space, while the other holds only in finite-dimensional spaces. -/
/-
**summable_norm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_norm_iff {α E : Type*} [NormedAddCommGroup E] [NormedSpace Real E
] [FiniteDimensional Real E] {f : α -> E} : (Summable fun x => ‖f x‖) ↔ Summable
 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Summable.abs`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommGroup α] [i
nst_1 : LinearOrder α] [IsOrderedAddMonoid α]   [inst_3 : UniformSpace α] [IsUni
fo…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.summable`：∀ {α : Type u_1} {ι : Type u_4} {X : α → Type u_5} [inst : 
(x : α) → AddCommMonoid (X x)]   [inst_1 : (x : α) → TopologicalSpace (X x)] {L 
:…
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `summable_sum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Add
CommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFilter β} [Continuou
sA…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `pi_norm_le_iff_of_nonneg`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fi
ntype ι] [inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r 
: ℝ}, 0 ≤ r → …
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearEquiv.summable`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Ty
pe u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring
 R₂] [inst_2 : AddCo…
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
In a finite-dimensional vector space over `ℝ`, the series `∑ x, ‖f x‖` is uncond
itionally
summable if and only if the series `∑ x, f x` is unconditionally summable. One i
mplication holds in
any complete normed space, while the other holds only in finite-dimensional spac
es.
-/
theorem summable_norm_iff {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : α → E} : (Summable fun x => ‖f x‖) ↔ Summable f := by
  refine ⟨Summable.of_norm, fun hf ↦ ?_⟩
  -- First we use a finite basis to reduce the problem to the case `E = Fin N → ℝ`
  suffices ∀ {N : ℕ} {g : α → Fin N → ℝ}, Summable g → Summable fun x => ‖g x‖ by
    obtain v := Module.finBasis ℝ E
    set e := v.equivFunL
    have H : Summable fun x => ‖e (f x)‖ := this (e.summable.2 hf)
    refine .of_norm_bounded (H.mul_left ↑‖(e.symm : (Fin (finrank ℝ E) → ℝ) →L[ℝ] E)‖₊) fun i ↦ ?_
    simpa using (e.symm : (Fin (finrank ℝ E) → ℝ) →L[ℝ] E).le_opNorm (e <| f i)
  clear! E
  -- Now we deal with `g : α → Fin N → ℝ`
  intro N g hg
  have : ∀ i, Summable fun x => ‖g x i‖ := fun i => (Pi.summable.1 hg i).abs
  refine .of_norm_bounded (summable_sum fun i (_ : i ∈ Finset.univ) => this i) fun x => ?_
  rw [norm_norm, pi_norm_le_iff_of_nonneg]
  · refine fun i => Finset.single_le_sum (f := fun i => ‖g x i‖) (fun i _ => ?_) (Finset.mem_univ i)
    exact norm_nonneg (g x i)
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _

alias ⟨_, Summable.norm⟩ := summable_norm_iff
/-
**summable_of_sum_range_norm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_sum_range_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSp
ace Real E] [FiniteDimensional Real E] {c : Real} {f : Nat -> E} (h : forall n, 
∑ i in Finset.range n, ‖f i‖ <= c) : Summable f
参数：h : forall n, ∑ i in Finset.range n, ‖f i‖ <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `summable_norm_iff`：summable_norm_iff {α E : Type*} [NormedAddCommGroup E
] [NormedSpace Real E] [FiniteDimensional Real E] {f : α -> E} : (Summable fun x
 => ‖f …
· 使用定理 `summable_of_sum_range_le`：summable_of_sum_range_le {f : Nat -> Real} {c 
: Real} (hf : forall n, 0 <= f n) (h : forall n, ∑ i in Finset.range n, f i <= c
) : Summable f
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem summable_of_sum_range_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {c : ℝ} {f : ℕ → E} (h : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ c) :
    Summable f :=
  summable_norm_iff.mp <| summable_of_sum_range_le (fun _ ↦ norm_nonneg _) h
/-
**summable_of_isBigO'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_isBigO' {ι E F : Type*} [NormedAddCommGroup E] [CompleteSpace 
E] [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F] {f : ι
 -> E} {g : ι -> F} (hg : Summable g) (h : f =O[cofinite] g) : Summable f
参数：hg : Summable g；h : f =O[cofinite] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_isBigO`：summable_of_isBigO {ι E} [SeminormedAddCommGroup E] 
[CompleteSpace E] {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : f =O[cofin
ite] g) …
· 使用定理 `Summable.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]   {f : α → E}, Summable 
f →…
· 使用定理 `Asymptotics.IsBigO.norm_right`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
-/
theorem summable_of_isBigO' {ι E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : ι → E} {g : ι → F}
    (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  summable_of_isBigO hg.norm h.norm_right
/-
**Asymptotics.IsBigO.comp_summable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Asymptotics.IsBigO.comp_summable {ι E F : Type*} [NormedAddCommGroup E] [N
ormedSpace Real E] [FiniteDimensional Real E] [NormedAddCommGroup F] [CompleteSp
ace F] {f : E -> F} (hf : f =O[𝓝 0] id) {g : ι -> E} (hg : Summable g) : Summabl
e (f ∘ g)
参数：hf : f =O[𝓝 0] id；hg : Summable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用引理 `Asymptotics.IsBigO.comp_summable_norm`：Asymptotics.IsBigO.comp_summable_
norm {ι E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {f : 
E -> F} {g : ι -> E} (hf : …
· 使用定理 `Summable.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]   {f : α → E}, Summable 
f →…
-/
lemma Asymptotics.IsBigO.comp_summable {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [CompleteSpace F]
    {f : E → F} (hf : f =O[𝓝 0] id) {g : ι → E} (hg : Summable g) : Summable (f ∘ g) :=
  .of_norm <| hf.comp_summable_norm hg.norm
/-
**summable_of_isBigO_nat'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_isBigO_nat' {E F : Type*} [NormedAddCommGroup E] [CompleteSpac
e E] [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F] {f :
 Nat -> E} {g : Nat -> F} (hg : Summable g) (h : f =O[atTop] g) : Summable f
参数：hg : Summable g；h : f =O[atTop] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_isBigO_nat`：summable_of_isBigO_nat {E} [SeminormedAddCommGro
up E] [CompleteSpace E] {f : Nat -> E} {g : Nat -> Real} (hg : Summable g) (h : 
f =O[atTop] …
· 使用定理 `Summable.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]   {f : α → E}, Summable 
f →…
· 使用定理 `Asymptotics.IsBigO.norm_right`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
-/
theorem summable_of_isBigO_nat' {E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : ℕ → E} {g : ℕ → F}
    (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_isBigO_nat hg.norm h.norm_right


open Nat Asymptotics in
/-- This is a version of `summable_norm_mul_geometric_of_norm_lt_one` for more general codomains. We
keep the original one due to import restrictions. -/
/-
**summable_norm_mul_geometric_of_norm_lt_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_norm_mul_geometric_of_norm_lt_one' {F : Type*} [NormedRing F] [No
rmOneClass F] [NormMulClass F] {k : Nat} {r : F} (hr : ‖r‖ < 1) {u : Nat -> F} (
hu : u =O[atTop] fun n => ((n ^ k : Nat) : F)) : Summable fun n : Nat => ‖u n * 
r ^ n‖
参数：hr : ‖r‖ < 1；hu : u =O[atTop] fun n => ((n ^ k : Nat) : F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `summable_of_isBigO_nat`：summable_of_isBigO_nat {E} [SeminormedAddCommGro
up E] [CompleteSpace E] {f : Nat -> E} {g : Nat -> Real} (hg : Summable g) (h : 
f =O[atTop] …
· 使用定理 `Summable.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]   {f : α → E}, Summable 
f →…
· 使用定理 `summable_geometric_of_lt_one`：summable_geometric_of_lt_one {r : Real} (h
₁ : 0 <= r) (h₂ : r < 1) : Summable fun n : Nat => r ^ n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_norm_pow_le`：eventually_norm_pow_le (a : α) : forallᶠ n : Nat
 in atTop, ‖a ^ n‖ <= ‖a‖ ^ n
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
This is a version of `summable_norm_mul_geometric_of_norm_lt_one` for more gener
al codomains. We
keep the original one due to import restrictions.
-/
theorem summable_norm_mul_geometric_of_norm_lt_one' {F : Type*} [NormedRing F]
    [NormOneClass F] [NormMulClass F] {k : ℕ} {r : F} (hr : ‖r‖ < 1) {u : ℕ → F}
    (hu : u =O[atTop] fun n ↦ ((n ^ k : ℕ) : F)) : Summable fun n : ℕ ↦ ‖u n * r ^ n‖ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h).norm
  calc
  fun n ↦ ‖(u n) * r ^ n‖
  _ =O[atTop] fun n ↦ ‖u n‖ * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : ℝ)‖) ?_).isBigO
      filter_upwards [eventually_norm_pow_le r] with n hn
      simp
  _ =O[atTop] fun n ↦ ‖((n : F) ^ k)‖ * ‖r‖ ^ n := by
      simpa [Nat.cast_pow] using
      (isBigO_norm_left.mpr (isBigO_norm_right.mpr hu)).mul (isBigO_refl (fun n ↦ (‖r‖ ^ n)) atTop)
  _ =O[atTop] fun n ↦ ‖r' ^ n‖ := by
      convert!
        isBigO_norm_right.mpr
          (isBigO_norm_left.mpr
            (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt k hrr').isBigO)
      simp only [norm_pow, norm_mul]
/-
**summable_of_isEquivalent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_isEquivalent {ι E : Type*} [NormedAddCommGroup E] [NormedSpace
 Real E] [FiniteDimensional Real E] {f : ι -> E} {g : ι -> E} (hg : Summable g) 
(h : f ~[cofinite] g) : Summable f
参数：hg : Summable g；h : f ~[cofinite] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_isBigO'`：summable_of_isBigO' {ι E F : Type*} [NormedAddCommG
roup E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDim
ensional …
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Asymptotics.IsEquivalent.isBigO`：∀ {α : Type u_1} {β : Type u_2} [inst :
 NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → u =O[l] v
-/
theorem summable_of_isEquivalent {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ι → E} {g : ι → E} (hg : Summable g) (h : f ~[cofinite] g) :
    Summable f :=
  summable_of_isBigO' hg h.isBigO
/-
**summable_of_isEquivalent_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_isEquivalent_nat {E : Type*} [NormedAddCommGroup E] [NormedSpa
ce Real E] [FiniteDimensional Real E] {f : Nat -> E} {g : Nat -> E} (hg : Summab
le g) (h : f ~[atTop] g) : Summable f
参数：hg : Summable g；h : f ~[atTop] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_isBigO_nat'`：summable_of_isBigO_nat' {E F : Type*} [NormedAd
dCommGroup E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace Real F] [Fin
iteDimensiona…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Asymptotics.IsEquivalent.isBigO`：∀ {α : Type u_1} {β : Type u_2} [inst :
 NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → u =O[l] v
-/
theorem summable_of_isEquivalent_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℕ → E} {g : ℕ → E} (hg : Summable g) (h : f ~[atTop] g) :
    Summable f :=
  summable_of_isBigO_nat' hg h.isBigO
/-
**Asymptotics.IsTheta.summable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.IsTheta.summable_iff {ι E F : Type*} [NormedAddCommGroup E] [N
ormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F] [FiniteDimensiona
l Real E] [FiniteDimensional Real F] {f : ι -> E} {g : ι -> F} (h : f =Θ[cofinit
e] g) : Summable f ↔ Summable g
参数：h : f =Θ[cofinite] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_isBigO'`：summable_of_isBigO' {ι E F : Type*} [NormedAddCommG
roup E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDim
ensional …
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Asymptotics.IsTheta.isBigO_symm`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}
,   f =Θ[l] g → g =O[…
· 使用定理 `Asymptotics.IsTheta.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f
 =Θ[l] g → f =O[…
-/
theorem Asymptotics.IsTheta.summable_iff {ι E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] {f : ι → E} {g : ι → F} (h : f =Θ[cofinite] g) :
    Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_isBigO' hf h.isBigO_symm, fun hg => summable_of_isBigO' hg h.isBigO⟩
/-
**Asymptotics.IsTheta.summable_iff_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.IsTheta.summable_iff_nat {E F : Type*} [NormedAddCommGroup E] 
[NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F] [FiniteDimensio
nal Real E] [FiniteDimensional Real F] {f : Nat -> E} {g : Nat -> F} (h : f =Θ[a
tTop] g) : Summable f ↔ Summable g
参数：h : f =Θ[atTop] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.summable_iff`：Asymptotics.IsTheta.summable_iff {ι E 
F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [N
ormedSpace Real F] [Fi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem Asymptotics.IsTheta.summable_iff_nat {E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] {f : ℕ → E} {g : ℕ → F} (h : f =Θ[atTop] g) :
    Summable f ↔ Summable g :=
  IsTheta.summable_iff <| by simpa [← Nat.cofinite_eq_atTop] using h
/-
**Asymptotics.IsEquivalent.summable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.IsEquivalent.summable_iff {ι E : Type*} [NormedAddCommGroup E]
 [NormedSpace Real E] [FiniteDimensional Real E] {f : ι -> E} {g : ι -> E} (h : 
f ~[cofinite] g) : Summable f ↔ Summable g
参数：h : f ~[cofinite] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.summable_iff`：Asymptotics.IsTheta.summable_iff {ι E 
F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [N
ormedSpace Real F] [Fi…
· 使用定理 `Asymptotics.IsEquivalent.isTheta`：∀ {α : Type u_1} {β : Type u_2} [inst 
: NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent
 l u v → u =Θ[l] v
-/
theorem Asymptotics.IsEquivalent.summable_iff {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ι → E} {g : ι → E} (h : f ~[cofinite] g) :
    Summable f ↔ Summable g :=
  h.isTheta.summable_iff

@[deprecated (since := "2026-02-07")]
alias IsEquivalent.summable_iff := Asymptotics.IsEquivalent.summable_iff
/-
**Asymptotics.IsEquivalent.summable_iff_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.IsEquivalent.summable_iff_nat {E : Type*} [NormedAddCommGroup 
E] [NormedSpace Real E] [FiniteDimensional Real E] {f : Nat -> E} {g : Nat -> E}
 (h : f ~[atTop] g) : Summable f ↔ Summable g
参数：h : f ~[atTop] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.summable_iff_nat`：Asymptotics.IsTheta.summable_iff_n
at {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real
 E] [NormedSpace Real F] […
· 使用定理 `Asymptotics.IsEquivalent.isTheta`：∀ {α : Type u_1} {β : Type u_2} [inst 
: NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent
 l u v → u =Θ[l] v
-/
theorem Asymptotics.IsEquivalent.summable_iff_nat {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℕ → E} {g : ℕ → E} (h : f ~[atTop] g) :
    Summable f ↔ Summable g :=
  h.isTheta.summable_iff_nat

@[deprecated (since := "2026-02-07")]
alias IsEquivalent.summable_iff_nat := Asymptotics.IsEquivalent.summable_iff_nat

namespace Module.Basis

variable {ι R M : Type*} [Finite ι]
  [NontriviallyNormedField R] [CompleteSpace R]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M]
  [Module R M] [ContinuousSMul R M] (B : Module.Basis ι R M)

-- Note that Finsupp has no topology so we need the coercion, see
-- https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/TVS.20and.20NormedSpace.20on.20Finsupp.2C.20DFinsupp.2C.20DirectSum.2C.20.2E.2E/near/512890984
/-
**Module.Basis.continuous_coe_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：continuous_coe_repr : Continuous (fun m : M => ⇑(B.repr m))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
-/
theorem continuous_coe_repr : Continuous (fun m : M => ⇑(B.repr m)) :=
  have := Finite.of_basis B
  LinearMap.continuous_of_finiteDimensional B.equivFun.toLinearMap

-- Note: this could be generalized if we had some typeclass to indicate "each of the projections
-- into the basis is continuous".
/-
**Module.Basis.continuous_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：continuous_toMatrix : Continuous fun (v : ι -> M) => B.toMatrix v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `instIsTopologicalAddGroupMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Ty
pe u_8} [inst : TopologicalSpace R] [inst_1 : AddGroup R]   [IsTopologicalAddGro
up R], IsTopologicalA…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instContinuousSMulMatrix`：∀ {α : Type u_2} {m : Type u_4} {n : Type u_5}
 {R : Type u_8} [inst : TopologicalSpace R] [inst_1 : TopologicalSpace α]   [ins
t_2 : SMul α R…
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
-/
theorem continuous_toMatrix : Continuous fun (v : ι → M) => B.toMatrix v :=
  let _ := Fintype.ofFinite ι
  have := Finite.of_basis B
  LinearMap.continuous_of_finiteDimensional B.toMatrixEquiv.toLinearMap

end Module.Basis

