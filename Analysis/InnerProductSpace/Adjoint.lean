/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Tactic.CrossRefAttribute


/-!
# Adjoint of operators on Hilbert spaces

Given an operator `A : E →L[𝕜] F`, where `E` and `F` are Hilbert spaces, its adjoint
`adjoint A : F →L[𝕜] E` is the unique operator such that `⟪x, A y⟫ = ⟪adjoint A x, y⟫` for all
`x` and `y`.

We then use this to put a C⋆-algebra structure on `E →L[𝕜] E` with the adjoint as the star
operation.

This construction is used to define an adjoint for linear maps (i.e. not continuous) between
finite-dimensional spaces.

## Main definitions

* `ContinuousLinearMap.adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] (F →L[𝕜] E)`: the adjoint of a continuous
  linear map, bundled as a conjugate-linear isometric equivalence.
* `LinearMap.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)`: the adjoint of a linear map between
  finite-dimensional spaces, this time only as a conjugate-linear equivalence, since there is no
  norm defined on these maps.

## Implementation notes

* The continuous conjugate-linear version `adjointAux` is only an intermediate
  definition and is not meant to be used outside this file.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]

## Tags

adjoint

-/

noncomputable section

open Module RCLike

open scoped ComplexConjugate

variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Adjoint operator -/


open InnerProductSpace

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace G]

/-- The adjoint, as a continuous conjugate-linear map. This is only meant as an auxiliary
definition for the main definition `adjoint`, where this is bundled as a conjugate-linear isometric
equivalence. -/
/-
**ContinuousLinearMap.adjointAux** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：adjointAux : (E ->L[𝕜] F) ->L⋆[𝕜] F ->L[𝕜] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjoint, as a continuous conjugate-linear map. This is only meant as an auxi
liary
definition for the main definition `adjoint`, where this is bundled as a conjuga
te-linear isometric
equivalence.
-/
def adjointAux : (E →L[𝕜] F) →L⋆[𝕜] F →L[𝕜] E :=
  (ContinuousLinearMap.compSL _ _ _ _ _ ((toDual 𝕜 E).symm : StrongDual 𝕜 E →L⋆[𝕜] E)).comp
    (toSesqForm : (E →L[𝕜] F) →L[𝕜] F →L⋆[𝕜] StrongDual 𝕜 E)

@[simp]
/-
**ContinuousLinearMap.adjointAux_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：adjointAux_apply (A : E ->L[𝕜] F) (x : F) : adjointAux A x = ((toDual 𝕜 E)
.symm : StrongDual 𝕜 E -> E) ((toSesqForm A) x)
参数：A : E ->L[𝕜] F；x : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjointAux_apply (A : E →L[𝕜] F) (x : F) :
    adjointAux A x = ((toDual 𝕜 E).symm : StrongDual 𝕜 E → E) ((toSesqForm A) x) :=
  rfl
/-
**ContinuousLinearMap.adjointAux_inner_left** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：adjointAux_inner_left (A : E ->L[𝕜] F) (x : E) (y : F) : ⟪adjointAux A y, 
x⟫ = ⟪y, A x⟫
参数：A : E ->L[𝕜] F；x : E；y : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjointAux_inner_left (A : E →L[𝕜] F) (x : E) (y : F) : ⟪adjointAux A y, x⟫ = ⟪y, A x⟫ := by
  simp
/-
**ContinuousLinearMap.adjointAux_inner_right** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：adjointAux_inner_right (A : E ->L[𝕜] F) (x : E) (y : F) : ⟪x, adjointAux A
 y⟫ = ⟪A x, y⟫
参数：A : E ->L[𝕜] F；x : E；y : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjointAux_inner_right (A : E →L[𝕜] F) (x : E) (y : F) :
    ⟪x, adjointAux A y⟫ = ⟪A x, y⟫ := by
  rw [← inner_conj_symm, adjointAux_inner_left, inner_conj_symm]

variable [CompleteSpace F]
/-
**ContinuousLinearMap.adjointAux_adjointAux** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：adjointAux_adjointAux (A : E ->L[𝕜] F) : adjointAux (adjointAux A) = A
参数：A : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjointAux_adjointAux (A : E →L[𝕜] F) : adjointAux (adjointAux A) = A := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjointAux_inner_right, adjointAux_inner_left]

@[simp]
/-
**ContinuousLinearMap.adjointAux_norm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：adjointAux_norm (A : E ->L[𝕜] F) : ‖adjointAux A‖ = ‖A‖
参数：A : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjointAux_norm (A : E →L[𝕜] F) : ‖adjointAux A‖ = ‖A‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [adjointAux_apply, LinearIsometryEquiv.norm_map]
    exact toSesqForm_apply_norm_le
  · nth_rw 1 [← adjointAux_adjointAux A]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [adjointAux_apply, LinearIsometryEquiv.norm_map]
    exact toSesqForm_apply_norm_le

public section

/-- The adjoint of a bounded operator `A` from a Hilbert space `E` to another Hilbert space `F`,
  denoted as `A†`. -/
@[wikidata Q1509647]
/-
**ContinuousLinearMap.adjoint** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：adjoint : (E ->L[𝕜] F) ≃ₗᵢ⋆[𝕜] F ->L[𝕜] E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.Adjoint.0.ContinuousLinearMa
p.adjointAux_norm`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike
 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedAddCommGroup F] [inst_3 :…

--- 原说明 ---
The adjoint of a bounded operator `A` from a Hilbert space `E` to another Hilber
t space `F`,
  denoted as `A†`.
-/
def adjoint : (E →L[𝕜] F) ≃ₗᵢ⋆[𝕜] F →L[𝕜] E :=
  LinearIsometryEquiv.ofSurjective { adjointAux with norm_map' := adjointAux_norm } fun A =>
    ⟨adjointAux A, adjointAux_adjointAux A⟩

@[inherit_doc]
scoped[InnerProduct] postfix:1000 "†" => ContinuousLinearMap.adjoint
open InnerProduct

/-- The fundamental property of the adjoint. -/
/-
**ContinuousLinearMap.adjoint_inner_left** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：adjoint_inner_left (A : E ->L[𝕜] F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A 
x⟫
参数：A : E ->L[𝕜] F；x : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.Adjoint.0.ContinuousLinearMa
p.adjointAux_inner_left`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : 
RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedAddCommGroup F] [ins
t_3 :…

--- 原说明 ---
The fundamental property of the adjoint.
-/
theorem adjoint_inner_left (A : E →L[𝕜] F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫ :=
  adjointAux_inner_left A x y

/-- The fundamental property of the adjoint. -/
/-
**ContinuousLinearMap.adjoint_inner_right** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：adjoint_inner_right (A : E ->L[𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x,
 y⟫
参数：A : E ->L[𝕜] F；x : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.Adjoint.0.ContinuousLinearMa
p.adjointAux_inner_right`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst :
 RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedAddCommGroup F] [in
st_3 :…

--- 原说明 ---
The fundamental property of the adjoint.
-/
theorem adjoint_inner_right (A : E →L[𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫ :=
  adjointAux_inner_right A x y

/-- The adjoint is involutive. -/
@[simp]
/-
**ContinuousLinearMap.adjoint_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：adjoint_adjoint (A : E ->L[𝕜] F) : A†† = A
参数：A : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.Adjoint.0.ContinuousLinearMa
p.adjointAux_adjointAux`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : 
RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedAddCommGroup F] [ins
t_3 :…

--- 原说明 ---
The adjoint is involutive.
-/
theorem adjoint_adjoint (A : E →L[𝕜] F) : A†† = A :=
  adjointAux_adjointAux A

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
/-
**ContinuousLinearMap.adjoint_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：adjoint_comp (A : F ->L[𝕜] G) (B : E ->L[𝕜] F) : (A ∘L B)† = B† ∘L A†
参数：A : F ->L[𝕜] G；B : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ext_inner_left`：ext_inner_left {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫)
 : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->L[
𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The adjoint of the composition of two operators is the composition of the two ad
joints
in reverse order.
-/
theorem adjoint_comp (A : F →L[𝕜] G) (B : E →L[𝕜] F) : (A ∘L B)† = B† ∘L A† := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp [adjoint_inner_right]
/-
**ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearMap`。
形式化陈述：apply_norm_sq_eq_inner_adjoint_left (A : E ->L[𝕜] F) (x : E) : ‖A x‖ ^ 2 =
 re ⟪(A† ∘L A) x, x⟫
参数：A : E ->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->L[𝕜]
 F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫
· 使用定理 `inner_self_eq_norm_sq`：inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^
 2
-/
theorem apply_norm_sq_eq_inner_adjoint_left (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ ^ 2 = re ⟪(A† ∘L A) x, x⟫ := by
  have h : ⟪(A† ∘L A) x, x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_left]; rfl
  rw [h, ← inner_self_eq_norm_sq (𝕜 := 𝕜) _]
/-
**ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_left** 是 Mathlib 中的一个定理，位
于命名空间 `ContinuousLinearMap`。
形式化陈述：apply_norm_eq_sqrt_inner_adjoint_left (A : E ->L[𝕜] F) (x : E) : ‖A x‖ = √
(re ⟪(A† ∘L A) x, x⟫)
参数：A : E ->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left`：apply_norm_sq_e
q_inner_adjoint_left (A : E ->L[𝕜] F) (x : E) : ‖A x‖ ^ 2 = re ⟪(A† ∘L A) x, x⟫
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem apply_norm_eq_sqrt_inner_adjoint_left (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ = √(re ⟪(A† ∘L A) x, x⟫) := by
  rw [← apply_norm_sq_eq_inner_adjoint_left, Real.sqrt_sq (norm_nonneg _)]
/-
**ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearMap`。
形式化陈述：apply_norm_sq_eq_inner_adjoint_right (A : E ->L[𝕜] F) (x : E) : ‖A x‖ ^ 2 
= re ⟪x, (A† ∘L A) x⟫
参数：A : E ->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->L[
𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫
· 使用定理 `inner_self_eq_norm_sq`：inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^
 2
-/
theorem apply_norm_sq_eq_inner_adjoint_right (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ ^ 2 = re ⟪x, (A† ∘L A) x⟫ := by
  have h : ⟪x, (A† ∘L A) x⟫ = ⟪A x, A x⟫ := by rw [← adjoint_inner_right]; rfl
  rw [h, ← inner_self_eq_norm_sq (𝕜 := 𝕜) _]
/-
**ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_right** 是 Mathlib 中的一个定理，
位于命名空间 `ContinuousLinearMap`。
形式化陈述：apply_norm_eq_sqrt_inner_adjoint_right (A : E ->L[𝕜] F) (x : E) : ‖A x‖ = 
√(re ⟪x, (A† ∘L A) x⟫)
参数：A : E ->L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right`：apply_norm_sq_
eq_inner_adjoint_right (A : E ->L[𝕜] F) (x : E) : ‖A x‖ ^ 2 = re ⟪x, (A† ∘L A) x
⟫
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem apply_norm_eq_sqrt_inner_adjoint_right (A : E →L[𝕜] F) (x : E) :
    ‖A x‖ = √(re ⟪x, (A† ∘L A) x⟫) := by
  rw [← apply_norm_sq_eq_inner_adjoint_right, Real.sqrt_sq (norm_nonneg _)]

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
/-
**ContinuousLinearMap.eq_adjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：eq_adjoint_iff (A : E ->L[𝕜] F) (B : F ->L[𝕜] E) : A = B† ↔ forall x y, ⟪A
 x, y⟫ = ⟪x, B y⟫
参数：A : E ->L[𝕜] F；B : F ->L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->L[𝕜]
 F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ext_inner_right`：ext_inner_right {x y : E} (h : forall v, ⟪x, v⟫ = ⟪y, v
⟫) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y
⟫ = ⟪x, B y⟫`
for all `x` and `y`.
-/
theorem eq_adjoint_iff (A : E →L[𝕜] F) (B : F →L[𝕜] E) : A = B† ↔ ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]

@[simp]
/-
**ContinuousLinearMap._root_.LinearMap.IsSymmetric.clm_adjoint_eq** 是 Mathlib 中的
一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.IsSymmetric.clm_adjoint_eq {A : E →L[𝕜] E} (hA : A.IsSymmetric) :
    A† = A := by
  rwa [eq_comm, eq_adjoint_iff A A]

set_option backward.isDefEq.respectTransparency.types false in
/-
**ContinuousLinearMap.adjoint_id** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：adjoint_id : (.id 𝕜 E)† = .id 𝕜 E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.clm_adjoint_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   [inst_3 : CompleteSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma adjoint_id : (.id 𝕜 E)† = .id 𝕜 E := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**ContinuousLinearMap.adjoint_one** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：adjoint_one : (1 : E ->L[𝕜] E)† = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.clm_adjoint_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   [inst_3 : CompleteSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma adjoint_one : (1 : E →L[𝕜] E)† = 1 := by simp
/-
**ContinuousLinearMap._root_.Submodule.adjoint_subtypeL** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.adjoint_subtypeL (U : Submodule 𝕜 E) [CompleteSpace U] :
    U.subtypeL† = U.orthogonalProjectionOnto := by
  symm
  simp [eq_adjoint_iff]
/-
**ContinuousLinearMap._root_.Submodule.adjoint_orthogonalProjectionOnto** 是 Math
lib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.adjoint_orthogonalProjectionOnto (U : Submodule 𝕜 E) [CompleteSpace U] :
    (U.orthogonalProjectionOnto : E →L[𝕜] U)† = U.subtypeL := by
  rw [← U.adjoint_subtypeL, adjoint_adjoint]

@[deprecated (since := "2026-05-05")] alias _root_.Submodule.adjoint_orthogonalProjection :=
  Submodule.adjoint_orthogonalProjectionOnto
/-
**ContinuousLinearMap.orthogonal_ker** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：orthogonal_ker (T : E ->L[𝕜] F) : T.kerᗮ = T†.range.topologicalClosure
参数：T : E ->L[𝕜] F。
该定理/引理给出了一组等式。
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
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.orthogonal_orthogonal_eq_closure`：orthogonal_orthogonal_eq_clo
sure [CompleteSpace E] : Kᗮᗮ = K.topologicalClosure
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ
· 使用定理 `ext_inner_left`：ext_inner_left {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫)
 : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->L[𝕜]
 F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem orthogonal_ker (T : E →L[𝕜] F) :
    T.kerᗮ = T†.range.topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply le_antisymm
  all_goals refine Submodule.orthogonal_le fun x hx ↦ ?_
  · refine ext_inner_left 𝕜 fun y ↦ ?_
    simp [← T.adjoint_inner_left, hx _]
  · rintro _ ⟨y, rfl⟩
    simp_all [T.adjoint_inner_left]
/-
**ContinuousLinearMap.orthogonal_range** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：orthogonal_range (T : E ->L[𝕜] F) : T.rangeᗮ = T†.ker
参数：T : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousLinearMap.orthogonal_ker`：orthogonal_ker (T : E ->L[𝕜] F) : T.
kerᗮ = T†.range.topologicalClosure
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.topologicalClosure.congr_simp`：∀ {R : Type u} {M : Type v} [in
st : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMonoid M]   [ins
t_3 : _root_.Module R M] [ins…
· 使用定理 `LinearMap.range.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u
_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用定理 `ContinuousLinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->L[𝕜] F) : 
A†† = A
· 使用引理 `Submodule.orthogonal_closure`：orthogonal_closure (K : Submodule 𝕜 E) : K
.topologicalClosureᗮ = Kᗮ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orthogonal_range (T : E →L[𝕜] F) : T.rangeᗮ = T†.ker := by
  rw [← T†.ker.orthogonal_orthogonal, T†.orthogonal_ker]
  simp

/-- The fitted value `A x` minimizes the distance to `y` among points in `A.range`
if and only if the adjoint of `A` sends the residual `y - A x` to zero. -/
/-
**ContinuousLinearMap.norm_eq_iInf_range_iff_adjoint_apply_eq_zero** 是 Mathlib 中
的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：norm_eq_iInf_range_iff_adjoint_apply_eq_zero (A : E ->L[𝕜] F) (y : F) (x :
 E) : (‖y - A x‖ = ⨅ z : A.range, ‖y - z‖) ↔ (A†) (y - A x) = 0
参数：A : E ->L[𝕜] F；y : F；x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.norm_eq_iInf_iff_inner_eq_zero`：norm_eq_iInf_iff_inner_eq_zero
 {u : E} {v : E} (hv : v in K) : (‖u - v‖ = ⨅ w : K, ‖u - w‖) ↔ forall w in K, ⟪
u - v, w⟫ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_orthogonal'`：mem_orthogonal' (v : E) : v in Kᗮ ↔ forall u 
in K, ⟪v, u⟫ = 0
· 使用定理 `ContinuousLinearMap.orthogonal_range`：orthogonal_range (T : E ->L[𝕜] F) 
: T.rangeᗮ = T†.ker
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `ContinuousLinearMap.coe_coe`：coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->
ₛₗ[σ₁₂] M₂) = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The fitted value `A x` minimizes the distance to `y` among points in `A.range`
if and only if the adjoint of `A` sends the residual `y - A x` to zero.
-/
theorem norm_eq_iInf_range_iff_adjoint_apply_eq_zero (A : E →L[𝕜] F) (y : F) (x : E) :
    (‖y - A x‖ = ⨅ z : A.range, ‖y - z‖) ↔ (A†) (y - A x) = 0 := by
  rw [A.range.norm_eq_iInf_iff_inner_eq_zero (by simp),
    ← Submodule.mem_orthogonal', A.orthogonal_range, LinearMap.mem_ker, coe_coe]

/-- The residual norm at `x` is minimal among all points of `E` if and only if
the adjoint of `A` sends the residual `y - A x` to zero. -/
/-
**ContinuousLinearMap.forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero** 是
 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero (A : E ->L[𝕜] F) (y
 : F) (x : E) : (forall z : E, ‖y - A x‖ <= ‖y - A z‖) ↔ (A†) (y - A x) = 0
参数：A : E ->L[𝕜] F；y : F；x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.norm_eq_iInf_range_iff_adjoint_apply_eq_zero`：norm_e
q_iInf_range_iff_adjoint_apply_eq_zero (A : E ->L[𝕜] F) (y : F) (x : E) : (‖y - 
A x‖ = ⨅ z : A.range, ‖y - z‖) ↔ (A†) (y - A x) = 0
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `le_ciInf_iff`：le_ciInf_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddBe
low (range f)) : a <= iInf f ↔ forall i, a <= f i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The residual norm at `x` is minimal among all points of `E` if and only if
the adjoint of `A` sends the residual `y - A x` to zero.
-/
theorem forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero
    (A : E →L[𝕜] F) (y : F) (x : E) :
    (∀ z : E, ‖y - A x‖ ≤ ‖y - A z‖) ↔ (A†) (y - A x) = 0 := by
  have hb : BddBelow (Set.range fun w : A.range => ‖y - w‖) := ⟨0, by rintro - ⟨_, rfl⟩; positivity⟩
  rw [← A.norm_eq_iInf_range_iff_adjoint_apply_eq_zero y x, le_antisymm_iff,
    and_iff_left (ciInf_le hb ⟨A x, x, rfl⟩), le_ciInf_iff hb]
  simp

omit [CompleteSpace E] in
/-
**ContinuousLinearMap.ker_le_ker_iff_range_le_range** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：ker_le_ker_iff_range_le_range [FiniteDimensional 𝕜 E] {T U : E ->L[𝕜] E} (
hT : T.IsSymmetric) (hU : U.IsSymmetric) : U.ker <= T.ker ↔ T.range <= U.range
参数：hT : T.IsSymmetric；hU : U.IsSymmetric。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `ContinuousLinearMap.orthogonal_ker`：orthogonal_ker (T : E ->L[𝕜] F) : T.
kerᗮ = T†.range.topologicalClosure
· 使用定理 `Submodule.topologicalClosure.congr_simp`：∀ {R : Type u} {M : Type v} [in
st : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMonoid M]   [ins
t_3 : _root_.Module R M] [ins…
· 使用定理 `LinearMap.range.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u
_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用定理 `LinearMap.IsSymmetric.clm_adjoint_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   [inst_3 : CompleteSpace…
· 使用定理 `Submodule.topologicalClosure_eq_self`：topologicalClosure_eq_self : K.top
ologicalClosure = K
· 使用定理 `Submodule.orthogonal_le`：orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <
= K₂) : K₂ᗮ <= K₁ᗮ
· 使用定理 `LinearMap.ker_le_ker_of_range`：ker_le_ker_of_range {S T : E ->ₗ[𝕜] E} (h
S : S.IsSymmetric) (hT : T.IsSymmetric) (h : range S <= range T) : ker T <= ker 
S
-/
theorem ker_le_ker_iff_range_le_range [FiniteDimensional 𝕜 E] {T U : E →L[𝕜] E}
    (hT : T.IsSymmetric) (hU : U.IsSymmetric) :
    U.ker ≤ T.ker ↔ T.range ≤ U.range := by
  refine ⟨fun h ↦ ?_, LinearMap.ker_le_ker_of_range hT hU⟩
  have := FiniteDimensional.complete 𝕜 E
  simpa [orthogonal_ker, hT, hU] using Submodule.orthogonal_le h

/-- Infinite-dimensional version of 7.64(b) in [axler2024]. -/
/-
**ContinuousLinearMap.ker_adjoint_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：ker_adjoint_comp_self (T : E ->L[𝕜] F) : (T† ∘L T).ker = T.ker
参数：T : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `ContinuousLinearMap.coe_coe`：coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->
ₛₗ[σ₁₂] M₂) = f
· 使用定理 `ContinuousLinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->L[𝕜]
 F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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

--- 原说明 ---
Infinite-dimensional version of 7.64(b) in [axler2024].
-/
theorem ker_adjoint_comp_self (T : E →L[𝕜] F) : (T† ∘L T).ker = T.ker := by
  refine le_antisymm (fun _ _ ↦ ?_) fun _ _ ↦ by simp_all
  rw [LinearMap.mem_ker, ← inner_self_eq_zero (𝕜 := 𝕜), coe_coe, ← adjoint_inner_left]
  simp_all
/-
**ContinuousLinearMap.ker_self_comp_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：ker_self_comp_adjoint (T : E ->L[𝕜] F) : (T ∘L T†).ker = T†.ker
参数：T : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->L[𝕜] F) : 
A†† = A
· 使用定理 `ContinuousLinearMap.ker_adjoint_comp_self`：ker_adjoint_comp_self (T : E 
->L[𝕜] F) : (T† ∘L T).ker = T.ker
-/
theorem ker_self_comp_adjoint (T : E →L[𝕜] F) : (T ∘L T†).ker = T†.ker := by
  simpa using T†.ker_adjoint_comp_self

/--
This lemma uses the simp-normal form `⇑(T†) ∘ ⇑T` instead of `⇑(T† ∘L T)`
(note the difference between `∘` and `∘L`).
You may need to rewrite with `ContinuousLinearMap.coe_comp'` before applying this lemma.
-/
/-
**ContinuousLinearMap.adjoint_comp_self_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 
`ContinuousLinearMap`。
形式化陈述：adjoint_comp_self_injective_iff (T : E ->L[𝕜] F) : Function.Injective (T† 
∘ T) ↔ Function.Injective T
参数：T : E ->L[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.coe_comp`：coe_comp (h : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->S
L[σ₁₂] M₂) : ⇑(h ∘SL f) = h ∘ f
· 使用定理 `ContinuousLinearMap.coe_coe`：coe_coe (f : M₁ ->SL[σ₁₂] M₂) : ⇑(f : M₁ ->
ₛₗ[σ₁₂] M₂) = f
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `ContinuousLinearMap.ker_adjoint_comp_self`：ker_adjoint_comp_self (T : E 
->L[𝕜] F) : (T† ∘L T).ker = T.ker
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
This lemma uses the simp-normal form `⇑(T†) ∘ ⇑T` instead of `⇑(T† ∘L T)`
(note the difference between `∘` and `∘L`).
You may need to rewrite with `ContinuousLinearMap.coe_comp'` before applying thi
s lemma.
-/
lemma adjoint_comp_self_injective_iff (T : E →L[𝕜] F) :
    Function.Injective (T† ∘ T) ↔ Function.Injective T := by
  rw [← coe_comp, ← coe_coe, ← LinearMap.ker_eq_bot, ← coe_coe, ← LinearMap.ker_eq_bot,
    ker_adjoint_comp_self]

/--
This lemma uses the simp-normal form `⇑T ∘ ⇑(T†)` instead of `⇑(T ∘L T†)`
(note the difference between `∘` and `∘L`).
You may need to rewrite with `ContinuousLinearMap.coe_comp'` before applying this lemma.
-/
/-
**ContinuousLinearMap.self_comp_adjoint_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 
`ContinuousLinearMap`。
形式化陈述：self_comp_adjoint_injective_iff (T : E ->L[𝕜] F) : Function.Injective (T ∘
 T†) ↔ Function.Injective (T†)
参数：T : E ->L[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->L[𝕜] F) : 
A†† = A
· 使用引理 `ContinuousLinearMap.adjoint_comp_self_injective_iff`：adjoint_comp_self_i
njective_iff (T : E ->L[𝕜] F) : Function.Injective (T† ∘ T) ↔ Function.Injective
 T

--- 原说明 ---
This lemma uses the simp-normal form `⇑T ∘ ⇑(T†)` instead of `⇑(T ∘L T†)`
(note the difference between `∘` and `∘L`).
You may need to rewrite with `ContinuousLinearMap.coe_comp'` before applying thi
s lemma.
-/
lemma self_comp_adjoint_injective_iff (T : E →L[𝕜] F) :
    Function.Injective (T ∘ T†) ↔ Function.Injective (T†) := by
  simpa using T†.adjoint_comp_self_injective_iff

/-- `E →L[𝕜] E` is a star algebra with the adjoint as the star operation. -/
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`E →L[𝕜] E` is a star algebra with the adjoint as the star operation.
-/
instance : Star (E →L[𝕜] E) :=
  ⟨adjoint⟩
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvolutiveStar (E →L[𝕜] E) :=
  ⟨adjoint_adjoint⟩
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarMul (E →L[𝕜] E) :=
  ⟨adjoint_comp⟩
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarRing (E →L[𝕜] E) :=
  ⟨map_add adjoint⟩
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarModule 𝕜 (E →L[𝕜] E) :=
  ⟨map_smulₛₗ adjoint⟩
/-
**ContinuousLinearMap.star_eq_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：star_eq_adjoint (A : E ->L[𝕜] E) : star A = A†
参数：A : E ->L[𝕜] E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_eq_adjoint (A : E →L[𝕜] E) : star A = A† :=
  rfl

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
/-
**ContinuousLinearMap.isSelfAdjoint_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：isSelfAdjoint_iff' {A : E ->L[𝕜] E} : IsSelfAdjoint A ↔ A† = A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A continuous linear operator is self-adjoint iff it is equal to its adjoint.
-/
theorem isSelfAdjoint_iff' {A : E →L[𝕜] E} : IsSelfAdjoint A ↔ A† = A :=
  Iff.rfl
/-
**ContinuousLinearMap.id_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : CompleteSpace E], Continuou
sLinearMap.id 𝕜 E ∈ unitary (E →L[𝕜] E)
参数：E →L[𝕜] E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
@[simp] lemma id_mem_unitary : .id 𝕜 E ∈ unitary (E →L[𝕜] E) := one_mem _
/-
**ContinuousLinearMap.norm_adjoint_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：norm_adjoint_comp_self (A : E ->L[𝕜] F) : ‖A† ∘L A‖ = ‖A‖ * ‖A‖
参数：A : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.opNorm_comp_le`：opNorm_comp_le (f : E ->SL[σ₁₂] F) :
 ‖h.comp f‖ <= ‖h‖ * ‖f‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Real.sqrt_le_sqrt_iff`：sqrt_le_sqrt_iff (hy : 0 <= y) : √x <= √y ↔ x <= 
y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `re_inner_le_norm`：re_inner_le_norm (x y : E) : re ⟪x, y⟫ <= ‖x‖ * ‖y‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `ContinuousLinearMap.apply_norm_eq_sqrt_inner_adjoint_left`：apply_norm_eq
_sqrt_inner_adjoint_left (A : E ->L[𝕜] F) (x : E) : ‖A x‖ = √(re ⟪(A† ∘L A) x, x
⟫)
· 使用定理 `Real.sqrt_le_sqrt`：sqrt_le_sqrt (h : x <= y) : √x <= √y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_adjoint_comp_self (A : E →L[𝕜] F) :
    ‖A† ∘L A‖ = ‖A‖ * ‖A‖ := by
  refine le_antisymm ?_ ?_
  · calc
      ‖A† ∘L A‖ ≤ ‖A†‖ * ‖A‖ := opNorm_comp_le _ _
      _ = ‖A‖ * ‖A‖ := by rw [LinearIsometryEquiv.norm_map]
  · rw [← sq, ← Real.sqrt_le_sqrt_iff (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    refine opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    have :=
      calc
        re ⟪(A† ∘L A) x, x⟫ ≤ ‖(A† ∘L A) x‖ * ‖x‖ := re_inner_le_norm _ _
        _ ≤ ‖A† ∘L A‖ * ‖x‖ * ‖x‖ := by gcongr; exact le_opNorm _ _
    calc
      ‖A x‖ = √(re ⟪(A† ∘L A) x, x⟫) := by rw [apply_norm_eq_sqrt_inner_adjoint_left]
      _ ≤ √(‖A† ∘L A‖ * ‖x‖ * ‖x‖) := Real.sqrt_le_sqrt this
      _ = √‖A† ∘L A‖ * ‖x‖ := by
        simp_rw [mul_assoc, Real.sqrt_mul (norm_nonneg _) (‖x‖ * ‖x‖),
          Real.sqrt_mul_self (norm_nonneg x)]
/-
**ContinuousLinearMap.adjoint_comp_self_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedAddCommGroup F] [inst_3 : InnerProductS
pace 𝕜 E] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : CompleteSpace E] [inst_6 
: CompleteSpace F] {A : E →L[𝕜] F}, ContinuousLinearMap.adjoint A ∘SL A = 0 ↔ A 
= 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.norm_adjoint_comp_self`：norm_adjoint_comp_self (A : 
E ->L[𝕜] F) : ‖A† ∘L A‖ = ‖A‖ * ‖A‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem adjoint_comp_self_eq_zero_iff {A : E →L[𝕜] F} :
    adjoint A ∘L A = 0 ↔ A = 0 := by rw [← norm_eq_zero]; simp [norm_adjoint_comp_self]

/-- The C⋆-algebra instance when `𝕜 := ℂ` can be found in
`Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap.lean`. -/
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The C⋆-algebra instance when `𝕜 := ℂ` can be found in
`Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap.lean`.
-/
instance : CStarRing (E →L[𝕜] E) where
  norm_mul_self_le x := le_of_eq <| Eq.symm <| norm_adjoint_comp_self x
/-
**ContinuousLinearMap.isAdjointPair_inner** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：isAdjointPair_inner (A : E ->L[𝕜] F) : LinearMap.IsAdjointPair (LinearMap.
flip (innerₛₗ 𝕜 (E
参数：A : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->L[𝕜]
 F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isAdjointPair_inner (A : E →L[𝕜] F) :
    LinearMap.IsAdjointPair (LinearMap.flip (innerₛₗ 𝕜 (E := E)))
      (innerₛₗ 𝕜 (E := F)).flip A (A†) := by
  intro x y
  simp [adjoint_inner_left]
/-
**ContinuousLinearMap.adjoint_innerSL_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：adjoint_innerSL_apply (x : E) : adjoint (innerSL 𝕜 x) = toSpanSingleton 𝕜 
x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext_ring`：ext_ring [TopologicalSpace R₁] {f g : R₁ -
>L[R₁] M₁} (h : f 1 = g 1) : f = g
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ext_inner_left`：ext_inner_left {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫)
 : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->L[
𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjoint_innerSL_apply (x : E) :
    adjoint (innerSL 𝕜 x) = toSpanSingleton 𝕜 x :=
  ext_ring <| ext_inner_left 𝕜 <| fun _ => by simp [adjoint_inner_right]
/-
**ContinuousLinearMap.adjoint_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：adjoint_toSpanSingleton (x : E) : adjoint (toSpanSingleton 𝕜 x) = innerSL 
𝕜 x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->L[𝕜] F) : 
A†† = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjoint_toSpanSingleton (x : E) :
    adjoint (toSpanSingleton 𝕜 x) = innerSL 𝕜 x := by
  simp [← adjoint_innerSL_apply]
/-
**ContinuousLinearMap.innerSL_apply_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：innerSL_apply_comp (x : F) (f : E ->L[𝕜] F) : innerSL 𝕜 x ∘L f = innerSL 𝕜
 (adjoint f x)
参数：x : F；f : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->L[𝕜]
 F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem innerSL_apply_comp (x : F) (f : E →L[𝕜] F) :
    innerSL 𝕜 x ∘L f = innerSL 𝕜 (adjoint f x) := by
  ext; simp [adjoint_inner_left]

omit [CompleteSpace E] in
/-
**ContinuousLinearMap.innerSL_apply_comp_of_isSymmetric** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousLinearMap`。
形式化陈述：innerSL_apply_comp_of_isSymmetric (x : E) {f : E ->L[𝕜] E} (hf : f.IsSymme
tric) : innerSL 𝕜 x ∘L f = innerSL 𝕜 (f x)
参数：x : E；hf : f.IsSymmetric。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.apply_clm`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst :
 RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] 
  {T : E →L[𝕜] E}, (↑…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem innerSL_apply_comp_of_isSymmetric (x : E) {f : E →L[𝕜] E} (hf : f.IsSymmetric) :
    innerSL 𝕜 x ∘L f = innerSL 𝕜 (f x) := by
  ext; simp [hf]
/-
**ContinuousLinearMap._root_.InnerProductSpace.adjoint_rankOne** 是 Mathlib 中的一个引
理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.InnerProductSpace.adjoint_rankOne (x : E) (y : F) :
    adjoint (rankOne 𝕜 x y) = rankOne 𝕜 y x := by
  simp [rankOne_def', adjoint_comp, ← adjoint_innerSL_apply]
/-
**ContinuousLinearMap._root_.InnerProductSpace.rankOne_comp** 是 Mathlib 中的一个引理，位
于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.InnerProductSpace.rankOne_comp {E G : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (x : E) (y : F) (f : G →L[𝕜] F) :
    rankOne 𝕜 x y ∘L f = rankOne 𝕜 x (adjoint f y) := by
  simp_rw [rankOne_def', comp_assoc, innerSL_apply_comp]

end

end ContinuousLinearMap

@[expose] public section

/-! ### Self-adjoint operators -/


namespace IsSelfAdjoint

open ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]

/-
**IsSelfAdjoint.adjoint_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：adjoint_eq {A : E ->L[𝕜] E} (hA : IsSelfAdjoint A) : A.adjoint = A
参数：hA : IsSelfAdjoint A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjoint_eq {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) : A.adjoint = A :=
  hA

/-- Every self-adjoint operator on an inner product space is symmetric. -/
/-
**IsSelfAdjoint.isSymmetric** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：isSymmetric {A : E ->L[𝕜] E} (hA : IsSelfAdjoint A) : (A : E ->ₗ[𝕜] E).IsS
ymmetric
参数：hA : IsSelfAdjoint A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->L[
𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫
· 使用定理 `IsSelfAdjoint.adjoint_eq`：adjoint_eq {A : E ->L[𝕜] E} (hA : IsSelfAdjoin
t A) : A.adjoint = A

--- 原说明 ---
Every self-adjoint operator on an inner product space is symmetric.
-/
theorem isSymmetric {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) : (A : E →ₗ[𝕜] E).IsSymmetric := by
  intro x y
  rw_mod_cast [← A.adjoint_inner_right, hA.adjoint_eq]

/-- Conjugating preserves self-adjointness. -/
/-
**IsSelfAdjoint.conj_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：conj_adjoint {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T) (S : E ->L[𝕜] F) : Is
SelfAdjoint (S ∘L T ∘L S.adjoint)
参数：hT : IsSelfAdjoint T；S : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.isSelfAdjoint_iff'`：isSelfAdjoint_iff' {A : E ->L[𝕜]
 E} : IsSelfAdjoint A ↔ A† = A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.adjoint_comp`：adjoint_comp (A : F ->L[𝕜] G) (B : E -
>L[𝕜] F) : (A ∘L B)† = B† ∘L A†
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->L[𝕜] F) : 
A†† = A
· 使用定理 `ContinuousLinearMap.comp_assoc`：comp_assoc {R₄ : Type*} [Semiring R₄] [M
odule R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₃₄ : R₃ ->+* R₄} [RingHomCo
mpTriple σ₁₃ σ₃₄ σ₁₄…

--- 原说明 ---
Conjugating preserves self-adjointness.
-/
theorem conj_adjoint {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (S : E →L[𝕜] F) :
    IsSelfAdjoint (S ∘L T ∘L S.adjoint) := by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _

/-- Conjugating preserves self-adjointness. -/
/-
**IsSelfAdjoint.adjoint_conj** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：adjoint_conj {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T) (S : F ->L[𝕜] E) : Is
SelfAdjoint (S.adjoint ∘L T ∘L S)
参数：hT : IsSelfAdjoint T；S : F ->L[𝕜] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.isSelfAdjoint_iff'`：isSelfAdjoint_iff' {A : E ->L[𝕜]
 E} : IsSelfAdjoint A ↔ A† = A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.adjoint_comp`：adjoint_comp (A : F ->L[𝕜] G) (B : E -
>L[𝕜] F) : (A ∘L B)† = B† ∘L A†
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->L[𝕜] F) : 
A†† = A
· 使用定理 `ContinuousLinearMap.comp_assoc`：comp_assoc {R₄ : Type*} [Semiring R₄] [M
odule R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₃₄ : R₃ ->+* R₄} [RingHomCo
mpTriple σ₁₃ σ₃₄ σ₁₄…

--- 原说明 ---
Conjugating preserves self-adjointness.
-/
theorem adjoint_conj {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (S : F →L[𝕜] E) :
    IsSelfAdjoint (S.adjoint ∘L T ∘L S) := by
  rw [isSelfAdjoint_iff'] at hT ⊢
  simp only [hT, adjoint_comp, adjoint_adjoint]
  exact ContinuousLinearMap.comp_assoc _ _ _
/-
**IsSelfAdjoint._root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric** 是 Mat
hlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric {A : E →L[𝕜] E} :
    IsSelfAdjoint A ↔ (A : E →ₗ[𝕜] E).IsSymmetric :=
  ⟨fun hA => hA.isSymmetric, fun hA =>
    ext fun x => ext_inner_right 𝕜 fun y => (A.adjoint_inner_left y x).symm ▸ (hA x y).symm⟩
/-
**IsSelfAdjoint._root_.LinearMap.IsSymmetric.isSelfAdjoint** 是 Mathlib 中的一个定理，位于
命名空间 `IsSelfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.IsSymmetric.isSelfAdjoint {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) : IsSelfAdjoint A := by
  rwa [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA

/-- The orthogonal projection is self-adjoint. -/
@[simp]
/-
**IsSelfAdjoint._root_.isSelfAdjoint_starProjection** 是 Mathlib 中的一个定理，位于命名空间 `I
sSelfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal projection is self-adjoint.
-/
theorem _root_.isSelfAdjoint_starProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsSelfAdjoint U.starProjection :=
  U.starProjection_isSymmetric.isSelfAdjoint
/-
**IsSelfAdjoint.conj_starProjection** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：conj_starProjection {T : E ->L[𝕜] E} (hT : IsSelfAdjoint T) (U : Submodule
 𝕜 E) [U.HasOrthogonalProjection] : IsSelfAdjoint (U.starProjection ∘L T ∘L U.st
arProjection)
参数：hT : IsSelfAdjoint T；U : Submodule 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.mul_def`：mul_def (f g : M₁ ->L[R₁] M₁) : f * g = f ∘
L g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsSelfAdjoint.conjugate_self`：conjugate_self {x : R} (hx : IsSelfAdjoint
 x) {z : R} (hz : IsSelfAdjoint z) : IsSelfAdjoint (z * x * z)
· 使用定理 `isSelfAdjoint_starProjection`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RC
Like 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst
_3 : CompleteSpace…
-/
theorem conj_starProjection {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsSelfAdjoint (U.starProjection ∘L T ∘L U.starProjection) := by
  rw [← mul_def, ← mul_def, ← mul_assoc]
  exact hT.conjugate_self <| isSelfAdjoint_starProjection U

end IsSelfAdjoint

namespace ContinuousLinearMap

variable {T : E →L[𝕜] E} [CompleteSpace E]

/-- An operator `T` is normal iff `‖T v‖ = ‖(adjoint T) v‖` for all `v`. -/
/-
**ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearMap`。
形式化陈述：isStarNormal_iff_norm_eq_adjoint : IsStarNormal T ↔ forall v : E, ‖T v‖ = 
‖adjoint T v‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isStarNormal_iff`：∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] (x :
 R), IsStarNormal x ↔ Commute (star x) x
· 使用定理 `Commute.eq_1`：∀ {S : Type u_3} [inst : Mul S] (a b : S), Commute a b = S
emiconjBy a b b
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSelfAdjoint.isSymmetric`：isSymmetric {A : E ->L[𝕜] E} (hA : IsSelfAdjo
int A) : (A : E ->ₗ[𝕜] E).IsSymmetric
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)
· 使用定理 `IsSelfAdjoint.star_mul_self`：star_mul_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (star x * x)
· 使用定理 `IsSelfAdjoint.mul_star_self`：mul_star_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (x * star x)
· 使用定理 `ContinuousLinearMap.toLinearMap_sub`：toLinearMap_sub (f g : M ->SL[σ₁₂] 
M₂) : (↑(f - g) : M ->ₛₗ[σ₁₂] M₂) = f - g
· 使用定理 `ContinuousLinearMap.star_eq_adjoint`：star_eq_adjoint (A : E ->L[𝕜] E) : 
star A = A†
· 使用定理 `LinearMap.IsSymmetric.inner_map_self_eq_zero`：∀ {𝕜 : Type u_1} {E : Type
 u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSp
ace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.IsSy…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_apply_eq_comp`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : Mul F} [self : IsMulApplyEqComp F α]   (f g : F) (x : α),
 (f * g…
· 使用定理 `ContinuousLinearMap.instIsMulApplyEqCompId`：∀ {R₁ : Type u_1} [inst : Se
miring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoi
d M₁]   [inst_3 : _root_.Module …
· 使用定理 `ContinuousLinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->L[𝕜]
 F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `ContinuousLinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->L[
𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
An operator `T` is normal iff `‖T v‖ = ‖(adjoint T) v‖` for all `v`.
-/
theorem isStarNormal_iff_norm_eq_adjoint :
    IsStarNormal T ↔ ∀ v : E, ‖T v‖ = ‖adjoint T v‖ := by
  rw [isStarNormal_iff, Commute, SemiconjBy, ← sub_eq_zero]
  simp_rw [ContinuousLinearMap.ext_iff, ← coe_coe, toLinearMap_sub, ← LinearMap.ext_iff,
    toLinearMap_zero]
  have := star_eq_adjoint T ▸ toLinearMap_sub (star _ * T) _ ▸
    ((IsSelfAdjoint.star_mul_self T).sub (IsSelfAdjoint.mul_star_self T)).isSymmetric
  simp_rw [star_eq_adjoint, ← LinearMap.IsSymmetric.inner_map_self_eq_zero this,
    LinearMap.sub_apply, inner_sub_left, coe_coe, mul_apply_eq_comp, adjoint_inner_left,
    inner_self_eq_norm_sq_to_K, ← adjoint_inner_right T, inner_self_eq_norm_sq_to_K,
    sub_eq_zero, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  norm_cast
/-
**ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_zero_iff** 是 Mathlib 中的一个定理，
位于命名空间 `ContinuousLinearMap.IsStarNormal`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E} [inst_3 : CompleteSpa
ce E],   IsStarNormal T → ∀ (x : E), (ContinuousLinearMap.adjoint T) x = 0 ↔ T x
 = 0
参数：x : E；ContinuousLinearMap.adjoint T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint`：isStarNormal_iff_n
orm_eq_adjoint : IsStarNormal T ↔ forall v : E, ‖T v‖ = ‖adjoint T v‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsStarNormal.adjoint_apply_eq_zero_iff (hT : IsStarNormal T) (x : E) :
    adjoint T x = 0 ↔ T x = 0 := by
  simp_rw [← norm_eq_zero (E := E), ← isStarNormal_iff_norm_eq_adjoint.mp hT]

open ContinuousLinearMap
/-
**ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearMap.IsStarNormal`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E} [inst_3 : CompleteSpa
ce E], IsStarNormal T → (↑(ContinuousLinearMap.adjoint T)).ker = (↑T).ker
参数：↑(ContinuousLinearMap.adjoint T)；↑T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_zero_iff`：∀ {𝕜 : Type 
u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : 
InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E} [inst_3…
-/
theorem IsStarNormal.ker_adjoint_eq_ker (hT : IsStarNormal T) :
    (adjoint T).ker = T.ker :=
  Submodule.ext hT.adjoint_apply_eq_zero_iff

/-- The range of a normal operator is pairwise orthogonal to its kernel.

This is a weaker version of `LinearMap.IsSymmetric.orthogonal_range`
but with stronger type class assumptions (i.e., `CompleteSpace`). -/
/-
**ContinuousLinearMap.IsStarNormal.orthogonal_range** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap.IsStarNormal`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E} [inst_3 : CompleteSpa
ce E], IsStarNormal T → (↑T).rangeᗮ = (↑T).ker
参数：↑T；↑T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker`：∀ {𝕜 : Type u_1} {E
 : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerPr
oductSpace 𝕜 E]   {T : E →L[𝕜] E} [inst_3…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.orthogonal_range`：orthogonal_range (T : E ->L[𝕜] F) 
: T.rangeᗮ = T†.ker

--- 原说明 ---
The range of a normal operator is pairwise orthogonal to its kernel.

This is a weaker version of `LinearMap.IsSymmetric.orthogonal_range`
but with stronger type class assumptions (i.e., `CompleteSpace`).
-/
theorem IsStarNormal.orthogonal_range (hT : IsStarNormal T) : T.rangeᗮ = T.ker :=
  T.orthogonal_range ▸ hT.ker_adjoint_eq_ker

set_option backward.isDefEq.respectTransparency false in
/- TODO: As we have a more general result of this for elements in non-unital C⋆-algebras
(see `Mathlib/Analysis/CStarAlgebra/Projection.lean`), we will want to simplify the proof
by using the complexification of an inner product space over `𝕜`. -/
/-- An idempotent operator is self-adjoint iff it is normal. -/
/-
**ContinuousLinearMap.IsIdempotentElem.isSelfAdjoint_iff_isStarNormal** 是 Mathli
b 中的一个定理，位于命名空间 `ContinuousLinearMap.IsIdempotentElem`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E} [inst_3 : CompleteSpa
ce E], IsIdempotentElem T → (IsSelfAdjoint T ↔ IsStarNormal T)
参数：IsSelfAdjoint T ↔ IsStarNormal T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isStarNormal_iff`：∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] (x :
 R), IsStarNormal x ↔ Commute (star x) x
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `ContinuousLinearMap.ext_iff`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `mul_apply_eq_comp`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : Mul F} [self : IsMulApplyEqComp F α]   (f g : F) (x : α),
 (f * g…
· 使用定理 `ContinuousLinearMap.instIsMulApplyEqCompId`：∀ {R₁ : Type u_1} [inst : Se
miring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoi
d M₁]   [inst_3 : _root_.Module …
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `LinearMap.IsSymmetric.clm_adjoint_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [i
nst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]
   [inst_3 : CompleteSpace…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
An idempotent operator is self-adjoint iff it is normal.
-/
theorem IsIdempotentElem.isSelfAdjoint_iff_isStarNormal (hT : IsIdempotentElem T) :
    IsSelfAdjoint T ↔ IsStarNormal T := by
  refine ⟨fun h => by rw [isStarNormal_iff, h], fun h => ?_⟩
  suffices T = star T * T from this ▸ IsSelfAdjoint.star_mul_self _
  rw [← sub_eq_zero, ContinuousLinearMap.ext_iff]
  simp_rw [zero_apply, ← norm_eq_zero (E := E)]
  have :=
    calc (∀ x : E, ‖(T - star T * T) x‖ = 0) ↔ ∀ x, ‖(adjoint (1 - T)) (T x)‖ = 0 := by
          simp [star_eq_adjoint, one_def]
      _ ↔ ∀ x, ‖(1 - T) (T x)‖ = 0 := by
          simp only [isStarNormal_iff_norm_eq_adjoint.mp h.one_sub]
      _ ↔ ∀ x, ‖(T - T * T) x‖ = 0 := by simp
      _ ↔ T - T * T = 0 := by simp only [norm_eq_zero, ContinuousLinearMap.ext_iff, zero_apply]
      _ ↔ IsIdempotentElem T := by simp only [sub_eq_zero, IsIdempotentElem, eq_comm]
  exact this.mpr hT

/-- A continuous linear map is a star projection iff it is idempotent and normal. -/
/-
**ContinuousLinearMap.isStarProjection_iff_isIdempotentElem_and_isStarNormal** 是
 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：isStarProjection_iff_isIdempotentElem_and_isStarNormal : IsStarProjection 
T ↔ IsIdempotentElem T ∧ IsStarNormal T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isStarProjection_iff`：∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] 
(p : R), IsStarProjection p ↔ IsIdempotentElem p ∧ IsSelfAdjoint p
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.isSelfAdjoint_iff_isStarNormal`：∀ {
𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [
inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E} [inst_3…

--- 原说明 ---
A continuous linear map is a star projection iff it is idempotent and normal.
-/
theorem isStarProjection_iff_isIdempotentElem_and_isStarNormal :
    IsStarProjection T ↔ IsIdempotentElem T ∧ IsStarNormal T := by
  rw [isStarProjection_iff, and_congr_right_iff]
  exact fun h => IsIdempotentElem.isSelfAdjoint_iff_isStarNormal h
/-
**ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection** 是 Mathlib 中的一
个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：isStarProjection_iff_isSymmetricProjection : IsStarProjection T ↔ T.IsSymm
etricProjection
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isStarProjection_iff_isSymmetricProjection :
    IsStarProjection T ↔ T.IsSymmetricProjection := by
  simp [isStarProjection_iff, LinearMap.isSymmetricProjection_iff,
    isSelfAdjoint_iff_isSymmetric, IsIdempotentElem, End.mul_eq_comp, ← toLinearMap_comp, mul_def]

alias ⟨IsStarProjection.isSymmetricProjection, LinearMap.IsSymmetricProjection.isStarProjection⟩ :=
  isStarProjection_iff_isSymmetricProjection

/-- Star projection operators are equal iff their range are. -/
/-
**ContinuousLinearMap.IsStarProjection.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousLinearMap.IsStarProjection`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E} [inst_3 : CompleteSpa
ce E] {S : E →L[𝕜] E},   IsStarProjection S → IsStarProjection T → (S = T ↔ (↑S)
.range = (↑T).range)
参数：S = T ↔ (↑S).range = (↑T).range。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetricProjection.ext_iff`：∀ {𝕜 : Type u_1} {E : Type u_2}
 [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜
 E]   {S T : E →ₗ[𝕜] E}, S.Is…
· 使用定理 `ContinuousLinearMap.IsStarProjection.isSymmetricProjection`：∀ {𝕜 : Type 
u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : 
InnerProductSpace 𝕜 E]   {T : E →L[𝕜] E} [inst_3…

--- 原说明 ---
Star projection operators are equal iff their range are.
-/
theorem IsStarProjection.ext_iff {S : E →L[𝕜] E}
    (hS : IsStarProjection S) (hT : IsStarProjection T) :
    S = T ↔ S.range = T.range := by
  simpa using hS.isSymmetricProjection.ext_iff hT.isSymmetricProjection

alias ⟨_, IsStarProjection.ext⟩ := IsStarProjection.ext_iff
/-
**ContinuousLinearMap._root_.InnerProductSpace.isStarProjection_rankOne_self** 是
 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.InnerProductSpace.isStarProjection_rankOne_self {x : E} (hx : ‖x‖ = 1) :
    IsStarProjection (rankOne 𝕜 x x) := (isSymmetricProjection_rankOne_self hx).isStarProjection

open Module End Submodule in
/-
**ContinuousLinearMap.orthogonal_mem_invtSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：orthogonal_mem_invtSubmodule {T : E ->L[𝕜] E} {U : Submodule 𝕜 E} (h : U i
n invtSubmodule T.adjoint.toLinearMap) : Uᗮ in invtSubmodule T.toLinearMap
参数：h : U in invtSubmodule T.adjoint.toLinearMap。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem orthogonal_mem_invtSubmodule {T : E →L[𝕜] E} {U : Submodule 𝕜 E}
    (h : U ∈ invtSubmodule T.adjoint.toLinearMap) :
    Uᗮ ∈ invtSubmodule T.toLinearMap := by
  simp only [mem_invtSubmodule_iff_forall_mem_of_mem, coe_coe, mem_orthogonal] at h ⊢
  grind [T.adjoint_inner_left]

open Module End in
/-
**ContinuousLinearMap.mem_invtSubmodule_adjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：mem_invtSubmodule_adjoint_iff {T : E ->L[𝕜] E} {U : Submodule 𝕜 E} [U.HasO
rthogonalProjection] : U in invtSubmodule T.adjoint.toLinearMap ↔ Uᗮ in invtSubm
odule T.toLinearMap where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.orthogonal_mem_invtSubmodule`：orthogonal_mem_invtSub
module {T : E ->L[𝕜] E} {U : Submodule 𝕜 E} (h : U in invtSubmodule T.adjoint.to
LinearMap) : Uᗮ in invtSubmodule T.toL…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->L[𝕜] F) : 
A†† = A
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
-/
theorem mem_invtSubmodule_adjoint_iff {T : E →L[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] :
    U ∈ invtSubmodule T.adjoint.toLinearMap ↔ Uᗮ ∈ invtSubmodule T.toLinearMap where
  mp := orthogonal_mem_invtSubmodule
  mpr := by simpa using orthogonal_mem_invtSubmodule (T := T.adjoint) (U := Uᗮ)

end ContinuousLinearMap

/-- `U.starProjection` is a star projection. -/
@[simp]
/-
**isStarProjection_starProjection** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStarProjection_starProjection [CompleteSpace E] {U : Submodule 𝕜 E} [U.H
asOrthogonalProjection] : IsStarProjection U.starProjection
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.isIdempotentElem_starProjection`：isIdempotentElem_starProjecti
on : IsIdempotentElem K.starProjection
· 使用定理 `isSelfAdjoint_starProjection`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RC
Like 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst
_3 : CompleteSpace…

--- 原说明 ---
`U.starProjection` is a star projection.
-/
theorem isStarProjection_starProjection [CompleteSpace E] {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] : IsStarProjection U.starProjection :=
  ⟨U.isIdempotentElem_starProjection, isSelfAdjoint_starProjection U⟩

open ContinuousLinearMap in
/-- An operator is a star projection if and only if it is an orthogonal projection. -/
/-
**isStarProjection_iff_eq_starProjection_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isStarProjection_iff_eq_starProjection_range [CompleteSpace E] {p : E ->L[
𝕜] E} : IsStarProjection p ↔ exists (_ : p.range.HasOrthogonalProjection), p = p
.range.starProjection
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection`：isStarPr
ojection_iff_isSymmetricProjection : IsStarProjection T ↔ T.IsSymmetricProjectio
n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An operator is a star projection if and only if it is an orthogonal projection.
-/
theorem isStarProjection_iff_eq_starProjection_range [CompleteSpace E] {p : E →L[𝕜] E} :
    IsStarProjection p ↔ ∃ (_ : p.range.HasOrthogonalProjection),
    p = p.range.starProjection := by
  simp_rw [p.isStarProjection_iff_isSymmetricProjection.eq,
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range, coe_inj]
/-
**isStarProjection_iff_eq_starProjection** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isStarProjection_iff_eq_starProjection [CompleteSpace E] {p : E ->L[𝕜] E} 
: IsStarProjection p ↔ exists (K : Submodule 𝕜 E) (_ : K.HasOrthogonalProjection
), p = K.starProjection
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isStarProjection_iff_eq_starProjection_range`：isStarProjection_iff_eq_st
arProjection_range [CompleteSpace E] {p : E ->L[𝕜] E} : IsStarProjection p ↔ exi
sts (_ : p.range.HasOrthogonalProj…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isStarProjection_iff_eq_starProjection [CompleteSpace E] {p : E →L[𝕜] E} :
    IsStarProjection p
      ↔ ∃ (K : Submodule 𝕜 E) (_ : K.HasOrthogonalProjection), p = K.starProjection :=
  ⟨fun h ↦ ⟨p.range, isStarProjection_iff_eq_starProjection_range.mp h⟩,
    by rintro ⟨_, _, rfl⟩; simp⟩

namespace LinearMap

variable [CompleteSpace E]
variable {T : E →ₗ[𝕜] E}

/-- The **Hellinger--Toeplitz theorem**: Construct a self-adjoint operator from an everywhere
  defined symmetric operator. -/
/-
**LinearMap.IsSymmetric.toSelfAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.IsSym
metric`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_2} →     [inst : RCLike 𝕜] →       [inst_1 
: NormedAddCommGroup E] →         [inst_2 : InnerProductSpace 𝕜 E] →           [
inst_3 : CompleteSpace E] → {T : E →ₗ[𝕜] E} → T.IsSymmetric → ↥(selfAdjoint (E →
L[𝕜] E))
参数：selfAdjoint (E →L[𝕜] E)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.continuous`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [
CompleteSpace E] {T : …

--- 原说明 ---
The **Hellinger--Toeplitz theorem**: Construct a self-adjoint operator from an e
verywhere
  defined symmetric operator.
-/
def IsSymmetric.toSelfAdjoint (hT : IsSymmetric T) : selfAdjoint (E →L[𝕜] E) :=
  ⟨⟨T, hT.continuous⟩, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT⟩
/-
**LinearMap.IsSymmetric.coe_toSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.I
sSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : CompleteSpace E] {T : E →ₗ[
𝕜] E} (hT : T.IsSymmetric), ↑↑hT.toSelfAdjoint = T
参数：hT : T.IsSymmetric。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem IsSymmetric.coe_toSelfAdjoint (hT : IsSymmetric T) : (hT.toSelfAdjoint : E →ₗ[𝕜] E) = T :=
  rfl
/-
**LinearMap.IsSymmetric.toSelfAdjoint_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
.IsSymmetric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : CompleteSpace E] {T : E →ₗ[
𝕜] E} (hT : T.IsSymmetric) {x : E}, ↑↑hT.toSelfAdjoint x = T x
参数：hT : T.IsSymmetric。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem IsSymmetric.toSelfAdjoint_apply (hT : IsSymmetric T) {x : E} :
    (hT.toSelfAdjoint : E → E) x = T x :=
  rfl

end LinearMap

namespace LinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]

/-- The adjoint of an operator from the finite-dimensional inner product space `E` to the
finite-dimensional inner product space `F`. -/
/-
**LinearMap.adjoint** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：adjoint : (E ->ₗ[𝕜] F) ≃ₗ⋆[𝕜] F ->ₗ[𝕜] E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K

--- 原说明 ---
The adjoint of an operator from the finite-dimensional inner product space `E` t
o the
finite-dimensional inner product space `F`.
-/
def adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] F →ₗ[𝕜] E :=
  haveI := FiniteDimensional.complete 𝕜 E
  haveI := FiniteDimensional.complete 𝕜 F
  /- Note: Instead of the two instances above, the following works:
    ```
      haveI := FiniteDimensional.complete 𝕜
      haveI := FiniteDimensional.complete 𝕜
    ```
    But removing one of the `have`s makes it fail. The reason is that `E` and `F` don't live
    in the same universe, so the first `have` can no longer be used for `F` after its universe
    metavariable has been assigned to that of `E`!
  -/
  ((LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] F) ≃ₗ[𝕜] E →L[𝕜] F).trans
      ContinuousLinearMap.adjoint.toLinearEquiv).trans
    LinearMap.toContinuousLinearMap.symm
/-
**LinearMap.adjoint_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：adjoint_toContinuousLinearMap (A : E ->ₗ[𝕜] F) : haveI
参数：A : E ->ₗ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
-/
theorem adjoint_toContinuousLinearMap (A : E →ₗ[𝕜] F) :
    haveI := FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.adjoint.toContinuousLinearMap = A.toContinuousLinearMap.adjoint :=
  rfl
/-
**LinearMap.adjoint_eq_toCLM_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：adjoint_eq_toCLM_adjoint (A : E ->ₗ[𝕜] F) : haveI
参数：A : E ->ₗ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
-/
theorem adjoint_eq_toCLM_adjoint (A : E →ₗ[𝕜] F) :
    haveI := FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.adjoint = A.toContinuousLinearMap.adjoint :=
  rfl
/-
**LinearMap._root_.ContinuousLinearMap.adjoint_toLinearMap** 是 Mathlib 中的一个定理，位于
命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.adjoint_toLinearMap (A : E →L[𝕜] F) :
    haveI := FiniteDimensional.complete 𝕜 E
    haveI := FiniteDimensional.complete 𝕜 F
    A.toLinearMap.adjoint = A.adjoint.toLinearMap :=
  rfl

/-- The fundamental property of the adjoint. -/
/-
**LinearMap.adjoint_inner_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：adjoint_inner_left (A : E ->ₗ[𝕜] F) (x : E) (y : F) : ⟪adjoint A y, x⟫ = ⟪
y, A x⟫
参数：A : E ->ₗ[𝕜] F；x : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_toContinuousLinearMap`：coe_toContinuousLinearMap (f : E ->
ₗ[𝕜] F') : ((LinearMap.toContinuousLinearMap f) : E ->ₗ[𝕜] F') = f
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `LinearMap.adjoint_eq_toCLM_adjoint`：adjoint_eq_toCLM_adjoint (A : E ->ₗ[
𝕜] F) : haveI
· 使用定理 `ContinuousLinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->L[𝕜]
 F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫

--- 原说明 ---
The fundamental property of the adjoint.
-/
theorem adjoint_inner_left (A : E →ₗ[𝕜] F) (x : E) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫ := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A, adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left _ x y

/-- The fundamental property of the adjoint. -/
/-
**LinearMap.adjoint_inner_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：adjoint_inner_right (A : E ->ₗ[𝕜] F) (x : E) (y : F) : ⟪x, adjoint A y⟫ = 
⟪A x, y⟫
参数：A : E ->ₗ[𝕜] F；x : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_toContinuousLinearMap`：coe_toContinuousLinearMap (f : E ->
ₗ[𝕜] F') : ((LinearMap.toContinuousLinearMap f) : E ->ₗ[𝕜] F') = f
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `LinearMap.adjoint_eq_toCLM_adjoint`：adjoint_eq_toCLM_adjoint (A : E ->ₗ[
𝕜] F) : haveI
· 使用定理 `ContinuousLinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->L[
𝕜] F) (x : E) (y : F) : ⟪x, (A†) y⟫ = ⟪A x, y⟫

--- 原说明 ---
The fundamental property of the adjoint.
-/
theorem adjoint_inner_right (A : E →ₗ[𝕜] F) (x : E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫ := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← coe_toContinuousLinearMap A, adjoint_eq_toCLM_adjoint]
  exact ContinuousLinearMap.adjoint_inner_right _ x y

/-- The adjoint is involutive. -/
@[simp]
/-
**LinearMap.adjoint_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：adjoint_adjoint (A : E ->ₗ[𝕜] F) : A.adjoint.adjoint = A
参数：A : E ->ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `ext_inner_left`：ext_inner_left {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫)
 : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->ₗ[𝕜] F) (x :
 E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫
· 使用定理 `LinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->ₗ[𝕜] F) (x : E
) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫

--- 原说明 ---
The adjoint is involutive.
-/
theorem adjoint_adjoint (A : E →ₗ[𝕜] F) : A.adjoint.adjoint = A := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [adjoint_inner_right, adjoint_inner_left]

/-- The adjoint of the composition of two operators is the composition of the two adjoints
in reverse order. -/
@[simp]
/-
**LinearMap.adjoint_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：adjoint_comp (A : F ->ₗ[𝕜] G) (B : E ->ₗ[𝕜] F) : (A ∘ₗ B).adjoint = B.adjo
int ∘ₗ A.adjoint
参数：A : F ->ₗ[𝕜] G；B : E ->ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `ext_inner_left`：ext_inner_left {x y : E} (h : forall v, ⟪v, x⟫ = ⟪v, y⟫)
 : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->ₗ[𝕜] F) (x :
 E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The adjoint of the composition of two operators is the composition of the two ad
joints
in reverse order.
-/
theorem adjoint_comp (A : F →ₗ[𝕜] G) (B : E →ₗ[𝕜] F) :
    (A ∘ₗ B).adjoint = B.adjoint ∘ₗ A.adjoint := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  simp only [adjoint_inner_right, LinearMap.coe_comp, Function.comp_apply]

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all `x` and `y`. -/
/-
**LinearMap.eq_adjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eq_adjoint_iff (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E) : A = B.adjoint ↔ forall 
x y, ⟪A x, y⟫ = ⟪x, B y⟫
参数：A : E ->ₗ[𝕜] F；B : F ->ₗ[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->ₗ[𝕜] F) (x : E
) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `ext_inner_right`：ext_inner_right {x y : E} (h : forall v, ⟪x, v⟫ = ⟪y, v
⟫) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y
⟫ = ⟪x, B y⟫`
for all `x` and `y`.
-/
theorem eq_adjoint_iff (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ x y, ⟪A x, y⟫ = ⟪x, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right 𝕜 fun y => by simp only [adjoint_inner_left, h x y]

@[simp]
/-
**LinearMap.IsSymmetric.adjoint_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymmet
ric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : FiniteDimensional 𝕜 E] {A :
 E →ₗ[𝕜] E}, A.IsSymmetric → LinearMap.adjoint A = A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `LinearMap.eq_adjoint_iff`：eq_adjoint_iff (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] 
E) : A = B.adjoint ↔ forall x y, ⟪A x, y⟫ = ⟪x, B y⟫
-/
theorem IsSymmetric.adjoint_eq {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) :
    A.adjoint = A := by
  rwa [eq_comm, eq_adjoint_iff A A]
/-
**LinearMap.adjoint_id** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：adjoint_id : (.id : E ->ₗ[𝕜] E).adjoint = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.adjoint_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [
inst_3 : FiniteDimensi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma adjoint_id : (.id : E →ₗ[𝕜] E).adjoint = .id := by simp
/-
**LinearMap.adjoint_one** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：adjoint_one : (1 : E ->ₗ[𝕜] E).adjoint = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.adjoint_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [
inst_3 : FiniteDimensi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma adjoint_one : (1 : E →ₗ[𝕜] E).adjoint = 1 := by simp

/-- 7.6(b) from [axler2024].
See `ContinuousLinearMap.orthogonal_ker` for the infinite-dimensional version. -/
/-
**LinearMap.orthogonal_ker** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：orthogonal_ker (A : E ->ₗ[𝕜] F) : A.kerᗮ = A.adjoint.range
参数：A : E ->ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.topologicalClosure_eq_self`：topologicalClosure_eq_self : K.top
ologicalClosure = K
· 使用定理 `ContinuousLinearMap.orthogonal_ker`：orthogonal_ker (T : E ->L[𝕜] F) : T.
kerᗮ = T†.range.topologicalClosure

--- 原说明 ---
7.6(b) from [axler2024].
See `ContinuousLinearMap.orthogonal_ker` for the infinite-dimensional version.
-/
lemma orthogonal_ker (A : E →ₗ[𝕜] F) : A.kerᗮ = A.adjoint.range := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.orthogonal_ker

/-- 7.6(a) from [axler2024].
See `ContinuousLinearMap.orthogonal_range` for the infinite-dimensional version. -/
/-
**LinearMap.orthogonal_range** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：orthogonal_range (A : E ->ₗ[𝕜] F) : A.rangeᗮ = A.adjoint.ker
参数：A : E ->ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.orthogonal_range`：orthogonal_range (T : E ->L[𝕜] F) 
: T.rangeᗮ = T†.ker
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…

--- 原说明 ---
7.6(a) from [axler2024].
See `ContinuousLinearMap.orthogonal_range` for the infinite-dimensional version.
-/
lemma orthogonal_range (A : E →ₗ[𝕜] F) : A.rangeᗮ = A.adjoint.ker := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.orthogonal_range

/-- 7.64(b) in [axler2024] -/
/-
**LinearMap.ker_adjoint_comp_self** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：ker_adjoint_comp_self (A : E ->ₗ[𝕜] F) : (A.adjoint ∘ₗ A).ker = A.ker
参数：A : E ->ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.ker_adjoint_comp_self`：ker_adjoint_comp_self (T : E 
->L[𝕜] F) : (T† ∘L T).ker = T.ker
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…

--- 原说明 ---
7.64(b) in [axler2024]
-/
lemma ker_adjoint_comp_self (A : E →ₗ[𝕜] F) : (A.adjoint ∘ₗ A).ker = A.ker := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using! A.toContinuousLinearMap.ker_adjoint_comp_self
/-
**LinearMap.ker_self_comp_adjoint** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：ker_self_comp_adjoint (A : E ->ₗ[𝕜] F) : (A ∘ₗ A.adjoint).ker = A.adjoint.
ker
参数：A : E ->ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->ₗ[𝕜] F) : A.adjoint.
adjoint = A
· 使用引理 `LinearMap.ker_adjoint_comp_self`：ker_adjoint_comp_self (A : E ->ₗ[𝕜] F) 
: (A.adjoint ∘ₗ A).ker = A.ker
-/
lemma ker_self_comp_adjoint (A : E →ₗ[𝕜] F) : (A ∘ₗ A.adjoint).ker = A.adjoint.ker := by
  simpa using A.adjoint.ker_adjoint_comp_self

/--
This lemma uses the simp-normal form `⇑(A.adjoint) ∘ ⇑A` instead of `⇑(A.adjoint ∘ₗ A)`
(note the difference between `∘` and `∘ₗ`).
You may need to rewrite with `LinearMap.coe_comp` before applying this lemma.
-/
/-
**LinearMap.adjoint_comp_self_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
`。
形式化陈述：adjoint_comp_self_injective_iff (A : E ->ₗ[𝕜] F) : Function.Injective (A.a
djoint ∘ A) ↔ Function.Injective A
参数：A : E ->ₗ[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用引理 `LinearMap.ker_adjoint_comp_self`：ker_adjoint_comp_self (A : E ->ₗ[𝕜] F) 
: (A.adjoint ∘ₗ A).ker = A.ker
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
This lemma uses the simp-normal form `⇑(A.adjoint) ∘ ⇑A` instead of `⇑(A.adjoint
 ∘ₗ A)`
(note the difference between `∘` and `∘ₗ`).
You may need to rewrite with `LinearMap.coe_comp` before applying this lemma.
-/
lemma adjoint_comp_self_injective_iff (A : E →ₗ[𝕜] F) :
    Function.Injective (A.adjoint ∘ A) ↔ Function.Injective A := by
  rw [← coe_comp, ← ker_eq_bot, ← ker_eq_bot, ker_adjoint_comp_self]

/--
This lemma uses the simp-normal form `⇑A ∘ ⇑(A.adjoint)` instead of `⇑(A ∘ₗ A.adjoint)`
(note the difference between `∘` and `∘ₗ`).
You may need to rewrite with `LinearMap.coe_comp` before applying this lemma.
-/
/-
**LinearMap.self_comp_adjoint_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
`。
形式化陈述：self_comp_adjoint_injective_iff (A : E ->ₗ[𝕜] F) : Function.Injective (A ∘
 A.adjoint) ↔ Function.Injective A.adjoint
参数：A : E ->ₗ[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->ₗ[𝕜] F) : A.adjoint.
adjoint = A
· 使用引理 `LinearMap.adjoint_comp_self_injective_iff`：adjoint_comp_self_injective_i
ff (A : E ->ₗ[𝕜] F) : Function.Injective (A.adjoint ∘ A) ↔ Function.Injective A

--- 原说明 ---
This lemma uses the simp-normal form `⇑A ∘ ⇑(A.adjoint)` instead of `⇑(A ∘ₗ A.ad
joint)`
(note the difference between `∘` and `∘ₗ`).
You may need to rewrite with `LinearMap.coe_comp` before applying this lemma.
-/
lemma self_comp_adjoint_injective_iff (A : E →ₗ[𝕜] F) :
    Function.Injective (A ∘ A.adjoint) ↔ Function.Injective A.adjoint := by
  simpa using A.adjoint.adjoint_comp_self_injective_iff

/-- 7.64(c) in [axler2024]. -/
/-
**LinearMap.range_adjoint_comp_self** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：range_adjoint_comp_self (A : E ->ₗ[𝕜] F) : (A.adjoint ∘ₗ A).range = A.adjo
int.range
参数：A : E ->ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.orthogonal_ker`：orthogonal_ker (A : E ->ₗ[𝕜] F) : A.kerᗮ = A.a
djoint.range
· 使用定理 `LinearMap.range.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u
_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用定理 `LinearMap.adjoint_comp`：adjoint_comp (A : F ->ₗ[𝕜] G) (B : E ->ₗ[𝕜] F) :
 (A ∘ₗ B).adjoint = B.adjoint ∘ₗ A.adjoint
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->ₗ[𝕜] F) : A.adjoint.
adjoint = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LinearMap.ker_adjoint_comp_self`：ker_adjoint_comp_self (A : E ->ₗ[𝕜] F) 
: (A.adjoint ∘ₗ A).ker = A.ker

--- 原说明 ---
7.64(c) in [axler2024].
-/
lemma range_adjoint_comp_self (A : E →ₗ[𝕜] F) : (A.adjoint ∘ₗ A).range = A.adjoint.range :=
  calc
    (A.adjoint ∘ₗ A).range = (A.adjoint ∘ₗ A).kerᗮ := by simp [orthogonal_ker]
    _ = A.adjoint.range := by rw [ker_adjoint_comp_self, orthogonal_ker]
/-
**LinearMap.range_self_comp_adjoint** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：range_self_comp_adjoint (A : E ->ₗ[𝕜] F) : (A ∘ₗ A.adjoint).range = A.rang
e
参数：A : E ->ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u
_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->ₗ[𝕜] F) : A.adjoint.
adjoint = A
· 使用引理 `LinearMap.range_adjoint_comp_self`：range_adjoint_comp_self (A : E ->ₗ[𝕜]
 F) : (A.adjoint ∘ₗ A).range = A.adjoint.range
-/
lemma range_self_comp_adjoint (A : E →ₗ[𝕜] F) : (A ∘ₗ A.adjoint).range = A.range := by
  simpa using A.adjoint.range_adjoint_comp_self

/-- Part of 7.64(d) in [axler2024]. -/
/-
**LinearMap.finrank_range_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：finrank_range_adjoint (A : E ->ₗ[𝕜] F) : Module.finrank 𝕜 A.adjoint.range 
= Module.finrank 𝕜 A.range
参数：A : E ->ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.finrank_range_add_finrank_ker`：finrank_range_add_finrank_ker [
FiniteDimensional K V] (f : V ->ₗ[K] V₂) : finrank K (LinearMap.range f) + finra
nk K (LinearMap.ker f) = finr…
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.finrank_add_finrank_orthogonal`：finrank_add_finrank_orthogonal
 [FiniteDimensional 𝕜 E] (K : Submodule 𝕜 E) : finrank 𝕜 K + finrank 𝕜 Kᗮ = finr
ank 𝕜 E
· 使用引理 `LinearMap.orthogonal_ker`：orthogonal_ker (A : E ->ₗ[𝕜] F) : A.kerᗮ = A.a
djoint.range
· 使用定理 `LinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->ₗ[𝕜] F) : A.adjoint.
adjoint = A
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b

--- 原说明 ---
Part of 7.64(d) in [axler2024].
-/
theorem finrank_range_adjoint (A : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 A.adjoint.range = Module.finrank 𝕜 A.range := calc
  _ = Module.finrank 𝕜 F - Module.finrank 𝕜 A.adjoint.ker := by
    simp [← A.adjoint.finrank_range_add_finrank_ker]
  _ = _ := by rw [← A.adjoint.ker.finrank_add_finrank_orthogonal,
    orthogonal_ker, adjoint_adjoint]; simp

/-- The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y⟫ = ⟪x, B y⟫`
for all basis vectors `x` and `y`. -/
/-
**LinearMap.eq_adjoint_iff_basis** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eq_adjoint_iff_basis {ι₁ : Type*} {ι₂ : Type*} (b₁ : Basis ι₁ 𝕜 E) (b₂ : B
asis ι₂ 𝕜 F) (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E) : A = B.adjoint ↔ forall (i₁ : ι₁
) (i₂ : ι₂), ⟪A (b₁ i₁), b₂ i₂⟫ = ⟪b₁ i₁, B (b₂ i₂)⟫
参数：b₁ : Basis ι₁ 𝕜 E；b₂ : Basis ι₂ 𝕜 F；A : E ->ₗ[𝕜] F；B : F ->ₗ[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->ₗ[𝕜] F) (x : E
) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `InnerProductSpace.ext_inner_right_basis`：ext_inner_right_basis {ι : Type
*} {x y : E} (b : Basis ι 𝕜 E) (h : forall i : ι, ⟪x, b i⟫ = ⟪y, b i⟫) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The adjoint is unique: a map `A` is the adjoint of `B` iff it satisfies `⟪A x, y
⟫ = ⟪x, B y⟫`
for all basis vectors `x` and `y`.
-/
theorem eq_adjoint_iff_basis {ι₁ : Type*} {ι₂ : Type*} (b₁ : Basis ι₁ 𝕜 E) (b₂ : Basis ι₂ 𝕜 F)
    (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ (i₁ : ι₁) (i₂ : ι₂), ⟪A (b₁ i₁), b₂ i₂⟫ = ⟪b₁ i₁, B (b₂ i₂)⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  refine Basis.ext b₁ fun i₁ => ?_
  exact ext_inner_right_basis b₂ fun i₂ => by simp only [adjoint_inner_left, h i₁ i₂]
/-
**LinearMap.eq_adjoint_iff_basis_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eq_adjoint_iff_basis_left {ι : Type*} (b : Basis ι 𝕜 E) (A : E ->ₗ[𝕜] F) (
B : F ->ₗ[𝕜] E) : A = B.adjoint ↔ forall i y, ⟪A (b i), y⟫ = ⟪b i, B y⟫
参数：b : Basis ι 𝕜 E；A : E ->ₗ[𝕜] F；B : F ->ₗ[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->ₗ[𝕜] F) (x : E
) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `ext_inner_right`：ext_inner_right {x y : E} (h : forall v, ⟪x, v⟫ = ⟪y, v
⟫) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_adjoint_iff_basis_left {ι : Type*} (b : Basis ι 𝕜 E) (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ i y, ⟪A (b i), y⟫ = ⟪b i, B y⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => Basis.ext b fun i => ?_⟩
  exact ext_inner_right 𝕜 fun y => by simp only [h i, adjoint_inner_left]
/-
**LinearMap.eq_adjoint_iff_basis_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eq_adjoint_iff_basis_right {ι : Type*} (b : Basis ι 𝕜 F) (A : E ->ₗ[𝕜] F) 
(B : F ->ₗ[𝕜] E) : A = B.adjoint ↔ forall i x, ⟪A x, b i⟫ = ⟪x, B (b i)⟫
参数：b : Basis ι 𝕜 F；A : E ->ₗ[𝕜] F；B : F ->ₗ[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->ₗ[𝕜] F) (x : E
) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `InnerProductSpace.ext_inner_right_basis`：ext_inner_right_basis {ι : Type
*} {x y : E} (b : Basis ι 𝕜 E) (h : forall i : ι, ⟪x, b i⟫ = ⟪y, b i⟫) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_adjoint_iff_basis_right {ι : Type*} (b : Basis ι 𝕜 F) (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) :
    A = B.adjoint ↔ ∀ i x, ⟪A x, b i⟫ = ⟪x, B (b i)⟫ := by
  refine ⟨fun h x y => by rw [h, adjoint_inner_left], fun h => ?_⟩
  ext x
  exact ext_inner_right_basis b fun i => by simp only [h i, adjoint_inner_left]

/-- `E →ₗ[𝕜] E` is a star algebra with the adjoint as the star operation. -/
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`E →ₗ[𝕜] E` is a star algebra with the adjoint as the star operation.
-/
instance : Star (E →ₗ[𝕜] E) :=
  ⟨adjoint⟩
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvolutiveStar (E →ₗ[𝕜] E) :=
  ⟨adjoint_adjoint⟩
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarMul (E →ₗ[𝕜] E) :=
  ⟨adjoint_comp⟩
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarRing (E →ₗ[𝕜] E) :=
  ⟨map_add adjoint⟩
/-
**LinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarModule 𝕜 (E →ₗ[𝕜] E) :=
  ⟨map_smulₛₗ adjoint⟩
/-
**LinearMap.star_eq_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：star_eq_adjoint (A : E ->ₗ[𝕜] E) : star A = A.adjoint
参数：A : E ->ₗ[𝕜] E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_eq_adjoint (A : E →ₗ[𝕜] E) : star A = A.adjoint :=
  rfl

/-- A continuous linear operator is self-adjoint iff it is equal to its adjoint. -/
/-
**LinearMap.isSelfAdjoint_iff'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isSelfAdjoint_iff' {A : E ->ₗ[𝕜] E} : IsSelfAdjoint A ↔ A.adjoint = A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A continuous linear operator is self-adjoint iff it is equal to its adjoint.
-/
theorem isSelfAdjoint_iff' {A : E →ₗ[𝕜] E} : IsSelfAdjoint A ↔ A.adjoint = A :=
  Iff.rfl
/-
**LinearMap.isSymmetric_iff_isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isSymmetric_iff_isSelfAdjoint (A : E ->ₗ[𝕜] E) : IsSymmetric A ↔ IsSelfAdj
oint A
参数：A : E ->ₗ[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.isSelfAdjoint_iff'`：isSelfAdjoint_iff' {A : E ->ₗ[𝕜] E} : IsSe
lfAdjoint A ↔ A.adjoint = A
· 使用定理 `LinearMap.IsSymmetric.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   (T 
: E →ₗ[𝕜] E), T.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.eq_adjoint_iff`：eq_adjoint_iff (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] 
E) : A = B.adjoint ↔ forall x y, ⟪A x, y⟫ = ⟪x, B y⟫
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem isSymmetric_iff_isSelfAdjoint (A : E →ₗ[𝕜] E) : IsSymmetric A ↔ IsSelfAdjoint A := by
  rw [isSelfAdjoint_iff', IsSymmetric, ← LinearMap.eq_adjoint_iff]
  exact eq_comm
/-
**LinearMap.id_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : FiniteDimensional 𝕜 E], Lin
earMap.id ∈ unitary (E →ₗ[𝕜] E)
参数：E →ₗ[𝕜] E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
@[simp] lemma id_mem_unitary : .id ∈ unitary (E →ₗ[𝕜] E) := one_mem _
/-
**LinearMap.isAdjointPair_inner** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isAdjointPair_inner (A : E ->ₗ[𝕜] F) : IsAdjointPair (innerₛₗ 𝕜 (E
参数：A : E ->ₗ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->ₗ[𝕜] F) (x : E
) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isAdjointPair_inner (A : E →ₗ[𝕜] F) :
    IsAdjointPair (innerₛₗ 𝕜 (E := E)).flip
      (innerₛₗ 𝕜 (E := F)).flip A A.adjoint := by
  intro x y
  simp [adjoint_inner_left]

/-! This next batch of lemmas is based on theorems like `LinearMap.IsPositive.conj_adjoint`, which
are in a downstream file but historically existed before these lemmas. We can't put them in the file
where `LinearMap.IsSymmetric` is defined because they depend on the adjoint. -/

@[aesop safe apply]
/-
**LinearMap.IsSymmetric.conj_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymm
etric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedAddCommGroup F] [inst_3 : InnerProductS
pace 𝕜 E] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : FiniteDimensional 𝕜 E] [i
nst_6 : FiniteDimensional 𝕜 F] {T : E →ₗ[𝕜] E},   T.IsSymmetric → ∀ (S : E →ₗ[𝕜]
 F), (S ∘ₗ T ∘ₗ LinearMap.adjoint S).IsSymmetric
参数：S : E →ₗ[𝕜] F；S ∘ₗ T ∘ₗ LinearMap.adjoint S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.adjoint_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [
inst_3 : FiniteDimensi…
· 使用定理 `LinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->ₗ[𝕜] F) : A.adjoint.
adjoint = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This next batch of lemmas is based on theorems like `LinearMap.IsPositive.conj_a
djoint`, which
are in a downstream file but historically existed before these lemmas. We can't 
put them in the file
where `LinearMap.IsSymmetric` is defined because they depend on the adjoint.
-/
theorem IsSymmetric.conj_adjoint {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (S : E →ₗ[𝕜] F) :
    (S ∘ₗ T ∘ₗ S.adjoint).IsSymmetric := fun _ _ ↦ by simp [← adjoint_inner_right, hT]
/-
**LinearMap.isSymmetric_self_comp_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isSymmetric_self_comp_adjoint (T : E ->ₗ[𝕜] F) : (T ∘ₗ adjoint T).IsSymmet
ric
参数：T : E ->ₗ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.conj_adjoint`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedA
ddCommGroup F] [inst_3 :…
· 使用定理 `LinearMap.IsSymmetric.id`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike
 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E],   Line
arMap.id.IsSym…
-/
theorem isSymmetric_self_comp_adjoint (T : E →ₗ[𝕜] F) : (T ∘ₗ adjoint T).IsSymmetric := by
  simpa using LinearMap.IsSymmetric.id.conj_adjoint T

@[aesop safe apply]
/-
**LinearMap.IsSymmetric.adjoint_conj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymm
etric`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : NormedAddCommGroup F] [inst_3 : InnerProductS
pace 𝕜 E] [inst_4 : InnerProductSpace 𝕜 F]   [inst_5 : FiniteDimensional 𝕜 E] [i
nst_6 : FiniteDimensional 𝕜 F] {T : E →ₗ[𝕜] E},   T.IsSymmetric → ∀ (S : F →ₗ[𝕜]
 E), (LinearMap.adjoint S ∘ₗ T ∘ₗ S).IsSymmetric
参数：S : F →ₗ[𝕜] E；LinearMap.adjoint S ∘ₗ T ∘ₗ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->ₗ[𝕜] F) : A.adjoint.
adjoint = A
· 使用定理 `LinearMap.IsSymmetric.conj_adjoint`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedA
ddCommGroup F] [inst_3 :…
-/
theorem IsSymmetric.adjoint_conj {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (S : F →ₗ[𝕜] E) :
    (S.adjoint ∘ₗ T ∘ₗ S).IsSymmetric := by
  simpa using hT.conj_adjoint S.adjoint

/-- Like `LinearMap.isSymmetric_adjoint_mul_self` but domain and range can be different -/
/-
**LinearMap.isSymmetric_adjoint_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isSymmetric_adjoint_comp_self (T : E ->ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmet
ric
参数：T : E ->ₗ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.adjoint_conj`：∀ {𝕜 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedA
ddCommGroup F] [inst_3 :…
· 使用定理 `LinearMap.IsSymmetric.id`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike
 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E],   Line
arMap.id.IsSym…

--- 原说明 ---
Like `LinearMap.isSymmetric_adjoint_mul_self` but domain and range can be differ
ent
-/
theorem isSymmetric_adjoint_comp_self (T : E →ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric := by
  simpa using LinearMap.IsSymmetric.id.adjoint_conj T

/-- The Gram operator T†T is symmetric. See `LinearMap.isSymmetric_adjoint_comp_self` for a version
where the domain and codomain are distinct. -/
/-
**LinearMap.isSymmetric_adjoint_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isSymmetric_adjoint_mul_self (T : E ->ₗ[𝕜] E) : IsSymmetric (T.adjoint * T
)
参数：T : E ->ₗ[𝕜] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->ₗ[𝕜] F) (x : E
) (y : F) : ⟪adjoint A y, x⟫ = ⟪y, A x⟫
· 使用定理 `LinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->ₗ[𝕜] F) (x :
 E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Gram operator T†T is symmetric. See `LinearMap.isSymmetric_adjoint_comp_self
` for a version
where the domain and codomain are distinct.
-/
theorem isSymmetric_adjoint_mul_self (T : E →ₗ[𝕜] E) : IsSymmetric (T.adjoint * T) := by
  intro x y
  simp [adjoint_inner_left, adjoint_inner_right]

/-- The Gram operator T†T is a positive operator. -/
/-
**LinearMap.re_inner_adjoint_mul_self_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p`。
形式化陈述：re_inner_adjoint_mul_self_nonneg (T : E ->ₗ[𝕜] E) (x : E) : 0 <= re ⟪x, (T
.adjoint * T) x⟫
参数：T : E ->ₗ[𝕜] E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->ₗ[𝕜] F) (x :
 E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
The Gram operator T†T is a positive operator.
-/
theorem re_inner_adjoint_mul_self_nonneg (T : E →ₗ[𝕜] E) (x : E) :
    0 ≤ re ⟪x, (T.adjoint * T) x⟫ := by
  simp only [Module.End.mul_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact sq_nonneg _

@[simp]
/-
**LinearMap.im_inner_adjoint_mul_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
形式化陈述：im_inner_adjoint_mul_self_eq_zero (T : E ->ₗ[𝕜] E) (x : E) : im ⟪x, T.adjo
int (T x)⟫ = 0
参数：T : E ->ₗ[𝕜] E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.adjoint_inner_right`：adjoint_inner_right (A : E ->ₗ[𝕜] F) (x :
 E) (y : F) : ⟪x, adjoint A y⟫ = ⟪A x, y⟫
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
-/
theorem im_inner_adjoint_mul_self_eq_zero (T : E →ₗ[𝕜] E) (x : E) :
    im ⟪x, T.adjoint (T x)⟫ = 0 := by
  simp only [adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast
/-
**LinearMap.isSelfAdjoint_toContinuousLinearMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap`。
形式化陈述：isSelfAdjoint_toContinuousLinearMap_iff (T : E ->ₗ[𝕜] E) : have
参数：T : E ->ₗ[𝕜] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSelfAdjoint_toContinuousLinearMap_iff (T : E →ₗ[𝕜] E) :
    have := FiniteDimensional.complete 𝕜 E
    IsSelfAdjoint T.toContinuousLinearMap ↔ IsSelfAdjoint T := by
  simp [IsSelfAdjoint, star, adjoint,
    ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap]
/-
**LinearMap._root_.ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff** 是 Mathlib
 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff (T : E →L[𝕜] E) :
    have := FiniteDimensional.complete 𝕜 E
    IsSelfAdjoint T.toLinearMap ↔ IsSelfAdjoint T := by
  simp only [IsSelfAdjoint, star, adjoint, LinearEquiv.trans_apply,
    coe_toContinuousLinearMap_symm,
    ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap]
  rfl
/-
**LinearMap.isStarProjection_toContinuousLinearMap_iff** 是 Mathlib 中的一个定理，位于命名空间
 `LinearMap`。
形式化陈述：isStarProjection_toContinuousLinearMap_iff {T : E ->ₗ[𝕜] E} : have
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isStarProjection_toContinuousLinearMap_iff {T : E →ₗ[𝕜] E} :
    have := FiniteDimensional.complete 𝕜 E
    IsStarProjection (toContinuousLinearMap T) ↔ IsStarProjection T := by
  simp [isStarProjection_iff, isSelfAdjoint_toContinuousLinearMap_iff,
    ← ContinuousLinearMap.isIdempotentElem_toLinearMap_iff]
/-
**LinearMap.isStarProjection_iff_isSymmetricProjection** 是 Mathlib 中的一个定理，位于命名空间
 `LinearMap`。
形式化陈述：isStarProjection_iff_isSymmetricProjection {T : E ->ₗ[𝕜] E} : IsStarProjec
tion T ↔ T.IsSymmetricProjection
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isStarProjection_iff_isSymmetricProjection {T : E →ₗ[𝕜] E} :
    IsStarProjection T ↔ T.IsSymmetricProjection := by
  simp [← isStarProjection_toContinuousLinearMap_iff,
    ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]

open LinearMap in
/-- Star projection operators are equal iff their range are. -/
/-
**LinearMap.IsStarProjection.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsStar
Projection`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup E] [inst_2 : InnerProductSpace 𝕜 E]   [inst_3 : FiniteDimensional 𝕜 E] {S T
 : E →ₗ[𝕜] E},   IsStarProjection S → IsStarProjection T → (S = T ↔ S.range = T.
range)
参数：S = T ↔ S.range = T.range。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `ContinuousLinearMap.IsStarProjection.ext_iff`：∀ {𝕜 : Type u_1} {E : Type
 u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSp
ace 𝕜 E]   {T : E →L[𝕜] E} [inst_3…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.isStarProjection_toContinuousLinearMap_iff`：isStarProjection_t
oContinuousLinearMap_iff {T : E ->ₗ[𝕜] E} : have

--- 原说明 ---
Star projection operators are equal iff their range are.
-/
theorem IsStarProjection.ext_iff {S T : E →ₗ[𝕜] E}
    (hS : IsStarProjection S) (hT : IsStarProjection T) :
    S = T ↔ LinearMap.range S = LinearMap.range T := by
  have := FiniteDimensional.complete 𝕜 E
  simpa using ContinuousLinearMap.IsStarProjection.ext_iff
    (S.isStarProjection_toContinuousLinearMap_iff.mpr hS)
    (T.isStarProjection_toContinuousLinearMap_iff.mpr hT)

alias ⟨_, IsStarProjection.ext⟩ := IsStarProjection.ext_iff
/-
**LinearMap.adjoint_inner** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjoint_innerₛₗ_apply (x : E) :
    adjoint (innerₛₗ 𝕜 x) = toSpanSingleton 𝕜 E x :=
  have := FiniteDimensional.complete 𝕜 E
  ext fun _ ↦ congr($(ContinuousLinearMap.adjoint_innerSL_apply x) _)
/-
**LinearMap.adjoint_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：adjoint_toSpanSingleton (x : E) : adjoint (toSpanSingleton 𝕜 E x) = innerₛ
ₗ 𝕜 x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.adjoint_adjoint`：adjoint_adjoint (A : E ->ₗ[𝕜] F) : A.adjoint.
adjoint = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjoint_toSpanSingleton (x : E) :
    adjoint (toSpanSingleton 𝕜 E x) = innerₛₗ 𝕜 x := by
  simp [← adjoint_innerₛₗ_apply]

open Module End in
/-- The linear map version of `ContinuousLinearMap.mem_invtSubmodule_adjoint_iff`
in a finite-dimensional space. -/
/-
**LinearMap._root_.Module.End.mem_invtSubmodule_adjoint_iff** 是 Mathlib 中的一个定理，位
于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map version of `ContinuousLinearMap.mem_invtSubmodule_adjoint_iff`
in a finite-dimensional space.
-/
theorem _root_.Module.End.mem_invtSubmodule_adjoint_iff {T : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} :
    U ∈ invtSubmodule T.adjoint ↔ Uᗮ ∈ invtSubmodule T :=
  have := FiniteDimensional.complete 𝕜 E
  ContinuousLinearMap.mem_invtSubmodule_adjoint_iff

end LinearMap

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

section linearIsometryEquiv
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

namespace ContinuousLinearMap

/-
**ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearMap`。
形式化陈述：inner_map_map_iff_adjoint_comp_self (u : H ->L[𝕜] K) : (forall x y : H, ⟪u
 x, u y⟫_𝕜 = ⟪x, y⟫_𝕜) ↔ adjoint u ∘L u = 1
参数：u : H ->L[𝕜] K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ext_inner_right`：ext_inner_right {x y : E} (h : forall v, ⟪x, v⟫ = ⟪y, v
⟫) : x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->L[𝕜]
 F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem inner_map_map_iff_adjoint_comp_self (u : H →L[𝕜] K) :
    (∀ x y : H, ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜) ↔ adjoint u ∘L u = 1 := by
  refine ⟨fun h ↦ ext fun x ↦ ?_, fun h ↦ ?_⟩
  · refine ext_inner_right 𝕜 fun y ↦ ?_
    simpa [star_eq_adjoint, adjoint_inner_left] using h x y
  · simp [← adjoint_inner_left, ← comp_apply, h]
/-
**ContinuousLinearMap.norm_map_iff_adjoint_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：norm_map_iff_adjoint_comp_self (u : H ->L[𝕜] K) : (forall x : H, ‖u x‖ = ‖
x‖) ↔ adjoint u ∘L u = 1
参数：u : H ->L[𝕜] K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.norm_map_iff_inner_map_map`：LinearMap.norm_map_iff_inner_map_m
ap {F : Type*} [FunLike F E E'] [LinearMapClass F 𝕜 E E'] (f : F) : (forall x, ‖
f x‖ = ‖x‖) ↔ (forall x y,…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self`：inner_map_map_i
ff_adjoint_comp_self (u : H ->L[𝕜] K) : (forall x y : H, ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜
) ↔ adjoint u ∘L u = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_map_iff_adjoint_comp_self (u : H →L[𝕜] K) :
    (∀ x : H, ‖u x‖ = ‖x‖) ↔ adjoint u ∘L u = 1 := by
  rw [LinearMap.norm_map_iff_inner_map_map u, u.inner_map_map_iff_adjoint_comp_self]
/-
**ContinuousLinearMap.isometry_iff_adjoint_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：isometry_iff_adjoint_comp_self (u : H ->L[𝕜] K) : Isometry u ↔ adjoint u ∘
L u = 1
参数：u : H ->L[𝕜] K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHomClass.isometry_iff_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F 
: Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [ins
t_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.norm_map_iff_adjoint_comp_self`：norm_map_iff_adjoint
_comp_self (u : H ->L[𝕜] K) : (forall x : H, ‖u x‖ = ‖x‖) ↔ adjoint u ∘L u = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isometry_iff_adjoint_comp_self (u : H →L[𝕜] K) :
    Isometry u ↔ adjoint u ∘L u = 1 := by
  rw [AddMonoidHomClass.isometry_iff_norm, norm_map_iff_adjoint_comp_self]

@[simp]
/-
**ContinuousLinearMap._root_.LinearIsometryEquiv.adjoint_eq_symm** 是 Mathlib 中的一
个引理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearIsometryEquiv.adjoint_eq_symm (e : H ≃ₗᵢ[𝕜] K) :
    adjoint (e : H →L[𝕜] K) = e.symm :=
  calc
    _ = adjoint (e : H →L[𝕜] K) ∘L e ∘L (e.symm : K →L[𝕜] H) := by simp
    _ = e.symm := by
      rw [← comp_assoc, norm_map_iff_adjoint_comp_self _ |>.mp e.norm_map, one_def, id_comp]

omit [CompleteSpace H] [CompleteSpace K] in
/-
**ContinuousLinearMap._root_.LinearIsometryEquiv.adjoint_toLinearMap_eq_symm** 是
 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometryEquiv.adjoint_toLinearMap_eq_symm
    [FiniteDimensional 𝕜 H] [FiniteDimensional 𝕜 K] (e : H ≃ₗᵢ[𝕜] K) :
    LinearMap.adjoint e.toLinearMap = e.symm.toLinearMap :=
  have := FiniteDimensional.complete 𝕜 H
  have := FiniteDimensional.complete 𝕜 K
  congr($e.adjoint_eq_symm)

@[simp]
/-
**ContinuousLinearMap._root_.LinearIsometryEquiv.star_eq_symm** 是 Mathlib 中的一个引理
，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearIsometryEquiv.star_eq_symm (e : H ≃ₗᵢ[𝕜] H) :
    star (e : H →L[𝕜] H) = e.symm :=
  e.adjoint_eq_symm
/-
**ContinuousLinearMap.norm_map_of_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：norm_map_of_mem_unitary {u : H ->L[𝕜] H} (hu : u in unitary (H ->L[𝕜] H)) 
(x : H) : ‖u x‖ = ‖x‖
参数：hu : u in unitary (H ->L[𝕜] H)；x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Unitary.star_mul_self_of_mem`：star_mul_self_of_mem {U : R} (hU : U in un
itary R) : star U * U = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.norm_map_iff_adjoint_comp_self`：norm_map_iff_adjoint
_comp_self (u : H ->L[𝕜] K) : (forall x : H, ‖u x‖ = ‖x‖) ↔ adjoint u ∘L u = 1
-/
theorem norm_map_of_mem_unitary {u : H →L[𝕜] H} (hu : u ∈ unitary (H →L[𝕜] H)) (x : H) :
    ‖u x‖ = ‖x‖ :=
  -- Elaborates faster with this broken out https://github.com/leanprover-community/mathlib4/issues/11299
  have := Unitary.star_mul_self_of_mem hu
  u.norm_map_iff_adjoint_comp_self.mpr this x
/-
**ContinuousLinearMap.inner_map_map_of_mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：inner_map_map_of_mem_unitary {u : H ->L[𝕜] H} (hu : u in unitary (H ->L[𝕜]
 H)) (x y : H) : ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜
参数：hu : u in unitary (H ->L[𝕜] H)；x y : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Unitary.star_mul_self_of_mem`：star_mul_self_of_mem {U : R} (hU : U in un
itary R) : star U * U = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self`：inner_map_map_i
ff_adjoint_comp_self (u : H ->L[𝕜] K) : (forall x y : H, ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜
) ↔ adjoint u ∘L u = 1
-/
theorem inner_map_map_of_mem_unitary {u : H →L[𝕜] H} (hu : u ∈ unitary (H →L[𝕜] H)) (x y : H) :
    ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  -- Elaborates faster with this broken out https://github.com/leanprover-community/mathlib4/issues/11299
  have := Unitary.star_mul_self_of_mem hu
  u.inner_map_map_iff_adjoint_comp_self.mpr this x y

end ContinuousLinearMap

namespace LinearIsometryEquiv

open ContinuousLinearMap ContinuousLinearEquiv in
/-- An isometric linear equivalence of two Hilbert spaces induces an equivalence of
⋆-algebras of their endomorphisms.

When `H = K`, this is exactly `Unitary.conjStarAlgAut`
(see `Unitary.conjStarAlgEquiv_unitaryLinearIsometryEquiv` and
`Unitary.conjStarAlgAut_symm_unitaryLinearIsometryEquiv`). -/
/-
**LinearIsometryEquiv.conjStarAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometry
Equiv`。
形式化陈述：conjStarAlgEquiv (e : H ≃ₗᵢ[𝕜] K) : (H ->L[𝕜] H) ≃⋆ₐ[𝕜] (K ->L[𝕜] K)
参数：e : H ≃ₗᵢ[𝕜] K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometric linear equivalence of two Hilbert spaces induces an equivalence of
⋆-algebras of their endomorphisms.

When `H = K`, this is exactly `Unitary.conjStarAlgAut`
(see `Unitary.conjStarAlgEquiv_unitaryLinearIsometryEquiv` and
`Unitary.conjStarAlgAut_symm_unitaryLinearIsometryEquiv`).
-/
def conjStarAlgEquiv (e : H ≃ₗᵢ[𝕜] K) : (H →L[𝕜] H) ≃⋆ₐ[𝕜] (K →L[𝕜] K) :=
  .ofAlgEquiv e.toContinuousLinearEquiv.conjContinuousAlgEquiv fun x ↦ by
    simp [star_eq_adjoint, conjContinuousAlgEquiv_apply, ← toContinuousLinearEquiv_symm, comp_assoc]
/-
**LinearIsometryEquiv.conjStarAlgEquiv_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearIsometryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {H : Type u_5} [inst_1 : NormedAddCommG
roup H] [inst_2 : InnerProductSpace 𝕜 H]   [inst_3 : CompleteSpace H] {K : Type 
u_6} [inst_4 : NormedAddCommGroup K] [inst_5 : InnerProductSpace 𝕜 K]   [inst_6 
: CompleteSpace K] (e : H ≃ₗᵢ[𝕜] K) (x : H →L[𝕜] H) (y : K), (e.conjStarAlgEquiv
 x) y = e (x (e.symm y))
参数：e : H ≃ₗᵢ[𝕜] K；x : H →L[𝕜] H；y : K；e.conjStarAlgEquiv x；x (e.symm y)。
黑盒证明引用了以下数学事实（定理与引理）：
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
@[simp] lemma conjStarAlgEquiv_apply_apply (e : H ≃ₗᵢ[𝕜] K) (x : H →L[𝕜] H) (y : K) :
    e.conjStarAlgEquiv x y = e (x (e.symm y)) := rfl
/-
**LinearIsometryEquiv.symm_conjStarAlgEquiv_apply_apply** 是 Mathlib 中的一个定理，位于命名空
间 `LinearIsometryEquiv`。
形式化陈述：symm_conjStarAlgEquiv_apply_apply (e : H ≃ₗᵢ[𝕜] K) (f : K ->L[𝕜] K) (x : H
) : e.conjStarAlgEquiv.symm f x = e.symm (f (e x))
参数：e : H ≃ₗᵢ[𝕜] K；f : K ->L[𝕜] K；x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem symm_conjStarAlgEquiv_apply_apply (e : H ≃ₗᵢ[𝕜] K) (f : K →L[𝕜] K) (x : H) :
    e.conjStarAlgEquiv.symm f x = e.symm (f (e x)) := rfl
/-
**LinearIsometryEquiv.conjStarAlgEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearIs
ometryEquiv`。
形式化陈述：conjStarAlgEquiv_apply (e : H ≃ₗᵢ[𝕜] K) (x : H ->L[𝕜] H) : e.conjStarAlgEq
uiv x = e ∘L x ∘L e.symm
参数：e : H ≃ₗᵢ[𝕜] K；x : H ->L[𝕜] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
lemma conjStarAlgEquiv_apply (e : H ≃ₗᵢ[𝕜] K) (x : H →L[𝕜] H) :
    e.conjStarAlgEquiv x = e ∘L x ∘L e.symm := rfl
/-
**LinearIsometryEquiv.symm_conjStarAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearIso
metryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {H : Type u_5} [inst_1 : NormedAddCommG
roup H] [inst_2 : InnerProductSpace 𝕜 H]   [inst_3 : CompleteSpace H] {K : Type 
u_6} [inst_4 : NormedAddCommGroup K] [inst_5 : InnerProductSpace 𝕜 K]   [inst_6 
: CompleteSpace K] (e : H ≃ₗᵢ[𝕜] K), e.conjStarAlgEquiv.symm = e.symm.conjStarAl
gEquiv
参数：e : H ≃ₗᵢ[𝕜] K。
黑盒证明引用了以下数学事实（定理与引理）：
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
@[simp] lemma symm_conjStarAlgEquiv (e : H ≃ₗᵢ[𝕜] K) :
    e.conjStarAlgEquiv.symm = e.symm.conjStarAlgEquiv := rfl
/-
**LinearIsometryEquiv.conjStarAlgEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearIso
metryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {H : Type u_5} [inst_1 : NormedAddCommG
roup H] [inst_2 : InnerProductSpace 𝕜 H]   [inst_3 : CompleteSpace H], (LinearIs
ometryEquiv.refl 𝕜 H).conjStarAlgEquiv = StarAlgEquiv.refl 𝕜 (H →L[𝕜] H)
参数：LinearIsometryEquiv.refl 𝕜 H；H →L[𝕜] H。
黑盒证明引用了以下数学事实（定理与引理）：
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
@[simp] theorem conjStarAlgEquiv_refl : conjStarAlgEquiv (.refl 𝕜 H) = .refl _ _ := rfl
/-
**LinearIsometryEquiv.conjStarAlgEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearIs
ometryEquiv`。
形式化陈述：conjStarAlgEquiv_trans {G : Type*} [NormedAddCommGroup G] [InnerProductSpa
ce 𝕜 G] [CompleteSpace G] (e : H ≃ₗᵢ[𝕜] K) (f : K ≃ₗᵢ[𝕜] G) : (e.trans f).conjSt
arAlgEquiv = e.conjStarAlgEquiv.trans f.conjStarAlgEquiv
参数：e : H ≃ₗᵢ[𝕜] K；f : K ≃ₗᵢ[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem conjStarAlgEquiv_trans {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [CompleteSpace G] (e : H ≃ₗᵢ[𝕜] K) (f : K ≃ₗᵢ[𝕜] G) :
    (e.trans f).conjStarAlgEquiv = e.conjStarAlgEquiv.trans f.conjStarAlgEquiv := rfl

set_option backward.isDefEq.respectTransparency false in
open ContinuousLinearEquiv ContinuousLinearMap in
/-
**LinearIsometryEquiv.conjStarAlgEquiv_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Linear
IsometryEquiv`。
形式化陈述：conjStarAlgEquiv_ext_iff (f g : H ≃ₗᵢ[𝕜] K) : f.conjStarAlgEquiv = g.conjS
tarAlgEquiv ↔ exists α : unitary 𝕜, f = α • g
参数：f g : H ≃ₗᵢ[𝕜] K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.comp_assoc`：comp_assoc {R₄ : Type*} [Semiring R₄] [M
odule R₄ M₄] {σ₁₄ : R₁ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₃₄ : R₃ ->+* R₄} [RingHomCo
mpTriple σ₁₃ σ₃₄ σ₁₄…
· 使用定理 `Subalgebra.mem_center_iff`：mem_center_iff {a : A} : a in center R A ↔ fo
rall b : A, b * a = a * b
· 使用引理 `Algebra.IsCentral.center_eq_bot`：center_eq_bot : Subalgebra.center K D =
 ⊥
· 使用定理 `Algebra.IsCentral.instContinuousLinearMap`：∀ {R : Type u_1} {V : Type u_
2} [inst : Field R] [inst_1 : AddCommGroup V] [inst_2 : TopologicalSpace R]   [i
nst_3 : TopologicalSpace V] [Is…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instSeparatingDual`：∀ {E : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] [i
nst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   SeparatingDual 𝕜 E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
（共 61 条，此处仅展示前 30 条）
-/
theorem conjStarAlgEquiv_ext_iff (f g : H ≃ₗᵢ[𝕜] K) :
    f.conjStarAlgEquiv = g.conjStarAlgEquiv ↔ ∃ α : unitary 𝕜, f = α • g := by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, LinearIsometryEquiv.ext_iff, conjStarAlgEquiv_apply,
    ← eq_toContinuousLinearMap_symm_comp, ← comp_assoc, toContinuousLinearEquiv_symm,
    eq_comp_toContinuousLinearMap_symm,
    comp_assoc, ← comp_assoc _ (f : H →L[𝕜] K), comp_coe, ← ContinuousLinearMap.mul_def,
    ← Subalgebra.mem_center_iff (R := 𝕜), Algebra.IsCentral.center_eq_bot, ← comp_coe,
    Algebra.mem_bot, Set.mem_range, Algebra.algebraMap_eq_smul_one]
  refine ⟨fun ⟨y, h⟩ ↦ ?_, fun ⟨y, h⟩ ↦ ⟨(y : 𝕜), by ext; simp [h]⟩⟩
  by_cases! hy : y = 0
  · exact ⟨1, fun x ↦ by simp [by simpa [hy] using congr($h x).symm]⟩
  have hfg : (f : H →L[𝕜] K) = y • g := by ext; simpa using congr(g ($h _)).symm
  have hgf : (g : H →L[𝕜] K) = star y • f := by
    ext x
    have := by simpa [map_smulₛₗ, ← ContinuousLinearEquiv.comp_coe, ← toContinuousLinearEquiv_symm,
      ← adjoint_eq_symm, ContinuousLinearMap.one_def] using congr(f (adjoint $h x)).symm
    simpa
  have : (g : H →L[𝕜] K) = (starRingEnd 𝕜 y * y) • g := by
    simp [← smul_smul, ← hfg, ← star_def, ← hgf]
  nth_rw 1 [← one_smul 𝕜 (g : H →L[𝕜] K)] at this
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero, eq_comm] at this
  obtain (this | this) := this
  · exact ⟨⟨y, by simp [Unitary.mem_iff, this, mul_comm y]⟩, fun x ↦ congr($hfg x)⟩
  · exact ⟨1, fun x ↦ by simp [by simpa using congr($this x)]⟩

end LinearIsometryEquiv
end linearIsometryEquiv

namespace Unitary

/-
**Unitary.norm_map** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：norm_map (u : unitary (H ->L[𝕜] H)) (x : H) : ‖(u : H ->L[𝕜] H) x‖ = ‖x‖
参数：u : unitary (H ->L[𝕜] H)；x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.norm_map_of_mem_unitary`：norm_map_of_mem_unitary {u 
: H ->L[𝕜] H} (hu : u in unitary (H ->L[𝕜] H)) (x : H) : ‖u x‖ = ‖x‖
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem norm_map (u : unitary (H →L[𝕜] H)) (x : H) : ‖(u : H →L[𝕜] H) x‖ = ‖x‖ :=
  u.val.norm_map_of_mem_unitary u.property x
/-
**Unitary.inner_map_map** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：inner_map_map (u : unitary (H ->L[𝕜] H)) (x y : H) : ⟪(u : H ->L[𝕜] H) x, 
(u : H ->L[𝕜] H) y⟫_𝕜 = ⟪x, y⟫_𝕜
参数：u : unitary (H ->L[𝕜] H)；x y : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.inner_map_map_of_mem_unitary`：inner_map_map_of_mem_u
nitary {u : H ->L[𝕜] H} (hu : u in unitary (H ->L[𝕜] H)) (x y : H) : ⟪u x, u y⟫_
𝕜 = ⟪x, y⟫_𝕜
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem inner_map_map (u : unitary (H →L[𝕜] H)) (x y : H) :
    ⟪(u : H →L[𝕜] H) x, (u : H →L[𝕜] H) y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  u.val.inner_map_map_of_mem_unitary u.property x y

/-- The unitary elements of continuous linear maps on a Hilbert space coincide with the linear
isometric equivalences on that Hilbert space. -/
/-
**Unitary.linearIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Unitary`。
形式化陈述：linearIsometryEquiv : unitary (H ->L[𝕜] H) ≃* (H ≃ₗᵢ[𝕜] H) where toFun u
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Unitary.norm_map`：norm_map (u : unitary (H ->L[𝕜] H)) (x : H) : ‖(u : H 
->L[𝕜] H) x‖ = ‖x‖

--- 原说明 ---
The unitary elements of continuous linear maps on a Hilbert space coincide with 
the linear
isometric equivalences on that Hilbert space.
-/
noncomputable def linearIsometryEquiv : unitary (H →L[𝕜] H) ≃* (H ≃ₗᵢ[𝕜] H) where
  toFun u :=
    { (u : H →L[𝕜] H) with
      norm_map' := norm_map u
      invFun := ↑(star u)
      left_inv := fun x ↦ congr($(star_mul_self u).val x)
      right_inv := fun x ↦ congr($(mul_star_self u).val x) }
  invFun e :=
    { val := e
      property := by
        let e' : (H →L[𝕜] H)ˣ :=
          { val := (e : H →L[𝕜] H)
            inv := (e.symm : H →L[𝕜] H)
            val_inv := by ext; simp
            inv_val := by ext; simp }
        exact IsUnit.mem_unitary_of_star_mul_self ⟨e', rfl⟩ <|
          (e : H →L[𝕜] H).norm_map_iff_adjoint_comp_self.mp e.norm_map }
  map_mul' u v := by ext; rfl

@[simp]
/-
**Unitary.coe_linearIsometryEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：coe_linearIsometryEquiv_apply (u : unitary (H ->L[𝕜] H)) : linearIsometryE
quiv u = (u : H ->L[𝕜] H)
参数：u : unitary (H ->L[𝕜] H)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma coe_linearIsometryEquiv_apply (u : unitary (H →L[𝕜] H)) :
    linearIsometryEquiv u = (u : H →L[𝕜] H) :=
  rfl

@[simp]
/-
**Unitary.coe_symm_linearIsometryEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`
。
形式化陈述：coe_symm_linearIsometryEquiv_apply (e : H ≃ₗᵢ[𝕜] H) : linearIsometryEquiv.
symm e = (e : H ->L[𝕜] H)
参数：e : H ≃ₗᵢ[𝕜] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma coe_symm_linearIsometryEquiv_apply (e : H ≃ₗᵢ[𝕜] H) :
    linearIsometryEquiv.symm e = (e : H →L[𝕜] H) :=
  rfl
/-
**Unitary.conjStarAlgEquiv_unitaryLinearIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 
`Unitary`。
形式化陈述：conjStarAlgEquiv_unitaryLinearIsometryEquiv (u : unitary (H ->L[𝕜] H)) : (
linearIsometryEquiv u).conjStarAlgEquiv = conjStarAlgAut 𝕜 _ u
参数：u : unitary (H ->L[𝕜] H)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem conjStarAlgEquiv_unitaryLinearIsometryEquiv (u : unitary (H →L[𝕜] H)) :
    (linearIsometryEquiv u).conjStarAlgEquiv = conjStarAlgAut 𝕜 _ u := rfl
/-
**Unitary.conjStarAlgAut_symm_unitaryLinearIsometryEquiv** 是 Mathlib 中的一个定理，位于命名
空间 `Unitary`。
形式化陈述：conjStarAlgAut_symm_unitaryLinearIsometryEquiv (u : H ≃ₗᵢ[𝕜] H) : conjStar
AlgAut 𝕜 (H ->L[𝕜] H) (linearIsometryEquiv.symm u) = u.conjStarAlgEquiv
参数：u : H ≃ₗᵢ[𝕜] H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjStarAlgAut_symm_unitaryLinearIsometryEquiv (u : H ≃ₗᵢ[𝕜] H) :
    conjStarAlgAut 𝕜 (H →L[𝕜] H) (linearIsometryEquiv.symm u) = u.conjStarAlgEquiv := by
  simp [← conjStarAlgEquiv_unitaryLinearIsometryEquiv]

end Unitary

end Unitary

section Matrix

open Matrix LinearMap

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
variable (v₁ : OrthonormalBasis n 𝕜 E) (v₂ : OrthonormalBasis m 𝕜 F)

/-- The linear map associated to the conjugate transpose of a matrix corresponding to two
orthonormal bases is the adjoint of the linear map associated to the matrix. -/
/-
**Matrix.toLin_conjTranspose** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Matrix.toLin_conjTranspose (A : Matrix m n 𝕜) : toLin v₂.toBasis v₁.toBasi
s Aᴴ = adjoint (toLin v₁.toBasis v₂.toBasis A)
参数：A : Matrix m n 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `LinearMap.eq_adjoint_iff_basis`：eq_adjoint_iff_basis {ι₁ : Type*} {ι₂ : 
Type*} (b₁ : Basis ι₁ 𝕜 E) (b₂ : Basis ι₂ 𝕜 F) (A : E ->ₗ[𝕜] F) (B : F ->ₗ[𝕜] E)
 : A = B.adjoint ↔ f…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.toLin_self`：Matrix.toLin_self [Fintype m] (M : Matrix m n R) (i :
 n) : Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The linear map associated to the conjugate transpose of a matrix corresponding t
o two
orthonormal bases is the adjoint of the linear map associated to the matrix.
-/
lemma Matrix.toLin_conjTranspose (A : Matrix m n 𝕜) :
    toLin v₂.toBasis v₁.toBasis Aᴴ = adjoint (toLin v₁.toBasis v₂.toBasis A) := by
  refine eq_adjoint_iff_basis v₂.toBasis v₁.toBasis _ _ |>.mpr fun i j ↦ ?_
  simp_rw [toLin_self]
  simp [sum_inner, inner_smul_left, inner_sum, inner_smul_right,
    orthonormal_iff_ite.mp v₁.orthonormal, orthonormal_iff_ite.mp v₂.orthonormal]

/-- The matrix associated to the adjoint of a linear map corresponding to two orthonormal bases
is the conjugate transpose of the matrix associated to the linear map. -/
/-
**LinearMap.toMatrix_adjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_adjoint (f : E ->ₗ[𝕜] F) : toMatrix v₂.toBasis v₁.toBas
is (adjoint f) = (toMatrix v₁.toBasis v₂.toBasis f)ᴴ
参数：f : E ->ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLin_toMatrix`：Matrix.toLin_toMatrix (f : M₁ ->ₗ[R] M₂) : Matrix
.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f
· 使用引理 `Matrix.toLin_conjTranspose`：Matrix.toLin_conjTranspose (A : Matrix m n 𝕜
) : toLin v₂.toBasis v₁.toBasis Aᴴ = adjoint (toLin v₁.toBasis v₂.toBasis A)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The matrix associated to the adjoint of a linear map corresponding to two orthon
ormal bases
is the conjugate transpose of the matrix associated to the linear map.
-/
lemma LinearMap.toMatrix_adjoint (f : E →ₗ[𝕜] F) :
    toMatrix v₂.toBasis v₁.toBasis (adjoint f) = (toMatrix v₁.toBasis v₂.toBasis f)ᴴ :=
  toLin v₂.toBasis v₁.toBasis |>.injective <| by simp [toLin_conjTranspose]

/-- The star algebra equivalence between the linear endomorphisms of finite-dimensional inner
product space and square matrices induced by the choice of an orthonormal basis. -/
@[simps]
/-
**LinearMap.toMatrixOrthonormal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixOrthonormal : (E ->ₗ[𝕜] E) ≃⋆ₐ[𝕜] Matrix n n 𝕜
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `LinearMap.toMatrix_adjoint`：LinearMap.toMatrix_adjoint (f : E ->ₗ[𝕜] F) 
: toMatrix v₂.toBasis v₁.toBasis (adjoint f) = (toMatrix v₁.toBasis v₂.toBasis f
)ᴴ

--- 原说明 ---
The star algebra equivalence between the linear endomorphisms of finite-dimensio
nal inner
product space and square matrices induced by the choice of an orthonormal basis.
-/
def LinearMap.toMatrixOrthonormal : (E →ₗ[𝕜] E) ≃⋆ₐ[𝕜] Matrix n n 𝕜 :=
  { LinearMap.toMatrix v₁.toBasis v₁.toBasis with
    map_mul' := LinearMap.toMatrix_mul v₁.toBasis
    map_star' := LinearMap.toMatrix_adjoint v₁ v₁ }
/-
**LinearMap.toMatrixOrthonormal_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixOrthonormal_apply_apply (f : E ->ₗ[𝕜] E) (i j : n) : toM
atrixOrthonormal v₁ f i j = ⟪v₁ i, f (v₁ j)⟫_𝕜
参数：f : E ->ₗ[𝕜] E；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `OrthonormalBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
-/
lemma LinearMap.toMatrixOrthonormal_apply_apply (f : E →ₗ[𝕜] E) (i j : n) :
    toMatrixOrthonormal v₁ f i j = ⟪v₁ i, f (v₁ j)⟫_𝕜 :=
  calc
    _ = v₁.repr (f (v₁ j)) i := f.toMatrix_apply ..
    _ = ⟪v₁ i, f (v₁ j)⟫_𝕜 := v₁.repr_apply_apply ..
/-
**LinearMap.toMatrixOrthonormal_reindex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrixOrthonormal_reindex (e : n ≃ m) (f : E ->ₗ[𝕜] E) : toMat
rixOrthonormal (v₁.reindex e) f = (toMatrixOrthonormal v₁ f).reindex e e
参数：e : n ≃ m；f : E ->ₗ[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrthonormalBasis.coe_reindex`：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Type
 u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2
 : InnerProductSpa…
· 使用定理 `OrthonormalBasis.repr_reindex`：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Typ
e u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_
2 : InnerProductSpa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma LinearMap.toMatrixOrthonormal_reindex (e : n ≃ m) (f : E →ₗ[𝕜] E) :
    toMatrixOrthonormal (v₁.reindex e) f = (toMatrixOrthonormal v₁ f).reindex e e :=
  Matrix.ext fun i j =>
    calc toMatrixOrthonormal (v₁.reindex e) f i j
      _ = (v₁.reindex e).repr (f (v₁.reindex e j)) i := f.toMatrix_apply ..
      _ = v₁.repr (f (v₁ (e.symm j))) (e.symm i) := by simp
      _ = toMatrixOrthonormal v₁ f (e.symm i) (e.symm j) := Eq.symm (f.toMatrix_apply ..)

open scoped ComplexConjugate

/-- The adjoint of the linear map associated to a matrix is the linear map associated to the
conjugate transpose of that matrix. -/
/-
**Matrix.toEuclideanLin_conjTranspose_eq_adjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A : Matrix m n 𝕜) : A.conj
Transpose.toEuclideanLin = A.toEuclideanLin.adjoint
参数：A : Matrix m n 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.toLin_conjTranspose`：Matrix.toLin_conjTranspose (A : Matrix m n 𝕜
) : toLin v₂.toBasis v₁.toBasis Aᴴ = adjoint (toLin v₁.toBasis v₂.toBasis A)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The adjoint of the linear map associated to a matrix is the linear map associate
d to the
conjugate transpose of that matrix.
-/
theorem Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A : Matrix m n 𝕜) :
    A.conjTranspose.toEuclideanLin = A.toEuclideanLin.adjoint :=
  A.toLin_conjTranspose (EuclideanSpace.basisFun n 𝕜) (EuclideanSpace.basisFun m 𝕜)

end Matrix

@[simp]
/-
**LinearIsometry.adjoint_comp_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.adjoint_comp_self {E E' : Type*} [NormedAddCommGroup E] [In
nerProductSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup E'] [InnerProductSpac
e 𝕜 E'] [CompleteSpace E'] (f : E ->ₗᵢ[𝕜] E') : f.toContinuousLinearMap.adjoint 
∘L f.toContinuousLinearMap = 1
参数：f : E ->ₗᵢ[𝕜] E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.isometry_iff_adjoint_comp_self`：isometry_iff_adjoint
_comp_self (u : H ->L[𝕜] K) : Isometry u ↔ adjoint u ∘L u = 1
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
-/
theorem LinearIsometry.adjoint_comp_self {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E'] (f : E →ₗᵢ[𝕜] E') :
    f.toContinuousLinearMap.adjoint ∘L f.toContinuousLinearMap = 1 :=
  f.toContinuousLinearMap.isometry_iff_adjoint_comp_self.mp f.isometry

/-- A version of `LinearIsometry.adjoint_comp_self` in terms of `LinearMap.adjoint`. -/
@[simp]
/-
**LinearIsometry.adjoint_comp_self'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.adjoint_comp_self' {E E' : Type*} [NormedAddCommGroup E] [I
nnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [NormedAddCommGroup E'] [InnerProd
uctSpace 𝕜 E'] [FiniteDimensional 𝕜 E'] (f : E ->ₗᵢ[𝕜] E') : f.adjoint ∘ₗ f.toLi
nearMap = LinearMap.id
参数：f : E ->ₗᵢ[𝕜] E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LinearIsometry.adjoint_comp_self`：LinearIsometry.adjoint_comp_self {E E'
 : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [Norm
edAddCommGroup E'] [In…

--- 原说明 ---
A version of `LinearIsometry.adjoint_comp_self` in terms of `LinearMap.adjoint`.
-/
theorem LinearIsometry.adjoint_comp_self' {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E'] (f : E →ₗᵢ[𝕜] E') :
    f.adjoint ∘ₗ f.toLinearMap = LinearMap.id := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 E'
  ext x
  exact congr($(f.adjoint_comp_self) x)
