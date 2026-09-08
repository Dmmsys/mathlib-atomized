/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!

# Partially defined linear operators on Hilbert spaces

We will develop the basics of the theory of unbounded operators on Hilbert spaces.

## Main definitions

* `LinearPMap.IsFormalAdjoint`: An operator `T` is a formal adjoint of `S` if for all `x` in the
  domain of `T` and `y` in the domain of `S`, we have that `⟪T x, y⟫ = ⟪x, S y⟫`.
* `LinearPMap.adjoint`: The adjoint of a map `E →ₗ.[𝕜] F` as a map `F →ₗ.[𝕜] E`.

## Main statements

* `LinearPMap.adjoint_isFormalAdjoint`: The adjoint is a formal adjoint
* `LinearPMap.IsFormalAdjoint.le_adjoint`: Every formal adjoint is contained in the adjoint
* `ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense`: The adjoint on
  `ContinuousLinearMap` and `LinearPMap` coincide.
* `LinearPMap.adjoint_isClosed`: The adjoint is a closed operator.
* `IsSelfAdjoint.isClosed`: Every self-adjoint operator is closed.

## Notation

* For `T : E →ₗ.[𝕜] F` the adjoint can be written as `T†`.
  This notation is localized in `LinearPMap`.

## Implementation notes

We use the junk value pattern to define the adjoint for all `LinearPMap`s. In the case that
`T : E →ₗ.[𝕜] F` is not densely defined the adjoint `T†` is the zero map from `T.adjoint.domain` to
`E`.

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]

## Tags

Unbounded operators, closed operators
-/

@[expose] public section


noncomputable section

open RCLike LinearPMap WithLp

open scoped ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearPMap

/-- An operator `T` is a formal adjoint of `S` if for all `x` in the domain of `T` and `y` in the
domain of `S`, we have that `⟪T x, y⟫ = ⟪x, S y⟫`. -/
/-
**LinearPMap.IsFormalAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：IsFormalAdjoint (T : E ->ₗ.[𝕜] F) (S : F ->ₗ.[𝕜] E) : Prop
参数：T : E ->ₗ.[𝕜] F；S : F ->ₗ.[𝕜] E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An operator `T` is a formal adjoint of `S` if for all `x` in the domain of `T` a
nd `y` in the
domain of `S`, we have that `⟪T x, y⟫ = ⟪x, S y⟫`.
-/
def IsFormalAdjoint (T : E →ₗ.[𝕜] F) (S : F →ₗ.[𝕜] E) : Prop :=
  ∀ (x : T.domain) (y : S.domain), ⟪T x, y⟫ = ⟪(x : E), S y⟫

variable {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}

@[symm]
/-
**LinearPMap.IsFormalAdjoint.symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap.IsFormal
Adjoint`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] {T : E →ₗ.[𝕜] F}   {S : F →ₗ.[𝕜] E}, 
T.IsFormalAdjoint S → S.IsFormalAdjoint T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
-/
protected theorem IsFormalAdjoint.symm (h : T.IsFormalAdjoint S) :
    S.IsFormalAdjoint T := fun y _ => by
  rw [← inner_conj_symm, ← inner_conj_symm (y : F), h]

variable (T)

/-- The domain of the adjoint operator.

This definition is needed to construct the adjoint operator and the preferred version to use is
`T.adjoint.domain` instead of `T.adjointDomain`. -/
/-
**LinearPMap.adjointDomain** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：adjointDomain : Submodule 𝕜 F where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The domain of the adjoint operator.

This definition is needed to construct the adjoint operator and the preferred ve
rsion to use is
`T.adjoint.domain` instead of `T.adjointDomain`.
-/
def adjointDomain : Submodule 𝕜 F where
  carrier := {y | Continuous ((innerₛₗ 𝕜 y).comp T.toFun)}
  zero_mem' := by
    rw [Set.mem_ofPred_eq, LinearMap.map_zero, LinearMap.zero_comp]
    exact continuous_zero
  add_mem' hx hy := by rw [Set.mem_ofPred_eq, LinearMap.map_add] at *; exact hx.add hy
  smul_mem' a x hx := by
    rw [Set.mem_ofPred_eq, LinearMap.map_smulₛₗ] at *
    exact hx.const_smul (conj a)

/-- The operator `fun x ↦ ⟪y, T x⟫` considered as a continuous linear operator
from `T.adjointDomain` to `𝕜`. -/
/-
**LinearPMap.adjointDomainMkCLM** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：adjointDomainMkCLM (y : T.adjointDomain) : StrongDual 𝕜 T.domain
参数：y : T.adjointDomain。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The operator `fun x ↦ ⟪y, T x⟫` considered as a continuous linear operator
from `T.adjointDomain` to `𝕜`.
-/
def adjointDomainMkCLM (y : T.adjointDomain) : StrongDual 𝕜 T.domain :=
  ⟨(innerₛₗ 𝕜 (y : F)).comp T.toFun, y.prop⟩
/-
**LinearPMap.adjointDomainMkCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：adjointDomainMkCLM_apply (y : T.adjointDomain) (x : T.domain) : adjointDom
ainMkCLM T y x = ⟪(y : F), T x⟫
参数：y : T.adjointDomain；x : T.domain。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjointDomainMkCLM_apply (y : T.adjointDomain) (x : T.domain) :
    adjointDomainMkCLM T y x = ⟪(y : F), T x⟫ :=
  rfl

/-- The unique continuous extension of the operator `adjointDomainMkCLM` to `E`. -/
/-
**LinearPMap.adjointDomainMkCLMExtend** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：adjointDomainMkCLMExtend (y : T.adjointDomain) : StrongDual 𝕜 E
参数：y : T.adjointDomain。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K

--- 原说明 ---
The unique continuous extension of the operator `adjointDomainMkCLM` to `E`.
-/
def adjointDomainMkCLMExtend (y : T.adjointDomain) : StrongDual 𝕜 E :=
  (T.adjointDomainMkCLM y).extend (Submodule.subtypeL T.domain)

variable {T}

@[simp]
/-
**LinearPMap.adjointDomainMkCLMExtend_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMa
p`。
形式化陈述：adjointDomainMkCLMExtend_apply (hT : Dense (T.domain : Set E)) (y : T.adjo
intDomain) (x : T.domain) : adjointDomainMkCLMExtend T y (x : E) = ⟪(y : F), T x
⟫
参数：hT : Dense (T.domain : Set E)；y : T.adjointDomain；x : T.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.extend_eq`：extend_eq (h_dense : DenseRange e) (h_e :
 IsUniformInducing e) (x : E) : extend f e (e x) = f x
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `Dense.denseRange_val`：Dense.denseRange_val (h : Dense s) : DenseRange ((
↑) : s -> X)
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `isUniformEmbedding_subtype_val`：isUniformEmbedding_subtype_val {p : α ->
 Prop} : IsUniformEmbedding (Subtype.val : Subtype p -> α)
-/
theorem adjointDomainMkCLMExtend_apply (hT : Dense (T.domain : Set E)) (y : T.adjointDomain)
    (x : T.domain) : adjointDomainMkCLMExtend T y (x : E) = ⟪(y : F), T x⟫ :=
  ContinuousLinearMap.extend_eq _ hT.denseRange_val
    isUniformEmbedding_subtype_val.isUniformInducing _

variable [CompleteSpace E]

variable (hT : Dense (T.domain : Set E))

/-- The adjoint as a linear map from its domain to `E`.

This is an auxiliary definition needed to define the adjoint operator as a `LinearPMap` without
the assumption that `T.domain` is dense. -/
/-
**LinearPMap.adjointAux** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：adjointAux : T.adjointDomain ->ₗ[𝕜] E where toFun y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjoint as a linear map from its domain to `E`.

This is an auxiliary definition needed to define the adjoint operator as a `Line
arPMap` without
the assumption that `T.domain` is dense.
-/
def adjointAux : T.adjointDomain →ₗ[𝕜] E where
  toFun y := (InnerProductSpace.toDual 𝕜 E).symm (adjointDomainMkCLMExtend T y)
  map_add' x y :=
    hT.eq_of_inner_left 𝕜 fun z zin => by
      simp [InnerProductSpace.toDual_symm_apply, inner_add_left,
        adjointDomainMkCLMExtend_apply hT _ ⟨z, zin⟩, inner_add_left]
  map_smul' _ _ :=
    hT.eq_of_inner_left 𝕜 fun z zin => by
      simp [inner_smul_left, RingHom.id_apply,
        InnerProductSpace.toDual_symm_apply, adjointDomainMkCLMExtend_apply hT _ ⟨z, zin⟩]
/-
**LinearPMap.adjointAux_inner** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：adjointAux_inner (y : T.adjointDomain) (x : T.domain) : ⟪adjointAux hT y, 
x⟫ = ⟪(y : F), T x⟫
参数：y : T.adjointDomain；x : T.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
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
· 使用定理 `InnerProductSpace.toDual_symm_apply`：toDual_symm_apply {x : E} {y : Stro
ngDual 𝕜 E} : ⟪(toDual 𝕜 E).symm y, x⟫ = y x
· 使用定理 `LinearPMap.adjointDomainMkCLMExtend_apply`：adjointDomainMkCLMExtend_appl
y (hT : Dense (T.domain : Set E)) (y : T.adjointDomain) (x : T.domain) : adjoint
DomainMkCLMExtend T y (x : E) =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjointAux_inner (y : T.adjointDomain) (x : T.domain) :
    ⟪adjointAux hT y, x⟫ = ⟪(y : F), T x⟫ := by
  simp [adjointAux, hT]
/-
**LinearPMap.adjointAux_unique** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：adjointAux_unique (y : T.adjointDomain) {x₀ : E} (hx₀ : forall x : T.domai
n, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) : adjointAux hT y = x₀
参数：y : T.adjointDomain；hx₀ : forall x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.eq_of_inner_left`：Dense.eq_of_inner_left (hS : Dense S) (h : foral
l v in S, ⟪x, v⟫ = ⟪y, v⟫) : x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearPMap.adjointAux_inner`：adjointAux_inner (y : T.adjointDomain) (x :
 T.domain) : ⟪adjointAux hT y, x⟫ = ⟪(y : F), T x⟫
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem adjointAux_unique (y : T.adjointDomain) {x₀ : E}
    (hx₀ : ∀ x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) : adjointAux hT y = x₀ :=
  hT.eq_of_inner_left 𝕜 fun v vin => (adjointAux_inner hT _ _).trans (hx₀ ⟨v, vin⟩).symm

variable (T)

open scoped Classical in
/-- The adjoint operator as a partially defined linear operator, denoted as `T†`. -/
/-
**LinearPMap.adjoint** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：adjoint : F ->ₗ.[𝕜] E where domain
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjoint operator as a partially defined linear operator, denoted as `T†`.
-/
def adjoint : F →ₗ.[𝕜] E where
  domain := T.adjointDomain
  toFun := if hT : Dense (T.domain : Set E) then adjointAux hT else 0

@[inherit_doc]
scoped postfix:1024 "†" => LinearPMap.adjoint
/-
**LinearPMap.mem_adjoint_domain_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：mem_adjoint_domain_iff (y : F) : y in T†.domain ↔ Continuous ((innerₛₗ 𝕜 y
).comp T.toFun)
参数：y : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_adjoint_domain_iff (y : F) : y ∈ T†.domain ↔ Continuous ((innerₛₗ 𝕜 y).comp T.toFun) :=
  Iff.rfl

variable {T}
/-
**LinearPMap.mem_adjoint_domain_of_exists** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`
。
形式化陈述：mem_adjoint_domain_of_exists (y : F) (h : exists w : E, forall x : T.domai
n, ⟪w, x⟫ = ⟪y, T x⟫) : y in T†.domain
参数：y : F；h : exists w : E, forall x : T.domain, ⟪w, x⟫ = ⟪y, T x⟫。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.mem_adjoint_domain_iff`：mem_adjoint_domain_iff (y : F) : y in
 T†.domain ↔ Continuous ((innerₛₗ 𝕜 y).comp T.toFun)
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem mem_adjoint_domain_of_exists (y : F) (h : ∃ w : E, ∀ x : T.domain, ⟪w, x⟫ = ⟪y, T x⟫) :
    y ∈ T†.domain := by
  obtain ⟨w, hw⟩ := h
  rw [T.mem_adjoint_domain_iff]
  have : Continuous ((innerSL 𝕜 w).comp T.domain.subtypeL) := by fun_prop
  convert this
  exact funext fun x => (hw x).symm

set_option backward.isDefEq.respectTransparency false in
/-
**LinearPMap.adjoint_apply_of_not_dense** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：adjoint_apply_of_not_dense (hT : ¬Dense (T.domain : Set E)) (y : T†.domain
) : T† y = 0
参数：hT : ¬Dense (T.domain : Set E)；y : T†.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjoint_apply_of_not_dense (hT : ¬Dense (T.domain : Set E)) (y : T†.domain) : T† y = 0 := by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, not_false_iff, dif_neg, LinearMap.zero_apply]
/-
**LinearPMap.adjoint_apply_of_dense** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：adjoint_apply_of_dense (y : T†.domain) : T† y = adjointAux hT y
参数：y : T†.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjoint_apply_of_dense (y : T†.domain) : T† y = adjointAux hT y := by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, dif_pos]

include hT in
/-
**LinearPMap.adjoint_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：adjoint_apply_eq (y : T†.domain) {x₀ : E} (hx₀ : forall x : T.domain, ⟪x₀,
 x⟫ = ⟪(y : F), T x⟫) : T† y = x₀
参数：y : T†.domain；hx₀ : forall x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.adjointAux_unique`：adjointAux_unique (y : T.adjointDomain) {x
₀ : E} (hx₀ : forall x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) : adjointAux hT y =
 x₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.adjoint_apply_of_dense`：adjoint_apply_of_dense (y : T†.domain
) : T† y = adjointAux hT y
-/
theorem adjoint_apply_eq (y : T†.domain) {x₀ : E} (hx₀ : ∀ x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) :
    T† y = x₀ :=
  (adjoint_apply_of_dense hT y).symm ▸ adjointAux_unique hT _ hx₀

include hT in
/-- The fundamental property of the adjoint. -/
/-
**LinearPMap.adjoint_isFormalAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：adjoint_isFormalAdjoint : T†.IsFormalAdjoint T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.adjointAux_inner`：adjointAux_inner (y : T.adjointDomain) (x :
 T.domain) : ⟪adjointAux hT y, x⟫ = ⟪(y : F), T x⟫
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.adjoint_apply_of_dense`：adjoint_apply_of_dense (y : T†.domain
) : T† y = adjointAux hT y

--- 原说明 ---
The fundamental property of the adjoint.
-/
theorem adjoint_isFormalAdjoint : T†.IsFormalAdjoint T := fun x =>
  (adjoint_apply_of_dense hT x).symm ▸ adjointAux_inner hT x

include hT in
/-- The adjoint is maximal in the sense that it contains every formal adjoint. -/
/-
**LinearPMap.IsFormalAdjoint.le_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap.Is
FormalAdjoint`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : NormedAddCom
mGroup F] [inst_4 : InnerProductSpace 𝕜 F] {T : E →ₗ.[𝕜] F}   {S : F →ₗ.[𝕜] E} [
inst_5 : CompleteSpace E], Dense ↑T.domain → T.IsFormalAdjoint S → S ≤ T.adjoint
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.mem_adjoint_domain_of_exists`：mem_adjoint_domain_of_exists (y
 : F) (h : exists w : E, forall x : T.domain, ⟪w, x⟫ = ⟪y, T x⟫) : y in T†.domai
n
· 使用定理 `LinearPMap.IsFormalAdjoint.symm`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Ty
pe u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProdu
ctSpace 𝕜 E] [inst_3 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.adjoint_apply_eq`：adjoint_apply_eq (y : T†.domain) {x₀ : E} (
hx₀ : forall x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) : T† y = x₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The adjoint is maximal in the sense that it contains every formal adjoint.
-/
theorem IsFormalAdjoint.le_adjoint (h : T.IsFormalAdjoint S) : S ≤ T† :=
  ⟨-- Trivially, every `x : S.domain` is in `T.adjoint.domain`
  fun x hx =>
    mem_adjoint_domain_of_exists _
      ⟨S ⟨x, hx⟩, h.symm ⟨x, hx⟩⟩,-- Equality on `S.domain` follows from equality
  -- `⟪v, S x⟫ = ⟪v, T.adjoint y⟫` for all `v : T.domain`:
  fun _ _ hxy => (adjoint_apply_eq hT _ fun _ => by rw [h.symm, hxy]).symm⟩

end LinearPMap

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]
variable (A : E →L[𝕜] F) {p : Submodule 𝕜 E}

set_option backward.isDefEq.respectTransparency false in
/-- Restricting `A` to a dense submodule and taking the `LinearPMap.adjoint` is the same
as taking the `ContinuousLinearMap.adjoint` interpreted as a `LinearPMap`. -/
/-
**ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense** 是 Mathlib 中的一个
定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：toPMap_adjoint_eq_adjoint_toPMap_of_dense (hp : Dense (p : Set E)) : (A.to
PMap p).adjoint = A.adjoint.toPMap ⊤
参数：hp : Dense (p : Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.ext`：ext {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain) (h' :
 forall ⦃x : E⦄ ⦃hf : x in f.domain⦄ ⦃hg : x in g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩
) : …
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
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `LinearPMap.adjoint_apply_eq`：adjoint_apply_eq (y : T†.domain) {x₀ : E} (
hx₀ : forall x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) : T† y = x₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.adjoint_inner_left`：adjoint_inner_left (A : E ->L[𝕜]
 F) (x : E) (y : F) : ⟪(A†) y, x⟫ = ⟪y, A x⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Restricting `A` to a dense submodule and taking the `LinearPMap.adjoint` is the 
same
as taking the `ContinuousLinearMap.adjoint` interpreted as a `LinearPMap`.
-/
theorem toPMap_adjoint_eq_adjoint_toPMap_of_dense (hp : Dense (p : Set E)) :
    (A.toPMap p).adjoint = A.adjoint.toPMap ⊤ := by
  ext x y hxy
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, iff_true,
      LinearPMap.mem_adjoint_domain_iff]
    exact ((innerSL 𝕜 x).comp <| A.comp <| Submodule.subtypeL _).cont
  refine LinearPMap.adjoint_apply_eq hp _ fun v => ?_
  simp only [adjoint_inner_left, LinearMap.toPMap_apply, coe_coe]

end ContinuousLinearMap

section Star

namespace LinearPMap

variable [CompleteSpace E]

/-
**LinearPMap.instStar** 是 Mathlib 中的一个实例，位于命名空间 `LinearPMap`。
形式化陈述：instStar : Star (E ->ₗ.[𝕜] E) where star
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStar : Star (E →ₗ.[𝕜] E) where
  star := fun A ↦ A.adjoint

variable {A : E →ₗ.[𝕜] E}
/-
**LinearPMap.isSelfAdjoint_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：isSelfAdjoint_def : IsSelfAdjoint A ↔ A† = A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isSelfAdjoint_def : IsSelfAdjoint A ↔ A† = A := Iff.rfl

/-- Every self-adjoint `LinearPMap` has dense domain.

This is not true by definition since we define the adjoint without the assumption that the
domain is dense, but the choice of the junk value implies that a `LinearPMap` cannot be self-adjoint
if it does not have dense domain. -/
/-
**LinearPMap._root_.IsSelfAdjoint.dense_domain** 是 Mathlib 中的一个定理，位于命名空间 `Linear
PMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every self-adjoint `LinearPMap` has dense domain.

This is not true by definition since we define the adjoint without the assumptio
n that the
domain is dense, but the choice of the junk value implies that a `LinearPMap` ca
nnot be self-adjoint
if it does not have dense domain.
-/
theorem _root_.IsSelfAdjoint.dense_domain (hA : IsSelfAdjoint A) : Dense (A.domain : Set E) := by
  by_contra h
  rw [isSelfAdjoint_def] at hA
  have h' : A.domain = ⊤ := by
    rw [← hA, Submodule.eq_top_iff']
    intro x
    rw [mem_adjoint_domain_iff, ← hA]
    refine (innerSL 𝕜 x).cont.comp ?_
    simp only [adjoint, h]
    exact continuous_const
  simp [h'] at h

end LinearPMap

end Star

/-! ### The graph of the adjoint -/

namespace Submodule

/-- The adjoint of a submodule

Note that the adjoint is taken with respect to the L^2 inner product on `E × F`, which is defined
as `WithLp 2 (E × F)`. -/
protected noncomputable
/-
**Submodule.adjoint** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：adjoint (g : Submodule 𝕜 (E × F)) : Submodule 𝕜 (F × E)
参数：g : Submodule 𝕜 (E × F)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
def adjoint (g : Submodule 𝕜 (E × F)) : Submodule 𝕜 (F × E) :=
  (g.map ((LinearEquiv.skewSwap 𝕜 F E).symm.trans
    (WithLp.linearEquiv 2 𝕜 (F × E)).symm).toLinearMap).orthogonal.map
      (WithLp.linearEquiv 2 𝕜 (F × E) : WithLp 2 (F × E) →ₗ[𝕜] F × E)

@[simp]
/-
**Submodule.mem_adjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_adjoint_iff (g : Submodule 𝕜 (E × F)) (x : F × E) : x in g.adjoint ↔ f
orall a b, (a, b) in g -> inner 𝕜 b x.fst - inner 𝕜 a x.snd = 0
参数：g : Submodule 𝕜 (E × F)；x : F × E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithLp.ofLp_fst`：∀ {p : ENNReal} {α : Type u_2} {β : Type u_3} (x : With
Lp p (α × β)), x.ofLp.1 = x.fst
· 使用定理 `WithLp.ofLp_snd`：∀ {p : ENNReal} {α : Type u_2} {β : Type u_3} (x : With
Lp p (α × β)), x.ofLp.2 = x.snd
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_adjoint_iff (g : Submodule 𝕜 (E × F)) (x : F × E) :
    x ∈ g.adjoint ↔
    ∀ a b, (a, b) ∈ g → inner 𝕜 b x.fst - inner 𝕜 a x.snd = 0 := by
  simp only [Submodule.adjoint, mem_map, mem_orthogonal, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.skewSwap_symm_apply, coe_symm_linearEquiv, Prod.exists,
    prod_inner_apply, ofLp_fst, ofLp_snd, forall_exists_index, and_imp, coe_linearEquiv]
  constructor
  · rintro ⟨y, h1, h2⟩ a b hab
    rw [← h2, WithLp.ofLp_fst, WithLp.ofLp_snd]
    specialize h1 (toLp 2 (b, -a)) a b hab rfl
    dsimp at h1
    simp only [inner_neg_left, ← sub_eq_add_neg] at h1
    exact h1
  · intro h
    refine ⟨toLp 2 x, ?_, rfl⟩
    intro u a b hab hu
    simp [← hu, ← sub_eq_add_neg, h a b hab]

variable {T : E →ₗ.[𝕜] F} [CompleteSpace E]
/-
**Submodule._root_.LinearPMap.adjoint_graph_eq_graph_adjoint** 是 Mathlib 中的一个定理，
位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearPMap.adjoint_graph_eq_graph_adjoint (hT : Dense (T.domain : Set E)) :
    T†.graph = T.graph.adjoint := by
  ext x
  simp only [mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, mem_adjoint_iff,
    forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨hx, h⟩ a ha
    rw [← h, (adjoint_isFormalAdjoint hT).symm ⟨a, ha⟩ ⟨x.fst, hx⟩, sub_self]
  · intro h
    simp_rw [sub_eq_zero] at h
    have hx : x.fst ∈ T†.domain := by
      apply mem_adjoint_domain_of_exists
      use x.snd
      rintro ⟨a, ha⟩
      rw [← inner_conj_symm, ← h a ha, inner_conj_symm]
    use hx
    apply hT.eq_of_inner_right 𝕜
    rintro a ha
    rw [← h a ha, (adjoint_isFormalAdjoint hT).symm ⟨a, ha⟩ ⟨x.fst, hx⟩]

@[simp]
/-
**Submodule._root_.LinearPMap.graph_adjoint_toLinearPMap_eq_adjoint** 是 Mathlib 
中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearPMap.graph_adjoint_toLinearPMap_eq_adjoint (hT : Dense (T.domain : Set E)) :
    T.graph.adjoint.toLinearPMap = T† := by
  apply eq_of_eq_graph
  rw [adjoint_graph_eq_graph_adjoint hT]
  apply Submodule.toLinearPMap_graph_eq
  intro x hx hx'
  simp only [mem_adjoint_iff, mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, hx',
    inner_zero_right, zero_sub, neg_eq_zero, forall_exists_index, forall_apply_eq_imp_iff] at hx
  apply hT.eq_zero_of_inner_right 𝕜
  exact fun a ha ↦ hx a ha

end Submodule

/-! ### Closedness -/

namespace LinearPMap

variable {T : E →ₗ.[𝕜] F} [CompleteSpace E]

/-
**LinearPMap.adjoint_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：adjoint_isClosed (hT : Dense (T.domain : Set E)) : T†.IsClosed
参数：hT : Dense (T.domain : Set E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.IsClosed.eq_1`：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3}
 [inst : CommRing R] [inst_1 : AddCommGroup E] [inst_2 : AddCommGroup F]   [inst
_3 : _root_.Mo…
· 使用定理 `LinearPMap.adjoint_graph_eq_graph_adjoint`：∀ {𝕜 : Type u_1} {E : Type u_
2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : 
InnerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Submodule.adjoint.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [
inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜
 E] [inst_3 …
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `LinearEquiv.image_eq_preimage_symm`：∀ {R : Type u_1} {S : Type u_6} {M :
 Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 :
 AddCommMonoid M] [inst_…
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用引理 `WithLp.prod_continuous_toLp`：prod_continuous_toLp : Continuous (@toLp p 
(α × β))
· 使用定理 `Submodule.isClosed_orthogonal`：isClosed_orthogonal : IsClosed (Kᗮ : Set 
E)
-/
theorem adjoint_isClosed (hT : Dense (T.domain : Set E)) :
    T†.IsClosed := by
  rw [IsClosed, adjoint_graph_eq_graph_adjoint hT, Submodule.adjoint]
  simp only [Submodule.map_coe]
  rw [LinearEquiv.coe_coe, LinearEquiv.image_eq_preimage_symm]
  exact (Submodule.isClosed_orthogonal _).preimage (WithLp.prod_continuous_toLp _ _ _)

/-- Every self-adjoint `LinearPMap` is closed. -/
/-
**LinearPMap._root_.IsSelfAdjoint.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every self-adjoint `LinearPMap` is closed.
-/
theorem _root_.IsSelfAdjoint.isClosed {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) : A.IsClosed := by
  rw [← isSelfAdjoint_def.mp hA]
  exact adjoint_isClosed hA.dense_domain

end LinearPMap

