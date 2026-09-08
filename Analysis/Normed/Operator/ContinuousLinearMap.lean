/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Topology.Algebra.Module.Equiv

/-! # Constructions of continuous linear maps between (semi-)normed spaces

A fundamental fact about (semi-)linear maps between normed spaces over sensible fields is that
continuity and boundedness are equivalent conditions.  That is, for normed spaces `E`, `F`, a
`LinearMap` `f : E →ₛₗ[σ] F` is the coercion of some `ContinuousLinearMap` `f' : E →SL[σ] F`, if
and only if there exists a bound `C` such that for all `x`, `‖f x‖ ≤ C * ‖x‖`.

We prove one direction in this file: `LinearMap.mkContinuous`, boundedness implies continuity. The
other direction, `ContinuousLinearMap.bound`, is deferred to a later file, where the
strong operator topology on `E →SL[σ] F` is available, because it is natural to use
`ContinuousLinearMap.bound` to define a norm `⨆ x, ‖f x‖ / ‖x‖` on `E →SL[σ] F` and to show that
this is compatible with the strong operator topology.

This file also contains several corollaries of `LinearMap.mkContinuous`: other "easy"
constructions of continuous linear maps between normed spaces.

This file is meant to be lightweight (it is imported by much of the analysis library); think twice
before adding imports!
-/

@[expose] public section

open Metric ContinuousLinearMap

open Set Real

open NNReal

variable {𝕜 𝕜₂ E F G : Type*}

/-! ## General constructions -/

section SeminormedAddCommGroup

variable [Ring 𝕜] [Ring 𝕜₂]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
variable [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 G]
variable {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/-- Construct a continuous linear map from a linear map and a bound on this linear map.
The fact that the norm of the continuous linear map is then controlled is given in
`LinearMap.mkContinuous_norm_le`. -/
/-
**LinearMap.mkContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.mkContinuous (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) : E ->S
L[σ] F
参数：C : Real；h : forall x, ‖f x‖ <= C * ‖x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a continuous linear map from a linear map and a bound on this linear m
ap.
The fact that the norm of the continuous linear map is then controlled is given 
in
`LinearMap.mkContinuous_norm_le`.
-/
def LinearMap.mkContinuous (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f, AddMonoidHomClass.continuous_of_bound f C h⟩

/-- Construct a continuous linear map from a linear map and the existence of a bound on this linear
map. If you have an explicit bound, use `LinearMap.mkContinuous` instead, as a norm estimate will
follow automatically in `LinearMap.mkContinuous_norm_le`. -/
/-
**LinearMap.mkContinuousOfExistsBound** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.mkContinuousOfExistsBound (h : exists C, forall x, ‖f x‖ <= C * 
‖x‖) : E ->SL[σ] F
参数：h : exists C, forall x, ‖f x‖ <= C * ‖x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a continuous linear map from a linear map and the existence of a bound
 on this linear
map. If you have an explicit bound, use `LinearMap.mkContinuous` instead, as a n
orm estimate will
follow automatically in `LinearMap.mkContinuous_norm_le`.
-/
def LinearMap.mkContinuousOfExistsBound (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f,
    let ⟨C, hC⟩ := h
    AddMonoidHomClass.continuous_of_bound f C hC⟩
/-
**continuous_of_linear_of_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_linear_of_bound {f : E -> G} (h_add : forall x y, f (x + y) 
= f x + f y) (h_smul : forall (c : 𝕜) (x), f (c • x) = c • f x) {C : Real} (h_bo
und : forall x, ‖f x‖ <= C * ‖x‖) : Continuous f
参数：h_add : forall x y, f (x + y) = f x + f y；h_smul : forall (c : 𝕜) (x), f (c •
 x) = c • f x；h_bound : forall x, ‖f x‖ <= C * ‖x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_linear_of_boundₛₗ`：continuous_of_linear_of_boundₛₗ {f : E 
-> F} (h_add : forall x y, f (x + y) = f x + f y) (h_smul : forall (c : 𝕜) (x), 
f (c • x) = σ c • f x…
-/
theorem continuous_of_linear_of_boundₛₗ {f : E → F} (h_add : ∀ x y, f (x + y) = f x + f y)
    (h_smul : ∀ (c : 𝕜) (x), f (c • x) = σ c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    Continuous f :=
  let φ : E →ₛₗ[σ] F :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound
/-
**continuous_of_linear_of_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_linear_of_bound {f : E -> G} (h_add : forall x y, f (x + y) 
= f x + f y) (h_smul : forall (c : 𝕜) (x), f (c • x) = c • f x) {C : Real} (h_bo
und : forall x, ‖f x‖ <= C * ‖x‖) : Continuous f
参数：h_add : forall x y, f (x + y) = f x + f y；h_smul : forall (c : 𝕜) (x), f (c •
 x) = c • f x；h_bound : forall x, ‖f x‖ <= C * ‖x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_linear_of_boundₛₗ`：continuous_of_linear_of_boundₛₗ {f : E 
-> F} (h_add : forall x y, f (x + y) = f x + f y) (h_smul : forall (c : 𝕜) (x), 
f (c • x) = σ c • f x…
-/
theorem continuous_of_linear_of_bound {f : E → G} (h_add : ∀ x y, f (x + y) = f x + f y)
    (h_smul : ∀ (c : 𝕜) (x), f (c • x) = c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    Continuous f :=
  continuous_of_linear_of_boundₛₗ (σ := RingHom.id 𝕜) h_add h_smul h_bound

@[simp, norm_cast]
/-
**LinearMap.mkContinuous_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.mkContinuous_coe (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) : (
f.mkContinuous C h : E ->ₛₗ[σ] F) = f
参数：C : Real；h : forall x, ‖f x‖ <= C * ‖x‖。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.mkContinuous_coe (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    (f.mkContinuous C h : E →ₛₗ[σ] F) = f :=
  rfl

@[simp]
/-
**LinearMap.mkContinuous_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.mkContinuous_apply (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) (
x : E) : f.mkContinuous C h x = f x
参数：C : Real；h : forall x, ‖f x‖ <= C * ‖x‖；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.mkContinuous_apply (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
    f.mkContinuous C h x = f x :=
  rfl

@[simp, norm_cast]
/-
**LinearMap.mkContinuousOfExistsBound_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.mkContinuousOfExistsBound_coe (h : exists C, forall x, ‖f x‖ <= 
C * ‖x‖) : (f.mkContinuousOfExistsBound h : E ->ₛₗ[σ] F) = f
参数：h : exists C, forall x, ‖f x‖ <= C * ‖x‖。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.mkContinuousOfExistsBound_coe (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    (f.mkContinuousOfExistsBound h : E →ₛₗ[σ] F) = f :=
  rfl

@[simp]
/-
**LinearMap.mkContinuousOfExistsBound_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.mkContinuousOfExistsBound_apply (h : exists C, forall x, ‖f x‖ <
= C * ‖x‖) (x : E) : f.mkContinuousOfExistsBound h x = f x
参数：h : exists C, forall x, ‖f x‖ <= C * ‖x‖；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.mkContinuousOfExistsBound_apply (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
    f.mkContinuousOfExistsBound h x = f x :=
  rfl

namespace ContinuousLinearMap

/-
**ContinuousLinearMap.antilipschitz_of_bound** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：antilipschitz_of_bound (f : E ->SL[σ] F) {K : Real>=0} (h : forall x, ‖x‖ 
<= K * ‖f x‖) : AntilipschitzWith K f
参数：f : E ->SL[σ] F；h : forall x, ‖x‖ <= K * ‖f x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.antilipschitz_of_bound`：∀ {𝓕 : Type u_1} {E : Type u_2
} {F : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]  
 [inst_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem antilipschitz_of_bound (f : E →SL[σ] F) {K : ℝ≥0} (h : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
    AntilipschitzWith K f :=
  AddMonoidHomClass.antilipschitz_of_bound _ h
/-
**ContinuousLinearMap.bound_of_antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：bound_of_antilipschitz (f : E ->SL[σ] F) {K : Real>=0} (h : AntilipschitzW
ith K f) (x) : ‖x‖ <= K * ‖f x‖
参数：f : E ->SL[σ] F；h : AntilipschitzWith K f；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem bound_of_antilipschitz (f : E →SL[σ] F) {K : ℝ≥0} (h : AntilipschitzWith K f) (x) :
    ‖x‖ ≤ K * ‖f x‖ :=
  ZeroHomClass.bound_of_antilipschitz _ h x

end ContinuousLinearMap

section

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ σ₂₁] [RingHomInvPair σ₂₁ σ]

/-- Construct a continuous linear equivalence from a linear equivalence together with
bounds in both directions. -/
/-
**LinearEquiv.toContinuousLinearEquivOfBounds** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.toContinuousLinearEquivOfBounds (e : E ≃ₛₗ[σ] F) (C_to C_inv :
 Real) (h_to : forall x, ‖e x‖ <= C_to * ‖x‖) (h_inv : forall x : F, ‖e.symm x‖ 
<= C_inv * ‖x‖) : E ≃SL[σ] F where toLinearEquiv
参数：e : E ≃ₛₗ[σ] F；C_to C_inv : Real；h_to : forall x, ‖e x‖ <= C_to * ‖x‖；h_inv :
 forall x : F, ‖e.symm x‖ <= C_inv * ‖x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a continuous linear equivalence from a linear equivalence together wit
h
bounds in both directions.
-/
def LinearEquiv.toContinuousLinearEquivOfBounds (e : E ≃ₛₗ[σ] F) (C_to C_inv : ℝ)
    (h_to : ∀ x, ‖e x‖ ≤ C_to * ‖x‖) (h_inv : ∀ x : F, ‖e.symm x‖ ≤ C_inv * ‖x‖) : E ≃SL[σ] F where
  toLinearEquiv := e
  continuous_toFun := AddMonoidHomClass.continuous_of_bound e C_to h_to
  continuous_invFun := AddMonoidHomClass.continuous_of_bound e.symm C_inv h_inv

end

end SeminormedAddCommGroup

section SeminormedBounded
variable [SeminormedRing 𝕜] [Ring 𝕜₂] [SeminormedAddCommGroup E]
variable [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Reinterpret a linear map `𝕜 →ₗ[𝕜] E` as a continuous linear map. This construction
is generalized to the case of any finite-dimensional domain
in `LinearMap.toContinuousLinearMap`. -/
/-
**LinearMap.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toContinuousLinearMap : (E ->ₗ[𝕜] F') ≃ₗ[𝕜] E ->L[𝕜] F' where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f

--- 原说明 ---
Reinterpret a linear map `𝕜 →ₗ[𝕜] E` as a continuous linear map. This constructi
on
is generalized to the case of any finite-dimensional domain
in `LinearMap.toContinuousLinearMap`.
-/
def LinearMap.toContinuousLinearMap₁ (f : 𝕜 →ₗ[𝕜] E) : 𝕜 →L[𝕜] E :=
  f.mkContinuous ‖f 1‖ fun x => by
    conv_lhs => rw [← mul_one x]
    rw [← smul_eq_mul, f.map_smul, mul_comm]; exact norm_smul_le _ _

@[simp]
/-
**LinearMap.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toContinuousLinearMap : (E ->ₗ[𝕜] F') ≃ₗ[𝕜] E ->L[𝕜] F' where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
-/
theorem LinearMap.toContinuousLinearMap₁_coe (f : 𝕜 →ₗ[𝕜] E) :
    (f.toContinuousLinearMap₁ : 𝕜 →ₗ[𝕜] E) = f :=
  rfl

@[simp]
/-
**LinearMap.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toContinuousLinearMap : (E ->ₗ[𝕜] F') ≃ₗ[𝕜] E ->L[𝕜] F' where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
-/
theorem LinearMap.toContinuousLinearMap₁_apply (f : 𝕜 →ₗ[𝕜] E) (x) :
    f.toContinuousLinearMap₁ x = f x :=
  rfl

end SeminormedBounded

section Normed
variable [Ring 𝕜] [Ring 𝕜₂]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [Module 𝕜 E] [Module 𝕜₂ F]
variable {σ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ] F) (x y z : E)

/-
**ContinuousLinearMap.isUniformEmbedding_of_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.isUniformEmbedding_of_bound {K : Real>=0} (hf : forall
 x, ‖x‖ <= K * ‖f x‖) : IsUniformEmbedding f
参数：hf : forall x, ‖x‖ <= K * ‖f x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntilipschitzWith.isUniformEmbedding`：isUniformEmbedding {α β : Type*} [
EMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β} (hf : Antilips
chitzWith K f) (hfc : Unif…
· 使用定理 `AddMonoidHomClass.antilipschitz_of_bound`：∀ {𝓕 : Type u_1} {E : Type u_2
} {F : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]  
 [inst_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
-/
theorem ContinuousLinearMap.isUniformEmbedding_of_bound {K : ℝ≥0} (hf : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
    IsUniformEmbedding f :=
  (AddMonoidHomClass.antilipschitz_of_bound f hf).isUniformEmbedding f.uniformContinuous

end Normed

/-! ## Homotheties -/

section Seminormed
variable [Ring 𝕜] [Ring 𝕜₂]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜₂ F]
variable {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/-- A (semi-)linear map which is a homothety is a continuous linear map.
Since the field `𝕜` need not have `ℝ` as a subfield, this theorem is not directly deducible from
the corresponding theorem about isometries plus a theorem about scalar multiplication.  Likewise
for the other theorems about homotheties in this file.
-/
/-
**ContinuousLinearMap.ofHomothety** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.ofHomothety (f : E ->ₛₗ[σ] F) (a : Real) (hf : forall 
x, ‖f x‖ = a * ‖x‖) : E ->SL[σ] F
参数：f : E ->ₛₗ[σ] F；a : Real；hf : forall x, ‖f x‖ = a * ‖x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (semi-)linear map which is a homothety is a continuous linear map.
Since the field `𝕜` need not have `ℝ` as a subfield, this theorem is not directl
y deducible from
the corresponding theorem about isometries plus a theorem about scalar multiplic
ation.  Likewise
for the other theorems about homotheties in this file.
-/
def ContinuousLinearMap.ofHomothety (f : E →ₛₗ[σ] F) (a : ℝ) (hf : ∀ x, ‖f x‖ = a * ‖x‖) :
    E →SL[σ] F :=
  f.mkContinuous a fun x => le_of_eq (hf x)

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ σ₂₁] [RingHomInvPair σ₂₁ σ]
/-
**ContinuousLinearEquiv.homothety_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.homothety_inverse (a : Real) (ha : 0 < a) (f : E ≃ₛₗ
[σ] F) : (forall x : E, ‖f x‖ = a * ‖x‖) -> forall y : F, ‖f.symm y‖ = a⁻¹ * ‖y‖
参数：a : Real；ha : 0 < a；f : E ≃ₛₗ[σ] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_inv_mul_iff_mul_eq₀`：eq_inv_mul_iff_mul_eq₀ (hb : b != 0) : a = b⁻¹ *
 c ↔ b * a = c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ContinuousLinearEquiv.homothety_inverse (a : ℝ) (ha : 0 < a) (f : E ≃ₛₗ[σ] F) :
    (∀ x : E, ‖f x‖ = a * ‖x‖) → ∀ y : F, ‖f.symm y‖ = a⁻¹ * ‖y‖ := by
  intro hf y
  simpa [eq_inv_mul_iff_mul_eq₀ (ne_of_gt ha)] using (hf (f.symm y)).symm

/-- A linear equivalence which is a homothety is a continuous linear equivalence. -/
/-
**ContinuousLinearEquiv.ofHomothety** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.ofHomothety (f : E ≃ₛₗ[σ] F) (a : Real) (ha : 0 < a)
 (hf : forall x, ‖f x‖ = a * ‖x‖) : E ≃SL[σ] F
参数：f : E ≃ₛₗ[σ] F；a : Real；ha : 0 < a；hf : forall x, ‖f x‖ = a * ‖x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence which is a homothety is a continuous linear equivalence.
-/
noncomputable def ContinuousLinearEquiv.ofHomothety (f : E ≃ₛₗ[σ] F) (a : ℝ) (ha : 0 < a)
    (hf : ∀ x, ‖f x‖ = a * ‖x‖) : E ≃SL[σ] F :=
  LinearEquiv.toContinuousLinearEquivOfBounds f a a⁻¹ (fun x => (hf x).le) fun x =>
    (ContinuousLinearEquiv.homothety_inverse a ha f hf x).le

end Seminormed

