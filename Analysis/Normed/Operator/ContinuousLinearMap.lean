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
continuity and boundedness are equivalent conditions. That is, for normed spaces `E`, `F`, a
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
variable {σ : 𝕜 ->+* 𝕜₂} (f : E ->ₛₗ[σ] F)

/--
Definition of `LinearMap.mkContinuous` / `LinearMap.mkContinuous` 的定义

English:
definition LinearMap.mkContinuous
  signature: (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖)
  body: ⟨f, AddMonoidHomClass.continuous_of_bound f C h⟩

中文:
定义 LinearMap.mkContinuous
  签名: (C : 实数) (h : 对任意 x, ‖f x‖ <= C * ‖x‖)
  定义体: ⟨f, AddMonoidHomClass.continuous_of_bound f C h⟩

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.continuous_of_bound, continuous_of_bound
-/
def LinearMap.mkContinuous (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) : E ->SL[σ] F :=
  ⟨f, AddMonoidHomClass.continuous_of_bound f C h⟩

/--
Definition of `LinearMap.mkContinuousOfExistsBound` / `LinearMap.mkContinuousOfExistsBound` 的定义

English:
definition LinearMap.mkContinuousOfExistsBound
  signature: (h : exists C, forall x, ‖f x‖ <= C * ‖x‖)
  body: ⟨f,
    let ⟨C, hC⟩ := h
    AddMonoidHomClass.continuous_of_bound f C hC⟩

中文:
定义 LinearMap.mkContinuousOfExistsBound
  签名: (h : 存在 C, 对任意 x, ‖f x‖ <= C * ‖x‖)
  定义体: ⟨f,
    let ⟨C, hC⟩ := h
    AddMonoidHomClass.continuous_of_bound f C hC⟩

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.continuous_of_bound, continuous_of_bound
-/
def LinearMap.mkContinuousOfExistsBound (h : exists C, forall x, ‖f x‖ <= C * ‖x‖) : E ->SL[σ] F :=
  ⟨f,
    let ⟨C, hC⟩ := h
    AddMonoidHomClass.continuous_of_bound f C hC⟩

/--
theorem `continuous_of_linear_of_boundₛₗ` / 定理 `continuous_of_linear_of_boundₛₗ`

English:
theorem continuous_of_linear_of_boundₛₗ
  statement: {f : E -> F} (h_add : forall x y, f (x + y) = f x + f y)
  proof: let φ : E ->ₛₗ[σ] F :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound

中文:
定理 continuous_of_linear_of_boundₛₗ
  结论: {f : E -> F} (h_add : 对任意 x y, f (x + y) = f x + f y)
  证明: let φ : E ->ₛₗ[σ] F :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.continuous_of_bound, continuous_of_bound, h_add, h_bound, h_smul, map_add, map_smul
-/
theorem continuous_of_linear_of_boundₛₗ {f : E -> F} (h_add : forall x y, f (x + y) = f x + f y)
    (h_smul : forall (c : 𝕜) (x), f (c • x) = σ c • f x) {C : Real} (h_bound : forall x, ‖f x‖ <= C * ‖x‖) :
    Continuous f :=
  let φ : E ->ₛₗ[σ] F :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound

/--
theorem `continuous_of_linear_of_bound` / 定理 `continuous_of_linear_of_bound`

English:
theorem continuous_of_linear_of_bound
  statement: {f : E -> G} (h_add : forall x y, f (x + y) = f x + f y)
  proof: continuous_of_linear_of_boundₛₗ (σ := RingHom.id 𝕜) h_add h_smul h_bound

@[simp, norm_cast]

中文:
定理 continuous_of_linear_of_bound
  结论: {f : E -> G} (h_add : 对任意 x y, f (x + y) = f x + f y)
  证明: continuous_of_linear_of_boundₛₗ (σ := RingHom.id 𝕜) h_add h_smul h_bound

@[simp, norm_cast]

Depends on / 依赖: RingHom, RingHom.id, h_add, h_bound, h_smul
-/
theorem continuous_of_linear_of_bound {f : E -> G} (h_add : forall x y, f (x + y) = f x + f y)
    (h_smul : forall (c : 𝕜) (x), f (c • x) = c • f x) {C : Real} (h_bound : forall x, ‖f x‖ <= C * ‖x‖) :
    Continuous f :=
  continuous_of_linear_of_boundₛₗ (σ := RingHom.id 𝕜) h_add h_smul h_bound

@[simp, norm_cast]
/--
theorem `LinearMap.mkContinuous_coe` / 定理 `LinearMap.mkContinuous_coe`

English:
theorem LinearMap.mkContinuous_coe
  given: (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖)
  proof: rfl

@[simp]

中文:
定理 LinearMap.mkContinuous_coe
  条件: (C : 实数) (h : 对任意 x, ‖f x‖ <= C * ‖x‖)
  证明: rfl

@[simp]
-/
theorem LinearMap.mkContinuous_coe (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) :
    (f.mkContinuous C h : E ->ₛₗ[σ] F) = f :=
  rfl

@[simp]
/--
theorem `LinearMap.mkContinuous_apply` / 定理 `LinearMap.mkContinuous_apply`

English:
theorem LinearMap.mkContinuous_apply
  given: (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) (x : E)
  proof: rfl

@[simp, norm_cast]

中文:
定理 LinearMap.mkContinuous_apply
  条件: (C : 实数) (h : 对任意 x, ‖f x‖ <= C * ‖x‖) (x : E)
  证明: rfl

@[simp, norm_cast]
-/
theorem LinearMap.mkContinuous_apply (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) (x : E) :
    f.mkContinuous C h x = f x :=
  rfl

@[simp, norm_cast]
/--
theorem `LinearMap.mkContinuousOfExistsBound_coe` / 定理 `LinearMap.mkContinuousOfExistsBound_coe`

English:
theorem LinearMap.mkContinuousOfExistsBound_coe
  given: (h : exists C, forall x, ‖f x‖ <= C * ‖x‖)
  proof: rfl

@[simp]

中文:
定理 LinearMap.mkContinuousOfExistsBound_coe
  条件: (h : 存在 C, 对任意 x, ‖f x‖ <= C * ‖x‖)
  证明: rfl

@[simp]
-/
theorem LinearMap.mkContinuousOfExistsBound_coe (h : exists C, forall x, ‖f x‖ <= C * ‖x‖) :
    (f.mkContinuousOfExistsBound h : E ->ₛₗ[σ] F) = f :=
  rfl

@[simp]
/--
theorem `LinearMap.mkContinuousOfExistsBound_apply` / 定理 `LinearMap.mkContinuousOfExistsBound_apply`

English:
theorem LinearMap.mkContinuousOfExistsBound_apply
  given: (h : exists C, forall x, ‖f x‖ <= C * ‖x‖) (x : E)
  proof: rfl

中文:
定理 LinearMap.mkContinuousOfExistsBound_apply
  条件: (h : 存在 C, 对任意 x, ‖f x‖ <= C * ‖x‖) (x : E)
  证明: rfl
-/
theorem LinearMap.mkContinuousOfExistsBound_apply (h : exists C, forall x, ‖f x‖ <= C * ‖x‖) (x : E) :
    f.mkContinuousOfExistsBound h x = f x :=
  rfl

namespace ContinuousLinearMap

/--
theorem `antilipschitz_of_bound` / 定理 `antilipschitz_of_bound`

English:
theorem antilipschitz_of_bound
  given: (f : E ->SL[σ] F) {K : Real>=0} (h : forall x, ‖x‖ <= K * ‖f x‖)
  proof: AddMonoidHomClass.antilipschitz_of_bound _ h

中文:
定理 antilipschitz_of_bound
  条件: (f : E ->SL[σ] F) {K : 实数>=0} (h : 对任意 x, ‖x‖ <= K * ‖f x‖)
  证明: AddMonoidHomClass.antilipschitz_of_bound _ h

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.antilipschitz_of_bound, antilipschitz_of_bound
-/
theorem antilipschitz_of_bound (f : E ->SL[σ] F) {K : Real>=0} (h : forall x, ‖x‖ <= K * ‖f x‖) :
    AntilipschitzWith K f :=
  AddMonoidHomClass.antilipschitz_of_bound _ h

/--
theorem `bound_of_antilipschitz` / 定理 `bound_of_antilipschitz`

English:
theorem bound_of_antilipschitz
  given: (f : E ->SL[σ] F) {K : Real>=0} (h : AntilipschitzWith K f) (x)
  proof: ZeroHomClass.bound_of_antilipschitz _ h x

中文:
定理 bound_of_antilipschitz
  条件: (f : E ->SL[σ] F) {K : 实数>=0} (h : AntilipschitzWith K f) (x)
  证明: ZeroHomClass.bound_of_antilipschitz _ h x

Depends on / 依赖: ZeroHomClass, ZeroHomClass.bound_of_antilipschitz, bound_of_antilipschitz
-/
theorem bound_of_antilipschitz (f : E ->SL[σ] F) {K : Real>=0} (h : AntilipschitzWith K f) (x) :
    ‖x‖ <= K * ‖f x‖ :=
  ZeroHomClass.bound_of_antilipschitz _ h x

end ContinuousLinearMap

section

variable {σ₂₁ : 𝕜₂ ->+* 𝕜} [RingHomInvPair σ σ₂₁] [RingHomInvPair σ₂₁ σ]

/--
Definition of `LinearEquiv.toContinuousLinearEquivOfBounds` / `LinearEquiv.toContinuousLinearEquivOfBounds` 的定义

English:
definition LinearEquiv.toContinuousLinearEquivOfBounds
  signature: (e : E ≃ₛₗ[σ] F) (C_to C_inv : Real)
  body: e
  continuous_toFun := AddMonoidHomClass.continuous_of_bound e C_to h_to
  continuous_invFun := AddMonoidHomClass.continuous_of_bound e.symm C_inv h_inv

中文:
定义 LinearEquiv.toContinuousLinearEquivOfBounds
  签名: (e : E ≃ₛₗ[σ] F) (C_to C_inv : 实数)
  定义体: e
  continuous_toFun := AddMonoidHomClass.continuous_of_bound e C_to h_to
  continuous_invFun := AddMonoidHomClass.continuous_of_bound e.symm C_inv h_inv
-/
def LinearEquiv.toContinuousLinearEquivOfBounds (e : E ≃ₛₗ[σ] F) (C_to C_inv : Real)
    (h_to : forall x, ‖e x‖ <= C_to * ‖x‖) (h_inv : forall x : F, ‖e.symm x‖ <= C_inv * ‖x‖) : E ≃SL[σ] F where
  toLinearEquiv := e
  continuous_toFun := AddMonoidHomClass.continuous_of_bound e C_to h_to
  continuous_invFun := AddMonoidHomClass.continuous_of_bound e.symm C_inv h_inv

end

end SeminormedAddCommGroup

section SeminormedBounded
variable [SeminormedRing 𝕜] [Ring 𝕜₂] [SeminormedAddCommGroup E]
variable [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
Definition of `LinearMap.toContinuousLinearMap₁` / `LinearMap.toContinuousLinearMap₁` 的定义

English:
definition LinearMap.toContinuousLinearMap₁
  signature: (f : 𝕜 ->ₗ[𝕜] E)
  body: f.mkContinuous ‖f 1‖ fun x => by
    conv_lhs => rw [← mul_one x]
    rw [← smul_eq_mul]; rw [f.map_smul]; rw [mul_comm]; exact norm_smul_le _ _

@[simp]

中文:
定义 LinearMap.toContinuousLinearMap₁
  签名: (f : 𝕜 ->ₗ[𝕜] E)
  定义体: f.mkContinuous ‖f 1‖ fun x => by
    conv_lhs => rw [← mul_one x]
    rw [← smul_eq_mul]; rw [f.map_smul]; rw [mul_comm]; exact norm_smul_le _ _

@[simp]

Depends on / 依赖: conv_lhs, f.map_smul, f.mkContinuous, map_smul, mkContinuous, mul_comm, mul_one, norm_smul_le, smul_eq_mul
-/
def LinearMap.toContinuousLinearMap₁ (f : 𝕜 ->ₗ[𝕜] E) : 𝕜 ->L[𝕜] E :=
  f.mkContinuous ‖f 1‖ fun x => by
    conv_lhs => rw [← mul_one x]
    rw [← smul_eq_mul]; rw [f.map_smul]; rw [mul_comm]; exact norm_smul_le _ _

@[simp]
/--
theorem `LinearMap.toContinuousLinearMap₁_coe` / 定理 `LinearMap.toContinuousLinearMap₁_coe`

English:
theorem LinearMap.toContinuousLinearMap₁_coe
  given: (f : 𝕜 ->ₗ[𝕜] E)
  proof: rfl

@[simp]

中文:
定理 LinearMap.toContinuousLinearMap₁_coe
  条件: (f : 𝕜 ->ₗ[𝕜] E)
  证明: rfl

@[simp]
-/
theorem LinearMap.toContinuousLinearMap₁_coe (f : 𝕜 ->ₗ[𝕜] E) :
    (f.toContinuousLinearMap₁ : 𝕜 ->ₗ[𝕜] E) = f :=
  rfl

@[simp]
/--
theorem `LinearMap.toContinuousLinearMap₁_apply` / 定理 `LinearMap.toContinuousLinearMap₁_apply`

English:
theorem LinearMap.toContinuousLinearMap₁_apply
  given: (f : 𝕜 ->ₗ[𝕜] E) (x)
  proof: rfl

中文:
定理 LinearMap.toContinuousLinearMap₁_apply
  条件: (f : 𝕜 ->ₗ[𝕜] E) (x)
  证明: rfl
-/
theorem LinearMap.toContinuousLinearMap₁_apply (f : 𝕜 ->ₗ[𝕜] E) (x) :
    f.toContinuousLinearMap₁ x = f x :=
  rfl

end SeminormedBounded

section Normed
variable [Ring 𝕜] [Ring 𝕜₂]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [Module 𝕜 E] [Module 𝕜₂ F]
variable {σ : 𝕜 ->+* 𝕜₂} (f g : E ->SL[σ] F) (x y z : E)

/--
theorem `ContinuousLinearMap.isUniformEmbedding_of_bound` / 定理 `ContinuousLinearMap.isUniformEmbedding_of_bound`

English:
theorem ContinuousLinearMap.isUniformEmbedding_of_bound
  given: {K : Real>=0} (hf : forall x, ‖x‖ <= K * ‖f x‖)
  proof: (AddMonoidHomClass.antilipschitz_of_bound f hf).isUniformEmbedding f.uniformContinuous

中文:
定理 ContinuousLinearMap.isUniformEmbedding_of_bound
  条件: {K : 实数>=0} (hf : 对任意 x, ‖x‖ <= K * ‖f x‖)
  证明: (AddMonoidHomClass.antilipschitz_of_bound f hf).isUniformEmbedding f.uniformContinuous

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.antilipschitz_of_bound, antilipschitz_of_bound, f.uniformContinuous, isUniformEmbedding, uniformContinuous
-/
theorem ContinuousLinearMap.isUniformEmbedding_of_bound {K : Real>=0} (hf : forall x, ‖x‖ <= K * ‖f x‖) :
    IsUniformEmbedding f :=
  (AddMonoidHomClass.antilipschitz_of_bound f hf).isUniformEmbedding f.uniformContinuous

end Normed

/-! ## Homotheties -/

section Seminormed
variable [Ring 𝕜] [Ring 𝕜₂]
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [Module 𝕜 E] [Module 𝕜₂ F]
variable {σ : 𝕜 ->+* 𝕜₂} (f : E ->ₛₗ[σ] F)

/--
Definition of `ContinuousLinearMap.ofHomothety` / `ContinuousLinearMap.ofHomothety` 的定义

English:
definition ContinuousLinearMap.ofHomothety
  signature: (f : E ->ₛₗ[σ] F) (a : Real) (hf : forall x, ‖f x‖ = a * ‖x‖)
  body: f.mkContinuous a fun x => le_of_eq (hf x)

中文:
定义 ContinuousLinearMap.ofHomothety
  签名: (f : E ->ₛₗ[σ] F) (a : 实数) (hf : 对任意 x, ‖f x‖ = a * ‖x‖)
  定义体: f.mkContinuous a fun x => le_of_eq (hf x)

Depends on / 依赖: f.mkContinuous, le_of_eq, mkContinuous
-/
def ContinuousLinearMap.ofHomothety (f : E ->ₛₗ[σ] F) (a : Real) (hf : forall x, ‖f x‖ = a * ‖x‖) :
    E ->SL[σ] F :=
  f.mkContinuous a fun x => le_of_eq (hf x)

variable {σ₂₁ : 𝕜₂ ->+* 𝕜} [RingHomInvPair σ σ₂₁] [RingHomInvPair σ₂₁ σ]

/--
theorem `ContinuousLinearEquiv.homothety_inverse` / 定理 `ContinuousLinearEquiv.homothety_inverse`

English:
theorem ContinuousLinearEquiv.homothety_inverse
  given: (a : Real) (ha : 0 < a) (f : E ≃ₛₗ[σ] F)
  proof: by
  intro hf y
  simpa [eq_inv_mul_iff_mul_eq₀ (ne_of_gt ha)] using (hf (f.symm y)).symm

中文:
定理 ContinuousLinearEquiv.homothety_inverse
  条件: (a : 实数) (ha : 0 < a) (f : E ≃ₛₗ[σ] F)
  证明: by
  intro hf y
  simpa [eq_inv_mul_iff_mul_eq₀ (ne_of_gt ha)] using (hf (f.symm y)).symm

Depends on / 依赖: f.symm, ne_of_gt
-/
theorem ContinuousLinearEquiv.homothety_inverse (a : Real) (ha : 0 < a) (f : E ≃ₛₗ[σ] F) :
    (forall x : E, ‖f x‖ = a * ‖x‖) -> forall y : F, ‖f.symm y‖ = a⁻¹ * ‖y‖ := by
  intro hf y
  simpa [eq_inv_mul_iff_mul_eq₀ (ne_of_gt ha)] using (hf (f.symm y)).symm

/--
Definition of `ContinuousLinearEquiv.ofHomothety` / `ContinuousLinearEquiv.ofHomothety` 的定义

English:
definition ContinuousLinearEquiv.ofHomothety
  signature: (f : E ≃ₛₗ[σ] F) (a : Real) (ha : 0 < a)
  body: LinearEquiv.toContinuousLinearEquivOfBounds f a a⁻¹ (fun x => (hf x).le) fun x =>
    (ContinuousLinearEquiv.homothety_inverse a ha f hf x).le

中文:
定义 ContinuousLinearEquiv.ofHomothety
  签名: (f : E ≃ₛₗ[σ] F) (a : 实数) (ha : 0 < a)
  定义体: LinearEquiv.toContinuousLinearEquivOfBounds f a a⁻¹ (fun x => (hf x).le) fun x =>
    (ContinuousLinearEquiv.homothety_inverse a ha f hf x).le

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.homothety_inverse, LinearEquiv, LinearEquiv.toContinuousLinearEquivOfBounds, homothety_inverse, toContinuousLinearEquivOfBounds
-/
noncomputable def ContinuousLinearEquiv.ofHomothety (f : E ≃ₛₗ[σ] F) (a : Real) (ha : 0 < a)
    (hf : forall x, ‖f x‖ = a * ‖x‖) : E ≃SL[σ] F :=
  LinearEquiv.toContinuousLinearEquivOfBounds f a a⁻¹ (fun x => (hf x).le) fun x =>
    (ContinuousLinearEquiv.homothety_inverse a ha f hf x).le

end Seminormed
