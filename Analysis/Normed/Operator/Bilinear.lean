/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Operator norm: bilinear maps

This file contains lemmas concerning operator norm as applied to bilinear maps `E × F → G`,
interpreted as linear maps `E → F → G` as usual (and similarly for semilinear variants).

-/

@[expose] public section

suppress_compilation

open Bornology
open Filter hiding map_smul
open scoped NNReal Topology Uniformity

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable {𝕜 𝕜₂ 𝕜₃ E Eₗ F Fₗ G Gₗ 𝓕 : Type*}

section SemiNormed

open Metric ContinuousLinearMap

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup Eₗ] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup G] [SeminormedAddCommGroup Gₗ]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  [NormedSpace 𝕜 Gₗ] {σ₁₂ : 𝕜 ->+* 𝕜₂} {σ₂₃ : 𝕜₂ ->+* 𝕜₃} {σ₁₃ : 𝕜 ->+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [FunLike 𝓕 E F]

namespace ContinuousLinearMap

section OpNorm

open Set Real

/--
theorem `opNorm_ext` / 定理 `opNorm_ext`

English:
theorem opNorm_ext
  statement: [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₂] F) (g : E ->SL[σ₁₃] G)
  proof: opNorm_eq_of_bounds (norm_nonneg _)
    (fun x => by
      rw [h x]
      exact le_opNorm _ _)
    fun c hc h₂ =>
    opNorm_le_bound _ hc fun z => by
      rw [← h z]
      exact h₂ z

中文:
定理 opNorm_ext
  结论: [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₂] F) (g : E ->SL[σ₁₃] G)
  证明: opNorm_eq_of_bounds (norm_nonneg _)
    (fun x => by
      rw [h x]
      exact le_opNorm _ _)
    fun c hc h₂ =>
    opNorm_le_bound _ hc fun z => by
      rw [← h z]
      exact h₂ z

Depends on / 依赖: le_opNorm, norm_nonneg, opNorm_eq_of_bounds, opNorm_le_bound
-/
theorem opNorm_ext [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₂] F) (g : E ->SL[σ₁₃] G)
    (h : forall x, ‖f x‖ = ‖g x‖) : ‖f‖ = ‖g‖ :=
  opNorm_eq_of_bounds (norm_nonneg _)
    (fun x => by
      rw [h x]
      exact le_opNorm _ _)
    fun c hc h₂ =>
    opNorm_le_bound _ hc fun z => by
      rw [← h z]
      exact h₂ z

variable [RingHomIsometric σ₂₃]

/--
theorem `opNorm_le_bound₂` / 定理 `opNorm_le_bound₂`

English:
theorem opNorm_le_bound₂
  statement: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) {C : Real} (h0 : 0 <= C)
  proof: f.opNorm_le_bound h0 fun x => (f x).opNorm_le_bound (by positivity) hC x

中文:
定理 opNorm_le_bound₂
  结论: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) {C : 实数} (h0 : 0 <= C)
  证明: f.opNorm_le_bound h0 fun x => (f x).opNorm_le_bound (by positivity) hC x

Depends on / 依赖: f.opNorm_le_bound, opNorm_le_bound
-/
theorem opNorm_le_bound₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) {C : Real} (h0 : 0 <= C)
    (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖y‖) : ‖f‖ <= C :=
f.opNorm_le_bound h0 fun x => (f x).opNorm_le_bound (by positivity) hC x

/--
theorem `le_opNorm₂` / 定理 `le_opNorm₂`

English:
theorem le_opNorm₂
  given: [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F)
  proof: (f x).le_of_opNorm_le (f.le_opNorm x) y

中文:
定理 le_opNorm₂
  条件: [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F)
  证明: (f x).le_of_opNorm_le (f.le_opNorm x) y

Depends on / 依赖: f.le_opNorm, le_of_opNorm_le, le_opNorm
-/
theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) :
    ‖f x y‖ <= ‖f‖ * ‖x‖ * ‖y‖ :=
  (f x).le_of_opNorm_le (f.le_opNorm x) y

/--
theorem `le_of_opNorm₂_le_of_le` / 定理 `le_of_opNorm₂_le_of_le`

English:
theorem le_of_opNorm₂_le_of_le
  statement: [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) {x : E} {y : F}
  proof: (f x).le_of_opNorm_le_of_le (f.le_of_opNorm_le_of_le hf hx) hy

中文:
定理 le_of_opNorm₂_le_of_le
  结论: [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) {x : E} {y : F}
  证明: (f x).le_of_opNorm_le_of_le (f.le_of_opNorm_le_of_le hf hx) hy

Depends on / 依赖: f.le_of_opNorm_le_of_le, le_of_opNorm_le_of_le
-/
theorem le_of_opNorm₂_le_of_le [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) {x : E} {y : F}
    {a b c : Real} (hf : ‖f‖ <= a) (hx : ‖x‖ <= b) (hy : ‖y‖ <= c) :
    ‖f x y‖ <= a * b * c :=
  (f x).le_of_opNorm_le_of_le (f.le_of_opNorm_le_of_le hf hx) hy

open scoped ENNReal

/--
theorem `opENorm_le_bound₂` / 定理 `opENorm_le_bound₂`

English:
theorem opENorm_le_bound₂
  statement: [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) {C : Real>=0∞}
  proof: f.opENorm_le_bound fun x => (f x).opENorm_le_bound hC x

中文:
定理 opENorm_le_bound₂
  结论: [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) {C : 实数>=0∞}
  证明: f.opENorm_le_bound fun x => (f x).opENorm_le_bound hC x

Depends on / 依赖: f.opENorm_le_bound, opENorm_le_bound
-/
theorem opENorm_le_bound₂ [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) {C : Real>=0∞}
    (hC : forall x y, ‖f x y‖ₑ <= C * ‖x‖ₑ * ‖y‖ₑ) : ‖f‖ₑ <= C :=
f.opENorm_le_bound fun x => (f x).opENorm_le_bound hC x

/--
theorem `le_opENorm₂` / 定理 `le_opENorm₂`

English:
theorem le_opENorm₂
  given: [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F)
  proof: (f x).le_of_opENorm_le (f.le_opENorm x) y

中文:
定理 le_opENorm₂
  条件: [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F)
  证明: (f x).le_of_opENorm_le (f.le_opENorm x) y

Depends on / 依赖: f.le_opENorm, le_of_opENorm_le, le_opENorm
-/
theorem le_opENorm₂ [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) :
    ‖f x y‖ₑ <= ‖f‖ₑ * ‖x‖ₑ * ‖y‖ₑ :=
  (f x).le_of_opENorm_le (f.le_opENorm x) y

end OpNorm

end ContinuousLinearMap

namespace LinearMap

/--
lemma `norm_mkContinuous₂_aux` / 引理 `norm_mkContinuous₂_aux`

English:
lemma norm_mkContinuous₂_aux
  statement: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) (C : Real)
  proof: (mkContinuous_norm_le' (f x) (h x)).trans_eq by
    rw [max_mul_of_nonneg _ _ (norm_nonneg x)]; rw [zero_mul]

中文:
引理 norm_mkContinuous₂_aux
  结论: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) (C : 实数)
  证明: (mkContinuous_norm_le' (f x) (h x)).trans_eq by
    rw [max_mul_of_nonneg _ _ (norm_nonneg x)]; rw [zero_mul]

Depends on / 依赖: max_mul_of_nonneg, mkContinuous_norm_le, norm_nonneg, trans_eq, zero_mul
-/
lemma norm_mkContinuous₂_aux (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) (C : Real)
    (h : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖y‖) (x : E) :
    ‖(f x).mkContinuous (C * ‖x‖) (h x)‖ <= max C 0 * ‖x‖ :=
(mkContinuous_norm_le' (f x) (h x)).trans_eq by
    rw [max_mul_of_nonneg _ _ (norm_nonneg x)]; rw [zero_mul]

variable [RingHomIsometric σ₂₃]

/--
Definition of `mkContinuousOfExistsBound₂` / `mkContinuousOfExistsBound₂` 的定义

English:
definition mkContinuousOfExistsBound₂
  signature: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G)
  body: LinearMap.mkContinuousOfExistsBound
    { toFun := fun x => (f x).mkContinuousOfExistsBound <| let ⟨C, hC⟩ := h; ⟨C * ‖x‖, hC x⟩
      map_add' := fun x y => by
        ext z
        simp
      map_smul' := fun c x => by
        ext z
        simp } <|
    let ⟨C, hC⟩ := h; ⟨max C 0, norm_mkContinuo

中文:
定义 mkContinuousOfExistsBound₂
  签名: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G)
  定义体: LinearMap.mkContinuousOfExistsBound
    { toFun := fun x => (f x).mkContinuousOfExistsBound <| let ⟨C, hC⟩ := h; ⟨C * ‖x‖, hC x⟩
      map_add' := fun x y => by
        ext z
        simp
      map_smul' := fun c x => by
        ext z
        simp } <|
    let ⟨C, hC⟩ := h; ⟨max C 0, norm_mkContinuo

Depends on / 依赖: LinearMap, LinearMap.mkContinuousOfExistsBound, map_add, map_smul, mkContinuousOfExistsBound
-/
def mkContinuousOfExistsBound₂ (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G)
    (h : exists C, forall x y, ‖f x y‖ <= C * ‖x‖ * ‖y‖) : E ->SL[σ₁₃] F ->SL[σ₂₃] G :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun x => (f x).mkContinuousOfExistsBound <| let ⟨C, hC⟩ := h; ⟨C * ‖x‖, hC x⟩
      map_add' := fun x y => by
        ext z
        simp
      map_smul' := fun c x => by
        ext z
        simp } <|
    let ⟨C, hC⟩ := h; ⟨max C 0, norm_mkContinuous₂_aux f C hC⟩

/--
Definition of `mkContinuous₂` / `mkContinuous₂` 的定义

English:
definition mkContinuous₂
  signature: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) (C : Real) (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖y‖)
  body: mkContinuousOfExistsBound₂ f ⟨C, hC⟩

@[simp]

中文:
定义 mkContinuous₂
  签名: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) (C : 实数) (hC : 对任意 x y, ‖f x y‖ <= C * ‖x‖ * ‖y‖)
  定义体: mkContinuousOfExistsBound₂ f ⟨C, hC⟩

@[simp]
-/
def mkContinuous₂ (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) (C : Real) (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖y‖) :
    E ->SL[σ₁₃] F ->SL[σ₂₃] G :=
  mkContinuousOfExistsBound₂ f ⟨C, hC⟩

@[simp]
/--
theorem `mkContinuous₂_apply` / 定理 `mkContinuous₂_apply`

English:
theorem mkContinuous₂_apply
  statement: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) {C : Real}
  proof: rfl

中文:
定理 mkContinuous₂_apply
  结论: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) {C : 实数}
  证明: rfl
-/
theorem mkContinuous₂_apply (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) {C : Real}
    (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖y‖) (x : E) (y : F) : f.mkContinuous₂ C hC x y = f x y :=
  rfl

/--
theorem `mkContinuous₂_norm_le'` / 定理 `mkContinuous₂_norm_le'`

English:
theorem mkContinuous₂_norm_le'
  statement: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) {C : Real}
  proof: mkContinuous_norm_le _ (le_max_iff.2 <| Or.inr le_rfl) (norm_mkContinuous₂_aux f C hC)

中文:
定理 mkContinuous₂_norm_le'
  结论: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) {C : 实数}
  证明: mkContinuous_norm_le _ (le_max_iff.2 <| Or.inr le_rfl) (norm_mkContinuous₂_aux f C hC)

Depends on / 依赖: Or.inr, le_max_iff, le_rfl, mkContinuous_norm_le
-/
theorem mkContinuous₂_norm_le' (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) {C : Real}
    (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ <= max C 0 :=
  mkContinuous_norm_le _ (le_max_iff.2 <| Or.inr le_rfl) (norm_mkContinuous₂_aux f C hC)

/--
theorem `mkContinuous₂_norm_le` / 定理 `mkContinuous₂_norm_le`

English:
theorem mkContinuous₂_norm_le
  statement: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) {C : Real} (h0 : 0 <= C)
  proof: (f.mkContinuous₂_norm_le' hC).trans_eq max_eq_left h0

中文:
定理 mkContinuous₂_norm_le
  结论: (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) {C : 实数} (h0 : 0 <= C)
  证明: (f.mkContinuous₂_norm_le' hC).trans_eq max_eq_left h0

Depends on / 依赖: f.mkContinuous, max_eq_left, trans_eq
-/
theorem mkContinuous₂_norm_le (f : E ->ₛₗ[σ₁₃] F ->ₛₗ[σ₂₃] G) {C : Real} (h0 : 0 <= C)
    (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ <= C :=
(f.mkContinuous₂_norm_le' hC).trans_eq max_eq_left h0

end LinearMap

namespace ContinuousLinearMap

variable [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]

/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  body: LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ σ₂₃ σ₁₃ (fun y x => f x y) (fun x y z => (f z).map_add x y)
      (fun c y x => (f x).map_smulₛₗ c y) (fun z x y => by simp only [f.map_add, add_apply])
        (fun c y x => by simp only [f.map_smulₛₗ, smul_apply]))
‖f‖ fun y x => (f.le_opNorm₂ x y).tra

中文:
定义 flip
  签名: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  定义体: LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ σ₂₃ σ₁₃ (fun y x => f x y) (fun x y z => (f z).map_add x y)
      (fun c y x => (f x).map_smulₛₗ c y) (fun z x y => by simp only [f.map_add, add_apply])
        (fun c y x => by simp only [f.map_smulₛₗ, smul_apply]))
‖f‖ fun y x => (f.le_opNorm₂ x y).tra

Depends on / 依赖: LinearMap, LinearMap.mk, LinearMap.mkContinuous, add_apply, f.le_opNorm, f.map_add, f.map_smul, map_add, mul_right_comm, smul_apply, trans_eq
-/
def flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : F ->SL[σ₂₃] E ->SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ σ₂₃ σ₁₃ (fun y x => f x y) (fun x y z => (f z).map_add x y)
      (fun c y x => (f x).map_smulₛₗ c y) (fun z x y => by simp only [f.map_add, add_apply])
        (fun c y x => by simp only [f.map_smulₛₗ, smul_apply]))
‖f‖ fun y x => (f.le_opNorm₂ x y).trans_eq by simp only [mul_right_comm]

/--
theorem `le_norm_flip` / 定理 `le_norm_flip`

English:
theorem le_norm_flip
  given: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  statement: ‖f‖ <= ‖flip f‖
  proof: f.opNorm_le_bound₂ (norm_nonneg f.flip) fun x y => by
    rw [mul_right_comm]
    exact (flip f).le_opNorm₂ y x

@[simp]

中文:
定理 le_norm_flip
  条件: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  结论: ‖f‖ <= ‖flip f‖
  证明: f.opNorm_le_bound₂ (norm_nonneg f.flip) fun x y => by
    rw [mul_right_comm]
    exact (flip f).le_opNorm₂ y x

@[simp]
-/
private theorem le_norm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : ‖f‖ <= ‖flip f‖ :=
  f.opNorm_le_bound₂ (norm_nonneg f.flip) fun x y => by
    rw [mul_right_comm]
    exact (flip f).le_opNorm₂ y x

@[simp]
/--
theorem `flip_apply` / 定理 `flip_apply`

English:
theorem flip_apply
  given: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F)
  statement: f.flip y x = f x y
  proof: rfl

@[simp]

中文:
定理 flip_apply
  条件: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F)
  结论: f.flip y x = f x y
  证明: rfl

@[simp]
-/
theorem flip_apply (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : f.flip y x = f x y :=
  rfl

@[simp]
/--
theorem `flip_flip` / 定理 `flip_flip`

English:
theorem flip_flip
  given: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  statement: f.flip.flip = f
  proof: by
  ext
  rfl

@[simp]

中文:
定理 flip_flip
  条件: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  结论: f.flip.flip = f
  证明: by
  ext
  rfl

@[simp]
-/
theorem flip_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : f.flip.flip = f := by
  ext
  rfl

@[simp]
/--
theorem `opNorm_flip` / 定理 `opNorm_flip`

English:
theorem opNorm_flip
  given: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  statement: ‖f.flip‖ = ‖f‖
  proof: le_antisymm (by simpa only [flip_flip] using le_norm_flip f.flip) (le_norm_flip f)

@[simp]

中文:
定理 opNorm_flip
  条件: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  结论: ‖f.flip‖ = ‖f‖
  证明: le_antisymm (by simpa only [flip_flip] using le_norm_flip f.flip) (le_norm_flip f)

@[simp]

Depends on / 依赖: f.flip, flip_flip, le_antisymm, le_norm_flip
-/
theorem opNorm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : ‖f.flip‖ = ‖f‖ :=
  le_antisymm (by simpa only [flip_flip] using le_norm_flip f.flip) (le_norm_flip f)

@[simp]
/--
theorem `opNNNorm_flip` / 定理 `opNNNorm_flip`

English:
theorem opNNNorm_flip
  given: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  statement: ‖f.flip‖₊ = ‖f‖₊
  proof: by
  simp [← NNReal.coe_inj]

@[simp]

中文:
定理 opNNNorm_flip
  条件: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  结论: ‖f.flip‖₊ = ‖f‖₊
  证明: by
  simp [← NNReal.coe_inj]

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_inj, coe_inj
-/
theorem opNNNorm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : ‖f.flip‖₊ = ‖f‖₊ := by
  simp [← NNReal.coe_inj]

@[simp]
/--
theorem `opENorm_flip` / 定理 `opENorm_flip`

English:
theorem opENorm_flip
  given: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  statement: ‖f.flip‖ₑ = ‖f‖ₑ
  proof: by
  simp [enorm_eq_nnnorm]

@[simp]

中文:
定理 opENorm_flip
  条件: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  结论: ‖f.flip‖ₑ = ‖f‖ₑ
  证明: by
  simp [enorm_eq_nnnorm]

@[simp]

Depends on / 依赖: enorm_eq_nnnorm
-/
theorem opENorm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : ‖f.flip‖ₑ = ‖f‖ₑ := by
  simp [enorm_eq_nnnorm]

@[simp]
/--
lemma `flip_zero` / 引理 `flip_zero`

English:
lemma flip_zero
  statement: flip (0 : E ->SL[σ₁₃] F ->SL[σ₂₃] G) = 0
  proof: rfl

@[simp]

中文:
引理 flip_zero
  结论: flip (0 : E ->SL[σ₁₃] F ->SL[σ₂₃] G) = 0
  证明: rfl

@[simp]
-/
lemma flip_zero : flip (0 : E ->SL[σ₁₃] F ->SL[σ₂₃] G) = 0 := rfl

@[simp]
/--
theorem `flip_add` / 定理 `flip_add`

English:
theorem flip_add
  given: (f g : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  statement: (f + g).flip = f.flip + g.flip
  proof: rfl

@[simp]

中文:
定理 flip_add
  条件: (f g : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  结论: (f + g).flip = f.flip + g.flip
  证明: rfl

@[simp]
-/
theorem flip_add (f g : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : (f + g).flip = f.flip + g.flip :=
  rfl

@[simp]
/--
theorem `flip_smul` / 定理 `flip_smul`

English:
theorem flip_smul
  given: (c : 𝕜₃) (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  statement: (c • f).flip = c • f.flip
  proof: rfl

中文:
定理 flip_smul
  条件: (c : 𝕜₃) (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
  结论: (c • f).flip = c • f.flip
  证明: rfl
-/
theorem flip_smul (c : 𝕜₃) (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : (c • f).flip = c • f.flip :=
  rfl

variable (E F G σ₁₃ σ₂₃)

/--
Definition of `flipₗᵢ'` / `flipₗᵢ'` 的定义

English:
definition flipₗᵢ'
  signature: : (E ->SL[σ₁₃] F ->SL[σ₂₃] G) ≃ₗᵢ[𝕜₃] F ->SL[σ₂₃] E ->SL[σ₁₃] G where
  body: flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip

中文:
定义 flipₗᵢ'
  签名: : (E ->SL[σ₁₃] F ->SL[σ₂₃] G) ≃ₗᵢ[𝕜₃] F ->SL[σ₂₃] E ->SL[σ₁₃] G where
  定义体: flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip
-/
def flipₗᵢ' : (E ->SL[σ₁₃] F ->SL[σ₂₃] G) ≃ₗᵢ[𝕜₃] F ->SL[σ₂₃] E ->SL[σ₁₃] G where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip

variable {E F G σ₁₃ σ₂₃}

@[simp]
/--
theorem `flipₗᵢ'_symm` / 定理 `flipₗᵢ'_symm`

English:
theorem flipₗᵢ'_symm
  statement: (flipₗᵢ' E F G σ₂₃ σ₁₃).symm = flipₗᵢ' F E G σ₁₃ σ₂₃
  proof: rfl

@[simp]

中文:
定理 flipₗᵢ'_symm
  结论: (flipₗᵢ' E F G σ₂₃ σ₁₃).symm = flipₗᵢ' F E G σ₁₃ σ₂₃
  证明: rfl

@[simp]
-/
theorem flipₗᵢ'_symm : (flipₗᵢ' E F G σ₂₃ σ₁₃).symm = flipₗᵢ' F E G σ₁₃ σ₂₃ :=
  rfl

@[simp]
/--
theorem `coe_flipₗᵢ'` / 定理 `coe_flipₗᵢ'`

English:
theorem coe_flipₗᵢ'
  statement: ⇑(flipₗᵢ' E F G σ₂₃ σ₁₃) = flip
  proof: rfl

中文:
定理 coe_flipₗᵢ'
  结论: ⇑(flipₗᵢ' E F G σ₂₃ σ₁₃) = flip
  证明: rfl
-/
theorem coe_flipₗᵢ' : ⇑(flipₗᵢ' E F G σ₂₃ σ₁₃) = flip :=
  rfl

variable (𝕜 E Fₗ Gₗ)

/--
Definition of `flipₗᵢ` / `flipₗᵢ` 的定义

English:
definition flipₗᵢ
  signature: : (E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) ≃ₗᵢ[𝕜] Fₗ ->L[𝕜] E ->L[𝕜] Gₗ where
  body: flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip

中文:
定义 flipₗᵢ
  签名: : (E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) ≃ₗᵢ[𝕜] Fₗ ->L[𝕜] E ->L[𝕜] Gₗ where
  定义体: flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip
-/
def flipₗᵢ : (E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) ≃ₗᵢ[𝕜] Fₗ ->L[𝕜] E ->L[𝕜] Gₗ where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip

variable {𝕜 E Fₗ Gₗ}

@[simp]
/--
theorem `flipₗᵢ_symm` / 定理 `flipₗᵢ_symm`

English:
theorem flipₗᵢ_symm
  statement: (flipₗᵢ 𝕜 E Fₗ Gₗ).symm = flipₗᵢ 𝕜 Fₗ E Gₗ
  proof: rfl

@[simp]

中文:
定理 flipₗᵢ_symm
  结论: (flipₗᵢ 𝕜 E Fₗ Gₗ).symm = flipₗᵢ 𝕜 Fₗ E Gₗ
  证明: rfl

@[simp]
-/
theorem flipₗᵢ_symm : (flipₗᵢ 𝕜 E Fₗ Gₗ).symm = flipₗᵢ 𝕜 Fₗ E Gₗ :=
  rfl

@[simp]
/--
theorem `coe_flipₗᵢ` / 定理 `coe_flipₗᵢ`

English:
theorem coe_flipₗᵢ
  statement: ⇑(flipₗᵢ 𝕜 E Fₗ Gₗ) = flip
  proof: rfl

中文:
定理 coe_flipₗᵢ
  结论: ⇑(flipₗᵢ 𝕜 E Fₗ Gₗ) = flip
  证明: rfl
-/
theorem coe_flipₗᵢ : ⇑(flipₗᵢ 𝕜 E Fₗ Gₗ) = flip :=
  rfl

variable (F σ₁₂)
variable [RingHomIsometric σ₁₂]

/--
Definition of `apply'` / `apply'` 的定义

English:
definition apply'
  signature: : E ->SL[σ₁₂] (E ->SL[σ₁₂] F) ->L[𝕜₂] F
  body: flip (.id 𝕜₂ (E ->SL[σ₁₂] F))

中文:
定义 apply'
  签名: : E ->SL[σ₁₂] (E ->SL[σ₁₂] F) ->L[𝕜₂] F
  定义体: flip (.id 𝕜₂ (E ->SL[σ₁₂] F))
-/
def apply' : E ->SL[σ₁₂] (E ->SL[σ₁₂] F) ->L[𝕜₂] F :=
  flip (.id 𝕜₂ (E ->SL[σ₁₂] F))

variable {F σ₁₂}

@[simp]
/--
theorem `apply_apply'` / 定理 `apply_apply'`

English:
theorem apply_apply'
  given: (v : E) (f : E ->SL[σ₁₂] F)
  statement: apply' F σ₁₂ v f = f v
  proof: rfl

中文:
定理 apply_apply'
  条件: (v : E) (f : E ->SL[σ₁₂] F)
  结论: apply' F σ₁₂ v f = f v
  证明: rfl
-/
theorem apply_apply' (v : E) (f : E ->SL[σ₁₂] F) : apply' F σ₁₂ v f = f v :=
  rfl

variable (𝕜 Fₗ)

/--
Definition of `apply` / `apply` 的定义

English:
definition apply
  signature: : E ->L[𝕜] (E ->L[𝕜] Fₗ) ->L[𝕜] Fₗ
  body: flip (.id 𝕜 (E ->L[𝕜] Fₗ))

中文:
定义 apply
  签名: : E ->L[𝕜] (E ->L[𝕜] Fₗ) ->L[𝕜] Fₗ
  定义体: flip (.id 𝕜 (E ->L[𝕜] Fₗ))
-/
def apply : E ->L[𝕜] (E ->L[𝕜] Fₗ) ->L[𝕜] Fₗ :=
  flip (.id 𝕜 (E ->L[𝕜] Fₗ))

variable {𝕜 Fₗ}

@[simp]
/--
theorem `apply_apply` / 定理 `apply_apply`

English:
theorem apply_apply
  given: (v : E) (f : E ->L[𝕜] Fₗ)
  statement: apply 𝕜 Fₗ v f = f v
  proof: rfl

中文:
定理 apply_apply
  条件: (v : E) (f : E ->L[𝕜] Fₗ)
  结论: apply 𝕜 Fₗ v f = f v
  证明: rfl
-/
theorem apply_apply (v : E) (f : E ->L[𝕜] Fₗ) : apply 𝕜 Fₗ v f = f v :=
  rfl

variable (σ₁₂ σ₂₃ E F G)


/--
Definition of `compSL` / `compSL` 的定义

English:
definition compSL
  signature: : (F ->SL[σ₂₃] G) ->L[𝕜₃] (E ->SL[σ₁₂] F) ->SL[σ₂₃] E ->SL[σ₁₃] G
  body: LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (RingHom.id 𝕜₃) σ₂₃ comp add_comp smul_comp comp_add fun c f g => by
      ext
      simp only [map_smulₛₗ, comp_apply, smul_apply])
    1 fun f g => by simpa only [one_mul] using! opNorm_comp_le f g

中文:
定义 compSL
  签名: : (F ->SL[σ₂₃] G) ->L[𝕜₃] (E ->SL[σ₁₂] F) ->SL[σ₂₃] E ->SL[σ₁₃] G
  定义体: LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (RingHom.id 𝕜₃) σ₂₃ comp add_comp smul_comp comp_add fun c f g => by
      ext
      simp only [map_smulₛₗ, comp_apply, smul_apply])
    1 fun f g => by simpa only [one_mul] using! opNorm_comp_le f g

Depends on / 依赖: LinearMap, LinearMap.mk, LinearMap.mkContinuous, RingHom, RingHom.id, add_comp, comp_add, comp_apply, one_mul, opNorm_comp_le, smul_apply, smul_comp
-/
def compSL : (F ->SL[σ₂₃] G) ->L[𝕜₃] (E ->SL[σ₁₂] F) ->SL[σ₂₃] E ->SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (RingHom.id 𝕜₃) σ₂₃ comp add_comp smul_comp comp_add fun c f g => by
      ext
      simp only [map_smulₛₗ, comp_apply, smul_apply])
    1 fun f g => by simpa only [one_mul] using! opNorm_comp_le f g

/--
theorem `norm_compSL_le` / 定理 `norm_compSL_le`

English:
theorem norm_compSL_le
  statement: ‖compSL E F G σ₁₂ σ₂₃‖ <= 1
  proof: LinearMap.mkContinuous₂_norm_le _ zero_le_one _

中文:
定理 norm_compSL_le
  结论: ‖compSL E F G σ₁₂ σ₂₃‖ <= 1
  证明: LinearMap.mkContinuous₂_norm_le _ zero_le_one _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, zero_le_one
-/
theorem norm_compSL_le : ‖compSL E F G σ₁₂ σ₂₃‖ <= 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

variable {σ₁₂ σ₂₃ E F G}

@[simp]
/--
theorem `compSL_apply` / 定理 `compSL_apply`

English:
theorem compSL_apply
  given: (f : F ->SL[σ₂₃] G) (g : E ->SL[σ₁₂] F)
  statement: compSL E F G σ₁₂ σ₂₃ f g = f.comp g
  proof: rfl

中文:
定理 compSL_apply
  条件: (f : F ->SL[σ₂₃] G) (g : E ->SL[σ₁₂] F)
  结论: compSL E F G σ₁₂ σ₂₃ f g = f.comp g
  证明: rfl
-/
theorem compSL_apply (f : F ->SL[σ₂₃] G) (g : E ->SL[σ₁₂] F) : compSL E F G σ₁₂ σ₂₃ f g = f.comp g :=
  rfl

/--
theorem `_root_.Continuous.const_clm_comp` / 定理 `_root_.Continuous.const_clm_comp`

English:
theorem _root_.Continuous.const_clm_comp
  statement: {X} [TopologicalSpace X] {f : X -> E ->SL[σ₁₂] F}
  proof: (compSL E F G σ₁₂ σ₂₃ g).continuous.comp hf

中文:
定理 _root_.Continuous.const_clm_comp
  结论: {X} [TopologicalSpace X] {f : X -> E ->SL[σ₁₂] F}
  证明: (compSL E F G σ₁₂ σ₂₃ g).continuous.comp hf

Depends on / 依赖: compSL, continuous, continuous.comp
-/
theorem _root_.Continuous.const_clm_comp {X} [TopologicalSpace X] {f : X -> E ->SL[σ₁₂] F}
    (hf : Continuous f) (g : F ->SL[σ₂₃] G) :
    Continuous (fun x => g.comp (f x) : X -> E ->SL[σ₁₃] G) :=
  (compSL E F G σ₁₂ σ₂₃ g).continuous.comp hf

-- Giving the implicit argument speeds up elaboration significantly
/--
theorem `_root_.Continuous.clm_comp_const` / 定理 `_root_.Continuous.clm_comp_const`

English:
theorem _root_.Continuous.clm_comp_const
  statement: {X} [TopologicalSpace X] {g : X -> F ->SL[σ₂₃] G}
  proof: (@ContinuousLinearMap.flip _ _ _ _ _ (E ->SL[σ₁₃] G) _ _ _ _ _ _ _ _ _ _ _ _ _
    (compSL E F G σ₁₂ σ₂₃) f).continuous.comp hg

中文:
定理 _root_.Continuous.clm_comp_const
  结论: {X} [TopologicalSpace X] {g : X -> F ->SL[σ₂₃] G}
  证明: (@ContinuousLinearMap.flip _ _ _ _ _ (E ->SL[σ₁₃] G) _ _ _ _ _ _ _ _ _ _ _ _ _
    (compSL E F G σ₁₂ σ₂₃) f).continuous.comp hg

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.flip, compSL, continuous, continuous.comp
-/
theorem _root_.Continuous.clm_comp_const {X} [TopologicalSpace X] {g : X -> F ->SL[σ₂₃] G}
    (hg : Continuous g) (f : E ->SL[σ₁₂] F) :
    Continuous (fun x => (g x).comp f : X -> E ->SL[σ₁₃] G) :=
  (@ContinuousLinearMap.flip _ _ _ _ _ (E ->SL[σ₁₃] G) _ _ _ _ _ _ _ _ _ _ _ _ _
    (compSL E F G σ₁₂ σ₂₃) f).continuous.comp hg

variable (𝕜 σ₁₂ σ₂₃ E Fₗ Gₗ)

/--
Definition of `compL` / `compL` 的定义

English:
definition compL
  signature: : (Fₗ ->L[𝕜] Gₗ) ->L[𝕜] (E ->L[𝕜] Fₗ) ->L[𝕜] E ->L[𝕜] Gₗ
  body: compSL E Fₗ Gₗ (RingHom.id 𝕜) (RingHom.id 𝕜)

中文:
定义 compL
  签名: : (Fₗ ->L[𝕜] Gₗ) ->L[𝕜] (E ->L[𝕜] Fₗ) ->L[𝕜] E ->L[𝕜] Gₗ
  定义体: compSL E Fₗ Gₗ (RingHom.id 𝕜) (RingHom.id 𝕜)

Depends on / 依赖: RingHom, RingHom.id, compSL
-/
def compL : (Fₗ ->L[𝕜] Gₗ) ->L[𝕜] (E ->L[𝕜] Fₗ) ->L[𝕜] E ->L[𝕜] Gₗ :=
  compSL E Fₗ Gₗ (RingHom.id 𝕜) (RingHom.id 𝕜)

/--
theorem `norm_compL_le` / 定理 `norm_compL_le`

English:
theorem norm_compL_le
  statement: ‖compL 𝕜 E Fₗ Gₗ‖ <= 1
  proof: norm_compSL_le _ _ _ _ _

@[simp]

中文:
定理 norm_compL_le
  结论: ‖compL 𝕜 E Fₗ Gₗ‖ <= 1
  证明: norm_compSL_le _ _ _ _ _

@[simp]

Depends on / 依赖: norm_compSL_le
-/
theorem norm_compL_le : ‖compL 𝕜 E Fₗ Gₗ‖ <= 1 :=
  norm_compSL_le _ _ _ _ _

@[simp]
/--
theorem `compL_apply` / 定理 `compL_apply`

English:
theorem compL_apply
  given: (f : Fₗ ->L[𝕜] Gₗ) (g : E ->L[𝕜] Fₗ)
  statement: compL 𝕜 E Fₗ Gₗ f g = f.comp g
  proof: rfl

中文:
定理 compL_apply
  条件: (f : Fₗ ->L[𝕜] Gₗ) (g : E ->L[𝕜] Fₗ)
  结论: compL 𝕜 E Fₗ Gₗ f g = f.comp g
  证明: rfl
-/
theorem compL_apply (f : Fₗ ->L[𝕜] Gₗ) (g : E ->L[𝕜] Fₗ) : compL 𝕜 E Fₗ Gₗ f g = f.comp g :=
  rfl

variable (Eₗ) {𝕜 E Fₗ Gₗ}

/-- Apply `L(x,-)` pointwise to bilinear maps, as a continuous bilinear map -/
@[simps! apply]
/--
Definition of `precompR` / `precompR` 的定义

English:
definition precompR
  signature: (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ)
  body: compL 𝕜 Eₗ Fₗ Gₗ ∘L L

中文:
定义 precompR
  签名: (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ)
  定义体: compL 𝕜 Eₗ Fₗ Gₗ ∘L L
-/
def precompR (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) : E ->L[𝕜] (Eₗ ->L[𝕜] Fₗ) ->L[𝕜] Eₗ ->L[𝕜] Gₗ :=
  compL 𝕜 Eₗ Fₗ Gₗ ∘L L

/--
Definition of `precompL` / `precompL` 的定义

English:
definition precompL
  signature: (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ)
  body: (precompR Eₗ (flip L)).flip

中文:
定义 precompL
  签名: (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ)
  定义体: (precompR Eₗ (flip L)).flip

Depends on / 依赖: precompR
-/
def precompL (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) : (Eₗ ->L[𝕜] E) ->L[𝕜] Fₗ ->L[𝕜] Eₗ ->L[𝕜] Gₗ :=
  (precompR Eₗ (flip L)).flip

/--
lemma `precompL_apply` / 引理 `precompL_apply`

English:
lemma precompL_apply
  given: (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) (u : Eₗ ->L[𝕜] E) (f : Fₗ) (g : Eₗ)
  proof: rfl

中文:
引理 precompL_apply
  条件: (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) (u : Eₗ ->L[𝕜] E) (f : Fₗ) (g : Eₗ)
  证明: rfl
-/
@[simp] lemma precompL_apply (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) (u : Eₗ ->L[𝕜] E) (f : Fₗ) (g : Eₗ) :
    precompL Eₗ L u f g = L (u g) f := rfl

/--
theorem `norm_precompR_le` / 定理 `norm_precompR_le`

English:
theorem norm_precompR_le
  given: (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ)
  statement: ‖precompR Eₗ L‖ <= ‖L‖
  proof: calc
    ‖precompR Eₗ L‖ <= ‖compL 𝕜 Eₗ Fₗ Gₗ‖ * ‖L‖ := opNorm_comp_le _ _
    _ <= 1 * ‖L‖ := by gcongr; apply norm_compL_le
    _ = ‖L‖ := by rw [one_mul]

中文:
定理 norm_precompR_le
  条件: (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ)
  结论: ‖precompR Eₗ L‖ <= ‖L‖
  证明: calc
    ‖precompR Eₗ L‖ <= ‖compL 𝕜 Eₗ Fₗ Gₗ‖ * ‖L‖ := opNorm_comp_le _ _
    _ <= 1 * ‖L‖ := by gcongr; apply norm_compL_le
    _ = ‖L‖ := by rw [one_mul]

Depends on / 依赖: norm_compL_le, one_mul, opNorm_comp_le, precompR
-/
theorem norm_precompR_le (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) : ‖precompR Eₗ L‖ <= ‖L‖ :=
  calc
    ‖precompR Eₗ L‖ <= ‖compL 𝕜 Eₗ Fₗ Gₗ‖ * ‖L‖ := opNorm_comp_le _ _
    _ <= 1 * ‖L‖ := by gcongr; apply norm_compL_le
    _ = ‖L‖ := by rw [one_mul]

/--
theorem `norm_precompL_le` / 定理 `norm_precompL_le`

English:
theorem norm_precompL_le
  given: (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ)
  statement: ‖precompL Eₗ L‖ <= ‖L‖
  proof: by
  rw [precompL]; rw [opNorm_flip]; rw [← opNorm_flip L]
  exact norm_precompR_le _ L.flip

中文:
定理 norm_precompL_le
  条件: (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ)
  结论: ‖precompL Eₗ L‖ <= ‖L‖
  证明: by
  rw [precompL]; rw [opNorm_flip]; rw [← opNorm_flip L]
  exact norm_precompR_le _ L.flip

Depends on / 依赖: L.flip, norm_precompR_le, opNorm_flip, precompL
-/
theorem norm_precompL_le (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) : ‖precompL Eₗ L‖ <= ‖L‖ := by
  rw [precompL]; rw [opNorm_flip]; rw [← opNorm_flip L]
  exact norm_precompR_le _ L.flip

end ContinuousLinearMap

variable {σ₂₁ : 𝕜₂ ->+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

namespace ContinuousLinearMap

variable {E' F' : Type*} [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F']
variable {𝕜₁' : Type*} {𝕜₂' : Type*} [NontriviallyNormedField 𝕜₁'] [NontriviallyNormedField 𝕜₂']
  [NormedSpace 𝕜₁' E'] [NormedSpace 𝕜₂' F'] {σ₁' : 𝕜₁' ->+* 𝕜} {σ₁₃' : 𝕜₁' ->+* 𝕜₃} {σ₂' : 𝕜₂' ->+* 𝕜₂}
  {σ₂₃' : 𝕜₂' ->+* 𝕜₃} [RingHomCompTriple σ₁' σ₁₃ σ₁₃'] [RingHomCompTriple σ₂' σ₂₃ σ₂₃']
  [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃'] [RingHomIsometric σ₂₃']

/--
Definition of `bilinearComp` / `bilinearComp` 的定义

English:
definition bilinearComp
  signature: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (gE : E' ->SL[σ₁'] E) (gF : F' ->SL[σ₂'] F)
  body: ((f.comp gE).flip.comp gF).flip

@[simp]

中文:
定义 bilinearComp
  签名: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (gE : E' ->SL[σ₁'] E) (gF : F' ->SL[σ₂'] F)
  定义体: ((f.comp gE).flip.comp gF).flip

@[simp]

Depends on / 依赖: f.comp, flip.comp
-/
def bilinearComp (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (gE : E' ->SL[σ₁'] E) (gF : F' ->SL[σ₂'] F) :
    E' ->SL[σ₁₃'] F' ->SL[σ₂₃'] G :=
  ((f.comp gE).flip.comp gF).flip

@[simp]
/--
theorem `bilinearComp_apply` / 定理 `bilinearComp_apply`

English:
theorem bilinearComp_apply
  statement: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (gE : E' ->SL[σ₁'] E) (gF : F' ->SL[σ₂'] F)
  proof: rfl

@[simp]

中文:
定理 bilinearComp_apply
  结论: (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (gE : E' ->SL[σ₁'] E) (gF : F' ->SL[σ₂'] F)
  证明: rfl

@[simp]
-/
theorem bilinearComp_apply (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (gE : E' ->SL[σ₁'] E) (gF : F' ->SL[σ₂'] F)
    (x : E') (y : F') : f.bilinearComp gE gF x y = f (gE x) (gF y) :=
  rfl

@[simp]
/--
lemma `bilinearComp_zero` / 引理 `bilinearComp_zero`

English:
lemma bilinearComp_zero
  given: {gE : E' ->SL[σ₁'] E} {gF : F' ->SL[σ₂'] F}
  proof: rfl

@[simp]

中文:
引理 bilinearComp_zero
  条件: {gE : E' ->SL[σ₁'] E} {gF : F' ->SL[σ₂'] F}
  证明: rfl

@[simp]
-/
lemma bilinearComp_zero {gE : E' ->SL[σ₁'] E} {gF : F' ->SL[σ₂'] F} :
    bilinearComp (0 : E ->SL[σ₁₃] F ->SL[σ₂₃] G) gE gF = 0 := rfl

@[simp]
/--
lemma `bilinearComp_zero_left` / 引理 `bilinearComp_zero_left`

English:
lemma bilinearComp_zero_left
  given: {f : E ->SL[σ₁₃] F ->SL[σ₂₃] G} {gF : F' ->SL[σ₂'] F}
  proof: by ext; simp

@[simp]

中文:
引理 bilinearComp_zero_left
  条件: {f : E ->SL[σ₁₃] F ->SL[σ₂₃] G} {gF : F' ->SL[σ₂'] F}
  证明: by ext; simp

@[simp]
-/
lemma bilinearComp_zero_left {f : E ->SL[σ₁₃] F ->SL[σ₂₃] G} {gF : F' ->SL[σ₂'] F} :
    bilinearComp f (0 : E' ->SL[σ₁'] E) gF = 0 := by ext; simp

@[simp]
/--
lemma `bilinearComp_zero_right` / 引理 `bilinearComp_zero_right`

English:
lemma bilinearComp_zero_right
  given: {f : E ->SL[σ₁₃] F ->SL[σ₂₃] G} {gE : E' ->SL[σ₁'] E}
  proof: by ext; simp

中文:
引理 bilinearComp_zero_right
  条件: {f : E ->SL[σ₁₃] F ->SL[σ₂₃] G} {gE : E' ->SL[σ₁'] E}
  证明: by ext; simp
-/
lemma bilinearComp_zero_right {f : E ->SL[σ₁₃] F ->SL[σ₂₃] G} {gE : E' ->SL[σ₁'] E} :
    bilinearComp f gE (0 : F' ->SL[σ₂'] F) = 0 := by ext; simp

variable [RingHomIsometric σ₁₃] [RingHomIsometric σ₁'] [RingHomIsometric σ₂']

/--
Definition of `deriv₂` / `deriv₂` 的定义

English:
definition deriv₂
  signature: (f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ)
  body: f.bilinearComp (fst _ _ _) (snd _ _ _) + f.flip.bilinearComp (snd _ _ _) (fst _ _ _)

@[simp]

中文:
定义 deriv₂
  签名: (f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ)
  定义体: f.bilinearComp (fst _ _ _) (snd _ _ _) + f.flip.bilinearComp (snd _ _ _) (fst _ _ _)

@[simp]

Depends on / 依赖: bilinearComp, f.bilinearComp, f.flip.bilinearComp
-/
def deriv₂ (f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) : E × Fₗ ->L[𝕜] E × Fₗ ->L[𝕜] Gₗ :=
  f.bilinearComp (fst _ _ _) (snd _ _ _) + f.flip.bilinearComp (snd _ _ _) (fst _ _ _)

@[simp]
/--
theorem `coe_deriv₂` / 定理 `coe_deriv₂`

English:
theorem coe_deriv₂
  given: (f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) (p : E × Fₗ)
  proof: rfl

中文:
定理 coe_deriv₂
  条件: (f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) (p : E × Fₗ)
  证明: rfl
-/
theorem coe_deriv₂ (f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) (p : E × Fₗ) :
    ⇑(f.deriv₂ p) = fun q : E × Fₗ => f p.1 q.2 + f q.1 p.2 :=
  rfl

/--
theorem `map_add_add` / 定理 `map_add_add`

English:
theorem map_add_add
  given: (f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) (x x' : E) (y y' : Fₗ)
  proof: by
  simp only [map_add, add_apply, coe_deriv₂, add_assoc]
  abel

中文:
定理 map_add_add
  条件: (f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) (x x' : E) (y y' : Fₗ)
  证明: by
  simp only [map_add, add_apply, coe_deriv₂, add_assoc]
  abel

Depends on / 依赖: add_apply, add_assoc, map_add
-/
theorem map_add_add (f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) (x x' : E) (y y' : Fₗ) :
    f (x + x') (y + y') = f x y + f.deriv₂ (x, y) (x', y') + f x' y' := by
  simp only [map_add, add_apply, coe_deriv₂, add_assoc]
  abel

/-- The norm of the tensor product of a scalar linear map and of an element of a normed space
is the product of the norms. -/
@[simp]
/--
theorem `norm_smulRight_apply` / 定理 `norm_smulRight_apply`

English:
theorem norm_smulRight_apply
  given: (c : StrongDual 𝕜 E) (f : Fₗ)
  statement: ‖smulRight c f‖ = ‖c‖ * ‖f‖
  proof: by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound _ (by positivity) fun x => ?_
    calc
      ‖c x • f‖ = ‖c x‖ * ‖f‖ := norm_smul _ _
      _ <= ‖c‖ * ‖x‖ * ‖f‖ := by gcongr; apply le_opNorm
      _ = ‖c‖ * ‖f‖ * ‖x‖ := by ring
  · obtain hf | hf := (norm_nonneg f).eq_or_lt'
    · simp [hf]

中文:
定理 norm_smulRight_apply
  条件: (c : StrongDual 𝕜 E) (f : Fₗ)
  结论: ‖smulRight c f‖ = ‖c‖ * ‖f‖
  证明: by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound _ (by positivity) fun x => ?_
    calc
      ‖c x • f‖ = ‖c x‖ * ‖f‖ := norm_smul _ _
      _ <= ‖c‖ * ‖x‖ * ‖f‖ := by gcongr; apply le_opNorm
      _ = ‖c‖ * ‖f‖ * ‖x‖ := by ring
  · obtain hf | hf := (norm_nonneg f).eq_or_lt'
    · simp [hf]

Depends on / 依赖: div_mul_eq_mul_div, eq_or_lt, le_antisymm, le_opNorm, norm_nonneg, norm_smul, opNorm_le_bound, smulRight
-/
theorem norm_smulRight_apply (c : StrongDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖ := by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound _ (by positivity) fun x => ?_
    calc
      ‖c x • f‖ = ‖c x‖ * ‖f‖ := norm_smul _ _
      _ <= ‖c‖ * ‖x‖ * ‖f‖ := by gcongr; apply le_opNorm
      _ = ‖c‖ * ‖f‖ * ‖x‖ := by ring
  · obtain hf | hf := (norm_nonneg f).eq_or_lt'
    · simp [hf]
    · rw [← le_div_iff₀ hf]
      refine opNorm_le_bound _ (by positivity) fun x => ?_
      rw [div_mul_eq_mul_div]; rw [le_div_iff₀ hf]
      calc
        ‖c x‖ * ‖f‖ = ‖c x • f‖ := (norm_smul _ _).symm
        _ = ‖smulRight c f x‖ := rfl
        _ <= ‖smulRight c f‖ * ‖x‖ := le_opNorm _ _

/-- The non-negative norm of the tensor product of a scalar linear map and of an element of a normed
space is the product of the non-negative norms. -/
@[simp]
/--
theorem `nnnorm_smulRight_apply` / 定理 `nnnorm_smulRight_apply`

English:
theorem nnnorm_smulRight_apply
  given: (c : StrongDual 𝕜 E) (f : Fₗ)
  statement: ‖smulRight c f‖₊ = ‖c‖₊ * ‖f‖₊
  proof: NNReal.eq c.norm_smulRight_apply f

中文:
定理 nnnorm_smulRight_apply
  条件: (c : StrongDual 𝕜 E) (f : Fₗ)
  结论: ‖smulRight c f‖₊ = ‖c‖₊ * ‖f‖₊
  证明: NNReal.eq c.norm_smulRight_apply f

Depends on / 依赖: NNReal, NNReal.eq, c.norm_smulRight_apply, norm_smulRight_apply
-/
theorem nnnorm_smulRight_apply (c : StrongDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖₊ = ‖c‖₊ * ‖f‖₊ :=
NNReal.eq c.norm_smulRight_apply f

/--
theorem `norm_toSpanSingleton` / 定理 `norm_toSpanSingleton`

English:
theorem norm_toSpanSingleton
  given: (x : E)
  statement: ‖toSpanSingleton 𝕜 x‖ = ‖x‖
  proof: by
  simp [← smulRight_id, norm_id]

中文:
定理 norm_toSpanSingleton
  条件: (x : E)
  结论: ‖toSpanSingleton 𝕜 x‖ = ‖x‖
  证明: by
  simp [← smulRight_id, norm_id]
-/
@[simp] theorem norm_toSpanSingleton (x : E) : ‖toSpanSingleton 𝕜 x‖ = ‖x‖ := by
  simp [← smulRight_id, norm_id]

/--
theorem `nnnorm_toSpanSingleton` / 定理 `nnnorm_toSpanSingleton`

English:
theorem nnnorm_toSpanSingleton
  given: (x : E)
  statement: ‖toSpanSingleton 𝕜 x‖₊ = ‖x‖₊
  proof: NNReal.eq norm_toSpanSingleton _

中文:
定理 nnnorm_toSpanSingleton
  条件: (x : E)
  结论: ‖toSpanSingleton 𝕜 x‖₊ = ‖x‖₊
  证明: NNReal.eq norm_toSpanSingleton _
-/
@[simp] theorem nnnorm_toSpanSingleton (x : E) : ‖toSpanSingleton 𝕜 x‖₊ = ‖x‖₊ :=
NNReal.eq norm_toSpanSingleton _

variable (𝕜 E Fₗ) in
/-- `ContinuousLinearMap.smulRight` as a continuous trilinear map:
`smulRightL (c : StrongDual 𝕜 E) (f : F) (x : E) = c x • f`.

This is also known as a rank-one operator.
See also `InnerProductSpace.rankOne` for the rank-one operator on Hilbert spaces. -/
@[simps! apply_apply]
/--
Definition of `smulRightL` / `smulRightL` 的定义

English:
definition smulRightL
  signature: : StrongDual 𝕜 E ->L[𝕜] Fₗ ->L[𝕜] E ->L[𝕜] Fₗ
  body: LinearMap.mkContinuous₂
    { toFun := smulRightₗ
      map_add' := fun c₁ c₂ => by
        ext x
        simp only [add_smul, coe_smulRightₗ, add_apply, smulRight_apply, LinearMap.add_apply]
      map_smul' := fun m c => by
        ext x
        simp [smul_smul] }
    1 fun c x => by
      simp onl

中文:
定义 smulRightL
  签名: : StrongDual 𝕜 E ->L[𝕜] Fₗ ->L[𝕜] E ->L[𝕜] Fₗ
  定义体: LinearMap.mkContinuous₂
    { toFun := smulRightₗ
      map_add' := fun c₁ c₂ => by
        ext x
        simp only [add_smul, coe_smulRightₗ, add_apply, smulRight_apply, LinearMap.add_apply]
      map_smul' := fun m c => by
        ext x
        simp [smul_smul] }
    1 fun c x => by
      simp onl

Depends on / 依赖: AddHom, AddHom.coe_mk, LinearMap, LinearMap.add_apply, LinearMap.coe_mk, LinearMap.mkContinuous, add_apply, add_smul, coe_mk, le_refl, map_add, map_smul, norm_smulRight_apply, one_mul, smulRight_apply, smul_smul
-/
def smulRightL : StrongDual 𝕜 E ->L[𝕜] Fₗ ->L[𝕜] E ->L[𝕜] Fₗ :=
  LinearMap.mkContinuous₂
    { toFun := smulRightₗ
      map_add' := fun c₁ c₂ => by
        ext x
        simp only [add_smul, coe_smulRightₗ, add_apply, smulRight_apply, LinearMap.add_apply]
      map_smul' := fun m c => by
        ext x
        simp [smul_smul] }
    1 fun c x => by
      simp only [coe_smulRightₗ, one_mul, norm_smulRight_apply, LinearMap.coe_mk, AddHom.coe_mk,
        le_refl]

end ContinuousLinearMap

end SemiNormed

section Restrict

namespace ContinuousLinearMap

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [IsScalarTower 𝕜 𝕜' G]

variable (𝕜) in
/--
Definition of `bilinearRestrictScalars` / `bilinearRestrictScalars` 的定义

English:
definition bilinearRestrictScalars
  signature: (B : E ->L[𝕜'] F ->L[𝕜'] G)
  body: (restrictScalarsL 𝕜' F G 𝕜 𝕜).comp (B.restrictScalars 𝕜)

中文:
定义 bilinearRestrictScalars
  签名: (B : E ->L[𝕜'] F ->L[𝕜'] G)
  定义体: (restrictScalarsL 𝕜' F G 𝕜 𝕜).comp (B.restrictScalars 𝕜)

Depends on / 依赖: B.restrictScalars, restrictScalars, restrictScalarsL
-/
def bilinearRestrictScalars (B : E ->L[𝕜'] F ->L[𝕜'] G) : E ->L[𝕜] F ->L[𝕜] G :=
  (restrictScalarsL 𝕜' F G 𝕜 𝕜).comp (B.restrictScalars 𝕜)

variable (B : E ->L[𝕜'] F ->L[𝕜'] G) (x : E) (y : F)

/--
theorem `bilinearRestrictScalars_eq_restrictScalarsL_comp_restrictScalars` / 定理 `bilinearRestrictScalars_eq_restrictScalarsL_comp_restrictScalars`

English:
theorem bilinearRestrictScalars_eq_restrictScalarsL_comp_restrictScalars
  proof: rfl

中文:
定理 bilinearRestrictScalars_eq_restrictScalarsL_comp_restrictScalars
  证明: rfl
-/
theorem bilinearRestrictScalars_eq_restrictScalarsL_comp_restrictScalars :
    B.bilinearRestrictScalars 𝕜 = (restrictScalarsL 𝕜' F G 𝕜 𝕜).comp (B.restrictScalars 𝕜) := rfl

/--
theorem `bilinearRestrictScalars_eq_restrictScalars_restrictScalarsL_comp` / 定理 `bilinearRestrictScalars_eq_restrictScalars_restrictScalarsL_comp`

English:
theorem bilinearRestrictScalars_eq_restrictScalars_restrictScalarsL_comp
  proof: rfl

中文:
定理 bilinearRestrictScalars_eq_restrictScalars_restrictScalarsL_comp
  证明: rfl
-/
theorem bilinearRestrictScalars_eq_restrictScalars_restrictScalarsL_comp :
    B.bilinearRestrictScalars 𝕜 = restrictScalars 𝕜 ((restrictScalarsL 𝕜' F G 𝕜 𝕜').comp B) := rfl

variable (𝕜) in
@[simp]
/--
theorem `bilinearRestrictScalars_apply_apply` / 定理 `bilinearRestrictScalars_apply_apply`

English:
theorem bilinearRestrictScalars_apply_apply
  statement: (B.bilinearRestrictScalars 𝕜) x y = B x y
  proof: rfl

@[simp]

中文:
定理 bilinearRestrictScalars_apply_apply
  结论: (B.bilinearRestrictScalars 𝕜) x y = B x y
  证明: rfl

@[simp]
-/
theorem bilinearRestrictScalars_apply_apply : (B.bilinearRestrictScalars 𝕜) x y = B x y := rfl

@[simp]
/--
theorem `norm_bilinearRestrictScalars` / 定理 `norm_bilinearRestrictScalars`

English:
theorem norm_bilinearRestrictScalars
  statement: ‖B.bilinearRestrictScalars 𝕜‖ = ‖B‖
  proof: rfl

中文:
定理 norm_bilinearRestrictScalars
  结论: ‖B.bilinearRestrictScalars 𝕜‖ = ‖B‖
  证明: rfl
-/
theorem norm_bilinearRestrictScalars : ‖B.bilinearRestrictScalars 𝕜‖ = ‖B‖ := rfl

end ContinuousLinearMap

end Restrict
