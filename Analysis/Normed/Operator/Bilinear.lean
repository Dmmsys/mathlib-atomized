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
  [NormedSpace 𝕜 Gₗ] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [FunLike 𝓕 E F]

namespace ContinuousLinearMap

section OpNorm

open Set Real

/-
**ContinuousLinearMap.opNorm_ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：opNorm_ext [RingHomIsometric σ₁₃] (f : E ->SL[σ₁₂] F) (g : E ->SL[σ₁₃] G) 
(h : forall x, ‖f x‖ = ‖g x‖) : ‖f‖ = ‖g‖
参数：f : E ->SL[σ₁₂] F；g : E ->SL[σ₁₃] G；h : forall x, ‖f x‖ = ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_eq_of_bounds`：opNorm_eq_of_bounds {φ : E ->SL
[σ₁₂] F} {M : Real} (M_nonneg : 0 <= M) (h_above : forall x, ‖φ x‖ <= M * ‖x‖) (
h_below : forall N >= 0, (for…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem opNorm_ext [RingHomIsometric σ₁₃] (f : E →SL[σ₁₂] F) (g : E →SL[σ₁₃] G)
    (h : ∀ x, ‖f x‖ = ‖g x‖) : ‖f‖ = ‖g‖ :=
  opNorm_eq_of_bounds (norm_nonneg _)
    (fun x => by
      rw [h x]
      exact le_opNorm _ _)
    fun c hc h₂ =>
    opNorm_le_bound _ hc fun z => by
      rw [← h z]
      exact h₂ z

variable [RingHomIsometric σ₂₃]
/-
**ContinuousLinearMap.opNorm_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：opNorm_le_bound (f : E ->SL[σ₁₂] F) {M : Real} (hMp : 0 <= M) (hM : forall
 x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
参数：f : E ->SL[σ₁₂] F；hMp : 0 <= M；hM : forall x, ‖f x‖ <= M * ‖x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `ContinuousLinearMap.bounds_bddBelow`：bounds_bddBelow {f : E ->SL[σ₁₂] F}
 : BddBelow { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
-/
theorem opNorm_le_bound₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f‖ ≤ C :=
  f.opNorm_le_bound h0 fun x => (f x).opNorm_le_bound (by positivity) <| hC x
/-
**ContinuousLinearMap.le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContinuousLinearMap.isLeast_opNorm`：isLeast_opNorm [RingHomIsometric σ₁₂
] (f : E ->SL[σ₁₂] F) : IsLeast {c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖} ‖f‖
-/
theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
    ‖f x y‖ ≤ ‖f‖ * ‖x‖ * ‖y‖ :=
  (f x).le_of_opNorm_le (f.le_opNorm x) y
/-
**ContinuousLinearMap.le_of_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_of_opNorm₂_le_of_le [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {x : E} {y : F}
    {a b c : ℝ} (hf : ‖f‖ ≤ a) (hx : ‖x‖ ≤ b) (hy : ‖y‖ ≤ c) :
    ‖f x y‖ ≤ a * b * c :=
  (f x).le_of_opNorm_le_of_le (f.le_of_opNorm_le_of_le hf hx) hy

open scoped ENNReal
/-
**ContinuousLinearMap.opENorm_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：opENorm_le_bound (f : E ->SL[σ₁₂] F) {M : Real>=0∞} (hM : forall x, ‖f x‖ₑ
 <= M * ‖x‖ₑ) : ‖f‖ₑ <= M
参数：f : E ->SL[σ₁₂] F；hM : forall x, ‖f x‖ₑ <= M * ‖x‖ₑ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem opENorm_le_bound₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {C : ℝ≥0∞}
    (hC : ∀ x y, ‖f x y‖ₑ ≤ C * ‖x‖ₑ * ‖y‖ₑ) : ‖f‖ₑ ≤ C :=
  f.opENorm_le_bound fun x => (f x).opENorm_le_bound <| hC x
/-
**ContinuousLinearMap.le_opENorm** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：le_opENorm (f : E ->SL[σ₁₂] F) (x : E) : ‖f x‖ₑ <= ‖f‖ₑ * ‖x‖ₑ
参数：f : E ->SL[σ₁₂] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.le_opNNNorm`：le_opNNNorm (f : E ->SL[σ₁₂] F) (x : E)
 : ‖f x‖₊ <= ‖f‖₊ * ‖x‖₊
-/
theorem le_opENorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
    ‖f x y‖ₑ ≤ ‖f‖ₑ * ‖x‖ₑ * ‖y‖ₑ :=
  (f x).le_of_opENorm_le (f.le_opENorm x) y

end OpNorm

end ContinuousLinearMap

namespace LinearMap

/-
**LinearMap.norm_mkContinuous** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_mkContinuous₂_aux (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ)
    (h : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) :
    ‖(f x).mkContinuous (C * ‖x‖) (h x)‖ ≤ max C 0 * ‖x‖ :=
  (mkContinuous_norm_le' (f x) (h x)).trans_eq <| by
    rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

variable [RingHomIsometric σ₂₃]

/-- Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corresponding linear
map and existence of a bound on the norm of the image. The linear map can be constructed using
`LinearMap.mk₂`.

If you have an explicit bound, use `LinearMap.mkContinuous₂` instead, as a norm estimate will
follow automatically in `LinearMap.mkContinuous₂_norm_le`. -/
/-
**LinearMap.mkContinuousOfExistsBound** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.mkContinuousOfExistsBound (h : exists C, forall x, ‖f x‖ <= C * 
‖x‖) : E ->SL[σ] F
参数：h : exists C, forall x, ‖f x‖ <= C * ‖x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corres
ponding linear
map and existence of a bound on the norm of the image. The linear map can be con
structed using
`LinearMap.mk₂`.

If you have an explicit bound, use `LinearMap.mkContinuous₂` instead, as a norm 
estimate will
follow automatically in `LinearMap.mkContinuous₂_norm_le`.
-/
def mkContinuousOfExistsBound₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G)
    (h : ∃ C, ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : E →SL[σ₁₃] F →SL[σ₂₃] G :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun x => (f x).mkContinuousOfExistsBound <| let ⟨C, hC⟩ := h; ⟨C * ‖x‖, hC x⟩
      map_add' := fun x y => by
        ext z
        simp
      map_smul' := fun c x => by
        ext z
        simp } <|
    let ⟨C, hC⟩ := h; ⟨max C 0, norm_mkContinuous₂_aux f C hC⟩

/-- Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corresponding linear
map and a bound on the norm of the image. The linear map can be constructed using
`LinearMap.mk₂`. Lemmas `LinearMap.mkContinuous₂_norm_le'` and `LinearMap.mkContinuous₂_norm_le`
provide estimates on the norm of an operator constructed using this function. -/
/-
**LinearMap.mkContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.mkContinuous (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) : E ->S
L[σ] F
参数：C : Real；h : forall x, ‖f x‖ <= C * ‖x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a bilinear map (represented as a map `E →L[𝕜] F →L[𝕜] G`) from the corres
ponding linear
map and a bound on the norm of the image. The linear map can be constructed usin
g
`LinearMap.mk₂`. Lemmas `LinearMap.mkContinuous₂_norm_le'` and `LinearMap.mkCont
inuous₂_norm_le`
provide estimates on the norm of an operator constructed using this function.
-/
def mkContinuous₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
    E →SL[σ₁₃] F →SL[σ₂₃] G :=
  mkContinuousOfExistsBound₂ f ⟨C, hC⟩

@[simp]
/-
**LinearMap.mkContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.mkContinuous (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) : E ->S
L[σ] F
参数：C : Real；h : forall x, ‖f x‖ <= C * ‖x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkContinuous₂_apply (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) (x : E) (y : F) : f.mkContinuous₂ C hC x y = f x y :=
  rfl
/-
**LinearMap.mkContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.mkContinuous (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) : E ->S
L[σ] F
参数：C : Real；h : forall x, ‖f x‖ <= C * ‖x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkContinuous₂_norm_le' (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ max C 0 :=
  mkContinuous_norm_le _ (le_max_iff.2 <| Or.inr le_rfl) (norm_mkContinuous₂_aux f C hC)
/-
**LinearMap.mkContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.mkContinuous (C : Real) (h : forall x, ‖f x‖ <= C * ‖x‖) : E ->S
L[σ] F
参数：C : Real；h : forall x, ‖f x‖ <= C * ‖x‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkContinuous₂_norm_le (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
    (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) : ‖f.mkContinuous₂ C hC‖ ≤ C :=
  (f.mkContinuous₂_norm_le' hC).trans_eq <| max_eq_left h0

end LinearMap

namespace ContinuousLinearMap

variable [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]

/-- Flip the order of arguments of a continuous bilinear map.
For a version bundled as `LinearIsometryEquiv`, see
`ContinuousLinearMap.flipL`. -/
/-
**ContinuousLinearMap.flip** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : F ->SL[σ₂₃] E ->SL[σ₁₃] G
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Flip the order of arguments of a continuous bilinear map.
For a version bundled as `LinearIsometryEquiv`, see
`ContinuousLinearMap.flipL`.
-/
def flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : F →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ σ₂₃ σ₁₃ (fun y x => f x y) (fun x y z => (f z).map_add x y)
      (fun c y x => (f x).map_smulₛₗ c y) (fun z x y => by simp only [f.map_add, add_apply])
        (fun c y x => by simp only [f.map_smulₛₗ, smul_apply]))
    ‖f‖ fun y x => (f.le_opNorm₂ x y).trans_eq <| by simp only [mul_right_comm]
/-
**ContinuousLinearMap.le_norm_flip** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem le_norm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f‖ ≤ ‖flip f‖ :=
  f.opNorm_le_bound₂ (norm_nonneg f.flip) fun x y => by
    rw [mul_right_comm]
    exact (flip f).le_opNorm₂ y x

@[simp]
/-
**ContinuousLinearMap.flip_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：flip_apply (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : f.flip y x = 
f x y
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G；x : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem flip_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) : f.flip y x = f x y :=
  rfl

@[simp]
/-
**ContinuousLinearMap.flip_flip** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：flip_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : f.flip.flip = f
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
theorem flip_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : f.flip.flip = f := by
  ext
  rfl

@[simp]
/-
**ContinuousLinearMap.opNorm_flip** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：opNorm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : ‖f.flip‖ = ‖f‖
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.flip_flip`：flip_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
 : f.flip.flip = f
· 使用定理 `_private.Mathlib.Analysis.Normed.Operator.Bilinear.0.ContinuousLinearMap
.le_norm_flip`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {𝕜₃ : Type u_3} {E : Type u_4} {
F : Type u_6} {G : Type u_8}   [inst : SeminormedAddCommGroup E] [inst_1 : …
-/
theorem opNorm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f.flip‖ = ‖f‖ :=
  le_antisymm (by simpa only [flip_flip] using le_norm_flip f.flip) (le_norm_flip f)

@[simp]
/-
**ContinuousLinearMap.opNNNorm_flip** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：opNNNorm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : ‖f.flip‖₊ = ‖f‖₊
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNorm_flip`：opNorm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃
] G) : ‖f.flip‖ = ‖f‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opNNNorm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f.flip‖₊ = ‖f‖₊ := by
  simp [← NNReal.coe_inj]

@[simp]
/-
**ContinuousLinearMap.opENorm_flip** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：opENorm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : ‖f.flip‖ₑ = ‖f‖ₑ
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNNNorm_flip`：opNNNorm_flip (f : E ->SL[σ₁₃] F ->SL
[σ₂₃] G) : ‖f.flip‖₊ = ‖f‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opENorm_flip (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : ‖f.flip‖ₑ = ‖f‖ₑ := by
  simp [enorm_eq_nnnorm]

@[simp]
/-
**ContinuousLinearMap.flip_zero** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：flip_zero : flip (0 : E ->SL[σ₁₃] F ->SL[σ₂₃] G) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma flip_zero : flip (0 : E →SL[σ₁₃] F →SL[σ₂₃] G) = 0 := rfl

@[simp]
/-
**ContinuousLinearMap.flip_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：flip_add (f g : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : (f + g).flip = f.flip + g.fli
p
参数：f g : E ->SL[σ₁₃] F ->SL[σ₂₃] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem flip_add (f g : E →SL[σ₁₃] F →SL[σ₂₃] G) : (f + g).flip = f.flip + g.flip :=
  rfl

@[simp]
/-
**ContinuousLinearMap.flip_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：flip_smul (c : 𝕜₃) (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : (c • f).flip = c • f.
flip
参数：c : 𝕜₃；f : E ->SL[σ₁₃] F ->SL[σ₂₃] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem flip_smul (c : 𝕜₃) (f : E →SL[σ₁₃] F →SL[σ₂₃] G) : (c • f).flip = c • f.flip :=
  rfl

variable (E F G σ₁₃ σ₂₃)

/-- Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `LinearIsometryEquiv`.
For an unbundled version see `ContinuousLinearMap.flip`. -/
/-
**ContinuousLinearMap.flip** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : F ->SL[σ₂₃] E ->SL[σ₁₃] G
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `LinearIsometryEquiv`.
For an unbundled version see `ContinuousLinearMap.flip`.
-/
def flipₗᵢ' : (E →SL[σ₁₃] F →SL[σ₂₃] G) ≃ₗᵢ[𝕜₃] F →SL[σ₂₃] E →SL[σ₁₃] G where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip

variable {E F G σ₁₃ σ₂₃}

@[simp]
/-
**ContinuousLinearMap.flip** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : F ->SL[σ₂₃] E ->SL[σ₁₃] G
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem flipₗᵢ'_symm : (flipₗᵢ' E F G σ₂₃ σ₁₃).symm = flipₗᵢ' F E G σ₁₃ σ₂₃ :=
  rfl

@[simp]
/-
**ContinuousLinearMap.coe_flip** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_flipₗᵢ' : ⇑(flipₗᵢ' E F G σ₂₃ σ₁₃) = flip :=
  rfl

variable (𝕜 E Fₗ Gₗ)

/-- Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `LinearIsometryEquiv`.
For an unbundled version see `ContinuousLinearMap.flip`. -/
/-
**ContinuousLinearMap.flip** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : F ->SL[σ₂₃] E ->SL[σ₁₃] G
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Flip the order of arguments of a continuous bilinear map.
This is a version bundled as a `LinearIsometryEquiv`.
For an unbundled version see `ContinuousLinearMap.flip`.
-/
def flipₗᵢ : (E →L[𝕜] Fₗ →L[𝕜] Gₗ) ≃ₗᵢ[𝕜] Fₗ →L[𝕜] E →L[𝕜] Gₗ where
  toFun := flip
  invFun := flip
  map_add' := flip_add
  map_smul' := flip_smul
  left_inv := flip_flip
  right_inv := flip_flip
  norm_map' := opNorm_flip

variable {𝕜 E Fₗ Gₗ}

@[simp]
/-
**ContinuousLinearMap.flip** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) : F ->SL[σ₂₃] E ->SL[σ₁₃] G
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem flipₗᵢ_symm : (flipₗᵢ 𝕜 E Fₗ Gₗ).symm = flipₗᵢ 𝕜 Fₗ E Gₗ :=
  rfl

@[simp]
/-
**ContinuousLinearMap.coe_flip** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_flipₗᵢ : ⇑(flipₗᵢ 𝕜 E Fₗ Gₗ) = flip :=
  rfl

variable (F σ₁₂)
variable [RingHomIsometric σ₁₂]

/-- The continuous semilinear map obtained by applying a continuous semilinear map at a given
vector.

This is the continuous version of `LinearMap.applyₗ`. -/
/-
**ContinuousLinearMap.apply'** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：apply' : E ->SL[σ₁₂] (E ->SL[σ₁₂] F) ->L[𝕜₂] F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
The continuous semilinear map obtained by applying a continuous semilinear map a
t a given
vector.

This is the continuous version of `LinearMap.applyₗ`.
-/
def apply' : E →SL[σ₁₂] (E →SL[σ₁₂] F) →L[𝕜₂] F :=
  flip (.id 𝕜₂ (E →SL[σ₁₂] F))

variable {F σ₁₂}

@[simp]
/-
**ContinuousLinearMap.apply_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：apply_apply' (v : E) (f : E ->SL[σ₁₂] F) : apply' F σ₁₂ v f = f v
参数：v : E；f : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem apply_apply' (v : E) (f : E →SL[σ₁₂] F) : apply' F σ₁₂ v f = f v :=
  rfl

variable (𝕜 Fₗ)

/-- The continuous semilinear map obtained by applying a continuous semilinear map at a given
vector.

This is the continuous version of `LinearMap.applyₗ`. -/
/-
**ContinuousLinearMap.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：apply : E ->L[𝕜] (E ->L[𝕜] Fₗ) ->L[𝕜] Fₗ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
The continuous semilinear map obtained by applying a continuous semilinear map a
t a given
vector.

This is the continuous version of `LinearMap.applyₗ`.
-/
def apply : E →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] Fₗ :=
  flip (.id 𝕜 (E →L[𝕜] Fₗ))

variable {𝕜 Fₗ}

@[simp]
/-
**ContinuousLinearMap.apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：apply_apply (v : E) (f : E ->L[𝕜] Fₗ) : apply 𝕜 Fₗ v f = f v
参数：v : E；f : E ->L[𝕜] Fₗ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem apply_apply (v : E) (f : E →L[𝕜] Fₗ) : apply 𝕜 Fₗ v f = f v :=
  rfl

variable (σ₁₂ σ₂₃ E F G)


/-- Composition of continuous semilinear maps as a continuous semibilinear map. -/
/-
**ContinuousLinearMap.compSL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：compSL : (F ->SL[σ₂₃] G) ->L[𝕜₃] (E ->SL[σ₁₂] F) ->SL[σ₂₃] E ->SL[σ₁₃] G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of continuous semilinear maps as a continuous semibilinear map.
-/
def compSL : (F →SL[σ₂₃] G) →L[𝕜₃] (E →SL[σ₁₂] F) →SL[σ₂₃] E →SL[σ₁₃] G :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (RingHom.id 𝕜₃) σ₂₃ comp add_comp smul_comp comp_add fun c f g => by
      ext
      simp only [map_smulₛₗ, comp_apply, smul_apply])
    1 fun f g => by simpa only [one_mul] using! opNorm_comp_le f g
/-
**ContinuousLinearMap.norm_compSL_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：norm_compSL_le : ‖compSL E F G σ₁₂ σ₂₃‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous₂_norm_le`：mkContinuous₂_norm_le (f : E ->ₛₗ[σ₁₃] 
F ->ₛₗ[σ₂₃] G) {C : Real} (h0 : 0 <= C) (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖
y‖) : ‖f.mkContinuous…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem norm_compSL_le : ‖compSL E F G σ₁₂ σ₂₃‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

variable {σ₁₂ σ₂₃ E F G}

@[simp]
/-
**ContinuousLinearMap.compSL_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：compSL_apply (f : F ->SL[σ₂₃] G) (g : E ->SL[σ₁₂] F) : compSL E F G σ₁₂ σ₂
₃ f g = f.comp g
参数：f : F ->SL[σ₂₃] G；g : E ->SL[σ₁₂] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem compSL_apply (f : F →SL[σ₂₃] G) (g : E →SL[σ₁₂] F) : compSL E F G σ₁₂ σ₂₃ f g = f.comp g :=
  rfl
/-
**ContinuousLinearMap._root_.Continuous.const_clm_comp** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.const_clm_comp {X} [TopologicalSpace X] {f : X → E →SL[σ₁₂] F}
    (hf : Continuous f) (g : F →SL[σ₂₃] G) :
    Continuous (fun x => g.comp (f x) : X → E →SL[σ₁₃] G) :=
  (compSL E F G σ₁₂ σ₂₃ g).continuous.comp hf

-- Giving the implicit argument speeds up elaboration significantly
/-
**ContinuousLinearMap._root_.Continuous.clm_comp_const** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.clm_comp_const {X} [TopologicalSpace X] {g : X → F →SL[σ₂₃] G}
    (hg : Continuous g) (f : E →SL[σ₁₂] F) :
    Continuous (fun x => (g x).comp f : X → E →SL[σ₁₃] G) :=
  (@ContinuousLinearMap.flip _ _ _ _ _ (E →SL[σ₁₃] G) _ _ _ _ _ _ _ _ _ _ _ _ _
    (compSL E F G σ₁₂ σ₂₃) f).continuous.comp hg

variable (𝕜 σ₁₂ σ₂₃ E Fₗ Gₗ)

/-- Composition of continuous linear maps as a continuous bilinear map. -/
/-
**ContinuousLinearMap.compL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：compL : (Fₗ ->L[𝕜] Gₗ) ->L[𝕜] (E ->L[𝕜] Fₗ) ->L[𝕜] E ->L[𝕜] Gₗ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of continuous linear maps as a continuous bilinear map.
-/
def compL : (Fₗ →L[𝕜] Gₗ) →L[𝕜] (E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ :=
  compSL E Fₗ Gₗ (RingHom.id 𝕜) (RingHom.id 𝕜)
/-
**ContinuousLinearMap.norm_compL_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：norm_compL_le : ‖compL 𝕜 E Fₗ Gₗ‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.norm_compSL_le`：norm_compSL_le : ‖compSL E F G σ₁₂ σ
₂₃‖ <= 1
-/
theorem norm_compL_le : ‖compL 𝕜 E Fₗ Gₗ‖ ≤ 1 :=
  norm_compSL_le _ _ _ _ _

@[simp]
/-
**ContinuousLinearMap.compL_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：compL_apply (f : Fₗ ->L[𝕜] Gₗ) (g : E ->L[𝕜] Fₗ) : compL 𝕜 E Fₗ Gₗ f g = f
.comp g
参数：f : Fₗ ->L[𝕜] Gₗ；g : E ->L[𝕜] Fₗ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem compL_apply (f : Fₗ →L[𝕜] Gₗ) (g : E →L[𝕜] Fₗ) : compL 𝕜 E Fₗ Gₗ f g = f.comp g :=
  rfl

variable (Eₗ) {𝕜 E Fₗ Gₗ}

/-- Apply `L(x,-)` pointwise to bilinear maps, as a continuous bilinear map -/
@[simps! apply]
/-
**ContinuousLinearMap.precompR** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：precompR (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) : E ->L[𝕜] (Eₗ ->L[𝕜] Fₗ) ->L[𝕜] Eₗ -
>L[𝕜] Gₗ
参数：L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Apply `L(x,-)` pointwise to bilinear maps, as a continuous bilinear map
-/
def precompR (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E →L[𝕜] (Eₗ →L[𝕜] Fₗ) →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  compL 𝕜 Eₗ Fₗ Gₗ ∘L L

/-- Apply `L(-,y)` pointwise to bilinear maps, as a continuous bilinear map -/
/-
**ContinuousLinearMap.precompL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：precompL (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) : (Eₗ ->L[𝕜] E) ->L[𝕜] Fₗ ->L[𝕜] Eₗ -
>L[𝕜] Gₗ
参数：L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Apply `L(-,y)` pointwise to bilinear maps, as a continuous bilinear map
-/
def precompL (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : (Eₗ →L[𝕜] E) →L[𝕜] Fₗ →L[𝕜] Eₗ →L[𝕜] Gₗ :=
  (precompR Eₗ (flip L)).flip
/-
**ContinuousLinearMap.precompL_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_4} (Eₗ : Type u_5) {Fₗ : Type u_7} {Gₗ : Type
 u_9} [inst : SeminormedAddCommGroup E]   [inst_1 : SeminormedAddCommGroup Eₗ] [
inst_2 : SeminormedAddCommGroup Fₗ] [inst_3 : SeminormedAddCommGroup Gₗ]   [inst
_4 : NontriviallyNormedField 𝕜] [inst_5 : NormedSpace 𝕜 E] [inst_6 : NormedSpace
 𝕜 Eₗ]   [inst_7 : NormedSpace 𝕜 Fₗ] [inst_8 : NormedSpace 𝕜 Gₗ] (L : E →L[𝕜] Fₗ
 →L[𝕜] Gₗ) (u : Eₗ →L[𝕜] E) (f : Fₗ) (g : Eₗ),   (((ContinuousLinearMap.precompL
 Eₗ L) u) f) g = (L (u g)) f
参数：Eₗ : Type u_5；L : E →L[𝕜] Fₗ →L[𝕜] Gₗ；u : Eₗ →L[𝕜] E；f : Fₗ；g : Eₗ；((Continuo
usLinearMap.precompL Eₗ L) u) f；L (u g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
@[simp] lemma precompL_apply (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (u : Eₗ →L[𝕜] E) (f : Fₗ) (g : Eₗ) :
    precompL Eₗ L u f g = L (u g) f := rfl
/-
**ContinuousLinearMap.norm_precompR_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：norm_precompR_le (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) : ‖precompR Eₗ L‖ <= ‖L‖
参数：L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.opNorm_comp_le`：opNorm_comp_le (f : E ->SL[σ₁₂] F) :
 ‖h.comp f‖ <= ‖h‖ * ‖f‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ContinuousLinearMap.norm_compL_le`：norm_compL_le : ‖compL 𝕜 E Fₗ Gₗ‖ <= 
1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem norm_precompR_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : ‖precompR Eₗ L‖ ≤ ‖L‖ :=
  calc
    ‖precompR Eₗ L‖ ≤ ‖compL 𝕜 Eₗ Fₗ Gₗ‖ * ‖L‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖L‖ := by gcongr; apply norm_compL_le
    _ = ‖L‖ := by rw [one_mul]
/-
**ContinuousLinearMap.norm_precompL_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：norm_precompL_le (L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) : ‖precompL Eₗ L‖ <= ‖L‖
参数：L : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.precompL.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_4} (Eₗ :
 Type u_5) {Fₗ : Type u_7} {Gₗ : Type u_9} [inst : SeminormedAddCommGroup E]   [
inst_1 : SeminormedAddC…
· 使用定理 `ContinuousLinearMap.opNorm_flip`：opNorm_flip (f : E ->SL[σ₁₃] F ->SL[σ₂₃
] G) : ‖f.flip‖ = ‖f‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.norm_precompR_le`：norm_precompR_le (L : E ->L[𝕜] Fₗ 
->L[𝕜] Gₗ) : ‖precompR Eₗ L‖ <= ‖L‖
-/
theorem norm_precompL_le (L : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : ‖precompL Eₗ L‖ ≤ ‖L‖ := by
  rw [precompL, opNorm_flip, ← opNorm_flip L]
  exact norm_precompR_le _ L.flip

end ContinuousLinearMap

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

namespace ContinuousLinearMap

variable {E' F' : Type*} [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F']
variable {𝕜₁' : Type*} {𝕜₂' : Type*} [NontriviallyNormedField 𝕜₁'] [NontriviallyNormedField 𝕜₂']
  [NormedSpace 𝕜₁' E'] [NormedSpace 𝕜₂' F'] {σ₁' : 𝕜₁' →+* 𝕜} {σ₁₃' : 𝕜₁' →+* 𝕜₃} {σ₂' : 𝕜₂' →+* 𝕜₂}
  {σ₂₃' : 𝕜₂' →+* 𝕜₃} [RingHomCompTriple σ₁' σ₁₃ σ₁₃'] [RingHomCompTriple σ₂' σ₂₃ σ₂₃']
  [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃'] [RingHomIsometric σ₂₃']

/-- Compose a bilinear map `E →SL[σ₁₃] F →SL[σ₂₃] G` with two linear maps
`E' →SL[σ₁'] E` and `F' →SL[σ₂'] F`. -/
/-
**ContinuousLinearMap.bilinearComp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：bilinearComp (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (gE : E' ->SL[σ₁'] E) (gF : F
' ->SL[σ₂'] F) : E' ->SL[σ₁₃'] F' ->SL[σ₂₃'] G
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G；gE : E' ->SL[σ₁'] E；gF : F' ->SL[σ₂'] F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Compose a bilinear map `E →SL[σ₁₃] F →SL[σ₂₃] G` with two linear maps
`E' →SL[σ₁'] E` and `F' →SL[σ₂'] F`.
-/
def bilinearComp (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F) :
    E' →SL[σ₁₃'] F' →SL[σ₂₃'] G :=
  ((f.comp gE).flip.comp gF).flip

@[simp]
/-
**ContinuousLinearMap.bilinearComp_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：bilinearComp_apply (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (gE : E' ->SL[σ₁'] E) (
gF : F' ->SL[σ₂'] F) (x : E') (y : F') : f.bilinearComp gE gF x y = f (gE x) (gF
 y)
参数：f : E ->SL[σ₁₃] F ->SL[σ₂₃] G；gE : E' ->SL[σ₁'] E；gF : F' ->SL[σ₂'] F；x : E'；
y : F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem bilinearComp_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (gE : E' →SL[σ₁'] E) (gF : F' →SL[σ₂'] F)
    (x : E') (y : F') : f.bilinearComp gE gF x y = f (gE x) (gF y) :=
  rfl

@[simp]
/-
**ContinuousLinearMap.bilinearComp_zero** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：bilinearComp_zero {gE : E' ->SL[σ₁'] E} {gF : F' ->SL[σ₂'] F} : bilinearCo
mp (0 : E ->SL[σ₁₃] F ->SL[σ₂₃] G) gE gF = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma bilinearComp_zero {gE : E' →SL[σ₁'] E} {gF : F' →SL[σ₂'] F} :
    bilinearComp (0 : E →SL[σ₁₃] F →SL[σ₂₃] G) gE gF = 0 := rfl

@[simp]
/-
**ContinuousLinearMap.bilinearComp_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：bilinearComp_zero_left {f : E ->SL[σ₁₃] F ->SL[σ₂₃] G} {gF : F' ->SL[σ₂'] 
F} : bilinearComp f (0 : E' ->SL[σ₁'] E) gF = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bilinearComp_zero_left {f : E →SL[σ₁₃] F →SL[σ₂₃] G} {gF : F' →SL[σ₂'] F} :
    bilinearComp f (0 : E' →SL[σ₁'] E) gF = 0 := by ext; simp

@[simp]
/-
**ContinuousLinearMap.bilinearComp_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：bilinearComp_zero_right {f : E ->SL[σ₁₃] F ->SL[σ₂₃] G} {gE : E' ->SL[σ₁']
 E} : bilinearComp f gE (0 : F' ->SL[σ₂'] F) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bilinearComp_zero_right {f : E →SL[σ₁₃] F →SL[σ₂₃] G} {gE : E' →SL[σ₁'] E} :
    bilinearComp f gE (0 : F' →SL[σ₂'] F) = 0 := by ext; simp

variable [RingHomIsometric σ₁₃] [RingHomIsometric σ₁'] [RingHomIsometric σ₂']

/-- Derivative of a continuous bilinear map `f : E →L[𝕜] F →L[𝕜] G` interpreted as a map `E × F → G`
at point `p : E × F` evaluated at `q : E × F`, as a continuous bilinear map. -/
/-
**ContinuousLinearMap.deriv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Type v} [inst_1 : N
ormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜} (e : 𝕜 →L[𝕜] F), deriv
 (⇑e) x = e 1
参数：e : 𝕜 →L[𝕜] F；⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `ContinuousLinearMap.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜
 F] {x : 𝕜} (e : 𝕜 →…

--- 原说明 ---
Derivative of a continuous bilinear map `f : E →L[𝕜] F →L[𝕜] G` interpreted as a
 map `E × F → G`
at point `p : E × F` evaluated at `q : E × F`, as a continuous bilinear map.
-/
def deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) : E × Fₗ →L[𝕜] E × Fₗ →L[𝕜] Gₗ :=
  f.bilinearComp (fst _ _ _) (snd _ _ _) + f.flip.bilinearComp (snd _ _ _) (fst _ _ _)

@[simp]
/-
**ContinuousLinearMap.coe_deriv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_deriv₂ (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (p : E × Fₗ) :
    ⇑(f.deriv₂ p) = fun q : E × Fₗ => f p.1 q.2 + f q.1 p.2 :=
  rfl
/-
**ContinuousLinearMap.map_add_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：map_add_add (f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ) (x x' : E) (y y' : Fₗ) : f (x + x'
) (y + y') = f x y + f.deriv₂ (x, y) (x', y') + f x' y'
参数：f : E ->L[𝕜] Fₗ ->L[𝕜] Gₗ；x x' : E；y y' : Fₗ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `_private.Mathlib.Analysis.Normed.Operator.Bilinear.0.ContinuousLinearMap
.map_add_add._abel_1_1`：∀ {𝕜 : Type u_3} {E : Type u_4} {Fₗ : Type u_2} {Gₗ : Ty
pe u_1} [inst : SeminormedAddCommGroup E]   [inst_1 : SeminormedAddCommGroup Fₗ]
 [in…
-/
theorem map_add_add (f : E →L[𝕜] Fₗ →L[𝕜] Gₗ) (x x' : E) (y y' : Fₗ) :
    f (x + x') (y + y') = f x y + f.deriv₂ (x, y) (x', y') + f x' y' := by
  simp only [map_add, add_apply, coe_deriv₂, add_assoc]
  abel

/-- The norm of the tensor product of a scalar linear map and of an element of a normed space
is the product of the norms. -/
@[simp]
/-
**ContinuousLinearMap.norm_smulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：norm_smulRight_apply (c : StrongDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖
 * ‖f‖
参数：c : StrongDual 𝕜 E；f : Fₗ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The norm of the tensor product of a scalar linear map and of an element of a nor
med space
is the product of the norms.
-/
theorem norm_smulRight_apply (c : StrongDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖ := by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound _ (by positivity) fun x => ?_
    calc
      ‖c x • f‖ = ‖c x‖ * ‖f‖ := norm_smul _ _
      _ ≤ ‖c‖ * ‖x‖ * ‖f‖ := by gcongr; apply le_opNorm
      _ = ‖c‖ * ‖f‖ * ‖x‖ := by ring
  · obtain hf | hf := (norm_nonneg f).eq_or_lt'
    · simp [hf]
    · rw [← le_div_iff₀ hf]
      refine opNorm_le_bound _ (by positivity) fun x => ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hf]
      calc
        ‖c x‖ * ‖f‖ = ‖c x • f‖ := (norm_smul _ _).symm
        _ = ‖smulRight c f x‖ := rfl
        _ ≤ ‖smulRight c f‖ * ‖x‖ := le_opNorm _ _

/-- The non-negative norm of the tensor product of a scalar linear map and of an element of a normed
space is the product of the non-negative norms. -/
@[simp]
/-
**ContinuousLinearMap.nnnorm_smulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：nnnorm_smulRight_apply (c : StrongDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖₊ = 
‖c‖₊ * ‖f‖₊
参数：c : StrongDual 𝕜 E；f : Fₗ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.norm_smulRight_apply`：norm_smulRight_apply (c : Stro
ngDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖

--- 原说明 ---
The non-negative norm of the tensor product of a scalar linear map and of an ele
ment of a normed
space is the product of the non-negative norms.
-/
theorem nnnorm_smulRight_apply (c : StrongDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖₊ = ‖c‖₊ * ‖f‖₊ :=
  NNReal.eq <| c.norm_smulRight_apply f
/-
**ContinuousLinearMap.norm_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_4} [inst : SeminormedAddCommGroup E] [inst_1 
: NontriviallyNormedField 𝕜]   [inst_2 : NormedSpace 𝕜 E] (x : E), ‖ContinuousLi
nearMap.toSpanSingleton 𝕜 x‖ = ‖x‖
参数：x : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.norm_smulRight_apply`：norm_smulRight_apply (c : Stro
ngDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖
· 使用定理 `ContinuousLinearMap.norm_id`：norm_id [NontrivialTopology E] : ‖Continuou
sLinearMap.id 𝕜 E‖ = 1
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem norm_toSpanSingleton (x : E) : ‖toSpanSingleton 𝕜 x‖ = ‖x‖ := by
  simp [← smulRight_id, norm_id]
/-
**ContinuousLinearMap.nnnorm_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_4} [inst : SeminormedAddCommGroup E] [inst_1 
: NontriviallyNormedField 𝕜]   [inst_2 : NormedSpace 𝕜 E] (x : E), ‖ContinuousLi
nearMap.toSpanSingleton 𝕜 x‖₊ = ‖x‖₊
参数：x : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.norm_toSpanSingleton`：∀ {𝕜 : Type u_1} {E : Type u_4
} [inst : SeminormedAddCommGroup E] [inst_1 : NontriviallyNormedField 𝕜]   [inst
_2 : NormedSpace 𝕜 E] (x : E),…
-/
@[simp] theorem nnnorm_toSpanSingleton (x : E) : ‖toSpanSingleton 𝕜 x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_toSpanSingleton _

variable (𝕜 E Fₗ) in
/-- `ContinuousLinearMap.smulRight` as a continuous trilinear map:
`smulRightL (c : StrongDual 𝕜 E) (f : F) (x : E) = c x • f`.

This is also known as a rank-one operator.
See also `InnerProductSpace.rankOne` for the rank-one operator on Hilbert spaces. -/
@[simps! apply_apply]
/-
**ContinuousLinearMap.smulRightL** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：smulRightL : StrongDual 𝕜 E ->L[𝕜] Fₗ ->L[𝕜] E ->L[𝕜] Fₗ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.smulRight` as a continuous trilinear map:
`smulRightL (c : StrongDual 𝕜 E) (f : F) (x : E) = c x • f`.

This is also known as a rank-one operator.
See also `InnerProductSpace.rankOne` for the rank-one operator on Hilbert spaces
.
-/
def smulRightL : StrongDual 𝕜 E →L[𝕜] Fₗ →L[𝕜] E →L[𝕜] Fₗ :=
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
/-- Convenience function for restricting the linearity of a bilinear map. -/
/-
**ContinuousLinearMap.bilinearRestrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：bilinearRestrictScalars (B : E ->L[𝕜'] F ->L[𝕜'] G) : E ->L[𝕜] F ->L[𝕜] G
参数：B : E ->L[𝕜'] F ->L[𝕜'] G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Convenience function for restricting the linearity of a bilinear map.
-/
def bilinearRestrictScalars (B : E →L[𝕜'] F →L[𝕜'] G) : E →L[𝕜] F →L[𝕜] G :=
  (restrictScalarsL 𝕜' F G 𝕜 𝕜).comp (B.restrictScalars 𝕜)

variable (B : E →L[𝕜'] F →L[𝕜'] G) (x : E) (y : F)
/-
**ContinuousLinearMap.bilinearRestrictScalars_eq_restrictScalarsL_comp_restrictS
calars** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：bilinearRestrictScalars_eq_restrictScalarsL_comp_restrictScalars : B.bilin
earRestrictScalars 𝕜 = (restrictScalarsL 𝕜' F G 𝕜 𝕜).comp (B.restrictScalars 𝕜)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem bilinearRestrictScalars_eq_restrictScalarsL_comp_restrictScalars :
    B.bilinearRestrictScalars 𝕜 = (restrictScalarsL 𝕜' F G 𝕜 𝕜).comp (B.restrictScalars 𝕜) := rfl
/-
**ContinuousLinearMap.bilinearRestrictScalars_eq_restrictScalars_restrictScalars
L_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：bilinearRestrictScalars_eq_restrictScalars_restrictScalarsL_comp : B.bilin
earRestrictScalars 𝕜 = restrictScalars 𝕜 ((restrictScalarsL 𝕜' F G 𝕜 𝕜').comp B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem bilinearRestrictScalars_eq_restrictScalars_restrictScalarsL_comp :
    B.bilinearRestrictScalars 𝕜 = restrictScalars 𝕜 ((restrictScalarsL 𝕜' F G 𝕜 𝕜').comp B) := rfl

variable (𝕜) in
@[simp]
/-
**ContinuousLinearMap.bilinearRestrictScalars_apply_apply** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearMap`。
形式化陈述：bilinearRestrictScalars_apply_apply : (B.bilinearRestrictScalars 𝕜) x y = 
B x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem bilinearRestrictScalars_apply_apply : (B.bilinearRestrictScalars 𝕜) x y = B x y := rfl

@[simp]
/-
**ContinuousLinearMap.norm_bilinearRestrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：norm_bilinearRestrictScalars : ‖B.bilinearRestrictScalars 𝕜‖ = ‖B‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem norm_bilinearRestrictScalars : ‖B.bilinearRestrictScalars 𝕜‖ = ‖B‖ := rfl

end ContinuousLinearMap

end Restrict

