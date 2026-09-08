/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.ContinuousLinearEquiv
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# (Strict) convexity and linear isometries

In this file we prove some basic lemmas about (strict) convexity and linear isometries.
-/

public section

open Function Set Metric
open scoped Convex

section SeminormedAddCommGroup

variable {𝕜 E F : Type*}
  [NormedField 𝕜] [PartialOrder 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

@[simp]
/-
**LinearIsometryEquiv.strictConvex_preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIsometryEquiv.strictConvex_preimage {s : Set F} (e : E ≃ₗᵢ[𝕜] F) : S
trictConvex 𝕜 (e ⁻¹' s) ↔ StrictConvex 𝕜 s
参数：e : E ≃ₗᵢ[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearEquiv.strictConvex_preimage`：strictConvex_preimage {s : 
Set F} (e : E ≃L[𝕜] F) : StrictConvex 𝕜 (e ⁻¹' s) ↔ StrictConvex 𝕜 s
-/
lemma LinearIsometryEquiv.strictConvex_preimage {s : Set F} (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvex 𝕜 (e ⁻¹' s) ↔ StrictConvex 𝕜 s :=
  e.toContinuousLinearEquiv.strictConvex_preimage

@[simp]
/-
**LinearIsometryEquiv.strictConvex_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIsometryEquiv.strictConvex_image {s : Set E} (e : E ≃ₗᵢ[𝕜] F) : Stri
ctConvex 𝕜 (e '' s) ↔ StrictConvex 𝕜 s
参数：e : E ≃ₗᵢ[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearEquiv.strictConvex_image`：strictConvex_image {s : Set E}
 (e : E ≃L[𝕜] F) : StrictConvex 𝕜 (e '' s) ↔ StrictConvex 𝕜 s
-/
lemma LinearIsometryEquiv.strictConvex_image {s : Set E} (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvex 𝕜 (e '' s) ↔ StrictConvex 𝕜 s :=
  e.toContinuousLinearEquiv.strictConvex_image

end SeminormedAddCommGroup

variable {𝕜 E F : Type*} [NormedField 𝕜] [PartialOrder 𝕜]

/-
**StrictConvex.linearIsometry_preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConvex.linearIsometry_preimage [NormedAddCommGroup E] [NormedSpace 𝕜
 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set F} (hs : StrictConvex 
𝕜 s) (e : E ->ₗᵢ[𝕜] F) : StrictConvex 𝕜 (e ⁻¹' s)
参数：hs : StrictConvex 𝕜 s；e : E ->ₗᵢ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvex.linear_preimage`：StrictConvex.linear_preimage {s : Set F} (
hs : StrictConvex 𝕜 s) (f : E ->ₗ[𝕜] F) (hf : Continuous f) (hfinj : Injective f
) : StrictConvex 𝕜…
· 使用定理 `LinearIsometry.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_
5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂}
 [inst_2 : Semi…
· 使用定理 `LinearIsometry.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E₂ : Type u_
6} {F : Type u_9} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} 
[inst_2 : Semi…
-/
lemma StrictConvex.linearIsometry_preimage [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set F}
    (hs : StrictConvex 𝕜 s) (e : E →ₗᵢ[𝕜] F) : StrictConvex 𝕜 (e ⁻¹' s) :=
  hs.linear_preimage _ e.continuous e.injective

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
/-
**LinearIsometryEquiv.strictConvexSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearIso
metryEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : NormedField 𝕜] [ins
t_1 : PartialOrder 𝕜]   [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 
E] [inst_4 : NormedAddCommGroup F] [inst_5 : NormedSpace 𝕜 F]   (e : E ≃ₗᵢ[𝕜] F)
, StrictConvexSpace 𝕜 E ↔ StrictConvexSpace 𝕜 F
参数：e : E ≃ₗᵢ[𝕜] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.map_zero`：map_zero : e 0 = 0
· 使用定理 `LinearIsometryEquiv.image_closedBall`：image_closedBall (x : E) (r : Real
) : e '' Metric.closedBall x r = Metric.closedBall (e x) r
· 使用引理 `LinearIsometryEquiv.strictConvex_image`：LinearIsometryEquiv.strictConvex
_image {s : Set E} (e : E ≃ₗᵢ[𝕜] F) : StrictConvex 𝕜 (e '' s) ↔ StrictConvex 𝕜 s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma LinearIsometryEquiv.strictConvexSpace_iff (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 E ↔ StrictConvexSpace 𝕜 F := by
  simp only [strictConvexSpace_iff, ← map_zero e, ← e.image_closedBall, e.strictConvex_image]
/-
**LinearIsometry.strictConvexSpace_range_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIsometry.strictConvexSpace_range_iff (e : E ->ₗᵢ[𝕜] F) : StrictConve
xSpace 𝕜 (e : E ->ₗ[𝕜] F).range ↔ StrictConvexSpace 𝕜 E
参数：e : E ->ₗᵢ[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearIsometryEquiv.strictConvexSpace_iff`：∀ {𝕜 : Type u_1} {E : Type u_
2} {F : Type u_3} [inst : NormedField 𝕜] [inst_1 : PartialOrder 𝕜]   [inst_2 : N
ormedAddCommGroup E] [inst_3 : …
-/
lemma LinearIsometry.strictConvexSpace_range_iff (e : E →ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 (e : E →ₗ[𝕜] F).range ↔ StrictConvexSpace 𝕜 E :=
  e.equivRange.strictConvexSpace_iff.symm
/-
**LinearIsometry.strictConvexSpace_range** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LinearIsometry.strictConvexSpace_range [StrictConvexSpace 𝕜 E] (e : E ->ₗᵢ
[𝕜] F) : StrictConvexSpace 𝕜 (e : E ->ₗ[𝕜] F).range
参数：e : E ->ₗᵢ[𝕜] F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用引理 `LinearIsometry.strictConvexSpace_range_iff`：LinearIsometry.strictConvexS
pace_range_iff (e : E ->ₗᵢ[𝕜] F) : StrictConvexSpace 𝕜 (e : E ->ₗ[𝕜] F).range ↔ 
StrictConvexSpace 𝕜 E
-/
instance LinearIsometry.strictConvexSpace_range [StrictConvexSpace 𝕜 E] (e : E →ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 (e : E →ₗ[𝕜] F).range :=
  e.strictConvexSpace_range_iff.mpr ‹_›
/-
**LinearIsometry.strictConvexSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIsometry.strictConvexSpace [StrictConvexSpace 𝕜 F] (f : E ->ₗᵢ[𝕜] F)
 : StrictConvexSpace 𝕜 E where strictConvex_closedBall r hr
参数：f : E ->ₗᵢ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.preimage_closedBall`：preimage_closedBall (hf : Isometry f) (x :
 α) (r : Real) : f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r
· 使用定理 `LinearIsometry.isometry`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type u_5}
 {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} [
inst_2 : Semi…
· 使用引理 `StrictConvex.linearIsometry_preimage`：StrictConvex.linearIsometry_preima
ge [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSp
ace 𝕜 F] {s : Set F} (hs :…
· 使用定理 `strictConvex_closedBall`：strictConvex_closedBall [StrictConvexSpace 𝕜 E]
 (x : E) (r : Real) : StrictConvex 𝕜 (closedBall x r)
-/
lemma LinearIsometry.strictConvexSpace [StrictConvexSpace 𝕜 F] (f : E →ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 E where
  strictConvex_closedBall r hr := by
    rw [← f.isometry.preimage_closedBall]
    exact (strictConvex_closedBall _ _ _).linearIsometry_preimage _

/-- A vector subspace of a strict convex space is a strict convex space.

This instance has priority 900
to make sure that instances like `LinearIsometry.strictConvexSpace_range`
are tried before this one. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vector subspace of a strict convex space is a strict convex space.

This instance has priority 900
to make sure that instances like `LinearIsometry.strictConvexSpace_range`
are tried before this one.
-/
instance (priority := 900) Submodule.instStrictConvexSpace [StrictConvexSpace 𝕜 E]
    (p : Submodule 𝕜 E) : StrictConvexSpace 𝕜 p :=
  p.subtypeₗᵢ.strictConvexSpace
