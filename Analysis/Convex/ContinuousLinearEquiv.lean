/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Strict
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# (Pre)images of strict convex sets under continuous linear equivalences

In this file we prove that the (pre)image of a strict convex set
under a continuous linear equivalence is a strict convex set.
-/

public section

variable {𝕜 E F : Type*}
  [Field 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

namespace ContinuousLinearEquiv

@[simp]
/-
**ContinuousLinearEquiv.strictConvex_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousLinearEquiv`。
形式化陈述：strictConvex_preimage {s : Set F} (e : E ≃L[𝕜] F) : StrictConvex 𝕜 (e ⁻¹' 
s) ↔ StrictConvex 𝕜 s
参数：e : E ≃L[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvex.linear_preimage`：StrictConvex.linear_preimage {s : Set F} (
hs : StrictConvex 𝕜 s) (f : E ->ₗ[𝕜] F) (hf : Continuous f) (hfinj : Injective f
) : StrictConvex 𝕜…
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `ContinuousLinearEquiv.injective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst
 : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [in
st_2 : RingHomInvPair…
· 使用定理 `Function.LeftInverse.preimage_preimage`：∀ {α : Type u_1} {β : Type u_2} 
{f : α → β} {g : β → α}, Function.LeftInverse g f → ∀ (s : Set α), f ⁻¹' g ⁻¹' s
 = s
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
-/
lemma strictConvex_preimage {s : Set F} (e : E ≃L[𝕜] F) :
    StrictConvex 𝕜 (e ⁻¹' s) ↔ StrictConvex 𝕜 s :=
  ⟨fun h ↦ Function.LeftInverse.preimage_preimage e.right_inv s ▸
    h.linear_preimage e.symm.toLinearMap e.symm.continuous e.symm.injective,
    fun h ↦ h.linear_preimage e.toLinearMap e.continuous e.injective⟩

@[simp]
/-
**ContinuousLinearEquiv.strictConvex_image** 是 Mathlib 中的一个引理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：strictConvex_image {s : Set E} (e : E ≃L[𝕜] F) : StrictConvex 𝕜 (e '' s) ↔
 StrictConvex 𝕜 s
参数：e : E ≃L[𝕜] F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.image_eq_preimage_symm`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用引理 `ContinuousLinearEquiv.strictConvex_preimage`：strictConvex_preimage {s : 
Set F} (e : E ≃L[𝕜] F) : StrictConvex 𝕜 (e ⁻¹' s) ↔ StrictConvex 𝕜 s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma strictConvex_image {s : Set E} (e : E ≃L[𝕜] F) :
    StrictConvex 𝕜 (e '' s) ↔ StrictConvex 𝕜 s := by
  rw [e.image_eq_preimage_symm, e.symm.strictConvex_preimage]

end ContinuousLinearEquiv

