/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivative of `x ↦ f (cx)`

In this file we prove that the derivative of `fun x ↦ f (c * x)`
equals `c` times the derivative of `f` evaluated at `c * x`.

Since Mathlib uses `0` as the fallback value for the derivatives whenever they are undefined,
the theorems in this file require neither differentiability of `f`,
nor assumptions like `UniqueDiffWithinAt 𝕜 s x`.
-/

public section

open Set
open scoped Pointwise

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {c : 𝕜} {f : 𝕜 → E} {f' : E} {s : Set 𝕜} {x : 𝕜}

/-
**hasDerivWithinAt_comp_mul_left_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_comp_mul_left_smul_iff : HasDerivWithinAt (f <| c * ·) (c
 • f') s x ↔ HasDerivWithinAt f f' (c • s) (c * x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.toSpanSingleton_smul`：toSpanSingleton_smul {α} [Mono
id α] [DistribMulAction α M₁] [ContinuousConstSMul α M₁] [SMulCommClass R₁ α M₁]
 (c : α) (x : M₁) : toSpanSing…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasDerivWithinAt_comp_mul_left_smul_iff :
    HasDerivWithinAt (f <| c * ·) (c • f') s x ↔ HasDerivWithinAt f f' (c • s) (c * x) := by
  simp only [hasDerivWithinAt_iff_hasFDerivWithinAt, ← smul_eq_mul,
    ← hasFDerivWithinAt_comp_smul_smul_iff, ContinuousLinearMap.toSpanSingleton_smul]

variable (c f s x) in
/-
**derivWithin_comp_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_comp_mul_left : derivWithin (f <| c * ·) s x = c • derivWithin
 f (c • s) (c * x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `derivWithin_const_smul_field`：derivWithin_const_smul_field (c : 𝕝) (f : 
𝕜 -> F) : derivWithin (c • f) s x = c • derivWithin f s x
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `derivWithin.eq_1`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F :
 Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 : Topo
logica…
· 使用定理 `fderivWithin_comp_smul_eq_fderivWithin_smul`：fderivWithin_comp_smul_eq_f
derivWithin_smul (c : 𝕜) : fderivWithin 𝕜 (f <| c • ·) s x = fderivWithin 𝕜 (c •
 f) (c • s) (c • x)
· 使用定理 `Pi.smul_def`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst : 
(i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i),   a • f = fun i => a • f i
-/
theorem derivWithin_comp_mul_left :
    derivWithin (f <| c * ·) s x = c • derivWithin f (c • s) (c * x) := by
  simp only [← smul_eq_mul]
  rw [← derivWithin_const_smul_field, derivWithin, derivWithin,
    fderivWithin_comp_smul_eq_fderivWithin_smul, Pi.smul_def]

variable (c f x) in
/-
**deriv_comp_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_comp_mul_left : deriv (f <| c * ·) x = c • deriv f (c * x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `fderiv_comp_smul`：fderiv_comp_smul (c : 𝕜) : fderiv 𝕜 (f <| c • ·) x = c
 • fderiv 𝕜 f (c • x)
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_comp_mul_left : deriv (f <| c * ·) x = c • deriv f (c * x) := by
  simp only [← smul_eq_mul, deriv, fderiv_comp_smul, smul_apply]
