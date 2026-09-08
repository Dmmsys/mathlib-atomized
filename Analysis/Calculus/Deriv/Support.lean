/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Support of the derivative of a function

In this file we prove that the (topological) support of a function includes the support of its
derivative. As a corollary, we show that the derivative of a function with compact support has
compact support.

## Keywords

derivative, support
-/

public section


universe u v

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : 𝕜 → E} {x : 𝕜}

/-! ### Support of derivatives -/


section Support

open Function

/-
**HasStrictDerivAt.of_notMem_tsupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) : HasStrictDerivA
t f 0 x
参数：h : x ∉ tsupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.congr_of_eventuallyEq`：HasStrictDerivAt.congr_of_eventu
allyEq (h : HasStrictDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictDerivAt f₁ f
' x
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `notMem_tsupport_iff_eventuallyEq`：∀ {α : Type u_2} {β : Type u_4} [inst 
: TopologicalSpace α] [inst_1 : Zero β] {f : α → β} {x : α},   x ∉ tsupport f ↔ 
f =ᶠ[nhds x] 0
-/
theorem HasStrictDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) : HasStrictDerivAt f 0 x := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictDerivAt_const x 0).congr_of_eventuallyEq h.symm
/-
**HasDerivAt.of_notMem_tsupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) : HasDerivAt f 0 x
参数：h : x ∉ tsupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `HasStrictDerivAt.of_notMem_tsupport`：HasStrictDerivAt.of_notMem_tsupport
 (h : x ∉ tsupport f) : HasStrictDerivAt f 0 x
-/
theorem HasDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) : HasDerivAt f 0 x :=
  (HasStrictDerivAt.of_notMem_tsupport h).hasDerivAt
/-
**HasDerivWithinAt.of_notMem_tsupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.of_notMem_tsupport {s : Set 𝕜} (h : x ∉ tsupport f) : Has
DerivWithinAt f 0 s x
参数：h : x ∉ tsupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `HasDerivAt.of_notMem_tsupport`：HasDerivAt.of_notMem_tsupport (h : x ∉ ts
upport f) : HasDerivAt f 0 x
-/
theorem HasDerivWithinAt.of_notMem_tsupport {s : Set 𝕜} (h : x ∉ tsupport f) :
    HasDerivWithinAt f 0 s x :=
  (HasDerivAt.of_notMem_tsupport h).hasDerivWithinAt
/-
**deriv_of_notMem_tsupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_of_notMem_tsupport (h : x ∉ tsupport f) : deriv f x = 0
参数：h : x ∉ tsupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.deriv_eq`：Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝
 x] f) : deriv f₁ x = deriv f x
· 使用定理 `notMem_tsupport_iff_eventuallyEq`：∀ {α : Type u_2} {β : Type u_4} [inst 
: TopologicalSpace α] [inst_1 : Zero β] {f : α → β} {x : α},   x ∉ tsupport f ↔ 
f =ᶠ[nhds x] 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_zero`：deriv_zero : deriv (0 : 𝕜 -> F) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_of_notMem_tsupport (h : x ∉ tsupport f) : deriv f x = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  simp [h.deriv_eq]
/-
**support_deriv_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：support_deriv_subset : support (deriv f) subseteq tsupport f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0
· 使用定理 `deriv_of_notMem_tsupport`：deriv_of_notMem_tsupport (h : x ∉ tsupport f) 
: deriv f x = 0
-/
theorem support_deriv_subset : support (deriv f) ⊆ tsupport f := fun x ↦ by
  rw [← not_imp_not, notMem_support]
  exact deriv_of_notMem_tsupport
/-
**tsupport_deriv_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsupport_deriv_subset : tsupport (deriv f) subseteq tsupport f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `support_deriv_subset`：support_deriv_subset : support (deriv f) subseteq 
tsupport f
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem tsupport_deriv_subset : tsupport (deriv f) ⊆ tsupport f :=
  closure_minimal support_deriv_subset isClosed_closure
/-
**HasCompactSupport.deriv** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactSupport`。
形式化陈述：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {E : Type v} [inst_1 : N
ormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {f : 𝕜 → E}, HasCompactSupport
 f → HasCompactSupport (deriv f)
参数：deriv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactSupport.mono'`：∀ {α : Type u_2} {β : Type u_4} {γ : Type u_5} 
[inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : Zero γ]   {f : α → β} {f
' : α → γ}, H…
· 使用定理 `support_deriv_subset`：support_deriv_subset : support (deriv f) subseteq 
tsupport f
-/
protected theorem HasCompactSupport.deriv (hf : HasCompactSupport f) :
    HasCompactSupport (deriv f) :=
  hf.mono' support_deriv_subset

end Support

