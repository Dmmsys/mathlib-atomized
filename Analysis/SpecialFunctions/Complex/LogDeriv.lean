/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiability of the complex `log` function

-/

public section

assert_not_exists IsConformalMap Conformal

open Set Filter

open scoped Real Topology

namespace Complex

/-
**Complex.isOpenMap_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isOpenMap_exp : IsOpenMap exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpenMap_of_hasStrictDerivAt`：isOpenMap_of_hasStrictDerivAt {f' : 𝕜 -> 
𝕜} (hf : forall x, HasStrictDerivAt f (f' x) x) (h0 : forall x, f' x != 0) : IsO
penMap f
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Complex.hasStrictDerivAt_exp`：hasStrictDerivAt_exp (x : Complex) : HasSt
rictDerivAt exp (exp x) x
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
-/
theorem isOpenMap_exp : IsOpenMap exp :=
  isOpenMap_of_hasStrictDerivAt hasStrictDerivAt_exp exp_ne_zero
/-
**Complex.hasStrictDerivAt_log** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictDerivAt_log {x : Complex} (h : x in slitPlane) : HasStrictDerivAt
 log x⁻¹ x
参数：h : x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.slitPlane_ne_zero`：∀ {z : ℂ}, z ∈ Complex.slitPlane → z ≠ 0
· 使用定理 `OpenPartialHomeomorph.hasStrictDerivAt_symm`：OpenPartialHomeomorph.hasSt
rictDerivAt_symm (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜} (ha : a in f.target)
 (hf' : f' != 0) (htff' : HasStri…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Complex.exp_log`：exp_log {x : Complex} (hx : x != 0) : exp (log x) = x
· 使用定理 `Complex.hasStrictDerivAt_exp`：hasStrictDerivAt_exp (x : Complex) : HasSt
rictDerivAt exp (exp x) x
-/
theorem hasStrictDerivAt_log {x : ℂ} (h : x ∈ slitPlane) : HasStrictDerivAt log x⁻¹ x :=
  have h0 : x ≠ 0 := slitPlane_ne_zero h
  expOpenPartialHomeomorph.hasStrictDerivAt_symm h h0 <| by
    simpa [exp_log h0] using! hasStrictDerivAt_exp (log x)
/-
**Complex.hasDerivAt_log** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasDerivAt_log {z : Complex} (hz : z in slitPlane) : HasDerivAt log z⁻¹ z
参数：hz : z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_log`：hasStrictDerivAt_log {x : Complex} (h : x 
in slitPlane) : HasStrictDerivAt log x⁻¹ x
-/
lemma hasDerivAt_log {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt log z⁻¹ z :=
  HasStrictDerivAt.hasDerivAt <| hasStrictDerivAt_log hz

@[fun_prop]
/-
**Complex.differentiableAt_log** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：differentiableAt_log {z : Complex} (hz : z in slitPlane) : DifferentiableA
t Complex log z
参数：hz : z in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用引理 `Complex.hasDerivAt_log`：hasDerivAt_log {z : Complex} (hz : z in slitPlan
e) : HasDerivAt log z⁻¹ z
-/
lemma differentiableAt_log {z : ℂ} (hz : z ∈ slitPlane) : DifferentiableAt ℂ log z :=
  (hasDerivAt_log hz).differentiableAt

@[fun_prop]
/-
**Complex.hasStrictFDerivAt_log_real** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictFDerivAt_log_real {x : Complex} (h : x in slitPlane) : HasStrictF
DerivAt log (x⁻¹ • (1 : Complex ->L[Real] Complex)) x
参数：h : x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.complexToReal_fderiv`：HasStrictDerivAt.complexToReal_fd
eriv {f : Complex -> Complex} {f' x : Complex} (h : HasStrictDerivAt f f' x) : H
asStrictFDerivAt f (f' • (1…
· 使用定理 `Complex.hasStrictDerivAt_log`：hasStrictDerivAt_log {x : Complex} (h : x 
in slitPlane) : HasStrictDerivAt log x⁻¹ x
-/
theorem hasStrictFDerivAt_log_real {x : ℂ} (h : x ∈ slitPlane) :
    HasStrictFDerivAt log (x⁻¹ • (1 : ℂ →L[ℝ] ℂ)) x :=
  (hasStrictDerivAt_log h).complexToReal_fderiv
/-
**Complex.contDiffAt_log** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：contDiffAt_log {x : Complex} (h : x in slitPlane) {n : WithTop Nat∞} : Con
tDiffAt Complex n log x
参数：h : x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.contDiffAt_symm_deriv`：OpenPartialHomeomorph.contD
iffAt_symm_deriv [CompleteSpace 𝕜] (f : OpenPartialHomeomorph 𝕜 𝕜) {f₀' a : 𝕜} (
h₀ : f₀' != 0) (ha : a in f.targe…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `Complex.hasDerivAt_exp`：hasDerivAt_exp (x : Complex) : HasDerivAt exp (e
xp x) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
-/
theorem contDiffAt_log {x : ℂ} (h : x ∈ slitPlane) {n : WithTop ℕ∞} : ContDiffAt ℂ n log x :=
  expOpenPartialHomeomorph.contDiffAt_symm_deriv (exp_ne_zero <| log x) h (hasDerivAt_exp _)
    contDiff_exp.contDiffAt
/-
**Complex.deriv_log** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：deriv_log {x : Complex} (h : x in slitPlane) : deriv log x = x⁻¹
参数：h : x in slitPlane。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `Complex.hasDerivAt_log`：hasDerivAt_log {z : Complex} (hz : z in slitPlan
e) : HasDerivAt log z⁻¹ z
-/
theorem deriv_log {x : ℂ} (h : x ∈ slitPlane) : deriv log x = x⁻¹ :=
  (hasDerivAt_log h).deriv

end Complex

section LogDeriv

open Complex Filter

open scoped Topology

variable {α : Type*} [TopologicalSpace α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-
**HasStrictFDerivAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.clog {f : E -> Complex} {f' : StrongDual Complex E} {x :
 E} (h₁ : HasStrictFDerivAt f f' x) (h₂ : f x in slitPlane) : HasStrictFDerivAt 
(fun t => log (f t)) ((f x)⁻¹ • f') x
参数：h₁ : HasStrictFDerivAt f f' x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Complex.hasStrictDerivAt_log`：hasStrictDerivAt_log {x : Complex} (h : x 
in slitPlane) : HasStrictDerivAt log x⁻¹ x
-/
theorem HasStrictFDerivAt.clog {f : E → ℂ} {f' : StrongDual ℂ E} {x : E}
    (h₁ : HasStrictFDerivAt f f' x) (h₂ : f x ∈ slitPlane) :
    HasStrictFDerivAt (fun t => log (f t)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAt_log h₂).comp_hasStrictFDerivAt x h₁
/-
**HasStrictDerivAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.clog {f : Complex -> Complex} {f' x : Complex} (h₁ : HasS
trictDerivAt f f' x) (h₂ : f x in slitPlane) : HasStrictDerivAt (fun t => log (f
 t)) (f' / f x) x
参数：h₁ : HasStrictDerivAt f f' x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `Complex.hasStrictDerivAt_log`：hasStrictDerivAt_log {x : Complex} (h : x 
in slitPlane) : HasStrictDerivAt log x⁻¹ x
-/
theorem HasStrictDerivAt.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : HasStrictDerivAt f f' x)
    (h₂ : f x ∈ slitPlane) : HasStrictDerivAt (fun t => log (f t)) (f' / f x) x := by
  rw [div_eq_inv_mul]; exact (hasStrictDerivAt_log h₂).comp x h₁
/-
**HasStrictDerivAt.clog_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.clog_real {f : Real -> Complex} {x : Real} {f' : Complex}
 (h₁ : HasStrictDerivAt f f' x) (h₂ : f x in slitPlane) : HasStrictDerivAt (fun 
t => log (f t)) (f' / f x) x
参数：h₁ : HasStrictDerivAt f f' x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `HasStrictFDerivAt.comp_hasStrictDerivAt`：HasStrictFDerivAt.comp_hasStric
tDerivAt (hl : HasStrictFDerivAt l l' (f x)) (hf : HasStrictDerivAt f f' x) : Ha
sStrictDerivAt (l ∘ f) (l' f'…
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
· 使用定理 `Complex.hasStrictFDerivAt_log_real`：hasStrictFDerivAt_log_real {x : Comp
lex} (h : x in slitPlane) : HasStrictFDerivAt log (x⁻¹ • (1 : Complex ->L[Real] 
Complex)) x
-/
theorem HasStrictDerivAt.clog_real {f : ℝ → ℂ} {x : ℝ} {f' : ℂ} (h₁ : HasStrictDerivAt f f' x)
    (h₂ : f x ∈ slitPlane) : HasStrictDerivAt (fun t => log (f t)) (f' / f x) x := by
  simpa only [div_eq_inv_mul] using! (hasStrictFDerivAt_log_real h₂).comp_hasStrictDerivAt x h₁
/-
**HasFDerivAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.clog {f : E -> Complex} {f' : StrongDual Complex E} {x : E} (h
₁ : HasFDerivAt f f' x) (h₂ : f x in slitPlane) : HasFDerivAt (fun t => log (f t
)) ((f x)⁻¹ • f') x
参数：h₁ : HasFDerivAt f f' x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_log`：hasStrictDerivAt_log {x : Complex} (h : x 
in slitPlane) : HasStrictDerivAt log x⁻¹ x
-/
theorem HasFDerivAt.clog {f : E → ℂ} {f' : StrongDual ℂ E} {x : E} (h₁ : HasFDerivAt f f' x)
    (h₂ : f x ∈ slitPlane) : HasFDerivAt (fun t => log (f t)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFDerivAt x h₁
/-
**HasDerivAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.clog {f : Complex -> Complex} {f' x : Complex} (h₁ : HasDerivAt
 f f' x) (h₂ : f x in slitPlane) : HasDerivAt (fun t => log (f t)) (f' / f x) x
参数：h₁ : HasDerivAt f f' x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_log`：hasStrictDerivAt_log {x : Complex} (h : x 
in slitPlane) : HasStrictDerivAt log x⁻¹ x
-/
theorem HasDerivAt.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : HasDerivAt f f' x)
    (h₂ : f x ∈ slitPlane) : HasDerivAt (fun t => log (f t)) (f' / f x) x := by
  rw [div_eq_inv_mul]; exact (hasStrictDerivAt_log h₂).hasDerivAt.comp x h₁
/-
**HasDerivAt.clog_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.clog_real {f : Real -> Complex} {x : Real} {f' : Complex} (h₁ :
 HasDerivAt f f' x) (h₂ : f x in slitPlane) : HasDerivAt (fun t => log (f t)) (f
' / f x) x
参数：h₁ : HasDerivAt f f' x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `HasFDerivAt.comp_hasDerivAt`：HasFDerivAt.comp_hasDerivAt (hl : HasFDeriv
At l l' (f x)) (hf : HasDerivAt f f' x) : HasDerivAt (l ∘ f) (l' f') x
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
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `Complex.hasStrictFDerivAt_log_real`：hasStrictFDerivAt_log_real {x : Comp
lex} (h : x in slitPlane) : HasStrictFDerivAt log (x⁻¹ • (1 : Complex ->L[Real] 
Complex)) x
-/
theorem HasDerivAt.clog_real {f : ℝ → ℂ} {x : ℝ} {f' : ℂ} (h₁ : HasDerivAt f f' x)
    (h₂ : f x ∈ slitPlane) : HasDerivAt (fun t => log (f t)) (f' / f x) x := by
  simpa only [div_eq_inv_mul] using!
    (hasStrictFDerivAt_log_real h₂).hasFDerivAt.comp_hasDerivAt x h₁
/-
**DifferentiableAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.clog {f : E -> Complex} {x : E} (h₁ : DifferentiableAt Co
mplex f x) (h₂ : f x in slitPlane) : DifferentiableAt Complex (fun t => log (f t
)) x
参数：h₁ : DifferentiableAt Complex f x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
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
· 使用定理 `HasFDerivAt.clog`：HasFDerivAt.clog {f : E -> Complex} {f' : StrongDual C
omplex E} {x : E} (h₁ : HasFDerivAt f f' x) (h₂ : f x in slitPlane) : HasFDerivA
t (fun…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.clog {f : E → ℂ} {x : E} (h₁ : DifferentiableAt ℂ f x)
    (h₂ : f x ∈ slitPlane) : DifferentiableAt ℂ (fun t => log (f t)) x :=
  (h₁.hasFDerivAt.clog h₂).differentiableAt
/-
**HasFDerivWithinAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.clog {f : E -> Complex} {f' : StrongDual Complex E} {s :
 Set E} {x : E} (h₁ : HasFDerivWithinAt f f' s x) (h₂ : f x in slitPlane) : HasF
DerivWithinAt (fun t => log (f t)) ((f x)⁻¹ • f') s x
参数：h₁ : HasFDerivWithinAt f f' s x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_log`：hasStrictDerivAt_log {x : Complex} (h : x 
in slitPlane) : HasStrictDerivAt log x⁻¹ x
-/
theorem HasFDerivWithinAt.clog {f : E → ℂ} {f' : StrongDual ℂ E} {s : Set E} {x : E}
    (h₁ : HasFDerivWithinAt f f' s x) (h₂ : f x ∈ slitPlane) :
    HasFDerivWithinAt (fun t => log (f t)) ((f x)⁻¹ • f') s x :=
  (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFDerivWithinAt x h₁
/-
**HasDerivWithinAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.clog {f : Complex -> Complex} {f' x : Complex} {s : Set C
omplex} (h₁ : HasDerivWithinAt f f' s x) (h₂ : f x in slitPlane) : HasDerivWithi
nAt (fun t => log (f t)) (f' / f x) s x
参数：h₁ : HasDerivWithinAt f f' s x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_log`：hasStrictDerivAt_log {x : Complex} (h : x 
in slitPlane) : HasStrictDerivAt log x⁻¹ x
-/
theorem HasDerivWithinAt.clog {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ} (h₁ : HasDerivWithinAt f f' s x)
    (h₂ : f x ∈ slitPlane) : HasDerivWithinAt (fun t => log (f t)) (f' / f x) s x := by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasDerivWithinAt x h₁
/-
**HasDerivWithinAt.clog_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.clog_real {f : Real -> Complex} {s : Set Real} {x : Real}
 {f' : Complex} (h₁ : HasDerivWithinAt f f' s x) (h₂ : f x in slitPlane) : HasDe
rivWithinAt (fun t => log (f t)) (f' / f x) s x
参数：h₁ : HasDerivWithinAt f f' s x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `HasFDerivAt.comp_hasDerivWithinAt`：HasFDerivAt.comp_hasDerivWithinAt (hl
 : HasFDerivAt l l' (f x)) (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (
l ∘ f) (l' f') s x
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
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `Complex.hasStrictFDerivAt_log_real`：hasStrictFDerivAt_log_real {x : Comp
lex} (h : x in slitPlane) : HasStrictFDerivAt log (x⁻¹ • (1 : Complex ->L[Real] 
Complex)) x
-/
theorem HasDerivWithinAt.clog_real {f : ℝ → ℂ} {s : Set ℝ} {x : ℝ} {f' : ℂ}
    (h₁ : HasDerivWithinAt f f' s x) (h₂ : f x ∈ slitPlane) :
    HasDerivWithinAt (fun t => log (f t)) (f' / f x) s x := by
  simpa only [div_eq_inv_mul] using!
    (hasStrictFDerivAt_log_real h₂).hasFDerivAt.comp_hasDerivWithinAt x h₁
/-
**DifferentiableWithinAt.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.clog {f : E -> Complex} {s : Set E} {x : E} (h₁ : D
ifferentiableWithinAt Complex f s x) (h₂ : f x in slitPlane) : DifferentiableWit
hinAt Complex (fun t => log (f t)) s x
参数：h₁ : DifferentiableWithinAt Complex f s x；h₂ : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
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
· 使用定理 `HasFDerivWithinAt.clog`：HasFDerivWithinAt.clog {f : E -> Complex} {f' : 
StrongDual Complex E} {s : Set E} {x : E} (h₁ : HasFDerivWithinAt f f' s x) (h₂ 
: f x in sli…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.clog {f : E → ℂ} {s : Set E} {x : E}
    (h₁ : DifferentiableWithinAt ℂ f s x) (h₂ : f x ∈ slitPlane) :
    DifferentiableWithinAt ℂ (fun t => log (f t)) s x :=
  (h₁.hasFDerivWithinAt.clog h₂).differentiableWithinAt
/-
**DifferentiableOn.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.clog {f : E -> Complex} {s : Set E} (h₁ : DifferentiableO
n Complex f s) (h₂ : forall x in s, f x in slitPlane) : DifferentiableOn Complex
 (fun t => log (f t)) s
参数：h₁ : DifferentiableOn Complex f s；h₂ : forall x in s, f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.clog`：DifferentiableWithinAt.clog {f : E -> Compl
ex} {s : Set E} {x : E} (h₁ : DifferentiableWithinAt Complex f s x) (h₂ : f x in
 slitPlane) : Dif…
-/
theorem DifferentiableOn.clog {f : E → ℂ} {s : Set E} (h₁ : DifferentiableOn ℂ f s)
    (h₂ : ∀ x ∈ s, f x ∈ slitPlane) : DifferentiableOn ℂ (fun t => log (f t)) s :=
  fun x hx => (h₁ x hx).clog (h₂ x hx)
/-
**Differentiable.clog** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.clog {f : E -> Complex} (h₁ : Differentiable Complex f) (h₂
 : forall x, f x in slitPlane) : Differentiable Complex fun t => log (f t)
参数：h₁ : Differentiable Complex f；h₂ : forall x, f x in slitPlane。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.clog`：DifferentiableAt.clog {f : E -> Complex} {x : E} 
(h₁ : DifferentiableAt Complex f x) (h₂ : f x in slitPlane) : DifferentiableAt C
omplex (fun…
-/
theorem Differentiable.clog {f : E → ℂ} (h₁ : Differentiable ℂ f)
    (h₂ : ∀ x, f x ∈ slitPlane) : Differentiable ℂ fun t => log (f t) := fun x =>
  (h₁ x).clog (h₂ x)

/-- The derivative of `log ∘ f` is the logarithmic derivative provided `f` is differentiable and
we are on the slitPlane. -/
/-
**Complex.deriv_log_comp_eq_logDeriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Complex.deriv_log_comp_eq_logDeriv {f : Complex -> Complex} {x : Complex} 
(h₁ : DifferentiableAt Complex f x) (h₂ : f x in Complex.slitPlane) : deriv (Com
plex.log ∘ f) x = logDeriv f x
参数：h₁ : DifferentiableAt Complex f x；h₂ : f x in Complex.slitPlane。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.clog`：HasDerivAt.clog {f : Complex -> Complex} {f' x : Comple
x} (h₁ : HasDerivAt f f' x) (h₂ : f x in slitPlane) : HasDerivAt (fun t => log (
f t))…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The derivative of `log ∘ f` is the logarithmic derivative provided `f` is differ
entiable and
we are on the slitPlane.
-/
lemma Complex.deriv_log_comp_eq_logDeriv {f : ℂ → ℂ} {x : ℂ} (h₁ : DifferentiableAt ℂ f x)
    (h₂ : f x ∈ Complex.slitPlane) : deriv (Complex.log ∘ f) x = logDeriv f x := by
  have A := (HasDerivAt.clog h₁.hasDerivAt h₂).deriv
  rw [← h₁.hasDerivAt.deriv] at A
  simp only [logDeriv, Pi.div_apply, ← A, Function.comp_def]

end LogDeriv

