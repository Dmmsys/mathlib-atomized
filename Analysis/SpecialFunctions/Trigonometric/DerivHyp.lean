/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Order.Monotone.Odd
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Differentiability of hyperbolic trigonometric functions

## Main statements

The differentiability of the hyperbolic trigonometric functions is proved, and their derivatives are
computed.

## Tags

sinh, cosh, tanh
-/

public section

noncomputable section

open scoped Asymptotics Topology Filter
open Set

namespace Complex

/-- The complex hyperbolic sine function is everywhere strictly differentiable, with the derivative
`cosh x`. -/
/-
**Complex.hasStrictDerivAt_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictDerivAt_sinh (x : Complex) : HasStrictDerivAt sinh (cosh x) x
参数：x : Complex。
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
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `mul_neg_one`：mul_neg_one (a : α) : a * -1 = -a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `HasStrictDerivAt.mul_const`：HasStrictDerivAt.mul_const (hc : HasStrictDe
rivAt c c' x) (d : 𝔸) : HasStrictDerivAt (fun y => c y * d) (c' * d) x
· 使用定理 `HasStrictDerivAt.sub`：HasStrictDerivAt.sub (hf : HasStrictDerivAt f f' x
) (hg : HasStrictDerivAt g g' x) : HasStrictDerivAt (f - g) (f' - g') x
· 使用定理 `Complex.hasStrictDerivAt_exp`：hasStrictDerivAt_exp (x : Complex) : HasSt
rictDerivAt exp (exp x) x
· 使用定理 `HasStrictDerivAt.cexp`：HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f'
 x) : HasStrictDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x
· 使用定理 `HasStrictDerivAt.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField
 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f
 : 𝕜 → F} {f' …
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x

--- 原说明 ---
The complex hyperbolic sine function is everywhere strictly differentiable, with
 the derivative
`cosh x`.
-/
theorem hasStrictDerivAt_sinh (x : ℂ) : HasStrictDerivAt sinh (cosh x) x := by
  simp only [cosh, div_eq_mul_inv]
  convert!
    ((hasStrictDerivAt_exp x).sub (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : ℂ)⁻¹ using 1
  rw [id, mul_neg_one, sub_eq_add_neg, neg_neg]

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative
`cosh x`. -/
/-
**Complex.hasDerivAt_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasDerivAt_sinh (x : Complex) : HasDerivAt sinh (cosh x) x
参数：x : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_sinh`：hasStrictDerivAt_sinh (x : Complex) : Has
StrictDerivAt sinh (cosh x) x

--- 原说明 ---
The complex hyperbolic sine function is everywhere differentiable, with the deri
vative
`cosh x`.
-/
theorem hasDerivAt_sinh (x : ℂ) : HasDerivAt sinh (cosh x) x :=
  (hasStrictDerivAt_sinh x).hasDerivAt
/-
**Complex.isEquivalent_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isEquivalent_sinh : sinh ~[𝓝 0] id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.sinh_zero`：sinh_zero : sinh 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Complex.cosh_zero`：cosh_zero : cosh 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.isLittleO`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `Complex.hasDerivAt_sinh`：hasDerivAt_sinh (x : Complex) : HasDerivAt sinh
 (cosh x) x
-/
theorem isEquivalent_sinh : sinh ~[𝓝 0] id := by simpa using! (hasDerivAt_sinh 0).isLittleO

@[fun_prop]
/-
**Complex.contDiff_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：contDiff_sinh {n} : ContDiff Complex n sinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.div_const`：ContDiff.div_const {f : E -> 𝕜'} {n} (hf : ContDiff 
𝕜 n f) (c : 𝕜') : ContDiff 𝕜 n fun x => f x / c
· 使用定理 `ContDiff.sub`：ContDiff.sub {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x - g x
· 使用定理 `Complex.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
· 使用定理 `ContDiff.cexp`：ContDiff.cexp {n} (h : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun
 x => Complex.exp (f x)
· 使用定理 `contDiff_neg`：contDiff_neg : ContDiff 𝕜 n fun p : F => -p
-/
theorem contDiff_sinh {n} : ContDiff ℂ n sinh :=
  (contDiff_exp.sub contDiff_neg.cexp).div_const _

@[simp]
/-
**Complex.differentiable_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiable_sinh : Differentiable Complex sinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Complex.hasDerivAt_sinh`：hasDerivAt_sinh (x : Complex) : HasDerivAt sinh
 (cosh x) x
-/
theorem differentiable_sinh : Differentiable ℂ sinh := fun x => (hasDerivAt_sinh x).differentiableAt

@[simp]
/-
**Complex.differentiableAt_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiableAt_sinh {x : Complex} : DifferentiableAt Complex sinh x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.differentiable_sinh`：differentiable_sinh : Differentiable Comple
x sinh
-/
theorem differentiableAt_sinh {x : ℂ} : DifferentiableAt ℂ sinh x :=
  differentiable_sinh x

/-- The function `Complex.sinh` is complex analytic. -/
@[fun_prop]
/-
**Complex.analyticAt_sinh** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticAt_sinh {x : Complex} : AnalyticAt Complex sinh x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.analyticAt`：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : 
AnalyticAt 𝕜 f x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_sinh`：contDiff_sinh {n} : ContDiff Complex n sinh

--- 原说明 ---
The function `Complex.sinh` is complex analytic.
-/
lemma analyticAt_sinh {x : ℂ} : AnalyticAt ℂ sinh x :=
  contDiff_sinh.contDiffAt.analyticAt

/-- The function `Complex.sinh` is complex analytic. -/
/-
**Complex.analyticWithinAt_sinh** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticWithinAt_sinh {x : Complex} {s : Set Complex} : AnalyticWithinAt C
omplex sinh s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Complex.contDiff_sinh`：contDiff_sinh {n} : ContDiff Complex n sinh

--- 原说明 ---
The function `Complex.sinh` is complex analytic.
-/
lemma analyticWithinAt_sinh {x : ℂ} {s : Set ℂ} : AnalyticWithinAt ℂ sinh s x :=
  contDiff_sinh.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.sinh` is complex analytic. -/
/-
**Complex.analyticOnNhd_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：analyticOnNhd_sinh {s : Set Complex} : AnalyticOnNhd Complex sinh s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.analyticAt_sinh`：analyticAt_sinh {x : Complex} : AnalyticAt Comp
lex sinh x

--- 原说明 ---
The function `Complex.sinh` is complex analytic.
-/
theorem analyticOnNhd_sinh {s : Set ℂ} : AnalyticOnNhd ℂ sinh s :=
  fun _ _ ↦ analyticAt_sinh

/-- The function `Complex.sinh` is complex analytic. -/
/-
**Complex.analyticOn_sinh** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticOn_sinh {s : Set Complex} : AnalyticOn Complex sinh s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Complex.contDiff_sinh`：contDiff_sinh {n} : ContDiff Complex n sinh

--- 原说明 ---
The function `Complex.sinh` is complex analytic.
-/
lemma analyticOn_sinh {s : Set ℂ} : AnalyticOn ℂ sinh s :=
  contDiff_sinh.contDiffOn.analyticOn

@[simp]
/-
**Complex.deriv_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：deriv_sinh : deriv sinh = cosh
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Complex.hasDerivAt_sinh`：hasDerivAt_sinh (x : Complex) : HasDerivAt sinh
 (cosh x) x
-/
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (hasDerivAt_sinh x).deriv

/-- The complex hyperbolic cosine function is everywhere strictly differentiable, with the
derivative `sinh x`. -/
/-
**Complex.hasStrictDerivAt_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictDerivAt_cosh (x : Complex) : HasStrictDerivAt cosh (sinh x) x
参数：x : Complex。
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
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `mul_neg_one`：mul_neg_one (a : α) : a * -1 = -a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HasStrictDerivAt.mul_const`：HasStrictDerivAt.mul_const (hc : HasStrictDe
rivAt c c' x) (d : 𝔸) : HasStrictDerivAt (fun y => c y * d) (c' * d) x
· 使用定理 `HasStrictDerivAt.add`：HasStrictDerivAt.add (hf : HasStrictDerivAt f f' x
) (hg : HasStrictDerivAt g g' x) : HasStrictDerivAt (f + g) (f' + g') x
· 使用定理 `Complex.hasStrictDerivAt_exp`：hasStrictDerivAt_exp (x : Complex) : HasSt
rictDerivAt exp (exp x) x
· 使用定理 `HasStrictDerivAt.cexp`：HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f'
 x) : HasStrictDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x
· 使用定理 `HasStrictDerivAt.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField
 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f
 : 𝕜 → F} {f' …
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x

--- 原说明 ---
The complex hyperbolic cosine function is everywhere strictly differentiable, wi
th the
derivative `sinh x`.
-/
theorem hasStrictDerivAt_cosh (x : ℂ) : HasStrictDerivAt cosh (sinh x) x := by
  simp only [sinh, div_eq_mul_inv]
  convert!
    ((hasStrictDerivAt_exp x).add (hasStrictDerivAt_id x).fun_neg.cexp).mul_const (2 : ℂ)⁻¹ using 1
  rw [id, mul_neg_one, sub_eq_add_neg]

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative
`sinh x`. -/
/-
**Complex.hasDerivAt_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasDerivAt_cosh (x : Complex) : HasDerivAt cosh (sinh x) x
参数：x : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_cosh`：hasStrictDerivAt_cosh (x : Complex) : Has
StrictDerivAt cosh (sinh x) x

--- 原说明 ---
The complex hyperbolic cosine function is everywhere differentiable, with the de
rivative
`sinh x`.
-/
theorem hasDerivAt_cosh (x : ℂ) : HasDerivAt cosh (sinh x) x :=
  (hasStrictDerivAt_cosh x).hasDerivAt

@[fun_prop]
/-
**Complex.contDiff_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：contDiff_cosh {n} : ContDiff Complex n cosh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.div_const`：ContDiff.div_const {f : E -> 𝕜'} {n} (hf : ContDiff 
𝕜 n f) (c : 𝕜') : ContDiff 𝕜 n fun x => f x / c
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `Complex.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
· 使用定理 `ContDiff.cexp`：ContDiff.cexp {n} (h : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun
 x => Complex.exp (f x)
· 使用定理 `contDiff_neg`：contDiff_neg : ContDiff 𝕜 n fun p : F => -p
-/
theorem contDiff_cosh {n} : ContDiff ℂ n cosh :=
  (contDiff_exp.add contDiff_neg.cexp).div_const _

@[simp]
/-
**Complex.differentiable_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiable_cosh : Differentiable Complex cosh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Complex.hasDerivAt_cosh`：hasDerivAt_cosh (x : Complex) : HasDerivAt cosh
 (sinh x) x
-/
theorem differentiable_cosh : Differentiable ℂ cosh := fun x => (hasDerivAt_cosh x).differentiableAt

@[simp]
/-
**Complex.differentiableAt_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiableAt_cosh {x : Complex} : DifferentiableAt Complex cosh x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.differentiable_cosh`：differentiable_cosh : Differentiable Comple
x cosh
-/
theorem differentiableAt_cosh {x : ℂ} : DifferentiableAt ℂ cosh x :=
  differentiable_cosh x

/-- The function `Complex.cosh` is complex analytic. -/
@[fun_prop]
/-
**Complex.analyticAt_cosh** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticAt_cosh {x : Complex} : AnalyticAt Complex cosh x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.analyticAt`：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : 
AnalyticAt 𝕜 f x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_cosh`：contDiff_cosh {n} : ContDiff Complex n cosh

--- 原说明 ---
The function `Complex.cosh` is complex analytic.
-/
lemma analyticAt_cosh {x : ℂ} : AnalyticAt ℂ cosh x :=
  contDiff_cosh.contDiffAt.analyticAt

/-- The function `Complex.cosh` is complex analytic. -/
/-
**Complex.analyticWithinAt_cosh** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticWithinAt_cosh {x : Complex} {s : Set Complex} : AnalyticWithinAt C
omplex cosh s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Complex.contDiff_cosh`：contDiff_cosh {n} : ContDiff Complex n cosh

--- 原说明 ---
The function `Complex.cosh` is complex analytic.
-/
lemma analyticWithinAt_cosh {x : ℂ} {s : Set ℂ} : AnalyticWithinAt ℂ cosh s x :=
  contDiff_cosh.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.cosh` is complex analytic. -/
/-
**Complex.analyticOnNhd_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：analyticOnNhd_cosh {s : Set Complex} : AnalyticOnNhd Complex cosh s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.analyticAt_cosh`：analyticAt_cosh {x : Complex} : AnalyticAt Comp
lex cosh x

--- 原说明 ---
The function `Complex.cosh` is complex analytic.
-/
theorem analyticOnNhd_cosh {s : Set ℂ} : AnalyticOnNhd ℂ cosh s :=
  fun _ _ ↦ analyticAt_cosh

/-- The function `Complex.cosh` is complex analytic. -/
/-
**Complex.analyticOn_cosh** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticOn_cosh {s : Set Complex} : AnalyticOn Complex cosh s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Complex.contDiff_cosh`：contDiff_cosh {n} : ContDiff Complex n cosh

--- 原说明 ---
The function `Complex.cosh` is complex analytic.
-/
lemma analyticOn_cosh {s : Set ℂ} : AnalyticOn ℂ cosh s :=
  contDiff_cosh.contDiffOn.analyticOn

@[simp]
/-
**Complex.deriv_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：deriv_cosh : deriv cosh = sinh
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Complex.hasDerivAt_cosh`：hasDerivAt_cosh (x : Complex) : HasDerivAt cosh
 (sinh x) x
-/
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (hasDerivAt_cosh x).deriv

end Complex

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : ℂ → ℂ` -/

variable {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ}

/-! #### `Complex.cosh` -/

/-
**HasStrictDerivAt.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.ccosh (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (
fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x
参数：hf : HasStrictDerivAt f f' x。
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
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `Complex.hasStrictDerivAt_cosh`：hasStrictDerivAt_cosh (x : Complex) : Has
StrictDerivAt cosh (sinh x) x

--- 原说明 ---
#### `Complex.cosh`
-/
theorem HasStrictDerivAt.ccosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.hasStrictDerivAt_cosh (f x)).comp x hf
/-
**HasDerivAt.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.ccosh (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Complex.c
osh (f x)) (Complex.sinh (f x) * f') x
参数：hf : HasDerivAt f f' x。
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
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Complex.hasDerivAt_cosh`：hasDerivAt_cosh (x : Complex) : HasDerivAt cosh
 (sinh x) x
-/
theorem HasDerivAt.ccosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x :=
  (Complex.hasDerivAt_cosh (f x)).comp x hf
/-
**HasDerivWithinAt.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.ccosh (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt
 (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') s x
参数：hf : HasDerivWithinAt f f' s x。
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
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `Complex.hasDerivAt_cosh`：hasDerivAt_cosh (x : Complex) : HasDerivAt cosh
 (sinh x) x
-/
theorem HasDerivWithinAt.ccosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') s x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf
/-
**derivWithin_ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_ccosh (hf : DifferentiableWithinAt Complex f s x) (hxs : Uniqu
eDiffWithinAt Complex s x) : derivWithin (fun x => Complex.cosh (f x)) s x = Com
plex.sinh (f x) * derivWithin f s x
参数：hf : DifferentiableWithinAt Complex f s x；hxs : UniqueDiffWithinAt Complex s 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.ccosh`：HasDerivWithinAt.ccosh (hf : HasDerivWithinAt f 
f' s x) : HasDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f
') s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.ccosh.derivWithin hxs

@[simp]
/-
**deriv_ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_ccosh (hc : DifferentiableAt Complex f x) : deriv (fun x => Complex.
cosh (f x)) x = Complex.sinh (f x) * deriv f x
参数：hc : DifferentiableAt Complex f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.ccosh`：HasDerivAt.ccosh (hf : HasDerivAt f f' x) : HasDerivAt
 (fun x => Complex.cosh (f x)) (Complex.sinh (f x) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_ccosh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) * deriv f x :=
  hc.hasDerivAt.ccosh.deriv

/-! #### `Complex.sinh` -/

/-
**HasStrictDerivAt.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.csinh (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (
fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x
参数：hf : HasStrictDerivAt f f' x。
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
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `Complex.hasStrictDerivAt_sinh`：hasStrictDerivAt_sinh (x : Complex) : Has
StrictDerivAt sinh (cosh x) x

--- 原说明 ---
#### `Complex.sinh`
-/
theorem HasStrictDerivAt.csinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.hasStrictDerivAt_sinh (f x)).comp x hf
/-
**HasDerivAt.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.csinh (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Complex.s
inh (f x)) (Complex.cosh (f x) * f') x
参数：hf : HasDerivAt f f' x。
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
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Complex.hasDerivAt_sinh`：hasDerivAt_sinh (x : Complex) : HasDerivAt sinh
 (cosh x) x
-/
theorem HasDerivAt.csinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x :=
  (Complex.hasDerivAt_sinh (f x)).comp x hf
/-
**HasDerivWithinAt.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.csinh (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt
 (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') s x
参数：hf : HasDerivWithinAt f f' s x。
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
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `Complex.hasDerivAt_sinh`：hasDerivAt_sinh (x : Complex) : HasDerivAt sinh
 (cosh x) x
-/
theorem HasDerivWithinAt.csinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') s x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf
/-
**derivWithin_csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_csinh (hf : DifferentiableWithinAt Complex f s x) (hxs : Uniqu
eDiffWithinAt Complex s x) : derivWithin (fun x => Complex.sinh (f x)) s x = Com
plex.cosh (f x) * derivWithin f s x
参数：hf : DifferentiableWithinAt Complex f s x；hxs : UniqueDiffWithinAt Complex s 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.csinh`：HasDerivWithinAt.csinh (hf : HasDerivWithinAt f 
f' s x) : HasDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f
') s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.csinh.derivWithin hxs

@[simp]
/-
**deriv_csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_csinh (hc : DifferentiableAt Complex f x) : deriv (fun x => Complex.
sinh (f x)) x = Complex.cosh (f x) * deriv f x
参数：hc : DifferentiableAt Complex f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.csinh`：HasDerivAt.csinh (hf : HasDerivAt f f' x) : HasDerivAt
 (fun x => Complex.sinh (f x)) (Complex.cosh (f x) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_csinh (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) * deriv f x :=
  hc.hasDerivAt.csinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : E → ℂ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {f' : StrongDual ℂ E}
  {x : E} {s : Set E}

/-! #### `Complex.cosh` -/

/-
**HasStrictFDerivAt.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.ccosh (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivA
t (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Complex.hasStrictDerivAt_cosh`：hasStrictDerivAt_cosh (x : Complex) : Has
StrictDerivAt cosh (sinh x) x

--- 原说明 ---
#### `Complex.cosh`
-/
theorem HasStrictFDerivAt.ccosh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf
/-
**HasFDerivAt.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.ccosh (hf : HasFDerivAt f f' x) : HasFDerivAt (fun x => Comple
x.cosh (f x)) (Complex.sinh (f x) • f') x
参数：hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Complex.hasDerivAt_cosh`：hasDerivAt_cosh (x : Complex) : HasDerivAt cosh
 (sinh x) x
-/
theorem HasFDerivAt.ccosh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf
/-
**HasFDerivWithinAt.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.ccosh (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithi
nAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') s x
参数：hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Complex.hasDerivAt_cosh`：hasDerivAt_cosh (x : Complex) : HasDerivAt cosh
 (sinh x) x
-/
theorem HasFDerivWithinAt.ccosh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') s x :=
  (Complex.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf
/-
**DifferentiableWithinAt.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.ccosh (hf : DifferentiableWithinAt Complex f s x) :
 DifferentiableWithinAt Complex (fun x => Complex.cosh (f x)) s x
参数：hf : DifferentiableWithinAt Complex f s x。
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
· 使用定理 `HasFDerivWithinAt.ccosh`：HasFDerivWithinAt.ccosh (hf : HasFDerivWithinAt
 f f' s x) : HasFDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x)
 • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.ccosh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.cosh (f x)) s x :=
  hf.hasFDerivWithinAt.ccosh.differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.ccosh (hc : DifferentiableAt Complex f x) : Differentiabl
eAt Complex (fun x => Complex.cosh (f x)) x
参数：hc : DifferentiableAt Complex f x。
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
· 使用定理 `HasFDerivAt.ccosh`：HasFDerivAt.ccosh (hf : HasFDerivAt f f' x) : HasFDer
ivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.ccosh (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.cosh (f x)) x :=
  hc.hasFDerivAt.ccosh.differentiableAt
/-
**DifferentiableOn.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.ccosh (hc : DifferentiableOn Complex f s) : Differentiabl
eOn Complex (fun x => Complex.cosh (f x)) s
参数：hc : DifferentiableOn Complex f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.ccosh`：DifferentiableWithinAt.ccosh (hf : Differe
ntiableWithinAt Complex f s x) : DifferentiableWithinAt Complex (fun x => Comple
x.cosh (f x)) s x
-/
theorem DifferentiableOn.ccosh (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.cosh (f x)) s := fun x h => (hc x h).ccosh

@[simp, fun_prop]
/-
**Differentiable.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.ccosh (hc : Differentiable Complex f) : Differentiable Comp
lex fun x => Complex.cosh (f x)
参数：hc : Differentiable Complex f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.ccosh`：DifferentiableAt.ccosh (hc : DifferentiableAt Co
mplex f x) : DifferentiableAt Complex (fun x => Complex.cosh (f x)) x
-/
theorem Differentiable.ccosh (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.cosh (f x) := fun x => (hc x).ccosh
/-
**fderivWithin_ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_ccosh (hf : DifferentiableWithinAt Complex f s x) (hxs : Uniq
ueDiffWithinAt Complex s x) : fderivWithin Complex (fun x => Complex.cosh (f x))
 s x = Complex.sinh (f x) • fderivWithin Complex f s x
参数：hf : DifferentiableWithinAt Complex f s x；hxs : UniqueDiffWithinAt Complex s 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `HasFDerivWithinAt.ccosh`：HasFDerivWithinAt.ccosh (hf : HasFDerivWithinAt
 f f' s x) : HasFDerivWithinAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x)
 • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_ccosh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.cosh (f x)) s x = Complex.sinh (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.ccosh.fderivWithin hxs

@[simp]
/-
**fderiv_ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_ccosh (hc : DifferentiableAt Complex f x) : fderiv Complex (fun x =
> Complex.cosh (f x)) x = Complex.sinh (f x) • fderiv Complex f x
参数：hc : DifferentiableAt Complex f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `HasFDerivAt.ccosh`：HasFDerivAt.ccosh (hf : HasFDerivAt f f' x) : HasFDer
ivAt (fun x => Complex.cosh (f x)) (Complex.sinh (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_ccosh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.cosh (f x)) x = Complex.sinh (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.ccosh.fderiv
/-
**ContDiff.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.ccosh {n} (h : ContDiff Complex n f) : ContDiff Complex n fun x =
> Complex.cosh (f x)
参数：h : ContDiff Complex n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Complex.contDiff_cosh`：contDiff_cosh {n} : ContDiff Complex n cosh
-/
theorem ContDiff.ccosh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.cosh (f x) :=
  Complex.contDiff_cosh.comp h
/-
**ContDiffAt.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.ccosh {n} (hf : ContDiffAt Complex n f x) : ContDiffAt Complex 
n (fun x => Complex.cosh (f x)) x
参数：hf : ContDiffAt Complex n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_cosh`：contDiff_cosh {n} : ContDiff Complex n cosh
-/
theorem ContDiffAt.ccosh {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.cosh (f x)) x :=
  Complex.contDiff_cosh.contDiffAt.comp x hf
/-
**ContDiffOn.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.ccosh {n} (hf : ContDiffOn Complex n f s) : ContDiffOn Complex 
n (fun x => Complex.cosh (f x)) s
参数：hf : ContDiffOn Complex n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `Complex.contDiff_cosh`：contDiff_cosh {n} : ContDiff Complex n cosh
-/
theorem ContDiffOn.ccosh {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.cosh (f x)) s :=
  Complex.contDiff_cosh.comp_contDiffOn hf
/-
**ContDiffWithinAt.ccosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.ccosh {n} (hf : ContDiffWithinAt Complex n f s x) : ContD
iffWithinAt Complex n (fun x => Complex.cosh (f x)) s x
参数：hf : ContDiffWithinAt Complex n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_cosh`：contDiff_cosh {n} : ContDiff Complex n cosh
-/
theorem ContDiffWithinAt.ccosh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.cosh (f x)) s x :=
  Complex.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf

/-! #### `Complex.sinh` -/

/-
**HasStrictFDerivAt.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.csinh (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivA
t (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Complex.hasStrictDerivAt_sinh`：hasStrictDerivAt_sinh (x : Complex) : Has
StrictDerivAt sinh (cosh x) x

--- 原说明 ---
#### `Complex.sinh`
-/
theorem HasStrictFDerivAt.csinh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf
/-
**HasFDerivAt.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.csinh (hf : HasFDerivAt f f' x) : HasFDerivAt (fun x => Comple
x.sinh (f x)) (Complex.cosh (f x) • f') x
参数：hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Complex.hasDerivAt_sinh`：hasDerivAt_sinh (x : Complex) : HasDerivAt sinh
 (cosh x) x
-/
theorem HasFDerivAt.csinh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf
/-
**HasFDerivWithinAt.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.csinh (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithi
nAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') s x
参数：hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Complex.hasDerivAt_sinh`：hasDerivAt_sinh (x : Complex) : HasDerivAt sinh
 (cosh x) x
-/
theorem HasFDerivWithinAt.csinh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') s x :=
  (Complex.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf
/-
**DifferentiableWithinAt.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.csinh (hf : DifferentiableWithinAt Complex f s x) :
 DifferentiableWithinAt Complex (fun x => Complex.sinh (f x)) s x
参数：hf : DifferentiableWithinAt Complex f s x。
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
· 使用定理 `HasFDerivWithinAt.csinh`：HasFDerivWithinAt.csinh (hf : HasFDerivWithinAt
 f f' s x) : HasFDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x)
 • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.csinh (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.sinh (f x)) s x :=
  hf.hasFDerivWithinAt.csinh.differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.csinh (hc : DifferentiableAt Complex f x) : Differentiabl
eAt Complex (fun x => Complex.sinh (f x)) x
参数：hc : DifferentiableAt Complex f x。
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
· 使用定理 `HasFDerivAt.csinh`：HasFDerivAt.csinh (hf : HasFDerivAt f f' x) : HasFDer
ivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.csinh (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.sinh (f x)) x :=
  hc.hasFDerivAt.csinh.differentiableAt
/-
**DifferentiableOn.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.csinh (hc : DifferentiableOn Complex f s) : Differentiabl
eOn Complex (fun x => Complex.sinh (f x)) s
参数：hc : DifferentiableOn Complex f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.csinh`：DifferentiableWithinAt.csinh (hf : Differe
ntiableWithinAt Complex f s x) : DifferentiableWithinAt Complex (fun x => Comple
x.sinh (f x)) s x
-/
theorem DifferentiableOn.csinh (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.sinh (f x)) s := fun x h => (hc x h).csinh

@[simp, fun_prop]
/-
**Differentiable.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.csinh (hc : Differentiable Complex f) : Differentiable Comp
lex fun x => Complex.sinh (f x)
参数：hc : Differentiable Complex f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.csinh`：DifferentiableAt.csinh (hc : DifferentiableAt Co
mplex f x) : DifferentiableAt Complex (fun x => Complex.sinh (f x)) x
-/
theorem Differentiable.csinh (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.sinh (f x) := fun x => (hc x).csinh
/-
**fderivWithin_csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_csinh (hf : DifferentiableWithinAt Complex f s x) (hxs : Uniq
ueDiffWithinAt Complex s x) : fderivWithin Complex (fun x => Complex.sinh (f x))
 s x = Complex.cosh (f x) • fderivWithin Complex f s x
参数：hf : DifferentiableWithinAt Complex f s x；hxs : UniqueDiffWithinAt Complex s 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `HasFDerivWithinAt.csinh`：HasFDerivWithinAt.csinh (hf : HasFDerivWithinAt
 f f' s x) : HasFDerivWithinAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x)
 • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_csinh (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.sinh (f x)) s x = Complex.cosh (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.csinh.fderivWithin hxs

@[simp]
/-
**fderiv_csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_csinh (hc : DifferentiableAt Complex f x) : fderiv Complex (fun x =
> Complex.sinh (f x)) x = Complex.cosh (f x) • fderiv Complex f x
参数：hc : DifferentiableAt Complex f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `HasFDerivAt.csinh`：HasFDerivAt.csinh (hf : HasFDerivAt f f' x) : HasFDer
ivAt (fun x => Complex.sinh (f x)) (Complex.cosh (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_csinh (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.sinh (f x)) x = Complex.cosh (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.csinh.fderiv
/-
**ContDiff.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.csinh {n} (h : ContDiff Complex n f) : ContDiff Complex n fun x =
> Complex.sinh (f x)
参数：h : ContDiff Complex n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Complex.contDiff_sinh`：contDiff_sinh {n} : ContDiff Complex n sinh
-/
theorem ContDiff.csinh {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.sinh (f x) :=
  Complex.contDiff_sinh.comp h
/-
**ContDiffAt.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.csinh {n} (hf : ContDiffAt Complex n f x) : ContDiffAt Complex 
n (fun x => Complex.sinh (f x)) x
参数：hf : ContDiffAt Complex n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_sinh`：contDiff_sinh {n} : ContDiff Complex n sinh
-/
theorem ContDiffAt.csinh {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.sinh (f x)) x :=
  Complex.contDiff_sinh.contDiffAt.comp x hf
/-
**ContDiffOn.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.csinh {n} (hf : ContDiffOn Complex n f s) : ContDiffOn Complex 
n (fun x => Complex.sinh (f x)) s
参数：hf : ContDiffOn Complex n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `Complex.contDiff_sinh`：contDiff_sinh {n} : ContDiff Complex n sinh
-/
theorem ContDiffOn.csinh {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.sinh (f x)) s :=
  Complex.contDiff_sinh.comp_contDiffOn hf
/-
**ContDiffWithinAt.csinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.csinh {n} (hf : ContDiffWithinAt Complex n f s x) : ContD
iffWithinAt Complex n (fun x => Complex.sinh (f x)) s x
参数：hf : ContDiffWithinAt Complex n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_sinh`：contDiff_sinh {n} : ContDiff Complex n sinh
-/
theorem ContDiffWithinAt.csinh {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.sinh (f x)) s x :=
  Complex.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

end

namespace Real

variable {x y z : ℝ}

/-
**Real.hasStrictDerivAt_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_sinh (x : Real) : HasStrictDerivAt sinh (cosh x) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.real_of_complex`：HasStrictDerivAt.real_of_complex (h : 
HasStrictDerivAt e e' z) : HasStrictDerivAt (fun x : Real => (e x).re) e'.re z
· 使用定理 `Complex.hasStrictDerivAt_sinh`：hasStrictDerivAt_sinh (x : Complex) : Has
StrictDerivAt sinh (cosh x) x
-/
theorem hasStrictDerivAt_sinh (x : ℝ) : HasStrictDerivAt sinh (cosh x) x :=
  (Complex.hasStrictDerivAt_sinh x).real_of_complex
/-
**Real.hasDerivAt_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_sinh (x : Real) : HasDerivAt sinh (cosh x) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.real_of_complex`：HasDerivAt.real_of_complex (h : HasDerivAt e
 e' z) : HasDerivAt (fun x : Real => (e x).re) e'.re z
· 使用定理 `Complex.hasDerivAt_sinh`：hasDerivAt_sinh (x : Complex) : HasDerivAt sinh
 (cosh x) x
-/
theorem hasDerivAt_sinh (x : ℝ) : HasDerivAt sinh (cosh x) x :=
  (Complex.hasDerivAt_sinh x).real_of_complex
/-
**Real.isEquivalent_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isEquivalent_sinh : sinh ~[𝓝 0] id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.sinh_zero`：sinh_zero : sinh 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Real.cosh_zero`：cosh_zero : cosh 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.isLittleO`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `Real.hasDerivAt_sinh`：hasDerivAt_sinh (x : Real) : HasDerivAt sinh (cosh
 x) x
-/
theorem isEquivalent_sinh : sinh ~[𝓝 0] id := by simpa using! (hasDerivAt_sinh 0).isLittleO

@[fun_prop]
/-
**Real.contDiff_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiff_sinh {n} : ContDiff Real n sinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.real_of_complex`：ContDiff.real_of_complex {n : WithTop Nat∞} (h
 : ContDiff Complex n e) : ContDiff Real n fun x : Real => (e x).re
· 使用定理 `Complex.contDiff_sinh`：contDiff_sinh {n} : ContDiff Complex n sinh
-/
theorem contDiff_sinh {n} : ContDiff ℝ n sinh :=
  Complex.contDiff_sinh.real_of_complex

@[simp]
/-
**Real.differentiable_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_sinh : Differentiable Real sinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Real.hasDerivAt_sinh`：hasDerivAt_sinh (x : Real) : HasDerivAt sinh (cosh
 x) x
-/
theorem differentiable_sinh : Differentiable ℝ sinh := fun x => (hasDerivAt_sinh x).differentiableAt

@[simp]
/-
**Real.differentiableAt_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_sinh : DifferentiableAt Real sinh x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.differentiable_sinh`：differentiable_sinh : Differentiable Real sinh
-/
theorem differentiableAt_sinh : DifferentiableAt ℝ sinh x :=
  differentiable_sinh x

/-- The function `Real.sinh` is real analytic. -/
@[fun_prop]
/-
**Real.analyticAt_sinh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticAt_sinh : AnalyticAt Real sinh x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.analyticAt`：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : 
AnalyticAt 𝕜 f x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_sinh`：contDiff_sinh {n} : ContDiff Real n sinh

--- 原说明 ---
The function `Real.sinh` is real analytic.
-/
lemma analyticAt_sinh : AnalyticAt ℝ sinh x :=
  contDiff_sinh.contDiffAt.analyticAt

/-- The function `Real.sinh` is real analytic. -/
/-
**Real.analyticWithinAt_sinh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticWithinAt_sinh {s : Set Real} : AnalyticWithinAt Real sinh s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Real.contDiff_sinh`：contDiff_sinh {n} : ContDiff Real n sinh

--- 原说明 ---
The function `Real.sinh` is real analytic.
-/
lemma analyticWithinAt_sinh {s : Set ℝ} : AnalyticWithinAt ℝ sinh s x :=
  contDiff_sinh.contDiffWithinAt.analyticWithinAt

/-- The function `Real.sinh` is real analytic. -/
/-
**Real.analyticOnNhd_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：analyticOnNhd_sinh {s : Set Real} : AnalyticOnNhd Real sinh s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.analyticAt_sinh`：analyticAt_sinh : AnalyticAt Real sinh x

--- 原说明 ---
The function `Real.sinh` is real analytic.
-/
theorem analyticOnNhd_sinh {s : Set ℝ} : AnalyticOnNhd ℝ sinh s :=
  fun _ _ ↦ analyticAt_sinh

/-- The function `Real.sinh` is real analytic. -/
/-
**Real.analyticOn_sinh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticOn_sinh {s : Set Real} : AnalyticOn Real sinh s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Real.contDiff_sinh`：contDiff_sinh {n} : ContDiff Real n sinh

--- 原说明 ---
The function `Real.sinh` is real analytic.
-/
lemma analyticOn_sinh {s : Set ℝ} : AnalyticOn ℝ sinh s :=
  contDiff_sinh.contDiffOn.analyticOn

@[simp]
/-
**Real.deriv_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_sinh : deriv sinh = cosh
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Real.hasDerivAt_sinh`：hasDerivAt_sinh (x : Real) : HasDerivAt sinh (cosh
 x) x
-/
theorem deriv_sinh : deriv sinh = cosh :=
  funext fun x => (hasDerivAt_sinh x).deriv
/-
**Real.hasStrictDerivAt_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_cosh (x : Real) : HasStrictDerivAt cosh (sinh x) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.real_of_complex`：HasStrictDerivAt.real_of_complex (h : 
HasStrictDerivAt e e' z) : HasStrictDerivAt (fun x : Real => (e x).re) e'.re z
· 使用定理 `Complex.hasStrictDerivAt_cosh`：hasStrictDerivAt_cosh (x : Complex) : Has
StrictDerivAt cosh (sinh x) x
-/
theorem hasStrictDerivAt_cosh (x : ℝ) : HasStrictDerivAt cosh (sinh x) x :=
  (Complex.hasStrictDerivAt_cosh x).real_of_complex
/-
**Real.hasDerivAt_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_cosh (x : Real) : HasDerivAt cosh (sinh x) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.real_of_complex`：HasDerivAt.real_of_complex (h : HasDerivAt e
 e' z) : HasDerivAt (fun x : Real => (e x).re) e'.re z
· 使用定理 `Complex.hasDerivAt_cosh`：hasDerivAt_cosh (x : Complex) : HasDerivAt cosh
 (sinh x) x
-/
theorem hasDerivAt_cosh (x : ℝ) : HasDerivAt cosh (sinh x) x :=
  (Complex.hasDerivAt_cosh x).real_of_complex

@[fun_prop]
/-
**Real.contDiff_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiff_cosh {n} : ContDiff Real n cosh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.real_of_complex`：ContDiff.real_of_complex {n : WithTop Nat∞} (h
 : ContDiff Complex n e) : ContDiff Real n fun x : Real => (e x).re
· 使用定理 `Complex.contDiff_cosh`：contDiff_cosh {n} : ContDiff Complex n cosh
-/
theorem contDiff_cosh {n} : ContDiff ℝ n cosh :=
  Complex.contDiff_cosh.real_of_complex

@[simp]
/-
**Real.differentiable_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_cosh : Differentiable Real cosh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Real.hasDerivAt_cosh`：hasDerivAt_cosh (x : Real) : HasDerivAt cosh (sinh
 x) x
-/
theorem differentiable_cosh : Differentiable ℝ cosh := fun x => (hasDerivAt_cosh x).differentiableAt

@[simp]
/-
**Real.differentiableAt_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_cosh : DifferentiableAt Real cosh x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.differentiable_cosh`：differentiable_cosh : Differentiable Real cosh
-/
theorem differentiableAt_cosh : DifferentiableAt ℝ cosh x :=
  differentiable_cosh x

/-- The function `Real.cosh` is real analytic. -/
@[fun_prop]
/-
**Real.analyticAt_cosh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticAt_cosh : AnalyticAt Real cosh x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.analyticAt`：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : 
AnalyticAt 𝕜 f x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_cosh`：contDiff_cosh {n} : ContDiff Real n cosh

--- 原说明 ---
The function `Real.cosh` is real analytic.
-/
lemma analyticAt_cosh : AnalyticAt ℝ cosh x :=
  contDiff_cosh.contDiffAt.analyticAt

/-- The function `Real.cosh` is real analytic. -/
/-
**Real.analyticWithinAt_cosh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticWithinAt_cosh {s : Set Real} : AnalyticWithinAt Real cosh s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Real.contDiff_cosh`：contDiff_cosh {n} : ContDiff Real n cosh

--- 原说明 ---
The function `Real.cosh` is real analytic.
-/
lemma analyticWithinAt_cosh {s : Set ℝ} : AnalyticWithinAt ℝ cosh s x :=
  contDiff_cosh.contDiffWithinAt.analyticWithinAt

/-- The function `Real.cosh` is real analytic. -/
/-
**Real.analyticOnNhd_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：analyticOnNhd_cosh {s : Set Real} : AnalyticOnNhd Real cosh s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.analyticAt_cosh`：analyticAt_cosh : AnalyticAt Real cosh x

--- 原说明 ---
The function `Real.cosh` is real analytic.
-/
theorem analyticOnNhd_cosh {s : Set ℝ} : AnalyticOnNhd ℝ cosh s :=
  fun _ _ ↦ analyticAt_cosh

/-- The function `Real.cosh` is real analytic. -/
/-
**Real.analyticOn_cosh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticOn_cosh {s : Set Real} : AnalyticOn Real cosh s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Real.contDiff_cosh`：contDiff_cosh {n} : ContDiff Real n cosh

--- 原说明 ---
The function `Real.cosh` is real analytic.
-/
lemma analyticOn_cosh {s : Set ℝ} : AnalyticOn ℝ cosh s :=
  contDiff_cosh.contDiffOn.analyticOn

@[simp]
/-
**Real.deriv_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_cosh : deriv cosh = sinh
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Real.hasDerivAt_cosh`：hasDerivAt_cosh (x : Real) : HasDerivAt cosh (sinh
 x) x
-/
theorem deriv_cosh : deriv cosh = sinh :=
  funext fun x => (hasDerivAt_cosh x).deriv

/-- `sinh` is strictly monotone. -/
/-
**Real.sinh_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_strictMono : StrictMono sinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_of_deriv_pos`：strictMono_of_deriv_pos {f : Real -> Real} (hf'
 : forall x, 0 < deriv f x) : StrictMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.deriv_sinh`：deriv_sinh : deriv sinh = cosh
· 使用定理 `Real.cosh_pos`：cosh_pos (x : Real) : 0 < Real.cosh x

--- 原说明 ---
`sinh` is strictly monotone.
-/
theorem sinh_strictMono : StrictMono sinh :=
  strictMono_of_deriv_pos <| by rw [Real.deriv_sinh]; exact cosh_pos

/-- `sinh` is injective, `∀ a b, sinh a = sinh b → a = b`. -/
/-
**Real.sinh_injective** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_injective : Function.Injective sinh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Real.sinh_strictMono`：sinh_strictMono : StrictMono sinh

--- 原说明 ---
`sinh` is injective, `∀ a b, sinh a = sinh b → a = b`.
-/
theorem sinh_injective : Function.Injective sinh :=
  sinh_strictMono.injective

@[simp]
/-
**Real.sinh_inj** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_inj : sinh x = sinh y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Real.sinh_injective`：sinh_injective : Function.Injective sinh
-/
theorem sinh_inj : sinh x = sinh y ↔ x = y :=
  sinh_injective.eq_iff

@[simp]
/-
**Real.sinh_le_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_le_sinh : sinh x <= sinh y ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Real.sinh_strictMono`：sinh_strictMono : StrictMono sinh
-/
theorem sinh_le_sinh : sinh x ≤ sinh y ↔ x ≤ y :=
  sinh_strictMono.le_iff_le

@[simp]
/-
**Real.sinh_lt_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_lt_sinh : sinh x < sinh y ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Real.sinh_strictMono`：sinh_strictMono : StrictMono sinh
-/
theorem sinh_lt_sinh : sinh x < sinh y ↔ x < y :=
  sinh_strictMono.lt_iff_lt
/-
**Real.sinh_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x : ℝ}, Real.sinh x = 0 ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sinh_inj`：sinh_inj : sinh x = sinh y ↔ x = y
· 使用定理 `Real.sinh_zero`：sinh_zero : sinh 0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma sinh_eq_zero : sinh x = 0 ↔ x = 0 := by rw [← @sinh_inj x, sinh_zero]
/-
**Real.sinh_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sinh_ne_zero : sinh x != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Real.sinh_eq_zero`：∀ {x : ℝ}, Real.sinh x = 0 ↔ x = 0
-/
lemma sinh_ne_zero : sinh x ≠ 0 ↔ x ≠ 0 := sinh_eq_zero.not

@[simp]
/-
**Real.sinh_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_pos_iff : 0 < sinh x ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sinh_zero`：sinh_zero : sinh 0 = 0
· 使用定理 `Real.sinh_lt_sinh`：sinh_lt_sinh : sinh x < sinh y ↔ x < y
-/
theorem sinh_pos_iff : 0 < sinh x ↔ 0 < x := by simpa only [sinh_zero] using @sinh_lt_sinh 0 x

@[simp]
/-
**Real.sinh_nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_nonpos_iff : sinh x <= 0 ↔ x <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sinh_zero`：sinh_zero : sinh 0 = 0
· 使用定理 `Real.sinh_le_sinh`：sinh_le_sinh : sinh x <= sinh y ↔ x <= y
-/
theorem sinh_nonpos_iff : sinh x ≤ 0 ↔ x ≤ 0 := by simpa only [sinh_zero] using @sinh_le_sinh x 0

@[simp]
/-
**Real.sinh_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_neg_iff : sinh x < 0 ↔ x < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sinh_zero`：sinh_zero : sinh 0 = 0
· 使用定理 `Real.sinh_lt_sinh`：sinh_lt_sinh : sinh x < sinh y ↔ x < y
-/
theorem sinh_neg_iff : sinh x < 0 ↔ x < 0 := by simpa only [sinh_zero] using @sinh_lt_sinh x 0

@[simp]
/-
**Real.sinh_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_nonneg_iff : 0 <= sinh x ↔ 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sinh_zero`：sinh_zero : sinh 0 = 0
· 使用定理 `Real.sinh_le_sinh`：sinh_le_sinh : sinh x <= sinh y ↔ x <= y
-/
theorem sinh_nonneg_iff : 0 ≤ sinh x ↔ 0 ≤ x := by simpa only [sinh_zero] using @sinh_le_sinh 0 x
/-
**Real.abs_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_sinh (x : Real) : |sinh x| = sinh |x|
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Real.sinh_neg`：sinh_neg : sinh (-x) = -sinh x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
-/
theorem abs_sinh (x : ℝ) : |sinh x| = sinh |x| := by
  cases le_total x 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]
/-
**Real.cosh_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cosh_strictMonoOn : StrictMonoOn cosh (Ici 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMonoOn_of_deriv_pos`：strictMonoOn_of_deriv_pos {D : Set Real} (hD 
: Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in i
nterior D, 0 < …
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Real.continuous_cosh`：continuous_cosh : Continuous cosh
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.deriv_cosh`：deriv_cosh : deriv cosh = sinh
· 使用定理 `Real.sinh_pos_iff`：sinh_pos_iff : 0 < sinh x ↔ 0 < x
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `interior_Ici`：interior_Ici [NoMinOrder α] {a : α} : interior (Ici a) = I
oi a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
-/
theorem cosh_strictMonoOn : StrictMonoOn cosh (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici _) continuous_cosh.continuousOn fun x hx => by
    rw [interior_Ici, mem_Ioi] at hx; rwa [deriv_cosh, sinh_pos_iff]

@[simp]
/-
**Real.cosh_le_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cosh_le_cosh : cosh x <= cosh y ↔ |x| <= |y|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `Real.cosh_strictMonoOn`：cosh_strictMonoOn : StrictMonoOn cosh (Ici 0)
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.cosh_abs`：cosh_abs : cosh |x| = cosh x
-/
theorem cosh_le_cosh : cosh x ≤ cosh y ↔ |x| ≤ |y| :=
  cosh_abs x ▸ cosh_abs y ▸ cosh_strictMonoOn.le_iff_le (abs_nonneg x) (abs_nonneg y)

@[simp]
/-
**Real.cosh_lt_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cosh_lt_cosh : cosh x < cosh y ↔ |x| < |y|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Real.cosh_le_cosh`：cosh_le_cosh : cosh x <= cosh y ↔ |x| <= |y|
-/
theorem cosh_lt_cosh : cosh x < cosh y ↔ |x| < |y| :=
  lt_iff_lt_of_le_iff_le cosh_le_cosh

@[simp]
/-
**Real.one_le_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_le_cosh (x : Real) : 1 <= cosh x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.cosh_le_cosh`：cosh_le_cosh : cosh x <= cosh y ↔ |x| <= |y|
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.cosh_zero`：cosh_zero : cosh 0 = 1
-/
theorem one_le_cosh (x : ℝ) : 1 ≤ cosh x :=
  cosh_zero ▸ cosh_le_cosh.2 (by simp only [_root_.abs_zero, _root_.abs_nonneg])

@[simp]
/-
**Real.one_lt_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：one_lt_cosh : 1 < cosh x ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Real.cosh_lt_cosh`：cosh_lt_cosh : cosh x < cosh y ↔ |x| < |y|
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Real.cosh_zero`：cosh_zero : cosh 0 = 1
-/
theorem one_lt_cosh : 1 < cosh x ↔ x ≠ 0 :=
  cosh_zero ▸ cosh_lt_cosh.trans (by simp only [_root_.abs_zero, abs_pos])
/-
**Real.sinh_sub_id_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_sub_id_strictMono : StrictMono fun x => sinh x - x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_of_odd_strictMonoOn_nonneg`：strictMono_of_odd_strictMonoOn_no
nneg {f : G -> H} (h₁ : forall x, f (-x) = -f x) (h₂ : StrictMonoOn f (Ici 0)) :
 StrictMono f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.sinh_neg`：sinh_neg : sinh (-x) = -sinh x
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp.0.Real
.sinh_sub_id_strictMono._abel_1_1`：∀ (x : ℝ), -Real.sinh x + x = x - Real.sinh x
· 使用定理 `strictMonoOn_of_deriv_pos`：strictMonoOn_of_deriv_pos {D : Set Real} (hD 
: Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in i
nterior D, 0 < …
· 使用定理 `convex_Ici`：convex_Ici (r : β) : Convex 𝕜 (Ici r)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Real.continuous_sinh`：continuous_sinh : Continuous sinh
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `deriv_fun_sub`：deriv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : Differe
ntiableAt 𝕜 g x) : deriv (fun y => f y - g y) x = deriv f x - deriv g x
· 使用定理 `Real.differentiableAt_sinh`：differentiableAt_sinh : DifferentiableAt Rea
l sinh x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `Real.deriv_sinh`：deriv_sinh : deriv sinh = cosh
· 使用定理 `deriv_id''`：deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 43 条，此处仅展示前 30 条）
-/
theorem sinh_sub_id_strictMono : StrictMono fun x => sinh x - x := by
  refine strictMono_of_odd_strictMonoOn_nonneg (fun x => by simp; abel) ?_
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ fun x hx => ?_
  · exact (continuous_sinh.sub continuous_id).continuousOn
  · rw [interior_Ici, mem_Ioi] at hx
    rw [deriv_fun_sub, deriv_sinh, deriv_id'', sub_pos, one_lt_cosh]
    exacts [hx.ne', differentiableAt_sinh, differentiableAt_id]

@[simp]
/-
**Real.self_le_sinh_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：self_le_sinh_iff : x <= sinh x ↔ 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.sinh_zero`：sinh_zero : sinh 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Real.sinh_sub_id_strictMono`：sinh_sub_id_strictMono : StrictMono fun x =
> sinh x - x
-/
theorem self_le_sinh_iff : x ≤ sinh x ↔ 0 ≤ x :=
  calc
    x ≤ sinh x ↔ sinh 0 - 0 ≤ sinh x - x := by simp
    _ ↔ 0 ≤ x := sinh_sub_id_strictMono.le_iff_le

@[simp]
/-
**Real.sinh_le_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_le_self_iff : sinh x <= x ↔ x <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.sinh_zero`：sinh_zero : sinh 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Real.sinh_sub_id_strictMono`：sinh_sub_id_strictMono : StrictMono fun x =
> sinh x - x
-/
theorem sinh_le_self_iff : sinh x ≤ x ↔ x ≤ 0 :=
  calc
    sinh x ≤ x ↔ sinh x - x ≤ sinh 0 - 0 := by simp
    _ ↔ x ≤ 0 := sinh_sub_id_strictMono.le_iff_le

@[simp]
/-
**Real.self_lt_sinh_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：self_lt_sinh_iff : x < sinh x ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Real.sinh_le_self_iff`：sinh_le_self_iff : sinh x <= x ↔ x <= 0
-/
theorem self_lt_sinh_iff : x < sinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le sinh_le_self_iff

@[simp]
/-
**Real.sinh_lt_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_lt_self_iff : sinh x < x ↔ x < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Real.self_le_sinh_iff`：self_le_sinh_iff : x <= sinh x ↔ 0 <= x
-/
theorem sinh_lt_self_iff : sinh x < x ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le self_le_sinh_iff

end Real

section iteratedDeriv

/-! ### Simp lemmas for iterated derivatives of `sinh` and `cosh`. -/

namespace Complex

@[simp]
/-
**Complex.iteratedDeriv_add_one_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_add_one_sinh (n : Nat) : iteratedDeriv (n + 1) sinh = iterat
edDeriv n cosh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iteratedDeriv_one`：iteratedDeriv_one : iteratedDeriv 1 f = deriv f
· 使用定理 `Complex.deriv_sinh`：deriv_sinh : deriv sinh = cosh
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
-/
theorem iteratedDeriv_add_one_sinh (n : ℕ) :
    iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
/-
**Complex.iteratedDeriv_add_one_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_add_one_cosh (n : Nat) : iteratedDeriv (n + 1) cosh = iterat
edDeriv n sinh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_one`：iteratedDeriv_one : iteratedDeriv 1 f = deriv f
· 使用定理 `Complex.deriv_cosh`：deriv_cosh : deriv cosh = sinh
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
-/
theorem iteratedDeriv_add_one_cosh (n : ℕ) :
    iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
/-
**Complex.iteratedDeriv_even_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_even_sinh (n : Nat) : iteratedDeriv (2 * n) sinh = sinh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.iteratedDeriv_add_one_sinh`：iteratedDeriv_add_one_sinh (n : Nat)
 : iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh
· 使用定理 `Complex.iteratedDeriv_add_one_cosh`：iteratedDeriv_add_one_cosh (n : Nat)
 : iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh
-/
theorem iteratedDeriv_even_sinh (n : ℕ) :
    iteratedDeriv (2 * n) sinh = sinh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

@[simp]
/-
**Complex.iteratedDeriv_even_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_even_cosh (n : Nat) : iteratedDeriv (2 * n) cosh = cosh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.iteratedDeriv_add_one_cosh`：iteratedDeriv_add_one_cosh (n : Nat)
 : iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh
· 使用定理 `Complex.iteratedDeriv_add_one_sinh`：iteratedDeriv_add_one_sinh (n : Nat)
 : iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh
-/
theorem iteratedDeriv_even_cosh (n : ℕ) :
    iteratedDeriv (2 * n) cosh = cosh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]
/-
**Complex.iteratedDeriv_odd_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_odd_sinh (n : Nat) : iteratedDeriv (2 * n + 1) sinh = cosh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.iteratedDeriv_add_one_sinh`：iteratedDeriv_add_one_sinh (n : Nat)
 : iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh
· 使用定理 `Complex.iteratedDeriv_even_cosh`：iteratedDeriv_even_cosh (n : Nat) : ite
ratedDeriv (2 * n) cosh = cosh
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_odd_sinh (n : ℕ) :
    iteratedDeriv (2 * n + 1) sinh = cosh := by simp
/-
**Complex.iteratedDeriv_odd_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_odd_cosh (n : Nat) : iteratedDeriv (2 * n + 1) cosh = sinh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.iteratedDeriv_add_one_cosh`：iteratedDeriv_add_one_cosh (n : Nat)
 : iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh
· 使用定理 `Complex.iteratedDeriv_even_sinh`：iteratedDeriv_even_sinh (n : Nat) : ite
ratedDeriv (2 * n) sinh = sinh
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_odd_cosh (n : ℕ) :
    iteratedDeriv (2 * n + 1) cosh = sinh := by simp
/-
**Complex.differentiable_iteratedDeriv_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiable_iteratedDeriv_sinh (n : Nat) : Differentiable Complex (iter
atedDeriv n sinh)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem differentiable_iteratedDeriv_sinh (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n sinh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]
/-
**Complex.differentiable_iteratedDeriv_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiable_iteratedDeriv_cosh (n : Nat) : Differentiable Complex (iter
atedDeriv n cosh)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem differentiable_iteratedDeriv_cosh (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n cosh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

end Complex

namespace Real

@[simp]
/-
**Real.iteratedDeriv_add_one_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_add_one_sinh (n : Nat) : iteratedDeriv (n + 1) sinh = iterat
edDeriv n cosh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iteratedDeriv_one`：iteratedDeriv_one : iteratedDeriv 1 f = deriv f
· 使用定理 `Real.deriv_sinh`：deriv_sinh : deriv sinh = cosh
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
-/
theorem iteratedDeriv_add_one_sinh (n : ℕ) :
    iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
/-
**Real.iteratedDeriv_add_one_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_add_one_cosh (n : Nat) : iteratedDeriv (n + 1) cosh = iterat
edDeriv n sinh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_one`：iteratedDeriv_one : iteratedDeriv 1 f = deriv f
· 使用定理 `Real.deriv_cosh`：deriv_cosh : deriv cosh = sinh
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
-/
theorem iteratedDeriv_add_one_cosh (n : ℕ) :
    iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
/-
**Real.iteratedDeriv_even_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_even_sinh (n : Nat) : iteratedDeriv (2 * n) sinh = sinh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.iteratedDeriv_add_one_sinh`：iteratedDeriv_add_one_sinh (n : Nat) : 
iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh
· 使用定理 `Real.iteratedDeriv_add_one_cosh`：iteratedDeriv_add_one_cosh (n : Nat) : 
iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh
-/
theorem iteratedDeriv_even_sinh (n : ℕ) :
    iteratedDeriv (2 * n) sinh = sinh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]

@[simp]
/-
**Real.iteratedDeriv_even_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_even_cosh (n : Nat) : iteratedDeriv (2 * n) cosh = cosh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.iteratedDeriv_add_one_cosh`：iteratedDeriv_add_one_cosh (n : Nat) : 
iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh
· 使用定理 `Real.iteratedDeriv_add_one_sinh`：iteratedDeriv_add_one_sinh (n : Nat) : 
iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh
-/
theorem iteratedDeriv_even_cosh (n : ℕ) :
    iteratedDeriv (2 * n) cosh = cosh := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add]
/-
**Real.iteratedDeriv_odd_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_odd_sinh (n : Nat) : iteratedDeriv (2 * n + 1) sinh = cosh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.iteratedDeriv_add_one_sinh`：iteratedDeriv_add_one_sinh (n : Nat) : 
iteratedDeriv (n + 1) sinh = iteratedDeriv n cosh
· 使用定理 `Real.iteratedDeriv_even_cosh`：iteratedDeriv_even_cosh (n : Nat) : iterat
edDeriv (2 * n) cosh = cosh
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_odd_sinh (n : ℕ) :
    iteratedDeriv (2 * n + 1) sinh = cosh := by simp
/-
**Real.iteratedDeriv_odd_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_odd_cosh (n : Nat) : iteratedDeriv (2 * n + 1) cosh = sinh
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.iteratedDeriv_add_one_cosh`：iteratedDeriv_add_one_cosh (n : Nat) : 
iteratedDeriv (n + 1) cosh = iteratedDeriv n sinh
· 使用定理 `Real.iteratedDeriv_even_sinh`：iteratedDeriv_even_sinh (n : Nat) : iterat
edDeriv (2 * n) sinh = sinh
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_odd_cosh (n : ℕ) :
    iteratedDeriv (2 * n + 1) cosh = sinh := by simp
/-
**Real.differentiable_iteratedDeriv_sinh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_iteratedDeriv_sinh (n : Nat) : Differentiable Real (iterate
dDeriv n sinh)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem differentiable_iteratedDeriv_sinh (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n sinh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sinh]
/-
**Real.differentiable_iteratedDeriv_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_iteratedDeriv_cosh (n : Nat) : Differentiable Real (iterate
dDeriv n cosh)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem differentiable_iteratedDeriv_cosh (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n cosh) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cosh]

@[simp]
/-
**Real.iteratedDerivWithin_sinh_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDerivWithin_sinh_Icc (n : Nat) {a b : Real} (h : a < b) {x : Real}
 (hx : x in Icc a b) : iteratedDerivWithin n sinh (Icc a b) x = iteratedDeriv n 
sinh x
参数：n : Nat；h : a < b；hx : x in Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDerivWithin_eq_iteratedDeriv`：iteratedDerivWithin_eq_iteratedDer
iv (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x) (hx : x in s) : iteratedDeri
vWithin n f s x = iterated…
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_sinh`：contDiff_sinh {n} : ContDiff Real n sinh
-/
theorem iteratedDerivWithin_sinh_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    iteratedDerivWithin n sinh (Icc a b) x = iteratedDeriv n sinh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_sinh.contDiffAt hx

@[simp]
/-
**Real.iteratedDerivWithin_cosh_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDerivWithin_cosh_Icc (n : Nat) {a b : Real} (h : a < b) {x : Real}
 (hx : x in Icc a b) : iteratedDerivWithin n cosh (Icc a b) x = iteratedDeriv n 
cosh x
参数：n : Nat；h : a < b；hx : x in Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDerivWithin_eq_iteratedDeriv`：iteratedDerivWithin_eq_iteratedDer
iv (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x) (hx : x in s) : iteratedDeri
vWithin n f s x = iterated…
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_cosh`：contDiff_cosh {n} : ContDiff Real n cosh
-/
theorem iteratedDerivWithin_cosh_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    iteratedDerivWithin n cosh (Icc a b) x = iteratedDeriv n cosh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_cosh.contDiffAt hx

@[simp]
/-
**Real.iteratedDerivWithin_sinh_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDerivWithin_sinh_Ioo (n : Nat) {a b x : Real} (hx : x in Ioo a b) 
: iteratedDerivWithin n sinh (Ioo a b) x = iteratedDeriv n sinh x
参数：n : Nat；hx : x in Ioo a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDerivWithin_eq_iteratedDeriv`：iteratedDerivWithin_eq_iteratedDer
iv (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x) (hx : x in s) : iteratedDeri
vWithin n f s x = iterated…
· 使用定理 `uniqueDiffOn_Ioo`：uniqueDiffOn_Ioo (a b : Real) : UniqueDiffOn Real (Ioo
 a b)
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_sinh`：contDiff_sinh {n} : ContDiff Real n sinh
-/
theorem iteratedDerivWithin_sinh_Ioo (n : ℕ) {a b x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDerivWithin n sinh (Ioo a b) x = iteratedDeriv n sinh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_sinh.contDiffAt hx

@[simp]
/-
**Real.iteratedDerivWithin_cosh_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDerivWithin_cosh_Ioo (n : Nat) {a b x : Real} (hx : x in Ioo a b) 
: iteratedDerivWithin n cosh (Ioo a b) x = iteratedDeriv n cosh x
参数：n : Nat；hx : x in Ioo a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedDerivWithin_eq_iteratedDeriv`：iteratedDerivWithin_eq_iteratedDer
iv (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x) (hx : x in s) : iteratedDeri
vWithin n f s x = iterated…
· 使用定理 `uniqueDiffOn_Ioo`：uniqueDiffOn_Ioo (a b : Real) : UniqueDiffOn Real (Ioo
 a b)
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_cosh`：contDiff_cosh {n} : ContDiff Real n cosh
-/
theorem iteratedDerivWithin_cosh_Ioo (n : ℕ) {a b x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDerivWithin n cosh (Ioo a b) x = iteratedDeriv n cosh x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_cosh.contDiffAt hx

end Real

end iteratedDeriv

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : ℝ → ℝ` -/

variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

/-! #### `Real.cosh` -/

/-
**HasStrictDerivAt.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.cosh (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (f
un x => Real.cosh (f x)) (Real.sinh (f x) * f') x
参数：hf : HasStrictDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `Real.hasStrictDerivAt_cosh`：hasStrictDerivAt_cosh (x : Real) : HasStrict
DerivAt cosh (sinh x) x

--- 原说明 ---
#### `Real.cosh`
-/
theorem HasStrictDerivAt.cosh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.hasStrictDerivAt_cosh (f x)).comp x hf
/-
**HasDerivAt.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.cosh (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.cosh 
(f x)) (Real.sinh (f x) * f') x
参数：hf : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Real.hasDerivAt_cosh`：hasDerivAt_cosh (x : Real) : HasDerivAt cosh (sinh
 x) x
-/
theorem HasDerivAt.cosh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x :=
  (Real.hasDerivAt_cosh (f x)).comp x hf
/-
**HasDerivWithinAt.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.cosh (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt 
(fun x => Real.cosh (f x)) (Real.sinh (f x) * f') s x
参数：hf : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `Real.hasDerivAt_cosh`：hasDerivAt_cosh (x : Real) : HasDerivAt cosh (sinh
 x) x
-/
theorem HasDerivWithinAt.cosh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') s x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasDerivWithinAt x hf
/-
**derivWithin_cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_cosh (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDif
fWithinAt Real s x) : derivWithin (fun x => Real.cosh (f x)) s x = Real.sinh (f 
x) * derivWithin f s x
参数：hf : DifferentiableWithinAt Real f s x；hxs : UniqueDiffWithinAt Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.cosh`：HasDerivWithinAt.cosh (hf : HasDerivWithinAt f f'
 s x) : HasDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) * f') s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.cosh (f x)) s x = Real.sinh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cosh.derivWithin hxs

@[simp]
/-
**deriv_cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_cosh (hc : DifferentiableAt Real f x) : deriv (fun x => Real.cosh (f
 x)) x = Real.sinh (f x) * deriv f x
参数：hc : DifferentiableAt Real f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.cosh`：HasDerivAt.cosh (hf : HasDerivAt f f' x) : HasDerivAt (
fun x => Real.cosh (f x)) (Real.sinh (f x) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_cosh (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.cosh (f x)) x = Real.sinh (f x) * deriv f x :=
  hc.hasDerivAt.cosh.deriv

/-! #### `Real.sinh` -/

/-
**HasStrictDerivAt.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.sinh (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (f
un x => Real.sinh (f x)) (Real.cosh (f x) * f') x
参数：hf : HasStrictDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `Real.hasStrictDerivAt_sinh`：hasStrictDerivAt_sinh (x : Real) : HasStrict
DerivAt sinh (cosh x) x

--- 原说明 ---
#### `Real.sinh`
-/
theorem HasStrictDerivAt.sinh (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.hasStrictDerivAt_sinh (f x)).comp x hf
/-
**HasDerivAt.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.sinh (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.sinh 
(f x)) (Real.cosh (f x) * f') x
参数：hf : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Real.hasDerivAt_sinh`：hasDerivAt_sinh (x : Real) : HasDerivAt sinh (cosh
 x) x
-/
theorem HasDerivAt.sinh (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x :=
  (Real.hasDerivAt_sinh (f x)).comp x hf
/-
**HasDerivWithinAt.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.sinh (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt 
(fun x => Real.sinh (f x)) (Real.cosh (f x) * f') s x
参数：hf : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `Real.hasDerivAt_sinh`：hasDerivAt_sinh (x : Real) : HasDerivAt sinh (cosh
 x) x
-/
theorem HasDerivWithinAt.sinh (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') s x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasDerivWithinAt x hf
/-
**derivWithin_sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_sinh (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDif
fWithinAt Real s x) : derivWithin (fun x => Real.sinh (f x)) s x = Real.cosh (f 
x) * derivWithin f s x
参数：hf : DifferentiableWithinAt Real f s x；hxs : UniqueDiffWithinAt Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.sinh`：HasDerivWithinAt.sinh (hf : HasDerivWithinAt f f'
 s x) : HasDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) * f') s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.sinh (f x)) s x = Real.cosh (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.sinh.derivWithin hxs

@[simp]
/-
**deriv_sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_sinh (hc : DifferentiableAt Real f x) : deriv (fun x => Real.sinh (f
 x)) x = Real.cosh (f x) * deriv f x
参数：hc : DifferentiableAt Real f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.sinh`：HasDerivAt.sinh (hf : HasDerivAt f f' x) : HasDerivAt (
fun x => Real.sinh (f x)) (Real.cosh (f x) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_sinh (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.sinh (f x)) x = Real.cosh (f x) * deriv f x :=
  hc.hasDerivAt.sinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : E → ℝ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : StrongDual ℝ E}
  {x : E} {s : Set E}

/-! #### `Real.cosh` -/

/-
**HasStrictFDerivAt.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.cosh (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivAt
 (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Real.hasStrictDerivAt_cosh`：hasStrictDerivAt_cosh (x : Real) : HasStrict
DerivAt cosh (sinh x) x

--- 原说明 ---
#### `Real.cosh`
-/
theorem HasStrictFDerivAt.cosh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.hasStrictDerivAt_cosh (f x)).comp_hasStrictFDerivAt x hf
/-
**HasFDerivAt.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.cosh (hf : HasFDerivAt f f' x) : HasFDerivAt (fun x => Real.co
sh (f x)) (Real.sinh (f x) • f') x
参数：hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Real.hasDerivAt_cosh`：hasDerivAt_cosh (x : Real) : HasDerivAt cosh (sinh
 x) x
-/
theorem HasFDerivAt.cosh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasFDerivAt x hf
/-
**HasFDerivWithinAt.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.cosh (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithin
At (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') s x
参数：hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Real.hasDerivAt_cosh`：hasDerivAt_cosh (x : Real) : HasDerivAt cosh (sinh
 x) x
-/
theorem HasFDerivWithinAt.cosh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') s x :=
  (Real.hasDerivAt_cosh (f x)).comp_hasFDerivWithinAt x hf
/-
**DifferentiableWithinAt.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.cosh (hf : DifferentiableWithinAt Real f s x) : Dif
ferentiableWithinAt Real (fun x => Real.cosh (f x)) s x
参数：hf : DifferentiableWithinAt Real f s x。
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasFDerivWithinAt.cosh`：HasFDerivWithinAt.cosh (hf : HasFDerivWithinAt f
 f' s x) : HasFDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') s
 x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.cosh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.cosh (f x)) s x :=
  hf.hasFDerivWithinAt.cosh.differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.cosh (hc : DifferentiableAt Real f x) : DifferentiableAt 
Real (fun x => Real.cosh (f x)) x
参数：hc : DifferentiableAt Real f x。
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasFDerivAt.cosh`：HasFDerivAt.cosh (hf : HasFDerivAt f f' x) : HasFDeriv
At (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.cosh (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.cosh (f x)) x :=
  hc.hasFDerivAt.cosh.differentiableAt
/-
**DifferentiableOn.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.cosh (hc : DifferentiableOn Real f s) : DifferentiableOn 
Real (fun x => Real.cosh (f x)) s
参数：hc : DifferentiableOn Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.cosh`：DifferentiableWithinAt.cosh (hf : Different
iableWithinAt Real f s x) : DifferentiableWithinAt Real (fun x => Real.cosh (f x
)) s x
-/
theorem DifferentiableOn.cosh (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.cosh (f x)) s := fun x h => (hc x h).cosh

@[simp, fun_prop]
/-
**Differentiable.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.cosh (hc : Differentiable Real f) : Differentiable Real fun
 x => Real.cosh (f x)
参数：hc : Differentiable Real f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.cosh`：DifferentiableAt.cosh (hc : DifferentiableAt Real
 f x) : DifferentiableAt Real (fun x => Real.cosh (f x)) x
-/
theorem Differentiable.cosh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.cosh (f x) :=
  fun x => (hc x).cosh
/-
**fderivWithin_cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_cosh (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDi
ffWithinAt Real s x) : fderivWithin Real (fun x => Real.cosh (f x)) s x = Real.s
inh (f x) • fderivWithin Real f s x
参数：hf : DifferentiableWithinAt Real f s x；hxs : UniqueDiffWithinAt Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.cosh`：HasFDerivWithinAt.cosh (hf : HasFDerivWithinAt f
 f' s x) : HasFDerivWithinAt (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') s
 x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_cosh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.cosh (f x)) s x = Real.sinh (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.cosh.fderivWithin hxs

@[simp]
/-
**fderiv_cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_cosh (hc : DifferentiableAt Real f x) : fderiv Real (fun x => Real.
cosh (f x)) x = Real.sinh (f x) • fderiv Real f x
参数：hc : DifferentiableAt Real f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.cosh`：HasFDerivAt.cosh (hf : HasFDerivAt f f' x) : HasFDeriv
At (fun x => Real.cosh (f x)) (Real.sinh (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_cosh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.cosh (f x)) x = Real.sinh (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.cosh.fderiv
/-
**ContDiff.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.cosh {n} (h : ContDiff Real n f) : ContDiff Real n fun x => Real.
cosh (f x)
参数：h : ContDiff Real n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Real.contDiff_cosh`：contDiff_cosh {n} : ContDiff Real n cosh
-/
theorem ContDiff.cosh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.cosh (f x) :=
  Real.contDiff_cosh.comp h
/-
**ContDiffAt.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.cosh {n} (hf : ContDiffAt Real n f x) : ContDiffAt Real n (fun 
x => Real.cosh (f x)) x
参数：hf : ContDiffAt Real n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_cosh`：contDiff_cosh {n} : ContDiff Real n cosh
-/
theorem ContDiffAt.cosh {n} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x => Real.cosh (f x)) x :=
  Real.contDiff_cosh.contDiffAt.comp x hf
/-
**ContDiffOn.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.cosh {n} (hf : ContDiffOn Real n f s) : ContDiffOn Real n (fun 
x => Real.cosh (f x)) s
参数：hf : ContDiffOn Real n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `Real.contDiff_cosh`：contDiff_cosh {n} : ContDiff Real n cosh
-/
theorem ContDiffOn.cosh {n} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun x => Real.cosh (f x)) s :=
  Real.contDiff_cosh.comp_contDiffOn hf
/-
**ContDiffWithinAt.cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.cosh {n} (hf : ContDiffWithinAt Real n f s x) : ContDiffW
ithinAt Real n (fun x => Real.cosh (f x)) s x
参数：hf : ContDiffWithinAt Real n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_cosh`：contDiff_cosh {n} : ContDiff Real n cosh
-/
theorem ContDiffWithinAt.cosh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.cosh (f x)) s x :=
  Real.contDiff_cosh.contDiffAt.comp_contDiffWithinAt x hf

/-! #### `Real.sinh` -/

/-
**HasStrictFDerivAt.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.sinh (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivAt
 (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Real.hasStrictDerivAt_sinh`：hasStrictDerivAt_sinh (x : Real) : HasStrict
DerivAt sinh (cosh x) x

--- 原说明 ---
#### `Real.sinh`
-/
theorem HasStrictFDerivAt.sinh (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.hasStrictDerivAt_sinh (f x)).comp_hasStrictFDerivAt x hf
/-
**HasFDerivAt.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.sinh (hf : HasFDerivAt f f' x) : HasFDerivAt (fun x => Real.si
nh (f x)) (Real.cosh (f x) • f') x
参数：hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Real.hasDerivAt_sinh`：hasDerivAt_sinh (x : Real) : HasDerivAt sinh (cosh
 x) x
-/
theorem HasFDerivAt.sinh (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasFDerivAt x hf
/-
**HasFDerivWithinAt.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.sinh (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithin
At (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') s x
参数：hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Real.hasDerivAt_sinh`：hasDerivAt_sinh (x : Real) : HasDerivAt sinh (cosh
 x) x
-/
theorem HasFDerivWithinAt.sinh (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') s x :=
  (Real.hasDerivAt_sinh (f x)).comp_hasFDerivWithinAt x hf
/-
**DifferentiableWithinAt.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.sinh (hf : DifferentiableWithinAt Real f s x) : Dif
ferentiableWithinAt Real (fun x => Real.sinh (f x)) s x
参数：hf : DifferentiableWithinAt Real f s x。
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasFDerivWithinAt.sinh`：HasFDerivWithinAt.sinh (hf : HasFDerivWithinAt f
 f' s x) : HasFDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') s
 x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.sinh (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.sinh (f x)) s x :=
  hf.hasFDerivWithinAt.sinh.differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.sinh (hc : DifferentiableAt Real f x) : DifferentiableAt 
Real (fun x => Real.sinh (f x)) x
参数：hc : DifferentiableAt Real f x。
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasFDerivAt.sinh`：HasFDerivAt.sinh (hf : HasFDerivAt f f' x) : HasFDeriv
At (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.sinh (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.sinh (f x)) x :=
  hc.hasFDerivAt.sinh.differentiableAt
/-
**DifferentiableOn.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.sinh (hc : DifferentiableOn Real f s) : DifferentiableOn 
Real (fun x => Real.sinh (f x)) s
参数：hc : DifferentiableOn Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.sinh`：DifferentiableWithinAt.sinh (hf : Different
iableWithinAt Real f s x) : DifferentiableWithinAt Real (fun x => Real.sinh (f x
)) s x
-/
theorem DifferentiableOn.sinh (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.sinh (f x)) s := fun x h => (hc x h).sinh

@[simp, fun_prop]
/-
**Differentiable.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.sinh (hc : Differentiable Real f) : Differentiable Real fun
 x => Real.sinh (f x)
参数：hc : Differentiable Real f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.sinh`：DifferentiableAt.sinh (hc : DifferentiableAt Real
 f x) : DifferentiableAt Real (fun x => Real.sinh (f x)) x
-/
theorem Differentiable.sinh (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.sinh (f x) :=
  fun x => (hc x).sinh
/-
**fderivWithin_sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_sinh (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDi
ffWithinAt Real s x) : fderivWithin Real (fun x => Real.sinh (f x)) s x = Real.c
osh (f x) • fderivWithin Real f s x
参数：hf : DifferentiableWithinAt Real f s x；hxs : UniqueDiffWithinAt Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.sinh`：HasFDerivWithinAt.sinh (hf : HasFDerivWithinAt f
 f' s x) : HasFDerivWithinAt (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') s
 x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_sinh (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.sinh (f x)) s x = Real.cosh (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.sinh.fderivWithin hxs

@[simp]
/-
**fderiv_sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_sinh (hc : DifferentiableAt Real f x) : fderiv Real (fun x => Real.
sinh (f x)) x = Real.cosh (f x) • fderiv Real f x
参数：hc : DifferentiableAt Real f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.sinh`：HasFDerivAt.sinh (hf : HasFDerivAt f f' x) : HasFDeriv
At (fun x => Real.sinh (f x)) (Real.cosh (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_sinh (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.sinh (f x)) x = Real.cosh (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.sinh.fderiv
/-
**ContDiff.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.sinh {n} (h : ContDiff Real n f) : ContDiff Real n fun x => Real.
sinh (f x)
参数：h : ContDiff Real n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Real.contDiff_sinh`：contDiff_sinh {n} : ContDiff Real n sinh
-/
theorem ContDiff.sinh {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.sinh (f x) :=
  Real.contDiff_sinh.comp h
/-
**ContDiffAt.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.sinh {n} (hf : ContDiffAt Real n f x) : ContDiffAt Real n (fun 
x => Real.sinh (f x)) x
参数：hf : ContDiffAt Real n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_sinh`：contDiff_sinh {n} : ContDiff Real n sinh
-/
theorem ContDiffAt.sinh {n} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun x => Real.sinh (f x)) x :=
  Real.contDiff_sinh.contDiffAt.comp x hf
/-
**ContDiffOn.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.sinh {n} (hf : ContDiffOn Real n f s) : ContDiffOn Real n (fun 
x => Real.sinh (f x)) s
参数：hf : ContDiffOn Real n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `Real.contDiff_sinh`：contDiff_sinh {n} : ContDiff Real n sinh
-/
theorem ContDiffOn.sinh {n} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun x => Real.sinh (f x)) s :=
  Real.contDiff_sinh.comp_contDiffOn hf
/-
**ContDiffWithinAt.sinh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.sinh {n} (hf : ContDiffWithinAt Real n f s x) : ContDiffW
ithinAt Real n (fun x => Real.sinh (f x)) s x
参数：hf : ContDiffWithinAt Real n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_sinh`：contDiff_sinh {n} : ContDiff Real n sinh
-/
theorem ContDiffWithinAt.sinh {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.sinh (f x)) s x :=
  Real.contDiff_sinh.contDiffAt.comp_contDiffWithinAt x hf

section LogDeriv

@[simp]
/-
**Complex.logDeriv_cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.logDeriv_cosh : logDeriv (Complex.cosh) = Complex.tanh
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv.eq_1`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNorm
edField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜']
 (f…
· 使用定理 `Complex.deriv_cosh`：deriv_cosh : deriv cosh = sinh
· 使用引理 `Pi.div_apply`：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i 
/ g i
· 使用定理 `Complex.tanh.eq_1`：∀ (z : ℂ), Complex.tanh z = Complex.sinh z / Complex.
cosh z
-/
theorem Complex.logDeriv_cosh : logDeriv (Complex.cosh) = Complex.tanh := by
  ext
  rw [logDeriv, Complex.deriv_cosh, Pi.div_apply, Complex.tanh]

@[simp]
/-
**Real.logDeriv_cosh** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.logDeriv_cosh : logDeriv (Real.cosh) = Real.tanh
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv.eq_1`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNorm
edField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜']
 (f…
· 使用定理 `Real.deriv_cosh`：deriv_cosh : deriv cosh = sinh
· 使用引理 `Pi.div_apply`：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i 
/ g i
· 使用定理 `Real.tanh_eq_sinh_div_cosh`：∀ (x : ℝ), Real.tanh x = Real.sinh x / Real.
cosh x
-/
theorem Real.logDeriv_cosh : logDeriv (Real.cosh) = Real.tanh := by
  ext
  rw [logDeriv, Real.deriv_cosh, Pi.div_apply, Real.tanh_eq_sinh_div_cosh]

end LogDeriv

end

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

alias ⟨_, sinh_pos_of_pos⟩ := Real.sinh_pos_iff
alias ⟨_, sinh_nonneg_of_nonneg⟩ := Real.sinh_nonneg_iff
alias ⟨_, sinh_ne_zero_of_ne_zero⟩ := Real.sinh_ne_zero

/-- Extension for the `positivity` tactic: `Real.sinh` is positive/nonnegative/nonzero if its input
is. -/
@[positivity Real.sinh _]
meta def evalSinh : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  let zα : Q(Zero ℝ) := q(inferInstance)
  let pα : Q(PartialOrder ℝ) := q(inferInstance)
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.sinh $a) =>
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa => return .positive q(sinh_pos_of_pos $pa)
    | .nonnegative pa => return .nonnegative q(sinh_nonneg_of_nonneg $pa)
    | .nonzero pa => return .nonzero q(sinh_ne_zero_of_ne_zero $pa)
    | _ => return .none
  | _, _, _ => throwError "not Real.sinh"

/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (x : ℝ) (hx : 0 < x) : 0 < x.sinh := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x.sinh := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (x : ℝ) (hx : x ≠ 0) : x.sinh ≠ 0 := by positivity

end Mathlib.Meta.Positivity

