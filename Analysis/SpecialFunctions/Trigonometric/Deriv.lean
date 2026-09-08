/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiability of trigonometric functions

## Main statements

The differentiability of the usual trigonometric functions is proved, and their derivatives are
computed.

## Tags

sin, cos, tan, angle
-/

public section

noncomputable section

open scoped Asymptotics Topology Filter
open Set

namespace Complex

/-- The complex sine function is everywhere strictly differentiable, with the derivative `cos x`. -/
/-
**Complex.hasStrictDerivAt_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictDerivAt_sin (x : Complex) : HasStrictDerivAt sin (cos x) x
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
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_neg_one`：mul_neg_one (a : α) : a * -1 = -a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `HasStrictDerivAt.mul_const`：HasStrictDerivAt.mul_const (hc : HasStrictDe
rivAt c c' x) (d : 𝔸) : HasStrictDerivAt (fun y => c y * d) (c' * d) x
· 使用定理 `HasStrictDerivAt.sub`：HasStrictDerivAt.sub (hf : HasStrictDerivAt f f' x
) (hg : HasStrictDerivAt g g' x) : HasStrictDerivAt (f - g) (f' - g') x
· 使用定理 `HasStrictDerivAt.cexp`：HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f'
 x) : HasStrictDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x
· 使用定理 `HasStrictDerivAt.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField
 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f
 : 𝕜 → F} {f' …
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x

--- 原说明 ---
The complex sine function is everywhere strictly differentiable, with the deriva
tive `cos x`.
-/
theorem hasStrictDerivAt_sin (x : ℂ) : HasStrictDerivAt sin (cos x) x := by
  simp only [cos, div_eq_mul_inv]
  convert!
    ((((hasStrictDerivAt_id x).fun_neg.mul_const I).cexp.sub
              ((hasStrictDerivAt_id x).mul_const I).cexp).mul_const
          I).mul_const
      (2 : ℂ)⁻¹ using 1
  simp only [id]
  rw [sub_mul, mul_assoc, mul_assoc, I_mul_I, neg_one_mul, neg_neg, mul_one, one_mul, mul_assoc,
    I_mul_I, mul_neg_one, sub_neg_eq_add, add_comm]

/-- The complex sine function is everywhere differentiable, with the derivative `cos x`. -/
/-
**Complex.hasDerivAt_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasDerivAt_sin (x : Complex) : HasDerivAt sin (cos x) x
参数：x : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_sin`：hasStrictDerivAt_sin (x : Complex) : HasSt
rictDerivAt sin (cos x) x

--- 原说明 ---
The complex sine function is everywhere differentiable, with the derivative `cos
 x`.
-/
theorem hasDerivAt_sin (x : ℂ) : HasDerivAt sin (cos x) x :=
  (hasStrictDerivAt_sin x).hasDerivAt
/-
**Complex.isEquivalent_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isEquivalent_sin : sin ~[𝓝 0] id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Complex.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.isLittleO`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `Complex.hasDerivAt_sin`：hasDerivAt_sin (x : Complex) : HasDerivAt sin (c
os x) x
-/
theorem isEquivalent_sin : sin ~[𝓝 0] id := by simpa using! (hasDerivAt_sin 0).isLittleO

@[fun_prop]
/-
**Complex.contDiff_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：contDiff_sin {n} : ContDiff Complex n sin
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.div_const`：ContDiff.div_const {f : E -> 𝕜'} {n} (hf : ContDiff 
𝕜 n f) (c : 𝕜') : ContDiff 𝕜 n fun x => f x / c
· 使用定理 `ContDiff.mul`：ContDiff.mul {f g : E -> 𝔸} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x * g x
· 使用定理 `ContDiff.sub`：ContDiff.sub {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x - g x
· 使用定理 `ContDiff.cexp`：ContDiff.cexp {n} (h : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun
 x => Complex.exp (f x)
· 使用定理 `contDiff_neg`：contDiff_neg : ContDiff 𝕜 n fun p : F => -p
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
theorem contDiff_sin {n} : ContDiff ℂ n sin :=
  (((contDiff_neg.mul contDiff_const).cexp.sub (contDiff_id.mul contDiff_const).cexp).mul
    contDiff_const).div_const _

@[simp]
/-
**Complex.differentiable_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiable_sin : Differentiable Complex sin
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Complex.hasDerivAt_sin`：hasDerivAt_sin (x : Complex) : HasDerivAt sin (c
os x) x
-/
theorem differentiable_sin : Differentiable ℂ sin := fun x => (hasDerivAt_sin x).differentiableAt

@[simp]
/-
**Complex.differentiableAt_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiableAt_sin {x : Complex} : DifferentiableAt Complex sin x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.differentiable_sin`：differentiable_sin : Differentiable Complex 
sin
-/
theorem differentiableAt_sin {x : ℂ} : DifferentiableAt ℂ sin x :=
  differentiable_sin x

/-- The function `Complex.sin` is complex analytic. -/
@[fun_prop]
/-
**Complex.analyticAt_sin** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticAt_sin {x : Complex} : AnalyticAt Complex sin x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.analyticAt`：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : 
AnalyticAt 𝕜 f x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_sin`：contDiff_sin {n} : ContDiff Complex n sin

--- 原说明 ---
The function `Complex.sin` is complex analytic.
-/
lemma analyticAt_sin {x : ℂ} : AnalyticAt ℂ sin x :=
  contDiff_sin.contDiffAt.analyticAt

/-- The function `Complex.sin` is complex analytic. -/
/-
**Complex.analyticWithinAt_sin** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticWithinAt_sin {x : Complex} {s : Set Complex} : AnalyticWithinAt Co
mplex sin s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Complex.contDiff_sin`：contDiff_sin {n} : ContDiff Complex n sin

--- 原说明 ---
The function `Complex.sin` is complex analytic.
-/
lemma analyticWithinAt_sin {x : ℂ} {s : Set ℂ} : AnalyticWithinAt ℂ sin s x :=
  contDiff_sin.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.sin` is complex analytic. -/
/-
**Complex.analyticOnNhd_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：analyticOnNhd_sin {s : Set Complex} : AnalyticOnNhd Complex sin s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.analyticAt_sin`：analyticAt_sin {x : Complex} : AnalyticAt Comple
x sin x

--- 原说明 ---
The function `Complex.sin` is complex analytic.
-/
theorem analyticOnNhd_sin {s : Set ℂ} : AnalyticOnNhd ℂ sin s :=
  fun _ _ ↦ analyticAt_sin

/-- The function `Complex.sin` is complex analytic. -/
/-
**Complex.analyticOn_sin** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticOn_sin {s : Set Complex} : AnalyticOn Complex sin s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Complex.contDiff_sin`：contDiff_sin {n} : ContDiff Complex n sin

--- 原说明 ---
The function `Complex.sin` is complex analytic.
-/
lemma analyticOn_sin {s : Set ℂ} : AnalyticOn ℂ sin s :=
  contDiff_sin.contDiffOn.analyticOn

@[simp]
/-
**Complex.deriv_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：deriv_sin : deriv sin = cos
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Complex.hasDerivAt_sin`：hasDerivAt_sin (x : Complex) : HasDerivAt sin (c
os x) x
-/
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (hasDerivAt_sin x).deriv

/-- The complex cosine function is everywhere strictly differentiable, with the derivative
`-sin x`. -/
/-
**Complex.hasStrictDerivAt_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictDerivAt_cos (x : Complex) : HasStrictDerivAt cos (-sin x) x
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
The complex cosine function is everywhere strictly differentiable, with the deri
vative
`-sin x`.
-/
theorem hasStrictDerivAt_cos (x : ℂ) : HasStrictDerivAt cos (-sin x) x := by
  simp only [sin, div_eq_mul_inv, neg_mul_eq_neg_mul]
  convert!
    (((hasStrictDerivAt_id x).mul_const I).cexp.add
          ((hasStrictDerivAt_id x).fun_neg.mul_const I).cexp).mul_const
      (2 : ℂ)⁻¹ using 1
  simp only [id]
  ring

/-- The complex cosine function is everywhere differentiable, with the derivative `-sin x`. -/
/-
**Complex.hasDerivAt_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasDerivAt_cos (x : Complex) : HasDerivAt cos (-sin x) x
参数：x : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_cos`：hasStrictDerivAt_cos (x : Complex) : HasSt
rictDerivAt cos (-sin x) x

--- 原说明 ---
The complex cosine function is everywhere differentiable, with the derivative `-
sin x`.
-/
theorem hasDerivAt_cos (x : ℂ) : HasDerivAt cos (-sin x) x :=
  (hasStrictDerivAt_cos x).hasDerivAt

@[fun_prop]
/-
**Complex.contDiff_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：contDiff_cos {n} : ContDiff Complex n cos
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.div_const`：ContDiff.div_const {f : E -> 𝕜'} {n} (hf : ContDiff 
𝕜 n f) (c : 𝕜') : ContDiff 𝕜 n fun x => f x / c
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `ContDiff.cexp`：ContDiff.cexp {n} (h : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun
 x => Complex.exp (f x)
· 使用定理 `ContDiff.mul`：ContDiff.mul {f g : E -> 𝔸} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x * g x
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `contDiff_neg`：contDiff_neg : ContDiff 𝕜 n fun p : F => -p
-/
theorem contDiff_cos {n} : ContDiff ℂ n cos :=
  ((contDiff_id.mul contDiff_const).cexp.add (contDiff_neg.mul contDiff_const).cexp).div_const _

@[simp]
/-
**Complex.differentiable_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiable_cos : Differentiable Complex cos
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Complex.hasDerivAt_cos`：hasDerivAt_cos (x : Complex) : HasDerivAt cos (-
sin x) x
-/
theorem differentiable_cos : Differentiable ℂ cos := fun x => (hasDerivAt_cos x).differentiableAt

@[simp]
/-
**Complex.differentiableAt_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiableAt_cos {x : Complex} : DifferentiableAt Complex cos x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.differentiable_cos`：differentiable_cos : Differentiable Complex 
cos
-/
theorem differentiableAt_cos {x : ℂ} : DifferentiableAt ℂ cos x :=
  differentiable_cos x

/-- The function `Complex.cos` is complex analytic. -/
@[fun_prop]
/-
**Complex.analyticAt_cos** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticAt_cos {x : Complex} : AnalyticAt Complex cos x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.analyticAt`：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : 
AnalyticAt 𝕜 f x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_cos`：contDiff_cos {n} : ContDiff Complex n cos

--- 原说明 ---
The function `Complex.cos` is complex analytic.
-/
lemma analyticAt_cos {x : ℂ} : AnalyticAt ℂ cos x :=
  contDiff_cos.contDiffAt.analyticAt

/-- The function `Complex.cos` is complex analytic. -/
/-
**Complex.analyticWithinAt_cos** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticWithinAt_cos {x : Complex} {s : Set Complex} : AnalyticWithinAt Co
mplex cos s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Complex.contDiff_cos`：contDiff_cos {n} : ContDiff Complex n cos

--- 原说明 ---
The function `Complex.cos` is complex analytic.
-/
lemma analyticWithinAt_cos {x : ℂ} {s : Set ℂ} : AnalyticWithinAt ℂ cos s x :=
  contDiff_cos.contDiffWithinAt.analyticWithinAt

/-- The function `Complex.cos` is complex analytic. -/
/-
**Complex.analyticOnNhd_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：analyticOnNhd_cos {s : Set Complex} : AnalyticOnNhd Complex cos s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.analyticAt_cos`：analyticAt_cos {x : Complex} : AnalyticAt Comple
x cos x

--- 原说明 ---
The function `Complex.cos` is complex analytic.
-/
theorem analyticOnNhd_cos {s : Set ℂ} : AnalyticOnNhd ℂ cos s :=
  fun _ _ ↦ analyticAt_cos

/-- The function `Complex.cos` is complex analytic. -/
/-
**Complex.analyticOn_cos** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：analyticOn_cos {s : Set Complex} : AnalyticOn Complex cos s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Complex.contDiff_cos`：contDiff_cos {n} : ContDiff Complex n cos

--- 原说明 ---
The function `Complex.cos` is complex analytic.
-/
lemma analyticOn_cos {s : Set ℂ} : AnalyticOn ℂ cos s :=
  contDiff_cos.contDiffOn.analyticOn
/-
**Complex.deriv_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：deriv_cos {x : Complex} : deriv cos x = -sin x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Complex.hasDerivAt_cos`：hasDerivAt_cos (x : Complex) : HasDerivAt cos (-
sin x) x
-/
theorem deriv_cos {x : ℂ} : deriv cos x = -sin x :=
  (hasDerivAt_cos x).deriv

@[simp]
/-
**Complex.deriv_cos'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：deriv_cos' : deriv cos = fun x => -sin x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.deriv_cos`：deriv_cos {x : Complex} : deriv cos x = -sin x
-/
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun _ => deriv_cos

end Complex

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : ℂ → ℂ` -/


variable {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ}

/-! #### `Complex.cos` -/


/-
**HasStrictDerivAt.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.ccos (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (f
un x => Complex.cos (f x)) (-Complex.sin (f x) * f') x
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
· 使用定理 `Complex.hasStrictDerivAt_cos`：hasStrictDerivAt_cos (x : Complex) : HasSt
rictDerivAt cos (-sin x) x

--- 原说明 ---
#### `Complex.cos`
-/
theorem HasStrictDerivAt.ccos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.hasStrictDerivAt_cos (f x)).comp x hf
/-
**HasDerivAt.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.ccos (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Complex.co
s (f x)) (-Complex.sin (f x) * f') x
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
· 使用定理 `Complex.hasDerivAt_cos`：hasDerivAt_cos (x : Complex) : HasDerivAt cos (-
sin x) x
-/
theorem HasDerivAt.ccos (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x :=
  (Complex.hasDerivAt_cos (f x)).comp x hf
/-
**HasDerivWithinAt.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.ccos (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt 
(fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') s x
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
· 使用定理 `Complex.hasDerivAt_cos`：hasDerivAt_cos (x : Complex) : HasDerivAt cos (-
sin x) x
-/
theorem HasDerivWithinAt.ccos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') s x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf
/-
**derivWithin_ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_ccos (hf : DifferentiableWithinAt Complex f s x) (hxs : Unique
DiffWithinAt Complex s x) : derivWithin (fun x => Complex.cos (f x)) s x = -Comp
lex.sin (f x) * derivWithin f s x
参数：hf : DifferentiableWithinAt Complex f s x；hxs : UniqueDiffWithinAt Complex s 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.ccos`：HasDerivWithinAt.ccos (hf : HasDerivWithinAt f f'
 s x) : HasDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') 
s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_ccos (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.ccos.derivWithin hxs

@[simp]
/-
**deriv_ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_ccos (hc : DifferentiableAt Complex f x) : deriv (fun x => Complex.c
os (f x)) x = -Complex.sin (f x) * deriv f x
参数：hc : DifferentiableAt Complex f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.ccos`：HasDerivAt.ccos (hf : HasDerivAt f f' x) : HasDerivAt (
fun x => Complex.cos (f x)) (-Complex.sin (f x) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_ccos (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.cos (f x)) x = -Complex.sin (f x) * deriv f x :=
  hc.hasDerivAt.ccos.deriv

/-! #### `Complex.sin` -/


/-
**HasStrictDerivAt.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.csin (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (f
un x => Complex.sin (f x)) (Complex.cos (f x) * f') x
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
· 使用定理 `Complex.hasStrictDerivAt_sin`：hasStrictDerivAt_sin (x : Complex) : HasSt
rictDerivAt sin (cos x) x

--- 原说明 ---
#### `Complex.sin`
-/
theorem HasStrictDerivAt.csin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.hasStrictDerivAt_sin (f x)).comp x hf
/-
**HasDerivAt.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.csin (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Complex.si
n (f x)) (Complex.cos (f x) * f') x
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
· 使用定理 `Complex.hasDerivAt_sin`：hasDerivAt_sin (x : Complex) : HasDerivAt sin (c
os x) x
-/
theorem HasDerivAt.csin (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x :=
  (Complex.hasDerivAt_sin (f x)).comp x hf
/-
**HasDerivWithinAt.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.csin (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt 
(fun x => Complex.sin (f x)) (Complex.cos (f x) * f') s x
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
· 使用定理 `Complex.hasDerivAt_sin`：hasDerivAt_sin (x : Complex) : HasDerivAt sin (c
os x) x
-/
theorem HasDerivWithinAt.csin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') s x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf
/-
**derivWithin_csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_csin (hf : DifferentiableWithinAt Complex f s x) (hxs : Unique
DiffWithinAt Complex s x) : derivWithin (fun x => Complex.sin (f x)) s x = Compl
ex.cos (f x) * derivWithin f s x
参数：hf : DifferentiableWithinAt Complex f s x；hxs : UniqueDiffWithinAt Complex s 
x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.csin`：HasDerivWithinAt.csin (hf : HasDerivWithinAt f f'
 s x) : HasDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) * f') s
 x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_csin (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    derivWithin (fun x => Complex.sin (f x)) s x = Complex.cos (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.csin.derivWithin hxs

@[simp]
/-
**deriv_csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_csin (hc : DifferentiableAt Complex f x) : deriv (fun x => Complex.s
in (f x)) x = Complex.cos (f x) * deriv f x
参数：hc : DifferentiableAt Complex f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.csin`：HasDerivAt.csin (hf : HasDerivAt f f' x) : HasDerivAt (
fun x => Complex.sin (f x)) (Complex.cos (f x) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_csin (hc : DifferentiableAt ℂ f x) :
    deriv (fun x => Complex.sin (f x)) x = Complex.cos (f x) * deriv f x :=
  hc.hasDerivAt.csin.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Complex.cos (f x)` etc., `f : E → ℂ` -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {f' : StrongDual ℂ E}
  {x : E} {s : Set E}

/-! #### `Complex.cos` -/


/-
**HasStrictFDerivAt.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.ccos (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivAt
 (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Complex.hasStrictDerivAt_cos`：hasStrictDerivAt_cos (x : Complex) : HasSt
rictDerivAt cos (-sin x) x

--- 原说明 ---
#### `Complex.cos`
-/
theorem HasStrictFDerivAt.ccos (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf
/-
**HasFDerivAt.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.ccos (hf : HasFDerivAt f f' x) : HasFDerivAt (fun x => Complex
.cos (f x)) (-Complex.sin (f x) • f') x
参数：hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Complex.hasDerivAt_cos`：hasDerivAt_cos (x : Complex) : HasDerivAt cos (-
sin x) x
-/
theorem HasFDerivAt.ccos (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf
/-
**HasFDerivWithinAt.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.ccos (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithin
At (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') s x
参数：hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Complex.hasDerivAt_cos`：hasDerivAt_cos (x : Complex) : HasDerivAt cos (-
sin x) x
-/
theorem HasFDerivWithinAt.ccos (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') s x :=
  (Complex.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf
/-
**DifferentiableWithinAt.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.ccos (hf : DifferentiableWithinAt Complex f s x) : 
DifferentiableWithinAt Complex (fun x => Complex.cos (f x)) s x
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
· 使用定理 `HasFDerivWithinAt.ccos`：HasFDerivWithinAt.ccos (hf : HasFDerivWithinAt f
 f' s x) : HasFDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • 
f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.ccos (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.cos (f x)) s x :=
  hf.hasFDerivWithinAt.ccos.differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.ccos (hc : DifferentiableAt Complex f x) : Differentiable
At Complex (fun x => Complex.cos (f x)) x
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
· 使用定理 `HasFDerivAt.ccos`：HasFDerivAt.ccos (hf : HasFDerivAt f f' x) : HasFDeriv
At (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.ccos (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.cos (f x)) x :=
  hc.hasFDerivAt.ccos.differentiableAt
/-
**DifferentiableOn.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.ccos (hc : DifferentiableOn Complex f s) : Differentiable
On Complex (fun x => Complex.cos (f x)) s
参数：hc : DifferentiableOn Complex f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.ccos`：DifferentiableWithinAt.ccos (hf : Different
iableWithinAt Complex f s x) : DifferentiableWithinAt Complex (fun x => Complex.
cos (f x)) s x
-/
theorem DifferentiableOn.ccos (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.cos (f x)) s := fun x h => (hc x h).ccos

@[simp, fun_prop]
/-
**Differentiable.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.ccos (hc : Differentiable Complex f) : Differentiable Compl
ex fun x => Complex.cos (f x)
参数：hc : Differentiable Complex f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.ccos`：DifferentiableAt.ccos (hc : DifferentiableAt Comp
lex f x) : DifferentiableAt Complex (fun x => Complex.cos (f x)) x
-/
theorem Differentiable.ccos (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.cos (f x) := fun x => (hc x).ccos
/-
**fderivWithin_ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_ccos (hf : DifferentiableWithinAt Complex f s x) (hxs : Uniqu
eDiffWithinAt Complex s x) : fderivWithin Complex (fun x => Complex.cos (f x)) s
 x = -Complex.sin (f x) • fderivWithin Complex f s x
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
· 使用定理 `HasFDerivWithinAt.ccos`：HasFDerivWithinAt.ccos (hf : HasFDerivWithinAt f
 f' s x) : HasFDerivWithinAt (fun x => Complex.cos (f x)) (-Complex.sin (f x) • 
f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_ccos (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.cos (f x)) s x = -Complex.sin (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.ccos.fderivWithin hxs

@[simp]
/-
**fderiv_ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_ccos (hc : DifferentiableAt Complex f x) : fderiv Complex (fun x =>
 Complex.cos (f x)) x = -Complex.sin (f x) • fderiv Complex f x
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
· 使用定理 `HasFDerivAt.ccos`：HasFDerivAt.ccos (hf : HasFDerivAt f f' x) : HasFDeriv
At (fun x => Complex.cos (f x)) (-Complex.sin (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_ccos (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.cos (f x)) x = -Complex.sin (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.ccos.fderiv
/-
**ContDiff.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.ccos {n} (h : ContDiff Complex n f) : ContDiff Complex n fun x =>
 Complex.cos (f x)
参数：h : ContDiff Complex n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Complex.contDiff_cos`：contDiff_cos {n} : ContDiff Complex n cos
-/
theorem ContDiff.ccos {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.cos (f x) :=
  Complex.contDiff_cos.comp h
/-
**ContDiffAt.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.ccos {n} (hf : ContDiffAt Complex n f x) : ContDiffAt Complex n
 (fun x => Complex.cos (f x)) x
参数：hf : ContDiffAt Complex n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_cos`：contDiff_cos {n} : ContDiff Complex n cos
-/
theorem ContDiffAt.ccos {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.cos (f x)) x :=
  Complex.contDiff_cos.contDiffAt.comp x hf
/-
**ContDiffOn.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.ccos {n} (hf : ContDiffOn Complex n f s) : ContDiffOn Complex n
 (fun x => Complex.cos (f x)) s
参数：hf : ContDiffOn Complex n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `Complex.contDiff_cos`：contDiff_cos {n} : ContDiff Complex n cos
-/
theorem ContDiffOn.ccos {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.cos (f x)) s :=
  Complex.contDiff_cos.comp_contDiffOn hf
/-
**ContDiffWithinAt.ccos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.ccos {n} (hf : ContDiffWithinAt Complex n f s x) : ContDi
ffWithinAt Complex n (fun x => Complex.cos (f x)) s x
参数：hf : ContDiffWithinAt Complex n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_cos`：contDiff_cos {n} : ContDiff Complex n cos
-/
theorem ContDiffWithinAt.ccos {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.cos (f x)) s x :=
  Complex.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf

/-! #### `Complex.sin` -/


/-
**HasStrictFDerivAt.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.csin (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivAt
 (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Complex.hasStrictDerivAt_sin`：hasStrictDerivAt_sin (x : Complex) : HasSt
rictDerivAt sin (cos x) x

--- 原说明 ---
#### `Complex.sin`
-/
theorem HasStrictFDerivAt.csin (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf
/-
**HasFDerivAt.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.csin (hf : HasFDerivAt f f' x) : HasFDerivAt (fun x => Complex
.sin (f x)) (Complex.cos (f x) • f') x
参数：hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Complex.hasDerivAt_sin`：hasDerivAt_sin (x : Complex) : HasDerivAt sin (c
os x) x
-/
theorem HasFDerivAt.csin (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf
/-
**HasFDerivWithinAt.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.csin (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithin
At (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') s x
参数：hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Complex.hasDerivAt_sin`：hasDerivAt_sin (x : Complex) : HasDerivAt sin (c
os x) x
-/
theorem HasFDerivWithinAt.csin (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') s x :=
  (Complex.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf
/-
**DifferentiableWithinAt.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.csin (hf : DifferentiableWithinAt Complex f s x) : 
DifferentiableWithinAt Complex (fun x => Complex.sin (f x)) s x
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
· 使用定理 `HasFDerivWithinAt.csin`：HasFDerivWithinAt.csin (hf : HasFDerivWithinAt f
 f' s x) : HasFDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f
') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.csin (hf : DifferentiableWithinAt ℂ f s x) :
    DifferentiableWithinAt ℂ (fun x => Complex.sin (f x)) s x :=
  hf.hasFDerivWithinAt.csin.differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.csin (hc : DifferentiableAt Complex f x) : Differentiable
At Complex (fun x => Complex.sin (f x)) x
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
· 使用定理 `HasFDerivAt.csin`：HasFDerivAt.csin (hf : HasFDerivAt f f' x) : HasFDeriv
At (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.csin (hc : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (fun x => Complex.sin (f x)) x :=
  hc.hasFDerivAt.csin.differentiableAt
/-
**DifferentiableOn.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.csin (hc : DifferentiableOn Complex f s) : Differentiable
On Complex (fun x => Complex.sin (f x)) s
参数：hc : DifferentiableOn Complex f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.csin`：DifferentiableWithinAt.csin (hf : Different
iableWithinAt Complex f s x) : DifferentiableWithinAt Complex (fun x => Complex.
sin (f x)) s x
-/
theorem DifferentiableOn.csin (hc : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun x => Complex.sin (f x)) s := fun x h => (hc x h).csin

@[simp, fun_prop]
/-
**Differentiable.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.csin (hc : Differentiable Complex f) : Differentiable Compl
ex fun x => Complex.sin (f x)
参数：hc : Differentiable Complex f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.csin`：DifferentiableAt.csin (hc : DifferentiableAt Comp
lex f x) : DifferentiableAt Complex (fun x => Complex.sin (f x)) x
-/
theorem Differentiable.csin (hc : Differentiable ℂ f) :
    Differentiable ℂ fun x => Complex.sin (f x) := fun x => (hc x).csin
/-
**fderivWithin_csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_csin (hf : DifferentiableWithinAt Complex f s x) (hxs : Uniqu
eDiffWithinAt Complex s x) : fderivWithin Complex (fun x => Complex.sin (f x)) s
 x = Complex.cos (f x) • fderivWithin Complex f s x
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
· 使用定理 `HasFDerivWithinAt.csin`：HasFDerivWithinAt.csin (hf : HasFDerivWithinAt f
 f' s x) : HasFDerivWithinAt (fun x => Complex.sin (f x)) (Complex.cos (f x) • f
') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_csin (hf : DifferentiableWithinAt ℂ f s x) (hxs : UniqueDiffWithinAt ℂ s x) :
    fderivWithin ℂ (fun x => Complex.sin (f x)) s x = Complex.cos (f x) • fderivWithin ℂ f s x :=
  hf.hasFDerivWithinAt.csin.fderivWithin hxs

@[simp]
/-
**fderiv_csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_csin (hc : DifferentiableAt Complex f x) : fderiv Complex (fun x =>
 Complex.sin (f x)) x = Complex.cos (f x) • fderiv Complex f x
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
· 使用定理 `HasFDerivAt.csin`：HasFDerivAt.csin (hf : HasFDerivAt f f' x) : HasFDeriv
At (fun x => Complex.sin (f x)) (Complex.cos (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_csin (hc : DifferentiableAt ℂ f x) :
    fderiv ℂ (fun x => Complex.sin (f x)) x = Complex.cos (f x) • fderiv ℂ f x :=
  hc.hasFDerivAt.csin.fderiv
/-
**ContDiff.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.csin {n} (h : ContDiff Complex n f) : ContDiff Complex n fun x =>
 Complex.sin (f x)
参数：h : ContDiff Complex n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Complex.contDiff_sin`：contDiff_sin {n} : ContDiff Complex n sin
-/
theorem ContDiff.csin {n} (h : ContDiff ℂ n f) : ContDiff ℂ n fun x => Complex.sin (f x) :=
  Complex.contDiff_sin.comp h
/-
**ContDiffAt.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.csin {n} (hf : ContDiffAt Complex n f x) : ContDiffAt Complex n
 (fun x => Complex.sin (f x)) x
参数：hf : ContDiffAt Complex n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_sin`：contDiff_sin {n} : ContDiff Complex n sin
-/
theorem ContDiffAt.csin {n} (hf : ContDiffAt ℂ n f x) :
    ContDiffAt ℂ n (fun x => Complex.sin (f x)) x :=
  Complex.contDiff_sin.contDiffAt.comp x hf
/-
**ContDiffOn.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.csin {n} (hf : ContDiffOn Complex n f s) : ContDiffOn Complex n
 (fun x => Complex.sin (f x)) s
参数：hf : ContDiffOn Complex n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `Complex.contDiff_sin`：contDiff_sin {n} : ContDiff Complex n sin
-/
theorem ContDiffOn.csin {n} (hf : ContDiffOn ℂ n f s) :
    ContDiffOn ℂ n (fun x => Complex.sin (f x)) s :=
  Complex.contDiff_sin.comp_contDiffOn hf
/-
**ContDiffWithinAt.csin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.csin {n} (hf : ContDiffWithinAt Complex n f s x) : ContDi
ffWithinAt Complex n (fun x => Complex.sin (f x)) s x
参数：hf : ContDiffWithinAt Complex n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Complex.contDiff_sin`：contDiff_sin {n} : ContDiff Complex n sin
-/
theorem ContDiffWithinAt.csin {n} (hf : ContDiffWithinAt ℂ n f s x) :
    ContDiffWithinAt ℂ n (fun x => Complex.sin (f x)) s x :=
  Complex.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf

end

namespace Real

variable {x y z : ℝ}

/-
**Real.hasStrictDerivAt_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_sin (x : Real) : HasStrictDerivAt sin (cos x) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.real_of_complex`：HasStrictDerivAt.real_of_complex (h : 
HasStrictDerivAt e e' z) : HasStrictDerivAt (fun x : Real => (e x).re) e'.re z
· 使用定理 `Complex.hasStrictDerivAt_sin`：hasStrictDerivAt_sin (x : Complex) : HasSt
rictDerivAt sin (cos x) x
-/
theorem hasStrictDerivAt_sin (x : ℝ) : HasStrictDerivAt sin (cos x) x :=
  (Complex.hasStrictDerivAt_sin x).real_of_complex
/-
**Real.hasDerivAt_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_sin (x : Real) : HasDerivAt sin (cos x) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Real.hasStrictDerivAt_sin`：hasStrictDerivAt_sin (x : Real) : HasStrictDe
rivAt sin (cos x) x
-/
theorem hasDerivAt_sin (x : ℝ) : HasDerivAt sin (cos x) x :=
  (hasStrictDerivAt_sin x).hasDerivAt
/-
**Real.isEquivalent_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isEquivalent_sin : sin ~[𝓝 0] id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.isLittleO`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `Real.hasDerivAt_sin`：hasDerivAt_sin (x : Real) : HasDerivAt sin (cos x) 
x
-/
theorem isEquivalent_sin : sin ~[𝓝 0] id := by simpa using! (hasDerivAt_sin 0).isLittleO

@[fun_prop]
/-
**Real.contDiff_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiff_sin {n} : ContDiff Real n sin
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.real_of_complex`：ContDiff.real_of_complex {n : WithTop Nat∞} (h
 : ContDiff Complex n e) : ContDiff Real n fun x : Real => (e x).re
· 使用定理 `Complex.contDiff_sin`：contDiff_sin {n} : ContDiff Complex n sin
-/
theorem contDiff_sin {n} : ContDiff ℝ n sin :=
  Complex.contDiff_sin.real_of_complex

@[simp]
/-
**Real.differentiable_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_sin : Differentiable Real sin
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Real.hasDerivAt_sin`：hasDerivAt_sin (x : Real) : HasDerivAt sin (cos x) 
x
-/
theorem differentiable_sin : Differentiable ℝ sin := fun x => (hasDerivAt_sin x).differentiableAt

@[simp]
/-
**Real.differentiableAt_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_sin : DifferentiableAt Real sin x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.differentiable_sin`：differentiable_sin : Differentiable Real sin
-/
theorem differentiableAt_sin : DifferentiableAt ℝ sin x :=
  differentiable_sin x

/-- The function `Real.sin` is real analytic. -/
@[fun_prop]
/-
**Real.analyticAt_sin** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticAt_sin : AnalyticAt Real sin x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.analyticAt`：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : 
AnalyticAt 𝕜 f x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_sin`：contDiff_sin {n} : ContDiff Real n sin

--- 原说明 ---
The function `Real.sin` is real analytic.
-/
lemma analyticAt_sin : AnalyticAt ℝ sin x :=
  contDiff_sin.contDiffAt.analyticAt

/-- The function `Real.sin` is real analytic. -/
/-
**Real.analyticWithinAt_sin** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticWithinAt_sin {s : Set Real} : AnalyticWithinAt Real sin s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Real.contDiff_sin`：contDiff_sin {n} : ContDiff Real n sin

--- 原说明 ---
The function `Real.sin` is real analytic.
-/
lemma analyticWithinAt_sin {s : Set ℝ} : AnalyticWithinAt ℝ sin s x :=
  contDiff_sin.contDiffWithinAt.analyticWithinAt

/-- The function `Real.sin` is real analytic. -/
/-
**Real.analyticOnNhd_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：analyticOnNhd_sin {s : Set Real} : AnalyticOnNhd Real sin s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.analyticAt_sin`：analyticAt_sin : AnalyticAt Real sin x

--- 原说明 ---
The function `Real.sin` is real analytic.
-/
theorem analyticOnNhd_sin {s : Set ℝ} : AnalyticOnNhd ℝ sin s :=
  fun _ _ ↦ analyticAt_sin

/-- The function `Real.sin` is real analytic. -/
/-
**Real.analyticOn_sin** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticOn_sin {s : Set Real} : AnalyticOn Real sin s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Real.contDiff_sin`：contDiff_sin {n} : ContDiff Real n sin

--- 原说明 ---
The function `Real.sin` is real analytic.
-/
lemma analyticOn_sin {s : Set ℝ} : AnalyticOn ℝ sin s :=
  contDiff_sin.contDiffOn.analyticOn

@[simp]
/-
**Real.deriv_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_sin : deriv sin = cos
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Real.hasDerivAt_sin`：hasDerivAt_sin (x : Real) : HasDerivAt sin (cos x) 
x
-/
theorem deriv_sin : deriv sin = cos :=
  funext fun x => (hasDerivAt_sin x).deriv
/-
**Real.hasStrictDerivAt_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_cos (x : Real) : HasStrictDerivAt cos (-sin x) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.real_of_complex`：HasStrictDerivAt.real_of_complex (h : 
HasStrictDerivAt e e' z) : HasStrictDerivAt (fun x : Real => (e x).re) e'.re z
· 使用定理 `Complex.hasStrictDerivAt_cos`：hasStrictDerivAt_cos (x : Complex) : HasSt
rictDerivAt cos (-sin x) x
-/
theorem hasStrictDerivAt_cos (x : ℝ) : HasStrictDerivAt cos (-sin x) x :=
  (Complex.hasStrictDerivAt_cos x).real_of_complex
/-
**Real.hasDerivAt_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_cos (x : Real) : HasDerivAt cos (-sin x) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.real_of_complex`：HasDerivAt.real_of_complex (h : HasDerivAt e
 e' z) : HasDerivAt (fun x : Real => (e x).re) e'.re z
· 使用定理 `Complex.hasDerivAt_cos`：hasDerivAt_cos (x : Complex) : HasDerivAt cos (-
sin x) x
-/
theorem hasDerivAt_cos (x : ℝ) : HasDerivAt cos (-sin x) x :=
  (Complex.hasDerivAt_cos x).real_of_complex

@[fun_prop]
/-
**Real.contDiff_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiff_cos {n} : ContDiff Real n cos
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.real_of_complex`：ContDiff.real_of_complex {n : WithTop Nat∞} (h
 : ContDiff Complex n e) : ContDiff Real n fun x : Real => (e x).re
· 使用定理 `Complex.contDiff_cos`：contDiff_cos {n} : ContDiff Complex n cos
-/
theorem contDiff_cos {n} : ContDiff ℝ n cos :=
  Complex.contDiff_cos.real_of_complex

@[simp]
/-
**Real.differentiable_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_cos : Differentiable Real cos
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Real.hasDerivAt_cos`：hasDerivAt_cos (x : Real) : HasDerivAt cos (-sin x)
 x
-/
theorem differentiable_cos : Differentiable ℝ cos := fun x => (hasDerivAt_cos x).differentiableAt

@[simp]
/-
**Real.differentiableAt_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_cos : DifferentiableAt Real cos x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.differentiable_cos`：differentiable_cos : Differentiable Real cos
-/
theorem differentiableAt_cos : DifferentiableAt ℝ cos x :=
  differentiable_cos x

/-- The function `Real.cos` is real analytic. -/
@[fun_prop]
/-
**Real.analyticAt_cos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticAt_cos : AnalyticAt Real cos x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.analyticAt`：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : 
AnalyticAt 𝕜 f x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_cos`：contDiff_cos {n} : ContDiff Real n cos

--- 原说明 ---
The function `Real.cos` is real analytic.
-/
lemma analyticAt_cos : AnalyticAt ℝ cos x :=
  contDiff_cos.contDiffAt.analyticAt

/-- The function `Real.cos` is real analytic. -/
/-
**Real.analyticWithinAt_cos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticWithinAt_cos {s : Set Real} : AnalyticWithinAt Real cos s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Real.contDiff_cos`：contDiff_cos {n} : ContDiff Real n cos

--- 原说明 ---
The function `Real.cos` is real analytic.
-/
lemma analyticWithinAt_cos {s : Set ℝ} : AnalyticWithinAt ℝ cos s x :=
  contDiff_cos.contDiffWithinAt.analyticWithinAt

/-- The function `Real.cos` is real analytic. -/
/-
**Real.analyticOnNhd_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：analyticOnNhd_cos {s : Set Real} : AnalyticOnNhd Real cos s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.analyticAt_cos`：analyticAt_cos : AnalyticAt Real cos x

--- 原说明 ---
The function `Real.cos` is real analytic.
-/
theorem analyticOnNhd_cos {s : Set ℝ} : AnalyticOnNhd ℝ cos s :=
  fun _ _ ↦ analyticAt_cos

/-- The function `Real.cos` is real analytic. -/
/-
**Real.analyticOn_cos** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticOn_cos {s : Set Real} : AnalyticOn Real cos s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `Real.contDiff_cos`：contDiff_cos {n} : ContDiff Real n cos

--- 原说明 ---
The function `Real.cos` is real analytic.
-/
lemma analyticOn_cos {s : Set ℝ} : AnalyticOn ℝ cos s :=
  contDiff_cos.contDiffOn.analyticOn
/-
**Real.deriv_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_cos : deriv cos x = -sin x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Real.hasDerivAt_cos`：hasDerivAt_cos (x : Real) : HasDerivAt cos (-sin x)
 x
-/
theorem deriv_cos : deriv cos x = -sin x :=
  (hasDerivAt_cos x).deriv

@[simp]
/-
**Real.deriv_cos'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_cos' : deriv cos = fun x => -sin x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.deriv_cos`：deriv_cos : deriv cos x = -sin x
-/
theorem deriv_cos' : deriv cos = fun x => -sin x :=
  funext fun _ => deriv_cos

end Real

section iteratedDeriv

/-! ### Simp lemmas for iterated derivatives of `sin` and `cos`. -/

namespace Complex

@[simp]
/-
**Complex.iteratedDeriv_add_one_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_add_one_sin (n : Nat) : iteratedDeriv (n + 1) sin = iterated
Deriv n cos
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
· 使用定理 `Complex.deriv_sin`：deriv_sin : deriv sin = cos
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
-/
theorem iteratedDeriv_add_one_sin (n : ℕ) :
    iteratedDeriv (n + 1) sin = iteratedDeriv n cos := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
/-
**Complex.iteratedDeriv_add_one_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_add_one_cos (n : Nat) : iteratedDeriv (n + 1) cos = - iterat
edDeriv n sin
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
· 使用定理 `Complex.deriv_cos'`：deriv_cos' : deriv cos = fun x => -sin x
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
· 使用定理 `deriv.neg'`：deriv.neg' : (deriv (-f)) = fun x => -deriv f x
-/
theorem iteratedDeriv_add_one_cos (n : ℕ) :
    iteratedDeriv (n + 1) cos = - iteratedDeriv n sin := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ, deriv.neg']
    ext x
    simp

@[simp]
/-
**Complex.iteratedDeriv_even_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_even_sin (n : Nat) : iteratedDeriv (2 * n) sin = (-1) ^ n * 
sin
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.iteratedDeriv_add_one_sin`：iteratedDeriv_add_one_sin (n : Nat) :
 iteratedDeriv (n + 1) sin = iteratedDeriv n cos
· 使用定理 `Complex.iteratedDeriv_add_one_cos`：iteratedDeriv_add_one_cos (n : Nat) :
 iteratedDeriv (n + 1) cos = - iteratedDeriv n sin
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
theorem iteratedDeriv_even_sin (n : ℕ) :
    iteratedDeriv (2 * n) sin = (-1) ^ n * sin := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

@[simp]
/-
**Complex.iteratedDeriv_even_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_even_cos (n : Nat) : iteratedDeriv (2 * n) cos = (-1) ^ n * 
cos
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.iteratedDeriv_add_one_cos`：iteratedDeriv_add_one_cos (n : Nat) :
 iteratedDeriv (n + 1) cos = - iteratedDeriv n sin
· 使用定理 `Complex.iteratedDeriv_add_one_sin`：iteratedDeriv_add_one_sin (n : Nat) :
 iteratedDeriv (n + 1) sin = iteratedDeriv n cos
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
theorem iteratedDeriv_even_cos (n : ℕ) :
    iteratedDeriv (2 * n) cos = (-1) ^ n * cos := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]
/-
**Complex.iteratedDeriv_odd_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_odd_sin (n : Nat) : iteratedDeriv (2 * n + 1) sin = (-1) ^ n
 * cos
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.iteratedDeriv_add_one_sin`：iteratedDeriv_add_one_sin (n : Nat) :
 iteratedDeriv (n + 1) sin = iteratedDeriv n cos
· 使用定理 `Complex.iteratedDeriv_even_cos`：iteratedDeriv_even_cos (n : Nat) : itera
tedDeriv (2 * n) cos = (-1) ^ n * cos
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_odd_sin (n : ℕ) :
    iteratedDeriv (2 * n + 1) sin = (-1) ^ n * cos := by simp
/-
**Complex.iteratedDeriv_odd_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：iteratedDeriv_odd_cos (n : Nat) : iteratedDeriv (2 * n + 1) cos = (-1) ^ (
n + 1) * sin
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.iteratedDeriv_add_one_cos`：iteratedDeriv_add_one_cos (n : Nat) :
 iteratedDeriv (n + 1) cos = - iteratedDeriv n sin
· 使用定理 `Complex.iteratedDeriv_even_sin`：iteratedDeriv_even_sin (n : Nat) : itera
tedDeriv (2 * n) sin = (-1) ^ n * sin
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_odd_cos (n : ℕ) :
    iteratedDeriv (2 * n + 1) cos = (-1) ^ (n + 1) * sin := by simp [pow_succ]
/-
**Complex.differentiable_iteratedDeriv_sin** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiable_iteratedDeriv_sin (n : Nat) : Differentiable Complex (itera
tedDeriv n sin)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem differentiable_iteratedDeriv_sin (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n sin) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sin]
/-
**Complex.differentiable_iteratedDeriv_cos** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：differentiable_iteratedDeriv_cos (n : Nat) : Differentiable Complex (itera
tedDeriv n cos)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem differentiable_iteratedDeriv_cos (n : ℕ) :
    Differentiable ℂ (iteratedDeriv n cos) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cos]

end Complex

namespace Real

@[simp]
/-
**Real.iteratedDeriv_add_one_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_add_one_sin (n : Nat) : iteratedDeriv (n + 1) sin = iterated
Deriv n cos
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
· 使用定理 `Real.deriv_sin`：deriv_sin : deriv sin = cos
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
-/
theorem iteratedDeriv_add_one_sin (n : ℕ) :
    iteratedDeriv (n + 1) sin = iteratedDeriv n cos := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
/-
**Real.iteratedDeriv_add_one_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_add_one_cos (n : Nat) : iteratedDeriv (n + 1) cos = - iterat
edDeriv n sin
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
· 使用定理 `Real.deriv_cos'`：deriv_cos' : deriv cos = fun x => -sin x
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
· 使用定理 `deriv.neg'`：deriv.neg' : (deriv (-f)) = fun x => -deriv f x
-/
theorem iteratedDeriv_add_one_cos (n : ℕ) :
    iteratedDeriv (n + 1) cos = - iteratedDeriv n sin := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ, deriv.neg']
    ext x
    simp

@[simp]
/-
**Real.iteratedDeriv_even_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_even_sin (n : Nat) : iteratedDeriv (2 * n) sin = (-1) ^ n * 
sin
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.iteratedDeriv_add_one_sin`：iteratedDeriv_add_one_sin (n : Nat) : it
eratedDeriv (n + 1) sin = iteratedDeriv n cos
· 使用定理 `Real.iteratedDeriv_add_one_cos`：iteratedDeriv_add_one_cos (n : Nat) : it
eratedDeriv (n + 1) cos = - iteratedDeriv n sin
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
theorem iteratedDeriv_even_sin (n : ℕ) :
    iteratedDeriv (2 * n) sin = (-1) ^ n * sin := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

@[simp]
/-
**Real.iteratedDeriv_even_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_even_cos (n : Nat) : iteratedDeriv (2 * n) cos = (-1) ^ n * 
cos
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
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.iteratedDeriv_add_one_cos`：iteratedDeriv_add_one_cos (n : Nat) : it
eratedDeriv (n + 1) cos = - iteratedDeriv n sin
· 使用定理 `Real.iteratedDeriv_add_one_sin`：iteratedDeriv_add_one_sin (n : Nat) : it
eratedDeriv (n + 1) sin = iteratedDeriv n cos
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
theorem iteratedDeriv_even_cos (n : ℕ) :
    iteratedDeriv (2 * n) cos = (-1) ^ n * cos := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]
/-
**Real.iteratedDeriv_odd_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_odd_sin (n : Nat) : iteratedDeriv (2 * n + 1) sin = (-1) ^ n
 * cos
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.iteratedDeriv_add_one_sin`：iteratedDeriv_add_one_sin (n : Nat) : it
eratedDeriv (n + 1) sin = iteratedDeriv n cos
· 使用定理 `Real.iteratedDeriv_even_cos`：iteratedDeriv_even_cos (n : Nat) : iterated
Deriv (2 * n) cos = (-1) ^ n * cos
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_odd_sin (n : ℕ) :
    iteratedDeriv (2 * n + 1) sin = (-1) ^ n * cos := by simp
/-
**Real.iteratedDeriv_odd_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_odd_cos (n : Nat) : iteratedDeriv (2 * n + 1) cos = (-1) ^ (
n + 1) * sin
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.iteratedDeriv_add_one_cos`：iteratedDeriv_add_one_cos (n : Nat) : it
eratedDeriv (n + 1) cos = - iteratedDeriv n sin
· 使用定理 `Real.iteratedDeriv_even_sin`：iteratedDeriv_even_sin (n : Nat) : iterated
Deriv (2 * n) sin = (-1) ^ n * sin
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_odd_cos (n : ℕ) :
    iteratedDeriv (2 * n + 1) cos = (-1) ^ (n + 1) * sin := by simp [pow_succ]
/-
**Real.differentiable_iteratedDeriv_sin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_iteratedDeriv_sin (n : Nat) : Differentiable Real (iterated
Deriv n sin)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem differentiable_iteratedDeriv_sin (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n sin) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sin]
/-
**Real.differentiable_iteratedDeriv_cos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_iteratedDeriv_cos (n : Nat) : Differentiable Real (iterated
Deriv n cos)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem differentiable_iteratedDeriv_cos (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n cos) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cos]
/-
**Real.abs_iteratedDeriv_sin_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_iteratedDeriv_sin_le_one (n : Nat) (x : Real) : |iteratedDeriv n sin x
| <= 1
参数：n : Nat；x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abs_iteratedDeriv_sin_le_one (n : ℕ) (x : ℝ) :
    |iteratedDeriv n sin x| ≤ 1 :=
  match n with
  | 0 => by simpa using Real.abs_sin_le_one x
  | 1 => by simpa using Real.abs_cos_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_sin_le_one n x
/-
**Real.abs_iteratedDeriv_cos_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_iteratedDeriv_cos_le_one (n : Nat) (x : Real) : |iteratedDeriv n cos x
| <= 1
参数：n : Nat；x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abs_iteratedDeriv_cos_le_one (n : ℕ) (x : ℝ) :
    |iteratedDeriv n cos x| ≤ 1 :=
  match n with
  | 0 => by simpa using Real.abs_cos_le_one x
  | 1 => by simpa using Real.abs_sin_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_cos_le_one n x

@[simp]
/-
**Real.iteratedDerivWithin_sin_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDerivWithin_sin_Icc (n : Nat) {a b : Real} (h : a < b) {x : Real} 
(hx : x in Icc a b) : iteratedDerivWithin n sin (Icc a b) x = iteratedDeriv n si
n x
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
· 使用定理 `Real.contDiff_sin`：contDiff_sin {n} : ContDiff Real n sin
-/
theorem iteratedDerivWithin_sin_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    iteratedDerivWithin n sin (Icc a b) x = iteratedDeriv n sin x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_sin.contDiffAt hx

@[simp]
/-
**Real.iteratedDerivWithin_cos_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDerivWithin_cos_Icc (n : Nat) {a b : Real} (h : a < b) {x : Real} 
(hx : x in Icc a b) : iteratedDerivWithin n cos (Icc a b) x = iteratedDeriv n co
s x
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
· 使用定理 `Real.contDiff_cos`：contDiff_cos {n} : ContDiff Real n cos
-/
theorem iteratedDerivWithin_cos_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    iteratedDerivWithin n cos (Icc a b) x = iteratedDeriv n cos x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc h) contDiff_cos.contDiffAt hx

@[simp]
/-
**Real.iteratedDerivWithin_sin_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDerivWithin_sin_Ioo (n : Nat) {a b x : Real} (hx : x in Ioo a b) :
 iteratedDerivWithin n sin (Ioo a b) x = iteratedDeriv n sin x
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
· 使用定理 `Real.contDiff_sin`：contDiff_sin {n} : ContDiff Real n sin
-/
theorem iteratedDerivWithin_sin_Ioo (n : ℕ) {a b x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDerivWithin n sin (Ioo a b) x = iteratedDeriv n sin x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_sin.contDiffAt hx

@[simp]
/-
**Real.iteratedDerivWithin_cos_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDerivWithin_cos_Ioo (n : Nat) {a b x : Real} (hx : x in Ioo a b) :
 iteratedDerivWithin n cos (Ioo a b) x = iteratedDeriv n cos x
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
· 使用定理 `Real.contDiff_cos`：contDiff_cos {n} : ContDiff Real n cos
-/
theorem iteratedDerivWithin_cos_Ioo (n : ℕ) {a b x : ℝ} (hx : x ∈ Ioo a b) :
    iteratedDerivWithin n cos (Ioo a b) x = iteratedDeriv n cos x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioo a b) contDiff_cos.contDiffAt hx

end Real

end iteratedDeriv

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : ℝ → ℝ` -/


variable {f : ℝ → ℝ} {f' x : ℝ} {s : Set ℝ}

/-! #### `Real.cos` -/


/-
**HasStrictDerivAt.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.cos (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (fu
n x => Real.cos (f x)) (-Real.sin (f x) * f') x
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
· 使用定理 `Real.hasStrictDerivAt_cos`：hasStrictDerivAt_cos (x : Real) : HasStrictDe
rivAt cos (-sin x) x

--- 原说明 ---
#### `Real.cos`
-/
theorem HasStrictDerivAt.cos (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.hasStrictDerivAt_cos (f x)).comp x hf
/-
**HasDerivAt.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.cos (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.cos (f
 x)) (-Real.sin (f x) * f') x
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
· 使用定理 `Real.hasDerivAt_cos`：hasDerivAt_cos (x : Real) : HasDerivAt cos (-sin x)
 x
-/
theorem HasDerivAt.cos (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') x :=
  (Real.hasDerivAt_cos (f x)).comp x hf
/-
**HasDerivWithinAt.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.cos (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (
fun x => Real.cos (f x)) (-Real.sin (f x) * f') s x
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
· 使用定理 `Real.hasDerivAt_cos`：hasDerivAt_cos (x : Real) : HasDerivAt cos (-sin x)
 x
-/
theorem HasDerivWithinAt.cos (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') s x :=
  (Real.hasDerivAt_cos (f x)).comp_hasDerivWithinAt x hf
/-
**derivWithin_cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_cos (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiff
WithinAt Real s x) : derivWithin (fun x => Real.cos (f x)) s x = -Real.sin (f x)
 * derivWithin f s x
参数：hf : DifferentiableWithinAt Real f s x；hxs : UniqueDiffWithinAt Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.cos`：HasDerivWithinAt.cos (hf : HasDerivWithinAt f f' s
 x) : HasDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) * f') s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_cos (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.cos (f x)) s x = -Real.sin (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cos.derivWithin hxs

@[simp]
/-
**deriv_cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_cos (hc : DifferentiableAt Real f x) : deriv (fun x => Real.cos (f x
)) x = -Real.sin (f x) * deriv f x
参数：hc : DifferentiableAt Real f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.cos`：HasDerivAt.cos (hf : HasDerivAt f f' x) : HasDerivAt (fu
n x => Real.cos (f x)) (-Real.sin (f x) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_cos (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.cos (f x)) x = -Real.sin (f x) * deriv f x :=
  hc.hasDerivAt.cos.deriv

/-! #### `Real.sin` -/


/-
**HasStrictDerivAt.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.sin (hf : HasStrictDerivAt f f' x) : HasStrictDerivAt (fu
n x => Real.sin (f x)) (Real.cos (f x) * f') x
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
· 使用定理 `Real.hasStrictDerivAt_sin`：hasStrictDerivAt_sin (x : Real) : HasStrictDe
rivAt sin (cos x) x

--- 原说明 ---
#### `Real.sin`
-/
theorem HasStrictDerivAt.sin (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.hasStrictDerivAt_sin (f x)).comp x hf
/-
**HasDerivAt.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.sin (hf : HasDerivAt f f' x) : HasDerivAt (fun x => Real.sin (f
 x)) (Real.cos (f x) * f') x
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
· 使用定理 `Real.hasDerivAt_sin`：hasDerivAt_sin (x : Real) : HasDerivAt sin (cos x) 
x
-/
theorem HasDerivAt.sin (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') x :=
  (Real.hasDerivAt_sin (f x)).comp x hf
/-
**HasDerivWithinAt.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.sin (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (
fun x => Real.sin (f x)) (Real.cos (f x) * f') s x
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
· 使用定理 `Real.hasDerivAt_sin`：hasDerivAt_sin (x : Real) : HasDerivAt sin (cos x) 
x
-/
theorem HasDerivWithinAt.sin (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') s x :=
  (Real.hasDerivAt_sin (f x)).comp_hasDerivWithinAt x hf
/-
**derivWithin_sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_sin (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiff
WithinAt Real s x) : derivWithin (fun x => Real.sin (f x)) s x = Real.cos (f x) 
* derivWithin f s x
参数：hf : DifferentiableWithinAt Real f s x；hxs : UniqueDiffWithinAt Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.sin`：HasDerivWithinAt.sin (hf : HasDerivWithinAt f f' s
 x) : HasDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_sin (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => Real.sin (f x)) s x = Real.cos (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.sin.derivWithin hxs

@[simp]
/-
**deriv_sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_sin (hc : DifferentiableAt Real f x) : deriv (fun x => Real.sin (f x
)) x = Real.cos (f x) * deriv f x
参数：hc : DifferentiableAt Real f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.sin`：HasDerivAt.sin (hf : HasDerivAt f f' x) : HasDerivAt (fu
n x => Real.sin (f x)) (Real.cos (f x) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_sin (hc : DifferentiableAt ℝ f x) :
    deriv (fun x => Real.sin (f x)) x = Real.cos (f x) * deriv f x :=
  hc.hasDerivAt.sin.deriv

end

section

/-! ### Simp lemmas for derivatives of `fun x => Real.cos (f x)` etc., `f : E → ℝ` -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {f' : StrongDual ℝ E}
  {x : E} {s : Set E}

/-! #### `Real.cos` -/


/-
**HasStrictFDerivAt.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.cos (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivAt 
(fun x => Real.cos (f x)) (-Real.sin (f x) • f') x
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Real.hasStrictDerivAt_cos`：hasStrictDerivAt_cos (x : Real) : HasStrictDe
rivAt cos (-sin x) x

--- 原说明 ---
#### `Real.cos`
-/
theorem HasStrictFDerivAt.cos (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.hasStrictDerivAt_cos (f x)).comp_hasStrictFDerivAt x hf
/-
**HasFDerivAt.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.cos (hf : HasFDerivAt f f' x) : HasFDerivAt (fun x => Real.cos
 (f x)) (-Real.sin (f x) • f') x
参数：hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Real.hasDerivAt_cos`：hasDerivAt_cos (x : Real) : HasDerivAt cos (-sin x)
 x
-/
theorem HasFDerivAt.cos (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x :=
  (Real.hasDerivAt_cos (f x)).comp_hasFDerivAt x hf
/-
**HasFDerivWithinAt.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.cos (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithinA
t (fun x => Real.cos (f x)) (-Real.sin (f x) • f') s x
参数：hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Real.hasDerivAt_cos`：hasDerivAt_cos (x : Real) : HasDerivAt cos (-sin x)
 x
-/
theorem HasFDerivWithinAt.cos (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') s x :=
  (Real.hasDerivAt_cos (f x)).comp_hasFDerivWithinAt x hf
/-
**DifferentiableWithinAt.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.cos (hf : DifferentiableWithinAt Real f s x) : Diff
erentiableWithinAt Real (fun x => Real.cos (f x)) s x
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
· 使用定理 `HasFDerivWithinAt.cos`：HasFDerivWithinAt.cos (hf : HasFDerivWithinAt f f
' s x) : HasFDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.cos (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.cos (f x)) s x :=
  hf.hasFDerivWithinAt.cos.differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.cos (hc : DifferentiableAt Real f x) : DifferentiableAt R
eal (fun x => Real.cos (f x)) x
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
· 使用定理 `HasFDerivAt.cos`：HasFDerivAt.cos (hf : HasFDerivAt f f' x) : HasFDerivAt
 (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.cos (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.cos (f x)) x :=
  hc.hasFDerivAt.cos.differentiableAt
/-
**DifferentiableOn.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.cos (hc : DifferentiableOn Real f s) : DifferentiableOn R
eal (fun x => Real.cos (f x)) s
参数：hc : DifferentiableOn Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.cos`：DifferentiableWithinAt.cos (hf : Differentia
bleWithinAt Real f s x) : DifferentiableWithinAt Real (fun x => Real.cos (f x)) 
s x
-/
theorem DifferentiableOn.cos (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.cos (f x)) s := fun x h => (hc x h).cos

@[simp, fun_prop]
/-
**Differentiable.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.cos (hc : Differentiable Real f) : Differentiable Real fun 
x => Real.cos (f x)
参数：hc : Differentiable Real f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.cos`：DifferentiableAt.cos (hc : DifferentiableAt Real f
 x) : DifferentiableAt Real (fun x => Real.cos (f x)) x
-/
theorem Differentiable.cos (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.cos (f x) :=
  fun x => (hc x).cos
/-
**fderivWithin_cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_cos (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDif
fWithinAt Real s x) : fderivWithin Real (fun x => Real.cos (f x)) s x = -Real.si
n (f x) • fderivWithin Real f s x
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
· 使用定理 `HasFDerivWithinAt.cos`：HasFDerivWithinAt.cos (hf : HasFDerivWithinAt f f
' s x) : HasFDerivWithinAt (fun x => Real.cos (f x)) (-Real.sin (f x) • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_cos (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.cos (f x)) s x = -Real.sin (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.cos.fderivWithin hxs

@[simp]
/-
**fderiv_cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_cos (hc : DifferentiableAt Real f x) : fderiv Real (fun x => Real.c
os (f x)) x = -Real.sin (f x) • fderiv Real f x
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
· 使用定理 `HasFDerivAt.cos`：HasFDerivAt.cos (hf : HasFDerivAt f f' x) : HasFDerivAt
 (fun x => Real.cos (f x)) (-Real.sin (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_cos (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.cos (f x)) x = -Real.sin (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.cos.fderiv
/-
**ContDiff.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.cos {n} (h : ContDiff Real n f) : ContDiff Real n fun x => Real.c
os (f x)
参数：h : ContDiff Real n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Real.contDiff_cos`：contDiff_cos {n} : ContDiff Real n cos
-/
theorem ContDiff.cos {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.cos (f x) :=
  Real.contDiff_cos.comp h
/-
**ContDiffAt.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.cos {n} (hf : ContDiffAt Real n f x) : ContDiffAt Real n (fun x
 => Real.cos (f x)) x
参数：hf : ContDiffAt Real n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_cos`：contDiff_cos {n} : ContDiff Real n cos
-/
theorem ContDiffAt.cos {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.cos (f x)) x :=
  Real.contDiff_cos.contDiffAt.comp x hf
/-
**ContDiffOn.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.cos {n} (hf : ContDiffOn Real n f s) : ContDiffOn Real n (fun x
 => Real.cos (f x)) s
参数：hf : ContDiffOn Real n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `Real.contDiff_cos`：contDiff_cos {n} : ContDiff Real n cos
-/
theorem ContDiffOn.cos {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.cos (f x)) s :=
  Real.contDiff_cos.comp_contDiffOn hf
/-
**ContDiffWithinAt.cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.cos {n} (hf : ContDiffWithinAt Real n f s x) : ContDiffWi
thinAt Real n (fun x => Real.cos (f x)) s x
参数：hf : ContDiffWithinAt Real n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_cos`：contDiff_cos {n} : ContDiff Real n cos
-/
theorem ContDiffWithinAt.cos {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.cos (f x)) s x :=
  Real.contDiff_cos.contDiffAt.comp_contDiffWithinAt x hf

/-! #### `Real.sin` -/


/-
**HasStrictFDerivAt.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.sin (hf : HasStrictFDerivAt f f' x) : HasStrictFDerivAt 
(fun x => Real.sin (f x)) (Real.cos (f x) • f') x
参数：hf : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Real.hasStrictDerivAt_sin`：hasStrictDerivAt_sin (x : Real) : HasStrictDe
rivAt sin (cos x) x

--- 原说明 ---
#### `Real.sin`
-/
theorem HasStrictFDerivAt.sin (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.hasStrictDerivAt_sin (f x)).comp_hasStrictFDerivAt x hf
/-
**HasFDerivAt.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.sin (hf : HasFDerivAt f f' x) : HasFDerivAt (fun x => Real.sin
 (f x)) (Real.cos (f x) • f') x
参数：hf : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Real.hasDerivAt_sin`：hasDerivAt_sin (x : Real) : HasDerivAt sin (cos x) 
x
-/
theorem HasFDerivAt.sin (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') x :=
  (Real.hasDerivAt_sin (f x)).comp_hasFDerivAt x hf
/-
**HasFDerivWithinAt.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.sin (hf : HasFDerivWithinAt f f' s x) : HasFDerivWithinA
t (fun x => Real.sin (f x)) (Real.cos (f x) • f') s x
参数：hf : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Real.hasDerivAt_sin`：hasDerivAt_sin (x : Real) : HasDerivAt sin (cos x) 
x
-/
theorem HasFDerivWithinAt.sin (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') s x :=
  (Real.hasDerivAt_sin (f x)).comp_hasFDerivWithinAt x hf
/-
**DifferentiableWithinAt.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.sin (hf : DifferentiableWithinAt Real f s x) : Diff
erentiableWithinAt Real (fun x => Real.sin (f x)) s x
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
· 使用定理 `HasFDerivWithinAt.sin`：HasFDerivWithinAt.sin (hf : HasFDerivWithinAt f f
' s x) : HasFDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.sin (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun x => Real.sin (f x)) s x :=
  hf.hasFDerivWithinAt.sin.differentiableWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.sin (hc : DifferentiableAt Real f x) : DifferentiableAt R
eal (fun x => Real.sin (f x)) x
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
· 使用定理 `HasFDerivAt.sin`：HasFDerivAt.sin (hf : HasFDerivAt f f' x) : HasFDerivAt
 (fun x => Real.sin (f x)) (Real.cos (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.sin (hc : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => Real.sin (f x)) x :=
  hc.hasFDerivAt.sin.differentiableAt
/-
**DifferentiableOn.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.sin (hc : DifferentiableOn Real f s) : DifferentiableOn R
eal (fun x => Real.sin (f x)) s
参数：hc : DifferentiableOn Real f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.sin`：DifferentiableWithinAt.sin (hf : Differentia
bleWithinAt Real f s x) : DifferentiableWithinAt Real (fun x => Real.sin (f x)) 
s x
-/
theorem DifferentiableOn.sin (hc : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun x => Real.sin (f x)) s := fun x h => (hc x h).sin

@[simp, fun_prop]
/-
**Differentiable.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.sin (hc : Differentiable Real f) : Differentiable Real fun 
x => Real.sin (f x)
参数：hc : Differentiable Real f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.sin`：DifferentiableAt.sin (hc : DifferentiableAt Real f
 x) : DifferentiableAt Real (fun x => Real.sin (f x)) x
-/
theorem Differentiable.sin (hc : Differentiable ℝ f) : Differentiable ℝ fun x => Real.sin (f x) :=
  fun x => (hc x).sin
/-
**fderivWithin_sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_sin (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDif
fWithinAt Real s x) : fderivWithin Real (fun x => Real.sin (f x)) s x = Real.cos
 (f x) • fderivWithin Real f s x
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
· 使用定理 `HasFDerivWithinAt.sin`：HasFDerivWithinAt.sin (hf : HasFDerivWithinAt f f
' s x) : HasFDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_sin (hf : DifferentiableWithinAt ℝ f s x) (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => Real.sin (f x)) s x = Real.cos (f x) • fderivWithin ℝ f s x :=
  hf.hasFDerivWithinAt.sin.fderivWithin hxs

@[simp]
/-
**fderiv_sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_sin (hc : DifferentiableAt Real f x) : fderiv Real (fun x => Real.s
in (f x)) x = Real.cos (f x) • fderiv Real f x
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
· 使用定理 `HasFDerivAt.sin`：HasFDerivAt.sin (hf : HasFDerivAt f f' x) : HasFDerivAt
 (fun x => Real.sin (f x)) (Real.cos (f x) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_sin (hc : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => Real.sin (f x)) x = Real.cos (f x) • fderiv ℝ f x :=
  hc.hasFDerivAt.sin.fderiv
/-
**ContDiff.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.sin {n} (h : ContDiff Real n f) : ContDiff Real n fun x => Real.s
in (f x)
参数：h : ContDiff Real n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Real.contDiff_sin`：contDiff_sin {n} : ContDiff Real n sin
-/
theorem ContDiff.sin {n} (h : ContDiff ℝ n f) : ContDiff ℝ n fun x => Real.sin (f x) :=
  Real.contDiff_sin.comp h
/-
**ContDiffAt.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.sin {n} (hf : ContDiffAt Real n f x) : ContDiffAt Real n (fun x
 => Real.sin (f x)) x
参数：hf : ContDiffAt Real n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_sin`：contDiff_sin {n} : ContDiff Real n sin
-/
theorem ContDiffAt.sin {n} (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun x => Real.sin (f x)) x :=
  Real.contDiff_sin.contDiffAt.comp x hf
/-
**ContDiffOn.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.sin {n} (hf : ContDiffOn Real n f s) : ContDiffOn Real n (fun x
 => Real.sin (f x)) s
参数：hf : ContDiffOn Real n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `Real.contDiff_sin`：contDiff_sin {n} : ContDiff Real n sin
-/
theorem ContDiffOn.sin {n} (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun x => Real.sin (f x)) s :=
  Real.contDiff_sin.comp_contDiffOn hf
/-
**ContDiffWithinAt.sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.sin {n} (hf : ContDiffWithinAt Real n f s x) : ContDiffWi
thinAt Real n (fun x => Real.sin (f x)) s x
参数：hf : ContDiffWithinAt Real n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_sin`：contDiff_sin {n} : ContDiff Real n sin
-/
theorem ContDiffWithinAt.sin {n} (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun x => Real.sin (f x)) s x :=
  Real.contDiff_sin.contDiffAt.comp_contDiffWithinAt x hf

section LogDeriv

@[simp]
/-
**Complex.logDeriv_sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.logDeriv_sin : logDeriv (Complex.sin) = Complex.cot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv.eq_1`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNorm
edField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜']
 (f…
· 使用定理 `Complex.deriv_sin`：deriv_sin : deriv sin = cos
· 使用引理 `Pi.div_apply`：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i 
/ g i
· 使用定理 `Complex.cot.eq_1`：∀ (z : ℂ), z.cot = Complex.cos z / Complex.sin z
-/
theorem Complex.logDeriv_sin : logDeriv (Complex.sin) = Complex.cot := by
  ext
  rw [logDeriv, Complex.deriv_sin, Pi.div_apply, Complex.cot]

@[simp]
/-
**Real.logDeriv_sin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.logDeriv_sin : logDeriv (Real.sin) = Real.cot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv.eq_1`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNorm
edField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜']
 (f…
· 使用定理 `Real.deriv_sin`：deriv_sin : deriv sin = cos
· 使用引理 `Pi.div_apply`：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i 
/ g i
· 使用定理 `Real.cot_eq_cos_div_sin`：∀ (x : ℝ), x.cot = Real.cos x / Real.sin x
-/
theorem Real.logDeriv_sin : logDeriv (Real.sin) = Real.cot := by
  ext
  rw [logDeriv, Real.deriv_sin, Pi.div_apply, Real.cot_eq_cos_div_sin]

@[simp]
/-
**Complex.logDeriv_cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.logDeriv_cos : logDeriv (Complex.cos) = -Complex.tan
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv.eq_1`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNorm
edField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜']
 (f…
· 使用定理 `Complex.deriv_cos'`：deriv_cos' : deriv cos = fun x => -sin x
· 使用引理 `Pi.div_apply`：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i 
/ g i
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用定理 `Complex.tan.eq_1`：∀ (z : ℂ), Complex.tan z = Complex.sin z / Complex.cos
 z
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
-/
theorem Complex.logDeriv_cos : logDeriv (Complex.cos) = -Complex.tan := by
  ext
  rw [logDeriv, Complex.deriv_cos', Pi.div_apply, Pi.neg_apply, Complex.tan, neg_div]

@[simp]
/-
**Real.logDeriv_cos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.logDeriv_cos : logDeriv (Real.cos) = -Real.tan
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv.eq_1`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNorm
edField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜']
 (f…
· 使用定理 `Real.deriv_cos'`：deriv_cos' : deriv cos = fun x => -sin x
· 使用引理 `Pi.div_apply`：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i 
/ g i
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Real.tan_eq_sin_div_cos`：∀ (x : ℝ), Real.tan x = Real.sin x / Real.cos x
-/
theorem Real.logDeriv_cos : logDeriv (Real.cos) = -Real.tan := by
  ext
  rw [logDeriv, Real.deriv_cos', Pi.div_apply, Pi.neg_apply, neg_div, Real.tan_eq_sin_div_cos]

@[simp]
/-
**Complex.logDeriv_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.logDeriv_exp : logDeriv (Complex.exp) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv.eq_1`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNorm
edField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜']
 (f…
· 使用定理 `Complex.deriv_exp`：deriv_exp : deriv exp = exp
· 使用引理 `Pi.div_apply`：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i 
/ g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
-/
theorem Complex.logDeriv_exp : logDeriv (Complex.exp) = 1 := by
  ext
  rw [logDeriv, Complex.deriv_exp, Pi.div_apply, ← exp_sub, sub_self, exp_zero, Pi.one_apply]

@[deprecated (since := "2026-02-05")] alias Complex.LogDeriv_exp := Complex.logDeriv_exp

@[simp]
/-
**Real.logDeriv_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.logDeriv_exp : logDeriv (Real.exp) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `logDeriv.eq_1`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNorm
edField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra 𝕜 𝕜']
 (f…
· 使用定理 `Real.deriv_exp`：deriv_exp : deriv exp = exp
· 使用引理 `Pi.div_apply`：div_apply (f g : forall i, G i) (i : ι) : (f / g) i = f i 
/ g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
-/
theorem Real.logDeriv_exp : logDeriv (Real.exp) = 1 := by
  ext
  rw [logDeriv, Real.deriv_exp, Pi.div_apply, ← exp_sub, sub_self, exp_zero, Pi.one_apply]

@[deprecated (since := "2026-02-05")] alias Real.LogDeriv_exp := Real.logDeriv_exp

end LogDeriv

end

