/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, David Loeffler, Heather Macbeth, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.FourierTransform

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Derivatives of the Fourier transform

In this file we compute the Fréchet derivative of the Fourier transform of `f`, where `f` is a
function such that both `f` and `v ↦ ‖v‖ * ‖f v‖` are integrable. Here the Fourier transform is
understood as an operator `(V → E) → (W → E)`, where `V` and `W` are normed `ℝ`-vector spaces
and the Fourier transform is taken with respect to a continuous `ℝ`-bilinear
pairing `L : V × W → ℝ` and a given reference measure `μ`.

We also investigate higher derivatives: Assuming that `‖v‖^n * ‖f v‖` is integrable, we show
that the Fourier transform of `f` is `C^n`.

We also study in a parallel way the Fourier transform of the derivative, which is obtained by
tensoring the Fourier transform of the original function with the bilinear form. We also get
results for iterated derivatives.

A consequence of these results is that, if a function is smooth and all its derivatives are
integrable when multiplied by `‖v‖^k`, then the same goes for its Fourier transform, with
explicit bounds.

We give specialized versions of these results on inner product spaces (where `L` is the scalar
product) and on the real line, where we express the one-dimensional derivative in more concrete
terms, as the Fourier transform of `-2πI x * f x` (or `(-2πI x)^n * f x` for higher derivatives).

## Main definitions and results

We introduce two convenience definitions:

* `VectorFourier.fourierSMulRight L f`: given `f : V → E` and `L` a bilinear pairing
  between `V` and `W`, then this is the function `fun v ↦ -(2 * π * I) (L v ⬝) • f v`,
  from `V` to `Hom (W, E)`.
  This is essentially `ContinuousLinearMap.smulRight`, up to the factor `- 2πI` designed to make
  sure that the Fourier integral of `fourierSMulRight L f` is the derivative of the Fourier
  integral of `f`.
* `VectorFourier.fourierPowSMulRight` is the higher-order analogue for higher derivatives:
  `fourierPowSMulRight L f v n` is informally `(-(2 * π * I))^n (L v ⬝)^n • f v`, in
  the space of continuous multilinear maps `W [×n]→L[ℝ] E`.

With these definitions, the statements read as follows, first in a general context
(arbitrary `L` and `μ`):

* `VectorFourier.hasFDerivAt_fourierIntegral`: the Fourier integral of `f` is differentiable, with
    derivative the Fourier integral of `fourierSMulRight L f`.
* `VectorFourier.differentiable_fourierIntegral`: the Fourier integral of `f` is differentiable.
* `VectorFourier.fderiv_fourierIntegral`: formula for the derivative of the Fourier integral of `f`.
* `VectorFourier.fourierIntegral_fderiv`: formula for the Fourier integral of the derivative of `f`.
* `VectorFourier.hasFTaylorSeriesUpTo_fourierIntegral`: under suitable integrability conditions,
  the Fourier integral of `f` has an explicit Taylor series up to order `N`, given by the Fourier
  integrals of `fun v ↦ fourierPowSMulRight L f v n`.
* `VectorFourier.contDiff_fourierIntegral`: under suitable integrability conditions,
  the Fourier integral of `f` is `C^n`.
* `VectorFourier.iteratedFDeriv_fourierIntegral`: under suitable integrability conditions,
  explicit formula for the `n`-th derivative of the Fourier integral of `f`, as the Fourier
  integral of `fun v ↦ fourierPowSMulRight L f v n`.
* `VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le`: explicit bounds for the `n`-th
  derivative of the Fourier integral, multiplied by a power function, in terms of corresponding
  integrals for the original function.

These statements are then specialized to the case of the usual Fourier transform on
finite-dimensional inner product spaces with their canonical Lebesgue measure (covering in
particular the case of the real line), replacing the namespace `VectorFourier` by
the namespace `Real` in the above statements.

We also give specialized versions of the one-dimensional real derivative (and iterated derivative)
in `Real.deriv_fourierIntegral` and `Real.iteratedDeriv_fourierIntegral`.
-/

@[expose] public section

noncomputable section

open Real Complex MeasureTheory Filter TopologicalSpace

open scoped FourierTransform Topology ContDiff

-- without this local instance, Lean tries first the instance
-- `secondCountableTopologyEither_of_right` (whose priority is 100) and takes a very long time to
-- fail. Since we only use the left instance in this file, we make sure it is tried first.
attribute [local instance 101] secondCountableTopologyEither_of_left

namespace Real

/-
**Real.hasDerivAt_fourierChar** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_fourierChar (x : Real) : HasDerivAt (𝐞 · : Real -> Complex) (2 
* π * I * 𝐞 x) x
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.fourierChar_apply`：fourierChar_apply (x : Real) : 𝐞 x = Complex.exp
 (↑(2 * π * x) * Complex.I)
· 使用定理 `fourier_coe_apply`：fourier_coe_apply {n : Int} {x : Real} : fourier n (x
 : AddCircle T) = Complex.exp (2 * π * Complex.I * n * x / T)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.RingNF.mul_assoc_rev`：mul_assoc_rev (a b c : R) : a * (b 
* c) = a * b * c
· 使用定理 `Mathlib.Tactic.RingNF.nat_rawCast_1`：nat_rawCast_1 : (Nat.rawCast 1 : R)
 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
（共 45 条，此处仅展示前 30 条）
-/
lemma hasDerivAt_fourierChar (x : ℝ) : HasDerivAt (𝐞 · : ℝ → ℂ) (2 * π * I * 𝐞 x) x := by
  have h1 (y : ℝ) : 𝐞 y = fourier 1 (y : UnitAddCircle) := by
    rw [fourierChar_apply, fourier_coe_apply]
    push_cast
    ring_nf
  simpa only [h1, Int.cast_one, ofReal_one, div_one, mul_one] using hasDerivAt_fourier 1 1 x
/-
**Real.differentiable_fourierChar** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：differentiable_fourierChar : Differentiable Real (𝐞 · : Real -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Real.hasDerivAt_fourierChar`：hasDerivAt_fourierChar (x : Real) : HasDeri
vAt (𝐞 · : Real -> Complex) (2 * π * I * 𝐞 x) x
-/
lemma differentiable_fourierChar : Differentiable ℝ (𝐞 · : ℝ → ℂ) :=
  fun x ↦ (Real.hasDerivAt_fourierChar x).differentiableAt
/-
**Real.deriv_fourierChar** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：deriv_fourierChar (x : Real) : deriv (𝐞 · : Real -> Complex) x = 2 * π * I
 * 𝐞 x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Real.hasDerivAt_fourierChar`：hasDerivAt_fourierChar (x : Real) : HasDeri
vAt (𝐞 · : Real -> Complex) (2 * π * I * 𝐞 x) x
-/
lemma deriv_fourierChar (x : ℝ) : deriv (𝐞 · : ℝ → ℂ) x = 2 * π * I * 𝐞 x :=
  (Real.hasDerivAt_fourierChar x).deriv

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ)
/-
**Real.hasFDerivAt_fourierChar_neg_bilinear_right** 是 Mathlib 中的一个引理，位于命名空间 `Rea
l`。
形式化陈述：hasFDerivAt_fourierChar_neg_bilinear_right (v : V) (w : W) : HasFDerivAt (
fun w => (𝐞 (-L v w) : Complex)) ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L v
))) w
参数：v : V；w : W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `ContinuousLinearMap.comp_neg`：comp_neg [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [
IsTopologicalAddGroup M₂] [IsTopologicalAddGroup M₃] (g : M₂ ->SL[σ₂₃] M₃) (f : 
M ->SL[σ₁₂] M₂) : …
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 49 条，此处仅展示前 30 条）
-/
lemma hasFDerivAt_fourierChar_neg_bilinear_right (v : V) (w : W) :
    HasFDerivAt (fun w ↦ (𝐞 (-L v w) : ℂ))
      ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L v))) w := by
  have ha : HasFDerivAt (fun w' : W ↦ L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert! (hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg using 1
  ext y
  simp only [neg_mul, neg_smul, neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ofRealCLM_apply, smul_eq_mul, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.toSpanSingleton_apply, real_smul, neg_inj]
  ring
/-
**Real.fderiv_fourierChar_neg_bilinear_right_apply** 是 Mathlib 中的一个引理，位于命名空间 `Re
al`。
形式化陈述：fderiv_fourierChar_neg_bilinear_right_apply (v : V) (w y : W) : fderiv Rea
l (fun w => (𝐞 (-L v w) : Complex)) w y = -2 * π * I * L v y * 𝐞 (-L v w)
参数：v : V；w y : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用引理 `Real.hasFDerivAt_fourierChar_neg_bilinear_right`：hasFDerivAt_fourierChar
_neg_bilinear_right (v : V) (w : W) : HasFDerivAt (fun w => (𝐞 (-L v w) : Comple
x)) ((-2 * π * I * 𝐞 (-L v w)) • (ofR…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 44 条，此处仅展示前 30 条）
-/
lemma fderiv_fourierChar_neg_bilinear_right_apply (v : V) (w y : W) :
    fderiv ℝ (fun w ↦ (𝐞 (-L v w) : ℂ)) w y = -2 * π * I * L v y * 𝐞 (-L v w) := by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_right L v w).fderiv, neg_mul, neg_smul,
    neg_apply, smul_apply, ContinuousLinearMap.comp_apply, ofRealCLM_apply, smul_eq_mul, neg_inj]
  ring
/-
**Real.differentiable_fourierChar_neg_bilinear_right** 是 Mathlib 中的一个引理，位于命名空间 `
Real`。
形式化陈述：differentiable_fourierChar_neg_bilinear_right (v : V) : Differentiable Rea
l (fun w => (𝐞 (-L v w) : Complex))
参数：v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Real.hasFDerivAt_fourierChar_neg_bilinear_right`：hasFDerivAt_fourierChar
_neg_bilinear_right (v : V) (w : W) : HasFDerivAt (fun w => (𝐞 (-L v w) : Comple
x)) ((-2 * π * I * 𝐞 (-L v w)) • (ofR…
-/
lemma differentiable_fourierChar_neg_bilinear_right (v : V) :
    Differentiable ℝ (fun w ↦ (𝐞 (-L v w) : ℂ)) :=
  fun w ↦ (hasFDerivAt_fourierChar_neg_bilinear_right L v w).differentiableAt
/-
**Real.hasFDerivAt_fourierChar_neg_bilinear_left** 是 Mathlib 中的一个引理，位于命名空间 `Real
`。
形式化陈述：hasFDerivAt_fourierChar_neg_bilinear_left (v : V) (w : W) : HasFDerivAt (f
un v => (𝐞 (-L v w) : Complex)) ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L.fl
ip w))) v
参数：v : V；w : W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `Real.hasFDerivAt_fourierChar_neg_bilinear_right`：hasFDerivAt_fourierChar
_neg_bilinear_right (v : V) (w : W) : HasFDerivAt (fun w => (𝐞 (-L v w) : Comple
x)) ((-2 * π * I * 𝐞 (-L v w)) • (ofR…
-/
lemma hasFDerivAt_fourierChar_neg_bilinear_left (v : V) (w : W) :
    HasFDerivAt (fun v ↦ (𝐞 (-L v w) : ℂ))
      ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L.flip w))) v :=
  hasFDerivAt_fourierChar_neg_bilinear_right L.flip w v
/-
**Real.fderiv_fourierChar_neg_bilinear_left_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rea
l`。
形式化陈述：fderiv_fourierChar_neg_bilinear_left_apply (v y : V) (w : W) : fderiv Real
 (fun v => (𝐞 (-L v w) : Complex)) v y = -2 * π * I * L y w * 𝐞 (-L v w)
参数：v y : V；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用引理 `Real.hasFDerivAt_fourierChar_neg_bilinear_left`：hasFDerivAt_fourierChar_
neg_bilinear_left (v : V) (w : W) : HasFDerivAt (fun v => (𝐞 (-L v w) : Complex)
) ((-2 * π * I * 𝐞 (-L v w)) • (ofRe…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 46 条，此处仅展示前 30 条）
-/
lemma fderiv_fourierChar_neg_bilinear_left_apply (v y : V) (w : W) :
    fderiv ℝ (fun v ↦ (𝐞 (-L v w) : ℂ)) v y = -2 * π * I * L y w * 𝐞 (-L v w) := by
  simp only [(hasFDerivAt_fourierChar_neg_bilinear_left L v w).fderiv, neg_mul, neg_smul, neg_apply,
    smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ofRealCLM_apply,
    smul_eq_mul, neg_inj]
  ring
/-
**Real.differentiable_fourierChar_neg_bilinear_left** 是 Mathlib 中的一个引理，位于命名空间 `R
eal`。
形式化陈述：differentiable_fourierChar_neg_bilinear_left (w : W) : Differentiable Real
 (fun v => (𝐞 (-L v w) : Complex))
参数：w : W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用引理 `Real.hasFDerivAt_fourierChar_neg_bilinear_left`：hasFDerivAt_fourierChar_
neg_bilinear_left (v : V) (w : W) : HasFDerivAt (fun v => (𝐞 (-L v w) : Complex)
) ((-2 * π * I * 𝐞 (-L v w)) • (ofRe…
-/
lemma differentiable_fourierChar_neg_bilinear_left (w : W) :
    Differentiable ℝ (fun v ↦ (𝐞 (-L v w) : ℂ)) :=
  fun v ↦ (hasFDerivAt_fourierChar_neg_bilinear_left L v w).differentiableAt

end Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace VectorFourier

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E)

/-- Send a function `f : V → E` to the function `f : V → Hom (W, E)` given by
`v ↦ (w ↦ -2 * π * I * L (v, w) • f v)`. This is designed so that the Fourier transform of
`fourierSMulRight L f` is the derivative of the Fourier transform of `f`. -/
/-
**VectorFourier.fourierSMulRight** 是 Mathlib 中的一个定义，位于命名空间 `VectorFourier`。
形式化陈述：fourierSMulRight (v : V) : (W ->L[Real] E)
参数：v : V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
Send a function `f : V → E` to the function `f : V → Hom (W, E)` given by
`v ↦ (w ↦ -2 * π * I * L (v, w) • f v)`. This is designed so that the Fourier tr
ansform of
`fourierSMulRight L f` is the derivative of the Fourier transform of `f`.
-/
def fourierSMulRight (v : V) : (W →L[ℝ] E) := -(2 * π * I) • (L v).smulRight (f v)
/-
**VectorFourier.fourierSMulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `VectorFourier`
。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{V : Type u_2} {W : Type u_3}   [inst_2 : NormedAddCommGroup V] [inst_3 : Normed
Space ℝ V] [inst_4 : NormedAddCommGroup W] [inst_5 : NormedSpace ℝ W]   (L : V →
L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) (w : W),   (VectorFourier.fourierSMulRight L
 f v) w = -(2 * ↑Real.pi * Complex.I) • (L v) w • f v
参数：L : V →L[ℝ] W →L[ℝ] ℝ；f : V → E；v : V；w : W；VectorFourier.fourierSMulRight L 
f v；2 * ↑Real.pi * Complex.I；L v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
@[simp] lemma fourierSMulRight_apply (v : V) (w : W) :
    fourierSMulRight L f v w = -(2 * π * I) • L v w • f v := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `w`-derivative of the Fourier transform integrand. -/
/-
**VectorFourier.hasFDerivAt_fourierChar_smul** 是 Mathlib 中的一个引理，位于命名空间 `VectorFo
urier`。
形式化陈述：hasFDerivAt_fourierChar_smul (v : V) (w : W) : HasFDerivAt (fun w' => 𝐞 (-
L v w') • f v) (𝐞 (-L v w) • fourierSMulRight L f v) w
参数：v : V；w : W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `ContinuousLinearMap.toSpanSingleton_apply`：toSpanSingleton_apply (x : M₁
) (r : R₁) : toSpanSingleton R₁ x r = r • x
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
The `w`-derivative of the Fourier transform integrand.
-/
lemma hasFDerivAt_fourierChar_smul (v : V) (w : W) :
    HasFDerivAt (fun w' ↦ 𝐞 (-L v w') • f v) (𝐞 (-L v w) • fourierSMulRight L f v) w := by
  have ha : HasFDerivAt (fun w' : W ↦ L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert! ((hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg).smul_const (f v)
  ext w' : 1
  simp_rw [fourierSMulRight, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ← smul_assoc, smul_comm,
    ← smul_assoc, real_smul, real_smul, Submonoid.smul_def, smul_eq_mul]
  push_cast
  ring_nf
/-
**VectorFourier.norm_fourierSMulRight** 是 Mathlib 中的一个引理，位于命名空间 `VectorFourier`。
形式化陈述：norm_fourierSMulRight (L : V ->L[Real] W ->L[Real] Real) (f : V -> E) (v :
 V) : ‖fourierSMulRight L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖
参数：L : V ->L[Real] W ->L[Real] Real；f : V -> E；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorFourier.fourierSMulRight.eq_1`：∀ {E : Type u_1} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℂ E] {V : Type u_2} {W : Type u_3}   [inst_2 :
 NormedAddCommGroup V] [i…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Complex.norm_I`：‖Complex.I‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.norm_of_nonneg`：∀ {r : ℝ}, 0 ≤ r → ‖↑r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Complex.norm_two`：‖2‖ = 2
· 使用定理 `ContinuousLinearMap.norm_smulRight_apply`：norm_smulRight_apply (c : Stro
ngDual 𝕜 E) (f : Fₗ) : ‖smulRight c f‖ = ‖c‖ * ‖f‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma norm_fourierSMulRight (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) :
    ‖fourierSMulRight L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ := by
  rw [fourierSMulRight, norm_smul _ (ContinuousLinearMap.smulRight (L v) (f v)),
    norm_neg, norm_mul, norm_mul, norm_I, mul_one, Complex.norm_of_nonneg pi_pos.le,
    Complex.norm_two, ContinuousLinearMap.norm_smulRight_apply, ← mul_assoc]
/-
**VectorFourier.norm_fourierSMulRight_le** 是 Mathlib 中的一个引理，位于命名空间 `VectorFourie
r`。
形式化陈述：norm_fourierSMulRight_le (L : V ->L[Real] W ->L[Real] Real) (f : V -> E) (
v : V) : ‖fourierSMulRight L f v‖ <= 2 * π * ‖L‖ * ‖v‖ * ‖f v‖
参数：L : V ->L[Real] W ->L[Real] Real；f : V -> E；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `VectorFourier.norm_fourierSMulRight`：norm_fourierSMulRight (L : V ->L[Re
al] W ->L[Real] Real) (f : V -> E) (v : V) : ‖fourierSMulRight L f v‖ = (2 * π) 
* ‖L v‖ * ‖f v‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 39 条，此处仅展示前 30 条）
-/
lemma norm_fourierSMulRight_le (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) :
    ‖fourierSMulRight L f v‖ ≤ 2 * π * ‖L‖ * ‖v‖ * ‖f v‖ := calc
  ‖fourierSMulRight L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ := norm_fourierSMulRight _ _ _
  _ ≤ (2 * π) * (‖L‖ * ‖v‖) * ‖f v‖ := by gcongr; exact L.le_opNorm _
  _ = 2 * π * ‖L‖ * ‖v‖ * ‖f v‖ := by ring
/-
**VectorFourier._root_.MeasureTheory.AEStronglyMeasurable.fourierSMulRight** 是 M
athlib 中的一个引理，位于命名空间 `VectorFourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.fourierSMulRight
    [SecondCountableTopologyEither V (W →L[ℝ] ℝ)] [MeasurableSpace V] [BorelSpace V]
    {L : V →L[ℝ] W →L[ℝ] ℝ} {f : V → E} {μ : Measure V}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun v ↦ fourierSMulRight L f v) μ := by
  apply AEStronglyMeasurable.fun_const_smul
  have aux0 : Continuous fun p : (W →L[ℝ] ℝ) × E ↦ p.1.smulRight p.2 :=
    (ContinuousLinearMap.smulRightL ℝ W E).continuous₂
  have aux1 : AEStronglyMeasurable (fun v ↦ (L v, f v)) μ :=
    L.continuous.aestronglyMeasurable.prodMk hf
  -- Elaboration without the expected type is faster here:
  exact (aux0.comp_aestronglyMeasurable aux1 :)

variable {f}

/-- Main theorem of this section: if both `f` and `x ↦ ‖x‖ * ‖f x‖` are integrable, then the
Fourier transform of `f` has a Fréchet derivative (everywhere in its domain) and its derivative is
the Fourier transform of `smulRight L f`. -/
/-
**VectorFourier.hasFDerivAt_fourierIntegral** 是 Mathlib 中的一个定理，位于命名空间 `VectorFou
rier`。
形式化陈述：hasFDerivAt_fourierIntegral [MeasurableSpace V] [BorelSpace V] [SecondCoun
tableTopology V] {μ : Measure V} (hf : Integrable f μ) (hf' : Integrable (fun v 
: V => ‖v‖ * ‖f v‖) μ) (w : W) : HasFDerivAt (fourierIntegral 𝐞 μ L.toLinearMap₁
₂ f) (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fourierSMulRight L f) w) w
参数：hf : Integrable f μ；hf' : Integrable (fun v : V => ‖v‖ * ‖f v‖) μ；w : W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `VectorFourier.fourierIntegral_convergent_iff`：fourierIntegral_convergent
_iff (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> 
E} (w : W) : Integrable (fun v : V…
· 使用定理 `Real.continuous_fourierChar`：continuous_fourierChar : Continuous 𝐞
· 使用定理 `ContinuousLinearMap.continuous₂`：ContinuousLinearMap.continuous₂ (f : E 
->L[𝕜] F ->L[𝕜] G) : Continuous (Function.uncurry fun x y => f x y)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_smul`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : 
X → G}, …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Main theorem of this section: if both `f` and `x ↦ ‖x‖ * ‖f x‖` are integrable, 
then the
Fourier transform of `f` has a Fréchet derivative (everywhere in its domain) and
 its derivative is
the Fourier transform of `smulRight L f`.
-/
theorem hasFDerivAt_fourierIntegral
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V}
    (hf : Integrable f μ) (hf' : Integrable (fun v : V ↦ ‖v‖ * ‖f v‖) μ) (w : W) :
    HasFDerivAt (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)
      (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fourierSMulRight L f) w) w := by
  let F : W → V → E := fun w' v ↦ 𝐞 (-L v w') • f v
  let F' : W → V → W →L[ℝ] E := fun w' v ↦ 𝐞 (-L v w') • fourierSMulRight L f v
  let B : V → ℝ := fun v ↦ 2 * π * ‖L‖ * ‖v‖ * ‖f v‖
  have h0 (w' : W) : Integrable (F w') μ :=
    (fourierIntegral_convergent_iff continuous_fourierChar
      (by apply L.continuous₂ : Continuous (fun p : V × W ↦ L.toLinearMap₁₂ p.1 p.2)) w').2 hf
  have h1 : ∀ᶠ w' in 𝓝 w, AEStronglyMeasurable (F w') μ :=
    Eventually.of_forall (fun w' ↦ (h0 w').aestronglyMeasurable)
  have h3 : AEStronglyMeasurable (F' w) μ := by
    refine .fun_smul ?_ hf.1.fourierSMulRight
    refine (continuous_fourierChar.comp ?_).aestronglyMeasurable
    fun_prop
  have h4 : (∀ᵐ v ∂μ, ∀ (w' : W), w' ∈ Metric.ball w 1 → ‖F' w' v‖ ≤ B v) := by
    filter_upwards with v w' _
    rw [Circle.norm_smul _ (fourierSMulRight L f v)]
    exact norm_fourierSMulRight_le L f v
  have h5 : Integrable B μ := by simpa only [← mul_assoc] using hf'.const_mul (2 * π * ‖L‖)
  have h6 : ∀ᵐ v ∂μ, ∀ w', w' ∈ Metric.ball w 1 → HasFDerivAt (fun x ↦ F x v) (F' w' v) w' :=
    ae_of_all _ (fun v w' _ ↦ hasFDerivAt_fourierChar_smul L f v w')
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds _ one_pos) h1 (h0 w)
    h3 h4 h5 h6
/-
**VectorFourier.fderiv_fourierIntegral** 是 Mathlib 中的一个引理，位于命名空间 `VectorFourier`
。
形式化陈述：fderiv_fourierIntegral [MeasurableSpace V] [BorelSpace V] [SecondCountable
Topology V] {μ : Measure V} (hf : Integrable f μ) (hf' : Integrable (fun v : V =
> ‖v‖ * ‖f v‖) μ) : fderiv Real (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) = fourie
rIntegral 𝐞 μ L.toLinearMap₁₂ (fourierSMulRight L f)
参数：hf : Integrable f μ；hf' : Integrable (fun v : V => ‖v‖ * ‖f v‖) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `VectorFourier.hasFDerivAt_fourierIntegral`：hasFDerivAt_fourierIntegral [
MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V} (h
f : Integrable f μ) (hf' : Inte…
-/
lemma fderiv_fourierIntegral
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V}
    (hf : Integrable f μ) (hf' : Integrable (fun v : V ↦ ‖v‖ * ‖f v‖) μ) :
    fderiv ℝ (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) =
      fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fourierSMulRight L f) := by
  ext w : 1
  exact (hasFDerivAt_fourierIntegral L hf hf' w).fderiv
/-
**VectorFourier.differentiable_fourierIntegral** 是 Mathlib 中的一个引理，位于命名空间 `Vector
Fourier`。
形式化陈述：differentiable_fourierIntegral [MeasurableSpace V] [BorelSpace V] [SecondC
ountableTopology V] {μ : Measure V} (hf : Integrable f μ) (hf' : Integrable (fun
 v : V => ‖v‖ * ‖f v‖) μ) : Differentiable Real (fourierIntegral 𝐞 μ L.toLinearM
ap₁₂ f)
参数：hf : Integrable f μ；hf' : Integrable (fun v : V => ‖v‖ * ‖f v‖) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `VectorFourier.hasFDerivAt_fourierIntegral`：hasFDerivAt_fourierIntegral [
MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V} (h
f : Integrable f μ) (hf' : Inte…
-/
lemma differentiable_fourierIntegral
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V}
    (hf : Integrable f μ) (hf' : Integrable (fun v : V ↦ ‖v‖ * ‖f v‖) μ) :
    Differentiable ℝ (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) :=
  fun w ↦ (hasFDerivAt_fourierIntegral L hf hf' w).differentiableAt

/-- The Fourier integral of the derivative of a function is obtained by multiplying the Fourier
integral of the original function by `-L w v`. -/
/-
**VectorFourier.fourierIntegral_fderiv** 是 Mathlib 中的一个定理，位于命名空间 `VectorFourier`
。
形式化陈述：fourierIntegral_fderiv [MeasurableSpace V] [BorelSpace V] [FiniteDimension
al Real V] {μ : Measure V} [Measure.IsAddHaarMeasure μ] (hf : Integrable f μ) (h
'f : Differentiable Real f) (hf' : Integrable (fderiv Real f) μ) : fourierIntegr
al 𝐞 μ L.toLinearMap₁₂ (fderiv Real f) = fourierSMulRight (-L.flip) (fourierInte
gral 𝐞 μ L.toLinearMap₁₂ f)
参数：hf : Integrable f μ；h'f : Differentiable Real f；hf' : Integrable (fderiv Real
 f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Real.fderiv_fourierChar_neg_bilinear_left_apply`：fderiv_fourierChar_neg_
bilinear_left_apply (v y : V) (w : W) : fderiv Real (fun v => (𝐞 (-L v w) : Comp
lex)) v y = -2 * π * I * L y w * 𝐞 (-…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`：integral_smul_fde
riv_eq_neg_fderiv_smul_of_integrable {f : E -> 𝕜} {g : E -> G} {v : E} (hf'g : I
ntegrable (fun x => fderiv Real f x v • g x…
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.fourierIntegral_convergent_iff'`：fourierIntegral_convergent_iff' {V
 W : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [NormedAddCommGroup W] [
NormedSpace Real W] [Measu…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The Fourier integral of the derivative of a function is obtained by multiplying 
the Fourier
integral of the original function by `-L w v`.
-/
theorem fourierIntegral_fderiv [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ]
    (hf : Integrable f μ) (h'f : Differentiable ℝ f) (hf' : Integrable (fderiv ℝ f) μ) :
    fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fderiv ℝ f)
      = fourierSMulRight (-L.flip) (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) := by
  ext w y
  let g (v : V) : ℂ := 𝐞 (-L v w)
  /- First rewrite things in a simplified form, without any real change. -/
  suffices ∫ x, g x • fderiv ℝ f x y ∂μ = ∫ x, (2 * ↑π * I * L y w * g x) • f x ∂μ by
    rw [fourierIntegral_continuousLinearMap_apply' hf']
    simpa only [fourierIntegral, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      fourierSMulRight_apply, neg_apply, ContinuousLinearMap.flip_apply, ← integral_smul, neg_smul,
      smul_neg, ← smul_smul, coe_smul, neg_neg]
  -- Key step: integrate by parts with respect to `y` to switch the derivative from `f` to `g`.
  have A x : fderiv ℝ g x y = - 2 * ↑π * I * L y w * g x :=
    fderiv_fourierChar_neg_bilinear_left_apply _ _ _ _
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable, ← integral_neg]
  · simp only [A, neg_mul, neg_smul, neg_neg]
  · have : Integrable (fun x ↦ (-(2 * ↑π * I * ↑((L y) w)) • ((g x : ℂ) • f x))) μ :=
      ((fourierIntegral_convergent_iff' _ _).2 hf).smul _
    convert! this using 2 with x
    simp only [A, neg_mul, neg_smul, smul_smul]
  · exact (fourierIntegral_convergent_iff' _ _).2 (hf'.apply_continuousLinearMap _)
  · exact (fourierIntegral_convergent_iff' _ _).2 hf
  · exact fun _ _ ↦ (differentiable_fourierChar_neg_bilinear_left _ _).differentiableAt
  · exact fun _ _ ↦ h'f.differentiableAt

/-- The formal multilinear series whose `n`-th term is
`(w₁, ..., wₙ) ↦ (-2πI)^n * L v w₁ * ... * L v wₙ • f v`, as a continuous multilinear map in
the space `W [×n]→L[ℝ] E`.

This is designed so that the Fourier transform of `v ↦ fourierPowSMulRight L f v n` is the
`n`-th derivative of the Fourier transform of `f`.
-/
/-
**VectorFourier.fourierPowSMulRight** 是 Mathlib 中的一个定义，位于命名空间 `VectorFourier`。
形式化陈述：fourierPowSMulRight (f : V -> E) (v : V) : FormalMultilinearSeries Real W 
E
参数：f : V -> E；v : V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
The formal multilinear series whose `n`-th term is
`(w₁, ..., wₙ) ↦ (-2πI)^n * L v w₁ * ... * L v wₙ • f v`, as a continuous multil
inear map in
the space `W [×n]→L[ℝ] E`.

This is designed so that the Fourier transform of `v ↦ fourierPowSMulRight L f v
 n` is the
`n`-th derivative of the Fourier transform of `f`.
-/
def fourierPowSMulRight (f : V → E) (v : V) : FormalMultilinearSeries ℝ W E := fun n ↦
  (- (2 * π * I)) ^ n • ((ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (f v)).compContinuousLinearMap
  (fun _ ↦ L v))

/- Increase the priority to make sure that this lemma is used instead of
`FormalMultilinearSeries.apply_eq_prod_smul_coeff` even in dimension 1. -/
/-
**VectorFourier.fourierPowSMulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `VectorFouri
er`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{V : Type u_2} {W : Type u_3}   [inst_2 : NormedAddCommGroup V] [inst_3 : Normed
Space ℝ V] [inst_4 : NormedAddCommGroup W] [inst_5 : NormedSpace ℝ W]   (L : V →
L[ℝ] W →L[ℝ] ℝ) {f : V → E} {v : V} {n : ℕ} {m : Fin n → W},   (VectorFourier.fo
urierPowSMulRight L f v n) m = (-(2 * ↑Real.pi * Complex.I)) ^ n • (∏ i, (L v) (
m i)) • f v
参数：L : V →L[ℝ] W →L[ℝ] ℝ；VectorFourier.fourierPowSMulRight L f v n；-(2 * ↑Real.p
i * Complex.I)；∏ i, (L v) (m i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Increase the priority to make sure that this lemma is used instead of
`FormalMultilinearSeries.apply_eq_prod_smul_coeff` even in dimension 1.
-/
@[simp 1100] lemma fourierPowSMulRight_apply {f : V → E} {v : V} {n : ℕ} {m : Fin n → W} :
    fourierPowSMulRight L f v n m = (- (2 * π * I)) ^ n • (∏ i, L v (m i)) • f v := by
  simp [fourierPowSMulRight]

open ContinuousMultilinearMap

/-- Decomposing `fourierPowSMulRight L f v n` as a composition of continuous bilinear and
multilinear maps, to deduce easily its continuity and differentiability properties. -/
/-
**VectorFourier.fourierPowSMulRight_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `VectorFou
rier`。
形式化陈述：fourierPowSMulRight_eq_comp {f : V -> E} {v : V} {n : Nat} : fourierPowSMu
lRight L f v n = (- (2 * π * I)) ^ n • smulRightL Real (fun (_ : Fin n) => W) E 
(compContinuousLinearMapLRight (ContinuousMultilinearMap.mkPiAlgebra Real (Fin n
) Real) (fun _ => L v)) (f v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…

--- 原说明 ---
Decomposing `fourierPowSMulRight L f v n` as a composition of continuous bilinea
r and
multilinear maps, to deduce easily its continuity and differentiability properti
es.
-/
lemma fourierPowSMulRight_eq_comp {f : V → E} {v : V} {n : ℕ} :
    fourierPowSMulRight L f v n = (- (2 * π * I)) ^ n • smulRightL ℝ (fun (_ : Fin n) ↦ W) E
      (compContinuousLinearMapLRight
        (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ) (fun _ ↦ L v)) (f v) := rfl

@[continuity, fun_prop]
/-
**VectorFourier._root_.Continuous.fourierPowSMulRight** 是 Mathlib 中的一个引理，位于命名空间 
`VectorFourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Continuous.fourierPowSMulRight {f : V → E} (hf : Continuous f) (n : ℕ) :
    Continuous (fun v ↦ fourierPowSMulRight L f v n) := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply Continuous.fun_const_smul
  apply (smulRightL ℝ (fun (_ : Fin n) ↦ W) E).continuous₂.comp₂ _ hf
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _ ↦ L.continuous))
/-
**VectorFourier._root_.ContDiff.fourierPowSMulRight** 是 Mathlib 中的一个引理，位于命名空间 `V
ectorFourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContDiff.fourierPowSMulRight
    {f : V → E} {k : ℕ∞ω} (hf : ContDiff ℝ k f) (n : ℕ) :
    ContDiff ℝ k (fun v ↦ fourierPowSMulRight L f v n) := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply ContDiff.const_smul
  apply (smulRightL ℝ (fun (_ : Fin n) ↦ W) E).isBoundedBilinearMap.contDiff.comp₂ _ hf
  apply (ContinuousMultilinearMap.contDiff _).comp
  exact contDiff_pi.2 (fun _ ↦ L.contDiff)
/-
**VectorFourier.norm_fourierPowSMulRight_le** 是 Mathlib 中的一个引理，位于命名空间 `VectorFou
rier`。
形式化陈述：norm_fourierPowSMulRight_le (f : V -> E) (v : V) (n : Nat) : ‖fourierPowSM
ulRight L f v n‖ <= (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖
参数：f : V -> E；v : V；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorFourier.fourierPowSMulRight_apply`：∀ {E : Type u_1} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℂ E] {V : Type u_2} {W : Type u_3}   [inst
_2 : NormedAddCommGroup V] [i…
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 80 条，此处仅展示前 30 条）
-/
lemma norm_fourierPowSMulRight_le (f : V → E) (v : V) (n : ℕ) :
    ‖fourierPowSMulRight L f v n‖ ≤ (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m ↦ ?_)
  calc
  ‖fourierPowSMulRight L f v n m‖
    = (2 * π) ^ n * ((∏ x : Fin n, |(L v) (m x)|) * ‖f v‖) := by
      simp [abs_of_nonneg pi_nonneg, norm_smul]
  _ ≤ (2 * π) ^ n * ((∏ x : Fin n, ‖L‖ * ‖v‖ * ‖m x‖) * ‖f v‖) := by
      gcongr with i _hi
      exact L.le_opNorm₂ v (m i)
  _ = (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ * ∏ i : Fin n, ‖m i‖ := by
      simp [Finset.prod_mul_distrib, mul_pow]; ring

/-- The iterated derivative of a function multiplied by `(L v ⬝) ^ n` can be controlled in terms
of the iterated derivatives of the initial function. -/
/-
**VectorFourier.norm_iteratedFDeriv_fourierPowSMulRight** 是 Mathlib 中的一个引理，位于命名空
间 `VectorFourier`。
形式化陈述：norm_iteratedFDeriv_fourierPowSMulRight {f : V -> E} {K : Nat∞ω} {C : Real
} (hf : ContDiff Real K f) {n : Nat} {k : Nat} (hk : k <= K) {v : V} (hv : foral
l i <= k, forall j <= n, ‖v‖ ^ j * ‖iteratedFDeriv Real i f v‖ <= C) : ‖iterated
FDeriv Real k (fun v => fourierPowSMulRight L f v n) v‖ <= (2 * π) ^ n * (2 * n 
+ 2) ^ k * ‖L‖ ^ n * C
参数：hf : ContDiff Real K f；hk : k <= K；hv : forall i <= k, forall j <= n, ‖v‖ ^ j
 * ‖iteratedFDeriv Real i f v‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.norm_compContinuousLinearMapLRight_le`：norm_com
pContinuousLinearMapLRight_le (g : ContinuousMultilinearMap 𝕜 E₁ G) : ‖compConti
nuousLinearMapLRight (E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.norm_mkPiAlgebra`：norm_mkPiAlgebra [NormOneClas
s A] : ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `ContinuousMultilinearMap.norm_iteratedFDeriv_le`：norm_iteratedFDeriv_le 
(n : Nat) (x : (i : ι) -> E i) : ‖iteratedFDeriv 𝕜 n f x‖ <= Nat.descFactorial (
Fintype.card ι) n * ‖f‖ * ‖x‖ ^ (Fint…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
（共 138 条，此处仅展示前 30 条）

--- 原说明 ---
The iterated derivative of a function multiplied by `(L v ⬝) ^ n` can be control
led in terms
of the iterated derivatives of the initial function.
-/
lemma norm_iteratedFDeriv_fourierPowSMulRight
    {f : V → E} {K : ℕ∞ω} {C : ℝ} (hf : ContDiff ℝ K f) {n : ℕ} {k : ℕ} (hk : k ≤ K)
    {v : V} (hv : ∀ i ≤ k, ∀ j ≤ n, ‖v‖ ^ j * ‖iteratedFDeriv ℝ i f v‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun v ↦ fourierPowSMulRight L f v n) v‖ ≤
      (2 * π) ^ n * (2 * n + 2) ^ k * ‖L‖ ^ n * C := by
  /- We write `fourierPowSMulRight L f v n` as a composition of bilinear and multilinear maps,
  thanks to `fourierPowSMulRight_eq_comp`, and then we control the iterated derivatives of these
  thanks to general bounds on derivatives of bilinear and multilinear maps. More precisely,
  `fourierPowSMulRight L f v n m = (- (2 * π * I))^n • (∏ i, L v (m i)) • f v`. Here,
  `(- (2 * π * I))^n` contributes `(2π)^n` to the bound. The second product is bilinear, so the
  iterated derivative is controlled as a weighted sum of those of `v ↦ ∏ i, L v (m i)` and of `f`.

  The harder part is to control the iterated derivatives of `v ↦ ∏ i, L v (m i)`. For this, one
  argues that this is multilinear in `v`, to apply general bounds for iterated derivatives of
  multilinear maps. More precisely, we write it as the composition of a multilinear map `T` (making
  the product operation) and the tuple of linear maps `v ↦ (L v ⬝, ..., L v ⬝)` -/
  simp_rw [fourierPowSMulRight_eq_comp]
  -- first step: controlling the iterated derivatives of `v ↦ ∏ i, L v (m i)`, written below
  -- as `v ↦ T (fun _ ↦ L v)`, or `T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) ↦ L))`.
  let T : (W →L[ℝ] ℝ) [×n]→L[ℝ] (W [×n]→L[ℝ] ℝ) :=
    compContinuousLinearMapLRight (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ)
  have I₁ m : ‖iteratedFDeriv ℝ m T (fun _ ↦ L v)‖ ≤
      n.descFactorial m * 1 * (‖L‖ * ‖v‖) ^ (n - m) := by
    have : ‖T‖ ≤ 1 := by
      apply (norm_compContinuousLinearMapLRight_le _ _).trans
      simp only [norm_mkPiAlgebra, le_refl]
    apply (ContinuousMultilinearMap.norm_iteratedFDeriv_le _ _ _).trans
    simp only [Fintype.card_fin]
    gcongr
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun _ ↦ ?_)
    exact ContinuousLinearMap.le_opNorm _ _
  have I₂ m : ‖iteratedFDeriv ℝ m (T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) ↦ L))) v‖ ≤
      (n.descFactorial m * 1 * (‖L‖ * ‖v‖) ^ (n - m)) * ‖L‖ ^ m := by
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (ContinuousMultilinearMap.contDiff _)
      _ (mod_cast le_top)]
    apply (norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_fin]
    gcongr
    · exact I₁ m
    · exact ContinuousLinearMap.norm_pi_le_of_le (fun _ ↦ le_rfl) (norm_nonneg _)
  have I₃ m : ‖iteratedFDeriv ℝ m (T ∘ (ContinuousLinearMap.pi (fun (_ : Fin n) ↦ L))) v‖ ≤
      n.descFactorial m * ‖L‖ ^ n * ‖v‖ ^ (n - m) := by
    apply (I₂ m).trans (le_of_eq _)
    rcases le_or_gt m n with hm | hm
    · rw [show ‖L‖ ^ n = ‖L‖ ^ (m + (n - m)) by rw [Nat.add_sub_cancel' hm], pow_add]
      ring
    · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr hm, CharP.cast_eq_zero, mul_one, zero_mul]
  -- second step: factor out the `(2 * π) ^ n` factor, and cancel it on both sides.
  have A : ContDiff ℝ K (fun y ↦ T (fun _ ↦ L y)) :=
    (ContinuousMultilinearMap.contDiff _).comp (contDiff_pi.2 fun _ ↦ L.contDiff)
  rw [iteratedFDeriv_const_smul_apply' (hf := ((smulRightL ℝ (fun _ ↦ W)
    E).isBoundedBilinearMap.contDiff.comp₂ (A.of_le hk) (hf.of_le hk)).contDiffAt),
    norm_smul (β := V [×k]→L[ℝ] (W [×n]→L[ℝ] E))]
  simp only [mul_assoc, norm_pow, norm_neg, Complex.norm_mul, Complex.norm_ofNat, norm_real,
    Real.norm_eq_abs, abs_of_nonneg pi_nonneg, norm_I, mul_one, smulRightL_apply, ge_iff_le]
  gcongr
  -- third step: argue that the scalar multiplication is bilinear to bound the iterated derivatives
  -- of `v ↦ (∏ i, L v (m i)) • f v` in terms of those of `v ↦ (∏ i, L v (m i))` and of `f`.
  -- The former are controlled by the first step, the latter by the assumptions.
  apply (ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one _ A hf _
    hk ContinuousMultilinearMap.norm_smulRightL_le).trans
  calc
  ∑ i ∈ Finset.range (k + 1),
    k.choose i * ‖iteratedFDeriv ℝ i (fun (y : V) ↦ T (fun _ ↦ L y)) v‖ *
      ‖iteratedFDeriv ℝ (k - i) f v‖
    ≤ ∑ i ∈ Finset.range (k + 1),
      k.choose i * (n.descFactorial i * ‖L‖ ^ n * ‖v‖ ^ (n - i)) *
        ‖iteratedFDeriv ℝ (k - i) f v‖ := by
    gcongr with i _hi
    exact I₃ i
  _ = ∑ i ∈ Finset.range (k + 1), (k.choose i * n.descFactorial i * ‖L‖ ^ n) *
        (‖v‖ ^ (n - i) * ‖iteratedFDeriv ℝ (k - i) f v‖) := by
    congr with i
    ring
  _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i * (n + 1 : ℕ) ^ k * ‖L‖ ^ n) * C := by
    gcongr with i hi
    · norm_cast
      calc n.descFactorial i ≤ n ^ i := Nat.descFactorial_le_pow _ _
      _ ≤ (n + 1) ^ i := by gcongr; lia
      _ ≤ (n + 1) ^ k := by gcongr; exacts [le_add_self, Finset.mem_range_succ_iff.mp hi]
    · exact hv _ (by lia) _ (by lia)
  _ = (2 * n + 2) ^ k * (‖L‖ ^ n * C) := by
    simp only [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, mul_one, ← mul_assoc,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, ← mul_pow, mul_add]

variable [MeasurableSpace V] [BorelSpace V] {μ : Measure V}

section SecondCountableTopology

variable [SecondCountableTopology V]

/-
**VectorFourier._root_.MeasureTheory.AEStronglyMeasurable.fourierPowSMulRight** 
是 Mathlib 中的一个引理，位于命名空间 `VectorFourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.fourierPowSMulRight
    (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    AEStronglyMeasurable (fun v ↦ fourierPowSMulRight L f v n) μ := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply AEStronglyMeasurable.fun_const_smul
  apply (smulRightL ℝ (fun (_ : Fin n) ↦ W) E).continuous₂.comp_aestronglyMeasurable₂ _ hf
  apply Continuous.aestronglyMeasurable
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _ ↦ L.continuous))
/-
**VectorFourier.integrable_fourierPowSMulRight** 是 Mathlib 中的一个引理，位于命名空间 `Vector
Fourier`。
形式化陈述：integrable_fourierPowSMulRight {n : Nat} (hf : Integrable (fun v => ‖v‖ ^ 
n * ‖f v‖) μ) (h'f : AEStronglyMeasurable f μ) : Integrable (fun v => fourierPow
SMulRight L f v n) μ
参数：hf : Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ；h'f : AEStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fourierPowSMulRight`：∀ {E : Type u_1}
 [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {V : Type u_2} {W : Ty
pe u_3}   [inst_2 : NormedAddCommGroup V] [i…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `VectorFourier.norm_fourierPowSMulRight_le`：norm_fourierPowSMulRight_le (
f : V -> E) (v : V) (n : Nat) : ‖fourierPowSMulRight L f v n‖ <= (2 * π * ‖L‖) ^
 n * ‖v‖ ^ n * ‖f v‖
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 42 条，此处仅展示前 30 条）
-/
lemma integrable_fourierPowSMulRight {n : ℕ} (hf : Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) : Integrable (fun v ↦ fourierPowSMulRight L f v n) μ := by
  refine (hf.const_mul ((2 * π * ‖L‖) ^ n)).mono' (h'f.fourierPowSMulRight L n) ?_
  filter_upwards with v
  exact (norm_fourierPowSMulRight_le L f v n).trans (le_of_eq (by ring))
/-
**VectorFourier.hasFTaylorSeriesUpTo_fourierIntegral** 是 Mathlib 中的一个引理，位于命名空间 `
VectorFourier`。
形式化陈述：hasFTaylorSeriesUpTo_fourierIntegral {N : Nat∞ω} (hf : forall (n : Nat), n
 <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ) (h'f : AEStronglyMeasurable f 
μ) : HasFTaylorSeriesUpTo N (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) (fun w n => 
fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v => fourierPowSMulRight L f v n) w)
参数：hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ；h'f 
: AEStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.curry0_apply`：ContinuousMultilinearMap.curry0_a
pply (f : G [×0]->L[𝕜] G') : f.curry0 = f 0
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `Real.fourierIntegral_continuousMultilinearMap_apply'`：fourierIntegral_co
ntinuousMultilinearMap_apply' {f : V -> ContinuousMultilinearMap Real M E} {m : 
(i : ι) -> M i} {w : W} (hf : Integrable f…
· 使用引理 `VectorFourier.integrable_fourierPowSMulRight`：integrable_fourierPowSMulR
ight {n : Nat} (hf : Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ) (h'f : AEStronglyM
easurable f μ) : Integrable (fun v…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `VectorFourier.fourierPowSMulRight_apply`：∀ {E : Type u_1} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℂ E] {V : Type u_2} {W : Type u_3}   [inst
_2 : NormedAddCommGroup V] [i…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
（共 109 条，此处仅展示前 30 条）
-/
lemma hasFTaylorSeriesUpTo_fourierIntegral {N : ℕ∞ω}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) :
    HasFTaylorSeriesUpTo N (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)
      (fun w n ↦ fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v ↦ fourierPowSMulRight L f v n) w) := by
  constructor
  · intro w
    rw [curry0_apply, Matrix.zero_empty, fourierIntegral_continuousMultilinearMap_apply'
      (integrable_fourierPowSMulRight L (hf 0 bot_le) h'f)]
    simp only [fourierPowSMulRight_apply, pow_zero, Finset.univ_eq_empty, Finset.prod_empty,
      one_smul]
  · intro n hn w
    have I₁ : Integrable (fun v ↦ fourierPowSMulRight L f v n) μ :=
      integrable_fourierPowSMulRight L (hf n hn.le) h'f
    have I₂ : Integrable (fun v ↦ ‖v‖ * ‖fourierPowSMulRight L f v n‖) μ := by
      apply ((hf (n + 1) (ENat.add_one_natCast_le_withTop_of_lt hn)).const_mul
          ((2 * π * ‖L‖) ^ n)).mono'
        (continuous_norm.aestronglyMeasurable.mul (h'f.fourierPowSMulRight L n).norm)
      filter_upwards with v
      simp only [Pi.mul_apply, norm_mul, norm_norm]
      calc
      ‖v‖ * ‖fourierPowSMulRight L f v n‖
        ≤ ‖v‖ * ((2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖) := by
          gcongr; apply norm_fourierPowSMulRight_le
      _ = (2 * π * ‖L‖) ^ n * (‖v‖ ^ (n + 1) * ‖f v‖) := by rw [pow_succ]; ring
    have I₃ : Integrable (fun v ↦ fourierPowSMulRight L f v (n + 1)) μ :=
      integrable_fourierPowSMulRight L (hf (n + 1) (ENat.add_one_natCast_le_withTop_of_lt hn)) h'f
    have I₄ : Integrable
        (fun v ↦ fourierSMulRight L (fun v ↦ fourierPowSMulRight L f v n) v) μ := by
      apply (I₂.const_mul ((2 * π * ‖L‖))).mono' (h'f.fourierPowSMulRight L n).fourierSMulRight
      filter_upwards with v
      exact (norm_fourierSMulRight_le _ _ _).trans (le_of_eq (by ring))
    have E : curryLeft
          (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v ↦ fourierPowSMulRight L f v (n + 1)) w) =
        fourierIntegral 𝐞 μ L.toLinearMap₁₂
          (fourierSMulRight L fun v ↦ fourierPowSMulRight L f v n) w := by
      ext w' m
      rw [curryLeft_apply, fourierIntegral_continuousMultilinearMap_apply' I₃,
        fourierIntegral_continuousLinearMap_apply' I₄,
        fourierIntegral_continuousMultilinearMap_apply' (I₄.apply_continuousLinearMap _)]
      congr with v
      simp only [fourierPowSMulRight_apply, mul_comm, pow_succ, neg_mul, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, neg_smul, fourierSMulRight_apply,
        neg_apply, smul_apply, smul_comm (M := ℝ) (N := ℂ) (α := E), smul_smul]
    exact E ▸ hasFDerivAt_fourierIntegral L I₁ I₂ w
  · intro n hn
    apply fourierIntegral_continuous Real.continuous_fourierChar (by apply L.continuous₂)
    exact integrable_fourierPowSMulRight L (hf n hn) h'f

/-- Variant of `hasFTaylorSeriesUpTo_fourierIntegral` in which the smoothness index is restricted
to `ℕ∞` (and so are the inequalities in the assumption `hf`). Avoids normcasting in some
applications. -/
/-
**VectorFourier.hasFTaylorSeriesUpTo_fourierIntegral'** 是 Mathlib 中的一个引理，位于命名空间 
`VectorFourier`。
形式化陈述：hasFTaylorSeriesUpTo_fourierIntegral' {N : Nat∞} (hf : forall (n : Nat), n
 <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ) (h'f : AEStronglyMeasurable f 
μ) : HasFTaylorSeriesUpTo N (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) (fun w n => 
fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v => fourierPowSMulRight L f v n) w)
参数：hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ；h'f 
: AEStronglyMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `VectorFourier.hasFTaylorSeriesUpTo_fourierIntegral`：hasFTaylorSeriesUpTo
_fourierIntegral {N : Nat∞ω} (hf : forall (n : Nat), n <= N -> Integrable (fun v
 => ‖v‖ ^ n * ‖f v‖) μ) (h'f : AEStrongl…

--- 原说明 ---
Variant of `hasFTaylorSeriesUpTo_fourierIntegral` in which the smoothness index 
is restricted
to `ℕ∞` (and so are the inequalities in the assumption `hf`). Avoids normcasting
 in some
applications.
-/
lemma hasFTaylorSeriesUpTo_fourierIntegral' {N : ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) :
    HasFTaylorSeriesUpTo N (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)
      (fun w n ↦ fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v ↦ fourierPowSMulRight L f v n) w) :=
  hasFTaylorSeriesUpTo_fourierIntegral _ (fun n hn ↦ hf n (mod_cast hn)) h'f

/-- If `‖v‖^n * ‖f v‖` is integrable for all `n ≤ N`, then the Fourier transform of `f` is `C^N`. -/
/-
**VectorFourier.contDiff_fourierIntegral** 是 Mathlib 中的一个定理，位于命名空间 `VectorFourie
r`。
形式化陈述：contDiff_fourierIntegral {N : Nat∞} (hf : forall (n : Nat), n <= N -> Inte
grable (fun v => ‖v‖ ^ n * ‖f v‖) μ) : ContDiff Real N (fourierIntegral 𝐞 μ L.to
LinearMap₁₂ f)
参数：hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `HasFTaylorSeriesUpTo.contDiff`：HasFTaylorSeriesUpTo.contDiff {n : Nat∞} 
{f' : E -> FormalMultilinearSeries 𝕜 E F} (hf : HasFTaylorSeriesUpTo n f f') : C
ontDiff 𝕜 n f
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用引理 `VectorFourier.hasFTaylorSeriesUpTo_fourierIntegral'`：hasFTaylorSeriesUpT
o_fourierIntegral' {N : Nat∞} (hf : forall (n : Nat), n <= N -> Integrable (fun 
v => ‖v‖ ^ n * ‖f v‖) μ) (h'f : AEStrongl…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c

--- 原说明 ---
If `‖v‖^n * ‖f v‖` is integrable for all `n ≤ N`, then the Fourier transform of 
`f` is `C^N`.
-/
theorem contDiff_fourierIntegral {N : ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖) μ) :
    ContDiff ℝ N (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) := by
  by_cases h'f : Integrable f μ
  · exact (hasFTaylorSeriesUpTo_fourierIntegral' L hf h'f.1).contDiff
  · have : fourierIntegral 𝐞 μ L.toLinearMap₁₂ f = 0 := by
      ext w; simp [fourierIntegral, integral, h'f]
    simpa [this] using! contDiff_const

/-- If `‖v‖^n * ‖f v‖` is integrable for all `n ≤ N`, then the `n`-th derivative of the Fourier
transform of `f` is the Fourier transform of `fourierPowSMulRight L f v n`,
i.e., `(L v ⬝) ^ n • f v`. -/
/-
**VectorFourier.iteratedFDeriv_fourierIntegral** 是 Mathlib 中的一个引理，位于命名空间 `Vector
Fourier`。
形式化陈述：iteratedFDeriv_fourierIntegral {N : Nat∞} (hf : forall (n : Nat), n <= N -
> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ) (h'f : AEStronglyMeasurable f μ) {n :
 Nat} (hn : n <= N) : iteratedFDeriv Real n (fourierIntegral 𝐞 μ L.toLinearMap₁₂
 f) = fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v => fourierPowSMulRight L f v n)
参数：hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ；h'f 
: AEStronglyMeasurable f μ；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFTaylorSeriesUpTo.eq_iteratedFDeriv`：HasFTaylorSeriesUpTo.eq_iterated
FDeriv (h : HasFTaylorSeriesUpTo n f p) {m : Nat} (hmn : m <= n) (x : E) : p x m
 = iteratedFDeriv 𝕜 m f x
· 使用引理 `VectorFourier.hasFTaylorSeriesUpTo_fourierIntegral'`：hasFTaylorSeriesUpT
o_fourierIntegral' {N : Nat∞} (hf : forall (n : Nat), n <= N -> Integrable (fun 
v => ‖v‖ ^ n * ‖f v‖) μ) (h'f : AEStrongl…

--- 原说明 ---
If `‖v‖^n * ‖f v‖` is integrable for all `n ≤ N`, then the `n`-th derivative of 
the Fourier
transform of `f` is the Fourier transform of `fourierPowSMulRight L f v n`,
i.e., `(L v ⬝) ^ n • f v`.
-/
lemma iteratedFDeriv_fourierIntegral {N : ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) {n : ℕ} (hn : n ≤ N) :
    iteratedFDeriv ℝ n (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) =
      fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun v ↦ fourierPowSMulRight L f v n) := by
  ext w : 1
  exact ((hasFTaylorSeriesUpTo_fourierIntegral' L hf h'f).eq_iteratedFDeriv
    (mod_cast hn) w).symm

end SecondCountableTopology

/-- The Fourier integral of the `n`-th derivative of a function is obtained by multiplying the
Fourier integral of the original function by `(2πI L w ⬝ )^n`. -/
/-
**VectorFourier.fourierIntegral_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Vector
Fourier`。
形式化陈述：fourierIntegral_iteratedFDeriv [FiniteDimensional Real V] {μ : Measure V} 
[Measure.IsAddHaarMeasure μ] {N : Nat∞} (hf : ContDiff Real N f) (h'f : forall (
n : Nat), n <= N -> Integrable (iteratedFDeriv Real n f) μ) {n : Nat} (hn : n <=
 N) : fourierIntegral 𝐞 μ L.toLinearMap₁₂ (iteratedFDeriv Real n f) = (fun w => 
fourierPowSMulRight (-L.flip) (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) w n)
参数：hf : ContDiff Real N f；h'f : forall (n : Nat), n <= N -> Integrable (iterated
FDeriv Real n f) μ；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.fourierIntegral_continuousMultilinearMap_apply'`：fourierIntegral_co
ntinuousMultilinearMap_apply' {f : V -> ContinuousMultilinearMap Real M E} {m : 
(i : ι) -> M i} {w : W} (hf : Integrable f…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `VectorFourier.fourierPowSMulRight_apply`：∀ {E : Type u_1} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℂ E] {V : Type u_2} {W : Type u_3}   [inst
_2 : NormedAddCommGroup V] [i…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 93 条，此处仅展示前 30 条）

--- 原说明 ---
The Fourier integral of the `n`-th derivative of a function is obtained by multi
plying the
Fourier integral of the original function by `(2πI L w ⬝ )^n`.
-/
theorem fourierIntegral_iteratedFDeriv [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (n : ℕ), n ≤ N → Integrable (iteratedFDeriv ℝ n f) μ) {n : ℕ} (hn : n ≤ N) :
    fourierIntegral 𝐞 μ L.toLinearMap₁₂ (iteratedFDeriv ℝ n f)
      = (fun w ↦ fourierPowSMulRight (-L.flip) (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) w n) := by
  induction n with
  | zero =>
    ext w m
    simp only [iteratedFDeriv_zero_apply, fourierPowSMulRight_apply, pow_zero, Finset.univ_eq_empty,
      neg_apply, ContinuousLinearMap.flip_apply, Finset.prod_empty, one_smul,
      fourierIntegral_continuousMultilinearMap_apply' ((h'f 0 bot_le))]
  | succ n ih =>
    ext w m
    have J : Integrable (fderiv ℝ (iteratedFDeriv ℝ n f)) μ := by
      specialize h'f (n + 1) hn
      rwa [iteratedFDeriv_succ_eq_comp_left, Function.comp_def,
          LinearIsometryEquiv.integrable_comp_iff (𝕜 := ℝ) (φ := fderiv ℝ (iteratedFDeriv ℝ n f))]
        at h'f
    suffices H : (fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fderiv ℝ (iteratedFDeriv ℝ n f)) w)
          (m 0) (Fin.tail m) =
        (-(2 * π * I)) ^ (n + 1) • (∏ x : Fin (n + 1), -L (m x) w) • ∫ v, 𝐞 (-L v w) • f v ∂μ by
      rw [fourierIntegral_continuousMultilinearMap_apply' (h'f _ hn)]
      simp only [iteratedFDeriv_succ_apply_left, fourierPowSMulRight_apply, neg_apply,
        ContinuousLinearMap.flip_apply]
      rw [← fourierIntegral_continuousMultilinearMap_apply' ((J.apply_continuousLinearMap _)),
          ← fourierIntegral_continuousLinearMap_apply' J]
      exact H
    have h'n : n < N := (Nat.cast_lt.mpr n.lt_succ_self).trans_le hn
    rw [fourierIntegral_fderiv _ (h'f n h'n.le)
      (hf.differentiable_iteratedFDeriv (mod_cast h'n)) J]
    simp only [ih h'n.le, fourierSMulRight_apply, neg_apply, ContinuousLinearMap.flip_apply,
      neg_smul, smul_neg, neg_neg, smul_apply, fourierPowSMulRight_apply, ← coe_smul (E := E),
      smul_smul]
    congr 1
    simp only [ofReal_prod, ofReal_neg, pow_succ, mul_neg, Fin.prod_univ_succ, neg_mul,
      ofReal_mul, neg_neg, Fin.tail_def]
    ring

/-- The `k`-th derivative of the Fourier integral of `f`, multiplied by `(L v w) ^ n`, is the
Fourier integral of the `n`-th derivative of `(L v w) ^ k * f`. -/
/-
**VectorFourier.fourierPowSMulRight_iteratedFDeriv_fourierIntegral** 是 Mathlib 中
的一个定理，位于命名空间 `VectorFourier`。
形式化陈述：fourierPowSMulRight_iteratedFDeriv_fourierIntegral [FiniteDimensional Real
 V] {μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : Nat∞} (hf : ContDiff Rea
l N f) (h'f : forall (k n : Nat), k <= K -> n <= N -> Integrable (fun v => ‖v‖ ^
 k * ‖iteratedFDeriv Real n f v‖) μ) {k n : Nat} (hk : k <= K) (hn : n <= N) {w 
: W} : fourierPowSMulRight (-L.flip) (iteratedFDeriv Real k (fourierIntegral 𝐞 μ
 L.toLinearMap₁₂ f)) w n = fourierIntegral 𝐞 μ L.toLinearMap₁₂ (iteratedFDeriv R
eal n (fun v => fourierPow
参数：hf : ContDiff Real N f；h'f : forall (k n : Nat), k <= K -> n <= N -> Integrab
le (fun v => ‖v‖ ^ k * ‖iteratedFDeriv Real n f v‖) μ；hk : k <= K；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
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
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorFourier.fourierIntegral_iteratedFDeriv`：fourierIntegral_iteratedFD
eriv [FiniteDimensional Real V] {μ : Measure V} [Measure.IsAddHaarMeasure μ] {N 
: Nat∞} (hf : ContDiff Real N f) (…
· 使用定理 `ContDiff.fourierPowSMulRight`：∀ {E : Type u_1} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] {V : Type u_2} {W : Type u_3}   [inst_2 : Normed
AddCommGroup V] [i…
· 使用定理 `MeasureTheory.integrable_finsetSum`：integrable_finsetSum {ι} (s : Finset
 ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (fu
n a => ∑ i in s, f i a) …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
The `k`-th derivative of the Fourier integral of `f`, multiplied by `(L v w) ^ n
`, is the
Fourier integral of the `n`-th derivative of `(L v w) ^ k * f`.
-/
theorem fourierPowSMulRight_iteratedFDeriv_fourierIntegral [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (k n : ℕ), k ≤ K → n ≤ N → Integrable (fun v ↦ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) μ)
    {k n : ℕ} (hk : k ≤ K) (hn : n ≤ N) {w : W} :
    fourierPowSMulRight (-L.flip)
      (iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n =
    fourierIntegral 𝐞 μ L.toLinearMap₁₂
      (iteratedFDeriv ℝ n (fun v ↦ fourierPowSMulRight L f v k)) w := by
  rw [fourierIntegral_iteratedFDeriv (N := N) _ (hf.fourierPowSMulRight _ _) _ hn]
  · congr
    rw [iteratedFDeriv_fourierIntegral (N := K) _ _ hf.continuous.aestronglyMeasurable hk]
    intro k hk
    simpa only [norm_iteratedFDeriv_zero] using h'f k 0 hk bot_le
  · intro m hm
    have I : Integrable (fun v ↦ ∑ p ∈ Finset.range (k + 1) ×ˢ Finset.range (m + 1),
        ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖) μ := by
      apply integrable_finsetSum _ (fun p hp ↦ ?_)
      simp only [Finset.mem_product, Finset.mem_range_succ_iff] at hp
      exact h'f _ _ ((Nat.cast_le.2 hp.1).trans hk) ((Nat.cast_le.2 hp.2).trans hm)
    apply (I.const_mul ((2 * π) ^ k * (2 * k + 2) ^ m * ‖L‖ ^ k)).mono'
      ((hf.fourierPowSMulRight L k).continuous_iteratedFDeriv (mod_cast hm)).aestronglyMeasurable
    filter_upwards with v
    refine norm_iteratedFDeriv_fourierPowSMulRight _ hf (mod_cast hm) (fun i hi j hj ↦ ?_)
    apply Finset.single_le_sum (f := fun p ↦ ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖) (a := (j, i))
    · intro i _hi
      positivity
    · simpa only [Finset.mem_product, Finset.mem_range_succ_iff] using ⟨hj, hi⟩

/-- One can bound the `k`-th derivative of the Fourier integral of `f`, multiplied by `(L v w) ^ n`,
in terms of integrals of iterated derivatives of `f` (of order up to `n`) multiplied by `‖v‖ ^ i`
(for `i ≤ k`).
Auxiliary version in terms of the operator norm of `fourierPowSMulRight (-L.flip) ⬝`. For a version
in terms of `|L v w| ^ n * ⬝`, see `pow_mul_norm_iteratedFDeriv_fourierIntegral_le`.
-/
/-
**VectorFourier.norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le** 是 M
athlib 中的一个定理，位于命名空间 `VectorFourier`。
形式化陈述：norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le [FiniteDimensio
nal Real V] {μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : Nat∞} (hf : Cont
Diff Real N f) (h'f : forall (k n : Nat), k <= K -> n <= N -> Integrable (fun v 
=> ‖v‖ ^ k * ‖iteratedFDeriv Real n f v‖) μ) {k n : Nat} (hk : k <= K) (hn : n <
= N) {w : W} : ‖fourierPowSMulRight (-L.flip) (iteratedFDeriv Real k (fourierInt
egral 𝐞 μ L.toLinearMap₁₂ f)) w n‖ <= (2 * π) ^ k * (2 * k + 2) ^ n * ‖L‖ ^ k * 
∑ p in Finset.range (k + 1
参数：hf : ContDiff Real N f；h'f : forall (k n : Nat), k <= K -> n <= N -> Integrab
le (fun v => ‖v‖ ^ k * ‖iteratedFDeriv Real n f v‖) μ；hk : k <= K；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
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
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorFourier.fourierPowSMulRight_iteratedFDeriv_fourierIntegral`：fourie
rPowSMulRight_iteratedFDeriv_fourierIntegral [FiniteDimensional Real V] {μ : Mea
sure V} [Measure.IsAddHaarMeasure μ] {K N : Nat∞} (hf …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `VectorFourier.norm_fourierIntegral_le_integral_norm`：norm_fourierIntegra
l_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (
f : V -> E) (w : W) : ‖fourierIntegral e …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
One can bound the `k`-th derivative of the Fourier integral of `f`, multiplied b
y `(L v w) ^ n`,
in terms of integrals of iterated derivatives of `f` (of order up to `n`) multip
lied by `‖v‖ ^ i`
(for `i ≤ k`).
Auxiliary version in terms of the operator norm of `fourierPowSMulRight (-L.flip
) ⬝`. For a version
in terms of `|L v w| ^ n * ⬝`, see `pow_mul_norm_iteratedFDeriv_fourierIntegral_
le`.
-/
theorem norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (k n : ℕ), k ≤ K → n ≤ N → Integrable (fun v ↦ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) μ)
    {k n : ℕ} (hk : k ≤ K) (hn : n ≤ N) {w : W} :
    ‖fourierPowSMulRight (-L.flip)
      (iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n‖ ≤
    (2 * π) ^ k * (2 * k + 2) ^ n * ‖L‖ ^ k * ∑ p ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1),
      ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ ∂μ := by
  rw [fourierPowSMulRight_iteratedFDeriv_fourierIntegral L hf h'f hk hn]
  apply (norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
  have I p (hp : p ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1)) :
      Integrable (fun v ↦ ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖) μ := by
    simp only [Finset.mem_product, Finset.mem_range_succ_iff] at hp
    exact h'f _ _ (le_trans (by simpa using hp.1) hk) (le_trans (by simpa using hp.2) hn)
  rw [← integral_finsetSum _ I, ← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards with v using norm_nonneg _
  · exact (integrable_finsetSum _ I).const_mul _
  · filter_upwards with v
    apply norm_iteratedFDeriv_fourierPowSMulRight _ hf (mod_cast hn) _
    intro i hi j hj
    apply Finset.single_le_sum (f := fun p ↦ ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖) (a := (j, i))
    · intro i _hi
      positivity
    · simp only [Finset.mem_product, Finset.mem_range_succ_iff]
      exact ⟨hj, hi⟩

/-- One can bound the `k`-th derivative of the Fourier integral of `f`, multiplied by `(L v w) ^ n`,
in terms of integrals of iterated derivatives of `f` (of order up to `n`) multiplied by `‖v‖ ^ i`
(for `i ≤ k`). -/
/-
**VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le** 是 Mathlib 中的一个引
理，位于命名空间 `VectorFourier`。
形式化陈述：pow_mul_norm_iteratedFDeriv_fourierIntegral_le [FiniteDimensional Real V] 
{μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : Nat∞} (hf : ContDiff Real N 
f) (h'f : forall (k n : Nat), k <= K -> n <= N -> Integrable (fun v => ‖v‖ ^ k *
 ‖iteratedFDeriv Real n f v‖) μ) {k n : Nat} (hk : k <= K) (hn : n <= N) (v : V)
 (w : W) : |L v w| ^ n * ‖(iteratedFDeriv Real k (fourierIntegral 𝐞 μ L.toLinear
Map₁₂ f)) w‖ <= ‖v‖ ^ n * (2 * π * ‖L‖) ^ k * (2 * k + 2) ^ n * ∑ p in Finset.ra
nge (k + 1) ×ˢ Finset.rang
参数：hf : ContDiff Real N f；h'f : forall (k n : Nat), k <= K -> n <= N -> Integrab
le (fun v => ‖v‖ ^ k * ‖iteratedFDeriv Real n f v‖) μ；hk : k <= K；hn : n <= N；v 
: V；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `le_mul_of_one_le_left`：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b
) (h : 1 <= a) : b <= a * b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 142 条，此处仅展示前 30 条）

--- 原说明 ---
One can bound the `k`-th derivative of the Fourier integral of `f`, multiplied b
y `(L v w) ^ n`,
in terms of integrals of iterated derivatives of `f` (of order up to `n`) multip
lied by `‖v‖ ^ i`
(for `i ≤ k`).
-/
lemma pow_mul_norm_iteratedFDeriv_fourierIntegral_le [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {K N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (k n : ℕ), k ≤ K → n ≤ N → Integrable (fun v ↦ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) μ)
    {k n : ℕ} (hk : k ≤ K) (hn : n ≤ N) (v : V) (w : W) :
    |L v w| ^ n * ‖(iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w‖ ≤
      ‖v‖ ^ n * (2 * π * ‖L‖) ^ k * (2 * k + 2) ^ n *
        ∑ p ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1),
          ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ ∂μ := calc
  |L v w| ^ n * ‖(iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w‖
  _ ≤ (2 * π) ^ n
      * (|L v w| ^ n * ‖iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f) w‖) := by
    apply le_mul_of_one_le_left (by positivity)
    apply one_le_pow₀
    linarith [one_le_pi_div_two]
  _ = ‖fourierPowSMulRight (-L.flip)
        (iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n (fun _ ↦ v)‖ := by
    simp [norm_smul, abs_of_nonneg pi_nonneg]
  _ ≤ ‖fourierPowSMulRight (-L.flip)
        (iteratedFDeriv ℝ k (fourierIntegral 𝐞 μ L.toLinearMap₁₂ f)) w n‖ * ∏ _ : Fin n, ‖v‖ :=
    le_opNorm _ _
  _ ≤ ((2 * π) ^ k * (2 * k + 2) ^ n * ‖L‖ ^ k *
      ∑ p ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ ∂μ) * ‖v‖ ^ n := by
    gcongr
    · apply norm_fourierPowSMulRight_iteratedFDeriv_fourierIntegral_le _ hf h'f hk hn
    · simp
  _ = ‖v‖ ^ n * (2 * π * ‖L‖) ^ k * (2 * k + 2) ^ n *
        ∑ p ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1),
          ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ ∂μ := by
    simp [mul_pow]
    ring

end VectorFourier

namespace Real
open VectorFourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {f : V → E}

/-- The Fréchet derivative of the Fourier transform of `f` is the Fourier transform of
`fun v ↦ -2 * π * I ⟪v, ⬝⟫ f v`. -/
/-
**Real.hasFDerivAt_fourier** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasFDerivAt_fourier (hf_int : Integrable f) (hvf_int : Integrable (fun v =
> ‖v‖ * ‖f v‖)) (x : V) : HasFDerivAt (𝓕 f) (𝓕 (fourierSMulRight (innerSL Real) 
f) x) x
参数：hf_int : Integrable f；hvf_int : Integrable (fun v => ‖v‖ * ‖f v‖)；x : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorFourier.hasFDerivAt_fourierIntegral`：hasFDerivAt_fourierIntegral [
MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V} (h
f : Integrable f μ) (hf' : Inte…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E

--- 原说明 ---
The Fréchet derivative of the Fourier transform of `f` is the Fourier transform 
of
`fun v ↦ -2 * π * I ⟪v, ⬝⟫ f v`.
-/
theorem hasFDerivAt_fourier
    (hf_int : Integrable f) (hvf_int : Integrable (fun v ↦ ‖v‖ * ‖f v‖)) (x : V) :
    HasFDerivAt (𝓕 f) (𝓕 (fourierSMulRight (innerSL ℝ) f) x) x :=
  VectorFourier.hasFDerivAt_fourierIntegral (innerSL ℝ) hf_int hvf_int x

/-- The Fréchet derivative of the Fourier transform of `f` is the Fourier transform of
`fun v ↦ -2 * π * I ⟪v, ⬝⟫ f v`. -/
/-
**Real.fderiv_fourier** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fderiv_fourier (hf_int : Integrable f) (hvf_int : Integrable (fun v => ‖v‖
 * ‖f v‖)) : fderiv Real (𝓕 f) = 𝓕 (fourierSMulRight (innerSL Real) f)
参数：hf_int : Integrable f；hvf_int : Integrable (fun v => ‖v‖ * ‖f v‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `VectorFourier.fderiv_fourierIntegral`：fderiv_fourierIntegral [Measurable
Space V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure V} (hf : Integr
able f μ) (hf' : Integrabl…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E

--- 原说明 ---
The Fréchet derivative of the Fourier transform of `f` is the Fourier transform 
of
`fun v ↦ -2 * π * I ⟪v, ⬝⟫ f v`.
-/
theorem fderiv_fourier
    (hf_int : Integrable f) (hvf_int : Integrable (fun v ↦ ‖v‖ * ‖f v‖)) :
    fderiv ℝ (𝓕 f) = 𝓕 (fourierSMulRight (innerSL ℝ) f) :=
  VectorFourier.fderiv_fourierIntegral (innerSL ℝ) hf_int hvf_int
/-
**Real.differentiable_fourier** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_fourier (hf_int : Integrable f) (hvf_int : Integrable (fun 
v => ‖v‖ * ‖f v‖)) : Differentiable Real (𝓕 f)
参数：hf_int : Integrable f；hvf_int : Integrable (fun v => ‖v‖ * ‖f v‖)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `VectorFourier.differentiable_fourierIntegral`：differentiable_fourierInte
gral [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {μ : Measure
 V} (hf : Integrable f μ) (hf' : I…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
-/
theorem differentiable_fourier
    (hf_int : Integrable f) (hvf_int : Integrable (fun v ↦ ‖v‖ * ‖f v‖)) :
    Differentiable ℝ (𝓕 f) :=
  VectorFourier.differentiable_fourierIntegral (innerSL ℝ) hf_int hvf_int

/-- The Fourier integral of the Fréchet derivative of a function is obtained by multiplying the
Fourier integral of the original function by `2πI ⟪v, w⟫`. -/
/-
**Real.fourier_fderiv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_fderiv (hf : Integrable f) (h'f : Differentiable Real f) (hf' : In
tegrable (fderiv Real f)) : 𝓕 (fderiv Real f) = fourierSMulRight (-innerSL Real)
 (𝓕 f)
参数：hf : Integrable f；h'f : Differentiable Real f；hf' : Integrable (fderiv Real f
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `instCStarRingReal`：CStarRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `flip_innerSL_real`：∀ (F : Type u_3) [inst : SeminormedAddCommGroup F] [i
nst_1 : InnerProductSpace ℝ F], (innerSL ℝ).flip = innerSL ℝ
· 使用定理 `VectorFourier.fourierIntegral_fderiv`：fourierIntegral_fderiv [Measurable
Space V] [BorelSpace V] [FiniteDimensional Real V] {μ : Measure V} [Measure.IsAd
dHaarMeasure μ] (hf : Inte…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…

--- 原说明 ---
The Fourier integral of the Fréchet derivative of a function is obtained by mult
iplying the
Fourier integral of the original function by `2πI ⟪v, w⟫`.
-/
theorem fourier_fderiv
    (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (fderiv ℝ f)) :
    𝓕 (fderiv ℝ f) = fourierSMulRight (-innerSL ℝ) (𝓕 f) := by
  rw [← flip_innerSL_real V]
  exact VectorFourier.fourierIntegral_fderiv (innerSL ℝ) hf h'f hf'

/-- If `‖v‖^n * ‖f v‖` is integrable, then the Fourier transform of `f` is `C^n`. -/
/-
**Real.contDiff_fourier** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiff_fourier {N : Nat∞} (hf : forall (n : Nat), n <= N -> Integrable (
fun v => ‖v‖ ^ n * ‖f v‖)) : ContDiff Real N (𝓕 f)
参数：hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorFourier.contDiff_fourierIntegral`：contDiff_fourierIntegral {N : Na
t∞} (hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ) :
 ContDiff Real N (fourierInt…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E

--- 原说明 ---
If `‖v‖^n * ‖f v‖` is integrable, then the Fourier transform of `f` is `C^n`.
-/
theorem contDiff_fourier {N : ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖)) :
    ContDiff ℝ N (𝓕 f) :=
  VectorFourier.contDiff_fourierIntegral (innerSL ℝ) hf

/-- If `‖v‖^n * ‖f v‖` is integrable, then the `n`-th derivative of the Fourier transform of `f` is
  the Fourier transform of `fun v ↦ (-2 * π * I) ^ n ⟪v, ⬝⟫^n f v`. -/
/-
**Real.iteratedFDeriv_fourier** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedFDeriv_fourier {N : Nat∞} (hf : forall (n : Nat), n <= N -> Integr
able (fun v => ‖v‖ ^ n * ‖f v‖)) (h'f : AEStronglyMeasurable f) {n : Nat} (hn : 
n <= N) : iteratedFDeriv Real n (𝓕 f) = 𝓕 (fun v => fourierPowSMulRight (innerSL
 Real) f v n)
参数：hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖)；h'f : 
AEStronglyMeasurable f；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `VectorFourier.iteratedFDeriv_fourierIntegral`：iteratedFDeriv_fourierInte
gral {N : Nat∞} (hf : forall (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n *
 ‖f v‖) μ) (h'f : AEStronglyMeasur…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E

--- 原说明 ---
If `‖v‖^n * ‖f v‖` is integrable, then the `n`-th derivative of the Fourier tran
sform of `f` is
  the Fourier transform of `fun v ↦ (-2 * π * I) ^ n ⟪v, ⬝⟫^n f v`.
-/
theorem iteratedFDeriv_fourier {N : ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖))
    (h'f : AEStronglyMeasurable f) {n : ℕ} (hn : n ≤ N) :
    iteratedFDeriv ℝ n (𝓕 f) = 𝓕 (fun v ↦ fourierPowSMulRight (innerSL ℝ) f v n) :=
  VectorFourier.iteratedFDeriv_fourierIntegral (innerSL ℝ) hf h'f hn

/-- The Fourier integral of the `n`-th derivative of a function is obtained by multiplying the
Fourier integral of the original function by `(2πI L w ⬝ )^n`. -/
/-
**Real.fourier_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_iteratedFDeriv {N : Nat∞} (hf : ContDiff Real N f) (h'f : forall (
n : Nat), n <= N -> Integrable (iteratedFDeriv Real n f)) {n : Nat} (hn : n <= N
) : 𝓕 (iteratedFDeriv Real n f) = (fun w => fourierPowSMulRight (-innerSL Real) 
(𝓕 f) w n)
参数：hf : ContDiff Real N f；h'f : forall (n : Nat), n <= N -> Integrable (iterated
FDeriv Real n f)；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `instCStarRingReal`：CStarRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `flip_innerSL_real`：∀ (F : Type u_3) [inst : SeminormedAddCommGroup F] [i
nst_1 : InnerProductSpace ℝ F], (innerSL ℝ).flip = innerSL ℝ
· 使用定理 `VectorFourier.fourierIntegral_iteratedFDeriv`：fourierIntegral_iteratedFD
eriv [FiniteDimensional Real V] {μ : Measure V} [Measure.IsAddHaarMeasure μ] {N 
: Nat∞} (hf : ContDiff Real N f) (…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…

--- 原说明 ---
The Fourier integral of the `n`-th derivative of a function is obtained by multi
plying the
Fourier integral of the original function by `(2πI L w ⬝ )^n`.
-/
theorem fourier_iteratedFDeriv {N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (n : ℕ), n ≤ N → Integrable (iteratedFDeriv ℝ n f)) {n : ℕ} (hn : n ≤ N) :
    𝓕 (iteratedFDeriv ℝ n f)
      = (fun w ↦ fourierPowSMulRight (-innerSL ℝ) (𝓕 f) w n) := by
  rw [← flip_innerSL_real V]
  exact VectorFourier.fourierIntegral_iteratedFDeriv (innerSL ℝ) hf h'f hn

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in -- simp followed by positivity
/-- One can bound `‖w‖^n * ‖D^k (𝓕 f) w‖` in terms of integrals of the derivatives of `f` (or order
at most `n`) multiplied by powers of `v` (of order at most `k`). -/
/-
**Real.pow_mul_norm_iteratedFDeriv_fourier_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：pow_mul_norm_iteratedFDeriv_fourier_le {K N : Nat∞} (hf : ContDiff Real N 
f) (h'f : forall (k n : Nat), k <= K -> n <= N -> Integrable (fun v => ‖v‖ ^ k *
 ‖iteratedFDeriv Real n f v‖)) {k n : Nat} (hk : k <= K) (hn : n <= N) (w : V) :
 ‖w‖ ^ n * ‖iteratedFDeriv Real k (𝓕 f) w‖ <= (2 * π) ^ k * (2 * k + 2) ^ n * ∑ 
p in Finset.range (k + 1) ×ˢ Finset.range (n + 1), ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDe
riv Real p.2 f v‖
参数：hf : ContDiff Real N f；h'f : forall (k n : Nat), k <= K -> n <= N -> Integrab
le (fun v => ‖v‖ ^ k * ‖iteratedFDeriv Real n f v‖)；hk : k <= K；hn : n <= N；w : 
V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le`：pow_mul_no
rm_iteratedFDeriv_fourierIntegral_le [FiniteDimensional Real V] {μ : Measure V} 
[Measure.IsAddHaarMeasure μ] {K N : Nat∞} (hf : Co…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `innerSL_apply_apply`：innerSL_apply_apply (v w : E) : innerSL 𝕜 v w = ⟪v,
 w⟫
· 使用定理 `real_inner_self_eq_norm_sq`：real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_
Real = ‖x‖ ^ 2
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
One can bound `‖w‖^n * ‖D^k (𝓕 f) w‖` in terms of integrals of the derivatives o
f `f` (or order
at most `n`) multiplied by powers of `v` (of order at most `k`).
-/
lemma pow_mul_norm_iteratedFDeriv_fourier_le
    {K N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (k n : ℕ), k ≤ K → n ≤ N → Integrable (fun v ↦ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖))
    {k n : ℕ} (hk : k ≤ K) (hn : n ≤ N) (w : V) :
    ‖w‖ ^ n * ‖iteratedFDeriv ℝ k (𝓕 f) w‖ ≤ (2 * π) ^ k * (2 * k + 2) ^ n *
      ∑ p ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1),
        ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ := by
  have Z : ‖w‖ ^ n * (‖w‖ ^ n * ‖iteratedFDeriv ℝ k (𝓕 f) w‖) ≤
      ‖w‖ ^ n * ((2 * (π * ‖innerSL (E := V) ℝ‖)) ^ k * ((2 * k + 2) ^ n *
          ∑ p ∈ Finset.range (k + 1) ×ˢ Finset.range (n + 1),
            ∫ (v : V), ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f v‖ ∂volume)) := by
    have := VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (innerSL ℝ) hf h'f hk hn
      w w
    simp only [innerSL_apply_apply _ w w, real_inner_self_eq_norm_sq w, abs_pow, abs_norm,
      mul_assoc] at this
    rwa [pow_two, mul_pow, mul_assoc] at this
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [pow_zero, one_mul, mul_one, zero_add, Finset.range_one, Finset.product_singleton,
      Finset.sum_map, Function.Embedding.coeFn_mk, norm_iteratedFDeriv_zero] at Z ⊢
    apply Z.trans
    conv_rhs => rw [← mul_one π]
    gcongr
    exact norm_innerSL_le _
  rcases eq_or_ne w 0 with rfl | hw
  · simp [hn]
    positivity
  rw [mul_le_mul_iff_right₀ (pow_pos (by simp [hw]) n)] at Z
  apply Z.trans
  conv_rhs => rw [← mul_one π]
  simp only [mul_assoc]
  gcongr
  exact norm_innerSL_le _
/-
**Real.hasDerivAt_fourier** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_fourier {f : Real -> E} (hf : Integrable f) (hf' : Integrable (
fun x : Real => x • f x)) (w : Real) : HasDerivAt (𝓕 f) (𝓕 (fun x : Real => (-2 
* π * I * x) • f x) w) w
参数：hf : Integrable f；hf' : Integrable (fun x : Real => x • f x)；w : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousLinearMap.ext_ring`：ext_ring [TopologicalSpace R₁] {f g : R₁ -
>L[R₁] M₁} (h : f 1 = g 1) : f = g
· 使用定理 `ContinuousLinearMap.smulRight_apply`：smulRight_apply {c : M₁ ->L[R] S} {
f : M₂} {x : M₁} : (smulRight c f : M₁ -> M₂) x = c x • f
· 使用定理 `ContinuousLinearMap.flip_apply`：flip_apply (f : E ->SL[σ₁₃] F ->SL[σ₂₃] 
G) (x : E) (y : F) : f.flip y x = f x y
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousLinearMap.mul_apply'`：mul_apply' (x y : R) : mul 𝕜 R x y = x *
 y
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
（共 60 条，此处仅展示前 30 条）
-/
lemma hasDerivAt_fourier
    {f : ℝ → E} (hf : Integrable f) (hf' : Integrable (fun x : ℝ ↦ x • f x)) (w : ℝ) :
    HasDerivAt (𝓕 f) (𝓕 (fun x : ℝ ↦ (-2 * π * I * x) • f x) w) w := by
  have hf'' : Integrable (fun v : ℝ ↦ ‖v‖ * ‖f v‖) := by simpa only [norm_smul] using! hf'.norm
  let L := ContinuousLinearMap.mul ℝ ℝ |>.flip
  have h_int : Integrable fun v ↦ fourierSMulRight L f v := by
    suffices Integrable fun v ↦ ContinuousLinearMap.smulRight (L v) (f v) by
      simpa only [fourierSMulRight, neg_smul, neg_mul, Pi.smul_apply] using! this.smul (-2 * π * I)
    convert! ((ContinuousLinearMap.toSpanSingletonLIE ℝ
      E).toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hf' using 2 with _ v
    apply ContinuousLinearMap.ext_ring
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply', one_mul, map_smul]
    exact congr_arg (fun x ↦ v • x) (one_smul ℝ (f v)).symm
  convert! (VectorFourier.hasFDerivAt_fourierIntegral L hf hf'' w).hasDerivAt using 1
  rw [fourierIntegral_continuousLinearMap_apply' h_int, VectorFourier.fourierIntegral,
    fourier_real_eq]
  simp [fourierSMulRight, L, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply', ← neg_mul, mul_smul]
/-
**Real.deriv_fourier** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_fourier {f : Real -> E} (hf : Integrable f) (hf' : Integrable (fun x
 : Real => x • f x)) : deriv (𝓕 f) = 𝓕 (fun x : Real => (-2 * π * I * x) • f x)
参数：hf : Integrable f；hf' : Integrable (fun x : Real => x • f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `Real.hasDerivAt_fourier`：hasDerivAt_fourier {f : Real -> E} (hf : Integr
able f) (hf' : Integrable (fun x : Real => x • f x)) (w : Real) : HasDerivAt (𝓕 
f) (𝓕 (fun x …
-/
theorem deriv_fourier
    {f : ℝ → E} (hf : Integrable f) (hf' : Integrable (fun x : ℝ ↦ x • f x)) :
    deriv (𝓕 f) = 𝓕 (fun x : ℝ ↦ (-2 * π * I * x) • f x) := by
  ext x
  exact (hasDerivAt_fourier hf hf' x).deriv

set_option backward.isDefEq.respectTransparency false in
/-- The Fourier integral of the Fréchet derivative of a function is obtained by multiplying the
Fourier integral of the original function by `2πI x`. -/
/-
**Real.fourier_deriv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_deriv {f : Real -> E} (hf : Integrable f) (h'f : Differentiable Re
al f) (hf' : Integrable (deriv f)) : 𝓕 (deriv f) = fun (x : Real) => (2 * π * I 
* x) • (𝓕 f x)
参数：hf : Integrable f；h'f : Differentiable Real f；hf' : Integrable (deriv f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.fourier_continuousLinearMap_apply`：fourier_continuousLinearMap_appl
y {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] {f : V -> (F ->L[Real]
 E)} {a : F} {v : V} (hf : I…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Real.fourier_fderiv`：fourier_fderiv (hf : Integrable f) (h'f : Different
iable Real f) (hf' : Integrable (fderiv Real f)) : 𝓕 (fderiv Real f) = fourierSM
ulRight (…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `innerSL_apply_apply`：innerSL_apply_apply (v w : E) : innerSL 𝕜 v w = ⟪v,
 w⟫
· 使用定理 `RCLike.inner_apply'`：RCLike.inner_apply' (x y : 𝕜) : ⟪x, y⟫ = conj x * y
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The Fourier integral of the Fréchet derivative of a function is obtained by mult
iplying the
Fourier integral of the original function by `2πI x`.
-/
theorem fourier_deriv
    {f : ℝ → E} (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f)) :
    𝓕 (deriv f) = fun (x : ℝ) ↦ (2 * π * I * x) • (𝓕 f x) := by
  ext x
  have I : Integrable (fun x ↦ fderiv ℝ f x) := by
    simpa only [← toSpanSingleton_deriv] using!
      (ContinuousLinearMap.smulRightL ℝ ℝ E 1).integrable_comp hf'
  have : 𝓕 (deriv f) x = 𝓕 (fderiv ℝ f) x 1 := by
    simp only [fourier_continuousLinearMap_apply I, fderiv_apply_one_eq_deriv]
  rw [this, fourier_fderiv hf h'f I]
  simp only [fourierSMulRight_apply, neg_apply, innerSL_apply_apply ℝ, smul_smul,
    RCLike.inner_apply', conj_trivial, mul_one, neg_smul, smul_neg, neg_neg, neg_mul, ← coe_smul]

set_option backward.isDefEq.respectTransparency false in
/-
**Real.iteratedDeriv_fourier** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iteratedDeriv_fourier {f : Real -> E} {N : Nat∞} {n : Nat} (hf : forall (n
 : Nat), n <= N -> Integrable (fun x => x ^ n • f x)) (hn : n <= N) : iteratedDe
riv n (𝓕 f) = 𝓕 (fun x : Real => (-2 * π * I * x) ^ n • f x)
参数：hf : forall (n : Nat), n <= N -> Integrable (fun x => x ^ n • f x)；hn : n <= 
N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `iteratedDeriv.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] (n :
 ℕ) (f :…
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Real.iteratedFDeriv_fourier`：iteratedFDeriv_fourier {N : Nat∞} (hf : for
all (n : Nat), n <= N -> Integrable (fun v => ‖v‖ ^ n * ‖f v‖)) (h'f : AEStrongl
yMeasurable f) {n…
· 使用定理 `Real.fourier_continuousMultilinearMap_apply`：fourier_continuousMultiline
arMap_apply {ι : Type*} [Fintype ι] {M : ι -> Type*} [forall i, NormedAddCommGro
up (M i)] [forall i, NormedSpace …
· 使用引理 `VectorFourier.integrable_fourierPowSMulRight`：integrable_fourierPowSMulR
ight {n : Nat} (hf : Integrable (fun v => ‖v‖ ^ n * ‖f v‖) μ) (h'f : AEStronglyM
easurable f μ) : Integrable (fun v…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `Real.fourier_eq`：fourier_eq (f : V -> E) (w : V) : 𝓕 f w = ∫ v, 𝐞 (-⟪v, 
w⟫) • f v
（共 54 条，此处仅展示前 30 条）
-/
theorem iteratedDeriv_fourier {f : ℝ → E} {N : ℕ∞} {n : ℕ}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun x ↦ x ^ n • f x)) (hn : n ≤ N) :
    iteratedDeriv n (𝓕 f) = 𝓕 (fun x : ℝ ↦ (-2 * π * I * x) ^ n • f x) := by
  ext x : 1
  have A (n : ℕ) (hn : n ≤ N) : Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖) := by
    convert! (hf n hn).norm with x
    simp [norm_smul]
  have B : AEStronglyMeasurable f := by simpa using (hf 0 zero_le).1
  rw [iteratedDeriv, iteratedFDeriv_fourier A B hn,
    fourier_continuousMultilinearMap_apply (integrable_fourierPowSMulRight _ (A n hn) B),
    fourier_eq, fourier_eq]
  congr with y
  suffices (-(2 * π * I)) ^ n • y ^ n • f y = (-(2 * π * I * y)) ^ n • f y by
    simpa [innerSL_apply_apply _]
  simp only [← neg_mul, ← coe_smul, smul_smul, mul_pow, ofReal_pow, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-
**Real.fourier_iteratedDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_iteratedDeriv {f : Real -> E} {N : Nat∞} {n : Nat} (hf : ContDiff 
Real N f) (h'f : forall (n : Nat), n <= N -> Integrable (iteratedDeriv n f)) (hn
 : n <= N) : 𝓕 (iteratedDeriv n f) = fun (x : Real) => (2 * π * I * x) ^ n • (𝓕 
f x)
参数：hf : ContDiff Real N f；h'f : forall (n : Nat), n <= N -> Integrable (iterated
Deriv n f)；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedFDeriv_eq_equiv_comp`：iteratedFDeriv_eq_equiv_comp : iteratedFDe
riv 𝕜 n f = ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDeriv n 
f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearIsometryEquiv.integrable_comp_iff`：LinearIsometryEquiv.integrable_
comp_iff {φ : α -> H} (L : H ≃ₛₗᵢ[σ] E) : Integrable (fun a : α => L (φ a)) μ ↔ 
Integrable φ μ
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.fourier_continuousMultilinearMap_apply`：fourier_continuousMultiline
arMap_apply {ι : Type*} [Fintype ι] {M : ι -> Type*} [forall i, NormedAddCommGro
up (M i)] [forall i, NormedSpace …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Real.fourier_iteratedFDeriv`：fourier_iteratedFDeriv {N : Nat∞} (hf : Con
tDiff Real N f) (h'f : forall (n : Nat), n <= N -> Integrable (iteratedFDeriv Re
al n f)) {n : Nat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `VectorFourier.fourierPowSMulRight_apply`：∀ {E : Type u_1} [inst : Normed
AddCommGroup E] [inst_1 : NormedSpace ℂ E] {V : Type u_2} {W : Type u_3}   [inst
_2 : NormedAddCommGroup V] [i…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
（共 44 条，此处仅展示前 30 条）
-/
theorem fourier_iteratedDeriv {f : ℝ → E} {N : ℕ∞} {n : ℕ} (hf : ContDiff ℝ N f)
    (h'f : ∀ (n : ℕ), n ≤ N → Integrable (iteratedDeriv n f)) (hn : n ≤ N) :
    𝓕 (iteratedDeriv n f) = fun (x : ℝ) ↦ (2 * π * I * x) ^ n • (𝓕 f x) := by
  ext x : 1
  have A : ∀ (n : ℕ), n ≤ N → Integrable (iteratedFDeriv ℝ n f) := by
    intro n hn
    rw [iteratedFDeriv_eq_equiv_comp]
    exact (LinearIsometryEquiv.integrable_comp_iff _).2 (h'f n hn)
  change 𝓕 (fun x ↦ iteratedDeriv n f x) x = _
  simp_rw [iteratedDeriv, ← fourier_continuousMultilinearMap_apply (A n hn),
    fourier_iteratedFDeriv hf A hn]
  simp [← coe_smul, smul_smul, ← mul_pow, innerSL_apply_apply ℝ]

end Real

