/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!

# Fourier analysis on the additive circle

This file contains basic results on Fourier series for functions on the additive circle
`AddCircle T = ℝ / ℤ • T`.

## Main definitions

* `haarAddCircle`, Haar measure on `AddCircle T`, normalized to have total measure `1`.
  Note that this is not the same normalisation
  as the standard measure defined in `IntervalIntegral.Periodic`,
  so we do not declare it as a `MeasureSpace` instance, to avoid confusion.
* for `n : ℤ`, `fourier n` is the monomial `fun x => exp (2 π i n x / T)`,
  bundled as a continuous map from `AddCircle T` to `ℂ`.
* `fourierBasis` is the Hilbert basis of `Lp ℂ 2 haarAddCircle` given by the images of the
  monomials `fourier n`.
* `fourierCoeff f n`, for `f : AddCircle T → E` (with `E` a complete normed `ℂ`-vector space), is
  the `n`-th Fourier coefficient of `f`, defined as an integral over `AddCircle T`. The lemma
  `fourierCoeff_eq_intervalIntegral` expresses this as an integral over `[a, a + T]` for any real
  `a`.
* `fourierCoeffOn`, for `f : ℝ → E` and `a < b` reals, is the `n`-th Fourier
  coefficient of the unique periodic function of period `b - a` which agrees with `f` on `(a, b]`.
  The lemma `fourierCoeffOn_eq_integral` expresses this as an integral over `[a, b]`.

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(AddCircle T, ℂ)`, i.e. that its `Submodule.topologicalClosure` is `⊤`.  This follows
from the Stone-Weierstrass theorem after checking that the span is a subalgebra, is closed under
conjugation, and separates points.

Using this and general theory on approximation of Lᵖ functions by continuous functions, we deduce
(`span_fourierLp_closure_eq_top`) that for any `1 ≤ p < ∞`, the span of the Fourier monomials is
dense in the Lᵖ space of `AddCircle T`. For `p = 2` we show (`orthonormal_fourier`) that the
monomials are also orthonormal, so they form a Hilbert basis for L², which is named as
`fourierBasis`; in particular, for `L²` functions `f`, the Fourier series of `f` converges to `f`
in the `L²` topology (`hasSum_fourier_series_L2`). Parseval's identity, `hasSum_sq_fourierCoeff`, is
a direct consequence.

For continuous maps `f : AddCircle T → ℂ`, the theorem
`hasSum_fourier_series_of_summable` states that if the sequence of Fourier
coefficients of `f` is summable, then the Fourier series `∑ (i : ℤ), fourierCoeff f i * fourier i`
converges to `f` in the uniform-convergence topology of `C(AddCircle T, ℂ)`.
-/

@[expose] public section


noncomputable section

open scoped ENNReal ComplexConjugate Real

open TopologicalSpace ContinuousMap MeasureTheory MeasureTheory.Measure Algebra Submodule Set

variable {T : ℝ}

namespace AddCircle

/-! ### Measure on `AddCircle T`

In this file we use the Haar measure on `AddCircle T` normalised to have total measure 1 (which is
**not** the same as the standard measure defined in `Topology.Instances.AddCircle`). -/

variable [hT : Fact (0 < T)]

/-- Haar measure on the additive circle, normalised to have total measure 1. -/
/-
**AddCircle.haarAddCircle** 是 Mathlib 中的一个定义，位于命名空间 `AddCircle`。
形式化陈述：haarAddCircle : Measure (AddCircle T)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Haar measure on the additive circle, normalised to have total measure 1.
-/
def haarAddCircle : Measure (AddCircle T) :=
  addHaarMeasure ⊤
deriving IsAddHaarMeasure
/-
**AddCircle.** 是 Mathlib 中的一个实例，位于命名空间 `AddCircle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsProbabilityMeasure (@haarAddCircle T _) :=
  IsProbabilityMeasure.mk addHaarMeasure_self
/-
**AddCircle.volume_eq_smul_haarAddCircle** 是 Mathlib 中的一个定理，位于命名空间 `AddCircle`。
形式化陈述：volume_eq_smul_haarAddCircle : (volume : Measure (AddCircle T)) = ENNReal.
ofReal T • (@haarAddCircle T _)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem volume_eq_smul_haarAddCircle :
    (volume : Measure (AddCircle T)) = ENNReal.ofReal T • (@haarAddCircle T _) :=
  rfl
/-
**AddCircle.integral_haarAddCircle** 是 Mathlib 中的一个引理，位于命名空间 `AddCircle`。
形式化陈述：integral_haarAddCircle {E : Type*} [NormedAddCommGroup E] [NormedSpace Rea
l E] {f : AddCircle T -> E} : ∫ t, f t ∂haarAddCircle = T⁻¹ • ∫ t, f t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.volume_eq_smul_haarAddCircle`：volume_eq_smul_haarAddCircle : (
volume : Measure (AddCircle T)) = ENNReal.ofReal T • (@haarAddCircle T _)
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma integral_haarAddCircle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AddCircle T → E} : ∫ t, f t ∂haarAddCircle = T⁻¹ • ∫ t, f t := by
  rw [volume_eq_smul_haarAddCircle, integral_smul_measure, ENNReal.toReal_ofReal hT.out.le,
    inv_smul_smul₀ hT.out.ne']

end AddCircle

namespace MeasureTheory

/-
**MeasureTheory.memLp_haarAddCircle_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：memLp_haarAddCircle_iff [hT : Fact (0 < T)] {f : AddCircle T -> Complex} {
p : Real>=0∞} : MemLp f p AddCircle.haarAddCircle ↔ MemLp f p
参数：0 < T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.volume_eq_smul_haarAddCircle`：volume_eq_smul_haarAddCircle : (
volume : Measure (AddCircle T)) = ENNReal.ofReal T • (@haarAddCircle T _)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `MeasureTheory.MemLp.smul_measure`：∀ {α : Type u_1} {m0 : MeasurableSpace
 α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topolog
icalSpace ε] [inst_1 :…
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `ENNReal.Finiteness.inv_ne_top`：∀ {a : ENNReal}, a ≠ 0 → a⁻¹ ≠ ⊤
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
lemma memLp_haarAddCircle_iff [hT : Fact (0 < T)] {f : AddCircle T → ℂ} {p : ℝ≥0∞} :
    MemLp f p AddCircle.haarAddCircle ↔ MemLp f p := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  have hT' := hT.out
  refine ⟨fun h ↦ h.smul_measure (by finiteness), fun h ↦ ?_⟩
  have := h.smul_measure (c := (ENNReal.ofReal T)⁻¹) (by finiteness)
  rwa [smul_smul, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_smul] at this

alias ⟨MemLp.of_haarAddCircle, MemLp.haarAddCircle⟩ := memLp_haarAddCircle_iff

end MeasureTheory

open AddCircle

section Monomials

/-- The family of exponential monomials `fun x => exp (2 π i n x / T)`, parametrized by `n : ℤ` and
considered as bundled continuous maps from `ℝ / ℤ • T` to `ℂ`. -/
/-
**fourier** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fourier (n : Int) : C(AddCircle T, Complex) where toFun x
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of exponential monomials `fun x => exp (2 π i n x / T)`, parametrized
 by `n : ℤ` and
considered as bundled continuous maps from `ℝ / ℤ • T` to `ℂ`.
-/
def fourier (n : ℤ) : C(AddCircle T, ℂ) where
  toFun x := toCircle (n • x :)
  continuous_toFun := continuous_induced_dom.comp <| continuous_toCircle.comp <| continuous_zsmul _

@[simp]
/-
**fourier_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_apply {n : Int} {x : AddCircle T} : fourier n x = toCircle (n • x 
:)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fourier_apply {n : ℤ} {x : AddCircle T} : fourier n x = toCircle (n • x :) :=
  rfl

-- simp normal form is `fourier_coe_apply'`
/-
**fourier_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_coe_apply {n : Int} {x : Real} : fourier n (x : AddCircle T) = Com
plex.exp (2 * π * Complex.I * n * x / T)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fourier_apply`：fourier_apply {n : Int} {x : AddCircle T} : fourier n x =
 toCircle (n • x :)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientAddGroup.mk_zsmul`：∀ {G : Type u_1} [inst : AddGroup G] (N : Add
Subgroup G) [nN : N.Normal] (a : G) (n : ℤ), ↑(n • a) = n • ↑a
· 使用定理 `AddCircle.scaled_exp_map_periodic`：scaled_exp_map_periodic : Function.Pe
riodic (fun x => Circle.exp (2 * π / T * x)) T
· 使用定理 `AddCircle.toCircle.eq_1`：∀ {T : ℝ}, AddCircle.toCircle = ⋯.lift
· 使用定理 `Function.Periodic.lift_coe`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{c : α} [inst : AddGroup α] (h : Function.Periodic f c) (a : α),   h.lift ↑a = f
 a
· 使用定理 `Circle.coe_exp`：coe_exp (t : Real) : exp t = Complex.exp (t * Complex.I)
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `Complex.ofReal_intCast`：∀ (n : ℤ), ↑↑n = ↑n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 39 条，此处仅展示前 30 条）
-/
theorem fourier_coe_apply {n : ℤ} {x : ℝ} :
    fourier n (x : AddCircle T) = Complex.exp (2 * π * Complex.I * n * x / T) := by
  rw [fourier_apply, ← QuotientAddGroup.mk_zsmul, toCircle, Function.Periodic.lift_coe,
    Circle.coe_exp, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul, zsmul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  norm_num
  congr 1; ring

@[simp]
/-
**fourier_coe_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_coe_apply' {n : Int} {x : Real} : toCircle (n • (x : AddCircle T) 
:) = Complex.exp (2 * π * Complex.I * n * x / T)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fourier_apply`：fourier_apply {n : Int} {x : AddCircle T} : fourier n x =
 toCircle (n • x :)
· 使用定理 `fourier_coe_apply`：fourier_coe_apply {n : Int} {x : Real} : fourier n (x
 : AddCircle T) = Complex.exp (2 * π * Complex.I * n * x / T)
-/
theorem fourier_coe_apply' {n : ℤ} {x : ℝ} :
    toCircle (n • (x : AddCircle T) :) = Complex.exp (2 * π * Complex.I * n * x / T) := by
  rw [← fourier_apply]; exact fourier_coe_apply

-- simp normal form is `fourier_zero'`
/-
**fourier_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_zero {x : AddCircle T} : fourier 0 x = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `AddCircle.toCircle_zero`：∀ {T : ℝ}, AddCircle.toCircle 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourier_zero {x : AddCircle T} : fourier 0 x = 1 := by
  simp
/-
**fourier_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_zero' : @toCircle T 0 = (1 : Complex)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCircle.toCircle_zero`：∀ {T : ℝ}, AddCircle.toCircle 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourier_zero' : @toCircle T 0 = (1 : ℂ) := by
  simp

-- simp normal form is *also* `fourier_zero'`
/-
**fourier_eval_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_eval_zero (n : Int) : fourier n (0 : AddCircle T) = 1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientAddGroup.mk_zero`：∀ {G : Type u_1} [inst : AddGroup G] (N : AddS
ubgroup G) [nN : N.Normal], ↑0 = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fourier_coe_apply`：fourier_coe_apply {n : Int} {x : Real} : fourier n (x
 : AddCircle T) = Complex.exp (2 * π * Complex.I * n * x / T)
· 使用定理 `Complex.ofReal_zero`：ofReal_zero : ((0 : Real) : Complex) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
-/
theorem fourier_eval_zero (n : ℤ) : fourier n (0 : AddCircle T) = 1 := by
  rw [← QuotientAddGroup.mk_zero, fourier_coe_apply, Complex.ofReal_zero, mul_zero,
    zero_div, Complex.exp_zero]
/-
**fourier_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_one {x : AddCircle T} : fourier 1 x = toCircle x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fourier_apply`：fourier_apply {n : Int} {x : AddCircle T} : fourier n x =
 toCircle (n • x :)
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
-/
theorem fourier_one {x : AddCircle T} : fourier 1 x = toCircle x := by rw [fourier_apply, one_zsmul]

-- simp normal form is `fourier_neg'`
/-
**fourier_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_neg {n : Int} {x : AddCircle T} : fourier (-n) x = conj (fourier n
 x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.induction_on`：∀ {α : Type u_1} [inst : AddGroup α] {s :
 AddSubgroup α} {C : α ⧸ s → Prop} (x : α ⧸ s), (∀ (z : α), C ↑z) → C x
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddCircle.scaled_exp_map_periodic`：scaled_exp_map_periodic : Function.Pe
riodic (fun x => Circle.exp (2 * π / T * x)) T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientAddGroup.mk_zsmul`：∀ {G : Type u_1} [inst : AddGroup G] (N : Add
Subgroup G) [nN : N.Normal] (a : G) (n : ℤ), ↑(n • a) = n • ↑a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourier_neg {n : ℤ} {x : AddCircle T} : fourier (-n) x = conj (fourier n x) := by
  induction x using QuotientAddGroup.induction_on
  simp_rw [fourier_apply, toCircle]
  rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_zsmul]
  simp_rw [Function.Periodic.lift_coe, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg,
    neg_smul, mul_neg]

@[simp]
/-
**fourier_neg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_neg' {n : Int} {x : AddCircle T} : @toCircle T (-(n • x)) = conj (
fourier n x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `fourier_apply`：fourier_apply {n : Int} {x : AddCircle T} : fourier n x =
 toCircle (n • x :)
· 使用定理 `fourier_neg`：fourier_neg {n : Int} {x : AddCircle T} : fourier (-n) x = 
conj (fourier n x)
-/
theorem fourier_neg' {n : ℤ} {x : AddCircle T} : @toCircle T (-(n • x)) = conj (fourier n x) := by
  rw [← neg_smul, ← fourier_apply]; exact fourier_neg

-- simp normal form is `fourier_add'`
/-
**fourier_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_add {m n : Int} {x : AddCircle T} : fourier (m + n) x = fourier m 
x * fourier n x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (m n : ℤ), (m + 
n) • a = m • a + n • a
· 使用定理 `AddCircle.toCircle_add`：toCircle_add (x y : AddCircle T) : toCircle (x +
 y) = toCircle x * toCircle y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourier_add {m n : ℤ} {x : AddCircle T} :
    fourier (m + n) x = fourier m x * fourier n x := by
  simp_rw [fourier_apply, add_zsmul, toCircle_add, Circle.coe_mul]

@[simp]
/-
**fourier_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_add' {m n : Int} {x : AddCircle T} : toCircle ((m + n) • x :) = fo
urier m x * fourier n x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fourier_apply`：fourier_apply {n : Int} {x : AddCircle T} : fourier n x =
 toCircle (n • x :)
· 使用定理 `fourier_add`：fourier_add {m n : Int} {x : AddCircle T} : fourier (m + n)
 x = fourier m x * fourier n x
-/
theorem fourier_add' {m n : ℤ} {x : AddCircle T} :
    toCircle ((m + n) • x :) = fourier m x * fourier n x := by
  rw [← fourier_apply]; exact fourier_add
/-
**fourier_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_norm [Fact (0 < T)] (n : Int) : ‖@fourier T n‖ = 1
参数：0 < T；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.norm_eq_iSup_norm`：norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x
‖
· 使用引理 `Circle.norm_coe`：norm_coe (z : Circle) : ‖(z : Complex)‖ = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem fourier_norm [Fact (0 < T)] (n : ℤ) : ‖@fourier T n‖ = 1 := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  have : ∀ x : AddCircle T, ‖fourier n x‖ = 1 := fun x => Circle.norm_coe _
  simp_rw [this]
  exact ciSup_const

set_option backward.isDefEq.respectTransparency false in
/-- For `n ≠ 0`, a translation by `T / 2 / n` negates the function `fourier n`. -/
/-
**fourier_add_half_inv_index** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourier_add_half_inv_index {n : Int} (hn : n != 0) (hT : 0 < T) (x : AddCi
rcle T) : @fourier T n (x + ↑(T / 2 / n)) = -fourier n x
参数：hn : n != 0；hT : 0 < T；x : AddCircle T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fourier_apply`：fourier_apply {n : Int} {x : AddCircle T} : fourier n x =
 toCircle (n • x :)
· 使用定理 `zsmul_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α) (
n : ℤ), n • (a + b) = n • a + n • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientAddGroup.mk_zsmul`：∀ {G : Type u_1} [inst : AddGroup G] (N : Add
Subgroup G) [nN : N.Normal] (a : G) (n : ℤ), ↑(n • a) = n • ↑a
· 使用定理 `AddCircle.toCircle_add`：toCircle_add (x y : AddCircle T) : toCircle (x +
 y) = toCircle x * toCircle y
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Metric.unitSphere.coe_mul`：Metric.unitSphere.coe_mul [SeminormedRing 𝕜] 
[NormMulClass 𝕜] [NormOneClass 𝕜] (x y : sphere (0 : 𝕜) 1) : ↑(x * y) = (x * y :
 𝕜)
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `AddCircle.scaled_exp_map_periodic`：scaled_exp_map_periodic : Function.Pe
riodic (fun x => Circle.exp (2 * π / T * x)) T
· 使用定理 `AddCircle.toCircle.eq_1`：∀ {T : ℝ}, AddCircle.toCircle = ⋯.lift
· 使用定理 `Function.Periodic.lift_coe`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{c : α} [inst : AddGroup α] (h : Function.Periodic f c) (a : α),   h.lift ↑a = f
 a
· 使用定理 `Circle.coe_exp`：coe_exp (t : Real) : exp t = Complex.exp (t * Complex.I)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
For `n ≠ 0`, a translation by `T / 2 / n` negates the function `fourier n`.
-/
theorem fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (hT : 0 < T) (x : AddCircle T) :
    @fourier T n (x + ↑(T / 2 / n)) = -fourier n x := by
  rw [fourier_apply, zsmul_add, ← QuotientAddGroup.mk_zsmul, toCircle_add,
    Metric.unitSphere.coe_mul]
  have : (@toCircle T (n • (T / 2 / n) : ℝ) : ℂ) = -1 := by
    rw [zsmul_eq_mul, toCircle, Function.Periodic.lift_coe, Circle.coe_exp]
    convert Complex.exp_pi_mul_I
    field_simp
  rw [this]; simp

/-- The star subalgebra of `C(AddCircle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` . -/
/-
**fourierSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fourierSubalgebra : StarSubalgebra Complex C(AddCircle T, Complex) where t
oSubalgebra
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ

--- 原说明 ---
The star subalgebra of `C(AddCircle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` 
.
-/
def fourierSubalgebra : StarSubalgebra ℂ C(AddCircle T, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range fourier)
  star_mem' := by
    change Algebra.adjoin ℂ (range (fourier (T := T))) ≤
      star (Algebra.adjoin ℂ (range (fourier (T := T))))
    refine adjoin_le ?_
    rintro - ⟨n, rfl⟩
    exact subset_adjoin ⟨-n, ext fun _ => fourier_neg⟩

/-- The star subalgebra of `C(AddCircle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is in fact the
linear span of these functions. -/
/-
**fourierSubalgebra_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierSubalgebra_coe : Subalgebra.toSubmodule (@fourierSubalgebra T).toSu
balgebra = span Complex (range (@fourier T))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_eq_span_of_subset`：adjoin_eq_span_of_subset {s : Set A} (
hs : ↑(Submonoid.closure s) subseteq (span R s : Set A)) : Subalgebra.toSubmodul
e (adjoin R s) = span …
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `fourier_zero`：fourier_zero {x : AddCircle T} : fourier 0 x = 1
· 使用定理 `fourier_add`：fourier_add {m n : Int} {x : AddCircle T} : fourier (m + n)
 x = fourier m x * fourier n x
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s

--- 原说明 ---
The star subalgebra of `C(AddCircle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` 
is in fact the
linear span of these functions.
-/
theorem fourierSubalgebra_coe :
    Subalgebra.toSubmodule (@fourierSubalgebra T).toSubalgebra = span ℂ (range (@fourier T)) := by
  apply adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_ hx
  · ext1 z; exact fourier_zero
  · rintro - - - - ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext1 z
    exact fourier_add

/- a post-port refactor made `fourierSubalgebra` into a `StarSubalgebra`, and eliminated
`conjInvariantSubalgebra` entirely, making this lemma irrelevant. -/

variable [hT : Fact (0 < T)]

set_option backward.isDefEq.respectTransparency.types false in
/-- The subalgebra of `C(AddCircle T, ℂ)` generated by `fourier n` for `n ∈ ℤ`
separates points. -/
/-
**fourierSubalgebra_separatesPoints** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierSubalgebra_separatesPoints : (@fourierSubalgebra T).SeparatesPoints
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fourier_one`：fourier_one {x : AddCircle T} : fourier 1 x = toCircle x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `AddCircle.injective_toCircle`：injective_toCircle (hT : T != 0) : Functio
n.Injective (@toCircle T)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b

--- 原说明 ---
The subalgebra of `C(AddCircle T, ℂ)` generated by `fourier n` for `n ∈ ℤ`
separates points.
-/
theorem fourierSubalgebra_separatesPoints : (@fourierSubalgebra T).SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨fourier 1, subset_adjoin ⟨1, rfl⟩, rfl⟩, ?_⟩
  dsimp only; rw [fourier_one, fourier_one]
  contrapose hxy
  rw [Subtype.coe_inj] at hxy
  exact injective_toCircle hT.elim.ne' hxy

/-- The subalgebra of `C(AddCircle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is dense. -/
/-
**fourierSubalgebra_closure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierSubalgebra_closure_eq_top : (@fourierSubalgebra T).topologicalClosu
re = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoint
s`：ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (A 
: StarSubalgebra 𝕜 C(X, 𝕜)) (hA : A.SeparatesPoints) : A.topolo…
· 使用定理 `fourierSubalgebra_separatesPoints`：fourierSubalgebra_separatesPoints : (
@fourierSubalgebra T).SeparatesPoints

--- 原说明 ---
The subalgebra of `C(AddCircle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is de
nse.
-/
theorem fourierSubalgebra_closure_eq_top : (@fourierSubalgebra T).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints fourierSubalgebra
    fourierSubalgebra_separatesPoints

/-- The linear span of the monomials `fourier n` is dense in `C(AddCircle T, ℂ)`. -/
/-
**span_fourier_closure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：span_fourier_closure_eq_top : (span Complex (range <| @fourier T)).topolog
icalClosure = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMap.instContinuousConstSMul`：∀ {α : Type u_1} [inst : Topologi
calSpace α] {R : Type u_3} {M : Type u_5} [inst_1 : TopologicalSpace M]   [inst_
2 : SMul R M] [inst_3 : Con…
· 使用定理 `ContinuousMap.instContinuousAddOfLocallyCompactSpace`：∀ {α : Type u_1} {
β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Locally
CompactSpace α]   [inst_3 : Add β] [inst_4…
· 使用定理 `QuotientAddGroup.instLocallyCompactSpace`：∀ {G : Type u_1} [inst : Topol
ogicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G] [LocallyCompact
Space G]   (N : AddSubgroup G)…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fourierSubalgebra_coe`：fourierSubalgebra_coe : Subalgebra.toSubmodule (@
fourierSubalgebra T).toSubalgebra = span Complex (range (@fourier T))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ContinuousMap.instIsTopologicalRingOfLocallyCompactSpace`：∀ {α : Type u_
1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [Loc
allyCompactSpace α]   [inst_3 : NonUnitalRing …
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMap.instNormedStarGroup`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace α] [inst_1 : SeminormedAddCommGroup β]   [inst_2 : StarAddMo
noid β] [inst_3 : Norme…
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `fourierSubalgebra_closure_eq_top`：fourierSubalgebra_closure_eq_top : (@f
ourierSubalgebra T).topologicalClosure = ⊤

--- 原说明 ---
The linear span of the monomials `fourier n` is dense in `C(AddCircle T, ℂ)`.
-/
theorem span_fourier_closure_eq_top : (span ℂ (range <| @fourier T)).topologicalClosure = ⊤ := by
  rw [← fourierSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    fourierSubalgebra_closure_eq_top

/-- The family of monomials `fourier n`, parametrized by `n : ℤ` and considered as
elements of the `Lp` space of functions `AddCircle T → ℂ`. -/
/-
**fourierLp** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：fourierLp (p : Real>=0∞) [Fact (1 <= p)] (n : Int) : Lp Complex p (@haarAd
dCircle T hT)
参数：p : Real>=0∞；1 <= p；n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of monomials `fourier n`, parametrized by `n : ℤ` and considered as
elements of the `Lp` space of functions `AddCircle T → ℂ`.
-/
abbrev fourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) : Lp ℂ p (@haarAddCircle T hT) :=
  toLp (E := ℂ) p haarAddCircle ℂ (fourier n)
/-
**coeFn_fourierLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coeFn_fourierLp (p : Real>=0∞) [Fact (1 <= p)] (n : Int) : @fourierLp T hT
 p _ n =ᵐ[haarAddCircle] fourier n
参数：p : Real>=0∞；1 <= p；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.coeFn_toLp`：coeFn_toLp (f : C(α, E)) : toLp (E
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AddCircle.instIsProbabilityMeasureRealHaarAddCircle`：∀ {T : ℝ} [hT : Fac
t (0 < T)], MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle
-/
theorem coeFn_fourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    @fourierLp T hT p _ n =ᵐ[haarAddCircle] fourier n :=
  coeFn_toLp haarAddCircle (fourier n)

/-- For each `1 ≤ p < ∞`, the linear span of the monomials `fourier n` is dense in
`Lp ℂ p haarAddCircle`. -/
/-
**span_fourierLp_closure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：span_fourierLp_closure_eq_top {p : Real>=0∞} [Fact (1 <= p)] (hp : p != ∞)
 : (span Complex (range (@fourierLp T _ p _))).topologicalClosure = ⊤
参数：1 <= p；hp : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AddCircle.instIsProbabilityMeasureRealHaarAddCircle`：∀ {T : ℝ} [hT : Fac
t (0 < T)], MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
For each `1 ≤ p < ∞`, the linear span of the monomials `fourier n` is dense in
`Lp ℂ p haarAddCircle`.
-/
theorem span_fourierLp_closure_eq_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (span ℂ (range (@fourierLp T _ p _))).topologicalClosure = ⊤ := by
  convert!
    (ContinuousMap.toLp_denseRange ℂ (@haarAddCircle T hT) ℂ hp).topologicalClosure_map_submodule
      span_fourier_closure_eq_top
  rw [map_span]
  unfold fourierLp
  rw [range_comp']
  simp only [ContinuousLinearMap.coe_coe]

/-- The monomials `fourier n` are an orthonormal set with respect to normalised Haar measure. -/
/-
**orthonormal_fourier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orthonormal_fourier : Orthonormal Complex (@fourierLp T _ 2 _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AddCircle.instIsProbabilityMeasureRealHaarAddCircle`：∀ {T : ℝ} [hT : Fac
t (0 < T)], MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
The monomials `fourier n` are an orthonormal set with respect to normalised Haar
 measure.
-/
theorem orthonormal_fourier : Orthonormal ℂ (@fourierLp T _ 2 _) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [ContinuousMap.inner_toLp (@haarAddCircle T hT) (fourier i) (fourier j)]
  simp_rw [← fourier_neg, ← fourier_add]
  split_ifs with h
  · simp [h]
  have hij : j + -i ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm h)
  convert!
    integral_eq_zero_of_add_right_eq_neg (μ := haarAddCircle)
      (fourier_add_half_inv_index hij hT.elim)

end Monomials

section ScopeHT

-- everything from here on needs `0 < T`
variable [hT : Fact (0 < T)]

section fourierCoeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `n`-th Fourier coefficient of a function `AddCircle T → E`, for `E` a complete normed
`ℂ`-vector space, defined as the integral over `AddCircle T` of `fourier (-n) t • f t`. -/
/-
**fourierCoeff** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fourierCoeff (f : AddCircle T -> E) (n : Int) : E
参数：f : AddCircle T -> E；n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th Fourier coefficient of a function `AddCircle T → E`, for `E` a comple
te normed
`ℂ`-vector space, defined as the integral over `AddCircle T` of `fourier (-n) t 
• f t`.
-/
def fourierCoeff (f : AddCircle T → E) (n : ℤ) : E :=
  ∫ t : AddCircle T, fourier (-n) t • f t ∂haarAddCircle

/-- The Fourier coefficients of a function on `AddCircle T` can be computed as an integral
over `[a, a + T]`, for any real `a`. -/
/-
**fourierCoeff_eq_intervalIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeff_eq_intervalIntegral (f : AddCircle T -> E) (n : Int) (a : Rea
l) : fourierCoeff f n = (1 / T) • ∫ x in a..a + T, @fourier T (-n) x • f x
参数：f : AddCircle T -> E；n : Int；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `fourierCoeff.eq_1`：∀ {T : ℝ} [hT : Fact (0 < T)] {E : Type u_1} [inst : 
NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E]   (f : AddCircle T → E) (n : ℤ)
, fouri…
· 使用定理 `AddCircle.intervalIntegral_preimage`：∀ (T : ℝ) [hT : Fact (0 < T)] {E : 
Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (t : ℝ)   (f 
: AddCircle T → E), ∫ (a …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AddCircle.volume_eq_smul_haarAddCircle`：volume_eq_smul_haarAddCircle : (
volume : Measure (AddCircle T)) = ENNReal.ofReal T • (@haarAddCircle T _)
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `one_div_mul_cancel`：one_div_mul_cancel (h : a != 0) : 1 / a * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
The Fourier coefficients of a function on `AddCircle T` can be computed as an in
tegral
over `[a, a + T]`, for any real `a`.
-/
theorem fourierCoeff_eq_intervalIntegral (f : AddCircle T → E) (n : ℤ) (a : ℝ) :
    fourierCoeff f n = (1 / T) • ∫ x in a..a + T, @fourier T (-n) x • f x := by
  have : ∀ x : ℝ, @fourier T (-n) x • f x = (fun z : AddCircle T => @fourier T (-n) z • f z) x := by
    intro x; rfl
  simp_rw +singlePass [this]
  rw [fourierCoeff, AddCircle.intervalIntegral_preimage T a (fun z => _ • _),
    volume_eq_smul_haarAddCircle, integral_smul_measure, ENNReal.toReal_ofReal hT.out.le,
    ← smul_assoc, smul_eq_mul, one_div_mul_cancel hT.out.ne', one_smul]
/-
**MeasureTheory.Integrable.fourier_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.Integrable.fourier_smul {f : AddCircle T -> E} (hf : Integra
ble f haarAddCircle) (n : Int) : Integrable (fun t => fourier n t • f t) haarAdd
Circle
参数：hf : Integrable f haarAddCircle；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.bdd_smul`：∀ {α : Type u_1} {β : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]  
 {𝕜 : Type u_8} [inst_1…
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fourier_apply`：fourier_apply {n : Int} {x : AddCircle T} : fourier n x =
 toCircle (n • x :)
· 使用引理 `Circle.norm_coe`：norm_coe (z : Circle) : ‖(z : Complex)‖ = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem MeasureTheory.Integrable.fourier_smul {f : AddCircle T → E}
    (hf : Integrable f haarAddCircle) (n : ℤ) :
    Integrable (fun t ↦ fourier n t • f t) haarAddCircle := by
  apply hf.bdd_smul 1
  · exact (map_continuous (fourier n)).aestronglyMeasurable
  · apply ae_of_all; intro t
    rw [fourier_apply, Circle.norm_coe]
/-
**fourierCoeff.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeff.add {f g : AddCircle T -> E} (hf : Integrable f haarAddCircle
) (hg : Integrable g haarAddCircle) : fourierCoeff (f + g) = fourierCoeff f + fo
urierCoeff g
参数：hf : Integrable f haarAddCircle；hg : Integrable g haarAddCircle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.fourier_smul`：MeasureTheory.Integrable.fourier_
smul {f : AddCircle T -> E} (hf : Integrable f haarAddCircle) (n : Int) : Integr
able (fun t => fourier n t …
-/
theorem fourierCoeff.add {f g : AddCircle T → E} (hf : Integrable f haarAddCircle)
    (hg : Integrable g haarAddCircle) :
    fourierCoeff (f + g) = fourierCoeff f + fourierCoeff g := by
  ext x
  simpa [fourierCoeff, -fourier_apply] using integral_add (hf.fourier_smul _) (hg.fourier_smul _)
/-
**fourierCoeff.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeff.sum {ι : Type*} (s : Finset ι) (f : ι -> AddCircle T -> E) (h
f : forall i in s, Integrable (f i) haarAddCircle) : fourierCoeff (∑ i in s, f i
) = ∑ i in s, fourierCoeff (f i)
参数：s : Finset ι；f : ι -> AddCircle T -> E；hf : forall i in s, Integrable (f i) h
aarAddCircle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `fourier_neg'`：fourier_neg' {n : Int} {x : AddCircle T} : @toCircle T (-(
n • x)) = conj (fourier n x)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `fourierCoeff.add`：fourierCoeff.add {f g : AddCircle T -> E} (hf : Integr
able f haarAddCircle) (hg : Integrable g haarAddCircle) : fourierCoeff (f + g) =
 fouri…
· 使用定理 `MeasureTheory.integrable_finsetSum'`：integrable_finsetSum' {ι} (s : Fins
et ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (
∑ i in s, f i) μ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem fourierCoeff.sum {ι : Type*} (s : Finset ι) (f : ι → AddCircle T → E)
    (hf : ∀ i ∈ s, Integrable (f i) haarAddCircle) :
    fourierCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, fourierCoeff (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext; simp [fourierCoeff]
  | insert a s ha iha =>
      obtain ⟨hf₁, hf₂⟩ := by simpa using hf
      rw [s.sum_insert ha, s.sum_insert ha,
        fourierCoeff.add hf₁ (integrable_finsetSum' s hf₂), iha hf₂]
/-
**fourierCoeff.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeff.const_smul (f : AddCircle T -> E) (c : Complex) (n : Int) : f
ourierCoeff (c • f :) n = c • fourierCoeff f n
参数：f : AddCircle T -> E；c : Complex；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierCoeff.const_smul (f : AddCircle T → E) (c : ℂ) (n : ℤ) :
    fourierCoeff (c • f :) n = c • fourierCoeff f n := by
  simp_rw [fourierCoeff, Pi.smul_apply, ← smul_assoc, smul_eq_mul, mul_comm, ← smul_eq_mul,
    smul_assoc, integral_smul]
/-
**fourierCoeff.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeff.const_mul (f : AddCircle T -> Complex) (c : Complex) (n : Int
) : fourierCoeff (fun x => c * f x) n = c * fourierCoeff f n
参数：f : AddCircle T -> Complex；c : Complex；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fourierCoeff.const_smul`：fourierCoeff.const_smul (f : AddCircle T -> E) 
(c : Complex) (n : Int) : fourierCoeff (c • f :) n = c • fourierCoeff f n
-/
theorem fourierCoeff.const_mul (f : AddCircle T → ℂ) (c : ℂ) (n : ℤ) :
    fourierCoeff (fun x => c * f x) n = c * fourierCoeff f n :=
  fourierCoeff.const_smul f c n
/-
**fourierCoeff_congr_ae** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fourierCoeff_congr_ae {f g : AddCircle T -> E} (h : f =ᵐ[haarAddCircle] g)
 : fourierCoeff f = fourierCoeff g
参数：h : f =ᵐ[haarAddCircle] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.smul`：∀ {α : Type u} {β : Type v} {𝕜 : Type u_2} [in
st : SMul 𝕜 β] {l : Filter α} {f f' : α → 𝕜} {g g' : α → β},   f =ᶠ[l] f' → g =ᶠ
[l] g' → (fun …
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
lemma fourierCoeff_congr_ae {f g : AddCircle T → E}
    (h : f =ᵐ[haarAddCircle] g) : fourierCoeff f = fourierCoeff g :=
  funext fun _ ↦ integral_congr_ae <| .smul (.refl _ _) h

/-- For a function on `ℝ`, the Fourier coefficients of `f` on `[a, b]` are defined as the
Fourier coefficients of the unique periodic function agreeing with `f` on `Ioc a b`. -/
/-
**fourierCoeffOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fourierCoeffOn {a b : Real} (hab : a < b) (f : Real -> E) (n : Int) : E
参数：hab : a < b；f : Real -> E；n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a function on `ℝ`, the Fourier coefficients of `f` on `[a, b]` are defined a
s the
Fourier coefficients of the unique periodic function agreeing with `f` on `Ioc a
 b`.
-/
def fourierCoeffOn {a b : ℝ} (hab : a < b) (f : ℝ → E) (n : ℤ) : E :=
  haveI := Fact.mk (by linarith : 0 < b - a)
  fourierCoeff (AddCircle.liftIoc (b - a) a f) n
/-
**fourierCoeffOn_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeffOn_eq_integral {a b : Real} (f : Real -> E) (n : Int) (hab : a
 < b) : fourierCoeffOn hab f n = (1 / (b - a)) • ∫ x in a..b, fourier (-n) (x : 
AddCircle (b - a)) • f x
参数：f : Real -> E；n : Int；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
· 使用定理 `Mathlib.Tactic.Linarith.sub_neg_of_lt`：sub_neg_of_lt [IsOrderedRing α] {
a b : α} : a < b -> a - b < 0
（共 45 条，此处仅展示前 30 条）
-/
theorem fourierCoeffOn_eq_integral {a b : ℝ} (f : ℝ → E) (n : ℤ) (hab : a < b) :
    fourierCoeffOn hab f n =
      (1 / (b - a)) • ∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • f x := by
  have := Fact.mk (by linarith : 0 < b - a)
  rw [fourierCoeffOn, fourierCoeff_eq_intervalIntegral _ _ a, add_sub, add_sub_cancel_left]
  congr 1
  simp_rw [intervalIntegral.integral_of_le hab.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [liftIoc_coe_apply]
  rwa [add_sub, add_sub_cancel_left]
/-
**fourierCoeffOn.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeffOn.const_smul {a b : Real} (f : Real -> E) (c : Complex) (n : 
Int) (hab : a < b) : fourierCoeffOn hab (c • f) n = c • fourierCoeffOn hab f n
参数：f : Real -> E；c : Complex；n : Int；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
· 使用定理 `Mathlib.Tactic.Linarith.sub_neg_of_lt`：sub_neg_of_lt [IsOrderedRing α] {
a b : α} : a < b -> a - b < 0
（共 32 条，此处仅展示前 30 条）
-/
theorem fourierCoeffOn.const_smul {a b : ℝ} (f : ℝ → E) (c : ℂ) (n : ℤ) (hab : a < b) :
    fourierCoeffOn hab (c • f) n = c • fourierCoeffOn hab f n := by
  have := Fact.mk (by linarith : 0 < b - a)
  apply fourierCoeff.const_smul
/-
**fourierCoeffOn.const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeffOn.const_mul {a b : Real} (f : Real -> Complex) (c : Complex) 
(n : Int) (hab : a < b) : fourierCoeffOn hab (fun x => c * f x) n = c * fourierC
oeffOn hab f n
参数：f : Real -> Complex；c : Complex；n : Int；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fourierCoeffOn.const_smul`：fourierCoeffOn.const_smul {a b : Real} (f : R
eal -> E) (c : Complex) (n : Int) (hab : a < b) : fourierCoeffOn hab (c • f) n =
 c • fourierCoe…
-/
theorem fourierCoeffOn.const_mul {a b : ℝ} (f : ℝ → ℂ) (c : ℂ) (n : ℤ) (hab : a < b) :
    fourierCoeffOn hab (fun x => c * f x) n = c * fourierCoeffOn hab f n :=
  fourierCoeffOn.const_smul _ _ _ _
/-
**fourierCoeffOn_congr_ae** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fourierCoeffOn_congr_ae {a b : Real} (hab : a < b) {f g : Real -> E} (h : 
f =ᵐ[volume.restrict (Ioc a b)] g) : fourierCoeffOn hab f = fourierCoeffOn hab g
参数：hab : a < b；h : f =ᵐ[volume.restrict (Ioc a b)] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fourierCoeffOn_eq_integral`：fourierCoeffOn_eq_integral {a b : Real} (f :
 Real -> E) (n : Int) (hab : a < b) : fourierCoeffOn hab f n = (1 / (b - a)) • ∫
 x in a..b, four…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_congr_ae_restrict`：integral_congr_ae_restrict 
{a b : Real} {f g : Real -> E} {μ : Measure Real} (h : f =ᵐ[μ.restrict (Ι a b)] 
g) : ∫ x in a..b, f x ∂μ = ∫ x in…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma fourierCoeffOn_congr_ae {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (h : f =ᵐ[volume.restrict (Ioc a b)] g) :
    fourierCoeffOn hab f = fourierCoeffOn hab g := by
  ext n
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr! 1
  apply intervalIntegral.integral_congr_ae_restrict
  simp only [uIoc_of_le hab.le]
  filter_upwards [h] with x hx
  rw [hx]
/-
**fourierCoeff_liftIoc_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeff_liftIoc_eq {a : Real} (f : Real -> Complex) (n : Int) : fouri
erCoeff (AddCircle.liftIoc T a f) n = fourierCoeffOn (lt_add_of_pos_right a hT.o
ut) f n
参数：f : Real -> Complex；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fourierCoeffOn_eq_integral`：fourierCoeffOn_eq_integral {a b : Real} (f :
 Real -> E) (n : Int) (hab : a < b) : fourierCoeffOn hab f n = (1 / (b - a)) • ∫
 x in a..b, four…
· 使用定理 `fourierCoeff_eq_intervalIntegral`：fourierCoeff_eq_intervalIntegral (f : 
AddCircle T -> E) (n : Int) (a : Real) : fourierCoeff f n = (1 / T) • ∫ x in a..
a + T, @fourier T (-n)…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `intervalIntegral.integral_congr_ae`：integral_congr_ae (h : forallᵐ x ∂μ,
 x in Ι a b -> f x = g x) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AddCircle.liftIoc_coe_apply`：liftIoc_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx 
: x in Ioc a (a + p)) : liftIoc p a f ↑x = f x
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem fourierCoeff_liftIoc_eq {a : ℝ} (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (AddCircle.liftIoc T a f) n =
    fourierCoeffOn (lt_add_of_pos_right a hT.out) f n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral, add_sub_cancel_left a T]
  · congr 1
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
    rw [liftIoc_coe_apply]
    rwa [uIoc_of_le (lt_add_of_pos_right a hT.out).le] at hx
/-
**fourierCoeff_liftIco_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeff_liftIco_eq {a : Real} (f : Real -> Complex) (n : Int) : fouri
erCoeff (AddCircle.liftIco T a f) n = fourierCoeffOn (lt_add_of_pos_right a hT.o
ut) f n
参数：f : Real -> Complex；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fourierCoeffOn_eq_integral`：fourierCoeffOn_eq_integral {a b : Real} (f :
 Real -> E) (n : Int) (hab : a < b) : fourierCoeffOn hab f n = (1 / (b - a)) • ∫
 x in a..b, four…
· 使用定理 `fourierCoeff_eq_intervalIntegral`：fourierCoeff_eq_intervalIntegral (f : 
AddCircle T -> E) (n : Int) (a : Real) : fourierCoeff f n = (1 / T) • ∫ x in a..
a + T, @fourier T (-n)…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `intervalIntegral.integral_congr_Ioo_of_le`：integral_congr_Ioo_of_le [Nul
lSingletonClass μ] (hab : a <= b) (h : (Ioo a b).EqOn f g) : ∫ x in a..b, f x ∂μ
 = ∫ x in a..b, g x ∂μ
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `AddCircle.liftIco_coe_apply`：liftIco_coe_apply {f : 𝕜 -> B} {x : 𝕜} (hx 
: x in Ico a (a + p)) : liftIco p a f ↑x = f x
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
-/
theorem fourierCoeff_liftIco_eq {a : ℝ} (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (AddCircle.liftIco T a f) n =
    fourierCoeffOn (lt_add_of_pos_right a hT.out) f n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral _ _ a, add_sub_cancel_left a T]
  congr 1
  refine intervalIntegral.integral_congr_Ioo_of_le (le_add_of_nonneg_right hT.out.le) fun x hx => ?_
  rw [liftIco_coe_apply (Ioo_subset_Ico_self hx)]

end fourierCoeff

section FourierL2

/-- We define `fourierBasis` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 haarAddCircle`,
which by definition is an isometric isomorphism from `Lp ℂ 2 haarAddCircle` to `ℓ²(ℤ, ℂ)`. -/
/-
**fourierBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fourierBasis : HilbertBasis Int Complex (Lp Complex 2 <| @haarAddCircle T 
hT)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `orthonormal_fourier`：orthonormal_fourier : Orthonormal Complex (@fourier
Lp T _ 2 _)

--- 原说明 ---
We define `fourierBasis` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 haarAddCi
rcle`,
which by definition is an isometric isomorphism from `Lp ℂ 2 haarAddCircle` to `
ℓ²(ℤ, ℂ)`.
-/
def fourierBasis : HilbertBasis ℤ ℂ (Lp ℂ 2 <| @haarAddCircle T hT) :=
  HilbertBasis.mk orthonormal_fourier (span_fourierLp_closure_eq_top (by simp)).ge

/-- The elements of the Hilbert basis `fourierBasis` are the functions `fourierLp 2`, i.e. the
monomials `fourier n` on the circle considered as elements of `L²`. -/
@[simp]
/-
**coe_fourierBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_fourierBasis : ⇑(@fourierBasis T hT) = @fourierLp T hT 2 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HilbertBasis.coe_mk`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {
E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E]
 [inst_3 …
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `orthonormal_fourier`：orthonormal_fourier : Orthonormal Complex (@fourier
Lp T _ 2 _)

--- 原说明 ---
The elements of the Hilbert basis `fourierBasis` are the functions `fourierLp 2`
, i.e. the
monomials `fourier n` on the circle considered as elements of `L²`.
-/
theorem coe_fourierBasis : ⇑(@fourierBasis T hT) = @fourierLp T hT 2 _ :=
  HilbertBasis.coe_mk _ _

/-- Under the isometric isomorphism `fourierBasis` from `Lp ℂ 2 haarAddCircle` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is `fourierCoeff f i`, i.e., the integral over `AddCircle T` of
`fun t => fourier (-i) t * f t` with respect to the Haar measure of total mass 1. -/
/-
**fourierBasis_repr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierBasis_repr (f : Lp Complex 2 <| @haarAddCircle T hT) (i : Int) : fo
urierBasis.repr f i = fourierCoeff f i
参数：f : Lp Complex 2 <| @haarAddCircle T hT；i : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HilbertBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] (b : Hil…
· 使用定理 `MeasureTheory.L2.inner_def`：inner_def (f g : α ->₂[μ] E) : ⟪f, g⟫ = ∫ a 
: α, ⟪f a, g a⟫ ∂μ
· 使用定理 `coe_fourierBasis`：coe_fourierBasis : ⇑(@fourierBasis T hT) = @fourierLp 
T hT 2 _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.inner_apply'`：RCLike.inner_apply' (x y : 𝕜) : ⟪x, y⟫ = conj x * y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `coeFn_fourierLp`：coeFn_fourierLp (p : Real>=0∞) [Fact (1 <= p)] (n : Int
) : @fourierLp T hT p _ n =ᵐ[haarAddCircle] fourier n
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fourier_neg`：fourier_neg {n : Int} {x : AddCircle T} : fourier (-n) x = 
conj (fourier n x)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b

--- 原说明 ---
Under the isometric isomorphism `fourierBasis` from `Lp ℂ 2 haarAddCircle` to `ℓ
²(ℤ, ℂ)`, the
`i`-th coefficient is `fourierCoeff f i`, i.e., the integral over `AddCircle T` 
of
`fun t => fourier (-i) t * f t` with respect to the Haar measure of total mass 1
.
-/
theorem fourierBasis_repr (f : Lp ℂ 2 <| @haarAddCircle T hT) (i : ℤ) :
    fourierBasis.repr f i = fourierCoeff f i := by
  trans ∫ t : AddCircle T, conj ((@fourierLp T hT 2 _ i : AddCircle T → ℂ) t) * f t ∂haarAddCircle
  · rw [fourierBasis.repr_apply_apply f i, MeasureTheory.L2.inner_def, coe_fourierBasis]
    simp only [RCLike.inner_apply']
  · apply integral_congr_ae
    filter_upwards [coeFn_fourierLp 2 i] with _ ht
    rw [ht, ← fourier_neg, smul_eq_mul]

/-- The Fourier series of an `L2` function `f` sums to `f`, in the `L²` space of `AddCircle T`. -/
/-
**hasSum_fourier_series_L2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_fourier_series_L2 (f : Lp Complex 2 <| @haarAddCircle T hT) : HasSu
m (fun i => fourierCoeff f i • fourierLp 2 i) f
参数：f : Lp Complex 2 <| @haarAddCircle T hT。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coe_fourierBasis`：coe_fourierBasis : ⇑(@fourierBasis T hT) = @fourierLp 
T hT 2 _
· 使用定理 `HilbertBasis.hasSum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : RCLike
 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace
 𝕜 E] (b : Hil…

--- 原说明 ---
The Fourier series of an `L2` function `f` sums to `f`, in the `L²` space of `Ad
dCircle T`.
-/
theorem hasSum_fourier_series_L2 (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f := by
  simp_rw [← fourierBasis_repr]; rw [← coe_fourierBasis]
  exact HilbertBasis.hasSum_repr fourierBasis f

/-- **Parseval's identity**: for an `L²` function `f` on `AddCircle T`, the sum of the squared
norms of the Fourier coefficients equals the `L²` norm of `f`. -/
/-
**hasSum_sq_fourierCoeff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_sq_fourierCoeff (f : Lp Complex 2 <| @haarAddCircle T hT) : HasSum 
(fun i => ‖fourierCoeff f i‖ ^ 2) (∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle)
参数：f : Lp Complex 2 <| @haarAddCircle T hT。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `lp.hasSum_norm`：hasSum_norm (hp : 0 < p.toReal) (f : lp E p) : HasSum (f
un i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.L2.inner_def`：inner_def (f g : α ->₂[μ] E) : ⟪f, g⟫ = ∫ a 
: α, ⟪f a, g a⟫ ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `integral_re`：integral_re {f : X -> 𝕜} (hf : Integrable f μ) : ∫ x, RCLik
e.re (f x) ∂μ = RCLike.re (∫ x, f x ∂μ)
· 使用定理 `MeasureTheory.L2.integrable_inner`：integrable_inner (f g : α ->₂[μ] E) :
 Integrable (fun x : α => ⟪f x, g x⟫) μ

--- 原说明 ---
**Parseval's identity**: for an `L²` function `f` on `AddCircle T`, the sum of t
he squared
norms of the Fourier coefficients equals the `L²` norm of `f`.
-/
theorem hasSum_sq_fourierCoeff (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    HasSum (fun i => ‖fourierCoeff f i‖ ^ 2) (∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle) := by
  simp_rw [← fourierBasis_repr]
  have H₁ : HasSum (fun i => ‖fourierBasis.repr f i‖ ^ 2) (‖fourierBasis.repr f‖ ^ 2) := by
    apply_mod_cast lp.hasSum_norm ?_ (fourierBasis.repr f)
    simp
  have H₂ : ‖fourierBasis.repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp
  have H₃ := congr_arg RCLike.re (@L2.inner_def (AddCircle T) ℂ ℂ _ _ _ _ _ f f)
  rw [← integral_re] at H₃
  · simp only [← norm_sq_eq_re_inner] at H₃
    rwa [H₂, H₃] at H₁
  · exact L2.integrable_inner f f
/-
**tsum_sq_fourierCoeff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_sq_fourierCoeff (f : Lp Complex 2 <| @haarAddCircle T hT) : ∑' i : In
t, ‖fourierCoeff f i‖ ^ 2 = ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle
参数：f : Lp Complex 2 <| @haarAddCircle T hT。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_sq_fourierCoeff`：hasSum_sq_fourierCoeff (f : Lp Complex 2 <| @haa
rAddCircle T hT) : HasSum (fun i => ‖fourierCoeff f i‖ ^ 2) (∫ t : AddCircle T, 
‖f t‖ ^ 2 ∂h…
-/
theorem tsum_sq_fourierCoeff (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ∑' i : ℤ, ‖fourierCoeff f i‖ ^ 2 = ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle :=
  (hasSum_sq_fourierCoeff _).tsum_eq

/-- **Parseval's identity**: for a function `f` which is square integrable on `(a,b]`,
the sum of the squared norms of the Fourier coefficients equals the `L²` norm of `f`. -/
/-
**hasSum_sq_fourierCoeffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_sq_fourierCoeffOn {a b : Real} {f : Real -> Complex} (hab : a < b) 
(hL2 : MemLp f 2 (volume.restrict (Ioc a b))) : HasSum (fun i => ‖fourierCoeffOn
 hab f i‖ ^ 2) ((b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2)
参数：hab : a < b；hL2 : MemLp f 2 (volume.restrict (Ioc a b))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
**Parseval's identity**: for a function `f` which is square integrable on `(a,b]
`,
the sum of the squared norms of the Fourier coefficients equals the `L²` norm of
 `f`.
-/
theorem hasSum_sq_fourierCoeffOn
    {a b : ℝ} {f : ℝ → ℂ} (hab : a < b) (hL2 : MemLp f 2 (volume.restrict (Ioc a b))) :
    HasSum (fun i => ‖fourierCoeffOn hab f i‖ ^ 2) ((b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2) := by
  have := Fact.mk (by linarith : 0 < b - a)
  rw [← add_sub_cancel a b] at hL2
  have h := hL2.memLp_liftIoc.haarAddCircle
  convert hasSum_sq_fourierCoeff h.toLp
  · simp [fourierCoeff_congr_ae h.coeFn_toLp, fourierCoeff_liftIoc_eq]
  · nth_rw 2 [← add_sub_cancel a b]
    rw [← AddCircle.integral_liftIoc_eq_intervalIntegral, ← Function.comp_def (f := (‖·‖ ^ 2))]
    simp only [liftIoc_comp_apply, ← AddCircle.integral_haarAddCircle]
    apply integral_congr_ae
    filter_upwards [h.coeFn_toLp] with x hx
    simp [hx]
/-
**tsum_sq_fourierCoeffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_sq_fourierCoeffOn {a b : Real} {f : Real -> Complex} (hab : a < b) (h
L2 : MemLp f 2 (volume.restrict (Ioc a b))) : ∑' (i : Int), ‖fourierCoeffOn hab 
f i‖ ^ 2 = (b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2
参数：hab : a < b；hL2 : MemLp f 2 (volume.restrict (Ioc a b))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_sq_fourierCoeffOn`：hasSum_sq_fourierCoeffOn {a b : Real} {f : Rea
l -> Complex} (hab : a < b) (hL2 : MemLp f 2 (volume.restrict (Ioc a b))) : HasS
um (fun i => ‖…
-/
theorem tsum_sq_fourierCoeffOn
    {a b : ℝ} {f : ℝ → ℂ} (hab : a < b) (hL2 : MemLp f 2 (volume.restrict (Ioc a b))) :
    ∑' (i : ℤ), ‖fourierCoeffOn hab f i‖ ^ 2 = (b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2 :=
  (hasSum_sq_fourierCoeffOn _ hL2).tsum_eq

end FourierL2

section Convergence

variable (f : C(AddCircle T, ℂ))

/-
**fourierCoeff_toLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeff_toLp (n : Int) : fourierCoeff (toLp (E
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AddCircle.instIsProbabilityMeasureRealHaarAddCircle`：∀ {T : ℝ} [hT : Fac
t (0 < T)], MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle
· 使用定理 `Filter.EventuallyEq.mul`：∀ {α : Type u} {β : Type v} [inst : Mul β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f * f' =ᶠ[l] g * g'
（共 34 条，此处仅展示前 30 条）
-/
theorem fourierCoeff_toLp (n : ℤ) :
    fourierCoeff (toLp (E := ℂ) 2 haarAddCircle ℂ f) n = fourierCoeff f n :=
  integral_congr_ae (Filter.EventuallyEq.mul (Filter.Eventually.of_forall (by tauto))
    (ContinuousMap.coeFn_toAEEqFun haarAddCircle f))

variable {f}

/-- If the sequence of Fourier coefficients of `f` is summable, then the Fourier series converges
uniformly to `f`. -/
/-
**hasSum_fourier_series_of_summable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_fourier_series_of_summable (h : Summable (fourierCoeff f)) : HasSum
 (fun i => fourierCoeff f i • fourier i) f
参数：h : Summable (fourierCoeff f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `QuotientAddGroup.borelSpace`：∀ {G : Type u_3} [inst : TopologicalSpace G
] [PolishSpace G] [inst_2 : AddGroup G] [IsTopologicalAddGroup G]   [inst_4 : Me
asurableSpace G] …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples`：∀ {a : ℝ}, 
DiscreteTopology ↥(AddSubgroup.zmultiples a)
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AddCircle.instIsProbabilityMeasureRealHaarAddCircle`：∀ {T : ℝ} [hT : Fac
t (0 < T)], MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle
· 使用定理 `hasSum_fourier_series_L2`：hasSum_fourier_series_L2 (f : Lp Complex 2 <| 
@haarAddCircle T hT) : HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f
· 使用定理 `ContinuousMap.hasSum_of_hasSum_Lp`：hasSum_of_hasSum_Lp {β : Type*} [μ.Is
OpenPosMeasure] {g : β -> C(α, E)} {f : C(α, E)} (hg : Summable g) (hg2 : HasSum
 (toLp (E
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
If the sequence of Fourier coefficients of `f` is summable, then the Fourier ser
ies converges
uniformly to `f`.
-/
theorem hasSum_fourier_series_of_summable (h : Summable (fourierCoeff f)) :
    HasSum (fun i => fourierCoeff f i • fourier i) f := by
  have sum_L2 := hasSum_fourier_series_L2 (toLp (E := ℂ) 2 haarAddCircle ℂ f)
  simp_rw [fourierCoeff_toLp] at sum_L2
  refine ContinuousMap.hasSum_of_hasSum_Lp (.of_norm ?_) sum_L2
  simp_rw [norm_smul, fourier_norm, mul_one]
  exact h.norm

/-- If the sequence of Fourier coefficients of `f` is summable, then the Fourier series of `f`
converges everywhere pointwise to `f`. -/
/-
**has_pointwise_sum_fourier_series_of_summable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：has_pointwise_sum_fourier_series_of_summable (h : Summable (fourierCoeff f
)) (x : AddCircle T) : HasSum (fun i => fourierCoeff f i • fourier i x) (f x)
参数：h : Summable (fourierCoeff f)；x : AddCircle T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u
_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂]
 [inst_2 : AddCo…
· 使用定理 `hasSum_fourier_series_of_summable`：hasSum_fourier_series_of_summable (h 
: Summable (fourierCoeff f)) : HasSum (fun i => fourierCoeff f i • fourier i) f

--- 原说明 ---
If the sequence of Fourier coefficients of `f` is summable, then the Fourier ser
ies of `f`
converges everywhere pointwise to `f`.
-/
theorem has_pointwise_sum_fourier_series_of_summable (h : Summable (fourierCoeff f))
    (x : AddCircle T) : HasSum (fun i => fourierCoeff f i • fourier i x) (f x) := by
  convert! (ContinuousMap.evalCLM ℂ x).hasSum (hasSum_fourier_series_of_summable h)

end Convergence

end ScopeHT

section computations

/-
**fourierCoeff_fourier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeff_fourier {T : Real} [hT : Fact (0 < T)] (n : Int) : fourierCoe
ff (T
参数：0 < T；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `fourierCoeff_congr_ae`：fourierCoeff_congr_ae {f g : AddCircle T -> E} (h
 : f =ᵐ[haarAddCircle] g) : fourierCoeff f = fourierCoeff g
· 使用定理 `coeFn_fourierLp`：coeFn_fourierLp (p : Real>=0∞) [Fact (1 <= p)] (n : Int
) : @fourierLp T hT p _ n =ᵐ[haarAddCircle] fourier n
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fourierBasis_repr`：fourierBasis_repr (f : Lp Complex 2 <| @haarAddCircle
 T hT) (i : Int) : fourierBasis.repr f i = fourierCoeff f i
· 使用定理 `HilbertBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_2} [inst : R
CLike 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduct
Space 𝕜 E] (b : Hil…
· 使用定理 `coe_fourierBasis`：coe_fourierBasis : ⇑(@fourierBasis T hT) = @fourierLp 
T hT 2 _
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `orthonormal_fourier`：orthonormal_fourier : Orthonormal Complex (@fourier
Lp T _ 2 _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem fourierCoeff_fourier {T : ℝ} [hT : Fact (0 < T)] (n : ℤ) :
    fourierCoeff (T := T) (fourier n) = Pi.single n 1 := by
  ext m
  rw [← fourierCoeff_congr_ae (coeFn_fourierLp 2 n), ← fourierBasis_repr,
    HilbertBasis.repr_apply_apply, coe_fourierBasis]
  obtain (rfl | hmn) := eq_or_ne m n
  · rw [inner_self_eq_norm_sq_to_K, (orthonormal_fourier (hT := hT)).1 m]; simp
  · rw [(orthonormal_fourier (hT := hT)).2 hmn]; simp [hmn]

end computations

section deriv

open Complex intervalIntegral

open scoped Interval

variable (T)

/-
**hasDerivAt_fourier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_fourier (n : Int) (x : Real) : HasDerivAt (fun y : Real => four
ier n (y : AddCircle T)) (2 * π * I * n / T * fourier n (x : AddCircle T)) x
参数：n : Int；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `fourier_coe_apply`：fourier_coe_apply {n : Int} {x : Real} : fourier n (x
 : AddCircle T) = Complex.exp (2 * π * Complex.I * n * x / T)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasDerivAt.comp_ofReal`：HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z)
 : HasDerivAt (fun y : Real => e ↑y) e' z
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Complex.hasDerivAt_exp`：hasDerivAt_exp (x : Complex) : HasDerivAt exp (e
xp x) x
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 41 条，此处仅展示前 30 条）
-/
theorem hasDerivAt_fourier (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourier n (y : AddCircle T))
      (2 * π * I * n / T * fourier n (x : AddCircle T)) x := by
  simp_rw [fourier_coe_apply]
  refine (?_ : HasDerivAt (fun y => exp (2 * π * I * n * y / T)) _ _).comp_ofReal
  rw [(fun α β => by ring : ∀ α β : ℂ, α * exp β = exp β * α)]
  refine (hasDerivAt_exp _).comp (x : ℂ) ?_
  convert! hasDerivAt_mul_const (2 * ↑π * I * ↑n / T) using 1
  ext1 y; ring
/-
**hasDerivAt_fourier_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_fourier_neg (n : Int) (x : Real) : HasDerivAt (fun y : Real => 
fourier (-n) (y : AddCircle T)) (-2 * π * I * n / T * fourier (-n) (x : AddCircl
e T)) x
参数：n : Int；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `fourier_neg'`：fourier_neg' {n : Int} {x : AddCircle T} : @toCircle T (-(
n • x)) = conj (fourier n x)
· 使用定理 `fourier_coe_apply'`：fourier_coe_apply' {n : Int} {x : Real} : toCircle (
n • (x : AddCircle T) :) = Complex.exp (2 * π * Complex.I * n * x / T)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `hasDerivAt_fourier`：hasDerivAt_fourier (n : Int) (x : Real) : HasDerivAt
 (fun y : Real => fourier n (y : AddCircle T)) (2 * π * I * n / T * fourier n (x
 : AddCi…
-/
theorem hasDerivAt_fourier_neg (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourier (-n) (y : AddCircle T))
      (-2 * π * I * n / T * fourier (-n) (x : AddCircle T)) x := by
  simpa using hasDerivAt_fourier T (-n) x

variable {T}
/-
**has_antideriv_at_fourier_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：has_antideriv_at_fourier_neg (hT : Fact (0 < T)) {n : Int} (hn : n != 0) (
x : Real) : HasDerivAt (fun y : Real => (T : Complex) / (-2 * π * I * n) * fouri
er (-n) (y : AddCircle T)) (fourier (-n) (x : AddCircle T)) x
参数：hT : Fact (0 < T)；hn : n != 0；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_div_eq_mul_div`：div_div_eq_mul_div : a / (b / c) = a * c / b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 67 条，此处仅展示前 30 条）
-/
theorem has_antideriv_at_fourier_neg (hT : Fact (0 < T)) {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (T : ℂ) / (-2 * π * I * n) * fourier (-n) (y : AddCircle T))
      (fourier (-n) (x : AddCircle T)) x := by
  convert! (hasDerivAt_fourier_neg T n x).div_const (-2 * π * I * n / T) using 1
  · ext1 y; rw [div_div_eq_mul_div]; ring
  · simp [mul_div_cancel_left₀, hn, (Fact.out : 0 < T).ne', Real.pi_pos.ne']

/-- Express Fourier coefficients of `f` on an interval in terms of those of its derivative. -/
/-
**fourierCoeffOn_of_hasDeriv_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeffOn_of_hasDeriv_right {a b : Real} (hab : a < b) {f f' : Real -
> Complex} {n : Int} (hn : n != 0) (hf : ContinuousOn f [[a, b]]) (hff' : forall
 x, x in Ioo (min a b) (max a b) -> HasDerivWithinAt f (f' x) (Ioi x) x) (hf' : 
IntervalIntegrable f' volume a b) : fourierCoeffOn hab f n = 1 / (-2 * π * I * n
) * (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeff
On hab f' n)
参数：hab : a < b；hn : n != 0；hf : ContinuousOn f [[a, b]]；hff' : forall x, x in Io
o (min a b) (max a b) -> HasDerivWithinAt f (f' x) (Ioi x) x；hf' : IntervalInteg
rable f' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
（共 99 条，此处仅展示前 30 条）

--- 原说明 ---
Express Fourier coefficients of `f` on an interval in terms of those of its deri
vative.
-/
theorem fourierCoeffOn_of_hasDeriv_right {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x, x ∈ Ioo (min a b) (max a b) → HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n = 1 / (-2 * π * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeffOn hab f' n) := by
  rw [← ofReal_sub]
  have hT : Fact (0 < b - a) := ⟨by linarith⟩
  simp_rw [fourierCoeffOn_eq_integral, smul_eq_mul, real_smul, ofReal_div, ofReal_one]
  conv => pattern (occs := 1 2 3) fourier _ _ * _ <;> (rw [mul_comm])
  rw [integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hf
    (fun x _ ↦ has_antideriv_at_fourier_neg hT hn x |>.continuousAt |>.continuousWithinAt) hff'
    (fun x _ ↦ has_antideriv_at_fourier_neg hT hn x |>.hasDerivWithinAt) hf'
    (((map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)).intervalIntegrable _ _)]
  have : ∀ u v w : ℂ, u * ((b - a : ℝ) / v * w) = (b - a : ℝ) / v * (u * w) := by intros; ring
  conv in intervalIntegral _ _ _ _ => congr; ext; rw [this]
  rw [(by ring : ((b - a : ℝ) : ℂ) / (-2 * π * I * n) = ((b - a : ℝ) : ℂ) * (1 / (-2 * π * I * n)))]
  have s2 : (b : AddCircle (b - a)) = (a : AddCircle (b - a)) := by
    simpa using coe_add_period (b - a) a
  rw [s2, intervalIntegral.integral_const_mul, ← sub_mul, mul_sub, mul_sub]
  congr 1
  · conv_lhs => rw [mul_comm, mul_div, mul_one]
    rw [div_eq_iff (ofReal_ne_zero.mpr hT.out.ne')]
    ring
  · ring

/-- Express Fourier coefficients of `f` on an interval in terms of those of its derivative. -/
/-
**fourierCoeffOn_of_hasDerivAt_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeffOn_of_hasDerivAt_Ioo {a b : Real} (hab : a < b) {f f' : Real -
> Complex} {n : Int} (hn : n != 0) (hf : ContinuousOn f [[a, b]]) (hff' : forall
 x, x in Ioo (min a b) (max a b) -> HasDerivAt f (f' x) x) (hf' : IntervalIntegr
able f' volume a b) : fourierCoeffOn hab f n = 1 / (-2 * π * I * n) * (fourier (
-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeffOn hab f' n)
参数：hab : a < b；hn : n != 0；hf : ContinuousOn f [[a, b]]；hff' : forall x, x in Io
o (min a b) (max a b) -> HasDerivAt f (f' x) x；hf' : IntervalIntegrable f' volum
e a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `fourierCoeffOn_of_hasDeriv_right`：fourierCoeffOn_of_hasDeriv_right {a b 
: Real} (hab : a < b) {f f' : Real -> Complex} {n : Int} (hn : n != 0) (hf : Con
tinuousOn f [[a, b]]) …
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
Express Fourier coefficients of `f` on an interval in terms of those of its deri
vative.
-/
theorem fourierCoeffOn_of_hasDerivAt_Ioo {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x, x ∈ Ioo (min a b) (max a b) → HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n = 1 / (-2 * π * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeffOn hab f' n) :=
  fourierCoeffOn_of_hasDeriv_right hab hn hf (fun x hx ↦ hff' x hx |>.hasDerivWithinAt) hf'

/-- Express Fourier coefficients of `f` on an interval in terms of those of its derivative. -/
/-
**fourierCoeffOn_of_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fourierCoeffOn_of_hasDerivAt {a b : Real} (hab : a < b) {f f' : Real -> Co
mplex} {n : Int} (hn : n != 0) (hf : forall x, x in [[a, b]] -> HasDerivAt f (f'
 x) x) (hf' : IntervalIntegrable f' volume a b) : fourierCoeffOn hab f n = 1 / (
-2 * π * I * n) * (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) 
* fourierCoeffOn hab f' n)
参数：hab : a < b；hn : n != 0；hf : forall x, x in [[a, b]] -> HasDerivAt f (f' x) x
；hf' : IntervalIntegrable f' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `fourierCoeffOn_of_hasDerivAt_Ioo`：fourierCoeffOn_of_hasDerivAt_Ioo {a b 
: Real} (hab : a < b) {f f' : Real -> Complex} {n : Int} (hn : n != 0) (hf : Con
tinuousOn f [[a, b]]) …
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Set.mem_Icc_of_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ioo a b → x ∈ Set.Icc a b

--- 原说明 ---
Express Fourier coefficients of `f` on an interval in terms of those of its deri
vative.
-/
theorem fourierCoeffOn_of_hasDerivAt {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x, x ∈ [[a, b]] → HasDerivAt f (f' x) x) (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n = 1 / (-2 * π * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeffOn hab f' n) :=
  fourierCoeffOn_of_hasDerivAt_Ioo hab hn
    (fun x hx ↦ hf x hx |>.continuousAt.continuousWithinAt)
    (fun x hx ↦ hf x <| mem_Icc_of_Ioo hx)
    hf'

end deriv

