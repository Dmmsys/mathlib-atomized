/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Monotonicity and ℒp seminorms
-/

public noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal ComplexConjugate

variable {α E F G : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

namespace MeasureTheory

section Monotonicity

variable {ε ε' : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ContinuousENorm ε']

/-
**MeasureTheory.eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {F : Type u_3} {G : Type u_4} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup F] [inst_1 : NormedAddCo
mmGroup G] {f : α → F} {g : α → G} {c : NNReal},   (∀ᵐ (x : α) ∂μ, ‖f x‖₊ ≤ c * 
‖g x‖₊) →     ∀ {p : ℝ}, 0 < p → MeasureTheory.eLpNorm' f p μ ≤ c • MeasureTheor
y.eLpNorm' g p μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_le_rpow_iff`：rpow_le_rpow_iff {x y : Real>=0∞} {z : Real} (
hz : 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `MeasureTheory.lintegral_const_mul'`：lintegral_const_mul' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用定理 `ENNReal.coe_le_coe._gcongr_2`：∀ {r q : NNReal}, r ≤ q → ↑r ≤ ↑q
· 使用定理 `NNReal.rpow_le_rpow`：∀ {x y : NNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤ y
 ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) {p : ℝ} (hp : 0 < p) :
    eLpNorm' f p μ ≤ c • eLpNorm' g p μ := by
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.smul_def, smul_eq_mul,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one, enorm,
    ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
    ← ENNReal.coe_mul]
  apply lintegral_mono_ae
  filter_upwards [h] with x hx
  rw [← NNReal.mul_rpow]
  gcongr

-- TODO: eventually, deprecate and remove the nnnorm version
/-
**MeasureTheory.eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε 
: Type u_5} {ε' : Type u_6}   [inst : TopologicalSpace ε] [inst_1 : ContinuousEN
orm ε] [inst_2 : TopologicalSpace ε'] [inst_3 : ContinuousENorm ε']   {f : α → ε
} {g : α → ε'} {c : NNReal},   (∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ↑c * ‖g x‖ₑ) →     ∀ {p 
: ℝ}, 0 < p → MeasureTheory.eLpNorm' f p μ ≤ c • MeasureTheory.eLpNorm' g p μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ↑c * ‖g x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_le_rpow_iff`：rpow_le_rpow_iff {x y : Real>=0∞} {z : Real} (
hz : 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `MeasureTheory.lintegral_const_mul'`：lintegral_const_mul' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 55 条，此处仅展示前 30 条）
-/
theorem eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' {f : α → ε} {g : α → ε'} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) {p : ℝ} (hp : 0 < p) :
    eLpNorm' f p μ ≤ c • eLpNorm' g p μ := by
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.smul_def, smul_eq_mul,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one,
    ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono_ae
  have aux (x) : (↑c) ^ p * ‖g x‖ₑ ^ p = (↑c * ‖g x‖ₑ) ^ p := by
    have : ¬(p < 0) := by linarith
    simp [ENNReal.mul_rpow_eq_ite, this]
  simpa [ENNReal.coe_rpow_of_nonneg _ hp.le, aux, ENNReal.rpow_le_rpow_iff hp]

section ESeminormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

/-- If `‖f x‖ₑ ≤ c * ‖g x‖ₑ` a.e., `eLpNorm' f p μ ≤ c * eLpNorm' g p μ` for all `p ∈ (0, ∞)`. -/
/-
**MeasureTheory.eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε'
 : Type u_6} [inst : TopologicalSpace ε']   [inst_1 : ContinuousENorm ε'] {ε : T
ype u_7} [inst_2 : TopologicalSpace ε] [inst_3 : ESeminormedAddMonoid ε]   {f : 
α → ε} {c : ENNReal} {g : α → ε'} {p : ℝ},   MeasureTheory.AEStronglyMeasurable 
g μ →     (∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) → 0 < p → MeasureTheory.eLpNorm' 
f p μ ≤ c * MeasureTheory.eLpNorm' g p μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
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
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
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
· 使用定理 `Mathlib.Tactic.Linarith.add_neg`：add_neg [IsStrictOrderedRing α] {a b : 
α} (ha : a < 0) (hb : b < 0) : a + b < 0
· 使用定理 `Mathlib.Tactic.Linarith.sub_neg_of_lt`：sub_neg_of_lt [IsOrderedRing α] {
a b : α} : a < b -> a - b < 0
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
If `‖f x‖ₑ ≤ c * ‖g x‖ₑ` a.e., `eLpNorm' f p μ ≤ c * eLpNorm' g p μ` for all `p 
∈ (0, ∞)`.
-/
theorem eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul {f : α → ε} {c : ℝ≥0∞} {g : α → ε'} {p : ℝ}
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) (hp : 0 < p) :
    eLpNorm' f p μ ≤ c * eLpNorm' g p μ := by
  have hp' : ¬(p < 0) := by linarith
  by_cases hc : c = ⊤
  · by_cases hg' : eLpNorm' g p μ = 0
    · have : ∀ᵐ (x : α) ∂μ, ‖g x‖ₑ = 0 := by
        simp only [eLpNorm'_eq_lintegral_enorm, one_div, ENNReal.rpow_eq_zero_iff, inv_pos, hp,
          and_true, inv_neg'', hp', and_false, or_false] at hg'
        rw [MeasureTheory.lintegral_eq_zero_iff' (by fun_prop)] at hg'
        exact hg'.mono fun x hx ↦ by simpa [hp, hp'] using hx
      have : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ = 0 := (this.and h).mono fun x ⟨h, h'⟩ ↦ by simp_all
      simpa only [hg', mul_zero, nonpos_iff_eq_zero] using eLpNorm'_eq_zero_of_ae_eq_zero hp this
    · simp_all
  have : c ^ p ≠ ⊤ := by simp [hp.le, hc]
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one,
    ← lintegral_const_mul' _ _ this]
  apply lintegral_mono_ae
  have aux (x) : (↑c) ^ p * ‖g x‖ₑ ^ p = (↑c * ‖g x‖ₑ) ^ p := by
    simp [ENNReal.mul_rpow_eq_ite, hp']
  simpa [ENNReal.coe_rpow_of_nonneg _ hp.le, aux, ENNReal.rpow_le_rpow_iff hp]

end ESeminormedAddMonoid

-- TODO: eventually, deprecate and remove the nnnorm version
/-
**MeasureTheory.eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' {f : α -> ε} {g :
 α -> ε'} {c : Real>=0∞} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) : eLpNormEssSu
p f μ <= c • eLpNormEssSup g μ
参数：h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `essSup_mono_ae`：essSup_mono_ae {f g : α -> β} (hfg : f <=ᵐ[μ] g) (hf : I
sCoboundedUnder (· <= ·) (ae μ) f
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `ENNReal.essSup_const_mul`：essSup_const_mul {a : Real>=0∞} : essSup (fun 
x : α => a * f x) μ = a * essSup f μ
-/
theorem eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' {f : α → ε} {g : α → ε'} {c : ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) : eLpNormEssSup f μ ≤ c • eLpNormEssSup g μ :=
  calc
    essSup (‖f ·‖ₑ) μ ≤ essSup (c * ‖g ·‖ₑ) μ := essSup_mono_ae <| h
    _ = c • essSup (‖g ·‖ₑ) μ := ENNReal.essSup_const_mul
/-
**MeasureTheory.eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul {f : α -> F} {g : 
α -> G} {c : Real>=0} (h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) : eLpNormEssSup f
 μ <= c • eLpNormEssSup g μ
参数：h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `essSup_mono_ae`：essSup_mono_ae {f g : α -> β} (hfg : f <=ᵐ[μ] g) (hf : I
sCoboundedUnder (· <= ·) (ae μ) f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.essSup_const_mul`：essSup_const_mul {a : Real>=0∞} : essSup (fun 
x : α => a * f x) μ = a * essSup f μ
-/
theorem eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : eLpNormEssSup f μ ≤ c • eLpNormEssSup g μ :=
  calc
    essSup (‖f ·‖ₑ) μ ≤ essSup (fun x => (↑(c * ‖g x‖₊) : ℝ≥0∞)) μ :=
      essSup_mono_ae <| h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx
    _ = essSup (c * ‖g ·‖ₑ) μ := by simp_rw [ENNReal.coe_mul, enorm]
    _ = c • essSup (‖g ·‖ₑ) μ := ENNReal.essSup_const_mul

-- TODO: eventually, deprecate and remove the nnnorm version
/-
**MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' {f : α -> ε} {g : α -> ε'} {c
 : Real>=0} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) (p : Real>=0∞) : eLpNorm f 
p μ <= c • eLpNorm g p μ
参数：h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ；p : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'`：
eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' {f : α -> ε} {g : α -> 
ε'} {c : Real>=0∞} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) …
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `MeasureTheory.eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'`：∀ {α : Typ
e u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_5} {ε' 
: Type u_6}   [inst : TopologicalSpace ε] [inst_1 …
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
-/
theorem eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' {f : α → ε} {g : α → ε'} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) (p : ℝ≥0∞) : eLpNorm f p μ ≤ c • eLpNorm g p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' h (ENNReal.toReal_pos h0 h_top)
/-
**MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul {f : α -> F} {g : α -> G} {c :
 Real>=0} (h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) (p : Real>=0∞) : eLpNorm f p 
μ <= c • eLpNorm g p μ
参数：h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊；p : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul`：e
LpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul {f : α -> F} {g : α -> G}
 {c : Real>=0} (h : forallᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) : e…
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `MeasureTheory.eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul`：∀ {α : Type
 u_1} {F : Type u_3} {G : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [inst : NormedAddCommGroup F] [inst_1…
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
-/
theorem eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) (p : ℝ≥0∞) : eLpNorm f p μ ≤ c • eLpNorm g p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul h
  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul h (ENNReal.toReal_pos h0 h_top)

-- TODO: add the whole family of lemmas?
/-
**MeasureTheory.le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg {α}
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b c : α} (ha : 0 ≤ a) (hb : b < 0) (hc : 0 ≤ c) : a ≤ b * c ↔ a = 0 ∧ c = 0 := by
  constructor
  · intro h
    exact
      ⟨(h.trans (mul_nonpos_of_nonpos_of_nonneg hb.le hc)).antisymm ha,
        (nonpos_of_mul_nonneg_right (ha.trans h) hb).antisymm hc⟩
  · rintro ⟨rfl, rfl⟩
    rw [mul_zero]

/-- When `c` is negative, `‖f x‖ ≤ c * ‖g x‖` is nonsense and forces both `f` and `g` to have an
`eLpNorm` of `0`. -/
/-
**MeasureTheory.eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg {f : α -> F} {g : α -> G} {c : R
eal} (h : forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖) (hc : c < 0) (p : Real>=0∞) : eLpNor
m f p μ = 0 ∧ eLpNorm g p μ = 0
参数：h : forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖；hc : c < 0；p : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity.0.Measur
eTheory.le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg`：∀ {α : Type u_7} [inst : 
Semiring α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {a b c : α},   0 ≤ 
a → b < 0 → 0 ≤ c → (a ≤ b * c ↔ a …
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
When `c` is negative, `‖f x‖ ≤ c * ‖g x‖` is nonsense and forces both `f` and `g
` to have an
`eLpNorm` of `0`.
-/
theorem eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg {f : α → F} {g : α → G} {c : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (hc : c < 0) (p : ℝ≥0∞) :
    eLpNorm f p μ = 0 ∧ eLpNorm g p μ = 0 := by
  simp_rw [le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg (norm_nonneg _) hc (norm_nonneg _),
    norm_eq_zero, eventually_and] at h
  change f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0 at h
  simp [eLpNorm_congr_ae h.1, eLpNorm_congr_ae h.2]
/-
**MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：eLpNorm_le_mul_eLpNorm_of_ae_le_mul {f : α -> F} {g : α -> G} {c : Real} (
h : forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖) (p : Real>=0∞) : eLpNorm f p μ <= ENNReal.
ofReal c * eLpNorm g p μ
参数：h : forallᵐ x ∂μ, ‖f x‖ <= c * ‖g x‖；p : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul`：eLpNorm_le_nn
real_smul_eLpNorm_of_ae_le_mul {f : α -> F} {g : α -> G} {c : Real>=0} (h : fora
llᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) (p : Real>=0∞) …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Real.le_coe_toNNReal`：∀ (r : ℝ), r ≤ ↑r.toNNReal
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (p : ℝ≥0∞) :
    eLpNorm f p μ ≤ ENNReal.ofReal c * eLpNorm g p μ :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (h.mono fun _x hx => hx.trans <| mul_le_mul_of_nonneg_right c.le_coe_toNNReal (norm_nonneg _)) _

-- TODO: eventually, deprecate and remove the nnnorm version
/-- If `‖f x‖ₑ ≤ c * ‖g x‖ₑ`, then `eLpNorm f p μ ≤ c * eLpNorm g p μ`.

This version assumes `c` is finite, but requires no measurability hypothesis on `g`. -/
/-
**MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：eLpNorm_le_mul_eLpNorm_of_ae_le_mul' {f : α -> ε} {g : α -> ε'} {c : Real>
=0} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) (p : Real>=0∞) : eLpNorm f p μ <= c
 * eLpNorm g p μ
参数：h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ；p : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'`：eLpNorm_le_n
nreal_smul_eLpNorm_of_ae_le_mul' {f : α -> ε} {g : α -> ε'} {c : Real>=0} (h : f
orallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) (p : Real>=0∞…

--- 原说明 ---
If `‖f x‖ₑ ≤ c * ‖g x‖ₑ`, then `eLpNorm f p μ ≤ c * eLpNorm g p μ`.

This version assumes `c` is finite, but requires no measurability hypothesis on 
`g`.
-/
theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul' {f : α → ε} {g : α → ε'} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) (p : ℝ≥0∞) :
    eLpNorm f p μ ≤ c * eLpNorm g p μ := by
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' h

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] in
/-- If `‖f x‖ₑ ≤ c * ‖g x‖ₑ`, then `eLpNorm f p μ ≤ c * eLpNorm g p μ`.

This version allows `c = ∞`, but requires `g` to be a.e. strongly measurable. -/
/-
**MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul''** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' {f : α -> ε} {c : Real>=0∞} {g : α -
> ε'} (p : Real>=0∞) (hg : AEStronglyMeasurable g μ) (h : forallᵐ x ∂μ, ‖f x‖ₑ <
= c * ‖g x‖ₑ) : eLpNorm f p μ <= c * eLpNorm g p μ
参数：p : Real>=0∞；hg : AEStronglyMeasurable g μ；h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g
 x‖ₑ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'`：
eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' {f : α -> ε} {g : α -> 
ε'} {c : Real>=0∞} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) …
· 使用定理 `MeasureTheory.eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul`：∀ {α : Type u_1} {m
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε' : Type u_6} [inst : Topo
logicalSpace ε']   [inst_1 : ContinuousEN…
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal

--- 原说明 ---
If `‖f x‖ₑ ≤ c * ‖g x‖ₑ`, then `eLpNorm f p μ ≤ c * eLpNorm g p μ`.

This version allows `c = ∞`, but requires `g` to be a.e. strongly measurable.
-/
theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' {f : α → ε} {c : ℝ≥0∞} {g : α → ε'} (p : ℝ≥0∞)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) :
    eLpNorm f p μ ≤ c * eLpNorm g p μ := by
  by_cases h₀ : p = 0
  · simp [h₀]
  simp only [eLpNorm, h₀, ↓reduceIte, mul_ite]
  by_cases hp' : p = ⊤
  · simpa [hp'] using eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
  · simpa [hp'] using eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul hg h (ENNReal.toReal_pos h₀ hp')
/-
**MeasureTheory.MemLp.of_nnnorm_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} {m : MeasurableSpace α} {p 
: ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] [inst_1
 : NormedAddCommGroup F] {f : α → E} {g : α → F} {c : NNReal},   MeasureTheory.M
emLp g p μ →     MeasureTheory.AEStronglyMeasurable f μ → (∀ᵐ (x : α) ∂μ, ‖f x‖₊
 ≤ c * ‖g x‖₊) → MeasureTheory.MemLp f p μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul`：eLpNorm_le_nn
real_smul_eLpNorm_of_ae_le_mul {f : α -> F} {g : α -> G} {c : Real>=0} (h : fora
llᵐ x ∂μ, ‖f x‖₊ <= c * ‖g x‖₊) (p : Real>=0∞) …
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
theorem MemLp.of_nnnorm_le_mul {f : α → E} {g : α → F} {c : ℝ≥0} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : MemLp f p μ :=
  ⟨hf, (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩
/-
**MeasureTheory.MemLp.of_enorm_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
emLp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {ε : Type u_5} {ε' : Type u_6}   [inst : TopologicalSpace ε] [inst_1 
: ContinuousENorm ε] [inst_2 : TopologicalSpace ε'] [inst_3 : ContinuousENorm ε'
]   {f : α → ε} {g : α → ε'} {c : NNReal},   MeasureTheory.MemLp g p μ →     Mea
sureTheory.AEStronglyMeasurable f μ → (∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ↑c * ‖g x‖ₑ) → Me
asureTheory.MemLp f p μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ↑c * ‖g x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'`：eLpNorm_le_n
nreal_smul_eLpNorm_of_ae_le_mul' {f : α -> ε} {g : α -> ε'} {c : Real>=0} (h : f
orallᵐ x ∂μ, ‖f x‖ₑ <= c * ‖g x‖ₑ) (p : Real>=0∞…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
theorem MemLp.of_enorm_le_mul
    {f : α → ε} {g : α → ε'} {c : ℝ≥0} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) : MemLp f p μ :=
  ⟨hf, (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩
/-
**MeasureTheory.MemLp.of_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} {m : MeasurableSpace α} {p 
: ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] [inst_1
 : NormedAddCommGroup F] {f : α → E} {g : α → F} {c : ℝ},   MeasureTheory.MemLp 
g p μ →     MeasureTheory.AEStronglyMeasurable f μ → (∀ᵐ (x : α) ∂μ, ‖f x‖ ≤ c *
 ‖g x‖) → MeasureTheory.MemLp f p μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ ≤ c * ‖g x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul`：eLpNorm_le_mul_eLpNor
m_of_ae_le_mul {f : α -> F} {g : α -> G} {c : Real} (h : forallᵐ x ∂μ, ‖f x‖ <= 
c * ‖g x‖) (p : Real>=0∞) : eLpNorm f p…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
theorem MemLp.of_le_mul {f : α → E} {g : α → F} {c : ℝ} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : MemLp f p μ :=
  ⟨hf,
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness)⟩

-- TODO: eventually, deprecate and remove the nnnorm version
/-
**MeasureTheory.MemLp.of_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`
。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {ε : Type u_5} {ε' : Type u_6}   [inst : TopologicalSpace ε] [inst_1 
: ContinuousENorm ε] [inst_2 : TopologicalSpace ε'] [inst_3 : ContinuousENorm ε'
]   {f : α → ε} {g : α → ε'} {c : NNReal},   MeasureTheory.MemLp g p μ →     Mea
sureTheory.AEStronglyMeasurable f μ → (∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ↑c * ‖g x‖ₑ) → Me
asureTheory.MemLp f p μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ↑c * ‖g x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul'`：eLpNorm_le_mul_eLpNo
rm_of_ae_le_mul' {f : α -> ε} {g : α -> ε'} {c : Real>=0} (h : forallᵐ x ∂μ, ‖f 
x‖ₑ <= c * ‖g x‖ₑ) (p : Real>=0∞) : eLpN…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
theorem MemLp.of_le_mul' {f : α → ε} {g : α → ε'} {c : ℝ≥0} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) : MemLp f p μ :=
  ⟨hf, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.coe_lt_top (by finiteness)⟩

end Monotonicity

/-
**MeasureTheory.le_eLpNorm_of_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：le_eLpNorm_of_bddBelow (hp : p != 0) (hp' : p != ∞) {f : α -> F} (C : Real
>=0) {s : Set α} (hs : MeasurableSet s) (hf : forallᵐ x ∂μ, x in s -> C <= ‖f x‖
₊) : C • μ s ^ (1 / p.toReal) <= eLpNorm f p μ
参数：hp : p != 0；hp' : p != ∞；C : Real>=0；hs : MeasurableSet s；hf : forallᵐ x ∂μ, 
x in s -> C <= ‖f x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.le_rpow_inv_iff`：le_rpow_inv_iff {x y : Real>=0∞} {z : Real} (hz
 : 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `MeasureTheory.setLIntegral_const`：setLIntegral_const (s : Set α) (c : Re
al>=0∞) : ∫⁻ _ in s, c ∂μ = c * μ s
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `coe_le_enorm`：∀ {E : Type u_8} [inst : NNNorm E] {x : E} {r : NNReal}, ↑
r ≤ ‖x‖ₑ ↔ r ≤ ‖x‖₊
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
（共 32 条，此处仅展示前 30 条）
-/
theorem le_eLpNorm_of_bddBelow (hp : p ≠ 0) (hp' : p ≠ ∞) {f : α → F} (C : ℝ≥0) {s : Set α}
    (hs : MeasurableSet s) (hf : ∀ᵐ x ∂μ, x ∈ s → C ≤ ‖f x‖₊) :
    C • μ s ^ (1 / p.toReal) ≤ eLpNorm f p μ := by
  rw [ENNReal.smul_def, smul_eq_mul, eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp',
    one_div, ENNReal.le_rpow_inv_iff (ENNReal.toReal_pos hp hp'),
    ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ (ENNReal.toReal_pos hp hp').ne', ENNReal.rpow_one, ← setLIntegral_const,
    ← lintegral_indicator hs]
  refine lintegral_mono_ae ?_
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem, hxs, true_implies] at hx ⊢
    gcongr
    rwa [coe_le_enorm]
  · simp [Set.indicator_of_notMem hxs]

section Star

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

@[simp]
/-
**MeasureTheory.eLpNorm_star** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_star {p : Real>=0∞} {f : α -> R} : eLpNorm (star f) p μ = eLpNorm 
f p μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_congr_norm_ae`：eLpNorm_congr_norm_ae {f : α -> F} 
{g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖ = ‖g x‖) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem eLpNorm_star {p : ℝ≥0∞} {f : α → R} : eLpNorm (star f) p μ = eLpNorm f p μ :=
  eLpNorm_congr_norm_ae <| .of_forall <| by simp

@[simp]
/-
**MeasureTheory.AEEqFun.eLpNorm_star** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AE
EqFun`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {R 
: Type u_5} [inst : NormedAddCommGroup R]   [inst_1 : StarAddMonoid R] [inst_2 :
 NormedStarGroup R] {p : ENNReal} {f : α →ₘ[μ] R},   MeasureTheory.eLpNorm (↑(st
ar f)) p μ = MeasureTheory.eLpNorm (↑f) p μ
参数：↑(star f)；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用引理 `MeasureTheory.AEEqFun.coeFn_star`：coeFn_star [Star R] [ContinuousStar R]
 (f : α ->ₘ[μ] R) : ↑(star f) =ᵐ[μ] (star f : α -> R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_star`：eLpNorm_star {p : Real>=0∞} {f : α -> R} : e
LpNorm (star f) p μ = eLpNorm f p μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem AEEqFun.eLpNorm_star {p : ℝ≥0∞} {f : α →ₘ[μ] R} : eLpNorm (star f : α →ₘ[μ] R) p μ =
    eLpNorm f p μ := eLpNorm_congr_ae (coeFn_star f) |>.trans <| by simp
/-
**MeasureTheory.MemLp.star** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {R 
: Type u_5} [inst : NormedAddCommGroup R]   [inst_1 : StarAddMonoid R] [NormedSt
arGroup R] {p : ENNReal} {f : α → R},   MeasureTheory.MemLp f p μ → MeasureTheor
y.MemLp (star f) p μ
参数：star f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.star`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {R : Type u_5} [inst : TopologicalSpace
 R]   [inst_1 : Star R] [Cont…
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_star`：eLpNorm_star {p : Real>=0∞} {f : α -> R} : e
LpNorm (star f) p μ = eLpNorm f p μ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem MemLp.star {p : ℝ≥0∞} {f : α → R} (hf : MemLp f p μ) : MemLp (star f) p μ :=
  ⟨hf.1.star, by simpa using hf.2⟩

end Star

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜}

/-
**MeasureTheory.eLpNorm_conj** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {𝕜 : Type u_5} [inst : RCLike 𝕜] 
(f : α → 𝕜) (p : ENNReal)   (μ : MeasureTheory.Measure α), MeasureTheory.eLpNorm
 ((starRingEnd (α → 𝕜)) f) p μ = MeasureTheory.eLpNorm f p μ
参数：f : α → 𝕜；p : ENNReal；μ : MeasureTheory.Measure α；(starRingEnd (α → 𝕜)) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma eLpNorm_conj (f : α → 𝕜) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (conj f) p μ = eLpNorm f p μ := by simp [← eLpNorm_norm]
/-
**MeasureTheory.MemLp.re** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {𝕜 : Type u_5} [inst : RCLike 𝕜]   {f : α → 𝕜}, MeasureTheory.MemLp f
 p μ → MeasureTheory.MemLp (fun x => RCLike.re (f x)) p μ
参数：fun x => RCLike.re (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `RCLike.norm_re_le_norm`：norm_re_le_norm (z : K) : ‖re z‖ <= ‖z‖
· 使用定理 `MeasureTheory.MemLp.of_le_mul`：∀ {α : Type u_1} {E : Type u_2} {F : Type
 u_3} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [ins
t : NormedAddCommGr…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `RCLike.continuous_re`：continuous_re : Continuous (re : K -> Real)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem MemLp.re (hf : MemLp f p μ) : MemLp (fun x => RCLike.re (f x)) p μ := by
  have : ∀ x, ‖RCLike.re (f x)‖ ≤ 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_re_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_re.comp_aestronglyMeasurable hf.1
/-
**MeasureTheory.MemLp.im** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {𝕜 : Type u_5} [inst : RCLike 𝕜]   {f : α → 𝕜}, MeasureTheory.MemLp f
 p μ → MeasureTheory.MemLp (fun x => RCLike.im (f x)) p μ
参数：fun x => RCLike.im (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `RCLike.norm_im_le_norm`：norm_im_le_norm (z : K) : ‖im z‖ <= ‖z‖
· 使用定理 `MeasureTheory.MemLp.of_le_mul`：∀ {α : Type u_1} {E : Type u_2} {F : Type
 u_3} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [ins
t : NormedAddCommGr…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `RCLike.continuous_im`：continuous_im : Continuous (im : K -> Real)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem MemLp.im (hf : MemLp f p μ) : MemLp (fun x => RCLike.im (f x)) p μ := by
  have : ∀ x, ‖RCLike.im (f x)‖ ≤ 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_im_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_im.comp_aestronglyMeasurable hf.1

end RCLike

end MeasureTheory

