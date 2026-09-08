/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Chebyshev-Markov inequality in terms of Lp seminorms

In this file we formulate several versions of the Chebyshev-Markov inequality
in terms of the `MeasureTheory.eLpNorm` seminorm.
-/

public section
open scoped NNReal ENNReal

namespace MeasureTheory

variable {α E ε' : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E]
  [TopologicalSpace ε'] [ContinuousENorm ε']
  {p : ℝ≥0∞} (μ : Measure α)

/-
**MeasureTheory.pow_mul_meas_ge_le_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：pow_mul_meas_ge_le_eLpNorm (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f :
 α -> ε'} (hf : AEStronglyMeasurable f μ) (ε : Real>=0∞) : (ε * μ { x | ε <= ‖f 
x‖ₑ ^ p.toReal }) ^ (1 / p.toReal) <= eLpNorm f p μ
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞；hf : AEStronglyMeasurable f μ；ε : Real
>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `MeasureTheory.mul_meas_ge_le_lintegral₀`：mul_meas_ge_le_lintegral₀ {f : 
α -> Real>=0∞} (hf : AEMeasurable f μ) (ε : Real>=0∞) : ε * μ { x | ε <= f x } <
= ∫⁻ a, f a ∂μ
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
theorem pow_mul_meas_ge_le_eLpNorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    {f : α → ε'} (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    (ε * μ { x | ε ≤ ‖f x‖ₑ ^ p.toReal }) ^ (1 / p.toReal) ≤ eLpNorm f p μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]
  gcongr
  exact mul_meas_ge_le_lintegral₀ (hf.enorm.pow_const _) ε
/-
**MeasureTheory.mul_meas_ge_le_pow_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：mul_meas_ge_le_pow_eLpNorm (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f :
 α -> ε'} (hf : AEStronglyMeasurable f μ) (ε : Real>=0∞) : ε * μ { x | ε <= ‖f x
‖ₑ ^ p.toReal } <= eLpNorm f p μ ^ p.toReal
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞；hf : AEStronglyMeasurable f μ；ε : Real
>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `one_div_mul_cancel`：one_div_mul_cancel (h : a != 0) : 1 / a * a = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ENNReal.toReal_eq_zero_iff`：toReal_eq_zero_iff (x : Real>=0∞) : x.toReal
 = 0 ↔ x = 0 ∨ x = ∞
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `MeasureTheory.pow_mul_meas_ge_le_eLpNorm`：pow_mul_meas_ge_le_eLpNorm (hp
_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε'} (hf : AEStronglyMeasurable
 f μ) (ε : Real>=0∞) : (ε * μ …
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
theorem mul_meas_ge_le_pow_eLpNorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    {f : α → ε'} (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ ‖f x‖ₑ ^ p.toReal } ≤ eLpNorm f p μ ^ p.toReal := by
  have : 1 / p.toReal * p.toReal = 1 := by
    refine one_div_mul_cancel ?_
    rw [Ne, ENNReal.toReal_eq_zero_iff]
    exact not_or_intro hp_ne_zero hp_ne_top
  rw [← ENNReal.rpow_one (ε * μ { x | ε ≤ ‖f x‖ₑ ^ p.toReal }), ← this, ENNReal.rpow_mul]
  gcongr
  exact pow_mul_meas_ge_le_eLpNorm μ hp_ne_zero hp_ne_top hf ε

/-- A version of Chebyshev-Markov's inequality using Lp-norms. -/
/-
**MeasureTheory.mul_meas_ge_le_pow_eLpNorm'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：mul_meas_ge_le_pow_eLpNorm' (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f 
: α -> ε'} (hf : AEStronglyMeasurable f μ) (ε : Real>=0∞) : ε ^ p.toReal * μ { x
 | ε <= ‖f x‖ₑ } <= eLpNorm f p μ ^ p.toReal
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞；hf : AEStronglyMeasurable f μ；ε : Real
>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_le_rpow_iff`：rpow_le_rpow_iff {x y : Real>=0∞} {z : Real} (
hz : 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.mul_meas_ge_le_pow_eLpNorm`：mul_meas_ge_le_pow_eLpNorm (hp
_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε'} (hf : AEStronglyMeasurable
 f μ) (ε : Real>=0∞) : ε * μ {…

--- 原说明 ---
A version of Chebyshev-Markov's inequality using Lp-norms.
-/
theorem mul_meas_ge_le_pow_eLpNorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    {f : α → ε'} (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε ^ p.toReal * μ { x | ε ≤ ‖f x‖ₑ } ≤ eLpNorm f p μ ^ p.toReal := by
  convert! mul_meas_ge_le_pow_eLpNorm μ hp_ne_zero hp_ne_top hf (ε ^ p.toReal) using 4
  ext x
  rw [ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
/-
**MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：meas_ge_le_mul_pow_eLpNorm_enorm (hp_ne_zero : p != 0) (hp_ne_top : p != ∞
) {f : α -> ε'} (hf : AEStronglyMeasurable f μ) {ε : Real>=0∞} (hε : ε != 0) (hm
eas_top : ε = ∞ -> μ {x | ‖f x‖ₑ = ⊤} = 0) : μ { x | ε <= ‖f x‖ₑ } <= ε⁻¹ ^ p.to
Real * eLpNorm f p μ ^ p.toReal
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞；hf : AEStronglyMeasurable f μ；hε : ε !
= 0；hmeas_top : ε = ∞ -> μ {x | ‖f x‖ₑ = ⊤} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.rpow_pos`：rpow_pos {p : Real} {x : Real>=0∞} (hx_pos : 0 < x) (h
x_ne_top : x != ⊤) : 0 < x ^ p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.rpow_ne_top_of_nonneg'`：rpow_ne_top_of_nonneg' {y : Real} {x : R
eal>=0∞} (hx : 0 < x) (hx' : x != ⊤) : x ^ y != ⊤
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `ENNReal.inv_rpow`：inv_rpow (x : Real>=0∞) (y : Real) : x⁻¹ ^ y = (x ^ y)
⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.mul_le_mul_iff_right`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * 
b ≤ a * c ↔ b ≤ c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.mul_meas_ge_le_pow_eLpNorm'`：mul_meas_ge_le_pow_eLpNorm' (
hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε'} (hf : AEStronglyMeasurab
le f μ) (ε : Real>=0∞) : ε ^ p.…
-/
theorem meas_ge_le_mul_pow_eLpNorm_enorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    {f : α → ε'} (hf : AEStronglyMeasurable f μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (hmeas_top : ε = ∞ → μ {x | ‖f x‖ₑ = ⊤} = 0) :
    μ { x | ε ≤ ‖f x‖ₑ } ≤ ε⁻¹ ^ p.toReal * eLpNorm f p μ ^ p.toReal := by
  by_cases h : ε = ∞
  · have : (0 : ℝ≥0∞) ^ p.toReal = 0 := by
      rw [ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
    simp [h, this, hmeas_top]
  · have hεpow : ε ^ p.toReal ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hε) h).ne.symm
    have hεpow' : ε ^ p.toReal ≠ ∞ := by finiteness
    rw [ENNReal.inv_rpow, ← ENNReal.mul_le_mul_iff_right hεpow hεpow', ← mul_assoc,
      ENNReal.mul_inv_cancel hεpow hεpow', one_mul]
    exact mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top hf ε
/-
**MeasureTheory.MemLp.meas_ge_lt_top'_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.MemLp`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_3} {m0 : MeasurableSpace α} [inst : Topologi
calSpace ε'] [inst_1 : ContinuousENorm ε']   {p : ENNReal} {μ : MeasureTheory.Me
asure α} {f : α → ε'},   MeasureTheory.MemLp f p μ →     p ≠ 0 → p ≠ ⊤ → ∀ {ε : 
ENNReal}, ε ≠ 0 → (ε = ⊤ → μ {x | ‖f x‖ₑ = ⊤} = 0) → μ {x | ε ≤ ‖f x‖ₑ} < ⊤
参数：ε = ⊤ → μ {x | ‖f x‖ₑ = ⊤} = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm`：meas_ge_le_mul_pow_eLpNo
rm_enorm (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε'} (hf : AEStrong
lyMeasurable f μ) {ε : Real>=0∞} (hε…
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.MemLp.eLpNorm_lt_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
theorem MemLp.meas_ge_lt_top'_enorm {μ : Measure α} {f : α → ε'} (hℒp : MemLp f p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε = ∞ → μ {x | ‖f x‖ₑ = ⊤} = 0) :
    μ { x | ε ≤ ‖f x‖ₑ } < ∞ := by
  apply meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top hℒp.aestronglyMeasurable hε hε'
    |>.trans_lt (ENNReal.mul_lt_top ?_ ?_)
  · simp [hε, lt_top_iff_ne_top]
  · simp [hℒp.eLpNorm_lt_top.ne, lt_top_iff_ne_top]
/-
**MeasureTheory.MemLp.meas_ge_lt_top'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
emLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} {f : α → E},   Measur
eTheory.MemLp f p μ → p ≠ 0 → p ≠ ⊤ → ∀ {ε : ENNReal}, ε ≠ 0 → μ {x | ε ≤ ↑‖f x‖
₊} < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.meas_ge_lt_top'_enorm`：∀ {α : Type u_1} {ε' : Type u
_3} {m0 : MeasurableSpace α} [inst : TopologicalSpace ε'] [inst_1 : ContinuousEN
orm ε']   {p : ENNReal} {μ : Me…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem MemLp.meas_ge_lt_top' {μ : Measure α} {f : α → E} (hℒp : MemLp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖₊ } < ∞ := by
  by_cases h : ε = ∞
  · simp [h]
  exact hℒp.meas_ge_lt_top'_enorm hp_ne_zero hp_ne_top hε (by simp)
/-
**MeasureTheory.MemLp.meas_ge_lt_top_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.MemLp`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_3} {m0 : MeasurableSpace α} [inst : Topologi
calSpace ε'] [inst_1 : ContinuousENorm ε']   {p : ENNReal} {μ : MeasureTheory.Me
asure α} {f : α → ε'},   MeasureTheory.MemLp f p μ → p ≠ 0 → p ≠ ⊤ → ∀ {ε : NNRe
al}, ε ≠ 0 → μ {x | ↑ε ≤ ‖f x‖ₑ} < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.meas_ge_lt_top'_enorm`：∀ {α : Type u_1} {ε' : Type u
_3} {m0 : MeasurableSpace α} [inst : TopologicalSpace ε'] [inst_1 : ContinuousEN
orm ε']   {p : ENNReal} {μ : Me…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem MemLp.meas_ge_lt_top_enorm {μ : Measure α} {f : α → ε'} (hℒp : MemLp f p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {ε : ℝ≥0} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖ₑ } < ∞ :=
  hℒp.meas_ge_lt_top'_enorm hp_ne_zero hp_ne_top (by simp [hε]) (by simp)
/-
**MeasureTheory.MemLp.meas_ge_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
mLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} [inst : NormedAdd
CommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} {f : α → E},   Measur
eTheory.MemLp f p μ → p ≠ 0 → p ≠ ⊤ → ∀ {ε : NNReal}, ε ≠ 0 → μ {x | ε ≤ ‖f x‖₊}
 < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.MemLp.meas_ge_lt_top'`：∀ {α : Type u_1} {E : Type u_2} {m0
 : MeasurableSpace α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : Measure
Theory.Measure α} {f : α …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem MemLp.meas_ge_lt_top {μ : Measure α} {f : α → E} (hℒp : MemLp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) {ε : ℝ≥0} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖₊ } < ∞ := by
  simp_rw [← ENNReal.coe_le_coe]
  apply hℒp.meas_ge_lt_top' hp_ne_zero hp_ne_top (by simp [hε])

end MeasureTheory

