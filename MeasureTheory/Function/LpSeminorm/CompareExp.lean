/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Eric Wieser
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Compare Lp seminorms for different values of `p`

In this file we compare `MeasureTheory.eLpNorm'` and `MeasureTheory.eLpNorm` for different
exponents.
-/

public section

open Filter ENNReal
open scoped Topology

namespace MeasureTheory

section SameSpace

variable {α ε ε' : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ε}
  [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

/-
**MeasureTheory.eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} {f : α → ε}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm 
ε] {p q : ℝ},   0 < p →     p ≤ q →       MeasureTheory.AEStronglyMeasurable f μ
 →         MeasureTheory.eLpNorm' f p μ ≤ MeasureTheory.eLpNorm' f q μ * μ Set.u
niv ^ (1 / p - 1 / q)
参数：1 / p - 1 / q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `MeasureTheory.lintegral_congr`：lintegral_congr {f g : α -> Real>=0∞} (h 
: forall a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm'_eq_lintegral_enorm`：∀ {α : Type u_1} {ε : Type u_
2} {m0 : MeasurableSpace α} [inst : ENorm ε] (f : α → ε) (q : ℝ)   (μ : MeasureT
heory.Measure α), MeasureTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
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
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
（共 53 条，此处仅展示前 30 条）
-/
theorem eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f p μ ≤ eLpNorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) := by
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hpq_eq : p = q
  · rw [hpq_eq, sub_self, ENNReal.rpow_zero, mul_one]
  have hpq : p < q := lt_of_le_of_ne hpq hpq_eq
  let g := fun _ : α => (1 : ℝ≥0∞)
  have h_rw : (∫⁻ a, ‖f a‖ₑ ^ p ∂μ) = ∫⁻ a, (‖f a‖ₑ * g a) ^ p ∂μ :=
    lintegral_congr fun a => by simp [g]
  repeat' rw [eLpNorm'_eq_lintegral_enorm]
  rw [h_rw]
  let r := p * q / (q - p)
  have hpqr : 1 / p = 1 / q + 1 / r := by simp [field]
  calc
    (∫⁻ a : α, (‖f a‖ₑ * g a) ^ p ∂μ) ^ (1 / p) ≤
        (∫⁻ a : α, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q) * (∫⁻ a : α, g a ^ r ∂μ) ^ (1 / r) :=
      ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.enorm aemeasurable_const
    _ = (∫⁻ a : α, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q) * μ Set.univ ^ (1 / p - 1 / q) := by
      rw [hpqr]; simp [r, g]
/-
**MeasureTheory.eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} {f : α → ε}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm 
ε] {q : ℝ},   0 < q → MeasureTheory.eLpNorm' f q μ ≤ MeasureTheory.eLpNormEssSup
 f μ * μ Set.univ ^ (1 / q)
参数：1 / q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.enorm_ae_le_eLpNormEssSup`：enorm_ae_le_eLpNormEssSup {_ : 
MeasurableSpace α} (f : α -> ε) (μ : Measure α) : forallᵐ x ∂μ, ‖f x‖ₑ <= eLpNor
mEssSup f μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'.eq_1`：∀ {α : Type u_1} {ε : Type u_2} [inst : ENo
rm ε] {x : MeasurableSpace α} (f : α → ε) (q : ℝ)   (μ : MeasureTheory.Measure α
), MeasureTheory.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
-/
theorem eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ {q : ℝ} (hq_pos : 0 < q) :
    eLpNorm' f q μ ≤ eLpNormEssSup f μ * μ Set.univ ^ (1 / q) := by
  have h_le : (∫⁻ a : α, ‖f a‖ₑ ^ q ∂μ) ≤ ∫⁻ _ : α, eLpNormEssSup f μ ^ q ∂μ := by
    refine lintegral_mono_ae ?_
    have h_nnnorm_le_eLpNorm_ess_sup := enorm_ae_le_eLpNormEssSup f μ
    exact h_nnnorm_le_eLpNorm_ess_sup.mono fun x hx => by gcongr
  rw [eLpNorm', ← ENNReal.rpow_one (eLpNormEssSup f μ)]
  nth_rw 2 [← mul_inv_cancel₀ (ne_of_lt hq_pos).symm]
  rw [ENNReal.rpow_mul, one_div, ← ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ q⁻¹)]
  gcongr
  rwa [lintegral_const] at h_le
/-
**MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：eLpNorm_le_eLpNorm_mul_rpow_measure_univ {p q : Real>=0∞} (hpq : p <= q) (
hf : AEStronglyMeasurable f μ) : eLpNorm f p μ <= eLpNorm f q μ * μ Set.univ ^ (
1 / p.toReal - 1 / q.toReal)
参数：hpq : p <= q；hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ`：∀ {α : Ty
pe u_1} {ε : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ε}   [inst : TopologicalSpace ε] [inst_1 : Co…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
（共 32 条，此处仅展示前 30 条）
-/
theorem eLpNorm_le_eLpNorm_mul_rpow_measure_univ {p q : ℝ≥0∞} (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ ≤ eLpNorm f q μ * μ Set.univ ^ (1 / p.toReal - 1 / q.toReal) := by
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  have hq0_lt : 0 < q := hp0.pos.trans_le hpq
  obtain rfl | hq_top := eq_or_ne q ∞
  · simp only [_root_.div_zero, one_div, ENNReal.toReal_top, sub_zero]
    obtain rfl | hp_top := eq_or_ne p ∞
    · simp
    rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
    refine (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hp_pos).trans (le_of_eq ?_)
    congr
    exact one_div _
  have hp_lt_top : p < ∞ := hpq.trans_lt (lt_top_iff_ne_top.mpr hq_top)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_lt_top.ne
  rw [eLpNorm_eq_eLpNorm' hp0 hp_lt_top.ne, eLpNorm_eq_eLpNorm' hq0_lt.ne.symm hq_top]
  have hpq_real : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq_top hpq
  exact eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp_pos hpq_real hf
/-
**MeasureTheory.eLpNorm'_le_eLpNorm'_of_exponent_le** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m : MeasurableSpace α} {f : α → ε} [inst 
: TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {p q : ℝ},   0 < p →     p 
≤ q →       ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ],         MeasureTheory.AEStronglyMeasurable f μ → MeasureTheory.eLpNorm' f p 
μ ≤ MeasureTheory.eLpNorm' f q μ
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ`：∀ {α : Type u_
1} {ε : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α →
 ε}   [inst : TopologicalSpace ε] [inst_1 : Co…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ENNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0∞) ^ x = 1
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
-/
theorem eLpNorm'_le_eLpNorm'_of_exponent_le {p q : ℝ} (hp0_lt : 0 < p)
    (hpq : p ≤ q) (μ : Measure α) [IsProbabilityMeasure μ] (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f p μ ≤ eLpNorm' f q μ := by
  have h_le_μ := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp0_lt hpq hf
  rwa [measure_univ, ENNReal.one_rpow, mul_one] at h_le_μ
/-
**MeasureTheory.eLpNorm'_le_eLpNormEssSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} {f : α → ε}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm 
ε] {q : ℝ},   0 < q → ∀ [MeasureTheory.IsProbabilityMeasure μ], MeasureTheory.eL
pNorm' f q μ ≤ MeasureTheory.eLpNormEssSup f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ`：∀ {α : Ty
pe u_1} {ε : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ε}   [inst : TopologicalSpace ε] [inst_1 : Co…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0∞) ^ x = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_le_eLpNormEssSup {q : ℝ} (hq_pos : 0 < q) [IsProbabilityMeasure μ] :
    eLpNorm' f q μ ≤ eLpNormEssSup f μ :=
  (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hq_pos).trans_eq (by simp [measure_univ])
/-
**MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：eLpNorm_le_eLpNorm_of_exponent_le {p q : Real>=0∞} (hpq : p <= q) [IsProba
bilityMeasure μ] (hf : AEStronglyMeasurable f μ) : eLpNorm f p μ <= eLpNorm f q 
μ
参数：hpq : p <= q；hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ`：eLpNorm_le_eLpNo
rm_mul_rpow_measure_univ {p q : Real>=0∞} (hpq : p <= q) (hf : AEStronglyMeasura
ble f μ) : eLpNorm f p μ <= eLpNorm f q μ * …
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0∞) ^ x = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm_le_eLpNorm_of_exponent_le {p q : ℝ≥0∞} (hpq : p ≤ q) [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) : eLpNorm f p μ ≤ eLpNorm f q μ :=
  (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf).trans (le_of_eq (by simp [measure_univ]))
/-
**MeasureTheory.eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} {f : α → ε}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm 
ε] {p q : ℝ} [MeasureTheory.IsFiniteMeasure μ],   MeasureTheory.AEStronglyMeasur
able f μ →     MeasureTheory.eLpNorm' f q μ < ⊤ → 0 ≤ p → p ≤ q → MeasureTheory.
eLpNorm' f p μ < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm'_exponent_zero`：∀ {α : Type u_1} {ε : Type u_2} {m
0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : ENorm ε] {f : α → ε
},   MeasureTheory.eLpNorm…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `MeasureTheory.eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ`：∀ {α : Type u_
1} {ε : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α →
 ε}   [inst : TopologicalSpace ε] [inst_1 : Co…
· 使用定理 `ENNReal.mul_lt_top_iff`：mul_lt_top_iff {a b : Real>=0∞} : a * b < ∞ ↔ a 
< ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用定理 `le_sub_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE α] [Add
LeftMono α] {a b c : α}, a ≤ b - c ↔ c ≤ b - a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `inv_le_inv₀`：inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le {p q : ℝ} [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) (hfq_lt_top : eLpNorm' f q μ < ∞) (hp_nonneg : 0 ≤ p)
    (hpq : p ≤ q) : eLpNorm' f p μ < ∞ := by
  rcases le_or_gt p 0 with hp_nonpos | hp_pos
  · rw [le_antisymm hp_nonpos hp_nonneg]
    simp
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  calc
    eLpNorm' f p μ ≤ eLpNorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) :=
      eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp_pos hpq hf
    _ < ∞ := by
      rw [ENNReal.mul_lt_top_iff]
      refine Or.inl ⟨hfq_lt_top, ENNReal.rpow_lt_top_of_nonneg ?_ (by finiteness)⟩
      rwa [le_sub_comm, sub_zero, one_div, one_div, inv_le_inv₀ hq_pos hp_pos]
/-
**MeasureTheory.MemLp.mono_exponent** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mem
Lp`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} {f : α → ε}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm 
ε] {p q : ENNReal} [MeasureTheory.IsFiniteMeasure μ],   MeasureTheory.MemLp f q 
μ → p ≤ q → MeasureTheory.MemLp f p μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.memLp_zero_iff_aestronglyMeasurable`：memLp_zero_iff_aestro
nglyMeasurable [TopologicalSpace ε] {f : α -> ε} : MemLp f 0 μ ↔ AEStronglyMeasu
rable f μ
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ`：∀ {α : Ty
pe u_1} {ε : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ε}   [inst : TopologicalSpace ε] [inst_1 : Co…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `MeasureTheory.eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le`：∀ {α : 
Type u_1} {ε : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {
f : α → ε}   [inst : TopologicalSpace ε] [inst_1 : Co…
-/
theorem MemLp.mono_exponent {p q : ℝ≥0∞} [IsFiniteMeasure μ] (hfq : MemLp f q μ)
    (hpq : p ≤ q) : MemLp f p μ := by
  obtain ⟨hfq_m, hfq_lt_top⟩ := hfq
  by_cases hp0 : p = 0
  · rwa [hp0, memLp_zero_iff_aestronglyMeasurable]
  rw [← Ne] at hp0
  refine ⟨hfq_m, ?_⟩
  by_cases hp_top : p = ∞
  · have hq_top : q = ∞ := by rwa [hp_top, top_le_iff] at hpq
    rw [hp_top]
    rwa [hq_top] at hfq_lt_top
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  by_cases hq_top : q = ∞
  · rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
    rw [hq_top, eLpNorm_exponent_top] at hfq_lt_top
    refine lt_of_le_of_lt (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hp_pos) ?_
    refine ENNReal.mul_lt_top hfq_lt_top ?_
    exact ENNReal.rpow_lt_top_of_nonneg (by simp [hp_pos.le]) (by finiteness)
  have hq0 : q ≠ 0 := by
    by_contra hq_eq_zero
    obtain rfl : p = 0 := le_antisymm (by rwa [hq_eq_zero] at hpq) zero_le
    rw [ENNReal.toReal_zero] at hp_pos
    exact (lt_irrefl _) hp_pos
  have hpq_real : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq_top hpq
  rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  rw [eLpNorm_eq_eLpNorm' hq0 hq_top] at hfq_lt_top
  exact eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le hfq_m hfq_lt_top hp_pos.le hpq_real

/-- If a function is supported on a finite-measure set and belongs to `ℒ^p`, then it belongs to
`ℒ^q` for any `q ≤ p`. -/
/-
**MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : TopologicalSpace ε']   [inst_1 : ESeminormedAddMonoid ε'] {
p q : ENNReal} {f : α → ε'},   MeasureTheory.MemLp f q μ → ∀ {s : Set α}, (∀ x ∉
 s, f x = 0) → μ s ≠ ⊤ → p ≤ q → MeasureTheory.MemLp f p μ
参数：∀ x ∉ s, f x = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.indicator_eq_self`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {
s : Set α} {f : α → M}, s.indicator f = f ↔ Function.support f ⊆ s
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.memLp_indicator_iff_restrict`：memLp_indicator_iff_restrict
 {f : α -> ε} (hs : MeasurableSet s) : MemLp (s.indicator f) p μ ↔ MemLp f p (μ.
restrict s)
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.MemLp.mono_exponent`：∀ {α : Type u_1} {ε : Type u_2} {m : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ε}   [inst : Topologic
alSpace ε] [inst_1 : Co…
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…

--- 原说明 ---
If a function is supported on a finite-measure set and belongs to `ℒ^p`, then it
 belongs to
`ℒ^q` for any `q ≤ p`.
-/
lemma MemLp.mono_exponent_of_measure_support_ne_top {p q : ℝ≥0∞} {f : α → ε'} (hfq : MemLp f q μ)
    {s : Set α} (hf : ∀ x, x ∉ s → f x = 0) (hs : μ s ≠ ∞) (hpq : p ≤ q) : MemLp f p μ := by
  have : (toMeasurable μ s).indicator f = f := by
    apply Set.indicator_eq_self.2
    apply Function.support_subset_iff'.2 fun x hx ↦ hf x ?_
    contrapose hx
    exact subset_toMeasurable μ s hx
  rw [← this, memLp_indicator_iff_restrict (measurableSet_toMeasurable μ s)] at hfq ⊢
  have : Fact (μ (toMeasurable μ s) < ∞) := ⟨by simpa [lt_top_iff_ne_top] using hs⟩
  exact hfq.mono_exponent hpq

end SameSpace

section Bilinear

variable {α E F G : Type*} {m : MeasurableSpace α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] {μ : Measure α}
  {f : α → E} {g : α → F}

open NNReal

/-
**MeasureTheory.eLpNorm_le_eLpNorm_top_mul_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：eLpNorm_le_eLpNorm_top_mul_eLpNorm (p : Real>=0∞) (f : α -> E) {g : α -> F
} (hg : AEStronglyMeasurable g μ) (b : E -> F -> G) (c : Real>=0) (h : forallᵐ x
 ∂μ, ‖b (f x) (g x)‖₊ <= c * ‖f x‖₊ * ‖g x‖₊) : eLpNorm (fun x => b (f x) (g x))
 p μ <= c * eLpNorm f ∞ μ * eLpNorm g p μ
参数：p : Real>=0∞；f : α -> E；hg : AEStronglyMeasurable g μ；b : E -> F -> G；c : Rea
l>=0；h : forallᵐ x ∂μ, ‖b (f x) (g x)‖₊ <= c * ‖f x‖₊ * ‖g x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_mono_ae_real`：eLpNorm_mono_ae_real {f : α -> F} {g
 : α -> Real} (h : forallᵐ x ∂μ, ‖f x‖ <= g x) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.eLpNorm_const_smul`：eLpNorm_const_smul (c : 𝕜) (f : α -> F
) (p : Real>=0∞) (μ : Measure α) : eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_norm`：eLpNorm_norm (f : α -> F) : eLpNorm (fun x =
> ‖f x‖) p μ = eLpNorm f p μ
· 使用定理 `enorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 : 
Mul α] [NormMulClass α] (a b : α), ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `enorm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), 
‖‖x‖‖ₑ = ‖x‖ₑ
· 使用定理 `ENNReal.essSup_mul_le`：essSup_mul_le (f g : α -> Real>=0∞) : essSup (f *
 g) μ <= essSup f μ * essSup g μ
（共 49 条，此处仅展示前 30 条）
-/
theorem eLpNorm_le_eLpNorm_top_mul_eLpNorm (p : ℝ≥0∞) (f : α → E) {g : α → F}
    (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) :
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ c * eLpNorm f ∞ μ * eLpNorm g p μ := by
  calc
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ eLpNorm (fun x => (c : ℝ) • ‖f x‖ * ‖g x‖) p μ :=
      eLpNorm_mono_ae_real h
    _ ≤ c * eLpNorm f ∞ μ * eLpNorm g p μ := ?_
  simp only [smul_mul_assoc, ← Pi.smul_def, eLpNorm_const_smul]
  rw [Real.enorm_eq_ofReal c.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_assoc]
  gcongr
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · simp
  · rw [← eLpNorm_norm f, ← eLpNorm_norm g]
    simp_rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm, enorm_mul, enorm_norm]
    exact ENNReal.essSup_mul_le (‖f ·‖ₑ) (‖g ·‖ₑ)
  obtain ⟨hp₁, hp₂⟩ := ENNReal.toReal_pos_iff.mp hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₁.ne' hp₂.ne, eLpNorm_exponent_top,
    eLpNormEssSup, one_div, ENNReal.rpow_inv_le_iff hp, enorm_mul, enorm_norm]
  rw [ENNReal.mul_rpow_of_nonneg (hz := hp.le), ENNReal.rpow_inv_rpow hp.ne',
    ← lintegral_const_mul'' _ (by fun_prop)]
  simp only [← ENNReal.mul_rpow_of_nonneg (hz := hp.le)]
  apply lintegral_mono_ae
  filter_upwards [h, enorm_ae_le_eLpNormEssSup f μ] with x hb hf
  gcongr
  exact hf
/-
**MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_top** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：eLpNorm_le_eLpNorm_mul_eLpNorm_top (p : Real>=0∞) {f : α -> E} (hf : AEStr
onglyMeasurable f μ) (g : α -> F) (b : E -> F -> G) (c : Real>=0) (h : forallᵐ x
 ∂μ, ‖b (f x) (g x)‖₊ <= c * ‖f x‖₊ * ‖g x‖₊) : eLpNorm (fun x => b (f x) (g x))
 p μ <= c * eLpNorm f p μ * eLpNorm g ∞ μ
参数：p : Real>=0∞；hf : AEStronglyMeasurable f μ；g : α -> F；b : E -> F -> G；c : Rea
l>=0；h : forallᵐ x ∂μ, ‖b (f x) (g x)‖₊ <= c * ‖f x‖₊ * ‖g x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_top_mul_eLpNorm`：eLpNorm_le_eLpNorm_top
_mul_eLpNorm (p : Real>=0∞) (f : α -> E) {g : α -> F} (hg : AEStronglyMeasurable
 g μ) (b : E -> F -> G) (c : Real>=0) …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm_top (p : ℝ≥0∞) {f : α → E} (hf : AEStronglyMeasurable f μ)
    (g : α → F) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) :
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ c * eLpNorm f p μ * eLpNorm g ∞ μ :=
  calc
    eLpNorm (fun x ↦ b (f x) (g x)) p μ ≤ c * eLpNorm g ∞ μ * eLpNorm f p μ :=
      eLpNorm_le_eLpNorm_top_mul_eLpNorm p g hf (flip b) c <| by
        convert! h using 3 with x
        simp only [mul_assoc, mul_comm ‖f x‖₊]
    _ = c * eLpNorm f p μ * eLpNorm g ∞ μ := by
      simp only [mul_assoc]; rw [mul_comm (eLpNorm _ _ _)]
/-
**MeasureTheory.eLpNorm'_le_eLpNorm'_mul_eLpNorm'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {m : Measura
bleSpace α} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] [ins
t_2 : NormedAddCommGroup G] {μ : MeasureTheory.Measure α} {f : α → E} {g : α → F
}   {p q r : ℝ},   MeasureTheory.AEStronglyMeasurable f μ →     MeasureTheory.AE
StronglyMeasurable g μ →       ∀ (b : E → F → G) (c : NNReal),         (∀ᵐ (x : 
α) ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) →           0 < r →             r
 < p →               1 / r = 1 / p + 1 / q →                 MeasureTheory.eLpNo
rm' (fun x => b (f x) (g x)) r μ ≤                   ↑c * MeasureTheory.eLpNorm'
 f p μ * MeasureTheory.eLpNorm' g q μ
参数：b : E → F → G；c : NNReal；∀ᵐ (x : α) ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖
₊；fun x => b (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nnnorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 :
 Mul α] [NormMulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNReal.nnnorm_eq`：∀ (x : NNReal), ‖↑x‖₊ = x
· 使用定理 `nnnorm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E),
 ‖‖x‖‖₊ = ‖x‖₊
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.eLpNorm'_const_smul`：∀ {α : Type u_1} {F : Type u_2} {m : 
MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α}   [inst : NormedAddComm
Group F] {𝕜 : Type u_3}…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 38 条，此处仅展示前 30 条）
-/
theorem eLpNorm'_le_eLpNorm'_mul_eLpNorm' {p q r : ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) (hro_lt : 0 < r) (hrp : r < p)
    (hpqr : 1 / r = 1 / p + 1 / q) :
    eLpNorm' (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm' f p μ * eLpNorm' g q μ := by
  calc
    eLpNorm' (fun x => b (f x) (g x)) r μ
      ≤ eLpNorm' (fun x ↦ (c : ℝ) • ‖f x‖ * ‖g x‖) r μ := by
      simp only [eLpNorm']
      gcongr ?_ ^ _
      refine lintegral_mono_ae <| h.mono fun a ha ↦ ?_
      gcongr
      simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
      simpa using! ha
    _ ≤ c * eLpNorm' f p μ * eLpNorm' g q μ := by
      simp only [smul_mul_assoc, ← Pi.smul_def, eLpNorm'_const_smul _ hro_lt]
      rw [Real.enorm_eq_ofReal c.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_assoc]
      gcongr
      simpa only [eLpNorm', enorm_mul, enorm_norm] using!
        ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hro_lt hrp hpqr μ hf.enorm hg.enorm

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
/-
**MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm {p q r : Real>=0∞} (hf : AEStrong
lyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (b : E -> F -> G) (c : Real>=0
) (h : forallᵐ x ∂μ, ‖b (f x) (g x)‖₊ <= c * ‖f x‖₊ * ‖g x‖₊) [hpqr : HolderTrip
le p q r] : eLpNorm (fun x => b (f x) (g x)) r μ <= c * eLpNorm f p μ * eLpNorm 
g q μ
参数：hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ；b : E -> F -> G；c
 : Real>=0；h : forallᵐ x ∂μ, ‖b (f x) (g x)‖₊ <= c * ‖f x‖₊ * ‖g x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ENNReal.HolderTriple.one_div_eq`：one_div_eq : 1 / r = 1 / p + 1 / q
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_top_mul_eLpNorm`：eLpNorm_le_eLpNorm_top
_mul_eLpNorm (p : Real>=0∞) (f : α -> E) {g : α -> F} (hg : AEStronglyMeasurable
 g μ) (b : E -> F -> G) (c : Real>=0) …
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_top`：eLpNorm_le_eLpNorm_mul
_eLpNorm_top (p : Real>=0∞) {f : α -> E} (hf : AEStronglyMeasurable f μ) (g : α 
-> F) (b : E -> F -> G) (c : Real>=0) …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise ope
ration
`fun x => b (f x) (g x)`.
-/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm {p q r : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) [hpqr : HolderTriple p q r] :
    eLpNorm (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm f p μ * eLpNorm g q μ := by
  have hpqr := hpqr.one_div_eq
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · simp_all
  · have : r = q := by simpa using hpqr
    exact this ▸ eLpNorm_le_eLpNorm_top_mul_eLpNorm r f hg b c h
  obtain (rfl | rfl | hq) := ENNReal.trichotomy q
  · simp_all
  · have : r = p := by simpa using hpqr
    exact this ▸ eLpNorm_le_eLpNorm_mul_eLpNorm_top p hf g b c h
  obtain ⟨hp₁, hp₂⟩ := ENNReal.toReal_pos_iff.mp hp
  obtain ⟨hq₁, hq₂⟩ := ENNReal.toReal_pos_iff.mp hq
  have hpqr' : 1 / r.toReal = 1 / p.toReal + 1 / q.toReal := by
    have := congr(ENNReal.toReal $(hpqr))
    rw [ENNReal.toReal_add (by simpa using hp₁.ne') (by simpa using hq₁.ne')] at this
    simpa
  have hr : 0 < r.toReal := one_div_pos.mp <| by rw [hpqr']; positivity
  obtain ⟨hr₁, hr₂⟩ := ENNReal.toReal_pos_iff.mp hr
  have hrp : r.toReal < p.toReal := lt_of_one_div_lt_one_div hp <|
    hpqr' ▸ lt_add_of_pos_right _ (by positivity)
  rw [eLpNorm_eq_eLpNorm', eLpNorm_eq_eLpNorm', eLpNorm_eq_eLpNorm']
  · exact eLpNorm'_le_eLpNorm'_mul_eLpNorm' hf hg b c h hr hrp hpqr'
  all_goals first | positivity | finiteness

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
/-
**MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {m : Measura
bleSpace α} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] [ins
t_2 : NormedAddCommGroup G] {μ : MeasureTheory.Measure α} {f : α → E} {g : α → F
}   {p q r : ENNReal},   MeasureTheory.AEStronglyMeasurable f μ →     MeasureThe
ory.AEStronglyMeasurable g μ →       ∀ (b : E → F → G) (c : NNReal),         (∀ᵐ
 (x : α) ∂μ, ‖b (f x) (g x)‖ ≤ ↑c * ‖f x‖ * ‖g x‖) →           ∀ [hpqr : p.Holde
rTriple q r],             MeasureTheory.eLpNorm (fun x => b (f x) (g x)) r μ ≤  
             ↑c * MeasureTheory.eLpNorm f p μ * MeasureTheory.eLpNorm g q μ
参数：b : E → F → G；c : NNReal；∀ᵐ (x : α) ∂μ, ‖b (f x) (g x)‖ ≤ ↑c * ‖f x‖ * ‖g x‖；
fun x => b (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm`：eLpNorm_le_eLpNo
rm_mul_eLpNorm_of_nnnorm {p q r : Real>=0∞} (hf : AEStronglyMeasurable f μ) (hg 
: AEStronglyMeasurable g μ) (b : E -> F -> G…

--- 原说明 ---
Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise ope
ration
`fun x => b (f x) (g x)`.
-/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm {p q r : ℝ≥0∞} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ ≤ c * ‖f x‖ * ‖g x‖) [hpqr : HolderTriple p q r] :
    eLpNorm (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm f p μ * eLpNorm g q μ :=
  eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg b c h

open NNReal in
/-
**MeasureTheory.MemLp.of_bilin** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} {m : Measura
bleSpace α} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] [ins
t_2 : NormedAddCommGroup G] {μ : MeasureTheory.Measure α} {p q r : ENNReal}   {f
 : α → E} {g : α → F} (b : E → F → G) (c : NNReal),   MeasureTheory.MemLp f p μ 
→     MeasureTheory.MemLp g q μ →       MeasureTheory.AEStronglyMeasurable (fun 
x => b (f x) (g x)) μ →         (∀ᵐ (x : α) ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * 
‖g x‖₊) →           ∀ [hpqr : p.HolderTriple q r], MeasureTheory.MemLp (fun x =>
 b (f x) (g x)) r μ
参数：b : E → F → G；c : NNReal；fun x => b (f x) (g x)；∀ᵐ (x : α) ∂μ, ‖b (f x) (g x)
‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊；fun x => b (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm`：eLpNorm_le_eLpNo
rm_mul_eLpNorm_of_nnnorm {p q r : Real>=0∞} (hf : AEStronglyMeasurable f μ) (hg 
: AEStronglyMeasurable g μ) (b : E -> F -> G…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
theorem MemLp.of_bilin {p q r : ℝ≥0∞} {f : α → E} {g : α → F} (b : E → F → G) (c : ℝ≥0)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (h : AEStronglyMeasurable (fun x ↦ b (f x) (g x)) μ)
    (hb : ∀ᵐ (x : α) ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊)
    [hpqr : HolderTriple p q r] :
    MemLp (fun x ↦ b (f x) (g x)) r μ := by
  refine ⟨h, ?_⟩
  apply (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf.1 hg.1 b c hb (hpqr := hpqr)).trans_lt
  finiteness [hf.2, hg.2]

end Bilinear

section IsBoundedSMul

variable {𝕜 α E F : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedRing 𝕜]
  [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]
  [NormedAddCommGroup F] [MulActionWithZero 𝕜 F] [IsBoundedSMul 𝕜 F] {f : α → E}

/-
**MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (p : Real>=0∞) (hf : AEStronglyMea
surable f μ) (φ : α -> 𝕜) : eLpNorm (φ • f) p μ <= eLpNorm φ ∞ μ * eLpNorm f p μ
参数：p : Real>=0∞；hf : AEStronglyMeasurable f μ；φ : α -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_top_mul_eLpNorm`：eLpNorm_le_eLpNorm_top
_mul_eLpNorm (p : Real>=0∞) (f : α -> E) {g : α -> F} (hg : AEStronglyMeasurable
 g μ) (b : E -> F -> G) (c : Real>=0) …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `nnnorm_smul_le`：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
-/
theorem eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (p : ℝ≥0∞) (hf : AEStronglyMeasurable f μ)
    (φ : α → 𝕜) : eLpNorm (φ • f) p μ ≤ eLpNorm φ ∞ μ * eLpNorm f p μ := by
  simpa using! (eLpNorm_le_eLpNorm_top_mul_eLpNorm p φ hf (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) :)
/-
**MeasureTheory.eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top (p : Real>=0∞) (f : α -> E) {φ : α
 -> 𝕜} (hφ : AEStronglyMeasurable φ μ) : eLpNorm (φ • f) p μ <= eLpNorm φ p μ * 
eLpNorm f ∞ μ
参数：p : Real>=0∞；f : α -> E；hφ : AEStronglyMeasurable φ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_top`：eLpNorm_le_eLpNorm_mul
_eLpNorm_top (p : Real>=0∞) {f : α -> E} (hf : AEStronglyMeasurable f μ) (g : α 
-> F) (b : E -> F -> G) (c : Real>=0) …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nnnorm_smul_le`：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
-/
theorem eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top (p : ℝ≥0∞) (f : α → E) {φ : α → 𝕜}
    (hφ : AEStronglyMeasurable φ μ) : eLpNorm (φ • f) p μ ≤ eLpNorm φ p μ * eLpNorm f ∞ μ := by
  simpa using! (eLpNorm_le_eLpNorm_mul_eLpNorm_top p hφ f (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) :)
/-
**MeasureTheory.eLpNorm'_smul_le_mul_eLpNorm'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [inst_1 : NormedAddCommGroup 
E] [inst_2 : MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E] {p q r : ℝ}   {f : α → E
},   MeasureTheory.AEStronglyMeasurable f μ →     ∀ {φ : α → 𝕜},       MeasureTh
eory.AEStronglyMeasurable φ μ →         0 < p →           p < q →             1 
/ p = 1 / q + 1 / r →               MeasureTheory.eLpNorm' (φ • f) p μ ≤ Measure
Theory.eLpNorm' φ q μ * MeasureTheory.eLpNorm' f r μ
参数：φ • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.eLpNorm'_le_eLpNorm'_mul_eLpNorm'`：∀ {α : Type u_1} {E : T
ype u_2} {F : Type u_3} {G : Type u_4} {m : MeasurableSpace α} [inst : NormedAdd
CommGroup E]   [inst_1 : NormedAddCom…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `nnnorm_smul_le`：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
-/
theorem eLpNorm'_smul_le_mul_eLpNorm' {p q r : ℝ} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {φ : α → 𝕜} (hφ : AEStronglyMeasurable φ μ) (hp0_lt : 0 < p) (hpq : p < q)
    (hpqr : 1 / p = 1 / q + 1 / r) : eLpNorm' (φ • f) p μ ≤ eLpNorm' φ q μ * eLpNorm' f r μ := by
  simpa using! eLpNorm'_le_eLpNorm'_mul_eLpNorm' hφ hf (· • ·) 1
    (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _)
    hp0_lt hpq hpqr

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of a scalar product `φ • f`. -/
/-
**MeasureTheory.eLpNorm_smul_le_mul_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：eLpNorm_smul_le_mul_eLpNorm {p q r : Real>=0∞} {f : α -> E} (hf : AEStrong
lyMeasurable f μ) {φ : α -> 𝕜} (hφ : AEStronglyMeasurable φ μ) [hpqr : HolderTri
ple p q r] : eLpNorm (φ • f) r μ <= eLpNorm φ p μ * eLpNorm f q μ
参数：hf : AEStronglyMeasurable f μ；hφ : AEStronglyMeasurable φ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm`：eLpNorm_le_eLpNo
rm_mul_eLpNorm_of_nnnorm {p q r : Real>=0∞} (hf : AEStronglyMeasurable f μ) (hg 
: AEStronglyMeasurable g μ) (b : E -> F -> G…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `nnnorm_smul_le`：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊

--- 原说明 ---
Hölder's inequality, as an inequality on the `ℒp` seminorm of a scalar product `
φ • f`.
-/
theorem eLpNorm_smul_le_mul_eLpNorm {p q r : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {φ : α → 𝕜} (hφ : AEStronglyMeasurable φ μ) [hpqr : HolderTriple p q r] :
    eLpNorm (φ • f) r μ ≤ eLpNorm φ p μ * eLpNorm f q μ := by
  simpa using! (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hφ hf (· • ·) 1
      (.of_forall fun _ => by simpa using! nnnorm_smul_le _ _) : _)
/-
**MeasureTheory.MemLp.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [inst_1 : NormedAddCommGroup 
E] [inst_2 : MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]   {p q r : ENNReal} {f :
 α → E} {φ : α → 𝕜},   MeasureTheory.MemLp f q μ → MeasureTheory.MemLp φ p μ → ∀
 [hpqr : p.HolderTriple q r], MeasureTheory.MemLp (φ • f) r μ
参数：φ • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_smul_le_mul_eLpNorm`：eLpNorm_smul_le_mul_eLpNorm {
p q r : Real>=0∞} {f : α -> E} (hf : AEStronglyMeasurable f μ) {φ : α -> 𝕜} (hφ 
: AEStronglyMeasurable φ μ) [hp…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `MeasureTheory.MemLp.eLpNorm_lt_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
theorem MemLp.smul {p q r : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : MemLp f q μ) (hφ : MemLp φ p μ)
    [hpqr : HolderTriple p q r] : MemLp (φ • f) r μ :=
  ⟨hφ.1.smul hf.1,
    eLpNorm_smul_le_mul_eLpNorm hf.1 hφ.1 |>.trans_lt <|
      ENNReal.mul_lt_top hφ.eLpNorm_lt_top hf.eLpNorm_lt_top⟩

end IsBoundedSMul

section Mul

variable {α : Type*} {_ : MeasurableSpace α} {𝕜 : Type*} [NormedRing 𝕜] {μ : Measure α}
  {p q r : ℝ≥0∞} {f : α → 𝕜} {φ : α → 𝕜}

/-
**MeasureTheory.MemLp.mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {𝕜 : Type u_2} [inst : NormedRing
 𝕜] {μ : MeasureTheory.Measure α}   {p q r : ENNReal} {f φ : α → 𝕜},   MeasureTh
eory.MemLp f q μ → MeasureTheory.MemLp φ p μ → ∀ [hpqr : p.HolderTriple q r], Me
asureTheory.MemLp (φ * f) r μ
参数：φ * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3}
 {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [
inst_1 : Norme…
-/
theorem MemLp.mul (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r] :
    MemLp (φ * f) r μ :=
  MemLp.smul hf hφ

/-- Variant of `MemLp.mul` where the function is written as `fun x ↦ φ x * f x`
instead of `φ * f`. -/
/-
**MeasureTheory.MemLp.mul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {x : MeasurableSpace α} {𝕜 : Type u_2} [inst : NormedRing
 𝕜] {μ : MeasureTheory.Measure α}   {p q r : ENNReal} {f φ : α → 𝕜},   MeasureTh
eory.MemLp f q μ →     MeasureTheory.MemLp φ p μ → ∀ [hpqr : p.HolderTriple q r]
, MeasureTheory.MemLp (fun x => φ x * f x) r μ
参数：fun x => φ x * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3}
 {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [
inst_1 : Norme…

--- 原说明 ---
Variant of `MemLp.mul` where the function is written as `fun x ↦ φ x * f x`
instead of `φ * f`.
-/
theorem MemLp.mul' (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r] :
    MemLp (fun x ↦ φ x * f x) r μ :=
  MemLp.smul hf hφ

end Mul

section Prod
variable {ι α 𝕜 : Type*} {_ : MeasurableSpace α} [NormedCommRing 𝕜] {μ : Measure α} {f : ι → α → 𝕜}
  {p : ι → ℝ≥0∞} {s : Finset ι}

open Finset in
/-- See `MemLp.prod'` for the applied version. -/
/-
**MeasureTheory.MemLp.prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {𝕜 : Type u_3} {x : MeasurableSpace α} [in
st : NormedCommRing 𝕜]   {μ : MeasureTheory.Measure α} {f : ι → α → 𝕜} {p : ι → 
ENNReal} {s : Finset ι},   (∀ i ∈ s, MeasureTheory.MemLp (f i) (p i) μ) → Measur
eTheory.MemLp (∏ i ∈ s, f i) (∑ i ∈ s, (p i)⁻¹)⁻¹ μ
参数：∀ i ∈ s, MeasureTheory.MemLp (f i) (p i) μ；∏ i ∈ s, f i；∑ i ∈ s, (p i)⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNormEssSup_const`：eLpNormEssSup_const (c : ε) (hμ : μ !
= 0) : eLpNormEssSup (fun _ : α => c) μ = ‖c‖ₑ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `MeasureTheory.MemLp.mul`：∀ {α : Type u_1} {x : MeasurableSpace α} {𝕜 : T
ype u_2} [inst : NormedRing 𝕜] {μ : MeasureTheory.Measure α}   {p q r : ENNReal}
 {f φ : α → 𝕜…
· 使用定理 `Finset.forall_of_forall_cons`：forall_of_forall_cons {p : α -> Prop} {h :
 a ∉ s} (H : forall x, x in cons a s h -> p x) (x) (h : x in s) : p x
· 使用定理 `Finset.mem_cons_self`：mem_cons_self (a : α) (s : Finset α) {h} : a in co
ns a s h
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See `MemLp.prod'` for the applied version.
-/
protected lemma MemLp.prod (hf : ∀ i ∈ s, MemLp (f i) (p i) μ) :
    MemLp (∏ i ∈ s, f i) (∑ i ∈ s, (p i)⁻¹)⁻¹ μ := by
  induction s using cons_induction with
  | empty =>
    by_cases hμ : μ = 0 <;>
      simp [MemLp, eLpNormEssSup_const, hμ, aestronglyMeasurable_const, Pi.one_def]
  | cons i s hi ih =>
    rw [prod_cons]
    exact (ih <| forall_of_forall_cons hf).mul (hf i <| mem_cons_self ..) (hpqr := ⟨by simp⟩)

/-- See `MemLp.prod` for the unapplied version. -/
/-
**MeasureTheory.MemLp.prod'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {𝕜 : Type u_3} {x : MeasurableSpace α} [in
st : NormedCommRing 𝕜]   {μ : MeasureTheory.Measure α} {f : ι → α → 𝕜} {p : ι → 
ENNReal} {s : Finset ι},   (∀ i ∈ s, MeasureTheory.MemLp (f i) (p i) μ) → Measur
eTheory.MemLp (fun ω => ∏ i ∈ s, f i ω) (∑ i ∈ s, (p i)⁻¹)⁻¹ μ
参数：∀ i ∈ s, MeasureTheory.MemLp (f i) (p i) μ；fun ω => ∏ i ∈ s, f i ω；∑ i ∈ s, (
p i)⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_fn`：Finset.prod_fn {α : Type*} {M : α -> Type*} {ι} [forall 
a, CommMonoid (M a)] (s : Finset ι) (g : ι -> forall a, M a) : ∏ c in s, g c = f
un a…
· 使用定理 `MeasureTheory.MemLp.prod`：∀ {ι : Type u_1} {α : Type u_2} {𝕜 : Type u_3}
 {x : MeasurableSpace α} [inst : NormedCommRing 𝕜]   {μ : MeasureTheory.Measure 
α} {f : ι → α …

--- 原说明 ---
See `MemLp.prod` for the unapplied version.
-/
protected lemma MemLp.prod' (hf : ∀ i ∈ s, MemLp (f i) (p i) μ) :
    MemLp (fun ω ↦ ∏ i ∈ s, f i ω) (∑ i ∈ s, (p i)⁻¹)⁻¹ μ := by
  simpa [Finset.prod_fn] using MemLp.prod hf

end Prod
end MeasureTheory

