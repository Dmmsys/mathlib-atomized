/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Triangle inequality for `Lp`-seminorm

In this file we prove several versions of the triangle inequality for the `Lp` seminorm,
as well as simple corollaries.
-/

public section

open Filter ENNReal
open scoped Topology

namespace MeasureTheory

variable {α E ε ε' : Type*} {m : MeasurableSpace α} [NormedAddCommGroup E]
  [TopologicalSpace ε] [ESeminormedAddMonoid ε] [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε']
  {p : ℝ≥0∞} {q : ℝ} {μ : Measure α} {f g : α → ε}

/-
**MeasureTheory.eLpNorm'_add_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {m : MeasurableSpace α} [inst : Topologica
lSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {q : ℝ} {μ : MeasureTheory.Measure
 α} {f g : α → ε},   MeasureTheory.AEStronglyMeasurable f μ →     MeasureTheory.
AEStronglyMeasurable g μ →       1 ≤ q → MeasureTheory.eLpNorm' (f + g) q μ ≤ Me
asureTheory.eLpNorm' f q μ + MeasureTheory.eLpNorm' g q μ
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ENNReal.lintegral_Lp_add_le`：lintegral_Lp_add_le {p : Real} {f g : α -> 
Real>=0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hp1 : 1 <= p) : (∫⁻ a
, (f + g) a ^ p ∂…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
-/
theorem eLpNorm'_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hq1 : 1 ≤ q) : eLpNorm' (f + g) q μ ≤ eLpNorm' f q μ + eLpNorm' g q μ :=
  calc
    (∫⁻ a, ‖(f + g) a‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (∫⁻ a, ((‖f ·‖ₑ) + (‖g ·‖ₑ)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, enorm_add_le]
    _ ≤ eLpNorm' f q μ + eLpNorm' g q μ := ENNReal.lintegral_Lp_add_le hf.enorm hg.enorm hq1
/-
**MeasureTheory.eLpNorm'_add_le_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {m : MeasurableSpace α} [inst : Topologica
lSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {q : ℝ} {μ : MeasureTheory.Measure
 α} {f g : α → ε},   MeasureTheory.AEStronglyMeasurable f μ →     0 ≤ q →       
q ≤ 1 →         MeasureTheory.eLpNorm' (f + g) q μ ≤           2 ^ (1 / q - 1) *
 (MeasureTheory.eLpNorm' f q μ + MeasureTheory.eLpNorm' g q μ)
参数：f + g；1 / q - 1；MeasureTheory.eLpNorm' f q μ + MeasureTheory.eLpNorm' g q μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `ENNReal.lintegral_Lp_add_le_of_le_one`：lintegral_Lp_add_le_of_le_one {p 
: Real} {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hp0 : 0 <= p) (hp1 : p <=
 1) : (∫⁻ a, (f + g) a ^ p …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
-/
theorem eLpNorm'_add_le_of_le_one (hf : AEStronglyMeasurable f μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    eLpNorm' (f + g) q μ ≤ 2 ^ (1 / q - 1) * (eLpNorm' f q μ + eLpNorm' g q μ) :=
  calc
    (∫⁻ a, ‖(f + g) a‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (∫⁻ a, (((‖f ·‖ₑ)) + (‖g ·‖ₑ)) a ^ q ∂μ) ^ (1 / q) := by
      gcongr with a
      simp only [Pi.add_apply, enorm_add_le]
    _ ≤ (2 : ℝ≥0∞) ^ (1 / q - 1) * (eLpNorm' f q μ + eLpNorm' g q μ) :=
      ENNReal.lintegral_Lp_add_le_of_le_one hf.enorm hq0 hq1
/-
**MeasureTheory.eLpNormEssSup_add_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNormEssSup_add_le : eLpNormEssSup (f + g) μ <= eLpNormEssSup f μ + eLpN
ormEssSup g μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `essSup_mono_ae`：essSup_mono_ae {f g : α -> β} (hfg : f <=ᵐ[μ] g) (hf : I
sCoboundedUnder (· <= ·) (ae μ) f
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `enorm_add_le`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESe
minormedAddMonoid E] (a b : E), ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `ENNReal.essSup_add_le`：essSup_add_le (f g : α -> Real>=0∞) : essSup (f +
 g) μ <= essSup f μ + essSup g μ
-/
theorem eLpNormEssSup_add_le :
    eLpNormEssSup (f + g) μ ≤ eLpNormEssSup f μ + eLpNormEssSup g μ := by
  refine le_trans (essSup_mono_ae (Eventually.of_forall fun x => ?_)) (ENNReal.essSup_add_le _ _)
  simp_rw [Pi.add_apply]
  exact enorm_add_le _ _
/-
**MeasureTheory.eLpNorm_add_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable 
g μ) (hp1 : 1 <= p) : eLpNorm (f + g) p μ <= eLpNorm f p μ + eLpNorm g p μ
参数：hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ；hp1 : 1 <= p。
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
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_one`：ENNReal.toReal 1 = 1
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `MeasureTheory.eLpNorm'_add_le`：∀ {α : Type u_1} {ε : Type u_3} {m : Meas
urableSpace α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {
q : ℝ} {μ : Measure…
-/
theorem eLpNorm_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp1 : 1 ≤ p) : eLpNorm (f + g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_add_le]
  have hp1_real : 1 ≤ p.toReal := by
    rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top]
  repeat rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_add_le hf hg hp1_real
/-
**MeasureTheory.eLpNorm_add_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_add_le' (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable
 g μ) (p : Real>=0∞) : eLpNorm (f + g) p μ <= LpAddConst p * (eLpNorm f p μ + eL
pNorm g p μ)
参数：hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ；p : Real>=0∞。
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm'_add_le_of_le_one`：∀ {α : Type u_1} {ε : Type u_3}
 {m : MeasurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMon
oid ε]   {q : ℝ} {μ : Measure…
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENNReal.LpAddConst_of_one_le`：LpAddConst_of_one_le {p : Real>=0∞} (hp : 
1 <= p) : LpAddConst p = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.eLpNorm_add_le`：eLpNorm_add_le (hf : AEStronglyMeasurable 
f μ) (hg : AEStronglyMeasurable g μ) (hp1 : 1 <= p) : eLpNorm (f + g) p μ <= eLp
Norm f p μ + eLpNo…
-/
theorem eLpNorm_add_le' (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) :
    eLpNorm (f + g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp
  rcases lt_or_ge p 1 with (h'p | h'p)
  · simp only [eLpNorm_eq_eLpNorm' hp (h'p.trans ENNReal.one_lt_top).ne]
    convert! eLpNorm'_add_le_of_le_one hf ENNReal.toReal_nonneg _
    · have : p ∈ Set.Ioo (0 : ℝ≥0∞) 1 := ⟨hp.bot_lt, h'p⟩
      simp only [LpAddConst, if_pos this]
    · simpa using ENNReal.toReal_mono ENNReal.one_ne_top h'p.le
  · simpa [LpAddConst_of_one_le h'p] using eLpNorm_add_le hf hg h'p

variable (μ ε) in
/-- Technical lemma to control the addition of functions in `L^p` even for `p < 1`: Given `δ > 0`,
there exists `η` such that two functions bounded by `η` in `L^p` have a sum bounded by `δ`. One
could take `η = δ / 2` for `p ≥ 1`, but the point of the lemma is that it works also for `p < 1`.
-/
/-
**MeasureTheory.exists_Lp_half** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_Lp_half (p : Real>=0∞) {δ : Real>=0∞} (hδ : δ != 0) : exists η : Re
al>=0∞, 0 < η ∧ forall (f g : α -> ε), AEStronglyMeasurable f μ -> AEStronglyMea
surable g μ -> eLpNorm f p μ <= η -> eLpNorm g p μ <= η -> eLpNorm (f + g) p μ <
 δ
参数：p : Real>=0∞；hδ : δ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.LpAddConst_lt_top`：LpAddConst_lt_top (p : Real>=0∞) : LpAddConst
 p < ∞
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `ENNReal.nhdsGT_zero_neBot`：(nhdsWithin 0 (Set.Ioi 0)).NeBot
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `MeasureTheory.eLpNorm_add_le'`：eLpNorm_add_le' (hf : AEStronglyMeasurabl
e f μ) (hg : AEStronglyMeasurable g μ) (p : Real>=0∞) : eLpNorm (f + g) p μ <= L
pAddConst p * (eLpN…
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
Technical lemma to control the addition of functions in `L^p` even for `p < 1`: 
Given `δ > 0`,
there exists `η` such that two functions bounded by `η` in `L^p` have a sum boun
ded by `δ`. One
could take `η = δ / 2` for `p ≥ 1`, but the point of the lemma is that it works 
also for `p < 1`.
-/
theorem exists_Lp_half (p : ℝ≥0∞) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ η : ℝ≥0∞,
      0 < η ∧
        ∀ (f g : α → ε), AEStronglyMeasurable f μ → AEStronglyMeasurable g μ →
          eLpNorm f p μ ≤ η → eLpNorm g p μ ≤ η → eLpNorm (f + g) p μ < δ := by
  have :
    Tendsto (fun η : ℝ≥0∞ => LpAddConst p * (η + η)) (𝓝[>] 0)
        (𝓝 (LpAddConst p * (0 + 0))) :=
    (ENNReal.Tendsto.const_mul (tendsto_id.add tendsto_id)
          (Or.inr (LpAddConst_lt_top p).ne)).mono_left
      nhdsWithin_le_nhds
  simp only [add_zero, mul_zero] at this
  rcases (((tendsto_order.1 this).2 δ hδ.bot_lt).and self_mem_nhdsWithin).exists with ⟨η, hη, ηpos⟩
  refine ⟨η, ηpos, fun f g hf hg Hf Hg => ?_⟩
  calc
    eLpNorm (f + g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
      eLpNorm_add_le' hf hg p
    _ ≤ LpAddConst p * (η + η) := by gcongr
    _ < δ := hη
/-
**MeasureTheory.eLpNorm_sub_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_sub_le' {f g : α -> E} (hf : AEStronglyMeasurable f μ) (hg : AEStr
onglyMeasurable g μ) (p : Real>=0∞) : eLpNorm (f - g) p μ <= LpAddConst p * (eLp
Norm f p μ + eLpNorm g p μ)
参数：hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ；p : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
· 使用定理 `MeasureTheory.eLpNorm_add_le'`：eLpNorm_add_le' (hf : AEStronglyMeasurabl
e f μ) (hg : AEStronglyMeasurable g μ) (p : Real>=0∞) : eLpNorm (f + g) p μ <= L
pAddConst p * (eLpN…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.neg`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem eLpNorm_sub_le' {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) :
    eLpNorm (f - g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) := by
  simpa only [sub_eq_add_neg, eLpNorm_neg] using eLpNorm_add_le' hf hg.neg p
/-
**MeasureTheory.eLpNorm_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_sub_le {f g : α -> E} (hf : AEStronglyMeasurable f μ) (hg : AEStro
nglyMeasurable g μ) (hp : 1 <= p) : eLpNorm (f - g) p μ <= eLpNorm f p μ + eLpNo
rm g p μ
参数：hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.LpAddConst_of_one_le`：LpAddConst_of_one_le {p : Real>=0∞} (hp : 
1 <= p) : LpAddConst p = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.eLpNorm_sub_le'`：eLpNorm_sub_le' {f g : α -> E} (hf : AESt
ronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (p : Real>=0∞) : eLpNorm (
f - g) p μ <= LpAdd…
-/
theorem eLpNorm_sub_le {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp : 1 ≤ p) : eLpNorm (f - g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ := by
  simpa [LpAddConst_of_one_le hp] using eLpNorm_sub_le' hf hg p
/-
**MeasureTheory.eLpNorm_add_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_add_lt_top (hf : MemLp f p μ) (hg : MemLp g p μ) : eLpNorm (f + g)
 p μ < ∞
参数：hf : MemLp f p μ；hg : MemLp g p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_add_le'`：eLpNorm_add_le' (hf : AEStronglyMeasurabl
e f μ) (hg : AEStronglyMeasurable g μ) (p : Real>=0∞) : eLpNorm (f + g) p μ <= L
pAddConst p * (eLpN…
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.LpAddConst_lt_top`：LpAddConst_lt_top (p : Real>=0∞) : LpAddConst
 p < ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem eLpNorm_add_lt_top (hf : MemLp f p μ) (hg : MemLp g p μ) :
    eLpNorm (f + g) p μ < ∞ :=
  calc
    eLpNorm (f + g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
      eLpNorm_add_le' hf.aestronglyMeasurable hg.aestronglyMeasurable p
    _ < ∞ := by
      apply ENNReal.mul_lt_top (LpAddConst_lt_top p)
      exact ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩
/-
**MeasureTheory.eLpNorm'_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε' : Type u_4} {m : MeasurableSpace α} [inst : Topologic
alSpace ε']   [inst_1 : ESeminormedAddCommMonoid ε'] {q : ℝ} {μ : MeasureTheory.
Measure α} [ContinuousAdd ε'] {ι : Type u_5}   {f : ι → α → ε'} {s : Finset ι}, 
  (∀ i ∈ s, MeasureTheory.AEStronglyMeasurable (f i) μ) →     1 ≤ q → MeasureThe
ory.eLpNorm' (∑ i ∈ s, f i) q μ ≤ ∑ i ∈ s, MeasureTheory.eLpNorm' (f i) q μ
参数：∀ i ∈ s, MeasureTheory.AEStronglyMeasurable (f i) μ；∑ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sum_of_subadditive_on_pred`：∀ {ι : Type u_1} {M : Type u_4} {N
 : Type u_5} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] [inst_2 : Preor
der N]   [IsOrderedAddMono…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.eLpNorm'_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
q : ℝ} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε
] [inst_1 : ESemi…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.eLpNorm'_add_le`：∀ {α : Type u_1} {ε : Type u_3} {m : Meas
urableSpace α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {
q : ℝ} {μ : Measure…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.add`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
-/
theorem eLpNorm'_sum_le [ContinuousAdd ε'] {ι} {f : ι → α → ε'} {s : Finset ι}
    (hfs : ∀ i, i ∈ s → AEStronglyMeasurable (f i) μ) (hq1 : 1 ≤ q) :
    eLpNorm' (∑ i ∈ s, f i) q μ ≤ ∑ i ∈ s, eLpNorm' (f i) q μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → ε' => eLpNorm' f q μ)
    (fun f => AEStronglyMeasurable f μ) (eLpNorm'_zero (zero_lt_one.trans_le hq1)).le
    (fun _f _g hf hg => eLpNorm'_add_le hf hg hq1) (fun _f _g hf hg => hf.add hg) _ hfs
/-
**MeasureTheory.eLpNorm_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_sum_le [ContinuousAdd ε'] {ι} {f : ι -> α -> ε'} {s : Finset ι} (h
fs : forall i, i in s -> AEStronglyMeasurable (f i) μ) (hp1 : 1 <= p) : eLpNorm 
(∑ i in s, f i) p μ <= ∑ i in s, eLpNorm (f i) p μ
参数：hfs : forall i, i in s -> AEStronglyMeasurable (f i) μ；hp1 : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sum_of_subadditive_on_pred`：∀ {ι : Type u_1} {M : Type u_4} {N
 : Type u_5} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] [inst_2 : Preor
der N]   [IsOrderedAddMono…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `MeasureTheory.eLpNorm_add_le`：eLpNorm_add_le (hf : AEStronglyMeasurable 
f μ) (hg : AEStronglyMeasurable g μ) (hp1 : 1 <= p) : eLpNorm (f + g) p μ <= eLp
Norm f p μ + eLpNo…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.add`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
-/
theorem eLpNorm_sum_le [ContinuousAdd ε'] {ι} {f : ι → α → ε'} {s : Finset ι}
    (hfs : ∀ i, i ∈ s → AEStronglyMeasurable (f i) μ) (hp1 : 1 ≤ p) :
    eLpNorm (∑ i ∈ s, f i) p μ ≤ ∑ i ∈ s, eLpNorm (f i) p μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → ε' => eLpNorm f p μ)
    (fun f => AEStronglyMeasurable f μ) eLpNorm_zero.le
    (fun _f _g hf hg => eLpNorm_add_le hf hg hp1)
    (fun _f _g hf hg => hf.add hg) _ hfs

-- TODO: We can prove `eLpNorm_expect_le` once we have `Module ℚ≥0 ℝ≥0∞`
/-
**MeasureTheory.MemLp.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_3} {m : MeasurableSpace α} [inst : Topologica
lSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : ENNReal} {μ : MeasureTheory.M
easure α} {f g : α → ε} [ContinuousAdd ε],   MeasureTheory.MemLp f p μ → Measure
Theory.MemLp g p μ → MeasureTheory.MemLp (f + g) p μ
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.add`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.eLpNorm_add_lt_top`：eLpNorm_add_lt_top (hf : MemLp f p μ) 
(hg : MemLp g p μ) : eLpNorm (f + g) p μ < ∞
-/
theorem MemLp.add [ContinuousAdd ε] (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (f + g) p μ :=
  ⟨AEStronglyMeasurable.add hf.1 hg.1, eLpNorm_add_lt_top hf hg⟩
/-
**MeasureTheory.MemLp.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} [inst : NormedAddC
ommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} {f g : α → E},   Measu
reTheory.MemLp f p μ → MeasureTheory.MemLp g p μ → MeasureTheory.MemLp (f - g) p
 μ
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.neg`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f : α …
-/
theorem MemLp.sub {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg
/-
**MeasureTheory.memLp_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_finsetSum [ContinuousAdd ε'] {ι} (s : Finset ι) {f : ι -> α -> ε'} (
hf : forall i in s, MemLp (f i) p μ) : MemLp (fun a => ∑ i in s, f i a) p μ
参数：s : Finset ι；hf : forall i in s, MemLp (f i) p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem memLp_finsetSum [ContinuousAdd ε']
    {ι} (s : Finset ι) {f : ι → α → ε'} (hf : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp (fun a => ∑ i ∈ s, f i a) p μ := by
  have : DecidableEq ι := Classical.decEq _
  revert hf
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

@[deprecated (since := "2026-04-08")] alias memLp_finset_sum := memLp_finsetSum
/-
**MeasureTheory.memLp_finsetSum'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_finsetSum' [ContinuousAdd ε'] {ι} (s : Finset ι) {f : ι -> α -> ε'} 
(hf : forall i in s, MemLp (f i) p μ) : MemLp (∑ i in s, f i) p μ
参数：s : Finset ι；hf : forall i in s, MemLp (f i) p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.memLp_finsetSum`：memLp_finsetSum [ContinuousAdd ε'] {ι} (s
 : Finset ι) {f : ι -> α -> ε'} (hf : forall i in s, MemLp (f i) p μ) : MemLp (f
un a => ∑ i in s, f…
-/
theorem memLp_finsetSum' [ContinuousAdd ε']
    {ι} (s : Finset ι) {f : ι → α → ε'} (hf : ∀ i ∈ s, MemLp (f i) p μ) :
    MemLp (∑ i ∈ s, f i) p μ := by
  convert! memLp_finsetSum s hf using 1
  ext x
  simp

@[deprecated (since := "2026-04-08")] alias memLp_finset_sum' := memLp_finsetSum'

end MeasureTheory

