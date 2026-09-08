/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.MeasureTheory.Function.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Basic theorems about ℒp space
-/

public section
noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology ComplexConjugate

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lp

section Top

/-
**MeasureTheory.MemLp.eLpNorm_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
mLp`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {p : ENNReal} {μ 
: MeasureTheory.Measure α} [inst : ENorm ε]   [inst_1 : TopologicalSpace ε] {f :
 α → ε}, MeasureTheory.MemLp f p μ → MeasureTheory.eLpNorm f p μ < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MemLp.eLpNorm_lt_top [TopologicalSpace ε] {f : α → ε} (hfp : MemLp f p μ) :
    eLpNorm f p μ < ∞ :=
  hfp.2

@[aesop (rule_sets := [finiteness]) unsafe 95% apply]
/-
**MeasureTheory.MemLp.eLpNorm_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
mLp`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {p : ENNReal} {μ 
: MeasureTheory.Measure α} [inst : ENorm ε]   [inst_1 : TopologicalSpace ε] {f :
 α → ε}, MeasureTheory.MemLp f p μ → MeasureTheory.eLpNorm f p μ ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MemLp.eLpNorm_ne_top [TopologicalSpace ε] {f : α → ε} (hfp : MemLp f p μ) :
    eLpNorm f p μ ≠ ∞ :=
  hfp.2.ne
/-
**MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {q : ℝ} {μ : Meas
ureTheory.Measure α} [inst : ENorm ε]   {f : α → ε}, 0 < q → MeasureTheory.eLpNo
rm' f q μ < ⊤ → ∫⁻ (a : α), ‖f a‖ₑ ^ q ∂μ < ⊤
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_rpow_enorm_eq_rpow_eLpNorm'`：lintegral_rpow_enor
m_eq_rpow_eLpNorm' {f : α -> ε} (hq0_lt : 0 < q) : ∫⁻ a, ‖f a‖ₑ ^ q ∂μ = eLpNorm
' f q μ ^ q
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
theorem lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top {f : α → ε} (hq0_lt : 0 < q)
    (hfq : eLpNorm' f q μ < ∞) : ∫⁻ a, ‖f a‖ₑ ^ q ∂μ < ∞ := by
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hq0_lt]
  exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hq0_lt) (ne_of_lt hfq)
/-
**MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top {f : α -> ε} (hp_ne_zero : p
 != 0) (hp_ne_top : p != ∞) (hfp : eLpNorm f p μ < ∞) : ∫⁻ a, ‖f a‖ₑ ^ p.toReal 
∂μ < ∞
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞；hfp : eLpNorm f p μ < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top`：∀ {α : Typ
e u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measur
e α} [inst : ENorm ε]   {f : α → ε}, 0 < q → Measu…
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
-/
theorem lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top {f : α → ε} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hfp : eLpNorm f p μ < ∞) : ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ < ∞ := by
  apply lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
  · exact ENNReal.toReal_pos hp_ne_zero hp_ne_top
  · simpa [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top] using hfp
/-
**MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top {f : α -> ε} (hp_ne_zero : 
p != 0) (hp_ne_top : p != ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) ^ p.toReal ∂μ 
< ∞
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top`：lintegral_r
pow_enorm_lt_top_of_eLpNorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_top
 : p != ∞) (hfp : eLpNorm f p μ < ∞) : ∫⁻ a, ‖f a…
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
-/
theorem eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top {f : α → ε} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) ^ p.toReal ∂μ < ∞ :=
  ⟨lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_ne_zero hp_ne_top, by
    intro h
    have hp' := ENNReal.toReal_pos hp_ne_zero hp_ne_top
    have : 0 < 1 / p.toReal := div_pos zero_lt_one hp'
    simpa [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top] using
      ENNReal.rpow_lt_top_of_nonneg (le_of_lt this) (ne_of_lt h)⟩

end Top

section Zero

@[simp]
/-
**MeasureTheory.eLpNorm'_exponent_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : ENorm ε] {f : α → ε},   MeasureTheory.eLpNorm' f 0 μ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'.eq_1`：∀ {α : Type u_1} {ε : Type u_2} [inst : ENo
rm ε] {x : MeasurableSpace α} (f : α → ε) (q : ℝ)   (μ : MeasureTheory.Measure α
), MeasureTheory.…
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
-/
theorem eLpNorm'_exponent_zero {f : α → ε} : eLpNorm' f 0 μ = 1 := by
  rw [eLpNorm', div_zero, ENNReal.rpow_zero]

@[simp]
/-
**MeasureTheory.eLpNorm_exponent_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_exponent_zero {f : α -> ε} : eLpNorm f 0 μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm_exponent_zero {f : α → ε} : eLpNorm f 0 μ = 0 := by simp [eLpNorm]

@[simp]
/-
**MeasureTheory.memLp_zero_iff_aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：memLp_zero_iff_aestronglyMeasurable [TopologicalSpace ε] {f : α -> ε} : Me
mLp f 0 μ ↔ AEStronglyMeasurable f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem memLp_zero_iff_aestronglyMeasurable [TopologicalSpace ε] {f : α → ε} :
    MemLp f 0 μ ↔ AEStronglyMeasurable f μ := by simp [MemLp, eLpNorm_exponent_zero]

section ESeminormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

@[simp]
/-
**MeasureTheory.eLpNorm'_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measu
re α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoi
d ε], 0 < q → MeasureTheory.eLpNorm' 0 q μ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_zero (hp0_lt : 0 < q) : eLpNorm' (0 : α → ε) q μ = 0 := by
  simp [eLpNorm'_eq_lintegral_enorm, hp0_lt]

@[simp]
/-
**MeasureTheory.eLpNorm'_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measu
re α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoi
d ε], q ≠ 0 → μ ≠ 0 → MeasureTheory.eLpNorm' 0 q μ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `MeasureTheory.eLpNorm'_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
q : ℝ} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε
] [inst_1 : ESemi…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `ENNReal.zero_rpow_of_neg`：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 :
 Real>=0∞) ^ y = ⊤
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.top_rpow_of_neg`：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : R
eal>=0∞) ^ y = 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) : eLpNorm' (0 : α → ε) q μ = 0 := by
  rcases le_or_gt 0 q with hq0 | hq_neg
  · exact eLpNorm'_zero (lt_of_le_of_ne hq0 hq0_ne.symm)
  · simp [eLpNorm'_eq_lintegral_enorm, hμ, hq_neg]

@[simp]
/-
**MeasureTheory.eLpNormEssSup_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNormEssSup_zero : eLpNormEssSup (0 : α -> ε) μ = 0
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `essSup_const_bot`：essSup_const_bot : essSup (fun _ : α => (⊥ : β)) μ = (
⊥ : β)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNormEssSup_zero : eLpNormEssSup (0 : α → ε) μ = 0 := by
  simp [eLpNormEssSup, ← bot_eq_zero', essSup_const_bot]

@[simp]
/-
**MeasureTheory.eLpNorm_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNormEssSup_zero`：eLpNormEssSup_zero : eLpNormEssSup (0 
: α -> ε) μ = 0
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MeasureTheory.eLpNorm'_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
q : ℝ} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε
] [inst_1 : ESemi…
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
-/
theorem eLpNorm_zero : eLpNorm (0 : α → ε) p μ = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, eLpNorm_exponent_top, eLpNormEssSup_zero]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, ENNReal.toReal_pos h0 h_top]

@[simp]
/-
**MeasureTheory.eLpNorm_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_zero' : eLpNorm (fun _ : α => (0 : ε)) p μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
-/
theorem eLpNorm_zero' : eLpNorm (fun _ : α => (0 : ε)) p μ = 0 := eLpNorm_zero
/-
**MeasureTheory.MemLp.zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ESeminormedAd
dMonoid ε], MeasureTheory.MemLp 0 p μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   [inst_1 : Zero β], Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
@[simp] lemma MemLp.zero : MemLp (0 : α → ε) p μ :=
  ⟨aestronglyMeasurable_zero, by rw [eLpNorm_zero]; exact ENNReal.coe_lt_top⟩
/-
**MeasureTheory.MemLp.zero'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ESeminormedAd
dMonoid ε], MeasureTheory.MemLp (fun x => 0) p μ
参数：fun x => 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p :
 ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpac
e ε] [inst_1 :…
-/
@[simp] lemma MemLp.zero' : MemLp (fun _ : α => (0 : ε)) p μ := MemLp.zero

variable [MeasurableSpace α]
/-
**MeasureTheory.eLpNorm'_measure_zero_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：∀ {α : Type u_1} {q : ℝ} {ε : Type u_7} [inst : TopologicalSpace ε] [inst_
1 : ESeminormedAddMonoid ε]   [inst_2 : MeasurableSpace α] {f : α → ε}, 0 < q → 
MeasureTheory.eLpNorm' f q 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_measure_zero_of_pos {f : α → ε} (hq_pos : 0 < q) :
    eLpNorm' f q (0 : Measure α) = 0 := by simp [eLpNorm', hq_pos]
/-
**MeasureTheory.eLpNorm'_measure_zero_of_exponent_zero** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_7} [inst : TopologicalSpace ε] [inst_1 : ESem
inormedAddMonoid ε]   [inst_2 : MeasurableSpace α] {f : α → ε}, MeasureTheory.eL
pNorm' f 0 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_measure_zero_of_exponent_zero {f : α → ε} : eLpNorm' f 0 (0 : Measure α) = 1 := by
  simp [eLpNorm']
/-
**MeasureTheory.eLpNorm'_measure_zero_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：∀ {α : Type u_1} {q : ℝ} {ε : Type u_7} [inst : TopologicalSpace ε] [inst_
1 : ESeminormedAddMonoid ε]   [inst_2 : MeasurableSpace α] {f : α → ε}, q < 0 → 
MeasureTheory.eLpNorm' f q 0 = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.zero_rpow_of_neg`：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 :
 Real>=0∞) ^ y = ⊤
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_measure_zero_of_neg {f : α → ε} (hq_neg : q < 0) :
    eLpNorm' f q (0 : Measure α) = ∞ := by simp [eLpNorm', hq_neg]

end ESeminormedAddMonoid

@[simp]
/-
**MeasureTheory.eLpNormEssSup_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：eLpNormEssSup_measure_zero {f : α -> ε} : eLpNormEssSup f (0 : Measure α) 
= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `essSup_measure_zero`：essSup_measure_zero {m : MeasurableSpace α} {f : α 
-> β} : essSup f (0 : Measure α) = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNormEssSup_measure_zero {f : α → ε} : eLpNormEssSup f (0 : Measure α) = 0 := by
  simp [eLpNormEssSup]

@[simp]
/-
**MeasureTheory.eLpNorm_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_measure_zero {f : α -> ε} : eLpNorm f p (0 : Measure α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNormEssSup_measure_zero`：eLpNormEssSup_measure_zero {f 
: α -> ε} : eLpNormEssSup f (0 : Measure α) = 0
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
-/
theorem eLpNorm_measure_zero {f : α → ε} : eLpNorm f p (0 : Measure α) = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm', ENNReal.toReal_pos h0 h_top]

section ContinuousENorm

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

/-
**MeasureTheory.memLp_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {ε : Type u_7} [in
st : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {f : α → ε}, MeasureTheo
ry.MemLp f p 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma memLp_measure_zero {f : α → ε} : MemLp f p (0 : Measure α) := by
  simp [MemLp]

end ContinuousENorm

end Zero

section Neg

@[simp]
/-
**MeasureTheory.eLpNorm'_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {F : Type u_5} {m0 : MeasurableSpace α} [inst : NormedAdd
CommGroup F] (f : α → F) (q : ℝ)   (μ : MeasureTheory.Measure α), MeasureTheory.
eLpNorm' (-f) q μ = MeasureTheory.eLpNorm' f q μ
参数：f : α → F；q : ℝ；μ : MeasureTheory.Measure α；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `enorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ₑ
 = ‖a‖ₑ
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_neg (f : α → F) (q : ℝ) (μ : Measure α) : eLpNorm' (-f) q μ = eLpNorm' f q μ := by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]
/-
**MeasureTheory.eLpNorm_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : Measure α) : eLpNorm (-f) p μ
 = eLpNorm f p μ
参数：f : α -> F；p : Real>=0∞；μ : Measure α。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `enorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ₑ
 = ‖a‖ₑ
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `MeasureTheory.eLpNorm'_neg`：∀ {α : Type u_1} {F : Type u_5} {m0 : Measur
ableSpace α} [inst : NormedAddCommGroup F] (f : α → F) (q : ℝ)   (μ : MeasureThe
ory.Measure α), …
-/
theorem eLpNorm_neg (f : α → F) (p : ℝ≥0∞) (μ : Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup_eq_essSup_enorm]
  simp [eLpNorm_eq_eLpNorm' h0 h_top]
/-
**MeasureTheory.eLpNorm_sub_comm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_sub_comm (f g : α -> E) (p : Real>=0∞) (μ : Measure α) : eLpNorm (
f - g) p μ = eLpNorm (g - f) p μ
参数：f g : α -> E；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eLpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (f - g) p μ = eLpNorm (g - f) p μ := by simp [← eLpNorm_neg (f := f - g)]
/-
**MeasureTheory.MemLp.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m0 : MeasurableSpace α} {p : ENNReal} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] {f : α → E}, MeasureT
heory.MemLp f p μ → MeasureTheory.MemLp (-f) p μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.neg`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MemLp.neg {f : α → E} (hf : MemLp f p μ) : MemLp (-f) p μ :=
  ⟨AEStronglyMeasurable.neg hf.1, by simp [hf.right]⟩
/-
**MeasureTheory.memLp_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_neg_iff {f : α -> E} : MemLp (-f) p μ ↔ MemLp f p μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.neg`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f : α …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem memLp_neg_iff {f : α → E} : MemLp (-f) p μ ↔ MemLp f p μ :=
  ⟨fun h => neg_neg f ▸ h.neg, MemLp.neg⟩

end Neg

section Const

variable {ε' ε'' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']

/-
**MeasureTheory.eLpNorm'_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {q : ℝ} {μ : Meas
ureTheory.Measure α} [inst : ENorm ε] (c : ε),   0 < q → MeasureTheory.eLpNorm' 
(fun x => c) q μ = ‖c‖ₑ * μ Set.univ ^ (1 / q)
参数：c : ε；fun x => c；1 / q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'_eq_lintegral_enorm`：∀ {α : Type u_1} {ε : Type u_
2} {m0 : MeasurableSpace α} [inst : ENorm ε] (f : α → ε) (q : ℝ)   (μ : MeasureT
heory.Measure α), MeasureTheory…
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
-/
theorem eLpNorm'_const (c : ε) (hq_pos : 0 < q) :
    eLpNorm' (fun _ : α => c) q μ = ‖c‖ₑ * μ Set.univ ^ (1 / q) := by
  rw [eLpNorm'_eq_lintegral_enorm, lintegral_const,
    ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ 1 / q)]
  congr
  rw [← ENNReal.rpow_mul]
  suffices hq_cancel : q * (1 / q) = 1 by rw [hq_cancel, ENNReal.rpow_one]
  rw [one_div, mul_inv_cancel₀ (ne_of_lt hq_pos).symm]

-- Generalising this to ESeminormedAddMonoid requires a case analysis whether ‖c‖ₑ = ⊤,
-- and will happen in a future PR.
/-
**MeasureTheory.eLpNorm'_const'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {F : Type u_5} {m0 : MeasurableSpace α} {q : ℝ} {μ : Meas
ureTheory.Measure α}   [inst : NormedAddCommGroup F] [MeasureTheory.IsFiniteMeas
ure μ] (c : F),   c ≠ 0 → q ≠ 0 → MeasureTheory.eLpNorm' (fun x => c) q μ = ‖c‖ₑ
 * μ Set.univ ^ (1 / q)
参数：c : F；fun x => c；1 / q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'_eq_lintegral_enorm`：∀ {α : Type u_1} {ε : Type u_
2} {m0 : MeasurableSpace α} [inst : ENorm ε] (f : α → ε) (q : ℝ)   (μ : MeasureT
heory.Measure α), MeasureTheory…
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `ENNReal.mul_rpow_of_ne_top`：mul_rpow_of_ne_top {x y : Real>=0∞} (hx : x 
!= ⊤) (hy : y != ⊤) (z : Real) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.rpow_ne_top_of_nonneg'`：rpow_ne_top_of_nonneg' {y : Real} {x : R
eal>=0∞} (hx : 0 < x) (hx' : x != ⊤) : x ^ y != ⊤
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
-/
theorem eLpNorm'_const' [IsFiniteMeasure μ] (c : F) (hc_ne_zero : c ≠ 0) (hq_ne_zero : q ≠ 0) :
    eLpNorm' (fun _ : α => c) q μ = ‖c‖ₑ * μ Set.univ ^ (1 / q) := by
  rw [eLpNorm'_eq_lintegral_enorm, lintegral_const,
    ENNReal.mul_rpow_of_ne_top _ (by finiteness)]
  · congr
    rw [← ENNReal.rpow_mul]
    suffices hp_cancel : q * (1 / q) = 1 by rw [hp_cancel, ENNReal.rpow_one]
    rw [one_div, mul_inv_cancel₀ hq_ne_zero]
  · finiteness [show ‖c‖ₑ ≠ 0 by simp [hc_ne_zero]]
/-
**MeasureTheory.eLpNormEssSup_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNormEssSup_const (c : ε) (hμ : μ != 0) : eLpNormEssSup (fun _ : α => c)
 μ = ‖c‖ₑ
参数：c : ε；hμ : μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.eLpNormEssSup_eq_essSup_enorm`：eLpNormEssSup_eq_essSup_eno
rm (f : α -> ε) (μ : Measure α) : eLpNormEssSup f μ = essSup (‖f ·‖ₑ) μ
· 使用定理 `essSup_const`：essSup_const (c : β) (hμ : μ != 0) : essSup (fun _ : α => 
c) μ = c
-/
theorem eLpNormEssSup_const (c : ε) (hμ : μ ≠ 0) : eLpNormEssSup (fun _ : α => c) μ = ‖c‖ₑ := by
  rw [eLpNormEssSup_eq_essSup_enorm, essSup_const _ hμ]
/-
**MeasureTheory.eLpNorm'_const_of_isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {q : ℝ} {μ : Meas
ureTheory.Measure α} [inst : ENorm ε] (c : ε),   0 < q → ∀ [MeasureTheory.IsProb
abilityMeasure μ], MeasureTheory.eLpNorm' (fun x => c) q μ = ‖c‖ₑ
参数：c : ε；fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'_const`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Meas
urableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α} [inst : ENorm ε] (c : ε),  
 0 < q → MeasureTh…
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
theorem eLpNorm'_const_of_isProbabilityMeasure (c : ε) (hq_pos : 0 < q) [IsProbabilityMeasure μ] :
    eLpNorm' (fun _ : α => c) q μ = ‖c‖ₑ := by simp [eLpNorm'_const c hq_pos, measure_univ]
/-
**MeasureTheory.eLpNorm_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_const (c : ε) (h0 : p != 0) (hμ : μ != 0) : eLpNorm (fun _ : α => 
c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal p)
参数：c : ε；h0 : p != 0；hμ : μ != 0。
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
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNormEssSup_const`：eLpNormEssSup_const (c : ε) (hμ : μ !
= 0) : eLpNormEssSup (fun _ : α => c) μ = ‖c‖ₑ
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `MeasureTheory.eLpNorm'_const`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Meas
urableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α} [inst : ENorm ε] (c : ε),  
 0 < q → MeasureTh…
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem eLpNorm_const (c : ε) (h0 : p ≠ 0) (hμ : μ ≠ 0) :
    eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal p) := by
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup_const c hμ]
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]
/-
**MeasureTheory.eLpNorm_const'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_const' (c : ε) (h0 : p != 0) (h_top : p != ∞) : eLpNorm (fun _ : α
 => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal p)
参数：c : ε；h0 : p != 0；h_top : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `MeasureTheory.eLpNorm'_const`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Meas
urableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α} [inst : ENorm ε] (c : ε),  
 0 < q → MeasureTh…
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm_const' (c : ε) (h0 : p ≠ 0) (h_top : p ≠ ∞) :
    eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal p) := by
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]

-- NB. If ‖c‖ₑ = ∞ and μ is finite, this claim is false: the right has side is true,
-- but the left-hand side is false (as the norm is infinite).
/-
**MeasureTheory.eLpNorm_const_lt_top_iff_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：eLpNorm_const_lt_top_iff_enorm {c : ε''} (hc' : ‖c‖ₑ != ∞) {p : Real>=0∞} 
(hp_ne_zero : p != 0) (hp_ne_top : p != ∞) : eLpNorm (fun _ : α => c) p μ < ∞ ↔ 
‖c‖ₑ = 0 ∨ μ Set.univ < ∞
参数：hc' : ‖c‖ₑ != ∞；hp_ne_zero : p != 0；hp_ne_top : p != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`：eLpNorm_lt
_top_iff_lintegral_rpow_enorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_t
op : p != ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MeasureTheory.eLpNorm_const'`：eLpNorm_const' (c : ε) (h0 : p != 0) (h_to
p : p != ∞) : eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.to
Real p)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `ENNReal.mul_lt_top_iff`：mul_lt_top_iff {a b : Real>=0∞} : a * b < ∞ ↔ a 
< ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
（共 38 条，此处仅展示前 30 条）
-/
theorem eLpNorm_const_lt_top_iff_enorm {c : ε''} (hc' : ‖c‖ₑ ≠ ∞)
    {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    eLpNorm (fun _ : α ↦ c) p μ < ∞ ↔ ‖c‖ₑ = 0 ∨ μ Set.univ < ∞ := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  by_cases hμ : μ = 0
  · simp only [hμ, Measure.coe_zero, Pi.zero_apply, or_true, ENNReal.zero_lt_top,
      eLpNorm_measure_zero]
  by_cases hc : ‖c‖ₑ = 0
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_ne_top]
    simp [hc, ENNReal.zero_rpow_of_pos hp]
  rw [eLpNorm_const' c hp_ne_zero hp_ne_top]
  obtain hμ_top | hμ_ne_top := eq_or_ne (μ .univ) ∞
  · simp [hc, hμ_top, hp]
  rw [ENNReal.mul_lt_top_iff]
  simpa [hμ, hc, hμ_ne_top, hμ_ne_top.lt_top, hc'.lt_top] using by finiteness
/-
**MeasureTheory.eLpNorm_const_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：eLpNorm_const_lt_top_iff {p : Real>=0∞} {c : F} (hp_ne_zero : p != 0) (hp_
ne_top : p != ∞) : eLpNorm (fun _ : α => c) p μ < ∞ ↔ c = 0 ∨ μ Set.univ < ∞
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_const_lt_top_iff_enorm`：eLpNorm_const_lt_top_iff_e
norm {c : ε''} (hc' : ‖c‖ₑ != ∞) {p : Real>=0∞} (hp_ne_zero : p != 0) (hp_ne_top
 : p != ∞) : eLpNorm (fun _ : α =>…
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eLpNorm_const_lt_top_iff {p : ℝ≥0∞} {c : F} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    eLpNorm (fun _ : α => c) p μ < ∞ ↔ c = 0 ∨ μ Set.univ < ∞ := by
  rw [eLpNorm_const_lt_top_iff_enorm enorm_ne_top hp_ne_zero hp_ne_top]; simp
/-
**MeasureTheory.memLp_const_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_const_enorm {c : ε'} (hc : ‖c‖ₑ != ⊤) [IsFiniteMeasure μ] : MemLp (f
un _ : α => c) p μ
参数：hc : ‖c‖ₑ != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `MeasureTheory.eLpNorm_const`：eLpNorm_const (c : ε) (h0 : p != 0) (hμ : μ
 != 0) : eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal 
p)
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.rpow_ne_top_of_nonneg`：rpow_ne_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y != ⊤
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
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem memLp_const_enorm {c : ε'} (hc : ‖c‖ₑ ≠ ⊤) [IsFiniteMeasure μ] :
    MemLp (fun _ : α ↦ c) p μ := by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  by_cases h0 : p = 0
  · simp [h0]
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [eLpNorm_const c h0 hμ]
  finiteness
/-
**MeasureTheory.memLp_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_const (c : E) [IsFiniteMeasure μ] : MemLp (fun _ : α => c) p μ
参数：c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.memLp_const_enorm`：memLp_const_enorm {c : ε'} (hc : ‖c‖ₑ !
= ⊤) [IsFiniteMeasure μ] : MemLp (fun _ : α => c) p μ
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
-/
theorem memLp_const (c : E) [IsFiniteMeasure μ] : MemLp (fun _ : α => c) p μ :=
  memLp_const_enorm enorm_ne_top
/-
**MeasureTheory.memLp_top_const_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_top_const_enorm {c : ε'} (hc : ‖c‖ₑ != ⊤) : MemLp (fun _ : α => c) ∞
 μ
参数：hc : ‖c‖ₑ != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `MeasureTheory.eLpNorm_const`：eLpNorm_const (c : ε) (h0 : p != 0) (hμ : μ
 != 0) : eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal 
p)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem memLp_top_const_enorm {c : ε'} (hc : ‖c‖ₑ ≠ ⊤) :
    MemLp (fun _ : α ↦ c) ∞ μ :=
  ⟨aestronglyMeasurable_const, by by_cases h : μ = 0 <;> simp [eLpNorm_const _, h, hc.lt_top]⟩
/-
**MeasureTheory.memLp_top_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_top_const (c : E) : MemLp (fun _ : α => c) ∞ μ
参数：c : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.memLp_top_const_enorm`：memLp_top_const_enorm {c : ε'} (hc 
: ‖c‖ₑ != ⊤) : MemLp (fun _ : α => c) ∞ μ
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
-/
theorem memLp_top_const (c : E) : MemLp (fun _ : α => c) ∞ μ :=
  memLp_top_const_enorm enorm_ne_top
/-
**MeasureTheory.memLp_const_iff_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_const_iff_enorm {p : Real>=0∞} {c : ε''} (hc : ‖c‖ₑ != ⊤) (hp_ne_zer
o : p != 0) (hp_ne_top : p != ∞) : MemLp (fun _ : α => c) p μ ↔ ‖c‖ₑ = 0 ∨ μ Set
.univ < ∞
参数：hc : ‖c‖ₑ != ⊤；hp_ne_zero : p != 0；hp_ne_top : p != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.eLpNorm_const_lt_top_iff_enorm`：eLpNorm_const_lt_top_iff_e
norm {c : ε''} (hc' : ‖c‖ₑ != ∞) {p : Real>=0∞} (hp_ne_zero : p != 0) (hp_ne_top
 : p != ∞) : eLpNorm (fun _ : α =>…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem memLp_const_iff_enorm
    {p : ℝ≥0∞} {c : ε''} (hc : ‖c‖ₑ ≠ ⊤) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp (fun _ : α ↦ c) p μ ↔ ‖c‖ₑ = 0 ∨ μ Set.univ < ∞ := by
  simp_all [MemLp, aestronglyMeasurable_const,
    eLpNorm_const_lt_top_iff_enorm hc hp_ne_zero hp_ne_top]
/-
**MeasureTheory.memLp_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_const_iff {p : Real>=0∞} {c : E} (hp_ne_zero : p != 0) (hp_ne_top : 
p != ∞) : MemLp (fun _ : α => c) p μ ↔ c = 0 ∨ μ Set.univ < ∞
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.memLp_const_iff_enorm`：memLp_const_iff_enorm {p : Real>=0∞
} {c : ε''} (hc : ‖c‖ₑ != ⊤) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) : MemLp 
(fun _ : α => c) p μ ↔ ‖c…
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem memLp_const_iff {p : ℝ≥0∞} {c : E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp (fun _ : α => c) p μ ↔ c = 0 ∨ μ Set.univ < ∞ := by
  rw [memLp_const_iff_enorm enorm_ne_top hp_ne_zero hp_ne_top]; simp

end Const

variable {f : α → F}

/-
**MeasureTheory.eLpNorm'_mono_enorm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {ε' : Type u_3} {m0 : MeasurableSpace α} {
q : ℝ} {μ : MeasureTheory.Measure α}   [inst : ENorm ε] [inst_1 : ENorm ε'] {f :
 α → ε} {g : α → ε'},   0 ≤ q → (∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) → MeasureTheory
.eLpNorm' f q μ ≤ MeasureTheory.eLpNorm' g q μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ。
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
-/
lemma eLpNorm'_mono_enorm_ae {f : α → ε} {g : α → ε'} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLpNorm' f q μ ≤ eLpNorm' g q μ := by
  simp only [eLpNorm'_eq_lintegral_enorm]
  gcongr ?_ ^ (1 / q)
  refine lintegral_mono_ae (h.mono fun x hx => ?_)
  gcongr
/-
**MeasureTheory.eLpNorm'_mono_nnnorm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：∀ {α : Type u_1} {F : Type u_5} {G : Type u_6} {m0 : MeasurableSpace α} {q
 : ℝ} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup F] [inst_1 : No
rmedAddCommGroup G] {f : α → F} {g : α → G},   0 ≤ q → (∀ᵐ (x : α) ∂μ, ‖f x‖₊ ≤ 
‖g x‖₊) → MeasureTheory.eLpNorm' f q μ ≤ MeasureTheory.eLpNorm' g q μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖₊ ≤ ‖g x‖₊。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'_mono_enorm_ae`：∀ {α : Type u_1} {ε : Type u_2} {ε
' : Type u_3} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α}   [
inst : ENorm ε] [inst_1 : …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
-/
lemma eLpNorm'_mono_nnnorm_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNorm' f q μ ≤ eLpNorm' g q μ :=
  eLpNorm'_mono_enorm_ae hq <| h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx
/-
**MeasureTheory.eLpNorm'_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {F : Type u_5} {G : Type u_6} {m0 : MeasurableSpace α} {q
 : ℝ} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup F] [inst_1 : No
rmedAddCommGroup G] {f : α → F} {g : α → G},   0 ≤ q → (∀ᵐ (x : α) ∂μ, ‖f x‖ ≤ ‖
g x‖) → MeasureTheory.eLpNorm' f q μ ≤ MeasureTheory.eLpNorm' g q μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ ≤ ‖g x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'_mono_enorm_ae`：∀ {α : Type u_1} {ε : Type u_2} {ε
' : Type u_3} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α}   [
inst : ENorm ε] [inst_1 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem eLpNorm'_mono_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    eLpNorm' f q μ ≤ eLpNorm' g q μ :=
  eLpNorm'_mono_enorm_ae hq (by simpa only [enorm_le_iff_norm_le] using h)
/-
**MeasureTheory.eLpNorm'_congr_enorm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {ε' : Type u_3} {m0 : MeasurableSpace α} {
q : ℝ} {μ : MeasureTheory.Measure α}   [inst : ENorm ε] [inst_1 : ENorm ε'] {f :
 α → ε} {g : α → ε'},   (∀ᵐ (x : α) ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) → MeasureTheory.eLpNorm
' f q μ = MeasureTheory.eLpNorm' g q μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ₑ = ‖g x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
-/
theorem eLpNorm'_congr_enorm_ae {f : α → ε} {g : α → ε'} (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) :
    eLpNorm' f q μ = eLpNorm' g q μ := by
  have : (‖f ·‖ₑ ^ q) =ᵐ[μ] (‖g ·‖ₑ ^ q) := hfg.mono fun x hx ↦ by simp [hx]
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_congr_ae this]
/-
**MeasureTheory.eLpNorm'_congr_nnnorm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：∀ {α : Type u_1} {F : Type u_5} {G : Type u_6} {m0 : MeasurableSpace α} {q
 : ℝ} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup F] [inst_1 : No
rmedAddCommGroup G] {f : α → F} {g : α → G},   (∀ᵐ (x : α) ∂μ, ‖f x‖₊ = ‖g x‖₊) 
→ MeasureTheory.eLpNorm' f q μ = MeasureTheory.eLpNorm' g q μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖₊ = ‖g x‖₊。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
-/
theorem eLpNorm'_congr_nnnorm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
    eLpNorm' f q μ = eLpNorm' g q μ := by
  have : (‖f ·‖ₑ ^ q) =ᵐ[μ] (‖g ·‖ₑ ^ q) := hfg.mono fun x hx ↦ by simp [enorm, hx]
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_congr_ae this]
/-
**MeasureTheory.eLpNorm'_congr_norm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：∀ {α : Type u_1} {F : Type u_5} {G : Type u_6} {m0 : MeasurableSpace α} {q
 : ℝ} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup F] [inst_1 : No
rmedAddCommGroup G] {f : α → F} {g : α → G},   (∀ᵐ (x : α) ∂μ, ‖f x‖ = ‖g x‖) → 
MeasureTheory.eLpNorm' f q μ = MeasureTheory.eLpNorm' g q μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ = ‖g x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'_congr_nnnorm_ae`：∀ {α : Type u_1} {F : Type u_5} 
{G : Type u_6} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α}   
[inst : NormedAddCommGroup F…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
-/
theorem eLpNorm'_congr_norm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
    eLpNorm' f q μ = eLpNorm' g q μ :=
  eLpNorm'_congr_nnnorm_ae <| hfg.mono fun _x hx => NNReal.eq hx
/-
**MeasureTheory.eLpNorm'_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {q : ℝ} {μ : Meas
ureTheory.Measure α} [inst : ENorm ε]   {f g : α → ε}, f =ᵐ[μ] g → MeasureTheory
.eLpNorm' f q μ = MeasureTheory.eLpNorm' g q μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'_congr_enorm_ae`：∀ {α : Type u_1} {ε : Type u_2} {
ε' : Type u_3} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α}   
[inst : ENorm ε] [inst_1 : …
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem eLpNorm'_congr_ae {f g : α → ε} (hfg : f =ᵐ[μ] g) : eLpNorm' f q μ = eLpNorm' g q μ :=
  eLpNorm'_congr_enorm_ae (hfg.fun_comp _)
/-
**MeasureTheory.eLpNormEssSup_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：eLpNormEssSup_congr_ae {f g : α -> ε} (hfg : f =ᵐ[μ] g) : eLpNormEssSup f 
μ = eLpNormEssSup g μ
参数：hfg : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `essSup_congr_ae`：essSup_congr_ae {f g : α -> β} (hfg : f =ᵐ[μ] g) : essS
up f μ = essSup g μ
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem eLpNormEssSup_congr_ae {f g : α → ε} (hfg : f =ᵐ[μ] g) :
    eLpNormEssSup f μ = eLpNormEssSup g μ :=
  essSup_congr_ae (hfg.fun_comp enorm)
/-
**MeasureTheory.eLpNormEssSup_mono_enorm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：eLpNormEssSup_mono_enorm_ae {f : α -> ε} {g : α -> ε'} (hfg : forallᵐ x ∂μ
, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNormEssSup f μ <= eLpNormEssSup g μ
参数：hfg : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ。
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
-/
theorem eLpNormEssSup_mono_enorm_ae {f : α → ε} {g : α → ε'} (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLpNormEssSup f μ ≤ eLpNormEssSup g μ :=
  essSup_mono_ae <| hfg
/-
**MeasureTheory.eLpNormEssSup_mono_nnnorm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：eLpNormEssSup_mono_nnnorm_ae {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ
, ‖f x‖₊ <= ‖g x‖₊) : eLpNormEssSup f μ <= eLpNormEssSup g μ
参数：hfg : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊。
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
-/
theorem eLpNormEssSup_mono_nnnorm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNormEssSup f μ ≤ eLpNormEssSup g μ :=
  essSup_mono_ae <| hfg.mono fun _x hx => ENNReal.coe_le_coe.mpr hx
/-
**MeasureTheory.eLpNorm_mono_enorm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_mono_enorm_ae {f : α -> ε} {g : α -> ε'} (h : forallᵐ x ∂μ, ‖f x‖ₑ
 <= ‖g x‖ₑ) : eLpNorm f p μ <= eLpNorm g p μ
参数：h : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.eLpNormEssSup_mono_enorm_ae`：eLpNormEssSup_mono_enorm_ae {
f : α -> ε} {g : α -> ε'} (hfg : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNormEssSup
 f μ <= eLpNormEssSup g μ
· 使用定理 `MeasureTheory.eLpNorm'_mono_enorm_ae`：∀ {α : Type u_1} {ε : Type u_2} {ε
' : Type u_3} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α}   [
inst : ENorm ε] [inst_1 : …
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
theorem eLpNorm_mono_enorm_ae {f : α → ε} {g : α → ε'} (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLpNorm f p μ ≤ eLpNorm g p μ := by
  simp only [eLpNorm]
  split_ifs
  · exact le_rfl
  · exact eLpNormEssSup_mono_enorm_ae h
  · exact eLpNorm'_mono_enorm_ae ENNReal.toReal_nonneg h
/-
**MeasureTheory.eLpNorm_mono_nnnorm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：eLpNorm_mono_nnnorm_ae {f : α -> F} {g : α -> G} (h : forallᵐ x ∂μ, ‖f x‖₊
 <= ‖g x‖₊) : eLpNorm f p μ <= eLpNorm g p μ
参数：h : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_mono_enorm_ae`：eLpNorm_mono_enorm_ae {f : α -> ε} 
{g : α -> ε'} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNorm f p μ <= eLpNorm g 
p μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
-/
theorem eLpNorm_mono_nnnorm_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_enorm_ae <| h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx
/-
**MeasureTheory.eLpNorm_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_mono_ae {f : α -> F} {g : α -> G} (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x
‖) : eLpNorm f p μ <= eLpNorm g p μ
参数：h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_mono_enorm_ae`：eLpNorm_mono_enorm_ae {f : α -> ε} 
{g : α -> ε'} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNorm f p μ <= eLpNorm g 
p μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem eLpNorm_mono_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_enorm_ae (by simpa only [enorm_le_iff_norm_le] using h)

@[deprecated (since := "2026-06-24")] alias eLpNorm_mono_ae' := eLpNorm_mono_enorm_ae
/-
**MeasureTheory.eLpNorm_mono_ae_real** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_mono_ae_real {f : α -> F} {g : α -> Real} (h : forallᵐ x ∂μ, ‖f x‖
 <= g x) : eLpNorm f p μ <= eLpNorm g p μ
参数：h : forallᵐ x ∂μ, ‖f x‖ <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_mono_ae`：eLpNorm_mono_ae {f : α -> F} {g : α -> G}
 (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
-/
theorem eLpNorm_mono_ae_real {f : α → F} {g : α → ℝ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_ae <| h.mono fun _x hx =>
    hx.trans ((le_abs_self _).trans (Real.norm_eq_abs _).symm.le)
/-
**MeasureTheory.eLpNorm_mono_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_mono_enorm {f : α -> ε} {g : α -> ε'} (h : forall x, ‖f x‖ₑ <= ‖g 
x‖ₑ) : eLpNorm f p μ <= eLpNorm g p μ
参数：h : forall x, ‖f x‖ₑ <= ‖g x‖ₑ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_mono_enorm_ae`：eLpNorm_mono_enorm_ae {f : α -> ε} 
{g : α -> ε'} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNorm f p μ <= eLpNorm g 
p μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem eLpNorm_mono_enorm {f : α → ε} {g : α → ε'} (h : ∀ x, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_enorm_ae (Eventually.of_forall h)
/-
**MeasureTheory.eLpNorm_mono_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_mono_nnnorm {f : α -> F} {g : α -> G} (h : forall x, ‖f x‖₊ <= ‖g 
x‖₊) : eLpNorm f p μ <= eLpNorm g p μ
参数：h : forall x, ‖f x‖₊ <= ‖g x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_mono_nnnorm_ae`：eLpNorm_mono_nnnorm_ae {f : α -> F
} {g : α -> G} (h : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊) : eLpNorm f p μ <= eLpNorm g
 p μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem eLpNorm_mono_nnnorm {f : α → F} {g : α → G} (h : ∀ x, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_nnnorm_ae (Eventually.of_forall h)
/-
**MeasureTheory.eLpNorm_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_mono {f : α -> F} {g : α -> G} (h : forall x, ‖f x‖ <= ‖g x‖) : eL
pNorm f p μ <= eLpNorm g p μ
参数：h : forall x, ‖f x‖ <= ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_mono_ae`：eLpNorm_mono_ae {f : α -> F} {g : α -> G}
 (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem eLpNorm_mono {f : α → F} {g : α → G} (h : ∀ x, ‖f x‖ ≤ ‖g x‖) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_ae (Eventually.of_forall h)
/-
**MeasureTheory.eLpNorm_mono_real** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_mono_real {f : α -> F} {g : α -> Real} (h : forall x, ‖f x‖ <= g x
) : eLpNorm f p μ <= eLpNorm g p μ
参数：h : forall x, ‖f x‖ <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_mono_ae_real`：eLpNorm_mono_ae_real {f : α -> F} {g
 : α -> Real} (h : forallᵐ x ∂μ, ‖f x‖ <= g x) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem eLpNorm_mono_real {f : α → F} {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_ae_real (Eventually.of_forall h)
/-
**MeasureTheory.eLpNormEssSup_le_of_ae_enorm_bound** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：eLpNormEssSup_le_of_ae_enorm_bound {f : α -> ε} {C : Real>=0∞} (hfC : fora
llᵐ x ∂μ, ‖f x‖ₑ <= C) : eLpNormEssSup f μ <= C
参数：hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `essSup_le_of_ae_le`：essSup_le_of_ae_le {f : α -> β} (c : β) (hf : f <=ᵐ[
μ] fun _ => c) (hfbdd : IsCoboundedUnder (· <= ·) (ae μ) f
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
-/
theorem eLpNormEssSup_le_of_ae_enorm_bound {f : α → ε} {C : ℝ≥0∞} (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) :
    eLpNormEssSup f μ ≤ C :=
  essSup_le_of_ae_le C hfC
/-
**MeasureTheory.eLpNormEssSup_le_of_ae_nnnorm_bound** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：eLpNormEssSup_le_of_ae_nnnorm_bound {f : α -> F} {C : Real>=0} (hfC : fora
llᵐ x ∂μ, ‖f x‖₊ <= C) : eLpNormEssSup f μ <= C
参数：hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `essSup_le_of_ae_le`：essSup_le_of_ae_le {f : α -> β} (c : β) (hf : f <=ᵐ[
μ] fun _ => c) (hfbdd : IsCoboundedUnder (· <= ·) (ae μ) f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
-/
theorem eLpNormEssSup_le_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    eLpNormEssSup f μ ≤ C :=
  essSup_le_of_ae_le (C : ℝ≥0∞) <| hfC.mono fun _x hx => ENNReal.coe_le_coe.mpr hx
/-
**MeasureTheory.eLpNormEssSup_le_of_ae_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：eLpNormEssSup_le_of_ae_bound {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, 
‖f x‖ <= C) : eLpNormEssSup f μ <= ENNReal.ofReal C
参数：hfC : forallᵐ x ∂μ, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNormEssSup_le_of_ae_nnnorm_bound`：eLpNormEssSup_le_of_a
e_nnnorm_bound {f : α -> F} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) : eL
pNormEssSup f μ <= C
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.le_coe_toNNReal`：∀ (r : ℝ), r ≤ ↑r.toNNReal
-/
theorem eLpNormEssSup_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNormEssSup f μ ≤ ENNReal.ofReal C :=
  eLpNormEssSup_le_of_ae_nnnorm_bound <| hfC.mono fun _x hx => hx.trans C.le_coe_toNNReal
/-
**MeasureTheory.eLpNormEssSup_lt_top_of_ae_enorm_bound** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：eLpNormEssSup_lt_top_of_ae_enorm_bound {f : α -> ε} {C : Real>=0} (hfC : f
orallᵐ x ∂μ, ‖f x‖ₑ <= C) : eLpNormEssSup f μ < ∞
参数：hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNormEssSup_le_of_ae_enorm_bound`：eLpNormEssSup_le_of_ae
_enorm_bound {f : α -> ε} {C : Real>=0∞} (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C) : eLp
NormEssSup f μ <= C
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
theorem eLpNormEssSup_lt_top_of_ae_enorm_bound {f : α → ε} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) :
    eLpNormEssSup f μ < ∞ :=
  (eLpNormEssSup_le_of_ae_enorm_bound hfC).trans_lt ENNReal.coe_lt_top
/-
**MeasureTheory.eLpNormEssSup_lt_top_of_ae_nnnorm_bound** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：eLpNormEssSup_lt_top_of_ae_nnnorm_bound {f : α -> F} {C : Real>=0} (hfC : 
forallᵐ x ∂μ, ‖f x‖₊ <= C) : eLpNormEssSup f μ < ∞
参数：hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNormEssSup_le_of_ae_nnnorm_bound`：eLpNormEssSup_le_of_a
e_nnnorm_bound {f : α -> F} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) : eL
pNormEssSup f μ <= C
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
theorem eLpNormEssSup_lt_top_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    eLpNormEssSup f μ < ∞ :=
  (eLpNormEssSup_le_of_ae_nnnorm_bound hfC).trans_lt ENNReal.coe_lt_top
/-
**MeasureTheory.eLpNormEssSup_lt_top_of_ae_bound** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：eLpNormEssSup_lt_top_of_ae_bound {f : α -> F} {C : Real} (hfC : forallᵐ x 
∂μ, ‖f x‖ <= C) : eLpNormEssSup f μ < ∞
参数：hfC : forallᵐ x ∂μ, ‖f x‖ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNormEssSup_le_of_ae_bound`：eLpNormEssSup_le_of_ae_bound
 {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : eLpNormEssSup f μ <=
 ENNReal.ofReal C
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
-/
theorem eLpNormEssSup_lt_top_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNormEssSup f μ < ∞ :=
  (eLpNormEssSup_le_of_ae_bound hfC).trans_lt ENNReal.ofReal_lt_top
/-
**MeasureTheory.eLpNorm_le_of_ae_enorm_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：eLpNorm_le_of_ae_enorm_bound {ε} [TopologicalSpace ε] [ESeminormedAddMonoi
d ε] {f : α -> ε} {C : Real>=0∞} (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C) : eLpNorm f p
 μ <= C • μ Set.univ ^ p.toReal⁻¹
参数：hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.eLpNorm_mono_enorm_ae`：eLpNorm_mono_enorm_ae {f : α -> ε} 
{g : α -> ε'} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNorm f p μ <= eLpNorm g 
p μ
· 使用定理 `MeasureTheory.eLpNorm_const`：eLpNorm_const (c : ε) (h0 : p != 0) (hμ : μ
 != 0) : eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal 
p)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `enorm_eq_self`：∀ (x : ENNReal), ‖x‖ₑ = x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
theorem eLpNorm_le_of_ae_enorm_bound {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    {f : α → ε} {C : ℝ≥0∞} (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) :
    eLpNorm f p μ ≤ C • μ Set.univ ^ p.toReal⁻¹ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  by_cases hp : p = 0
  · simp [hp]
  have : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖C‖ₑ := hfC.mono fun x hx ↦ hx.trans (le_refl C)
  refine (eLpNorm_mono_enorm_ae this).trans_eq ?_
  rw [eLpNorm_const _ hp (NeZero.ne μ), one_div, enorm_eq_self, smul_eq_mul]
/-
**MeasureTheory.eLpNorm_le_of_ae_nnnorm_bound** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：eLpNorm_le_of_ae_nnnorm_bound {f : α -> F} {C : Real>=0} (hfC : forallᵐ x 
∂μ, ‖f x‖₊ <= C) : eLpNorm f p μ <= C • μ Set.univ ^ p.toReal⁻¹
参数：hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_le_of_ae_enorm_bound`：eLpNorm_le_of_ae_enorm_bound
 {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f : α -> ε} {C : Real>=0∞} (
hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C)…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem eLpNorm_le_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    eLpNorm f p μ ≤ C • μ Set.univ ^ p.toReal⁻¹ := by
  simpa [C.enorm_eq, ENNReal.smul_def, smul_eq_mul] using
    (eLpNorm_le_of_ae_enorm_bound (f := f) (C := (C : ℝ≥0∞))
      (hfC.mono fun _ hx => by simpa using hx))
/-
**MeasureTheory.eLpNorm_le_of_ae_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：eLpNorm_le_of_ae_bound {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ 
<= C) : eLpNorm f p μ <= μ Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal C
参数：hfC : forallᵐ x ∂μ, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.eLpNorm_le_of_ae_nnnorm_bound`：eLpNorm_le_of_ae_nnnorm_bou
nd {f : α -> F} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <= C) : eLpNorm f p μ 
<= C • μ Set.univ ^ p.toReal⁻¹
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.le_coe_toNNReal`：∀ (r : ℝ), r ≤ ↑r.toNNReal
-/
theorem eLpNorm_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNorm f p μ ≤ μ Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal C := by
  rw [← mul_comm]
  exact eLpNorm_le_of_ae_nnnorm_bound (hfC.mono fun x hx => hx.trans C.le_coe_toNNReal)
/-
**MeasureTheory.eLpNorm_congr_enorm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：eLpNorm_congr_enorm_ae {f : α -> ε} {g : α -> ε'} (hfg : forallᵐ x ∂μ, ‖f 
x‖ₑ = ‖g x‖ₑ) : eLpNorm f p μ = eLpNorm g p μ
参数：hfg : forallᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.eLpNorm_mono_enorm_ae`：eLpNorm_mono_enorm_ae {f : α -> ε} 
{g : α -> ε'} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNorm f p μ <= eLpNorm g 
p μ
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem eLpNorm_congr_enorm_ae {f : α → ε} {g : α → ε'} (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) :
    eLpNorm f p μ = eLpNorm g p μ :=
  le_antisymm (eLpNorm_mono_enorm_ae <| EventuallyEq.le hfg)
    (eLpNorm_mono_enorm_ae <| (EventuallyEq.symm hfg).le)
/-
**MeasureTheory.eLpNorm_congr_nnnorm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：eLpNorm_congr_nnnorm_ae {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f 
x‖₊ = ‖g x‖₊) : eLpNorm f p μ = eLpNorm g p μ
参数：hfg : forallᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.eLpNorm_mono_nnnorm_ae`：eLpNorm_mono_nnnorm_ae {f : α -> F
} {g : α -> G} (h : forallᵐ x ∂μ, ‖f x‖₊ <= ‖g x‖₊) : eLpNorm f p μ <= eLpNorm g
 p μ
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem eLpNorm_congr_nnnorm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
    eLpNorm f p μ = eLpNorm g p μ :=
  le_antisymm (eLpNorm_mono_nnnorm_ae <| EventuallyEq.le hfg)
    (eLpNorm_mono_nnnorm_ae <| (EventuallyEq.symm hfg).le)
/-
**MeasureTheory.eLpNorm_congr_norm_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_congr_norm_ae {f : α -> F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖
 = ‖g x‖) : eLpNorm f p μ = eLpNorm g p μ
参数：hfg : forallᵐ x ∂μ, ‖f x‖ = ‖g x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_congr_nnnorm_ae`：eLpNorm_congr_nnnorm_ae {f : α ->
 F} {g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) : eLpNorm f p μ = eLpNorm
 g p μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
-/
theorem eLpNorm_congr_norm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
    eLpNorm f p μ = eLpNorm g p μ :=
  eLpNorm_congr_nnnorm_ae <| hfg.mono fun _x hx => NNReal.eq hx

open scoped symmDiff in
/-
**MeasureTheory.eLpNorm_indicator_sub_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：eLpNorm_indicator_sub_indicator (s t : Set α) (f : α -> E) : eLpNorm (s.in
dicator f - t.indicator f) p μ = eLpNorm ((s ∆ t).indicator f) p μ
参数：s t : Set α；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_congr_norm_ae`：eLpNorm_congr_norm_ae {f : α -> F} 
{g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖ = ‖g x‖) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.apply_indicator_symmDiff`：∀ {α : Type u_1} {β : Type u_2} {G : Type 
u_6} [inst : AddGroup G] {g : G → β},   (∀ (x : G), g (-x) = g x) →     ∀ (s t :
 Set α) (f : α → G…
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm_indicator_sub_indicator (s t : Set α) (f : α → E) :
    eLpNorm (s.indicator f - t.indicator f) p μ = eLpNorm ((s ∆ t).indicator f) p μ :=
  eLpNorm_congr_norm_ae <| ae_of_all _ fun x ↦ by simp [Set.apply_indicator_symmDiff norm_neg]

@[simp]
/-
**MeasureTheory.eLpNorm'_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {F : Type u_5} {m0 : MeasurableSpace α} {q : ℝ} {μ : Meas
ureTheory.Measure α}   [inst : NormedAddCommGroup F] {f : α → F}, MeasureTheory.
eLpNorm' (fun a => ‖f a‖) q μ = MeasureTheory.eLpNorm' f q μ
参数：fun a => ‖f a‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `enorm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), 
‖‖x‖‖ₑ = ‖x‖ₑ
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_norm {f : α → F} : eLpNorm' (fun a => ‖f a‖) q μ = eLpNorm' f q μ := by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]
/-
**MeasureTheory.eLpNorm'_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {q : ℝ} {μ : Meas
ureTheory.Measure α} [inst : ENorm ε]   {f : α → ε}, MeasureTheory.eLpNorm' (fun
 a => ‖f a‖ₑ) q μ = MeasureTheory.eLpNorm' f q μ
参数：fun a => ‖f a‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_enorm {f : α → ε} : eLpNorm' (fun a => ‖f a‖ₑ) q μ = eLpNorm' f q μ := by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]
/-
**MeasureTheory.eLpNorm_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_norm (f : α -> F) : eLpNorm (fun x => ‖f x‖) p μ = eLpNorm f p μ
参数：f : α -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_congr_norm_ae`：eLpNorm_congr_norm_ae {f : α -> F} 
{g : α -> G} (hfg : forallᵐ x ∂μ, ‖f x‖ = ‖g x‖) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
-/
theorem eLpNorm_norm (f : α → F) : eLpNorm (fun x => ‖f x‖) p μ = eLpNorm f p μ :=
  eLpNorm_congr_norm_ae <| Eventually.of_forall fun _ => norm_norm _

@[simp]
/-
**MeasureTheory.eLpNorm_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_enorm (f : α -> ε) : eLpNorm (fun x => ‖f x‖ₑ) p μ = eLpNorm f p μ
参数：f : α -> ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_congr_enorm_ae`：eLpNorm_congr_enorm_ae {f : α -> ε
} {g : α -> ε'} (hfg : forallᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) : eLpNorm f p μ = eLpNorm 
g p μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `enorm_enorm`：enorm_enorm {ε : Type*} [ENorm ε] (x : ε) : ‖‖x‖ₑ‖ₑ = ‖x‖ₑ
-/
theorem eLpNorm_enorm (f : α → ε) : eLpNorm (fun x ↦ ‖f x‖ₑ) p μ = eLpNorm f p μ :=
  eLpNorm_congr_enorm_ae <| Eventually.of_forall fun _ => enorm_enorm _
/-
**MeasureTheory.eLpNorm'_enorm_rpow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : ENorm ε] (f : α → ε)   (p q : ℝ), 0 < q → MeasureTheory.eLp
Norm' (fun x => ‖f x‖ₑ ^ q) p μ = MeasureTheory.eLpNorm' f (p * q) μ ^ q
参数：f : α → ε；p q : ℝ；fun x => ‖f x‖ₑ ^ q；p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_enorm_rpow (f : α → ε) (p q : ℝ) (hq_pos : 0 < q) :
    eLpNorm' (‖f ·‖ₑ ^ q) p μ = eLpNorm' f (p * q) μ ^ q := by
  simp_rw [eLpNorm', ← ENNReal.rpow_mul, ← one_div_mul_one_div, one_div,
    mul_assoc, inv_mul_cancel₀ hq_pos.ne.symm, mul_one, enorm_eq_self, ← ENNReal.rpow_mul, mul_comm]

/-- `f : α → ℝ` and `ENNReal.ofReal ∘ f : α → ℝ≥0∞` have the same `eLpNorm`.
Usually, you should not use this lemma (but use enorms everywhere.) -/
/-
**MeasureTheory.eLpNorm_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_ofReal (f : α -> Real) (hf : forallᵐ x ∂μ, 0 <= f x) : eLpNorm (EN
NReal.ofReal ∘ f) p μ = eLpNorm f p μ
参数：f : α -> Real；hf : forallᵐ x ∂μ, 0 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_congr_enorm_ae`：eLpNorm_congr_enorm_ae {f : α -> ε
} {g : α -> ε'} (hfg : forallᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) : eLpNorm f p μ = eLpNorm 
g p μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `Real.enorm_ofReal_of_nonneg`：enorm_ofReal_of_nonneg {a : Real} (ha : 0 <
= a) : ‖ENNReal.ofReal a‖ₑ = ‖a‖ₑ

--- 原说明 ---
`f : α → ℝ` and `ENNReal.ofReal ∘ f : α → ℝ≥0∞` have the same `eLpNorm`.
Usually, you should not use this lemma (but use enorms everywhere.)
-/
lemma eLpNorm_ofReal (f : α → ℝ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    eLpNorm (ENNReal.ofReal ∘ f) p μ = eLpNorm f p μ :=
  eLpNorm_congr_enorm_ae <| hf.mono fun _x hx ↦ Real.enorm_ofReal_of_nonneg hx
/-
**MeasureTheory.eLpNorm'_norm_rpow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {F : Type u_5} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : NormedAddCommGroup F]   (f : α → F) (p q : ℝ),   0 < q → Me
asureTheory.eLpNorm' (fun x => ‖f x‖ ^ q) p μ = MeasureTheory.eLpNorm' f (p * q)
 μ ^ q
参数：f : α → F；p q : ℝ；fun x => ‖f x‖ ^ q；p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_rpow_of_nonneg`：ofReal_rpow_of_nonneg {x p : Real} (hx_no
nneg : 0 <= x) (hp_nonneg : 0 <= p) : ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^
 p)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_norm_rpow (f : α → F) (p q : ℝ) (hq_pos : 0 < q) :
    eLpNorm' (fun x => ‖f x‖ ^ q) p μ = eLpNorm' f (p * q) μ ^ q := by
  simp_rw [eLpNorm', ← ENNReal.rpow_mul, ← one_div_mul_one_div, one_div,
    mul_assoc, inv_mul_cancel₀ hq_pos.ne.symm, mul_one, ← ofReal_norm,
    Real.norm_eq_abs, abs_eq_self.mpr (Real.rpow_nonneg (norm_nonneg _) _), mul_comm p,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq_pos.le, ENNReal.rpow_mul]
/-
**MeasureTheory.eLpNorm_enorm_rpow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_enorm_rpow (f : α -> ε) (hq_pos : 0 < q) : eLpNorm (‖f ·‖ₑ ^ q) p 
μ = eLpNorm f (p * ENNReal.ofReal q) μ ^ q
参数：f : α -> ε；hq_pos : 0 < q。
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `ENNReal.top_mul'`：top_mul' : ∞ * a = if a = 0 then 0 else ∞
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `ENNReal.strictMono_rpow_of_pos`：strictMono_rpow_of_pos {z : Real} (h : 0
 < z) : StrictMono fun x : Real>=0∞ => x ^ z
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENNReal.rpow_left_bijective`：rpow_left_bijective {x : Real} (hx : x != 0
) : Function.Bijective fun y : Real>=0∞ => y ^ x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.essSup_apply`：OrderIso.essSup_apply {_ : MeasurableSpace α} {γ}
 [ConditionallyCompleteLattice γ] (f : α -> β) (μ : Measure α) (g : β ≃o γ) (hf 
: IsBounded…
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
（共 38 条，此处仅展示前 30 条）
-/
theorem eLpNorm_enorm_rpow (f : α → ε) (hq_pos : 0 < q) :
    eLpNorm (‖f ·‖ₑ ^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ ^ q := by
  by_cases h0 : p = 0
  · simp [h0, ENNReal.zero_rpow_of_pos hq_pos]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, ENNReal.top_mul', hq_pos.not_ge,
      ENNReal.ofReal_eq_zero, if_false, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
    have h_rpow : essSup (‖‖f ·‖ₑ ^ q‖ₑ) μ = essSup (‖f ·‖ₑ ^ q) μ := by congr
    rw [h_rpow]
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hq_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hq_pos.ne.symm).2
    let iso := h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj
    exact (iso.essSup_apply (fun x => ‖f x‖ₑ) μ).symm
  rw [eLpNorm_eq_eLpNorm' h0 hp_top, eLpNorm_eq_eLpNorm' _ (by finiteness)]
  swap
  · refine mul_ne_zero h0 ?_
    rwa [Ne, ENNReal.ofReal_eq_zero, not_le]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq_pos.le]
  exact eLpNorm'_enorm_rpow f p.toReal q hq_pos
/-
**MeasureTheory.eLpNorm_norm_rpow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_norm_rpow (f : α -> F) (hq_pos : 0 < q) : eLpNorm (fun x => ‖f x‖ 
^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ ^ q
参数：f : α -> F；hq_pos : 0 < q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_enorm_rpow`：eLpNorm_enorm_rpow (f : α -> ε) (hq_po
s : 0 < q) : eLpNorm (‖f ·‖ₑ ^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ ^ q
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `ENNReal.ofReal_rpow_of_nonneg`：ofReal_rpow_of_nonneg {x p : Real} (hx_no
nneg : 0 <= x) (hp_nonneg : 0 <= p) : ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^
 p)
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `MeasureTheory.eLpNorm_ofReal`：eLpNorm_ofReal (f : α -> Real) (hf : foral
lᵐ x ∂μ, 0 <= f x) : eLpNorm (ENNReal.ofReal ∘ f) p μ = eLpNorm f p μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
-/
theorem eLpNorm_norm_rpow (f : α → F) (hq_pos : 0 < q) :
    eLpNorm (fun x => ‖f x‖ ^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ ^ q := by
  rw [← eLpNorm_enorm_rpow f hq_pos]
  symm
  convert! eLpNorm_ofReal (fun x ↦ ‖f x‖ ^ q) (by filter_upwards with x using by positivity)
  rw [Function.comp_apply, ← ofReal_norm]
  exact ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
/-
**MeasureTheory.eLpNorm_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_congr_ae {f g : α -> ε} (hfg : f =ᵐ[μ] g) : eLpNorm f p μ = eLpNor
m g p μ
参数：hfg : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_congr_enorm_ae`：eLpNorm_congr_enorm_ae {f : α -> ε
} {g : α -> ε'} (hfg : forallᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) : eLpNorm f p μ = eLpNorm 
g p μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem eLpNorm_congr_ae {f g : α → ε} (hfg : f =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ :=
  eLpNorm_congr_enorm_ae <| hfg.mono fun _x hx => hx ▸ rfl
/-
**MeasureTheory.memLp_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_congr_ae [TopologicalSpace ε] {f g : α -> ε} (hfg : f =ᵐ[μ] g) : Mem
Lp f p μ ↔ MemLp g p μ
参数：hfg : f =ᵐ[μ] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `aestronglyMeasurable_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f g 
: α → β}, f =ᵐ[μ…
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem memLp_congr_ae [TopologicalSpace ε] {f g : α → ε} (hfg : f =ᵐ[μ] g) :
    MemLp f p μ ↔ MemLp g p μ := by
  simp only [MemLp, eLpNorm_congr_ae hfg, aestronglyMeasurable_congr hfg]
/-
**MeasureTheory.MemLp.ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {p : ENNReal} {μ 
: MeasureTheory.Measure α} [inst : ENorm ε]   [inst_1 : TopologicalSpace ε] {f g
 : α → ε}, f =ᵐ[μ] g → MeasureTheory.MemLp f p μ → MeasureTheory.MemLp g p μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_congr_ae`：memLp_congr_ae [TopologicalSpace ε] {f g :
 α -> ε} (hfg : f =ᵐ[μ] g) : MemLp f p μ ↔ MemLp g p μ
-/
theorem MemLp.ae_eq [TopologicalSpace ε] {f g : α → ε} (hfg : f =ᵐ[μ] g) (hf_Lp : MemLp f p μ) :
    MemLp g p μ :=
  (memLp_congr_ae hfg).1 hf_Lp

section ContinuousENorm

variable {ε ε' : Type*}
  [TopologicalSpace ε] [TopologicalSpace ε'] [ContinuousENorm ε] [ContinuousENorm ε']

/-
**MeasureTheory.MemLp.of_le_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp
`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7} {ε' : Type u_8}   [inst : TopologicalSpace ε] [inst_1
 : TopologicalSpace ε'] [inst_2 : ContinuousENorm ε] [inst_3 : ContinuousENorm ε
']   {f : α → ε} {g : α → ε'},   MeasureTheory.MemLp g p μ →     MeasureTheory.A
EStronglyMeasurable f μ → (∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) → MeasureTheory.MemLp
 f p μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_mono_enorm_ae`：eLpNorm_mono_enorm_ae {f : α -> ε} 
{g : α -> ε'} (h : forallᵐ x ∂μ, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNorm f p μ <= eLpNorm g 
p μ
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
theorem MemLp.of_le_enorm {f : α → ε} {g : α → ε'} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) : MemLp f p μ :=
  ⟨hf, (eLpNorm_mono_enorm_ae hfg).trans_lt (by finiteness)⟩
/-
**MeasureTheory.MemLp.of_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {F : Type u_5} {m0 : MeasurableSpace α} {p
 : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] [inst_
1 : NormedAddCommGroup F] {f : α → E} {g : α → F},   MeasureTheory.MemLp g p μ →
     MeasureTheory.AEStronglyMeasurable f μ → (∀ᵐ (x : α) ∂μ, ‖f x‖ ≤ ‖g x‖) → M
easureTheory.MemLp f p μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ ≤ ‖g x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_mono_ae`：eLpNorm_mono_ae {f : α -> F} {g : α -> G}
 (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
theorem MemLp.of_le {f : α → E} {g : α → F} (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ)
    (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) : MemLp f p μ :=
  ⟨hf, (eLpNorm_mono_ae hfg).trans_lt (by finiteness)⟩

alias MemLp.mono := MemLp.of_le
/-
**MeasureTheory.MemLp.mono'_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp
`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENo
rm ε] {f : α → ε} {g : α → ENNReal},   MeasureTheory.MemLp g p μ →     MeasureTh
eory.AEStronglyMeasurable f μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ g a) → MeasureTheory.Me
mLp f p μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.of_le_enorm`：∀ {α : Type u_1} {m0 : MeasurableSpace 
α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7} {ε' : Type u_8}   
[inst : TopologicalSp…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem MemLp.mono'_enorm {f : α → ε} {g : α → ℝ≥0∞}
    (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ g a) : MemLp f p μ :=
  MemLp.of_le_enorm hg hf <| h.mono fun _x hx ↦ le_trans hx le_rfl
/-
**MeasureTheory.MemLp.mono'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m0 : MeasurableSpace α} {p : ENNReal} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] {f : α → E} {g : α → 
ℝ},   MeasureTheory.MemLp g p μ →     MeasureTheory.AEStronglyMeasurable f μ → (
∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ g a) → MeasureTheory.MemLp f p μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.of_le`：∀ {α : Type u_1} {E : Type u_4} {F : Type u_5
} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst :
 NormedAddCommG…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem MemLp.mono' {f : α → E} {g : α → ℝ} (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : MemLp f p μ :=
  hg.of_le hf <| h.mono fun _x hx => le_trans hx (le_abs_self _)
/-
**MeasureTheory.MemLp.congr_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp
`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7} {ε' : Type u_8}   [inst : TopologicalSpace ε] [inst_1
 : TopologicalSpace ε'] [inst_2 : ContinuousENorm ε] [inst_3 : ContinuousENorm ε
']   {f : α → ε} {g : α → ε'},   MeasureTheory.MemLp f p μ →     MeasureTheory.A
EStronglyMeasurable g μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) → MeasureTheory.MemLp
 g p μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g a‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.of_le_enorm`：∀ {α : Type u_1} {m0 : MeasurableSpace 
α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7} {ε' : Type u_8}   
[inst : TopologicalSp…
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem MemLp.congr_enorm {f : α → ε} {g : α → ε'} (hf : MemLp f p μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : MemLp g p μ :=
  hf.of_le_enorm hg <| EventuallyEq.le <| EventuallyEq.symm h
/-
**MeasureTheory.MemLp.congr_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`
。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {F : Type u_5} {m0 : MeasurableSpace α} {p
 : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] [inst_
1 : NormedAddCommGroup F] {f : α → E} {g : α → F},   MeasureTheory.MemLp f p μ →
     MeasureTheory.AEStronglyMeasurable g μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ = ‖g a‖) → M
easureTheory.MemLp g p μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ = ‖g a‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.mono`：∀ {α : Type u_1} {E : Type u_4} {F : Type u_5}
 {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : 
NormedAddCommG…
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem MemLp.congr_norm {f : α → E} {g : α → F} (hf : MemLp f p μ) (hg : AEStronglyMeasurable g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : MemLp g p μ :=
  hf.mono hg <| EventuallyEq.le <| EventuallyEq.symm h
/-
**MeasureTheory.memLp_congr_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_congr_enorm {f : α -> ε} {g : α -> ε'} (hf : AEStronglyMeasurable f 
μ) (hg : AEStronglyMeasurable g μ) (h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : MemLp f
 p μ ↔ MemLp g p μ
参数：hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ；h : forallᵐ a ∂μ,
 ‖f a‖ₑ = ‖g a‖ₑ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.congr_enorm`：∀ {α : Type u_1} {m0 : MeasurableSpace 
α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7} {ε' : Type u_8}   
[inst : TopologicalSp…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem memLp_congr_enorm {f : α → ε} {g : α → ε'} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : MemLp f p μ ↔ MemLp g p μ :=
  ⟨fun h2f => h2f.congr_enorm hg h, fun h2g => h2g.congr_enorm hf <| EventuallyEq.symm h⟩
/-
**MeasureTheory.memLp_congr_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_congr_norm {f : α -> E} {g : α -> F} (hf : AEStronglyMeasurable f μ)
 (hg : AEStronglyMeasurable g μ) (h : forallᵐ a ∂μ, ‖f a‖ = ‖g a‖) : MemLp f p μ
 ↔ MemLp g p μ
参数：hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ；h : forallᵐ a ∂μ,
 ‖f a‖ = ‖g a‖。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.congr_norm`：∀ {α : Type u_1} {E : Type u_4} {F : Typ
e u_5} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [i
nst : NormedAddCommG…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem memLp_congr_norm {f : α → E} {g : α → F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : MemLp f p μ ↔ MemLp g p μ :=
  ⟨fun h2f => h2f.congr_norm hg h, fun h2g => h2g.congr_norm hf <| EventuallyEq.symm h⟩
/-
**MeasureTheory.memLp_top_of_bound_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：memLp_top_of_bound_enorm {f : α -> ε} (hf : AEStronglyMeasurable f μ) (C :
 Real>=0) (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C) : MemLp f ∞ μ
参数：hf : AEStronglyMeasurable f μ；C : Real>=0；hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNormEssSup_lt_top_of_ae_enorm_bound`：eLpNormEssSup_lt_t
op_of_ae_enorm_bound {f : α -> ε} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖ₑ <= C
) : eLpNormEssSup f μ < ∞
-/
theorem memLp_top_of_bound_enorm {f : α → ε} (hf : AEStronglyMeasurable f μ) (C : ℝ≥0)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) : MemLp f ∞ μ :=
  ⟨hf, by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_lt_top_of_ae_enorm_bound hfC⟩
/-
**MeasureTheory.memLp_top_of_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_top_of_bound {f : α -> E} (hf : AEStronglyMeasurable f μ) (C : Real)
 (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f ∞ μ
参数：hf : AEStronglyMeasurable f μ；C : Real；hfC : forallᵐ x ∂μ, ‖f x‖ <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNormEssSup_lt_top_of_ae_bound`：eLpNormEssSup_lt_top_of_
ae_bound {f : α -> F} {C : Real} (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : eLpNormEssSu
p f μ < ∞
-/
theorem memLp_top_of_bound {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : MemLp f ∞ μ :=
  ⟨hf, by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_lt_top_of_ae_bound hfC⟩
/-
**MeasureTheory.MemLp.of_enorm_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
mLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENo
rm ε] [MeasureTheory.IsFiniteMeasure μ] {f : α → ε},   MeasureTheory.AEStronglyM
easurable f μ →     ∀ {C : ENNReal}, C ≠ ⊤ → (∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ C) → Measu
reTheory.MemLp f p μ
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ₑ ≤ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.of_le_enorm`：∀ {α : Type u_1} {m0 : MeasurableSpace 
α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7} {ε' : Type u_8}   
[inst : TopologicalSp…
· 使用定理 `MeasureTheory.memLp_const_enorm`：memLp_const_enorm {c : ε'} (hc : ‖c‖ₑ !
= ⊤) [IsFiniteMeasure μ] : MemLp (fun _ : α => c) p μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `enorm_eq_self`：∀ (x : ENNReal), ‖x‖ₑ = x
-/
theorem MemLp.of_enorm_bound [IsFiniteMeasure μ] {f : α → ε} (hf : AEStronglyMeasurable f μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) : MemLp f p μ := by
  apply (memLp_const_enorm hC).of_le_enorm (ε' := ℝ≥0∞) hf <| hfC.mono fun _x hx ↦ ?_
  rw [enorm_eq_self]; exact hx
/-
**MeasureTheory.MemLp.of_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m0 : MeasurableSpace α} {p : ENNReal} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] [MeasureTheory.IsFini
teMeasure μ] {f : α → E},   MeasureTheory.AEStronglyMeasurable f μ → ∀ (C : ℝ), 
(∀ᵐ (x : α) ∂μ, ‖f x‖ ≤ C) → MeasureTheory.MemLp f p μ
参数：C : ℝ；∀ᵐ (x : α) ∂μ, ‖f x‖ ≤ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.of_le`：∀ {α : Type u_1} {E : Type u_4} {F : Type u_5
} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst :
 NormedAddCommG…
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem MemLp.of_bound [IsFiniteMeasure μ] {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : MemLp f p μ :=
  (memLp_const C).of_le hf (hfC.mono fun _x hx => le_trans hx (le_abs_self _))
/-
**MeasureTheory.memLp_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_of_bounded [IsFiniteMeasure μ] {a b : Real} {f : α -> Real} (h : for
allᵐ x ∂μ, f x in Set.Icc a b) (hX : AEStronglyMeasurable f μ) (p : ENNReal) : M
emLp f p μ
参数：h : forallᵐ x ∂μ, f x in Set.Icc a b；hX : AEStronglyMeasurable f μ；p : ENNRea
l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.MemLp.mono'`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measura
bleSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommG
roup E] {f : α …
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `abs_le_max_abs_abs`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : L
inearOrder G] [IsOrderedAddMonoid G] {a b c : G},   a ≤ b → b ≤ c → |b| ≤ max |a
| |c|
-/
theorem memLp_of_bounded [IsFiniteMeasure μ]
    {a b : ℝ} {f : α → ℝ} (h : ∀ᵐ x ∂μ, f x ∈ Set.Icc a b)
    (hX : AEStronglyMeasurable f μ) (p : ENNReal) : MemLp f p μ :=
  have ha : ∀ᵐ x ∂μ, a ≤ f x := h.mono fun ω h => h.1
  have hb : ∀ᵐ x ∂μ, f x ≤ b := h.mono fun ω h => h.2
  (memLp_const (max |a| |b|)).mono' hX (by filter_upwards [ha, hb] with x using abs_le_max_abs_abs)

@[gcongr, mono]
/-
**MeasureTheory.eLpNorm'_mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {q : ℝ} {μ ν : MeasureTheory.Mea
sure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε
] (f : α → ε),   ν ≤ μ → 0 ≤ q → MeasureTheory.eLpNorm' f q ν ≤ MeasureTheory.eL
pNorm' f q μ
参数：f : α → ε。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
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
-/
theorem eLpNorm'_mono_measure (f : α → ε) (hμν : ν ≤ μ) (hq : 0 ≤ q) :
    eLpNorm' f q ν ≤ eLpNorm' f q μ := by
  simp_rw [eLpNorm']
  gcongr

@[gcongr, mono]
/-
**MeasureTheory.eLpNormEssSup_mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：eLpNormEssSup_mono_measure (f : α -> ε) (hμν : ν ≪ μ) : eLpNormEssSup f ν 
<= eLpNormEssSup f μ
参数：f : α -> ε；hμν : ν ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `essSup_mono_measure`：essSup_mono_measure {f : α -> β} (hμν : ν ≪ μ) (hνf
 : IsCoboundedUnder (· <= ·) (ae ν) f
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
-/
theorem eLpNormEssSup_mono_measure (f : α → ε) (hμν : ν ≪ μ) :
    eLpNormEssSup f ν ≤ eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup]
  exact essSup_mono_measure hμν

@[gcongr, mono]
/-
**MeasureTheory.eLpNorm_mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_mono_measure (f : α -> ε) (hμν : ν <= μ) : eLpNorm f p ν <= eLpNor
m f p μ
参数：f : α -> ε；hμν : ν <= μ。
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
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.eLpNormEssSup_mono_measure`：eLpNormEssSup_mono_measure (f 
: α -> ε) (hμν : ν ≪ μ) : eLpNormEssSup f ν <= eLpNormEssSup f μ
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `MeasureTheory.eLpNorm'_mono_measure`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} {q : ℝ} {μ ν : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topologi
calSpace ε] [inst_1 : Con…
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
theorem eLpNorm_mono_measure (f : α → ε) (hμν : ν ≤ μ) : eLpNorm f p ν ≤ eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_mono_measure f (Measure.absolutelyContinuous_of_le hμν)]
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_mono_measure f hμν ENNReal.toReal_nonneg
/-
**MeasureTheory.MemLp.mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemL
p`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ ν : MeasureTheo
ry.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousE
Norm ε] {f : α → ε},   ν ≤ μ → MeasureTheory.MemLp f p μ → MeasureTheory.MemLp f
 p ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_measure`：mono_measure {ν : Measu
re α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ) : AEStronglyMeasurable[m] 
f ν
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_mono_measure`：eLpNorm_mono_measure (f : α -> ε) (h
μν : ν <= μ) : eLpNorm f p ν <= eLpNorm f p μ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MemLp.mono_measure {f : α → ε} (hμν : ν ≤ μ) (hf : MemLp f p μ) :
    MemLp f p ν :=
  ⟨hf.1.mono_measure hμν, (eLpNorm_mono_measure f hμν).trans_lt hf.2⟩

end ContinuousENorm

section ENormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]

/-- For a function `f` with support in `s`, the Lᵖ norms of `f` with respect to `μ` and
`μ.restrict s` are the same. -/
/-
**MeasureTheory.eLpNorm_restrict_eq_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：eLpNorm_restrict_eq_of_support_subset {s : Set α} {f : α -> ε} (hsf : f.su
pport subseteq s) : eLpNorm f p (μ.restrict s) = eLpNorm f p μ
参数：hsf : f.support subseteq s。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用引理 `ENNReal.essSup_restrict_eq_of_support_subset`：essSup_restrict_eq_of_supp
ort_subset {s : Set α} {f : α -> Real>=0∞} (hsf : f.support subseteq s) : essSup
 f (μ.restrict s) = essSup f μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `enorm_ne_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : EN
ormedAddMonoid E] {a : E}, ‖a‖ₑ ≠ 0 ↔ a ≠ 0
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用引理 `MeasureTheory.setLIntegral_eq_of_support_subset`：setLIntegral_eq_of_supp
ort_subset {s : Set α} {f : α -> Real>=0∞} (hsf : f.support subseteq s) : ∫⁻ x i
n s, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
For a function `f` with support in `s`, the Lᵖ norms of `f` with respect to `μ` 
and
`μ.restrict s` are the same.
-/
theorem eLpNorm_restrict_eq_of_support_subset {s : Set α} {f : α → ε} (hsf : f.support ⊆ s) :
    eLpNorm f p (μ.restrict s) = eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
    exact ENNReal.essSup_restrict_eq_of_support_subset fun x hx ↦ hsf <| enorm_ne_zero.1 hx
  · simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top, eLpNorm'_eq_lintegral_enorm]
    congr 1
    apply setLIntegral_eq_of_support_subset
    have : ¬(p.toReal ≤ 0) := by simpa only [not_le] using ENNReal.toReal_pos hp0 hp_top
    simpa [this] using hsf

end ENormedAddMonoid

section ContinuousENorm

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

/-
**MeasureTheory.MemLp.restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENo
rm ε] (s : Set α) {f : α → ε},   MeasureTheory.MemLp f p μ → MeasureTheory.MemLp
 f p (μ.restrict s)
参数：s : Set α；μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.mono_measure`：∀ {α : Type u_1} {m0 : MeasurableSpace
 α} {p : ENNReal} {μ ν : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topol
ogicalSpace ε] [inst_1…
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
theorem MemLp.restrict (s : Set α) {f : α → ε} (hf : MemLp f p μ) :
    MemLp f p (μ.restrict s) :=
  hf.mono_measure Measure.restrict_le_self
/-
**MeasureTheory.eLpNorm'_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε
 : Type u_7} [inst : TopologicalSpace ε]   [inst_1 : ContinuousENorm ε] {p : ℝ},
   0 ≤ p → ∀ {f : α → ε} (c : ENNReal), MeasureTheory.eLpNorm' f p (c • μ) = c ^
 (1 / p) * MeasureTheory.eLpNorm' f p μ
参数：c : ENNReal；c • μ；1 / p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm'_smul_measure {p : ℝ} (hp : 0 ≤ p) {f : α → ε} (c : ℝ≥0∞) :
    eLpNorm' f p (c • μ) = c ^ (1 / p) * eLpNorm' f p μ := by
  simp [eLpNorm', ENNReal.mul_rpow_of_nonneg, hp]

end ContinuousENorm

section SMul
variable {R : Type*} [Semiring R] [IsDomain R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
  [Module.IsTorsionFree R ℝ≥0∞] {c : R}

/-
**MeasureTheory.eLpNormEssSup_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : ENorm ε] {R : Type u_7}   [inst_1 : Semiring R] [IsDomain R
] [inst_3 : _root_.Module R ENNReal] [inst_4 : IsScalarTower R ENNReal ENNReal] 
  [Module.IsTorsionFree R ENNReal] {c : R},   c ≠ 0 → ∀ (f : α → ε), MeasureTheo
ry.eLpNormEssSup f (c • μ) = MeasureTheory.eLpNormEssSup f μ
参数：f : α → ε；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `essSup_smul_measure`：essSup_smul_measure (hc : c != 0) (f : α -> β) : es
sSup f (c • μ) = essSup f μ
-/
@[simp] lemma eLpNormEssSup_smul_measure (hc : c ≠ 0) (f : α → ε) :
    eLpNormEssSup f (c • μ) = eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup]
  exact essSup_smul_measure hc _

end SMul

/-
**MeasureTheory.eLpNormEssSup_ennreal_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : ENorm ε] {c : ENNReal},   c ≠ 0 → ∀ (f : α → ε), MeasureThe
ory.eLpNormEssSup f (c • μ) = MeasureTheory.eLpNormEssSup f μ
参数：f : α → ε；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `essSup_ennreal_smul_measure`：essSup_ennreal_smul_measure {c : Real>=0∞} 
(hc : c != 0) (f : α -> β) : essSup f (c • μ) = essSup f μ
-/
@[simp] lemma eLpNormEssSup_ennreal_smul_measure {c : ℝ≥0∞} (hc : c ≠ 0) (f : α → ε) :
    eLpNormEssSup f (c • μ) = eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup]; exact essSup_ennreal_smul_measure hc _

section ContinuousENorm

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

/-- Use `eLpNorm_smul_measure_of_ne_top` instead. -/
/-
**MeasureTheory.eLpNorm_smul_measure_of_ne_zero_of_ne_top** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use `eLpNorm_smul_measure_of_ne_top` instead.
-/
private theorem eLpNorm_smul_measure_of_ne_zero_of_ne_top {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) {f : α → ε} (c : ℝ≥0∞) :
    eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  simp_rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top]
  rw [eLpNorm'_smul_measure ENNReal.toReal_nonneg]
  congr
  simp_rw [one_div]
  rw [ENNReal.toReal_inv]

/-- See `eLpNorm_smul_measure_of_ne_zero'` for a version with scalar multiplication by `ℝ≥0`. -/
/-
**MeasureTheory.eLpNorm_smul_measure_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：eLpNorm_smul_measure_of_ne_zero {c : Real>=0∞} (hc : c != 0) (f : α -> ε) 
(p : Real>=0∞) (μ : Measure α) : eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpN
orm f p μ
参数：hc : c != 0；f : α -> ε；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNormEssSup_ennreal_smul_measure`：∀ {α : Type u_1} {ε : 
Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : ENorm ε
] {c : ENNReal},   c ≠ 0 → ∀ (f : α → …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSeminorm.Basic.0.MeasureTheory
.eLpNorm_smul_measure_of_ne_zero_of_ne_top`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ : MeasureTheory.Measure α} {ε : Type u_7} [inst : TopologicalSpace ε]  
 [inst_1 : ContinuousENo…

--- 原说明 ---
See `eLpNorm_smul_measure_of_ne_zero'` for a version with scalar multiplication 
by `ℝ≥0`.
-/
theorem eLpNorm_smul_measure_of_ne_zero {c : ℝ≥0∞} (hc : c ≠ 0) (f : α → ε) (p : ℝ≥0∞)
    (μ : Measure α) : eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [*]
  exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_top c
/-
**MeasureTheory.eLpNorm_smul_measure_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：eLpNorm_smul_measure_le (c : Real>=0∞) (f : α -> ε) (p : Real>=0∞) (μ : Me
asure α) : eLpNorm f p (c • μ) <= c ^ (1 / p).toReal • eLpNorm f p μ
参数：c : Real>=0∞；f : α -> ε；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.eLpNorm_smul_measure_of_ne_zero`：eLpNorm_smul_measure_of_n
e_zero {c : Real>=0∞} (hc : c != 0) (f : α -> ε) (p : Real>=0∞) (μ : Measure α) 
: eLpNorm f p (c • μ) = c ^ (1 / p)…
-/
theorem eLpNorm_smul_measure_le (c : ℝ≥0∞) (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm f p (c • μ) ≤ c ^ (1 / p).toReal • eLpNorm f p μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (eLpNorm_smul_measure_of_ne_zero hc f p μ).le

/-- See `eLpNorm_smul_measure_of_ne_zero` for a version with scalar multiplication by `ℝ≥0∞`. -/
/-
**MeasureTheory.eLpNorm_smul_measure_of_ne_zero'** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：eLpNorm_smul_measure_of_ne_zero' {c : Real>=0} (hc : c != 0) (f : α -> ε) 
(p : Real>=0∞) (μ : Measure α) : eLpNorm f p (c • μ) = c ^ p.toReal⁻¹ • eLpNorm 
f p μ
参数：hc : c != 0；f : α -> ε；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.eLpNorm_smul_measure_of_ne_zero`：eLpNorm_smul_measure_of_n
e_zero {c : Real>=0∞} (hc : c != 0) (f : α -> ε) (p : Real>=0∞) (μ : Measure α) 
: eLpNorm f p (c • μ) = c ^ (1 / p)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹

--- 原说明 ---
See `eLpNorm_smul_measure_of_ne_zero` for a version with scalar multiplication b
y `ℝ≥0∞`.
-/
lemma eLpNorm_smul_measure_of_ne_zero' {c : ℝ≥0} (hc : c ≠ 0) (f : α → ε) (p : ℝ≥0∞)
    (μ : Measure α) : eLpNorm f p (c • μ) = c ^ p.toReal⁻¹ • eLpNorm f p μ :=
  (eLpNorm_smul_measure_of_ne_zero (ENNReal.coe_ne_zero.2 hc) ..).trans (by simp; norm_cast)

/-- See `eLpNorm_smul_measure_of_ne_top'` for a version with scalar multiplication by `ℝ≥0`. -/
/-
**MeasureTheory.eLpNorm_smul_measure_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：eLpNorm_smul_measure_of_ne_top {p : Real>=0∞} (hp_ne_top : p != ∞) (f : α 
-> ε) (c : Real>=0∞) : eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ
参数：hp_ne_top : p != ∞；f : α -> ε；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSeminorm.Basic.0.MeasureTheory
.eLpNorm_smul_measure_of_ne_zero_of_ne_top`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ : MeasureTheory.Measure α} {ε : Type u_7} [inst : TopologicalSpace ε]  
 [inst_1 : ContinuousENo…

--- 原说明 ---
See `eLpNorm_smul_measure_of_ne_top'` for a version with scalar multiplication b
y `ℝ≥0`.
-/
theorem eLpNorm_smul_measure_of_ne_top {p : ℝ≥0∞} (hp_ne_top : p ≠ ∞) (f : α → ε) (c : ℝ≥0∞) :
    eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_ne_top c

/-- See `eLpNorm_smul_measure_of_ne_top'` for a version with scalar multiplication by `ℝ≥0∞`. -/
/-
**MeasureTheory.eLpNorm_smul_measure_of_ne_top'** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：eLpNorm_smul_measure_of_ne_top' (hp : p != ∞) (c : Real>=0) (f : α -> ε) :
 eLpNorm f p (c • μ) = c ^ p.toReal⁻¹ • eLpNorm f p μ
参数：hp : p != ∞；c : Real>=0；f : α -> ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_nonneg_of_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_
1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a → 0 ≤ a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.eLpNorm_smul_measure_of_ne_top`：eLpNorm_smul_measure_of_ne
_top {p : Real>=0∞} (hp_ne_top : p != ∞) (f : α -> ε) (c : Real>=0∞) : eLpNorm f
 p (c • μ) = c ^ (1 / p).toReal • …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See `eLpNorm_smul_measure_of_ne_top'` for a version with scalar multiplication b
y `ℝ≥0∞`.
-/
lemma eLpNorm_smul_measure_of_ne_top' (hp : p ≠ ∞) (c : ℝ≥0) (f : α → ε) :
    eLpNorm f p (c • μ) = c ^ p.toReal⁻¹ • eLpNorm f p μ := by
  have : 0 ≤ p.toReal⁻¹ := by positivity
  refine (eLpNorm_smul_measure_of_ne_top hp ..).trans ?_
  simp [ENNReal.smul_def, ENNReal.coe_rpow_of_nonneg, this]
/-
**MeasureTheory.eLpNorm_one_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：eLpNorm_one_smul_measure {f : α -> ε} (c : Real>=0∞) : eLpNorm f 1 (c • μ)
 = c * eLpNorm f 1 μ
参数：c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_smul_measure_of_ne_top`：eLpNorm_smul_measure_of_ne
_top {p : Real>=0∞} (hp_ne_top : p != ∞) (f : α -> ε) (c : Real>=0∞) : eLpNorm f
 p (c • μ) = c ^ (1 / p).toReal • …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm_one_smul_measure {f : α → ε} (c : ℝ≥0∞) :
    eLpNorm f 1 (c • μ) = c * eLpNorm f 1 μ := by
  rw [eLpNorm_smul_measure_of_ne_top] <;> simp
/-
**MeasureTheory.eLpNorm_le_of_measure_le_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：eLpNorm_le_of_measure_le_smul {c : Real>=0∞} {μ μ' : Measure α} (h : μ' <=
 c • μ) {f : α -> ε} {p : Real>=0∞} : eLpNorm f p μ' <= c ^ (1 / p).toReal • eLp
Norm f p μ
参数：h : μ' <= c • μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.eLpNorm_mono_measure`：eLpNorm_mono_measure (f : α -> ε) (h
μν : ν <= μ) : eLpNorm f p ν <= eLpNorm f p μ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.eLpNorm_smul_measure_le`：eLpNorm_smul_measure_le (c : Real
>=0∞) (f : α -> ε) (p : Real>=0∞) (μ : Measure α) : eLpNorm f p (c • μ) <= c ^ (
1 / p).toReal • eLpNorm f p…
-/
theorem eLpNorm_le_of_measure_le_smul {c : ℝ≥0∞}
    {μ μ' : Measure α} (h : μ' ≤ c • μ) {f : α → ε} {p : ℝ≥0∞} :
    eLpNorm f p μ' ≤ c ^ (1 / p).toReal • eLpNorm f p μ := by
  grw [h, eLpNorm_smul_measure_le]
/-
**MeasureTheory.MemLp.of_measure_le_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.MemLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENo
rm ε] {μ' : MeasureTheory.Measure α} {c : ENNReal},   c ≠ ⊤ → μ' ≤ c • μ → ∀ {f 
: α → ε}, MeasureTheory.MemLp f p μ → MeasureTheory.MemLp f p μ'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le_smul`：absolutelyContinu
ous_of_le_smul {μ' : Measure α} {c : Real>=0∞} (hμ'_le : μ' <= c • μ) : μ' ≪ μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `MeasureTheory.eLpNorm_le_of_measure_le_smul`：eLpNorm_le_of_measure_le_sm
ul {c : Real>=0∞} {μ μ' : Measure α} (h : μ' <= c • μ) {f : α -> ε} {p : Real>=0
∞} : eLpNorm f p μ' <= c ^ (1 / p…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MemLp.of_measure_le_smul {μ' : Measure α} {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hμ'_le : μ' ≤ c • μ) {f : α → ε} (hf : MemLp f p μ) : MemLp f p μ' := by
  refine ⟨hf.1.mono_ac (Measure.absolutelyContinuous_of_le_smul hμ'_le), ?_⟩
  grw [eLpNorm_le_of_measure_le_smul hμ'_le]
  exact ENNReal.mul_lt_top (Ne.lt_top (by simp [hc])) hf.2
/-
**MeasureTheory.MemLp.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemL
p`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENo
rm ε] {f : α → ε} {c : ENNReal},   MeasureTheory.MemLp f p μ → c ≠ ⊤ → MeasureTh
eory.MemLp f p (c • μ)
参数：c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.of_measure_le_smul`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : T
opologicalSpace ε] [inst_1 :…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem MemLp.smul_measure {f : α → ε} {c : ℝ≥0∞} (hf : MemLp f p μ) (hc : c ≠ ∞) :
    MemLp f p (c • μ) :=
  hf.of_measure_le_smul hc le_rfl

variable {ε : Type*} [ENorm ε] in
/-
**MeasureTheory.eLpNorm_one_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：eLpNorm_one_add_measure (f : α -> ε) (μ ν : Measure α) : eLpNorm f 1 (μ + 
ν) = eLpNorm f 1 μ + eLpNorm f 1 ν
参数：f : α -> ε；μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ
· 使用定理 `MeasureTheory.lintegral_add_measure`：lintegral_add_measure (f : α -> Rea
l>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
-/
theorem eLpNorm_one_add_measure (f : α → ε) (μ ν : Measure α) :
    eLpNorm f 1 (μ + ν) = eLpNorm f 1 μ + eLpNorm f 1 ν := by
  simp_rw [eLpNorm_one_eq_lintegral_enorm]
  rw [lintegral_add_measure _ μ ν]
/-
**MeasureTheory.eLpNorm_le_add_measure_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：eLpNorm_le_add_measure_right (f : α -> ε) (μ ν : Measure α) {p : Real>=0∞}
 : eLpNorm f p μ <= eLpNorm f p (μ + ν)
参数：f : α -> ε；μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.eLpNorm_mono_measure`：eLpNorm_mono_measure (f : α -> ε) (h
μν : ν <= μ) : eLpNorm f p ν <= eLpNorm f p μ
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem eLpNorm_le_add_measure_right (f : α → ε) (μ ν : Measure α) {p : ℝ≥0∞} :
    eLpNorm f p μ ≤ eLpNorm f p (μ + ν) := by
  grw [← Measure.le_add_right le_rfl]
/-
**MeasureTheory.eLpNorm_le_add_measure_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：eLpNorm_le_add_measure_left (f : α -> ε) (μ ν : Measure α) {p : Real>=0∞} 
: eLpNorm f p ν <= eLpNorm f p (μ + ν)
参数：f : α -> ε；μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.eLpNorm_mono_measure`：eLpNorm_mono_measure (f : α -> ε) (h
μν : ν <= μ) : eLpNorm f p ν <= eLpNorm f p μ
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem eLpNorm_le_add_measure_left (f : α → ε) (μ ν : Measure α) {p : ℝ≥0∞} :
    eLpNorm f p ν ≤ eLpNorm f p (μ + ν) := by
  grw [← Measure.le_add_left le_rfl]

variable {ε : Type*} [ENorm ε] in
/-
**MeasureTheory.eLpNormEssSup_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNormEssSup_eq_iSup (hμ : forall a, μ {a} != 0) (f : α -> ε) : eLpNormEs
sSup f μ = ⨆ a, ‖f a‖ₑ
参数：hμ : forall a, μ {a} != 0；f : α -> ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `essSup_eq_iSup`：essSup_eq_iSup (hμ : forall a, μ {a} != 0) (f : α -> β) 
: essSup f μ = ⨆ i, f i
-/
lemma eLpNormEssSup_eq_iSup (hμ : ∀ a, μ {a} ≠ 0) (f : α → ε) : eLpNormEssSup f μ = ⨆ a, ‖f a‖ₑ :=
  essSup_eq_iSup hμ _

variable {ε : Type*} [ENorm ε] in
/-
**MeasureTheory.eLpNormEssSup_count** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {ε : Type u_8} [inst : ENorm ε] 
[MeasurableSingletonClass α] (f : α → ε),   MeasureTheory.eLpNormEssSup f Measur
eTheory.Measure.count = ⨆ a, ‖f a‖ₑ
参数：f : α → ε。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `essSup_count`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} [i
nst : CompleteLattice β] [MeasurableSingletonClass α]   (f : α → β), essSup f Me
as…
-/
@[simp] lemma eLpNormEssSup_count [MeasurableSingletonClass α] (f : α → ε) :
    eLpNormEssSup f .count = ⨆ a, ‖f a‖ₑ := essSup_count _
/-
**MeasureTheory.MemLp.left_of_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.MemLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ ν : MeasureTheo
ry.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousE
Norm ε] {f : α → ε},   MeasureTheory.MemLp f p (μ + ν) → MeasureTheory.MemLp f p
 μ
参数：μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.mono_measure`：∀ {α : Type u_1} {m0 : MeasurableSpace
 α} {p : ENNReal} {μ ν : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topol
ogicalSpace ε] [inst_1…
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem MemLp.left_of_add_measure {f : α → ε} (h : MemLp f p (μ + ν)) :
    MemLp f p μ :=
  h.mono_measure <| Measure.le_add_right <| le_refl _
/-
**MeasureTheory.MemLp.right_of_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ ν : MeasureTheo
ry.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousE
Norm ε] {f : α → ε},   MeasureTheory.MemLp f p (μ + ν) → MeasureTheory.MemLp f p
 ν
参数：μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.mono_measure`：∀ {α : Type u_1} {m0 : MeasurableSpace
 α} {p : ENNReal} {μ ν : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topol
ogicalSpace ε] [inst_1…
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem MemLp.right_of_add_measure {f : α → ε} (h : MemLp f p (μ + ν)) :
    MemLp f p ν :=
  h.mono_measure <| Measure.le_add_left <| le_refl _
/-
**MeasureTheory.MemLp.enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENo
rm ε] {f : α → ε},   MeasureTheory.MemLp f p μ → MeasureTheory.MemLp (fun x => ‖
f x‖ₑ) p μ
参数：fun x => ‖f x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_enorm`：eLpNorm_enorm (f : α -> ε) : eLpNorm (fun x
 => ‖f x‖ₑ) p μ = eLpNorm f p μ
· 使用定理 `MeasureTheory.MemLp.eLpNorm_lt_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
theorem MemLp.enorm {f : α → ε} (h : MemLp f p μ) : MemLp (‖f ·‖ₑ) p μ :=
  ⟨h.aestronglyMeasurable.enorm.aestronglyMeasurable,
    by simp_rw [MeasureTheory.eLpNorm_enorm, h.eLpNorm_lt_top]⟩
/-
**MeasureTheory.MemLp.norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m0 : MeasurableSpace α} {p : ENNReal} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] {f : α → E}, MeasureT
heory.MemLp f p μ → MeasureTheory.MemLp (fun x => ‖f x‖) p μ
参数：fun x => ‖f x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.of_le`：∀ {α : Type u_1} {E : Type u_4} {F : Type u_5
} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst :
 NormedAddCommG…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
-/
theorem MemLp.norm {f : α → E} (h : MemLp f p μ) : MemLp (fun x => ‖f x‖) p μ :=
  h.of_le h.aestronglyMeasurable.norm (Eventually.of_forall fun x => by simp)
/-
**MeasureTheory.memLp_enorm_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_enorm_iff {f : α -> ε} (hf : AEStronglyMeasurable f μ) : MemLp (‖f ·
‖ₑ) p μ ↔ MemLp f p μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_enorm`：eLpNorm_enorm (f : α -> ε) : eLpNorm (fun x
 => ‖f x‖ₑ) p μ = eLpNorm f p μ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.MemLp.enorm`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p 
: ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpa
ce ε] [inst_1 :…
-/
theorem memLp_enorm_iff {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    MemLp (‖f ·‖ₑ) p μ ↔ MemLp f p μ :=
  ⟨fun h => ⟨hf, by rw [← eLpNorm_enorm]; exact h.2⟩, fun h => h.enorm⟩
/-
**MeasureTheory.memLp_norm_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_norm_iff {f : α -> E} (hf : AEStronglyMeasurable f μ) : MemLp (fun x
 => ‖f x‖) p μ ↔ MemLp f p μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_norm`：eLpNorm_norm (f : α -> F) : eLpNorm (fun x =
> ‖f x‖) p μ = eLpNorm f p μ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.MemLp.norm`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurab
leSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGr
oup E] {f : α …
-/
theorem memLp_norm_iff {f : α → E} (hf : AEStronglyMeasurable f μ) :
    MemLp (fun x => ‖f x‖) p μ ↔ MemLp f p μ :=
  ⟨fun h => ⟨hf, by rw [← eLpNorm_norm]; exact h.2⟩, fun h => h.norm⟩

end ContinuousENorm

section ESeminormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

/-
**MeasureTheory.eLpNorm'_eq_zero_of_ae_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measu
re α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoi
d ε] {f : α → ε},   0 < q → f =ᵐ[μ] 0 → MeasureTheory.eLpNorm' f q μ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'_congr_ae`：∀ {α : Type u_1} {ε : Type u_2} {m0 : M
easurableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α} [inst : ENorm ε]   {f g 
: α → ε}, f =ᵐ[μ] g →…
· 使用定理 `MeasureTheory.eLpNorm'_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
q : ℝ} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε
] [inst_1 : ESemi…
-/
theorem eLpNorm'_eq_zero_of_ae_zero {f : α → ε} (hq0_lt : 0 < q) (hf_zero : f =ᵐ[μ] 0) :
    eLpNorm' f q μ = 0 := by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero hq0_lt]
/-
**MeasureTheory.eLpNorm'_eq_zero_of_ae_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measu
re α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoi
d ε],   q ≠ 0 → μ ≠ 0 → ∀ {f : α → ε}, f =ᵐ[μ] 0 → MeasureTheory.eLpNorm' f q μ 
= 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'_congr_ae`：∀ {α : Type u_1} {ε : Type u_2} {m0 : M
easurableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α} [inst : ENorm ε]   {f g 
: α → ε}, f =ᵐ[μ] g →…
· 使用定理 `MeasureTheory.eLpNorm'_zero'`：∀ {α : Type u_1} {m0 : MeasurableSpace α} 
{q : ℝ} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpace 
ε] [inst_1 : ESemi…
-/
theorem eLpNorm'_eq_zero_of_ae_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) {f : α → ε}
    (hf_zero : f =ᵐ[μ] 0) :
    eLpNorm' f q μ = 0 := by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero' hq0_ne hμ]
/-
**MeasureTheory.eLpNorm_eq_zero_of_ae_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：eLpNorm_eq_zero_of_ae_zero {f : α -> ε} (hf : f =ᵐ[μ] 0) : eLpNorm f p μ =
 0
参数：hf : f =ᵐ[μ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
-/
theorem eLpNorm_eq_zero_of_ae_zero {f : α → ε} (hf : f =ᵐ[μ] 0) : eLpNorm f p μ = 0 := by
  rw [← eLpNorm_zero (p := p) (μ := μ) (α := α) (ε := ε)]
  exact eLpNorm_congr_ae hf
/-
**MeasureTheory.eLpNorm'_eq_zero_of_ae_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε
 : Type u_7} [inst : TopologicalSpace ε]   [inst_1 : ESeminormedAddMonoid ε] {f 
: α → ε} {p : ℝ},   0 < p → (∀ᵐ (x : α) ∂μ, ‖f x‖ₑ = 0) → MeasureTheory.eLpNorm'
 f p μ = 0
参数：∀ᵐ (x : α) ∂μ, ‖f x‖ₑ = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm'_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
q : ℝ} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε
] [inst_1 : ESemi…
· 使用定理 `MeasureTheory.eLpNorm'_congr_enorm_ae`：∀ {α : Type u_1} {ε : Type u_2} {
ε' : Type u_3} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α}   
[inst : ENorm ε] [inst_1 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem eLpNorm'_eq_zero_of_ae_eq_zero {f : α → ε} {p : ℝ} (hp : 0 < p)
    (hf : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ = 0) : eLpNorm' f p μ = 0 := by
  rw [← eLpNorm'_zero hp (μ := μ) (ε := ε)]
  exact eLpNorm'_congr_enorm_ae (by simp [hf])

variable {ε : Type*} [ENorm ε] in
/-
**MeasureTheory.ae_le_eLpNormEssSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_le_eLpNormEssSup {f : α -> ε} : forallᵐ y ∂μ, ‖f y‖ₑ <= eLpNormEssSup f
 μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ae_le_essSup`：ae_le_essSup (hf : IsBoundedUnder (· <= ·) (ae μ) f
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem ae_le_eLpNormEssSup {f : α → ε} : ∀ᵐ y ∂μ, ‖f y‖ₑ ≤ eLpNormEssSup f μ :=
  ae_le_essSup

-- NB. Changing this lemma to use ‖‖ₑ makes it false (only => still holds);
-- unlike a nnnorm, the enorm can be ∞.
/-
**MeasureTheory.eLpNormEssSup_lt_top_iff_isBoundedUnder** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：eLpNormEssSup_lt_top_iff_isBoundedUnder : eLpNormEssSup f μ < ⊤ ↔ IsBounde
dUnder (· <= ·) (ae μ) fun x => ‖f x‖₊ where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.ae_le_eLpNormEssSup`：ae_le_eLpNormEssSup {f : α -> ε} : fo
rallᵐ y ∂μ, ‖f y‖ₑ <= eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNormEssSup_lt_top_of_ae_nnnorm_bound`：eLpNormEssSup_lt_
top_of_ae_nnnorm_bound {f : α -> F} {C : Real>=0} (hfC : forallᵐ x ∂μ, ‖f x‖₊ <=
 C) : eLpNormEssSup f μ < ∞
-/
lemma eLpNormEssSup_lt_top_iff_isBoundedUnder :
    eLpNormEssSup f μ < ⊤ ↔ IsBoundedUnder (· ≤ ·) (ae μ) fun x ↦ ‖f x‖₊ where
  mp h := ⟨(eLpNormEssSup f μ).toNNReal, by
    simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal h.ne]; exact ae_le_eLpNormEssSup⟩
  mpr := by rintro ⟨C, hC⟩; exact eLpNormEssSup_lt_top_of_ae_nnnorm_bound (C := C) hC

variable {ε : Type*} [ENorm ε] in
/-
**MeasureTheory.meas_eLpNormEssSup_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：meas_eLpNormEssSup_lt {f : α -> ε} : μ { y | eLpNormEssSup f μ < ‖f y‖ₑ } 
= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `meas_essSup_lt`：meas_essSup_lt (hf : IsBoundedUnder (· <= ·) (ae μ) f
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem meas_eLpNormEssSup_lt {f : α → ε} : μ { y | eLpNormEssSup f μ < ‖f y‖ₑ } = 0 :=
  meas_essSup_lt
/-
**MeasureTheory.eLpNorm_lt_top_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：eLpNorm_lt_top_of_finite [Finite α] [IsFiniteMeasure μ] : eLpNorm f p μ < 
∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `Filter.IsBoundedUnder.le_of_finite`：∀ {α : Type u_1} {β : Type u_2} [ins
t : Preorder α] [Nonempty α] [IsDirectedOrder α] [Finite β] {f : Filter β}   {u 
: β → α}, Filter.IsBound…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instArchimedean`：Archimedean NNReal
· 使用定理 `MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`：eLpNorm_lt
_top_iff_lintegral_rpow_enorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_t
op : p != ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) …
· 使用定理 `IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.IsFinit
eMeasure μ]   {f : α → ENNReal}, (∃ c, ∀ (x …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `Finite.exists_le`：Finite.exists_le [IsDirectedOrder α] (f : ι -> α) : ex
ists M, forall i, f i <= M
-/
lemma eLpNorm_lt_top_of_finite [Finite α] [IsFiniteMeasure μ] : eLpNorm f p μ < ∞ := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top, eLpNormEssSup_lt_top_iff_isBoundedUnder]
    exact .le_of_finite
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp]
  refine IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal μ ?_
  simp_rw [enorm, ← ENNReal.coe_rpow_of_nonneg _ ENNReal.toReal_nonneg]
  norm_cast
  exact Finite.exists_le _
/-
**MeasureTheory.MemLp.of_discrete** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp
`。
形式化陈述：∀ {α : Type u_1} {F : Type u_5} {m0 : MeasurableSpace α} {p : ENNReal} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup F] {f : α → F} [Discrete
MeasurableSpace α] [Finite α] [MeasureTheory.IsFiniteMeasure μ],   MeasureTheory
.MemLp f p μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_le`：Finite.exists_le [IsDirectedOrder α] (f : ι -> α) : ex
ists M, forall i, f i <= M
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instArchimedean`：Archimedean NNReal
· 使用定理 `MeasureTheory.MemLp.of_bound`：∀ {α : Type u_1} {E : Type u_4} {m0 : Meas
urableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup E] [Measur…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.of_discrete`：of_discrete [Countable α
] [MeasurableSingletonClass α] : AEStronglyMeasurable f μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorelSpace_of_discreteMeasurableSpace`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α], StandardBorelSpace
 α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
@[simp] lemma MemLp.of_discrete [DiscreteMeasurableSpace α] [Finite α] [IsFiniteMeasure μ] :
    MemLp f p μ :=
  let ⟨C, hC⟩ := Finite.exists_le (‖f ·‖₊); .of_bound .of_discrete C <| .of_forall hC
/-
**MeasureTheory.eLpNorm_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε
 : Type u_7} [inst : TopologicalSpace ε]   [inst_1 : ESeminormedAddMonoid ε] [Is
Empty α] (f : α → ε) (p : ENNReal), MeasureTheory.eLpNorm f p μ = 0
参数：f : α → ε；p : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma eLpNorm_of_isEmpty [IsEmpty α] (f : α → ε) (p : ℝ≥0∞) : eLpNorm f p μ = 0 := by
  simp [Subsingleton.elim f 0]

end ESeminormedAddMonoid

section ENormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]

/-
**MeasureTheory.ae_eq_zero_of_eLpNorm'_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measu
re α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ENormedAddMonoid ε]
 {f : α → ε},   0 ≤ q → MeasureTheory.AEStronglyMeasurable f μ → MeasureTheory.e
LpNorm' f q μ = 0 → f =ᵐ[μ] 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ae_eq_zero_of_eLpNorm'_eq_zero {f : α → ε} (hq0 : 0 ≤ q) (hf : AEStronglyMeasurable f μ)
    (h : eLpNorm' f q μ = 0) : f =ᵐ[μ] 0 := by
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_eq_zero_iff' (hf.enorm.pow_const q), one_div,
    ENNReal.rpow_eq_zero_iff, inv_pos, inv_neg'', hq0.not_gt, and_false, or_false] at h
  refine h.left.mono fun x hx ↦ ?_
  simp only [Pi.ofNat_apply, ENNReal.rpow_eq_zero_iff, enorm_eq_zero, h.2.not_gt, and_false,
    or_false] at hx
  simp [hx.1]
/-
**MeasureTheory.eLpNorm'_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {q : ℝ} {μ : MeasureTheory.Measu
re α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ENormedAddMonoid ε]
,   0 < q → ∀ {f : α → ε}, MeasureTheory.AEStronglyMeasurable f μ → (MeasureTheo
ry.eLpNorm' f q μ = 0 ↔ f =ᵐ[μ] 0)
参数：MeasureTheory.eLpNorm' f q μ = 0 ↔ f =ᵐ[μ] 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_zero_of_eLpNorm'_eq_zero`：∀ {α : Type u_1} {m0 : Mea
surableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : T
opologicalSpace ε] [inst_1 : ENorm…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.eLpNorm'_eq_zero_of_ae_zero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} {q : ℝ} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topo
logicalSpace ε] [inst_1 : ESemi…
-/
theorem eLpNorm'_eq_zero_iff (hq0_lt : 0 < q) {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f q μ = 0 ↔ f =ᵐ[μ] 0 :=
  ⟨ae_eq_zero_of_eLpNorm'_eq_zero (le_of_lt hq0_lt) hf, eLpNorm'_eq_zero_of_ae_zero hq0_lt⟩

variable {ε : Type*} [ENorm ε] in
/-
**MeasureTheory.enorm_ae_le_eLpNormEssSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：enorm_ae_le_eLpNormEssSup {_ : MeasurableSpace α} (f : α -> ε) (μ : Measur
e α) : forallᵐ x ∂μ, ‖f x‖ₑ <= eLpNormEssSup f μ
参数：f : α -> ε；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.ae_le_essSup`：ae_le_essSup (f : α -> Real>=0∞) : forallᵐ y ∂μ, f
 y <= essSup f μ
-/
theorem enorm_ae_le_eLpNormEssSup {_ : MeasurableSpace α} (f : α → ε) (μ : Measure α) :
    ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ eLpNormEssSup f μ :=
  ENNReal.ae_le_essSup fun x => ‖f x‖ₑ

@[simp]
/-
**MeasureTheory.eLpNormEssSup_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：eLpNormEssSup_eq_zero_iff {f : α -> ε} : eLpNormEssSup f μ = 0 ↔ f =ᵐ[μ] 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eLpNormEssSup_eq_zero_iff {f : α → ε} : eLpNormEssSup f μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp [EventuallyEq, eLpNormEssSup_eq_essSup_enorm]
/-
**MeasureTheory.eLpNorm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_eq_zero_iff {f : α -> ε} (hf : AEStronglyMeasurable f μ) (h0 : p !
= 0) : eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0
参数：hf : AEStronglyMeasurable f μ；h0 : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNormEssSup_eq_zero_iff`：eLpNormEssSup_eq_zero_iff {f : 
α -> ε} : eLpNormEssSup f μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `MeasureTheory.eLpNorm'_eq_zero_iff`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {q : ℝ} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topological
Space ε] [inst_1 : ENorm…
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
-/
theorem eLpNorm_eq_zero_iff {f : α → ε} (hf : AEStronglyMeasurable f μ) (h0 : p ≠ 0) :
    eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  by_cases h_top : p = ∞
  · rw [h_top, eLpNorm_exponent_top, eLpNormEssSup_eq_zero_iff]
  rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_eq_zero_iff (ENNReal.toReal_pos h0 h_top) hf

end ENormedAddMonoid

section MapMeasure

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  {β : Type*} {mβ : MeasurableSpace β} {f : α → β} {g : β → ε}

/-
**MeasureTheory.eLpNormEssSup_map_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：eLpNormEssSup_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ)) 
(hf : AEMeasurable f μ) : eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘
 f) μ
参数：hg : AEStronglyMeasurable g (Measure.map f μ)；hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `essSup_map_measure`：essSup_map_measure (hg : AEMeasurable g (Measure.map
 f μ)) (hf : AEMeasurable f μ) (hg_co : IsCoboundedUnder (· <= ·) (ae (Measure.m
ap f μ))…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
-/
theorem eLpNormEssSup_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘ f) μ :=
  essSup_map_measure hg.enorm hf
/-
**MeasureTheory.eLpNorm_map_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : 
AEMeasurable f μ) : eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ
参数：hg : AEStronglyMeasurable g (Measure.map f μ)；hf : AEMeasurable f μ。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `MeasureTheory.eLpNormEssSup_map_measure`：eLpNormEssSup_map_measure (hg :
 AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : eLpNormEssS
up g (Measure.map f μ) = eLpN…
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用定理 `MeasureTheory.lintegral_map'`：lintegral_map' {f : β -> Real>=0∞} {g : α 
-> β} (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f 
a ∂Measure.map g μ…
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
-/
theorem eLpNorm_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top]
    exact eLpNormEssSup_map_measure hg hf
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_top,
    lintegral_map' (hg.enorm.pow_const p.toReal) hf, Function.comp_apply]
/-
**MeasureTheory.memLp_map_measure_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_map_measure_iff (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf 
: AEMeasurable f μ) : MemLp g p (Measure.map f μ) ↔ MemLp (g ∘ f) p μ
参数：hg : AEStronglyMeasurable g (Measure.map f μ)；hf : AEMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_map_measure`：eLpNorm_map_measure (hg : AEStronglyM
easurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : eLpNorm g p (Measure.ma
p f μ) = eLpNorm (g ∘ f…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_aemeasurable`：comp_aemeasurable 
{γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Me
asure γ} (hg : AEStronglyMeasurable g (Mea…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem memLp_map_measure_iff (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : MemLp g p (Measure.map f μ) ↔ MemLp (g ∘ f) p μ := by
  simp [MemLp, eLpNorm_map_measure hg hf, hg.comp_aemeasurable hf, hg]
/-
**MeasureTheory.MemLp.comp_of_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp
`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENo
rm ε] {β : Type u_8} {mβ : MeasurableSpace β} {f : α → β}   {g : β → ε},   Measu
reTheory.MemLp g p (MeasureTheory.Measure.map f μ) → AEMeasurable f μ → MeasureT
heory.MemLp (g ∘ f) p μ
参数：MeasureTheory.Measure.map f μ；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_map_measure_iff`：memLp_map_measure_iff (hg : AEStron
glyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : MemLp g p (Measure.
map f μ) ↔ MemLp (g ∘ f) …
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
-/
theorem MemLp.comp_of_map (hg : MemLp g p (Measure.map f μ)) (hf : AEMeasurable f μ) :
    MemLp (g ∘ f) p μ :=
  (memLp_map_measure_iff hg.aestronglyMeasurable hf).1 hg
/-
**MeasureTheory.eLpNorm_comp_measurePreserving** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：eLpNorm_comp_measurePreserving {ν : MeasureTheory.Measure β} (hg : AEStron
glyMeasurable g ν) (hf : MeasurePreserving f μ ν) : eLpNorm (g ∘ f) p μ = eLpNor
m g p ν
参数：hg : AEStronglyMeasurable g ν；hf : MeasurePreserving f μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_map_measure`：eLpNorm_map_measure (hg : AEStronglyM
easurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : eLpNorm g p (Measure.ma
p f μ) = eLpNorm (g ∘ f…
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.MeasurePreserving.aemeasurable`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : MeasureTheor
y.Measure α}   {μb : MeasureTheory…
-/
theorem eLpNorm_comp_measurePreserving {ν : MeasureTheory.Measure β} (hg : AEStronglyMeasurable g ν)
    (hf : MeasurePreserving f μ ν) : eLpNorm (g ∘ f) p μ = eLpNorm g p ν :=
  Eq.symm <| hf.map_eq ▸ eLpNorm_map_measure (hf.map_eq ▸ hg) hf.aemeasurable
/-
**MeasureTheory.AEEqFun.eLpNorm_compMeasurePreserving** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.AEEqFun`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {m0 : MeasurableSpace α} {p : ENNReal} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] {β : Type u_8} {mβ : 
MeasurableSpace β} {f : α → β} {ν : MeasureTheory.Measure β}   (g : β →ₘ[ν] E) (
hf : MeasureTheory.MeasurePreserving f μ ν),   MeasureTheory.eLpNorm (↑(g.compMe
asurePreserving f hf)) p μ = MeasureTheory.eLpNorm (↑g) p ν
参数：g : β →ₘ[ν] E；hf : MeasureTheory.MeasurePreserving f μ ν；↑(g.compMeasurePrese
rving f hf)；↑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.AEEqFun.coeFn_compMeasurePreserving`：coeFn_compMeasurePres
erving (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν) : g.compMeasurePreserving
 f hf =ᵐ[μ] g ∘ f
· 使用定理 `MeasureTheory.eLpNorm_comp_measurePreserving`：eLpNorm_comp_measurePreser
ving {ν : MeasureTheory.Measure β} (hg : AEStronglyMeasurable g ν) (hf : Measure
Preserving f μ ν) : eLpNorm (g ∘ f…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
-/
theorem AEEqFun.eLpNorm_compMeasurePreserving {ν : MeasureTheory.Measure β} (g : β →ₘ[ν] E)
    (hf : MeasurePreserving f μ ν) :
    eLpNorm (g.compMeasurePreserving f hf) p μ = eLpNorm g p ν := by
  rw [eLpNorm_congr_ae (g.coeFn_compMeasurePreserving _)]
  exact eLpNorm_comp_measurePreserving g.aestronglyMeasurable hf
/-
**MeasureTheory.MemLp.comp_measurePreserving** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ContinuousENo
rm ε] {β : Type u_8} {mβ : MeasurableSpace β} {f : α → β}   {g : β → ε} {ν : Mea
sureTheory.Measure β},   MeasureTheory.MemLp g p ν → MeasureTheory.MeasurePreser
ving f μ ν → MeasureTheory.MemLp (g ∘ f) p μ
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.comp_of_map`：∀ {α : Type u_1} {m0 : MeasurableSpace 
α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topologi
calSpace ε] [inst_1 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.MeasurePreserving.aemeasurable`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : MeasureTheor
y.Measure α}   {μb : MeasureTheory…
-/
theorem MemLp.comp_measurePreserving {ν : MeasureTheory.Measure β} (hg : MemLp g p ν)
    (hf : MeasurePreserving f μ ν) : MemLp (g ∘ f) p μ :=
  .comp_of_map (hf.map_eq.symm ▸ hg) hf.aemeasurable
/-
**MeasureTheory._root_.MeasurableEmbedding.eLpNormEssSup_map_measure** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.eLpNormEssSup_map_measure (hf : MeasurableEmbedding f) :
    eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘ f) μ :=
  hf.essSup_map_measure
/-
**MeasureTheory._root_.MeasurableEmbedding.eLpNorm_map_measure** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.eLpNorm_map_measure (hf : MeasurableEmbedding f) :
    eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp : p = ∞
  · simp_rw [hp, eLpNorm_exponent_top]
    exact hf.essSup_map_measure
  · simp [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp, hf.lintegral_map]
/-
**MeasureTheory._root_.MeasurableEmbedding.memLp_map_measure_iff** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.memLp_map_measure_iff (hf : MeasurableEmbedding f) :
    MemLp g p (Measure.map f μ) ↔ MemLp (g ∘ f) p μ := by
  simp_rw [MemLp, hf.aestronglyMeasurable_map_iff, hf.eLpNorm_map_measure]
/-
**MeasureTheory._root_.MeasurableEquiv.memLp_map_measure_iff** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEquiv.memLp_map_measure_iff (f : α ≃ᵐ β) :
    MemLp g p (Measure.map f μ) ↔ MemLp (g ∘ f) p μ :=
  f.measurableEmbedding.memLp_map_measure_iff

end MapMeasure

section Liminf

variable [MeasurableSpace E] [OpensMeasurableSpace E] {R : ℝ≥0}

/-
**MeasureTheory.ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd {p : Real>=0∞} {f : Nat -> α -> E}
 (hfmeas : forall n, Measurable (f n)) (hbdd : forall n, eLpNorm (f n) p μ <= R)
 : forallᵐ x ∂μ, liminf (fun n => ((‖f n x‖ₑ) ^ p.toReal : Real>=0∞)) atTop < ∞
参数：hfmeas : forall n, Measurable (f n)；hbdd : forall n, eLpNorm (f n) p μ <= R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.liminf_const`：liminf_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : liminf (fun _ => b) f = b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `MeasureTheory.ae_lt_top`：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable 
f) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `Measurable.liminf`：Measurable.liminf {f : Nat -> δ -> α} (hf : forall i,
 Measurable (f i)) : Measurable fun x => liminf (fun i => f i x) atTop
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `Measurable.pow_const`：Measurable.pow_const (hf : Measurable f) (c : γ) :
 Measurable fun x => f x ^ c
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `Measurable.nnnorm`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpa
ce α] [inst_1 : NormedAddCommGroup α] [OpensMeasurableSpace α]   [inst_3 : Measu
rableSp…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.lintegral_liminf_le`：lintegral_liminf_le {ι : Type*} {f : 
ι -> α -> Real>=0∞} {u : Filter ι} [IsCountablyGenerated u] (h_meas : forall i, 
Measurable (f i)) : ∫⁻ …
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
（共 46 条，此处仅展示前 30 条）
-/
theorem ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd {p : ℝ≥0∞} {f : ℕ → α → E}
    (hfmeas : ∀ n, Measurable (f n)) (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) :
    ∀ᵐ x ∂μ, liminf (fun n => ((‖f n x‖ₑ) ^ p.toReal : ℝ≥0∞)) atTop < ∞ := by
  by_cases hp0 : p.toReal = 0
  · simp only [hp0, ENNReal.rpow_zero]
    filter_upwards with _
    rw [liminf_const (1 : ℝ≥0∞)]
    exact ENNReal.one_lt_top
  have hp : p ≠ 0 := fun h => by simp [h] at hp0
  have hp' : p ≠ ∞ := fun h => by simp [h] at hp0
  refine
    ae_lt_top (.liminf fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
      (lt_of_le_of_lt
          (lintegral_liminf_le fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
          (lt_of_le_of_lt ?_ (by finiteness : (R : ℝ≥0∞) ^ p.toReal < ∞))).ne
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp', one_div] at hbdd
  simp_rw [liminf_eq, eventually_atTop]
  exact
    sSup_le fun b ⟨a, ha⟩ =>
      (ha a le_rfl).trans ((ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hp hp')).1 (hbdd _))
/-
**MeasureTheory.ae_bdd_liminf_atTop_of_eLpNorm_bdd** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：ae_bdd_liminf_atTop_of_eLpNorm_bdd {p : Real>=0∞} (hp : p != 0) {f : Nat -
> α -> E} (hfmeas : forall n, Measurable (f n)) (hbdd : forall n, eLpNorm (f n) 
p μ <= R) : forallᵐ x ∂μ, liminf (fun n => (‖f n x‖ₑ)) atTop < ∞
参数：hp : p != 0；hfmeas : forall n, Measurable (f n)；hbdd : forall n, eLpNorm (f n
) p μ <= R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ae_lt_of_essSup_lt`：ae_lt_of_essSup_lt (hx : essSup f μ < x) (hf : IsBou
ndedUnder (· <= ·) (ae μ) f
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.liminf_le_of_frequently_le'`：liminf_le_of_frequently_le' {α β} [C
ompleteLattice β] {f : Filter α} {u : α -> β} {x : β} (h : existsᶠ a in f, u a <
= x) : liminf u f <= x
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
· 使用定理 `MeasureTheory.ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd`：ae_bdd_liminf_atT
op_rpow_of_eLpNorm_bdd {p : Real>=0∞} {f : Nat -> α -> E} (hfmeas : forall n, Me
asurable (f n)) (hbdd : forall n, eLpNorm (…
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
（共 43 条，此处仅展示前 30 条）
-/
theorem ae_bdd_liminf_atTop_of_eLpNorm_bdd {p : ℝ≥0∞} (hp : p ≠ 0) {f : ℕ → α → E}
    (hfmeas : ∀ n, Measurable (f n)) (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) :
    ∀ᵐ x ∂μ, liminf (fun n => (‖f n x‖ₑ)) atTop < ∞ := by
  by_cases hp' : p = ∞
  · subst hp'
    simp_rw [eLpNorm_exponent_top] at hbdd
    have : ∀ n, ∀ᵐ x ∂μ, (‖f n x‖ₑ) < R + 1 := fun n =>
      ae_lt_of_essSup_lt
        (lt_of_le_of_lt (hbdd n) <| ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero)
    rw [← ae_all_iff] at this
    filter_upwards [this] with x hx using lt_of_le_of_lt
        (liminf_le_of_frequently_le' <| Frequently.of_forall fun n => (hx n).le)
        (ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.one_lt_top⟩)
  filter_upwards [ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd hfmeas hbdd] with x hx
  have hppos : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have :
    liminf (fun n => (‖f n x‖ₑ) ^ p.toReal) atTop =
      liminf (fun n => (‖f n x‖ₑ)) atTop ^ p.toReal := by
    change
      liminf (fun n => ENNReal.orderIsoRpow p.toReal hppos (‖f n x‖ₑ)) atTop =
        ENNReal.orderIsoRpow p.toReal hppos (liminf (fun n => (‖f n x‖ₑ)) atTop)
    refine (OrderIso.liminf_apply (ENNReal.orderIsoRpow p.toReal _) ?_ ?_ ?_ ?_).symm <;>
      isBoundedDefault
  rw [this] at hx
  rw [← ENNReal.rpow_one (liminf (‖f · x‖ₑ) atTop), ← mul_inv_cancel₀ hppos.ne.symm,
    ENNReal.rpow_mul]
  exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 hppos.le) hx.ne

end Liminf

/-- A continuous function with compact support belongs to `L^∞`.
See `Continuous.memLp_of_hasCompactSupport` for a version for `L^p`. -/
/-
**MeasureTheory._root_.Continuous.memLp_top_of_hasCompactSupport** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous function with compact support belongs to `L^∞`.
See `Continuous.memLp_of_hasCompactSupport` for a version for `L^p`.
-/
theorem _root_.Continuous.memLp_top_of_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → E} (hf : Continuous f) (h'f : HasCompactSupport f) (μ : Measure X) : MemLp f ⊤ μ := by
  borelize E
  rcases hf.bounded_above_of_compact_support h'f with ⟨C, hC⟩
  apply memLp_top_of_bound ?_ C (Filter.Eventually.of_forall hC)
  exact (hf.stronglyMeasurable_of_hasCompactSupport h'f).aestronglyMeasurable

end Lp
end MeasureTheory

