/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# ℒp space

This file describes properties of almost everywhere strongly measurable functions with finite
`p`-seminorm, denoted by `eLpNorm f p μ` and defined for `p:ℝ≥0∞` as `0` if `p=0`,
`(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and `essSup ‖f‖ μ` for `p=∞`.

The Prop-valued `MemLp f p μ` states that a function `f : α → E` has finite `p`-seminorm
and is almost everywhere strongly measurable.

## Main definitions

* `eLpNorm' f p μ` : `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a measurable
  space and `F` is a normed group.
* `eLpNormEssSup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `essSup ‖f‖ μ`.
* `eLpNorm f p μ` : for `p : ℝ≥0∞`, seminorm in `ℒp`, equal to `0` for `p=0`, to `eLpNorm' f p μ`
  for `0 < p < ∞` and to `eLpNormEssSup f μ` for `p = ∞`.

* `MemLp f p μ` : property that the function `f` is almost everywhere strongly measurable and has
  finite `p`-seminorm for the measure `μ` (`eLpNorm f p μ < ∞`)

-/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {f : α → E}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lp

/-!
### ℒp seminorm

We define the ℒp seminorm, denoted by `eLpNorm f p μ`. For real `p`, it is given by an integral
formula (for which we use the notation `eLpNorm' f p μ`), and for `p = ∞` it is the essential
supremum (for which we use the notation `eLpNormEssSup f μ`).

We also define a predicate `MemLp f p μ`, requesting that a function is almost everywhere
measurable and has finite `eLpNorm f p μ`.

This paragraph is devoted to the basic properties of these definitions. It is constructed as
follows: for a given property, we prove it for `eLpNorm'` and `eLpNormEssSup` when it makes sense,
deduce it for `eLpNorm`, and translate it in terms of `MemLp`.
-/


/-- `(∫ ‖f a‖^q ∂μ) ^ (1/q)`, which is a seminorm on the space of measurable functions for which
this quantity is finite.

Note: this is a purely auxiliary quantity; lemmas about `eLpNorm'` should only be used to
prove results about `eLpNorm`; every `eLpNorm'` lemma should have a `eLpNorm` version. -/
/-
**MeasureTheory.eLpNorm'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f 0 μ = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(∫ ‖f a‖^q ∂μ) ^ (1/q)`, which is a seminorm on the space of measurable functio
ns for which
this quantity is finite.

Note: this is a purely auxiliary quantity; lemmas about `eLpNorm'` should only b
e used to
prove results about `eLpNorm`; every `eLpNorm'` lemma should have a `eLpNorm` ve
rsion.
-/
def eLpNorm' {_ : MeasurableSpace α} (f : α → ε) (q : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  (∫⁻ a, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q)
/-
**MeasureTheory.eLpNorm'_eq_lintegral_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} [inst : ENorm ε] 
(f : α → ε) (q : ℝ)   (μ : MeasureTheory.Measure α), MeasureTheory.eLpNorm' f q 
μ = (∫⁻ (a : α), ‖f a‖ₑ ^ q ∂μ) ^ (1 / q)
参数：f : α → ε；q : ℝ；μ : MeasureTheory.Measure α；∫⁻ (a : α), ‖f a‖ₑ ^ q ∂μ；1 / q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
-/
lemma eLpNorm'_eq_lintegral_enorm (f : α → ε) (q : ℝ) (μ : Measure α) :
    eLpNorm' f q μ = (∫⁻ a, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q) :=
  rfl

/-- seminorm for `ℒ∞`, equal to the essential supremum of `‖f‖`. -/
/-
**MeasureTheory.eLpNormEssSup** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNormEssSup (f : α -> ε) (μ : Measure α)
参数：f : α -> ε；μ : Measure α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
seminorm for `ℒ∞`, equal to the essential supremum of `‖f‖`.
-/
def eLpNormEssSup (f : α → ε) (μ : Measure α) :=
  essSup (fun x => ‖f x‖ₑ) μ
/-
**MeasureTheory.eLpNormEssSup_eq_essSup_enorm** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：eLpNormEssSup_eq_essSup_enorm (f : α -> ε) (μ : Measure α) : eLpNormEssSup
 f μ = essSup (‖f ·‖ₑ) μ
参数：f : α -> ε；μ : Measure α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eLpNormEssSup_eq_essSup_enorm (f : α → ε) (μ : Measure α) :
    eLpNormEssSup f μ = essSup (‖f ·‖ₑ) μ := rfl

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`essSup ‖f‖ μ` for `p = ∞`. -/
/-
**MeasureTheory.eLpNorm** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm {_ : MeasurableSpace α} (f : α -> ε) (p : Real>=0∞) (μ : Measure α
参数：f : α -> ε；p : Real>=0∞。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1

--- 原说明 ---
`ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < 
∞` and to
`essSup ‖f‖ μ` for `p = ∞`.
-/
def eLpNorm {_ : MeasurableSpace α}
    (f : α → ε) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f (ENNReal.toReal p) μ

variable {μ ν : Measure α}
/-
**MeasureTheory.eLpNorm_eq_eLpNorm'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_eq_eLpNorm' (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε
} : eLpNorm f p μ = eLpNorm' f (ENNReal.toReal p) μ
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm_eq_eLpNorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → ε} :
    eLpNorm f p μ = eLpNorm' f (ENNReal.toReal p) μ := by simp [eLpNorm, hp_ne_zero, hp_ne_top]
/-
**MeasureTheory.eLpNorm_nnreal_eq_eLpNorm'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：eLpNorm_nnreal_eq_eLpNorm' {f : α -> ε} {p : Real>=0} (hp : p != 0) : eLpN
orm f p μ = eLpNorm' f p μ
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
lemma eLpNorm_nnreal_eq_eLpNorm' {f : α → ε} {p : ℝ≥0} (hp : p ≠ 0) :
    eLpNorm f p μ = eLpNorm' f p μ :=
  eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top
/-
**MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory`。
形式化陈述：eLpNorm_eq_lintegral_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : 
p != ∞) {f : α -> ε} : eLpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toR
eal)
参数：hp_ne_zero : p != 0；hp_ne_top : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `MeasureTheory.eLpNorm'_eq_lintegral_enorm`：∀ {α : Type u_1} {ε : Type u_
2} {m0 : MeasurableSpace α} [inst : ENorm ε] (f : α → ε) (q : ℝ)   (μ : MeasureT
heory.Measure α), MeasureTheory…
-/
lemma eLpNorm_eq_lintegral_rpow_enorm_toReal (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → ε} :
    eLpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top, eLpNorm'_eq_lintegral_enorm]

@[deprecated (since := "2026-02-09")]
alias eLpNorm_eq_lintegral_rpow_enorm := eLpNorm_eq_lintegral_rpow_enorm_toReal
/-
**MeasureTheory.eLpNorm_nnreal_eq_lintegral** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：eLpNorm_nnreal_eq_lintegral {f : α -> ε} {p : Real>=0} (hp : p != 0) : eLp
Norm f p μ = (∫⁻ x, ‖f x‖ₑ ^ (p : Real) ∂μ) ^ (1 / (p : Real))
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eLpNorm_nnreal_eq_eLpNorm'`：eLpNorm_nnreal_eq_eLpNorm' {f 
: α -> ε} {p : Real>=0} (hp : p != 0) : eLpNorm f p μ = eLpNorm' f p μ
-/
lemma eLpNorm_nnreal_eq_lintegral {f : α → ε} {p : ℝ≥0} (hp : p ≠ 0) :
    eLpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) :=
  eLpNorm_nnreal_eq_eLpNorm' hp
/-
**MeasureTheory.eLpNorm_one_eq_lintegral_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：eLpNorm_one_eq_lintegral_enorm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ
 ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `one_div_one`：one_div_one : (1 : G) / 1 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm_one_eq_lintegral_enorm {f : α → ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal one_ne_zero ENNReal.coe_ne_top,
    ENNReal.toReal_one, one_div_one, ENNReal.rpow_one]

@[simp]
/-
**MeasureTheory.eLpNorm_exponent_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_exponent_top {f : α -> ε} : eLpNorm f ∞ μ = eLpNormEssSup f μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eLpNorm_exponent_top {f : α → ε} : eLpNorm f ∞ μ = eLpNormEssSup f μ := by simp [eLpNorm]

/-- The property that `f : α → E` is a.e. strongly measurable and `(∫ ‖f a‖ ^ p ∂μ) ^ (1/p)`
is finite if `p < ∞`, or `essSup ‖f‖ < ∞` if `p = ∞`. -/
/-
**MeasureTheory.MemLp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：MemLp [TopologicalSpace ε] (f : α -> ε) (p : Real>=0∞) (μ : Measure α
参数：f : α -> ε；p : Real>=0∞。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that `f : α → E` is a.e. strongly measurable and `(∫ ‖f a‖ ^ p ∂μ) 
^ (1/p)`
is finite if `p < ∞`, or `essSup ‖f‖ < ∞` if `p = ∞`.
-/
def MemLp [TopologicalSpace ε] (f : α → ε) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞
/-
**MeasureTheory.MemLp.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.MemLp`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} [inst : ENorm ε] 
{μ : MeasureTheory.Measure α}   [inst_1 : TopologicalSpace ε] {f : α → ε} {p : E
NNReal},   MeasureTheory.MemLp f p μ → MeasureTheory.AEStronglyMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem MemLp.aestronglyMeasurable [TopologicalSpace ε] {f : α → ε} {p : ℝ≥0∞} (h : MemLp f p μ) :
    AEStronglyMeasurable f μ :=
  h.1
/-
**MeasureTheory.MemLp.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemL
p`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_2} {m0 : MeasurableSpace α} [inst : ENorm ε] 
{μ : MeasureTheory.Measure α}   [inst_1 : MeasurableSpace ε] [inst_2 : Topologic
alSpace ε] [TopologicalSpace.PseudoMetrizableSpace ε] [BorelSpace ε]   {f : α → 
ε} {p : ENNReal}, MeasureTheory.MemLp f p μ → AEMeasurable f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
-/
lemma MemLp.aemeasurable [MeasurableSpace ε] [TopologicalSpace ε]
    [TopologicalSpace.PseudoMetrizableSpace ε] [BorelSpace ε]
    {f : α → ε} {p : ℝ≥0∞} (hf : MemLp f p μ) :
    AEMeasurable f μ :=
  hf.aestronglyMeasurable.aemeasurable
/-
**MeasureTheory.lintegral_rpow_enorm_eq_rpow_eLpNorm'** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：lintegral_rpow_enorm_eq_rpow_eLpNorm' {f : α -> ε} (hq0_lt : 0 < q) : ∫⁻ a
, ‖f a‖ₑ ^ q ∂μ = eLpNorm' f q μ ^ q
参数：hq0_lt : 0 < q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'_eq_lintegral_enorm`：∀ {α : Type u_1} {ε : Type u_
2} {m0 : MeasurableSpace α} [inst : ENorm ε] (f : α → ε) (q : ℝ)   (μ : MeasureT
heory.Measure α), MeasureTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
-/
theorem lintegral_rpow_enorm_eq_rpow_eLpNorm' {f : α → ε} (hq0_lt : 0 < q) :
    ∫⁻ a, ‖f a‖ₑ ^ q ∂μ = eLpNorm' f q μ ^ q := by
  rw [eLpNorm'_eq_lintegral_enorm, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀, ENNReal.rpow_one]
  exact hq0_lt.ne'
/-
**MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：eLpNorm_nnreal_pow_eq_lintegral {f : α -> ε} {p : Real>=0} (hp : p != 0) :
 eLpNorm f p μ ^ (p : Real) = ∫⁻ x, ‖f x‖ₑ ^ (p : Real) ∂μ
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `MeasureTheory.lintegral_rpow_enorm_eq_rpow_eLpNorm'`：lintegral_rpow_enor
m_eq_rpow_eLpNorm' {f : α -> ε} (hq0_lt : 0 < q) : ∫⁻ a, ‖f a‖ₑ ^ q ∂μ = eLpNorm
' f q μ ^ q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eLpNorm_nnreal_pow_eq_lintegral {f : α → ε} {p : ℝ≥0} (hp : p ≠ 0) :
    eLpNorm f p μ ^ (p : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) ∂μ := by
  simp [eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hp)]

/-- Real-valued `ℒp` seminorm, equal to `0` for `p = 0`, to `(∫ ‖f a‖^p ∂μ) ^ p⁻¹` for `0 < p < ∞`
and to `essSup ‖f‖ μ` for `p = ∞`.

This is well-defined only if `MemLp f p μ`. Otherwise, it equals `0`. -/
/-
**MeasureTheory.lpNorm** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm (f : α -> E) (p : Real>=0∞) (μ : Measure α) : Real
参数：f : α -> E；p : Real>=0∞；μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Real-valued `ℒp` seminorm, equal to `0` for `p = 0`, to `(∫ ‖f a‖^p ∂μ) ^ p⁻¹` f
or `0 < p < ∞`
and to `essSup ‖f‖ μ` for `p = ∞`.

This is well-defined only if `MemLp f p μ`. Otherwise, it equals `0`.
-/
noncomputable def lpNorm (f : α → E) (p : ℝ≥0∞) (μ : Measure α) : ℝ :=
  open scoped Classical in if AEStronglyMeasurable f μ then (eLpNorm f p μ).toReal else 0

end Lp

end MeasureTheory

