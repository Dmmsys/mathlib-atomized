/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Bernoulli distribution

We define the **Bernoulli distribution** over an arbitrary measurable space `X`. Given `x y : X`
and `p : I` (`I` is the `unitInterval`),
`Ber(x, y, p) := toNNReal p • dirac x + toNNReal (σ p) • dirac y`.
It is the measure which gives mass `p` to `{x}` and `1 - p` to `{y}`.

## Main definition

* `bernoulliMeasure x y p`: The measure `Ber(x, y, p)` which gives mass
  `p` to `{x}` and `1 - p` to `{y}`.

## Notation

* `Ber(x, y, p)`: notation for `bernoulliMeasure x y p`.

## Tags

Bernoulli distribution
-/

public section

open MeasureTheory Measure unitInterval
open scoped ENNReal

namespace ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {x y : X} {p : I}

/-- The **Bernoulli distribution** over an arbitrary measurable space `X`.
Given `x y : X` and `p : I` (`I` is the `unitInterval`),
it is the measure which gives mass `p` to `{x}` and `1 - p` to `{y}`. -/
@[expose]
/-
**ProbabilityTheory.bernoulliMeasure** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：bernoulliMeasure (x y : X) (p : I) : Measure X
参数：x y : X；p : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Bernoulli distribution** over an arbitrary measurable space `X`.
Given `x y : X` and `p : I` (`I` is the `unitInterval`),
it is the measure which gives mass `p` to `{x}` and `1 - p` to `{y}`.
-/
noncomputable def bernoulliMeasure (x y : X) (p : I) : Measure X :=
  toNNReal p • dirac x + toNNReal (σ p) • dirac y

@[inherit_doc]
scoped notation "Ber(" x ", " y ", " p ")" => bernoulliMeasure x y p
/-
**ProbabilityTheory.bernoulliMeasure_def** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：bernoulliMeasure_def (x y : X) (p : I) : Ber(x, y, p) = toNNReal p • dirac
 x + toNNReal (σ p) • dirac y
参数：x y : X；p : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bernoulliMeasure_def (x y : X) (p : I) :
    Ber(x, y, p) = toNNReal p • dirac x + toNNReal (σ p) • dirac y := rfl

@[simp]
/-
**ProbabilityTheory.bernoulliMeasure_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：bernoulliMeasure_zero (x y : X) : bernoulliMeasure x y 0 = dirac y
参数：x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `unitInterval.symm_zero`：symm_zero : σ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bernoulliMeasure_zero (x y : X) : bernoulliMeasure x y 0 = dirac y := by
  simp [bernoulliMeasure_def]

@[simp]
/-
**ProbabilityTheory.bernoulliMeasure_one** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：bernoulliMeasure_one (x y : X) : bernoulliMeasure x y 1 = dirac x
参数：x y : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `unitInterval.symm_one`：symm_one : σ 1 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bernoulliMeasure_one (x y : X) : bernoulliMeasure x y 1 = dirac x := by
  simp [bernoulliMeasure_def]
/-
**ProbabilityTheory.bernoulliMeasure_apply** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：bernoulliMeasure_apply (p : I) {s : Set X} (hs : MeasurableSet s) [Decidab
lePred (· in s)] : Ber(x, y, p) s = if x in s then if y in s then (1 : Real>=0∞)
 else toNNReal p else if y in s then toNNReal (σ p) else 0
参数：p : I；hs : MeasurableSet s；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `ENNReal.smul_one`：smul_one (c : Real>=0) : c • (1 : Real>=0∞) = (c : Rea
l>=0∞)
· 使用定理 `unitInterval.toNNReal_add_toNNReal_symm`：∀ (x : ↑unitInterval), unitInte
rval.toNNReal x + unitInterval.toNNReal (unitInterval.symm x) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma bernoulliMeasure_apply (p : I) {s : Set X}
    (hs : MeasurableSet s) [DecidablePred (· ∈ s)] :
    Ber(x, y, p) s =
      if x ∈ s
        then if y ∈ s
          then (1 : ℝ≥0∞)
          else toNNReal p
        else if y ∈ s
          then toNNReal (σ p)
          else 0 := by
  split_ifs <;> simp_all [bernoulliMeasure_def, ← ENNReal.coe_add]
/-
**ProbabilityTheory.bernoulliMeasure_real_apply** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：bernoulliMeasure_real_apply (p : I) {s : Set X} (hs : MeasurableSet s) [De
cidablePred (· in s)] : Ber(x, y, p).real s = if x in s then if y in s then (1 :
 Real) else toNNReal p else if y in s then toNNReal (σ p) else 0
参数：p : I；hs : MeasurableSet s；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bernoulliMeasure_apply`：bernoulliMeasure_apply (p : I)
 {s : Set X} (hs : MeasurableSet s) [DecidablePred (· in s)] : Ber(x, y, p) s = 
if x in s then if y in s then …
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bernoulliMeasure_real_apply (p : I) {s : Set X}
    (hs : MeasurableSet s) [DecidablePred (· ∈ s)] :
    Ber(x, y, p).real s =
      if x ∈ s
        then if y ∈ s
          then (1 : ℝ)
          else toNNReal p
        else if y ∈ s
          then toNNReal (σ p)
          else 0 := by
  simp [measureReal_def, bernoulliMeasure_apply p hs, apply_ite ENNReal.toReal]

@[simp]
/-
**ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_mem** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：bernoulliMeasure_apply_of_mem_of_mem (p : I) {s : Set X} (hs : MeasurableS
et s) (hx : x in s) (hy : y in s) : Ber(x, y, p) s = 1
参数：p : I；hs : MeasurableSet s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bernoulliMeasure_apply`：bernoulliMeasure_apply (p : I)
 {s : Set X} (hs : MeasurableSet s) [DecidablePred (· in s)] : Ber(x, y, p) s = 
if x in s then if y in s then …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bernoulliMeasure_apply_of_mem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∈ s) :
    Ber(x, y, p) s = 1 := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
/-
**ProbabilityTheory.bernoulliMeasure_real_apply_of_mem_of_mem** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory`。
形式化陈述：bernoulliMeasure_real_apply_of_mem_of_mem (p : I) {s : Set X} (hs : Measur
ableSet s) (hx : x in s) (hy : y in s) : Ber(x, y, p).real s = 1
参数：p : I；hs : MeasurableSet s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bernoulliMeasure_real_apply`：bernoulliMeasure_real_app
ly (p : I) {s : Set X} (hs : MeasurableSet s) [DecidablePred (· in s)] : Ber(x, 
y, p).real s = if x in s then if y …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bernoulliMeasure_real_apply_of_mem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∈ s) :
    Ber(x, y, p).real s = 1 := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
/-
**ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：bernoulliMeasure_apply_of_mem_of_notMem (p : I) {s : Set X} (hs : Measurab
leSet s) (hx : x in s) (hy : y ∉ s) : Ber(x, y, p) s = toNNReal p
参数：p : I；hs : MeasurableSet s；hx : x in s；hy : y ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bernoulliMeasure_apply`：bernoulliMeasure_apply (p : I)
 {s : Set X} (hs : MeasurableSet s) [DecidablePred (· in s)] : Ber(x, y, p) s = 
if x in s then if y in s then …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bernoulliMeasure_apply_of_mem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∉ s) :
    Ber(x, y, p) s = toNNReal p := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
/-
**ProbabilityTheory.bernoulliMeasure_real_apply_of_mem_of_notMem** 是 Mathlib 中的一
个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：bernoulliMeasure_real_apply_of_mem_of_notMem (p : I) {s : Set X} (hs : Mea
surableSet s) (hx : x in s) (hy : y ∉ s) : Ber(x, y, p).real s = p
参数：p : I；hs : MeasurableSet s；hx : x in s；hy : y ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bernoulliMeasure_real_apply`：bernoulliMeasure_real_app
ly (p : I) {s : Set X} (hs : MeasurableSet s) [DecidablePred (· in s)] : Ber(x, 
y, p).real s = if x in s then if y …
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bernoulliMeasure_real_apply_of_mem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∈ s) (hy : y ∉ s) :
    Ber(x, y, p).real s = p := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
/-
**ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：bernoulliMeasure_apply_of_notMem_of_mem (p : I) {s : Set X} (hs : Measurab
leSet s) (hx : x ∉ s) (hy : y in s) : Ber(x, y, p) s = toNNReal (σ p)
参数：p : I；hs : MeasurableSet s；hx : x ∉ s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bernoulliMeasure_apply`：bernoulliMeasure_apply (p : I)
 {s : Set X} (hs : MeasurableSet s) [DecidablePred (· in s)] : Ber(x, y, p) s = 
if x in s then if y in s then …
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bernoulliMeasure_apply_of_notMem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∈ s) :
    Ber(x, y, p) s = toNNReal (σ p) := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
/-
**ProbabilityTheory.bernoulliMeasure_real_apply_of_notMem_of_mem** 是 Mathlib 中的一
个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：bernoulliMeasure_real_apply_of_notMem_of_mem (p : I) {s : Set X} (hs : Mea
surableSet s) (hx : x ∉ s) (hy : y in s) : Ber(x, y, p).real s = 1 - p
参数：p : I；hs : MeasurableSet s；hx : x ∉ s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bernoulliMeasure_real_apply`：bernoulliMeasure_real_app
ly (p : I) {s : Set X} (hs : MeasurableSet s) [DecidablePred (· in s)] : Ber(x, 
y, p).real s = if x in s then if y …
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bernoulliMeasure_real_apply_of_notMem_of_mem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∈ s) :
    Ber(x, y, p).real s = 1 - p := by
  classical
  simp_all [bernoulliMeasure_real_apply]

@[simp]
/-
**ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_notMem** 是 Mathlib 中的一个引
理，位于命名空间 `ProbabilityTheory`。
形式化陈述：bernoulliMeasure_apply_of_notMem_of_notMem (p : I) {s : Set X} (hs : Measu
rableSet s) (hx : x ∉ s) (hy : y ∉ s) : Ber(x, y, p) s = 0
参数：p : I；hs : MeasurableSet s；hx : x ∉ s；hy : y ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bernoulliMeasure_apply`：bernoulliMeasure_apply (p : I)
 {s : Set X} (hs : MeasurableSet s) [DecidablePred (· in s)] : Ber(x, y, p) s = 
if x in s then if y in s then …
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bernoulliMeasure_apply_of_notMem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∉ s) :
    Ber(x, y, p) s = 0 := by
  classical
  simp_all [bernoulliMeasure_apply]

@[simp]
/-
**ProbabilityTheory.bernoulliMeasure_real_apply_of_notMem_of_notMem** 是 Mathlib 
中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：bernoulliMeasure_real_apply_of_notMem_of_notMem (p : I) {s : Set X} (hs : 
MeasurableSet s) (hx : x ∉ s) (hy : y ∉ s) : Ber(x, y, p).real s = 0
参数：p : I；hs : MeasurableSet s；hx : x ∉ s；hy : y ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bernoulliMeasure_real_apply`：bernoulliMeasure_real_app
ly (p : I) {s : Set X} (hs : MeasurableSet s) [DecidablePred (· in s)] : Ber(x, 
y, p).real s = if x in s then if y …
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bernoulliMeasure_real_apply_of_notMem_of_notMem (p : I) {s : Set X}
    (hs : MeasurableSet s) (hx : x ∉ s) (hy : y ∉ s) :
    Ber(x, y, p).real s = 0 := by
  classical
  simp_all [bernoulliMeasure_real_apply]
/-
**ProbabilityTheory.** 是 Mathlib 中的一个实例，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsProbabilityMeasure Ber(x, y, p) where
  measure_univ := by simp [bernoulliMeasure_def]

@[simp]
/-
**ProbabilityTheory.bernoulliMeasure_self_eq_dirac** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：bernoulliMeasure_self_eq_dirac (x : X) (p : I) : bernoulliMeasure x x p = 
dirac x
参数：x : X；p : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `unitInterval.toNNReal_add_toNNReal_symm`：∀ (x : ↑unitInterval), unitInte
rval.toNNReal x + unitInterval.toNNReal (unitInterval.symm x) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bernoulliMeasure_self_eq_dirac (x : X) (p : I) :
    bernoulliMeasure x x p = dirac x := by
  simp [bernoulliMeasure_def, ← add_smul]

@[simp]
/-
**ProbabilityTheory.map_bernoulliMeasure** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：map_bernoulliMeasure [MeasurableSingletonClass X] [MeasurableSingletonClas
s Y] (x y : X) (f : X -> Y) (p : I) : Ber(x, y, p).map f = bernoulliMeasure (f x
) (f y) p
参数：x y : X；f : X -> Y；p : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.aemeasurable_dirac`：aemeasurable_dirac [MeasurableSingleto
nClass α] {a : α} {f : α -> β} : AEMeasurable f (Measure.dirac a)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AEMeasurable.map_add₀`：∀ {α : Type u_2} {β : Type u_3} {m0 : MeasurableS
pace α} [inst : MeasurableSpace β] {μ ν : MeasureTheory.Measure α}   {f : α → β}
,   AEMeasu…
· 使用定理 `AEMeasurable.smul_measure`：smul_measure [SMul R Real>=0∞] [IsScalarTower
 R Real>=0∞ Real>=0∞] (h : AEMeasurable f μ) (c : R) : AEMeasurable f (c • μ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用定理 `MeasureTheory.Measure.map_dirac`：∀ {α : Type u_1} {β : Type u_2} [inst :
 MeasurableSpace α] [inst_1 : MeasurableSpace β] [MeasurableSingletonClass α]   
[MeasurableSingletonC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_bernoulliMeasure [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (x y : X) (f : X → Y) (p : I) :
    Ber(x, y, p).map f = bernoulliMeasure (f x) (f y) p := by
  have hf (x : X) : AEMeasurable f (dirac x) := by fun_prop
  simp only [bernoulliMeasure_def]
  rw [AEMeasurable.map_add₀ (by fun_prop) (by fun_prop)]
  simp
/-
**ProbabilityTheory.map_bernoulliMeasure'** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：map_bernoulliMeasure' (x y : X) {f : X -> Y} (hf : Measurable f) (p : I) :
 Ber(x, y, p).map f = bernoulliMeasure (f x) (f y) p
参数：x y : X；hf : Measurable f；p : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_add`：∀ {α : Type u_1} {β : Type u_2} {mα : Mea
surableSpace α} {mβ : MeasurableSpace β} (μ ν : MeasureTheory.Measure α)   {f : 
α → β},   Measurabl…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用定理 `MeasureTheory.Measure.map_dirac'`：map_dirac' {f : α -> β} (hf : Measurab
le f) (a : α) : (dirac a).map f = dirac (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_bernoulliMeasure' (x y : X) {f : X → Y} (hf : Measurable f) (p : I) :
    Ber(x, y, p).map f = bernoulliMeasure (f x) (f y) p := by
  simp [bernoulliMeasure_def, Measure.map_add _ _ hf, Measure.map_smul, map_dirac' hf]

section Integral

variable {E : Type*} [NormedAddCommGroup E]

/-
**ProbabilityTheory.integrable_bernoulliMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：integrable_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I)
 (f : X -> E) : Integrable f Ber(x, y, p)
参数：x y : X；p : I；f : X -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma integrable_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I) (f : X → E) :
    Integrable f Ber(x, y, p) := by
  simp [bernoulliMeasure_def, integrable_add_measure, integrable_dirac,
    Integrable.smul_measure_nnreal]

variable [NormedSpace ℝ E] [CompleteSpace E]
/-
**ProbabilityTheory.integral_bernoulliMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：integral_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I) (
f : X -> E) : ∫ z, f z ∂Ber(x, y, p) = (p : Real) • (f x) + (1 - p : Real) • (f 
y)
参数：x y : X；p : I；f : X -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.bernoulliMeasure_def`：bernoulliMeasure_def (x y : X) (
p : I) : Ber(x, y, p) = toNNReal p • dirac x + toNNReal (σ p) • dirac y
· 使用定理 `MeasureTheory.integral_add_measure`：integral_add_measure {f : α -> G} (h
μ : Integrable f μ) (hν : Integrable f ν) : ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ 
x, f x ∂ν
· 使用定理 `MeasureTheory.Integrable.smul_measure_nnreal`：∀ {α : Type u_1} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalS
pace ε]   [inst_1 : ESeminormedAdd…
· 使用引理 `MeasureTheory.integrable_dirac`：integrable_dirac [MeasurableSingletonCla
ss α] {a : α} {f : α -> ε} (hfa : ‖f a‖ₑ < ∞) : Integrable f (Measure.dirac a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_smul_nnreal_measure`：integral_smul_nnreal_measure
 (f : α -> G) (c : Real>=0) : ∫ x, f x ∂(c • μ) = c • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I) (f : X → E) :
    ∫ z, f z ∂Ber(x, y, p) = (p : ℝ) • (f x) + (1 - p : ℝ) • (f y) := by
  rw [bernoulliMeasure_def, integral_add_measure]
  · simp [NNReal.smul_def]
  all_goals exact (integrable_dirac (by simp)).smul_measure_nnreal

end Integral

end ProbabilityTheory

