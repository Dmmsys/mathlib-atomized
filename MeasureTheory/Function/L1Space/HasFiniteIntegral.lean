/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Function with finite integral

In this file we define the predicate `HasFiniteIntegral`, which is then used to define the
predicate `Integrable` in the corresponding file.

## Main definition

* Let `f : α → β` be a function, where `α` is a `MeasureSpace` and `β` a `NormedAddCommGroup`.
  Then `HasFiniteIntegral f` means `∫⁻ a, ‖f a‖ₑ < ∞`.

## Tags

finite integral

-/

@[expose] public section

noncomputable section

open Topology ENNReal MeasureTheory NNReal

open Set Filter TopologicalSpace ENNReal EMetric MeasureTheory

variable {α β γ ε ε' ε'' : Type*} {m : MeasurableSpace α} {μ ν : Measure α}
variable [NormedAddCommGroup β] [NormedAddCommGroup γ] [ENorm ε] [ENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']

namespace MeasureTheory

/-! ### Some results about the Lebesgue integral involving a normed group -/

/-
**MeasureTheory.lintegral_enorm_eq_lintegral_edist** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：lintegral_enorm_eq_lintegral_edist (f : α -> β) : ∫⁻ a, ‖f a‖ₑ ∂μ = ∫⁻ a, 
edist (f a) 0 ∂μ
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Some results about the Lebesgue integral involving a normed group
-/
lemma lintegral_enorm_eq_lintegral_edist (f : α → β) :
    ∫⁻ a, ‖f a‖ₑ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ := by simp only [edist_zero_right]
/-
**MeasureTheory.lintegral_norm_eq_lintegral_edist** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：lintegral_norm_eq_lintegral_edist (f : α -> β) : ∫⁻ a, ENNReal.ofReal ‖f a
‖ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_norm_eq_lintegral_edist (f : α → β) :
    ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp only [ofReal_norm, edist_zero_right]
/-
**MeasureTheory.lintegral_edist_triangle** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：lintegral_edist_triangle {f g h : α -> β} (hf : AEStronglyMeasurable f μ) 
(hh : AEStronglyMeasurable h μ) : (∫⁻ a, edist (f a) (g a) ∂μ) <= (∫⁻ a, edist (
f a) (h a) ∂μ) + ∫⁻ a, edist (g a) (h a) ∂μ
参数：hf : AEStronglyMeasurable f μ；hh : AEStronglyMeasurable h μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_left'`：lintegral_add_left' {f : α -> Real>=0
∞} (hf : AEMeasurable f μ) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a 
∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.edist`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : PseudoMetricSpa
ce β]   {f g : α → β},   Measu…
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `edist_triangle_right`：edist_triangle_right (x y z : α) : edist x y <= ed
ist x z + edist y z
-/
theorem lintegral_edist_triangle {f g h : α → β} (hf : AEStronglyMeasurable f μ)
    (hh : AEStronglyMeasurable h μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) ≤ (∫⁻ a, edist (f a) (h a) ∂μ) + ∫⁻ a, edist (g a) (h a) ∂μ := by
  rw [← lintegral_add_left' (hf.edist hh)]
  refine lintegral_mono fun a => ?_
  apply edist_triangle_right

-- Yaël: Why do the following four lemmas even exist?
/-
**MeasureTheory.lintegral_enorm_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_enorm_zero : ∫⁻ _ : α, ‖(0 : ε'')‖ₑ ∂μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_enorm_zero : ∫⁻ _ : α, ‖(0 : ε'')‖ₑ ∂μ = 0 := by simp
/-
**MeasureTheory.lintegral_enorm_add_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：lintegral_enorm_add_left {f : α -> ε''} (hf : AEStronglyMeasurable f μ) (g
 : α -> ε') : ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ + ∫⁻ a, ‖g a‖ₑ ∂μ
参数：hf : AEStronglyMeasurable f μ；g : α -> ε'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_add_left'`：lintegral_add_left' {f : α -> Real>=0
∞} (hf : AEMeasurable f μ) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a 
∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
-/
theorem lintegral_enorm_add_left {f : α → ε''} (hf : AEStronglyMeasurable f μ) (g : α → ε') :
    ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ + ∫⁻ a, ‖g a‖ₑ ∂μ :=
  lintegral_add_left' hf.enorm _
/-
**MeasureTheory.lintegral_enorm_add_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：lintegral_enorm_add_right (f : α -> ε') {g : α -> ε''} (hg : AEStronglyMea
surable g μ) : ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ + ∫⁻ a, ‖g a‖ₑ ∂μ
参数：f : α -> ε'；hg : AEStronglyMeasurable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_add_right'`：lintegral_add_right' (f : α -> Real>
=0∞) {g : α -> Real>=0∞} (hg : AEMeasurable g μ) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f 
a ∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
-/
theorem lintegral_enorm_add_right (f : α → ε') {g : α → ε''} (hg : AEStronglyMeasurable g μ) :
    ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ + ∫⁻ a, ‖g a‖ₑ ∂μ :=
  lintegral_add_right' _ hg.enorm
/-
**MeasureTheory.lintegral_enorm_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_enorm_neg {f : α -> β} : ∫⁻ a, ‖(-f) a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `enorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ₑ
 = ‖a‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_enorm_neg {f : α → β} : ∫⁻ a, ‖(-f) a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ := by simp

/-! ### The predicate `HasFiniteIntegral` -/


/-- `HasFiniteIntegral f μ` means that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `HasFiniteIntegral f` means `HasFiniteIntegral f volume`. -/
@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：HasFiniteIntegral {_ : MeasurableSpace α} (f : α -> ε) (μ : Measure α
参数：f : α -> ε。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasFiniteIntegral f μ` means that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `HasFiniteIntegral f` means `HasFiniteIntegral f volume`.
-/
def HasFiniteIntegral {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
/-
**MeasureTheory.hasFiniteIntegral_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hasFiniteIntegral_def {_ : MeasurableSpace α} (f : α -> ε) (μ : Measure α)
 : HasFiniteIntegral f μ ↔ (∫⁻ a, ‖f a‖ₑ ∂μ < ∞)
参数：f : α -> ε；μ : Measure α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasFiniteIntegral_def {_ : MeasurableSpace α} (f : α → ε) (μ : Measure α) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ‖f a‖ₑ ∂μ < ∞) :=
  Iff.rfl
/-
**MeasureTheory.hasFiniteIntegral_iff_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：hasFiniteIntegral_iff_enorm {f : α -> ε} : HasFiniteIntegral f μ ↔ ∫⁻ a, ‖
f a‖ₑ ∂μ < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFiniteIntegral_iff_enorm {f : α → ε} : HasFiniteIntegral f μ ↔ ∫⁻ a, ‖f a‖ₑ ∂μ < ∞ := by
  simp only [HasFiniteIntegral]
/-
**MeasureTheory.hasFiniteIntegral_iff_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：hasFiniteIntegral_iff_norm (f : α -> β) : HasFiniteIntegral f μ ↔ (∫⁻ a, E
NNReal.ofReal ‖f a‖ ∂μ) < ∞
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFiniteIntegral_iff_norm (f : α → β) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) < ∞ := by
  simp only [hasFiniteIntegral_iff_enorm, ofReal_norm]
/-
**MeasureTheory.hasFiniteIntegral_iff_edist** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：hasFiniteIntegral_iff_edist (f : α -> β) : HasFiniteIntegral f μ ↔ (∫⁻ a, 
edist (f a) 0 ∂μ) < ∞
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFiniteIntegral_iff_edist (f : α → β) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, edist (f a) 0 ∂μ) < ∞ := by
  simp only [hasFiniteIntegral_iff_norm, edist_dist, dist_zero_right]
/-
**MeasureTheory.hasFiniteIntegral_iff_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：hasFiniteIntegral_iff_ofReal {f : α -> Real} (h : 0 <=ᵐ[μ] f) : HasFiniteI
ntegral f μ ↔ (∫⁻ a, ENNReal.ofReal (f a) ∂μ) < ∞
参数：h : 0 <=ᵐ[μ] f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_enorm`：hasFiniteIntegral_iff_enorm {
f : α -> ε} : HasFiniteIntegral f μ ↔ ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
· 使用定理 `MeasureTheory.lintegral_enorm_of_ae_nonneg`：lintegral_enorm_of_ae_nonneg
 {f : α -> Real} (h_nonneg : 0 <=ᵐ[μ] f) : ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, .ofReal (f x)
 ∂μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasFiniteIntegral_iff_ofReal {f : α → ℝ} (h : 0 ≤ᵐ[μ] f) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal (f a) ∂μ) < ∞ := by
  rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_of_ae_nonneg h]
/-
**MeasureTheory.hasFiniteIntegral_iff_ofNNReal** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：hasFiniteIntegral_iff_ofNNReal {f : α -> Real>=0} : HasFiniteIntegral (fun
 x => (f x : Real)) μ ↔ (∫⁻ a, f a ∂μ) < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFiniteIntegral_iff_ofNNReal {f : α → ℝ≥0} :
    HasFiniteIntegral (fun x => (f x : ℝ)) μ ↔ (∫⁻ a, f a ∂μ) < ∞ := by
  simp [hasFiniteIntegral_iff_norm]
/-
**MeasureTheory.HasFiniteIntegral.mono_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ
 : MeasureTheory.Measure α} [inst : ENorm ε]   [inst_1 : ENorm ε'] {f : α → ε} {
g : α → ε'},   MeasureTheory.HasFiniteIntegral g μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ ‖g
 a‖ₑ) → MeasureTheory.HasFiniteIntegral f μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ ‖g a‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
-/
theorem HasFiniteIntegral.mono_enorm {f : α → ε} {g : α → ε'} (hg : HasFiniteIntegral g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ ‖g a‖ₑ) : HasFiniteIntegral f μ := by
  simp only [hasFiniteIntegral_iff_enorm] at *
  calc
    (∫⁻ a, ‖f a‖ₑ ∂μ) ≤ ∫⁻ a : α, ‖g a‖ₑ ∂μ := lintegral_mono_ae h
    _ < ∞ := hg
/-
**MeasureTheory.HasFiniteIntegral.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] [inst_1 : NormedAddCo
mmGroup γ] {f : α → β} {g : α → γ},   MeasureTheory.HasFiniteIntegral g μ → (∀ᵐ 
(a : α) ∂μ, ‖f a‖ ≤ ‖g a‖) → MeasureTheory.HasFiniteIntegral f μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ ‖g a‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono_enorm`：∀ {α : Type u_1} {ε : Type u
_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst 
: ENorm ε]   [inst_1 : ENorm ε']…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `enorm_le_iff_norm_le`：∀ {E : Type u_5} {F : Type u_6} [inst : Seminormed
AddGroup E] [inst_1 : SeminormedAddGroup F] {x : E} {y : F},   ‖x‖ₑ ≤ ‖y‖ₑ ↔ ‖x‖
 ≤ ‖y‖
-/
theorem HasFiniteIntegral.mono {f : α → β} {g : α → γ} (hg : HasFiniteIntegral g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ ‖g a‖) : HasFiniteIntegral f μ :=
  hg.mono_enorm <| h.mono fun _x hx ↦ enorm_le_iff_norm_le.mpr hx
/-
**MeasureTheory.HasFiniteIntegral.mono_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   [inst_1 : Lattice β] [HasSolidNorm β
] [AddLeftMono β] {f g : α → β},   MeasureTheory.HasFiniteIntegral g μ →     (∀ᵐ
 (a : α) ∂μ, 0 ≤ f a) → (∀ᵐ (a : α) ∂μ, f a ≤ g a) → MeasureTheory.HasFiniteInte
gral f μ
参数：∀ᵐ (a : α) ∂μ, 0 ≤ f a；∀ᵐ (a : α) ∂μ, f a ≤ g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup β] [inst_1…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `norm_le_norm_of_abs_le_abs`：norm_le_norm_of_abs_le_abs {a b : α} (h : |a
| <= |b|) : ‖a‖ <= ‖b‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem HasFiniteIntegral.mono_nonneg [Lattice β] [HasSolidNorm β] [AddLeftMono β] {f g : α → β}
    (hg : HasFiniteIntegral g μ) (hnonneg : ∀ᵐ a ∂μ, 0 ≤ f a) (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    HasFiniteIntegral f μ := by
  refine HasFiniteIntegral.mono hg ?_
  filter_upwards [hnonneg, h] with a hn ha
  apply norm_le_norm_of_abs_le_abs
  rwa [abs_of_nonneg hn, abs_of_nonneg (hn.trans ha)]
/-
**MeasureTheory.HasFiniteIntegral.mono'_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : ENorm ε] {f : α → ε}   {g : α → ENNReal},   MeasureTheory.Ha
sFiniteIntegral g μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ g a) → MeasureTheory.HasFiniteInt
egral f μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono_enorm`：∀ {α : Type u_1} {ε : Type u
_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst 
: ENorm ε]   [inst_1 : ENorm ε']…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem HasFiniteIntegral.mono'_enorm {f : α → ε} {g : α → ℝ≥0∞} (hg : HasFiniteIntegral g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ g a) : HasFiniteIntegral f μ :=
  hg.mono_enorm <| h.mono fun _x hx ↦ le_trans hx le_rfl
/-
**MeasureTheory.HasFiniteIntegral.mono'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β} {g : α → ℝ},   MeasureTh
eory.HasFiniteIntegral g μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ g a) → MeasureTheory.HasFin
iteIntegral f μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup β] [inst_1…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem HasFiniteIntegral.mono' {f : α → β} {g : α → ℝ} (hg : HasFiniteIntegral g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : HasFiniteIntegral f μ :=
  hg.mono <| h.mono fun _x hx => le_trans hx (le_abs_self _)
/-
**MeasureTheory.HasFiniteIntegral.congr'_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ
 : MeasureTheory.Measure α} [inst : ENorm ε]   [inst_1 : ENorm ε'] {f : α → ε} {
g : α → ε'},   MeasureTheory.HasFiniteIntegral f μ → (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g
 a‖ₑ) → MeasureTheory.HasFiniteIntegral g μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g a‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono_enorm`：∀ {α : Type u_1} {ε : Type u
_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst 
: ENorm ε]   [inst_1 : ENorm ε']…
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem HasFiniteIntegral.congr'_enorm {f : α → ε} {g : α → ε'} (hf : HasFiniteIntegral f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : HasFiniteIntegral g μ :=
  hf.mono_enorm <| EventuallyEq.le <| EventuallyEq.symm h
/-
**MeasureTheory.HasFiniteIntegral.congr'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : NormedAddCommGroup β] [inst_1 : NormedAddCo
mmGroup γ] {f : α → β} {g : α → γ},   MeasureTheory.HasFiniteIntegral f μ → (∀ᵐ 
(a : α) ∂μ, ‖f a‖ = ‖g a‖) → MeasureTheory.HasFiniteIntegral g μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ = ‖g a‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup β] [inst_1…
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem HasFiniteIntegral.congr' {f : α → β} {g : α → γ} (hf : HasFiniteIntegral f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : HasFiniteIntegral g μ :=
  hf.mono <| EventuallyEq.le <| EventuallyEq.symm h
/-
**MeasureTheory.hasFiniteIntegral_congr'_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ
 : MeasureTheory.Measure α} [inst : ENorm ε]   [inst_1 : ENorm ε'] {f : α → ε} {
g : α → ε'},   (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) → (MeasureTheory.HasFiniteIntegr
al f μ ↔ MeasureTheory.HasFiniteIntegral g μ)
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ₑ = ‖g a‖ₑ；MeasureTheory.HasFiniteIntegral f μ ↔ MeasureT
heory.HasFiniteIntegral g μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.congr'_enorm`：∀ {α : Type u_1} {ε : Type
 u_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [ins
t : ENorm ε]   [inst_1 : ENorm ε']…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem hasFiniteIntegral_congr'_enorm {f : α → ε} {g : α → ε'} (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
  ⟨fun hf => hf.congr'_enorm h, fun hg => hg.congr'_enorm <| EventuallyEq.symm h⟩
/-
**MeasureTheory.hasFiniteIntegral_congr'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：hasFiniteIntegral_congr'_enorm {f : α -> ε} {g : α -> ε'} (h : forallᵐ a ∂
μ, ‖f a‖ₑ = ‖g a‖ₑ) : HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ
参数：h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.congr'`：∀ {α : Type u_1} {β : Type u_2} 
{γ : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : N
ormedAddCommGroup β] [inst_1…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem hasFiniteIntegral_congr' {f : α → β} {g : α → γ} (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr' <| EventuallyEq.symm h⟩
/-
**MeasureTheory.HasFiniteIntegral.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : ENorm ε] {f g : α → ε},   MeasureTheory.HasFiniteIntegral f 
μ → f =ᵐ[μ] g → MeasureTheory.HasFiniteIntegral g μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.congr'_enorm`：∀ {α : Type u_1} {ε : Type
 u_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [ins
t : ENorm ε]   [inst_1 : ENorm ε']…
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem HasFiniteIntegral.congr {f g : α → ε} (hf : HasFiniteIntegral f μ) (h : f =ᵐ[μ] g) :
    HasFiniteIntegral g μ :=
  hf.congr'_enorm <| h.fun_comp enorm
/-
**MeasureTheory.hasFiniteIntegral_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：hasFiniteIntegral_congr {f g : α -> ε} (h : f =ᵐ[μ] g) : HasFiniteIntegral
 f μ ↔ HasFiniteIntegral g μ
参数：h : f =ᵐ[μ] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.hasFiniteIntegral_congr'_enorm`：∀ {α : Type u_1} {ε : Type
 u_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [ins
t : ENorm ε]   [inst_1 : ENorm ε']…
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem hasFiniteIntegral_congr {f g : α → ε} (h : f =ᵐ[μ] g) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
  hasFiniteIntegral_congr'_enorm <| h.fun_comp enorm
/-
**MeasureTheory.hasFiniteIntegral_const_iff_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：hasFiniteIntegral_const_iff_enorm {c : ε} (hc : ‖c‖ₑ != ∞) : HasFiniteInte
gral (fun _ : α => c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasure μ
参数：hc : ‖c‖ₑ != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem hasFiniteIntegral_const_iff_enorm {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    HasFiniteIntegral (fun _ : α ↦ c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasure μ := by
  simpa [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top, ENNReal.mul_eq_top,
    or_iff_not_imp_left, isFiniteMeasure_iff] using fun h h' ↦ (hc h').elim
/-
**MeasureTheory.hasFiniteIntegral_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：hasFiniteIntegral_const_iff {c : β} : HasFiniteIntegral (fun _ : α => c) μ
 ↔ c = 0 ∨ IsFiniteMeasure μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasFiniteIntegral_const_iff_enorm`：hasFiniteIntegral_const
_iff_enorm {c : ε} (hc : ‖c‖ₑ != ∞) : HasFiniteIntegral (fun _ : α => c) μ ↔ ‖c‖
ₑ = 0 ∨ IsFiniteMeasure μ
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFiniteIntegral_const_iff {c : β} :
    HasFiniteIntegral (fun _ : α => c) μ ↔ c = 0 ∨ IsFiniteMeasure μ := by
  simp [hasFiniteIntegral_const_iff_enorm enorm_ne_top]
/-
**MeasureTheory.hasFiniteIntegral_const_iff_isFiniteMeasure_enorm** 是 Mathlib 中的
一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hasFiniteIntegral_const_iff_isFiniteMeasure_enorm {c : ε} (hc : ‖c‖ₑ != 0)
 (hc' : ‖c‖ₑ != ∞) : HasFiniteIntegral (fun _ => c) μ ↔ IsFiniteMeasure μ
参数：hc : ‖c‖ₑ != 0；hc' : ‖c‖ₑ != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasFiniteIntegral_const_iff_enorm`：hasFiniteIntegral_const
_iff_enorm {c : ε} (hc : ‖c‖ₑ != ∞) : HasFiniteIntegral (fun _ : α => c) μ ↔ ‖c‖
ₑ = 0 ∨ IsFiniteMeasure μ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasFiniteIntegral_const_iff_isFiniteMeasure_enorm {c : ε} (hc : ‖c‖ₑ ≠ 0) (hc' : ‖c‖ₑ ≠ ∞) :
    HasFiniteIntegral (fun _ ↦ c) μ ↔ IsFiniteMeasure μ := by
  simp [hasFiniteIntegral_const_iff_enorm hc', hc, isFiniteMeasure_iff]
/-
**MeasureTheory.hasFiniteIntegral_const_iff_isFiniteMeasure** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory`。
形式化陈述：hasFiniteIntegral_const_iff_isFiniteMeasure {c : β} (hc : c != 0) : HasFin
iteIntegral (fun _ => c) μ ↔ IsFiniteMeasure μ
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.hasFiniteIntegral_const_iff_isFiniteMeasure_enorm`：hasFini
teIntegral_const_iff_isFiniteMeasure_enorm {c : ε} (hc : ‖c‖ₑ != 0) (hc' : ‖c‖ₑ 
!= ∞) : HasFiniteIntegral (fun _ => c) μ ↔ IsFiniteMe…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `enorm_ne_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : EN
ormedAddMonoid E] {a : E}, ‖a‖ₑ ≠ 0 ↔ a ≠ 0
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
-/
lemma hasFiniteIntegral_const_iff_isFiniteMeasure {c : β} (hc : c ≠ 0) :
    HasFiniteIntegral (fun _ ↦ c) μ ↔ IsFiniteMeasure μ :=
  hasFiniteIntegral_const_iff_isFiniteMeasure_enorm (enorm_ne_zero.mpr hc) enorm_ne_top

@[fun_prop]
/-
**MeasureTheory.hasFiniteIntegral_const_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：hasFiniteIntegral_const_enorm [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞)
 : HasFiniteIntegral (fun _ : α => c) μ
参数：hc : ‖c‖ₑ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.hasFiniteIntegral_const_iff_enorm`：hasFiniteIntegral_const
_iff_enorm {c : ε} (hc : ‖c‖ₑ != ∞) : HasFiniteIntegral (fun _ : α => c) μ ↔ ‖c‖
ₑ = 0 ∨ IsFiniteMeasure μ
-/
theorem hasFiniteIntegral_const_enorm [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ ≠ ∞) :
    HasFiniteIntegral (fun _ : α ↦ c) μ :=
  (hasFiniteIntegral_const_iff_enorm hc).2 <| .inr ‹_›

@[fun_prop]
/-
**MeasureTheory.hasFiniteIntegral_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：hasFiniteIntegral_const [IsFiniteMeasure μ] (c : β) : HasFiniteIntegral (f
un _ : α => c) μ
参数：c : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.hasFiniteIntegral_const_iff`：hasFiniteIntegral_const_iff {
c : β} : HasFiniteIntegral (fun _ : α => c) μ ↔ c = 0 ∨ IsFiniteMeasure μ
-/
theorem hasFiniteIntegral_const [IsFiniteMeasure μ] (c : β) :
    HasFiniteIntegral (fun _ : α => c) μ :=
  hasFiniteIntegral_const_iff.2 <| .inr ‹_›
/-
**MeasureTheory.HasFiniteIntegral.of_mem_Icc_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [Me
asureTheory.IsFiniteMeasure μ]   {a b : ENNReal},   a ≠ ⊤ → b ≠ ⊤ → ∀ {X : α → E
NNReal}, (∀ᵐ (ω : α) ∂μ, X ω ∈ Set.Icc a b) → MeasureTheory.HasFiniteIntegral X 
μ
参数：∀ᵐ (ω : α) ∂μ, X ω ∈ Set.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono'_enorm`：∀ {α : Type u_1} {ε : Type 
u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : ENorm ε] {f :
 α → ε}   {g : α → ENNReal},   Me…
· 使用定理 `MeasureTheory.hasFiniteIntegral_const_enorm`：hasFiniteIntegral_const_eno
rm [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞) : HasFiniteIntegral (fun _ : α =
> c) μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem HasFiniteIntegral.of_mem_Icc_of_ne_top [IsFiniteMeasure μ]
    {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) {X : α → ℝ≥0∞} (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    HasFiniteIntegral X μ := by
  have : ‖max ‖a‖ₑ ‖b‖ₑ‖ₑ ≠ ⊤ := by simp [ha, hb]
  apply (hasFiniteIntegral_const_enorm this (μ := μ)).mono'_enorm
  filter_upwards [h.mono fun ω h ↦ h.1, h.mono fun ω h ↦ h.2] with ω h₁ h₂ using by simp [h₂]
/-
**MeasureTheory.HasFiniteIntegral.of_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [Me
asureTheory.IsFiniteMeasure μ] (a b : ℝ)   {X : α → ℝ}, (∀ᵐ (ω : α) ∂μ, X ω ∈ Se
t.Icc a b) → MeasureTheory.HasFiniteIntegral X μ
参数：a b : ℝ；∀ᵐ (ω : α) ∂μ, X ω ∈ Set.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono'`：∀ {α : Type u_1} {β : Type u_2} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup 
β]   {f : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.hasFiniteIntegral_const`：hasFiniteIntegral_const [IsFinite
Measure μ] (c : β) : HasFiniteIntegral (fun _ : α => c) μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `abs_le_max_abs_abs`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : L
inearOrder G] [IsOrderedAddMonoid G] {a b c : G},   a ≤ b → b ≤ c → |b| ≤ max |a
| |c|
-/
theorem HasFiniteIntegral.of_mem_Icc [IsFiniteMeasure μ] (a b : ℝ) {X : α → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    HasFiniteIntegral X μ := by
  apply (hasFiniteIntegral_const (max ‖a‖ ‖b‖)).mono'
  filter_upwards [h.mono fun ω h ↦ h.1, h.mono fun ω h ↦ h.2] with ω using abs_le_max_abs_abs
/-
**MeasureTheory.HasFiniteIntegral.of_bounded_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : ENorm ε]   [MeasureTheory.IsFiniteMeasure μ] {f : α → ε} {C 
: ENNReal},   autoParam (‖C‖ₑ ≠ ⊤) MeasureTheory.HasFiniteIntegral.of_bounded_en
orm._auto_1 →     (∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ C) → MeasureTheory.HasFiniteIntegral 
f μ
参数：‖C‖ₑ ≠ ⊤；∀ᵐ (a : α) ∂μ, ‖f a‖ₑ ≤ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono'_enorm`：∀ {α : Type u_1} {ε : Type 
u_4} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : ENorm ε] {f :
 α → ε}   {g : α → ENNReal},   Me…
· 使用定理 `MeasureTheory.hasFiniteIntegral_const_enorm`：hasFiniteIntegral_const_eno
rm [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞) : HasFiniteIntegral (fun _ : α =
> c) μ
-/
theorem HasFiniteIntegral.of_bounded_enorm [IsFiniteMeasure μ] {f : α → ε} {C : ℝ≥0∞}
    (hC' : ‖C‖ₑ ≠ ∞ := by finiteness) (hC : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ C) : HasFiniteIntegral f μ :=
  (hasFiniteIntegral_const_enorm hC').mono'_enorm hC
/-
**MeasureTheory.HasFiniteIntegral.of_bounded** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   [MeasureTheory.IsFiniteMeasure μ] {f
 : α → β} {C : ℝ},   (∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ C) → MeasureTheory.HasFiniteIntegra
l f μ
参数：∀ᵐ (a : α) ∂μ, ‖f a‖ ≤ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono'`：∀ {α : Type u_1} {β : Type u_2} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup 
β]   {f : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.hasFiniteIntegral_const`：hasFiniteIntegral_const [IsFinite
Measure μ] (c : β) : HasFiniteIntegral (fun _ : α => c) μ
-/
theorem HasFiniteIntegral.of_bounded [IsFiniteMeasure μ] {f : α → β} {C : ℝ}
    (hC : ∀ᵐ a ∂μ, ‖f a‖ ≤ C) : HasFiniteIntegral f μ :=
  (hasFiniteIntegral_const C).mono' hC

-- TODO: generalise this to f with codomain ε
-- requires generalising `norm_le_pi_norm` and friends to enorms
@[simp]
/-
**MeasureTheory.HasFiniteIntegral.of_finite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   [Finite α] [MeasureTheory.IsFiniteMe
asure μ] {f : α → β}, MeasureTheory.HasFiniteIntegral f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_bounded`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   [MeasureTheory.IsFinit…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `norm_le_pi_norm`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] 
[inst_1 : (i : ι) → SeminormedAddGroup (G i)] (f : (i : ι) → G i)   (i : ι), ‖f 
i‖ ≤ …
-/
theorem HasFiniteIntegral.of_finite [Finite α] [IsFiniteMeasure μ] {f : α → β} :
    HasFiniteIntegral f μ :=
  let ⟨_⟩ := nonempty_fintype α
  .of_bounded <| ae_of_all μ <| norm_le_pi_norm f
/-
**MeasureTheory.HasFiniteIntegral.mono_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {m : MeasurableSpace α} {μ ν : MeasureTheo
ry.Measure α} [inst : ENorm ε] {f : α → ε},   MeasureTheory.HasFiniteIntegral f 
ν → μ ≤ ν → MeasureTheory.HasFiniteIntegral f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.lintegral_mono'`：lintegral_mono' {m : MeasurableSpace α} ⦃
μ ν : Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a
 ∂μ <= ∫⁻ a, g a ∂ν
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem HasFiniteIntegral.mono_measure {f : α → ε} (h : HasFiniteIntegral f ν) (hμ : μ ≤ ν) :
    HasFiniteIntegral f μ :=
  lt_of_le_of_lt (lintegral_mono' hμ le_rfl) h

@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral.add_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {m : MeasurableSpace α} {μ ν : MeasureTheo
ry.Measure α} [inst : ENorm ε] {f : α → ε},   MeasureTheory.HasFiniteIntegral f 
μ → MeasureTheory.HasFiniteIntegral f ν → MeasureTheory.HasFiniteIntegral f (μ +
 ν)
参数：μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_add_measure`：lintegral_add_measure (f : α -> Rea
l>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
-/
theorem HasFiniteIntegral.add_measure {f : α → ε} (hμ : HasFiniteIntegral f μ)
    (hν : HasFiniteIntegral f ν) : HasFiniteIntegral f (μ + ν) := by
  simp only [HasFiniteIntegral, lintegral_add_measure] at *
  exact add_lt_top.2 ⟨hμ, hν⟩
/-
**MeasureTheory.HasFiniteIntegral.left_of_add_measure** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {m : MeasurableSpace α} {μ ν : MeasureTheo
ry.Measure α} [inst : ENorm ε] {f : α → ε},   MeasureTheory.HasFiniteIntegral f 
(μ + ν) → MeasureTheory.HasFiniteIntegral f μ
参数：μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono_measure`：∀ {α : Type u_1} {ε : Type
 u_4} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : ENorm ε] {
f : α → ε},   MeasureTheory.HasFin…
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem HasFiniteIntegral.left_of_add_measure {f : α → ε} (h : HasFiniteIntegral f (μ + ν)) :
    HasFiniteIntegral f μ :=
  h.mono_measure <| Measure.le_add_right <| le_rfl
/-
**MeasureTheory.HasFiniteIntegral.right_of_add_measure** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {m : MeasurableSpace α} {μ ν : MeasureTheo
ry.Measure α} [inst : ENorm ε] {f : α → ε},   MeasureTheory.HasFiniteIntegral f 
(μ + ν) → MeasureTheory.HasFiniteIntegral f ν
参数：μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono_measure`：∀ {α : Type u_1} {ε : Type
 u_4} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : ENorm ε] {
f : α → ε},   MeasureTheory.HasFin…
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem HasFiniteIntegral.right_of_add_measure {f : α → ε} (h : HasFiniteIntegral f (μ + ν)) :
    HasFiniteIntegral f ν :=
  h.mono_measure <| Measure.le_add_left <| le_rfl

@[simp]
/-
**MeasureTheory.hasFiniteIntegral_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：hasFiniteIntegral_add_measure {f : α -> ε} : HasFiniteIntegral f (μ + ν) ↔
 HasFiniteIntegral f μ ∧ HasFiniteIntegral f ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.left_of_add_measure`：∀ {α : Type u_1} {ε
 : Type u_4} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : ENo
rm ε] {f : α → ε},   MeasureTheory.HasFin…
· 使用定理 `MeasureTheory.HasFiniteIntegral.right_of_add_measure`：∀ {α : Type u_1} {
ε : Type u_4} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : EN
orm ε] {f : α → ε},   MeasureTheory.HasFin…
· 使用定理 `MeasureTheory.HasFiniteIntegral.add_measure`：∀ {α : Type u_1} {ε : Type 
u_4} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : ENorm ε] {f
 : α → ε},   MeasureTheory.HasFin…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem hasFiniteIntegral_add_measure {f : α → ε} :
    HasFiniteIntegral f (μ + ν) ↔ HasFiniteIntegral f μ ∧ HasFiniteIntegral f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩
/-
**MeasureTheory.HasFiniteIntegral.smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : ENorm ε] {f : α → ε},   MeasureTheory.HasFiniteIntegral f μ 
→ ∀ {c : ENNReal}, c ≠ ⊤ → MeasureTheory.HasFiniteIntegral f (c • μ)
参数：c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem HasFiniteIntegral.smul_measure {f : α → ε} (h : HasFiniteIntegral f μ) {c : ℝ≥0∞}
    (hc : c ≠ ∞) : HasFiniteIntegral f (c • μ) := by
  simp only [HasFiniteIntegral, lintegral_smul_measure] at *
  exact mul_lt_top hc.lt_top h

@[fun_prop, simp]
/-
**MeasureTheory.hasFiniteIntegral_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：hasFiniteIntegral_zero_measure {m : MeasurableSpace α} (f : α -> ε) : HasF
initeIntegral f (0 : Measure α)
参数：f : α -> ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
-/
theorem hasFiniteIntegral_zero_measure {m : MeasurableSpace α} (f : α → ε) :
    HasFiniteIntegral f (0 : Measure α) := by
  simp only [HasFiniteIntegral, lintegral_zero_measure, zero_lt_top]

variable (α μ) in
@[to_fun (attr := fun_prop, simp) hasFiniteIntegral_fun_zero]
/-
**MeasureTheory.hasFiniteIntegral_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：hasFiniteIntegral_zero {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMon
oid ε] : HasFiniteIntegral (0 : α -> ε) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem hasFiniteIntegral_zero {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] :
    HasFiniteIntegral (0 : α → ε) μ := by
  simp [hasFiniteIntegral_iff_enorm]

@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.H
asFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β}, MeasureTheory.HasFinite
Integral f μ → MeasureTheory.HasFiniteIntegral (-f) μ
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `enorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ₑ
 = ‖a‖ₑ
-/
theorem HasFiniteIntegral.neg {f : α → β} (hfi : HasFiniteIntegral f μ) :
    HasFiniteIntegral (-f) μ := by simpa [hasFiniteIntegral_iff_enorm] using hfi

@[simp]
/-
**MeasureTheory.hasFiniteIntegral_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：hasFiniteIntegral_neg_iff {f : α -> β} : HasFiniteIntegral (-f) μ ↔ HasFin
iteIntegral f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.neg`：∀ {α : Type u_1} {β : Type u_2} {m 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]
   {f : α → β}, MeasureTh…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem hasFiniteIntegral_neg_iff {f : α → β} : HasFiniteIntegral (-f) μ ↔ HasFiniteIntegral f μ :=
  ⟨fun h => neg_neg f ▸ h.neg, HasFiniteIntegral.neg⟩

@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral.enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : ENorm ε] {f : α → ε},   MeasureTheory.HasFiniteIntegral f μ 
→ MeasureTheory.HasFiniteIntegral (fun x => ‖f x‖ₑ) μ
参数：fun x => ‖f x‖ₑ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasFiniteIntegral.enorm {f : α → ε} (hfi : HasFiniteIntegral f μ) :
    HasFiniteIntegral (‖f ·‖ₑ) μ := by simpa [hasFiniteIntegral_iff_enorm] using hfi

@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral.norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {f : α → β}, MeasureTheory.HasFinite
Integral f μ → MeasureTheory.HasFiniteIntegral (fun a => ‖f a‖) μ
参数：fun a => ‖f a‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `enorm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), 
‖‖x‖‖ₑ = ‖x‖ₑ
-/
theorem HasFiniteIntegral.norm {f : α → β} (hfi : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => ‖f a‖) μ := by simpa [hasFiniteIntegral_iff_enorm] using hfi
/-
**MeasureTheory.hasFiniteIntegral_enorm_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：hasFiniteIntegral_enorm_iff (f : α -> ε) : HasFiniteIntegral (‖f ·‖ₑ) μ ↔ 
HasFiniteIntegral f μ
参数：f : α -> ε。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.hasFiniteIntegral_congr'_enorm`：∀ {α : Type u_1} {ε : Type
 u_4} {ε' : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [ins
t : ENorm ε]   [inst_1 : ENorm ε']…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `enorm_enorm`：enorm_enorm {ε : Type*} [ENorm ε] (x : ε) : ‖‖x‖ₑ‖ₑ = ‖x‖ₑ
-/
theorem hasFiniteIntegral_enorm_iff (f : α → ε) :
    HasFiniteIntegral (‖f ·‖ₑ) μ ↔ HasFiniteIntegral f μ :=
  hasFiniteIntegral_congr'_enorm <| Eventually.of_forall fun x => enorm_enorm (f x)
/-
**MeasureTheory.hasFiniteIntegral_norm_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：hasFiniteIntegral_norm_iff (f : α -> β) : HasFiniteIntegral (fun a => ‖f a
‖) μ ↔ HasFiniteIntegral f μ
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.hasFiniteIntegral_congr'`：hasFiniteIntegral_congr'_enorm {
f : α -> ε} {g : α -> ε'} (h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : HasFiniteIntegra
l f μ ↔ HasFiniteIntegral g …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
-/
theorem hasFiniteIntegral_norm_iff (f : α → β) :
    HasFiniteIntegral (fun a => ‖f a‖) μ ↔ HasFiniteIntegral f μ :=
  hasFiniteIntegral_congr' <| Eventually.of_forall fun x => norm_norm (f x)
/-
**MeasureTheory.HasFiniteIntegral.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   [Subsingleton α] [MeasureTheory.IsFi
niteMeasure μ] {f : α → β}, MeasureTheory.HasFiniteIntegral f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_finite`：∀ {α : Type u_1} {β : Type u_
2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGr
oup β]   [Finite α] [MeasureThe…
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
-/
theorem HasFiniteIntegral.of_subsingleton [Subsingleton α] [IsFiniteMeasure μ] {f : α → β} :
    HasFiniteIntegral f μ :=
  .of_finite
/-
**MeasureTheory.HasFiniteIntegral.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   [IsEmpty α] {f : α → β}, MeasureTheo
ry.HasFiniteIntegral f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_finite`：∀ {α : Type u_1} {β : Type u_
2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGr
oup β]   [Finite α] [MeasureThe…
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `MeasureTheory.isFiniteMeasureOfIsEmpty`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [IsEmpty α], MeasureTheory.IsFiniteMeasu
re μ
-/
theorem HasFiniteIntegral.of_isEmpty [IsEmpty α] {f : α → β} :
    HasFiniteIntegral f μ :=
  .of_finite

@[simp]
/-
**MeasureTheory.HasFiniteIntegral.of_subsingleton_codomain** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ε 
: Type u_7} [inst : TopologicalSpace ε]   [inst_1 : ESeminormedAddMonoid ε] [Sub
singleton ε] {f : α → ε}, MeasureTheory.HasFiniteIntegral f μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.congr`：∀ {α : Type u_1} {ε : Type u_4} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : ENorm ε] {f g : α →
 ε},   MeasureTheory.HasFin…
· 使用定理 `MeasureTheory.hasFiniteIntegral_zero`：hasFiniteIntegral_zero {ε : Type*}
 [TopologicalSpace ε] [ESeminormedAddMonoid ε] : HasFiniteIntegral (0 : α -> ε) 
μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem HasFiniteIntegral.of_subsingleton_codomain
    {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [Subsingleton ε] {f : α → ε} :
    HasFiniteIntegral f μ :=
  hasFiniteIntegral_zero _ _ |>.congr <| .of_forall fun _ ↦ Subsingleton.elim _ _
/-
**MeasureTheory.hasFiniteIntegral_toReal_of_lintegral_ne_top** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：hasFiniteIntegral_toReal_of_lintegral_ne_top {f : α -> Real>=0∞} (hf : ∫⁻ 
x, f x ∂μ != ∞) : HasFiniteIntegral (fun x => (f x).toReal) μ
参数：hf : ∫⁻ x, f x ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.enorm_of_nonneg`：enorm_of_nonneg (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem hasFiniteIntegral_toReal_of_lintegral_ne_top {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    HasFiniteIntegral (fun x ↦ (f x).toReal) μ := by
  have h x : ‖(f x).toReal‖ₑ = .ofReal (f x).toReal := by
    rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
  simp_rw [hasFiniteIntegral_iff_enorm, h]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (lt_top_iff_ne_top.2 hf)
  by_cases hfx : f x = ∞
  · simp [hfx]
  · lift f x to ℝ≥0 using hfx with fx h
    simp
/-
**MeasureTheory.hasFiniteIntegral_toReal_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：hasFiniteIntegral_toReal_iff {f : α -> Real>=0∞} (hf : forallᵐ x ∂μ, f x !
= ∞) : HasFiniteIntegral (fun x => (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ != ∞
参数：hf : forallᵐ x ∂μ, f x != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Real.enorm_of_nonneg`：enorm_of_nonneg (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasFiniteIntegral_toReal_iff {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    HasFiniteIntegral (fun x ↦ (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ ≠ ∞ := by
  have : ∀ᵐ x ∂μ, .ofReal (f x).toReal = f x := by filter_upwards [hf] with x hx; simp [hx]
  simp [hasFiniteIntegral_iff_enorm, Real.enorm_of_nonneg ENNReal.toReal_nonneg,
    lintegral_congr_ae this, lt_top_iff_ne_top]
/-
**MeasureTheory.isFiniteMeasure_withDensity_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：isFiniteMeasure_withDensity_ofReal {f : α -> Real} (hfi : HasFiniteIntegra
l f μ) : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal <| f x)
参数：hfi : HasFiniteIntegral f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isFiniteMeasure_withDensity`：isFiniteMeasure_withDensity {
f : α -> Real>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞) : IsFiniteMeasure (μ.withDensity f)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Real.ofReal_le_enorm`：ofReal_le_enorm (r : Real) : ENNReal.ofReal r <= ‖
r‖ₑ
-/
theorem isFiniteMeasure_withDensity_ofReal {f : α → ℝ} (hfi : HasFiniteIntegral f μ) :
    IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal <| f x) := by
  refine isFiniteMeasure_withDensity ((lintegral_mono fun x => ?_).trans_lt hfi).ne
  exact Real.ofReal_le_enorm (f x)

section DominatedConvergence

variable {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
  {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {F' : ℕ → α → ε} {f' : α → ε} {bound' : α → ℝ≥0∞}

/-
**MeasureTheory.all_ae_norm_ofReal_F_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：all_ae_norm_ofReal_F_le_bound (h : forall n, forallᵐ a ∂μ, ‖F n a‖ <= boun
d a) : forall n, forallᵐ a ∂μ, ENNReal.ofReal ‖F n a‖ <= ENNReal.ofReal (bound a
)
参数：h : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
-/
theorem all_ae_norm_ofReal_F_le_bound (h : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a) :
    ∀ n, ∀ᵐ a ∂μ, ENNReal.ofReal ‖F n a‖ ≤ ENNReal.ofReal (bound a) := fun n =>
  (h n).mono fun _ h => ENNReal.ofReal_le_ofReal h

@[deprecated (since := "2026-01-26")] alias
all_ae_ofReal_F_le_bound := all_ae_norm_ofReal_F_le_bound
/-
**MeasureTheory.ae_tendsto_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_tendsto_enorm (h : forallᵐ a ∂μ, Tendsto (fun n => F' n a) atTop <| 𝓝 <
| f' a) : forallᵐ a ∂μ, Tendsto (fun n => ‖F' n a‖ₑ) atTop 𝓝 ‖f' a‖ₑ
参数：h : forallᵐ a ∂μ, Tendsto (fun n => F' n a) atTop <| 𝓝 <| f' a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ
-/
theorem ae_tendsto_enorm (h : ∀ᵐ a ∂μ, Tendsto (fun n ↦ F' n a) atTop <| 𝓝 <| f' a) :
    ∀ᵐ a ∂μ, Tendsto (fun n ↦ ‖F' n a‖ₑ) atTop <| 𝓝 <| ‖f' a‖ₑ :=
  h.mono fun _ h ↦ Tendsto.comp (Continuous.tendsto continuous_enorm _) h
/-
**MeasureTheory.ae_tendsto_ofReal_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：ae_tendsto_ofReal_norm (h : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop <
| 𝓝 <| f a) : forallᵐ a ∂μ, Tendsto (fun n => ENNReal.ofReal ‖F n a‖) atTop 𝓝 EN
NReal.ofReal ‖f a‖
参数：h : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop <| 𝓝 <| f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
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
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.ae_tendsto_enorm`：ae_tendsto_enorm (h : forallᵐ a ∂μ, Tend
sto (fun n => F' n a) atTop <| 𝓝 <| f' a) : forallᵐ a ∂μ, Tendsto (fun n => ‖F' 
n a‖ₑ) atTop 𝓝 ‖f' a…
-/
theorem ae_tendsto_ofReal_norm (h : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop <| 𝓝 <| f a) :
    ∀ᵐ a ∂μ, Tendsto (fun n => ENNReal.ofReal ‖F n a‖) atTop <| 𝓝 <| ENNReal.ofReal ‖f a‖ := by
  convert! ae_tendsto_enorm h <;> simp

@[deprecated (since := "2026-01-26")] alias all_ae_tendsto_ofReal_norm := ae_tendsto_ofReal_norm
/-
**MeasureTheory.ae_norm_ofReal_f_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：ae_norm_ofReal_f_le_bound (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bo
und a) (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : forall
ᵐ a ∂μ, ENNReal.ofReal ‖f a‖ <= ENNReal.ofReal (bound a)
参数：h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a；h_lim : forallᵐ a ∂μ, Te
ndsto (fun n => F n a) atTop (𝓝 (f a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.all_ae_norm_ofReal_F_le_bound`：all_ae_norm_ofReal_F_le_bou
nd (h : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a) : forall n, forallᵐ a ∂μ, EN
NReal.ofReal ‖F n a‖ <= ENNReal.o…
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.ae_tendsto_ofReal_norm`：ae_tendsto_ofReal_norm (h : forall
ᵐ a ∂μ, Tendsto (fun n => F n a) atTop <| 𝓝 <| f a) : forallᵐ a ∂μ, Tendsto (fun
 n => ENNReal.ofReal ‖F n …
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem ae_norm_ofReal_f_le_bound (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    ∀ᵐ a ∂μ, ENNReal.ofReal ‖f a‖ ≤ ENNReal.ofReal (bound a) := by
  have F_le_bound := all_ae_norm_ofReal_F_le_bound h_bound
  rw [← ae_all_iff] at F_le_bound
  apply F_le_bound.mp ((ae_tendsto_ofReal_norm h_lim).mono _)
  intro a tendsto_norm F_le_bound
  exact le_of_tendsto' tendsto_norm F_le_bound

@[deprecated (since := "2026-01-26")] alias all_ae_ofReal_f_le_bound := ae_norm_ofReal_f_le_bound
/-
**MeasureTheory.ae_enorm_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_enorm_le_bound (h_bound : forall n, forallᵐ a ∂μ, ‖F' n a‖ₑ <= bound' a
) (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F' n a) atTop (𝓝 (f' a))) : forallᵐ a
 ∂μ, ‖f' a‖ₑ <= bound' a
参数：h_bound : forall n, forallᵐ a ∂μ, ‖F' n a‖ₑ <= bound' a；h_lim : forallᵐ a ∂μ,
 Tendsto (fun n => F' n a) atTop (𝓝 (f' a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.ae_tendsto_enorm`：ae_tendsto_enorm (h : forallᵐ a ∂μ, Tend
sto (fun n => F' n a) atTop <| 𝓝 <| f' a) : forallᵐ a ∂μ, Tendsto (fun n => ‖F' 
n a‖ₑ) atTop 𝓝 ‖f' a…
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem ae_enorm_le_bound (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F' n a‖ₑ ≤ bound' a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n ↦ F' n a) atTop (𝓝 (f' a))) :
    ∀ᵐ a ∂μ, ‖f' a‖ₑ ≤ bound' a := by
  rw [← ae_all_iff] at h_bound
  apply h_bound.mp ((ae_tendsto_enorm h_lim).mono _)
  intro a tendsto_norm h_bound
  exact le_of_tendsto' tendsto_norm h_bound
/-
**MeasureTheory.hasFiniteIntegral_of_dominated_convergence_enorm** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hasFiniteIntegral_of_dominated_convergence_enorm (bound_hasFiniteIntegral 
: HasFiniteIntegral bound' μ) (h_bound : forall n, forallᵐ a ∂μ, ‖F' n a‖ₑ <= bo
und' a) (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F' n a) atTop (𝓝 (f' a))) : Has
FiniteIntegral f' μ
参数：bound_hasFiniteIntegral : HasFiniteIntegral bound' μ；h_bound : forall n, fora
llᵐ a ∂μ, ‖F' n a‖ₑ <= bound' a；h_lim : forallᵐ a ∂μ, Tendsto (fun n => F' n a) 
atTop (𝓝 (f' a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_enorm`：hasFiniteIntegral_iff_enorm {
f : α -> ε} : HasFiniteIntegral f μ ↔ ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_enorm_le_bound`：ae_enorm_le_bound (h_bound : forall n, 
forallᵐ a ∂μ, ‖F' n a‖ₑ <= bound' a) (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F'
 n a) atTop (𝓝 (f' a)…
-/
theorem hasFiniteIntegral_of_dominated_convergence_enorm
    (bound_hasFiniteIntegral : HasFiniteIntegral bound' μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F' n a‖ₑ ≤ bound' a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n ↦ F' n a) atTop (𝓝 (f' a))) : HasFiniteIntegral f' μ := by
  /- `‖F' n a‖ₑ ≤ bound' a` and `‖F' n a‖ₑ --> ‖f' a‖ₑ` implies `‖f a‖ₑ ≤ bound' a`,
    and so `∫ ‖f'‖ₑ ≤ ∫ bound' < ∞` since `bound'` has finite integral -/
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ a, ‖f' a‖ₑ ∂μ) ≤ ∫⁻ a, bound' a ∂μ :=
      lintegral_mono_ae <| ae_enorm_le_bound h_bound h_lim
    _ < ∞ := bound_hasFiniteIntegral
/-
**MeasureTheory.hasFiniteIntegral_of_dominated_convergence** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：hasFiniteIntegral_of_dominated_convergence (bound_hasFiniteIntegral : HasF
initeIntegral bound μ) (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a) (h
_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : HasFiniteIntegr
al f μ
参数：bound_hasFiniteIntegral : HasFiniteIntegral bound μ；h_bound : forall n, foral
lᵐ a ∂μ, ‖F n a‖ <= bound a；h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop
 (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_norm`：hasFiniteIntegral_iff_norm (f 
: α -> β) : HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) < ∞
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_norm_ofReal_f_le_bound`：ae_norm_ofReal_f_le_bound (h_bo
und : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a) (h_lim : forallᵐ a ∂μ, Tendsto
 (fun n => F n a) atTop (𝓝 (f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_ofReal`：hasFiniteIntegral_iff_ofReal
 {f : α -> Real} (h : 0 <=ᵐ[μ] f) : HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofRea
l (f a) ∂μ) < ∞
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem hasFiniteIntegral_of_dominated_convergence
    (bound_hasFiniteIntegral : HasFiniteIntegral bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : HasFiniteIntegral f μ := by
  /- `‖F n a‖ ≤ bound a` and `‖F n a‖ --> ‖f a‖` implies `‖f a‖ ≤ bound a`,
    and so `∫ ‖f‖ ≤ ∫ bound < ∞` since `bound` is has_finite_integral -/
  rw [hasFiniteIntegral_iff_norm]
  calc
    (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (bound a) ∂μ :=
      lintegral_mono_ae <| ae_norm_ofReal_f_le_bound h_bound h_lim
    _ < ∞ := by
      rw [← hasFiniteIntegral_iff_ofReal]
      · exact bound_hasFiniteIntegral
      exact (h_bound 0).mono fun a h => le_trans (norm_nonneg _) h

-- TODO: generalise this to `f` and `F` taking values in a new class `ENormedSubmonoid`
/-
**MeasureTheory.tendsto_lintegral_norm_of_dominated_convergence** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_lintegral_norm_of_dominated_convergence (F_measurable : forall n, 
AEStronglyMeasurable (F n) μ) (bound_hasFiniteIntegral : HasFiniteIntegral bound
 μ) (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a) (h_lim : forallᵐ a ∂μ
, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : Tendsto (fun n => ∫⁻ a, ENNReal.of
Real ‖F n a - f a‖ ∂μ) atTop (𝓝 0)
参数：F_measurable : forall n, AEStronglyMeasurable (F n) μ；bound_hasFiniteIntegral
 : HasFiniteIntegral bound μ；h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound 
a；h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aestronglyMeasurable_of_tendsto_ae`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {ι : Type u_5} [Topolog…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_norm_ofReal_f_le_bound`：ae_norm_ofReal_f_le_bound (h_bo
und : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a) (h_lim : forallᵐ a ∂μ, Tendsto
 (fun n => F n a) atTop (𝓝 (f…
· 使用定理 `MeasureTheory.all_ae_norm_ofReal_F_le_bound`：all_ae_norm_ofReal_F_le_bou
nd (h : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a) : forall n, forallᵐ a ∂μ, EN
NReal.ofReal ‖F n a‖ <= ENNReal.o…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `norm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a - b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
（共 50 条，此处仅展示前 30 条）
-/
theorem tendsto_lintegral_norm_of_dominated_convergence
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ)
    (bound_hasFiniteIntegral : HasFiniteIntegral bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, ENNReal.ofReal ‖F n a - f a‖ ∂μ) atTop (𝓝 0) := by
  have f_measurable : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ F_measurable h_lim
  let b a := 2 * ENNReal.ofReal (bound a)
  /- `‖F n a‖ ≤ bound a` and `F n a --> f a` implies `‖f a‖ ≤ bound a`, and thus by the
    triangle inequality, have `‖F n a - f a‖ ≤ 2 * (bound a)`. -/
  have hb : ∀ n, ∀ᵐ a ∂μ, ENNReal.ofReal ‖F n a - f a‖ ≤ b a := by
    intro n
    filter_upwards [all_ae_norm_ofReal_F_le_bound h_bound n,
      ae_norm_ofReal_f_le_bound h_bound h_lim] with a h₁ h₂
    calc
      ENNReal.ofReal ‖F n a - f a‖ ≤ ENNReal.ofReal ‖F n a‖ + ENNReal.ofReal ‖f a‖ := by
        rw [← ENNReal.ofReal_add]
        · apply ofReal_le_ofReal
          apply norm_sub_le
        · exact norm_nonneg _
        · exact norm_nonneg _
      _ ≤ ENNReal.ofReal (bound a) + ENNReal.ofReal (bound a) := add_le_add h₁ h₂
      _ = b a := by rw [← two_mul]
  -- On the other hand, `F n a --> f a` implies that `‖F n a - f a‖ --> 0`
  have h : ∀ᵐ a ∂μ, Tendsto (fun n => ENNReal.ofReal ‖F n a - f a‖) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine h_lim.mono fun a h => (continuous_ofReal.tendsto _).comp ?_
    rwa [← tendsto_iff_norm_sub_tendsto_zero]
  /- Therefore, by the dominated convergence theorem for nonnegative integration, have
    ` ∫ ‖f a - F n a‖ --> 0 ` -/
  suffices Tendsto (fun n => ∫⁻ a, ENNReal.ofReal ‖F n a - f a‖ ∂μ) atTop (𝓝 (∫⁻ _ : α, 0 ∂μ)) by
    rwa [lintegral_zero] at this
  -- Using the dominated convergence theorem.
  refine tendsto_lintegral_of_dominated_convergence' _ ?_ hb ?_ ?_
  -- Show `fun a => ‖f a - F n a‖` is almost everywhere measurable for all `n`
  · exact fun n =>
      measurable_ofReal.comp_aemeasurable ((F_measurable n).sub f_measurable).norm.aemeasurable
  -- Show `2 * bound` `HasFiniteIntegral`
  · rw [hasFiniteIntegral_iff_ofReal] at bound_hasFiniteIntegral
    · calc
        ∫⁻ a, b a ∂μ = 2 * ∫⁻ a, ENNReal.ofReal (bound a) ∂μ := by
          rw [lintegral_const_mul']
          finiteness
        _ ≠ ∞ := mul_ne_top coe_ne_top bound_hasFiniteIntegral.ne
    filter_upwards [h_bound 0] with _ h using le_trans (norm_nonneg _) h
  -- Show `‖f a - F n a‖ --> 0`
  · exact h

end DominatedConvergence

section PosPart

/-! Lemmas used for defining the positive part of an `L¹` function -/

@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral.max_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   MeasureTheory.HasFiniteIntegral f μ → MeasureTheory.HasFiniteIntegra
l (fun a => max (f a) 0) μ
参数：fun a => max (f a) 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup β] [inst_1…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Lemmas used for defining the positive part of an `L¹` function
-/
theorem HasFiniteIntegral.max_zero {f : α → ℝ} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => max (f a) 0) μ :=
  hf.mono <| Eventually.of_forall fun x => by simp [abs_le, le_abs_self]

@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral.min_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   MeasureTheory.HasFiniteIntegral f μ → MeasureTheory.HasFiniteIntegra
l (fun a => min (f a) 0) μ
参数：fun a => min (f a) 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup β] [inst_1…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `neg_abs_le`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] [AddLeftMono α] (a : α), -|a| ≤ a
-/
theorem HasFiniteIntegral.min_zero {f : α → ℝ} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => min (f a) 0) μ :=
  hf.mono <| Eventually.of_forall fun x => by simpa [abs_le] using neg_abs_le _

end PosPart

section NormedSpace

variable {𝕜 : Type*}

@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral.smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup β]   {𝕜 : Type u_7} [inst_1 : NormedAddCo
mmGroup 𝕜] [inst_2 : SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β] (c : 𝕜) {f : α → β},
   MeasureTheory.HasFiniteIntegral f μ → MeasureTheory.HasFiniteIntegral (c • f)
 μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用引理 `enorm_smul_le`：enorm_smul_le : ‖r • x‖ₑ <= ‖r‖ₑ * ‖x‖ₑ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const_mul'`：lintegral_const_mul' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
theorem HasFiniteIntegral.smul [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β]
    (c : 𝕜) {f : α → β} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (c • f) μ := by
  simp only [HasFiniteIntegral]
  calc
    ∫⁻ a : α, ‖c • f a‖ₑ ∂μ ≤ ∫⁻ a : α, ‖c‖ₑ * ‖f a‖ₑ ∂μ := lintegral_mono fun i ↦ enorm_smul_le
    _ < ∞ := by
      rw [lintegral_const_mul']
      exacts [mul_lt_top coe_lt_top hf, coe_ne_top]

-- TODO: weaken the hypothesis to a version of `ENormSMulClass` with `≤`,
-- once such a typeclass exists.
-- This will let us unify with `HasFiniteIntegral.smul` above.
@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral.smul_enorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε'' : Type u_6} {m : MeasurableSpace α} {μ : MeasureTheo
ry.Measure α} [inst : TopologicalSpace ε'']   [inst_1 : ESeminormedAddMonoid ε''
] {𝕜 : Type u_7} [inst_2 : NormedAddGroup 𝕜] [inst_3 : SMul 𝕜 ε'']   [ENormSMulC
lass 𝕜 ε''] (c : 𝕜) {f : α → ε''},   MeasureTheory.HasFiniteIntegral f μ → Measu
reTheory.HasFiniteIntegral (c • f) μ
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_congr`：lintegral_congr {f g : α -> Real>=0∞} (h 
: forall a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const_mul'`：lintegral_const_mul' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
theorem HasFiniteIntegral.smul_enorm [NormedAddGroup 𝕜] [SMul 𝕜 ε''] [ENormSMulClass 𝕜 ε'']
    (c : 𝕜) {f : α → ε''} (hf : HasFiniteIntegral f μ) : HasFiniteIntegral (c • f) μ := by
  simp only [HasFiniteIntegral]
  calc
    ∫⁻ a : α, ‖c • f a‖ₑ ∂μ = ∫⁻ a : α, ‖c‖ₑ * ‖f a‖ₑ ∂μ := lintegral_congr fun i ↦ enorm_smul _ _
    _ < ∞ := by
      rw [lintegral_const_mul']
      exacts [mul_lt_top coe_lt_top hf, coe_ne_top]
/-
**MeasureTheory.hasFiniteIntegral_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：hasFiniteIntegral_smul_iff [NormedRing 𝕜] [MulActionWithZero 𝕜 β] [IsBound
edSMul 𝕜 β] {c : 𝕜} (hc : IsUnit c) (f : α -> β) : HasFiniteIntegral (c • f) μ ↔
 HasFiniteIntegral f μ
参数：hc : IsUnit c；f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MeasureTheory.HasFiniteIntegral.smul`：∀ {α : Type u_1} {β : Type u_2} {m
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β
]   {𝕜 : Type u_7} [inst_1…
-/
theorem hasFiniteIntegral_smul_iff [NormedRing 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β]
    {c : 𝕜} (hc : IsUnit c) (f : α → β) :
    HasFiniteIntegral (c • f) μ ↔ HasFiniteIntegral f μ := by
  obtain ⟨c, rfl⟩ := hc
  constructor
  · intro h
    simpa only [smul_smul, Units.inv_mul, one_smul] using h.smul ((c⁻¹ : 𝕜ˣ) : 𝕜)
  exact HasFiniteIntegral.smul _

@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_7} [inst : NormedRing 𝕜] {f : α → 𝕜},   MeasureTheory.HasFiniteIntegral
 f μ → ∀ (c : 𝕜), MeasureTheory.HasFiniteIntegral (fun x => c * f x) μ
参数：c : 𝕜；fun x => c * f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.smul`：∀ {α : Type u_1} {β : Type u_2} {m
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β
]   {𝕜 : Type u_7} [inst_1…
-/
theorem HasFiniteIntegral.const_mul [NormedRing 𝕜] {f : α → 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜) :
    HasFiniteIntegral (fun x => c * f x) μ :=
  h.smul c

@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {𝕜 
: Type u_7} [inst : NormedRing 𝕜] {f : α → 𝕜},   MeasureTheory.HasFiniteIntegral
 f μ → ∀ (c : 𝕜), MeasureTheory.HasFiniteIntegral (fun x => f x * c) μ
参数：c : 𝕜；fun x => f x * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFiniteIntegral.smul`：∀ {α : Type u_1} {β : Type u_2} {m
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β
]   {𝕜 : Type u_7} [inst_1…
-/
theorem HasFiniteIntegral.mul_const [NormedRing 𝕜] {f : α → 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜) :
    HasFiniteIntegral (fun x => f x * c) μ :=
  h.smul (MulOpposite.op c)

section count

variable [MeasurableSingletonClass α]

/-- A function has finite integral for the counting measure iff its enorm has finite `tsum`. -/
-- Note that asking for mere summability makes no sense, as every sequence in ℝ≥0∞ is summable.
/-
**MeasureTheory.hasFiniteIntegral_count_iff_enorm** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：hasFiniteIntegral_count_iff_enorm {f : α -> ε} : HasFiniteIntegral f Measu
re.count ↔ tsum (‖f ·‖ₑ) < ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_count`：lintegral_count [MeasurableSingletonClass
 α] (f : α -> Real>=0∞) : ∫⁻ a, f a ∂count = ∑' a, f a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasFiniteIntegral_count_iff_enorm {f : α → ε} :
    HasFiniteIntegral f Measure.count ↔ tsum (‖f ·‖ₑ) < ⊤ := by
  simp only [hasFiniteIntegral_iff_enorm, lintegral_count]

/-- A function has finite integral for the counting measure iff its norm is summable. -/
/-
**MeasureTheory.hasFiniteIntegral_count_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：hasFiniteIntegral_count_iff {f : α -> β} : HasFiniteIntegral f Measure.cou
nt ↔ Summable (‖f ·‖)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_count`：lintegral_count [MeasurableSingletonClass
 α] (f : α -> Real>=0∞) : ∫⁻ a, f a ∂count = ∑' a, f a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function has finite integral for the counting measure iff its norm is summable
.
-/
lemma hasFiniteIntegral_count_iff {f : α → β} :
    HasFiniteIntegral f Measure.count ↔ Summable (‖f ·‖) := by
  simp only [hasFiniteIntegral_iff_enorm, enorm, lintegral_count, lt_top_iff_ne_top,
    tsum_coe_ne_top_iff_summable, ← summable_coe, coe_nnnorm]

end count

section restrict

variable {E : Type*} [NormedAddCommGroup E] {f : α → ε}

@[fun_prop]
/-
**MeasureTheory.HasFiniteIntegral.restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.HasFiniteIntegral`。
形式化陈述：∀ {α : Type u_1} {ε : Type u_4} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : ENorm ε] {f : α → ε},   MeasureTheory.HasFiniteIntegral f μ 
→ ∀ {s : Set α}, MeasureTheory.HasFiniteIntegral f (μ.restrict s)
参数：μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.lintegral_mono_set`：lintegral_mono_set {_ : MeasurableSpac
e α} ⦃μ : Measure α⦄ {s t : Set α} {f : α -> Real>=0∞} (hst : s subseteq t) : ∫⁻
 x in s, f x ∂μ <= ∫⁻ …
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma HasFiniteIntegral.restrict (h : HasFiniteIntegral f μ) {s : Set α} :
    HasFiniteIntegral f (μ.restrict s) := by
  refine lt_of_le_of_lt ?_ h
  simpa [Measure.restrict_univ] using lintegral_mono_set (subset_univ s)

end restrict

end NormedSpace

end MeasureTheory

