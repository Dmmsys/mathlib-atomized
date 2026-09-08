/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Results relating `Measure.tilted` to `mgf` and `cgf`

For a random variable `X : Ω → ℝ` and a measure `μ`, the tilted measure `μ.tilted (t * X ·)` is
linked to the moment-generating function (`mgf`) and the cumulant-generating function (`cgf`)
of `X`.

## Main statements

* `integral_tilted_mul_self`: the integral of `X` against the tilted measure `μ.tilted (t * X ·)`
  is the first derivative of the cumulant-generating function of `X` at `t`.
  `(μ.tilted (t * X ·))[X] = deriv (cgf X μ) t`
* `variance_tilted_mul`: the variance of `X` under the tilted measure `μ.tilted (t * X ·)`
  is the second derivative of the cumulant-generating function of `X` at `t`.
  `Var[X; μ.tilted (t * X ·)] = iteratedDeriv 2 (cgf X μ) t`

-/

public section


open MeasureTheory Real Set Finset

open scoped NNReal ENNReal ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {X : Ω → ℝ} {t u : ℝ}

namespace ProbabilityTheory

section Apply

/-! ### Apply lemmas for `tilted` expressed with `mgf` or `cgf`. -/

/-
**ProbabilityTheory.tilted_mul_apply_mgf'** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：tilted_mul_apply_mgf' {s : Set Ω} (hs : MeasurableSet s) : μ.tilted (t * X
 ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_apply'`：tilted_apply' (μ : Measure α) (f : α -> Rea
l) {s : Set α} (hs : MeasurableSet s) : μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal
 (exp (f a) / ∫ x…
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …

--- 原说明 ---
### Apply lemmas for `tilted` expressed with `mgf` or `cgf`.
-/
lemma tilted_mul_apply_mgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [tilted_apply' _ _ hs, mgf]
/-
**ProbabilityTheory.tilted_mul_apply_mgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：tilted_mul_apply_mgf [SFinite μ] (s : Set Ω) : μ.tilted (t * X ·) s = ∫⁻ a
 in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ
参数：s : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_apply`：tilted_apply (μ : Measure α) [SFinite μ] (f 
: α -> Real) (s : Set α) : μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) /
 ∫ x, exp (f x) …
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
-/
lemma tilted_mul_apply_mgf [SFinite μ] (s : Set Ω) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [tilted_apply, mgf]
/-
**ProbabilityTheory.tilted_mul_apply_cgf'** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：tilted_mul_apply_cgf' {s : Set Ω} (hs : MeasurableSet s) (ht : Integrable 
(fun ω => exp (t * X ω)) μ) : μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (
exp (t * X a - cgf X μ t)) ∂μ
参数：hs : MeasurableSet s；ht : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `MeasureTheory.Measure.restrict_zero`：restrict_zero {_m0 : MeasurableSpac
e α} (s : Set α) : (0 : Measure α).restrict s = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.tilted_mul_apply_mgf'`：tilted_mul_apply_mgf' {s : Set 
Ω} (hs : MeasurableSet s) : μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (ex
p (t * X a) / mgf X μ t) ∂μ
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用引理 `ProbabilityTheory.exp_cgf`：exp_cgf [hμ : NeZero μ] (hX : Integrable (fun
 ω => exp (t * X ω)) μ) : exp (cgf X μ t) = mgf X μ t
-/
lemma tilted_mul_apply_cgf' {s : Set Ω} (hs : MeasurableSet s)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_mgf' hs, exp_sub, exp_cgf ht]
/-
**ProbabilityTheory.tilted_mul_apply_cgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：tilted_mul_apply_cgf [SFinite μ] (s : Set Ω) (ht : Integrable (fun ω => ex
p (t * X ω)) μ) : μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a
 - cgf X μ t)) ∂μ
参数：s : Set Ω；ht : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `MeasureTheory.Measure.restrict_zero`：restrict_zero {_m0 : MeasurableSpac
e α} (s : Set α) : (0 : Measure α).restrict s = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.tilted_mul_apply_mgf`：tilted_mul_apply_mgf [SFinite μ]
 (s : Set Ω) : μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) /
 mgf X μ t) ∂μ
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用引理 `ProbabilityTheory.exp_cgf`：exp_cgf [hμ : NeZero μ] (hX : Integrable (fun
 ω => exp (t * X ω)) μ) : exp (cgf X μ t) = mgf X μ t
-/
lemma tilted_mul_apply_cgf [SFinite μ] (s : Set Ω) (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_mgf s, exp_sub, exp_cgf ht]
/-
**ProbabilityTheory.tilted_mul_apply_eq_ofReal_integral_mgf'** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory`。
形式化陈述：tilted_mul_apply_eq_ofReal_integral_mgf' {s : Set Ω} (hs : MeasurableSet s
) : μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂
μ)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_apply_eq_ofReal_integral'`：tilted_apply_eq_ofReal_i
ntegral' {s : Set α} (f : α -> Real) (hs : MeasurableSet s) : μ.tilted f s = ENN
Real.ofReal (∫ a in s, exp (f a) / ∫…
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
-/
lemma tilted_mul_apply_eq_ofReal_integral_mgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [tilted_apply_eq_ofReal_integral' _ hs, mgf]
/-
**ProbabilityTheory.tilted_mul_apply_eq_ofReal_integral_mgf** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：tilted_mul_apply_eq_ofReal_integral_mgf [SFinite μ] (s : Set Ω) : μ.tilted
 (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ)
参数：s : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_apply_eq_ofReal_integral`：tilted_apply_eq_ofReal_in
tegral [SFinite μ] (f : α -> Real) (s : Set α) : μ.tilted f s = ENNReal.ofReal (
∫ a in s, exp (f a) / ∫ x, exp (f x…
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
-/
lemma tilted_mul_apply_eq_ofReal_integral_mgf [SFinite μ] (s : Set Ω) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [tilted_apply_eq_ofReal_integral _ s, mgf]
/-
**ProbabilityTheory.tilted_mul_apply_eq_ofReal_integral_cgf'** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory`。
形式化陈述：tilted_mul_apply_eq_ofReal_integral_cgf' {s : Set Ω} (hs : MeasurableSet s
) (ht : Integrable (fun ω => exp (t * X ω)) μ) : μ.tilted (t * X ·) s = ENNReal.
ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ)
参数：hs : MeasurableSet s；ht : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `MeasureTheory.Measure.restrict_zero`：restrict_zero {_m0 : MeasurableSpac
e α} (s : Set α) : (0 : Measure α).restrict s = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.tilted_mul_apply_eq_ofReal_integral_mgf'`：tilted_mul_a
pply_eq_ofReal_integral_mgf' {s : Set Ω} (hs : MeasurableSet s) : μ.tilted (t * 
X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a)…
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用引理 `ProbabilityTheory.exp_cgf`：exp_cgf [hμ : NeZero μ] (hX : Integrable (fun
 ω => exp (t * X ω)) μ) : exp (cgf X μ t) = mgf X μ t
-/
lemma tilted_mul_apply_eq_ofReal_integral_cgf' {s : Set Ω} (hs : MeasurableSet s)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf' hs, exp_sub]
    rwa [exp_cgf]
/-
**ProbabilityTheory.tilted_mul_apply_eq_ofReal_integral_cgf** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory`。
形式化陈述：tilted_mul_apply_eq_ofReal_integral_cgf [SFinite μ] (s : Set Ω) (ht : Inte
grable (fun ω => exp (t * X ω)) μ) : μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a 
in s, exp (t * X a - cgf X μ t) ∂μ)
参数：s : Set Ω；ht : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `MeasureTheory.Measure.restrict_zero`：restrict_zero {_m0 : MeasurableSpac
e α} (s : Set α) : (0 : Measure α).restrict s = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.tilted_mul_apply_eq_ofReal_integral_mgf`：tilted_mul_ap
ply_eq_ofReal_integral_mgf [SFinite μ] (s : Set Ω) : μ.tilted (t * X ·) s = ENNR
eal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t…
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用引理 `ProbabilityTheory.exp_cgf`：exp_cgf [hμ : NeZero μ] (hX : Integrable (fun
 ω => exp (t * X ω)) μ) : exp (cgf X μ t) = mgf X μ t
-/
lemma tilted_mul_apply_eq_ofReal_integral_cgf [SFinite μ] (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf s, exp_sub]
    rwa [exp_cgf]

end Apply

section Integral

/-! ### Integral of `tilted` expressed with `mgf` or `cgf`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
**ProbabilityTheory.setIntegral_tilted_mul_eq_mgf'** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：setIntegral_tilted_mul_eq_mgf' (g : Ω -> E) {s : Set Ω} (hs : MeasurableSe
t s) : ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, (exp (t * X x) / mgf X μ 
t) • (g x) ∂μ
参数：g : Ω -> E；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.setIntegral_tilted'`：setIntegral_tilted' (f : α -> Real) (
g : α -> E) {s : Set α} (hs : MeasurableSet s) : ∫ x in s, g x ∂(μ.tilted f) = ∫
 x in s, (exp (f x) / ∫…
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
-/
lemma setIntegral_tilted_mul_eq_mgf' (g : Ω → E) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [setIntegral_tilted' _ _ hs, mgf]
/-
**ProbabilityTheory.setIntegral_tilted_mul_eq_mgf** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：setIntegral_tilted_mul_eq_mgf [SFinite μ] (g : Ω -> E) (s : Set Ω) : ∫ x i
n s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂
μ
参数：g : Ω -> E；s : Set Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.setIntegral_tilted`：setIntegral_tilted [SFinite μ] (f : α 
-> Real) (g : α -> E) (s : Set α) : ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, (exp
 (f x) / ∫ x, exp (f x…
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
-/
lemma setIntegral_tilted_mul_eq_mgf [SFinite μ] (g : Ω → E) (s : Set Ω) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [setIntegral_tilted, mgf]
/-
**ProbabilityTheory.setIntegral_tilted_mul_eq_cgf'** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：setIntegral_tilted_mul_eq_cgf' (g : Ω -> E) {s : Set Ω} (hs : MeasurableSe
t s) (ht : Integrable (fun ω => exp (t * X ω)) μ) : ∫ x in s, g x ∂(μ.tilted (t 
* X ·)) = ∫ x in s, exp (t * X x - cgf X μ t) • (g x) ∂μ
参数：g : Ω -> E；hs : MeasurableSet s；ht : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `MeasureTheory.Measure.restrict_zero`：restrict_zero {_m0 : MeasurableSpac
e α} (s : Set α) : (0 : Measure α).restrict s = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.setIntegral_tilted_mul_eq_mgf'`：setIntegral_tilted_mul
_eq_mgf' (g : Ω -> E) {s : Set Ω} (hs : MeasurableSet s) : ∫ x in s, g x ∂(μ.til
ted (t * X ·)) = ∫ x in s, (exp (t * X…
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用引理 `ProbabilityTheory.exp_cgf`：exp_cgf [hμ : NeZero μ] (hX : Integrable (fun
 ω => exp (t * X ω)) μ) : exp (cgf X μ t) = mgf X μ t
-/
lemma setIntegral_tilted_mul_eq_cgf' (g : Ω → E) {s : Set Ω}
    (hs : MeasurableSet s) (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, exp (t * X x - cgf X μ t) • (g x) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [setIntegral_tilted_mul_eq_mgf' _ hs, exp_sub, exp_cgf ht]
/-
**ProbabilityTheory.setIntegral_tilted_mul_eq_cgf** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：setIntegral_tilted_mul_eq_cgf [SFinite μ] (g : Ω -> E) (s : Set Ω) (ht : I
ntegrable (fun ω => exp (t * X ω)) μ) : ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ 
x in s, exp (t * X x - cgf X μ t) • (g x) ∂μ
参数：g : Ω -> E；s : Set Ω；ht : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `MeasureTheory.Measure.restrict_zero`：restrict_zero {_m0 : MeasurableSpac
e α} (s : Set α) : (0 : Measure α).restrict s = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.setIntegral_tilted_mul_eq_mgf`：setIntegral_tilted_mul_
eq_mgf [SFinite μ] (g : Ω -> E) (s : Set Ω) : ∫ x in s, g x ∂(μ.tilted (t * X ·)
) = ∫ x in s, (exp (t * X x) / mgf X …
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用引理 `ProbabilityTheory.exp_cgf`：exp_cgf [hμ : NeZero μ] (hX : Integrable (fun
 ω => exp (t * X ω)) μ) : exp (cgf X μ t) = mgf X μ t
-/
lemma setIntegral_tilted_mul_eq_cgf [SFinite μ] (g : Ω → E) (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, exp (t * X x - cgf X μ t) • (g x) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [setIntegral_tilted_mul_eq_mgf, exp_sub, exp_cgf ht]
/-
**ProbabilityTheory.integral_tilted_mul_eq_mgf** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：integral_tilted_mul_eq_mgf (g : Ω -> E) : ∫ ω, g ω ∂(μ.tilted (t * X ·)) =
 ∫ ω, (exp (t * X ω) / mgf X μ t) • (g ω) ∂μ
参数：g : Ω -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.integral_tilted`：integral_tilted (f : α -> Real) (g : α ->
 E) : ∫ x, g x ∂(μ.tilted f) = ∫ x, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
-/
lemma integral_tilted_mul_eq_mgf (g : Ω → E) :
    ∫ ω, g ω ∂(μ.tilted (t * X ·)) = ∫ ω, (exp (t * X ω) / mgf X μ t) • (g ω) ∂μ := by
  rw [integral_tilted, mgf]
/-
**ProbabilityTheory.integral_tilted_mul_eq_cgf** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：integral_tilted_mul_eq_cgf (g : Ω -> E) (ht : Integrable (fun ω => exp (t 
* X ω)) μ) : ∫ ω, g ω ∂(μ.tilted (t * X ·)) = ∫ ω, exp (t * X ω - cgf X μ t) • (
g ω) ∂μ
参数：g : Ω -> E；ht : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.integral_tilted_mul_eq_mgf`：integral_tilted_mul_eq_mgf
 (g : Ω -> E) : ∫ ω, g ω ∂(μ.tilted (t * X ·)) = ∫ ω, (exp (t * X ω) / mgf X μ t
) • (g ω) ∂μ
· 使用定理 `Real.exp_sub`：exp_sub : exp (x - y) = exp x / exp y
· 使用引理 `ProbabilityTheory.exp_cgf`：exp_cgf [hμ : NeZero μ] (hX : Integrable (fun
 ω => exp (t * X ω)) μ) : exp (cgf X μ t) = mgf X μ t
-/
lemma integral_tilted_mul_eq_cgf (g : Ω → E) (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    ∫ ω, g ω ∂(μ.tilted (t * X ·)) = ∫ ω, exp (t * X ω - cgf X μ t) • (g ω) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [integral_tilted_mul_eq_mgf, exp_sub]
    rwa [exp_cgf]

/-- The integral of `X` against the tilted measure `μ.tilted (t * X ·)` is the first derivative of
the cumulant-generating function of `X` at `t`. -/
/-
**ProbabilityTheory.integral_tilted_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：integral_tilted_mul_self (ht : t in interior (integrableExpSet X μ)) : (μ.
tilted (t * X ·))[X] = deriv (cgf X μ) t
参数：ht : t in interior (integrableExpSet X μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.integral_tilted_mul_eq_mgf`：integral_tilted_mul_eq_mgf
 (g : Ω -> E) : ∫ ω, g ω ∂(μ.tilted (t * X ·)) = ∫ ω, (exp (t * X ω) / mgf X μ t
) • (g ω) ∂μ
· 使用引理 `ProbabilityTheory.deriv_cgf`：deriv_cgf (h : v in interior (integrableExp
Set X μ)) : deriv (cgf X μ) v = μ[fun ω => X ω * exp (v * X ω)] / mgf X μ v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0

--- 原说明 ---
The integral of `X` against the tilted measure `μ.tilted (t * X ·)` is the first
 derivative of
the cumulant-generating function of `X` at `t`.
-/
lemma integral_tilted_mul_self (ht : t ∈ interior (integrableExpSet X μ)) :
    (μ.tilted (t * X ·))[X] = deriv (cgf X μ) t := by
  simp_rw [integral_tilted_mul_eq_mgf, deriv_cgf ht, ← integral_div, smul_eq_mul]
  congr with ω
  ring

end Integral

/-
**ProbabilityTheory.memLp_tilted_mul** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：memLp_tilted_mul (ht : t in interior (integrableExpSet X μ)) (p : Real>=0)
 : MemLp X p (μ.tilted (t * X ·))
参数：ht : t in interior (integrableExpSet X μ)；p : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.aemeasurable_of_mem_interior_integrableExpSet`：aemeasu
rable_of_mem_interior_integrableExpSet (hv : v in interior (integrableExpSet X μ
)) : AEMeasurable X μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用引理 `MeasureTheory.tilted_absolutelyContinuous`：tilted_absolutelyContinuous (
μ : Measure α) (f : α -> Real) : μ.tilted f ≪ μ
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`：eLpNorm_lt
_top_iff_lintegral_rpow_enorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_t
op : p != ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.ofReal_rpow_of_nonneg`：ofReal_rpow_of_nonneg {x p : Real} (hx_no
nneg : 0 <= x) (hp_nonneg : 0 <= p) : ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^
 p)
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `MeasureTheory.Integrable.lintegral_lt_top`：∀ {α : Type u_1} {mα : Measur
ableSpace α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrab
le f μ → ∫⁻ (x : α), ENNReal.of…
· 使用引理 `MeasureTheory.integrable_tilted_iff`：integrable_tilted_iff {E : Type*} [
NormedAddCommGroup E] [NormedSpace Real E] {f : α -> Real} (hf : Integrable (fun
 x => exp (f x)) μ) (g : …
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `ProbabilityTheory.integrable_rpow_abs_mul_exp_of_mem_interior_integrable
ExpSet`：integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet (hv : v in 
interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) : Integrab…
-/
lemma memLp_tilted_mul (ht : t ∈ interior (integrableExpSet X μ)) (p : ℝ≥0) :
    MemLp X p (μ.tilted (t * X ·)) := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet ht
  by_cases hp : p = 0
  · simpa [hp] using hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _)
  refine ⟨hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _), ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top]
  rotate_left
  · simp [hp]
  · simp
  simp_rw [ENNReal.coe_toReal, ← ofReal_norm, norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (x := |X _|) (p := p) (abs_nonneg (X _)) p.2]
  refine Integrable.lintegral_lt_top ?_
  simp_rw [integrable_tilted_iff (interior_subset (s := integrableExpSet X μ) ht),
    smul_eq_mul, mul_comm]
  exact integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet ht p.2

/-- The variance of `X` under the tilted measure `μ.tilted (t * X ·)` is the second derivative of
the cumulant-generating function of `X` at `t`. -/
/-
**ProbabilityTheory.variance_tilted_mul** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：variance_tilted_mul (ht : t in interior (integrableExpSet X μ)) : Var[X; μ
.tilted (t * X ·)] = iteratedDeriv 2 (cgf X μ) t
参数：ht : t in interior (integrableExpSet X μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.variance_eq_integral`：variance_eq_integral (hX : AEMea
surable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用引理 `ProbabilityTheory.memLp_tilted_mul`：memLp_tilted_mul (ht : t in interior
 (integrableExpSet X μ)) (p : Real>=0) : MemLp X p (μ.tilted (t * X ·))
· 使用引理 `ProbabilityTheory.integral_tilted_mul_self`：integral_tilted_mul_self (ht
 : t in interior (integrableExpSet X μ)) : (μ.tilted (t * X ·))[X] = deriv (cgf 
X μ) t
· 使用引理 `ProbabilityTheory.iteratedDeriv_two_cgf_eq_integral`：iteratedDeriv_two_c
gf_eq_integral (h : v in interior (integrableExpSet X μ)) : iteratedDeriv 2 (cgf
 X μ) v = μ[fun ω => (X ω - deriv (cgf X …
· 使用引理 `ProbabilityTheory.integral_tilted_mul_eq_mgf`：integral_tilted_mul_eq_mgf
 (g : Ω -> E) : ∫ ω, g ω ∂(μ.tilted (t * X ·)) = ∫ ω, (exp (t * X ω) / mgf X μ t
) • (g ω) ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_div`：integral_div {L : Type*} [RCLike L] (r : L) 
(f : α -> L) : ∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
The variance of `X` under the tilted measure `μ.tilted (t * X ·)` is the second 
derivative of
the cumulant-generating function of `X` at `t`.
-/
lemma variance_tilted_mul (ht : t ∈ interior (integrableExpSet X μ)) :
    Var[X; μ.tilted (t * X ·)] = iteratedDeriv 2 (cgf X μ) t := by
  rw [variance_eq_integral]
  swap; · exact (memLp_tilted_mul ht 1).aestronglyMeasurable.aemeasurable
  rw [integral_tilted_mul_self ht, iteratedDeriv_two_cgf_eq_integral ht, integral_tilted_mul_eq_mgf,
    ← integral_div]
  simp only [smul_eq_mul]
  congr with ω
  ring

end ProbabilityTheory

