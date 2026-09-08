/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.MeasureTheory.Integral.CircleAverage


/-!
# The Proximity Function of Value Distribution Theory

This file defines the "proximity function" attached to a meromorphic function defined on the complex
plane.  Also known as the `Nevanlinna Proximity Function`, this is one of the three main functions
used in Value Distribution Theory.

The proximity function is a logarithmically weighted measure quantifying how well a meromorphic
function `f` approximates the constant function `a` on the circle of radius `R` in the complex
plane.  The definition ensures that large values correspond to good approximation.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.
-/

@[expose] public section

open Filter Metric Real Set

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E]
  {f g : ℂ → E} {a : WithTop E} {a₀ : E}

open Real

variable (f a) in
/--
The Proximity Function of Value Distribution Theory

If `f : ℂ → E` is meromorphic and `a : WithTop E` is any value, the proximity function is a
logarithmically weighted measure quantifying how well a meromorphic function `f` approximates the
constant function `a` on the circle of radius `R` in the complex plane.  In the special case where
`a = ⊤`, it quantifies how well `f` approximates infinity.
-/
/-
**ValueDistribution.proximity** 是 Mathlib 中的一个定义，位于命名空间 `ValueDistribution`。
形式化陈述：proximity : Real -> Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Proximity Function of Value Distribution Theory

If `f : ℂ → E` is meromorphic and `a : WithTop E` is any value, the proximity fu
nction is a
logarithmically weighted measure quantifying how well a meromorphic function `f`
 approximates the
constant function `a` on the circle of radius `R` in the complex plane.  In the 
special case where
`a = ⊤`, it quantifies how well `f` approximates infinity.
-/
noncomputable def proximity : ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact circleAverage (log⁺ ‖f ·‖) 0
  · exact circleAverage (log⁺ ‖f · - a.untop₀‖⁻¹) 0

/-- Expand the definition of `proximity f a₀` in case where `a₀` is finite. -/
/-
**ValueDistribution.proximity_coe** 是 Mathlib 中的一个引理，位于命名空间 `ValueDistribution`。
形式化陈述：proximity_coe : proximity f a₀ = circleAverage (log⁺ ‖f · - a₀‖⁻¹) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Expand the definition of `proximity f a₀` in case where `a₀` is finite.
-/
lemma proximity_coe :
    proximity f a₀ = circleAverage (log⁺ ‖f · - a₀‖⁻¹) 0 := by
  simp [proximity]

/--
Expand the definition of `proximity f a₀` in case where `a₀` is zero.
-/
/-
**ValueDistribution.proximity_zero** 是 Mathlib 中的一个引理，位于命名空间 `ValueDistribution`
。
形式化陈述：proximity_zero : proximity f 0 = circleAverage (log⁺ ‖f ·‖⁻¹) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Expand the definition of `proximity f a₀` in case where `a₀` is zero.
-/
lemma proximity_zero : proximity f 0 = circleAverage (log⁺ ‖f ·‖⁻¹) 0 := by
  simp [proximity]

/--
For complex-valued functions, expand the definition of `proximity f a₀` in case where `a₀` is zero.
This is a simple variant of `proximity_zero` defined above.
-/
/-
**ValueDistribution.proximity_zero_of_complexValued** 是 Mathlib 中的一个引理，位于命名空间 `V
alueDistribution`。
形式化陈述：proximity_zero_of_complexValued {f : Complex -> Complex} : proximity f 0 =
 circleAverage (log⁺ ‖f⁻¹ ·‖) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For complex-valued functions, expand the definition of `proximity f a₀` in case 
where `a₀` is zero.
This is a simple variant of `proximity_zero` defined above.
-/
lemma proximity_zero_of_complexValued {f : ℂ → ℂ} :
    proximity f 0 = circleAverage (log⁺ ‖f⁻¹ ·‖) 0 := by
  simp [proximity]

/--
Expand the definition of `proximity f a` in case where `a₀ = ⊤`.
-/
/-
**ValueDistribution.proximity_top** 是 Mathlib 中的一个引理，位于命名空间 `ValueDistribution`。
形式化陈述：proximity_top : proximity f ⊤ = circleAverage (log⁺ ‖f ·‖) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Expand the definition of `proximity f a` in case where `a₀ = ⊤`.
-/
lemma proximity_top : proximity f ⊤ = circleAverage (log⁺ ‖f ·‖) 0 := by
  simp [proximity]

/-!
## Elementary Properties of the Proximity Function
-/

/--
If two functions differ only on a discrete set, then their proximity functions
agree, except perhaps at radius 0.
-/
/-
**ValueDistribution.proximity_congr_codiscreteWithin** 是 Mathlib 中的一个引理，位于命名空间 `
ValueDistribution`。
形式化陈述：proximity_congr_codiscreteWithin {f g : Complex -> E} {a : WithTop E} {r :
 Real} (hfg : f =ᶠ[codiscreteWithin (sphere 0 |r|)] g) (hr : r != 0) : proximity
 f a r = proximity g a r
参数：hfg : f =ᶠ[codiscreteWithin (sphere 0 |r|)] g；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.circleAverage_congr_codiscreteWithin`：circleAverage_congr_codiscret
eWithin (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R != 0) : circleA
verage f₁ c R = circleAverage f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
If two functions differ only on a discrete set, then their proximity functions
agree, except perhaps at radius 0.
-/
lemma proximity_congr_codiscreteWithin {f g : ℂ → E} {a : WithTop E} {r : ℝ}
    (hfg : f =ᶠ[codiscreteWithin (sphere 0 |r|)] g) (hr : r ≠ 0) :
    proximity f a r = proximity g a r := by
  by_cases h : a = ⊤
  all_goals
    simp only [proximity, h, ↓reduceDIte]
    apply circleAverage_congr_codiscreteWithin _ hr
    filter_upwards [hfg] using by aesop

/--
If two functions differ only on a discrete set, then their proximity functions
agree, except perhaps at radius 0.
-/
/-
**ValueDistribution.proximity_congr_codiscrete** 是 Mathlib 中的一个引理，位于命名空间 `ValueD
istribution`。
形式化陈述：proximity_congr_codiscrete {f g : Complex -> E} {a : WithTop E} {r : Real}
 (hfg : f =ᶠ[codiscrete Complex] g) (hr : r != 0) : proximity f a r = proximity 
g a r
参数：hfg : f =ᶠ[codiscrete Complex] g；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ValueDistribution.proximity_congr_codiscreteWithin`：proximity_congr_codi
screteWithin {f g : Complex -> E} {a : WithTop E} {r : Real} (hfg : f =ᶠ[codiscr
eteWithin (sphere 0 |r|)] g) (hr : r != …
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用引理 `Filter.codiscreteWithin_mono`：Filter.codiscreteWithin_mono {U₁ U : Set X
} (hU : U₁ subseteq U) : codiscreteWithin U₁ <= codiscreteWithin U
· 使用定理 `trivial`：True

--- 原说明 ---
If two functions differ only on a discrete set, then their proximity functions
agree, except perhaps at radius 0.
-/
lemma proximity_congr_codiscrete {f g : ℂ → E} {a : WithTop E} {r : ℝ}
    (hfg : f =ᶠ[codiscrete ℂ] g) (hr : r ≠ 0) :
    proximity f a r = proximity g a r :=
  proximity_congr_codiscreteWithin (hfg.filter_mono (codiscreteWithin_mono (by tauto))) hr

/--
For finite values `a₀`, the proximity function `proximity f a₀` equals the proximity function for
the value zero of the shifted function `f - a₀`.
-/
/-
**ValueDistribution.proximity_coe_eq_proximity_sub_const_zero** 是 Mathlib 中的一个引理
，位于命名空间 `ValueDistribution`。
形式化陈述：proximity_coe_eq_proximity_sub_const_zero : proximity f a₀ = proximity (f 
- fun _ => a₀) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For finite values `a₀`, the proximity function `proximity f a₀` equals the proxi
mity function for
the value zero of the shifted function `f - a₀`.
-/
lemma proximity_coe_eq_proximity_sub_const_zero :
    proximity f a₀ = proximity (f - fun _ ↦ a₀) 0 := by
  simp [proximity]

/--
For complex-valued `f`, establish a simple relation between the proximity functions of `f` and of
`f⁻¹`.
-/
/-
**ValueDistribution.proximity_inv** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribution`。
形式化陈述：proximity_inv {f : Complex -> Complex} : proximity f⁻¹ ⊤ = proximity f 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ValueDistribution.proximity_top`：proximity_top : proximity f ⊤ = circleA
verage (log⁺ ‖f ·‖) 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `ValueDistribution.proximity_zero`：proximity_zero : proximity f 0 = circl
eAverage (log⁺ ‖f ·‖⁻¹) 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For complex-valued `f`, establish a simple relation between the proximity functi
ons of `f` and of
`f⁻¹`.
-/
theorem proximity_inv {f : ℂ → ℂ} : proximity f⁻¹ ⊤ = proximity f 0 := by
  simp [proximity_zero, proximity_top]

/--
For complex-valued `f`, the difference between `proximity f ⊤` and `proximity f⁻¹ ⊤` is the circle
average of `log ‖f ·‖`.
-/
/-
**ValueDistribution.proximity_sub_proximity_inv_eq_circleAverage** 是 Mathlib 中的一
个定理，位于命名空间 `ValueDistribution`。
形式化陈述：proximity_sub_proximity_inv_eq_circleAverage {f : Complex -> Complex} (h₁f
 : Meromorphic f) : proximity f ⊤ - proximity f⁻¹ ⊤ = circleAverage (log ‖f ·‖) 
0
参数：h₁f : Meromorphic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.circleAverage_sub`：circleAverage_sub (hf₁ : CircleIntegrable f₁ c R
) (hf₂ : CircleIntegrable f₂ c R) : circleAverage (f₁ - f₂) c R = circleAverage 
f₁ c R - cir…
· 使用定理 `MeromorphicOn.circleIntegrable_posLog_norm`：MeromorphicOn.circleIntegrab
le_posLog_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log⁺ ‖f
 ·‖) c R
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用引理 `Meromorphic.inv`：inv {f : 𝕜 -> 𝕜'} (hf : Meromorphic f) : Meromorphic f⁻
¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
For complex-valued `f`, the difference between `proximity f ⊤` and `proximity f⁻
¹ ⊤` is the circle
average of `log ‖f ·‖`.
-/
theorem proximity_sub_proximity_inv_eq_circleAverage {f : ℂ → ℂ} (h₁f : Meromorphic f) :
    proximity f ⊤ - proximity f⁻¹ ⊤ = circleAverage (log ‖f ·‖) 0 := by
  ext R
  simp only [proximity, ↓reduceDIte, Pi.inv_apply, norm_inv, Pi.sub_apply]
  rw [← circleAverage_sub]
  · simp_rw [← posLog_sub_posLog_inv, Pi.sub_def]
  · apply h₁f.meromorphicOn.circleIntegrable_posLog_norm
  · simp_rw [← norm_inv]
    apply h₁f.inv.meromorphicOn.circleIntegrable_posLog_norm

/--
The proximity function is even.
-/
/-
**ValueDistribution.proximity_even** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribution`
。
形式化陈述：proximity_even : (proximity f a).Even
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.circleAverage_neg_radius`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} {R : ℝ},   Real.circleAvera
ge f c (-R) = Real.…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
The proximity function is even.
-/
theorem proximity_even : (proximity f a).Even := by
  intro r
  by_cases h : a = ⊤ <;> simp [proximity, h]

/--
The proximity function is non-negative.
-/
/-
**ValueDistribution.proximity_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistributio
n`。
形式化陈述：proximity_nonneg {a : WithTop E} : 0 <= proximity f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.circleAverage_nonneg_of_nonneg`：circleAverage_nonneg_of_nonneg {c :
 Complex} {R : Real} {f : Complex -> Real} (h₂f : forall x in Metric.sphere c |R
|, 0 <= f x) : 0 <= circl…
· 使用定理 `Real.posLog_nonneg`：posLog_nonneg : 0 <= log⁺ x
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
The proximity function is non-negative.
-/
theorem proximity_nonneg {a : WithTop E} :
    0 ≤ proximity f a := by
  by_cases h : a = ⊤ <;>
  · intro r
    simpa [proximity, h] using circleAverage_nonneg_of_nonneg (fun x _ ↦ posLog_nonneg)
/-
**ValueDistribution.proximity_const** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribution
`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] {c : E} {r : ℝ},   ValueDis
tribution.proximity (fun x => c) ⊤ r = ‖c‖.posLog
参数：fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.circleAverage_const`：circleAverage_const [CompleteSpace E] (a : E) 
(c : Complex) (R : Real) : circleAverage (fun _ => a) c R = a
-/
@[simp] lemma proximity_const {c : E} {r : ℝ} :
    proximity (fun _ ↦ c) ⊤ r = log⁺ ‖c‖ := by
  simp [proximity, circleAverage_const]

/--
If `f` is continuous, then so is its proximitiy function at `⊤`.
-/
/-
**ValueDistribution.continuous_proximity_top** 是 Mathlib 中的一个定理，位于命名空间 `ValueDis
tribution`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] {f : ℂ → E}, Continuous f →
 Continuous (ValueDistribution.proximity f ⊤)
参数：ValueDistribution.proximity f ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Real.Continuous.circleAverage`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] {c : ℂ} {f : ℂ → E},   Continuous f → Continuou
s (Real.circleAvera…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Real.continuous_posLog`：Continuous Real.posLog
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…

--- 原说明 ---
If `f` is continuous, then so is its proximitiy function at `⊤`.
-/
@[fun_prop] theorem continuous_proximity_top (hf : Continuous f) :
    Continuous (proximity f ⊤) := by
  simp only [proximity, reduceDIte]
  fun_prop

/-!
## Behaviour under Arithmetic Operations
-/

/--
The proximity function of a sum of functions at `⊤` is less than or equal to the sum of the
proximity functions of the summand, plus `log` of the number of summands.
-/
/-
**ValueDistribution.proximity_sum_top_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistrib
ution`。
形式化陈述：proximity_sum_top_le [NormedSpace Complex E] {α : Type*} (s : Finset α) (f
 : α -> Complex -> E) (hf : forall a in s, Meromorphic (f a)) : proximity (∑ a i
n s, f a) ⊤ <= ∑ a in s, (proximity (f a) ⊤) + (fun _ => log s.card)
参数：s : Finset α；f : α -> Complex -> E；hf : forall a in s, Meromorphic (f a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ValueDistribution.proximity_top`：proximity_top : proximity f ⊤ = circleA
verage (log⁺ ‖f ·‖) 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeromorphicOn.circleIntegrable_posLog_norm`：MeromorphicOn.circleIntegrab
le_posLog_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log⁺ ‖f
 ·‖) c R
· 使用定理 `Real.circleAverage_mono`：circleAverage_mono {c : Complex} {R : Real} {f₁
 f₂ : Complex -> Real} (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f
₂ c R) (h : f…
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用定理 `Meromorphic.fun_sum`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {ι 
: Type u_…
· 使用定理 `CircleIntegrable.fun_add`：∀ {E : Type u_1} [inst : NormedAddCommGroup E]
 {f g : ℂ → E} {c : ℂ} {R : ℝ},   CircleIntegrable f c R → CircleIntegrable g c 
R → CircleInte…
· 使用定理 `CircleIntegrable.fun_sum`：∀ {E : Type u_1} [inst : NormedAddCommGroup E]
 {c : ℂ} {R : ℝ} {ι : Type u_3} (s : Finset ι) {f : ι → ℂ → E},   (∀ i ∈ s, Circ
leIntegrable (…
· 使用定理 `circleIntegrable_const`：circleIntegrable_const (a : E) (c : Complex) (R 
: Real) : CircleIntegrable (fun _ => a) c R
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Real.posLog_norm_sum_le`：posLog_norm_sum_le {E : Type*} [SeminormedAddCo
mmGroup E] {α : Type*} (s : Finset α) (f : α -> E) : log⁺ ‖∑ t in s, f t‖ <= log
 s.card + ∑ t…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.circleAverage_const`：circleAverage_const [CompleteSpace E] (a : E) 
(c : Complex) (R : Real) : circleAverage (fun _ => a) c R = a
· 使用定理 `Real.circleAverage_sum`：circleAverage_sum {ι : Type*} {s : Finset ι} {f 
: ι -> Complex -> E} (h : forall i in s, CircleIntegrable (f i) c R) : circleAve
rage (∑ i in…
· 使用定理 `Real.circleAverage_add`：circleAverage_add (hf₁ : CircleIntegrable f₁ c R
) (hf₂ : CircleIntegrable f₂ c R) : circleAverage (f₁ + f₂) c R = circleAverage 
f₁ c R + cir…
· 使用定理 `CircleIntegrable.sum`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] {c 
: ℂ} {R : ℝ} {ι : Type u_3} (s : Finset ι) {f : ι → ℂ → E},   (∀ i ∈ s, CircleIn
tegrable (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The proximity function of a sum of functions at `⊤` is less than or equal to the
 sum of the
proximity functions of the summand, plus `log` of the number of summands.
-/
theorem proximity_sum_top_le [NormedSpace ℂ E] {α : Type*} (s : Finset α) (f : α → ℂ → E)
    (hf : ∀ a ∈ s, Meromorphic (f a)) :
    proximity (∑ a ∈ s, f a) ⊤ ≤ ∑ a ∈ s, (proximity (f a) ⊤) + (fun _ ↦ log s.card) := by
  simp only [proximity_top, Finset.sum_apply]
  intro r
  have h₂f : ∀ i ∈ s, CircleIntegrable (log⁺ ‖f i ·‖) 0 r :=
    fun i hi ↦ MeromorphicOn.circleIntegrable_posLog_norm (fun x hx ↦ hf i hi x)
  simp only [Pi.add_apply, Finset.sum_apply]
  calc circleAverage (log⁺ ‖∑ c ∈ s, f c ·‖) 0 r
    _ ≤ circleAverage (∑ c ∈ s, log⁺ ‖f c ·‖ + log s.card) 0 r := by
      apply circleAverage_mono
      · apply (Meromorphic.fun_sum hf).meromorphicOn.circleIntegrable_posLog_norm
      · fun_prop
      · intro x hx
        rw [add_comm]
        apply posLog_norm_sum_le
    _ = ∑ c ∈ s, circleAverage (log⁺ ‖f c ·‖) 0 r + log s.card := by
      nth_rw 2 [← circleAverage_const (log s.card) 0 r]
      rw [← circleAverage_sum h₂f, ← circleAverage_add (CircleIntegrable.sum s h₂f)
        (circleIntegrable_const (log s.card) 0 r)]
      congr 1
      ext x
      simp

/--
The proximity function of `f + g` at `⊤` is less than or equal to the sum of the proximity functions
of `f` and `g`, plus `log 2` (where `2` is the number of summands).
-/
/-
**ValueDistribution.proximity_add_top_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistrib
ution`。
形式化陈述：proximity_add_top_le [NormedSpace Complex E] {f₁ f₂ : Complex -> E} (h₁f₁ 
: Meromorphic f₁) (h₁f₂ : Meromorphic f₂) : proximity (f₁ + f₂) ⊤ <= (proximity 
f₁ ⊤) + (proximity f₂ ⊤) + (fun _ => log 2)
参数：h₁f₁ : Meromorphic f₁；h₁f₂ : Meromorphic f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `ValueDistribution.proximity_sum_top_le`：proximity_sum_top_le [NormedSpac
e Complex E] {α : Type*} (s : Finset α) (f : α -> Complex -> E) (hf : forall a i
n s, Meromorphic (f a)) : pr…
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
The proximity function of `f + g` at `⊤` is less than or equal to the sum of the
 proximity functions
of `f` and `g`, plus `log 2` (where `2` is the number of summands).
-/
theorem proximity_add_top_le [NormedSpace ℂ E] {f₁ f₂ : ℂ → E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    proximity (f₁ + f₂) ⊤ ≤ (proximity f₁ ⊤) + (proximity f₂ ⊤) + (fun _ ↦ log 2) := by
  simpa using proximity_sum_top_le Finset.univ ![f₁, f₂]
    (fun i ↦ by fin_cases i <;> aesop)

/--
The proximity function `f * g` at `⊤` is less than or equal to the sum of the proximity functions of
`f` and `g`, respectively.
-/
/-
**ValueDistribution.proximity_mul_top_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistrib
ution`。
形式化陈述：proximity_mul_top_le {f₁ f₂ : Complex -> Complex} (h₁f₁ : Meromorphic f₁) 
(h₁f₂ : Meromorphic f₂) : proximity (f₁ * f₂) ⊤ <= proximity f₁ ⊤ + proximity f₂
 ⊤
参数：h₁f₁ : Meromorphic f₁；h₁f₂ : Meromorphic f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用定理 `Real.circleAverage_mono`：circleAverage_mono {c : Complex} {R : Real} {f₁
 f₂ : Complex -> Real} (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f
₂ c R) (h : f…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `MeromorphicOn.circleIntegrable_posLog_norm`：MeromorphicOn.circleIntegrab
le_posLog_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log⁺ ‖f
 ·‖) c R
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用定理 `Meromorphic.fun_mul`：∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : Nontrivial
lyNormedField 𝕜] [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : NormedAlgebra
 𝕜 𝕜'] {f…
· 使用定理 `CircleIntegrable.add`：add (hf : CircleIntegrable f c R) (hg : CircleInte
grable g c R) : CircleIntegrable (f + g) c R
· 使用定理 `Real.posLog_mul`：posLog_mul : log⁺ (x * y) <= log⁺ x + log⁺ y
· 使用定理 `Real.circleAverage_add`：circleAverage_add (hf₁ : CircleIntegrable f₁ c R
) (hf₂ : CircleIntegrable f₂ c R) : circleAverage (f₁ + f₂) c R = circleAverage 
f₁ c R + cir…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
The proximity function `f * g` at `⊤` is less than or equal to the sum of the pr
oximity functions of
`f` and `g`, respectively.
-/
theorem proximity_mul_top_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) :
    proximity (f₁ * f₂) ⊤ ≤ proximity f₁ ⊤ + proximity f₂ ⊤ := by
  calc proximity (f₁ * f₂) ⊤
    _ = circleAverage (fun x ↦ log⁺ (‖f₁ x‖ * ‖f₂ x‖)) 0 := by
      simp [proximity]
    _ ≤ circleAverage (fun x ↦ log⁺ ‖f₁ x‖ + log⁺ ‖f₂ x‖) 0 := by
      intro r
      apply circleAverage_mono
      · simp_rw [← norm_mul]
        apply MeromorphicOn.circleIntegrable_posLog_norm
        apply Meromorphic.meromorphicOn
        fun_prop
      · apply (MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₁ x)).add
          (MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₂ x))
      · exact fun _ _ ↦ posLog_mul
    _ = circleAverage (log⁺ ‖f₁ ·‖) 0 + circleAverage (log⁺ ‖f₂ ·‖) 0 := by
      ext r
      apply circleAverage_add
      · exact MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₁ x)
      · exact MeromorphicOn.circleIntegrable_posLog_norm (fun x a ↦ h₁f₂ x)
    _ = proximity f₁ ⊤ + proximity f₂ ⊤ := by simp [proximity]

/--
The proximity function `f * g` at `0` is less than or equal to the sum of the proximity functions of
`f` and `g`, respectively.
-/
/-
**ValueDistribution.proximity_mul_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistri
bution`。
形式化陈述：proximity_mul_zero_le {f₁ f₂ : Complex -> Complex} (h₁f₁ : Meromorphic f₁)
 (h₁f₂ : Meromorphic f₂) : proximity (f₁ * f₂) 0 <= (proximity f₁ 0) + (proximit
y f₂ 0)
参数：h₁f₁ : Meromorphic f₁；h₁f₂ : Meromorphic f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValueDistribution.proximity_inv`：proximity_inv {f : Complex -> Complex} 
: proximity f⁻¹ ⊤ = proximity f 0
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `ValueDistribution.proximity_mul_top_le`：proximity_mul_top_le {f₁ f₂ : Co
mplex -> Complex} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) : proximity (f
₁ * f₂) ⊤ <= proximity f₁ ⊤ …
· 使用引理 `Meromorphic.inv`：inv {f : 𝕜 -> 𝕜'} (hf : Meromorphic f) : Meromorphic f⁻
¹

--- 原说明 ---
The proximity function `f * g` at `0` is less than or equal to the sum of the pr
oximity functions of
`f` and `g`, respectively.
-/
theorem proximity_mul_zero_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) :
    proximity (f₁ * f₂) 0 ≤ (proximity f₁ 0) + (proximity f₂ 0) := by
  calc proximity (f₁ * f₂) 0
    _ ≤ (proximity f₁⁻¹ ⊤) + (proximity f₂⁻¹ ⊤) := by
      rw [← proximity_inv, mul_inv]
      apply proximity_mul_top_le h₁f₁.inv h₁f₂.inv
    _ = (proximity f₁ 0) + (proximity f₂ 0) := by
      rw [proximity_inv, proximity_inv]

/--
For natural numbers `n`, the proximity function of `f ^ n` at `⊤` equals `n` times the proximity
function of `f` at `⊤`.
-/
/-
**ValueDistribution.proximity_pow_top** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistributi
on`。
形式化陈述：∀ {f : ℂ → ℂ} {n : ℕ}, ValueDistribution.proximity (f ^ n) ⊤ = n • ValueDi
stribution.proximity f ⊤
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.posLog_pow`：∀ (n : ℕ) (x : ℝ), (x ^ n).posLog = ↑n * x.posLog
· 使用定理 `Real.circleAverage_fun_smul`：circleAverage_fun_smul : circleAverage (fun
 z => a • f z) c R = a • circleAverage f c R
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a

--- 原说明 ---
For natural numbers `n`, the proximity function of `f ^ n` at `⊤` equals `n` tim
es the proximity
function of `f` at `⊤`.
-/
@[simp] theorem proximity_pow_top {f : ℂ → ℂ} {n : ℕ} :
    proximity (f ^ n) ⊤ = n • (proximity f ⊤) := by
  ext x
  simp [proximity, ← smul_eq_mul, circleAverage_fun_smul]

/--
For natural numbers `n`, the proximity function of `f ^ n` at `0` equals `n` times the proximity
function of `f` at `0`.
-/
/-
**ValueDistribution.proximity_pow_zero** 是 Mathlib 中的一个定理，位于命名空间 `ValueDistribut
ion`。
形式化陈述：∀ {f : ℂ → ℂ} {n : ℕ}, ValueDistribution.proximity (f ^ n) 0 = n • ValueDi
stribution.proximity f 0
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ValueDistribution.proximity_inv`：proximity_inv {f : Complex -> Complex} 
: proximity f⁻¹ ⊤ = proximity f 0
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `ValueDistribution.proximity_pow_top`：∀ {f : ℂ → ℂ} {n : ℕ}, ValueDistrib
ution.proximity (f ^ n) ⊤ = n • ValueDistribution.proximity f ⊤

--- 原说明 ---
For natural numbers `n`, the proximity function of `f ^ n` at `0` equals `n` tim
es the proximity
function of `f` at `0`.
-/
@[simp] theorem proximity_pow_zero {f : ℂ → ℂ} {n : ℕ} :
    proximity (f ^ n) 0 = n • (proximity f 0) := by
  rw [← proximity_inv, ← proximity_inv, ← inv_pow, proximity_pow_top]

end ValueDistribution

