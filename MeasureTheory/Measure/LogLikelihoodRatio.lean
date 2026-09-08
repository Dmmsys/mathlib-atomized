/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Log-likelihood Ratio

The likelihood ratio between two measures `μ` and `ν` is their Radon-Nikodym derivative
`μ.rnDeriv ν`. The logarithm of that function is often used instead: this is the log-likelihood
ratio.

This file contains a definition of the log-likelihood ratio (llr) and its properties.

## Main definitions

* `llr μ ν`: Log-Likelihood Ratio between `μ` and `ν`, defined as the function
  `x ↦ log (μ.rnDeriv ν x).toReal`.

-/

@[expose] public section

open Real

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {f : α → ℝ}

/-- Log-Likelihood Ratio between two measures. -/
/-
**MeasureTheory.llr** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：llr (μ ν : Measure α) (x : α) : Real
参数：μ ν : Measure α；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Log-Likelihood Ratio between two measures.
-/
noncomputable def llr (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal
/-
**MeasureTheory.llr_def** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：llr_def (μ ν : Measure α) : llr μ ν = fun x => log (μ.rnDeriv ν x).toReal
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma llr_def (μ ν : Measure α) : llr μ ν = fun x ↦ log (μ.rnDeriv ν x).toReal := rfl
/-
**MeasureTheory.llr_self** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：llr_self (μ : Measure α) [SigmaFinite μ] : llr μ μ =ᵐ[μ] 0
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_self`：rnDeriv_self (μ : Measure α) [SigmaF
inite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ => 1
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma llr_self (μ : Measure α) [SigmaFinite μ] : llr μ μ =ᵐ[μ] 0 := by
  filter_upwards [μ.rnDeriv_self] with a ha using by simp [llr, ha]
/-
**MeasureTheory.exp_llr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：exp_llr (μ ν : Measure α) [SigmaFinite μ] : (fun x => exp (llr μ ν x)) =ᵐ[
ν] fun x => if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv ν x).toReal
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.llr.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace α} (μ ν :
 MeasureTheory.Measure α) (x : α),   MeasureTheory.llr μ ν x = Real.log (μ.rnDer
iv ν x).toRe…
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma exp_llr (μ ν : Measure α) [SigmaFinite μ] :
    (fun x ↦ exp (llr μ ν x))
      =ᵐ[ν] fun x ↦ if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv ν x).toReal := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [llr, h_zero, ENNReal.toReal_zero, log_zero, exp_zero, ite_true]
  · rw [llr, exp_log, if_neg h_zero]
    exact ENNReal.toReal_pos h_zero hx.ne
/-
**MeasureTheory.exp_llr_of_ac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：exp_llr_of_ac (μ ν : Measure α) [SigmaFinite μ] [Measure.HaveLebesgueDecom
position μ ν] (hμν : μ ≪ ν) : (fun x => exp (llr μ ν x)) =ᵐ[μ] fun x => (μ.rnDer
iv ν x).toReal
参数：μ ν : Measure α；hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_pos`：rnDeriv_pos [HaveLebesgueDecompositio
n μ ν] (hμν : μ ≪ ν) : forallᵐ x ∂μ, 0 < μ.rnDeriv ν x
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用引理 `MeasureTheory.exp_llr`：exp_llr (μ ν : Measure α) [SigmaFinite μ] : (fun 
x => exp (llr μ ν x)) =ᵐ[ν] fun x => if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv
 ν x).toRea…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma exp_llr_of_ac (μ ν : Measure α) [SigmaFinite μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) :
    (fun x ↦ exp (llr μ ν x)) =ᵐ[μ] fun x ↦ (μ.rnDeriv ν x).toReal := by
  filter_upwards [hμν.ae_le (exp_llr μ ν), Measure.rnDeriv_pos hμν] with x hx_eq hx_pos
  rw [hx_eq, if_neg hx_pos.ne']
/-
**MeasureTheory.exp_llr_of_ac'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：exp_llr_of_ac' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hμν : ν 
≪ μ) : (fun x => exp (llr μ ν x)) =ᵐ[ν] fun x => (μ.rnDeriv ν x).toReal
参数：μ ν : Measure α；hμν : ν ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_pos'`：rnDeriv_pos' [HaveLebesgueDecomposit
ion ν μ] [SigmaFinite μ] (hμν : μ ≪ ν) : forallᵐ x ∂μ, 0 < ν.rnDeriv μ x
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.exp_llr`：exp_llr (μ ν : Measure α) [SigmaFinite μ] : (fun 
x => exp (llr μ ν x)) =ᵐ[ν] fun x => if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv
 ν x).toRea…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma exp_llr_of_ac' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ) :
    (fun x ↦ exp (llr μ ν x)) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toReal := by
  filter_upwards [exp_llr μ ν, Measure.rnDeriv_pos' hμν] with x hx hx_pos
  rwa [if_neg hx_pos.ne'] at hx
/-
**MeasureTheory.neg_llr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) : -llr μ ν =ᵐ[μ] llr
 ν μ
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.inv_rnDeriv`：inv_rnDeriv [SigmaFinite μ] [SigmaFin
ite ν] (hμν : μ ≪ ν) : (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用定理 `MeasureTheory.llr.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace α} (μ ν :
 MeasureTheory.Measure α) (x : α),   MeasureTheory.llr μ ν x = Real.log (μ.rnDer
iv ν x).toRe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
-/
lemma neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    -llr μ ν =ᵐ[μ] llr ν μ := by
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [Pi.neg_apply, llr, llr, ← log_inv, ← ENNReal.toReal_inv]
  congr
/-
**MeasureTheory.exp_neg_llr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：exp_neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) : (fun x => exp 
(-llr μ ν x)) =ᵐ[μ] fun x => (ν.rnDeriv μ x).toReal
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.exp_llr_of_ac'`：exp_llr_of_ac' (μ ν : Measure α) [SigmaFin
ite μ] [SigmaFinite ν] (hμν : ν ≪ μ) : (fun x => exp (llr μ ν x)) =ᵐ[ν] fun x =>
 (μ.rnDeriv ν x).t…
· 使用引理 `MeasureTheory.neg_llr`：neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ 
≪ ν) : -llr μ ν =ᵐ[μ] llr ν μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
-/
lemma exp_neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (fun x ↦ exp (-llr μ ν x)) =ᵐ[μ] fun x ↦ (ν.rnDeriv μ x).toReal := by
  filter_upwards [neg_llr hμν, exp_llr_of_ac' ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply] at hx
  rw [hx, hx_exp_log]
/-
**MeasureTheory.exp_neg_llr'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：exp_neg_llr' [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ) : (fun x => exp
 (-llr μ ν x)) =ᵐ[ν] fun x => (ν.rnDeriv μ x).toReal
参数：hμν : ν ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.exp_llr_of_ac`：exp_llr_of_ac (μ ν : Measure α) [SigmaFinit
e μ] [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) : (fun x => exp (llr 
μ ν x)) =ᵐ[μ] fun…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.neg_llr`：neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ 
≪ ν) : -llr μ ν =ᵐ[μ] llr ν μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
-/
lemma exp_neg_llr' [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ) :
    (fun x ↦ exp (-llr μ ν x)) =ᵐ[ν] fun x ↦ (ν.rnDeriv μ x).toReal := by
  filter_upwards [neg_llr hμν, exp_llr_of_ac ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply, neg_eq_iff_eq_neg] at hx
  rw [← hx, hx_exp_log]

@[fun_prop]
/-
**MeasureTheory.measurable_llr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measurable_llr (μ ν : Measure α) : Measurable (llr μ ν)
参数：μ ν : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.log`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Me
asurable f → Measurable fun x => Real.log (f x)
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
-/
lemma measurable_llr (μ ν : Measure α) : Measurable (llr μ ν) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_toReal.log

@[fun_prop]
/-
**MeasureTheory.stronglyMeasurable_llr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：stronglyMeasurable_llr (μ ν : Measure α) : StronglyMeasurable (llr μ ν)
参数：μ ν : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `MeasureTheory.measurable_llr`：measurable_llr (μ ν : Measure α) : Measura
ble (llr μ ν)
-/
lemma stronglyMeasurable_llr (μ ν : Measure α) : StronglyMeasurable (llr μ ν) :=
  (measurable_llr μ ν).stronglyMeasurable
/-
**MeasureTheory.llr_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：llr_smul_left [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν] 
(hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_ne_top : c != ∞) : llr (c • μ) ν 
=ᵐ[μ] fun x => llr μ ν x + log c.toReal
参数：hμν : μ ≪ ν；c : Real>=0∞；hc : c != 0；hc_ne_top : c != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.rnDeriv_smul_left_of_ne_top`：rnDeriv_smul_left_of_
ne_top (ν μ : Measure α) [IsFiniteMeasure ν] [ν.HaveLebesgueDecomposition μ] {r 
: Real>=0∞} (hr : r != ∞) : (r • ν).rnD…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `MeasureTheory.Measure.rnDeriv_pos`：rnDeriv_pos [HaveLebesgueDecompositio
n μ ν] (hμν : μ ≪ ν) : forallᵐ x ∂μ, 0 < μ.rnDeriv ν x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `ENNReal.toReal_ne_zero`：toReal_ne_zero : a.toReal != 0 ↔ a != 0 ∧ a != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
-/
lemma llr_smul_left [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    llr (c • μ) ν =ᵐ[μ] fun x ↦ llr μ ν x + log c.toReal := by
  simp only [llr, llr_def]
  have h := Measure.rnDeriv_smul_left_of_ne_top μ ν hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [log_mul]
  rotate_left
  · rw [ENNReal.toReal_ne_zero]
    simp [hc, hc_ne_top]
  · rw [ENNReal.toReal_ne_zero]
    simp [hx_pos.ne', hx_ne_top.ne]
  ring
/-
**MeasureTheory.llr_smul_nnreal_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：llr_smul_nnreal_left [IsFiniteMeasure μ] [Measure.HaveLebesgueDecompositio
n μ ν] (hμν : μ ≪ ν) (c : Real>=0) (hc : c != 0) : llr (c • μ) ν =ᵐ[μ] fun x => 
llr μ ν x + log c
参数：hμν : μ ≪ ν；c : Real>=0；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.coe_nnreal_smul`：coe_nnreal_smul (c : Real>=0) (μ 
: Measure α) : (c : Real>=0∞) • μ = c • μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.llr_smul_left`：llr_smul_left [IsFiniteMeasure μ] [Measure.
HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_ne
_top : c != ∞) : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma llr_smul_nnreal_left [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0) (hc : c ≠ 0) :
    llr (c • μ) ν =ᵐ[μ] fun x ↦ llr μ ν x + log c := by
  rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_left hμν (c : ℝ≥0∞) (by simpa) (by simp)] with x hx
  rw [hx]
  simp
/-
**MeasureTheory.llr_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：llr_smul_right [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
 (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_ne_top : c != ∞) : llr μ (c • ν)
 =ᵐ[μ] fun x => llr μ ν x - log c.toReal
参数：hμν : μ ≪ ν；c : Real>=0∞；hc : c != 0；hc_ne_top : c != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.rnDeriv_smul_right_of_ne_top`：rnDeriv_smul_right_o
f_ne_top (ν μ : Measure α) [IsFiniteMeasure ν] [ν.HaveLebesgueDecomposition μ] {
r : Real>=0∞} (hr : r != 0) (hr_ne_top :…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `MeasureTheory.Measure.rnDeriv_pos`：rnDeriv_pos [HaveLebesgueDecompositio
n μ ν] (hμν : μ ≪ ν) : forallᵐ x ∂μ, 0 < μ.rnDeriv ν x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `ENNReal.toReal_ne_zero`：toReal_ne_zero : a.toReal != 0 ↔ a != 0 ∧ a != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 42 条，此处仅展示前 30 条）
-/
lemma llr_smul_right [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    llr μ (c • ν) =ᵐ[μ] fun x ↦ llr μ ν x - log c.toReal := by
  simp only [llr, llr_def]
  have h := Measure.rnDeriv_smul_right_of_ne_top μ ν hc hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [log_mul]
  rotate_left
  · rw [ENNReal.toReal_ne_zero]
    simp [hc, hc_ne_top]
  · rw [ENNReal.toReal_ne_zero]
    simp [hx_pos.ne', hx_ne_top.ne]
  rw [ENNReal.toReal_inv, log_inv]
  ring
/-
**MeasureTheory.llr_smul_nnreal_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：llr_smul_nnreal_right [IsFiniteMeasure μ] [Measure.HaveLebesgueDecompositi
on μ ν] (hμν : μ ≪ ν) (c : Real>=0) (hc : c != 0) : llr μ (c • ν) =ᵐ[μ] fun x =>
 llr μ ν x - log c
参数：hμν : μ ≪ ν；c : Real>=0；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.coe_nnreal_smul`：coe_nnreal_smul (c : Real>=0) (μ 
: Measure α) : (c : Real>=0∞) • μ = c • μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.llr_smul_right`：llr_smul_right [IsFiniteMeasure μ] [Measur
e.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_
ne_top : c != ∞) :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma llr_smul_nnreal_right [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0) (hc : c ≠ 0) :
    llr μ (c • ν) =ᵐ[μ] fun x ↦ llr μ ν x - log c := by
  rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_right hμν (c : ℝ≥0∞) (by simpa) (by simp)] with x hx
  rw [hx]
  simp
/-
**MeasureTheory.llr_smul_inv_left_eq_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：llr_smul_inv_left_eq_smul_right [IsFiniteMeasure μ] [Measure.HaveLebesgueD
ecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_ne_top : c != ∞
) : llr (c⁻¹ • μ) ν =ᵐ[μ] llr μ (c • ν)
参数：hμν : μ ≪ ν；c : Real>=0∞；hc : c != 0；hc_ne_top : c != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.llr_smul_right`：llr_smul_right [IsFiniteMeasure μ] [Measur
e.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_
ne_top : c != ∞) :…
· 使用引理 `MeasureTheory.llr_smul_left`：llr_smul_left [IsFiniteMeasure μ] [Measure.
HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_ne
_top : c != ∞) : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma llr_smul_inv_left_eq_smul_right [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    llr (c⁻¹ • μ) ν =ᵐ[μ] llr μ (c • ν) := by
  have hc' : c⁻¹ ≠ 0 := by simp [hc_ne_top]
  have hc_ne_top' : c⁻¹ ≠ ∞ := by simp [hc]
  filter_upwards [llr_smul_left hμν c⁻¹ hc' hc_ne_top', llr_smul_right hμν c hc hc_ne_top] with
    x hx_left hx_right
  rw [hx_left, hx_right]
  simp [sub_eq_add_neg]
/-
**MeasureTheory.llr_smul_same** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：llr_smul_same [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν] 
(hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_ne_top : c != ∞) : llr (c • μ) (c
 • ν) =ᵐ[μ] llr μ ν
参数：hμν : μ ≪ ν；c : Real>=0∞；hc : c != 0；hc_ne_top : c != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用定理 `MeasureTheory.Measure.rnDeriv_smul_same`：rnDeriv_smul_same (ν μ : Measur
e α) [IsFiniteMeasure ν] [ν.HaveLebesgueDecomposition μ] {r : Real>=0} (hr : r !
= 0) : (r • ν).rnDeriv (r • μ…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma llr_smul_same [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    llr (c • μ) (c • ν) =ᵐ[μ] llr μ ν := by
  simp only [llr_def]
  lift c to ℝ≥0 using hc_ne_top
  norm_cast at hc
  filter_upwards [hμν.ae_le (Measure.rnDeriv_smul_same μ ν hc)] with x hx using by simp [hx]
/-
**MeasureTheory.llr_smul_nnreal_same** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：llr_smul_nnreal_same [IsFiniteMeasure μ] [Measure.HaveLebesgueDecompositio
n μ ν] (hμν : μ ≪ ν) (c : Real>=0) (hc : c != 0) : llr (c • μ) (c • ν) =ᵐ[μ] llr
 μ ν
参数：hμν : μ ≪ ν；c : Real>=0；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.llr_smul_same`：llr_smul_same [IsFiniteMeasure μ] [Measure.
HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_ne
_top : c != ∞) : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma llr_smul_nnreal_same [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0) (hc : c ≠ 0) :
    llr (c • μ) (c • ν) =ᵐ[μ] llr μ ν := by
  simp_rw [← Measure.coe_nnreal_smul]
  filter_upwards [llr_smul_same hμν (c : ℝ≥0∞) (by simpa) (by simp)] with x hx
  rw [hx]
/-
**MeasureTheory.integrable_rnDeriv_mul_log_iff** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：integrable_rnDeriv_mul_log_iff [SigmaFinite μ] [μ.HaveLebesgueDecompositio
n ν] (hμν : μ ≪ ν) : Integrable (fun a => (μ.rnDeriv ν a).toReal * log (μ.rnDeri
v ν a).toReal) ν ↔ Integrable (llr μ ν) μ
参数：hμν : μ ≪ ν。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_rnDeriv_smul_iff`：integrable_rnDeriv_smul_iff (
hμν : μ ≪ ν) : Integrable (fun x => (μ.rnDeriv ν x).toReal • f x) ν ↔ Integrable
 f μ
-/
lemma integrable_rnDeriv_mul_log_iff [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) :
    Integrable (fun a ↦ (μ.rnDeriv ν a).toReal * log (μ.rnDeriv ν a).toReal) ν
      ↔ Integrable (llr μ ν) μ :=
  integrable_rnDeriv_smul_iff hμν
/-
**MeasureTheory.integral_rnDeriv_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integral_rnDeriv_mul_log [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (
hμν : μ ≪ ν) : ∫ a, (μ.rnDeriv ν a).toReal * log (μ.rnDeriv ν a).toReal ∂ν = ∫ a
, llr μ ν a ∂μ
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_rnDeriv_smul`：integral_rnDeriv_smul (hμν : μ ≪ ν)
 : ∫ x, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_rnDeriv_mul_log [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) :
    ∫ a, (μ.rnDeriv ν a).toReal * log (μ.rnDeriv ν a).toReal ∂ν = ∫ a, llr μ ν a ∂μ := by
  simp_rw [← smul_eq_mul, integral_rnDeriv_smul hμν, llr]

section llr_tilted

/-
**MeasureTheory.llr_tilted_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：llr_tilted_left [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : Integr
able (fun x => exp (f x)) μ) (hfν : AEMeasurable f ν) : (llr (μ.tilted f) ν) =ᵐ[
μ] fun x => f x - log (∫ z, exp (f z) ∂μ) + llr μ ν x
参数：hμν : μ ≪ ν；hf : Integrable (fun x => exp (f x)) μ；hfν : AEMeasurable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用引理 `MeasureTheory.Measure.rnDeriv_pos`：rnDeriv_pos [HaveLebesgueDecompositio
n μ ν] (hμν : μ ≪ ν) : forallᵐ x ∂μ, 0 < μ.rnDeriv ν x
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.toReal_rnDeriv_tilted_left`：toReal_rnDeriv_tilted_left {ν 
: Measure α} [SigmaFinite μ] [SigmaFinite ν] (hfν : AEMeasurable f ν) : (fun x =
> ((μ.tilted f).rnDeriv ν x).t…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.llr.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace α} (μ ν :
 MeasureTheory.Measure α) (x : α),   MeasureTheory.llr μ ν x = Real.log (μ.rnDer
iv ν x).toRe…
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用引理 `MeasureTheory.integral_exp_pos`：integral_exp_pos {μ : Measure α} {f : α 
-> Real} [hμ : NeZero μ] (hf : Integrable (fun x => Real.exp (f x)) μ) : 0 < ∫ x
, Real.exp (f x) ∂μ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
（共 32 条，此处仅展示前 30 条）
-/
lemma llr_tilted_left [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    (hf : Integrable (fun x ↦ exp (f x)) μ) (hfν : AEMeasurable f ν) :
    (llr (μ.tilted f) ν) =ᵐ[μ] fun x ↦ f x - log (∫ z, exp (f z) ∂μ) + llr μ ν x := by
  cases eq_zero_or_neZero μ with
  | inl hμ =>
    simp only [hμ, ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  | inr h0 =>
    filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_left μ hfν), Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
    rw [llr, hx, log_mul, div_eq_mul_inv, log_mul (exp_pos _).ne', log_exp, log_inv, llr,
      ← sub_eq_add_neg]
    · simp only [ne_eq, inv_eq_zero]
      exact (integral_exp_pos hf).ne'
    · simp only [ne_eq, div_eq_zero_iff]
      push Not
      exact ⟨(exp_pos _).ne', (integral_exp_pos hf).ne'⟩
    · simp [ENNReal.toReal_eq_zero_iff, hx_lt_top.ne, hx_pos.ne']
/-
**MeasureTheory.integrable_llr_tilted_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integrable_llr_tilted_left [IsFiniteMeasure μ] [SigmaFinite ν] (hμν : μ ≪ 
ν) (hf : Integrable f μ) (h_int : Integrable (llr μ ν) μ) (hfμ : Integrable (fun
 x => exp (f x)) μ) (hfν : AEMeasurable f ν) : Integrable (llr (μ.tilted f) ν) μ
参数：hμν : μ ≪ ν；hf : Integrable f μ；h_int : Integrable (llr μ ν) μ；hfμ : Integrab
le (fun x => exp (f x)) μ；hfν : AEMeasurable f ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用引理 `MeasureTheory.llr_tilted_left`：llr_tilted_left [SigmaFinite μ] [SigmaFin
ite ν] (hμν : μ ≪ ν) (hf : Integrable (fun x => exp (f x)) μ) (hfν : AEMeasurabl
e f ν) : (llr (μ.ti…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
-/
lemma integrable_llr_tilted_left [IsFiniteMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hf : Integrable f μ) (h_int : Integrable (llr μ ν) μ)
    (hfμ : Integrable (fun x ↦ exp (f x)) μ) (hfν : AEMeasurable f ν) :
    Integrable (llr (μ.tilted f) ν) μ := by
  rw [integrable_congr (llr_tilted_left hμν hfμ hfν)]
  exact Integrable.add (hf.sub (integrable_const _)) h_int
/-
**MeasureTheory.integral_llr_tilted_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integral_llr_tilted_left [IsProbabilityMeasure μ] [SigmaFinite ν] (hμν : μ
 ≪ ν) (hf : Integrable f μ) (h_int : Integrable (llr μ ν) μ) (hfμ : Integrable (
fun x => exp (f x)) μ) (hfν : AEMeasurable f ν) : ∫ x, llr (μ.tilted f) ν x ∂μ =
 ∫ x, llr μ ν x ∂μ + ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ)
参数：hμν : μ ≪ ν；hf : Integrable f μ；h_int : Integrable (llr μ ν) μ；hfμ : Integrab
le (fun x => exp (f x)) μ；hfν : AEMeasurable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用引理 `MeasureTheory.llr_tilted_left`：llr_tilted_left [SigmaFinite μ] [SigmaFin
ite ν] (hμν : μ ≪ ν) (hf : Integrable (fun x => exp (f x)) μ) (hfν : AEMeasurabl
e f ν) : (llr (μ.ti…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.LogLikelihoodRatio.0.MeasureTheor
y.integral_llr_tilted_left._abel_1_1`：∀ {α : Type u_1} {mα : MeasurableSpace α} 
{μ ν : MeasureTheory.Measure α} {f : α → ℝ},   ∫ (x : α), f x ∂μ - Real.log (∫ (
x : α), Real.exp (…
-/
lemma integral_llr_tilted_left [IsProbabilityMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hf : Integrable f μ) (h_int : Integrable (llr μ ν) μ)
    (hfμ : Integrable (fun x ↦ exp (f x)) μ) (hfν : AEMeasurable f ν) :
    ∫ x, llr (μ.tilted f) ν x ∂μ = ∫ x, llr μ ν x ∂μ + ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ) := by
  calc ∫ x, llr (μ.tilted f) ν x ∂μ
    = ∫ x, f x - log (∫ x, exp (f x) ∂μ) + llr μ ν x ∂μ :=
        integral_congr_ae (llr_tilted_left hμν hfμ hfν)
  _ = ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ) + ∫ x, llr μ ν x ∂μ := by
        rw [integral_add ?_ h_int]
        swap; · exact hf.sub (integrable_const _)
        rw [integral_sub hf (integrable_const _)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  _ = ∫ x, llr μ ν x ∂μ + ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ) := by abel
/-
**MeasureTheory.llr_tilted_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：llr_tilted_right [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : Integ
rable (fun x => exp (f x)) ν) : (llr μ (ν.tilted f)) =ᵐ[μ] fun x => -f x + log (
∫ z, exp (f z) ∂ν) + llr μ ν x
参数：hμν : μ ≪ ν；hf : Integrable (fun x => exp (f x)) ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用引理 `MeasureTheory.Measure.rnDeriv_pos`：rnDeriv_pos [HaveLebesgueDecompositio
n μ ν] (hμν : μ ≪ ν) : forallᵐ x ∂μ, 0 < μ.rnDeriv ν x
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.toReal_rnDeriv_tilted_right`：toReal_rnDeriv_tilted_right (
μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hf : Integrable (fun x => exp 
(f x)) ν) : (fun x => (μ.rnDeri…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.llr.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace α} (μ ν :
 MeasureTheory.Measure α) (x : α),   MeasureTheory.llr μ ν x = Real.log (μ.rnDer
iv ν x).toRe…
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用引理 `MeasureTheory.integral_exp_pos`：integral_exp_pos {μ : Measure α} {f : α 
-> Real} [hμ : NeZero μ] (hf : Integrable (fun x => Real.exp (f x)) μ) : 0 < ∫ x
, Real.exp (f x) ∂μ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
（共 32 条，此处仅展示前 30 条）
-/
lemma llr_tilted_right [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hf : Integrable (fun x ↦ exp (f x)) ν) :
    (llr μ (ν.tilted f)) =ᵐ[μ] fun x ↦ -f x + log (∫ z, exp (f z) ∂ν) + llr μ ν x := by
  cases eq_zero_or_neZero ν with
  | inl h =>
    have hμ : μ = 0 := by ext s _; exact hμν (by simp [h])
    simp only [hμ, ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  | inr h0 =>
    filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_right μ ν hf), Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
    rw [llr, hx, log_mul, log_mul (exp_pos _).ne', log_exp, llr]
    · exact (integral_exp_pos hf).ne'
    · refine (mul_pos (exp_pos _) (integral_exp_pos hf)).ne'
    · simp [ENNReal.toReal_eq_zero_iff, hx_lt_top.ne, hx_pos.ne']
/-
**MeasureTheory.integrable_llr_tilted_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integrable_llr_tilted_right [IsFiniteMeasure μ] [SigmaFinite ν] (hμν : μ ≪
 ν) (hfμ : Integrable f μ) (h_int : Integrable (llr μ ν) μ) (hfν : Integrable (f
un x => exp (f x)) ν) : Integrable (llr μ (ν.tilted f)) μ
参数：hμν : μ ≪ ν；hfμ : Integrable f μ；h_int : Integrable (llr μ ν) μ；hfν : Integra
ble (fun x => exp (f x)) ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用引理 `MeasureTheory.llr_tilted_right`：llr_tilted_right [SigmaFinite μ] [SigmaF
inite ν] (hμν : μ ≪ ν) (hf : Integrable (fun x => exp (f x)) ν) : (llr μ (ν.tilt
ed f)) =ᵐ[μ] fun x =…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
-/
lemma integrable_llr_tilted_right [IsFiniteMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hfμ : Integrable f μ)
    (h_int : Integrable (llr μ ν) μ) (hfν : Integrable (fun x ↦ exp (f x)) ν) :
    Integrable (llr μ (ν.tilted f)) μ := by
  rw [integrable_congr (llr_tilted_right hμν hfν)]
  exact Integrable.add (hfμ.neg.add (integrable_const _)) h_int
/-
**MeasureTheory.integral_llr_tilted_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integral_llr_tilted_right [IsProbabilityMeasure μ] [SigmaFinite ν] (hμν : 
μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x => exp (f x)) ν) (h_int :
 Integrable (llr μ ν) μ) : ∫ x, llr μ (ν.tilted f) x ∂μ = ∫ x, llr μ ν x ∂μ - ∫ 
x, f x ∂μ + log (∫ x, exp (f x) ∂ν)
参数：hμν : μ ≪ ν；hfμ : Integrable f μ；hfν : Integrable (fun x => exp (f x)) ν；h_in
t : Integrable (llr μ ν) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用引理 `MeasureTheory.llr_tilted_right`：llr_tilted_right [SigmaFinite μ] [SigmaF
inite ν] (hμν : μ ≪ ν) (hf : Integrable (fun x => exp (f x)) ν) : (llr μ (ν.tilt
ed f)) =ᵐ[μ] fun x =…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.LogLikelihoodRatio.0.MeasureTheor
y.integral_llr_tilted_right._abel_1_1`：∀ {α : Type u_1} {mα : MeasurableSpace α}
 {μ ν : MeasureTheory.Measure α} {f : α → ℝ},   -∫ (x : α), f x ∂μ + Real.log (∫
 (x : α), Real.exp …
-/
lemma integral_llr_tilted_right [IsProbabilityMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ exp (f x)) ν)
    (h_int : Integrable (llr μ ν) μ) :
    ∫ x, llr μ (ν.tilted f) x ∂μ = ∫ x, llr μ ν x ∂μ - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) := by
  calc ∫ x, llr μ (ν.tilted f) x ∂μ
    = ∫ x, -f x + log (∫ x, exp (f x) ∂ν) + llr μ ν x ∂μ :=
        integral_congr_ae (llr_tilted_right hμν hfν)
  _ = -∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) + ∫ x, llr μ ν x ∂μ := by
        rw [← integral_neg, integral_add ?_ h_int]
        swap; · exact hfμ.neg.add (integrable_const _)
        rw [integral_add ?_ (integrable_const _)]
        swap; · exact hfμ.neg
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  _ = ∫ x, llr μ ν x ∂μ - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) := by abel

end llr_tilted

end MeasureTheory

