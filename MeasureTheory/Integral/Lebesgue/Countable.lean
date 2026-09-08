/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Lebesgue integral over finite and countable types, sets and measures

The lemmas in this file require at least one of the following of the Lebesgue integral:
* The type of the set of integration is finite or countable
* The set of integration is finite or countable
* The measure is finite, s-finite or sigma-finite
-/

public section

namespace MeasureTheory

open Set ENNReal NNReal Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

section FiniteMeasure

/-
**MeasureTheory.setLIntegral_const_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：setLIntegral_const_lt_top [IsFiniteMeasure μ] (s : Set α) {c : Real>=0∞} (
hc : c != ∞) : ∫⁻ _ in s, c ∂μ < ∞
参数：s : Set α；hc : c != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
theorem setLIntegral_const_lt_top [IsFiniteMeasure μ] (s : Set α) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    ∫⁻ _ in s, c ∂μ < ∞ := by
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top (μ.restrict s) univ)
/-
**MeasureTheory.lintegral_const_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lintegral_const_lt_top [IsFiniteMeasure μ] {c : Real>=0∞} (hc : c != ∞) : 
∫⁻ _, c ∂μ < ∞
参数：hc : c != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.setLIntegral_const_lt_top`：setLIntegral_const_lt_top [IsFi
niteMeasure μ] (s : Set α) {c : Real>=0∞} (hc : c != ∞) : ∫⁻ _ in s, c ∂μ < ∞
-/
theorem lintegral_const_lt_top [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) : ∫⁻ _, c ∂μ < ∞ := by
  simpa only [Measure.restrict_univ] using setLIntegral_const_lt_top (univ : Set α) hc
/-
**MeasureTheory.lintegral_eq_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_eq_const [IsProbabilityMeasure μ] {f : α -> Real>=0∞} {c : Real>
=0∞} (hf : forallᵐ x ∂μ, f x = c) : ∫⁻ x, f x ∂μ = c
参数：hf : forallᵐ x ∂μ, f x = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lintegral_eq_const [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, f x = c) : ∫⁻ x, f x ∂μ = c := by simp [lintegral_congr_ae hf]
/-
**MeasureTheory.lintegral_le_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_le_const [IsProbabilityMeasure μ] {f : α -> Real>=0∞} {c : Real>
=0∞} (hf : forallᵐ x ∂μ, f x <= c) : ∫⁻ x, f x ∂μ <= c
参数：hf : forallᵐ x ∂μ, f x <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lintegral_le_const [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, f x ≤ c) : ∫⁻ x, f x ∂μ ≤ c :=
  (lintegral_mono_ae hf).trans_eq (by simp)
/-
**MeasureTheory.iInf_le_lintegral** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：iInf_le_lintegral [IsProbabilityMeasure μ] (f : α -> Real>=0∞) : ⨅ x, f x 
<= ∫⁻ x, f x ∂μ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `MeasureTheory.iInf_mul_le_lintegral`：iInf_mul_le_lintegral (f : α -> Rea
l>=0∞) : (⨅ x, f x) * μ .univ <= ∫⁻ x, f x ∂μ
-/
lemma iInf_le_lintegral [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) : ⨅ x, f x ≤ ∫⁻ x, f x ∂μ :=
  le_trans (by simp) (iInf_mul_le_lintegral f)
/-
**MeasureTheory.lintegral_le_iSup** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_le_iSup [IsProbabilityMeasure μ] (f : α -> Real>=0∞) : ∫⁻ x, f x
 ∂μ <= ⨆ x, f x
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `MeasureTheory.lintegral_le_iSup_mul`：lintegral_le_iSup_mul (f : α -> Rea
l>=0∞) : ∫⁻ x, f x ∂μ <= (⨆ x, f x) * μ .univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma lintegral_le_iSup [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ ≤ ⨆ x, f x :=
  le_trans (lintegral_le_iSup_mul f) (by simp)

variable (μ) in
/-
**MeasureTheory._root_.IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
    [IsFiniteMeasure μ] {f : α → ℝ≥0∞} (f_bdd : ∃ c : ℝ≥0, ∀ x, f x ≤ c) : ∫⁻ x, f x ∂μ < ∞ := by
  rw [← μ.restrict_univ]
  refine setLIntegral_lt_top_of_le_nnreal (measure_ne_top _ _) ?_
  simpa using f_bdd

end FiniteMeasure

section DiracAndCount

/-
**MeasureTheory.lintegral_dirac'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_dirac' (a : α) {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f
 a ∂dirac a = f a
参数：a : α；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_eq_dirac'`：ae_eq_dirac' [MeasurableSingletonClass β] {a
 : α} {f : α -> β} (hf : Measurable f) : f =ᵐ[dirac a] const α (f a)
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_dirac' (a : α) {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a := by
  simp [lintegral_congr_ae (ae_eq_dirac' hf)]

@[simp]
/-
**MeasureTheory.lintegral_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_dirac [MeasurableSingletonClass α] (a : α) (f : α -> Real>=0∞) :
 ∫⁻ a, f a ∂dirac a = f a
参数：a : α；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_eq_dirac`：ae_eq_dirac [MeasurableSingletonClass α] {a :
 α} (f : α -> δ) : f =ᵐ[dirac a] const α (f a)
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_dirac [MeasurableSingletonClass α] (a : α) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂dirac a = f a := by simp [lintegral_congr_ae (ae_eq_dirac f)]
/-
**MeasureTheory.setLIntegral_dirac'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_dirac' {a : α} {f : α -> Real>=0∞} (hf : Measurable f) {s : S
et α} (hs : MeasurableSet s) [Decidable (a in s)] : ∫⁻ x in s, f x ∂Measure.dira
c a = if a in s then f a else 0
参数：hf : Measurable f；hs : MeasurableSet s；a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.restrict_dirac'`：restrict_dirac' (hs : MeasurableSet s) [D
ecidable (a in s)] : (Measure.dirac a).restrict s = if a in s then Measure.dirac
 a else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
-/
theorem setLIntegral_dirac' {a : α} {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α}
    (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫⁻ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac' hs]
  split_ifs
  · exact lintegral_dirac' _ hf
  · exact lintegral_zero_measure _
/-
**MeasureTheory.setLIntegral_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_dirac {a : α} (f : α -> Real>=0∞) (s : Set α) [MeasurableSing
letonClass α] [Decidable (a in s)] : ∫⁻ x in s, f x ∂Measure.dirac a = if a in s
 then f a else 0
参数：f : α -> Real>=0∞；s : Set α；a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.restrict_dirac`：restrict_dirac [MeasurableSingletonClass α
] [Decidable (a in s)] : (Measure.dirac a).restrict s = if a in s then Measure.d
irac a else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
-/
theorem setLIntegral_dirac {a : α} (f : α → ℝ≥0∞) (s : Set α) [MeasurableSingletonClass α]
    [Decidable (a ∈ s)] : ∫⁻ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac]
  split_ifs
  · exact lintegral_dirac _ _
  · exact lintegral_zero_measure _
/-
**MeasureTheory.lintegral_count'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_count' {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂coun
t = ∑' a, f a
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count.eq_1`：∀ {α : Type u_1} [inst : MeasurableSpa
ce α],   MeasureTheory.Measure.count = MeasureTheory.Measure.sum MeasureTheory.M
easure.dirac
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
-/
theorem lintegral_count' {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂count = ∑' a, f a := by
  rw [count, lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac' a hf
/-
**MeasureTheory.lintegral_count** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_count [MeasurableSingletonClass α] (f : α -> Real>=0∞) : ∫⁻ a, f
 a ∂count = ∑' a, f a
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count.eq_1`：∀ {α : Type u_1} [inst : MeasurableSpa
ce α],   MeasureTheory.Measure.count = MeasureTheory.Measure.sum MeasureTheory.M
easure.dirac
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a
-/
theorem lintegral_count [MeasurableSingletonClass α] (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂count = ∑' a, f a := by
  rw [count, lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac a f

/-- Markov's inequality for the counting measure with hypothesis using `tsum` in `ℝ≥0∞`. -/
/-
**MeasureTheory._root_.ENNReal.count_const_le_le_of_tsum_le** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Markov's inequality for the counting measure with hypothesis using `tsum` in `ℝ≥
0∞`.
-/
theorem _root_.ENNReal.count_const_le_le_of_tsum_le [MeasurableSingletonClass α] {a : α → ℝ≥0∞}
    (a_mble : Measurable a) {c : ℝ≥0∞} (tsum_le_c : ∑' i, a i ≤ c) {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0)
    (ε_ne_top : ε ≠ ∞) : Measure.count { i : α | ε ≤ a i } ≤ c / ε := by
  rw [← lintegral_count] at tsum_le_c
  apply (MeasureTheory.meas_ge_le_lintegral_div a_mble.aemeasurable ε_ne_zero ε_ne_top).trans
  exact ENNReal.div_le_div tsum_le_c rfl.le

/-- Markov's inequality for the counting measure with hypothesis using `tsum` in `ℝ≥0`. -/
/-
**MeasureTheory._root_.NNReal.count_const_le_le_of_tsum_le** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Markov's inequality for the counting measure with hypothesis using `tsum` in `ℝ≥
0`.
-/
theorem _root_.NNReal.count_const_le_le_of_tsum_le [MeasurableSingletonClass α] {a : α → ℝ≥0}
    (a_mble : Measurable a) (a_summable : Summable a) {c : ℝ≥0} (tsum_le_c : ∑' i, a i ≤ c)
    {ε : ℝ≥0} (ε_ne_zero : ε ≠ 0) : Measure.count { i : α | ε ≤ a i } ≤ c / ε := by
  rw [show (fun i => ε ≤ a i) = fun i => (ε : ℝ≥0∞) ≤ ((↑) ∘ a) i by
      simp only [ENNReal.coe_le_coe, Function.comp]]
  apply
    ENNReal.count_const_le_le_of_tsum_le (measurable_coe_nnreal_ennreal.comp a_mble) _
      (mod_cast ε_ne_zero) (@ENNReal.coe_ne_top ε)
  convert! ENNReal.coe_le_coe.mpr tsum_le_c
  simp_rw [Function.comp_apply]
  rw [ENNReal.tsum_coe_eq a_summable.hasSum]

end DiracAndCount

section Countable

/-
**MeasureTheory.lintegral_countable'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_countable' [Countable α] [MeasurableSingletonClass α] (f : α -> 
Real>=0∞) : ∫⁻ a, f a ∂μ = ∑' a, f a * μ {a}
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.sum_smul_dirac`：sum_smul_dirac [Countable α] [Meas
urableSingletonClass α] (μ : Measure α) : (sum fun a => μ {a} • dirac a) = μ
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_countable' [Countable α] [MeasurableSingletonClass α] (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ = ∑' a, f a * μ {a} := by
  conv_lhs => rw [← sum_smul_dirac μ, lintegral_sum_measure]
  congr 1 with a : 1
  simp [mul_comm]
/-
**MeasureTheory.lintegral_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_singleton' {f : α -> Real>=0∞} (hf : Measurable f) (a : α) : ∫⁻ 
x in {a}, f x ∂μ = f a * μ {a}
参数：hf : Measurable f；a : α。
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
· 使用定理 `MeasureTheory.Measure.restrict_singleton`：restrict_singleton (μ : Measur
e α) (a : α) : μ.restrict {a} = μ {a} • dirac a
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_singleton' {f : α → ℝ≥0∞} (hf : Measurable f) (a : α) :
    ∫⁻ x in {a}, f x ∂μ = f a * μ {a} := by
  simp [lintegral_dirac' _ hf, mul_comm]
/-
**MeasureTheory.lintegral_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_singleton [MeasurableSingletonClass α] (f : α -> Real>=0∞) (a : 
α) : ∫⁻ x in {a}, f x ∂μ = f a * μ {a}
参数：f : α -> Real>=0∞；a : α。
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
· 使用定理 `MeasureTheory.Measure.restrict_singleton`：restrict_singleton (μ : Measur
e α) (a : α) : μ.restrict {a} = μ {a} • dirac a
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `MeasureTheory.lintegral_dirac`：lintegral_dirac [MeasurableSingletonClass
 α] (a : α) (f : α -> Real>=0∞) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_singleton [MeasurableSingletonClass α] (f : α → ℝ≥0∞) (a : α) :
    ∫⁻ x in {a}, f x ∂μ = f a * μ {a} := by
  simp [mul_comm]
/-
**MeasureTheory.lintegral_countable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_countable [MeasurableSingletonClass α] (f : α -> Real>=0∞) {s : 
Set α} (hs : s.Countable) : ∫⁻ a in s, f a ∂μ = ∑' a : s, f a * μ {(a : α)}
参数：f : α -> Real>=0∞；hs : s.Countable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `MeasureTheory.lintegral_biUnion`：lintegral_biUnion {t : Set β} {s : β ->
 Set α} (ht : t.Countable) (hm : forall i in t, MeasurableSet (s i)) (hd : t.Pai
rwiseDisjoint s) (f :…
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `Set.pairwiseDisjoint_fiber`：pairwiseDisjoint_fiber (f : ι -> α) (s : Set
 α) : s.PairwiseDisjoint fun a => f ⁻¹' {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_singleton`：lintegral_singleton [MeasurableSingle
tonClass α] (f : α -> Real>=0∞) (a : α) : ∫⁻ x in {a}, f x ∂μ = f a * μ {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_countable [MeasurableSingletonClass α] (f : α → ℝ≥0∞) {s : Set α}
    (hs : s.Countable) : ∫⁻ a in s, f a ∂μ = ∑' a : s, f a * μ {(a : α)} :=
  calc
    ∫⁻ a in s, f a ∂μ = ∫⁻ a in ⋃ x ∈ s, {x}, f a ∂μ := by rw [biUnion_of_singleton]
    _ = ∑' a : s, ∫⁻ x in {(a : α)}, f x ∂μ :=
      (lintegral_biUnion hs (fun _ _ => measurableSet_singleton _) (pairwiseDisjoint_fiber id s) _)
    _ = ∑' a : s, f a * μ {(a : α)} := by simp only [lintegral_singleton]
/-
**MeasureTheory.lintegral_insert** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_insert [MeasurableSingletonClass α] {a : α} {s : Set α} (h : a ∉
 s) (f : α -> Real>=0∞) : ∫⁻ x in insert a s, f x ∂μ = f a * μ {a} + ∫⁻ x in s, 
f x ∂μ
参数：h : a ∉ s；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `MeasureTheory.lintegral_union`：lintegral_union {f : α -> Real>=0∞} {A B 
: Set α} (hB : MeasurableSet B) (hAB : Disjoint A B) : ∫⁻ a in A union B, f a ∂μ
 = ∫⁻ a in A, f a ∂…
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用定理 `MeasureTheory.lintegral_singleton`：lintegral_singleton [MeasurableSingle
tonClass α] (f : α -> Real>=0∞) (a : α) : ∫⁻ x in {a}, f x ∂μ = f a * μ {a}
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem lintegral_insert [MeasurableSingletonClass α] {a : α} {s : Set α} (h : a ∉ s)
    (f : α → ℝ≥0∞) : ∫⁻ x in insert a s, f x ∂μ = f a * μ {a} + ∫⁻ x in s, f x ∂μ := by
  rw [← union_singleton, lintegral_union (measurableSet_singleton a), lintegral_singleton,
    add_comm]
  rwa [disjoint_singleton_right]
/-
**MeasureTheory.lintegral_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_finset [MeasurableSingletonClass α] (s : Finset α) (f : α -> Rea
l>=0∞) : ∫⁻ x in s, f x ∂μ = ∑ x in s, f x * μ {x}
参数：s : Finset α；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_countable`：lintegral_countable [MeasurableSingle
tonClass α] (f : α -> Real>=0∞) {s : Set α} (hs : s.Countable) : ∫⁻ a in s, f a 
∂μ = ∑' a : s, f a * μ …
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_finset [MeasurableSingletonClass α] (s : Finset α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x ∈ s, f x * μ {x} := by
  simp only [lintegral_countable _ s.countable_toSet, ← Finset.tsum_subtype']
/-
**MeasureTheory.lintegral_fintype** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_fintype [MeasurableSingletonClass α] [Fintype α] (f : α -> Real>
=0∞) : ∫⁻ x, f x ∂μ = ∑ x, f x * μ {x}
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_finset`：lintegral_finset [MeasurableSingletonCla
ss α] (s : Finset α) (f : α -> Real>=0∞) : ∫⁻ x in s, f x ∂μ = ∑ x in s, f x * μ
 {x}
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
theorem lintegral_fintype [MeasurableSingletonClass α] [Fintype α] (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∑ x, f x * μ {x} := by
  rw [← lintegral_finset, Finset.coe_univ, Measure.restrict_univ]
/-
**MeasureTheory.lintegral_unique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_unique [Unique α] (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ = f default
 * μ univ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_congr`：lintegral_congr {f g : α -> Real>=0∞} (h 
: forall a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
-/
theorem lintegral_unique [Unique α] (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ = f default * μ univ :=
  calc
    ∫⁻ x, f x ∂μ = ∫⁻ _, f default ∂μ := lintegral_congr <| Unique.forall_iff.2 rfl
    _ = f default * μ univ := lintegral_const _

end Countable

section SFinite

variable (μ) in
/-- If `μ` is an s-finite measure, then for any function `f`
there exists a measurable function `g ≤ f`
that has the same Lebesgue integral over every set.

For the integral over the whole space, the statement is true without extra assumptions,
see `exists_measurable_le_lintegral_eq`.
See also `MeasureTheory.Measure.restrict_toMeasurable_of_sFinite` for a similar result. -/
/-
**MeasureTheory.exists_measurable_le_forall_setLIntegral_eq** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：exists_measurable_le_forall_setLIntegral_eq [SFinite μ] (f : α -> Real>=0∞
) : exists g : α -> Real>=0∞, Measurable g ∧ g <= f ∧ forall s, ∫⁻ a in s, f a ∂
μ = ∫⁻ a in s, g a ∂μ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.exists_measurable_le_lintegral_eq`：exists_measurable_le_li
ntegral_eq (f : α -> Real>=0∞) : exists g : α -> Real>=0∞, Measurable g ∧ g <= f
 ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Measurable.iSup`：∀ {α : Type u_1} {δ : Type u_4} [inst : TopologicalSpac
e α] {mα : MeasurableSpace α} [BorelSpace α]   {mδ : MeasurableSpace δ} [inst_2 
: Con…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.lintegral_eq_nnreal`：lintegral_eq_nnreal {m : MeasurableSp
ace α} (f : α -> Real>=0∞) (μ : Measure α) : ∫⁻ a, f a ∂μ = ⨆ (φ : α ->ₛ Real>=0
) (_ : forall x, ↑(φ x)…
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Finset.bddAbove`：∀ {α : Type u} [inst : SemilatticeSup α] [Nonempty α] (
s : Finset α), BddAbove ↑s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.SimpleFunc.mem_range_self`：mem_range_self (f : α ->ₛ β) (x
 : α) : f x in f.range
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.IsFinit
eMeasure μ]   {f : α → ENNReal}, (∃ c, ∀ (x …
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
If `μ` is an s-finite measure, then for any function `f`
there exists a measurable function `g ≤ f`
that has the same Lebesgue integral over every set.

For the integral over the whole space, the statement is true without extra assum
ptions,
see `exists_measurable_le_lintegral_eq`.
See also `MeasureTheory.Measure.restrict_toMeasurable_of_sFinite` for a similar 
result.
-/
theorem exists_measurable_le_forall_setLIntegral_eq [SFinite μ] (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ ∀ s, ∫⁻ a in s, f a ∂μ = ∫⁻ a in s, g a ∂μ := by
  -- We only need to prove the `≤` inequality for the integrals, the other one follows from `g ≤ f`.
  rsuffices ⟨g, hgm, hgle, hleg⟩ :
      ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ ∀ s, ∫⁻ a in s, f a ∂μ ≤ ∫⁻ a in s, g a ∂μ
  · exact ⟨g, hgm, hgle, fun s ↦ (hleg s).antisymm (lintegral_mono hgle)⟩
  -- Without loss of generality, `μ` is a finite measure.
  wlog h : IsFiniteMeasure μ generalizing μ
  · choose g hgm hgle hgint using fun n ↦ @this (sfiniteSeq μ n) _ inferInstance
    refine ⟨fun x ↦ ⨆ n, g n x, .iSup hgm, fun x ↦ iSup_le (hgle · x), fun s ↦ ?_⟩
    rw [← sum_sfiniteSeq μ, Measure.restrict_sum_of_countable,
      lintegral_sum_measure, lintegral_sum_measure]
    exact ENNReal.tsum_le_tsum fun n ↦ (hgint n s).trans (lintegral_mono fun x ↦ le_iSup (g · x) _)
  -- According to `exists_measurable_le_lintegral_eq`, for any natural `n`
  -- we can choose a measurable function $g_{n}$
  -- such that $g_{n}(x) ≤ \min (f(x), n)$ for all $x$
  -- and both sides have the same integral over the whole space w.r.t. $μ$.
  have (n : ℕ) : ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ g ≤ n ∧
      ∫⁻ a, min (f a) n ∂μ = ∫⁻ a, g a ∂μ := by
    simpa [and_assoc] using exists_measurable_le_lintegral_eq μ (f ⊓ n)
  choose g hgm hgf hgle hgint using this
  -- Let `φ` be the pointwise supremum of the functions $g_{n}$.
  -- Clearly, `φ` is a measurable function and `φ ≤ f`.
  set φ : α → ℝ≥0∞ := fun x ↦ ⨆ n, g n x
  have hφm : Measurable φ := by fun_prop
  have hφle : φ ≤ f := fun x ↦ iSup_le (hgf · x)
  refine ⟨φ, hφm, hφle, fun s ↦ ?_⟩
  -- Now we show the inequality between set integrals.
  -- Choose a simple function `ψ ≤ f` with values in `ℝ≥0` and prove for `ψ`.
  rw [lintegral_eq_nnreal]
  refine iSup₂_le fun ψ hψ ↦ ?_
  -- Choose `n` such that `ψ x ≤ n` for all `x`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ x, ψ x ≤ n := by
    rcases ψ.range.bddAbove with ⟨C, hC⟩
    exact ⟨⌈C⌉₊, fun x ↦ (hC <| ψ.mem_range_self x).trans (Nat.le_ceil _)⟩
  calc
    (ψ.map (↑)).lintegral (μ.restrict s) = ∫⁻ a in s, ψ a ∂μ :=
      SimpleFunc.lintegral_eq_lintegral .. |>.symm
    _ ≤ ∫⁻ a in s, min (f a) n ∂μ :=
      lintegral_mono fun a ↦ le_min (hψ _) (ENNReal.coe_le_coe.2 (hn a))
    _ ≤ ∫⁻ a in s, g n a ∂μ := by
      have : ∫⁻ a in (toMeasurable μ s)ᶜ, min (f a) n ∂μ ≠ ∞ :=
        IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal _ ⟨n, fun _ ↦ min_le_right ..⟩ |>.ne
      have hsm : MeasurableSet (toMeasurable μ s) := measurableSet_toMeasurable ..
      apply ENNReal.le_of_add_le_add_right this
      rw [← μ.restrict_toMeasurable_of_sFinite, lintegral_add_compl _ hsm, hgint,
        ← lintegral_add_compl _ hsm]
      gcongr with x
      exact le_min (hgf n x) (hgle n x)
    _ ≤ _ := lintegral_mono fun x ↦ le_iSup (g · x) n

/-- In a sigma-finite measure space, there exists an integrable function which is
positive everywhere (and with an arbitrarily small integral). -/
/-
**MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：exists_pos_lintegral_lt_of_sigmaFinite (μ : Measure α) [SigmaFinite μ] {ε 
: Real>=0∞} (ε0 : ε != 0) : exists g : α -> Real>=0, (forall x, 0 < g x) ∧ Measu
rable g ∧ ∫⁻ x, g x ∂μ < ε
参数：μ : Measure α；ε0 : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `disjointed_subset`：disjointed_subset [Preorder ι] [LocallyFiniteOrderBot
 ι] (f : ι -> Set α) (i : ι) : disjointed f i subseteq f i
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `ENNReal.exists_pos_tsum_mul_lt_of_countable`：exists_pos_tsum_mul_lt_of_c
ountable {ε : Real>=0∞} (hε : ε != 0) {ι} [Countable ι] (w : ι -> Real>=0∞) (hw 
: forall i, w i != ∞) : exists δ …
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measurableSet_spanningSetsIndex`：measurableSet_spanningSet
sIndex (μ : Measure α) [SigmaFinite μ] : Measurable (spanningSetsIndex μ)
· 使用定理 `MeasureTheory.preimage_spanningSetsIndex_singleton`：preimage_spanningSet
sIndex_singleton (μ : Measure α) [SigmaFinite μ] (n : Nat) : spanningSetsIndex μ
 ⁻¹' {n} = disjointed (spanningSets μ) n
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_from_nat`：measurable_from_nat {f : Nat -> α} : Measurable f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `MeasureTheory.lintegral_comp`：lintegral_comp {f : β -> Real>=0∞} {g : α 
-> β} (hf : Measurable f) (hg : Measurable g) : lintegral μ (f ∘ g) = ∫⁻ a, f a 
∂map g μ
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_countable'`：lintegral_countable' [Countable α] [
MeasurableSingletonClass α] (f : α -> Real>=0∞) : ∫⁻ a, f a ∂μ = ∑' a, f a * μ {
a}
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
In a sigma-finite measure space, there exists an integrable function which is
positive everywhere (and with an arbitrarily small integral).
-/
theorem exists_pos_lintegral_lt_of_sigmaFinite (μ : Measure α) [SigmaFinite μ] {ε : ℝ≥0∞}
    (ε0 : ε ≠ 0) : ∃ g : α → ℝ≥0, (∀ x, 0 < g x) ∧ Measurable g ∧ ∫⁻ x, g x ∂μ < ε := by
  /- Let `s` be a covering of `α` by pairwise disjoint measurable sets of finite measure. Let
    `δ : ℕ → ℝ≥0` be a positive function such that `∑' i, μ (s i) * δ i < ε`. Then the function that
     is equal to `δ n` on `s n` is a positive function with integral less than `ε`. -/
  set s : ℕ → Set α := disjointed (spanningSets μ)
  have : ∀ n, μ (s n) < ∞ := fun n =>
    (measure_mono <| disjointed_subset _ _).trans_lt (measure_spanningSets_lt_top μ n)
  obtain ⟨δ, δpos, δsum⟩ : ∃ δ : ℕ → ℝ≥0, (∀ i, 0 < δ i) ∧ (∑' i, μ (s i) * δ i) < ε :=
    ENNReal.exists_pos_tsum_mul_lt_of_countable ε0 _ fun n => (this n).ne
  set N : α → ℕ := spanningSetsIndex μ
  have hN_meas : Measurable N := measurableSet_spanningSetsIndex μ
  have hNs : ∀ n, N ⁻¹' {n} = s n := preimage_spanningSetsIndex_singleton μ
  refine ⟨δ ∘ N, fun x => δpos _, measurable_from_nat.comp hN_meas, ?_⟩
  simp_rw [Function.comp_apply, ← Function.comp_apply (f := (fun n ↦ (↑(δ n) : ℝ≥0∞))),
    lintegral_comp measurable_from_nat.coe_nnreal_ennreal hN_meas]
  simpa [N, hNs, lintegral_countable', measurableSet_spanningSetsIndex, mul_comm] using δsum

omit [MeasurableSpace α]

variable {m m0 : MeasurableSpace α}

local infixr:25 " →ₛ " => SimpleFunc
/-
**MeasureTheory.univ_le_of_forall_fin_meas_le** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：univ_le_of_forall_fin_meas_le {μ : Measure α} (hm : m <= m0) [SigmaFinite 
(μ.trim hm)] (C : Real>=0∞) {f : Set α -> Real>=0∞} (hf : forall s, MeasurableSe
t[m] s -> μ s != ∞ -> f s <= C) (h_F_lim : forall S : Nat -> Set α, (forall n, M
easurableSet[m] (S n)) -> Monotone S -> f (⋃ n, S n) <= ⨆ n, f (S n)) : f univ <
= C
参数：hm : m <= m0；μ.trim hm；C : Real>=0∞；hf : forall s, MeasurableSet[m] s -> μ s 
!= ∞ -> f s <= C；h_F_lim : forall S : Nat -> Set α, (forall n, MeasurableSet[m] 
(S n)) -> Monotone S -> f (⋃ n, S n) <= ⨆ n, f (S n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.monotone_spanningSets`：monotone_spanningSets (μ : Measure 
α) [SigmaFinite μ] : Monotone (spanningSets μ)
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.le_trim`：le_trim (hm : m <= m0) : μ s <= μ.trim hm s
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
-/
theorem univ_le_of_forall_fin_meas_le {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) {f : Set α → ℝ≥0∞} (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → f s ≤ C)
    (h_F_lim :
      ∀ S : ℕ → Set α, (∀ n, MeasurableSet[m] (S n)) → Monotone S → f (⋃ n, S n) ≤ ⨆ n, f (S n)) :
    f univ ≤ C := by
  let S := @spanningSets _ m (μ.trim hm) _
  have hS_mono : Monotone S := @monotone_spanningSets _ m (μ.trim hm) _
  have hS_meas : ∀ n, MeasurableSet[m] (S n) := @measurableSet_spanningSets _ m (μ.trim hm) _
  rw [← @iUnion_spanningSets _ m (μ.trim hm)]
  refine (h_F_lim S hS_meas hS_mono).trans ?_
  refine iSup_le fun n => hf (S n) (hS_meas n) ?_
  exact ((le_trim hm).trans_lt (@measure_spanningSets_lt_top _ m (μ.trim hm) _ n)).ne

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. -/
/-
**MeasureTheory.lintegral_le_of_forall_fin_meas_trim_le** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：lintegral_le_of_forall_fin_meas_trim_le {μ : Measure α} (hm : m <= m0) [Si
gmaFinite (μ.trim hm)] (C : Real>=0∞) {f : α -> Real>=0∞} (hf : forall s, Measur
ableSet[m] s -> μ s != ∞ -> ∫⁻ x in s, f x ∂μ <= C) : ∫⁻ x, f x ∂μ <= C
参数：hm : m <= m0；μ.trim hm；C : Real>=0∞；hf : forall s, MeasurableSet[m] s -> μ s 
!= ∞ -> ∫⁻ x in s, f x ∂μ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.univ_le_of_forall_fin_meas_le`：univ_le_of_forall_fin_meas_
le {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)] (C : Real>=0∞) {f : 
Set α -> Real>=0∞} (hf : forall s…
· 使用定理 `MeasureTheory.setLIntegral_iUnion_of_directed`：setLIntegral_iUnion_of_di
rected {ι : Type*} [Countable ι] (f : α -> Real>=0∞) {s : ι -> Set α} (hd : Dire
cted (· subseteq ·) s) : ∫⁻ x in ⋃ …
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `directed_of_isDirected_le`：directed_of_isDirected_le [LE α] [IsDirectedO
rder α] {f : α -> β} {r : β -> β -> Prop} (H : forall ⦃i j⦄, i <= j -> r (f i) (
f j)) : Directe…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If the Lebesgue integral of a function is bounded by some constant on all sets w
ith finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, th
en the integral
over the whole space is bounded by that same constant.
-/
theorem lintegral_le_of_forall_fin_meas_trim_le {μ : Measure α} (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] (C : ℝ≥0∞) {f : α → ℝ≥0∞}
    (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C := by
  have : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by simp only [Measure.restrict_univ]
  rw [← this]
  refine univ_le_of_forall_fin_meas_le hm C hf fun S _ hS_mono => ?_
  rw [setLIntegral_iUnion_of_directed]
  exact directed_of_isDirected_le hS_mono

alias lintegral_le_of_forall_fin_meas_le_of_measurable := lintegral_le_of_forall_fin_meas_trim_le

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure and the measure is σ-finite, then the integral over the whole space is bounded by that same
constant. -/
/-
**MeasureTheory.lintegral_le_of_forall_fin_meas_le** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：lintegral_le_of_forall_fin_meas_le [MeasurableSpace α] {μ : Measure α} [Si
gmaFinite μ] (C : Real>=0∞) {f : α -> Real>=0∞} (hf : forall s, MeasurableSet s 
-> μ s != ∞ -> ∫⁻ x in s, f x ∂μ <= C) : ∫⁻ x, f x ∂μ <= C
参数：C : Real>=0∞；hf : forall s, MeasurableSet s -> μ s != ∞ -> ∫⁻ x in s, f x ∂μ 
<= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.trim_eq_self`：trim_eq_self [MeasurableSpace α] {μ : Measur
e α} : μ.trim le_rfl = μ
· 使用定理 `MeasureTheory.lintegral_le_of_forall_fin_meas_trim_le`：lintegral_le_of_f
orall_fin_meas_trim_le {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)] 
(C : Real>=0∞) {f : α -> Real>=0∞} (hf : fo…

--- 原说明 ---
If the Lebesgue integral of a function is bounded by some constant on all sets w
ith finite
measure and the measure is σ-finite, then the integral over the whole space is b
ounded by that same
constant.
-/
theorem lintegral_le_of_forall_fin_meas_le [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    (C : ℝ≥0∞) {f : α → ℝ≥0∞}
    (hf : ∀ s, MeasurableSet s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C :=
  have : SigmaFinite (μ.trim le_rfl) := by rwa [trim_eq_self]
  lintegral_le_of_forall_fin_meas_trim_le _ C hf
/-
**MeasureTheory.SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [Me
asureTheory.SigmaFinite μ]   {f : MeasureTheory.SimpleFunc α NNReal} {L : ENNRea
l},   L < ∫⁻ (x : α), ↑(f x) ∂μ → ∃ g, (∀ (x : α), g x ≤ f x) ∧ ∫⁻ (x : α), ↑(g 
x) ∂μ < ⊤ ∧ L < ∫⁻ (x : α), ↑(g x) ∂μ
参数：x : α；f x；∀ (x : α), g x ≤ f x；x : α；g x；x : α；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ENNReal.not_lt_zero`：not_lt_zero : ¬a < 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
· 使用定理 `ENNReal.coe_indicator`：coe_indicator {α} (s : Set α) (f : α -> Real>=0) 
(a : α) : ((s.indicator f a : Real>=0) : Real>=0∞) = s.indicator (fun x => ↑(f x
)) a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `ENNReal.div_lt_iff`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ c ≠ ⊤ →
 (c / b < a ↔ c < a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.Measure.exists_subset_measure_lt_top`：exists_subset_measur
e_lt_top [SigmaFinite μ] {r : Real>=0∞} (hs : MeasurableSet s) (h's : r < μ s) :
 exists t, MeasurableSet t ∧ t subseteq …
· 使用定理 `Set.indicator_le_indicator_of_subset`：∀ {α : Type u_2} {M : Type u_3} [i
nst : Preorder M] [inst_1 : Zero M] {s t : Set α} {f : α → M},   s ⊆ t → 0 ≤ f →
 s.indicator f ≤ t.indicat…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
（共 48 条，此处仅展示前 30 条）
-/
theorem SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α}
    {μ : Measure α} [SigmaFinite μ] {f : α →ₛ ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  induction f using MeasureTheory.SimpleFunc.induction generalizing L with
  | @const c s hs =>
    simp only [hs, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
      piecewise_eq_indicator, lintegral_indicator, lintegral_const, Measure.restrict_apply',
      ENNReal.coe_indicator, Function.const_apply] at hL
    have c_ne_zero : c ≠ 0 := by
      intro hc
      simp only [hc, ENNReal.coe_zero, zero_mul, not_lt_zero] at hL
    have : L / c < μ s := by
      rwa [ENNReal.div_lt_iff, mul_comm]
      · simp only [c_ne_zero, Ne, ENNReal.coe_eq_zero, not_false_iff, true_or]
      · simp only [Ne, coe_ne_top, not_false_iff, true_or]
    obtain ⟨t, ht, ts, mlt, t_top⟩ :
      ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ L / ↑c < μ t ∧ μ t < ∞ :=
      Measure.exists_subset_measure_lt_top hs this
    refine ⟨piecewise t ht (const α c) (const α 0), fun x => ?_, ?_, ?_⟩
    · refine indicator_le_indicator_of_subset ts (fun x => ?_) x
      exact zero_le
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', ENNReal.mul_lt_top ENNReal.coe_lt_top t_top]
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', univ_inter]
      rwa [mul_comm, ← ENNReal.div_lt_iff]
      · simp only [c_ne_zero, Ne, ENNReal.coe_eq_zero, not_false_iff, true_or]
      · simp only [Ne, coe_ne_top, not_false_iff, true_or]
  | @add f₁ f₂ _ h₁ h₂ =>
    replace hL : L < ∫⁻ x, f₁ x ∂μ + ∫⁻ x, f₂ x ∂μ := by
      rwa [← lintegral_add_left f₁.measurable.coe_nnreal_ennreal]
    by_cases hf₁ : ∫⁻ x, f₁ x ∂μ = 0
    · simp only [hf₁, zero_add] at hL
      rcases h₂ hL with ⟨g, g_le, g_top, gL⟩
      refine ⟨g, fun x => (g_le x).trans ?_, g_top, gL⟩
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_left, zero_le]
    by_cases hf₂ : ∫⁻ x, f₂ x ∂μ = 0
    · simp only [hf₂, add_zero] at hL
      rcases h₁ hL with ⟨g, g_le, g_top, gL⟩
      refine ⟨g, fun x => (g_le x).trans ?_, g_top, gL⟩
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_right, zero_le]
    obtain ⟨L₁, hL₁, L₂, hL₂, hL⟩ : ∃ L₁ < ∫⁻ x, f₁ x ∂μ, ∃ L₂ < ∫⁻ x, f₂ x ∂μ, L < L₁ + L₂ :=
      ENNReal.exists_lt_add_of_lt_add hL hf₁ hf₂
    rcases h₁ hL₁ with ⟨g₁, g₁_le, g₁_top, hg₁⟩
    rcases h₂ hL₂ with ⟨g₂, g₂_le, g₂_top, hg₂⟩
    refine ⟨g₁ + g₂, fun x => add_le_add (g₁_le x) (g₂_le x), ?_, ?_⟩
    · apply lt_of_le_of_lt _ (add_lt_top.2 ⟨g₁_top, g₂_top⟩)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      exact le_rfl
    · apply hL.trans ((ENNReal.add_lt_add hg₁ hg₂).trans_le _)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      simp only [coe_add, Pi.add_apply, ENNReal.coe_add, le_rfl]
/-
**MeasureTheory.exists_lt_lintegral_simpleFunc_of_lt_lintegral** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α} {μ 
: Measure α} [SigmaFinite μ] {f : α -> Real>=0} {L : Real>=0∞} (hL : L < ∫⁻ x, f
 x ∂μ) : exists g : α ->ₛ Real>=0, (forall x, g x <= f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L
 < ∫⁻ x, g x ∂μ
参数：hL : L < ∫⁻ x, f x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_eq_nnreal`：lintegral_eq_nnreal {m : MeasurableSp
ace α} (f : α -> Real>=0∞) (μ : Measure α) : ∫⁻ a, f a ∂μ = ⨆ (φ : α ->ₛ Real>=0
) (_ : forall x, ↑(φ x)…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
· 使用定理 `MeasureTheory.SimpleFunc.coe_map`：coe_map (g : β -> γ) (f : α ->ₛ β) : (
f.map g : α -> γ) = g ∘ f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral`
：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [Measure
Theory.SigmaFinite μ]   {f : MeasureTheory.SimpleFunc α NNRea…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
-/
theorem exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α} {μ : Measure α}
    [SigmaFinite μ] {f : α → ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  simp_rw [lintegral_eq_nnreal, lt_iSup_iff] at hL
  rcases hL with ⟨g₀, hg₀, g₀L⟩
  have h'L : L < ∫⁻ x, g₀ x ∂μ := by
    convert! g₀L
    rw [← SimpleFunc.lintegral_eq_lintegral, SimpleFunc.coe_map]
    simp only [Function.comp_apply]
  rcases SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral h'L with ⟨g, hg, gL, gtop⟩
  exact ⟨g, fun x => (hg x).trans (ENNReal.coe_le_coe.1 (hg₀ x)), gL, gtop⟩

end SFinite

end MeasureTheory

