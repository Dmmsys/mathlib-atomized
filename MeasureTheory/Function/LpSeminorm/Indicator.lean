/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# ℒp seminorms and indicator functions
-/

public section
noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology ComplexConjugate

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lp

variable {f : α → F}

section Indicator

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {c : ε} {hf : AEStronglyMeasurable f μ} {s : Set α}
  {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε']

/-
**MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：eLpNorm_indicator_eq_eLpNorm_restrict {f : α -> ε} {s : Set α} (hs : Measu
rableSet s) : eLpNorm (s.indicator f) p μ = eLpNorm f p (μ.restrict s)
参数：hs : MeasurableSet s。
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
· 使用引理 `enorm_indicator_eq_indicator_enorm`：enorm_indicator_eq_indicator_enorm :
 ‖indicator s f a‖ₑ = indicator s (fun a => ‖f a‖ₑ) a
· 使用定理 `ENNReal.essSup_indicator_eq_essSup_restrict`：essSup_indicator_eq_essSup_
restrict {s : Set α} {f : α -> Real>=0∞} (hs : MeasurableSet s) : essSup (s.indi
cator f) μ = essSup f (μ.restrict…
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Set.indicator_comp_of_zero`：∀ {α : Type u_1} {M : Type u_3} {N : Type u_
4} [inst : Zero M] [inst_1 : Zero N] {s : Set α} {f : α → M} {g : M → N},   g 0 
= 0 → s.indicato…
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
-/
lemma eLpNorm_indicator_eq_eLpNorm_restrict {f : α → ε} {s : Set α} (hs : MeasurableSet s) :
    eLpNorm (s.indicator f) p μ = eLpNorm f p (μ.restrict s) := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm,
       enorm_indicator_eq_indicator_enorm, ENNReal.essSup_indicator_eq_essSup_restrict hs]
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_top]
  rw [← lintegral_indicator hs]
  congr
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [eq_comm, ← Function.comp_def (fun x : ℝ≥0∞ => x ^ p.toReal), Set.indicator_comp_of_zero,
    Function.comp_def]
  simp [ENNReal.toReal_pos hp_zero hp_top]
/-
**MeasureTheory.eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict** 是 Mathlib 中的
一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict (hs : MeasurableSet s) :
 eLpNormEssSup (s.indicator f) μ = eLpNormEssSup f (μ.restrict s)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`：eLpNorm_indicator_e
q_eLpNorm_restrict {f : α -> ε} {s : Set α} (hs : MeasurableSet s) : eLpNorm (s.
indicator f) p μ = eLpNorm f p (μ.restric…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict (hs : MeasurableSet s) :
    eLpNormEssSup (s.indicator f) μ = eLpNormEssSup f (μ.restrict s) := by
  simp_rw [← eLpNorm_exponent_top, eLpNorm_indicator_eq_eLpNorm_restrict hs]
/-
**MeasureTheory.eLpNorm_restrict_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_restrict_le (f : α -> ε') (p : Real>=0∞) (μ : Measure α) (s : Set 
α) : eLpNorm f p (μ.restrict s) <= eLpNorm f p μ
参数：f : α -> ε'；p : Real>=0∞；μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_mono_measure`：eLpNorm_mono_measure (f : α -> ε) (h
μν : ν <= μ) : eLpNorm f p ν <= eLpNorm f p μ
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
lemma eLpNorm_restrict_le (f : α → ε') (p : ℝ≥0∞) (μ : Measure α) (s : Set α) :
    eLpNorm f p (μ.restrict s) ≤ eLpNorm f p μ :=
  eLpNorm_mono_measure f Measure.restrict_le_self
/-
**MeasureTheory.eLpNorm_indicator_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_indicator_le (f : α -> ε) : eLpNorm (s.indicator f) p μ <= eLpNorm
 f p μ
参数：f : α -> ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_mono_enorm`：eLpNorm_mono_enorm {f : α -> ε} {g : α
 -> ε'} (h : forall x, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `enorm_indicator_eq_indicator_enorm`：enorm_indicator_eq_indicator_enorm :
 ‖indicator s f a‖ₑ = indicator s (fun a => ‖f a‖ₑ) a
· 使用定理 `Set.indicator_le_self`：∀ {α : Type u_2} {M : Type u_3} [inst : AddMonoid
 M] [inst_1 : PartialOrder M] [CanonicallyOrderedAdd M] (s : Set α)   (f : α → M
), s.indica…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma eLpNorm_indicator_le (f : α → ε) :
    eLpNorm (s.indicator f) p μ ≤ eLpNorm f p μ := by
  apply eLpNorm_mono_enorm
  simp_rw [enorm_indicator_eq_indicator_enorm]
  exact s.indicator_le_self _
/-
**MeasureTheory.eLpNormEssSup_indicator_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：eLpNormEssSup_indicator_le (s : Set α) (f : α -> ε) : eLpNormEssSup (s.ind
icator f) μ <= eLpNormEssSup f μ
参数：s : Set α；f : α -> ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `essSup_mono_ae`：essSup_mono_ae {f g : α -> β} (hfg : f <=ᵐ[μ] g) (hf : I
sCoboundedUnder (· <= ·) (ae μ) f
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `enorm_indicator_eq_indicator_enorm`：enorm_indicator_eq_indicator_enorm :
 ‖indicator s f a‖ₑ = indicator s (fun a => ‖f a‖ₑ) a
· 使用定理 `Set.indicator_le_self`：∀ {α : Type u_2} {M : Type u_3} [inst : AddMonoid
 M] [inst_1 : PartialOrder M] [CanonicallyOrderedAdd M] (s : Set α)   (f : α → M
), s.indica…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
-/
lemma eLpNormEssSup_indicator_le (s : Set α) (f : α → ε) :
    eLpNormEssSup (s.indicator f) μ ≤ eLpNormEssSup f μ := by
  refine essSup_mono_ae (.of_forall fun x => ?_)
  simp_rw [enorm_indicator_eq_indicator_enorm]
  exact Set.indicator_le_self s _ x
/-
**MeasureTheory.eLpNormEssSup_indicator_const_le** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：eLpNormEssSup_indicator_const_le (s : Set α) (c : ε) : eLpNormEssSup (s.in
dicator fun _ : α => c) μ <= ‖c‖ₑ
参数：s : Set α；c : ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNormEssSup_measure_zero`：eLpNormEssSup_measure_zero {f 
: α -> ε} : eLpNormEssSup f (0 : Measure α) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.eLpNormEssSup_indicator_le`：eLpNormEssSup_indicator_le (s 
: Set α) (f : α -> ε) : eLpNormEssSup (s.indicator f) μ <= eLpNormEssSup f μ
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.eLpNormEssSup_const`：eLpNormEssSup_const (c : ε) (hμ : μ !
= 0) : eLpNormEssSup (fun _ : α => c) μ = ‖c‖ₑ
-/
lemma eLpNormEssSup_indicator_const_le (s : Set α) (c : ε) :
    eLpNormEssSup (s.indicator fun _ : α => c) μ ≤ ‖c‖ₑ := by
  obtain rfl | hμ0 := eq_or_ne μ 0
  · simp
  · exact (eLpNormEssSup_indicator_le s fun _ => c).trans (eLpNormEssSup_const c hμ0).le
/-
**MeasureTheory.eLpNormEssSup_indicator_const_eq** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：eLpNormEssSup_indicator_const_eq (s : Set α) (c : ε) (hμs : μ s != 0) : eL
pNormEssSup (s.indicator fun _ : α => c) μ = ‖c‖ₑ
参数：s : Set α；c : ε；hμs : μ s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `MeasureTheory.eLpNormEssSup_indicator_const_le`：eLpNormEssSup_indicator_
const_le (s : Set α) (c : ε) : eLpNormEssSup (s.indicator fun _ : α => c) μ <= ‖
c‖ₑ
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `ae_lt_of_essSup_lt`：ae_lt_of_essSup_lt (hx : essSup f μ < x) (hf : IsBou
ndedUnder (· <= ·) (ae μ) f
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma eLpNormEssSup_indicator_const_eq (s : Set α) (c : ε) (hμs : μ s ≠ 0) :
    eLpNormEssSup (s.indicator fun _ : α => c) μ = ‖c‖ₑ := by
  refine le_antisymm (eLpNormEssSup_indicator_const_le s c) ?_
  by_contra! h
  have h' := ae_iff.mp (ae_lt_of_essSup_lt h)
  push Not at h'
  refine hμs (measure_mono_null (fun x hx_mem => ?_) h')
  rw [Set.mem_ofPred_eq, Set.indicator_of_mem hx_mem]
/-
**MeasureTheory.eLpNorm_indicator_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：eLpNorm_indicator_const (hs : MeasurableSet s) (hp : p != 0) (hp_top : p !
= ∞) : eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal)
参数：hs : MeasurableSet s；hp : p != 0；hp_top : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eLpNorm_indicator_const₀`：eLpNorm_indicator_const₀ (hs : N
ullMeasurableSet s μ) (hp : p != 0) (hp_top : p != ∞) : eLpNorm (s.indicator fun
 _ => c) p μ = ‖c‖ₑ * μ s ^ …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
lemma eLpNorm_indicator_const₀ (hs : NullMeasurableSet s μ) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) :=
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  calc
    eLpNorm (s.indicator fun _ => c) p μ
      = (∫⁻ x, (‖(s.indicator fun _ ↦ c) x‖ₑ ^ p.toReal) ∂μ) ^ (1 / p.toReal) :=
          eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp_top
    _ = (∫⁻ x, (s.indicator fun _ ↦ ‖c‖ₑ ^ p.toReal) x ∂μ) ^ (1 / p.toReal) := by
      congr 2
      refine (Set.comp_indicator_const c (fun x ↦ (‖x‖ₑ) ^ p.toReal) ?_)
      simp [hp_pos]
    _ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
      rw [lintegral_indicator_const₀ hs, ENNReal.mul_rpow_of_nonneg, ← ENNReal.rpow_mul,
        mul_one_div_cancel hp_pos.ne', ENNReal.rpow_one]
      positivity
/-
**MeasureTheory.eLpNorm_indicator_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：eLpNorm_indicator_const (hs : MeasurableSet s) (hp : p != 0) (hp_top : p !
= ∞) : eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal)
参数：hs : MeasurableSet s；hp : p != 0；hp_top : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eLpNorm_indicator_const₀`：eLpNorm_indicator_const₀ (hs : N
ullMeasurableSet s μ) (hp : p != 0) (hp_top : p != ∞) : eLpNorm (s.indicator fun
 _ => c) p μ = ‖c‖ₑ * μ s ^ …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
lemma eLpNorm_indicator_const (hs : MeasurableSet s) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) :=
  eLpNorm_indicator_const₀ hs.nullMeasurableSet hp hp_top
/-
**MeasureTheory.eLpNorm_indicator_const'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：eLpNorm_indicator_const' (hs : MeasurableSet s) (hμs : μ s != 0) (hp : p !
= 0) : eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal)
参数：hs : MeasurableSet s；hμs : μ s != 0；hp : p != 0。
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
· 使用引理 `MeasureTheory.eLpNormEssSup_indicator_const_eq`：eLpNormEssSup_indicator_
const_eq (s : Set α) (c : ε) (hμs : μ s != 0) : eLpNormEssSup (s.indicator fun _
 : α => c) μ = ‖c‖ₑ
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.eLpNorm_indicator_const`：eLpNorm_indicator_const (hs : Mea
surableSet s) (hp : p != 0) (hp_top : p != ∞) : eLpNorm (s.indicator fun _ => c)
 p μ = ‖c‖ₑ * μ s ^ (1 / p.…
-/
lemma eLpNorm_indicator_const' (hs : MeasurableSet s) (hμs : μ s ≠ 0) (hp : p ≠ 0) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_indicator_const_eq s c hμs]
  · exact eLpNorm_indicator_const hs hp hp_top

variable (c) in
/-
**MeasureTheory.eLpNorm_indicator_const_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：eLpNorm_indicator_const_le (p : Real>=0∞) : eLpNorm (s.indicator fun _ => 
c) p μ <= ‖c‖ₑ * μ s ^ (1 / p.toReal)
参数：p : Real>=0∞。
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
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用引理 `MeasureTheory.eLpNormEssSup_indicator_const_le`：eLpNormEssSup_indicator_
const_le (s : Set α) (c : ε) : eLpNormEssSup (s.indicator fun _ : α => c) μ <= ‖
c‖ₑ
· 使用定理 `MeasureTheory.eLpNorm_mono_enorm`：eLpNorm_mono_enorm {f : α -> ε} {g : α
 -> ε'} (h : forall x, ‖f x‖ₑ <= ‖g x‖ₑ) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `enorm_indicator_le_of_subset`：enorm_indicator_le_of_subset (h : s subset
eq t) (f : α -> ε) (a : α) : ‖indicator s f a‖ₑ <= ‖indicator t f a‖ₑ
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用引理 `MeasureTheory.eLpNorm_indicator_const`：eLpNorm_indicator_const (hs : Mea
surableSet s) (hp : p != 0) (hp_top : p != ∞) : eLpNorm (s.indicator fun _ => c)
 p μ = ‖c‖ₑ * μ s ^ (1 / p.…
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
-/
lemma eLpNorm_indicator_const_le (p : ℝ≥0∞) :
    eLpNorm (s.indicator fun _ => c) p μ ≤ ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain rfl | h'p := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top, ENNReal.toReal_top, _root_.div_zero, ENNReal.rpow_zero,
      mul_one]
    exact eLpNormEssSup_indicator_const_le _ _
  let t := toMeasurable μ s
  calc
    eLpNorm (s.indicator fun _ => c) p μ ≤ eLpNorm (t.indicator fun _ ↦ c) p μ :=
      eLpNorm_mono_enorm (enorm_indicator_le_of_subset (subset_toMeasurable _ _) _)
    _ = ‖c‖ₑ * μ t ^ (1 / p.toReal) :=
      eLpNorm_indicator_const (measurableSet_toMeasurable ..) hp h'p
    _ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by rw [measure_toMeasurable]
/-
**MeasureTheory.MemLp.indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ESeminormedAd
dMonoid ε] {s : Set α} {f : α → ε},   MeasurableSet s → MeasureTheory.MemLp f p 
μ → MeasureTheory.MemLp (s.indicator f) p μ
参数：s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 : Z…
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `MeasureTheory.eLpNorm_indicator_le`：eLpNorm_indicator_le (f : α -> ε) : 
eLpNorm (s.indicator f) p μ <= eLpNorm f p μ
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
lemma MemLp.indicator {f : α → ε} (hs : MeasurableSet s) (hf : MemLp f p μ) :
    MemLp (s.indicator f) p μ :=
  ⟨hf.aestronglyMeasurable.indicator hs, lt_of_le_of_lt (eLpNorm_indicator_le f) (by finiteness)⟩
/-
**MeasureTheory.memLp_indicator_iff_restrict** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：memLp_indicator_iff_restrict {f : α -> ε} (hs : MeasurableSet s) : MemLp (
s.indicator f) p μ ↔ MemLp f p (μ.restrict s)
参数：hs : MeasurableSet s。
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
· 使用定理 `aestronglyMeasurable_indicator_iff`：∀ {α : Type u_1} {β : Type u_2} [ins
t : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}  
 {f : α → β} [inst_1 : Z…
· 使用引理 `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`：eLpNorm_indicator_e
q_eLpNorm_restrict {f : α -> ε} {s : Set α} (hs : MeasurableSet s) : eLpNorm (s.
indicator f) p μ = eLpNorm f p (μ.restric…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma memLp_indicator_iff_restrict {f : α → ε} (hs : MeasurableSet s) :
    MemLp (s.indicator f) p μ ↔ MemLp f p (μ.restrict s) := by
  simp [MemLp, aestronglyMeasurable_indicator_iff hs, eLpNorm_indicator_eq_eLpNorm_restrict hs]
/-
**MeasureTheory.memLp_indicator_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：memLp_indicator_const (p : Real>=0∞) (hs : MeasurableSet s) (c : E) (hμsc 
: c = 0 ∨ μ s != ∞) : MemLp (s.indicator fun _ => c) p μ
参数：p : Real>=0∞；hs : MeasurableSet s；c : E；hμsc : c = 0 ∨ μ s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.memLp_indicator_iff_restrict`：memLp_indicator_iff_restrict
 {f : α -> ε} (hs : MeasurableSet s) : MemLp (s.indicator f) p μ ↔ MemLp f p (μ.
restrict s)
· 使用定理 `MeasureTheory.MemLp.zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p :
 ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpac
e ε] [inst_1 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
-/
lemma memLp_indicator_const (p : ℝ≥0∞) (hs : MeasurableSet s) (c : E) (hμsc : c = 0 ∨ μ s ≠ ∞) :
    MemLp (s.indicator fun _ => c) p μ := by
  rw [memLp_indicator_iff_restrict hs]
  obtain rfl | hμ := hμsc
  · exact MemLp.zero
  · have := Fact.mk hμ.lt_top
    apply memLp_const
/-
**MeasureTheory.eLpNormEssSup_piecewise** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：eLpNormEssSup_piecewise (f g : α -> ε) [DecidablePred (· in s)] (hs : Meas
urableSet s) : eLpNormEssSup (Set.piecewise s f g) μ = max (eLpNormEssSup f (μ.r
estrict s)) (eLpNormEssSup g (μ.restrict sᶜ))
参数：f g : α -> ε；· in s；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.essSup_piecewise`：essSup_piecewise {s : Set α} [DecidablePred (·
 in s)] {g} (hs : MeasurableSet s) : essSup (s.piecewise f g) μ = max (essSup f 
(μ.restrict s)…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma eLpNormEssSup_piecewise (f g : α → ε) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    eLpNormEssSup (Set.piecewise s f g) μ
      = max (eLpNormEssSup f (μ.restrict s)) (eLpNormEssSup g (μ.restrict sᶜ)) := by
  simp only [eLpNormEssSup, ← ENNReal.essSup_piecewise hs]
  congr with x
  by_cases hx : x ∈ s <;> simp [hx]
/-
**MeasureTheory.eLpNorm_top_piecewise** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_top_piecewise (f g : α -> ε) [DecidablePred (· in s)] (hs : Measur
ableSet s) : eLpNorm (Set.piecewise s f g) ∞ μ = max (eLpNorm f ∞ (μ.restrict s)
) (eLpNorm g ∞ (μ.restrict sᶜ))
参数：f g : α -> ε；· in s；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eLpNormEssSup_piecewise`：eLpNormEssSup_piecewise (f g : α 
-> ε) [DecidablePred (· in s)] (hs : MeasurableSet s) : eLpNormEssSup (Set.piece
wise s f g) μ = max (eLpNor…
-/
lemma eLpNorm_top_piecewise (f g : α → ε) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    eLpNorm (Set.piecewise s f g) ∞ μ
      = max (eLpNorm f ∞ (μ.restrict s)) (eLpNorm g ∞ (μ.restrict sᶜ)) :=
  eLpNormEssSup_piecewise f g hs
/-
**MeasureTheory.MemLp.piecewise** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {ε : Type u_7}   [inst : TopologicalSpace ε] [inst_1 : ESeminormedAd
dMonoid ε] {s : Set α} {f : α → ε}   [inst_2 : DecidablePred fun x => x ∈ s] {g 
: α → ε},   MeasurableSet s →     MeasureTheory.MemLp f p (μ.restrict s) →      
 MeasureTheory.MemLp g p (μ.restrict sᶜ) → MeasureTheory.MemLp (s.piecewise f g)
 p μ
参数：μ.restrict s；μ.restrict sᶜ；s.piecewise f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEStronglyMeasurable.piecewise`：piecewise {s : Set α} [Dec
idablePred (· in s)] (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (μ.rest
rict s)) (hg : AEStronglyMeasurabl…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `MeasureTheory.eLpNorm_top_piecewise`：eLpNorm_top_piecewise (f g : α -> ε
) [DecidablePred (· in s)] (hs : MeasurableSet s) : eLpNorm (Set.piecewise s f g
) ∞ μ = max (eLpNorm f ∞ …
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`：eLpNorm_lt
_top_iff_lintegral_rpow_enorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_t
op : p != ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) …
· 使用定理 `MeasureTheory.lintegral_add_compl`：lintegral_add_compl (f : α -> Real>=0
∞) {A : Set α} (hA : MeasurableSet A) : ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ =
 ∫⁻ x, f x ∂μ
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top`：lintegral_r
pow_enorm_lt_top_of_eLpNorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_top
 : p != ∞) (hfp : eLpNorm f p μ < ∞) : ∫⁻ a, ‖f a…
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
protected lemma MemLp.piecewise {f : α → ε} [DecidablePred (· ∈ s)] {g} (hs : MeasurableSet s)
    (hf : MemLp f p (μ.restrict s)) (hg : MemLp g p (μ.restrict sᶜ)) :
    MemLp (s.piecewise f g) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, memLp_zero_iff_aestronglyMeasurable]
    exact AEStronglyMeasurable.piecewise hs hf.1 hg.1
  refine ⟨AEStronglyMeasurable.piecewise hs hf.1 hg.1, ?_⟩
  obtain rfl | hp_top := eq_or_ne p ∞
  · rw [eLpNorm_top_piecewise f g hs]
    exact max_lt hf.2 hg.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_zero hp_top, ← lintegral_add_compl _ hs,
    ENNReal.add_lt_top]
  constructor
  · have h (x) (hx : x ∈ s) : ‖Set.piecewise s f g x‖ₑ ^ p.toReal = ‖f x‖ₑ ^ p.toReal := by
      simp [hx]
    rw [setLIntegral_congr_fun hs h]
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_top hf.2
  · have h (x) (hx : x ∈ sᶜ) : ‖Set.piecewise s f g x‖ₑ ^ p.toReal = ‖g x‖ₑ ^ p.toReal := by
      have hx' : x ∉ s := hx
      simp [hx']
    rw [setLIntegral_congr_fun hs.compl h]
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_top hg.2
/-
**MeasureTheory.eLpNorm_indicator_sub_le_of_dist_bdd** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：eLpNorm_indicator_sub_le_of_dist_bdd {β : Type*} [NormedAddCommGroup β] (μ
 : Measure α
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
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.eLpNorm_mono`：eLpNorm_mono {f : α -> F} {g : α -> G} (h : 
forall x, ‖f x‖ <= ‖g x‖) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `MeasureTheory.eLpNorm_indicator_const`：eLpNorm_indicator_const (hs : Mea
surableSet s) (hp : p != 0) (hp_top : p != ∞) : eLpNorm (s.indicator fun _ => c)
 p μ = ‖c‖ₑ * μ s ^ (1 / p.…
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
-/
theorem eLpNorm_indicator_sub_le_of_dist_bdd {β : Type*} [NormedAddCommGroup β]
    (μ : Measure α := by volume_tac) (hp' : p ≠ ∞) (hs : MeasurableSet s)
    {f g : α → β} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ x ∈ s, dist (f x) (g x) ≤ c) :
    eLpNorm (s.indicator (f - g)) p μ ≤ ENNReal.ofReal c * μ s ^ (1 / p.toReal) := by
  by_cases hp : p = 0
  · simp [hp]
  have : ∀ x, ‖s.indicator (f - g) x‖ ≤ ‖s.indicator (fun _ => c) x‖ := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.sub_apply, ← dist_eq_norm,
        Real.norm_eq_abs, abs_of_nonneg hc]
      exact hf x hx
    · simp [Set.indicator_of_notMem hx]
  grw [eLpNorm_mono this, eLpNorm_indicator_const hs hp hp', ← ofReal_norm,
    Real.norm_eq_abs, abs_of_nonneg hc]
/-
**MeasureTheory.eLpNorm_sub_le_of_dist_bdd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：eLpNorm_sub_le_of_dist_bdd {β : Type*} [NormedAddCommGroup β] (μ : Measure
 α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_eq_self`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {
s : Set α} {f : α → M}, s.indicator f = f ↔ Function.support f ⊆ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Function.support_sub`：∀ {α : Type u_1} {G : Type u_3} [inst : Subtractio
nMonoid G] (f g : α → G),   (Function.support fun x => f x - g x) ⊆ Function.sup
port f ∪ F…
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_indicator_sub_le_of_dist_bdd`：eLpNorm_indicator_su
b_le_of_dist_bdd {β : Type*} [NormedAddCommGroup β] (μ : Measure α
-/
theorem eLpNorm_sub_le_of_dist_bdd {β : Type*} [NormedAddCommGroup β]
    (μ : Measure α := by volume_tac) (hp : p ≠ ⊤) (hs : MeasurableSet s) {c : ℝ} (hc : 0 ≤ c)
    {f g : α → β} (h : ∀ x, dist (f x) (g x) ≤ c) (hs₁ : f.support ⊆ s) (hs₂ : g.support ⊆ s) :
    eLpNorm (f - g) p μ ≤ ENNReal.ofReal c * μ s ^ (1 / p.toReal) := by
  have hs₃ : s.indicator (f - g) = f - g := by
    rw [Set.indicator_eq_self]
    exact (Function.support_sub _ _).trans (Set.union_subset hs₁ hs₂)
  rw [← hs₃]
  exact eLpNorm_indicator_sub_le_of_dist_bdd μ hp hs hc (fun x _ ↦ h x)

end Indicator

section UnifTight

/-- A single function that is `MemLp f p μ` is tight with respect to `μ`. -/
/-
**MeasureTheory.MemLp.exists_eLpNorm_indicator_compl_lt** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory
.Measure α} {β : Type u_7}   [inst : NormedAddCommGroup β],   p ≠ ⊤ →     ∀ {f :
 α → β},       MeasureTheory.MemLp f p μ →         ∀ {ε : ENNReal}, ε ≠ 0 → ∃ s,
 MeasurableSet s ∧ μ s < ⊤ ∧ MeasureTheory.eLpNorm (sᶜ.indicator f) p μ < ε
参数：sᶜ.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `Set.indicator_univ`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f :
 α → M), Set.univ.indicator f = f
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.exists_setLIntegral_compl_lt`：exists_setLIntegral_compl_lt
 {f : α -> Real>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞) {ε : Real>=0∞} (hε : ε != 0) : exi
sts s : Set α, MeasurableSet s ∧…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`：eLpNorm_lt
_top_iff_lintegral_rpow_enorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_t
op : p != ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`：eLpNorm_indicator_e
q_eLpNorm_restrict {f : α -> ε} {s : Set α} (hs : MeasurableSet s) : eLpNorm (s.
indicator f) p μ = eLpNorm f p (μ.restric…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A single function that is `MemLp f p μ` is tight with respect to `μ`.
-/
theorem MemLp.exists_eLpNorm_indicator_compl_lt {β : Type*} [NormedAddCommGroup β] (hp_top : p ≠ ∞)
    {f : α → β} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : Set α, MeasurableSet s ∧ μ s < ∞ ∧ eLpNorm (sᶜ.indicator f) p μ < ε := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · use ∅; simp [pos_iff_ne_zero.2 hε] -- first take care of `p = 0`
  · obtain ⟨s, hsm, hs, hε⟩ :
        ∃ s, MeasurableSet s ∧ μ s < ∞ ∧ ∫⁻ a in sᶜ, (‖f a‖ₑ) ^ p.toReal ∂μ < ε ^ p.toReal := by
      apply exists_setLIntegral_compl_lt
      · exact ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp_top).1 hf.2).ne
      · simp [*]
    refine ⟨s, hsm, hs, ?_⟩
    rwa [eLpNorm_indicator_eq_eLpNorm_restrict hsm.compl,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top, one_div, ENNReal.rpow_inv_lt_iff]
    simp [ENNReal.toReal_pos, *]

end UnifTight
end Lp
end MeasureTheory

