/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Results about both conditional expectations

For non-negative real functions, we have two versions of the conditional expectation:
`condExp` and `condLExp`, built from the Bochner and Lebesgue integrals respectively.
In this file, we gather results that involve both versions.

## Main statements

* `MeasureTheory.toReal_condLExp`: the two definitions of the conditional expectation agree
  almost everywhere. That is, `(fun x ↦ (μ⁻[f | m] x).toReal) =ᵐ[μ] μ[fun x ↦ (f x).toReal | m]`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*}

/-- The two definitions of the conditional expectation `condExp` and `condLExp` (for Bochner and
Lebesgue integrals respectively) agree almost everywhere. -/
/-
**MeasureTheory.toReal_condLExp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：toReal_condLExp (m : MeasurableSpace 𝓧) {m𝓧 : MeasurableSpace 𝓧} {μ : Meas
ure 𝓧} {f : 𝓧 -> Real>=0∞} (hf_meas : AEMeasurable f μ) (hf : ∫⁻ x, f x ∂μ != ∞)
 : (fun x => (μ⁻[f|m] x).toReal) =ᵐ[μ] μ[fun x => (f x).toReal | m]
参数：m : MeasurableSpace 𝓧；hf_meas : AEMeasurable f μ；hf : ∫⁻ x, f x ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`：ae_eq_condExp_of_f
orall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim hm)] {f g : α -> E} (hf
 : Integrable f μ) (hg_int_finite : forall…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.integrable_toReal_iff`：integrable_toReal_iff {f : α -> Rea
l>=0∞} (hf : AEMeasurable f μ) (hf_ne_top : forallᵐ x ∂μ, f x != ∞) : Integrable
 (fun x => (f x).toReal) …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_lt_top'`：ae_lt_top' {f : α -> Real>=0∞} (hf : AEMeasura
ble f μ) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.measurable_condLExp'`：measurable_condLExp' (mΩ : Measurabl
eSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ₀] P⁻[X|mΩ]
· 使用引理 `MeasureTheory.condLExp_ne_top`：condLExp_ne_top {f : Ω -> Real>=0∞} (hf :
 ∫⁻ x, f x ∂P != ∞) : forallᵐ x ∂P, P⁻[f|mΩ] x != ∞
· 使用定理 `MeasureTheory.lintegral_condLExp`：lintegral_condLExp (P : Measure[mΩ₀] Ω
) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) : ∫⁻ ω, P⁻[X|mΩ] ω ∂P = ∫⁻ 
ω, X ω ∂P
· 使用定理 `MeasureTheory.integral_toReal`：integral_toReal {f : α -> Real>=0∞} (hfm 
: AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a,
 f a ∂μ).toReal
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用引理 `MeasureTheory.condLExp_lt_top`：condLExp_lt_top {f : Ω -> Real>=0∞} (hf :
 ∫⁻ x, f x ∂P != ∞) : forallᵐ x ∂P, P⁻[f|mΩ] x < ∞
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.setLIntegral_le_lintegral`：setLIntegral_le_lintegral (s : 
Set α) (f : α -> Real>=0∞) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x, f x ∂μ
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.setLIntegral_condLExp`：setLIntegral_condLExp (P : Measure[
mΩ₀] Ω) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) {s : Set Ω} (hs : Mea
surableSet[mΩ] s) : ∫⁻ ω …
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The two definitions of the conditional expectation `condExp` and `condLExp` (for
 Bochner and
Lebesgue integrals respectively) agree almost everywhere.
-/
lemma toReal_condLExp (m : MeasurableSpace 𝓧) {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧}
    {f : 𝓧 → ℝ≥0∞} (hf_meas : AEMeasurable f μ) (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    (fun x ↦ (μ⁻[f|m] x).toReal) =ᵐ[μ] μ[fun x ↦ (f x).toReal | m] := by
  by_cases hm : m ≤ m𝓧
  swap; · simp [condLExp_of_not_le hm, condExp_of_not_le hm]; rfl
  by_cases hμ : SigmaFinite (μ.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hμ, condExp_of_not_sigmaFinite hm hμ]; rfl
  refine ae_eq_condExp_of_forall_setIntegral_eq hm (E := ℝ) ?_ ?_ ?_ ?_ (μ := μ)
  · rwa [integrable_toReal_iff (by fun_prop)]
    filter_upwards [ae_lt_top' (by fun_prop) hf] with x hx using hx.ne
  · refine fun s hs hsμ ↦ Integrable.integrableOn ?_
    rwa [integrable_toReal_iff (by fun_prop) (condLExp_ne_top hf), lintegral_condLExp]
  · intro s hs hsμ
    rw [integral_toReal (by fun_prop), integral_toReal (by fun_prop),
      setLIntegral_condLExp _ _ _ hs]
    · exact ae_lt_top' hf_meas.restrict ((setLIntegral_le_lintegral _ _).trans_lt hf.lt_top).ne
    · exact ae_restrict_of_ae (condLExp_lt_top hf)
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)

/-- The two definitions of the conditional expectation `condExp` and `condLExp` (for Bochner and
Lebesgue integrals respectively) agree almost everywhere. -/
/-
**MeasureTheory.condLExp_ofReal** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_ofReal (m : MeasurableSpace 𝓧) {m𝓧 : MeasurableSpace 𝓧} {μ : Meas
ure 𝓧} {f : 𝓧 -> Real} (hf : Integrable f μ) (h'f : 0 <=ᵐ[μ] f) : μ⁻[fun x => EN
NReal.ofReal (f x) | m] =ᵐ[μ] fun x => ENNReal.ofReal (μ[f | m] x)
参数：m : MeasurableSpace 𝓧；hf : Integrable f μ；h'f : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `MeasureTheory.condExp_nonneg`：condExp_nonneg (hf : 0 <=ᵐ[μ] f) : 0 <=ᵐ[μ
] μ[f | m]
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.ae_lt_top`：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable 
f) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `MeasureTheory.measurable_condLExp'`：measurable_condLExp' (mΩ : Measurabl
eSpace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ₀] P⁻[X|mΩ]
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_condLExp`：lintegral_condLExp (P : Measure[mΩ₀] Ω
) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) : ∫⁻ ω, P⁻[X|mΩ] ω ∂P = ∫⁻ 
ω, X ω ∂P
· 使用引理 `MeasureTheory.toReal_condLExp`：toReal_condLExp (m : MeasurableSpace 𝓧) {
m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧} {f : 𝓧 -> Real>=0∞} (hf_meas : AEMeasura
ble f μ) (hf : ∫⁻ x…
· 使用引理 `AEMeasurable.ennreal_ofReal`：AEMeasurable.ennreal_ofReal {f : α -> Real}
 {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal
 (f x)) μ
· 使用定理 `MeasureTheory.Integrable.aemeasurable`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]
   [inst_1 : ContinuousENor…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ENNReal.toReal_eq_toReal_iff'`：toReal_eq_toReal_iff' {x y : Real>=0∞} (h
x : x != ⊤) (hy : y != ⊤) : x.toReal = y.toReal ↔ x = y
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
The two definitions of the conditional expectation `condExp` and `condLExp` (for
 Bochner and
Lebesgue integrals respectively) agree almost everywhere.
-/
lemma condLExp_ofReal (m : MeasurableSpace 𝓧) {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧}
    {f : 𝓧 → ℝ} (hf : Integrable f μ) (h'f : 0 ≤ᵐ[μ] f) :
    μ⁻[fun x ↦ ENNReal.ofReal (f x) | m] =ᵐ[μ] fun x ↦ ENNReal.ofReal (μ[f | m] x) := by
  by_cases hm : m ≤ m𝓧
  swap; · simp [condLExp_of_not_le hm, condExp_of_not_le hm]; rfl
  by_cases hμ : SigmaFinite (μ.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hμ, condExp_of_not_sigmaFinite hm hμ]; rfl
  have A : μ[fun x ↦ (ENNReal.ofReal (f x)).toReal | m] =ᵐ[μ] μ[f | m] := by
    apply condExp_congr_ae
    filter_upwards [h'f] with x hx using ENNReal.toReal_ofReal hx
  have B : 0 ≤ᵐ[μ] μ[f | m] := condExp_nonneg h'f
  let g x := ENNReal.ofReal (f x)
  have I : ∫⁻ x, g x ∂μ ≠ ∞ := by
    have : ∫⁻ x, g x ∂μ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [h'f] with x hx using by simp [g, Real.enorm_eq_ofReal hx]
    rw [this]
    exact hf.2.ne
  have J : ∀ᵐ x ∂μ, μ⁻[g | m] x < ∞ := by
    apply ae_lt_top (by fun_prop)
    convert I using 1
    exact lintegral_condLExp _ _ _
  filter_upwards [toReal_condLExp m (f := g) (by fun_prop) I, h'f, A, B, J]
    with a ha h'a h''a h'''a C
  rw [← ENNReal.toReal_eq_toReal_iff' C.ne, ENNReal.toReal_ofReal h'''a, ha, h''a]
  simp

/-- The two definitions of the conditional expectation `condExp` and `condLExp` (for Bochner and
Lebesgue integrals respectively) agree almost everywhere. -/
/-
**MeasureTheory.condLExp_enorm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：condLExp_enorm (m : MeasurableSpace 𝓧) {m𝓧 : MeasurableSpace 𝓧} {μ : Measu
re 𝓧} {f : 𝓧 -> Real} (hf : Integrable f μ) (h'f : 0 <=ᵐ[μ] f) : μ⁻[fun x => ‖f 
x‖ₑ | m] =ᵐ[μ] fun x => ‖μ[f | m] x‖ₑ
参数：m : MeasurableSpace 𝓧；hf : Integrable f μ；h'f : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condLExp_congr_ae`：condLExp_congr_ae {P : Measure[mΩ₀] Ω} 
{X Y : Ω -> Real>=0∞} (hXY : X =ᵐ[P] Y) : P⁻[X|mΩ] =ᵐ[P] P⁻[Y|mΩ]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用引理 `MeasureTheory.condLExp_ofReal`：condLExp_ofReal (m : MeasurableSpace 𝓧) {
m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧} {f : 𝓧 -> Real} (hf : Integrable f μ) (h
'f : 0 <=ᵐ[μ] f) : …
· 使用引理 `MeasureTheory.condExp_nonneg`：condExp_nonneg (hf : 0 <=ᵐ[μ] f) : 0 <=ᵐ[μ
] μ[f | m]
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α

--- 原说明 ---
The two definitions of the conditional expectation `condExp` and `condLExp` (for
 Bochner and
Lebesgue integrals respectively) agree almost everywhere.
-/
lemma condLExp_enorm (m : MeasurableSpace 𝓧) {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧}
    {f : 𝓧 → ℝ} (hf : Integrable f μ) (h'f : 0 ≤ᵐ[μ] f) :
    μ⁻[fun x ↦ ‖f x‖ₑ | m] =ᵐ[μ] fun x ↦ ‖μ[f | m] x‖ₑ := by
  have A : μ⁻[fun x ↦ ENNReal.ofReal (f x) | m] =ᵐ[μ] μ⁻[fun x ↦ ‖f x‖ₑ | m] := by
    apply condLExp_congr_ae
    filter_upwards [h'f] with x hx using by simp [Real.enorm_eq_ofReal hx]
  grw [← A, condLExp_ofReal m hf h'f]
  filter_upwards [condExp_nonneg h'f (m := m)] with x hx using by simp [Real.enorm_eq_ofReal hx]
/-
**MeasureTheory.lintegral_enorm_condExp_indicator** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：lintegral_enorm_condExp_indicator {m : MeasurableSpace 𝓧} {m𝓧 : Measurable
Space 𝓧} (hm : m <= m𝓧) {μ : Measure 𝓧} [SigmaFinite (μ.trim hm)] {s : Set 𝓧} (h
s : MeasurableSet s) (h's : μ s != ∞
参数：hm : m <= m𝓧；μ.trim hm；hs : MeasurableSet s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.condLExp_enorm`：condLExp_enorm (m : MeasurableSpace 𝓧) {m𝓧
 : MeasurableSpace 𝓧} {μ : Measure 𝓧} {f : 𝓧 -> Real} (hf : Integrable f μ) (h'f
 : 0 <=ᵐ[μ] f) : μ…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `enorm_indicator_eq_indicator_enorm`：enorm_indicator_eq_indicator_enorm :
 ‖indicator s f a‖ₑ = indicator s (fun a => ‖f a‖ₑ) a
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `MeasureTheory.lintegral_condLExp`：lintegral_condLExp (P : Measure[mΩ₀] Ω
) [hσ : SigmaFinite (P.trim hm)] (X : Ω -> Real>=0∞) : ∫⁻ ω, P⁻[X|mΩ] ω ∂P = ∫⁻ 
ω, X ω ∂P
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lintegral_enorm_condExp_indicator
    {m : MeasurableSpace 𝓧} {m𝓧 : MeasurableSpace 𝓧} (hm : m ≤ m𝓧) {μ : Measure 𝓧}
    [SigmaFinite (μ.trim hm)] {s : Set 𝓧} (hs : MeasurableSet s) (h's : μ s ≠ ∞ := by finiteness) :
    ∫⁻ a, ‖μ[s.indicator (1 : 𝓧 → ℝ) | m] a‖ₑ ∂μ = μ s := calc
  _ = ∫⁻ a, μ⁻[fun x ↦ ‖s.indicator (1 : 𝓧 → ℝ) x‖ₑ | m] a ∂μ := by
    apply lintegral_congr_ae
    apply (condLExp_enorm _ _ _).symm
    · apply (integrable_indicator_iff hs).2
      apply integrableOn_const h's
    · filter_upwards with x
      simp only [Pi.zero_apply, Set.indicator, Pi.one_apply]
      grind
  _ = μ s := by
    simp [lintegral_condLExp hm, enorm_indicator_eq_indicator_enorm, lintegral_indicator hs]

end MeasureTheory

