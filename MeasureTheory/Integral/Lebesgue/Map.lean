/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Behavior of the Lebesgue integral under maps
-/

public section

namespace MeasureTheory

open Set Filter ENNReal SimpleFunc

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

section Map

open Measure

/-
**MeasureTheory.lintegral_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_map {f : β -> Real>=0∞} {g : α -> β} (hf : Measurable f) (hg : M
easurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_eq_iSup_eapprox_lintegral`：lintegral_eq_iSup_eap
prox_lintegral {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = ⨆ n, (ea
pprox f n).lintegral μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.SimpleFunc.ext`：ext {f g : α ->ₛ β} (H : forall a, f a = g
 a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.eapprox_comp`：eapprox_comp [MeasurableSpace γ] 
{f : γ -> Real>=0∞} {g : α -> γ} {n : Nat} (hf : Measurable f) (hg : Measurable 
g) : (eapprox (f ∘ g) n : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_map`：lintegral_map {β} [MeasurableSpa
ce β] (g : β ->ₛ Real>=0∞) {f : α -> β} (hf : Measurable f) : g.lintegral (Measu
re.map f μ) = (g.comp f hf).…
-/
theorem lintegral_map {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f)
    (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  simp only [← Function.comp_apply (f := f) (g := g)]
  rw [lintegral_eq_iSup_eapprox_lintegral (hf.comp hg)]
  congr with n : 1
  convert! SimpleFunc.lintegral_map _ hg
  ext1 x; simp only [eapprox_comp hf hg, coe_comp]
/-
**MeasureTheory.lintegral_map'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_map' {f : β -> Real>=0∞} {g : α -> β} (hf : AEMeasurable f (Meas
ure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, f (g 
a) ∂μ
参数：hf : AEMeasurable f (Measure.map g μ)；hg : AEMeasurable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_comp`：ae_eq_comp {f : α -> β} {g g' : β -> δ} (hf : 
AEMeasurable f μ) (h : g =ᵐ[μ.map f] g') : g ∘ f =ᵐ[μ] g' ∘ f
-/
theorem lintegral_map' {f : β → ℝ≥0∞} {g : α → β}
    (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, f (g a) ∂μ :=
  calc
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, hf.mk f a ∂Measure.map g μ :=
      lintegral_congr_ae hf.ae_eq_mk
    _ = ∫⁻ a, hf.mk f a ∂Measure.map (hg.mk g) μ := by
      congr 1
      exact Measure.map_congr hg.ae_eq_mk
    _ = ∫⁻ a, hf.mk f (hg.mk g a) ∂μ := lintegral_map hf.measurable_mk hg.measurable_mk
    _ = ∫⁻ a, hf.mk f (g a) ∂μ := lintegral_congr_ae <| hg.ae_eq_mk.symm.fun_comp _
    _ = ∫⁻ a, f (g a) ∂μ := lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)
/-
**MeasureTheory.lintegral_map_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_map_le (f : β -> Real>=0∞) (g : α -> β) : ∫⁻ a, f a ∂Measure.map
 g μ <= ∫⁻ a, f (g a) ∂μ
参数：f : β -> Real>=0∞；g : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.iSup_lintegral_measurable_le_eq_lintegral`：iSup_lintegral_
measurable_le_eq_lintegral (f : α -> Real>=0∞) : ⨆ (g : α -> Real>=0∞) (_ : Meas
urable g) (_ : g <= f), ∫⁻ a, g a ∂μ = ∫⁻ a, …
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasureTheory.lintegral_map'`：lintegral_map' {f : β -> Real>=0∞} {g : α 
-> β} (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f 
a ∂Measure.map g μ…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem lintegral_map_le (f : β → ℝ≥0∞) (g : α → β) :
    ∫⁻ a, f a ∂Measure.map g μ ≤ ∫⁻ a, f (g a) ∂μ := by
  by_cases hg : AEMeasurable g μ
  · rw [← iSup_lintegral_measurable_le_eq_lintegral]
    refine iSup₂_le fun i hi => iSup_le fun h'i => ?_
    rw [lintegral_map' hi.aemeasurable hg]
    exact lintegral_mono fun _ ↦ h'i _
  · simp [map_of_not_aemeasurable hg]
/-
**MeasureTheory.lintegral_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_comp {f : β -> Real>=0∞} {g : α -> β} (hf : Measurable f) (hg : 
Measurable g) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂map g μ
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
-/
theorem lintegral_comp {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f)
    (hg : Measurable g) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂map g μ :=
  (lintegral_map hf hg).symm

/-- Generalization of `lintegral_comp` to ae-measurable functions. -/
/-
**MeasureTheory.lintegral_comp'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_comp' {f : β -> Real>=0∞} {g : α -> β} (hf : AEMeasurable f (μ.m
ap g)) (hg : AEMeasurable g μ) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂μ.map g
参数：hf : AEMeasurable f (μ.map g)；hg : AEMeasurable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_map'`：lintegral_map' {f : β -> Real>=0∞} {g : α 
-> β} (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f 
a ∂Measure.map g μ…

--- 原说明 ---
Generalization of `lintegral_comp` to ae-measurable functions.
-/
theorem lintegral_comp' {f : β → ℝ≥0∞} {g : α → β} (hf : AEMeasurable f (μ.map g))
    (hg : AEMeasurable g μ) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂μ.map g :=
  (lintegral_map' hf hg).symm
/-
**MeasureTheory.setLIntegral_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_map {f : β -> Real>=0∞} {g : α -> β} {s : Set β} (hs : Measur
ableSet s) (hf : Measurable f) (hg : Measurable g) : ∫⁻ y in s, f y ∂map g μ = ∫
⁻ x in g ⁻¹' s, f (g x) ∂μ
参数：hs : MeasurableSet s；hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_map`：restrict_map {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : (μ.map f).restrict s = (μ.restric
t <| f ⁻¹' s).map f
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
-/
theorem setLIntegral_map {f : β → ℝ≥0∞} {g : α → β} {s : Set β}
    (hs : MeasurableSet s) (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ y in s, f y ∂map g μ = ∫⁻ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [restrict_map hg hs, lintegral_map hf hg]
/-
**MeasureTheory.lintegral_indicator_const_comp** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：lintegral_indicator_const_comp {f : α -> β} {s : Set β} (hf : Measurable f
) (hs : MeasurableSet s) (c : Real>=0∞) : ∫⁻ a, s.indicator (fun _ => c) (f a) ∂
μ = c * μ (f ⁻¹' s)
参数：hf : Measurable f；hs : MeasurableSet s；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.lintegral_indicator_const`：lintegral_indicator_const {s : 
Set α} (hs : MeasurableSet s) (c : Real>=0∞) : ∫⁻ a, s.indicator (fun _ => c) a 
∂μ = c * μ s
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
-/
theorem lintegral_indicator_const_comp {f : α → β} {s : Set β}
    (hf : Measurable f) (hs : MeasurableSet s) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) (f a) ∂μ = c * μ (f ⁻¹' s) := by
  rw [← lintegral_map (measurable_const.indicator hs) hf, lintegral_indicator_const hs,
    Measure.map_apply hf hs]

/-- If `g : α → β` is a measurable embedding and `f : β → ℝ≥0∞` is any function (not necessarily
measurable), then `∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ`. Compare with `lintegral_map` which
applies to any measurable `g : α → β` but requires that `f` is measurable as well. -/
/-
**MeasureTheory._root_.MeasurableEmbedding.lintegral_map** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g : α → β` is a measurable embedding and `f : β → ℝ≥0∞` is any function (not
 necessarily
measurable), then `∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ`. Compare with `linte
gral_map` which
applies to any measurable `g : α → β` but requires that `f` is measurable as wel
l.
-/
theorem _root_.MeasurableEmbedding.lintegral_map {g : α → β}
    (hg : MeasurableEmbedding g) (f : β → ℝ≥0∞) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ := by
  rw [lintegral, lintegral]
  refine le_antisymm (iSup₂_le fun f₀ hf₀ => ?_) (iSup₂_le fun f₀ hf₀ => ?_)
  · rw [SimpleFunc.lintegral_map _ hg.measurable]
    have : (f₀.comp g hg.measurable : α → ℝ≥0∞) ≤ f ∘ g := fun x => hf₀ (g x)
    exact le_iSup_of_le (comp f₀ g hg.measurable) (by exact le_iSup (α := ℝ≥0∞) _ this)
  · rw [← f₀.extend_comp_eq hg (const _ 0), ← SimpleFunc.lintegral_map, ←
      SimpleFunc.lintegral_eq_lintegral, ← lintegral]
    refine lintegral_mono_ae (hg.ae_map_iff.2 <| Eventually.of_forall fun x => ?_)
    exact (extend_apply _ _ _ _).trans_le (hf₀ _)

/-- The `lintegral` transforms appropriately under a measurable equivalence `g : α ≃ᵐ β`.
(Compare `lintegral_map`, which applies to a wider class of functions `g : α → β`, but requires
measurability of the function being integrated.) -/
/-
**MeasureTheory.lintegral_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_map_equiv (f : β -> Real>=0∞) (g : α ≃ᵐ β) : ∫⁻ a, f a ∂map g μ 
= ∫⁻ a, f (g a) ∂μ
参数：f : β -> Real>=0∞；g : α ≃ᵐ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α}
   {g : α → β},   Measu…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e

--- 原说明 ---
The `lintegral` transforms appropriately under a measurable equivalence `g : α ≃
ᵐ β`.
(Compare `lintegral_map`, which applies to a wider class of functions `g : α → β
`, but requires
measurability of the function being integrated.)
-/
theorem lintegral_map_equiv (f : β → ℝ≥0∞) (g : α ≃ᵐ β) :
    ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ :=
  g.measurableEmbedding.lintegral_map f
/-
**MeasureTheory.lintegral_subtype_comap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：lintegral_subtype_comap {s : Set α} (hs : MeasurableSet s) (f : α -> Real>
=0∞) : ∫⁻ x : s, f x ∂(μ.comap (↑)) = ∫⁻ x in s, f x ∂μ
参数：hs : MeasurableSet s；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEmbedding.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α}
   {g : α → β},   Measu…
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…
-/
theorem lintegral_subtype_comap {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∫⁻ x : s, f x ∂(μ.comap (↑)) = ∫⁻ x in s, f x ∂μ := by
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map, map_comap_subtype_coe hs]
/-
**MeasureTheory.setLIntegral_subtype** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_subtype {s : Set α} (hs : MeasurableSet s) (t : Set s) (f : α
 -> Real>=0∞) : ∫⁻ x in t, f x ∂(μ.comap (↑)) = ∫⁻ x in (↑) '' t, f x ∂μ
参数：hs : MeasurableSet s；t : Set s；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasurableEmbedding.restrict_comap`：restrict_comap (μ : Measure β) (s : 
Set α) : (μ.comap f).restrict s = (μ.restrict (f '' s)).comap f
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `MeasureTheory.lintegral_subtype_comap`：lintegral_subtype_comap {s : Set 
α} (hs : MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ x : s, f x ∂(μ.comap (↑)) = ∫
⁻ x in s, f x ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Subtype.coe_image_subset`：coe_image_subset (s : Set α) (t : Set s) : ((↑
) : s -> α) '' t subseteq s
-/
theorem setLIntegral_subtype {s : Set α} (hs : MeasurableSet s) (t : Set s) (f : α → ℝ≥0∞) :
    ∫⁻ x in t, f x ∂(μ.comap (↑)) = ∫⁻ x in (↑) '' t, f x ∂μ := by
  rw [(MeasurableEmbedding.subtype_coe hs).restrict_comap, lintegral_subtype_comap hs,
    restrict_restrict hs, inter_eq_right.2 (Subtype.coe_image_subset _ _)]

end Map

namespace MeasurePreserving

variable {g : α → β} (hg : MeasurePreserving g μ ν)

/-
**MeasureTheory.MeasurePreserving.lintegral_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   {ν : MeasureTheory.Measure β} (f :
 β → ENNReal) (g : α ≃ᵐ β),   MeasureTheory.MeasurePreserving (⇑g) μ ν → ∫⁻ (a :
 β), f a ∂ν = ∫⁻ (a : α), f (g a) ∂μ
参数：f : β → ENNReal；g : α ≃ᵐ β；⇑g；a : β；a : α；g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_map_equiv`：lintegral_map_equiv (f : β -> Real>=0
∞) (g : α ≃ᵐ β) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
-/
protected theorem lintegral_map_equiv (f : β → ℝ≥0∞) (g : α ≃ᵐ β) (hg : MeasurePreserving g μ ν) :
    ∫⁻ a, f a ∂ν = ∫⁻ a, f (g a) ∂μ := by
  rw [← MeasureTheory.lintegral_map_equiv f g, hg.map_eq]

include hg
/-
**MeasureTheory.MeasurePreserving.lintegral_comp** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.MeasurePreserving`。
形式化陈述：lintegral_comp {f : β -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f (g a) ∂μ 
= ∫⁻ b, f b ∂ν
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
-/
theorem lintegral_comp {f : β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, lintegral_map hf hg.measurable]
/-
**MeasureTheory.MeasurePreserving.lintegral_comp_emb** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.MeasurePreserving`。
形式化陈述：lintegral_comp_emb (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) : ∫⁻ 
a, f (g a) ∂μ = ∫⁻ b, f b ∂ν
参数：hge : MeasurableEmbedding g；f : β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasurableEmbedding.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α}
   {g : α → β},   Measu…
-/
theorem lintegral_comp_emb (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞) :
    ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, hge.lintegral_map]
/-
**MeasureTheory.MeasurePreserving.setLIntegral_comp_preimage** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：setLIntegral_comp_preimage {s : Set β} (hs : MeasurableSet s) {f : β -> Re
al>=0∞} (hf : Measurable f) : ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν
参数：hs : MeasurableSet s；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.setLIntegral_map`：setLIntegral_map {f : β -> Real>=0∞} {g 
: α -> β} {s : Set β} (hs : MeasurableSet s) (hf : Measurable f) (hg : Measurabl
e g) : ∫⁻ y in s, f …
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
-/
theorem setLIntegral_comp_preimage
    {s : Set β} (hs : MeasurableSet s) {f : β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq, setLIntegral_map hs hf hg.measurable]
/-
**MeasureTheory.MeasurePreserving.setLIntegral_comp_preimage_emb** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：setLIntegral_comp_preimage_emb (hge : MeasurableEmbedding g) (f : β -> Rea
l>=0∞) (s : Set β) : ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν
参数：hge : MeasurableEmbedding g；f : β -> Real>=0∞；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasurableEmbedding.restrict_map`：restrict_map (μ : Measure α) (s : Set 
β) : (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f
· 使用定理 `MeasurableEmbedding.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α}
   {g : α → β},   Measu…
-/
theorem setLIntegral_comp_preimage_emb (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞) (s : Set β) :
    ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq, hge.restrict_map, hge.lintegral_map]
/-
**MeasureTheory.MeasurePreserving.setLIntegral_comp_emb** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.MeasurePreserving`。
形式化陈述：setLIntegral_comp_emb (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) (s
 : Set α) : ∫⁻ a in s, f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν
参数：hge : MeasurableEmbedding g；f : β -> Real>=0∞；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.setLIntegral_comp_preimage_emb`：setLInte
gral_comp_preimage_emb (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) (s : Se
t β) : ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b …
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `MeasurableEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddin
g f → Function.Inje…
-/
theorem setLIntegral_comp_emb (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞) (s : Set α) :
    ∫⁻ a in s, f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν := by
  rw [← hg.setLIntegral_comp_preimage_emb hge, Set.preimage_image_eq _ hge.injective]

end MeasurePreserving

end MeasureTheory

