/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Dynamics.Ergodic.Function
public import Mathlib.Dynamics.Ergodic.RadonNikodym
public import Mathlib.Probability.ConditionalProbability

/-!
# Ergodic measures as extreme points

In this file we prove that a finite measure `μ` is an ergodic measure for a self-map `f`
iff it is an extreme point of the set of invariant measures of `f` with the same total volume.
We also specialize this result to probability measures.
-/

public section

open Filter Set Function MeasureTheory Measure ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {X : Type*} {m : MeasurableSpace X} {μ ν : Measure X} {f : X → X}

namespace Ergodic

/-- Given a constant `c ≠ ∞`, an extreme point of the set of measures that are invariant under `f`
and have total mass `c` is an ergodic measure. -/
/-
**Ergodic.of_mem_extremePoints_measure_univ_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ergodi
c`。
形式化陈述：of_mem_extremePoints_measure_univ_eq {c : Real>=0∞} (hc : c != ∞) (h : μ i
n extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = c}) : Ergodic f
 μ
参数：hc : c != ∞；h : μ in extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ ν 
univ = c}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ergodic.zero_measure`：zero_measure {f : α -> α} (hf : Measurable f) : @E
rgodic α m f 0 where measurable
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `MeasureTheory.MeasurePreserving.smul_measure`：smul_measure {R : Type*} [
SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] {f : α -> β} (hf : MeasureP
reserving f μa μb) (c : R) : Measu…
· 使用定理 `MeasureTheory.MeasurePreserving.restrict_preimage`：restrict_preimage {f 
: α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : MeasurableSet s) : 
MeasurePreserving f (μa.restrict (f ⁻¹'…
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ProbabilityTheory.cond_isProbabilityMeasure`：cond_isProbabilityMeasure [
IsFiniteMeasure μ] (hcs : μ s != 0) : IsProbabilityMeasure μ[|s]
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `ENNReal.div_pos`：∀ {a b : ENNReal}, a ≠ 0 → b ≠ ⊤ → 0 < a / b
· 使用定理 `ENNReal.add_div`：∀ {a b c : ENNReal}, (a + b) / c = a / c + b / c
· 使用定理 `MeasureTheory.measure_add_measure_compl`：measure_add_measure_compl (h : 
MeasurableSet s) : μ s + μ sᶜ = μ univ
· 使用定理 `ENNReal.div_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Given a constant `c ≠ ∞`, an extreme point of the set of measures that are invar
iant under `f`
and have total mass `c` is an ergodic measure.
-/
theorem of_mem_extremePoints_measure_univ_eq {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = c}) : Ergodic f μ := by
  have hf : MeasurePreserving f μ μ := h.1.1
  rcases eq_or_ne c 0 with rfl | hc₀
  · convert! zero_measure hf.measurable
    rw [← measure_univ_eq_zero, h.1.2]
  · refine ⟨hf, ⟨?_⟩⟩
    have : IsFiniteMeasure μ := by
      constructor
      rwa [h.1.2, lt_top_iff_ne_top]
    set S := {ν | MeasurePreserving f ν ν ∧ ν univ = c}
    have {s : Set X} (hsm : MeasurableSet s) (hfs : f ⁻¹' s = s) (hμs : μ s ≠ 0) :
        c • μ[|s] ∈ S := by
      refine ⟨.smul_measure (.smul_measure ?_ _) c, ?_⟩
      · convert! hf.restrict_preimage hsm
        exact hfs.symm
      · rw [Measure.smul_apply, (cond_isProbabilityMeasure hμs).1, smul_eq_mul, mul_one]
    intro s hsm hfs
    by_contra H
    obtain ⟨hs, hs'⟩ : μ s ≠ 0 ∧ μ sᶜ ≠ 0 := by
      simpa [eventuallyConst_set, ae_iff, and_comm] using! H
    have hcond : c • μ[|s] = μ := by
      apply h.2 (this hsm hfs hs) (this hsm.compl (by rw [preimage_compl, hfs]) hs')
      refine ⟨μ s / c, μ sᶜ / c, ENNReal.div_pos hs hc, ENNReal.div_pos hs' hc, ?_, ?_⟩
      · rw [← ENNReal.add_div, measure_add_measure_compl hsm, h.1.2, ENNReal.div_self hc₀ hc]
      · simp [ProbabilityTheory.cond, smul_smul, ← mul_assoc, ENNReal.div_mul_cancel,
          ENNReal.mul_inv_cancel, *]
    rw [← hcond] at hs'
    simp [ProbabilityTheory.cond_apply, hsm] at hs'

/-- An extreme point of the set of invariant probability measures is an ergodic measure. -/
/-
**Ergodic.of_mem_extremePoints** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：of_mem_extremePoints (h : μ in extremePoints Real>=0∞ {ν | MeasurePreservi
ng f ν ν ∧ IsProbabilityMeasure ν}) : Ergodic f μ
参数：h : μ in extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityM
easure ν}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ergodic.of_mem_extremePoints_measure_univ_eq`：of_mem_extremePoints_measu
re_univ_eq {c : Real>=0∞} (hc : c != ∞) (h : μ in extremePoints Real>=0∞ {ν | Me
asurePreserving f ν ν ∧ ν univ = c…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
An extreme point of the set of invariant probability measures is an ergodic meas
ure.
-/
theorem of_mem_extremePoints
    (h : μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν}) :
    Ergodic f μ :=
  .of_mem_extremePoints_measure_univ_eq ENNReal.one_ne_top <| by
    simpa only [isProbabilityMeasure_iff] using h

-- TODO: do we need `IsFiniteMeasure ν` here?
/-
**Ergodic.eq_smul_of_absolutelyContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：eq_smul_of_absolutelyContinuous [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h
μ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : exists c : Real
>=0∞, ν = c • μ
参数：hμ : Ergodic f μ；hfν : MeasurePreserving f ν ν；hνμ : ν ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MeasurePreserving.rnDeriv_comp_aeEq`：rnDeriv_comp_aeEq [Is
FiniteMeasure ν] {f : X -> X} (hfμ : MeasurePreserving f μ μ) (hfν : MeasurePres
erving f ν ν) : μ.rnDeriv ν ∘ f =ᵐ[ν] μ…
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ergodic.ae_eq_const_of_ae_eq_comp₀`：Ergodic.ae_eq_const_of_ae_eq_comp₀ (
h : Ergodic f μ) (hgm : NullMeasurable g μ) (hg_eq : g ∘ f =ᵐ[μ] g) : exists c, 
g =ᵐ[μ] const α c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `countablyGenerated_of_standardBorel`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableSpace.CountablyGenerated α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `Measurable.nullMeasurable`：∀ {α : Type u_2} {β : Type u_3} [m : Measurab
leSpace α] [inst : MeasurableSpace β] {f : α → β}   {μ : MeasureTheory.Measure α
}, Measurable f…
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.setLIntegral_rnDeriv`：setLIntegral_rnDeriv [HaveLe
besgueDecomposition μ ν] [SFinite ν] (hμν : μ ≪ ν) (s : Set α) : ∫⁻ x in s, μ.rn
Deriv ν x ∂ν = μ s
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
（共 33 条，此处仅展示前 30 条）
-/
theorem eq_smul_of_absolutelyContinuous [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Ergodic f μ)
    (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ∃ c : ℝ≥0∞, ν = c • μ := by
  have := hfν.rnDeriv_comp_aeEq hμ.toMeasurePreserving
  obtain ⟨c, hc⟩ := hμ.ae_eq_const_of_ae_eq_comp₀ (measurable_rnDeriv _ _).nullMeasurable this
  use c
  ext s hs
  calc
    ν s = ∫⁻ a in s, ν.rnDeriv μ a ∂μ := .symm <| setLIntegral_rnDeriv hνμ _
    _ = ∫⁻ _ in s, c ∂μ := lintegral_congr_ae <| hc.filter_mono <| ae_mono restrict_le_self
    _ = (c • μ) s := by simp
/-
**Ergodic.eq_of_absolutelyContinuous_measure_univ_eq** 是 Mathlib 中的一个定理，位于命名空间 `
Ergodic`。
形式化陈述：eq_of_absolutelyContinuous_measure_univ_eq [IsFiniteMeasure μ] [IsFiniteMe
asure ν] (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) (huniv
 : ν univ = μ univ) : ν = μ
参数：hμ : Ergodic f μ；hfν : MeasurePreserving f ν ν；hνμ : ν ≪ μ；huniv : ν univ = μ
 univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ergodic.eq_smul_of_absolutelyContinuous`：eq_smul_of_absolutelyContinuous
 [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Ergodic f μ) (hfν : MeasurePreser
ving f ν ν) (hνμ : ν ≪ μ) : e…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem eq_of_absolutelyContinuous_measure_univ_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) (huniv : ν univ = μ univ) :
    ν = μ := by
  rcases hμ.eq_smul_of_absolutelyContinuous hfν hνμ with ⟨c, rfl⟩
  rcases eq_or_ne μ 0 with rfl | hμ₀
  · simp
  · simp_all [ENNReal.mul_eq_right]
/-
**Ergodic.eq_of_absolutelyContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：eq_of_absolutelyContinuous [IsProbabilityMeasure μ] [IsProbabilityMeasure 
ν] (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ν = μ
参数：hμ : Ergodic f μ；hfν : MeasurePreserving f ν ν；hνμ : ν ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ergodic.eq_of_absolutelyContinuous_measure_univ_eq`：eq_of_absolutelyCont
inuous_measure_univ_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Ergodic f μ
) (hfν : MeasurePreserving f ν ν) (hνμ :…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_of_absolutelyContinuous [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ν = μ :=
  eq_of_absolutelyContinuous_measure_univ_eq hμ hfν hνμ <| by simp
/-
**Ergodic.mem_extremePoints_measure_univ_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：mem_extremePoints_measure_univ_eq [IsFiniteMeasure μ] (hμ : Ergodic f μ) :
 μ in extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = μ univ}
参数：hμ : Ergodic f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_extremePoints_iff_left`：mem_extremePoints_iff_left : x in A.extremeP
oints 𝕜 ↔ x in A ∧ forall x₁ in A, forall x₂ in A, x in openSegment 𝕜 x₁ x₂ -> x
₁ = x
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `Ergodic.eq_of_absolutelyContinuous_measure_univ_eq`：eq_of_absolutelyCont
inuous_measure_univ_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Ergodic f μ
) (hfν : MeasurePreserving f ν ν) (hνμ :…
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_right`：add_right (h1 : μ 
≪ ν) (ν' : Measure α) : μ ≪ ν + ν'
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_smul`：absolutelyContinuous_sm
ul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem mem_extremePoints_measure_univ_eq [IsFiniteMeasure μ] (hμ : Ergodic f μ) :
    μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = μ univ} := by
  rw [mem_extremePoints_iff_left]
  refine ⟨⟨hμ.toMeasurePreserving, rfl⟩, ?_⟩
  rintro ν₁ ⟨hfν₁, hν₁μ⟩ ν₂ ⟨hfν₂, hν₂μ⟩ ⟨a, b, ha, hb, hab, rfl⟩
  have : IsFiniteMeasure ν₁ := ⟨by rw [hν₁μ]; apply measure_lt_top⟩
  apply hμ.eq_of_absolutelyContinuous_measure_univ_eq hfν₁ (.add_right _ _) hν₁μ
  apply absolutelyContinuous_smul ha.ne'
/-
**Ergodic.mem_extremePoints** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：mem_extremePoints [IsProbabilityMeasure μ] (hμ : Ergodic f μ) : μ in extre
mePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν}
参数：hμ : Ergodic f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `Ergodic.mem_extremePoints_measure_univ_eq`：mem_extremePoints_measure_uni
v_eq [IsFiniteMeasure μ] (hμ : Ergodic f μ) : μ in extremePoints Real>=0∞ {ν | M
easurePreserving f ν ν ∧ ν univ…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
-/
theorem mem_extremePoints [IsProbabilityMeasure μ] (hμ : Ergodic f μ) :
    μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} := by
  simpa only [isProbabilityMeasure_iff, measure_univ] using hμ.mem_extremePoints_measure_univ_eq
/-
**Ergodic.iff_mem_extremePoints_measure_univ_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ergod
ic`。
形式化陈述：iff_mem_extremePoints_measure_univ_eq [IsFiniteMeasure μ] : Ergodic f μ ↔ 
μ in extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = μ univ}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ergodic.mem_extremePoints_measure_univ_eq`：mem_extremePoints_measure_uni
v_eq [IsFiniteMeasure μ] (hμ : Ergodic f μ) : μ in extremePoints Real>=0∞ {ν | M
easurePreserving f ν ν ∧ ν univ…
· 使用定理 `Ergodic.of_mem_extremePoints_measure_univ_eq`：of_mem_extremePoints_measu
re_univ_eq {c : Real>=0∞} (hc : c != ∞) (h : μ in extremePoints Real>=0∞ {ν | Me
asurePreserving f ν ν ∧ ν univ = c…
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem iff_mem_extremePoints_measure_univ_eq [IsFiniteMeasure μ] :
    Ergodic f μ ↔ μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = μ univ} :=
  ⟨mem_extremePoints_measure_univ_eq, of_mem_extremePoints_measure_univ_eq (measure_ne_top _ _)⟩
/-
**Ergodic.iff_mem_extremePoints** 是 Mathlib 中的一个定理，位于命名空间 `Ergodic`。
形式化陈述：iff_mem_extremePoints [IsProbabilityMeasure μ] : Ergodic f μ ↔ μ in extrem
ePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ergodic.mem_extremePoints`：mem_extremePoints [IsProbabilityMeasure μ] (h
μ : Ergodic f μ) : μ in extremePoints Real>=0∞ {ν | MeasurePreserving f ν ν ∧ Is
ProbabilityMeas…
· 使用定理 `Ergodic.of_mem_extremePoints`：of_mem_extremePoints (h : μ in extremePoin
ts Real>=0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν}) : Ergodic f 
μ
-/
theorem iff_mem_extremePoints [IsProbabilityMeasure μ] :
    Ergodic f μ ↔ μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} :=
  ⟨mem_extremePoints, of_mem_extremePoints⟩

end Ergodic

