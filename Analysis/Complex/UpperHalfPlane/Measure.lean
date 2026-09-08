/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Invariant measure on the upper half-plane

We equip the upper half-plane with a measure, defined as the restriction of the usual measure
on `ℂ` weighted by the function `1 / (im z) ^ 2`. We show that this measure is invariant under
the action of `GL(2, ℝ)`.
-/

open MeasureTheory
open scoped NNReal

public noncomputable section

namespace UpperHalfPlane

/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MeasurableSpace ℍ := .comap UpperHalfPlane.coe inferInstance
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BorelSpace ℍ := ⟨borel_comap.symm⟩
/-
**UpperHalfPlane.measurableEmbedding_coe** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPla
ne`。
形式化陈述：measurableEmbedding_coe : MeasurableEmbedding UpperHalfPlane.coe
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [mβ 
: TopologicalSpace β] [inst_2 : Me…
· 使用定理 `UpperHalfPlane.instBorelSpace`：BorelSpace UpperHalfPlane
· 使用定理 `UpperHalfPlane.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbeddin
g ((↑) : ℍ -> Complex)
-/
lemma measurableEmbedding_coe : MeasurableEmbedding UpperHalfPlane.coe :=
  isOpenEmbedding_coe.measurableEmbedding

@[fun_prop]
/-
**UpperHalfPlane.measurable_coe** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：measurable_coe : Measurable UpperHalfPlane.coe
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用引理 `UpperHalfPlane.measurableEmbedding_coe`：measurableEmbedding_coe : Measur
ableEmbedding UpperHalfPlane.coe
-/
lemma measurable_coe : Measurable UpperHalfPlane.coe :=
  measurableEmbedding_coe.measurable

/-- The invariant measure on the upper half-plane, defined by `dx dy / y ^ 2`. -/
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The invariant measure on the upper half-plane, defined by `dx dy / y ^ 2`.
-/
instance : MeasureSpace ℍ :=
  ⟨(volume.comap UpperHalfPlane.coe).withDensity
    fun z ↦ ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)⟩
/-
**UpperHalfPlane.volume_def** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：volume_def : (volume : Measure ℍ) = (volume.comap UpperHalfPlane.coe).with
Density fun z => ↑((1 / NNReal.mk z.im z.im_pos.le : Real>=0) ^ 2)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem volume_def :
    (volume : Measure ℍ) = (volume.comap UpperHalfPlane.coe).withDensity fun z ↦
      ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) :=
  rfl
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFiniteMeasureOnCompacts (volume.comap UpperHalfPlane.coe) :=
  .comap' _ continuous_coe measurableEmbedding_coe
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocallyFiniteMeasure (volume.comap UpperHalfPlane.coe) := inferInstance
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SigmaFinite (volume.comap UpperHalfPlane.coe) := inferInstance
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SFinite (volume.comap UpperHalfPlane.coe) := inferInstance
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocallyFiniteMeasure (volume : Measure ℍ) := by
  refine .withDensity_coe ?_
  refine .pow (.div₀ continuous_const ?_ ?_) _
  · exact continuous_im.subtype_mk _
  · exact fun x ↦ NNReal.ne_iff.mp x.im_ne_zero
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFiniteMeasureOnCompacts (volume : Measure ℍ) := inferInstance
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SigmaFinite (volume : Measure ℍ) := inferInstance
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SFinite (volume : Measure ℍ) := inferInstance

/-- Express the volume of a measurable set as a Lebesgue integral
over the corresponding subset of `ℂ`. -/
/-
**UpperHalfPlane.volume_eq_lintegral** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：volume_eq_lintegral (s : Set ℍ) : volume s = ∫⁻ z : Complex in (↑) '' s, ↑
((1 / ‖z.im‖₊) ^ 2 : NNReal)
参数：s : Set ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用引理 `UpperHalfPlane.measurable_coe`：measurable_coe : Measurable UpperHalfPlan
e.coe
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEmbedding.map_comap`：map_comap (μ : Measure β) : (comap f μ).m
ap f = μ.restrict (range f)
· 使用引理 `UpperHalfPlane.measurableEmbedding_coe`：measurableEmbedding_coe : Measur
ableEmbedding UpperHalfPlane.coe
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `UpperHalfPlane.volume_def`：volume_def : (volume : Measure ℍ) = (volume.c
omap UpperHalfPlane.coe).withDensity fun z => ↑((1 / NNReal.mk z.im z.im_pos.le 
: Real>=0) ^ 2)
· 使用定理 `MeasureTheory.withDensity_apply'`：withDensity_apply' [SFinite μ] (f : α 
-> Real>=0∞) (s : Set α) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `UpperHalfPlane.instSFiniteComapComplexCoeVolume`：MeasureTheory.SFinite (
MeasureTheory.Measure.comap UpperHalfPlane.coe MeasureTheory.volume)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `MeasureTheory.Measure.restrict_restrict'`：restrict_restrict' (ht : Measu
rableSet t) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasurableEmbedding.measurableSet_range`：measurableSet_range (hf : Measu
rableEmbedding f) : MeasurableSet (range f)
· 使用定理 `MeasureTheory.MeasurePreserving.setLIntegral_comp_emb`：setLIntegral_comp
_emb (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) (s : Set α) : ∫⁻ a in s, 
f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.nnnorm_of_nonneg`：nnnorm_of_nonneg (hr : 0 <= r) : ‖r‖₊ = .mk r hr
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Express the volume of a measurable set as a Lebesgue integral
over the corresponding subset of `ℂ`.
-/
lemma volume_eq_lintegral (s : Set ℍ) :
    volume s = ∫⁻ z : ℂ in (↑) '' s, ↑((1 / ‖z.im‖₊) ^ 2 : NNReal) := by
  have : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  rw [volume_def, withDensity_apply',
    ← Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _),
    ← Measure.restrict_restrict', ← this.setLIntegral_comp_emb measurableEmbedding_coe]
  · simp [Real.nnnorm_of_nonneg (im_pos _).le]
  · exact measurableEmbedding_coe.measurableSet_range

/-- The measure on the upper half-plane is invariant under `GL(2, ℝ)`. -/
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measure on the upper half-plane is invariant under `GL(2, ℝ)`.
-/
instance : SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume := by
  -- It suffices to show `volume (g • s) = volume s` for measurable sets `s`. First
  -- we write this as a lintegral over subsets of `ℂ`.
  refine ((smulInvariantMeasure_tfae _ _).out 2 0).mp fun g s hs ↦ ?_
  rw [volume_eq_lintegral, volume_eq_lintegral, ← Set.image_smul, Set.image_image]
  -- We want to apply the Jacobian change-of-variable formula.
  have hinj : Set.InjOn (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) (UpperHalfPlane.coe '' s) :=
    .image_of_comp <| by simp
  have main := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      volume (measurableEmbedding_coe.measurableSet_image.mpr hs)
      (Set.forall_mem_image.mpr fun z hz ↦
        (hasStrictFDerivAt_smul g _).hasFDerivAt.hasFDerivWithinAt)
      hinj
      (fun z ↦ ↑((1 / ‖z.im‖₊) ^ 2 : NNReal))
  convert! main using 1
  · simp [Set.image_image]
  · apply setLIntegral_congr_fun (measurableEmbedding_coe.measurableSet_image.mpr hs)
    rintro _ ⟨τ, -, rfl⟩
    simp only [← Real.enorm_eq_ofReal_abs, enorm_eq_nnnorm]
    have : ‖(SignType.sign g.val.det : ℝ)‖₊ = 1 := by
      rcases g.det_ne_zero.lt_or_gt with h | h <;> simp [h]
    have := g.det_ne_zero
    have := denom_ne_zero g τ
    norm_cast
    ext
    simp [det_smulFDeriv, *, im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, field]

end UpperHalfPlane

end

