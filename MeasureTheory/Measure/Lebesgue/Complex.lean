/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Lebesgue measure on `ℂ`

In this file, we consider the Lebesgue measure on `ℂ` defined as the push-forward of the volume
on `ℝ²` under the natural isomorphism and prove that it is equal to the measure `volume` of `ℂ`
coming from its `InnerProductSpace` structure over `ℝ`. For that, we consider the two frequently
used ways to represent `ℝ²` in `mathlib`: `ℝ × ℝ` and `Fin 2 → ℝ`, define measurable equivalences
(`MeasurableEquiv`) to both types and prove that both of them are volume preserving (in the sense
of `MeasureTheory.measurePreserving`).
-/

@[expose] public section

open MeasureTheory Module

noncomputable section

namespace Complex

/-- Measurable equivalence between `ℂ` and `ℝ² = Fin 2 → ℝ`. -/
/-
**Complex.measurableEquivPi** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：measurableEquivPi : Complex ≃ᵐ (Fin 2 -> Real)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instT2Space`：T2Space ℂ

--- 原说明 ---
Measurable equivalence between `ℂ` and `ℝ² = Fin 2 → ℝ`.
-/
def measurableEquivPi : ℂ ≃ᵐ (Fin 2 → ℝ) :=
  basisOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

@[simp]
/-
**Complex.measurableEquivPi_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurableEquivPi_apply (a : Complex) : measurableEquivPi a = ![a.re, a.im
]
参数：a : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurableEquivPi_apply (a : ℂ) :
    measurableEquivPi a = ![a.re, a.im] := rfl

@[simp]
/-
**Complex.measurableEquivPi_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurableEquivPi_symm_apply (p : (Fin 2) -> Real) : measurableEquivPi.sym
m p = (p 0) + (p 1) * I
参数：p : (Fin 2) -> Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurableEquivPi_symm_apply (p : (Fin 2) → ℝ) :
    measurableEquivPi.symm p = (p 0) + (p 1) * I := rfl

/-- Measurable equivalence between `ℂ` and `ℝ × ℝ`. -/
/-
**Complex.measurableEquivRealProd** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：measurableEquivRealProd : Complex ≃ᵐ Real × Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Measurable equivalence between `ℂ` and `ℝ × ℝ`.
-/
def measurableEquivRealProd : ℂ ≃ᵐ ℝ × ℝ :=
  equivRealProdCLM.toHomeomorph.toMeasurableEquiv

@[simp]
/-
**Complex.measurableEquivRealProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：measurableEquivRealProd_apply (a : Complex) : measurableEquivRealProd a = 
(a.re, a.im)
参数：a : Complex。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurableEquivRealProd_apply (a : ℂ) : measurableEquivRealProd a = (a.re, a.im) := rfl

@[simp]
/-
**Complex.measurableEquivRealProd_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`
。
形式化陈述：measurableEquivRealProd_symm_apply (p : Real × Real) : measurableEquivReal
Prod.symm p = { re
参数：p : Real × Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurableEquivRealProd_symm_apply (p : ℝ × ℝ) :
    measurableEquivRealProd.symm p = { re := p.1, im := p.2 } := rfl
/-
**Complex.volume_preserving_equiv_pi** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：volume_preserving_equiv_pi : MeasurePreserving measurableEquivPi
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.addHaarMeasure_eq_volume_pi`：addHaarMeasure_eq_volume_pi (
ι : Type*) [Fintype ι] : addHaarMeasure (piIcc01 ι) = volume
· 使用定理 `Module.Basis.parallelepiped_basisFun`：parallelepiped_basisFun (ι : Type*
) [Fintype ι] : (Pi.basisFun Real ι).parallelepiped = TopologicalSpace.PositiveC
ompacts.piIcc01 ι
· 使用定理 `Module.Basis.addHaar_def`：∀ {ι : Type u_5} {E : Type u_6} [inst : Fintyp
e ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 : Meas
urableSpace E]…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Complex.measurableEquivPi.eq_1`：Complex.measurableEquivPi = Complex.basi
sOneI.equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
· 使用定理 `Homeomorph.toMeasurableEquiv_symm_coe`：Homeomorph.toMeasurableEquiv_symm
_coe (h : γ ≃ₜ γ₂) : (h.toMeasurableEquiv.symm : γ₂ -> γ) = h.symm
· 使用定理 `ContinuousLinearEquiv.coe_symm_toHomeomorph`：coe_symm_toHomeomorph (e : 
M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph.symm = e.symm
· 使用定理 `Module.Basis.map_addHaar`：map_addHaar {ι E F : Type*} [Fintype ι] [Norme
dAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F
] [MeasurableS…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.addHaar_eq_iff`：addHaar_eq_iff [SecondCountableTopology E] 
(b : Basis ι Real E) (μ : Measure E) [SigmaFinite μ] [IsAddLeftInvariant μ] : b.
addHaar = μ ↔ μ b…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
（共 34 条，此处仅展示前 30 条）
-/
theorem volume_preserving_equiv_pi : MeasurePreserving measurableEquivPi := by
  convert! (measurableEquivPi.symm.measurable.measurePreserving volume).symm
  rw [← addHaarMeasure_eq_volume_pi, ← Basis.parallelepiped_basisFun, ← Basis.addHaar,
    measurableEquivPi, Homeomorph.toMeasurableEquiv_symm_coe,
    ContinuousLinearEquiv.coe_symm_toHomeomorph, Basis.map_addHaar, eq_comm]
  exact (Basis.addHaar_eq_iff _ _).mpr Complex.orthonormalBasisOneI.volume_parallelepiped
/-
**Complex.volume_preserving_equiv_real_prod** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：volume_preserving_equiv_real_prod : MeasurePreserving measurableEquivRealP
rod
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用定理 `MeasureTheory.volume_preserving_finTwoArrow`：volume_preserving_finTwoArr
ow (α : Type u) [MeasureSpace α] [SigmaFinite (volume : Measure α)] : MeasurePre
serving (@MeasurableEquiv.finTwoA…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Complex.volume_preserving_equiv_pi`：volume_preserving_equiv_pi : Measure
Preserving measurableEquivPi
-/
theorem volume_preserving_equiv_real_prod : MeasurePreserving measurableEquivRealProd :=
  (volume_preserving_finTwoArrow ℝ).comp volume_preserving_equiv_pi

end Complex

