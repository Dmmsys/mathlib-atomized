/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Volume forms and measures on inner product spaces

A volume form induces a Lebesgue measure on general finite-dimensional real vector spaces. In this
file, we discuss the specific situation of inner product spaces, where an orientation gives
rise to a canonical volume form. We show that the measure coming from this volume form gives
measure `1` to the parallelepiped spanned by any orthonormal basis, and that it coincides with
the canonical `volume` from the `MeasureSpace` instance.
-/

@[expose] public section

open Module MeasureTheory MeasureTheory.Measure Set WithLp

variable {ι E F : Type*}

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

namespace LinearIsometryEquiv

variable (f : E ≃ₗᵢ[ℝ] F)

/-- Every linear isometry equivalence is a measurable equivalence. -/
/-
**LinearIsometryEquiv.toMeasurableEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearIsometr
yEquiv`。
形式化陈述：toMeasurableEquiv : E ≃ᵐ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every linear isometry equivalence is a measurable equivalence.
-/
def toMeasurableEquiv : E ≃ᵐ F := f.toHomeomorph.toMeasurableEquiv
/-
**LinearIsometryEquiv.coe_toMeasurableEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearIso
metryEquiv`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup F] [inst_1 : In
nerProductSpace ℝ F]   [inst_2 : NormedAddCommGroup E] [inst_3 : InnerProductSpa
ce ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : Measura
bleSpace F] [inst_7 : BorelSpace F] (f : E ≃ₗᵢ[ℝ] F), ⇑f.toMeasurableEquiv = ⇑f
参数：f : E ≃ₗᵢ[ℝ] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_toMeasurableEquiv : (f.toMeasurableEquiv : E → F) = f := rfl
/-
**LinearIsometryEquiv.toMeasurableEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIs
ometryEquiv`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup F] [inst_1 : In
nerProductSpace ℝ F]   [inst_2 : NormedAddCommGroup E] [inst_3 : InnerProductSpa
ce ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : Measura
bleSpace F] [inst_7 : BorelSpace F] (f : E ≃ₗᵢ[ℝ] F),   f.symm.toMeasurableEquiv
 = f.toMeasurableEquiv.symm
参数：f : E ≃ₗᵢ[ℝ] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toMeasurableEquiv_symm : f.symm.toMeasurableEquiv = f.toMeasurableEquiv.symm := rfl
/-
**LinearIsometryEquiv.coe_symm_toMeasurableEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Line
arIsometryEquiv`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup F] [inst_1 : In
nerProductSpace ℝ F]   [inst_2 : NormedAddCommGroup E] [inst_3 : InnerProductSpa
ce ℝ E] [inst_4 : MeasurableSpace E] [inst_5 : BorelSpace E]   [inst_6 : Measura
bleSpace F] [inst_7 : BorelSpace F] (f : E ≃ₗᵢ[ℝ] F), ⇑f.toMeasurableEquiv.symm 
= ⇑f.symm
参数：f : E ≃ₗᵢ[ℝ] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_symm_toMeasurableEquiv : ⇑f.toMeasurableEquiv.symm = f.symm := rfl

end LinearIsometryEquiv

variable [Fintype ι]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

section
variable {m n : ℕ} [_i : Fact (finrank ℝ F = n)]

/-- The volume form coming from an orientation in an inner product space gives measure `1` to the
parallelepiped associated to any orthonormal basis. This is a rephrasing of
`abs_volumeForm_apply_of_orthonormal` in terms of measures. -/
/-
**Orientation.measure_orthonormalBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orientation.measure_orthonormalBasis (o : Orientation Real F (Fin n)) (b :
 OrthonormalBasis ι Real F) : o.volumeForm.measure (parallelepiped b) = 1
参数：o : Orientation Real F (Fin n)；b : OrthonormalBasis ι Real F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrthonormalBasis.coe_reindex`：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Type
 u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2
 : InnerProductSpa…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `parallelepiped_comp_equiv`：parallelepiped_comp_equiv (v : ι -> E) (e : ι
' ≃ ι) : parallelepiped (v ∘ e) = parallelepiped v
· 使用定理 `AlternatingMap.measure_parallelepiped`：∀ {G : Type u_3} [inst : NormedAd
dCommGroup G] [inst_1 : NormedSpace ℝ G] [inst_2 : MeasurableSpace G]   [inst_3 
: BorelSpace G] [inst_4 : F…
· 使用定理 `Orientation.abs_volumeForm_apply_of_orthonormal`：abs_volumeForm_apply_of
_orthonormal (v : OrthonormalBasis (Fin n) Real E) : |o.volumeForm v| = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1

--- 原说明 ---
The volume form coming from an orientation in an inner product space gives measu
re `1` to the
parallelepiped associated to any orthonormal basis. This is a rephrasing of
`abs_volumeForm_apply_of_orthonormal` in terms of measures.
-/
theorem Orientation.measure_orthonormalBasis (o : Orientation ℝ F (Fin n))
    (b : OrthonormalBasis ι ℝ F) : o.volumeForm.measure (parallelepiped b) = 1 := by
  have e : ι ≃ Fin n := by
    refine Fintype.equivFinOfCardEq ?_
    rw [← _i.out, finrank_eq_card_basis b.toBasis]
  have A : ⇑b = b.reindex e ∘ e := by
    ext x
    simp only [OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]
  rw [A, parallelepiped_comp_equiv, AlternatingMap.measure_parallelepiped,
    o.abs_volumeForm_apply_of_orthonormal, ENNReal.ofReal_one]

/-- In an oriented inner product space, the measure coming from the canonical volume form
associated to an orientation coincides with the volume. -/
/-
**Orientation.measure_eq_volume** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orientation.measure_eq_volume (o : Orientation Real F (Fin n)) : o.volumeF
orm.measure = volume
参数：o : Orientation Real F (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orientation.measure_orthonormalBasis`：Orientation.measure_orthonormalBas
is (o : Orientation Real F (Fin n)) (b : OrthonormalBasis ι Real F) : o.volumeFo
rm.measure (parallelepiped…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaarMeasure_unique`：∀ {G : Type u_1} [inst : Ad
dGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G]   [in
st_3 : MeasurableSpace G] [inst_4…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.Measure.instIsLocallyFiniteMeasureMeasure`：∀ {G : Type u_3
} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] [inst_2 : MeasurableS
pace G]   [inst_3 : BorelSpace G] [inst_4 : F…
· 使用定理 `MeasureTheory.Measure.instIsAddLeftInvariantMeasure`：∀ {G : Type u_3} [i
nst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] [inst_2 : MeasurableSpace
 G]   [inst_3 : BorelSpace G] [inst_4 : F…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.addHaar_def`：∀ {ι : Type u_5} {E : Type u_6} [inst : Fintyp
e ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 : Meas
urableSpace E]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In an oriented inner product space, the measure coming from the canonical volume
 form
associated to an orientation coincides with the volume.
-/
theorem Orientation.measure_eq_volume (o : Orientation ℝ F (Fin n)) :
    o.volumeForm.measure = volume := by
  have A : o.volumeForm.measure (stdOrthonormalBasis ℝ F).toBasis.parallelepiped = 1 :=
    Orientation.measure_orthonormalBasis o (stdOrthonormalBasis ℝ F)
  rw [addHaarMeasure_unique o.volumeForm.measure
    (stdOrthonormalBasis ℝ F).toBasis.parallelepiped, A, one_smul]
  simp only [volume, Basis.addHaar]

end

/-- The volume measure in a finite-dimensional inner product space gives measure `1` to the
parallelepiped spanned by any orthonormal basis. -/
/-
**OrthonormalBasis.volume_parallelepiped** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthonormalBasis.volume_parallelepiped (b : OrthonormalBasis ι Real F) : v
olume (parallelepiped b) = 1
参数：b : OrthonormalBasis ι Real F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Orientation.measure_eq_volume`：Orientation.measure_eq_volume (o : Orient
ation Real F (Fin n)) : o.volumeForm.measure = volume
· 使用定理 `Orientation.measure_orthonormalBasis`：Orientation.measure_orthonormalBas
is (o : Orientation Real F (Fin n)) (b : OrthonormalBasis ι Real F) : o.volumeFo
rm.measure (parallelepiped…

--- 原说明 ---
The volume measure in a finite-dimensional inner product space gives measure `1`
 to the
parallelepiped spanned by any orthonormal basis.
-/
theorem OrthonormalBasis.volume_parallelepiped (b : OrthonormalBasis ι ℝ F) :
    volume (parallelepiped b) = 1 := by
  have : Fact (finrank ℝ F = finrank ℝ F) := ⟨rfl⟩
  let o := (stdOrthonormalBasis ℝ F).toBasis.orientation
  rw [← o.measure_eq_volume]
  exact o.measure_orthonormalBasis b

/-- The Haar measure defined by any orthonormal basis of a finite-dimensional inner product space
is equal to its volume measure. -/
/-
**OrthonormalBasis.addHaar_eq_volume** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthonormalBasis.addHaar_eq_volume {ι F : Type*} [Fintype ι] [NormedAddCom
mGroup F] [InnerProductSpace Real F] [FiniteDimensional Real F] [MeasurableSpace
 F] [BorelSpace F] (b : OrthonormalBasis ι Real F) : b.toBasis.addHaar = volume
参数：b : OrthonormalBasis ι Real F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.addHaar_eq_iff`：addHaar_eq_iff [SecondCountableTopology E] 
(b : Basis ι Real E) (μ : Measure E) [SigmaFinite μ] [IsAddLeftInvariant μ] : b.
addHaar = μ ↔ μ b…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `OrthonormalBasis.volume_parallelepiped`：OrthonormalBasis.volume_parallel
epiped (b : OrthonormalBasis ι Real F) : volume (parallelepiped b) = 1

--- 原说明 ---
The Haar measure defined by any orthonormal basis of a finite-dimensional inner 
product space
is equal to its volume measure.
-/
theorem OrthonormalBasis.addHaar_eq_volume {ι F : Type*} [Fintype ι] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (b : OrthonormalBasis ι ℝ F) :
    b.toBasis.addHaar = volume := by
  rw [Basis.addHaar_eq_iff]
  exact b.volume_parallelepiped

/-- An orthonormal basis of a finite-dimensional inner product space defines a measurable
equivalence between the space and the Euclidean space of the same dimension. -/
/-
**OrthonormalBasis.measurableEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrthonormalBasis.measurableEquiv (b : OrthonormalBasis ι Real F) : F ≃ᵐ Eu
clideanSpace Real ι
参数：b : OrthonormalBasis ι Real F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
An orthonormal basis of a finite-dimensional inner product space defines a measu
rable
equivalence between the space and the Euclidean space of the same dimension.
-/
noncomputable def OrthonormalBasis.measurableEquiv (b : OrthonormalBasis ι ℝ F) :
    F ≃ᵐ EuclideanSpace ℝ ι := b.repr.toHomeomorph.toMeasurableEquiv

/-- The measurable equivalence defined by an orthonormal basis is volume preserving. -/
/-
**OrthonormalBasis.measurePreserving_measurableEquiv** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：OrthonormalBasis.measurePreserving_measurableEquiv (b : OrthonormalBasis ι
 Real F) : MeasurePreserving b.measurableEquiv volume volume
参数：b : OrthonormalBasis ι Real F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.addHaar_eq_volume`：OrthonormalBasis.addHaar_eq_volume {
ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace Real F] [Fini
teDimensional Real F] [M…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MeasurableEquiv.coe_toEquiv_symm`：coe_toEquiv_symm (e : α ≃ᵐ β) : (e.toE
quiv.symm : β -> α) = e.symm
· 使用定理 `Module.Basis.map_addHaar`：map_addHaar {ι E F : Type*} [Fintype ι] [Norme
dAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F
] [MeasurableS…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Measurable.measurePreserving`：∀ {α : Type u_1} {β : Type u_2} [inst : Me
asurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measurable f → ∀ (μ
a : MeasureTheory.…
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e

--- 原说明 ---
The measurable equivalence defined by an orthonormal basis is volume preserving.
-/
theorem OrthonormalBasis.measurePreserving_measurableEquiv (b : OrthonormalBasis ι ℝ F) :
    MeasurePreserving b.measurableEquiv volume volume := by
  convert! (b.measurableEquiv.symm.measurable.measurePreserving _).symm
  rw [← (EuclideanSpace.basisFun ι ℝ).addHaar_eq_volume]
  erw [MeasurableEquiv.coe_toEquiv_symm, Basis.map_addHaar _ b.repr.symm.toContinuousLinearEquiv]
  exact b.addHaar_eq_volume.symm
/-
**OrthonormalBasis.measurePreserving_repr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthonormalBasis.measurePreserving_repr (b : OrthonormalBasis ι Real F) : 
MeasurePreserving b.repr volume volume
参数：b : OrthonormalBasis ι Real F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrthonormalBasis.measurePreserving_measurableEquiv`：OrthonormalBasis.mea
surePreserving_measurableEquiv (b : OrthonormalBasis ι Real F) : MeasurePreservi
ng b.measurableEquiv volume volume
-/
theorem OrthonormalBasis.measurePreserving_repr (b : OrthonormalBasis ι ℝ F) :
    MeasurePreserving b.repr volume volume := b.measurePreserving_measurableEquiv
/-
**OrthonormalBasis.measurePreserving_repr_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthonormalBasis.measurePreserving_repr_symm (b : OrthonormalBasis ι Real 
F) : MeasurePreserving b.repr.symm volume volume
参数：b : OrthonormalBasis ι Real F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `OrthonormalBasis.measurePreserving_measurableEquiv`：OrthonormalBasis.mea
surePreserving_measurableEquiv (b : OrthonormalBasis ι Real F) : MeasurePreservi
ng b.measurableEquiv volume volume
-/
theorem OrthonormalBasis.measurePreserving_repr_symm (b : OrthonormalBasis ι ℝ F) :
    MeasurePreserving b.repr.symm volume volume := b.measurePreserving_measurableEquiv.symm

section PiLp

variable (ι : Type*)

variable [Fintype ι]

/-- The measure equivalence between `EuclideanSpace ℝ ι` and `ι → ℝ` is volume preserving. -/
/-
**EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp : MeasurePreser
ving (MeasurableEquiv.toLp 2 (ι -> Real)).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.addHaarMeasure_eq_volume_pi`：addHaarMeasure_eq_volume_pi (
ι : Type*) [Fintype ι] : addHaarMeasure (piIcc01 ι) = volume
· 使用定理 `Module.Basis.parallelepiped_basisFun`：parallelepiped_basisFun (ι : Type*
) [Fintype ι] : (Pi.basisFun Real ι).parallelepiped = TopologicalSpace.PositiveC
ompacts.piIcc01 ι
· 使用定理 `Module.Basis.addHaar_def`：∀ {ι : Type u_5} {E : Type u_6} [inst : Fintyp
e ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 : Meas
urableSpace E]…
· 使用引理 `MeasurableEquiv.coe_toLp`：coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithL
p.toLp p
· 使用引理 `PiLp.coe_symm_continuousLinearEquiv`：coe_symm_continuousLinearEquiv : ⇑(
PiLp.continuousLinearEquiv p 𝕜 β).symm = toLp p
· 使用定理 `Module.Basis.map_addHaar`：map_addHaar {ι E F : Type*} [Fintype ι] [Norme
dAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F
] [MeasurableS…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `OrthonormalBasis.addHaar_eq_volume`：OrthonormalBasis.addHaar_eq_volume {
ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace Real F] [Fini
teDimensional Real F] [M…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Measurable.measurePreserving`：∀ {α : Type u_1} {β : Type u_2} [inst : Me
asurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measurable f → ∀ (μ
a : MeasureTheory.…
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e

--- 原说明 ---
The measure equivalence between `EuclideanSpace ℝ ι` and `ι → ℝ` is volume prese
rving.
-/
theorem EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp :
    MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ)).symm := by
  suffices volume = map (MeasurableEquiv.toLp 2 (ι → ℝ)) volume by
    convert! ((MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.measurePreserving _).symm
  rw [← addHaarMeasure_eq_volume_pi, ← Basis.parallelepiped_basisFun, ← Basis.addHaar_def,
    MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ, Basis.map_addHaar]
  exact (EuclideanSpace.basisFun _ _).addHaar_eq_volume.symm

/-- A copy of `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`
for the canonical spelling of the equivalence. -/
/-
**PiLp.volume_preserving_ofLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PiLp.volume_preserving_ofLp : MeasurePreserving (@ofLp 2 (ι -> Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`：EuclideanSpa
ce.volume_preserving_symm_measurableEquiv_toLp : MeasurePreserving (MeasurableEq
uiv.toLp 2 (ι -> Real)).symm

--- 原说明 ---
A copy of `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`
for the canonical spelling of the equivalence.
-/
theorem PiLp.volume_preserving_ofLp : MeasurePreserving (@ofLp 2 (ι → ℝ)) :=
  EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι

/-- The reverse direction of `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`, since
`MeasurePreserving.symm` only works for `MeasurableEquiv`s. -/
/-
**PiLp.volume_preserving_toLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PiLp.volume_preserving_toLp : MeasurePreserving (@toLp 2 (ι -> Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`：EuclideanSpa
ce.volume_preserving_symm_measurableEquiv_toLp : MeasurePreserving (MeasurableEq
uiv.toLp 2 (ι -> Real)).symm

--- 原说明 ---
The reverse direction of `EuclideanSpace.volume_preserving_symm_measurableEquiv_
toLp`, since
`MeasurePreserving.symm` only works for `MeasurableEquiv`s.
-/
theorem PiLp.volume_preserving_toLp : MeasurePreserving (@toLp 2 (ι → ℝ)) :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm
/-
**volume_euclideanSpace_eq_dirac** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：volume_euclideanSpace_eq_dirac [IsEmpty ι] : (volume : Measure (EuclideanS
pace Real ι)) = Measure.dirac 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `PiLp.volume_preserving_toLp`：PiLp.volume_preserving_toLp : MeasurePreser
ving (@toLp 2 (ι -> Real))
· 使用引理 `MeasureTheory.Measure.volume_pi_eq_dirac`：volume_pi_eq_dirac {ι : Type*}
 [Fintype ι] [IsEmpty ι] {α : ι -> Type*} [forall i, MeasureSpace (α i)] (x : fo
rall a, α a
· 使用定理 `MeasureTheory.Measure.map_dirac`：∀ {α : Type u_1} {β : Type u_2} [inst :
 MeasurableSpace α] [inst_1 : MeasurableSpace β] [MeasurableSingletonClass α]   
[MeasurableSingletonC…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `WithLp.toLp_zero`：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup V]
, WithLp.toLp p 0 = 0
-/
lemma volume_euclideanSpace_eq_dirac [IsEmpty ι] :
    (volume : Measure (EuclideanSpace ℝ ι)) = Measure.dirac 0 := by
  rw [← (PiLp.volume_preserving_toLp ι).map_eq, volume_pi_eq_dirac 0, map_dirac, toLp_zero]

end PiLp

namespace LinearIsometryEquiv

/-- Every linear isometry on a real finite-dimensional Hilbert space is measure-preserving. -/
/-
**LinearIsometryEquiv.measurePreserving** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometr
yEquiv`。
形式化陈述：measurePreserving (f : E ≃ₗᵢ[Real] F) : MeasurePreserving f
参数：f : E ≃ₗᵢ[Real] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `exists_orthonormalBasis`：∀ (𝕜 : Type u_3) [inst : RCLike 𝕜] (E : Type u_
4) [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [FiniteDim
ensional 𝕜 E]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.addHaar_eq_volume`：OrthonormalBasis.addHaar_eq_volume {
ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace Real F] [Fini
teDimensional Real F] [M…
· 使用定理 `Module.Basis.map_addHaar`：map_addHaar {ι E F : Type*} [Fintype ι] [Norme
dAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F
] [MeasurableS…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α

--- 原说明 ---
Every linear isometry on a real finite-dimensional Hilbert space is measure-pres
erving.
-/
theorem measurePreserving (f : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving f := by
  refine ⟨f.continuous.measurable, ?_⟩
  rcases exists_orthonormalBasis ℝ E with ⟨w, b, _hw⟩
  erw [← OrthonormalBasis.addHaar_eq_volume b, ← OrthonormalBasis.addHaar_eq_volume (b.map f),
    Basis.map_addHaar _ f.toContinuousLinearEquiv]
  congr

end LinearIsometryEquiv

section Prod

variable (U V : Type*)
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [MeasurableSpace U] [BorelSpace U]
variable [FiniteDimensional ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
variable [FiniteDimensional ℝ V]

/-- Decompose `WithLp 2 (U × V) ≃ᵐ U × V` into a series of known measure-preserving equivalences -/
/-
**volumePreservingSymmMeasurableEquivToLpProdAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Decompose `WithLp 2 (U × V) ≃ᵐ U × V` into a series of known measure-preserving 
equivalences
-/
private noncomputable def volumePreservingSymmMeasurableEquivToLpProdAux :
    WithLp 2 (U × V) ≃ᵐ U × V :=
  ( -- WithLp 2 (U × V) ≃ₗᵢ[ℝ] WithLp 2 (WithLp 2 (Fin .. → ℝ) × WithLp 2 (Fin .. → ℝ)
    (LinearIsometryEquiv.withLpProdCongr 2
      (stdOrthonormalBasis ℝ U).repr
      (stdOrthonormalBasis ℝ V).repr).trans <|
    -- .. ≃ₗᵢ[ℝ] WithLp 2 (Fin (finrank ℝ U) ⊕ Fin (finrank ℝ V) → ℝ)
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ ↦ ℝ)).symm
  ).toMeasurableEquiv.trans <|
  -- .. ≃ᵐ Fin (finrank ℝ U) ⊕ Fin (finrank ℝ V) → ℝ
  (MeasurableEquiv.toLp 2 _).symm.trans <|
  -- .. ≃ᵐ Fin (finrank ℝ U) → ℝ × Fin (finrank ℝ V) → ℝ
  (MeasurableEquiv.sumPiEquivProdPi (fun _ ↦ ℝ)).trans <|
  -- .. ≃ᵐ U × V
  (MeasurableEquiv.prodCongr
    ((MeasurableEquiv.toLp 2 _).trans (stdOrthonormalBasis ℝ U).repr.symm.toMeasurableEquiv)
    ((MeasurableEquiv.toLp 2 _).trans (stdOrthonormalBasis ℝ V).repr.symm.toMeasurableEquiv))

/-- The measure equivalence between `WithLp 2 (U × V)` and `U × V` is volume preserving. -/
/-
**WithLp.volume_preserving_symm_measurableEquiv_toLp_prod** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：WithLp.volume_preserving_symm_measurableEquiv_toLp_prod : MeasurePreservin
g (MeasurableEquiv.toLp 2 (U × V)).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.MeasurePreserving.trans`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {e : α…
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableSum`：∀ {α : Type u} {β : Type v} [Countable α] [Countable β
], Countable (α ⊕ β)
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearIsometryEquiv.measurePreserving`：measurePreserving (f : E ≃ₗᵢ[Real
] F) : MeasurePreserving f
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`：EuclideanSpa
ce.volume_preserving_symm_measurableEquiv_toLp : MeasurePreserving (MeasurableEq
uiv.toLp 2 (ι -> Real)).symm
· 使用定理 `MeasureTheory.measurePreserving_sumPiEquivProdPi`：measurePreserving_sumP
iEquivProdPi {X : ι oplus ι' -> Type*} {_m : forall i, MeasurableSpace (X i)} (μ
 : forall i, Measure (X i)) [forall i,…
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
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.MeasurePreserving.prod`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {δ : T…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
The measure equivalence between `WithLp 2 (U × V)` and `U × V` is volume preserv
ing.
-/
theorem WithLp.volume_preserving_symm_measurableEquiv_toLp_prod :
    MeasurePreserving (MeasurableEquiv.toLp 2 (U × V)).symm := by
  suffices MeasurePreserving (volumePreservingSymmMeasurableEquivToLpProdAux U V) by
    convert! this
    ext uv
    <;> simp [volumePreservingSymmMeasurableEquivToLpProdAux, MeasurableEquiv.coe_sumPiEquivProdPi,
      MeasurableEquiv.prodCongr]
  refine (LinearIsometryEquiv.measurePreserving _).trans ?_
  refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).trans ?_
  refine (measurePreserving_sumPiEquivProdPi _).trans ?_
  refine MeasurePreserving.prod ?_ ?_
  all_goals
  · refine (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm.trans ?_
    exact (LinearIsometryEquiv.measurePreserving _)

/-- A copy of `WithLp.volume_preserving_symm_measurableEquiv_toLp_prod`
for the canonical spelling of the equivalence. -/
/-
**WithLp.volume_preserving_ofLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithLp.volume_preserving_ofLp : MeasurePreserving (@ofLp 2 (U × V))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithLp.volume_preserving_symm_measurableEquiv_toLp_prod`：WithLp.volume_p
reserving_symm_measurableEquiv_toLp_prod : MeasurePreserving (MeasurableEquiv.to
Lp 2 (U × V)).symm

--- 原说明 ---
A copy of `WithLp.volume_preserving_symm_measurableEquiv_toLp_prod`
for the canonical spelling of the equivalence.
-/
theorem WithLp.volume_preserving_ofLp : MeasurePreserving (@ofLp 2 (U × V)) :=
  volume_preserving_symm_measurableEquiv_toLp_prod U V

/-- The reverse direction of `WithLp.volume_preserving_ofLp`, since
`MeasurePreserving.symm` only works for `MeasurableEquiv`s. -/
/-
**WithLp.volume_preserving_toLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithLp.volume_preserving_toLp : MeasurePreserving (@toLp 2 (U × V))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `WithLp.volume_preserving_symm_measurableEquiv_toLp_prod`：WithLp.volume_p
reserving_symm_measurableEquiv_toLp_prod : MeasurePreserving (MeasurableEquiv.to
Lp 2 (U × V)).symm

--- 原说明 ---
The reverse direction of `WithLp.volume_preserving_ofLp`, since
`MeasurePreserving.symm` only works for `MeasurableEquiv`s.
-/
theorem WithLp.volume_preserving_toLp : MeasurePreserving (@toLp 2 (U × V)) :=
  (volume_preserving_symm_measurableEquiv_toLp_prod U V).symm

end Prod

/-- Volume on a 1-dimensional real vector space is equivalent to a scaled volume on ℝ. -/
/-
**MeasureTheory.volume_eq_of_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.volume_eq_of_finrank_eq_one (h : Module.finrank Real E = 1) 
{v : E} (hv : v != 0) : (volume : Measure E) = ‖v‖ₑ • (volume : Measure Real).ma
p (· • v)
参数：h : Module.finrank Real E = 1；hv : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_singleton_eq_top_iff`：span_singleton_eq_top_iff (x : M) :
 R ∙ x = ⊤ ↔ forall v, exists r : R, r • x = v
· 使用引理 `exists_smul_eq_of_finrank_eq_one`：exists_smul_eq_of_finrank_eq_one (h : 
finrank K V = 1) {x : V} (hx : x != 0) (y : V) : exists (c : K), c • x = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Measurable.smul_const`：Measurable.smul_const (hf : Measurable f) (y : X)
 : Measurable fun x => f x • y
· 使用定理 `ContinuousSMul.toMeasurableSMul`：∀ {M : Type u_7} {α : Type u_8} [inst :
 TopologicalSpace M] [inst_1 : TopologicalSpace α] [inst_2 : MeasurableSpace M] 
  [inst_3 : Measurabl…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.fun_const_smul`：∀ {M : Type u_2} {X : Type u_3} {α : Type u_4
} [inst : MeasurableSpace X] [inst_1 : SMul M X] {m : MeasurableSpace α}   {g : 
α → X} [Measura…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `measurableSMul_of_mul`：∀ (M : Type u_2) [inst : Mul M] [inst_1 : Measura
bleSpace M] [MeasurableMul M], MeasurableSMul M M
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
Volume on a 1-dimensional real vector space is equivalent to a scaled volume on 
ℝ.
-/
theorem MeasureTheory.volume_eq_of_finrank_eq_one (h : Module.finrank ℝ E = 1) {v : E}
    (hv : v ≠ 0) : (volume : Measure E) = ‖v‖ₑ • (volume : Measure ℝ).map (· • v) := calc
  volume = ((volume : Measure ℝ).map (‖v‖⁻¹ • ·)).map (· • v) := by
    have hv' : Submodule.span ℝ {‖v‖⁻¹ • v} = ⊤ := by
      rw [Submodule.span_singleton_eq_top_iff]
      apply exists_smul_eq_of_finrank_eq_one h
      simpa
    let f : ℝ ≃ₗᵢ[ℝ] E := (LinearIsometryEquiv.toSpanUnitSingleton (‖v‖⁻¹ • v)
      (by simp [norm_smul, hv])).trans (LinearIsometryEquiv.ofTop E _ hv')
    rw [map_map (by fun_prop) (by fun_prop)]
    convert! f.measurePreserving.map_eq.symm
    ext x
    simp [f, mul_comm, smul_smul]
  _ = ‖v‖ₑ • (volume : Measure ℝ).map (· • v) := by
    rw [map_addHaar_smul _ (by simpa using hv)]
    simp
