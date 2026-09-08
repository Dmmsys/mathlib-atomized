/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Volume measure for Euclidean geometry

In this file we introduce a `d`-dimensional measure for `n`-dimensional Euclidean affine space,
namely `MeasureTheory.Measure.euclideanHausdorffMeasure d` with notation `μHE[d]`.
This is the suitable measure to describe area and volume in an environment of arbitrary dimension.
It is characterized by the following properties:

* Coincides with Lebesgue measure when `d = n`.
* Preserved through isometry, and specifically through affine subspace inclusion.

Internally, this is defined as the `MeasureTheory.Measure.hausdorffMeasure` scaled by a factor.
The factor is defined nonconstructively as the `MeasureTheory.Measure.addHaarScalarFactor` between
the Hausdorff measure and the Lebesgue measure on a model Euclidean space.

TODO: show the scaling factor equals to the ratio between the volume of `d`-dimensional
`Metric.ball` with Euclidean metric and with sup metric.

## Main definitions

* `MeasureTheory.Measure.euclideanHausdorffMeasure`: the Euclidean Hausdorff measure.

## Main statements

* `EuclideanGeometry.measurePreserving_vaddConst`: `μHE[d]` on an affine space matches volume on the
  associated inner product space.
* `AffineSubspace.euclideanHausdorffMeasure_coe_image`: `μHE[d]` is preserved through subspace
  inclusion.

## Tags

Hausdorff measure, measure, metric measure, volume, area
-/

open MeasureTheory Measure Module

public section

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (d : ℕ) : (μH[d] : Measure (EuclideanSpace ℝ (Fin d))).IsAddHaarMeasure := by
  simpa using MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := EuclideanSpace ℝ (Fin d))

variable {X Y : Type*}
variable [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/--
Euclidean Hausdorff measure `μHE[d]`, defined as `μH[d]` scaled to agree with Lebesgue measure
on a `d`-dimensional Euclidean space. While this is defined on any (e)metric space, it is intended
to be used for affine space associated with an inner product space, where it agrees with the volume
measure on the inner product space.
-/
noncomputable
/-
**MeasureTheory.Measure.euclideanHausdorffMeasure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MeasureTheory.Measure.euclideanHausdorffMeasure (d : Nat) : Measure X
参数：d : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
-/
def MeasureTheory.Measure.euclideanHausdorffMeasure (d : ℕ) : Measure X :=
  addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] • μH[d]

@[inherit_doc]
scoped[MeasureTheory] notation "μHE[" d "]" => MeasureTheory.Measure.euclideanHausdorffMeasure d

/-- show the scaling factor equals to the ratio between the volume of `d`-dimensional
`Metric.ball` with Euclidean metric and with sup metric (i.e. a cube), or explicitly,
$\pi^{d/2} / (2^d \Gamma (d/2+1))$. -/
proof_wanted MeasureTheory.Measure.addHaarScalarFactor_hausdorffMeasure_eq (d : ℕ) :
    addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] =
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) / volume (Metric.ball (0 : Fin d → ℝ) 1)

/-
**MeasureTheory.Measure.euclideanHausdorffMeasure_def** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：MeasureTheory.Measure.euclideanHausdorffMeasure_def (d : Nat) : (μHE[d] : 
Measure X) = addHaarScalarFactor (volume : Measure (EuclideanSpace Real (Fin d))
) μH[d] • μH[d]
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_def (d : ℕ) :
    (μHE[d] : Measure X) =
    addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] • μH[d] := by
  rfl

set_option backward.isDefEq.respectTransparency false in -- needed by simplifying `1 • _`
/-- `μHE[0]` and `μH[0]` are equal. -/
@[simp]
/-
**MeasureTheory.Measure.euclideanHausdorffMeasure_zero** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：MeasureTheory.Measure.euclideanHausdorffMeasure_zero : (μHE[0] : Measure X
) = (μH[0] : Measure X)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_def`：MeasureTheory.Measu
re.euclideanHausdorffMeasure_def (d : Nat) : (μHE[d] : Measure X) = addHaarScala
rFactor (volume : Measure (EuclideanSpace…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure.congr_simp`：∀ {X : Type u_2} [ins
t : EMetricSpace X] [inst_1 : MeasurableSpace X] [inst_2 : BorelSpace X] (d d_1 
: ℝ),   d = d_1 → MeasureTheory.Measure…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.Measure.addHaarScalarFactor.congr_simp`：∀ {G : Type u_1} [
inst : TopologicalSpace G] [inst_1 : AddGroup G] [inst_2 : IsTopologicalAddGroup
 G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_zero_singleton`：hausdorffMeasure_
zero_singleton (x : X) : μH[0] ({x} : Set X) = 1
· 使用定理 `OrthonormalBasis.volume_parallelepiped`：OrthonormalBasis.volume_parallel
epiped (b : OrthonormalBasis ι Real F) : volume (parallelepiped b) = 1
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
`μHE[0]` and `μH[0]` are equal.
-/
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero :
    (μHE[0] : Measure X) = (μH[0] : Measure X) := by
  let basis : OrthonormalBasis (Fin 0) ℝ (EuclideanSpace ℝ (Fin 0)) :=
    EuclideanSpace.basisFun (Fin 0) ℝ
  have heq : ({0} : Set (EuclideanSpace ℝ (Fin 0))) = parallelepiped basis := by
    simp [parallelepiped]
  obtain h := isAddLeftInvariant_eq_smul (volume : Measure (EuclideanSpace ℝ (Fin 0))) μH[(0 : ℕ)]
  obtain h := congr($h.symm {0})
  conv_rhs at h => rw [heq, OrthonormalBasis.volume_parallelepiped]
  simp_rw [CharP.cast_eq_zero, smul_apply, hausdorffMeasure_zero_singleton, ENNReal.smul_def,
    smul_eq_mul, mul_one, ENNReal.coe_eq_one] at h
  simp [euclideanHausdorffMeasure_def, h]

/-- The scalar that defines `μHE[d]` is non-zero. -/
/-
**MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero** 是 
Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 
(d : Nat) : addHaarScalarFactor (volume : Measure (EuclideanSpace Real (Fin d)))
 μH[d] != 0
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.volume_parallelepiped`：OrthonormalBasis.volume_parallel
epiped (b : OrthonormalBasis ι Real F) : volume (parallelepiped b) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasureTheory.Measure.isAddLeftInvariant_eq_smul`：∀ {G : Type u_1} [inst
 : TopologicalSpace G] [inst_1 : AddGroup G] [inst_2 : IsTopologicalAddGroup G] 
  [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E

--- 原说明 ---
The scalar that defines `μHE[d]` is non-zero.
-/
theorem MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (d : ℕ) :
    addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] ≠ 0 := by
  intro h0
  obtain h := isAddLeftInvariant_eq_smul (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d]
  obtain h := congr($h (parallelepiped (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d)))))
  simp [OrthonormalBasis.volume_parallelepiped, h0] at h

set_option backward.isDefEq.respectTransparency false in -- needed by `ENNReal.smul_def`
/-
**MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure** 是 Mathlib 中的一个实例，位于
命名空间 ``。
形式化陈述：MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure {E : Type*} [Norm
edAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E] [MeasurableSpa
ce E] [BorelSpace E] : (μHE[Module.finrank Real E] : Measure E).IsAddHaarMeasure
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_def`：MeasureTheory.Measu
re.euclideanHausdorffMeasure_def (d : Nat) : (μHE[d] : Measure X) = addHaarScala
rFactor (volume : Measure (EuclideanSpace…
· 使用定理 `ENNReal.smul_def`：smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>
=0) (x : M) : c • x = (c : Real>=0∞) • x
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.smul`：∀ {G : Type u_1} [inst : Me
asurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ : Meas
ureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zer
o`：MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (d 
: Nat) : addHaarScalarFactor (volume : Measure (EuclideanSpace …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
instance MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] : (μHE[Module.finrank ℝ E] : Measure E).IsAddHaarMeasure := by
  rw [euclideanHausdorffMeasure_def, ENNReal.smul_def]
  exact IsAddHaarMeasure.smul _
    (by simpa using addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Module.finrank ℝ E))
    (by simp)

set_option backward.isDefEq.respectTransparency false in -- needed by `ENNReal.smul_top`
/-- If `d₁ < d₂`, then for any set s we have either `μHE[d₂] s = 0`, or `μHE[d₁] s = ∞`. -/
/-
**MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top {d₁ d₂ : Nat} 
(h : d₁ < d₂) (s : Set X) : μHE[d₂] s = 0 ∨ μHE[d₁] s = ⊤
参数：h : d₁ < d₂；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_def`：MeasureTheory.Measu
re.euclideanHausdorffMeasure_def (d : Nat) : (μHE[d] : Measure X) = addHaarScala
rFactor (volume : Measure (EuclideanSpace…
· 使用定理 `MeasureTheory.Measure.hausdorffMeasure_zero_or_top`：hausdorffMeasure_zer
o_or_top {d₁ d₂ : Real} (h : d₁ < d₂) (s : Set X) : μH[d₂] s = 0 ∨ μH[d₁] s = ∞
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `ENNReal.smul_top`：smul_top {R : Type*} [Semiring R] [IsDomain R] [Module
 R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] [Module.IsTorsionFree R Real>=0
∞] [De…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b

--- 原说明 ---
If `d₁ < d₂`, then for any set s we have either `μHE[d₂] s = 0`, or `μHE[d₁] s =
 ∞`.
-/
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top {d₁ d₂ : ℕ} (h : d₁ < d₂)
    (s : Set X) : μHE[d₂] s = 0 ∨ μHE[d₁] s = ⊤ := by
  simp_rw [euclideanHausdorffMeasure_def]
  obtain h | h := hausdorffMeasure_zero_or_top (show (d₁ : ℝ) < d₂ by simpa using h) s
  · simp [h]
  · right
    rw [smul_apply, h, ENNReal.smul_top]
    simp [addHaarScalarFactor_volume_hausdorffMeasure_ne_zero]

/-!
### `μHE[d]` is preserved through isometry
-/

/-
**IsometryEquiv.measurePreserving_euclideanHausdorffMeasure** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：IsometryEquiv.measurePreserving_euclideanHausdorffMeasure (e : X ≃ᵢ Y) (d 
: Nat) : MeasurePreserving e μHE[d] μHE[d]
参数：e : X ≃ᵢ Y；d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.smul_measure`：smul_measure {R : Type*} [
SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] {f : α -> β} (hf : MeasureP
reserving f μa μb) (c : R) : Measu…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsometryEquiv.measurePreserving_hausdorffMeasure`：measurePreserving_haus
dorffMeasure (e : X ≃ᵢ Y) (d : Real) : MeasurePreserving e μH[d] μH[d]
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure

--- 原说明 ---
### `μHE[d]` is preserved through isometry
-/
theorem IsometryEquiv.measurePreserving_euclideanHausdorffMeasure (e : X ≃ᵢ Y) (d : ℕ) :
    MeasurePreserving e μHE[d] μHE[d] :=
  (IsometryEquiv.measurePreserving_hausdorffMeasure e d).smul_measure _
/-
**Isometry.euclideanHausdorffMeasure_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.euclideanHausdorffMeasure_image {f : X -> Y} {d : Nat} (hf : Isom
etry f) (s : Set X) : μHE[d] (f '' s) = μHE[d] s
参数：hf : Isometry f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_def`：MeasureTheory.Measu
re.euclideanHausdorffMeasure_def (d : Nat) : (μHE[d] : Measure X) = addHaarScala
rFactor (volume : Measure (EuclideanSpace…
· 使用定理 `Isometry.hausdorffMeasure_image`：hausdorffMeasure_image (hf : Isometry f
) (hd : 0 <= d ∨ Surjective f) (s : Set X) : μH[d] (f '' s) = μH[d] s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem Isometry.euclideanHausdorffMeasure_image {f : X → Y} {d : ℕ} (hf : Isometry f) (s : Set X) :
    μHE[d] (f '' s) = μHE[d] s := by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [Isometry.hausdorffMeasure_image hf (by simp)]
/-
**Isometry.euclideanHausdorffMeasure_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.euclideanHausdorffMeasure_preimage {f : X -> Y} {d : Nat} (hf : I
sometry f) (s : Set Y) : μHE[d] (f ⁻¹' s) = μHE[d] (s inter Set.range f)
参数：hf : Isometry f；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_def`：MeasureTheory.Measu
re.euclideanHausdorffMeasure_def (d : Nat) : (μHE[d] : Measure X) = addHaarScala
rFactor (volume : Measure (EuclideanSpace…
· 使用定理 `Isometry.hausdorffMeasure_preimage`：hausdorffMeasure_preimage (hf : Isom
etry f) (hd : 0 <= d ∨ Surjective f) (s : Set Y) : μH[d] (f ⁻¹' s) = μH[d] (s in
ter range f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem Isometry.euclideanHausdorffMeasure_preimage {f : X → Y} {d : ℕ} (hf : Isometry f)
    (s : Set Y) : μHE[d] (f ⁻¹' s) = μHE[d] (s ∩ Set.range f) := by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [Isometry.hausdorffMeasure_preimage hf (by simp)]
/-
**Isometry.map_euclideanHausdorffMeasure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Isometry.map_euclideanHausdorffMeasure {f : X -> Y} {d : Nat} (hf : Isomet
ry f) : μHE[d].map f = μHE[d].restrict (Set.range f)
参数：hf : Isometry f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_def`：MeasureTheory.Measu
re.euclideanHausdorffMeasure_def (d : Nat) : (μHE[d] : Measure X) = addHaarScala
rFactor (volume : Measure (EuclideanSpace…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用定理 `Isometry.map_hausdorffMeasure`：map_hausdorffMeasure (hf : Isometry f) (h
d : 0 <= d ∨ Surjective f) : Measure.map f μH[d] = μH[d].restrict (range f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MeasureTheory.Measure.restrict_smul`：restrict_smul {_m0 : MeasurableSpac
e α} {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (
μ : Measure α) (s : Set α…
-/
theorem Isometry.map_euclideanHausdorffMeasure {f : X → Y} {d : ℕ} (hf : Isometry f) :
    μHE[d].map f = μHE[d].restrict (Set.range f) := by
  simp_rw [euclideanHausdorffMeasure_def]
  rw [Measure.map_smul, map_hausdorffMeasure hf (by simp), Measure.restrict_smul]

/-!
### Applying scalers to `μHE[d]`
-/

open scoped Pointwise in
/-
**MeasureTheory.Measure.euclideanHausdorffMeasure_smul** 是 Mathlib 中的一个定理，位于命名空间
 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ {𝕜 : Type*} {E : Type*}
    [NormedAddCommGroup E] [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    [MeasurableSpace E] [BorelSpace E] (d : ℕ) {r : 𝕜} (hr : r ≠ 0) (s : Set E) :
    μHE[d] (r • s) = ‖r‖₊ ^ d • μHE[d] s := by
  rw [euclideanHausdorffMeasure_def, Measure.smul_apply, hausdorffMeasure_smul₀ (by simp) hr,
    Measure.smul_apply, smul_comm]
  simp

section Homothety
variable {𝕜 V P : Type*} [NormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [MeasurableSpace P] [MetricSpace P] [NormedAddTorsor V P] [BorelSpace P]

/-
**MeasureTheory.euclideanHausdorffMeasure_homothety_image** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：MeasureTheory.euclideanHausdorffMeasure_homothety_image (d : Nat) (x : P) 
{c : 𝕜} (hc : c != 0) (s : Set P) : μHE[d] (AffineMap.homothety x c '' s) = ‖c‖₊
 ^ d • μHE[d] s
参数：d : Nat；x : P；hc : c != 0；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_def`：MeasureTheory.Measu
re.euclideanHausdorffMeasure_def (d : Nat) : (μHE[d] : Measure X) = addHaarScala
rFactor (volume : Measure (EuclideanSpace…
· 使用定理 `MeasureTheory.hausdorffMeasure_homothety_image`：hausdorffMeasure_homothe
ty_image {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0) (s : Set P) : μH
[d] (AffineMap.homothety x c '' s) =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
-/
theorem MeasureTheory.euclideanHausdorffMeasure_homothety_image (d : ℕ) (x : P) {c : 𝕜}
    (hc : c ≠ 0) (s : Set P) :
    μHE[d] (AffineMap.homothety x c '' s) = ‖c‖₊ ^ d • μHE[d] s := by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [hausdorffMeasure_homothety_image (by simp) x hc, smul_comm, NNReal.rpow_natCast]
/-
**MeasureTheory.euclideanHausdorffMeasure_homothety_preimage** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：MeasureTheory.euclideanHausdorffMeasure_homothety_preimage (d : Nat) (x : 
P) {c : 𝕜} (hc : c != 0) (s : Set P) : μHE[d] (AffineMap.homothety x c ⁻¹' s) = 
‖c‖₊⁻¹ ^ d • μHE[d] s
参数：d : Nat；x : P；hc : c != 0；s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_def`：MeasureTheory.Measu
re.euclideanHausdorffMeasure_def (d : Nat) : (μHE[d] : Measure X) = addHaarScala
rFactor (volume : Measure (EuclideanSpace…
· 使用定理 `MeasureTheory.hausdorffMeasure_homothety_preimage`：hausdorffMeasure_homo
thety_preimage {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0) (s : Set P
) : μH[d] (AffineMap.homothety x c ⁻¹' …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
-/
theorem MeasureTheory.euclideanHausdorffMeasure_homothety_preimage (d : ℕ) (x : P) {c : 𝕜}
    (hc : c ≠ 0) (s : Set P) :
    μHE[d] (AffineMap.homothety x c ⁻¹' s) = ‖c‖₊⁻¹ ^ d • μHE[d] s := by
  simp_rw [euclideanHausdorffMeasure_def, Measure.smul_apply]
  rw [hausdorffMeasure_homothety_preimage (by simp) x hc, smul_comm, NNReal.rpow_natCast]

end Homothety

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
variable [FiniteDimensional ℝ V]
variable [MetricSpace P] [MeasurableSpace P] [BorelSpace P] [NormedAddTorsor V P]

/-!
### `μHE[d]` agree with the volume measure on inner product spaces
-/

/-
**EuclideanSpace.euclideanHausdorffMeasure_eq_volume** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：EuclideanSpace.euclideanHausdorffMeasure_eq_volume (d : Nat) : (μHE[d] : M
easure (EuclideanSpace Real (Fin d))) = volume
参数：d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instIsAddHaarMeasureEuclideanSpaceRealFinHausdorffMeasureCast`：∀ (d : ℕ)
, (MeasureTheory.Measure.hausdorffMeasure ↑d).IsAddHaarMeasure
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.euclideanHausdorffMeasure_def`：MeasureTheory.Measu
re.euclideanHausdorffMeasure_def (d : Nat) : (μHE[d] : Measure X) = addHaarScala
rFactor (volume : Measure (EuclideanSpace…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.isAddLeftInvariant_eq_smul`：∀ {G : Type u_1} [inst
 : TopologicalSpace G] [inst_1 : AddGroup G] [inst_2 : IsTopologicalAddGroup G] 
  [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E

--- 原说明 ---
### `μHE[d]` agree with the volume measure on inner product spaces
-/
theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume (d : ℕ) :
    (μHE[d] : Measure (EuclideanSpace ℝ (Fin d))) = volume := by
  rw [euclideanHausdorffMeasure_def, ← isAddLeftInvariant_eq_smul]
/-
**InnerProductSpace.euclideanHausdorffMeasure_eq_volume** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：InnerProductSpace.euclideanHausdorffMeasure_eq_volume : (μHE[finrank Real 
V] : Measure V) = volume
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `OrthonormalBasis.measurePreserving_repr_symm`：OrthonormalBasis.measurePr
eserving_repr_symm (b : OrthonormalBasis ι Real F) : MeasurePreserving b.repr.sy
mm volume volume
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `IsometryEquiv.measurePreserving_euclideanHausdorffMeasure`：IsometryEquiv
.measurePreserving_euclideanHausdorffMeasure (e : X ≃ᵢ Y) (d : Nat) : MeasurePre
serving e μHE[d] μHE[d]
· 使用定理 `EuclideanSpace.euclideanHausdorffMeasure_eq_volume`：EuclideanSpace.eucli
deanHausdorffMeasure_eq_volume (d : Nat) : (μHE[d] : Measure (EuclideanSpace Rea
l (Fin d))) = volume
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem InnerProductSpace.euclideanHausdorffMeasure_eq_volume :
    (μHE[finrank ℝ V] : Measure V) = volume := by
  rw [← (stdOrthonormalBasis ℝ V).measurePreserving_repr_symm.map_eq,
    ← (stdOrthonormalBasis ℝ V).repr.toIsometryEquiv
      |>.symm.measurePreserving_euclideanHausdorffMeasure _ |>.map_eq,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  simp

/-!
### `μHE[d]` on an affine space matches the volume measure on the associated inner product space.
-/
/-- We may want to endow an affine space with a `MeasureSpace` that transfers `volume` from its
associated inner product space. If it is implemented, we can unify this lemma with the previous one.
-/
/-
**EuclideanGeometry.euclideanHausdorffMeasure_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanGeometry.euclideanHausdorffMeasure_eq (p : P) : μHE[finrank Real 
V] = volume.map (IsometryEquiv.vaddConst p)
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `IsometryEquiv.measurePreserving_euclideanHausdorffMeasure`：IsometryEquiv
.measurePreserving_euclideanHausdorffMeasure (e : X ≃ᵢ Y) (d : Nat) : MeasurePre
serving e μHE[d] μHE[d]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.euclideanHausdorffMeasure_eq_volume`：InnerProductSpace
.euclideanHausdorffMeasure_eq_volume : (μHE[finrank Real V] : Measure V) = volum
e

--- 原说明 ---
We may want to endow an affine space with a `MeasureSpace` that transfers `volum
e` from its
associated inner product space. If it is implemented, we can unify this lemma wi
th the previous one.
-/
theorem EuclideanGeometry.euclideanHausdorffMeasure_eq (p : P) :
    μHE[finrank ℝ V] = volume.map (IsometryEquiv.vaddConst p) := by
  have h := (IsometryEquiv.vaddConst p)
    |>.measurePreserving_euclideanHausdorffMeasure (finrank ℝ V) |>.map_eq
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  exact h.symm
/-
**EuclideanGeometry.measurePreserving_vaddConst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanGeometry.measurePreserving_vaddConst (p : P) : MeasurePreserving 
(IsometryEquiv.vaddConst p) volume μHE[finrank Real V] where measurable
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.measurable`：∀ {α : Type u_1} {γ : Type u_3} [inst : Topologic
alSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]   [inst_3 : Top
ologicalSpa…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.euclideanHausdorffMeasure_eq`：EuclideanGeometry.euclid
eanHausdorffMeasure_eq (p : P) : μHE[finrank Real V] = volume.map (IsometryEquiv
.vaddConst p)
-/
theorem EuclideanGeometry.measurePreserving_vaddConst (p : P) :
    MeasurePreserving (IsometryEquiv.vaddConst p) volume μHE[finrank ℝ V] where
  measurable := (IsometryEquiv.vaddConst p).toHomeomorph.measurable
  map_eq := (euclideanHausdorffMeasure_eq p).symm

open EuclideanGeometry

/-!
### `μHE[d]` is preserved through subspace inclusion
-/

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
/-
**AffineSubspace.euclideanHausdorffMeasure_coe_image** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：AffineSubspace.euclideanHausdorffMeasure_coe_image (d : Nat) (s : AffineSu
bspace Real P) (t : Set s) : μHE[d] (Subtype.val '' t) = μHE[d] t
参数：d : Nat；s : AffineSubspace Real P；t : Set s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.euclideanHausdorffMeasure_image`：Isometry.euclideanHausdorffMea
sure_image {f : X -> Y} {d : Nat} (hf : Isometry f) (s : Set X) : μHE[d] (f '' s
) = μHE[d] s
· 使用定理 `isometry_subtype_coe`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {s : 
Set α}, Isometry Subtype.val
-/
theorem AffineSubspace.euclideanHausdorffMeasure_coe_image (d : ℕ) (s : AffineSubspace ℝ P)
    (t : Set s) : μHE[d] (Subtype.val '' t) = μHE[d] t :=
  isometry_subtype_coe.euclideanHausdorffMeasure_image _

/-!
### `μHE[d]` is translation invariant
-/

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `μHE[d]` is translation invariant
-/
instance {α : Type*} [AddGroup α] [AddAction α X] [IsIsometricVAdd α X] (d : ℕ) :
    VAddInvariantMeasure α X μHE[d] := by
  rw [euclideanHausdorffMeasure_def]
  infer_instance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup X] [IsIsometricVAdd X X] (d : ℕ) :
    (μHE[d] : Measure X).IsAddLeftInvariant := by
  rw [euclideanHausdorffMeasure_def]
  infer_instance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup X] [IsIsometricVAdd Xᵃᵒᵖ X] (d : ℕ) :
    (μHE[d] : Measure X).IsAddRightInvariant := by
  rw [euclideanHausdorffMeasure_def]
  infer_instance

/-!
### Integration formula for `μHE[d]`
-/

/-- A measurable equivalence between an affine space and its orthogonal decomposition by a base
point and a direction. We show that this is measure preserving between `μHE[finrank ℝ V]` and
`volume` at `Submodule.measurePreserving_measurableEquivProd`.

This is similar to `Submodule.orthogonalDecomposition` as a `MeasurableEquiv`, but as the right-hand
side is not with L²-norm, this is not an isometry.
-/
/-
**Submodule.measurableEquivProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.measurableEquivProd (s : Submodule Real V) (p : P) : P ≃ᵐ s × sᗮ
参数：s : Submodule Real V；p : P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
A measurable equivalence between an affine space and its orthogonal decompositio
n by a base
point and a direction. We show that this is measure preserving between `μHE[finr
ank ℝ V]` and
`volume` at `Submodule.measurePreserving_measurableEquivProd`.

This is similar to `Submodule.orthogonalDecomposition` as a `MeasurableEquiv`, b
ut as the right-hand
side is not with L²-norm, this is not an isometry.
-/
noncomputable def Submodule.measurableEquivProd (s : Submodule ℝ V) (p : P) : P ≃ᵐ s × sᗮ :=
  (IsometryEquiv.vaddConst p).toHomeomorph.toMeasurableEquiv.symm.trans <|
  s.orthogonalDecomposition.toHomeomorph.toMeasurableEquiv.trans <|
  (MeasurableEquiv.toLp 2 _).symm

@[simp]
/-
**Submodule.measurableEquivProd_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.measurableEquivProd_apply (s : Submodule Real V) (p q : P) : s.m
easurableEquivProd p q = (s.orthogonalProjectionOnto (q -ᵥ p), sᗮ.orthogonalProj
ectionOnto (q -ᵥ p))
参数：s : Submodule Real V；p q : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasurableEquiv.trans_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : Measurab
leSpace γ] (ab : …
· 使用定理 `IsometryEquiv.vaddConst_symm_apply`：∀ {V : Type u_2} {P : Type u_3} [ins
t : SeminormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedA
ddTorsor V P] (x p' : P)…
· 使用定理 `Submodule.orthogonalDecomposition_apply`：orthogonalDecomposition_apply :
 K.orthogonalDecomposition x = .toLp 2 (K.orthogonalProjectionOnto x, Kᗮ.orthogo
nalProjectionOnto x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Submodule.measurableEquivProd_apply (s : Submodule ℝ V) (p q : P) :
    s.measurableEquivProd p q =
    (s.orthogonalProjectionOnto (q -ᵥ p), sᗮ.orthogonalProjectionOnto (q -ᵥ p)) := by
  simp [measurableEquivProd]

@[simp]
/-
**Submodule.measurableEquivProd_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.measurableEquivProd_symm_apply (s : Submodule Real V) (p : P) (q
 : s × sᗮ) : (s.measurableEquivProd p).symm q = (q.1.val + q.2.val) +ᵥ p
参数：s : Submodule Real V；p : P；q : s × sᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasurableEquiv.trans_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 : Measurab
leSpace γ] (ab : …
· 使用定理 `Submodule.orthogonalDecomposition_symm_apply`：∀ {𝕜 : Type u_1} {E : Type
 u_4} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSp
ace 𝕜 E]   (K : Submodule 𝕜 E) [in…
· 使用定理 `IsometryEquiv.vaddConst_apply`：∀ {V : Type u_2} {P : Type u_3} [inst : S
eminormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTor
sor V P] (x : P) (v…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Submodule.measurableEquivProd_symm_apply (s : Submodule ℝ V) (p : P) (q : s × sᗮ) :
    (s.measurableEquivProd p).symm q = (q.1.val + q.2.val) +ᵥ p := by
  simp [measurableEquivProd]
/-
**Submodule.measurePreserving_measurableEquivProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.measurePreserving_measurableEquivProd (s : Submodule Real V) (p 
: P) : MeasurePreserving (s.measurableEquivProd p) μHE[finrank Real V]
参数：s : Submodule Real V；p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.trans`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {e : α…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `EuclideanGeometry.measurePreserving_vaddConst`：EuclideanGeometry.measure
Preserving_vaddConst (p : P) : MeasurePreserving (IsometryEquiv.vaddConst p) vol
ume μHE[finrank Real V] where measu…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `HereditarilyLindelof.to_Lindelof`：∀ {X : Type u} [inst : TopologicalSpac
e X] [HereditarilyLindelofSpace X], LindelofSpace X
· 使用定理 `instHereditarilyLindelofSpaceSubtype`：∀ {X : Type u} [inst : Topological
Space X] [HereditarilyLindelofSpace X] (p : X → Prop),   HereditarilyLindelofSpa
ce { x // p x }
· 使用定理 `SecondCountableTopology.toHereditarilyLindelof`：∀ {X : Type u} [inst : T
opologicalSpace X] [SecondCountableTopology X], HereditarilyLindelofSpace X
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `LinearIsometryEquiv.measurePreserving`：measurePreserving (f : E ≃ₗᵢ[Real
] F) : MeasurePreserving f
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `WithLp.volume_preserving_ofLp`：WithLp.volume_preserving_ofLp : MeasurePr
eserving (@ofLp 2 (U × V))
-/
theorem Submodule.measurePreserving_measurableEquivProd (s : Submodule ℝ V) (p : P) :
    MeasurePreserving (s.measurableEquivProd p) μHE[finrank ℝ V] := by
  refine (measurePreserving_vaddConst _).symm.trans ?_
  refine s.orthogonalDecomposition.measurePreserving.trans ?_
  exact WithLp.volume_preserving_ofLp _ _

/-- The $n$-dimensional volume of an object in an $n$-dimensional space is equal to the integral
of the volume of $(n-d)$-dimensional cross-section along an orthogonal $d$-dimensional subspace.
This is an analogue to `MeasureTheory.Measure.prod_apply`. -/
/-
**AffineSubspace.euclideanHausdorffMeasure_eq_lintegral** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：AffineSubspace.euclideanHausdorffMeasure_eq_lintegral (s : AffineSubspace 
Real P) [hs : Nonempty s] {t : Set P} (ht : MeasurableSet t) : μHE[finrank Real 
V] t = ∫⁻ (x : s), μHE[finrank Real s.directionᗮ] (t inter mk' x.val s.direction
ᗮ) ∂μHE[finrank Real s.direction]
参数：s : AffineSubspace Real P；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage_equiv`：measure_preimage
_equiv {f : α ≃ᵐ β} (hf : MeasurePreserving f μa μb) (s : Set β) : μa (f ⁻¹' s) 
= μb s
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Submodule.measurePreserving_measurableEquivProd`：Submodule.measurePreser
ving_measurableEquivProd (s : Submodule Real V) (p : P) : MeasurePreserving (s.m
easurableEquivProd p) μHE[finrank Rea…
· 使用定理 `MeasureTheory.Measure.volume_eq_prod`：volume_eq_prod (α β) [MeasureSpace
 α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (v
olume : Measure β)
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
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
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `HereditarilyLindelof.to_Lindelof`：∀ {X : Type u} [inst : TopologicalSpac
e X] [HereditarilyLindelofSpace X], LindelofSpace X
· 使用定理 `instHereditarilyLindelofSpaceSubtype`：∀ {X : Type u} [inst : Topological
Space X] [HereditarilyLindelofSpace X] (p : X → Prop),   HereditarilyLindelofSpa
ce { x // p x }
· 使用定理 `SecondCountableTopology.toHereditarilyLindelof`：∀ {X : Type u} [inst : T
opologicalSpace X] [SecondCountableTopology X], HereditarilyLindelofSpace X
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `EuclideanGeometry.euclideanHausdorffMeasure_eq`：EuclideanGeometry.euclid
eanHausdorffMeasure_eq (p : P) : μHE[finrank Real V] = volume.map (IsometryEquiv
.vaddConst p)
· 使用定理 `MeasurableEmbedding.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α}
   {g : α → β},   Measu…
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
The $n$-dimensional volume of an object in an $n$-dimensional space is equal to 
the integral
of the volume of $(n-d)$-dimensional cross-section along an orthogonal $d$-dimen
sional subspace.
This is an analogue to `MeasureTheory.Measure.prod_apply`.
-/
theorem AffineSubspace.euclideanHausdorffMeasure_eq_lintegral (s : AffineSubspace ℝ P)
    [hs : Nonempty s] {t : Set P} (ht : MeasurableSet t) :
    μHE[finrank ℝ V] t = ∫⁻ (x : s), μHE[finrank ℝ s.directionᗮ] (t ∩ mk' x.val s.directionᗮ)
      ∂μHE[finrank ℝ s.direction] := by
  obtain p := hs.some
  rw [← (s.direction.measurePreserving_measurableEquivProd p.val).symm.measure_preimage_equiv,
    volume_eq_prod, prod_apply (by measurability), euclideanHausdorffMeasure_eq,
    MeasurableEmbedding.lintegral_map
        (by simpa using (IsometryEquiv.vaddConst p).toHomeomorph.measurableEmbedding)]
  congr with x
  let u : Set (mk' (x +ᵥ p).val s.directionᗮ) := Subtype.val ⁻¹' (t ∩ mk' (x +ᵥ p).val s.directionᗮ)
  have hu : MeasurableSet u :=
    (ht.inter (closed_of_finiteDimensional _).measurableSet).preimage measurable_subtype_coe
  have hinter : t ∩ (mk' (x +ᵥ p).val s.directionᗮ) = Subtype.val '' u := by
    ext x
    simp [u]
  have hxp : (x +ᵥ p).val ∈ mk' (x +ᵥ p).val s.directionᗮ := by simp
  have hrank : finrank ℝ s.directionᗮ = finrank ℝ (mk' (x +ᵥ p).val s.directionᗮ).direction := by
    rw [direction_mk']
  rw [IsometryEquiv.vaddConst_apply, hinter, euclideanHausdorffMeasure_coe_image, hrank,
    euclideanHausdorffMeasure_eq ⟨x +ᵥ p, hxp⟩, map_apply (by fun_prop) hu]
  /- we have ⊢ volume (a : Set A) = volume (b : Set B). We'd like show a = b, but A and B are
    non-defeq subspaces!
    Lucky we have just developed euclideanHausdorffMeasure, which allows us to move the measure to
    the global vector space. -/
  simp_rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  conv_lhs => rw [← isometry_subtype_coe.euclideanHausdorffMeasure_image]
  conv_rhs => rw [← isometry_subtype_coe.euclideanHausdorffMeasure_image]
  congrm μHE[$hrank] ?_
  ext y
  simp [u, vadd_vadd, add_comm]

/-- The $n$-dimensional volume of an object in an $n$-dimensional space is equal to the integral
of the volume of $(n-1)$-dimensional orthogonal cross-section along a line defined by a direction
vector. This is a special case of `AffineSubspace.euclideanHausdorffMeasure_eq_lintegral` with a
one-dimensional subspace. -/
/-
**EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral (p : P) {v : V} (
hv : v != 0) {t : Set P} (ht : MeasurableSet t) : μHE[finrank Real V] t = ‖v‖ₑ *
 ∫⁻ (x : Real), μHE[finrank Real V - 1] (t inter AffineSubspace.mk' (x • v +ᵥ p)
 (Real ∙ v)ᗮ)
参数：p : P；hv : v != 0；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.finrank_add_finrank_orthogonal`：finrank_add_finrank_orthogonal
 [FiniteDimensional 𝕜 E] (K : Submodule 𝕜 E) : finrank 𝕜 K + finrank 𝕜 Kᗮ = finr
ank 𝕜 E
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AffineSubspace.instNonemptySubtypeMemMk'`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `MeasurableEmbedding.comp`：comp (hg : MeasurableEmbedding g) (hf : Measur
ableEmbedding f) : MeasurableEmbedding (g ∘ f)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `EuclideanGeometry.euclideanHausdorffMeasure_eq`：EuclideanGeometry.euclid
eanHausdorffMeasure_eq (p : P) : μHE[finrank Real V] = volume.map (IsometryEquiv
.vaddConst p)
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableEmbedding.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   MeasurableEmbeddi
ng f → Measurable f
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.volume_eq_of_finrank_eq_one`：MeasureTheory.volume_eq_of_fi
nrank_eq_one (h : Module.finrank Real E = 1) {v : E} (hv : v != 0) : (volume : M
easure E) = ‖v‖ₑ • (volume : Me…
· 使用定理 `AffineSubspace.euclideanHausdorffMeasure_eq_lintegral`：AffineSubspace.eu
clideanHausdorffMeasure_eq_lintegral (s : AffineSubspace Real P) [hs : Nonempty 
s] {t : Set P} (ht : MeasurableSet t) : μHE…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `MeasurableEmbedding.lintegral_map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α}
   {g : α → β},   Measu…
· 使用定理 `MeasureTheory.Measure.euclideanHausdorffMeasure.congr_simp`：∀ {X : Type 
u_1} [inst : EMetricSpace X] [inst_1 : MeasurableSpace X] [inst_2 : BorelSpace X
] (d d_1 : ℕ),   d = d_1 → MeasureTheory.Measure…

--- 原说明 ---
The $n$-dimensional volume of an object in an $n$-dimensional space is equal to 
the integral
of the volume of $(n-1)$-dimensional orthogonal cross-section along a line defin
ed by a direction
vector. This is a special case of `AffineSubspace.euclideanHausdorffMeasure_eq_l
integral` with a
one-dimensional subspace.
-/
theorem EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral (p : P) {v : V} (hv : v ≠ 0)
    {t : Set P} (ht : MeasurableSet t) :
    μHE[finrank ℝ V] t =
      ‖v‖ₑ * ∫⁻ (x : ℝ), μHE[finrank ℝ V - 1] (t ∩ AffineSubspace.mk' (x • v +ᵥ p) (ℝ ∙ v)ᗮ) := by
  have hrank : finrank ℝ (AffineSubspace.mk' p (ℝ ∙ v)).direction = 1 := by
    rw [AffineSubspace.direction_mk']
    apply finrank_span_singleton hv
  have hrank' : finrank ℝ (AffineSubspace.mk' p (ℝ ∙ v)).directionᗮ = finrank ℝ V - 1 := by
    rw [← (AffineSubspace.mk' p (ℝ ∙ v)).direction.finrank_add_finrank_orthogonal, hrank,
      Nat.add_sub_cancel_left]
  let f : ℝ ≃L[ℝ] (AffineSubspace.mk' p (ℝ ∙ v)).direction :=
    (ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ v hv).trans
    (ContinuousLinearEquiv.ofEq (ℝ ∙ v) ((AffineSubspace.mk' p (ℝ ∙ v)).direction) (by simp))
  have hf : MeasurableEmbedding f := f.toHomeomorph.measurableEmbedding
  let p' : AffineSubspace.mk' p (ℝ ∙ v) := ⟨p, by simp⟩
  let g : ℝ → AffineSubspace.mk' p (ℝ ∙ v) := IsometryEquiv.vaddConst p' ∘ f
  have hadd : MeasurableEmbedding (IsometryEquiv.vaddConst p') :=
    (IsometryEquiv.vaddConst p').toHomeomorph.measurableEmbedding
  have hg : MeasurableEmbedding g := hadd.comp hf
  have hm : μHE[finrank ℝ (AffineSubspace.mk' p (ℝ ∙ v)).direction] =
      ‖v‖ₑ • (volume : Measure ℝ).map g := by
    unfold g
    rw [euclideanHausdorffMeasure_eq p', ← map_map hadd.measurable hf.measurable,
      ← Measure.map_smul]
    congr
    let v' : (AffineSubspace.mk' p (ℝ ∙ v)).direction := ⟨v, by simp⟩
    suffices volume = ‖v'‖ₑ • volume.map f by simpa [v']
    exact volume_eq_of_finrank_eq_one hrank (by simpa [v'] using hv)
  have hx (x : ℝ) : x • v +ᵥ p = g x := by rfl
  simp_rw [(AffineSubspace.mk' p (ℝ ∙ v)).euclideanHausdorffMeasure_eq_lintegral ht, hx,
    hm, lintegral_smul_measure, hg.lintegral_map, smul_eq_mul, hrank', AffineSubspace.direction_mk']
