/-
Copyright (c) 2025 Noam Atar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Atar
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Modular character of a locally compact group

On a locally compact group, there is a natural homomorphism `G → ℝ≥0*`, which for `g : G` gives the
value `μ (· * g⁻¹) / μ`, where `μ` is an (inner regular) Haar measure. This file defines this
homomorphism, called the modular character, and shows that it is independent of the chosen Haar
measure.

TODO: Show that the character is continuous.

## Main Declarations

* `modularCharacterFun`: Define the modular character function. If `μ` is a left Haar measure on `G`
  and `g : G`, the measure `A ↦ μ (A g⁻¹)` is also a left Haar measure, so by uniqueness is of the
  form `Δ(g) μ`, for `Δ(g) ∈ ℝ≥0`. This `Δ` is the modular character. The result that this does not
  depend on the measure chosen is `modularCharacterFun_eq_haarScalarFactor`.
* `modularCharacter`: The homomorphism G →* ℝ≥0 whose toFun is `modularCharacterFun`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MeasureTheory

namespace Measure

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The modular character as a map is `g ↦ μ (· * g⁻¹) / μ`, where `μ` is a left Haar measure.

  See also `modularCharacter` that defines the map as a homomorphism. -/
@[to_additive /-- The additive modular character as a map is `g ↦ μ (· - g) / μ`, where `μ` is an
  left additive Haar measure. -/]
/-
**MeasureTheory.Measure.modularCharacterFun** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：modularCharacterFun (g : G) : Real>=0
参数：g : G。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def modularCharacterFun (g : G) : ℝ≥0 :=
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  haarScalarFactor (map (· * g) MeasureTheory.Measure.haar) MeasureTheory.Measure.haar

/-- Independence of modularCharacterFun from the chosen Haar measure. -/
@[to_additive /-- Independence of addModularCharacterFun from the chosen Haar measure -/]
/-
**MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：modularCharacterFun_eq_haarScalarFactor [MeasurableSpace G] [BorelSpace G]
 (μ : Measure G) [IsHaarMeasure μ] (g : G) : modularCharacterFun g = haarScalarF
actor (map (· * g) μ) μ
参数：μ : Measure G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `exists_continuous_nonneg_pos`：exists_continuous_nonneg_pos [RegularSpace
 X] [LocallyCompactSpace X] (x : X) : exists f : C(X, Real), HasCompactSupport f
 ∧ 0 <= (f : X -> …
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`：Continuous.
integral_pos_of_hasCompactSupport_nonneg_nonzero [IsFiniteMeasureOnCompacts μ] {
f : X -> Real} {x : X} (f_cont : Continuous f) (f…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `NNReal.coe_injective`：Function.Injective NNReal.toReal
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactS
upport`：integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (μ' μ : Measure
 G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvar…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasCompactSupport.comp_homeomorph`：∀ {X : Type u_9} {Y : Type u_10} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {M : Type u_11}   [inst_2 
: Zero M] {f : Y → M}, …
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `NNReal.coe_ne_zero`：∀ {r : NNReal}, ↑r ≠ 0 ↔ r ≠ 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_pos_of_isHaarMeasure`：haarScalarF
actor_pos_of_isHaarMeasure (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ
'] : 0 < haarScalarFactor μ' μ
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_eq_integral_div`：haarScalarFactor
_eq_integral_div (μ' μ : Measure G) [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts
 μ'] [IsMulLeftInvariant μ'] {f : G -> Real}…
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `AEMeasurable.mul_const`：AEMeasurable.mul_const [MeasurableMul M] (hf : A
EMeasurable f μ) (c : M) : AEMeasurable (fun x => f x * c) μ
· 使用定理 `aemeasurable_id'`：aemeasurable_id' : AEMeasurable (fun x => x) μ
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Independence of modularCharacterFun from the chosen Haar measure.
-/
lemma modularCharacterFun_eq_haarScalarFactor [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsHaarMeasure μ] (g : G) : modularCharacterFun g = haarScalarFactor (map (· * g) μ) μ := by
  let ν := MeasureTheory.Measure.haar (G := G)
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_one⟩ :
    ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_f_ne_zero (μ₀ : Measure G) [IsHaarMeasure μ₀] : ∫ x, f x ∂μ₀ ≠ 0 :=
    ne_of_gt (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_one)
  apply NNReal.coe_injective
  have t : (∫ x, f (x * g) ∂ν) = (∫ x, f (x * g) ∂(haarScalarFactor ν μ • μ)) := by
    refine integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μ ?_ ?_
    · exact Continuous.comp' f_cont (continuous_mul_const g)
    · have j : (fun x ↦ f (x * g)) = (f ∘ (Homeomorph.mulRight g)) := rfl
      rw [j]
      exact HasCompactSupport.comp_homeomorph f_comp _
  have r : (haarScalarFactor ν μ : ℝ) / (haarScalarFactor ν μ) = 1 := by
    refine div_self ?_
    rw [NNReal.coe_ne_zero]
    apply (ne_of_lt (haarScalarFactor_pos_of_isHaarMeasure _ _)).symm
  calc
  ↑(modularCharacterFun g) = ↑(haarScalarFactor (map (· * g) ν) ν) := by borelize G; rfl
  _ = (∫ x, f x ∂(map (· * g) ν)) / ∫ x, f x ∂ν :=
    haarScalarFactor_eq_integral_div _ _ f_cont f_comp (int_f_ne_zero ν)
  _ = (∫ x, f (x * g) ∂ν) / ∫ x, f x ∂ν := by
    rw [integral_map (AEMeasurable.mul_const aemeasurable_id' _)
    (Continuous.aestronglyMeasurable f_cont)]
  _ = (∫ x, f (x * g) ∂(haarScalarFactor ν μ • μ)) / ∫ x, f x ∂ν := by rw [t]
  _ = (∫ x, f (x * g) ∂(haarScalarFactor ν μ • μ)) / ∫ x, f x ∂(haarScalarFactor ν μ • μ) := by
    rw [integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μ f_cont f_comp]
  _ = (haarScalarFactor ν μ • ∫ x, f (x * g) ∂μ) / (haarScalarFactor ν μ • ∫ x, f x ∂μ) := by
    rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  _ = (haarScalarFactor ν μ / haarScalarFactor ν μ) * ((∫ x, f (x * g) ∂μ) / ∫ x, f x ∂μ) :=
    mul_div_mul_comm _ _ _ _
  _ = 1 * ((∫ x, f (x * g) ∂μ) / ∫ x, f x ∂μ) := by rw [r]
  _ = (∫ x, f (x * g) ∂μ) / ∫ x, f x ∂μ := by rw [one_mul]
  _ = (∫ x, f x ∂(map (· * g) μ)) / ∫ x, f x ∂μ := by
    rw [integral_map (AEMeasurable.mul_const aemeasurable_id' _)
    (Continuous.aestronglyMeasurable f_cont)]
  _ = haarScalarFactor (map (· * g) μ) μ :=
    (haarScalarFactor_eq_integral_div _ _ f_cont f_comp (int_f_ne_zero μ)).symm

@[to_additive]
/-
**MeasureTheory.Measure.map_right_mul_eq_modularCharacterFun_smul** 是 Mathlib 中的
一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：map_right_mul_eq_modularCharacterFun_smul [MeasurableSpace G] [BorelSpace 
G] (μ : Measure G) [IsHaarMeasure μ] [InnerRegular μ] (g : G) : map (· * g) μ = 
modularCharacterFun g • μ
参数：μ : Measure G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor`：modularCh
aracterFun_eq_haarScalarFactor [MeasurableSpace G] [BorelSpace G] (μ : Measure G
) [IsHaarMeasure μ] (g : G) : modularCharacterFun g…
· 使用引理 `MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_innerRegular`：isMulL
eftInvariant_eq_smul_of_innerRegular [LocallyCompactSpace G] (μ' μ : Measure G) 
[IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMu…
-/
lemma map_right_mul_eq_modularCharacterFun_smul [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsHaarMeasure μ] [InnerRegular μ] (g : G) : map (· * g) μ = modularCharacterFun g • μ := by
  rw [modularCharacterFun_eq_haarScalarFactor μ _]
  exact isMulLeftInvariant_eq_smul_of_innerRegular _ μ

@[to_additive]
/-
**MeasureTheory.Measure.modularCharacterFun_pos** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：modularCharacterFun_pos (g : G) : 0 < modularCharacterFun g
参数：g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor`：modularCh
aracterFun_eq_haarScalarFactor [MeasurableSpace G] [BorelSpace G] (μ : Measure G
) [IsHaarMeasure μ] (g : G) : modularCharacterFun g…
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_pos_of_isHaarMeasure`：haarScalarF
actor_pos_of_isHaarMeasure (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ
'] : 0 < haarScalarFactor μ' μ
-/
lemma modularCharacterFun_pos (g : G) : 0 < modularCharacterFun g := by
  borelize G
  rw [modularCharacterFun_eq_haarScalarFactor MeasureTheory.Measure.haar g]
  exact haarScalarFactor_pos_of_isHaarMeasure _ _

@[to_additive]
/-
**MeasureTheory.Measure.modularCharacterFun_map_one** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：modularCharacterFun_map_one : modularCharacterFun (1 : G) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.Measure.map_id'`：map_id' : map (fun x => x) μ = μ
· 使用定理 `MeasureTheory.Measure.haarScalarFactor.congr_simp`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : Group G] [inst_2 : IsTopologicalGroup G]   [in
st_3 : MeasurableSpace G] [inst_4 : Bor…
· 使用引理 `MeasureTheory.Measure.haarScalarFactor_self`：haarScalarFactor_self (μ : 
Measure G) [IsHaarMeasure μ] : haarScalarFactor μ μ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma modularCharacterFun_map_one : modularCharacterFun (1 : G) = 1 := by
  simp [modularCharacterFun, haarScalarFactor_self]

@[to_additive]
/-
**MeasureTheory.Measure.modularCharacterFun_map_mul** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：modularCharacterFun_map_mul (g h : G) : modularCharacterFun (g * h) = modu
larCharacterFun g * modularCharacterFun h
参数：g h : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mul_const`：Measurable.mul_const [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => f x * c
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor`：modularCh
aracterFun_eq_haarScalarFactor [MeasurableSpace G] [BorelSpace G] (μ : Measure G
) [IsHaarMeasure μ] (g : G) : modularCharacterFun g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `comp_mul_right`：comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y *
 x))
· 使用定理 `MeasureTheory.Measure.haarScalarFactor.congr_simp`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : Group G] [inst_2 : IsTopologicalGroup G]   [in
st_3 : MeasurableSpace G] [inst_4 : Bor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma modularCharacterFun_map_mul (g h : G) : modularCharacterFun (g * h) =
    modularCharacterFun g * modularCharacterFun h := by
  borelize G
  have mul_g_meas : Measurable (· * g) := Measurable.mul_const (fun ⦃_⦄ a ↦ a) g
  have mul_h_meas : Measurable (· * h) := Measurable.mul_const (fun ⦃_⦄ a ↦ a) h
  let ν := MeasureTheory.Measure.haar (G := G)
  symm
  calc
    modularCharacterFun g * modularCharacterFun h =
      modularCharacterFun h * modularCharacterFun g := mul_comm _ _
    _ = haarScalarFactor (map (· * h) (map (· * g) ν)) (map (· * g) ν) *
      modularCharacterFun g := by
      rw [modularCharacterFun_eq_haarScalarFactor (map (· * g) ν) _]
    _ = haarScalarFactor (map (· * h) (map (· * g) ν)) (map (· * g) ν) *
      haarScalarFactor (map (· * g) ν) ν := rfl
    _ = haarScalarFactor (map (· * (g * h)) ν) ν := by simp only [map_map mul_h_meas mul_g_meas,
      comp_mul_right, ← haarScalarFactor_eq_mul]

/-- The modular character homomorphism. The underlying function is `modularCharacterFun`, which is
`g ↦ μ (· * g⁻¹) / μ`, where `μ` is a left Haar measure.
-/
/-
**MeasureTheory.Measure.modularCharacter** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：modularCharacter : G ->* Real>=0 where toFun
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.modularCharacterFun_map_one`：modularCharacterFun_m
ap_one : modularCharacterFun (1 : G) = 1
· 使用引理 `MeasureTheory.Measure.modularCharacterFun_map_mul`：modularCharacterFun_m
ap_mul (g h : G) : modularCharacterFun (g * h) = modularCharacterFun g * modular
CharacterFun h

--- 原说明 ---
The modular character homomorphism. The underlying function is `modularCharacter
Fun`, which is
`g ↦ μ (· * g⁻¹) / μ`, where `μ` is a left Haar measure.
-/
noncomputable def modularCharacter : G →* ℝ≥0 where
  toFun := modularCharacterFun
  map_one' := modularCharacterFun_map_one
  map_mul' := modularCharacterFun_map_mul

end Measure

end MeasureTheory

