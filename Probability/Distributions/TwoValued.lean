/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.CondVar

import Mathlib.Probability.Notation

/-!
# Distributions on two values

This file proves a few lemmas about random variables that take at most two values.
-/

public section

open MeasureTheory
open scoped ProbabilityTheory

namespace MeasureTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}

/-- If an `AEMeasurable` function is ae equal to `0` or `1`, then its integral is equal to the
measure of the set where it equals `1`. -/
/-
**MeasureTheory.integral_of_ae_eq_zero_or_one** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_of_ae_eq_zero_or_one (hXmeas : AEMeasurable X μ) (hX : forallᵐ ω 
∂μ, X ω = 0 ∨ X ω = 1) : μ[X] = μ.real {ω | X ω = 1}
参数：hXmeas : AEMeasurable X μ；hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac`：ae_eq_or_e
q_iff_map_eq_dirac_add_dirac {μ : Measure β} (hf : AEMeasurable f μ) (ha : a₁ !=
 a₂) : (forallᵐ b ∂μ, f b = a₁ ∨ f b = a₂) ↔ μ.map…
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
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `MeasureTheory.lintegral_add_measure`：lintegral_add_measure (f : α -> Rea
l>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
If an `AEMeasurable` function is ae equal to `0` or `1`, then its integral is eq
ual to the
measure of the set where it equals `1`.
-/
lemma integral_of_ae_eq_zero_or_one (hXmeas : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    μ[X] = μ.real {ω | X ω = 1} := by
  refine (integral_map (f := id) hXmeas <| by fun_prop).symm.trans ?_
  rw [(Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac hXmeas zero_ne_one).1 hX]
  by_cases h : μ {ω | X ω = 1} = ⊤
  · simp [h, Measure.real, Set.preimage, integral_undef, Integrable, HasFiniteIntegral]
  rw [integral_add_measure ⟨by fun_prop, by simp [HasFiniteIntegral]⟩ <|
    .smul_measure (by simp [integrable_dirac]) h]
  simp [Measure.real, Set.preimage]

/-- If a random variable is ae equal to `0` or `1`, then one minus its expectation is equal to the
probability that it equals `0`. -/
/-
**MeasureTheory.integral_one_sub_of_ae_eq_zero_or_one** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：integral_one_sub_of_ae_eq_zero_or_one (hXmeas : AEMeasurable X μ) (hX : fo
rallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) : ∫ ω, 1 - X ω ∂μ = μ.real {ω | X ω = 0}
参数：hXmeas : AEMeasurable X μ；hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_of_ae_eq_zero_or_one`：integral_of_ae_eq_zero_or_o
ne (hXmeas : AEMeasurable X μ) (hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) : μ[X] = μ
.real {ω | X ω = 1}
· 使用定理 `AEMeasurable.sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSpac
e G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   {μ : MeasureTheory
.Measu…
· 使用定理 `ContinuousSub.measurableSub₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Sub γ] [Con…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a random variable is ae equal to `0` or `1`, then one minus its expectation i
s equal to the
probability that it equals `0`.
-/
lemma integral_one_sub_of_ae_eq_zero_or_one (hXmeas : AEMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) : ∫ ω, 1 - X ω ∂μ = μ.real {ω | X ω = 0} := by
  calc
    _ = μ.real {ω | 1 - X ω = 1} :=
      integral_of_ae_eq_zero_or_one (aemeasurable_const (b := 1).sub hXmeas)
        (by simpa [sub_eq_zero, or_comm, eq_comm (a := (1 : ℝ))] using hX)
    _ = μ.real {ω | X ω = 0} := by simp

end MeasureTheory


namespace ProbabilityTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure ℝ} {P : Measure Ω}

/-- If a random variable is ae equal to `0` or `1`, then its conditional variance is the product of
the conditional probabilities that it's equal to `0` and that it's equal to `1`. -/
/-
**ProbabilityTheory.condVar_of_ae_eq_zero_or_one** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：condVar_of_ae_eq_zero_or_one {m₀ : MeasurableSpace Ω} (hm : m <= m₀) {μ : 
Measure[m₀] Ω} [IsFiniteMeasure μ] (hXmeas : AEMeasurable[m₀] X μ) (hX : forallᵐ
 ω ∂μ, X ω = 0 ∨ X ω = 1) : Var[X; μ | m] =ᵐ[μ] μ[X | m] * μ[1 - X | m]
参数：hm : m <= m₀；hXmeas : AEMeasurable[m₀] X μ；hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω =
 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp`：condVar_ae_eq
_condExp_sq_sub_sq_condExp (hm : m <= m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
 : Var[X; μ | m] =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] …
· 使用定理 `MeasureTheory.MemLp.of_bound`：∀ {α : Type u_1} {E : Type u_4} {m0 : Meas
urableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup E] [Measur…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `MeasureTheory.ae_eq_rfl`：ae_eq_rfl {f : α -> β} : f =ᵐ[μ] f
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_sub_mul`：one_sub_mul (a b : α) : (1 - a) * b = b - a * b
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If a random variable is ae equal to `0` or `1`, then its conditional variance is
 the product of
the conditional probabilities that it's equal to `0` and that it's equal to `1`.
-/
lemma condVar_of_ae_eq_zero_or_one {m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {μ : Measure[m₀] Ω}
    [IsFiniteMeasure μ] (hXmeas : AEMeasurable[m₀] X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Var[X; μ | m] =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
  wlog hXmeas : Measurable[m₀] X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEMeasurable[m₀] X μ›
    calc
      Var[X; μ | m]
      _ =ᵐ[μ] Var[Y; μ | m] := condVar_congr_ae hXY
      _ =ᵐ[μ] μ[Y | m] * μ[1 - Y | m] := by
        refine this hm hYmeas.aemeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
        refine .mul ?_ ?_ <;>
          exact condExp_congr_ae <| by filter_upwards [hXY] with ω hω; simp [hω]
  calc
    _ =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2 :=
      condVar_ae_eq_condExp_sq_sub_sq_condExp hm <| .of_bound hXmeas.aestronglyMeasurable 1 <| by
        filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] - μ[X | m] ^ 2 := by
      refine .sub ?_ ae_eq_rfl
      exact condExp_congr_ae <| by filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
      rw [sq, ← one_sub_mul, mul_comm]
      refine .mul ae_eq_rfl ?_
      calc
        1 - μ[X | m]
        _ = μ[1 | m] - μ[X | m] := by simp [Pi.one_def, hm]
        _ =ᵐ[μ] μ[1 - X | m] := by
          refine (condExp_sub (integrable_const _)
            (.of_bound (C := 1) hXmeas.aestronglyMeasurable ?_) _).symm
          filter_upwards [hX]
          rintro ω (hω | hω) <;> simp [hω]

/-- If a random variable is ae equal to `0` or `1`, then its variance is the product of
the probabilities that it's equal to `0` and that it's equal to `1`. -/
/-
**ProbabilityTheory.variance_of_ae_eq_zero_or_one** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：variance_of_ae_eq_zero_or_one {μ : Measure Ω} [IsZeroOrProbabilityMeasure 
μ] (hXmeas : AEMeasurable X μ) (hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) : Var[X; μ
] = μ.real {ω | X ω = 0} * μ.real {ω | X ω = 1}
参数：hXmeas : AEMeasurable X μ；hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.eq_zero_or_isProbabilityMeasure`：eq_zero_or_isProbabilityM
easure : μ = 0 ∨ IsProbabilityMeasure μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.variance_zero_measure`：∀ {Ω : Type u_1} {mΩ : Measurab
leSpace Ω} {X : Ω → ℝ}, ProbabilityTheory.variance X 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.condVar_bot`：condVar_bot [IsProbabilityMeasure μ] (hX 
: AEMeasurable X μ) : Var[X; μ | ⊥] = fun _ω => Var[X; μ]
· 使用定理 `MeasureTheory.condExp_bot`：condExp_bot [IsProbabilityMeasure μ] (f : α -
> E) : μ[f | ⊥] = fun _ => ∫ x, f x ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.integral_of_ae_eq_zero_or_one`：integral_of_ae_eq_zero_or_o
ne (hXmeas : AEMeasurable X μ) (hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) : μ[X] = μ
.real {ω | X ω = 1}
· 使用引理 `MeasureTheory.integral_one_sub_of_ae_eq_zero_or_one`：integral_one_sub_of
_ae_eq_zero_or_one (hXmeas : AEMeasurable X μ) (hX : forallᵐ ω ∂μ, X ω = 0 ∨ X ω
 = 1) : ∫ ω, 1 - X ω ∂μ = μ.real {ω | X ω…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.Measure.ae.neBot`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [NeZero μ], (MeasureTheory.ae μ).NeBot
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用引理 `ProbabilityTheory.condVar_of_ae_eq_zero_or_one`：condVar_of_ae_eq_zero_or
_one {m₀ : MeasurableSpace Ω} (hm : m <= m₀) {μ : Measure[m₀] Ω} [IsFiniteMeasur
e μ] (hXmeas : AEMeasurable[m₀] X μ)…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…

--- 原说明 ---
If a random variable is ae equal to `0` or `1`, then its variance is the product
 of
the probabilities that it's equal to `0` and that it's equal to `1`.
-/
lemma variance_of_ae_eq_zero_or_one {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    (hXmeas : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Var[X; μ] = μ.real {ω | X ω = 0} * μ.real {ω | X ω = 1} := by
  obtain rfl | hμ := eq_zero_or_isProbabilityMeasure μ
  · simp
  simpa [Pi.mul_def, integral_of_ae_eq_zero_or_one, integral_one_sub_of_ae_eq_zero_or_one, mul_comm,
    *] using condVar_of_ae_eq_zero_or_one bot_le hXmeas hX

end ProbabilityTheory

