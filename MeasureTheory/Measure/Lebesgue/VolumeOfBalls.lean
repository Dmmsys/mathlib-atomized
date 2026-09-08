/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Volume of balls

Let `E` be a finite-dimensional normed `ℝ`-vector space equipped with a Haar measure `μ`. We
prove that
`μ (Metric.ball 0 1) = (∫ (x : E), Real.exp (- ‖x‖ ^ p) ∂μ) / Real.Gamma (finrank ℝ E / p + 1)`
for any real number `p` with `0 < p`, see `MeasureTheory.measure_unitBall_eq_integral_div_gamma`. We
also prove the corresponding result to compute `μ {x : E | g x < 1}` where `g : E → ℝ` is a function
defining a norm on `E`, see `MeasureTheory.measure_lt_one_eq_integral_div_gamma`.

Using these formulas, we compute the volume of the unit balls in several cases.

* `MeasureTheory.volume_sum_rpow_lt` / `MeasureTheory.volume_sum_rpow_le`: volume of the open and
  closed balls for the norm `Lp` over a real finite-dimensional vector space with `1 ≤ p`. These
  are computed as `volume {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) < r}` and
  `volume {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) ≤ r}` since the spaces `PiLp` do not have a
  `MeasureSpace` instance.

* `Complex.volume_sum_rpow_lt_one` / `Complex.volume_sum_rpow_lt`: same as above but for complex
  finite-dimensional vector space.

* `EuclideanSpace.volume_ball` / `EuclideanSpace.volume_closedBall` : volume of open and closed
  balls in a finite-dimensional Euclidean space.

* `InnerProductSpace.volume_ball` / `InnerProductSpace.volume_closedBall`: volume of open and closed
  balls in a finite-dimensional real inner product space.

* `Complex.volume_ball` / `Complex.volume_closedBall`: volume of open and closed balls in `ℂ`.
-/

public section

section general_case

open MeasureTheory MeasureTheory.Measure Module ENNReal

/-
**MeasureTheory.measure_unitBall_eq_integral_div_gamma** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：MeasureTheory.measure_unitBall_eq_integral_div_gamma {E : Type*} {p : Real
} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E] [Measur
ableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (hp : 0 < p) : 
μ (Metric.ball 0 1) = .ofReal ((∫ (x : E), Real.exp (-‖x‖ ^ p) ∂μ) / Real.Gamma 
(finrank Real E / p + 1))
参数：μ : Measure E；hp : 0 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Nonempty.eq_zero`：∀ {α : Type u_1} [Subsingleton α] [inst : Zero α] 
{s : Set α}, s.Nonempty → s = {0}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.nonempty_ball`：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `MeasureTheory.integral_singleton`：integral_singleton [MeasurableSingleto
nClass α] {μ : Measure α} (f : α -> E) (a : α) : ∫ a in {a}, f a ∂μ = μ.real {a}
 • f a
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
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.instOfFiniteOfDiscreteTopology`：∀ {Y : Type u_2} [Fin
ite Y] [inst : UniformSpace Y] [DiscreteTopology Y], DiscreteUniformity Y
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
（共 135 条，此处仅展示前 30 条）
-/
theorem MeasureTheory.measure_unitBall_eq_integral_div_gamma {E : Type*} {p : ℝ}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (hp : 0 < p) :
    μ (Metric.ball 0 1) =
      .ofReal ((∫ (x : E), Real.exp (-‖x‖ ^ p) ∂μ) / Real.Gamma (finrank ℝ E / p + 1)) := by
  obtain hE | hE := subsingleton_or_nontrivial E
  · rw [(Metric.nonempty_ball.mpr zero_lt_one).eq_zero, ← setIntegral_univ,
      Set.univ_nonempty.eq_zero, integral_singleton, finrank_zero_of_subsingleton, Nat.cast_zero,
      zero_div, zero_add, Real.Gamma_one, div_one, norm_zero, Real.zero_rpow hp.ne', neg_zero,
      Real.exp_zero, smul_eq_mul, mul_one, measureReal_def, ofReal_toReal (measure_ne_top μ {0})]
  · have : (0 : ℝ) < finrank ℝ E := Nat.cast_pos.mpr finrank_pos
    have : ((∫ y in Set.Ioi (0 : ℝ), y ^ (finrank ℝ E - 1) • Real.exp (-y ^ p)) /
        Real.Gamma ((finrank ℝ E) / p + 1)) * (finrank ℝ E) = 1 := by
      simp_rw [← Real.rpow_natCast _ (finrank ℝ E - 1), smul_eq_mul, Nat.cast_sub finrank_pos,
        Nat.cast_one]
      rw [integral_rpow_mul_exp_neg_rpow hp (by linarith), sub_add_cancel,
        Real.Gamma_add_one (ne_of_gt (by positivity))]
      field
    rw [integral_fun_norm_addHaar μ (fun x => Real.exp (-x ^ p)), nsmul_eq_mul, smul_eq_mul,
      mul_div_assoc, mul_div_assoc, mul_comm, mul_assoc, this, mul_one, ofReal_measureReal _]
    exact ne_of_lt measure_ball_lt_top

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] [mE : MeasurableSpace E]
  [tE : TopologicalSpace E] [IsTopologicalAddGroup E] [BorelSpace E] [T2Space E]
  [ContinuousSMul ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {g : E → ℝ} (h1 : g 0 = 0)
  (h2 : ∀ x, g (-x) = g x) (h3 : ∀ x y, g (x + y) ≤ g x + g y) (h4 : ∀ {x}, g x = 0 → x = 0)
  (h5 : ∀ r x, g (r • x) ≤ |r| * (g x))
include h1 h2 h3 h4 h5
/-
**MeasureTheory.measure_lt_one_eq_integral_div_gamma** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：MeasureTheory.measure_lt_one_eq_integral_div_gamma {p : Real} (hp : 0 < p)
 : μ {x : E | g x < 1} = .ofReal ((∫ (x : E), Real.exp (-(g x) ^ p) ∂μ) / Real.G
amma (finrank Real E / p + 1))
参数：hp : 0 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `measurableSet_ball`：measurableSet_ball : MeasurableSet (Metric.ball x ε)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Measurable.measurePreserving`：∀ {α : Type u_1} {β : Type u_2} [inst : Me
asurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measurable f → ∀ (μ
a : MeasureTheory.…
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp'`：∀ {α : Type u_1} {G : Ty
pe u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : Measurable
Space α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.measure_unitBall_eq_integral_div_gamma`：MeasureTheory.meas
ure_unitBall_eq_integral_div_gamma {E : Type*} {p : Real} [NormedAddCommGroup E]
 [NormedSpace Real E] [FiniteDimensional R…
· 使用定理 `ContinuousLinearEquiv.isAddHaarMeasure_map`：∀ {E : Type u_3} {F : Type u
_4} {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S]   [i
nst_2 : AddCommGroup E] [inst_3 …
-/
theorem MeasureTheory.measure_lt_one_eq_integral_div_gamma {p : ℝ} (hp : 0 < p) :
    μ {x : E | g x < 1} =
      .ofReal ((∫ (x : E), Real.exp (-(g x) ^ p) ∂μ) / Real.Gamma (finrank ℝ E / p + 1)) := by
  -- We copy `E` to a new type `F` on which we will put the norm defined by `g`
  let F : Type _ := E
  let p : AddGroupNorm F := ⟨⟨g, h1, h3, h2⟩, fun x hx ↦ h4 hx⟩
  let : NormedAddCommGroup F := AddGroupNorm.toNormedAddCommGroup p
  let : NormedSpace ℝ F := { norm_smul_le := fun _ _ ↦ h5 _ _ }
  -- We put the new topology on F
  let : TopologicalSpace F := UniformSpace.toTopologicalSpace
  let : MeasurableSpace F := borel F
  have : BorelSpace F := { measurable_eq := rfl }
  -- The map between `E` and `F` as a continuous linear equivalence
  let φ := @LinearEquiv.toContinuousLinearEquiv ℝ _ E _ _ tE _ _ F _ _ _ _ _ _ _ _ _
    (LinearEquiv.refl ℝ E : E ≃ₗ[ℝ] F)
  -- The measure `ν` is the measure on `F` defined by `μ`
  -- Since we have two different topologies, it is necessary to specify the topology of E
  let ν : Measure F := @Measure.map E F mE _ φ μ
  convert! (measure_unitBall_eq_integral_div_gamma ν hp) using 1
  · rw [@Measure.map_apply E F mE _ μ φ _ _ measurableSet_ball]
    · congr!
      simp_rw [Metric.ball, dist_zero_right]
      rfl
    · refine @Continuous.measurable E F tE mE _ _ _ _ φ ?_
      exact @ContinuousLinearEquiv.continuous ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ
  · -- The map between `E` and `F` as a measurable equivalence
    let ψ := @Homeomorph.toMeasurableEquiv E F tE mE _ _ _ _
      (@ContinuousLinearEquiv.toHomeomorph ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ)
    -- The map `ψ` is measure preserving by construction
    have : @MeasurePreserving E F mE _ ψ μ ν :=
      @Measurable.measurePreserving E F mE _ ψ (@MeasurableEquiv.measurable E F mE _ ψ) _
    rw [← this.integral_comp']
    rfl
/-
**MeasureTheory.measure_le_eq_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.measure_le_eq_lt [Nontrivial E] (r : Real) : μ {x : E | g x 
<= r} = μ {x : E | g x < r}
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `measurableSet_closedBall`：measurableSet_closedBall : MeasurableSet (Metr
ic.closedBall x ε)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `measurableSet_ball`：measurableSet_ball : MeasurableSet (Metric.ball x ε)
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball`：addHaar_closed
Ball_eq_addHaar_ball [Nontrivial E] (x : E) (r : Real) : μ (closedBall x r) = μ 
(ball x r)
· 使用定理 `ContinuousLinearEquiv.isAddHaarMeasure_map`：∀ {E : Type u_3} {F : Type u
_4} {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S]   [i
nst_2 : AddCommGroup E] [inst_3 …
-/
theorem MeasureTheory.measure_le_eq_lt [Nontrivial E] (r : ℝ) :
    μ {x : E | g x ≤ r} = μ {x : E | g x < r} := by
  -- We copy `E` to a new type `F` on which we will put the norm defined by `g`
  let F : Type _ := E
  let p : AddGroupNorm F := ⟨⟨g, h1, h3, h2⟩, fun x hx ↦ h4 hx⟩
  let : NormedAddCommGroup F := AddGroupNorm.toNormedAddCommGroup p
  let : NormedSpace ℝ F := { norm_smul_le := fun _ _ ↦ h5 _ _ }
  -- We put the new topology on F
  let : TopologicalSpace F := UniformSpace.toTopologicalSpace
  let : MeasurableSpace F := borel F
  have : BorelSpace F := { measurable_eq := rfl }
  -- The map between `E` and `F` as a continuous linear equivalence
  let φ := @LinearEquiv.toContinuousLinearEquiv ℝ _ E _ _ tE _ _ F _ _ _ _ _ _ _ _ _
    (LinearEquiv.refl ℝ E : E ≃ₗ[ℝ] F)
  -- The measure `ν` is the measure on `F` defined by `μ`
  -- Since we have two different topologies, it is necessary to specify the topology of E
  let ν : Measure F := @Measure.map E F mE _ φ μ
  convert! addHaar_closedBall_eq_addHaar_ball ν 0 r using 1
  · rw [@Measure.map_apply E F mE _ μ φ _ _ measurableSet_closedBall]
    · congr!
      simp_rw [Metric.closedBall, dist_zero_right]
      rfl
    · refine @Continuous.measurable E F tE mE _ _ _ _ φ ?_
      exact @ContinuousLinearEquiv.continuous ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ
  · rw [@Measure.map_apply E F mE _ μ φ _ _ measurableSet_ball]
    · congr!
      simp_rw [Metric.ball, dist_zero_right]
      rfl
    · refine @Continuous.measurable E F tE mE _ _ _ _ φ ?_
      exact @ContinuousLinearEquiv.continuous ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ

end general_case

section LpSpace

open Real Fintype ENNReal Module MeasureTheory MeasureTheory.Measure WithLp

variable (ι : Type*) [Fintype ι] {p : ℝ}

/-
**MeasureTheory.volume_sum_rpow_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.volume_sum_rpow_lt_one (hp : 1 <= p) : volume {x : ι -> Real
 | ∑ i, |x i| ^ p < 1} = .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card
 ι / p + 1))
参数：hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 107 条，此处仅展示前 30 条）
-/
theorem MeasureTheory.volume_sum_rpow_lt_one (hp : 1 ≤ p) :
    volume {x : ι → ℝ | ∑ i, |x i| ^ p < 1} =
      .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  have h₂ : ∀ x : ι → ℝ, 0 ≤ ∑ i, |x i| ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg (abs_nonneg _) _) _
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm (x : ι → ℝ) : ‖toLp (.ofReal p) x‖ = (∑ i, |x i| ^ p) ^ (1 / p) := by
    simp [PiLp.norm_eq_sum (f := toLp (.ofReal p) x) (this.symm ▸ h₁), this]
  have : Fact (1 ≤ ENNReal.ofReal p) := fact_iff.mpr (ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero : ‖toLp (.ofReal p) (0 : ι → ℝ)‖ = 0 := norm_zero
  have eq_zero (x : ι → ℝ) : ‖toLp (.ofReal p) x‖ = 0 ↔ x = 0 :=
    norm_eq_zero.trans (toLp_eq_zero _)
  have nm_neg := fun x : ι → ℝ => norm_neg (toLp (.ofReal p) x)
  have nm_add := fun x y : ι → ℝ => norm_add_le (toLp (.ofReal p) x) (toLp (.ofReal p) y)
  have nm_smul := fun (r : ℝ) (x : ι → ℝ) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => ℝ)) r (toLp (.ofReal p) x)
  simp_rw [← toLp_neg, ← toLp_add, ← toLp_smul, eq_norm,
    norm_eq_abs] at eq_zero nm_zero nm_neg nm_add nm_smul
  -- We use `measure_lt_one_eq_integral_div_gamma` with `g` equals to the norm `L_p`
  convert!
    (measure_lt_one_eq_integral_div_gamma (volume : Measure (ι → ℝ)) (g := fun x =>
      (∑ i, |x i| ^ p) ^ (1 / p)) nm_zero nm_neg nm_add (eq_zero _).mp (fun r x => nm_smul r x)
      (by linarith : 0 < p)) using 4
  · rw [rpow_lt_one_iff' _ (one_div_pos.mpr h₁)]
    exact Finset.sum_nonneg' (fun _ => rpow_nonneg (abs_nonneg _) _)
  · simp_rw [← rpow_mul (h₂ _), div_mul_cancel₀ _ (ne_of_gt h₁), Real.rpow_one,
      ← Finset.sum_neg_distrib, exp_sum]
    rw [integral_fintype_prod_volume_eq_pow fun x : ℝ => exp (- |x| ^ p), integral_comp_abs
      (f := fun x => exp (- x ^ p)), integral_exp_neg_rpow h₁]
  · rw [finrank_fintype_fun_eq_card]
/-
**MeasureTheory.volume_sum_rpow_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.volume_sum_rpow_lt [Nonempty ι] {p : Real} (hp : 1 <= p) (r 
: Real) : volume {x : ι -> Real | (∑ i, |x i| ^ p) ^ (1 / p) < r} = (.ofReal r) 
^ card ι * .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card ι / p + 1))
参数：hp : 1 <= p；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.zero_eq_ofReal`：zero_eq_ofReal {p : Real} : 0 = ENNReal.ofReal p
 ↔ p <= 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fin.pos'`：∀ {n : ℕ} [Nonempty (Fin n)], 0 < n
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Fintype.instNeZeroNatCardOfNonempty`：∀ {α : Type u_1} [inst : Fintype α]
 [Nonempty α], NeZero (Fintype.card α)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MeasureTheory.volume_sum_rpow_lt_one`：MeasureTheory.volume_sum_rpow_lt_o
ne (hp : 1 <= p) : volume {x : ι -> Real | ∑ i, |x i| ^ p < 1} = .ofReal ((2 * G
amma (1 / p + 1)) ^ card ι…
· 使用定理 `ENNReal.ofReal_pow`：ofReal_pow {p : Real} (hp : 0 <= p) (n : Nat) : ENNR
eal.ofReal (p ^ n) = ENNReal.ofReal p ^ n
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Module.finrank_pi`：Module.finrank_pi {ι : Type v} [Fintype ι] : finrank 
R (ι -> R) = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
（共 105 条，此处仅展示前 30 条）
-/
theorem MeasureTheory.volume_sum_rpow_lt [Nonempty ι] {p : ℝ} (hp : 1 ≤ p) (r : ℝ) :
    volume {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) < r} = (.ofReal r) ^ card ι *
      .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card ι / p + 1)) := by
  have h₁ (x : ι → ℝ) : 0 ≤ ∑ i, |x i| ^ p := by positivity
  have h₂ : ∀ x : ι → ℝ, 0 ≤ (∑ i, |x i| ^ p) ^ (1 / p) := fun x => rpow_nonneg (h₁ x) _
  obtain hr | hr := le_or_gt r 0
  · have : {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) < r} = ∅ := by
      ext x
      refine ⟨fun hx => ?_, fun hx => hx.elim⟩
      exact not_le.mpr (lt_of_lt_of_le (Set.mem_ofPred.mp hx) hr) (h₂ x)
    rw [this, measure_empty, ← zero_eq_ofReal.mpr hr, zero_pow Fin.pos'.ne', zero_mul]
  · rw [← volume_sum_rpow_lt_one _ hp, ← ofReal_pow (le_of_lt hr), ← finrank_pi ℝ]
    convert! addHaar_smul_of_nonneg volume (le_of_lt hr) {x : ι → ℝ | ∑ i, |x i| ^ p < 1} using 2
    simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hr), Set.preimage_ofPred_eq, Pi.smul_apply,
      smul_eq_mul, abs_mul, mul_rpow (abs_nonneg _) (abs_nonneg _), abs_inv,
      inv_rpow (abs_nonneg _), ← Finset.mul_sum, abs_eq_self.mpr (le_of_lt hr),
      inv_mul_lt_iff₀ (rpow_pos_of_pos hr _), mul_one, ← rpow_lt_rpow_iff
      (rpow_nonneg (h₁ _) _) (le_of_lt hr) (by linarith : 0 < p), ← rpow_mul
      (h₁ _), div_mul_cancel₀ _ (ne_of_gt (by linarith) : p ≠ 0), Real.rpow_one]
/-
**MeasureTheory.volume_sum_rpow_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.volume_sum_rpow_le [Nonempty ι] {p : Real} (hp : 1 <= p) (r 
: Real) : volume {x : ι -> Real | (∑ i, |x i| ^ p) ^ (1 / p) <= r} = (.ofReal r)
 ^ card ι * .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card ι / p + 1))
参数：hp : 1 <= p；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 85 条，此处仅展示前 30 条）
-/
theorem MeasureTheory.volume_sum_rpow_le [Nonempty ι] {p : ℝ} (hp : 1 ≤ p) (r : ℝ) :
    volume {x : ι → ℝ | (∑ i, |x i| ^ p) ^ (1 / p) ≤ r} = (.ofReal r) ^ card ι *
      .ofReal ((2 * Gamma (1 / p + 1)) ^ card ι / Gamma (card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  -- We collect facts about `Lp` norms that will be used in `measure_le_one_eq_lt_one`
  have eq_norm (x : ι → ℝ) : ‖toLp (.ofReal p) x‖ = (∑ i, |x i| ^ p) ^ (1 / p) := by
    simp [PiLp.norm_eq_sum (f := toLp (.ofReal p) x) (this.symm ▸ h₁), this]
  have : Fact (1 ≤ ENNReal.ofReal p) := fact_iff.mpr (ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero : ‖toLp (.ofReal p) (0 : ι → ℝ)‖ = 0 := norm_zero
  have eq_zero (x : ι → ℝ) : ‖toLp (.ofReal p) x‖ = 0 ↔ x = 0 :=
    norm_eq_zero.trans (toLp_eq_zero _)
  have nm_neg := fun x : ι → ℝ => norm_neg (toLp (.ofReal p) x)
  have nm_add := fun x y : ι → ℝ => norm_add_le (toLp (.ofReal p) x) (toLp (.ofReal p) y)
  have nm_smul := fun (r : ℝ) (x : ι → ℝ) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => ℝ)) r (toLp (.ofReal p) x)
  simp_rw [← toLp_neg, ← toLp_add, ← toLp_smul, eq_norm,
    norm_eq_abs] at eq_zero nm_zero nm_neg nm_add nm_smul
  rw [measure_le_eq_lt _ nm_zero (fun x ↦ nm_neg x) (fun x y ↦ nm_add x y) (eq_zero _).mp
    (fun r x => nm_smul r x), volume_sum_rpow_lt _ hp]
/-
**Complex.volume_sum_rpow_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.volume_sum_rpow_lt_one {p : Real} (hp : 1 <= p) : volume {x : ι ->
 Complex | ∑ i, ‖x i‖ ^ p < 1} = .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι 
/ Real.Gamma (2 * card ι / p + 1))
参数：hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 113 条，此处仅展示前 30 条）
-/
theorem Complex.volume_sum_rpow_lt_one {p : ℝ} (hp : 1 ≤ p) :
    volume {x : ι → ℂ | ∑ i, ‖x i‖ ^ p < 1} =
      .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  have h₂ : ∀ x : ι → ℂ, 0 ≤ ∑ i, ‖x i‖ ^ p := by
    refine fun _ => Finset.sum_nonneg' ?_
    exact fun i => (fun _ => rpow_nonneg (norm_nonneg _) _) _
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm (x : ι → ℂ) : ‖toLp (.ofReal p) x‖ = (∑ i, ‖x i‖ ^ p) ^ (1 / p) := by
    simp [PiLp.norm_eq_sum (f := toLp (.ofReal p) x) (this.symm ▸ h₁), this]
  have : Fact (1 ≤ ENNReal.ofReal p) := fact_iff.mpr (ENNReal.ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero : ‖toLp (.ofReal p) (0 : ι → ℂ)‖ = 0 := norm_zero
  have eq_zero (x : ι → ℂ) : ‖toLp (.ofReal p) x‖ = 0 ↔ x = 0 :=
    norm_eq_zero.trans (toLp_eq_zero _)
  have nm_neg := fun x : ι → ℂ => norm_neg (toLp (.ofReal p) x)
  have nm_add := fun x y : ι → ℂ => norm_add_le (toLp (.ofReal p) x) (toLp (.ofReal p) y)
  have nm_smul := fun (r : ℝ) (x : ι → ℂ) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => ℂ)) r (toLp (.ofReal p) x)
  simp_rw [← toLp_neg, ← toLp_add, ← toLp_smul, eq_norm] at eq_zero nm_zero nm_neg nm_add nm_smul
  -- We use `measure_lt_one_eq_integral_div_gamma` with `g` equals to the norm `L_p`
  convert!
    measure_lt_one_eq_integral_div_gamma (volume : Measure (ι → ℂ)) (g := fun x =>
      (∑ i, ‖x i‖ ^ p) ^ (1 / p)) nm_zero nm_neg nm_add (eq_zero _).mp (fun r x => nm_smul r x)
      (by linarith : 0 < p) using 4
  · rw [rpow_lt_one_iff' _ (one_div_pos.mpr h₁)]
    exact Finset.sum_nonneg' (fun _ => rpow_nonneg (norm_nonneg _) _)
  · simp_rw [← rpow_mul (h₂ _), div_mul_cancel₀ _ (ne_of_gt h₁), Real.rpow_one,
      ← Finset.sum_neg_distrib, Real.exp_sum]
    rw [integral_fintype_prod_volume_eq_pow fun x : ℂ => Real.exp (- ‖x‖ ^ p),
      Complex.integral_exp_neg_rpow hp]
  · rw [finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, smul_eq_mul,
      Nat.cast_mul, Nat.cast_ofNat, Fintype.card, mul_comm]
/-
**Complex.volume_sum_rpow_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.volume_sum_rpow_lt [Nonempty ι] {p : Real} (hp : 1 <= p) (r : Real
) : volume {x : ι -> Complex | (∑ i, ‖x i‖ ^ p) ^ (1 / p) < r} = (.ofReal r) ^ (
2 * card ι) * .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * c
ard ι / p + 1))
参数：hp : 1 <= p；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.zero_eq_ofReal`：zero_eq_ofReal {p : Real} : 0 = ENNReal.ofReal p
 ↔ p <= 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fin.pos'`：∀ {n : ℕ} [Nonempty (Fin n)], 0 < n
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHMul`：∀ {n m : ℕ} [hn : NeZero n] [hm : NeZero m], NeZero (
n * m)
· 使用定理 `Fintype.instNeZeroNatCardOfNonempty`：∀ {α : Type u_1} [inst : Fintype α]
 [Nonempty α], NeZero (Fintype.card α)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.volume_sum_rpow_lt_one`：Complex.volume_sum_rpow_lt_one {p : Real
} (hp : 1 <= p) : volume {x : ι -> Complex | ∑ i, ‖x i‖ ^ p < 1} = .ofReal ((π *
 Real.Gamma (2 / p +…
· 使用定理 `ENNReal.ofReal_pow`：ofReal_pow {p : Real} (hp : 0 <= p) (n : Nat) : ENNR
eal.ofReal (p ^ n) = ENNReal.ofReal p ^ n
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 122 条，此处仅展示前 30 条）
-/
theorem Complex.volume_sum_rpow_lt [Nonempty ι] {p : ℝ} (hp : 1 ≤ p) (r : ℝ) :
    volume {x : ι → ℂ | (∑ i, ‖x i‖ ^ p) ^ (1 / p) < r} = (.ofReal r) ^ (2 * card ι) *
      .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * card ι / p + 1)) := by
  have h₁ (x : ι → ℂ) : 0 ≤ ∑ i, ‖x i‖ ^ p := by positivity
  have h₂ : ∀ x : ι → ℂ, 0 ≤ (∑ i, ‖x i‖ ^ p) ^ (1 / p) := fun x => rpow_nonneg (h₁ x) _
  obtain hr | hr := le_or_gt r 0
  · have : {x : ι → ℂ | (∑ i, ‖x i‖ ^ p) ^ (1 / p) < r} = ∅ := by
      ext x
      refine ⟨fun hx => ?_, fun hx => hx.elim⟩
      exact not_le.mpr (lt_of_lt_of_le (Set.mem_ofPred.mp hx) hr) (h₂ x)
    rw [this, measure_empty, ← zero_eq_ofReal.mpr hr, zero_pow Fin.pos'.ne', zero_mul]
  · rw [← Complex.volume_sum_rpow_lt_one _ hp, ← ENNReal.ofReal_pow (le_of_lt hr)]
    convert! addHaar_smul_of_nonneg volume (le_of_lt hr) {x : ι → ℂ | ∑ i, ‖x i‖ ^ p < 1} using 2
    · simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hr), Set.preimage_ofPred_eq, Pi.smul_apply,
        norm_smul, mul_rpow (norm_nonneg _) (norm_nonneg _), Real.norm_eq_abs, abs_inv, inv_rpow
        (abs_nonneg _), ← Finset.mul_sum, abs_eq_self.mpr (le_of_lt hr), inv_mul_lt_iff₀
        (rpow_pos_of_pos hr _), mul_one, ← rpow_lt_rpow_iff (rpow_nonneg (h₁ _) _)
        (le_of_lt hr) (by linarith : 0 < p), ← rpow_mul (h₁ _), div_mul_cancel₀ _
        (ne_of_gt (by linarith) : p ≠ 0), Real.rpow_one]
    · simp_rw [finrank_pi_fintype ℝ, Complex.finrank_real_complex, Finset.sum_const, smul_eq_mul,
        mul_comm, Fintype.card]
/-
**Complex.volume_sum_rpow_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.volume_sum_rpow_le [Nonempty ι] {p : Real} (hp : 1 <= p) (r : Real
) : volume {x : ι -> Complex | (∑ i, ‖x i‖ ^ p) ^ (1 / p) <= r} = (.ofReal r) ^ 
(2 * card ι) * .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * 
card ι / p + 1))
参数：hp : 1 <= p；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 86 条，此处仅展示前 30 条）
-/
theorem Complex.volume_sum_rpow_le [Nonempty ι] {p : ℝ} (hp : 1 ≤ p) (r : ℝ) :
    volume {x : ι → ℂ | (∑ i, ‖x i‖ ^ p) ^ (1 / p) ≤ r} = (.ofReal r) ^ (2 * card ι) *
      .ofReal ((π * Real.Gamma (2 / p + 1)) ^ card ι / Real.Gamma (2 * card ι / p + 1)) := by
  have h₁ : 0 < p := by linarith
  have : (ENNReal.ofReal p).toReal = p := toReal_ofReal (le_of_lt h₁)
  -- We collect facts about `Lp` norms that will be used in `measure_lt_one_eq_integral_div_gamma`
  have eq_norm (x : ι → ℂ) : ‖toLp (.ofReal p) x‖ = (∑ i, ‖x i‖ ^ p) ^ (1 / p) := by
    simp [PiLp.norm_eq_sum (f := toLp (.ofReal p) x) (this.symm ▸ h₁), this]
  have : Fact (1 ≤ ENNReal.ofReal p) := fact_iff.mpr (ENNReal.ofReal_one ▸ (ofReal_le_ofReal hp))
  have nm_zero : ‖toLp (.ofReal p) (0 : ι → ℂ)‖ = 0 := norm_zero
  have eq_zero (x : ι → ℂ) : ‖toLp (.ofReal p) x‖ = 0 ↔ x = 0 :=
    norm_eq_zero.trans (toLp_eq_zero _)
  have nm_neg := fun x : ι → ℂ => norm_neg (toLp (.ofReal p) x)
  have nm_add := fun x y : ι → ℂ => norm_add_le (toLp (.ofReal p) x) (toLp (.ofReal p) y)
  have nm_smul := fun (r : ℝ) (x : ι → ℂ) =>
    norm_smul_le (β := PiLp (.ofReal p) (fun _ : ι => ℂ)) r (toLp (.ofReal p) x)
  simp_rw [← toLp_neg, ← toLp_add, ← toLp_smul, eq_norm] at eq_zero nm_zero nm_neg nm_add nm_smul
  rw [measure_le_eq_lt _ nm_zero (fun x ↦ nm_neg x) (fun x y ↦ nm_add x y) (eq_zero _).mp
    (fun r x => nm_smul r x), Complex.volume_sum_rpow_lt _ hp]

end LpSpace

namespace EuclideanSpace

variable (ι : Type*) [Nonempty ι] [Fintype ι]

open Fintype Real MeasureTheory MeasureTheory.Measure ENNReal

/-
**EuclideanSpace.volume_ball** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanSpace`。
形式化陈述：volume_ball (x : EuclideanSpace Real ι) (r : Real) : volume (Metric.ball x
 r) = (.ofReal r) ^ card ι * .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1))
参数：x : EuclideanSpace Real ι；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ball_eq_empty`：ball_eq_empty : ball x ε = ∅ ↔ ε <= 0
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.zero_eq_ofReal`：zero_eq_ofReal {p : Real} : 0 = ENNReal.ofReal p
 ↔ p <= 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `PiLp.volume_preserving_toLp`：PiLp.volume_preserving_toLp : MeasurePreser
ving (@toLp 2 (ι -> Real))
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `measurableSet_ball`：measurableSet_ball : MeasurableSet (Metric.ball x ε)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EuclideanSpace.ball_zero_eq`：EuclideanSpace.ball_zero_eq {n : Type*} [Fi
ntype n] (r : Real) (hr : 0 <= r) : Metric.ball (0 : EuclideanSpace Real n) r = 
{x | ∑ i, x i ^ 2…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
（共 51 条，此处仅展示前 30 条）
-/
theorem volume_ball (x : EuclideanSpace ℝ ι) (r : ℝ) :
    volume (Metric.ball x r) = (.ofReal r) ^ card ι *
      .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1)) := by
  obtain hr | hr := le_total r 0
  · rw [Metric.ball_eq_empty.mpr hr, measure_empty, ← zero_eq_ofReal.mpr hr, zero_pow card_ne_zero,
      zero_mul]
  · suffices volume (Metric.ball (0 : EuclideanSpace ℝ ι) 1) =
        .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1)) by
      rw [Measure.addHaar_ball _ _ hr, this, ofReal_pow hr, finrank_euclideanSpace]
    rw [← (PiLp.volume_preserving_toLp ι).measure_preimage
      measurableSet_ball.nullMeasurableSet]
    simp only [Set.preimage, ball_zero_eq _ zero_le_one, one_pow, Set.mem_ofPred_eq]
    convert! volume_sum_rpow_lt_one ι one_le_two using 4
    · simp [sq_abs]
    · rw [Gamma_add_one (by simp), Gamma_one_half_eq, ← mul_assoc, mul_div_cancel₀ _
        two_ne_zero, one_mul]
/-
**EuclideanSpace.volume_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanSpace`。
形式化陈述：volume_closedBall (x : EuclideanSpace Real ι) (r : Real) : volume (Metric.
closedBall x r) = (.ofReal r) ^ card ι * .ofReal (√π ^ card ι / Gamma (card ι / 
2 + 1))
参数：x : EuclideanSpace Real ι；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball`：addHaar_closed
Ball_eq_addHaar_ball [Nontrivial E] (x : E) (r : Real) : μ (closedBall x r) = μ 
(ball x r)
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `EuclideanSpace.volume_ball`：volume_ball (x : EuclideanSpace Real ι) (r :
 Real) : volume (Metric.ball x r) = (.ofReal r) ^ card ι * .ofReal (√π ^ card ι 
/ Gamma (card ι …
-/
theorem volume_closedBall (x : EuclideanSpace ℝ ι) (r : ℝ) :
    volume (Metric.closedBall x r) = (.ofReal r) ^ card ι *
      .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1)) := by
  rw [addHaar_closedBall_eq_addHaar_ball, EuclideanSpace.volume_ball]

end EuclideanSpace

namespace InnerProductSpace

open scoped Nat
open MeasureTheory MeasureTheory.Measure ENNReal Real Module Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Nontrivial

variable [Nontrivial E]

/-
**InnerProductSpace.volume_ball** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：volume_ball (x : E) (r : Real) : volume (Metric.ball x r) = (.ofReal r) ^ 
finrank Real E * .ofReal (√π ^ finrank Real E / Gamma (finrank Real E / 2 + 1))
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `OrthonormalBasis.measurePreserving_repr_symm`：OrthonormalBasis.measurePr
eserving_repr_symm (b : OrthonormalBasis ι Real F) : MeasurePreserving b.repr.sy
mm volume volume
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `measurableSet_ball`：measurableSet_ball : MeasurableSet (Metric.ball x ε)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.pos_iff_nonempty`：∀ {n : ℕ}, 0 < n ↔ Nonempty (Fin n)
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `EuclideanSpace.volume_ball`：volume_ball (x : EuclideanSpace Real ι) (r :
 Real) : volume (Metric.ball x r) = (.ofReal r) ^ card ι * .ofReal (√π ^ card ι 
/ Gamma (card ι …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearIsometryEquiv.preimage_ball`：preimage_ball (x : E₂) (r : Real) : e
 ⁻¹' Metric.ball x r = Metric.ball (e.symm x) r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
theorem volume_ball (x : E) (r : ℝ) :
    volume (Metric.ball x r) = (.ofReal r) ^ finrank ℝ E *
      .ofReal (√π ^ finrank ℝ E / Gamma (finrank ℝ E / 2 + 1)) := by
  rw [← ((stdOrthonormalBasis ℝ E).measurePreserving_repr_symm).measure_preimage
      measurableSet_ball.nullMeasurableSet]
  have : Nonempty (Fin (finrank ℝ E)) := Fin.pos_iff_nonempty.mp finrank_pos
  have := EuclideanSpace.volume_ball (Fin (finrank ℝ E)) ((stdOrthonormalBasis ℝ E).repr x) r
  simp_rw [Fintype.card_fin] at this
  convert! this
  simp only [LinearIsometryEquiv.preimage_ball, LinearIsometryEquiv.symm_symm]
/-
**InnerProductSpace.volume_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpa
ce`。
形式化陈述：volume_closedBall (x : E) (r : Real) : volume (Metric.closedBall x r) = (.
ofReal r) ^ finrank Real E * .ofReal (√π ^ finrank Real E / Gamma (finrank Real 
E / 2 + 1))
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball`：addHaar_closed
Ball_eq_addHaar_ball [Nontrivial E] (x : E) (r : Real) : μ (closedBall x r) = μ 
(ball x r)
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `InnerProductSpace.volume_ball`：volume_ball (x : E) (r : Real) : volume (
Metric.ball x r) = (.ofReal r) ^ finrank Real E * .ofReal (√π ^ finrank Real E /
 Gamma (finrank Rea…
-/
theorem volume_closedBall (x : E) (r : ℝ) :
    volume (Metric.closedBall x r) = (.ofReal r) ^ finrank ℝ E *
      .ofReal (√π ^ finrank ℝ E / Gamma (finrank ℝ E / 2 + 1)) := by
  rw [addHaar_closedBall_eq_addHaar_ball, InnerProductSpace.volume_ball _]
/-
**InnerProductSpace.volume_ball_of_dim_even** 是 Mathlib 中的一个引理，位于命名空间 `InnerProd
uctSpace`。
形式化陈述：volume_ball_of_dim_even {k : Nat} (hk : finrank Real E = 2 * k) (x : E) (r
 : Real) : volume (ball x r) = .ofReal r ^ finrank Real E * .ofReal (π ^ k / (k 
: Nat)!)
参数：hk : finrank Real E = 2 * k；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.volume_ball`：volume_ball (x : E) (r : Real) : volume (
Metric.ball x r) = (.ofReal r) ^ finrank Real E * .ofReal (√π ^ finrank Real E /
 Gamma (finrank Rea…
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `Real.pi_nonneg`：pi_nonneg : 0 <= π
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.Gamma_nat_eq_factorial`：Gamma_nat_eq_factorial (n : Nat) : Gamma (n
 + 1) = n !
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_ball_of_dim_even {k : ℕ} (hk : finrank ℝ E = 2 * k) (x : E) (r : ℝ) :
    volume (ball x r) = .ofReal r ^ finrank ℝ E * .ofReal (π ^ k / (k : ℕ)!) := by
  rw [volume_ball, hk, pow_mul, pow_mul, sq_sqrt pi_nonneg]
  congr
  simp [Gamma_nat_eq_factorial]
/-
**InnerProductSpace.volume_closedBall_of_dim_even** 是 Mathlib 中的一个引理，位于命名空间 `Inn
erProductSpace`。
形式化陈述：volume_closedBall_of_dim_even {k : Nat} (hk : finrank Real E = 2 * k) (x :
 E) (r : Real) : volume (closedBall x r) = .ofReal r ^ finrank Real E * .ofReal 
(π ^ k / (k : Nat)!)
参数：hk : finrank Real E = 2 * k；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball`：addHaar_closed
Ball_eq_addHaar_ball [Nontrivial E] (x : E) (r : Real) : μ (closedBall x r) = μ 
(ball x r)
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用引理 `InnerProductSpace.volume_ball_of_dim_even`：volume_ball_of_dim_even {k : 
Nat} (hk : finrank Real E = 2 * k) (x : E) (r : Real) : volume (ball x r) = .ofR
eal r ^ finrank Real E * .ofRea…
-/
lemma volume_closedBall_of_dim_even {k : ℕ} (hk : finrank ℝ E = 2 * k) (x : E) (r : ℝ) :
    volume (closedBall x r) = .ofReal r ^ finrank ℝ E * .ofReal (π ^ k / (k : ℕ)!) := by
  rw [addHaar_closedBall_eq_addHaar_ball, volume_ball_of_dim_even hk x]

end Nontrivial

/-
**InnerProductSpace.volume_ball_of_dim_odd** 是 Mathlib 中的一个引理，位于命名空间 `InnerProdu
ctSpace`。
形式化陈述：volume_ball_of_dim_odd {k : Nat} (hk : finrank Real E = 2 * k + 1) (x : E)
 (r : Real) : volume (ball x r) = .ofReal r ^ finrank Real E * .ofReal (π ^ k * 
2 ^ (k + 1) / (finrank Real E : Nat)‼)
参数：hk : finrank Real E = 2 * k + 1；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.nontrivial_of_finrank_pos`：Module.nontrivial_of_finrank_pos (h : 
0 < finrank R M) : Nontrivial M
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.volume_ball`：volume_ball (x : E) (r : Real) : volume (
Metric.ball x r) = (.ofReal r) ^ finrank Real E * .ofReal (√π ^ finrank Real E /
 Gamma (finrank Rea…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `Real.pi_nonneg`：pi_nonneg : 0 <= π
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₂`：div_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval / l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval / ((r₂, x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
（共 64 条，此处仅展示前 30 条）
-/
lemma volume_ball_of_dim_odd {k : ℕ} (hk : finrank ℝ E = 2 * k + 1) (x : E) (r : ℝ) :
    volume (ball x r) =
      .ofReal r ^ finrank ℝ E * .ofReal (π ^ k * 2 ^ (k + 1) / (finrank ℝ E : ℕ)‼) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (hk ▸ (2 * k).succ_pos)
  rw [volume_ball, hk, pow_succ (√π), pow_mul, sq_sqrt pi_nonneg, mul_div_assoc, mul_div_assoc]
  congr 3
  suffices √π / (↑(2 * k + 1)‼ * √π / 2 ^ (k + 1)) = 2 ^ (k + 1) / ↑(2 * k + 1)‼ by
    simpa [add_div, add_right_comm, -one_div, Gamma_nat_add_one_add_half]
  field
/-
**InnerProductSpace.volume_closedBall_of_dim_odd** 是 Mathlib 中的一个引理，位于命名空间 `Inne
rProductSpace`。
形式化陈述：volume_closedBall_of_dim_odd {k : Nat} (hk : finrank Real E = 2 * k + 1) (
x : E) (r : Real) : volume (closedBall x r) = .ofReal r ^ finrank Real E * .ofRe
al (π ^ k * 2 ^ (k + 1) / (finrank Real E : Nat)‼)
参数：hk : finrank Real E = 2 * k + 1；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.nontrivial_of_finrank_pos`：Module.nontrivial_of_finrank_pos (h : 
0 < finrank R M) : Nontrivial M
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball`：addHaar_closed
Ball_eq_addHaar_ball [Nontrivial E] (x : E) (r : Real) : μ (closedBall x r) = μ 
(ball x r)
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用引理 `InnerProductSpace.volume_ball_of_dim_odd`：volume_ball_of_dim_odd {k : Na
t} (hk : finrank Real E = 2 * k + 1) (x : E) (r : Real) : volume (ball x r) = .o
fReal r ^ finrank Real E * .of…
-/
lemma volume_closedBall_of_dim_odd {k : ℕ} (hk : finrank ℝ E = 2 * k + 1) (x : E) (r : ℝ) :
    volume (closedBall x r) =
      .ofReal r ^ finrank ℝ E * .ofReal (π ^ k * 2 ^ (k + 1) / (finrank ℝ E : ℕ)‼) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (hk ▸ (2 * k).succ_pos)
  rw [addHaar_closedBall_eq_addHaar_ball, volume_ball_of_dim_odd hk x r]

end InnerProductSpace

namespace EuclideanSpace

open Real MeasureTheory MeasureTheory.Measure ENNReal Metric

@[simp]
/-
**EuclideanSpace.volume_ball_fin_two** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanSpace`。
形式化陈述：volume_ball_fin_two (x : EuclideanSpace Real (Fin 2)) (r : Real) : volume 
(ball x r) = .ofReal r ^ 2 * .ofReal π
参数：x : EuclideanSpace Real (Fin 2)；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InnerProductSpace.volume_ball_of_dim_even`：volume_ball_of_dim_even {k : 
Nat} (hk : finrank Real E = 2 * k) (x : E) (r : Real) : volume (ball x r) = .ofR
eal r ^ finrank Real E * .ofRea…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finrank_euclideanSpace`：finrank_euclideanSpace : Module.finrank 𝕜 (Eucli
deanSpace 𝕜 ι) = Fintype.card ι
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用引理 `Mathlib.Meta.NormNum.isNat_factorial`：isNat_factorial {n x : Nat} (h₁ : 
IsNat n x) (a : Nat) (h₂ : (1).ascFactorial x = a) : IsNat (n !) a
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma volume_ball_fin_two (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    volume (ball x r) = .ofReal r ^ 2 * .ofReal π := by
  norm_num [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp) x]

@[simp]
/-
**EuclideanSpace.volume_closedBall_fin_two** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanS
pace`。
形式化陈述：volume_closedBall_fin_two (x : EuclideanSpace Real (Fin 2)) (r : Real) : v
olume (closedBall x r) = .ofReal r ^ 2 * .ofReal π
参数：x : EuclideanSpace Real (Fin 2)；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball`：addHaar_closed
Ball_eq_addHaar_ball [Nontrivial E] (x : E) (r : Real) : μ (closedBall x r) = μ 
(ball x r)
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EuclideanSpace.volume_ball_fin_two`：volume_ball_fin_two (x : EuclideanSp
ace Real (Fin 2)) (r : Real) : volume (ball x r) = .ofReal r ^ 2 * .ofReal π
-/
lemma volume_closedBall_fin_two (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    volume (closedBall x r) = .ofReal r ^ 2 * .ofReal π := by
  rw [addHaar_closedBall_eq_addHaar_ball, volume_ball_fin_two x r]

@[simp]
/-
**EuclideanSpace.volume_ball_fin_three** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanSpace
`。
形式化陈述：volume_ball_fin_three (x : EuclideanSpace Real (Fin 3)) (r : Real) : volum
e (ball x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3)
参数：x : EuclideanSpace Real (Fin 3)；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InnerProductSpace.volume_ball_of_dim_odd`：volume_ball_of_dim_odd {k : Na
t} (hk : finrank Real E = 2 * k + 1) (x : E) (r : Real) : volume (ball x r) = .o
fReal r ^ finrank Real E * .of…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finrank_euclideanSpace`：finrank_euclideanSpace : Module.finrank 𝕜 (Eucli
deanSpace 𝕜 ι) = Fintype.card ι
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `Nat.doubleFactorial.eq_3`：∀ (k : ℕ), k.succ.succ.doubleFactorial = (k + 
2) * k.doubleFactorial
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma volume_ball_fin_three (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    volume (ball x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3) := by
  norm_num [InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by simp) x]

@[simp]
/-
**EuclideanSpace.volume_closedBall_fin_three** 是 Mathlib 中的一个引理，位于命名空间 `Euclidea
nSpace`。
形式化陈述：volume_closedBall_fin_three (x : EuclideanSpace Real (Fin 3)) (r : Real) :
 volume (closedBall x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3)
参数：x : EuclideanSpace Real (Fin 3)；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball`：addHaar_closed
Ball_eq_addHaar_ball [Nontrivial E] (x : E) (r : Real) : μ (closedBall x r) = μ 
(ball x r)
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `EuclideanSpace.volume_ball_fin_three`：volume_ball_fin_three (x : Euclide
anSpace Real (Fin 3)) (r : Real) : volume (ball x r) = .ofReal r ^ 3 * .ofReal (
π * 4 / 3)
-/
lemma volume_closedBall_fin_three (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    volume (closedBall x r) = .ofReal r ^ 3 * .ofReal (π * 4 / 3) := by
  rw [addHaar_closedBall_eq_addHaar_ball, volume_ball_fin_three x]

end EuclideanSpace

section Complex

open MeasureTheory MeasureTheory.Measure ENNReal

@[simp]
/-
**Complex.volume_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.volume_ball (a : Complex) (r : Real) : volume (Metric.ball a r) = 
.ofReal r ^ 2 * NNReal.pi
参数：a : Complex；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InnerProductSpace.volume_ball_of_dim_even`：volume_ball_of_dim_even {k : 
Nat} (hk : finrank Real E = 2 * k) (x : E) (r : Real) : volume (ball x r) = .ofR
eal r ^ finrank Real E * .ofRea…
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.finrank_real_complex`：finrank_real_complex : finrank Real Comple
x = 2
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
-/
theorem Complex.volume_ball (a : ℂ) (r : ℝ) :
    volume (Metric.ball a r) = .ofReal r ^ 2 * NNReal.pi := by
  simp [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp) a,
    ← NNReal.coe_real_pi, ofReal_coe_nnreal]

@[simp]
/-
**Complex.volume_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.volume_closedBall (a : Complex) (r : Real) : volume (Metric.closed
Ball a r) = .ofReal r ^ 2 * NNReal.pi
参数：a : Complex；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball`：addHaar_closed
Ball_eq_addHaar_ball [Nontrivial E] (x : E) (r : Real) : μ (closedBall x r) = μ 
(ball x r)
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Complex.volume_ball`：Complex.volume_ball (a : Complex) (r : Real) : volu
me (Metric.ball a r) = .ofReal r ^ 2 * NNReal.pi
-/
theorem Complex.volume_closedBall (a : ℂ) (r : ℝ) :
    volume (Metric.closedBall a r) = .ofReal r ^ 2 * NNReal.pi := by
  rw [addHaar_closedBall_eq_addHaar_ball, Complex.volume_ball]

end Complex

