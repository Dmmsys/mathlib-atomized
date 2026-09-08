/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Fernique's theorem for Gaussian measures

We show that the product of two identical Gaussian measures is invariant under rotation.
We then deduce Fernique's theorem, which states that for a Gaussian measure `μ`, there exists
`C > 0` such that the function `x ↦ exp (C * ‖x‖ ^ 2)` is integrable with respect to `μ`.
As a consequence, a Gaussian measure has finite moments of all orders.

## Main statements

* `IsGaussian.exists_integrable_exp_sq`: **Fernique's theorem**. For a Gaussian measure on a
  second-countable normed space, there exists `C > 0` such that the function
  `x ↦ exp (C * ‖x‖ ^ 2)` is integrable.
* `IsGaussian.memLp_id`: a Gaussian measure in a second-countable Banach space has finite moments
  of all orders.

## References

* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]

-/

public section

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal Real Topology

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsGaussian μ]

section Rotation

/-- Characteristic function of a centered Gaussian measure.
For a Gaussian measure, the hypothesis `∀ L : StrongDual ℝ E, μ[L] = 0` is equivalent to the simpler
`μ[id] = 0`, but at this point we don't know yet that `μ` has a first moment so we can't use it.
See `charFunDual_eq_of_integral_eq_zero` -/
/-
**ProbabilityTheory.IsGaussian.charFunDual_eq_of_forall_strongDual_eq_zero** 是 M
athlib 中的一个引理，位于命名空间 `ProbabilityTheory.IsGaussian`。
形式化陈述：charFunDual_eq_of_forall_strongDual_eq_zero (hμ : forall L : StrongDual Re
al E, μ[L] = 0) (L : StrongDual Real E) : charFunDual μ L = exp (- Var[L; μ] / 2
)
参数：hμ : forall L : StrongDual Real E, μ[L] = 0；L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsGaussian.charFunDual_eq`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E] [Bor
elSpace E]   {μ : MeasureTheory.M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `integral_complex_ofReal`：integral_complex_ofReal {f : X -> Real} : ∫ x, 
(f x : Complex) ∂μ = ∫ x, f x ∂μ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Characteristic function of a centered Gaussian measure.
For a Gaussian measure, the hypothesis `∀ L : StrongDual ℝ E, μ[L] = 0` is equiv
alent to the simpler
`μ[id] = 0`, but at this point we don't know yet that `μ` has a first moment so 
we can't use it.
See `charFunDual_eq_of_integral_eq_zero`
-/
lemma charFunDual_eq_of_forall_strongDual_eq_zero (hμ : ∀ L : StrongDual ℝ E, μ[L] = 0)
    (L : StrongDual ℝ E) :
    charFunDual μ L = exp (- Var[L; μ] / 2) := by
  simp [charFunDual_eq L, integral_complex_ofReal, hμ L, neg_div]

/-- For a centered Gaussian measure `μ`, the product measure `μ.prod μ` is invariant under rotation.
The hypothesis `∀ L : StrongDual ℝ E, μ[L] = 0` is equivalent to the simpler
`μ[id] = 0`, but at this point we don't know yet that `μ` has a first moment so we can't use it.
See `map_rotation_eq_self`. -/
/-
**ProbabilityTheory.IsGaussian.map_rotation_eq_self_of_forall_strongDual_eq_zero
** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.IsGaussian`。
形式化陈述：map_rotation_eq_self_of_forall_strongDual_eq_zero [SecondCountableTopology
 E] [CompleteSpace E] (hμ : forall L : StrongDual Real E, μ[L] = 0) (θ : Real) :
 (μ.prod μ).map (ContinuousLinearMap.rotation θ) = μ.prod μ
参数：hμ : forall L : StrongDual Real E, μ[L] = 0；θ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_charFunDual`：∀ {E : Type u_2} [inst : Norme
dAddCommGroup E] [inst_1 : NormedSpace ℝ E] {mE : MeasurableSpace E} [BorelSpace
 E]   [SecondCountableTopology…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFunDual_map`：charFunDual_map [OpensMeasurableSpace E] 
[BorelSpace F] (L : E ->L[Real] F) (L' : StrongDual Real F) : charFunDual (μ.map
 L) L' = charFunDua…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.charFunDual_prod`：charFunDual_prod [SFinite μ] [SFinite ν]
 (L : StrongDual Real (E × F)) : charFunDual (μ.prod ν) L = charFunDual μ (L.com
p (.inl Real E F)) *…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.IsGaussian.charFunDual_eq_of_forall_strongDual_eq_zero
`：charFunDual_eq_of_forall_strongDual_eq_zero (hμ : forall L : StrongDual Real E
, μ[L] = 0) (L : StrongDual Real E) : charFunDual μ L = exp (-…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
For a centered Gaussian measure `μ`, the product measure `μ.prod μ` is invariant
 under rotation.
The hypothesis `∀ L : StrongDual ℝ E, μ[L] = 0` is equivalent to the simpler
`μ[id] = 0`, but at this point we don't know yet that `μ` has a first moment so 
we can't use it.
See `map_rotation_eq_self`.
-/
lemma map_rotation_eq_self_of_forall_strongDual_eq_zero
    [SecondCountableTopology E] [CompleteSpace E]
    (hμ : ∀ L : StrongDual ℝ E, μ[L] = 0) (θ : ℝ) :
    (μ.prod μ).map (ContinuousLinearMap.rotation θ) = μ.prod μ := by
  refine Measure.ext_of_charFunDual ?_
  ext L
  simp_rw [charFunDual_map, charFunDual_prod, charFunDual_eq_of_forall_strongDual_eq_zero hμ,
    ← Complex.exp_add]
  rw [← add_div, ← add_div, ← neg_add, ← neg_add]
  congr 3
  norm_cast
  have h1 : (L.comp (.rotation θ)).comp (.inl ℝ E E)
      = Real.cos θ • L.comp (.inl ℝ E E) - Real.sin θ • L.comp (.inr ℝ E E) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.rotation_apply, smul_zero, add_zero]
    rw [← L.comp_inl_add_comp_inr]
    simp [-neg_smul, sub_eq_add_neg]
  have h2 : (L.comp (.rotation θ)).comp (.inr ℝ E E)
      = Real.sin θ • L.comp (.inl ℝ E E) + Real.cos θ • L.comp (.inr ℝ E E) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.rotation_apply, smul_zero, zero_add, add_apply, smul_apply,
      ContinuousLinearMap.inl_apply, smul_eq_mul]
    rw [← L.comp_inl_add_comp_inr]
    simp
  rw [h1, h2]
  simp only [FunLike.coe_sub, FunLike.coe_smul,
    FunLike.coe_add]
  rw [variance_sub, variance_smul, variance_add, variance_smul, variance_smul, covariance_smul_left,
    covariance_smul_right, variance_smul, covariance_smul_left, covariance_smul_right]
  · have h := Real.cos_sq_add_sin_sq θ
    grind
  all_goals exact (memLp_dual _ _ _ (by simp)).const_smul _

end Rotation

section Fernique

variable [SecondCountableTopology E]

/-- The convolution of a Gaussian measure `μ` and its map by `x ↦ -x` is centered. -/
/-
**ProbabilityTheory.IsGaussian.integral_dual_conv_map_neg_eq_zero** 是 Mathlib 中的
一个引理，位于命名空间 `ProbabilityTheory.IsGaussian`。
形式化陈述：integral_dual_conv_map_neg_eq_zero (L : StrongDual Real E) : (μ ∗ (μ.map (
ContinuousLinearEquiv.neg Real)))[L] = 0
参数：L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_conv`：∀ {M : Type u_1} {F : Type u_2} [inst : Add
Monoid M] {mM : MeasurableSpace M} [MeasurableAdd₂ M]   [inst_2 : NormedAddCommG
roup F] {μ ν : Me…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
· 使用定理 `ProbabilityTheory.IsGaussian.integrable_dual`：∀ {E : Type u_1} [inst : N
ormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E] [Bo
relSpace E]   (μ : MeasureTheory.M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
The convolution of a Gaussian measure `μ` and its map by `x ↦ -x` is centered.
-/
lemma integral_dual_conv_map_neg_eq_zero (L : StrongDual ℝ E) :
    (μ ∗ (μ.map (ContinuousLinearEquiv.neg ℝ)))[L] = 0 := by
  rw [integral_conv (by fun_prop)]
  simp only [map_add]
  calc ∫ x, ∫ y, L x + L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) ∂μ
  _ = ∫ x, L x + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) ∂μ := by
    congr with x
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp [-ContinuousLinearEquiv.coe_neg, integral_const, smul_eq_mul]
  _ = ∫ x, L x ∂μ + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg ℝ) := by
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp
  _ = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp [integral_neg]

/-- If `x ↦ exp (C * ‖x‖ ^ 2)` is integrable with respect to the centered Gaussian
`μ ∗ (μ.map (ContinuousLinearEquiv.neg ℝ))`, then for all `C' < C`, `x ↦ exp (C' * ‖x‖ ^ 2)`
is integrable with respect to `μ`. -/
/-
**ProbabilityTheory.IsGaussian.integrable_exp_sq_of_conv_neg** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.IsGaussian`。
形式化陈述：integrable_exp_sq_of_conv_neg (μ : Measure E) [IsGaussian μ] {C C' : Real}
 (hint : Integrable (fun x => rexp (C * ‖x‖ ^ 2)) (μ ∗ (μ.map (ContinuousLinearE
quiv.neg Real)))) (hC'_pos : 0 < C') (hC'_lt : C' < C) : Integrable (fun x => re
xp (C' * ‖x‖ ^ 2)) μ
参数：μ : Measure E；hint : Integrable (fun x => rexp (C * ‖x‖ ^ 2)) (μ ∗ (μ.map (Co
ntinuousLinearEquiv.neg Real)))；hC'_pos : 0 < C'；hC'_lt : C' < C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_conv_iff`：∀ {M : Type u_1} {F : Type u_2} [inst
 : AddMonoid M] {mM : MeasurableSpace M} [MeasurableAdd₂ M]   [inst_2 : NormedAd
dCommGroup F] {μ ν : Me…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.rexp`：Continuous.rexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_mul`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_pow`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 :…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 141 条，此处仅展示前 30 条）

--- 原说明 ---
If `x ↦ exp (C * ‖x‖ ^ 2)` is integrable with respect to the centered Gaussian
`μ ∗ (μ.map (ContinuousLinearEquiv.neg ℝ))`, then for all `C' < C`, `x ↦ exp (C'
 * ‖x‖ ^ 2)`
is integrable with respect to `μ`.
-/
lemma integrable_exp_sq_of_conv_neg (μ : Measure E) [IsGaussian μ] {C C' : ℝ}
    (hint : Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2))
      (μ ∗ (μ.map (ContinuousLinearEquiv.neg ℝ))))
    (hC'_pos : 0 < C') (hC'_lt : C' < C) :
    Integrable (fun x ↦ rexp (C' * ‖x‖ ^ 2)) μ := by
  have h_int : ∀ᵐ y ∂μ, Integrable (fun x ↦ rexp (C * ‖x - y‖ ^ 2)) μ := by
    rw [integrable_conv_iff (by fun_prop)] at hint
    replace hC := hint.1
    simp only [ContinuousLinearEquiv.coe_neg] at hC
    filter_upwards [hC] with y hy
    rw [integrable_map_measure (by fun_prop) (by fun_prop)] at hy
    convert! hy with x
    simp only [Function.comp_apply, Pi.neg_apply, id_eq, Real.exp_eq_exp, mul_eq_mul_left_iff,
      norm_nonneg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀]
    left
    simp_rw [← sub_eq_add_neg, norm_sub_rev]
  obtain ⟨y, hy⟩ : ∃ y, Integrable (fun x ↦ rexp (C * ‖x - y‖ ^ 2)) μ := h_int.exists
  let ε := (C - C') / C'
  have hε : 0 < ε := div_pos (by rwa [sub_pos]) (by positivity)
  suffices ∀ x, rexp (C' * ‖x‖ ^ 2) ≤ rexp (C / ε * ‖y‖ ^ 2) * rexp (C * ‖x - y‖ ^ 2) by
    refine integrable_of_le_of_le (g₁ := 0)
      (g₂ := fun x ↦ rexp (C / ε * ‖y‖ ^ 2) * rexp (C * ‖x - y‖ ^ 2)) (by fun_prop) ?_ ?_
      (integrable_const _) (hy.const_mul _)
    · exact ae_of_all _ fun _ ↦ by positivity
    · exact ae_of_all _ this
  intro x
  rw [← Real.exp_add]
  gcongr -- `⊢ C' * ‖x‖ ^ 2 ≤ C / ε * ‖y‖ ^ 2 + C * ‖x - y‖ ^ 2` with `ε = (C - C') / C'`
  have h_le : ‖x‖ ^ 2 ≤ (1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2 := by
    calc ‖x‖ ^ 2
    _ = ‖x - y + y‖ ^ 2 := by simp
    _ ≤ (‖x - y‖ + ‖y‖) ^ 2 := by grw [norm_add_le (x - y) y]
    _ = ‖x - y‖ ^ 2 + ‖y‖ ^ 2 + 2 * ‖x - y‖ * ‖y‖ := by ring
    _ ≤ ‖x - y‖ ^ 2 + ‖y‖ ^ 2 + ε * ‖x - y‖ ^ 2 + ε⁻¹ * ‖y‖ ^ 2 := by
      simp_rw [add_assoc]
      gcongr
      exact two_mul_le_add_mul_sq (by positivity)
    _ = (1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2 := by ring
  calc C' * ‖x‖ ^ 2
  _ ≤ C' * ((1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2) := by gcongr
  _ = C / ε * ‖y‖ ^ 2 + C * ‖x - y‖ ^ 2 := by grind

/-- **Fernique's theorem**: for a Gaussian measure, there exists `C > 0` such that the function
`x ↦ exp (C * ‖x‖ ^ 2)` is integrable. -/
/-
**ProbabilityTheory.IsGaussian.exists_integrable_exp_sq** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.IsGaussian`。
形式化陈述：exists_integrable_exp_sq [CompleteSpace E] (μ : Measure E) [IsGaussian μ] 
: exists C, 0 < C ∧ Integrable (fun x => rexp (C * ‖x‖ ^ 2)) μ
参数：μ : Measure E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ProbabilityTheory.exists_integrable_exp_sq_of_map_rotation_eq_self`：exis
ts_integrable_exp_sq_of_map_rotation_eq_self [IsFiniteMeasure μ] (h_rot : (μ.pro
d μ).map (ContinuousLinearMap.rotation (-(π / 4))) = μ.p…
· 使用定理 `MeasureTheory.Measure.finite_of_finite_conv`：∀ {M : Type u_1} [inst : Ad
dMonoid M] [inst_1 : MeasurableSpace M] (μ ν : MeasureTheory.Measure M)   [Measu
reTheory.IsFiniteMeasure μ] [Meas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用引理 `ProbabilityTheory.IsGaussian.map_rotation_eq_self_of_forall_strongDual_e
q_zero`：map_rotation_eq_self_of_forall_strongDual_eq_zero [SecondCountableTopolo
gy E] [CompleteSpace E] (hμ : forall L : StrongDual Real E, μ[L] = 0…
· 使用引理 `ProbabilityTheory.IsGaussian.integral_dual_conv_map_neg_eq_zero`：integra
l_dual_conv_map_neg_eq_zero (L : StrongDual Real E) : (μ ∗ (μ.map (ContinuousLin
earEquiv.neg Real)))[L] = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `ProbabilityTheory.IsGaussian.integrable_exp_sq_of_conv_neg`：integrable_e
xp_sq_of_conv_neg (μ : Measure E) [IsGaussian μ] {C C' : Real} (hint : Integrabl
e (fun x => rexp (C * ‖x‖ ^ 2)) (μ ∗ (μ.map (Con…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
**Fernique's theorem**: for a Gaussian measure, there exists `C > 0` such that t
he function
`x ↦ exp (C * ‖x‖ ^ 2)` is integrable.
-/
theorem exists_integrable_exp_sq [CompleteSpace E] (μ : Measure E) [IsGaussian μ] :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := by
  -- Since `μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)` is a centered Gaussian measure, it is invariant
  -- under rotation. We can thus apply a version of Fernique's theorem to it.
  obtain ⟨C, hC_pos, hC⟩ : ∃ C, 0 < C
      ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) (μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)) :=
    exists_integrable_exp_sq_of_map_rotation_eq_self
      (map_rotation_eq_self_of_forall_strongDual_eq_zero
        (integral_dual_conv_map_neg_eq_zero (μ := μ)) _)
  -- We must now prove that the integrability with respect to
  -- `μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)` implies integrability with respect to `μ` for
  -- another constant `C' < C`.
  refine ⟨C / 2, by positivity, ?_⟩
  exact integrable_exp_sq_of_conv_neg μ hC (by positivity) (by simp [hC_pos])

end Fernique

section FiniteMoments

variable [CompleteSpace E] [SecondCountableTopology E]

/-- A Gaussian measure has moments of all orders.
That is, the identity is in L^p for all finite `p`. -/
/-
**ProbabilityTheory.IsGaussian.memLp_id** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.IsGaussian`。
形式化陈述：memLp_id (μ : Measure E) [IsGaussian μ] (p : Real>=0∞) (hp : p != ∞) : Mem
Lp id p μ
参数：μ : Measure E；p : Real>=0∞；hp : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_div`：coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `ProbabilityTheory.memLp_of_mem_interior_integrableExpSet`：memLp_of_mem_i
nterior_integrableExpSet (h : 0 in interior (integrableExpSet X μ)) (p : Real>=0
) : MemLp X p μ
· 使用定理 `ProbabilityTheory.IsGaussian.exists_integrable_exp_sq`：exists_integrable
_exp_sq [CompleteSpace E] (μ : Measure E) [IsGaussian μ] : exists C, 0 < C ∧ Int
egrable (fun x => rexp (C * ‖x‖ ^ 2)) μ
· 使用引理 `MeasureTheory.integrable_of_le_of_le`：integrable_of_le_of_le {f g₁ g₂ : 
α -> Real} (hf : AEStronglyMeasurable f μ) (h_le₁ : g₁ <=ᵐ[μ] f) (h_le₂ : f <=ᵐ[
μ] g₂) (h_int₁ : Integrabl…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.rexp`：Continuous.rexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_mul`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_pow`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 :…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
A Gaussian measure has moments of all orders.
That is, the identity is in L^p for all finite `p`.
-/
lemma memLp_id (μ : Measure E) [IsGaussian μ] (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp id p μ := by
  suffices MemLp (fun x ↦ ‖x‖ ^ 2) (p / 2) μ by
    rw [← memLp_norm_rpow_iff (q := 2) (by fun_prop) (by simp) (by simp)]
    simpa using this
  lift p to ℝ≥0 using hp
  convert! memLp_of_mem_interior_integrableExpSet ?_ (p / 2)
  · simp
  obtain ⟨C, hC_pos, hC⟩ := exists_integrable_exp_sq μ
  have hC_neg : Integrable (fun x ↦ rexp (-C * ‖x‖ ^ 2)) μ := by -- `-C` could be any negative
    refine integrable_of_le_of_le (g₁ := 0) (g₂ := 1) (by fun_prop)
      (ae_of_all _ fun _ ↦ by positivity) ?_ (integrable_const _) (integrable_const _)
    filter_upwards with x
    simp only [neg_mul, Pi.one_apply, Real.exp_le_one_iff, Left.neg_nonpos_iff]
    positivity
  have h_subset : Set.Ioo (-C) C ⊆ interior (integrableExpSet (fun x ↦ ‖x‖ ^ 2) μ) := by
    rw [IsOpen.subset_interior_iff isOpen_Ioo]
    exact fun x hx ↦ integrable_exp_mul_of_le_of_le hC_neg hC hx.1.le hx.2.le
  exact h_subset ⟨by simp [hC_pos], hC_pos⟩

@[to_fun integrable_fun_id]
/-
**ProbabilityTheory.IsGaussian.integrable_id** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.IsGaussian`。
形式化陈述：integrable_id : Integrable id μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用引理 `ProbabilityTheory.IsGaussian.memLp_id`：memLp_id (μ : Measure E) [IsGauss
ian μ] (p : Real>=0∞) (hp : p != ∞) : MemLp id p μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma integrable_id : Integrable id μ :=
  memLp_one_iff_integrable.1 <| memLp_id μ 1 (by norm_num)

@[to_fun memLp_two_fun_id]
/-
**ProbabilityTheory.IsGaussian.memLp_two_id** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.IsGaussian`。
形式化陈述：memLp_two_id : MemLp id 2 μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussian.memLp_id`：memLp_id (μ : Measure E) [IsGauss
ian μ] (p : Real>=0∞) (hp : p != ∞) : MemLp id p μ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma memLp_two_id : MemLp id 2 μ := memLp_id μ 2 (by norm_num)
/-
**ProbabilityTheory.IsGaussian.integral_dual** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.IsGaussian`。
形式化陈述：integral_dual (L : StrongDual Real E) : μ[L] = L (∫ x, x ∂μ)
参数：L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `MeasureTheory.MemLp.integrable`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用引理 `ProbabilityTheory.IsGaussian.memLp_id`：memLp_id (μ : Measure E) [IsGauss
ian μ] (p : Real>=0∞) (hp : p != ∞) : MemLp id p μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma integral_dual (L : StrongDual ℝ E) : μ[L] = L (∫ x, x ∂μ) :=
  L.integral_comp_comm ((memLp_id μ 1 (by simp)).integrable le_rfl)

/-- A Gaussian measure with variance zero is a Dirac. -/
/-
**ProbabilityTheory.IsGaussian.eq_dirac_of_variance_eq_zero** 是 Mathlib 中的一个引理，位
于命名空间 `ProbabilityTheory.IsGaussian`。
形式化陈述：eq_dirac_of_variance_eq_zero (h : forall L : StrongDual Real E, Var[L; μ] 
= 0) : μ = Measure.dirac (∫ x, x ∂μ)
参数：h : forall L : StrongDual Real E, Var[L; μ] = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_charFunDual`：∀ {E : Type u_2} [inst : Norme
dAddCommGroup E] [inst_1 : NormedSpace ℝ E] {mE : MeasurableSpace E} [BorelSpace
 E]   [SecondCountableTopology…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用定理 `MeasureTheory.Measure.dirac.instIsFiniteMeasure`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] {a : α}, MeasureTheory.IsFiniteMeasure (MeasureTheory.Measu
re.dirac a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFunDual_dirac`：charFunDual_dirac [OpensMeasurableSpace
 E] {x : E} (L : StrongDual Real E) : charFunDual (Measure.dirac x) L = cexp (L 
x * I)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.IsGaussian.charFunDual_eq`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E] [Bor
elSpace E]   {μ : MeasureTheory.M…
· 使用定理 `integral_complex_ofReal`：integral_complex_ofReal {f : X -> Real} : ∫ x, 
(f x : Complex) ∂μ = ∫ x, f x ∂μ
· 使用引理 `ProbabilityTheory.IsGaussian.integral_dual`：integral_dual (L : StrongDua
l Real E) : μ[L] = L (∫ x, x ∂μ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A Gaussian measure with variance zero is a Dirac.
-/
lemma eq_dirac_of_variance_eq_zero (h : ∀ L : StrongDual ℝ E, Var[L; μ] = 0) :
    μ = Measure.dirac (∫ x, x ∂μ) := by
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [charFunDual_dirac, charFunDual_eq L, h L, integral_complex_ofReal, integral_dual L]
  simp

/-- If a Gaussian measure is not a Dirac, then it has value zero on singletons. -/
/-
**ProbabilityTheory.IsGaussian.nullSingletonClass** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.IsGaussian`。
形式化陈述：nullSingletonClass (h : forall x, μ != Measure.dirac x) : NullSingletonCla
ss μ where measure_singleton x
参数：h : forall x, μ != Measure.dirac x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.IsGaussian.eq_dirac_of_variance_eq_zero`：eq_dirac_of_v
ariance_eq_zero (h : forall L : StrongDual Real E, Var[L; μ] = 0) : μ = Measure.
dirac (∫ x, x ∂μ)
· 使用定理 `ProbabilityTheory.IsGaussian.map_eq_gaussianReal`：∀ {E : Type u_1} {inst
 : TopologicalSpace E} {inst_1 : AddCommMonoid E} {inst_2 : _root_.Module ℝ E}  
 {mE : MeasurableSpace E} {μ : Measure…
· 使用引理 `ProbabilityTheory.nullSingletonClass_gaussianReal`：nullSingletonClass_ga
ussianReal {μ : Real} {v : Real>=0} (h : v != 0) : NullSingletonClass (gaussianR
eal μ v)
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `ProbabilityTheory.variance_nonneg`：variance_nonneg (X : Ω -> Real) (μ : 
Measure Ω) : 0 <= variance X μ
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
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
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If a Gaussian measure is not a Dirac, then it has value zero on singletons.
-/
lemma nullSingletonClass (h : ∀ x, μ ≠ Measure.dirac x) : NullSingletonClass μ where
  measure_singleton x := by
    obtain ⟨L, hL⟩ : ∃ L : StrongDual ℝ E, Var[L; μ] ≠ 0 := by
      contrapose! h
      exact ⟨_, eq_dirac_of_variance_eq_zero h⟩
    have hL_zero : μ.map L {L x} = 0 := by
      have : NullSingletonClass (μ.map L) := by
        rw [map_eq_gaussianReal L]
        refine nullSingletonClass_gaussianReal ?_
        simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
        exact lt_of_le_of_ne (variance_nonneg _ _) hL.symm
      rw [measure_singleton]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hL_zero
    refine measure_mono_null ?_ hL_zero
    exact fun ⦃a⦄ ↦ congrArg ⇑L

@[deprecated (since := "2026-06-09")]
alias noAtoms := nullSingletonClass

/-- Characteristic function of a centered Gaussian measure. -/
/-
**ProbabilityTheory.IsGaussian.charFunDual_eq_of_integral_eq_zero** 是 Mathlib 中的
一个引理，位于命名空间 `ProbabilityTheory.IsGaussian`。
形式化陈述：charFunDual_eq_of_integral_eq_zero (hμ : μ[id] = 0) (L : StrongDual Real E
) : charFunDual μ L = exp (- Var[L; μ] / 2)
参数：hμ : μ[id] = 0；L : StrongDual Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussian.charFunDual_eq_of_forall_strongDual_eq_zero
`：charFunDual_eq_of_forall_strongDual_eq_zero (hμ : forall L : StrongDual Real E
, μ[L] = 0) (L : StrongDual Real E) : charFunDual μ L = exp (-…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.IsGaussian.integral_dual`：integral_dual (L : StrongDua
l Real E) : μ[L] = L (∫ x, x ∂μ)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Characteristic function of a centered Gaussian measure.
-/
lemma charFunDual_eq_of_integral_eq_zero (hμ : μ[id] = 0) (L : StrongDual ℝ E) :
    charFunDual μ L = exp (- Var[L; μ] / 2) := by
  refine charFunDual_eq_of_forall_strongDual_eq_zero (fun L ↦ ?_) L
  simp only [id_eq] at hμ
  simp [integral_dual, hμ]

/-- For a centered Gaussian measure `μ`, the product measure `μ.prod μ` is invariant under
rotation. -/
/-
**ProbabilityTheory.IsGaussian.map_rotation_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.IsGaussian`。
形式化陈述：map_rotation_eq_self (hμ : μ[id] = 0) (θ : Real) : (μ.prod μ).map (Continu
ousLinearMap.rotation θ) = μ.prod μ
参数：hμ : μ[id] = 0；θ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussian.map_rotation_eq_self_of_forall_strongDual_e
q_zero`：map_rotation_eq_self_of_forall_strongDual_eq_zero [SecondCountableTopolo
gy E] [CompleteSpace E] (hμ : forall L : StrongDual Real E, μ[L] = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.IsGaussian.integral_dual`：integral_dual (L : StrongDua
l Real E) : μ[L] = L (∫ x, x ∂μ)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For a centered Gaussian measure `μ`, the product measure `μ.prod μ` is invariant
 under
rotation.
-/
lemma map_rotation_eq_self (hμ : μ[id] = 0) (θ : ℝ) :
    (μ.prod μ).map (ContinuousLinearMap.rotation θ) = μ.prod μ := by
  refine map_rotation_eq_self_of_forall_strongDual_eq_zero (fun L ↦ ?_) θ
  simp only [id_eq] at hμ
  simp [integral_dual, hμ]

end FiniteMoments

end ProbabilityTheory.IsGaussian

