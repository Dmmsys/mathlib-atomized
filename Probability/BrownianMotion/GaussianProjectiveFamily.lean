/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Finite dimensional distributions of Brownian motion

In this file we define `projectiveFamily : (I : Finset ℝ≥0) → Measure (I → ℝ)`. Each
`projectiveFamily I` is the centered Gaussian measure over `I → ℝ`
with covariance matrix given by `covMatrix I s t := min s t`.
Note that we build a measure over `I → ℝ` rather than `EuclideanSpace I ℝ`. This is because
we want to extend this family to a measure over `ℝ≥0 → ℝ` through the Kolmogorov's extension
theorem, which is phrased in this language.

We prove that these measures satisfy `IsProjectiveMeasureFamily`, which means that they can be
extended into a measure over `ℝ≥0 → ℝ` thanks to the Kolmogorov's extension theorem
(not in Mathlib yet). The obtained measure is a measure over the set of real processes indexed
by `ℝ≥0` and is the law of the Brownian motion.

## Main definition

* `BrownianReal.projectiveFamily I`: The centered Gaussian measure over `I → ℝ`
  with covariance matrix given by `covMatrix I s t := min s t`.

## Main statement

* `BrownianReal.isProjectiveMeasureFamily_projectiveFamily`:
  `BrownianReal.projectiveFamily` satisfies `IsProjectiveMeasureFamily`,
  which means it can be extended into a measure over `ℝ≥0 → ℝ`.

## Tags

Brownian motion, covariance matrix, projective family
-/

@[expose] public section


open MeasureTheory NormedSpace Set WithLp
open scoped ENNReal NNReal

namespace ProbabilityTheory.BrownianReal

variable {I J : Finset ℝ≥0}

/-- The covariance matrix of the finite dimensional distribution of the Brownian motion
indexed by `I`. -/
/-
**ProbabilityTheory.BrownianReal.covMatrix** 是 Mathlib 中的一个定义，位于命名空间 `Probabilit
yTheory.BrownianReal`。
形式化陈述：covMatrix (I : Finset Real>=0) : Matrix I I Real
参数：I : Finset Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The covariance matrix of the finite dimensional distribution of the Brownian mot
ion
indexed by `I`.
-/
def covMatrix (I : Finset ℝ≥0) : Matrix I I ℝ := .of fun s t ↦ min s t

@[simp]
/-
**ProbabilityTheory.BrownianReal.covMatrix_apply** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.BrownianReal`。
形式化陈述：covMatrix_apply (s t : I) : covMatrix I s t = min s.1 t.1
参数：s t : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma covMatrix_apply (s t : I) :
    covMatrix I s t = min s.1 t.1 := rfl
/-
**ProbabilityTheory.BrownianReal.covMatrix_submatrix** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory.BrownianReal`。
形式化陈述：covMatrix_submatrix (hJI : J subseteq I) : (covMatrix I).submatrix (fun i 
: J => ⟨i.1, hJI i.2⟩) (fun i : J => ⟨i.1, hJI i.2⟩) = covMatrix J
参数：hJI : J subseteq I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma covMatrix_submatrix (hJI : J ⊆ I) :
    (covMatrix I).submatrix (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩) =
    covMatrix J := rfl
/-
**ProbabilityTheory.BrownianReal.posSemidef_covMatrix** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.BrownianReal`。
形式化陈述：posSemidef_covMatrix (I : Finset Real>=0) : (covMatrix I).PosSemidef
参数：I : Finset Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_min`：coe_min (x y : Real>=0) : ((min x y : Real>=0) : Real) =
 min (x : Real) (y : Real)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Icc_inter_Icc`：Icc_inter_Icc : Icc a₁ b₁ inter Icc a₂ b₂ = Icc (a₁ ⊔
 a₂) (b₁ ⊓ b₂)
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `Real.volume_real_Icc`：volume_real_Icc {a b : Real} : volume.real (Icc a 
b) = max (b - a) 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.posSemidef_matrix_measure_inter`：∀ {α : Type u_1} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} {ι : Type u_5} [Finite ι] {s : ι →
 Set α},   (∀ (j : ι), MeasurableSe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsCompact.measure_ne_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
lemma posSemidef_covMatrix (I : Finset ℝ≥0) :
    (covMatrix I).PosSemidef := by
  have : covMatrix I = .of fun s t ↦ volume.real ((Icc 0 s.1.1) ∩ (Icc 0 t.1.1)) := by
    ext; simp [Icc_inter_Icc]
  rw [this]
  exact posSemidef_matrix_measure_inter (fun _ ↦ measurableSet_Icc)
    (fun _ ↦ isCompact_Icc.measure_ne_top)

/-- Each `projectiveFamily I` is the centered Gaussian measure with covariance matrix given
by `covMatrix I s t := min s t`.

Note that we build a measure over `I → ℝ` rather than `EuclideanSpace I ℝ`. This is because
we want to extend this family to a measure over `ℝ≥0 → ℝ` through the Kolmogorov's extension
theorem, which is phrased in this language. -/
/-
**ProbabilityTheory.BrownianReal.projectiveFamily** 是 Mathlib 中的一个定义，位于命名空间 `Pro
babilityTheory.BrownianReal`。
形式化陈述：projectiveFamily (I : Finset Real>=0) : Measure (I -> Real)
参数：I : Finset Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each `projectiveFamily I` is the centered Gaussian measure with covariance matri
x given
by `covMatrix I s t := min s t`.

Note that we build a measure over `I → ℝ` rather than `EuclideanSpace I ℝ`. This
 is because
we want to extend this family to a measure over `ℝ≥0 → ℝ` through the Kolmogorov
's extension
theorem, which is phrased in this language.
-/
noncomputable def projectiveFamily (I : Finset ℝ≥0) : Measure (I → ℝ) :=
  multivariateGaussian 0 (covMatrix I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

/-- Up to a measurable equivalence, `projectiveFamily I` is the centered multivariate Gaussian
with covariance matrix `covMatrix I`. -/
/-
**ProbabilityTheory.BrownianReal.measurePreserving_ofLp_multivariateGaussian** 是
 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：measurePreserving_ofLp_multivariateGaussian (I : Finset Real>=0) : Measure
Preserving ofLp (multivariateGaussian 0 (covMatrix I)) (projectiveFamily I) wher
e measurable
参数：I : Finset Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithLp.measurable_ofLp`：measurable_ofLp : Measurable (@ofLp p X)

--- 原说明 ---
Up to a measurable equivalence, `projectiveFamily I` is the centered multivariat
e Gaussian
with covariance matrix `covMatrix I`.
-/
lemma measurePreserving_ofLp_multivariateGaussian (I : Finset ℝ≥0) :
    MeasurePreserving ofLp
      (multivariateGaussian 0 (covMatrix I)) (projectiveFamily I) where
  measurable := by fun_prop
  map_eq := rfl

/-- Up to a measurable equivalence, `projectiveFamily I` is the centered multivariate Gaussian
with covariance matrix `covMatrix I`. -/
/-
**ProbabilityTheory.BrownianReal.measurePreserving_toLp_projectiveFamily** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：measurePreserving_toLp_projectiveFamily (I : Finset Real>=0) : MeasurePres
erving (toLp 2) (projectiveFamily I) (multivariateGaussian 0 (covMatrix I)) wher
e measurable
参数：I : Finset Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WithLp.measurable_toLp`：measurable_toLp : Measurable (@toLp p X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.BrownianReal.projectiveFamily.eq_1`：∀ (I : Finset NNRe
al),   ProbabilityTheory.BrownianReal.projectiveFamily I =     MeasureTheory.Mea
sure.map (⇑(MeasurableEquiv.toLp 2 (↥I → ℝ…
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableEquiv.self_comp_symm`：self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm
 = id
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Up to a measurable equivalence, `projectiveFamily I` is the centered multivariat
e Gaussian
with covariance matrix `covMatrix I`.
-/
lemma measurePreserving_toLp_projectiveFamily (I : Finset ℝ≥0) :
    MeasurePreserving (toLp 2) (projectiveFamily I)
      (multivariateGaussian 0 (covMatrix I)) where
  measurable := by fun_prop
  map_eq := by
    rw [projectiveFamily, Measure.map_map]
    · simp [← MeasurableEquiv.coe_toLp]
    all_goals fun_prop
/-
**ProbabilityTheory.BrownianReal.integral_projectiveFamily** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：integral_projectiveFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace 
Real E] (I : Finset Real>=0) (f : (I -> Real) -> E) : ∫ x, f x ∂projectiveFamily
 I = ∫ x, f (ofLp x) ∂multivariateGaussian 0 (covMatrix I)
参数：I : Finset Real>=0；f : (I -> Real) -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_projectiveFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset ℝ≥0) (f : (I → ℝ) → E) :
    ∫ x, f x ∂projectiveFamily I =
      ∫ x, f (ofLp x) ∂multivariateGaussian 0 (covMatrix I) := by
  simp [projectiveFamily, integral_map_equiv]

@[to_fun covariance_fun_projectiveFamily]
/-
**ProbabilityTheory.BrownianReal.covariance_projectiveFamily** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：covariance_projectiveFamily (I : Finset Real>=0) (f g : (I -> Real) -> Rea
l) : cov[f, g; projectiveFamily I] = cov[f ∘ ofLp, g ∘ ofLp; multivariateGaussia
n 0 (covMatrix I)]
参数：I : Finset Real>=0；f g : (I -> Real) -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.BrownianReal.projectiveFamily.eq_1`：∀ (I : Finset NNRe
al),   ProbabilityTheory.BrownianReal.projectiveFamily I =     MeasureTheory.Mea
sure.map (⇑(MeasurableEquiv.toLp 2 (↥I → ℝ…
· 使用引理 `ProbabilityTheory.covariance_map_equiv`：covariance_map_equiv (X Y : Ω ->
 Real) (Z : Ω' ≃ᵐ Ω) : cov[X, Y; μ.map Z] = cov[X ∘ Z, Y ∘ Z; μ]
-/
lemma covariance_projectiveFamily (I : Finset ℝ≥0) (f g : (I → ℝ) → ℝ) :
    cov[f, g; projectiveFamily I] =
      cov[f ∘ ofLp, g ∘ ofLp; multivariateGaussian 0 (covMatrix I)] := by
  rw [projectiveFamily, covariance_map_equiv]
  rfl

@[to_fun variance_fun_projectiveFamily]
/-
**ProbabilityTheory.BrownianReal.variance_projectiveFamily** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：variance_projectiveFamily (I : Finset Real>=0) (f : (I -> Real) -> Real) :
 Var[f; projectiveFamily I] = Var[f ∘ ofLp; multivariateGaussian 0 (covMatrix I)
]
参数：I : Finset Real>=0；f : (I -> Real) -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.BrownianReal.projectiveFamily.eq_1`：∀ (I : Finset NNRe
al),   ProbabilityTheory.BrownianReal.projectiveFamily I =     MeasureTheory.Mea
sure.map (⇑(MeasurableEquiv.toLp 2 (↥I → ℝ…
· 使用引理 `ProbabilityTheory.variance_map_equiv`：variance_map_equiv {Ω' : Type*} {m
Ω' : MeasurableSpace Ω'} {μ : Measure Ω'} (X : Ω -> Real) (Y : Ω' ≃ᵐ Ω) : Var[X;
 μ.map Y] = Var[X ∘ Y; μ]
-/
lemma variance_projectiveFamily (I : Finset ℝ≥0) (f : (I → ℝ) → ℝ) :
    Var[f; projectiveFamily I] =
      Var[f ∘ ofLp; multivariateGaussian 0 (covMatrix I)] := by
  rw [projectiveFamily, variance_map_equiv]
  rfl
/-
**ProbabilityTheory.BrownianReal.isGaussian_projectiveFamily** 是 Mathlib 中的一个实例，
位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：isGaussian_projectiveFamily (I : Finset Real>=0) : IsGaussian (projectiveF
amily I)
参数：I : Finset Real>=0。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.BrownianReal.projectiveFamily.eq_1`：∀ (I : Finset NNRe
al),   ProbabilityTheory.BrownianReal.projectiveFamily I =     MeasureTheory.Mea
sure.map (⇑(MeasurableEquiv.toLp 2 (↥I → ℝ…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
-/
instance isGaussian_projectiveFamily (I : Finset ℝ≥0) :
    IsGaussian (projectiveFamily I) := by
  rw [projectiveFamily,
    show ⇑(MeasurableEquiv.toLp 2 (I → ℝ)).symm = ⇑(EuclideanSpace.equiv I ℝ) from rfl]
  infer_instance

@[simp]
/-
**ProbabilityTheory.BrownianReal.integral_id_projectiveFamily** 是 Mathlib 中的一个引理
，位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：integral_id_projectiveFamily (I : Finset Real>=0) : ∫ x, x ∂(projectiveFam
ily I) = 0
参数：I : Finset Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.BrownianReal.integral_projectiveFamily`：integral_proje
ctiveFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] (I : Finset 
Real>=0) (f : (I -> Real) -> E) : ∫ x, f x ∂pr…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PiLp.coe_continuousLinearEquiv`：coe_continuousLinearEquiv : ⇑(PiLp.conti
nuousLinearEquiv p 𝕜 β) = ofLp
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用引理 `ContinuousLinearEquiv.integral_comp_id_comm`：integral_comp_id_comm (L : 
E ≃L[𝕜] F) : μ[L] = L (∫ x, x ∂μ)
· 使用引理 `ProbabilityTheory.integral_id_multivariateGaussian`：integral_id_multivar
iateGaussian : ∫ x, x ∂(multivariateGaussian μ S) = μ
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
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
-/
lemma integral_id_projectiveFamily (I : Finset ℝ≥0) :
    ∫ x, x ∂(projectiveFamily I) = 0 := by
  rw [integral_projectiveFamily, ← PiLp.coe_continuousLinearEquiv 2 ℝ,
    ContinuousLinearEquiv.integral_comp_id_comm, integral_id_multivariateGaussian, map_zero]
/-
**ProbabilityTheory.BrownianReal.integral_id_projectiveFamily'** 是 Mathlib 中的一个引
理，位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：integral_id_projectiveFamily' (I : Finset Real>=0) : (projectiveFamily I)[
id] = 0
参数：I : Finset Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.BrownianReal.integral_id_projectiveFamily`：integral_id
_projectiveFamily (I : Finset Real>=0) : ∫ x, x ∂(projectiveFamily I) = 0
-/
lemma integral_id_projectiveFamily' (I : Finset ℝ≥0) :
    (projectiveFamily I)[id] = 0 := integral_id_projectiveFamily I

@[simp]
/-
**ProbabilityTheory.BrownianReal.integral_eval_projectiveFamily** 是 Mathlib 中的一个
引理，位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：integral_eval_projectiveFamily (I : Finset Real>=0) (s : I) : ∫ x, x s ∂(p
rojectiveFamily I) = 0
参数：I : Finset Real>=0；s : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousLinearMap.integral_comp_id_comm`：integral_comp_id_comm (h : In
tegrable id μ) (L : E ->L[𝕜] F) : μ[L] = L (∫ x, x ∂μ)
· 使用引理 `ProbabilityTheory.IsGaussian.integrable_id`：integrable_id : Integrable i
d μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用引理 `ProbabilityTheory.BrownianReal.integral_id_projectiveFamily`：integral_id
_projectiveFamily (I : Finset Real>=0) : ∫ x, x ∂(projectiveFamily I) = 0
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
-/
lemma integral_eval_projectiveFamily (I : Finset ℝ≥0) (s : I) :
    ∫ x, x s ∂(projectiveFamily I) = 0 := by
  conv => enter [1, 2]; change fun x ↦ ContinuousLinearMap.proj (R := ℝ) s x
  rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_projectiveFamily, map_zero]
  exact IsGaussian.integrable_id
/-
**ProbabilityTheory.BrownianReal.covariance_eval_projectiveFamily** 是 Mathlib 中的
一个引理，位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：covariance_eval_projectiveFamily (I : Finset Real>=0) (s t : I) : cov[fun 
x => x s, fun x => x t; projectiveFamily I] = min s.1 t.1
参数：I : Finset Real>=0；s t : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.BrownianReal.covariance_fun_projectiveFamily`：∀ (I : F
inset NNReal) (f g : (↥I → ℝ) → ℝ),   ProbabilityTheory.covariance f g (Probabil
ityTheory.BrownianReal.projectiveFamily I) =     Pro…
· 使用引理 `ProbabilityTheory.covariance_eval_multivariateGaussian`：covariance_eval_
multivariateGaussian (hS : S.PosSemidef) (i j : ι) : cov[fun x => x i, fun x => 
x j; multivariateGaussian μ S] = S i j
· 使用引理 `ProbabilityTheory.BrownianReal.posSemidef_covMatrix`：posSemidef_covMatri
x (I : Finset Real>=0) : (covMatrix I).PosSemidef
· 使用引理 `ProbabilityTheory.BrownianReal.covMatrix_apply`：covMatrix_apply (s t : I
) : covMatrix I s t = min s.1 t.1
-/
lemma covariance_eval_projectiveFamily (I : Finset ℝ≥0) (s t : I) :
    cov[fun x ↦ x s, fun x ↦ x t; projectiveFamily I] = min s.1 t.1 := by
  rw [covariance_fun_projectiveFamily,
    covariance_eval_multivariateGaussian (posSemidef_covMatrix I),
    covMatrix_apply]
/-
**ProbabilityTheory.BrownianReal.variance_eval_projectiveFamily** 是 Mathlib 中的一个
引理，位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：variance_eval_projectiveFamily (s : I) : Var[fun x => x s; projectiveFamil
y I] = s
参数：s : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.covariance_self`：covariance_self {X : Ω -> Real} (hX :
 AEMeasurable X μ) : cov[X, X; μ] = Var[X; μ]
· 使用定理 `AEMeasurable.eval`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : Measure
Theory.Measure α} {δ : Type u_6} {X : δ → Type u_7}   {mX : (a : δ) → Measurable
Space (…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用引理 `ProbabilityTheory.BrownianReal.covariance_eval_projectiveFamily`：covaria
nce_eval_projectiveFamily (I : Finset Real>=0) (s t : I) : cov[fun x => x s, fun
 x => x t; projectiveFamily I] = min s.1 t.1
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
-/
lemma variance_eval_projectiveFamily (s : I) :
    Var[fun x ↦ x s; projectiveFamily I] = s := by
  rw [← covariance_self, covariance_eval_projectiveFamily, min_self]
  exact aemeasurable_id.eval s

/-- The distribution of finite-dimensional marginals of the real Brownian motion at time `s`
is the centered Gaussian with variance `s`. -/
/-
**ProbabilityTheory.BrownianReal.measurePreserving_eval_projectiveFamily** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：measurePreserving_eval_projectiveFamily (s : I) : MeasurePreserving (fun x
 => x s) (projectiveFamily I) (gaussianReal 0 s) where measurable
参数：s : I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.HasGaussianLaw.map_eq_gaussianReal`：∀ {Ω : Type u_1} {
mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {X : Ω → ℝ},   Probability
Theory.HasGaussianLaw X P →     MeasureThe…
· 使用引理 `ProbabilityTheory.HasGaussianLaw.eval`：eval (hX : HasGaussianLaw (fun ω 
=> (X · ω)) P) (i : ι) : HasGaussianLaw (X i) P
· 使用定理 `ProbabilityTheory.IsGaussian.hasGaussianLaw_id`：∀ {E : Type u_2} [inst :
 TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E]   {
mE : MeasurableSpace E} {μ : Measure…
· 使用引理 `ProbabilityTheory.BrownianReal.integral_eval_projectiveFamily`：integral_
eval_projectiveFamily (I : Finset Real>=0) (s : I) : ∫ x, x s ∂(projectiveFamily
 I) = 0
· 使用引理 `ProbabilityTheory.BrownianReal.variance_eval_projectiveFamily`：variance_
eval_projectiveFamily (s : I) : Var[fun x => x s; projectiveFamily I] = s
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r

--- 原说明 ---
The distribution of finite-dimensional marginals of the real Brownian motion at 
time `s`
is the centered Gaussian with variance `s`.
-/
lemma measurePreserving_eval_projectiveFamily (s : I) :
    MeasurePreserving (fun x ↦ x s) (projectiveFamily I) (gaussianReal 0 s) where
  measurable := by fun_prop
  map_eq := by
    rw [(IsGaussian.hasGaussianLaw_id.eval s).map_eq_gaussianReal,
      integral_eval_projectiveFamily,
      variance_eval_projectiveFamily, Real.toNNReal_coe]

/-- The distribution of the increment of the real Brownian motion from time `s` to time `t`
is the centered Gaussian with variance `t - s`. -/
/-
**ProbabilityTheory.BrownianReal.measurePreserving_eval_sub_eval_projectiveFamil
y** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：measurePreserving_eval_sub_eval_projectiveFamily (I : Finset Real>=0) (s t
 : I) : MeasurePreserving (fun x => x s - x t) (projectiveFamily I) (gaussianRea
l 0 (nndist s.1 t.1)) where measurable
参数：I : Finset Real>=0；s t : I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.fun_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableSub₂ 
G], Meas…
· 使用定理 `ContinuousSub.measurableSub₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Sub γ] [Con…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.HasGaussianLaw.map_eq_gaussianReal`：∀ {Ω : Type u_1} {
mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {X : Ω → ℝ},   Probability
Theory.HasGaussianLaw X P →     MeasureThe…
· 使用引理 `ProbabilityTheory.HasGaussianLaw.sub`：sub (hXY : HasGaussianLaw (fun ω =
> (X ω, Y ω)) P) : HasGaussianLaw (X - Y) P
· 使用引理 `ProbabilityTheory.HasGaussianLaw.prodMk`：prodMk [Finite ι] (hX : HasGaus
sianLaw (fun ω => (X · ω)) P) (i j : ι) : HasGaussianLaw (fun ω => (X i ω, X j ω
)) P
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ProbabilityTheory.IsGaussian.hasGaussianLaw_id`：∀ {E : Type u_2} [inst :
 TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E]   {
mE : MeasurableSpace E} {μ : Measure…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.variance_fun_sub`：variance_fun_sub [IsFiniteMeasure μ]
 (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) : Var[fun ω => X ω - Y ω; μ] = Var[X; μ] 
- 2 * cov[X, Y; μ] + Var…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用引理 `ProbabilityTheory.HasGaussianLaw.memLp_two`：memLp_two [CompleteSpace E] 
[SecondCountableTopology E] (hX : HasGaussianLaw X P) : MemLp X 2 P
· 使用引理 `ProbabilityTheory.HasGaussianLaw.eval`：eval (hX : HasGaussianLaw (fun ω 
=> (X · ω)) P) (i : ι) : HasGaussianLaw (X i) P
· 使用引理 `ProbabilityTheory.BrownianReal.variance_eval_projectiveFamily`：variance_
eval_projectiveFamily (s : I) : Var[fun x => x s; projectiveFamily I] = s
· 使用引理 `ProbabilityTheory.BrownianReal.covariance_eval_projectiveFamily`：covaria
nce_eval_projectiveFamily (I : Finset Real>=0) (s t : I) : cov[fun x => x s, fun
 x => x t; projectiveFamily I] = min s.1 t.1
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用引理 `ProbabilityTheory.HasGaussianLaw.integrable`：integrable [CompleteSpace E
] [SecondCountableTopology E] (hX : HasGaussianLaw X P) : Integrable X P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ProbabilityTheory.BrownianReal.integral_eval_projectiveFamily`：integral_
eval_projectiveFamily (I : Finset Real>=0) (s : I) : ∫ x, x s ∂(projectiveFamily
 I) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
The distribution of the increment of the real Brownian motion from time `s` to t
ime `t`
is the centered Gaussian with variance `t - s`.
-/
lemma measurePreserving_eval_sub_eval_projectiveFamily (I : Finset ℝ≥0) (s t : I) :
    MeasurePreserving (fun x ↦ x s - x t) (projectiveFamily I)
      (gaussianReal 0 (nndist s.1 t.1)) where
  measurable := by fun_prop
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal, variance_fun_sub,
      variance_eval_projectiveFamily, variance_eval_projectiveFamily,
      covariance_eval_projectiveFamily, integral_sub]
    · congr
      · simp
      norm_cast
      rw [sub_add_eq_add_sub, ← NNReal.coe_add, ← NNReal.coe_sub, Real.toNNReal_coe]
      · wlog hst : (s : ℝ≥0) ≤ t generalizing s t
        · convert this t s (le_of_not_ge hst) using 1
          · rw [add_comm, min_comm]
          · rw [nndist_comm]
        grw [min_eq_left hst, NNReal.nndist_eq, max_eq_right (by grw [hst]), two_mul,
          add_tsub_add_eq_tsub_left]
      nth_grw 1 [two_mul, min_le_left, min_le_right]
    · exact (IsGaussian.hasGaussianLaw_id.eval s).integrable
    · exact (IsGaussian.hasGaussianLaw_id.eval t).integrable
    · exact (IsGaussian.hasGaussianLaw_id.eval s).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.eval t).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.prodMk s t).sub
/-
**ProbabilityTheory.BrownianReal.isProjectiveMeasureFamily_projectiveFamily** 是 
Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：isProjectiveMeasureFamily_projectiveFamily : IsProjectiveMeasureFamily (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.BrownianReal.projectiveFamily.eq_1`：∀ (I : Finset NNRe
al),   ProbabilityTheory.BrownianReal.projectiveFamily I =     MeasureTheory.Mea
sure.map (⇑(MeasurableEquiv.toLp 2 (↥I → ℝ…
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.MeasurePreserving.comp`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {μa : …
· 使用引理 `ProbabilityTheory.BrownianReal.measurePreserving_ofLp_multivariateGaussi
an`：measurePreserving_ofLp_multivariateGaussian (I : Finset Real>=0) : MeasurePr
eserving ofLp (multivariateGaussian 0 (covMatrix I)) (projective…
· 使用引理 `ProbabilityTheory.measurePreserving_restrict₂_multivariateGaussian`：meas
urePreserving_restrict₂_multivariateGaussian {ι : Type*} [DecidableEq ι] {I J : 
Finset ι} {μ : EuclideanSpace Real I} {S : Matrix I I Re…
· 使用引理 `ProbabilityTheory.BrownianReal.posSemidef_covMatrix`：posSemidef_covMatri
x (I : Finset Real>=0) : (covMatrix I).PosSemidef
-/
lemma isProjectiveMeasureFamily_projectiveFamily :
    IsProjectiveMeasureFamily (α := fun _ ↦ ℝ) projectiveFamily := by
  intro I J hJI
  nth_rw 2 [projectiveFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        ofLp ∘ (EuclideanSpace.restrict₂ hJI) := by ext; simp
    rw [this, ((measurePreserving_ofLp_multivariateGaussian J).comp
        (measurePreserving_restrict₂_multivariateGaussian (posSemidef_covMatrix I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _ -- fun_prop fails
  · fun_prop

/-- If one restricts the finite-dimensional distribution of the real Brownian motion over a finset
`J` to a smaller finset `I`, one obtains the finite-dimensional distribution of
the real Brownian motion over `I`. -/
/-
**ProbabilityTheory.BrownianReal.measurePreserving_restrict_projectiveFamily** 是
 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.BrownianReal`。
形式化陈述：measurePreserving_restrict_projectiveFamily (hIJ : I subseteq J) : Measure
Preserving (Finset.restrict₂ (π
参数：hIJ : I subseteq J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.measurable_restrict₂`：Finset.measurable_restrict₂ {s t : Finset δ
} (hst : s subseteq t) : Measurable (Finset.restrict₂ (π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.BrownianReal.isProjectiveMeasureFamily_projectiveFamil
y`：isProjectiveMeasureFamily_projectiveFamily : IsProjectiveMeasureFamily (α

--- 原说明 ---
If one restricts the finite-dimensional distribution of the real Brownian motion
 over a finset
`J` to a smaller finset `I`, one obtains the finite-dimensional distribution of
the real Brownian motion over `I`.
-/
lemma measurePreserving_restrict_projectiveFamily (hIJ : I ⊆ J) :
    MeasurePreserving (Finset.restrict₂ (π := fun _ ↦ ℝ) hIJ) (projectiveFamily J)
      (projectiveFamily I) where
  measurable := Finset.measurable_restrict₂ _
  map_eq := isProjectiveMeasureFamily_projectiveFamily J I hIJ |>.symm

end ProbabilityTheory.BrownianReal

