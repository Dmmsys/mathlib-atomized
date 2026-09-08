/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess

/-!
# Brownian motion

In this file we define two predicates over stochastic processes `X : ℝ≥0 → Ω → ℝ` given
a probability measure `P : Measure Ω`. `IsPreBrownianReal X P` means that
`X` is a pre-Brownian motion. It means that it has the law of the Brownian motion, namely that
its finite dimensional distributions are given by `projectiveFamily`. Then
`IsBrownianReal X P` means that `X` is a Brownian motion, which means that it is a pre-Brownian
motion with almost surely continuous paths.

We prove that a centered Gaussian process `X` with covariances given by `cov[X s, X t; P] = min s t`
is a pre-Brownian motion and provide basic invariance properties. We also prove the
weak Markov property: if `B` is a pre-Brownian motion and `t₀ : ℝ≥0`, then the process
`t ↦ B (t + t₀) - B t₀` is a pre-Brownian motion independent from `(B t | t ≤ t₀)`.

## Main definitions

* `IsPreBrownianReal X P`: A stochastic process is called pre-Brownian if its finite-dimensional
  laws are those of the Brownian motion, see `projectiveFamily`.
* `IsBrownianReal X P`: A stochastic process is called Brownian if its finite-dimensional laws
  are those of the Brownian motion, see `IsPreBrownianReal`,
  and if it has almost-surely continuous paths.

## Main statements

* `IsGaussianProcess.isPreBrownianReal_of_covariance`: A centered Gaussian process with the right
  covariance is a pre-Brownian motion.
* `HasIndepIncrements.isPreBrownianReal_of_hasLaw`: A stochastic process `X` with independent
  increments and such that for all `t`, `X t` has law `gaussianReal 0 t` is a pre-Brownian motion.
* `IsPreBrownianReal.indepFun_shift`: The weak Markov property: If `B` is a pre-Brownian motion,
  then `B (t₀ + t) - B t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.

## Tags

pre-Brownian motion, Brownian motion, Markov property

-/

@[expose] public section

open MeasureTheory ProbabilityTheory.BrownianReal
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B X : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace ProbabilityTheory

section IsPreBrownianReal

/-! ### Pre-Brownian motion -/

/-- A stochastic process is called **pre-Brownian** if its finite-dimensional laws are those
of the Brownian motion, see `projectiveFamily`.

Note: we name the constructor `mk'` so as to define later `IsPreBrownianReal.mk`, which to
pre-Brownian motion will associate a continuous modification,
in a way similar to `AEMeasurable.mk`. -/
/-
**ProbabilityTheory.IsPreBrownianReal** 是 Mathlib 中的一个结构，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：IsPreBrownianReal (X : Real>=0 -> Ω -> Real) (P : Measure Ω
参数：X : Real>=0 -> Ω -> Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A stochastic process is called **pre-Brownian** if its finite-dimensional laws a
re those
of the Brownian motion, see `projectiveFamily`.

Note: we name the constructor `mk'` so as to define later `IsPreBrownianReal.mk`
, which to
pre-Brownian motion will associate a continuous modification,
in a way similar to `AEMeasurable.mk`.
-/
structure IsPreBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop where
  mk' ::
  hasLaw : ∀ I : Finset ℝ≥0, HasLaw (fun ω ↦ I.restrict (X · ω)) (projectiveFamily I) P

/-- A modification of a pre-Brownian process is pre-Brownian. -/
/-
**ProbabilityTheory.IsPreBrownianReal.congr** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω} {C : NNReal → Ω → ℝ},   ProbabilityTheory.IsPreBrownianReal B
 P → (∀ (t : NNReal), B t =ᵐ[P] C t) → ProbabilityTheory.IsPreBrownianReal C P
参数：∀ (t : NNReal), B t =ᵐ[P] C t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.HasLaw.congr`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Me
asurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X Y : Ω → 𝓧}   {μ : MeasureTheory.Mea
sure 𝓧} {P : Measure…
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.hasLaw`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Measure Ω) Pr
obabilityTheory.IsPreBrownianRea…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A modification of a pre-Brownian process is pre-Brownian.
-/
lemma IsPreBrownianReal.congr {C : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (h : ∀ t, B t =ᵐ[P] C t) :
    IsPreBrownianReal C P where
  hasLaw I := by
    refine (hB.hasLaw I).congr ?_
    have : ∀ᵐ ω ∂P, ∀ i : I, B i ω = C i ω := ae_all_iff.2 fun _ ↦ h _
    filter_upwards [this] with ω hω using funext fun i ↦ (hω i).symm
/-
**ProbabilityTheory.IsPreBrownianReal.isGaussianProcess** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P → ProbabilityTheor
y.IsGaussianProcess B P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.hasGaussianLaw`：∀ {Ω : Type u_1} {E : Type u_2}
 {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : TopologicalSpace
 E]   [inst_1 : AddCommMonoid…
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.hasLaw`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Measure Ω) Pr
obabilityTheory.IsPreBrownianRea…
-/
lemma IsPreBrownianReal.isGaussianProcess (hB : IsPreBrownianReal B P) : IsGaussianProcess B P where
  hasGaussianLaw I := (hB.hasLaw I).hasGaussianLaw
/-
**ProbabilityTheory.IsPreBrownianReal.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P → ∀ (t : NNReal), 
AEMeasurable (B t) P
参数：t : NNReal；B t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.aemeasurable`：∀ {Ω : Type u_1} {E : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topologica
lSpace E]   [inst_1 : AddCommMonoid…
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_eval`：hasGaussianLaw_
eval (hX : IsGaussianProcess X P) (t : T) : HasGaussianLaw (X t) P
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.isGaussianProcess`：∀ {Ω : Type u_1} 
{mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   P
robabilityTheory.IsPreBrownianReal B P → Pr…
-/
lemma IsPreBrownianReal.aemeasurable (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    AEMeasurable (B t) P :=
  HasGaussianLaw.aemeasurable (hB.isGaussianProcess.hasGaussianLaw_eval t)
/-
**ProbabilityTheory.IsPreBrownianReal.hasLaw_eval** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P →     ∀ (t : NNRea
l), ProbabilityTheory.HasLaw (B t) (ProbabilityTheory.gaussianReal 0 t) P
参数：t : NNReal；B t；ProbabilityTheory.gaussianReal 0 t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Mea
surableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measur
e 𝓧} {P : MeasureTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.MeasurePreserving.hasLaw`：∀ {Ω : Type u_1} {𝓧 : Type u_2} 
{mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheo
ry.Measure 𝓧} {P : MeasureTh…
· 使用引理 `ProbabilityTheory.BrownianReal.measurePreserving_eval_projectiveFamily`：
measurePreserving_eval_projectiveFamily (s : I) : MeasurePreserving (fun x => x 
s) (projectiveFamily I) (gaussianReal 0 s) where measurable
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.hasLaw`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Measure Ω) Pr
obabilityTheory.IsPreBrownianRea…
-/
lemma IsPreBrownianReal.hasLaw_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    HasLaw (B t) (gaussianReal 0 t) P :=
  (measurePreserving_eval_projectiveFamily ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw {t})
/-
**ProbabilityTheory.IsPreBrownianReal.eval_zero_ae_eq_zero** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P → ∀ᵐ (ω : Ω) ∂P, B
 0 ω = 0
参数：ω : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.hasLaw_eval`：∀ {Ω : Type u_1} {mΩ : 
MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   Probabi
lityTheory.IsPreBrownianReal B P →   …
· 使用定理 `ProbabilityTheory.HasLaw.ae_eq_of_dirac`：∀ {Ω : Type u_1} {𝓧 : Type u_2}
 {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {P : MeasureThe
ory.Measure Ω} [MeasurableSin…
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
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.gaussianReal_zero_var`：gaussianReal_zero_var (μ : Real
) : gaussianReal μ 0 = Measure.dirac μ
-/
lemma IsPreBrownianReal.eval_zero_ae_eq_zero (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, B 0 ω = 0 := by
  have := hB.hasLaw_eval 0
  rw [gaussianReal_zero_var] at this
  exact this.ae_eq_of_dirac
/-
**ProbabilityTheory.IsPreBrownianReal.hasLaw_sub** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P →     ∀ (s t : NNR
eal), ProbabilityTheory.HasLaw (B s - B t) (ProbabilityTheory.gaussianReal 0 (nn
dist ↑s ↑t)) P
参数：s t : NNReal；B s - B t；ProbabilityTheory.gaussianReal 0 (nndist ↑s ↑t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasLaw.comp`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : Mea
surableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Measur
e 𝓧} {P : MeasureTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `MeasureTheory.MeasurePreserving.hasLaw`：∀ {Ω : Type u_1} {𝓧 : Type u_2} 
{mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheo
ry.Measure 𝓧} {P : MeasureTh…
· 使用引理 `ProbabilityTheory.BrownianReal.measurePreserving_eval_sub_eval_projectiv
eFamily`：measurePreserving_eval_sub_eval_projectiveFamily (I : Finset Real>=0) (
s t : I) : MeasurePreserving (fun x => x s - x t) (projectiveFamily I…
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.hasLaw`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Measure Ω) Pr
obabilityTheory.IsPreBrownianRea…
-/
lemma IsPreBrownianReal.hasLaw_sub (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    HasLaw (B s - B t) (gaussianReal 0 (nndist s.1 t.1)) P :=
  (measurePreserving_eval_sub_eval_projectiveFamily
    {s, t} ⟨s, by simp⟩ ⟨t, by simp⟩).hasLaw.comp (hB.hasLaw _)
/-
**ProbabilityTheory.IsPreBrownianReal.integral_eval** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P → ∀ (t : NNReal), 
∫ (x : Ω), B t x ∂P = 0
参数：t : NNReal；x : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.HasLaw.integral_eq`：∀ {Ω : Type u_1} {mΩ : MeasurableS
pace Ω} {P : MeasureTheory.Measure Ω} {E : Type u_3} [inst : NormedAddCommGroup 
E]   [inst_1 : NormedSpace…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.hasLaw_eval`：∀ {Ω : Type u_1} {mΩ : 
MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   Probabi
lityTheory.IsPreBrownianReal B P →   …
· 使用引理 `ProbabilityTheory.integral_id_gaussianReal`：integral_id_gaussianReal : ∫
 x, x ∂gaussianReal μ v = μ
-/
lemma IsPreBrownianReal.integral_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    P[B t] = 0 := by
  rw [(hB.hasLaw_eval t).integral_eq, integral_id_gaussianReal]
/-
**ProbabilityTheory.IsPreBrownianReal.integrable_eval** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P → ∀ (t : NNReal), 
MeasureTheory.Integrable (B t) P
参数：t : NNReal；B t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.integrable`：integrable [CompleteSpace E
] [SecondCountableTopology E] (hX : HasGaussianLaw X P) : Integrable X P
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_eval`：hasGaussianLaw_
eval (hX : IsGaussianProcess X P) (t : T) : HasGaussianLaw (X t) P
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.isGaussianProcess`：∀ {Ω : Type u_1} 
{mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   P
robabilityTheory.IsPreBrownianReal B P → Pr…
-/
lemma IsPreBrownianReal.integrable_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Integrable (B t) P := (hB.isGaussianProcess.hasGaussianLaw_eval t).integrable
/-
**ProbabilityTheory.IsPreBrownianReal.covariance_eval** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P → ∀ (s t : NNReal)
, ProbabilityTheory.covariance (B s) (B t) P = ↑(min s t)
参数：s t : NNReal；B s；B t；min s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.BrownianReal.covariance_eval_projectiveFamily`：covaria
nce_eval_projectiveFamily (I : Finset Real>=0) (s t : I) : cov[fun x => x s, fun
 x => x t; projectiveFamily I] = min s.1 t.1
· 使用定理 `ProbabilityTheory.HasLaw.covariance_fun_comp`：∀ {Ω : Type u_1} {𝓧 : Type
 u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : Measu
reTheory.Measure 𝓧} {P : MeasureTh…
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.hasLaw`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Measure Ω) Pr
obabilityTheory.IsPreBrownianRea…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma IsPreBrownianReal.covariance_eval (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    cov[B s, B t; P] = min s t := by
  convert (hB.hasLaw {s, t}).covariance_fun_comp
    (f := Function.eval ⟨s, by simp⟩) (g := fun x ↦ x ⟨t, by simp⟩) ?_ ?_
  · simp
  · simp
  · rw [covariance_eval_projectiveFamily]
  all_goals exact Measurable.aemeasurable (by fun_prop)
/-
**ProbabilityTheory.IsPreBrownianReal.covariance_fun_eval** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P →     ∀ (s t : NNR
eal), ProbabilityTheory.covariance (fun ω => B s ω) (fun ω => B t ω) P = ↑(min s
 t)
参数：s t : NNReal；fun ω => B s ω；fun ω => B t ω；min s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.covariance_eval`：∀ {Ω : Type u_1} {m
Ω : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   Pro
babilityTheory.IsPreBrownianReal B P → ∀ …
-/
lemma IsPreBrownianReal.covariance_fun_eval (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    cov[fun ω ↦ B s ω, fun ω ↦ B t ω; P] = min s t :=
  hB.covariance_eval s t

/-- A centered Gaussian process with the right covariance is a pre-Brownian motion. -/
/-
**ProbabilityTheory.IsGaussianProcess.isPreBrownianReal_of_covariance** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsGaussianProcess X P →     (∀ (t : NNRe
al), ∫ (x : Ω), X t x ∂P = 0) →       (∀ (s t : NNReal), s ≤ t → ProbabilityTheo
ry.covariance (X s) (X t) P = ↑s) →         ProbabilityTheory.IsPreBrownianReal 
X P
参数：∀ (t : NNReal), ∫ (x : Ω), X t x ∂P = 0；∀ (s t : NNReal), s ≤ t → Probability
Theory.covariance (X s) (X t) P = ↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `ProbabilityTheory.IsGaussianProcess.aemeasurable`：aemeasurable (hX : IsG
aussianProcess X P) (t : T) : AEMeasurable (X t) P
· 使用定理 `MeasurableEquiv.map_measurableEquiv_injective`：map_measurableEquiv_injec
tive (e : α ≃ᵐ β) : Injective (Measure.map e)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasurableEquiv.coe_toLp`：coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithL
p.toLp p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PiLp.coe_symm_continuousLinearEquiv`：coe_symm_continuousLinearEquiv : ⇑(
PiLp.continuousLinearEquiv p 𝕜 β).symm = toLp p
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isGaussian_map`：∀ {Ω : Type u_1} {E : T
ype u_2} {mΩ : MeasurableSpace Ω} [inst : TopologicalSpace E] [inst_1 : AddCommM
onoid E]   [inst_2 : _root_.Module ℝ …
· 使用定理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw`：∀ {Ω : Type u_1} {E 
: Type u_2} {T : Type u_3} {mΩ : MeasurableSpace Ω} [inst : MeasurableSpace E]  
 [inst_1 : TopologicalSpace E] [inst_2 :…
· 使用定理 `ProbabilityTheory.IsGaussian.ext`：∀ {E : Type u_1} [inst : NormedAddComm
Group E] [SecondCountableTopology E] [CompleteSpace E]   [inst_3 : MeasurableSpa
ce E] [inst_4 : BorelS…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用引理 `ContinuousLinearEquiv.integral_comp_id_comm`：integral_comp_id_comm (L : 
E ≃L[𝕜] F) : μ[L] = L (∫ x, x ∂μ)
· 使用定理 `ContinuousLinearEquiv.integral_comp_comm`：integral_comp_comm (L : E ≃L[𝕜
] F) (φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
A centered Gaussian process with the right covariance is a pre-Brownian motion.
-/
theorem IsGaussianProcess.isPreBrownianReal_of_covariance (h1 : IsGaussianProcess X P)
    (h2 : ∀ t, P[X t] = 0) (h3 : ∀ s t, s ≤ t → cov[X s, X t; P] = s) :
    IsPreBrownianReal X P where
  hasLaw I := by
    refine ⟨aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _, ?_⟩
    apply (MeasurableEquiv.toLp 2 (_ → ℝ)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ]
    have := (h1.hasGaussianLaw I).isGaussian_map
    apply IsGaussian.ext
    · rw [integral_map, integral_map, integral_map]
      · simp only [id_eq]
        rw [ContinuousLinearEquiv.integral_comp_id_comm,
          ContinuousLinearEquiv.integral_comp_comm]
        simp only [PiLp.continuousLinearEquiv_symm_apply, integral_id_projectiveFamily,
          WithLp.toLp_zero, WithLp.toLp_eq_zero]
        congr with i
        rw [eval_integral]
        · simpa using h2 _
        · exact fun _ ↦ (h1.hasGaussianLaw_eval _).integrable
      any_goals fun_prop
      exact aemeasurable_pi_lambda _ fun _ ↦ h1.aemeasurable _
    · rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_of_isSymm isPosSemidef_covarianceBilin.isSymm
        isPosSemidef_covarianceBilin.isSymm fun x ↦ ?_
      simp only [ContinuousLinearMap.toBilinForm_apply]
      rw [PiLp.coe_symm_continuousLinearEquiv, covarianceBilin_apply_pi, covarianceBilin_apply_pi]
      · congrm ∑ i, ∑ j, _ * ?_
        rw [covariance_eval_projectiveFamily, covariance_map]
        · wlog hij : i.1 ≤ j.1 generalizing i j
          · rw [covariance_comm, this j i (by grind), min_comm]
          rw [min_eq_left hij]
          exact h3 i j hij
        any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
        exact aemeasurable_pi_lambda _ (fun _ ↦ h1.aemeasurable _)
      · exact fun i ↦ (IsGaussian.hasGaussianLaw_id.eval i).memLp_two
      · exact fun i ↦ ((h1.hasGaussianLaw I).isGaussian_map.hasGaussianLaw_id.eval i).memLp_two

/-- A pre-Brownian motion has independent increments. -/
/-
**ProbabilityTheory.IsPreBrownianReal.hasIndepIncrements** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P → ProbabilityTheor
y.HasIndepIncrements B P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.isProbabilityMeasure`：isProbabilityM
easure (hX : IsGaussianProcess X P) : IsProbabilityMeasure P
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.isGaussianProcess`：∀ {Ω : Type u_1} 
{mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   P
robabilityTheory.IsPreBrownianReal B P → Pr…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_eq_zero`：∀ {Ω :
 Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2}
 [Finite ι] {X : ι → Ω → ℝ},   ProbabilityTheory.HasGa…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_increments`：hasGaussi
anLaw_increments (hX : IsGaussianProcess X P) {n : Nat} {t : Fin (n + 1) -> T} :
 HasGaussianLaw (fun ω (i : Fin n) => X (t i.succ) …
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covariance_fun_sub_fun_sub`：covariance_fun_sub_fun_sub
 [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) (h
T : MemLp T 2 μ) : cov[fun ω => X …
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用引理 `ProbabilityTheory.HasGaussianLaw.memLp_two`：memLp_two [CompleteSpace E] 
[SecondCountableTopology E] (hX : HasGaussianLaw X P) : MemLp X 2 P
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_eval`：hasGaussianLaw_
eval (hX : IsGaussianProcess X P) (t : T) : HasGaussianLaw (X t) P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.covariance_fun_eval`：∀ {Ω : Type u_1
} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},  
 ProbabilityTheory.IsPreBrownianReal B P →   …
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Fin.strictMono_succ`：strictMono_succ : StrictMono (succ : Fin n -> Fin (
n + 1))
· 使用定理 `Fin.le_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.le_castSucc_iff`：∀ {n : ℕ} {i : Fin (n + 1)} {j : Fin n}, i ≤ j.cast
Succ ↔ i < j.succ
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
A pre-Brownian motion has independent increments.
-/
lemma IsPreBrownianReal.hasIndepIncrements (hB : IsPreBrownianReal B P) :
    HasIndepIncrements B P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine fun n t ht ↦ hB.isGaussianProcess.hasGaussianLaw_increments.iIndepFun_of_covariance_eq_zero
    fun i j hij ↦ ?_
  rw [covariance_fun_sub_fun_sub]
  · simp_rw [hB.covariance_fun_eval]
    wlog h : i < j generalizing i j
    · simp_rw [← this j i hij.symm (by grind), min_comm]
      grind
    have h1 : i.succ ≤ j.succ := Fin.strictMono_succ h |>.le
    have h2 : i.castSucc ≤ j.succ := Fin.le_of_lt h1
    have h3 : i.castSucc ≤ j.castSucc := Fin.le_castSucc_iff.mpr h1
    rw [min_eq_left (ht h1), min_eq_left (ht h), min_eq_left (ht h2), min_eq_left (ht h3)]
    simp
  all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

/-- A stochastic process `X` with independent increments and such that for all `t`, `X t`
has law `gaussianReal 0 t` is a pre-Brownian motion. -/
/-
**ProbabilityTheory.HasIndepIncrements.isPreBrownianReal_of_hasLaw** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory.HasIndepIncrements`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   (∀ (t : NNReal), ProbabilityTheory.HasLaw (X t) (Probabili
tyTheory.gaussianReal 0 t) P) →     ProbabilityTheory.HasIndepIncrements X P → P
robabilityTheory.IsPreBrownianReal X P
参数：∀ (t : NNReal), ProbabilityTheory.HasLaw (X t) (ProbabilityTheory.gaussianRea
l 0 t) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.HasLaw.ae_eq_of_dirac`：∀ {Ω : Type u_1} {𝓧 : Type u_2}
 {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {P : MeasureThe
ory.Measure Ω} [MeasurableSin…
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
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.gaussianReal_zero_var`：gaussianReal_zero_var (μ : Real
) : gaussianReal μ 0 = Measure.dirac μ
· 使用定理 `ProbabilityTheory.IsGaussianProcess.isPreBrownianReal_of_covariance`：∀ {
Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X : NNReal → Ω → ℝ} {P : MeasureTheory.M
easure Ω},   ProbabilityTheory.IsGaussianProcess X P →   …
· 使用定理 `ProbabilityTheory.HasIndepIncrements.isGaussianProcess`：∀ {T : Type u_1}
 {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measu
re Ω}   [inst : LinearOrder T] [inst_1 : Ord…
· 使用定理 `ProbabilityTheory.HasLaw.hasGaussianLaw`：∀ {Ω : Type u_1} {E : Type u_2}
 {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : TopologicalSpace
 E]   [inst_1 : AddCommMonoid…
· 使用定理 `ProbabilityTheory.HasLaw.integral_eq`：∀ {Ω : Type u_1} {mΩ : MeasurableS
pace Ω} {P : MeasureTheory.Measure Ω} {E : Type u_3} [inst : NormedAddCommGroup 
E]   [inst_1 : NormedSpace…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用引理 `ProbabilityTheory.integral_id_gaussianReal`：integral_id_gaussianReal : ∫
 x, x ∂gaussianReal μ v = μ
· 使用定理 `ProbabilityTheory.HasIndepIncrements.indepFun_eval_sub`：∀ {T : Type u_1}
 {Ω : Type u_2} {E : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measu
re Ω} {X : T → Ω → E}   [inst : Preorder T] …
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ProbabilityTheory.HasLaw.isProbabilityMeasure`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : Meas
ureTheory.Measure 𝓧} {P : MeasureTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
A stochastic process `X` with independent increments and such that for all `t`, 
`X t`
has law `gaussianReal 0 t` is a pre-Brownian motion.
-/
theorem HasIndepIncrements.isPreBrownianReal_of_hasLaw
    (law : ∀ t, HasLaw (X t) (gaussianReal 0 t) P) (incr : HasIndepIncrements X P) :
    IsPreBrownianReal X P := by
  have h0 : ∀ᵐ ω ∂P, X 0 ω = 0 := by
      apply HasLaw.ae_eq_of_dirac
      rw [← gaussianReal_zero_var]
      exact law 0
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · exact incr.isGaussianProcess (fun t ↦ (law t).hasGaussianLaw) h0
  · rw [(law t).integral_eq, integral_id_gaussianReal]
  have h1 := incr.indepFun_eval_sub zero_le hst h0
  have := (law 0).isProbabilityMeasure
  have h2 : X t = X t - X s + X s := by simp
  rw [h2, covariance_add_right, h1.covariance_eq_zero, covariance_self, (law s).variance_eq,
    variance_id_gaussianReal]
  · simp
  · exact (law s).aemeasurable
  · exact (law s).hasGaussianLaw.memLp_two
  · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
  · exact (law s).hasGaussianLaw.memLp_two
  · exact (law t).hasGaussianLaw.memLp_two.sub (law s).hasGaussianLaw.memLp_two
  · exact (law s).hasGaussianLaw.memLp_two
/-
**ProbabilityTheory.IsPreBrownianReal.neg** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P → ProbabilityTheor
y.IsPreBrownianReal (-B) P
参数：-B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasIndepIncrements.isPreBrownianReal_of_hasLaw`：∀ {Ω :
 Type u_1} {mΩ : MeasurableSpace Ω} {X : NNReal → Ω → ℝ} {P : MeasureTheory.Meas
ure Ω},   (∀ (t : NNReal), ProbabilityTheory.HasLaw (X…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `ProbabilityTheory.gaussianReal_neg`：gaussianReal_neg (hX : HasLaw X (gau
ssianReal μ v) P) : HasLaw (-X) (gaussianReal (-μ) v) P
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.hasLaw_eval`：∀ {Ω : Type u_1} {mΩ : 
MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   Probabi
lityTheory.IsPreBrownianReal B P →   …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `ProbabilityTheory.iIndepFun.comp`：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ :
 MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type u_10}   {γ : ι →
 Type u_11} {mβ : (i :…
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.hasIndepIncrements`：∀ {Ω : Type u_1}
 {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   
ProbabilityTheory.IsPreBrownianReal B P → Pr…
· 使用定理 `Measurable.fun_neg`：∀ {G : Type u_2} {α : Type u_3} [inst : Neg G] [inst
_1 : MeasurableSpace G] [MeasurableNeg G] {m : MeasurableSpace α}   {f : α → G},
 Measura…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
lemma IsPreBrownianReal.neg (hB : IsPreBrownianReal B P) : IsPreBrownianReal (-B) P := by
  refine HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t ↦ ?_) (fun n t ht ↦ ?_)
  · simpa using gaussianReal_neg (hB.hasLaw_eval t)
  convert (hB.hasIndepIncrements n t ht).comp (fun _ x ↦ -x) (by fun_prop)
  simp
  grind

/-- If `B` is a pre-Brownian motion and `c > 0`, then
`t ↦ (√c)⁻¹ B (c t)` is a pre-Brownian motion. -/
/-
**ProbabilityTheory.IsPreBrownianReal.smul** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P →     ∀ {c : NNRea
l}, c ≠ 0 → ProbabilityTheory.IsPreBrownianReal (fun t ω => (√↑c)⁻¹ * B (c * t) 
ω) P
参数：fun t ω => (√↑c)⁻¹ * B (c * t) ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsGaussianProcess.isPreBrownianReal_of_covariance`：∀ {
Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X : NNReal → Ω → ℝ} {P : MeasureTheory.M
easure Ω},   ProbabilityTheory.IsGaussianProcess X P →   …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.IsGaussianProcess.smul`：smul (c : T -> Real) (hX : IsG
aussianProcess X P) : IsGaussianProcess (fun t ω => c t • (X t ω)) P
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.IsGaussianProcess.comp_right`：comp_right (h : IsGaussi
anProcess X P) (f : S -> T) : IsGaussianProcess (X ∘ f) P
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.isGaussianProcess`：∀ {Ω : Type u_1} 
{mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   P
robabilityTheory.IsPreBrownianReal B P → Pr…
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.integral_eval`：∀ {Ω : Type u_1} {mΩ 
: MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   Proba
bilityTheory.IsPreBrownianReal B P → ∀ …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ProbabilityTheory.covariance_const_mul_left`：covariance_const_mul_left (
c : Real) : cov[fun ω => c * X ω, Y; μ] = c * cov[X, Y; μ]
· 使用引理 `ProbabilityTheory.covariance_const_mul_right`：covariance_const_mul_right
 (c : Real) : cov[X, fun ω => c * Y ω; μ] = c * cov[X, Y; μ]
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.covariance_eval`：∀ {Ω : Type u_1} {m
Ω : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   Pro
babilityTheory.IsPreBrownianReal B P → ∀ …
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
If `B` is a pre-Brownian motion and `c > 0`, then
`t ↦ (√c)⁻¹ B (c t)` is a pre-Brownian motion.
-/
lemma IsPreBrownianReal.smul (hB : IsPreBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsPreBrownianReal (fun t ω ↦ (√c)⁻¹ * B (c * t) ω) P := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · have this t ω : (√c)⁻¹ * B (c * t) ω = (√c)⁻¹ • ((B ∘ (c * ·)) t ω) := rfl
    simp_rw [this]
    exact (hB.isGaussianProcess.comp_right _).smul _
  · rw [integral_const_mul, hB.integral_eval, mul_zero]
  · rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval, min_eq_left]
    · simp [field]
    · exact mul_le_mul_right hst c

/-- **Weak Markov property**: If `B` is a pre-Brownian motion, then
`t ↦ B (t₀ + t) - B t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.
This is the proof that it is pre-Brownian,
see `IsPreBrownianReal.indepFun_shift` for independence. -/
/-
**ProbabilityTheory.IsPreBrownianReal.shift** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P →     ∀ (t₀ : NNRe
al), ProbabilityTheory.IsPreBrownianReal (fun t ω => B (t₀ + t) ω - B t₀ ω) P
参数：t₀ : NNReal；fun t ω => B (t₀ + t) ω - B t₀ ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsGaussianProcess.isPreBrownianReal_of_covariance`：∀ {
Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X : NNReal → Ω → ℝ} {P : MeasureTheory.M
easure Ω},   ProbabilityTheory.IsGaussianProcess X P →   …
· 使用引理 `ProbabilityTheory.IsGaussianProcess.shift`：shift [Add T] (h : IsGaussian
Process X P) (t₀ : T) : IsGaussianProcess (fun t ω => X (t₀ + t) ω - X t₀ ω) P
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.isGaussianProcess`：∀ {Ω : Type u_1} 
{mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   P
robabilityTheory.IsPreBrownianReal B P → Pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用引理 `ProbabilityTheory.HasGaussianLaw.integrable`：integrable [CompleteSpace E
] [SecondCountableTopology E] (hX : HasGaussianLaw X P) : Integrable X P
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_eval`：hasGaussianLaw_
eval (hX : IsGaussianProcess X P) (t : T) : HasGaussianLaw (X t) P
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.integral_eval`：∀ {Ω : Type u_1} {mΩ 
: MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   Proba
bilityTheory.IsPreBrownianReal B P → ∀ …
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `ProbabilityTheory.IsGaussianProcess.isProbabilityMeasure`：isProbabilityM
easure (hX : IsGaussianProcess X P) : IsProbabilityMeasure P
· 使用引理 `ProbabilityTheory.covariance_fun_sub_left`：covariance_fun_sub_left [IsFi
niteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[fu
n ω => X ω - Y ω, Z; μ] = cov[X…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用引理 `ProbabilityTheory.HasGaussianLaw.memLp_two`：memLp_two [CompleteSpace E] 
[SecondCountableTopology E] (hX : HasGaussianLaw X P) : MemLp X 2 P
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_sub`：hasGaussianLaw_s
ub (hX : IsGaussianProcess X P) {s t : T} : HasGaussianLaw (X s - X t) P
· 使用引理 `ProbabilityTheory.covariance_fun_sub_right`：covariance_fun_sub_right [Is
FiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[
X, fun ω => Y ω - Z ω; μ] = cov[…
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.covariance_eval`：∀ {Ω : Type u_1} {m
Ω : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   Pro
babilityTheory.IsPreBrownianReal B P → ∀ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_min`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LinearOrder α] [AddLe
ftMono α] (a b c : α), a + min b c = min (a + b) (a + c)
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Weak Markov property**: If `B` is a pre-Brownian motion, then
`t ↦ B (t₀ + t) - B t₀` is a pre-Brownian motion which is independent from `(B t
, t ≤ t₀)`.
This is the proof that it is pre-Brownian,
see `IsPreBrownianReal.indepFun_shift` for independence.
-/
lemma IsPreBrownianReal.shift (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) :
    IsPreBrownianReal (fun t ω ↦ B (t₀ + t) ω - B t₀ ω) P := by
  refine (hB.isGaussianProcess.shift t₀).isPreBrownianReal_of_covariance
    (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · rw [integral_sub, hB.integral_eval, hB.integral_eval, sub_zero]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).integrable
  · have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right,
      hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, ← add_min,
      min_eq_left hst, min_eq_right, min_eq_left, min_self]
    any_goals simp
    any_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    exact hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two

/-- **Weak Markov property**: If `B` is a pre-Brownian motion, then
`B (t₀ + t) - B t₀` is a pre-Brownian motion which is independent from `(B t, t ≤ t₀)`.
This is the proof of independence, see `IsPreBrownianReal.shift` for the proof
that it is pre-Brownian. -/
/-
**ProbabilityTheory.IsPreBrownianReal.indepFun_shift** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P →     ∀ (t₀ : NNRe
al), ProbabilityTheory.IndepFun (fun ω t => B (t₀ + t) ω - B t₀ ω) (fun ω t => B
 (↑t) ω) P
参数：t₀ : NNReal；fun ω t => B (t₀ + t) ω - B t₀ ω；fun ω t => B (↑t) ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.aemeasurable`：∀ {Ω : Type u_1} {mΩ :
 MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   Probab
ilityTheory.IsPreBrownianReal B P → ∀ …
· 使用引理 `ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero`：inde
pFun_of_covariance_eq_zero {X : S -> Ω -> Real} {Y : T -> Ω -> Real} (hXY : IsGa
ussianProcess (Sum.elim X Y) P) (mX : forall s, AEMeasur…
· 使用引理 `ProbabilityTheory.IsGaussianProcess.of_isGaussianProcess`：of_isGaussianP
rocess (hX : IsGaussianProcess X P) (h : forall s, exists I : Finset T, exists L
 : (I -> E) ->L[Real] F, forall ω, Y s ω = L (…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.isGaussianProcess`：∀ {Ω : Type u_1} 
{mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   P
robabilityTheory.IsPreBrownianReal B P → Pr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `_private.Mathlib.Probability.BrownianMotion.Basic.0.ProbabilityTheory.Is
PreBrownianReal.indepFun_shift._abel_1_1`：∀ (t₀ t : NNReal) (x y : ↥{t₀, t₀ + t}
 → ℝ),   x ⟨t₀ + t, ⋯⟩ + y ⟨t₀ + t, ⋯⟩ - (x ⟨t₀, ⋯⟩ + y ⟨t₀, ⋯⟩) = x ⟨t₀ + t, ⋯⟩
 - x ⟨t₀, ⋯⟩ + (y ⟨t₀ …
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
**Weak Markov property**: If `B` is a pre-Brownian motion, then
`B (t₀ + t) - B t₀` is a pre-Brownian motion which is independent from `(B t, t 
≤ t₀)`.
This is the proof of independence, see `IsPreBrownianReal.shift` for the proof
that it is pre-Brownian.
-/
lemma IsPreBrownianReal.indepFun_shift (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) :
    IndepFun (fun ω t ↦ B (t₀ + t) ω - B t₀ ω) (fun ω (t : Set.Iic t₀) ↦ B t ω) P := by
  have mX t := hB.aemeasurable t
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hB.isGaussianProcess.of_isGaussianProcess
    rintro (t | ⟨t, ht⟩)
    · exact ⟨{t₀, t₀ + t},
        { toFun x := x ⟨t₀ + t, by simp⟩ - x ⟨t₀, by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{t},
        { toFun x := x ⟨t, by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  any_goals fun_prop
  · rintro s ⟨t, ht : t ≤ t₀⟩
    have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_fun_sub_left, hB.covariance_eval, hB.covariance_eval, min_eq_right, min_eq_right,
      sub_self]
    · grind
    · simp [ht, le_add_right]
    all_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two

/-- If `B` is a pre-Brownian motion then `t ↦ t * B (1 / t)` is a pre-Brownian motion. -/
/-
**ProbabilityTheory.IsPreBrownianReal.inv** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.IsPreBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measur
eTheory.Measure Ω},   ProbabilityTheory.IsPreBrownianReal B P → ProbabilityTheor
y.IsPreBrownianReal (fun t ω => ↑t * B (1 / t) ω) P
参数：fun t ω => ↑t * B (1 / t) ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsGaussianProcess.isPreBrownianReal_of_covariance`：∀ {
Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X : NNReal → Ω → ℝ} {P : MeasureTheory.M
easure Ω},   ProbabilityTheory.IsGaussianProcess X P →   …
· 使用引理 `ProbabilityTheory.IsGaussianProcess.smul`：smul (c : T -> Real) (hX : IsG
aussianProcess X P) : IsGaussianProcess (fun t ω => c t • (X t ω)) P
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.IsGaussianProcess.comp_right`：comp_right (h : IsGaussi
anProcess X P) (f : S -> T) : IsGaussianProcess (X ∘ f) P
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.isGaussianProcess`：∀ {Ω : Type u_1} 
{mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   P
robabilityTheory.IsPreBrownianReal B P → Pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.integral_eval`：∀ {Ω : Type u_1} {mΩ 
: MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   Proba
bilityTheory.IsPreBrownianReal B P → ∀ …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ProbabilityTheory.IsGaussianProcess.isProbabilityMeasure`：isProbabilityM
easure (hX : IsGaussianProcess X P) : IsProbabilityMeasure P
· 使用引理 `ProbabilityTheory.covariance_const_mul_left`：covariance_const_mul_left (
c : Real) : cov[fun ω => c * X ω, Y; μ] = c * cov[X, Y; μ]
· 使用引理 `ProbabilityTheory.covariance_const_mul_right`：covariance_const_mul_right
 (c : Real) : cov[X, fun ω => c * Y ω; μ] = c * cov[X, Y; μ]
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.covariance_eval`：∀ {Ω : Type u_1} {m
Ω : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   Pro
babilityTheory.IsPreBrownianReal B P → ∀ …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `one_div_le_one_div_of_le`：one_div_le_one_div_of_le (ha : 0 < a) (h : a <
= b) : 1 / b <= 1 / a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
If `B` is a pre-Brownian motion then `t ↦ t * B (1 / t)` is a pre-Brownian motio
n.
-/
lemma IsPreBrownianReal.inv (hB : IsPreBrownianReal B P) :
    IsPreBrownianReal (fun t ω ↦ t * (B (1 / t) ω)) P := by
  refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t ↦ ?_) (fun s t hst ↦ ?_)
  · exact (IsGaussianProcess.comp_right hB.isGaussianProcess _).smul _
  · rw [integral_const_mul, hB.integral_eval, mul_zero]
  · have := hB.isGaussianProcess.isProbabilityMeasure
    rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval]
    obtain rfl | hs := eq_or_ne s 0
    · simp
    have : 0 < t := (pos_of_ne_zero hs).trans_le hst
    rw [min_eq_right]
    · norm_cast
      field_simp
    exact one_div_le_one_div_of_le (pos_of_ne_zero hs) hst

end IsPreBrownianReal

section IsBrownianReal

/-! ### Brownian motion -/

variable {B X : ℝ≥0 → Ω → ℝ}

/-- A stochastic process is called **Brownian** if its finite-dimensional laws are those
of the Brownian motion, see `IsPreBrownianReal`, and if it has almost-surely continuous paths. -/
/-
**ProbabilityTheory.IsBrownianReal** 是 Mathlib 中的一个结构，位于命名空间 `ProbabilityTheory`
。
形式化陈述：IsBrownianReal (X : Real>=0 -> Ω -> Real) (P : Measure Ω
参数：X : Real>=0 -> Ω -> Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A stochastic process is called **Brownian** if its finite-dimensional laws are t
hose
of the Brownian motion, see `IsPreBrownianReal`, and if it has almost-surely con
tinuous paths.
-/
structure IsBrownianReal (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) : Prop
    extends IsPreBrownianReal X P where
  cont : ∀ᵐ ω ∂P, Continuous (X · ω)
/-
**ProbabilityTheory.IsBrownianReal.neg** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.IsBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {B
 : NNReal → Ω → ℝ},   ProbabilityTheory.IsBrownianReal B P → ProbabilityTheory.I
sBrownianReal (-B) P
参数：-B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.neg`：∀ {Ω : Type u_1} {mΩ : Measurab
leSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   ProbabilityTheo
ry.IsPreBrownianReal B P → Pr…
· 使用定理 `ProbabilityTheory.IsBrownianReal.toIsPreBrownianReal`：∀ {Ω : Type u_1} {
mΩ : MeasurableSpace Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Mea
sure Ω) ProbabilityTheory.IsBrownianReal._…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsBrownianReal.cont`：∀ {Ω : Type u_1} {mΩ : Measurable
Space Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Measure Ω) Probabi
lityTheory.IsBrownianReal._…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
lemma IsBrownianReal.neg (hB : IsBrownianReal B P) :
    IsBrownianReal (-B) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.neg
  cont := hB.cont.mono (fun _ _ ↦ by simpa [← Pi.neg_def, continuous_neg_iff])

/-- If `B` is a Brownian motion and `c > 0`, then `t ↦ (√c)⁻¹ B (c t)` is a Brownian motion. -/
/-
**ProbabilityTheory.IsBrownianReal.smul** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.IsBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {B
 : NNReal → Ω → ℝ},   ProbabilityTheory.IsBrownianReal B P →     ∀ {c : NNReal},
 c ≠ 0 → ProbabilityTheory.IsBrownianReal (fun t ω => (√↑c)⁻¹ * B (c * t) ω) P
参数：fun t ω => (√↑c)⁻¹ * B (c * t) ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.smul`：∀ {Ω : Type u_1} {mΩ : Measura
bleSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   ProbabilityThe
ory.IsPreBrownianReal B P →   …
· 使用定理 `ProbabilityTheory.IsBrownianReal.toIsPreBrownianReal`：∀ {Ω : Type u_1} {
mΩ : MeasurableSpace Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Mea
sure Ω) ProbabilityTheory.IsBrownianReal._…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsBrownianReal.cont`：∀ {Ω : Type u_1} {mΩ : Measurable
Space Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Measure Ω) Probabi
lityTheory.IsBrownianReal._…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)

--- 原说明 ---
If `B` is a Brownian motion and `c > 0`, then `t ↦ (√c)⁻¹ B (c t)` is a Brownian
 motion.
-/
lemma IsBrownianReal.smul (hB : IsBrownianReal B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianReal (fun t ω ↦ (√c)⁻¹ * B (c * t) ω) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.smul hc
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop
/-
**ProbabilityTheory.IsBrownianReal.shift** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.IsBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {B
 : NNReal → Ω → ℝ},   ProbabilityTheory.IsBrownianReal B P →     ∀ (t₀ : NNReal)
, ProbabilityTheory.IsBrownianReal (fun t ω => B (t₀ + t) ω - B t₀ ω) P
参数：t₀ : NNReal；fun t ω => B (t₀ + t) ω - B t₀ ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.shift`：∀ {Ω : Type u_1} {mΩ : Measur
ableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω},   ProbabilityTh
eory.IsPreBrownianReal B P →   …
· 使用定理 `ProbabilityTheory.IsBrownianReal.toIsPreBrownianReal`：∀ {Ω : Type u_1} {
mΩ : MeasurableSpace Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Mea
sure Ω) ProbabilityTheory.IsBrownianReal._…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsBrownianReal.cont`：∀ {Ω : Type u_1} {mΩ : Measurable
Space Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Measure Ω) Probabi
lityTheory.IsBrownianReal._…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
lemma IsBrownianReal.shift (hB : IsBrownianReal B P) (t₀ : ℝ≥0) :
    IsBrownianReal (fun t ω ↦ B (t₀ + t) ω - B t₀ ω) P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.shift t₀
  cont := by
    filter_upwards [hB.cont] with ω h
    fun_prop
/-
**ProbabilityTheory.IsBrownianReal.tendsto_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.IsBrownianReal`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {B
 : NNReal → Ω → ℝ},   ProbabilityTheory.IsBrownianReal B P → ∀ᵐ (ω : Ω) ∂P, Filt
er.Tendsto (fun x => B x ω) (nhds 0) (nhds 0)
参数：ω : Ω；fun x => B x ω；nhds 0；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsPreBrownianReal.eval_zero_ae_eq_zero`：∀ {Ω : Type u_
1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : MeasureTheory.Measure Ω}, 
  ProbabilityTheory.IsPreBrownianReal B P → ∀ᵐ…
· 使用定理 `ProbabilityTheory.IsBrownianReal.toIsPreBrownianReal`：∀ {Ω : Type u_1} {
mΩ : MeasurableSpace Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Mea
sure Ω) ProbabilityTheory.IsBrownianReal._…
· 使用定理 `ProbabilityTheory.IsBrownianReal.cont`：∀ {Ω : Type u_1} {mΩ : Measurable
Space Ω} {X : NNReal → Ω → ℝ}   {P : autoParam (MeasureTheory.Measure Ω) Probabi
lityTheory.IsBrownianReal._…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
-/
lemma IsBrownianReal.tendsto_nhds_zero (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Filter.Tendsto (B · ω) (𝓝 0) (𝓝 0) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω h1 h2
  convert h1.tendsto 0
  exact h2.symm

end IsBrownianReal

end ProbabilityTheory

