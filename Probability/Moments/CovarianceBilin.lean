/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.CovarianceBilinDual

/-!
# Covariance in Hilbert spaces

Given a measure `μ` defined over a Banach space `E`, one can consider the associated covariance
bilinear form which maps `L₁ L₂ : StrongDual ℝ E` to `cov[L₁, L₂; μ]`. This is called
`covarianceBilinDual μ` and is defined in the `CovarianceBilinDual` file.

In the special case where `E` is a Hilbert space, each `L : StrongDual ℝ E` can be represented
as the scalar product against some element of `E`. This motivates the definition of
`covarianceBilin`, which is a continuous bilinear form mapping `x y : E` to
`cov[⟪x, ·⟫, ⟪y, ·⟫; μ]`.

## Main definitions

* `covarianceBilin μ`: the continuous bilinear form over `E` representing the covariance of a
  measure over `E`.
* `covarianceOperator μ`: the bounded operator over `E` such that
  `⟪covarianceOperator μ x, y⟫ = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂μ`.

## Tags

covariance, Hilbert space, bilinear form
-/

@[expose] public section

open MeasureTheory InnerProductSpace NormedSpace WithLp EuclideanSpace
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Covariance of a measure on an inner product space, as a continuous bilinear form. -/
noncomputable
/-
**ProbabilityTheory.covarianceBilin** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory
`。
形式化陈述：covarianceBilin (μ : Measure E) : E ->L[Real] E ->L[Real] Real
参数：μ : Measure E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def covarianceBilin (μ : Measure E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (covarianceBilinDual μ)
    (toDualMap ℝ E).toContinuousLinearMap (toDualMap ℝ E).toContinuousLinearMap

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ProbabilityTheory.covarianceBilin_zero** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：covarianceBilin_zero : covarianceBilin (0 : Measure E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.covarianceBilin.eq_1`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : MeasurableSpace E]   [
inst_3 : BorelSpace E] (μ : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.bilinearComp.congr_simp`：∀ {𝕜 : Type u_1} {𝕜₂ : Type
 u_2} {𝕜₃ : Type u_3} {E : Type u_4} {F : Type u_6} {G : Type u_8}   [inst : Sem
inormedAddCommGroup E] [inst_1 : …
· 使用引理 `ProbabilityTheory.covarianceBilinDual_zero`：covarianceBilinDual_zero : c
ovarianceBilinDual (0 : Measure E) = 0
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covarianceBilin_zero : covarianceBilin (0 : Measure E) = 0 := by
  rw [covarianceBilin]
  simp
/-
**ProbabilityTheory.covarianceBilin_eq_covarianceBilinDual** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory`。
形式化陈述：covarianceBilin_eq_covarianceBilinDual (x y : E) : covarianceBilin μ x y =
 covarianceBilinDual μ (toDualMap Real E x) (toDualMap Real E y)
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
lemma covarianceBilin_eq_covarianceBilinDual (x y : E) :
    covarianceBilin μ x y = covarianceBilinDual μ (toDualMap ℝ E x) (toDualMap ℝ E y) := rfl

@[simp]
/-
**ProbabilityTheory.covarianceBilin_of_not_memLp** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：covarianceBilin_of_not_memLp (h : ¬MemLp id 2 μ) : covarianceBilin μ = 0
参数：h : ¬MemLp id 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilinDual_of_not_memLp`：covarianceBilinDual_
of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) : covarianceBilinD
ual μ L₁ L₂ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covarianceBilin_of_not_memLp (h : ¬MemLp id 2 μ) :
    covarianceBilin μ = 0 := by
  ext
  simp [covarianceBilin_eq_covarianceBilinDual, h]

set_option backward.isDefEq.respectTransparency.types false in
/-
**ProbabilityTheory.covarianceBilin_apply** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：covarianceBilin_apply [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 
2 μ) (x y : E) : covarianceBilin μ x y = ∫ z, ⟪x, z - μ[id]⟫ * ⟪y, z - μ[id]⟫ ∂μ
参数：h : MemLp id 2 μ；x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilinDual_apply'`：covarianceBilinDual_apply'
 (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) : covarianceBilinDual μ L₁ L₂ = 
∫ x, L₁ (x - μ[id]) * L₂ (x - μ[id…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covarianceBilin_apply [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) :
    covarianceBilin μ x y = ∫ z, ⟪x, z - μ[id]⟫ * ⟪y, z - μ[id]⟫ ∂μ := by
  simp [covarianceBilin, covarianceBilinDual_apply' h]
/-
**ProbabilityTheory.covarianceBilin_comm** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：covarianceBilin_comm (x y : E) : covarianceBilin μ x y = covarianceBilin μ
 y x
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilin_eq_covarianceBilinDual`：covarianceBili
n_eq_covarianceBilinDual (x y : E) : covarianceBilin μ x y = covarianceBilinDual
 μ (toDualMap Real E x) (toDualMap Real E y)
· 使用引理 `ProbabilityTheory.covarianceBilinDual_comm`：covarianceBilinDual_comm (L₁
 L₂ : StrongDual Real E) : covarianceBilinDual μ L₁ L₂ = covarianceBilinDual μ L
₂ L₁
-/
lemma covarianceBilin_comm (x y : E) :
    covarianceBilin μ x y = covarianceBilin μ y x := by
  rw [covarianceBilin_eq_covarianceBilinDual, covarianceBilinDual_comm,
    covarianceBilin_eq_covarianceBilinDual]
/-
**ProbabilityTheory.covarianceBilin_self** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：covarianceBilin_self [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2
 μ) (x : E) : covarianceBilin μ x x = Var[fun u => ⟪x, u⟫; μ]
参数：h : MemLp id 2 μ；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilin_eq_covarianceBilinDual`：covarianceBili
n_eq_covarianceBilinDual (x y : E) : covarianceBilin μ x y = covarianceBilinDual
 μ (toDualMap Real E x) (toDualMap Real E y)
· 使用引理 `ProbabilityTheory.covarianceBilinDual_self_eq_variance`：covarianceBilinD
ual_self_eq_variance (h : MemLp id 2 μ) (L : StrongDual Real E) : covarianceBili
nDual μ L L = Var[L; μ]
-/
lemma covarianceBilin_self [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x : E) :
    covarianceBilin μ x x = Var[fun u ↦ ⟪x, u⟫; μ] := by
  rw [covarianceBilin_eq_covarianceBilinDual, covarianceBilinDual_self_eq_variance h]
  rfl
/-
**ProbabilityTheory.covarianceBilin_apply_eq_cov** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：covarianceBilin_apply_eq_cov [CompleteSpace E] [IsFiniteMeasure μ] (h : Me
mLp id 2 μ) (x y : E) : covarianceBilin μ x y = cov[fun u => ⟪x, u⟫, fun u => ⟪y
, u⟫; μ]
参数：h : MemLp id 2 μ；x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilin_eq_covarianceBilinDual`：covarianceBili
n_eq_covarianceBilinDual (x y : E) : covarianceBilin μ x y = covarianceBilinDual
 μ (toDualMap Real E x) (toDualMap Real E y)
· 使用引理 `ProbabilityTheory.covarianceBilinDual_eq_covariance`：covarianceBilinDual
_eq_covariance (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) : covarianceBilinD
ual μ L₁ L₂ = cov[L₁, L₂; μ]
-/
lemma covarianceBilin_apply_eq_cov [CompleteSpace E] [IsFiniteMeasure μ]
    (h : MemLp id 2 μ) (x y : E) :
    covarianceBilin μ x y = cov[fun u ↦ ⟪x, u⟫, fun u ↦ ⟪y, u⟫; μ] := by
  rw [covarianceBilin_eq_covarianceBilinDual, covarianceBilinDual_eq_covariance h]
  rfl
/-
**ProbabilityTheory.covarianceBilin_real** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：covarianceBilin_real {μ : Measure Real} [IsFiniteMeasure μ] (x y : Real) :
 covarianceBilin μ x y = x * y * Var[id; μ]
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.covarianceBilin_apply_eq_cov`：covarianceBilin_apply_eq
_cov [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) : covari
anceBilin μ x y = cov[fun u => ⟪x, u…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `ProbabilityTheory.covariance_const_mul_left`：covariance_const_mul_left (
c : Real) : cov[fun ω => c * X ω, Y; μ] = c * cov[X, Y; μ]
· 使用引理 `ProbabilityTheory.covariance_const_mul_right`：covariance_const_mul_right
 (c : Real) : cov[X, fun ω => c * Y ω; μ] = c * cov[X, Y; μ]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `ProbabilityTheory.covariance_self`：covariance_self {X : Ω -> Real} (hX :
 AEMeasurable X μ) : cov[X, X; μ] = Var[X; μ]
· 使用定理 `aemeasurable_id'`：aemeasurable_id' : AEMeasurable (fun x => x) μ
· 使用定理 `Function.id_def`：∀ {α : Sort u_1}, id = fun x => x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `ProbabilityTheory.covarianceBilin_of_not_memLp`：covarianceBilin_of_not_m
emLp (h : ¬MemLp id 2 μ) : covarianceBilin μ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
（共 37 条，此处仅展示前 30 条）
-/
lemma covarianceBilin_real {μ : Measure ℝ} [IsFiniteMeasure μ] (x y : ℝ) :
    covarianceBilin μ x y = x * y * Var[id; μ] := by
  by_cases h : MemLp id 2 μ
  · simp only [covarianceBilin_apply_eq_cov h, RCLike.inner_apply, conj_trivial, mul_comm]
    rw [covariance_const_mul_left, covariance_const_mul_right, ← mul_assoc,
      covariance_self aemeasurable_id', Function.id_def]
  · simp [h, variance_of_not_memLp, aestronglyMeasurable_id]
/-
**ProbabilityTheory.covarianceBilin_real_self** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：covarianceBilin_real_self {μ : Measure Real} [IsFiniteMeasure μ] (x : Real
) : covarianceBilin μ x x = x ^ 2 * Var[id; μ]
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilin_real`：covarianceBilin_real {μ : Measur
e Real} [IsFiniteMeasure μ] (x y : Real) : covarianceBilin μ x y = x * y * Var[i
d; μ]
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
lemma covarianceBilin_real_self {μ : Measure ℝ} [IsFiniteMeasure μ] (x : ℝ) :
    covarianceBilin μ x x = x ^ 2 * Var[id; μ] := by
  rw [covarianceBilin_real, pow_two]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ProbabilityTheory.covarianceBilin_self_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：covarianceBilin_self_nonneg (x : E) : 0 <= covarianceBilin μ x x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
lemma covarianceBilin_self_nonneg (x : E) :
    0 ≤ covarianceBilin μ x x := by
  simp [covarianceBilin]
/-
**ProbabilityTheory.isPosSemidef_covarianceBilin** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：isPosSemidef_covarianceBilin : (covarianceBilin μ).toBilinForm.IsPosSemide
f where eq
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.covarianceBilin_comm`：covarianceBilin_comm (x y : E) :
 covarianceBilin μ x y = covarianceBilin μ y x
· 使用引理 `ProbabilityTheory.covarianceBilin_self_nonneg`：covarianceBilin_self_nonn
eg (x : E) : 0 <= covarianceBilin μ x x
-/
lemma isPosSemidef_covarianceBilin :
    (covarianceBilin μ).toBilinForm.IsPosSemidef where
  eq := covarianceBilin_comm
  nonneg := covarianceBilin_self_nonneg
/-
**ProbabilityTheory.covarianceBilin_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：covarianceBilin_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 
Real F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [Complete
Space F] [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : E ->L[Rea
l] F) (u v : F) : covarianceBilin (μ.map L) u v = covarianceBilin μ (L.adjoint u
) (L.adjoint v)
参数：h : MemLp id 2 μ；L : E ->L[Real] F；u v : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilin_apply`：covarianceBilin_apply [Complete
Space E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) : covarianceBilin μ x 
y = ∫ z, ⟪x, z - μ[id]⟫ * ⟪y,…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_map_measure_iff`：memLp_map_measure_iff (hg : AEStron
glyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : MemLp g p (Measure.
map f μ) ↔ MemLp (g ∘ f) …
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `ContinuousLinearMap.comp_memLp'`：comp_memLp' (L : E ->SL[σ] F) {f : α ->
 E} (hf : MemLp f p μ) : MemLp (L ∘ f) p μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ContinuousLinearMap.integral_id_map`：integral_id_map (h : Integrable id 
μ) (L : E ->L[𝕜] F) : ∫ x, x ∂(μ.map L) = L (∫ x, x ∂μ)
· 使用定理 `MeasureTheory.MemLp.integrable`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 49 条，此处仅展示前 30 条）
-/
lemma covarianceBilin_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [CompleteSpace F]
    [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : E →L[ℝ] F) (u v : F) :
    covarianceBilin (μ.map L) u v = covarianceBilin μ (L.adjoint u) (L.adjoint v) := by
  rw [covarianceBilin_apply, covarianceBilin_apply h]
  · simp_rw [id, L.integral_id_map (h.integrable (by simp))]
    rw [integral_map]
    · simp_rw [← map_sub, ← L.adjoint_inner_left]
    all_goals fun_prop
  · exact memLp_map_measure_iff (by fun_prop) (by fun_prop) |>.2 (L.comp_memLp' h)
/-
**ProbabilityTheory.covarianceBilin_map_const_add** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：covarianceBilin_map_const_add [CompleteSpace E] [IsProbabilityMeasure μ] (
c : E) : covarianceBilin (μ.map (fun x => c + x)) = covarianceBilin μ
参数：c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.memLp_map_measure_iff`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst 
: TopologicalSpace ε] [inst_1 :…
· 使用定理 `measurableEmbedding_addLeft`：∀ {G : Type u_1} [inst : AddGroup G] [inst_
1 : MeasurableSpace G] [MeasurableAdd G] (g : G),   MeasurableEmbedding fun x =>
 g + x
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilin_apply`：covarianceBilin_apply [Complete
Space E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) : covarianceBilin μ x 
y = ∫ z, ⟪x, z - μ[id]⟫ * ⟪y,…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `AEMeasurable.const_add`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurab
leSpace M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   {μ : MeasureTh
eory.Measure…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
（共 70 条，此处仅展示前 30 条）
-/
lemma covarianceBilin_map_const_add [CompleteSpace E] [IsProbabilityMeasure μ] (c : E) :
    covarianceBilin (μ.map (fun x ↦ c + x)) = covarianceBilin μ := by
  by_cases h : MemLp id 2 μ
  · ext x y
    have h_Lp : MemLp id 2 (μ.map (fun x ↦ c + x)) :=
      (measurableEmbedding_addLeft _).memLp_map_measure_iff.mpr <| (memLp_const c).add h
    rw [covarianceBilin_apply h_Lp,
      covarianceBilin_apply h, integral_map (by fun_prop) (by fun_prop)]
    congr with z
    rw [integral_map (by fun_prop) h_Lp.1]
    simp only [id_eq]
    rw [integral_add (integrable_const _)]
    · simp
    · exact h.integrable (by simp)
  · ext
    rw [covarianceBilin_of_not_memLp, covarianceBilin_of_not_memLp h]
    rw [(measurableEmbedding_addLeft _).memLp_map_measure_iff.not]
    contrapose h
    convert! (memLp_const (-c)).add h
    ext; simp
/-
**ProbabilityTheory.covarianceBilin_apply_basisFun** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：covarianceBilin_apply_basisFun {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableS
pace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι -> Ω -> Real} (hX : forall i,
 MemLp (X i) 2 μ) (i j : ι) : covarianceBilin (μ.map (fun ω => toLp 2 (X · ω))) 
(basisFun ι Real i) (basisFun ι Real j) = cov[X i, X j; μ]
参数：hX : forall i, MemLp (X i) 2 μ；i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.MemLp.aemeasurable`：∀ {α : Type u_1} {ε : Type u_2} {m0 : 
MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [inst_1 : Me
asurableSpace ε] [inst…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilin_apply_eq_cov`：covarianceBilin_apply_eq
_cov [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) : covari
anceBilin μ x y = cov[fun u => ⟪x, u…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_map_measure_iff`：memLp_map_measure_iff (hg : AEStron
glyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : MemLp g p (Measure.
map f μ) ↔ MemLp (g ∘ f) …
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用引理 `WithLp.measurable_toLp`：measurable_toLp : Measurable (@toLp p X)
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.MemLp.of_eval_piLp`：∀ {X : Type u_1} {mX : MeasurableSpace
 X} {μ : MeasureTheory.Measure X} {p q : ENNReal} [inst : Fact (1 ≤ q)]   {ι : T
ype u_2} [inst_1 : Fin…
· 使用引理 `ProbabilityTheory.covariance_map`：covariance_map {Z : Ω' -> Ω} (hX : AES
tronglyMeasurable X (μ.map Z)) (hY : AEStronglyMeasurable Y (μ.map Z)) (hZ : AEM
easurable Z μ) : cov[X…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
（共 36 条，此处仅展示前 30 条）
-/
lemma covarianceBilin_apply_basisFun {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) (i j : ι) :
    covarianceBilin (μ.map (fun ω ↦ toLp 2 (X · ω)))
      (basisFun ι ℝ i) (basisFun ι ℝ j) = cov[X i, X j; μ] := by
  have (i : ι) := (hX i).aemeasurable
  rw [covarianceBilin_apply_eq_cov, covariance_map]
  · simp [basisFun_inner]; rfl
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 (MemLp.of_eval_piLp hX)
/-
**ProbabilityTheory.covarianceBilin_apply_basisFun_self** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：covarianceBilin_apply_basisFun_self {ι Ω : Type*} [Fintype ι] {mΩ : Measur
ableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι -> Ω -> Real} (hX : fora
ll i, MemLp (X i) 2 μ) (i : ι) : covarianceBilin (μ.map (fun ω => toLp 2 (X · ω)
)) (basisFun ι Real i) (basisFun ι Real i) = Var[X i; μ]
参数：hX : forall i, MemLp (X i) 2 μ；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilin_apply_basisFun`：covarianceBilin_apply_
basisFun {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsF
initeMeasure μ] {X : ι -> Ω -> Real} (…
· 使用引理 `ProbabilityTheory.covariance_self`：covariance_self {X : Ω -> Real} (hX :
 AEMeasurable X μ) : cov[X, X; μ] = Var[X; μ]
· 使用定理 `MeasureTheory.MemLp.aemeasurable`：∀ {α : Type u_1} {ε : Type u_2} {m0 : 
MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [inst_1 : Me
asurableSpace ε] [inst…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
-/
lemma covarianceBilin_apply_basisFun_self {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) (i : ι) :
    covarianceBilin (μ.map (fun ω ↦ toLp 2 (X · ω)))
      (basisFun ι ℝ i) (basisFun ι ℝ i) = Var[X i; μ] := by
  rw [covarianceBilin_apply_basisFun hX, covariance_self]
  have (i : ι) := (hX i).aemeasurable
  fun_prop
/-
**ProbabilityTheory.covarianceBilin_apply_pi** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：covarianceBilin_apply_pi {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω
} {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι -> Ω -> Real} (hX : forall i, MemLp
 (X i) 2 μ) (x y : EuclideanSpace Real ι) : covarianceBilin (μ.map (fun ω => toL
p 2 (X · ω))) x y = ∑ i, ∑ j, x i * y j * cov[X i, X j; μ]
参数：hX : forall i, MemLp (X i) 2 μ；x y : EuclideanSpace Real ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.MemLp.aemeasurable`：∀ {α : Type u_1} {ε : Type u_2} {m0 : 
MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [inst_1 : Me
asurableSpace ε] [inst…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.covarianceBilin_apply_eq_cov`：covarianceBilin_apply_eq
_cov [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) : covari
anceBilin μ x y = cov[fun u => ⟪x, u…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_map_measure_iff`：memLp_map_measure_iff (hg : AEStron
glyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : MemLp g p (Measure.
map f μ) ↔ MemLp (g ∘ f) …
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用引理 `WithLp.measurable_toLp`：measurable_toLp : Measurable (@toLp p X)
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.MemLp.of_eval_piLp`：∀ {X : Type u_1} {mX : MeasurableSpace
 X} {μ : MeasureTheory.Measure X} {p q : ENNReal} [inst : Fact (1 ≤ q)]   {ι : T
ype u_2} [inst_1 : Fin…
· 使用引理 `ProbabilityTheory.covariance_map_fun`：covariance_map_fun {Z : Ω' -> Ω} (
hX : AEStronglyMeasurable X (μ.map Z)) (hY : AEStronglyMeasurable Y (μ.map Z)) (
hZ : AEMeasurable Z μ) : c…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
（共 58 条，此处仅展示前 30 条）
-/
lemma covarianceBilin_apply_pi {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (x y : EuclideanSpace ℝ ι) :
    covarianceBilin (μ.map (fun ω ↦ toLp 2 (X · ω))) x y =
      ∑ i, ∑ j, x i * y j * cov[X i, X j; μ] := by
  have (i : ι) := (hX i).aemeasurable
  nth_rw 1 [covarianceBilin_apply_eq_cov, covariance_map_fun, ← (basisFun ι ℝ).sum_repr' x,
    ← (basisFun ι ℝ).sum_repr' y]
  · simp_rw [sum_inner, real_inner_smul_left, basisFun_inner]
    rw [covariance_fun_sum_fun_sum]
    · refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [covariance_const_mul_left, covariance_const_mul_right]
      ring
    all_goals exact fun i ↦ (hX i).const_mul _
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 (MemLp.of_eval_piLp hX)

section covarianceOperator

variable [CompleteSpace E]

/-- The covariance operator of the measure `μ`. This is the bounded operator `F : E →L[ℝ] E`
associated to the continuous bilinear form `B : E →L[ℝ] E →L[ℝ] ℝ` such that
`B x y = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂μ` (see `covarianceOperator_inner`). Namely we have
`B x y = ⟪F x, y⟫`.

Note that the bilinear form `B` is the _uncentered_ covariance bilinear form associated to the
measure `µ`, which is not to be confused with the covariance bilinear form defined earlier in this
file as `covarianceBilin μ`. -/
/-
**ProbabilityTheory.covarianceOperator** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：covarianceOperator (μ : Measure E) : E ->L[Real] E
参数：μ : Measure E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The covariance operator of the measure `μ`. This is the bounded operator `F : E 
→L[ℝ] E`
associated to the continuous bilinear form `B : E →L[ℝ] E →L[ℝ] ℝ` such that
`B x y = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂μ` (see `covarianceOperator_inner`). Namely we ha
ve
`B x y = ⟪F x, y⟫`.

Note that the bilinear form `B` is the _uncentered_ covariance bilinear form ass
ociated to the
measure `µ`, which is not to be confused with the covariance bilinear form defin
ed earlier in this
file as `covarianceBilin μ`.
-/
noncomputable def covarianceOperator (μ : Measure E) : E →L[ℝ] E :=
  continuousLinearMapOfBilin <| ContinuousLinearMap.bilinearComp (uncenteredCovarianceBilinDual μ)
    (toDualMap ℝ E).toContinuousLinearMap (toDualMap ℝ E).toContinuousLinearMap

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ProbabilityTheory.covarianceOperator_zero** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：covarianceOperator_zero : covarianceOperator (0 : Measure E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `InnerProductSpace.continuousLinearMapOfBilin.congr_simp`：∀ {𝕜 : Type u_1
} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : Inn
erProductSpace 𝕜 E]   [inst_3 : CompleteSpace…
· 使用定理 `ContinuousLinearMap.bilinearComp.congr_simp`：∀ {𝕜 : Type u_1} {𝕜₂ : Type
 u_2} {𝕜₃ : Type u_3} {E : Type u_4} {F : Type u_6} {G : Type u_8}   [inst : Sem
inormedAddCommGroup E] [inst_1 : …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `ProbabilityTheory.uncenteredCovarianceBilinDual_zero`：uncenteredCovarian
ceBilinDual_zero : uncenteredCovarianceBilinDual (0 : Measure E) = 0
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `InnerProductSpace.continuousLinearMapOfBilin_zero`：continuousLinearMapOf
Bilin_zero : (0 : E ->L⋆[𝕜] E ->L[𝕜] 𝕜)♯ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covarianceOperator_zero : covarianceOperator (0 : Measure E) = 0 := by
  simp [covarianceOperator]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ProbabilityTheory.covarianceOperator_of_not_memLp** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：covarianceOperator_of_not_memLp (hμ : ¬MemLp id 2 μ) : covarianceOperator 
μ = 0
参数：hμ : ¬MemLp id 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.unique_continuousLinearMapOfBilin`：unique_continuousLi
nearMapOfBilin {v f : E} (is_lax_milgram : forall w, ⟪f, w⟫ = B v w) : f = B♯ v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用引理 `ProbabilityTheory.uncenteredCovarianceBilinDual_of_not_memLp`：uncentered
CovarianceBilinDual_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual Real E
) : uncenteredCovarianceBilinDual μ L₁ L₂ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covarianceOperator_of_not_memLp (hμ : ¬MemLp id 2 μ) :
    covarianceOperator μ = 0 := by
  ext x
  refine (unique_continuousLinearMapOfBilin _ fun y ↦ ?_).symm
  simp [hμ, uncenteredCovarianceBilinDual_of_not_memLp]

set_option backward.isDefEq.respectTransparency.types false in
/-
**ProbabilityTheory.covarianceOperator_inner** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：covarianceOperator_inner (hμ : MemLp id 2 μ) (x y : E) : ⟪covarianceOperat
or μ x, y⟫ = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂μ
参数：hμ : MemLp id 2 μ；x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `InnerProductSpace.continuousLinearMapOfBilin_apply`：continuousLinearMapO
fBilin_apply (v w : E) : ⟪B♯ v, w⟫ = B v w
· 使用引理 `ProbabilityTheory.uncenteredCovarianceBilinDual_apply`：uncenteredCovaria
nceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual Real E) : uncenteredCo
varianceBilinDual μ L₁ L₂ = ∫ x, L₁ x * L₂ …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma covarianceOperator_inner (hμ : MemLp id 2 μ) (x y : E) :
    ⟪covarianceOperator μ x, y⟫ = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂μ := by
  simp [covarianceOperator, uncenteredCovarianceBilinDual_apply hμ]
/-
**ProbabilityTheory.covarianceOperator_apply** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：covarianceOperator_apply (hμ : MemLp id 2 μ) (x : E) : covarianceOperator 
μ x = ∫ y, ⟪x, y⟫ • y ∂μ
参数：hμ : MemLp id 2 μ；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.unique_continuousLinearMapOfBilin`：unique_continuousLi
nearMapOfBilin {v f : E} (is_lax_milgram : forall w, ⟪f, w⟫ = B v w) : f = B♯ v
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `integral_inner`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureThe
ory.Measure α} {E : Type u_2} {𝕜 : Type u_3} [inst : RCLike 𝕜]   [inst_1 : Norme
dAdd…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {E : Type u_3}
 {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedRing 𝕜] [
inst_1 : Norme…
· 使用定理 `MeasureTheory.MemLp.const_inner`：∀ {α : Type u_1} {m : MeasurableSpace α
} {p : ENNReal} {μ : MeasureTheory.Measure α} {E : Type u_2} {𝕜 : Type u_3}   [i
nst : RCLike 𝕜] [inst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用引理 `ProbabilityTheory.covarianceOperator_inner`：covarianceOperator_inner (hμ
 : MemLp id 2 μ) (x y : E) : ⟪covarianceOperator μ x, y⟫ = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ 
∂μ
-/
lemma covarianceOperator_apply (hμ : MemLp id 2 μ) (x : E) :
    covarianceOperator μ x = ∫ y, ⟪x, y⟫ • y ∂μ := by
  refine (unique_continuousLinearMapOfBilin _ fun y ↦ ?_).symm
  rw [real_inner_comm, ← integral_inner]
  · simp_rw [inner_smul_right, ← continuousLinearMapOfBilin_apply, ← covarianceOperator_inner hμ]
    rfl
  exact memLp_one_iff_integrable.1 <| hμ.smul (hμ.const_inner x)
/-
**ProbabilityTheory.isPositive_covarianceOperator** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：isPositive_covarianceOperator : (covarianceOperator μ).toLinearMap.IsPosit
ive
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ProbabilityTheory.covarianceOperator_inner`：covarianceOperator_inner (hμ
 : MemLp id 2 μ) (x y : E) : ⟪covarianceOperator μ x, y⟫ = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ 
∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用引理 `ProbabilityTheory.covarianceOperator_of_not_memLp`：covarianceOperator_of
_not_memLp (hμ : ¬MemLp id 2 μ) : covarianceOperator μ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma isPositive_covarianceOperator : (covarianceOperator μ).toLinearMap.IsPositive := by
  by_cases hμ : MemLp id 2 μ
  swap; · simp [hμ]
  refine ⟨fun x y ↦ ?_, fun x ↦ ?_⟩
  · simp_rw [ContinuousLinearMap.coe_coe, real_inner_comm _ x, covarianceOperator_inner hμ,
      mul_comm]
  · simp only [ContinuousLinearMap.coe_coe, covarianceOperator_inner hμ, ← pow_two,
      RCLike.re_to_real]
    positivity

end covarianceOperator

end ProbabilityTheory

