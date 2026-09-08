/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
public import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Independence of Gaussian random variables

In this file we prove some results linking Gaussian random variables and independence. It is
a well known fact that if `(X, Y)` is Gaussian, then `X` and `Y` are independent if their covariance
is zero. We prove many versions of this theorem in different settings: in Banach spaces,
Hilbert spaces, and for families of real random variables.

We also prove that independent Gaussian random variables are jointly Gaussian.

## Main statements

* `iIndepFun.hasGaussianLaw`: Independent Gaussian random variables are jointly Gaussian,
  indexed version.
* `IndepFun.hasGaussianLaw`: Independent Gaussian random variables are jointly Gaussian,
  product version.
* `HasGaussianLaw.iIndepFun_of_covariance_eq_zero`: If $(X_i)_{i \in \iota}$ are jointly Gaussian,
  then they are independent if for all $i \ne j$, $\mathrm{Cov}(X_i, X_j) = 0$.
* `HasGaussianLaw.indepFun_of_covariance_eq_zero`: If $(X, Y)$ is Gaussian,
  then $X$ and $Y$ are independent if $\mathrm{Cov}(X, Y) = 0$.

## Tags

Gaussian random variable
-/

open MeasureTheory WithLp Complex Finset ContinuousLinearMap InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}


section Diagonal

namespace ContinuousLinearMap

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {L : (i : ι) → StrongDual ℝ (E i) →L[ℝ] StrongDual ℝ (E i) →L[ℝ] ℝ}

/-- Given `L i : (E i)' × (E i)' → ℝ` a family of continuous bilinear forms,
`diagonalStrongDualPi L` is the continuous bilinear form over `(Π i, E i)'`
which maps `(x, y) : (Π i, E i)' × (Π i, E i)'` to
`∑ i, L i (fun a ↦ x aᵢ) (fun a ↦ y aᵢ)`.

This is an implementation detail used in `iIndepFun.hasGaussianLaw`. -/
noncomputable
/-
**ContinuousLinearMap.diagonalStrongDualPi** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
LinearMap`。
形式化陈述：diagonalStrongDualPi (L : (i : ι) -> StrongDual Real (E i) ->L[Real] Stron
gDual Real (E i) ->L[Real] Real) : StrongDual Real (Π i, E i) ->L[Real] StrongDu
al Real (Π i, E i) ->L[Real] Real
参数：L : (i : ι) -> StrongDual Real (E i) ->L[Real] StrongDual Real (E i) ->L[Real
] Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def diagonalStrongDualPi (L : (i : ι) → StrongDual ℝ (E i) →L[ℝ] StrongDual ℝ (E i) →L[ℝ] ℝ) :
    StrongDual ℝ (Π i, E i) →L[ℝ] StrongDual ℝ (Π i, E i) →L[ℝ] ℝ :=
  letI g : LinearMap.BilinForm ℝ (StrongDual ℝ (Π i, E i)) := LinearMap.mk₂ ℝ
    (fun x y ↦ ∑ i, L i (x ∘L (single ℝ E i)) (y ∘L (single ℝ E i)))
    (fun x y z ↦ by simp [sum_add_distrib])
    (fun c m n ↦ by simp [mul_sum])
    (fun x y z ↦ by simp [sum_add_distrib])
    (fun c m n ↦ by simp [mul_sum])
  LinearMap.mkContinuous₂ g (∑ i, ‖L i‖) <| by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_sum_le, sum_mul, sum_mul]
    gcongr with i _
    grw [le_opNorm₂]
    gcongr <;> grw [opNorm_comp_le, norm_single_le_one, mul_one]
/-
**ContinuousLinearMap.diagonalStrongDualPi_apply** 是 Mathlib 中的一个引理，位于命名空间 `Cont
inuousLinearMap`。
形式化陈述：diagonalStrongDualPi_apply (x y : StrongDual Real (Π i, E i)) : diagonalSt
rongDualPi L x y = ∑ i, L i (x ∘L (.single Real E i)) (y ∘L (.single Real E i))
参数：x y : StrongDual Real (Π i, E i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diagonalStrongDualPi_apply (x y : StrongDual ℝ (Π i, E i)) :
    diagonalStrongDualPi L x y = ∑ i, L i (x ∘L (.single ℝ E i)) (y ∘L (.single ℝ E i)) := rfl
/-
**ContinuousLinearMap.toBilinForm_diagonalStrongDualPi_apply** 是 Mathlib 中的一个引理，
位于命名空间 `ContinuousLinearMap`。
形式化陈述：toBilinForm_diagonalStrongDualPi_apply (x y : StrongDual Real (Π i, E i)) 
: (diagonalStrongDualPi L).toBilinForm x y = ∑ i, (L i).toBilinForm (x ∘L (.sing
le Real E i)) (y ∘L (.single Real E i))
参数：x y : StrongDual Real (Π i, E i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toBilinForm_diagonalStrongDualPi_apply (x y : StrongDual ℝ (Π i, E i)) :
    (diagonalStrongDualPi L).toBilinForm x y =
    ∑ i, (L i).toBilinForm (x ∘L (.single ℝ E i)) (y ∘L (.single ℝ E i)) := rfl
/-
**ContinuousLinearMap.isPosSemidef_diagonalStrongDualPi** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousLinearMap`。
形式化陈述：isPosSemidef_diagonalStrongDualPi (hL : forall i, (L i).toBilinForm.IsPosS
emidef) : (diagonalStrongDualPi L).toBilinForm.IsPosSemidef where eq x y
参数：hL : forall i, (L i).toBilinForm.IsPosSemidef。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isPosSemidef_diagonalStrongDualPi (hL : ∀ i, (L i).toBilinForm.IsPosSemidef) :
    (diagonalStrongDualPi L).toBilinForm.IsPosSemidef where
  eq x y := by
    simp_rw [toBilinForm_diagonalStrongDualPi_apply, fun i ↦ (hL i).eq]
  nonneg x := by
    rw [toBilinForm_diagonalStrongDualPi_apply]
    exact sum_nonneg fun i _ ↦ (hL i).nonneg _

end Pi

section Prod

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {L₁ : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ}
  {L₂ : StrongDual ℝ F →L[ℝ] StrongDual ℝ F →L[ℝ] ℝ}

/-- Given `L₁ : E' × E' → ℝ` and `L₂ : F' × F' → ℝ` two continuous bilinear forms,
`diagonalStrongDualProd L₁ L₂` is the continuous bilinear form over `(E × F)'`
which maps `(x, y) : (E × F)' × (E × F)'` to
`L₁ (fun (a, b) ↦ x a) (fun (a, b) ↦ y a) + L₂ (fun (a, b) ↦ x b) (fun (a, b) ↦ y b)`.

This is an implementation detail used in `IndepFun.hasGaussianLaw`. -/
noncomputable
/-
**ContinuousLinearMap.diagonalStrongDualProd** 是 Mathlib 中的一个定义，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：diagonalStrongDualProd (L₁ : StrongDual Real E ->L[Real] StrongDual Real E
 ->L[Real] Real) (L₂ : StrongDual Real F ->L[Real] StrongDual Real F ->L[Real] R
eal) : StrongDual Real (E × F) ->L[Real] StrongDual Real (E × F) ->L[Real] Real
参数：L₁ : StrongDual Real E ->L[Real] StrongDual Real E ->L[Real] Real；L₂ : Strong
Dual Real F ->L[Real] StrongDual Real F ->L[Real] Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def diagonalStrongDualProd
    (L₁ : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ)
    (L₂ : StrongDual ℝ F →L[ℝ] StrongDual ℝ F →L[ℝ] ℝ) :
    StrongDual ℝ (E × F) →L[ℝ] StrongDual ℝ (E × F) →L[ℝ] ℝ :=
  letI g : LinearMap.BilinForm ℝ (StrongDual ℝ (E × F)) := LinearMap.mk₂ ℝ
    (fun x y ↦ L₁ (x ∘L (inl ℝ E F)) (y ∘L (inl ℝ E F)) + L₂ (x ∘L (inr ℝ E F)) (y ∘L (inr ℝ E F)))
    (fun x y z ↦ by simp [add_add_add_comm])
    (fun c m n ↦ by simp [mul_add])
    (fun x y z ↦ by simp [add_add_add_comm])
    (fun c m n ↦ by simp [mul_add])
  LinearMap.mkContinuous₂ g (‖L₁‖ + ‖L₂‖) <| by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_add_le, add_mul, add_mul]
    gcongr
    · grw [le_opNorm₂]
      gcongr <;> grw [opNorm_comp_le, norm_inl_le_one, mul_one]
    · grw [le_opNorm₂]
      gcongr <;> grw [opNorm_comp_le, norm_inr_le_one, mul_one]
/-
**ContinuousLinearMap.diagonalStrongDualProd_apply** 是 Mathlib 中的一个引理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：diagonalStrongDualProd_apply (x y : StrongDual Real (E × F)) : diagonalStr
ongDualProd L₁ L₂ x y = L₁ (x ∘L (inl Real E F)) (y ∘L (inl Real E F)) + L₂ (x ∘
L (inr Real E F)) (y ∘L (inr Real E F))
参数：x y : StrongDual Real (E × F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma diagonalStrongDualProd_apply (x y : StrongDual ℝ (E × F)) :
    diagonalStrongDualProd L₁ L₂ x y =
    L₁ (x ∘L (inl ℝ E F)) (y ∘L (inl ℝ E F)) + L₂ (x ∘L (inr ℝ E F)) (y ∘L (inr ℝ E F)) := rfl
/-
**ContinuousLinearMap.toBilinForm_diagonalStrongDualProd_apply** 是 Mathlib 中的一个引
理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：toBilinForm_diagonalStrongDualProd_apply (x y : StrongDual Real (E × F)) :
 (diagonalStrongDualProd L₁ L₂).toBilinForm x y = L₁.toBilinForm (x ∘L (inl Real
 E F)) (y ∘L (inl Real E F)) + L₂.toBilinForm (x ∘L (inr Real E F)) (y ∘L (inr R
eal E F))
参数：x y : StrongDual Real (E × F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toBilinForm_diagonalStrongDualProd_apply (x y : StrongDual ℝ (E × F)) :
    (diagonalStrongDualProd L₁ L₂).toBilinForm x y =
    L₁.toBilinForm (x ∘L (inl ℝ E F)) (y ∘L (inl ℝ E F)) +
    L₂.toBilinForm (x ∘L (inr ℝ E F)) (y ∘L (inr ℝ E F)) := rfl
/-
**ContinuousLinearMap.isPosSemidef_diagonalStrongDualProd** 是 Mathlib 中的一个引理，位于命
名空间 `ContinuousLinearMap`。
形式化陈述：isPosSemidef_diagonalStrongDualProd (h₁ : L₁.toBilinForm.IsPosSemidef) (h₂
 : L₂.toBilinForm.IsPosSemidef) : (diagonalStrongDualProd L₁ L₂).toBilinForm.IsP
osSemidef where eq x y
参数：h₁ : L₁.toBilinForm.IsPosSemidef；h₂ : L₂.toBilinForm.IsPosSemidef。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isPosSemidef_diagonalStrongDualProd
    (h₁ : L₁.toBilinForm.IsPosSemidef) (h₂ : L₂.toBilinForm.IsPosSemidef) :
    (diagonalStrongDualProd L₁ L₂).toBilinForm.IsPosSemidef where
  eq x y := by
    simp_rw [toBilinForm_diagonalStrongDualProd_apply, h₁.eq, h₂.eq]
  nonneg x := by
    rw [toBilinForm_diagonalStrongDualProd_apply]
    exact add_nonneg (h₁.nonneg _) (h₂.nonneg _)

end Prod

end ContinuousLinearMap

end Diagonal


public section

namespace ProbabilityTheory

section iIndepFun

variable {ι : Type*} [Finite ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]

section NormedSpace

variable [∀ i, NormedSpace ℝ (E i)] {X : Π i, Ω → (E i)}

/-- Independent Gaussian random variables are jointly Gaussian. -/
/-
**ProbabilityTheory.iIndepFun.hasGaussianLaw** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} [Finite ι] {E : ι → Type u_3}   [inst : (i : ι) → NormedAddCommGrou
p (E i)] [inst_1 : (i : ι) → MeasurableSpace (E i)]   [∀ (i : ι), CompleteSpace 
(E i)] [∀ (i : ι), BorelSpace (E i)] [∀ (i : ι), SecondCountableTopology (E i)] 
  [inst_5 : (i : ι) → NormedSpace ℝ (E i)] {X : (i : ι) → Ω → E i},   (∀ (i : ι)
, ProbabilityTheory.HasGaussianLaw (X i) P) →     ProbabilityTheory.iIndepFun X 
P → ProbabilityTheory.HasGaussianLaw (fun ω x => X x ω) P
参数：i : ι；E i；i : ι；E i；i : ι；E i；i : ι；E i；i : ι；E i；i : ι；E i；i : ι；∀ (i : ι), 
ProbabilityTheory.HasGaussianLaw (X i) P；fun ω x => X x ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type 
u_10}   {m : (i : ι) → MeasurableSpace…
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.isGaussian_iff_gaussian_charFunDual`：isGaussian_iff_ga
ussian_charFunDual [IsFiniteMeasure μ] : IsGaussian μ ↔ exists (m : E) (f : Stro
ngDual Real E ->L[Real] StrongDual Real E -…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `_private.Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Indep
endence.0.ContinuousLinearMap.isPosSemidef_diagonalStrongDualPi`：∀ {ι : Type u_2
} [inst : Fintype ι] [inst_1 : DecidableEq ι] {E : ι → Type u_3}   [inst_2 : (i 
: ι) → NormedAddCommGroup (E i)] [inst_3 : (i…
· 使用引理 `ProbabilityTheory.isPosSemidef_covarianceBilinDual`：isPosSemidef_covaria
nceBilinDual : (covarianceBilinDual μ).toBilinForm.IsPosSemidef where eq
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.iIndepFun_iff_charFunDual_pi`：iIndepFun_iff_charFunDua
l_pi (hX : forall i, AEMeasurable (X i) P) : iIndepFun X P ↔ forall L, charFunDu
al (P.map (fun ω => (X · ω))) L = ∏ …
· 使用定理 `ProbabilityTheory.HasGaussianLaw.aemeasurable`：∀ {Ω : Type u_1} {E : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topologica
lSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.sum_single_apply`：sum_single_apply [Fintype ι] [DecidableEq ι]
 (v : Π i, φ i) : ∑ i, Pi.single i (v i) = v
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Independent Gaussian random variables are jointly Gaussian.
-/
lemma iIndepFun.hasGaussianLaw (hX1 : ∀ i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P) :
    HasGaussianLaw (fun ω ↦ (X · ω)) P where
  isGaussian_map := by
    have := hX2.isProbabilityMeasure
    let := Fintype.ofFinite ι
    rw [isGaussian_iff_gaussian_charFunDual]
    classical
    refine ⟨fun i ↦ ∫ x, x ∂P.map (X i),
      .diagonalStrongDualPi (fun i ↦ covarianceBilinDual (P.map (X i))),
      isPosSemidef_diagonalStrongDualPi (fun _ ↦ isPosSemidef_covarianceBilinDual), fun L ↦ ?_⟩
    rw [(iIndepFun_iff_charFunDual_pi (by fun_prop)).1 hX2]
    simp only [← LinearMap.sum_single_apply E (fun i ↦ ∫ x, x ∂P.map (X i)), map_sum, ofReal_sum,
      sum_mul, diagonalStrongDualPi_apply, sum_div, ← sum_sub_distrib, exp_sum]
    congr with i
    rw [(hX1 i).isGaussian_map.charFunDual_eq, integral_complex_ofReal, integral_comp_id_comm,
      covarianceBilinDual_self_eq_variance]
    · simp
    · exact (hX1 i).isGaussian_map.memLp_two_id
    · exact (hX1 i).isGaussian_map.integrable_id

/-- If $(X_i)_{i \in \iota}$ are jointly Gaussian and uncorrelated, then they are independent. -/
/-
**ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_strongDual** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} [Finite ι] {E : ι → Type u_3}   [inst : (i : ι) → NormedAddCommGrou
p (E i)] [inst_1 : (i : ι) → MeasurableSpace (E i)]   [∀ (i : ι), CompleteSpace 
(E i)] [∀ (i : ι), BorelSpace (E i)] [∀ (i : ι), SecondCountableTopology (E i)] 
  [inst_5 : (i : ι) → NormedSpace ℝ (E i)] {X : (i : ι) → Ω → E i},   Probabilit
yTheory.HasGaussianLaw (fun ω i => X i ω) P →     (∀ (i j : ι),         i ≠ j → 
          ∀ (L₁ : StrongDual ℝ (E i)) (L₂ : StrongDual ℝ (E j)),             Pro
babilityTheory.covariance (⇑L₁ ∘ X i) (⇑L₂ ∘ X j) P = 0) →       ProbabilityTheo
ry.iIndepFun X P
参数：i : ι；E i；i : ι；E i；i : ι；E i；i : ι；E i；i : ι；E i；i : ι；E i；i : ι；fun ω i => 
X i ω；∀ (i j : ι),         i ≠ j →           ∀ (L₁ : StrongDual ℝ (E i)) (L₂ : S
trongDual ℝ (E j)),             ProbabilityTheory.covariance (⇑L₁ ∘ X i) (⇑L₂ ∘ 
X j) P = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isProbabilityMeasure`：∀ {Ω : Type u_1} 
{E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : To
pologicalSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.iIndepFun_iff_charFunDual_pi`：iIndepFun_iff_charFunDua
l_pi (hX : forall i, AEMeasurable (X i) P) : iIndepFun X P ↔ forall L, charFunDu
al (P.map (fun ω => (X · ω))) L = ∏ …
· 使用定理 `AEMeasurable.eval`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : Measure
Theory.Measure α} {δ : Type u_6} {X : δ → Type u_7}   {mX : (a : δ) → Measurable
Space (…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.aemeasurable`：∀ {Ω : Type u_1} {E : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topologica
lSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.single_apply`：∀ (R : Type u_1) [inst : Semiring R] {
ι : Type u_4} (φ : ι → Type u_5) [inst_1 : (i : ι) → TopologicalSpace (φ i)]   [
inst_2 : (i : ι) → Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用引理 `LinearMap.sum_single_apply`：sum_single_apply [Fintype ι] [DecidableEq ι]
 (v : Π i, φ i) : ∑ i, Pi.single i (v i) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.HasGaussianLaw.charFunDual_map_eq_fun`：charFunDual_map
_eq_fun (L : StrongDual Real E) (hX : HasGaussianLaw X P) : charFunDual (P.map X
) L = exp ((∫ ω, L (X ω) ∂P) * I - Var[fun ω …
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `ProbabilityTheory.HasGaussianLaw.eval`：eval (hX : HasGaussianLaw (fun ω 
=> (X · ω)) P) (i : ι) : HasGaussianLaw (X i) P
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_finsetSum`：integral_finsetSum {ι} (s : Finset ι) 
{f : ι -> α -> G} (hf : forall i in s, Integrable (f i) μ) : ∫ a, ∑ i in s, f i 
a ∂μ = ∑ i in s, ∫ a, …
· 使用定理 `MeasureTheory.Integrable.ofReal`：∀ {α : Type u_1} {m : MeasurableSpace α
} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : RCLike 𝕜] {f : α → ℝ},   
MeasureTheory.Integra…
· 使用引理 `ProbabilityTheory.HasGaussianLaw.integrable`：integrable [CompleteSpace E
] [SecondCountableTopology E] (hX : HasGaussianLaw X P) : Integrable X P
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map_fun`：map_fun (hX : HasGaussianLaw X
 P) (L : E ->L[Real] F) : HasGaussianLaw (fun ω => L (X ω)) P
· 使用引理 `ProbabilityTheory.variance_fun_sum`：variance_fun_sum [IsFiniteMeasure μ]
 [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) : Var[fun ω => ∑ i, X i ω; μ] = ∑ 
i, ∑ j, cov[X i, X j; μ]
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If $(X_i)_{i \in \iota}$ are jointly Gaussian and uncorrelated, then they are in
dependent.
-/
lemma HasGaussianLaw.iIndepFun_of_covariance_strongDual (hX : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h : ∀ i j, i ≠ j → ∀ (L₁ : StrongDual ℝ (E i)) (L₂ : StrongDual ℝ (E j)),
      cov[L₁ ∘ (X i), L₂ ∘ (X j); P] = 0) :
    iIndepFun X P := by
  simp_rw [Function.comp_def] at h
  have := hX.isProbabilityMeasure
  classical
  let := Fintype.ofFinite ι
  rw [iIndepFun_iff_charFunDual_pi fun i ↦ hX.aemeasurable.eval i]
  intro L
  have this ω : L (X · ω) = ∑ i, (L ∘L (single ℝ E i)) (X i ω) := by
    simp [← map_sum, LinearMap.sum_single_apply]
  simp_rw [hX.charFunDual_map_eq_fun, fun i ↦ (hX.eval i).charFunDual_map_eq_fun, ← Complex.exp_sum,
    sum_sub_distrib, ← sum_mul, this]
  congr
  · simp_rw [← Complex.ofReal_sum]
    rw [integral_finsetSum _ fun i _ ↦ ((hX.eval i).map_fun _).integrable.ofReal]
  · rw [variance_fun_sum fun i ↦ ((hX.eval i).map_fun _).memLp_two]
    simp only [← sum_div, ← ofReal_sum, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_left_inj', ofReal_inj]
    congr with i
    rw [sum_eq_single_of_mem i (by grind) (fun j _ hij ↦ h i j hij.symm _ _),
      covariance_self ((hX.eval i).map_fun _).aemeasurable]

end NormedSpace

section InnerProductSpace

variable [∀ i, InnerProductSpace ℝ (E i)]

/-- If $(X_i)_{i \in \iota}$ are jointly Gaussian and uncorrelated, then they are independent. -/
/-
**ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_inner** 是 Mathlib 中的一
个定理，位于命名空间 `ProbabilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} [Finite ι] {E : ι → Type u_3}   [inst : (i : ι) → NormedAddCommGrou
p (E i)] [inst_1 : (i : ι) → MeasurableSpace (E i)]   [∀ (i : ι), CompleteSpace 
(E i)] [∀ (i : ι), BorelSpace (E i)] [∀ (i : ι), SecondCountableTopology (E i)] 
  [inst_5 : (i : ι) → InnerProductSpace ℝ (E i)] {X : (i : ι) → Ω → E i},   Prob
abilityTheory.HasGaussianLaw (fun ω i => X i ω) P →     (∀ (i j : ι),         i 
≠ j →           ∀ (x : E i) (y : E j),             ProbabilityTheory.covariance 
(fun ω => inner ℝ x (X i ω)) (fun ω => inner ℝ y (X j ω)) P = 0) →       Probabi
lityTheory.iIndepFun X P
参数：i : ι；E i；i : ι；E i；i : ι；E i；i : ι；E i；i : ι；E i；i : ι；E i；i : ι；fun ω i => 
X i ω；∀ (i j : ι),         i ≠ j →           ∀ (x : E i) (y : E j),             
ProbabilityTheory.covariance (fun ω => inner ℝ x (X i ω)) (fun ω => inner ℝ y (X
 j ω)) P = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_strongDual`：∀ {
Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u
_2} [Finite ι] {E : ι → Type u_3}   [inst : (i : ι) → Nor…
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `InnerProductSpace.toDual_symm_apply`：toDual_symm_apply {x : E} {y : Stro
ngDual 𝕜 E} : ⟪(toDual 𝕜 E).symm y, x⟫ = y x

--- 原说明 ---
If $(X_i)_{i \in \iota}$ are jointly Gaussian and uncorrelated, then they are in
dependent.
-/
lemma HasGaussianLaw.iIndepFun_of_covariance_inner
    {X : Π i, Ω → (E i)} (hX : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h : ∀ i j, i ≠ j → ∀ (x : E i) (y : E j),
      cov[fun ω ↦ ⟪x, X i ω⟫, fun ω ↦ ⟪y, X j ω⟫; P] = 0) :
    iIndepFun X P :=
  hX.iIndepFun_of_covariance_strongDual fun i j hij L₁ L₂ ↦ by
    simpa using! h i j hij ((toDual ℝ (E i)).symm L₁) ((toDual ℝ (E j)).symm L₂)

end InnerProductSpace

section Real

/-- If $((X_{i,j})_{j \in \kappa_i})_{i \in \iota}$ are jointly Gaussian, then they are independent
if for all $i_1 \ne i_2 \in \iota$ and for all $j_1 \in \kappa_{i_1}, j_2 \in \kappa_{i_2}$,
$\mathrm{Cov}(X_{i_1, j_1}, X_{i_2, j_2}) = 0$. -/
/-
**ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_eval** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} [Finite ι] {κ : ι → Type u_4}   [∀ (i : ι), Finite (κ i)] {X : (i :
 ι) → κ i → Ω → ℝ},   ProbabilityTheory.HasGaussianLaw (fun ω i j => X i j ω) P 
→     (∀ (i j : ι), i ≠ j → ∀ (k : κ i) (l : κ j), ProbabilityTheory.covariance 
(X i k) (X j l) P = 0) →       ProbabilityTheory.iIndepFun (fun i ω j => X i j ω
) P
参数：i : ι；κ i；i : ι；fun ω i j => X i j ω；∀ (i j : ι), i ≠ j → ∀ (k : κ i) (l : κ 
j), ProbabilityTheory.covariance (X i k) (X j l) P = 0；fun i ω j => X i j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isProbabilityMeasure`：∀ {Ω : Type u_1} 
{E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : To
pologicalSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.iIndepFun.comp`：∀ {Ω : Type u_1} {ι : Type u_2} {_mΩ :
 MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type u_10}   {γ : ι →
 Type u_11} {mβ : (i :…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_inner`：∀ {Ω : T
ype u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2} [
Finite ι] {E : ι → Type u_3}   [inst : (i : ι) → Nor…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map_equiv`：map_equiv (hX : HasGaussianL
aw X P) (L : E ≃L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.sum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLik
e 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpac
e 𝕜 E] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用引理 `ProbabilityTheory.covariance_fun_sum_fun_sum`：covariance_fun_sum_fun_sum
 [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' -> Ω -> Real} (hX : forall i, Mem
Lp (X i) 2 μ) (hY : forall i, MemL…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `EuclideanSpace.basisFun_inner`：basisFun_inner (x : EuclideanSpace 𝕜 ι) (
i : ι) : ⟪basisFun ι 𝕜 i, x⟫ = x i
· 使用定理 `MeasureTheory.MemLp.const_mul`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {𝕜 : Type u_3}   [inst : NormedRing 
𝕜] {f : α → 𝕜}, Mea…
· 使用引理 `ProbabilityTheory.HasGaussianLaw.memLp_two`：memLp_two [CompleteSpace E] 
[SecondCountableTopology E] (hX : HasGaussianLaw X P) : MemLp X 2 P
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If $((X_{i,j})_{j \in \kappa_i})_{i \in \iota}$ are jointly Gaussian, then they 
are independent
if for all $i_1 \ne i_2 \in \iota$ and for all $j_1 \in \kappa_{i_1}, j_2 \in \k
appa_{i_2}$,
$\mathrm{Cov}(X_{i_1, j_1}, X_{i_2, j_2}) = 0$.
-/
lemma HasGaussianLaw.iIndepFun_of_covariance_eval {κ : ι → Type*} [∀ i, Finite (κ i)]
    {X : (i : ι) → κ i → Ω → ℝ} (hX : HasGaussianLaw (fun ω i j ↦ X i j ω) P)
    (h : ∀ i j, i ≠ j → ∀ k l, cov[X i k, X j l; P] = 0) :
    iIndepFun (fun i ω j ↦ X i j ω) P := by
  have := hX.isProbabilityMeasure
  have : (fun i ω j ↦ X i j ω) = fun i ↦ (ofLp ∘ (toLp 2 ∘ fun ω j ↦ X i j ω)) := by ext; simp
  rw [this]
  let (i : ι) := Fintype.ofFinite (κ i)
  let := Fintype.ofFinite ι
  refine (HasGaussianLaw.iIndepFun_of_covariance_inner ?_ fun i j hij x y ↦ ?_).comp _ (by fun_prop)
  · exact hX.map_equiv (.piCongrRight (fun _ ↦ (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm))
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x, ← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ ↦ sum_eq_zero fun l _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, h i j hij k l, mul_zero, mul_zero]
  · simpa using fun j ↦ ((hX.eval i).eval j).memLp_two.const_mul _
  · simpa using fun i ↦ ((hX.eval j).eval i).memLp_two.const_mul _

/-- If $(X_i)_{i \in \iota}$ are jointly Gaussian, then they are independent if for all $i \ne j$,
$\mathrm{Cov}(X_i, X_j) = 0$. -/
/-
**ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_eq_zero** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_2} [Finite ι] {X : ι → Ω → ℝ},   ProbabilityTheory.HasGaussianLaw (fun
 ω x => X x ω) P →     (∀ (i j : ι), i ≠ j → ProbabilityTheory.covariance (X i) 
(X j) P = 0) → ProbabilityTheory.iIndepFun X P
参数：fun ω x => X x ω；∀ (i j : ι), i ≠ j → ProbabilityTheory.covariance (X i) (X j
) P = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_strongDual`：∀ {
Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u
_2} [Finite ι] {E : ι → Type u_3}   [inst : (i : ι) → Nor…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用引理 `ProbabilityTheory.covariance_mul_const_right`：covariance_mul_const_right
 (c : Real) : cov[X, fun ω => Y ω * c; μ] = cov[X, Y; μ] * c
· 使用引理 `ProbabilityTheory.covariance_mul_const_left`：covariance_mul_const_left (
c : Real) : cov[fun ω => X ω * c, Y; μ] = cov[X, Y; μ] * c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If $(X_i)_{i \in \iota}$ are jointly Gaussian, then they are independent if for 
all $i \ne j$,
$\mathrm{Cov}(X_i, X_j) = 0$.
-/
lemma HasGaussianLaw.iIndepFun_of_covariance_eq_zero {X : ι → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (h : ∀ i j : ι, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P :=
  hX.iIndepFun_of_covariance_strongDual fun i j hij L₁ L₂ ↦ by
    simp [Function.comp_def, ← toDual_symm_apply, covariance_mul_const_right,
      covariance_mul_const_left, h, hij]

end Real

end iIndepFun

section IndepFun

variable {E F : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [MeasurableSpace F]
    [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- Independent Gaussian random variables are jointly Gaussian. -/
/-
**ProbabilityTheory.IndepFun.hasGaussianLaw** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E
 : Type u_2} {F : Type u_3}   [inst : NormedAddCommGroup E] [inst_1 : Measurable
Space E] [CompleteSpace E] [BorelSpace E]   [SecondCountableTopology E] [inst_5 
: NormedAddCommGroup F] [inst_6 : MeasurableSpace F] [CompleteSpace F]   [BorelS
pace F] [SecondCountableTopology F] [inst_10 : NormedSpace ℝ E] [inst_11 : Norme
dSpace ℝ F] {X : Ω → E}   {Y : Ω → F},   ProbabilityTheory.HasGaussianLaw X P → 
    ProbabilityTheory.HasGaussianLaw Y P →       ProbabilityTheory.IndepFun X Y 
P → ProbabilityTheory.HasGaussianLaw (fun ω => (X ω, Y ω)) P
参数：fun ω => (X ω, Y ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isProbabilityMeasure`：∀ {Ω : Type u_1} 
{E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : To
pologicalSpace E]   [inst_1 : AddCommMonoid…
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.isGaussian_iff_gaussian_charFunDual`：isGaussian_iff_ga
ussian_charFunDual [IsFiniteMeasure μ] : IsGaussian μ ↔ exists (m : E) (f : Stro
ngDual Real E ->L[Real] StrongDual Real E -…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `_private.Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Indep
endence.0.ContinuousLinearMap.isPosSemidef_diagonalStrongDualProd`：∀ {E : Type u
_2} {F : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [ins
t_2 : NormedAddCommGroup F]   [inst_3 : NormedS…
· 使用引理 `ProbabilityTheory.isPosSemidef_covarianceBilinDual`：isPosSemidef_covaria
nceBilinDual : (covarianceBilinDual μ).toBilinForm.IsPosSemidef where eq
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.indepFun_iff_charFunDual_prod`：indepFun_iff_charFunDua
l_prod (hX : AEMeasurable X P) (hY : AEMeasurable Y P) : X ⟂ᵢ[P] Y ↔ forall L, c
harFunDual (P.map (fun ω => (X ω, Y ω…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.aemeasurable`：∀ {Ω : Type u_1} {E : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topologica
lSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Independent Gaussian random variables are jointly Gaussian.
-/
lemma IndepFun.hasGaussianLaw [NormedSpace ℝ E] [NormedSpace ℝ F] {X : Ω → E} {Y : Ω → F}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (hXY : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P where
  isGaussian_map := by
    have := hX.isProbabilityMeasure
    rw [isGaussian_iff_gaussian_charFunDual]
    refine ⟨(∫ x, x ∂P.map X, ∫ y, y ∂P.map Y),
      .diagonalStrongDualProd (covarianceBilinDual (P.map X)) (covarianceBilinDual (P.map Y)),
      isPosSemidef_diagonalStrongDualProd isPosSemidef_covarianceBilinDual
        isPosSemidef_covarianceBilinDual, fun L ↦ ?_⟩
    rw [(indepFun_iff_charFunDual_prod (by fun_prop) (by fun_prop)).1 hXY]
    have : (∫ x, x ∂Measure.map X P, ∫ y, y ∂Measure.map Y P) =
        ContinuousLinearMap.inl ℝ E F (∫ x, x ∂Measure.map X P) +
        ContinuousLinearMap.inr ℝ E F (∫ y, y ∂Measure.map Y P) := by simp
    simp only [this, map_add, ofReal_add, add_mul, diagonalStrongDualProd_apply, add_div,
      add_sub_add_comm, exp_add]
    congr
    · rw [hX.isGaussian_map.charFunDual_eq, integral_complex_ofReal, integral_comp_id_comm,
        covarianceBilinDual_self_eq_variance]
      · simp
      · exact hX.isGaussian_map.memLp_two_id
      · exact hX.isGaussian_map.integrable_id
    · rw [hY.isGaussian_map.charFunDual_eq, integral_complex_ofReal, integral_comp_id_comm,
        covarianceBilinDual_self_eq_variance]
      · simp
      · exact hY.isGaussian_map.memLp_two_id
      · exact hY.isGaussian_map.integrable_id

/-- If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if they are uncorrelated. -/
/-
**ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_strongDual** 是 Mathlib
 中的一个定理，位于命名空间 `ProbabilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E
 : Type u_2} {F : Type u_3}   [inst : NormedAddCommGroup E] [inst_1 : Measurable
Space E] [CompleteSpace E] [BorelSpace E]   [SecondCountableTopology E] [inst_5 
: NormedAddCommGroup F] [inst_6 : MeasurableSpace F] [CompleteSpace F]   [BorelS
pace F] [SecondCountableTopology F] [inst_10 : NormedSpace ℝ E] [inst_11 : Norme
dSpace ℝ F] {X : Ω → E}   {Y : Ω → F},   ProbabilityTheory.HasGaussianLaw (fun ω
 => (X ω, Y ω)) P →     (∀ (L₁ : StrongDual ℝ E) (L₂ : StrongDual ℝ F), Probabil
ityTheory.covariance (⇑L₁ ∘ X) (⇑L₂ ∘ Y) P = 0) →       ProbabilityTheory.IndepF
un X Y P
参数：fun ω => (X ω, Y ω)；∀ (L₁ : StrongDual ℝ E) (L₂ : StrongDual ℝ F), Probabilit
yTheory.covariance (⇑L₁ ∘ X) (⇑L₂ ∘ Y) P = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isProbabilityMeasure`：∀ {Ω : Type u_1} 
{E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : To
pologicalSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.indepFun_iff_charFunDual_prod`：indepFun_iff_charFunDua
l_prod (hX : AEMeasurable X P) (hY : AEMeasurable Y P) : X ⟂ᵢ[P] Y ↔ forall L, c
harFunDual (P.map (fun ω => (X ω, Y ω…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.aemeasurable`：∀ {Ω : Type u_1} {E : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topologica
lSpace E]   [inst_1 : AddCommMonoid…
· 使用引理 `ProbabilityTheory.HasGaussianLaw.fst`：fst (hXY : HasGaussianLaw (fun ω =
> (X ω, Y ω)) P) : HasGaussianLaw X P
· 使用引理 `ProbabilityTheory.HasGaussianLaw.snd`：snd (hXY : HasGaussianLaw (fun ω =
> (X ω, Y ω)) P) : HasGaussianLaw Y P
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.HasGaussianLaw.charFunDual_map_eq`：charFunDual_map_eq 
(L : StrongDual Real E) (hX : HasGaussianLaw X P) : charFunDual (P.map X) L = ex
p ((P[L ∘ X] : Real) * I - Var[L ∘ X; P] …
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `sub_add_sub_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a - b + (c - d) = a + c - (b + d)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用引理 `ProbabilityTheory.HasGaussianLaw.integrable`：integrable [CompleteSpace E
] [SecondCountableTopology E] (hX : HasGaussianLaw X P) : Integrable X P
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用引理 `ProbabilityTheory.variance_add`：variance_add [IsFiniteMeasure μ] (hX : M
emLp X 2 μ) (hY : MemLp Y 2 μ) : Var[X + Y; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + 
Var[Y; μ]
· 使用引理 `ProbabilityTheory.HasGaussianLaw.memLp_two`：memLp_two [CompleteSpace E] 
[SecondCountableTopology E] (hX : HasGaussianLaw X P) : MemLp X 2 P
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if they are uncorrelat
ed.
-/
lemma HasGaussianLaw.indepFun_of_covariance_strongDual [NormedSpace ℝ E] [NormedSpace ℝ F]
    {X : Ω → E} {Y : Ω → F} (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h : ∀ (L₁ : StrongDual ℝ E) (L₂ : StrongDual ℝ F), cov[L₁ ∘ X, L₂ ∘ Y; P] = 0) :
    IndepFun X Y P := by
  have := hXY.isProbabilityMeasure
  rw [indepFun_iff_charFunDual_prod hXY.fst.aemeasurable hXY.snd.aemeasurable]
  intro L
  have : L ∘ (fun ω ↦ (X ω, Y ω)) = (L ∘L (.inl ℝ E F)) ∘ X + (L ∘L (.inr ℝ E F)) ∘ Y := by
    ext; simp [-comp_apply, ← comp_inl_add_comp_inr]
  rw [hXY.charFunDual_map_eq, hXY.fst.charFunDual_map_eq, hXY.snd.charFunDual_map_eq, ← exp_add,
    sub_add_sub_comm, ← add_mul, ← ofReal_add, ← integral_add, ← add_div, ← ofReal_add, this,
    variance_add, h, mul_zero, add_zero]
  · simp
  · exact (hXY.fst.map _).memLp_two
  · exact (hXY.snd.map _).memLp_two
  · exact (hXY.fst.map _).integrable
  · exact (hXY.snd.map _).integrable

/-- If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if they are uncorrelated. -/
/-
**ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_inner** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E
 : Type u_2} {F : Type u_3}   [inst : NormedAddCommGroup E] [inst_1 : Measurable
Space E] [CompleteSpace E] [BorelSpace E]   [SecondCountableTopology E] [inst_5 
: NormedAddCommGroup F] [inst_6 : MeasurableSpace F] [CompleteSpace F]   [BorelS
pace F] [SecondCountableTopology F] [inst_10 : InnerProductSpace ℝ E] [inst_11 :
 InnerProductSpace ℝ F]   {X : Ω → E} {Y : Ω → F},   ProbabilityTheory.HasGaussi
anLaw (fun ω => (X ω, Y ω)) P →     (∀ (x : E) (y : F), ProbabilityTheory.covari
ance (fun ω => inner ℝ x (X ω)) (fun ω => inner ℝ y (Y ω)) P = 0) →       Probab
ilityTheory.IndepFun X Y P
参数：fun ω => (X ω, Y ω)；∀ (x : E) (y : F), ProbabilityTheory.covariance (fun ω =>
 inner ℝ x (X ω)) (fun ω => inner ℝ y (Y ω)) P = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_strongDual`：∀ {Ω
 : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E : Type u_
2} {F : Type u_3}   [inst : NormedAddCommGroup E] [inst_…
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `InnerProductSpace.toDual_symm_apply`：toDual_symm_apply {x : E} {y : Stro
ngDual 𝕜 E} : ⟪(toDual 𝕜 E).symm y, x⟫ = y x

--- 原说明 ---
If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if they are uncorrelat
ed.
-/
lemma HasGaussianLaw.indepFun_of_covariance_inner [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    {X : Ω → E} {Y : Ω → F} (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h : ∀ x y, cov[fun ω ↦ ⟪x, X ω⟫, fun ω ↦ ⟪y, Y ω⟫; P] = 0) :
    IndepFun X Y P :=
  hXY.indepFun_of_covariance_strongDual fun L₁ L₂ ↦ by
    simpa using! h ((toDual ℝ E).symm L₁) ((toDual ℝ F).symm L₂)

/-- If $((X_i)_{i \in \iota}, (Y_j)_{j \in \kappa})$ is Gaussian, then $(X_i)_{i \in \iota}$ and
$(Y_j)_{j \in \kappa}$ are independent if for all $i \in \iota, j \in \kappa$,
$\mathrm{Cov}(X_i, Y_j) = 0$. -/
/-
**ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_eval** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι
 : Type u_4} {κ : Type u_5} [Finite ι]   [Finite κ] {X : ι → Ω → ℝ} {Y : κ → Ω →
 ℝ},   ProbabilityTheory.HasGaussianLaw (fun ω => (fun i => X i ω, fun j => Y j 
ω)) P →     (∀ (i : ι) (j : κ), ProbabilityTheory.covariance (X i) (Y j) P = 0) 
→       ProbabilityTheory.IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) P
参数：fun ω => (fun i => X i ω, fun j => Y j ω)；∀ (i : ι) (j : κ), ProbabilityTheor
y.covariance (X i) (Y j) P = 0；fun ω i => X i ω；fun ω j => Y j ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isProbabilityMeasure`：∀ {Ω : Type u_1} 
{E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : To
pologicalSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IndepFun.comp`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {γ : Type u_8} {γ' : Type u_9} {_mΩ : MeasurableSpace Ω}   {μ : Measure
Theory.Measure Ω} {f …
· 使用定理 `ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_inner`：∀ {Ω : Ty
pe u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E : Type u_2} {F
 : Type u_3}   [inst : NormedAddCommGroup E] [inst_…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map_equiv`：map_equiv (hX : HasGaussianL
aw X P) (L : E ≃L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.sum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLik
e 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpac
e 𝕜 E] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用引理 `ProbabilityTheory.covariance_fun_sum_fun_sum`：covariance_fun_sum_fun_sum
 [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' -> Ω -> Real} (hX : forall i, Mem
Lp (X i) 2 μ) (hY : forall i, MemL…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `EuclideanSpace.basisFun_inner`：basisFun_inner (x : EuclideanSpace 𝕜 ι) (
i : ι) : ⟪basisFun ι 𝕜 i, x⟫ = x i
· 使用定理 `MeasureTheory.MemLp.const_mul`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {𝕜 : Type u_3}   [inst : NormedRing 
𝕜] {f : α → 𝕜}, Mea…
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If $((X_i)_{i \in \iota}, (Y_j)_{j \in \kappa})$ is Gaussian, then $(X_i)_{i \in
 \iota}$ and
$(Y_j)_{j \in \kappa}$ are independent if for all $i \in \iota, j \in \kappa$,
$\mathrm{Cov}(X_i, Y_j) = 0$.
-/
lemma HasGaussianLaw.indepFun_of_covariance_eval {ι κ : Type*} [Finite ι] [Finite κ]
    {X : ι → Ω → ℝ} {Y : κ → Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω)) P)
    (h : ∀ i j, cov[X i, Y j; P] = 0) :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P := by
  have := hXY.isProbabilityMeasure
  have hX : (fun ω i ↦ X i ω) = (ofLp ∘ (toLp 2 ∘ fun ω i ↦ X i ω)) := by ext; simp
  have hY : (fun ω j ↦ Y j ω) = (ofLp ∘ (toLp 2 ∘ fun ω j ↦ Y j ω)) := by ext; simp
  rw [hX, hY]
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  refine IndepFun.comp (HasGaussianLaw.indepFun_of_covariance_inner ?_ fun x y ↦ ?_)
    (by fun_prop) (by fun_prop)
  · exact hXY.map_equiv (.prodCongr (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm)
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x, ← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ ↦ sum_eq_zero fun l _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, h, mul_zero, mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
    EuclideanSpace.basisFun_inner]
    exact fun i ↦ (hXY.fst.eval i).memLp_two.const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun j ↦ (hXY.snd.eval j).memLp_two.const_mul _

/-- If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if $\mathrm{Cov}(X, Y) = 0$. -/
/-
**ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_eq_zero** 是 Mathlib 中的
一个定理，位于命名空间 `ProbabilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {X
 Y : Ω → ℝ},   ProbabilityTheory.HasGaussianLaw (fun ω => (X ω, Y ω)) P →     Pr
obabilityTheory.covariance X Y P = 0 → ProbabilityTheory.IndepFun X Y P
参数：fun ω => (X ω, Y ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_strongDual`：∀ {Ω
 : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E : Type u_
2} {F : Type u_3}   [inst : NormedAddCommGroup E] [inst_…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用引理 `ProbabilityTheory.covariance_mul_const_right`：covariance_mul_const_right
 (c : Real) : cov[X, fun ω => Y ω * c; μ] = cov[X, Y; μ] * c
· 使用引理 `ProbabilityTheory.covariance_mul_const_left`：covariance_mul_const_left (
c : Real) : cov[fun ω => X ω * c, Y; μ] = cov[X, Y; μ] * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if $\mathrm{Cov}(X, Y)
 = 0$.
-/
lemma HasGaussianLaw.indepFun_of_covariance_eq_zero {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) (h : cov[X, Y; P] = 0) :
    IndepFun X Y P :=
  hXY.indepFun_of_covariance_strongDual fun L₁ L₂ ↦ by
    simp [Function.comp_def, ← toDual_symm_apply, covariance_mul_const_right,
      covariance_mul_const_left, h]

end IndepFun

section AddSub

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-
**ProbabilityTheory.iIndepFun.hasGaussianLaw_sum** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E
 : Type u_2} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [inst_2 
: MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E
]   {ι : Type u_3} [inst_6 : Fintype ι] {X : ι → Ω → E},   (∀ (i : ι), Probabili
tyTheory.HasGaussianLaw (X i) P) →     ProbabilityTheory.iIndepFun X P → Probabi
lityTheory.HasGaussianLaw (∑ i, X i) P
参数：∀ (i : ι), ProbabilityTheory.HasGaussianLaw (X i) P；∑ i, X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.sum`：sum {E : Type*} [NormedAddCommGrou
p E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTop
ology E] {X : ι -> Ω -> E}…
· 使用定理 `ProbabilityTheory.iIndepFun.hasGaussianLaw`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2} [Finite ι] {E : ι → T
ype u_3}   [inst : (i : ι) → Nor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma iIndepFun.hasGaussianLaw_sum [CompleteSpace E] {ι : Type*} [Fintype ι] {X : ι → Ω → E}
    (hX1 : ∀ i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P) :
    HasGaussianLaw (∑ i, X i) P :=
  (hX2.hasGaussianLaw hX1).sum
/-
**ProbabilityTheory.iIndepFun.hasGaussianLaw_fun_sum** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E
 : Type u_2} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [inst_2 
: MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E
]   {ι : Type u_3} [inst_6 : Fintype ι] {X : ι → Ω → E},   (∀ (i : ι), Probabili
tyTheory.HasGaussianLaw (X i) P) →     ProbabilityTheory.iIndepFun X P → Probabi
lityTheory.HasGaussianLaw (fun ω => ∑ i, X i ω) P
参数：∀ (i : ι), ProbabilityTheory.HasGaussianLaw (X i) P；fun ω => ∑ i, X i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.fun_sum`：fun_sum {E : Type*} [NormedAdd
CommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E] [SecondCoun
tableTopology E] {X : ι -> Ω -…
· 使用定理 `ProbabilityTheory.iIndepFun.hasGaussianLaw`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u_2} [Finite ι] {E : ι → T
ype u_3}   [inst : (i : ι) → Nor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma iIndepFun.hasGaussianLaw_fun_sum [CompleteSpace E] {ι : Type*} [Fintype ι] {X : ι → Ω → E}
    (hX1 : ∀ i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P) :
    HasGaussianLaw (fun ω ↦ ∑ i, X i ω) P :=
    (hX2.hasGaussianLaw hX1).fun_sum
/-
**ProbabilityTheory.iIndepFun.hasGaussianLaw_add** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E
 : Type u_2} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [inst_2 
: MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E
]   {X Y : Ω → E},   ProbabilityTheory.HasGaussianLaw X P →     ProbabilityTheor
y.HasGaussianLaw Y P → ProbabilityTheory.IndepFun X Y P → ProbabilityTheory.HasG
aussianLaw (X + Y) P
参数：X + Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.add`：add (hXY : HasGaussianLaw (fun ω =
> (X ω, Y ω)) P) : HasGaussianLaw (X + Y) P
· 使用定理 `ProbabilityTheory.IndepFun.hasGaussianLaw`：∀ {Ω : Type u_1} {mΩ : Measur
ableSpace Ω} {P : MeasureTheory.Measure Ω} {E : Type u_2} {F : Type u_3}   [inst
 : NormedAddCommGroup E] [inst_…
-/
lemma iIndepFun.hasGaussianLaw_add [CompleteSpace E] {X Y : Ω → E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (X + Y) P :=
  (h.hasGaussianLaw hX hY).add
/-
**ProbabilityTheory.iIndepFun.hasGaussianLaw_fun_add** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E
 : Type u_2} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [inst_2 
: MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E
]   {X Y : Ω → E},   ProbabilityTheory.HasGaussianLaw X P →     ProbabilityTheor
y.HasGaussianLaw Y P →       ProbabilityTheory.IndepFun X Y P → ProbabilityTheor
y.HasGaussianLaw (fun ω => X ω + Y ω) P
参数：fun ω => X ω + Y ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.add`：add (hXY : HasGaussianLaw (fun ω =
> (X ω, Y ω)) P) : HasGaussianLaw (X + Y) P
· 使用定理 `ProbabilityTheory.IndepFun.hasGaussianLaw`：∀ {Ω : Type u_1} {mΩ : Measur
ableSpace Ω} {P : MeasureTheory.Measure Ω} {E : Type u_2} {F : Type u_3}   [inst
 : NormedAddCommGroup E] [inst_…
-/
lemma iIndepFun.hasGaussianLaw_fun_add [CompleteSpace E] {X Y : Ω → E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (fun ω ↦ X ω + Y ω) P :=
  (h.hasGaussianLaw hX hY).add
/-
**ProbabilityTheory.iIndepFun.hasGaussianLaw_sub** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E
 : Type u_2} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [inst_2 
: MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E
]   {X Y : Ω → E},   ProbabilityTheory.HasGaussianLaw X P →     ProbabilityTheor
y.HasGaussianLaw Y P → ProbabilityTheory.IndepFun X Y P → ProbabilityTheory.HasG
aussianLaw (X - Y) P
参数：X - Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.sub`：sub (hXY : HasGaussianLaw (fun ω =
> (X ω, Y ω)) P) : HasGaussianLaw (X - Y) P
· 使用定理 `ProbabilityTheory.IndepFun.hasGaussianLaw`：∀ {Ω : Type u_1} {mΩ : Measur
ableSpace Ω} {P : MeasureTheory.Measure Ω} {E : Type u_2} {F : Type u_3}   [inst
 : NormedAddCommGroup E] [inst_…
-/
lemma iIndepFun.hasGaussianLaw_sub [CompleteSpace E] {X Y : Ω → E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (X - Y) P :=
  (h.hasGaussianLaw hX hY).sub
/-
**ProbabilityTheory.iIndepFun.hasGaussianLaw_fun_sub** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E
 : Type u_2} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [inst_2 
: MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E
]   {X Y : Ω → E},   ProbabilityTheory.HasGaussianLaw X P →     ProbabilityTheor
y.HasGaussianLaw Y P →       ProbabilityTheory.IndepFun X Y P → ProbabilityTheor
y.HasGaussianLaw (fun ω => X ω - Y ω) P
参数：fun ω => X ω - Y ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.sub`：sub (hXY : HasGaussianLaw (fun ω =
> (X ω, Y ω)) P) : HasGaussianLaw (X - Y) P
· 使用定理 `ProbabilityTheory.IndepFun.hasGaussianLaw`：∀ {Ω : Type u_1} {mΩ : Measur
ableSpace Ω} {P : MeasureTheory.Measure Ω} {E : Type u_2} {F : Type u_3}   [inst
 : NormedAddCommGroup E] [inst_…
-/
lemma iIndepFun.hasGaussianLaw_fun_sub [CompleteSpace E] {X Y : Ω → E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (fun ω ↦ X ω - Y ω) P :=
  (h.hasGaussianLaw hX hY).sub

/-- If `X` and `Y` are two Gaussian random variables such that `X` and `Y - X` are independent,
then `Y - X` is Gaussian.

This lemma is useful to prove that a process with independent increments and whose marginals
are Gaussian has Gaussian increments. -/
/-
**ProbabilityTheory.IndepFun.hasGaussianLaw_sub_of_sub** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E
 : Type u_2} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [inst_2 
: MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {X Y : Ω → E},  
 ProbabilityTheory.HasGaussianLaw X P →     ProbabilityTheory.HasGaussianLaw Y P
 →       ProbabilityTheory.IndepFun X (Y - X) P → ProbabilityTheory.HasGaussianL
aw (Y - X) P
参数：Y - X；Y - X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isProbabilityMeasure`：∀ {Ω : Type u_1} 
{E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : To
pologicalSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.hasGaussianLaw_iff_charFunDual_map_eq`：∀ {Ω : Type u_1
} {E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : 
NormedAddCommGroup E]   [inst_1 : MeasurableS…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AEMeasurable.sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSpac
e G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   {μ : MeasureTheory
.Measu…
· 使用定理 `ContinuousSub.measurableSub₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Sub γ] [Con…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ProbabilityTheory.HasGaussianLaw.aemeasurable`：∀ {Ω : Type u_1} {E : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topologica
lSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.HasGaussianLaw.charFunDual_map_eq`：charFunDual_map_eq 
(L : StrongDual Real E) (hX : HasGaussianLaw X P) : charFunDual (P.map X) L = ex
p ((P[L ∘ X] : Real) * I - Var[L ∘ X; P] …
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `ProbabilityTheory.IndepFun.charFunDual_map_add_eq_mul`：∀ {Ω : Type u_1} 
{mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMe
asure P] {E : Type u_2}   {mE : MeasurableS…
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `sub_add_sub_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a - b + (c - d) = a + c - (b + d)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
If `X` and `Y` are two Gaussian random variables such that `X` and `Y - X` are i
ndependent,
then `Y - X` is Gaussian.

This lemma is useful to prove that a process with independent increments and who
se marginals
are Gaussian has Gaussian increments.
-/
lemma IndepFun.hasGaussianLaw_sub_of_sub {X Y : Ω → E} (hX : HasGaussianLaw X P)
    (hY : HasGaussianLaw Y P) (h : IndepFun X (Y - X) P) :
    HasGaussianLaw (Y - X) P := by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  rw [hasGaussianLaw_iff_charFunDual_map_eq (by fun_prop)]
  intro L
  apply mul_left_cancel₀ (a := charFunDual (P.map X) L)
  · simp [hX.charFunDual_map_eq]
  rw [← Pi.mul_apply, ← h.charFunDual_map_add_eq_mul, add_sub_cancel, hX.charFunDual_map_eq,
    ← exp_add, sub_add_sub_comm, ← add_mul, ← ofReal_add, ← integral_add, ← add_div, ← ofReal_add,
    ← IndepFun.variance_add, hY.charFunDual_map_eq]
  · congr with ω <;> simp
  any_goals fun_prop
  · exact (hX.map L).memLp_two
  · rw [map_comp_sub]
    exact (hY.map L).memLp_two.sub (hX.map L).memLp_two
  · exact h.comp (by fun_prop) (by fun_prop)
  · exact (hX.map L).integrable
  · rw [map_comp_sub]
    exact (hY.map L).integrable.sub (hX.map L).integrable

end AddSub

end ProbabilityTheory

