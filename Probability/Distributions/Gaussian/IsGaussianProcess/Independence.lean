/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.Process.Basic

/-!
# Independence of Gaussian processes

This file contains properties about independence of Gaussian processes. More precisely, we prove
different versions of the following statement: if some stochastic processes are jointly Gaussian,
then they are independent if their marginals are uncorrelated.

## Main statements

* `iIndepFun_of_covariance_eq_zero`: Assume that the processes $((X^t_s)_{s \in S_t})_{t \in T}$
  are jointly Gaussian. Then they are independent if for all $t_1, t_2 \in T$ with $t_1 \ne t_2$
  and $s_1 \in S_{t_1}$, $s_2 \in S_{t_2}$, $\mathrm{Cov}(X^{t_1}_{s_1}, X^{t_2}_{s_2} = 0$.

* `indepFun_of_covariance_eq_zero`: Two Gaussian processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$
  that are jointly Gaussian are independent if for all $s \in S$ and $t \in T$,
  $\mathrm{Cov}(X_s, Y_t) = 0$.

## Implementation note

To talk about the joint process of two processes `X : S → Ω → E` and `Y : T → Ω → E`,
we consider the process `Sum.elim X Y : S ⊕ T → Ω → E`, where `S ⊕ T` is
the disjoint union of `S` and `T`, `Sum S T`.

Similarly, the joint process of a family of stochastic processes `X : (t : T) → (s : S t) → Ω → E`
is the process `(p : (t : T) × S t) ↦ X p.1 p.2`, where `(t : T) × S t` is the type of dependent
pairs `Sigma`.

## Tags

Gaussian process, independence
-/

public section

open MeasureTheory InnerProductSpace Finset
open scoped ENNReal NNReal RealInnerProductSpace

namespace ProbabilityTheory.IsGaussianProcess

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]

section iIndepFun

variable {S : T → Type*} {X : (t : T) → (s : S t) → Ω → E}

/-- Assume that the processes $((X^t_s)_{s \in S_t})_{t \in T}$ are jointly Gaussian. Then they are
independent if for all $t_1, t_2 \in T$ with $t_1 \ne t_2$ and
$s_1 \in S_{t_1}$, $s_2 \in S_{t_2}$, $X^{t_1}_{s_1}$ and $X^{t_2}_{s_2}$ are uncorrelated. -/
/-
**ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_strongDual** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：iIndepFun_of_covariance_strongDual [NormedSpace Real E] (hX : IsGaussianPr
ocess (fun (p : (t : T) × S t) ω => X p.1 p.2 ω) P) (mX : forall t s, AEMeasurab
le (X t s) P) (h : forall t₁ t₂, t₁ != t₂ -> forall (s₁ : S t₁) (s₂ : S t₂) (L₁ 
L₂ : StrongDual Real E), cov[L₁ ∘ X t₁ s₁, L₂ ∘ X t₂ s₂; P] = 0) : iIndepFun (fu
n t ω s => X t s ω) P
参数：hX : IsGaussianProcess (fun (p : (t : T) × S t) ω => X p.1 p.2 ω) P；mX : fora
ll t s, AEMeasurable (X t s) P；h : forall t₁ t₂, t₁ != t₂ -> forall (s₁ : S t₁) 
(s₂ : S t₂) (L₁ L₂ : StrongDual Real E), cov[L₁ ∘ X t₁ s₁, L₂ ∘ X t₂ s₂; P] = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.isProbabilityMeasure`：isProbabilityM
easure (hX : IsGaussianProcess X P) : IsProbabilityMeasure P
· 使用定理 `ProbabilityTheory.iIndepFun.iIndepFun_process₀`：∀ {S : Type u_1} {Ω : Ty
pe u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {T : S → Type u_4
}   {𝓧 : (i : S) → T i → Type u_5} […
· 使用定理 `ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_strongDual`：∀ {
Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {ι : Type u
_2} [Finite ι] {E : ι → Type u_3}   [inst : (i : ι) → Nor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw`：∀ {Ω : Type u_1} {E 
: Type u_2} {T : Type u_3} {mΩ : MeasurableSpace Ω} [inst : MeasurableSpace E]  
 [inst_1 : TopologicalSpace E] [inst_2 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousLinearMap.sum_comp_single`：sum_comp_single [Fintype ι] [Decida
bleEq ι] (L : (Π i, φ i) ->L[R] M) (v : Π i, φ i) : ∑ i, L.comp (.single R φ i) 
(v i) = L v
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `ProbabilityTheory.covariance_sum_sum`：covariance_sum_sum [Fintype ι] {ι'
 : Type*} [Fintype ι'] {Y : ι' -> Ω -> Real} (hX : forall i, MemLp (X i) 2 μ) (h
Y : forall i, MemLp (Y i) …
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用引理 `ProbabilityTheory.HasGaussianLaw.memLp_two`：memLp_two [CompleteSpace E] 
[SecondCountableTopology E] (hX : HasGaussianLaw X P) : MemLp X 2 P
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw_eval`：hasGaussianLaw_
eval (hX : IsGaussianProcess X P) (t : T) : HasGaussianLaw (X t) P
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0

--- 原说明 ---
Assume that the processes $((X^t_s)_{s \in S_t})_{t \in T}$ are jointly Gaussian
. Then they are
independent if for all $t_1, t_2 \in T$ with $t_1 \ne t_2$ and
$s_1 \in S_{t_1}$, $s_2 \in S_{t_2}$, $X^{t_1}_{s_1}$ and $X^{t_2}_{s_2}$ are un
correlated.
-/
lemma iIndepFun_of_covariance_strongDual [NormedSpace ℝ E]
    (hX : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (mX : ∀ t s, AEMeasurable (X t s) P)
    (h : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂) (L₁ L₂ : StrongDual ℝ E),
      cov[L₁ ∘ X t₁ s₁, L₂ ∘ X t₂ s₂; P] = 0) :
    iIndepFun (fun t ω s ↦ X t s ω) P := by
  have := hX.isProbabilityMeasure
  classical
  refine iIndepFun.iIndepFun_process₀ mX fun I J ↦
    HasGaussianLaw.iIndepFun_of_covariance_strongDual ?_ fun i j hij L₁ L₂ ↦ ?_
  · let L : (I.sigma (fun i ↦ if hi : i ∈ I then J ⟨i, hi⟩ else ∅) → E) →L[ℝ] (i : I) → J i → E :=
      { toFun x i j := x ⟨⟨i, j⟩, by simp⟩
        map_add' x y := by ext; simp
        map_smul' c x := by ext; simp }
    exact (hX.hasGaussianLaw _).map L
  have h1 : L₁ ∘ (fun ω k ↦ X i k ω) = ∑ k : J i, (L₁ ∘L .single ℝ _ k) ∘ X i k := by
    ext; simp [-ContinuousLinearMap.comp_apply, ← L₁.sum_comp_single]
  have h2 : L₂ ∘ (fun ω k ↦ X j k ω) = ∑ k : J j, (L₂ ∘L .single ℝ _ k) ∘ X j k := by
    ext; simp [-ContinuousLinearMap.comp_apply, ← L₂.sum_comp_single]
  rw [h1, h2, covariance_sum_sum]
  · exact sum_eq_zero fun _ _ ↦ sum_eq_zero fun _ _ ↦ h i j (by simpa) ..
  · exact fun k ↦ ((hX.hasGaussianLaw_eval ⟨i, k⟩).map _).memLp_two
  · exact fun k ↦ ((hX.hasGaussianLaw_eval ⟨j, k⟩).map _).memLp_two

/-- Assume that the processes $((X^t_s)_{s \in S_t})_{t \in T}$ are jointly Gaussian. Then they are
independent if for all $t_1, t_2 \in T$ with $t_1 \ne t_2$ and
$s_1 \in S_{t_1}$, $s_2 \in S_{t_2}$, $X^{t_1}_{s_1}$ and $X^{t_2}_{s_2}$ are uncorrelated. -/
/-
**ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_inner** 是 Mathlib 
中的一个引理，位于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：iIndepFun_of_covariance_inner [InnerProductSpace Real E] (hX : IsGaussianP
rocess (fun (p : (t : T) × S t) ω => X p.1 p.2 ω) P) (mX : forall t s, AEMeasura
ble (X t s) P) (h : forall t₁ t₂, t₁ != t₂ -> forall (s₁ : S t₁) (s₂ : S t₂) (x 
y : E), cov[fun ω => ⟪x, X t₁ s₁ ω⟫, fun ω => ⟪y, X t₂ s₂ ω⟫; P] = 0) : Probabil
ityTheory.iIndepFun (fun t ω s => X t s ω) P
参数：hX : IsGaussianProcess (fun (p : (t : T) × S t) ω => X p.1 p.2 ω) P；mX : fora
ll t s, AEMeasurable (X t s) P；h : forall t₁ t₂, t₁ != t₂ -> forall (s₁ : S t₁) 
(s₂ : S t₂) (x y : E), cov[fun ω => ⟪x, X t₁ s₁ ω⟫, fun ω => ⟪y, X t₂ s₂ ω⟫; P] 
= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_strongDual`：
iIndepFun_of_covariance_strongDual [NormedSpace Real E] (hX : IsGaussianProcess 
(fun (p : (t : T) × S t) ω => X p.1 p.2 ω) P) (mX : forall t…
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
Assume that the processes $((X^t_s)_{s \in S_t})_{t \in T}$ are jointly Gaussian
. Then they are
independent if for all $t_1, t_2 \in T$ with $t_1 \ne t_2$ and
$s_1 \in S_{t_1}$, $s_2 \in S_{t_2}$, $X^{t_1}_{s_1}$ and $X^{t_2}_{s_2}$ are un
correlated.
-/
lemma iIndepFun_of_covariance_inner [InnerProductSpace ℝ E]
    (hX : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (mX : ∀ t s, AEMeasurable (X t s) P)
    (h : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂) (x y : E),
      cov[fun ω ↦ ⟪x, X t₁ s₁ ω⟫, fun ω ↦ ⟪y, X t₂ s₂ ω⟫; P] = 0) :
    ProbabilityTheory.iIndepFun (fun t ω s ↦ X t s ω) P :=
  hX.iIndepFun_of_covariance_strongDual mX fun t₁ t₂ ht s₁ s₂ L₁ L₂ ↦ by
    simpa using! h t₁ t₂ ht s₁ s₂ ((toDual ℝ E).symm L₁) ((toDual ℝ E).symm L₂)

/-- Assume that the processes $((X^t_s)_{s \in S_t})_{t \in T}$ are jointly Gaussian. Then they are
independent if for all $t_1, t_2 \in T$ with $t_1 \ne t_2$ and
$s_1 \in S_{t_1}$, $s_2 \in S_{t_2}$, $X^{t_1}_{s_1}$ and $X^{t_2}_{s_2}$ are uncorrelated. -/
/-
**ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_eq_zero** 是 Mathli
b 中的一个引理，位于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：iIndepFun_of_covariance_eq_zero {X : (t : T) -> (s : S t) -> Ω -> Real} (h
X : IsGaussianProcess (fun (p : (t : T) × S t) ω => X p.1 p.2 ω) P) (mX : forall
 t s, AEMeasurable (X t s) P) (h : forall t₁ t₂, t₁ != t₂ -> forall (s₁ : S t₁) 
(s₂ : S t₂), cov[X t₁ s₁, X t₂ s₂; P] = 0) : ProbabilityTheory.iIndepFun (fun t 
ω s => X t s ω) P
参数：t : T；s : S t；hX : IsGaussianProcess (fun (p : (t : T) × S t) ω => X p.1 p.2 
ω) P；mX : forall t s, AEMeasurable (X t s) P；h : forall t₁ t₂, t₁ != t₂ -> foral
l (s₁ : S t₁) (s₂ : S t₂), cov[X t₁ s₁, X t₂ s₂; P] = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_inner`：iInde
pFun_of_covariance_inner [InnerProductSpace Real E] (hX : IsGaussianProcess (fun
 (p : (t : T) × S t) ω => X p.1 p.2 ω) P) (mX : forall …
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
Assume that the processes $((X^t_s)_{s \in S_t})_{t \in T}$ are jointly Gaussian
. Then they are
independent if for all $t_1, t_2 \in T$ with $t_1 \ne t_2$ and
$s_1 \in S_{t_1}$, $s_2 \in S_{t_2}$, $X^{t_1}_{s_1}$ and $X^{t_2}_{s_2}$ are un
correlated.
-/
lemma iIndepFun_of_covariance_eq_zero {X : (t : T) → (s : S t) → Ω → ℝ}
    (hX : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (mX : ∀ t s, AEMeasurable (X t s) P)
    (h : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂), cov[X t₁ s₁, X t₂ s₂; P] = 0) :
    ProbabilityTheory.iIndepFun (fun t ω s ↦ X t s ω) P :=
  hX.iIndepFun_of_covariance_inner mX fun _ _ h' _ _ _ _ ↦ by
    simp [covariance_mul_const_left, covariance_mul_const_right, h _ _ h']

end iIndepFun

section IndepFun

variable {S : Type*} {X : S → Ω → E} {Y : T → Ω → E}

/-- Two Gaussian processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ that are jointly Gaussian
are independent if for all $s \in S$ and $t \in T$, $X_s$ and $Y_t$ are uncorrelated. -/
/-
**ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_strongDual** 是 Math
lib 中的一个引理，位于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：indepFun_of_covariance_strongDual [NormedSpace Real E] (hXY : IsGaussianPr
ocess (Sum.elim X Y) P) (mX : forall s, AEMeasurable (X s) P) (mY : forall t, AE
Measurable (Y t) P) (h : forall s t (L₁ L₂ : StrongDual Real E), cov[L₁ ∘ X s, L
₂ ∘ Y t; P] = 0) : IndepFun (fun ω s => X s ω) (fun ω t => Y t ω) P
参数：hXY : IsGaussianProcess (Sum.elim X Y) P；mX : forall s, AEMeasurable (X s) P；
mY : forall t, AEMeasurable (Y t) P；h : forall s t (L₁ L₂ : StrongDual Real E), 
cov[L₁ ∘ X s, L₂ ∘ Y t; P] = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.isProbabilityMeasure`：isProbabilityM
easure (hX : IsGaussianProcess X P) : IsProbabilityMeasure P
· 使用定理 `ProbabilityTheory.IndepFun.process_indepFun_process₀`：∀ {S : Type u_1} {
Ω : Type u_3} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {T : Type u
_4} {𝓧 : S → Type u_5}   {𝓨 : T → Type u_6…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_strongDual`：∀ {Ω
 : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {E : Type u_
2} {F : Type u_3}   [inst : NormedAddCommGroup E] [inst_…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.inl_mem_disjSum`：inl_mem_disjSum : inl a in s.disjSum t ↔ a in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finset.inr_mem_disjSum`：inr_mem_disjSum : inr b in s.disjSum t ↔ b in t
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `ProbabilityTheory.IsGaussianProcess.hasGaussianLaw`：∀ {Ω : Type u_1} {E 
: Type u_2} {T : Type u_3} {mΩ : MeasurableSpace Ω} [inst : MeasurableSpace E]  
 [inst_1 : TopologicalSpace E] [inst_2 :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousLinearMap.sum_comp_single`：sum_comp_single [Fintype ι] [Decida
bleEq ι] (L : (Π i, φ i) ->L[R] M) (v : Π i, φ i) : ∑ i, L.comp (.single R φ i) 
(v i) = L v
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `ProbabilityTheory.covariance_sum_sum`：covariance_sum_sum [Fintype ι] {ι'
 : Type*} [Fintype ι'] {Y : ι' -> Ω -> Real} (hX : forall i, MemLp (X i) 2 μ) (h
Y : forall i, MemLp (Y i) …
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Two Gaussian processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ that are jointly 
Gaussian
are independent if for all $s \in S$ and $t \in T$, $X_s$ and $Y_t$ are uncorrel
ated.
-/
lemma indepFun_of_covariance_strongDual [NormedSpace ℝ E]
    (hXY : IsGaussianProcess (Sum.elim X Y) P)
    (mX : ∀ s, AEMeasurable (X s) P) (mY : ∀ t, AEMeasurable (Y t) P)
    (h : ∀ s t (L₁ L₂ : StrongDual ℝ E), cov[L₁ ∘ X s, L₂ ∘ Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P := by
  have := hXY.isProbabilityMeasure
  refine IndepFun.process_indepFun_process₀ mX mY fun I J ↦
    HasGaussianLaw.indepFun_of_covariance_strongDual ?_ fun L₁ L₂ ↦ ?_
  · let L : (I.disjSum J → E) →L[ℝ] (I → E) × (J → E) :=
      { toFun x := (fun s ↦ x ⟨Sum.inl s, inl_mem_disjSum.2 s.2⟩,
          fun t ↦ x ⟨Sum.inr t, inr_mem_disjSum.2 t.2⟩)
        map_add' x y := by ext <;> simp
        map_smul' c x := by ext <;> simp }
    exact (hXY.hasGaussianLaw _).map L
  classical
  have h1 : L₁ ∘ (fun ω i ↦ X i ω) = ∑ i : I, (L₁ ∘L .single ℝ _ i) ∘ X i := by
    ext; simp [-ContinuousLinearMap.comp_apply, ← L₁.sum_comp_single]
  have h2 : L₂ ∘ (fun ω j ↦ Y j ω) = ∑ j : J, (L₂ ∘L .single ℝ _ j) ∘ Y j := by
    ext; simp [-ContinuousLinearMap.comp_apply, ← L₂.sum_comp_single]
  rw [h1, h2, covariance_sum_sum]
  · exact sum_eq_zero fun i _ ↦ sum_eq_zero fun j _ ↦ h ..
  · exact fun s ↦ ((hXY.hasGaussianLaw_eval (.inl s)).map _).memLp_two
  · exact fun t ↦ ((hXY.hasGaussianLaw_eval (.inr t)).map _).memLp_two

/-- Two Gaussian processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ that are jointly Gaussian
are independent if for all $s \in S$ and $t \in T$, $X_s$ and $Y_t$ are uncorrelated. -/
/-
**ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_inner** 是 Mathlib 中
的一个引理，位于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：indepFun_of_covariance_inner [InnerProductSpace Real E] (hXY : IsGaussianP
rocess (Sum.elim X Y) P) (mX : forall s, AEMeasurable (X s) P) (mY : forall t, A
EMeasurable (Y t) P) (h : forall s t x y, cov[fun ω => ⟪x, X s ω⟫, fun ω => ⟪y, 
Y t ω⟫; P] = 0) : IndepFun (fun ω s => X s ω) (fun ω t => Y t ω) P
参数：hXY : IsGaussianProcess (Sum.elim X Y) P；mX : forall s, AEMeasurable (X s) P；
mY : forall t, AEMeasurable (Y t) P；h : forall s t x y, cov[fun ω => ⟪x, X s ω⟫,
 fun ω => ⟪y, Y t ω⟫; P] = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_strongDual`：i
ndepFun_of_covariance_strongDual [NormedSpace Real E] (hXY : IsGaussianProcess (
Sum.elim X Y) P) (mX : forall s, AEMeasurable (X s) P) (mY …
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
Two Gaussian processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ that are jointly 
Gaussian
are independent if for all $s \in S$ and $t \in T$, $X_s$ and $Y_t$ are uncorrel
ated.
-/
lemma indepFun_of_covariance_inner [InnerProductSpace ℝ E]
    (hXY : IsGaussianProcess (Sum.elim X Y) P)
    (mX : ∀ s, AEMeasurable (X s) P) (mY : ∀ t, AEMeasurable (Y t) P)
    (h : ∀ s t x y, cov[fun ω ↦ ⟪x, X s ω⟫, fun ω ↦ ⟪y, Y t ω⟫; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  hXY.indepFun_of_covariance_strongDual mX mY fun s t L₁ L₂ ↦ by
    simpa using! h s t ((toDual ℝ E).symm L₁) ((toDual ℝ E).symm L₂)

/-- Two Gaussian processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ that are jointly Gaussian
are independent if for all $s \in S$ and $t \in T$, $X_s$ and $Y_t$ are uncorrelated. -/
/-
**ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero** 是 Mathlib
 中的一个引理，位于命名空间 `ProbabilityTheory.IsGaussianProcess`。
形式化陈述：indepFun_of_covariance_eq_zero {X : S -> Ω -> Real} {Y : T -> Ω -> Real} (
hXY : IsGaussianProcess (Sum.elim X Y) P) (mX : forall s, AEMeasurable (X s) P) 
(mY : forall t, AEMeasurable (Y t) P) (h : forall s t, cov[X s, Y t; P] = 0) : I
ndepFun (fun ω s => X s ω) (fun ω t => Y t ω) P
参数：hXY : IsGaussianProcess (Sum.elim X Y) P；mX : forall s, AEMeasurable (X s) P；
mY : forall t, AEMeasurable (Y t) P；h : forall s t, cov[X s, Y t; P] = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_inner`：indepF
un_of_covariance_inner [InnerProductSpace Real E] (hXY : IsGaussianProcess (Sum.
elim X Y) P) (mX : forall s, AEMeasurable (X s) P) (mY…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
Two Gaussian processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ that are jointly 
Gaussian
are independent if for all $s \in S$ and $t \in T$, $X_s$ and $Y_t$ are uncorrel
ated.
-/
lemma indepFun_of_covariance_eq_zero {X : S → Ω → ℝ} {Y : T → Ω → ℝ}
    (hXY : IsGaussianProcess (Sum.elim X Y) P) (mX : ∀ s, AEMeasurable (X s) P)
    (mY : ∀ t, AEMeasurable (Y t) P) (h : ∀ s t, cov[X s, Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  hXY.indepFun_of_covariance_inner mX mY fun _ _ _ _ ↦ by
    simp [covariance_mul_const_left, covariance_mul_const_right, h]

end IndepFun

end ProbabilityTheory.IsGaussianProcess

