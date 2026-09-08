/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Moments.CovarianceBilin

import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Facts about Gaussian characteristic function

In this file we prove that Gaussian measures over a Banach space `E` are exactly those measures
`μ` such that there exist `m : E` and `f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ`
positive semidefinite (satisfying `f.toBilinForm.IsPosSemidef`) such that
`charFunDual μ L = exp (L m * I - f L L / 2)`.
We also prove that such `m` and `f` are unique and equal to `∫ x, x ∂μ` and `covarianceBilinDual μ`.

We also specialize these statements in the case of Hilbert spaces, with
`f : E →L[ℝ] E →L[ℝ] ℝ`, `charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)` and
`f = covarianceBilin μ`.

## Main statements

* `isGaussian_iff_gaussian_charFunDual μ`: the measure `μ` is Gaussian if and only if there
  exist `m : E` and `f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ`
  satisfying `f.toBilinForm.IsPosSemidef` and `charFunDual μ L = exp (L m * I - f L L / 2)`.
* `isGaussian_iff_gaussian_charFun μ`: the measure `μ` is Gaussian if and only if there
  exist `m : E` and `f : E →L[ℝ]  E →L[ℝ] ℝ`
  satisfying `f.toBilinForm.IsPosSemidef` and `charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)`.

## Tags

Gaussian measure, characteristic function
-/

public section


open Complex MeasureTheory WithLp ContinuousLinearMap

open scoped Matrix NNReal Real RealInnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E}

section NormedSpace

variable [NormedSpace ℝ E]

/-
**ProbabilityTheory.IsGaussian.charFunDual_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory.IsGaussian`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [SecondCountableTopology E]
 [CompleteSpace E]   [inst_3 : MeasurableSpace E] [inst_4 : BorelSpace E] {μ : M
easureTheory.Measure E} [inst_5 : NormedSpace ℝ E]   [ProbabilityTheory.IsGaussi
an μ] (L : StrongDual ℝ E),   MeasureTheory.charFunDual μ L =     Complex.exp (↑
(L (∫ (x : E), id x ∂μ)) * Complex.I - ↑(((ProbabilityTheory.covarianceBilinDual
 μ) L) L) / 2)
参数：L : StrongDual ℝ E；↑(L (∫ (x : E), id x ∂μ)) * Complex.I - ↑(((ProbabilityThe
ory.covarianceBilinDual μ) L) L) / 2。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsGaussian.charFunDual_eq`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E] [Bor
elSpace E]   {μ : MeasureTheory.M…
· 使用引理 `ProbabilityTheory.covarianceBilinDual_self_eq_variance`：covarianceBilinD
ual_self_eq_variance (h : MemLp id 2 μ) (L : StrongDual Real E) : covarianceBili
nDual μ L L = Var[L; μ]
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用引理 `ProbabilityTheory.IsGaussian.memLp_two_id`：memLp_two_id : MemLp id 2 μ
· 使用定理 `integral_complex_ofReal`：integral_complex_ofReal {f : X -> Real} : ∫ x, 
(f x : Complex) ∂μ = ∫ x, f x ∂μ
· 使用引理 `ContinuousLinearMap.integral_comp_id_comm'`：integral_comp_id_comm' (h : 
Integrable id μ) (L : E ->L[𝕜] F) : μ[L] = L μ[id]
· 使用引理 `ProbabilityTheory.IsGaussian.integrable_id`：integrable_id : Integrable i
d μ
-/
lemma IsGaussian.charFunDual_eq' [IsGaussian μ] (L : StrongDual ℝ E) :
    charFunDual μ L = exp ((L μ[id]) * I - covarianceBilinDual μ L L / 2) := by
  rw [IsGaussian.charFunDual_eq, covarianceBilinDual_self_eq_variance, integral_complex_ofReal,
    L.integral_comp_id_comm']
  · exact IsGaussian.integrable_id
  · exact IsGaussian.memLp_two_id

/-- The measure `μ` is Gaussian if and only if there
exist `m : E` and `f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ`
satisfying `f.toBilinForm.IsPosSemidef` and `charFunDual μ L = exp (L m * I - f L L / 2)`. -/
/-
**ProbabilityTheory.isGaussian_iff_gaussian_charFunDual** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：isGaussian_iff_gaussian_charFunDual [IsFiniteMeasure μ] : IsGaussian μ ↔ e
xists (m : E) (f : StrongDual Real E ->L[Real] StrongDual Real E ->L[Real] Real)
, f.toBilinForm.IsPosSemidef ∧ forall L, charFunDual μ L = exp (L m * I - f L L 
/ 2)
该定理/引理刻画了左右两侧的等价关系。
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
· 使用引理 `ProbabilityTheory.isPosSemidef_covarianceBilinDual`：isPosSemidef_covaria
nceBilinDual : (covarianceBilinDual μ).toBilinForm.IsPosSemidef where eq
· 使用定理 `ProbabilityTheory.IsGaussian.charFunDual_eq'`：∀ {E : Type u_1} [inst : N
ormedAddCommGroup E] [SecondCountableTopology E] [CompleteSpace E]   [inst_3 : M
easurableSpace E] [inst_4 : BorelS…
· 使用引理 `ProbabilityTheory.isGaussian_of_map_eq_gaussianReal`：isGaussian_of_map_e
q_gaussianReal {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module Real E
] {mE : MeasurableSpace E} [OpensMeasurab…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.ext_of_charFun`：∀ {E : Type u_3} [inst : Measurabl
eSpace E] {μ ν : MeasureTheory.Measure E} [inst_1 : NormedAddCommGroup E]   [ins
t_2 : InnerProductSpace ℝ …
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.charFun_map_eq_charFunDual_smul`：charFun_map_eq_charFunDua
l_smul [OpensMeasurableSpace E] (L : StrongDual Real E) (u : Real) : charFun (μ.
map L) u = charFunDual μ (u • L)
· 使用定理 `ProbabilityTheory.charFun_gaussianReal`：charFun_gaussianReal (t : Real) 
: charFun (gaussianReal μ v) t = cexp (t * μ * I - v * t ^ 2 / 2)
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 68 条，此处仅展示前 30 条）

--- 原说明 ---
The measure `μ` is Gaussian if and only if there
exist `m : E` and `f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ`
satisfying `f.toBilinForm.IsPosSemidef` and `charFunDual μ L = exp (L m * I - f 
L L / 2)`.
-/
lemma isGaussian_iff_gaussian_charFunDual [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∃ (m : E) (f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ),
      f.toBilinForm.IsPosSemidef ∧ ∀ L, charFunDual μ L = exp (L m * I - f L L / 2) := by
  refine ⟨fun h ↦ ⟨μ[id], covarianceBilinDual μ, isPosSemidef_covarianceBilinDual,
    h.charFunDual_eq'⟩,
    fun ⟨m, f, hf, h⟩ ↦ isGaussian_of_map_eq_gaussianReal fun L ↦ ⟨L m, (f L L).toNNReal, ?_⟩⟩
  apply Measure.ext_of_charFun
  ext t
  simp_rw [charFun_map_eq_charFunDual_smul, h, charFun_gaussianReal,
    smul_apply, map_smul, smul_apply, smul_eq_mul]
  norm_cast
  congrm exp (_ - ofReal ?_)
  rw [Real.coe_toNNReal]
  · ring
  exact hf.nonneg L
/-
**ProbabilityTheory.gaussian_charFunDual_congr** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：gaussian_charFunDual_congr [IsFiniteMeasure μ] {m : E} {f : StrongDual Rea
l E ->L[Real] StrongDual Real E ->L[Real] Real} (hf : f.toBilinForm.IsPosSemidef
) (h : forall L, charFunDual μ L = exp (L m * I - f L L / 2)) : m = ∫ x, x ∂μ ∧ 
f = covarianceBilinDual μ
参数：hf : f.toBilinForm.IsPosSemidef；h : forall L, charFunDual μ L = exp (L m * I 
- f L L / 2)。
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ProbabilityTheory.isGaussian_iff_gaussian_charFunDual`：isGaussian_iff_ga
ussian_charFunDual [IsFiniteMeasure μ] : IsGaussian μ ↔ exists (m : E) (f : Stro
ngDual Real E ->L[Real] StrongDual Real E -…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
（共 159 条，此处仅展示前 30 条）
-/
lemma gaussian_charFunDual_congr [IsFiniteMeasure μ] {m : E}
    {f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ}
    (hf : f.toBilinForm.IsPosSemidef) (h : ∀ L, charFunDual μ L = exp (L m * I - f L L / 2)) :
    m = ∫ x, x ∂μ ∧ f = covarianceBilinDual μ := by
  have h' := isGaussian_iff_gaussian_charFunDual.2 ⟨m, f, hf, h⟩
  simp_rw [h'.charFunDual_eq', Complex.exp_eq_exp_iff_exists_int] at h
  choose n hn using h
  have h L : (n L : ℂ) = (L (∫ x, id x ∂μ) * I - covarianceBilinDual μ L L / 2 -
      L m * I + f L L / 2) / (2 * π * I) := by
    rw [hn L]
    field_simp
    ring
  have : Continuous n := by
    rw [← Complex.isometry_intCast.comp_continuous_iff]
    change Continuous (fun L ↦ (n L : ℂ))
    simp_rw [h]
    fun_prop
  have := (IsLocallyConstant.iff_continuous n).2 this |>.eq_const
  have this L : n L = 0 := by
    rw [this 0, ← Int.cast_inj (α := ℂ)]
    simp [h]
  simp only [id_eq, this, Int.cast_zero, zero_mul, add_zero, Complex.ext_iff, sub_re, mul_re,
    ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, div_ofNat_re, zero_sub, neg_inj,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj', sub_im, mul_im, div_ofNat_im,
    zero_div, sub_zero] at hn
  constructor
  · rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
    simp [hn]
  · rw [← toBilinForm_inj]
    apply LinearMap.BilinForm.ext_of_isSymm hf.isSymm isPosSemidef_covarianceBilinDual.isSymm
    intro x
    simp [covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id, (hn x).1.symm]

/-- Two Gaussian measures are equal if they have same mean and same covariance. -/
/-
**ProbabilityTheory.IsGaussian.ext_covarianceBilinDual** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.IsGaussian`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [SecondCountableTopology E]
 [CompleteSpace E]   [inst_3 : MeasurableSpace E] [inst_4 : BorelSpace E] {μ : M
easureTheory.Measure E} [inst_5 : NormedSpace ℝ E]   {ν : MeasureTheory.Measure 
E} [ProbabilityTheory.IsGaussian μ] [ProbabilityTheory.IsGaussian ν],   ∫ (x : E
), id x ∂μ = ∫ (x : E), id x ∂ν →     ProbabilityTheory.covarianceBilinDual μ = 
ProbabilityTheory.covarianceBilinDual ν → μ = ν
参数：x : E；x : E。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsGaussian.charFunDual_eq'`：∀ {E : Type u_1} [inst : N
ormedAddCommGroup E] [SecondCountableTopology E] [CompleteSpace E]   [inst_3 : M
easurableSpace E] [inst_4 : BorelS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two Gaussian measures are equal if they have same mean and same covariance.
-/
protected lemma IsGaussian.ext_covarianceBilinDual {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilinDual μ = covarianceBilinDual ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq', hm, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. -/
/-
**ProbabilityTheory.IsGaussian.ext_iff_covarianceBilinDual** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory.IsGaussian`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [SecondCountableTopology E]
 [CompleteSpace E]   [inst_3 : MeasurableSpace E] [inst_4 : BorelSpace E] {μ : M
easureTheory.Measure E} [inst_5 : NormedSpace ℝ E]   {ν : MeasureTheory.Measure 
E} [ProbabilityTheory.IsGaussian μ] [ProbabilityTheory.IsGaussian ν],   μ = ν ↔ 
    ∫ (x : E), id x ∂μ = ∫ (x : E), id x ∂ν ∧       ProbabilityTheory.covariance
BilinDual μ = ProbabilityTheory.covarianceBilinDual ν
参数：x : E；x : E。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.covarianceBilinDual.congr_simp`：∀ {E : Type u_1} [inst
 : NormedAddCommGroup E] {mE : MeasurableSpace E} [inst_1 : NormedSpace ℝ E]   [
inst_2 : BorelSpace E] (μ μ_1 : Measur…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ProbabilityTheory.IsGaussian.ext_covarianceBilinDual`：∀ {E : Type u_1} [
inst : NormedAddCommGroup E] [SecondCountableTopology E] [CompleteSpace E]   [in
st_3 : MeasurableSpace E] [inst_4 : BorelS…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Two Gaussian measures are equal if and only if they have same mean and same cova
riance.
-/
protected lemma IsGaussian.ext_iff_covarianceBilinDual {ν : Measure E} [IsGaussian μ]
    [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilinDual μ = covarianceBilinDual ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext_covarianceBilinDual h.1 h.2

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E]

/-
**ProbabilityTheory.IsGaussian.charFun_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IsGaussian`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [SecondCountableTopology E]
 [CompleteSpace E]   [inst_3 : MeasurableSpace E] [inst_4 : BorelSpace E] {μ : M
easureTheory.Measure E} [inst_5 : InnerProductSpace ℝ E]   [ProbabilityTheory.Is
Gaussian μ] (t : E),   MeasureTheory.charFun μ t =     Complex.exp (↑(inner ℝ t 
(∫ (x : E), id x ∂μ)) * Complex.I - ↑(((ProbabilityTheory.covarianceBilin μ) t) 
t) / 2)
参数：t : E；↑(inner ℝ t (∫ (x : E), id x ∂μ)) * Complex.I - ↑(((ProbabilityTheory.c
ovarianceBilin μ) t) t) / 2。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsGaussian.charFun_eq`：∀ {E : Type u_3} [inst : Normed
AddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : MeasurableSpace E]   
[BorelSpace E] {μ : MeasureTh…
· 使用引理 `ProbabilityTheory.covarianceBilin_self`：covarianceBilin_self [CompleteSp
ace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x : E) : covarianceBilin μ x x = 
Var[fun u => ⟪x, u⟫; μ]
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用引理 `ProbabilityTheory.IsGaussian.memLp_two_id`：memLp_two_id : MemLp id 2 μ
· 使用定理 `integral_complex_ofReal`：integral_complex_ofReal {f : X -> Real} : ∫ x, 
(f x : Complex) ∂μ = ∫ x, f x ∂μ
· 使用定理 `integral_inner`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureThe
ory.Measure α} {E : Type u_2} {𝕜 : Type u_3} [inst : RCLike 𝕜]   [inst_1 : Norme
dAdd…
· 使用引理 `ProbabilityTheory.IsGaussian.integrable_id`：integrable_id : Integrable i
d μ
-/
lemma IsGaussian.charFun_eq' [IsGaussian μ] (t : E) :
    charFun μ t = exp (⟪t, μ[id]⟫ * I - covarianceBilin μ t t / 2) := by
  rw [IsGaussian.charFun_eq, covarianceBilin_self, integral_complex_ofReal,
    integral_inner]
  · rfl
  · exact IsGaussian.integrable_id
  · exact IsGaussian.memLp_two_id

set_option backward.isDefEq.respectTransparency.types false in
/-- The measure `μ` is Gaussian if and only if there
exist `m : E` and `f : E →L[ℝ]  E →L[ℝ] ℝ`
satisfying `f.toBilinForm.IsPosSemidef` and `charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)`. -/
/-
**ProbabilityTheory.isGaussian_iff_gaussian_charFun** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：isGaussian_iff_gaussian_charFun [IsFiniteMeasure μ] : IsGaussian μ ↔ exist
s (m : E) (f : E ->L[Real] E ->L[Real] Real), f.toBilinForm.IsPosSemidef ∧ foral
l t, charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.isGaussian_iff_gaussian_charFunDual`：isGaussian_iff_ga
ussian_charFunDual [IsFiniteMeasure μ] : IsGaussian μ ↔ exists (m : E) (f : Stro
ngDual Real E ->L[Real] StrongDual Real E -…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LinearMap.BilinForm.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B : Li
nearMap.BilinForm R…
· 使用定理 `LinearMap.BilinForm.IsPosSemidef.isSymm`：∀ {R : Type u_1} {M : Type u_2}
 [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]
   [inst_3 : LE R] {B : Linea…
· 使用定理 `LinearMap.BilinForm.IsNonneg.nonneg`：∀ {R : Type u_1} {M : Type u_2} [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
inst_3 : LE R] {B : Linea…
· 使用定理 `LinearMap.BilinForm.IsPosSemidef.isNonneg`：∀ {R : Type u_1} {M : Type u_
2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R 
M]   [inst_3 : LE R] {B : Linea…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.charFun_eq_charFunDual_toDualMap`：charFun_eq_charFunDual_t
oDualMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] {mE : Mea
surableSpace E} {μ : Measure E} (t :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `InnerProductSpace.toDual_symm_apply`：toDual_symm_apply {x : E} {y : Stro
ngDual 𝕜 E} : ⟪(toDual 𝕜 E).symm y, x⟫ = y x

--- 原说明 ---
The measure `μ` is Gaussian if and only if there
exist `m : E` and `f : E →L[ℝ]  E →L[ℝ] ℝ`
satisfying `f.toBilinForm.IsPosSemidef` and `charFun μ t = exp (⟪t, m⟫ * I - f t
 t / 2)`.
-/
lemma isGaussian_iff_gaussian_charFun [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∃ (m : E) (f : E →L[ℝ] E →L[ℝ] ℝ),
      f.toBilinForm.IsPosSemidef ∧ ∀ t, charFun μ t = exp (⟪t, m⟫ * I - f t t / 2) := by
  rw [isGaussian_iff_gaussian_charFunDual]
  refine ⟨fun ⟨m, f, hf, h⟩ ↦ ⟨m,
    f.bilinearComp (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap
      (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap,
    ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩,
    fun ⟨m, f, hf, h⟩ ↦ ⟨m,
      f.bilinearComp (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
        (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap,
    ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩⟩
  any_goals simpa using hf.eq ..
  any_goals simpa using hf.nonneg _
  · simp [charFun_eq_charFunDual_toDualMap, h, -InnerProductSpace.toContinuousLinearMap_toDualMap]
  · simp [← charFun_toDual_symm_eq_charFunDual, h]

set_option backward.isDefEq.respectTransparency.types false in
/-- If the characteristic function of `μ` takes the form of a gaussian characteristic function,
then the parameters have to be the expectation and the covariance bilinear form. -/
/-
**ProbabilityTheory.gaussian_charFun_congr** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：gaussian_charFun_congr [IsFiniteMeasure μ] (m : E) (f : E ->L[Real] E ->L[
Real] Real) (hf : f.toBilinForm.IsPosSemidef) (h : forall t, charFun μ t = exp (
⟪t, m⟫ * I - f t t / 2)) : m = ∫ x, x ∂μ ∧ f = covarianceBilin μ
参数：m : E；f : E ->L[Real] E ->L[Real] Real；hf : f.toBilinForm.IsPosSemidef；h : fo
rall t, charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)。
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.toDual_symm_apply`：toDual_symm_apply {x : E} {y : Stro
ngDual 𝕜 E} : ⟪(toDual 𝕜 E).symm y, x⟫ = y x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearMap.BilinForm.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B : Li
nearMap.BilinForm R…
· 使用定理 `LinearMap.BilinForm.IsPosSemidef.isSymm`：∀ {R : Type u_1} {M : Type u_2}
 [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]
   [inst_3 : LE R] {B : Linea…
· 使用定理 `LinearMap.BilinForm.IsNonneg.nonneg`：∀ {R : Type u_1} {M : Type u_2} [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
inst_3 : LE R] {B : Linea…
· 使用定理 `LinearMap.BilinForm.IsPosSemidef.isNonneg`：∀ {R : Type u_1} {M : Type u_
2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R 
M]   [inst_3 : LE R] {B : Linea…
· 使用引理 `ProbabilityTheory.gaussian_charFunDual_congr`：gaussian_charFunDual_congr
 [IsFiniteMeasure μ] {m : E} {f : StrongDual Real E ->L[Real] StrongDual Real E 
->L[Real] Real} (hf : f.toBilinFor…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If the characteristic function of `μ` takes the form of a gaussian characteristi
c function,
then the parameters have to be the expectation and the covariance bilinear form.
-/
lemma gaussian_charFun_congr [IsFiniteMeasure μ] (m : E) (f : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : f.toBilinForm.IsPosSemidef) (h : ∀ t, charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)) :
    m = ∫ x, x ∂μ ∧ f = covarianceBilin μ := by
  let g : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ :=
    f.bilinearComp (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
      (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
  have : ∀ L : StrongDual ℝ E, charFunDual μ L = exp (L m * I - g L L / 2) := by
    simp [← charFun_toDual_symm_eq_charFunDual, h, g]
  have hg : g.toBilinForm.IsPosSemidef :=
    ⟨⟨fun x y ↦ by simpa [g] using hf.eq ..⟩, ⟨fun x ↦ by simpa [g] using hf.nonneg _⟩⟩
  have := gaussian_charFunDual_congr hg this
  refine ⟨this.1, ?_⟩
  ext
  simp [covarianceBilin, ← this.2, g, ← InnerProductSpace.toDual_apply_eq_toDualMap_apply,
    -InnerProductSpace.toContinuousLinearMap_toDualMap]

/-- Two Gaussian measures are equal if they have same mean and same covariance. This is
`IsGaussian.ext_covarianceBilinDual` specialized to Hilbert spaces. -/
/-
**ProbabilityTheory.IsGaussian.ext** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.
IsGaussian`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [SecondCountableTopology E]
 [CompleteSpace E]   [inst_3 : MeasurableSpace E] [inst_4 : BorelSpace E] {μ : M
easureTheory.Measure E} [inst_5 : InnerProductSpace ℝ E]   {ν : MeasureTheory.Me
asure E} [ProbabilityTheory.IsGaussian μ] [ProbabilityTheory.IsGaussian ν],   ∫ 
(x : E), id x ∂μ = ∫ (x : E), id x ∂ν →     ProbabilityTheory.covarianceBilin μ 
= ProbabilityTheory.covarianceBilin ν → μ = ν
参数：x : E；x : E。
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
· 使用定理 `MeasureTheory.Measure.ext_of_charFun`：∀ {E : Type u_3} [inst : Measurabl
eSpace E] {μ ν : MeasureTheory.Measure E} [inst_1 : NormedAddCommGroup E]   [ins
t_2 : InnerProductSpace ℝ …
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
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsGaussian.charFun_eq'`：∀ {E : Type u_1} [inst : Norme
dAddCommGroup E] [SecondCountableTopology E] [CompleteSpace E]   [inst_3 : Measu
rableSpace E] [inst_4 : BorelS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two Gaussian measures are equal if they have same mean and same covariance. This
 is
`IsGaussian.ext_covarianceBilinDual` specialized to Hilbert spaces.
-/
protected lemma IsGaussian.ext {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilin μ = covarianceBilin ν) : μ = ν := by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [IsGaussian.charFun_eq', hm, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. This is
`IsGaussian.ext_iff_covarianceBilinDual` specialized to Hilbert spaces. -/
/-
**ProbabilityTheory.IsGaussian.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory.IsGaussian`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [SecondCountableTopology E]
 [CompleteSpace E]   [inst_3 : MeasurableSpace E] [inst_4 : BorelSpace E] {μ : M
easureTheory.Measure E} [inst_5 : InnerProductSpace ℝ E]   {ν : MeasureTheory.Me
asure E} [ProbabilityTheory.IsGaussian μ] [ProbabilityTheory.IsGaussian ν],   μ 
= ν ↔     ∫ (x : E), id x ∂μ = ∫ (x : E), id x ∂ν ∧ ProbabilityTheory.covariance
Bilin μ = ProbabilityTheory.covarianceBilin ν
参数：x : E；x : E。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.covarianceBilin.congr_simp`：∀ {E : Type u_1} [inst : N
ormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : MeasurableSpace 
E]   [inst_3 : BorelSpace E] (μ μ_…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ProbabilityTheory.IsGaussian.ext`：∀ {E : Type u_1} [inst : NormedAddComm
Group E] [SecondCountableTopology E] [CompleteSpace E]   [inst_3 : MeasurableSpa
ce E] [inst_4 : BorelS…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Two Gaussian measures are equal if and only if they have same mean and same cova
riance. This is
`IsGaussian.ext_iff_covarianceBilinDual` specialized to Hilbert spaces.
-/
protected lemma IsGaussian.ext_iff {ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilin μ = covarianceBilin ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext h.1 h.2

end InnerProductSpace

end ProbabilityTheory

