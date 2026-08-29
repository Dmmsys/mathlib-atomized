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
  {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace Real (E i)]
  {L : (i : ι) -> StrongDual Real (E i) ->L[Real] StrongDual Real (E i) ->L[Real] Real}

/-- Given `L i : (E i)' × (E i)' → ℝ` a family of continuous bilinear forms,
`diagonalStrongDualPi L` is the continuous bilinear form over `(Π i, E i)'`
which maps `(x, y) : (Π i, E i)' × (Π i, E i)'` to
`∑ i, L i (fun a ↦ x aᵢ) (fun a ↦ y aᵢ)`.

This is an implementation detail used in `iIndepFun.hasGaussianLaw`. -/
noncomputable
/--
Definition of `diagonalStrongDualPi` / `diagonalStrongDualPi` 的定义

English:
definition diagonalStrongDualPi
  signature: (L : (i : ι) -> StrongDual Real (E i) ->L[Real] StrongDual Real (E i) ->L[Real] Real)
  body: letI g : LinearMap.BilinForm Real (StrongDual Real (Π i, E i)) := LinearMap.mk₂ Real
    (fun x y => ∑ i, L i (x ∘L (single Real E i)) (y ∘L (single Real E i)))
    (fun x y z => by simp [sum_add_distrib])
    (fun c m n => by simp [mul_sum])
    (fun x y z => by simp [sum_add_distrib])
    (fun c m n => by simp [mul_sum])
LinearMap.mkContinuous₂ g (∑ i, ‖L i‖) by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_sum_le, sum_mul, sum_mul]
    gcongr with i _
    grw [le_opNorm₂]
    gcongr <;> grw [opNorm_comp_le, norm_single_le_one, mul_one]

中文:
定义 diagonalStrongDualPi
  签名: (L : (i : ι) -> StrongDual 实数 (E i) ->L[实数] StrongDual 实数 (E i) ->L[实数] 实数)
  定义体: letI g : LinearMap.BilinForm Real (StrongDual Real (Π i, E i)) := LinearMap.mk₂ Real
    (fun x y => ∑ i, L i (x ∘L (single Real E i)) (y ∘L (single Real E i)))
    (fun x y z => by simp [sum_add_distrib])
    (fun c m n => by simp [mul_sum])
    (fun x y z => by simp [sum_add_distrib])
    (fun c m n => by simp [mul_sum])
LinearMap.mkContinuous₂ g (∑ i, ‖L i‖) by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_sum_le, sum_mul, sum_mul]
    gcongr with i _
    grw [le_opNorm₂]
    gcongr <;> grw [opNorm_comp_le, norm_single_le_one, mul_one]

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm, LinearMap.mk, LinearMap.mkContinuous, StrongDual, mul_sum, norm_si, norm_sum_le, opNorm_comp_le, single, sum_add_distrib, sum_mul
-/
def diagonalStrongDualPi (L : (i : ι) -> StrongDual Real (E i) ->L[Real] StrongDual Real (E i) ->L[Real] Real) :
    StrongDual Real (Π i, E i) ->L[Real] StrongDual Real (Π i, E i) ->L[Real] Real :=
  letI g : LinearMap.BilinForm Real (StrongDual Real (Π i, E i)) := LinearMap.mk₂ Real
    (fun x y => ∑ i, L i (x ∘L (single Real E i)) (y ∘L (single Real E i)))
    (fun x y z => by simp [sum_add_distrib])
    (fun c m n => by simp [mul_sum])
    (fun x y z => by simp [sum_add_distrib])
    (fun c m n => by simp [mul_sum])
LinearMap.mkContinuous₂ g (∑ i, ‖L i‖) by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_sum_le, sum_mul, sum_mul]
    gcongr with i _
    grw [le_opNorm₂]
    gcongr <;> grw [opNorm_comp_le, norm_single_le_one, mul_one]

/--
lemma `diagonalStrongDualPi_apply` / 引理 `diagonalStrongDualPi_apply`

English:
lemma diagonalStrongDualPi_apply
  given: (x y : StrongDual Real (Π i, E i))
  proof: rfl

中文:
引理 diagonalStrongDualPi_apply
  条件: (x y : StrongDual 实数 (Π i, E i))
  证明: rfl
-/
lemma diagonalStrongDualPi_apply (x y : StrongDual Real (Π i, E i)) :
    diagonalStrongDualPi L x y = ∑ i, L i (x ∘L (.single Real E i)) (y ∘L (.single Real E i)) := rfl

/--
lemma `toBilinForm_diagonalStrongDualPi_apply` / 引理 `toBilinForm_diagonalStrongDualPi_apply`

English:
lemma toBilinForm_diagonalStrongDualPi_apply
  given: (x y : StrongDual Real (Π i, E i))
  proof: rfl

中文:
引理 toBilinForm_diagonalStrongDualPi_apply
  条件: (x y : StrongDual 实数 (Π i, E i))
  证明: rfl
-/
lemma toBilinForm_diagonalStrongDualPi_apply (x y : StrongDual Real (Π i, E i)) :
    (diagonalStrongDualPi L).toBilinForm x y =
    ∑ i, (L i).toBilinForm (x ∘L (.single Real E i)) (y ∘L (.single Real E i)) := rfl

/--
lemma `isPosSemidef_diagonalStrongDualPi` / 引理 `isPosSemidef_diagonalStrongDualPi`

English:
lemma isPosSemidef_diagonalStrongDualPi
  given: (hL : forall i, (L i).toBilinForm.IsPosSemidef)
  proof: by
    simp_rw [toBilinForm_diagonalStrongDualPi_apply, fun i => (hL i).eq]
  nonneg x := by
    rw [toBilinForm_diagonalStrongDualPi_apply]
    exact sum_nonneg fun i _ => (hL i).nonneg _

中文:
引理 isPosSemidef_diagonalStrongDualPi
  条件: (hL : 对任意 i, (L i).toBilinForm.是PosSemidef)
  证明: by
    simp_rw [toBilinForm_diagonalStrongDualPi_apply, fun i => (hL i).eq]
  nonneg x := by
    rw [toBilinForm_diagonalStrongDualPi_apply]
    exact sum_nonneg fun i _ => (hL i).nonneg _

Depends on / 依赖: nonneg, simp_rw, sum_nonneg, toBilinForm_diagonalStrongDualPi_apply
-/
lemma isPosSemidef_diagonalStrongDualPi (hL : forall i, (L i).toBilinForm.IsPosSemidef) :
    (diagonalStrongDualPi L).toBilinForm.IsPosSemidef where
  eq x y := by
    simp_rw [toBilinForm_diagonalStrongDualPi_apply, fun i => (hL i).eq]
  nonneg x := by
    rw [toBilinForm_diagonalStrongDualPi_apply]
    exact sum_nonneg fun i _ => (hL i).nonneg _

end Pi

section Prod

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F] [NormedSpace Real F]
  {L₁ : StrongDual Real E ->L[Real] StrongDual Real E ->L[Real] Real}
  {L₂ : StrongDual Real F ->L[Real] StrongDual Real F ->L[Real] Real}

/-- Given `L₁ : E' × E' → ℝ` and `L₂ : F' × F' → ℝ` two continuous bilinear forms,
`diagonalStrongDualProd L₁ L₂` is the continuous bilinear form over `(E × F)'`
which maps `(x, y) : (E × F)' × (E × F)'` to
`L₁ (fun (a, b) ↦ x a) (fun (a, b) ↦ y a) + L₂ (fun (a, b) ↦ x b) (fun (a, b) ↦ y b)`.

This is an implementation detail used in `IndepFun.hasGaussianLaw`. -/
noncomputable
/--
Definition of `diagonalStrongDualProd` / `diagonalStrongDualProd` 的定义

English:
definition diagonalStrongDualProd
  body: letI g : LinearMap.BilinForm Real (StrongDual Real (E × F)) := LinearMap.mk₂ Real
    (fun x y => L₁ (x ∘L (inl Real E F)) (y ∘L (inl Real E F)) + L₂ (x ∘L (inr Real E F)) (y ∘L (inr Real E F)))
    (fun x y z => by simp [add_add_add_comm])
    (fun c m n => by simp [mul_add])
    (fun x y z => by simp [add_add_add_comm])
    (fun c m n => by simp [mul_add])
LinearMap.mkContinuous₂ g (‖L₁‖ + ‖L₂‖) by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_add_le, add_mul, add_mul]
    gcongr
    · grw [le_opNorm₂]
      gcongr <;> grw [opNorm_comp_le, norm_inl_le_one, mul_one]
    · grw [le_opNorm₂]
      gcongr <;> grw [opNorm_comp_le, norm_inr_le_one, mul_one]

中文:
定义 diagonalStrongDualProd
  定义体: letI g : LinearMap.BilinForm Real (StrongDual Real (E × F)) := LinearMap.mk₂ Real
    (fun x y => L₁ (x ∘L (inl Real E F)) (y ∘L (inl Real E F)) + L₂ (x ∘L (inr Real E F)) (y ∘L (inr Real E F)))
    (fun x y z => by simp [add_add_add_comm])
    (fun c m n => by simp [mul_add])
    (fun x y z => by simp [add_add_add_comm])
    (fun c m n => by simp [mul_add])
LinearMap.mkContinuous₂ g (‖L₁‖ + ‖L₂‖) by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_add_le, add_mul, add_mul]
    gcongr
    · grw [le_opNorm₂]
      gcongr <;> grw [opNorm_comp_le, norm_inl_le_one, mul_one]
    · grw [le_opNorm₂]
      gcongr <;> grw [opNorm_comp_le, norm_inr_le_one, mul_one]

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm, LinearMap.mk, LinearMap.mkContinuous, StrongDual, add_add_add_comm, add_mul, mul_add, norm_add_le
-/
def diagonalStrongDualProd
    (L₁ : StrongDual Real E ->L[Real] StrongDual Real E ->L[Real] Real)
    (L₂ : StrongDual Real F ->L[Real] StrongDual Real F ->L[Real] Real) :
    StrongDual Real (E × F) ->L[Real] StrongDual Real (E × F) ->L[Real] Real :=
  letI g : LinearMap.BilinForm Real (StrongDual Real (E × F)) := LinearMap.mk₂ Real
    (fun x y => L₁ (x ∘L (inl Real E F)) (y ∘L (inl Real E F)) + L₂ (x ∘L (inr Real E F)) (y ∘L (inr Real E F)))
    (fun x y z => by simp [add_add_add_comm])
    (fun c m n => by simp [mul_add])
    (fun x y z => by simp [add_add_add_comm])
    (fun c m n => by simp [mul_add])
LinearMap.mkContinuous₂ g (‖L₁‖ + ‖L₂‖) by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_add_le, add_mul, add_mul]
    gcongr
    · grw [le_opNorm₂]
      gcongr <;> grw [opNorm_comp_le, norm_inl_le_one, mul_one]
    · grw [le_opNorm₂]
      gcongr <;> grw [opNorm_comp_le, norm_inr_le_one, mul_one]

/--
lemma `diagonalStrongDualProd_apply` / 引理 `diagonalStrongDualProd_apply`

English:
lemma diagonalStrongDualProd_apply
  given: (x y : StrongDual Real (E × F))
  proof: rfl

中文:
引理 diagonalStrongDualProd_apply
  条件: (x y : StrongDual 实数 (E × F))
  证明: rfl
-/
lemma diagonalStrongDualProd_apply (x y : StrongDual Real (E × F)) :
    diagonalStrongDualProd L₁ L₂ x y =
    L₁ (x ∘L (inl Real E F)) (y ∘L (inl Real E F)) + L₂ (x ∘L (inr Real E F)) (y ∘L (inr Real E F)) := rfl

/--
lemma `toBilinForm_diagonalStrongDualProd_apply` / 引理 `toBilinForm_diagonalStrongDualProd_apply`

English:
lemma toBilinForm_diagonalStrongDualProd_apply
  given: (x y : StrongDual Real (E × F))
  proof: rfl

中文:
引理 toBilinForm_diagonalStrongDualProd_apply
  条件: (x y : StrongDual 实数 (E × F))
  证明: rfl
-/
lemma toBilinForm_diagonalStrongDualProd_apply (x y : StrongDual Real (E × F)) :
    (diagonalStrongDualProd L₁ L₂).toBilinForm x y =
    L₁.toBilinForm (x ∘L (inl Real E F)) (y ∘L (inl Real E F)) +
    L₂.toBilinForm (x ∘L (inr Real E F)) (y ∘L (inr Real E F)) := rfl

/--
lemma `isPosSemidef_diagonalStrongDualProd` / 引理 `isPosSemidef_diagonalStrongDualProd`

English:
lemma isPosSemidef_diagonalStrongDualProd
  proof: by
    simp_rw [toBilinForm_diagonalStrongDualProd_apply, h₁.eq, h₂.eq]
  nonneg x := by
    rw [toBilinForm_diagonalStrongDualProd_apply]
    exact add_nonneg (h₁.nonneg _) (h₂.nonneg _)

中文:
引理 isPosSemidef_diagonalStrongDualProd
  证明: by
    simp_rw [toBilinForm_diagonalStrongDualProd_apply, h₁.eq, h₂.eq]
  nonneg x := by
    rw [toBilinForm_diagonalStrongDualProd_apply]
    exact add_nonneg (h₁.nonneg _) (h₂.nonneg _)

Depends on / 依赖: add_nonneg, nonneg, simp_rw, toBilinForm_diagonalStrongDualProd_apply
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

variable {ι : Type*} [Finite ι] {E : ι -> Type*}
  [forall i, NormedAddCommGroup (E i)] [forall i, MeasurableSpace (E i)]
  [forall i, CompleteSpace (E i)] [forall i, BorelSpace (E i)] [forall i, SecondCountableTopology (E i)]

section NormedSpace

variable [forall i, NormedSpace Real (E i)] {X : Π i, Ω -> (E i)}

/--
lemma `iIndepFun.hasGaussianLaw` / 引理 `iIndepFun.hasGaussianLaw`

English:
lemma iIndepFun.hasGaussianLaw
  given: (hX1 : forall i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P)
  proof: by
    have := hX2.isProbabilityMeasure
    let := Fintype.ofFinite ι
    rw [isGaussian_iff_gaussian_charFunDual]
    classical
    refine ⟨fun i => ∫ x, x ∂P.map (X i),
      .diagonalStrongDualPi (fun i => covarianceBilinDual (P.map (X i))),
      isPosSemidef_diagonalStrongDualPi (fun _ => isPosSemidef_covarianceBilinDual), fun L => ?_⟩
    rw [(iIndepFun_iff_charFunDual_pi (by fun_prop)).1 hX2]
    simp only [← LinearMap.sum_single_apply E (fun i => ∫ x, x ∂P.map (X i)), map_sum, ofReal_sum,
      sum_mul, diagonalStrongDualPi_apply, sum_div, ← sum_sub_distrib, exp_sum]
    congr with i
    rw [(hX1 i).isGaussian_map.charFunDual_eq]; rw [integral_complex_ofReal]; rw [integral_comp_id_comm]; rw [covarianceBilinDual_self_eq_variance]
    · simp
    · exact (hX1 i).isGaussian_map.memLp_two_id
    · exact (hX1 i).isGaussian_map.integrable_id

中文:
引理 iIndepFun.hasGaussianLaw
  条件: (hX1 : 对任意 i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P)
  证明: by
    have := hX2.isProbabilityMeasure
    let := Fintype.ofFinite ι
    rw [isGaussian_iff_gaussian_charFunDual]
    classical
    refine ⟨fun i => ∫ x, x ∂P.map (X i),
      .diagonalStrongDualPi (fun i => covarianceBilinDual (P.map (X i))),
      isPosSemidef_diagonalStrongDualPi (fun _ => isPosSemidef_covarianceBilinDual), fun L => ?_⟩
    rw [(iIndepFun_iff_charFunDual_pi (by fun_prop)).1 hX2]
    simp only [← LinearMap.sum_single_apply E (fun i => ∫ x, x ∂P.map (X i)), map_sum, ofReal_sum,
      sum_mul, diagonalStrongDualPi_apply, sum_div, ← sum_sub_distrib, exp_sum]
    congr with i
    rw [(hX1 i).isGaussian_map.charFunDual_eq]; rw [integral_complex_ofReal]; rw [integral_comp_id_comm]; rw [covarianceBilinDual_self_eq_variance]
    · simp
    · exact (hX1 i).isGaussian_map.memLp_two_id
    · exact (hX1 i).isGaussian_map.integrable_id

Depends on / 依赖: Fintype, Fintype.ofFinite, LinearMap, LinearMap.sum_single_apply, P.map, classical, covarianceBilinDual, diagonalStrongDualPi, diagonalStrongDualPi_apply, fun_prop, hX2.isProbabilityMeasure, iIndepFun_iff_charFunDual_pi, isGaussian_iff_gaussian_charFunDual, isPosSemidef_covarianceBilinDual, isPosSemidef_diagonalStrongDualPi, isProbabilityMeasure, map_sum, ofFinite, ofReal_sum, sum_mul
-/
lemma iIndepFun.hasGaussianLaw (hX1 : forall i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P) :
    HasGaussianLaw (fun ω => (X · ω)) P where
  isGaussian_map := by
    have := hX2.isProbabilityMeasure
    let := Fintype.ofFinite ι
    rw [isGaussian_iff_gaussian_charFunDual]
    classical
    refine ⟨fun i => ∫ x, x ∂P.map (X i),
      .diagonalStrongDualPi (fun i => covarianceBilinDual (P.map (X i))),
      isPosSemidef_diagonalStrongDualPi (fun _ => isPosSemidef_covarianceBilinDual), fun L => ?_⟩
    rw [(iIndepFun_iff_charFunDual_pi (by fun_prop)).1 hX2]
    simp only [← LinearMap.sum_single_apply E (fun i => ∫ x, x ∂P.map (X i)), map_sum, ofReal_sum,
      sum_mul, diagonalStrongDualPi_apply, sum_div, ← sum_sub_distrib, exp_sum]
    congr with i
    rw [(hX1 i).isGaussian_map.charFunDual_eq]; rw [integral_complex_ofReal]; rw [integral_comp_id_comm]; rw [covarianceBilinDual_self_eq_variance]
    · simp
    · exact (hX1 i).isGaussian_map.memLp_two_id
    · exact (hX1 i).isGaussian_map.integrable_id

/--
lemma `HasGaussianLaw.iIndepFun_of_covariance_strongDual` / 引理 `HasGaussianLaw.iIndepFun_of_covariance_strongDual`

English:
lemma HasGaussianLaw.iIndepFun_of_covariance_strongDual
  statement: (hX : HasGaussianLaw (fun ω i => X i ω) P)
  proof: by
  simp_rw [Function.comp_def] at h
  have := hX.isProbabilityMeasure
  classical
  let := Fintype.ofFinite ι
  rw [iIndepFun_iff_charFunDual_pi fun i => hX.aemeasurable.eval i]
  intro L
  have this ω : L (X · ω) = ∑ i, (L ∘L (single Real E i)) (X i ω) := by
    simp [← map_sum, LinearMap.sum_single_apply]
  simp_rw [hX.charFunDual_map_eq_fun, fun i => (hX.eval i).charFunDual_map_eq_fun, ← Complex.exp_sum,
    sum_sub_distrib, ← sum_mul, this]
  congr
  · simp_rw [← Complex.ofReal_sum]
    rw [integral_finsetSum _ fun i _ => ((hX.eval i).map_fun _).integrable.ofReal]
  · rw [variance_fun_sum fun i => ((hX.eval i).map_fun _).memLp_two]
    simp only [← sum_div, ← ofReal_sum, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_left_inj', ofReal_inj]
    congr with i
    rw [sum_eq_single_of_mem i (by grind) (fun j _ hij => h i j hij.symm _ _)]; rw [covariance_self ((hX.eval i).map_fun _).aemeasurable]

中文:
引理 HasGaussianLaw.iIndepFun_of_covariance_strongDual
  结论: (hX : HasGaussianLaw (fun ω i => X i ω) P)
  证明: by
  simp_rw [Function.comp_def] at h
  have := hX.isProbabilityMeasure
  classical
  let := Fintype.ofFinite ι
  rw [iIndepFun_iff_charFunDual_pi fun i => hX.aemeasurable.eval i]
  intro L
  have this ω : L (X · ω) = ∑ i, (L ∘L (single Real E i)) (X i ω) := by
    simp [← map_sum, LinearMap.sum_single_apply]
  simp_rw [hX.charFunDual_map_eq_fun, fun i => (hX.eval i).charFunDual_map_eq_fun, ← Complex.exp_sum,
    sum_sub_distrib, ← sum_mul, this]
  congr
  · simp_rw [← Complex.ofReal_sum]
    rw [integral_finsetSum _ fun i _ => ((hX.eval i).map_fun _).integrable.ofReal]
  · rw [variance_fun_sum fun i => ((hX.eval i).map_fun _).memLp_two]
    simp only [← sum_div, ← ofReal_sum, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_left_inj', ofReal_inj]
    congr with i
    rw [sum_eq_single_of_mem i (by grind) (fun j _ hij => h i j hij.symm _ _)]; rw [covariance_self ((hX.eval i).map_fun _).aemeasurable]

Depends on / 依赖: Complex.exp_sum, Complex.ofReal_sum, Fintype, Fintype.ofFinite, Function, Function.comp_def, LinearMap, LinearMap.sum_single_apply, aemeasurable, charFunDual_map_eq_fun, classical, comp_def, exp_sum, hX.aemeasurable.eval, hX.charFunDual_map_eq_fun, hX.eval, hX.isProbabilityMeasure, iIndepFun_iff_charFunDual_pi, integral_finsetSum, isProbabilityMeasure
-/
lemma HasGaussianLaw.iIndepFun_of_covariance_strongDual (hX : HasGaussianLaw (fun ω i => X i ω) P)
    (h : forall i j, i != j -> forall (L₁ : StrongDual Real (E i)) (L₂ : StrongDual Real (E j)),
      cov[L₁ ∘ (X i), L₂ ∘ (X j); P] = 0) :
    iIndepFun X P := by
  simp_rw [Function.comp_def] at h
  have := hX.isProbabilityMeasure
  classical
  let := Fintype.ofFinite ι
  rw [iIndepFun_iff_charFunDual_pi fun i => hX.aemeasurable.eval i]
  intro L
  have this ω : L (X · ω) = ∑ i, (L ∘L (single Real E i)) (X i ω) := by
    simp [← map_sum, LinearMap.sum_single_apply]
  simp_rw [hX.charFunDual_map_eq_fun, fun i => (hX.eval i).charFunDual_map_eq_fun, ← Complex.exp_sum,
    sum_sub_distrib, ← sum_mul, this]
  congr
  · simp_rw [← Complex.ofReal_sum]
    rw [integral_finsetSum _ fun i _ => ((hX.eval i).map_fun _).integrable.ofReal]
  · rw [variance_fun_sum fun i => ((hX.eval i).map_fun _).memLp_two]
    simp only [← sum_div, ← ofReal_sum, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_left_inj', ofReal_inj]
    congr with i
    rw [sum_eq_single_of_mem i (by grind) (fun j _ hij => h i j hij.symm _ _)]; rw [covariance_self ((hX.eval i).map_fun _).aemeasurable]

end NormedSpace

section InnerProductSpace

variable [forall i, InnerProductSpace Real (E i)]

/--
lemma `HasGaussianLaw.iIndepFun_of_covariance_inner` / 引理 `HasGaussianLaw.iIndepFun_of_covariance_inner`

English:
lemma HasGaussianLaw.iIndepFun_of_covariance_inner
  proof: hX.iIndepFun_of_covariance_strongDual fun i j hij L₁ L₂ => by
    simpa using! h i j hij ((toDual Real (E i)).symm L₁) ((toDual Real (E j)).symm L₂)

中文:
引理 HasGaussianLaw.iIndepFun_of_covariance_inner
  证明: hX.iIndepFun_of_covariance_strongDual fun i j hij L₁ L₂ => by
    simpa using! h i j hij ((toDual Real (E i)).symm L₁) ((toDual Real (E j)).symm L₂)

Depends on / 依赖: hX.iIndepFun_of_covariance_strongDual, iIndepFun_of_covariance_strongDual, toDual
-/
lemma HasGaussianLaw.iIndepFun_of_covariance_inner
    {X : Π i, Ω -> (E i)} (hX : HasGaussianLaw (fun ω i => X i ω) P)
    (h : forall i j, i != j -> forall (x : E i) (y : E j),
      cov[fun ω => ⟪x, X i ω⟫, fun ω => ⟪y, X j ω⟫; P] = 0) :
    iIndepFun X P :=
  hX.iIndepFun_of_covariance_strongDual fun i j hij L₁ L₂ => by
    simpa using! h i j hij ((toDual Real (E i)).symm L₁) ((toDual Real (E j)).symm L₂)

end InnerProductSpace

section Real

/--
lemma `HasGaussianLaw.iIndepFun_of_covariance_eval` / 引理 `HasGaussianLaw.iIndepFun_of_covariance_eval`

English:
lemma HasGaussianLaw.iIndepFun_of_covariance_eval
  statement: {κ : ι -> Type*} [forall i, Finite (κ i)]
  proof: by
  have := hX.isProbabilityMeasure
  have : (fun i ω j => X i j ω) = fun i => (ofLp ∘ (toLp 2 ∘ fun ω j => X i j ω)) := by ext; simp
  rw [this]
  let (i : ι) := Fintype.ofFinite (κ i)
  let := Fintype.ofFinite ι
  refine (HasGaussianLaw.iIndepFun_of_covariance_inner ?_ fun i j hij x y => ?_).comp _ (by fun_prop)
  · exact hX.map_equiv (.piCongrRight (fun _ => (PiLp.continuousLinearEquiv 2 Real (fun _ => Real)).symm))
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x]; rw [← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ => sum_eq_zero fun l _ => ?_
    rw [covariance_const_mul_left]; rw [covariance_const_mul_right]; rw [h i j hij k l]; rw [mul_zero]; rw [mul_zero]
  · simpa using fun j => ((hX.eval i).eval j).memLp_two.const_mul _
  · simpa using fun i => ((hX.eval j).eval i).memLp_two.const_mul _

中文:
引理 HasGaussianLaw.iIndepFun_of_covariance_eval
  结论: {κ : ι -> 类型} [对任意 i, 有限 (κ i)]
  证明: by
  have := hX.isProbabilityMeasure
  have : (fun i ω j => X i j ω) = fun i => (ofLp ∘ (toLp 2 ∘ fun ω j => X i j ω)) := by ext; simp
  rw [this]
  let (i : ι) := Fintype.ofFinite (κ i)
  let := Fintype.ofFinite ι
  refine (HasGaussianLaw.iIndepFun_of_covariance_inner ?_ fun i j hij x y => ?_).comp _ (by fun_prop)
  · exact hX.map_equiv (.piCongrRight (fun _ => (PiLp.continuousLinearEquiv 2 Real (fun _ => Real)).symm))
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x]; rw [← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ => sum_eq_zero fun l _ => ?_
    rw [covariance_const_mul_left]; rw [covariance_const_mul_right]; rw [h i j hij k l]; rw [mul_zero]; rw [mul_zero]
  · simpa using fun j => ((hX.eval i).eval j).memLp_two.const_mul _
  · simpa using fun i => ((hX.eval j).eval i).memLp_two.const_mul _

Depends on / 依赖: EuclideanSpace, EuclideanSpace.basisFun, Fintype, Fintype.ofFinite, HasGaussianLaw, HasGaussianLaw.iIndepFun_of_covariance_inner, PiLp.continuousLinearEquiv, basisFun, continuousLinearEquiv, fun_prop, hX.isProbabilityMeasure, hX.map_equiv, iIndepFun_of_covariance_inner, isProbabilityMeasure, map_equiv, ofFinite, piCongrRight, sum_r, sum_repr
-/
lemma HasGaussianLaw.iIndepFun_of_covariance_eval {κ : ι -> Type*} [forall i, Finite (κ i)]
    {X : (i : ι) -> κ i -> Ω -> Real} (hX : HasGaussianLaw (fun ω i j => X i j ω) P)
    (h : forall i j, i != j -> forall k l, cov[X i k, X j l; P] = 0) :
    iIndepFun (fun i ω j => X i j ω) P := by
  have := hX.isProbabilityMeasure
  have : (fun i ω j => X i j ω) = fun i => (ofLp ∘ (toLp 2 ∘ fun ω j => X i j ω)) := by ext; simp
  rw [this]
  let (i : ι) := Fintype.ofFinite (κ i)
  let := Fintype.ofFinite ι
  refine (HasGaussianLaw.iIndepFun_of_covariance_inner ?_ fun i j hij x y => ?_).comp _ (by fun_prop)
  · exact hX.map_equiv (.piCongrRight (fun _ => (PiLp.continuousLinearEquiv 2 Real (fun _ => Real)).symm))
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x]; rw [← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ => sum_eq_zero fun l _ => ?_
    rw [covariance_const_mul_left]; rw [covariance_const_mul_right]; rw [h i j hij k l]; rw [mul_zero]; rw [mul_zero]
  · simpa using fun j => ((hX.eval i).eval j).memLp_two.const_mul _
  · simpa using fun i => ((hX.eval j).eval i).memLp_two.const_mul _

/--
lemma `HasGaussianLaw.iIndepFun_of_covariance_eq_zero` / 引理 `HasGaussianLaw.iIndepFun_of_covariance_eq_zero`

English:
lemma HasGaussianLaw.iIndepFun_of_covariance_eq_zero
  statement: {X : ι -> Ω -> Real}
  proof: hX.iIndepFun_of_covariance_strongDual fun i j hij L₁ L₂ => by
    simp [Function.comp_def, ← toDual_symm_apply, covariance_mul_const_right,
      covariance_mul_const_left, h, hij]

中文:
引理 HasGaussianLaw.iIndepFun_of_covariance_eq_zero
  结论: {X : ι -> Ω -> 实数}
  证明: hX.iIndepFun_of_covariance_strongDual fun i j hij L₁ L₂ => by
    simp [Function.comp_def, ← toDual_symm_apply, covariance_mul_const_right,
      covariance_mul_const_left, h, hij]

Depends on / 依赖: Function, Function.comp_def, comp_def, covariance_mul_const_left, covariance_mul_const_right, hX.iIndepFun_of_covariance_strongDual, iIndepFun_of_covariance_strongDual, toDual_symm_apply
-/
lemma HasGaussianLaw.iIndepFun_of_covariance_eq_zero {X : ι -> Ω -> Real}
    (hX : HasGaussianLaw (fun ω => (X · ω)) P) (h : forall i j : ι, i != j -> cov[X i, X j; P] = 0) :
    iIndepFun X P :=
  hX.iIndepFun_of_covariance_strongDual fun i j hij L₁ L₂ => by
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

/--
lemma `IndepFun.hasGaussianLaw` / 引理 `IndepFun.hasGaussianLaw`

English:
lemma IndepFun.hasGaussianLaw
  statement: [NormedSpace Real E] [NormedSpace Real F] {X : Ω -> E} {Y : Ω -> F}
  proof: by
    have := hX.isProbabilityMeasure
    rw [isGaussian_iff_gaussian_charFunDual]
    refine ⟨(∫ x, x ∂P.map X, ∫ y, y ∂P.map Y),
      .diagonalStrongDualProd (covarianceBilinDual (P.map X)) (covarianceBilinDual (P.map Y)),
      isPosSemidef_diagonalStrongDualProd isPosSemidef_covarianceBilinDual
        isPosSemidef_covarianceBilinDual, fun L => ?_⟩
    rw [(indepFun_iff_charFunDual_prod (by fun_prop) (by fun_prop)).1 hXY]
    have : (∫ x, x ∂Measure.map X P, ∫ y, y ∂Measure.map Y P) =
        ContinuousLinearMap.inl Real E F (∫ x, x ∂Measure.map X P) +
        ContinuousLinearMap.inr Real E F (∫ y, y ∂Measure.map Y P) := by simp
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

中文:
引理 IndepFun.hasGaussianLaw
  结论: [赋范空间 实数 E] [赋范空间 实数 F] {X : Ω -> E} {Y : Ω -> F}
  证明: by
    have := hX.isProbabilityMeasure
    rw [isGaussian_iff_gaussian_charFunDual]
    refine ⟨(∫ x, x ∂P.map X, ∫ y, y ∂P.map Y),
      .diagonalStrongDualProd (covarianceBilinDual (P.map X)) (covarianceBilinDual (P.map Y)),
      isPosSemidef_diagonalStrongDualProd isPosSemidef_covarianceBilinDual
        isPosSemidef_covarianceBilinDual, fun L => ?_⟩
    rw [(indepFun_iff_charFunDual_prod (by fun_prop) (by fun_prop)).1 hXY]
    have : (∫ x, x ∂Measure.map X P, ∫ y, y ∂Measure.map Y P) =
        ContinuousLinearMap.inl Real E F (∫ x, x ∂Measure.map X P) +
        ContinuousLinearMap.inr Real E F (∫ y, y ∂Measure.map Y P) := by simp
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

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.inl, Measure, Measure.map, P.map, covarianceBilinDual, diagonalStrongDualProd, fun_prop, hX.isProbabilityMeasure, indepFun_iff_charFunDual_prod, isGaussian_iff_gaussian_charFunDual, isPosSemidef_covarianceBilinDual, isPosSemidef_diagonalStrongDualProd, isProbabilityMeasure
-/
lemma IndepFun.hasGaussianLaw [NormedSpace Real E] [NormedSpace Real F] {X : Ω -> E} {Y : Ω -> F}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (hXY : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (fun ω => (X ω, Y ω)) P where
  isGaussian_map := by
    have := hX.isProbabilityMeasure
    rw [isGaussian_iff_gaussian_charFunDual]
    refine ⟨(∫ x, x ∂P.map X, ∫ y, y ∂P.map Y),
      .diagonalStrongDualProd (covarianceBilinDual (P.map X)) (covarianceBilinDual (P.map Y)),
      isPosSemidef_diagonalStrongDualProd isPosSemidef_covarianceBilinDual
        isPosSemidef_covarianceBilinDual, fun L => ?_⟩
    rw [(indepFun_iff_charFunDual_prod (by fun_prop) (by fun_prop)).1 hXY]
    have : (∫ x, x ∂Measure.map X P, ∫ y, y ∂Measure.map Y P) =
        ContinuousLinearMap.inl Real E F (∫ x, x ∂Measure.map X P) +
        ContinuousLinearMap.inr Real E F (∫ y, y ∂Measure.map Y P) := by simp
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

/--
lemma `HasGaussianLaw.indepFun_of_covariance_strongDual` / 引理 `HasGaussianLaw.indepFun_of_covariance_strongDual`

English:
lemma HasGaussianLaw.indepFun_of_covariance_strongDual
  statement: [NormedSpace Real E] [NormedSpace Real F]
  proof: by
  have := hXY.isProbabilityMeasure
  rw [indepFun_iff_charFunDual_prod hXY.fst.aemeasurable hXY.snd.aemeasurable]
  intro L
  have : L ∘ (fun ω => (X ω, Y ω)) = (L ∘L (.inl Real E F)) ∘ X + (L ∘L (.inr Real E F)) ∘ Y := by
    ext; simp [-comp_apply, ← comp_inl_add_comp_inr]
  rw [hXY.charFunDual_map_eq]; rw [hXY.fst.charFunDual_map_eq]; rw [hXY.snd.charFunDual_map_eq]; rw [← exp_add]; rw [sub_add_sub_comm]; rw [← add_mul]; rw [← ofReal_add]; rw [← integral_add]; rw [← add_div]; rw [← ofReal_add]; rw [this]; rw [variance_add]; rw [h]; rw [mul_zero]; rw [add_zero]
  · simp
  · exact (hXY.fst.map _).memLp_two
  · exact (hXY.snd.map _).memLp_two
  · exact (hXY.fst.map _).integrable
  · exact (hXY.snd.map _).integrable

中文:
引理 HasGaussianLaw.indepFun_of_covariance_strongDual
  结论: [赋范空间 实数 E] [赋范空间 实数 F]
  证明: by
  have := hXY.isProbabilityMeasure
  rw [indepFun_iff_charFunDual_prod hXY.fst.aemeasurable hXY.snd.aemeasurable]
  intro L
  have : L ∘ (fun ω => (X ω, Y ω)) = (L ∘L (.inl Real E F)) ∘ X + (L ∘L (.inr Real E F)) ∘ Y := by
    ext; simp [-comp_apply, ← comp_inl_add_comp_inr]
  rw [hXY.charFunDual_map_eq]; rw [hXY.fst.charFunDual_map_eq]; rw [hXY.snd.charFunDual_map_eq]; rw [← exp_add]; rw [sub_add_sub_comm]; rw [← add_mul]; rw [← ofReal_add]; rw [← integral_add]; rw [← add_div]; rw [← ofReal_add]; rw [this]; rw [variance_add]; rw [h]; rw [mul_zero]; rw [add_zero]
  · simp
  · exact (hXY.fst.map _).memLp_two
  · exact (hXY.snd.map _).memLp_two
  · exact (hXY.fst.map _).integrable
  · exact (hXY.snd.map _).integrable

Depends on / 依赖: add_div, add_mul, aemeasurable, charFunDual_map_eq, comp_apply, comp_inl_add_comp_inr, exp_add, hXY.charFunDual_map_eq, hXY.fst.aemeasurable, hXY.fst.charFunDual_map_eq, hXY.isProbabilityMeasure, hXY.snd.aemeasurable, hXY.snd.charFunDual_map_eq, indepFun_iff_charFunDual_prod, integral_add, isProbabilityMeasure, ofReal_add, sub_add_sub_comm
-/
lemma HasGaussianLaw.indepFun_of_covariance_strongDual [NormedSpace Real E] [NormedSpace Real F]
    {X : Ω -> E} {Y : Ω -> F} (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (h : forall (L₁ : StrongDual Real E) (L₂ : StrongDual Real F), cov[L₁ ∘ X, L₂ ∘ Y; P] = 0) :
    IndepFun X Y P := by
  have := hXY.isProbabilityMeasure
  rw [indepFun_iff_charFunDual_prod hXY.fst.aemeasurable hXY.snd.aemeasurable]
  intro L
  have : L ∘ (fun ω => (X ω, Y ω)) = (L ∘L (.inl Real E F)) ∘ X + (L ∘L (.inr Real E F)) ∘ Y := by
    ext; simp [-comp_apply, ← comp_inl_add_comp_inr]
  rw [hXY.charFunDual_map_eq]; rw [hXY.fst.charFunDual_map_eq]; rw [hXY.snd.charFunDual_map_eq]; rw [← exp_add]; rw [sub_add_sub_comm]; rw [← add_mul]; rw [← ofReal_add]; rw [← integral_add]; rw [← add_div]; rw [← ofReal_add]; rw [this]; rw [variance_add]; rw [h]; rw [mul_zero]; rw [add_zero]
  · simp
  · exact (hXY.fst.map _).memLp_two
  · exact (hXY.snd.map _).memLp_two
  · exact (hXY.fst.map _).integrable
  · exact (hXY.snd.map _).integrable

/--
lemma `HasGaussianLaw.indepFun_of_covariance_inner` / 引理 `HasGaussianLaw.indepFun_of_covariance_inner`

English:
lemma HasGaussianLaw.indepFun_of_covariance_inner
  statement: [InnerProductSpace Real E] [InnerProductSpace Real F]
  proof: hXY.indepFun_of_covariance_strongDual fun L₁ L₂ => by
    simpa using! h ((toDual Real E).symm L₁) ((toDual Real F).symm L₂)

中文:
引理 HasGaussianLaw.indepFun_of_covariance_inner
  结论: [内积空间 实数 E] [内积空间 实数 F]
  证明: hXY.indepFun_of_covariance_strongDual fun L₁ L₂ => by
    simpa using! h ((toDual Real E).symm L₁) ((toDual Real F).symm L₂)

Depends on / 依赖: hXY.indepFun_of_covariance_strongDual, indepFun_of_covariance_strongDual, toDual
-/
lemma HasGaussianLaw.indepFun_of_covariance_inner [InnerProductSpace Real E] [InnerProductSpace Real F]
    {X : Ω -> E} {Y : Ω -> F} (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (h : forall x y, cov[fun ω => ⟪x, X ω⟫, fun ω => ⟪y, Y ω⟫; P] = 0) :
    IndepFun X Y P :=
  hXY.indepFun_of_covariance_strongDual fun L₁ L₂ => by
    simpa using! h ((toDual Real E).symm L₁) ((toDual Real F).symm L₂)

/--
lemma `HasGaussianLaw.indepFun_of_covariance_eval` / 引理 `HasGaussianLaw.indepFun_of_covariance_eval`

English:
lemma HasGaussianLaw.indepFun_of_covariance_eval
  statement: {ι κ : Type*} [Finite ι] [Finite κ]
  proof: by
  have := hXY.isProbabilityMeasure
  have hX : (fun ω i => X i ω) = (ofLp ∘ (toLp 2 ∘ fun ω i => X i ω)) := by ext; simp
  have hY : (fun ω j => Y j ω) = (ofLp ∘ (toLp 2 ∘ fun ω j => Y j ω)) := by ext; simp
  rw [hX]; rw [hY]
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  refine IndepFun.comp (HasGaussianLaw.indepFun_of_covariance_inner ?_ fun x y => ?_)
    (by fun_prop) (by fun_prop)
  · exact hXY.map_equiv (.prodCongr (PiLp.continuousLinearEquiv 2 Real (fun _ => Real)).symm
      (PiLp.continuousLinearEquiv 2 Real (fun _ => Real)).symm)
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x]; rw [← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ => sum_eq_zero fun l _ => ?_
    rw [covariance_const_mul_left]; rw [covariance_const_mul_right]; rw [h]; rw [mul_zero]; rw [mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
    EuclideanSpace.basisFun_inner]
    exact fun i => (hXY.fst.eval i).memLp_two.const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun j => (hXY.snd.eval j).memLp_two.const_mul _

中文:
引理 HasGaussianLaw.indepFun_of_covariance_eval
  结论: {ι κ : 类型} [有限 ι] [有限 κ]
  证明: by
  have := hXY.isProbabilityMeasure
  have hX : (fun ω i => X i ω) = (ofLp ∘ (toLp 2 ∘ fun ω i => X i ω)) := by ext; simp
  have hY : (fun ω j => Y j ω) = (ofLp ∘ (toLp 2 ∘ fun ω j => Y j ω)) := by ext; simp
  rw [hX]; rw [hY]
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  refine IndepFun.comp (HasGaussianLaw.indepFun_of_covariance_inner ?_ fun x y => ?_)
    (by fun_prop) (by fun_prop)
  · exact hXY.map_equiv (.prodCongr (PiLp.continuousLinearEquiv 2 Real (fun _ => Real)).symm
      (PiLp.continuousLinearEquiv 2 Real (fun _ => Real)).symm)
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x]; rw [← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ => sum_eq_zero fun l _ => ?_
    rw [covariance_const_mul_left]; rw [covariance_const_mul_right]; rw [h]; rw [mul_zero]; rw [mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
    EuclideanSpace.basisFun_inner]
    exact fun i => (hXY.fst.eval i).memLp_two.const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun j => (hXY.snd.eval j).memLp_two.const_mul _

Depends on / 依赖: Fintype, Fintype.ofFinite, HasGaussianLaw, HasGaussianLaw.indepFun_of_covariance_inner, IndepFun, IndepFun.comp, PiLp.continuousLinearEq, PiLp.continuousLinearEquiv, continuousLinearEq, continuousLinearEquiv, fun_prop, hXY.isProbabilityMeasure, hXY.map_equiv, indepFun_of_covariance_inner, isProbabilityMeasure, map_equiv, ofFinite, prodCongr
-/
lemma HasGaussianLaw.indepFun_of_covariance_eval {ι κ : Type*} [Finite ι] [Finite κ]
    {X : ι -> Ω -> Real} {Y : κ -> Ω -> Real}
    (hXY : HasGaussianLaw (fun ω => (fun i => X i ω, fun j => Y j ω)) P)
    (h : forall i j, cov[X i, Y j; P] = 0) :
    IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) P := by
  have := hXY.isProbabilityMeasure
  have hX : (fun ω i => X i ω) = (ofLp ∘ (toLp 2 ∘ fun ω i => X i ω)) := by ext; simp
  have hY : (fun ω j => Y j ω) = (ofLp ∘ (toLp 2 ∘ fun ω j => Y j ω)) := by ext; simp
  rw [hX]; rw [hY]
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  refine IndepFun.comp (HasGaussianLaw.indepFun_of_covariance_inner ?_ fun x y => ?_)
    (by fun_prop) (by fun_prop)
  · exact hXY.map_equiv (.prodCongr (PiLp.continuousLinearEquiv 2 Real (fun _ => Real)).symm
      (PiLp.continuousLinearEquiv 2 Real (fun _ => Real)).symm)
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x]; rw [← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ => sum_eq_zero fun l _ => ?_
    rw [covariance_const_mul_left]; rw [covariance_const_mul_right]; rw [h]; rw [mul_zero]; rw [mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
    EuclideanSpace.basisFun_inner]
    exact fun i => (hXY.fst.eval i).memLp_two.const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun j => (hXY.snd.eval j).memLp_two.const_mul _

/--
lemma `HasGaussianLaw.indepFun_of_covariance_eq_zero` / 引理 `HasGaussianLaw.indepFun_of_covariance_eq_zero`

English:
lemma HasGaussianLaw.indepFun_of_covariance_eq_zero
  statement: {X Y : Ω -> Real}
  proof: hXY.indepFun_of_covariance_strongDual fun L₁ L₂ => by
    simp [Function.comp_def, ← toDual_symm_apply, covariance_mul_const_right,
      covariance_mul_const_left, h]

中文:
引理 HasGaussianLaw.indepFun_of_covariance_eq_zero
  结论: {X Y : Ω -> 实数}
  证明: hXY.indepFun_of_covariance_strongDual fun L₁ L₂ => by
    simp [Function.comp_def, ← toDual_symm_apply, covariance_mul_const_right,
      covariance_mul_const_left, h]

Depends on / 依赖: Function, Function.comp_def, comp_def, covariance_mul_const_left, covariance_mul_const_right, hXY.indepFun_of_covariance_strongDual, indepFun_of_covariance_strongDual, toDual_symm_apply
-/
lemma HasGaussianLaw.indepFun_of_covariance_eq_zero {X Y : Ω -> Real}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) (h : cov[X, Y; P] = 0) :
    IndepFun X Y P :=
  hXY.indepFun_of_covariance_strongDual fun L₁ L₂ => by
    simp [Function.comp_def, ← toDual_symm_apply, covariance_mul_const_right,
      covariance_mul_const_left, h]

end IndepFun

section AddSub

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/--
lemma `iIndepFun.hasGaussianLaw_sum` / 引理 `iIndepFun.hasGaussianLaw_sum`

English:
lemma iIndepFun.hasGaussianLaw_sum
  statement: [CompleteSpace E] {ι : Type*} [Fintype ι] {X : ι -> Ω -> E}
  proof: (hX2.hasGaussianLaw hX1).sum

中文:
引理 iIndepFun.hasGaussianLaw_sum
  结论: [完备空间 E] {ι : 类型} [有限类型 ι] {X : ι -> Ω -> E}
  证明: (hX2.hasGaussianLaw hX1).sum

Depends on / 依赖: hX2.hasGaussianLaw, hasGaussianLaw
-/
lemma iIndepFun.hasGaussianLaw_sum [CompleteSpace E] {ι : Type*} [Fintype ι] {X : ι -> Ω -> E}
    (hX1 : forall i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P) :
    HasGaussianLaw (∑ i, X i) P :=
  (hX2.hasGaussianLaw hX1).sum

/--
lemma `iIndepFun.hasGaussianLaw_fun_sum` / 引理 `iIndepFun.hasGaussianLaw_fun_sum`

English:
lemma iIndepFun.hasGaussianLaw_fun_sum
  statement: [CompleteSpace E] {ι : Type*} [Fintype ι] {X : ι -> Ω -> E}
  proof: (hX2.hasGaussianLaw hX1).fun_sum

中文:
引理 iIndepFun.hasGaussianLaw_fun_sum
  结论: [完备空间 E] {ι : 类型} [有限类型 ι] {X : ι -> Ω -> E}
  证明: (hX2.hasGaussianLaw hX1).fun_sum

Depends on / 依赖: fun_sum, hX2.hasGaussianLaw, hasGaussianLaw
-/
lemma iIndepFun.hasGaussianLaw_fun_sum [CompleteSpace E] {ι : Type*} [Fintype ι] {X : ι -> Ω -> E}
    (hX1 : forall i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P) :
    HasGaussianLaw (fun ω => ∑ i, X i ω) P :=
    (hX2.hasGaussianLaw hX1).fun_sum

/--
lemma `iIndepFun.hasGaussianLaw_add` / 引理 `iIndepFun.hasGaussianLaw_add`

English:
lemma iIndepFun.hasGaussianLaw_add
  statement: [CompleteSpace E] {X Y : Ω -> E}
  proof: (h.hasGaussianLaw hX hY).add

中文:
引理 iIndepFun.hasGaussianLaw_add
  结论: [完备空间 E] {X Y : Ω -> E}
  证明: (h.hasGaussianLaw hX hY).add

Depends on / 依赖: h.hasGaussianLaw, hasGaussianLaw
-/
lemma iIndepFun.hasGaussianLaw_add [CompleteSpace E] {X Y : Ω -> E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (X + Y) P :=
  (h.hasGaussianLaw hX hY).add

/--
lemma `iIndepFun.hasGaussianLaw_fun_add` / 引理 `iIndepFun.hasGaussianLaw_fun_add`

English:
lemma iIndepFun.hasGaussianLaw_fun_add
  statement: [CompleteSpace E] {X Y : Ω -> E}
  proof: (h.hasGaussianLaw hX hY).add

中文:
引理 iIndepFun.hasGaussianLaw_fun_add
  结论: [完备空间 E] {X Y : Ω -> E}
  证明: (h.hasGaussianLaw hX hY).add

Depends on / 依赖: Finite, Module, Module.Finite.equiv, MvPolynomial, MvPolynomial.isEmptyAlgEquiv, h.hasGaussianLaw, hasGaussianLaw, isEmptyAlgEquiv, toLinearEquiv, toLinearEquiv.symm
-/
lemma iIndepFun.hasGaussianLaw_fun_add [CompleteSpace E] {X Y : Ω -> E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (fun ω => X ω + Y ω) P :=
  (h.hasGaussianLaw hX hY).add

/--
lemma `iIndepFun.hasGaussianLaw_sub` / 引理 `iIndepFun.hasGaussianLaw_sub`

English:
lemma iIndepFun.hasGaussianLaw_sub
  statement: [CompleteSpace E] {X Y : Ω -> E}
  proof: (h.hasGaussianLaw hX hY).sub

中文:
引理 iIndepFun.hasGaussianLaw_sub
  结论: [完备空间 E] {X Y : Ω -> E}
  证明: (h.hasGaussianLaw hX hY).sub

Depends on / 依赖: h.hasGaussianLaw, hasGaussianLaw
-/
lemma iIndepFun.hasGaussianLaw_sub [CompleteSpace E] {X Y : Ω -> E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (X - Y) P :=
  (h.hasGaussianLaw hX hY).sub

/--
lemma `iIndepFun.hasGaussianLaw_fun_sub` / 引理 `iIndepFun.hasGaussianLaw_fun_sub`

English:
lemma iIndepFun.hasGaussianLaw_fun_sub
  statement: [CompleteSpace E] {X Y : Ω -> E}
  proof: (h.hasGaussianLaw hX hY).sub

中文:
引理 iIndepFun.hasGaussianLaw_fun_sub
  结论: [完备空间 E] {X Y : Ω -> E}
  证明: (h.hasGaussianLaw hX hY).sub

Depends on / 依赖: h.hasGaussianLaw, hasGaussianLaw
-/
lemma iIndepFun.hasGaussianLaw_fun_sub [CompleteSpace E] {X Y : Ω -> E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (fun ω => X ω - Y ω) P :=
  (h.hasGaussianLaw hX hY).sub

/--
lemma `IndepFun.hasGaussianLaw_sub_of_sub` / 引理 `IndepFun.hasGaussianLaw_sub_of_sub`

English:
lemma IndepFun.hasGaussianLaw_sub_of_sub
  statement: {X Y : Ω -> E} (hX : HasGaussianLaw X P)
  proof: by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  rw [hasGaussianLaw_iff_charFunDual_map_eq (by fun_prop)]
  intro L
  apply mul_left_cancel₀ (a := charFunDual (P.map X) L)
  · simp [hX.charFunDual_map_eq]
  rw [← Pi.mul_apply]; rw [← h.charFunDual_map_add_eq_mul]; rw [add_sub_cancel]; rw [hX.charFunDual_map_eq]; rw [← exp_add]; rw [sub_add_sub_comm]; rw [← add_mul]; rw [← ofReal_add]; rw [← integral_add]; rw [← add_div]; rw [← ofReal_add]; rw [← IndepFun.variance_add]; rw [hY.charFunDual_map_eq]
  · congr with ω <;> simp
  any_goals fun_prop
  · exact (hX.map L).memLp_two
  · rw [map_comp_sub]
    exact (hY.map L).memLp_two.sub (hX.map L).memLp_two
  · exact h.comp (by fun_prop) (by fun_prop)
  · exact (hX.map L).integrable
  · rw [map_comp_sub]
    exact (hY.map L).integrable.sub (hX.map L).integrable

中文:
引理 IndepFun.hasGaussianLaw_sub_of_sub
  结论: {X Y : Ω -> E} (hX : HasGaussianLaw X P)
  证明: by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  rw [hasGaussianLaw_iff_charFunDual_map_eq (by fun_prop)]
  intro L
  apply mul_left_cancel₀ (a := charFunDual (P.map X) L)
  · simp [hX.charFunDual_map_eq]
  rw [← Pi.mul_apply]; rw [← h.charFunDual_map_add_eq_mul]; rw [add_sub_cancel]; rw [hX.charFunDual_map_eq]; rw [← exp_add]; rw [sub_add_sub_comm]; rw [← add_mul]; rw [← ofReal_add]; rw [← integral_add]; rw [← add_div]; rw [← ofReal_add]; rw [← IndepFun.variance_add]; rw [hY.charFunDual_map_eq]
  · congr with ω <;> simp
  any_goals fun_prop
  · exact (hX.map L).memLp_two
  · rw [map_comp_sub]
    exact (hY.map L).memLp_two.sub (hX.map L).memLp_two
  · exact h.comp (by fun_prop) (by fun_prop)
  · exact (hX.map L).integrable
  · rw [map_comp_sub]
    exact (hY.map L).integrable.sub (hX.map L).integrable

Depends on / 依赖: IndepFun, IndepFun.variance_add, IsProbabilityMeasure, P.map, Pi.mul_apply, add_div, add_mul, add_sub_cancel, charFunDual, charFunDual_map_, charFunDual_map_add_eq_mul, charFunDual_map_eq, exp_add, fun_prop, h.charFunDual_map_add_eq_mul, hX.charFunDual_map_eq, hX.isProbabilityMeasure, hY.charFunDual_map_, hasGaussianLaw_iff_charFunDual_map_eq, integral_add
-/
lemma IndepFun.hasGaussianLaw_sub_of_sub {X Y : Ω -> E} (hX : HasGaussianLaw X P)
    (hY : HasGaussianLaw Y P) (h : IndepFun X (Y - X) P) :
    HasGaussianLaw (Y - X) P := by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  rw [hasGaussianLaw_iff_charFunDual_map_eq (by fun_prop)]
  intro L
  apply mul_left_cancel₀ (a := charFunDual (P.map X) L)
  · simp [hX.charFunDual_map_eq]
  rw [← Pi.mul_apply]; rw [← h.charFunDual_map_add_eq_mul]; rw [add_sub_cancel]; rw [hX.charFunDual_map_eq]; rw [← exp_add]; rw [sub_add_sub_comm]; rw [← add_mul]; rw [← ofReal_add]; rw [← integral_add]; rw [← add_div]; rw [← ofReal_add]; rw [← IndepFun.variance_add]; rw [hY.charFunDual_map_eq]
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
