/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Instances.RealVectorSpace

/-!

# Normed space structure on `ℂ`.

This file gathers basic facts of analytic nature on the complex numbers.

## Main results

This file registers `ℂ` as a normed field, expresses basic properties of the norm, and gives tools
on the real vector space structure of `ℂ`. Notably, it defines the following functions in the
namespace `Complex`.

|Name |Type |Description |
|------------------|-------------|--------------------------------------------------------|
|`equivRealProdCLM`|ℂ ≃L[ℝ] ℝ × ℝ|The natural `ContinuousLinearEquiv` from `ℂ` to `ℝ × ℝ` |
|`reCLM` |ℂ →L[ℝ] ℝ |Real part function as a `ContinuousLinearMap` |
|`imCLM` |ℂ →L[ℝ] ℝ |Imaginary part function as a `ContinuousLinearMap` |
|`ofRealCLM` |ℝ →L[ℝ] ℂ |Embedding of the reals as a `ContinuousLinearMap` |
|`ofRealLI` |ℝ →ₗᵢ[ℝ] ℂ |Embedding of the reals as a `LinearIsometry` |
|`conjCLE` |ℂ ≃L[ℝ] ℂ |Complex conjugation as a `ContinuousLinearEquiv` |
|`conjLIE` |ℂ ≃ₗᵢ[ℝ] ℂ |Complex conjugation as a `LinearIsometryEquiv` |

We also register the fact that `ℂ` is an `RCLike` field.

-/

@[expose] public section


assert_not_exists Absorbs

namespace Complex

/--
Instance `instModuleSelf` / 实例 `instModuleSelf`

English:
instance instModuleSelf
  signature: : Module Complex Complex
  body: delta% inferInstance

中文:
实例 instModuleSelf
  签名: : Module Complex Complex
  定义体: delta% inferInstance
-/
instance instModuleSelf : Module Complex Complex := delta% inferInstance

end Complex

noncomputable section

namespace Complex
variable {z : Complex}

open ComplexConjugate Topology Filter

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedField Complex
  body: rfl
  norm_mul := Complex.norm_mul

中文:
实例 :
  签名: NormedField Complex
  定义体: rfl
  norm_mul := Complex.norm_mul
-/
instance : NormedField Complex where
  dist_eq _ _ := rfl
  norm_mul := Complex.norm_mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DenselyNormedField Complex
  body: let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [norm_real, Real.norm_of_nonneg (h₀.trans_lt h.1).le]⟩

中文:
实例 :
  签名: DenselyNormedField Complex
  定义体: let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [norm_real, Real.norm_of_nonneg (h₀.trans_lt h.1).le]⟩

Depends on / 依赖: Real.norm_of_nonneg, exists_between, norm_of_nonneg, norm_real, trans_lt
-/
instance : DenselyNormedField Complex where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [norm_real, Real.norm_of_nonneg (h₀.trans_lt h.1).le]⟩

instance {R : Type*} [NormedField R] [NormedAlgebra R Real] : NormedAlgebra R Complex where
  norm_smul_le r x := by
    rw [← algebraMap_smul Real r x]; rw [real_smul]; rw [norm_mul]; rw [norm_real]; rw [norm_algebraMap']

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace Complex E]

-- see Note [lower instance priority]
/-- The module structure from `Module.complexToReal` is a normed space. -/
instance (priority := 900) _root_.NormedSpace.complexToReal : NormedSpace Real E :=
  NormedSpace.restrictScalars Real Complex E

-- see Note [lower instance priority]
/-- The algebra structure from `Algebra.complexToReal` is a normed algebra. -/
instance (priority := 900) _root_.NormedAlgebra.complexToReal {A : Type*} [SeminormedRing A]
    [NormedAlgebra Complex A] : NormedAlgebra Real A :=
  NormedAlgebra.restrictScalars Real Complex A

-- This result cannot be moved to `Data/Complex/Norm` since `ℤ` gets its norm from its
-- normed ring structure and that file does not know about rings
/--
lemma `nnnorm_intCast` / 引理 `nnnorm_intCast`

English:
lemma nnnorm_intCast
  given: (n : Int)
  statement: ‖(n : Complex)‖₊ = ‖n‖₊
  proof: by
  ext; exact norm_intCast n

@[continuity, fun_prop]

中文:
引理 nnnorm_intCast
  条件: (n : 整数)
  结论: ‖(n : Complex)‖₊ = ‖n‖₊
  证明: by
  ext; exact norm_intCast n

@[continuity, fun_prop]
-/
@[simp 1100, norm_cast] lemma nnnorm_intCast (n : Int) : ‖(n : Complex)‖₊ = ‖n‖₊ := by
  ext; exact norm_intCast n

@[continuity, fun_prop]
/--
theorem `continuous_normSq` / 定理 `continuous_normSq`

English:
theorem continuous_normSq
  statement: Continuous normSq
  proof: by
  simpa [← Complex.normSq_eq_norm_sq] using continuous_norm (E := Complex).fun_pow 2

中文:
定理 continuous_normSq
  结论: Continuous normSq
  证明: by
  simpa [← Complex.normSq_eq_norm_sq] using continuous_norm (E := Complex).fun_pow 2

Depends on / 依赖: Complex.normSq_eq_norm_sq, continuous_norm, fun_pow, normSq_eq_norm_sq
-/
theorem continuous_normSq : Continuous normSq := by
  simpa [← Complex.normSq_eq_norm_sq] using continuous_norm (E := Complex).fun_pow 2

/--
theorem `nnnorm_eq_one_of_pow_eq_one` / 定理 `nnnorm_eq_one_of_pow_eq_one`

English:
theorem nnnorm_eq_one_of_pow_eq_one
  given: {ζ : Complex} {n : Nat} (h : ζ ^ n = 1) (hn : n != 0)
  statement: ‖ζ‖₊ = 1
  proof: (pow_left_inj₀ zero_le zero_le hn).1 by rw [← nnnorm_pow, h, nnnorm_one, one_pow]

中文:
定理 nnnorm_eq_one_of_pow_eq_one
  条件: {ζ : Complex} {n : 自然数} (h : ζ ^ n = 1) (hn : n != 0)
  结论: ‖ζ‖₊ = 1
  证明: (pow_left_inj₀ zero_le zero_le hn).1 by rw [← nnnorm_pow, h, nnnorm_one, one_pow]

Depends on / 依赖: nnnorm_one, nnnorm_pow, one_pow, zero_le
-/
theorem nnnorm_eq_one_of_pow_eq_one {ζ : Complex} {n : Nat} (h : ζ ^ n = 1) (hn : n != 0) : ‖ζ‖₊ = 1 :=
(pow_left_inj₀ zero_le zero_le hn).1 by rw [← nnnorm_pow, h, nnnorm_one, one_pow]

/--
theorem `norm_eq_one_of_pow_eq_one` / 定理 `norm_eq_one_of_pow_eq_one`

English:
theorem norm_eq_one_of_pow_eq_one
  given: {ζ : Complex} {n : Nat} (h : ζ ^ n = 1) (hn : n != 0)
  statement: ‖ζ‖ = 1
  proof: congr_arg Subtype.val (nnnorm_eq_one_of_pow_eq_one h hn)

中文:
定理 norm_eq_one_of_pow_eq_one
  条件: {ζ : Complex} {n : 自然数} (h : ζ ^ n = 1) (hn : n != 0)
  结论: ‖ζ‖ = 1
  证明: congr_arg Subtype.val (nnnorm_eq_one_of_pow_eq_one h hn)

Depends on / 依赖: Subtype, Subtype.val, congr_arg, nnnorm_eq_one_of_pow_eq_one
-/
theorem norm_eq_one_of_pow_eq_one {ζ : Complex} {n : Nat} (h : ζ ^ n = 1) (hn : n != 0) : ‖ζ‖ = 1 :=
  congr_arg Subtype.val (nnnorm_eq_one_of_pow_eq_one h hn)

/--
lemma `le_of_eq_sum_of_eq_sum_norm` / 引理 `le_of_eq_sum_of_eq_sum_norm`

English:
lemma le_of_eq_sum_of_eq_sum_norm
  statement: {ι : Type*} {a b : Real} (f : ι -> Complex) (s : Finset ι) (ha₀ : 0 <= a)
  proof: by
  norm_cast at hb; rw [← Complex.norm_of_nonneg ha₀, ha, hb]; exact norm_sum_le s f

中文:
引理 le_of_eq_sum_of_eq_sum_norm
  结论: {ι : 类型} {a b : 实数} (f : ι -> Complex) (s : Finset ι) (ha₀ : 0 <= a)
  证明: by
  norm_cast at hb; rw [← Complex.norm_of_nonneg ha₀, ha, hb]; exact norm_sum_le s f

Depends on / 依赖: Complex.norm_of_nonneg, norm_of_nonneg, norm_sum_le, quasispectrum, quasispectrum.zero_mem, zero_mem
-/
lemma le_of_eq_sum_of_eq_sum_norm {ι : Type*} {a b : Real} (f : ι -> Complex) (s : Finset ι) (ha₀ : 0 <= a)
    (ha : a = ∑ i in s, f i) (hb : b = ∑ i in s, (‖f i‖ : Complex)) : a <= b := by
  norm_cast at hb; rw [← Complex.norm_of_nonneg ha₀, ha, hb]; exact norm_sum_le s f

/--
theorem `equivRealProd_apply_le` / 定理 `equivRealProd_apply_le`

English:
theorem equivRealProd_apply_le
  given: (z : Complex)
  statement: ‖equivRealProd z‖ <= ‖z‖
  proof: by
  simp [Prod.norm_def, abs_re_le_norm, abs_im_le_norm]

中文:
定理 equivRealProd_apply_le
  条件: (z : Complex)
  结论: ‖equiv实数Prod z‖ <= ‖z‖
  证明: by
  simp [Prod.norm_def, abs_re_le_norm, abs_im_le_norm]

Depends on / 依赖: Prod.norm_def, abs_im_le_norm, abs_re_le_norm, norm_def
-/
theorem equivRealProd_apply_le (z : Complex) : ‖equivRealProd z‖ <= ‖z‖ := by
  simp [Prod.norm_def, abs_re_le_norm, abs_im_le_norm]

/--
theorem `equivRealProd_apply_le'` / 定理 `equivRealProd_apply_le'`

English:
theorem equivRealProd_apply_le'
  given: (z : Complex)
  statement: ‖equivRealProd z‖ <= 1 * ‖z‖
  proof: by
  simpa using equivRealProd_apply_le z

中文:
定理 equivRealProd_apply_le'
  条件: (z : Complex)
  结论: ‖equiv实数Prod z‖ <= 1 * ‖z‖
  证明: by
  simpa using equivRealProd_apply_le z

Depends on / 依赖: equivRealProd_apply_le
-/
theorem equivRealProd_apply_le' (z : Complex) : ‖equivRealProd z‖ <= 1 * ‖z‖ := by
  simpa using equivRealProd_apply_le z

/--
theorem `lipschitz_equivRealProd` / 定理 `lipschitz_equivRealProd`

English:
theorem lipschitz_equivRealProd
  statement: LipschitzWith 1 equivRealProd
  proof: by
  simpa using! AddMonoidHomClass.lipschitz_of_bound equivRealProdLm 1 equivRealProd_apply_le'

中文:
定理 lipschitz_equivRealProd
  结论: LipschitzWith 1 equiv实数Prod
  证明: by
  simpa using! AddMonoidHomClass.lipschitz_of_bound equivRealProdLm 1 equivRealProd_apply_le'

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.lipschitz_of_bound, equivRealProdLm, equivRealProd_apply_le, lipschitz_of_bound
-/
theorem lipschitz_equivRealProd : LipschitzWith 1 equivRealProd := by
  simpa using! AddMonoidHomClass.lipschitz_of_bound equivRealProdLm 1 equivRealProd_apply_le'

/--
theorem `antilipschitz_equivRealProd` / 定理 `antilipschitz_equivRealProd`

English:
theorem antilipschitz_equivRealProd
  statement: AntilipschitzWith (NNReal.sqrt 2) equivRealProd
  proof: AddMonoidHomClass.antilipschitz_of_bound equivRealProdLm fun z => by
    simpa only [Real.coe_sqrt, NNReal.coe_ofNat] using! norm_le_sqrt_two_mul_max z

@[fun_prop]

中文:
定理 antilipschitz_equivRealProd
  结论: AntilipschitzWith (NN实数.sqrt 2) equiv实数Prod
  证明: AddMonoidHomClass.antilipschitz_of_bound equivRealProdLm fun z => by
    simpa only [Real.coe_sqrt, NNReal.coe_ofNat] using! norm_le_sqrt_two_mul_max z

@[fun_prop]

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.antilipschitz_of_bound, NNReal, NNReal.coe_ofNat, Real.coe_sqrt, antilipschitz_of_bound, coe_ofNat, coe_sqrt, equivRealProdLm, norm_le_sqrt_two_mul_max
-/
theorem antilipschitz_equivRealProd : AntilipschitzWith (NNReal.sqrt 2) equivRealProd :=
  AddMonoidHomClass.antilipschitz_of_bound equivRealProdLm fun z => by
    simpa only [Real.coe_sqrt, NNReal.coe_ofNat] using! norm_le_sqrt_two_mul_max z

@[fun_prop]
/--
theorem `isUniformEmbedding_equivRealProd` / 定理 `isUniformEmbedding_equivRealProd`

English:
theorem isUniformEmbedding_equivRealProd
  statement: IsUniformEmbedding equivRealProd
  proof: antilipschitz_equivRealProd.isUniformEmbedding lipschitz_equivRealProd.uniformContinuous

中文:
定理 isUniformEmbedding_equivRealProd
  结论: IsUniformEmbedding equiv实数Prod
  证明: antilipschitz_equivRealProd.isUniformEmbedding lipschitz_equivRealProd.uniformContinuous

Depends on / 依赖: antilipschitz_equivRealProd, antilipschitz_equivRealProd.isUniformEmbedding, isUniformEmbedding, lipschitz_equivRealProd, lipschitz_equivRealProd.uniformContinuous, uniformContinuous
-/
theorem isUniformEmbedding_equivRealProd : IsUniformEmbedding equivRealProd :=
  antilipschitz_equivRealProd.isUniformEmbedding lipschitz_equivRealProd.uniformContinuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSpace Complex
  body: (completeSpace_congr isUniformEmbedding_equivRealProd).mpr inferInstance

中文:
实例 :
  签名: CompleteSpace Complex
  定义体: (completeSpace_congr isUniformEmbedding_equivRealProd).mpr inferInstance

Depends on / 依赖: completeSpace_congr, isUniformEmbedding_equivRealProd
-/
instance : CompleteSpace Complex :=
  (completeSpace_congr isUniformEmbedding_equivRealProd).mpr inferInstance

/--
Instance `instT2Space` / 实例 `instT2Space`

English:
instance instT2Space
  signature: : T2Space Complex
  body: TopologicalSpace.t2Space_of_metrizableSpace

中文:
实例 instT2Space
  签名: : T2Space Complex
  定义体: TopologicalSpace.t2Space_of_metrizableSpace

Depends on / 依赖: TopologicalSpace, TopologicalSpace.t2Space_of_metrizableSpace, t2Space_of_metrizableSpace
-/
instance instT2Space : T2Space Complex := TopologicalSpace.t2Space_of_metrizableSpace

/-- The natural `ContinuousLinearEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
/--
Definition of `equivRealProdCLM` / `equivRealProdCLM` 的定义

English:
definition equivRealProdCLM
  signature: : Complex ≃L[Real] Real × Real
  body: equivRealProdLm.toContinuousLinearEquivOfBounds 1 (√2) equivRealProd_apply_le' fun p =>
    norm_le_sqrt_two_mul_max (equivRealProd.symm p)

中文:
定义 equivRealProdCLM
  签名: : Complex ≃L[实数] 实数 × 实数
  定义体: equivRealProdLm.toContinuousLinearEquivOfBounds 1 (√2) equivRealProd_apply_le' fun p =>
    norm_le_sqrt_two_mul_max (equivRealProd.symm p)

Depends on / 依赖: equivRealProd, equivRealProd.symm, equivRealProdLm, equivRealProdLm.toContinuousLinearEquivOfBounds, equivRealProd_apply_le, norm_le_sqrt_two_mul_max, toContinuousLinearEquivOfBounds
-/
def equivRealProdCLM : Complex ≃L[Real] Real × Real :=
  equivRealProdLm.toContinuousLinearEquivOfBounds 1 (√2) equivRealProd_apply_le' fun p =>
    norm_le_sqrt_two_mul_max (equivRealProd.symm p)

/--
theorem `equivRealProdCLM_symm_apply` / 定理 `equivRealProdCLM_symm_apply`

English:
theorem equivRealProdCLM_symm_apply
  given: (p : Real × Real)
  proof: Complex.equivRealProd_symm_apply p

中文:
定理 equivRealProdCLM_symm_apply
  条件: (p : 实数 × 实数)
  证明: Complex.equivRealProd_symm_apply p

Depends on / 依赖: Complex.equivRealProd_symm_apply, equivRealProd_symm_apply
-/
theorem equivRealProdCLM_symm_apply (p : Real × Real) :
    Complex.equivRealProdCLM.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ProperSpace Complex
  body: lipschitz_equivRealProd.properSpace
  equivRealProdCLM.toHomeomorph.isProperMap

中文:
实例 :
  签名: 命题erSpace Complex
  定义体: lipschitz_equivRealProd.properSpace
  equivRealProdCLM.toHomeomorph.isProperMap

Depends on / 依赖: lipschitz_equivRealProd, lipschitz_equivRealProd.properSpace, properSpace
-/
instance : ProperSpace Complex := lipschitz_equivRealProd.properSpace
  equivRealProdCLM.toHomeomorph.isProperMap

/--
theorem `tendsto_normSq_cocompact_atTop` / 定理 `tendsto_normSq_cocompact_atTop`

English:
theorem tendsto_normSq_cocompact_atTop
  statement: Tendsto normSq (cocompact Complex) atTop
  proof: by
  simpa [norm_mul_self_eq_normSq]
    using tendsto_norm_cocompact_atTop.atTop_mul_atTop₀ (tendsto_norm_cocompact_atTop (E := Complex))

中文:
定理 tendsto_normSq_cocompact_atTop
  结论: Tendsto normSq (cocompact Complex) atTop
  证明: by
  simpa [norm_mul_self_eq_normSq]
    using tendsto_norm_cocompact_atTop.atTop_mul_atTop₀ (tendsto_norm_cocompact_atTop (E := Complex))

Depends on / 依赖: norm_mul_self_eq_normSq, tendsto_norm_cocompact_atTop, tendsto_norm_cocompact_atTop.atTop_mul_atTop
-/
theorem tendsto_normSq_cocompact_atTop : Tendsto normSq (cocompact Complex) atTop := by
  simpa [norm_mul_self_eq_normSq]
    using tendsto_norm_cocompact_atTop.atTop_mul_atTop₀ (tendsto_norm_cocompact_atTop (E := Complex))

open ContinuousLinearMap

/--
Definition of `reCLM` / `reCLM` 的定义

English:
definition reCLM
  signature: : Complex ->L[Real] Real
  body: reLm.mkContinuous 1 fun x => by simp [abs_re_le_norm]

@[continuity, fun_prop]

中文:
定义 reCLM
  签名: : Complex ->L[实数] 实数
  定义体: reLm.mkContinuous 1 fun x => by simp [abs_re_le_norm]

@[continuity, fun_prop]

Depends on / 依赖: abs_re_le_norm, mkContinuous, reLm.mkContinuous
-/
def reCLM : Complex ->L[Real] Real :=
  reLm.mkContinuous 1 fun x => by simp [abs_re_le_norm]

@[continuity, fun_prop]
/--
theorem `continuous_re` / 定理 `continuous_re`

English:
theorem continuous_re
  statement: Continuous re
  proof: reCLM.continuous

@[fun_prop]

中文:
定理 continuous_re
  结论: Continuous re
  证明: reCLM.continuous

@[fun_prop]

Depends on / 依赖: continuous, reCLM.continuous
-/
theorem continuous_re : Continuous re :=
  reCLM.continuous

@[fun_prop]
/--
lemma `uniformContinuous_re` / 引理 `uniformContinuous_re`

English:
lemma uniformContinuous_re
  statement: UniformContinuous re
  proof: reCLM.uniformContinuous

@[deprecated (since := "2026-02-03")] alias uniformlyContinuous_re :=
  uniformContinuous_re

@[simp]

中文:
引理 uniformContinuous_re
  结论: UniformContinuous re
  证明: reCLM.uniformContinuous

@[deprecated (since := "2026-02-03")] alias uniformlyContinuous_re :=
  uniformContinuous_re

@[simp]

Depends on / 依赖: reCLM.uniformContinuous, uniformContinuous
-/
lemma uniformContinuous_re : UniformContinuous re :=
  reCLM.uniformContinuous

@[deprecated (since := "2026-02-03")] alias uniformlyContinuous_re :=
  uniformContinuous_re

@[simp]
/--
theorem `reCLM_coe` / 定理 `reCLM_coe`

English:
theorem reCLM_coe
  statement: (reCLM : Complex ->ₗ[Real] Real) = reLm
  proof: rfl

@[simp]

中文:
定理 reCLM_coe
  结论: (reCLM : Complex ->ₗ[实数] 实数) = reLm
  证明: rfl

@[simp]
-/
theorem reCLM_coe : (reCLM : Complex ->ₗ[Real] Real) = reLm :=
  rfl

@[simp]
/--
theorem `reCLM_apply` / 定理 `reCLM_apply`

English:
theorem reCLM_apply
  given: (z : Complex)
  statement: (reCLM : Complex -> Real) z = z.re
  proof: rfl

中文:
定理 reCLM_apply
  条件: (z : Complex)
  结论: (reCLM : Complex -> 实数) z = z.re
  证明: rfl
-/
theorem reCLM_apply (z : Complex) : (reCLM : Complex -> Real) z = z.re :=
  rfl

/--
Definition of `imCLM` / `imCLM` 的定义

English:
definition imCLM
  signature: : Complex ->L[Real] Real
  body: imLm.mkContinuous 1 fun x => by simp [abs_im_le_norm]

@[continuity, fun_prop]

中文:
定义 imCLM
  签名: : Complex ->L[实数] 实数
  定义体: imLm.mkContinuous 1 fun x => by simp [abs_im_le_norm]

@[continuity, fun_prop]

Depends on / 依赖: abs_im_le_norm, imLm.mkContinuous, mkContinuous
-/
def imCLM : Complex ->L[Real] Real :=
  imLm.mkContinuous 1 fun x => by simp [abs_im_le_norm]

@[continuity, fun_prop]
/--
theorem `continuous_im` / 定理 `continuous_im`

English:
theorem continuous_im
  statement: Continuous im
  proof: imCLM.continuous

@[fun_prop]

中文:
定理 continuous_im
  结论: Continuous im
  证明: imCLM.continuous

@[fun_prop]

Depends on / 依赖: continuous, imCLM.continuous
-/
theorem continuous_im : Continuous im :=
  imCLM.continuous

@[fun_prop]
/--
lemma `uniformContinuous_im` / 引理 `uniformContinuous_im`

English:
lemma uniformContinuous_im
  statement: UniformContinuous im
  proof: imCLM.uniformContinuous

@[deprecated (since := "2026-02-03")] alias uniformlyContinuous_im :=
  uniformContinuous_im

@[simp]

中文:
引理 uniformContinuous_im
  结论: UniformContinuous im
  证明: imCLM.uniformContinuous

@[deprecated (since := "2026-02-03")] alias uniformlyContinuous_im :=
  uniformContinuous_im

@[simp]

Depends on / 依赖: imCLM.uniformContinuous, uniformContinuous
-/
lemma uniformContinuous_im : UniformContinuous im :=
  imCLM.uniformContinuous

@[deprecated (since := "2026-02-03")] alias uniformlyContinuous_im :=
  uniformContinuous_im

@[simp]
/--
theorem `imCLM_coe` / 定理 `imCLM_coe`

English:
theorem imCLM_coe
  statement: (imCLM : Complex ->ₗ[Real] Real) = imLm
  proof: rfl

@[simp]

中文:
定理 imCLM_coe
  结论: (imCLM : Complex ->ₗ[实数] 实数) = imLm
  证明: rfl

@[simp]
-/
theorem imCLM_coe : (imCLM : Complex ->ₗ[Real] Real) = imLm :=
  rfl

@[simp]
/--
theorem `imCLM_apply` / 定理 `imCLM_apply`

English:
theorem imCLM_apply
  given: (z : Complex)
  statement: (imCLM : Complex -> Real) z = z.im
  proof: rfl

中文:
定理 imCLM_apply
  条件: (z : Complex)
  结论: (imCLM : Complex -> 实数) z = z.im
  证明: rfl
-/
theorem imCLM_apply (z : Complex) : (imCLM : Complex -> Real) z = z.im :=
  rfl

/--
theorem `restrictScalars_toSpanSingleton'` / 定理 `restrictScalars_toSpanSingleton'`

English:
theorem restrictScalars_toSpanSingleton'
  given: (x : E)
  proof: by
  ext ⟨a, b⟩
  simp [map_add, mk_eq_add_mul_I, mul_smul, smul_comm I b x]

中文:
定理 restrictScalars_toSpanSingleton'
  条件: (x : E)
  证明: by
  ext ⟨a, b⟩
  simp [map_add, mk_eq_add_mul_I, mul_smul, smul_comm I b x]

Depends on / 依赖: map_add, mk_eq_add_mul_I, mul_smul, smul_comm
-/
theorem restrictScalars_toSpanSingleton' (x : E) :
    ContinuousLinearMap.restrictScalars Real (toSpanSingleton Complex x : Complex ->L[Complex] E) =
      reCLM.smulRight x + I • imCLM.smulRight x := by
  ext ⟨a, b⟩
  simp [map_add, mk_eq_add_mul_I, mul_smul, smul_comm I b x]

/--
theorem `restrictScalars_toSpanSingleton` / 定理 `restrictScalars_toSpanSingleton`

English:
theorem restrictScalars_toSpanSingleton
  given: (x : Complex)
  proof: by
  ext1 z
  dsimp
  apply mul_comm

中文:
定理 restrictScalars_toSpanSingleton
  条件: (x : Complex)
  证明: by
  ext1 z
  dsimp
  apply mul_comm

Depends on / 依赖: mul_comm
-/
theorem restrictScalars_toSpanSingleton (x : Complex) :
    ContinuousLinearMap.restrictScalars Real (toSpanSingleton Complex x : Complex ->L[Complex] Complex) =
    x • (1 : Complex ->L[Real] Complex) := by
  ext1 z
  dsimp
  apply mul_comm

/--
Definition of `conjLIE` / `conjLIE` 的定义

English:
definition conjLIE
  signature: : Complex ≃ₗᵢ[Real] Complex
  body: ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp]

中文:
定义 conjLIE
  签名: : Complex ≃ₗᵢ[实数] Complex
  定义体: ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp]

Depends on / 依赖: conjAe, conjAe.toLinearEquiv, norm_conj, toLinearEquiv
-/
def conjLIE : Complex ≃ₗᵢ[Real] Complex :=
  ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp]
/--
theorem `conjLIE_apply` / 定理 `conjLIE_apply`

English:
theorem conjLIE_apply
  given: (z : Complex)
  statement: conjLIE z = conj z
  proof: rfl

@[simp]

中文:
定理 conjLIE_apply
  条件: (z : Complex)
  结论: conjLIE z = conj z
  证明: rfl

@[simp]
-/
theorem conjLIE_apply (z : Complex) : conjLIE z = conj z :=
  rfl

@[simp]
/--
theorem `conjLIE_symm` / 定理 `conjLIE_symm`

English:
theorem conjLIE_symm
  statement: conjLIE.symm = conjLIE
  proof: rfl

中文:
定理 conjLIE_symm
  结论: conjLIE.symm = conjLIE
  证明: rfl
-/
theorem conjLIE_symm : conjLIE.symm = conjLIE :=
  rfl

/--
theorem `isometry_conj` / 定理 `isometry_conj`

English:
theorem isometry_conj
  statement: Isometry (conj : Complex -> Complex)
  proof: conjLIE.isometry

@[simp]

中文:
定理 isometry_conj
  结论: Isometry (conj : Complex -> Complex)
  证明: conjLIE.isometry

@[simp]

Depends on / 依赖: conjLIE, conjLIE.isometry, isometry
-/
theorem isometry_conj : Isometry (conj : Complex -> Complex) :=
  conjLIE.isometry

@[simp]
/--
theorem `dist_conj_conj` / 定理 `dist_conj_conj`

English:
theorem dist_conj_conj
  given: (z w : Complex)
  statement: dist (conj z) (conj w) = dist z w
  proof: isometry_conj.dist_eq z w

@[simp]

中文:
定理 dist_conj_conj
  条件: (z w : Complex)
  结论: dist (conj z) (conj w) = dist z w
  证明: isometry_conj.dist_eq z w

@[simp]

Depends on / 依赖: dist_eq, isometry_conj, isometry_conj.dist_eq
-/
theorem dist_conj_conj (z w : Complex) : dist (conj z) (conj w) = dist z w :=
  isometry_conj.dist_eq z w

@[simp]
/--
theorem `nndist_conj_conj` / 定理 `nndist_conj_conj`

English:
theorem nndist_conj_conj
  given: (z w : Complex)
  statement: nndist (conj z) (conj w) = nndist z w
  proof: isometry_conj.nndist_eq z w

中文:
定理 nndist_conj_conj
  条件: (z w : Complex)
  结论: nndist (conj z) (conj w) = nndist z w
  证明: isometry_conj.nndist_eq z w

Depends on / 依赖: isometry_conj, isometry_conj.nndist_eq, nndist_eq
-/
theorem nndist_conj_conj (z w : Complex) : nndist (conj z) (conj w) = nndist z w :=
  isometry_conj.nndist_eq z w

/--
theorem `dist_conj_comm` / 定理 `dist_conj_comm`

English:
theorem dist_conj_comm
  given: (z w : Complex)
  statement: dist (conj z) w = dist z (conj w)
  proof: by
  rw [← dist_conj_conj]; rw [conj_conj]

中文:
定理 dist_conj_comm
  条件: (z w : Complex)
  结论: dist (conj z) w = dist z (conj w)
  证明: by
  rw [← dist_conj_conj]; rw [conj_conj]

Depends on / 依赖: conj_conj, dist_conj_conj
-/
theorem dist_conj_comm (z w : Complex) : dist (conj z) w = dist z (conj w) := by
  rw [← dist_conj_conj]; rw [conj_conj]

/--
theorem `nndist_conj_comm` / 定理 `nndist_conj_comm`

English:
theorem nndist_conj_comm
  given: (z w : Complex)
  statement: nndist (conj z) w = nndist z (conj w)
  proof: Subtype.ext dist_conj_comm _ _

中文:
定理 nndist_conj_comm
  条件: (z w : Complex)
  结论: nndist (conj z) w = nndist z (conj w)
  证明: Subtype.ext dist_conj_comm _ _

Depends on / 依赖: Subtype, Subtype.ext, dist_conj_comm
-/
theorem nndist_conj_comm (z w : Complex) : nndist (conj z) w = nndist z (conj w) :=
Subtype.ext dist_conj_comm _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousStar Complex
  body: ⟨conjLIE.continuous⟩

@[continuity, fun_prop]

中文:
实例 :
  签名: ContinuousStar Complex
  定义体: ⟨conjLIE.continuous⟩

@[continuity, fun_prop]

Depends on / 依赖: conjLIE, conjLIE.continuous, continuous
-/
instance : ContinuousStar Complex :=
  ⟨conjLIE.continuous⟩

@[continuity, fun_prop]
/--
theorem `continuous_conj` / 定理 `continuous_conj`

English:
theorem continuous_conj
  statement: Continuous (conj : Complex -> Complex)
  proof: continuous_star

中文:
定理 continuous_conj
  结论: Continuous (conj : Complex -> Complex)
  证明: continuous_star

Depends on / 依赖: continuous_star
-/
theorem continuous_conj : Continuous (conj : Complex -> Complex) :=
  continuous_star

/--
theorem `ringHom_eq_id_or_conj_of_continuous` / 定理 `ringHom_eq_id_or_conj_of_continuous`

English:
theorem ringHom_eq_id_or_conj_of_continuous
  given: {f : Complex ->+* Complex} (hf : Continuous f)
  proof: by
  simpa only [DFunLike.ext_iff] using! real_algHom_eq_id_or_conj (AlgHom.mk' f (map_real_smul f hf))

中文:
定理 ringHom_eq_id_or_conj_of_continuous
  条件: {f : Complex ->+* Complex} (hf : Continuous f)
  证明: by
  simpa only [DFunLike.ext_iff] using! real_algHom_eq_id_or_conj (AlgHom.mk' f (map_real_smul f hf))

Depends on / 依赖: AlgHom, AlgHom.mk, DFunLike, DFunLike.ext_iff, ext_iff, map_real_smul, real_algHom_eq_id_or_conj
-/
theorem ringHom_eq_id_or_conj_of_continuous {f : Complex ->+* Complex} (hf : Continuous f) :
    f = RingHom.id Complex ∨ f = conj := by
  simpa only [DFunLike.ext_iff] using! real_algHom_eq_id_or_conj (AlgHom.mk' f (map_real_smul f hf))

/--
Definition of `conjCAE` / `conjCAE` 的定义

English:
definition conjCAE
  signature: : Complex ≃A[Real] Complex
  body: { conjAe, conjLIE.toContinuousLinearEquiv with }

中文:
定义 conjCAE
  签名: : Complex ≃A[实数] Complex
  定义体: { conjAe, conjLIE.toContinuousLinearEquiv with }

Depends on / 依赖: conjAe, conjLIE, conjLIE.toContinuousLinearEquiv, toContinuousLinearEquiv
-/
def conjCAE : Complex ≃A[Real] Complex := { conjAe, conjLIE.toContinuousLinearEquiv with }

/--
Definition of `conjCLE` / `conjCLE` 的定义

English:
abbreviation conjCLE
  signature: : Complex ≃L[Real] Complex
  body: conjCAE.toContinuousLinearEquiv

中文:
缩写 conjCLE
  签名: : Complex ≃L[实数] Complex
  定义体: conjCAE.toContinuousLinearEquiv

Depends on / 依赖: conjCAE, conjCAE.toContinuousLinearEquiv, toContinuousLinearEquiv
-/
abbrev conjCLE : Complex ≃L[Real] Complex := conjCAE.toContinuousLinearEquiv

/--
lemma `conjLIE_toCLE` / 引理 `conjLIE_toCLE`

English:
lemma conjLIE_toCLE
  statement: conjLIE.toContinuousLinearEquiv = conjCLE
  proof: rfl

@[simp]

中文:
引理 conjLIE_toCLE
  结论: conjLIE.toContinuousLinearEquiv = conjCLE
  证明: rfl

@[simp]
-/
@[simp] lemma conjLIE_toCLE : conjLIE.toContinuousLinearEquiv = conjCLE := rfl

@[simp]
/--
theorem `conjCAE_toAlgEquiv` / 定理 `conjCAE_toAlgEquiv`

English:
theorem conjCAE_toAlgEquiv
  statement: conjCAE.toAlgEquiv = conjAe
  proof: rfl

中文:
定理 conjCAE_toAlgEquiv
  结论: conjCAE.toAlgEquiv = conjAe
  证明: rfl
-/
theorem conjCAE_toAlgEquiv : conjCAE.toAlgEquiv = conjAe :=
  rfl

/--
theorem `conjCLE_toLinearEquiv` / 定理 `conjCLE_toLinearEquiv`

English:
theorem conjCLE_toLinearEquiv
  statement: conjCLE.toLinearEquiv = conjAe.toLinearEquiv
  proof: rfl

@[deprecated "Now provable by simp" (since := "2026-04-13")]

中文:
定理 conjCLE_toLinearEquiv
  结论: conjCLE.toLinearEquiv = conjAe.toLinearEquiv
  证明: rfl

@[deprecated "Now provable by simp" (since := "2026-04-13")]
-/
@[simp] theorem conjCLE_toLinearEquiv : conjCLE.toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[deprecated "Now provable by simp" (since := "2026-04-13")]
/--
lemma `conjCLE_coe_toLinearMap` / 引理 `conjCLE_coe_toLinearMap`

English:
lemma conjCLE_coe_toLinearMap
  statement: (conjCLE : Complex ->ₗ[Real] Complex) = conjAe.toLinearMap
  proof: by simp

@[simp]

中文:
引理 conjCLE_coe_toLinearMap
  结论: (conjCLE : Complex ->ₗ[实数] Complex) = conjAe.toLinearMap
  证明: by simp

@[simp]
-/
lemma conjCLE_coe_toLinearMap : (conjCLE : Complex ->ₗ[Real] Complex) = conjAe.toLinearMap := by simp

@[simp]
/--
theorem `conjCAE_apply` / 定理 `conjCAE_apply`

English:
theorem conjCAE_apply
  given: (z : Complex)
  statement: conjCAE z = conj z
  proof: rfl

中文:
定理 conjCAE_apply
  条件: (z : Complex)
  结论: conjCAE z = conj z
  证明: rfl
-/
theorem conjCAE_apply (z : Complex) : conjCAE z = conj z :=
  rfl

-- simp tag not needed because conjCLE is `abbrev`
/--
theorem `conjCLE_apply` / 定理 `conjCLE_apply`

English:
theorem conjCLE_apply
  given: (z : Complex)
  statement: conjCLE z = conj z
  proof: rfl

中文:
定理 conjCLE_apply
  条件: (z : Complex)
  结论: conjCLE z = conj z
  证明: rfl
-/
theorem conjCLE_apply (z : Complex) : conjCLE z = conj z :=
  rfl

/--
lemma `conjCAE_toLinearMap` / 引理 `conjCAE_toLinearMap`

English:
lemma conjCAE_toLinearMap
  statement: conjCAE.toLinearMap = conjAe.toLinearMap
  proof: rfl

中文:
引理 conjCAE_toLinearMap
  结论: conjCAE.toLinearMap = conjAe.toLinearMap
  证明: rfl
-/
@[simp] lemma conjCAE_toLinearMap : conjCAE.toLinearMap = conjAe.toLinearMap := rfl

/--
Definition of `ofRealLI` / `ofRealLI` 的定义

English:
definition ofRealLI
  signature: : Real ->ₗᵢ[Real] Complex
  body: ⟨ofRealAm.toLinearMap, norm_real⟩

@[simp]

中文:
定义 ofRealLI
  签名: : 实数 ->ₗᵢ[实数] Complex
  定义体: ⟨ofRealAm.toLinearMap, norm_real⟩

@[simp]

Depends on / 依赖: norm_real, ofRealAm, ofRealAm.toLinearMap, toLinearMap
-/
def ofRealLI : Real ->ₗᵢ[Real] Complex :=
  ⟨ofRealAm.toLinearMap, norm_real⟩

@[simp]
/--
theorem `ofRealLI_apply` / 定理 `ofRealLI_apply`

English:
theorem ofRealLI_apply
  given: (x : Real)
  statement: ofRealLI x = x
  proof: rfl

中文:
定理 ofRealLI_apply
  条件: (x : 实数)
  结论: of实数LI x = x
  证明: rfl
-/
theorem ofRealLI_apply (x : Real) : ofRealLI x = x := rfl

/--
theorem `isometry_ofReal` / 定理 `isometry_ofReal`

English:
theorem isometry_ofReal
  statement: Isometry ((↑) : Real -> Complex)
  proof: ofRealLI.isometry

@[continuity, fun_prop]

中文:
定理 isometry_ofReal
  结论: Isometry ((↑) : 实数 -> Complex)
  证明: ofRealLI.isometry

@[continuity, fun_prop]

Depends on / 依赖: isometry, ofRealLI, ofRealLI.isometry
-/
theorem isometry_ofReal : Isometry ((↑) : Real -> Complex) :=
  ofRealLI.isometry

@[continuity, fun_prop]
/--
theorem `continuous_ofReal` / 定理 `continuous_ofReal`

English:
theorem continuous_ofReal
  statement: Continuous ((↑) : Real -> Complex)
  proof: ofRealLI.continuous

中文:
定理 continuous_ofReal
  结论: Continuous ((↑) : 实数 -> Complex)
  证明: ofRealLI.continuous

Depends on / 依赖: continuous, ofRealLI, ofRealLI.continuous
-/
theorem continuous_ofReal : Continuous ((↑) : Real -> Complex) :=
  ofRealLI.continuous

/--
theorem `isUniformEmbedding_ofReal` / 定理 `isUniformEmbedding_ofReal`

English:
theorem isUniformEmbedding_ofReal
  statement: IsUniformEmbedding ((↑) : Real -> Complex)
  proof: ofRealLI.isometry.isUniformEmbedding

中文:
定理 isUniformEmbedding_ofReal
  结论: IsUniformEmbedding ((↑) : 实数 -> Complex)
  证明: ofRealLI.isometry.isUniformEmbedding

Depends on / 依赖: isUniformEmbedding, isometry, ofRealLI, ofRealLI.isometry.isUniformEmbedding
-/
theorem isUniformEmbedding_ofReal : IsUniformEmbedding ((↑) : Real -> Complex) :=
  ofRealLI.isometry.isUniformEmbedding

/--
lemma `_root_.RCLike.isUniformEmbedding_ofReal` / 引理 `_root_.RCLike.isUniformEmbedding_ofReal`

English:
lemma _root_.RCLike.isUniformEmbedding_ofReal
  given: {𝕜 : Type*} [RCLike 𝕜]
  proof: RCLike.ofRealLI.isometry.isUniformEmbedding

中文:
引理 _root_.RCLike.isUniformEmbedding_ofReal
  条件: {𝕜 : 类型} [RCLike 𝕜]
  证明: RCLike.ofRealLI.isometry.isUniformEmbedding

Depends on / 依赖: RCLike, RCLike.ofRealLI.isometry.isUniformEmbedding, isUniformEmbedding, isometry, ofRealLI
-/
lemma _root_.RCLike.isUniformEmbedding_ofReal {𝕜 : Type*} [RCLike 𝕜] :
    IsUniformEmbedding ((↑) : Real -> 𝕜) :=
  RCLike.ofRealLI.isometry.isUniformEmbedding

/--
theorem `_root_.Filter.tendsto_ofReal_iff` / 定理 `_root_.Filter.tendsto_ofReal_iff`

English:
theorem _root_.Filter.tendsto_ofReal_iff
  given: {α : Type*} {l : Filter α} {f : α -> Real} {x : Real}
  proof: isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm

中文:
定理 _root_.Filter.tendsto_ofReal_iff
  条件: {α : 类型} {l : Filter α} {f : α -> 实数} {x : 实数}
  证明: isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm

Depends on / 依赖: isClosedEmbedding, isUniformEmbedding_ofReal, isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm, tendsto_nhds_iff
-/
theorem _root_.Filter.tendsto_ofReal_iff {α : Type*} {l : Filter α} {f : α -> Real} {x : Real} :
    Tendsto (fun x => (f x : Complex)) l (𝓝 (x : Complex)) ↔ Tendsto f l (𝓝 x) :=
  isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm

/--
lemma `_root_.Filter.tendsto_ofReal_iff'` / 引理 `_root_.Filter.tendsto_ofReal_iff'`

English:
lemma _root_.Filter.tendsto_ofReal_iff'
  statement: {α 𝕜 : Type*} [RCLike 𝕜]
  proof: RCLike.isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm

中文:
引理 _root_.Filter.tendsto_ofReal_iff'
  结论: {α 𝕜 : 类型} [RCLike 𝕜]
  证明: RCLike.isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm

Depends on / 依赖: RCLike, RCLike.isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm, isClosedEmbedding, isUniformEmbedding_ofReal, tendsto_nhds_iff
-/
lemma _root_.Filter.tendsto_ofReal_iff' {α 𝕜 : Type*} [RCLike 𝕜]
    {l : Filter α} {f : α -> Real} {x : Real} :
    Tendsto (fun x => (f x : 𝕜)) l (𝓝 (x : 𝕜)) ↔ Tendsto f l (𝓝 x) :=
  RCLike.isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_nhds_iff.symm

/--
lemma `_root_.Filter.Tendsto.ofReal` / 引理 `_root_.Filter.Tendsto.ofReal`

English:
lemma _root_.Filter.Tendsto.ofReal
  statement: {α : Type*} {l : Filter α} {f : α -> Real} {x : Real}
  proof: tendsto_ofReal_iff.mpr hf

中文:
引理 _root_.Filter.Tendsto.ofReal
  结论: {α : 类型} {l : Filter α} {f : α -> 实数} {x : 实数}
  证明: tendsto_ofReal_iff.mpr hf

Depends on / 依赖: tendsto_ofReal_iff, tendsto_ofReal_iff.mpr
-/
lemma _root_.Filter.Tendsto.ofReal {α : Type*} {l : Filter α} {f : α -> Real} {x : Real}
    (hf : Tendsto f l (𝓝 x)) : Tendsto (fun x => (f x : Complex)) l (𝓝 (x : Complex)) :=
  tendsto_ofReal_iff.mpr hf

/--
theorem `ringHom_eq_ofReal_of_continuous` / 定理 `ringHom_eq_ofReal_of_continuous`

English:
theorem ringHom_eq_ofReal_of_continuous
  given: {f : Real ->+* Complex} (h : Continuous f)
  statement: f = ofRealHom
  proof: by
  convert!
congr_arg AlgHom.toRingHom
      Subsingleton.elim (AlgHom.mk' f <| map_real_smul f h) (Algebra.ofId Real Complex)

中文:
定理 ringHom_eq_ofReal_of_continuous
  条件: {f : 实数 ->+* Complex} (h : Continuous f)
  结论: f = of实数Hom
  证明: by
  convert!
congr_arg AlgHom.toRingHom
      Subsingleton.elim (AlgHom.mk' f <| map_real_smul f h) (Algebra.ofId Real Complex)

Depends on / 依赖: AlgHom, AlgHom.mk, AlgHom.toRingHom, Algebra, Algebra.ofId, Subsingleton, Subsingleton.elim, congr_arg, convert, map_real_smul, toRingHom
-/
theorem ringHom_eq_ofReal_of_continuous {f : Real ->+* Complex} (h : Continuous f) : f = ofRealHom := by
  convert!
congr_arg AlgHom.toRingHom
      Subsingleton.elim (AlgHom.mk' f <| map_real_smul f h) (Algebra.ofId Real Complex)

/--
Definition of `ofRealCLM` / `ofRealCLM` 的定义

English:
definition ofRealCLM
  signature: : Real ->L[Real] Complex
  body: ofRealLI.toContinuousLinearMap

@[simp]

中文:
定义 ofRealCLM
  签名: : 实数 ->L[实数] Complex
  定义体: ofRealLI.toContinuousLinearMap

@[simp]

Depends on / 依赖: ofRealLI, ofRealLI.toContinuousLinearMap, toContinuousLinearMap
-/
def ofRealCLM : Real ->L[Real] Complex :=
  ofRealLI.toContinuousLinearMap

@[simp]
/--
theorem `ofRealCLM_coe` / 定理 `ofRealCLM_coe`

English:
theorem ofRealCLM_coe
  statement: (ofRealCLM : Real ->ₗ[Real] Complex) = ofRealAm.toLinearMap
  proof: rfl

@[simp]

中文:
定理 ofRealCLM_coe
  结论: (of实数CLM : 实数 ->ₗ[实数] Complex) = of实数Am.toLinearMap
  证明: rfl

@[simp]
-/
theorem ofRealCLM_coe : (ofRealCLM : Real ->ₗ[Real] Complex) = ofRealAm.toLinearMap :=
  rfl

@[simp]
/--
theorem `ofRealCLM_apply` / 定理 `ofRealCLM_apply`

English:
theorem ofRealCLM_apply
  given: (x : Real)
  statement: ofRealCLM x = x
  proof: rfl

中文:
定理 ofRealCLM_apply
  条件: (x : 实数)
  结论: of实数CLM x = x
  证明: rfl
-/
theorem ofRealCLM_apply (x : Real) : ofRealCLM x = x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RCLike Complex
  body: ⟨⟨Complex.re, Complex.zero_re⟩, Complex.add_re⟩
  im := ⟨⟨Complex.im, Complex.zero_im⟩, Complex.add_im⟩
  I := Complex.I
  I_re_ax := I_re
  I_mul_I_ax := .inr Complex.I_mul_I
  re_add_im_ax := re_add_im
  ofReal_re_ax := ofReal_re
  ofReal_im_ax := ofReal_im
  mul_re_ax := mul_re
  mul_im_ax := mul

中文:
实例 :
  签名: RCLike Complex
  定义体: ⟨⟨Complex.re, Complex.zero_re⟩, Complex.add_re⟩
  im := ⟨⟨Complex.im, Complex.zero_im⟩, Complex.add_im⟩
  I := Complex.I
  I_re_ax := I_re
  I_mul_I_ax := .inr Complex.I_mul_I
  re_add_im_ax := re_add_im
  ofReal_re_ax := ofReal_re
  ofReal_im_ax := ofReal_im
  mul_re_ax := mul_re
  mul_im_ax := mul

Depends on / 依赖: Complex.add_re, Complex.re, Complex.zero_re, add_re, zero_re
-/
noncomputable instance : RCLike Complex where
  re := ⟨⟨Complex.re, Complex.zero_re⟩, Complex.add_re⟩
  im := ⟨⟨Complex.im, Complex.zero_im⟩, Complex.add_im⟩
  I := Complex.I
  I_re_ax := I_re
  I_mul_I_ax := .inr Complex.I_mul_I
  re_add_im_ax := re_add_im
  ofReal_re_ax := ofReal_re
  ofReal_im_ax := ofReal_im
  mul_re_ax := mul_re
  mul_im_ax := mul_im
  conj_re_ax _ := rfl
  conj_im_ax _ := rfl
  conj_I_ax := conj_I
  norm_sq_eq_def_ax z := (normSq_eq_norm_sq z).symm
  mul_im_I_ax _ := mul_one _
  toPartialOrder := Complex.partialOrder
  le_iff_re_im := Iff.rfl

/--
theorem `_root_.RCLike.re_eq_complex_re` / 定理 `_root_.RCLike.re_eq_complex_re`

English:
theorem _root_.RCLike.re_eq_complex_re
  statement: ⇑(RCLike.re : Complex ->+ Real) = Complex.re
  proof: rfl

中文:
定理 _root_.RCLike.re_eq_complex_re
  结论: ⇑(RCLike.re : Complex ->+ 实数) = Complex.re
  证明: rfl
-/
theorem _root_.RCLike.re_eq_complex_re : ⇑(RCLike.re : Complex ->+ Real) = Complex.re :=
  rfl

/--
theorem `_root_.RCLike.im_eq_complex_im` / 定理 `_root_.RCLike.im_eq_complex_im`

English:
theorem _root_.RCLike.im_eq_complex_im
  statement: ⇑(RCLike.im : Complex ->+ Real) = Complex.im
  proof: rfl

中文:
定理 _root_.RCLike.im_eq_complex_im
  结论: ⇑(RCLike.im : Complex ->+ 实数) = Complex.im
  证明: rfl
-/
theorem _root_.RCLike.im_eq_complex_im : ⇑(RCLike.im : Complex ->+ Real) = Complex.im :=
  rfl

/--
theorem `_root_.RCLike.ofReal_eq_complex_ofReal` / 定理 `_root_.RCLike.ofReal_eq_complex_ofReal`

English:
theorem _root_.RCLike.ofReal_eq_complex_ofReal
  statement: (RCLike.ofReal : Real -> Complex) = Complex.ofReal
  proof: rfl

中文:
定理 _root_.RCLike.ofReal_eq_complex_ofReal
  结论: (RCLike.of实数 : 实数 -> Complex) = Complex.of实数
  证明: rfl
-/
theorem _root_.RCLike.ofReal_eq_complex_ofReal : (RCLike.ofReal : Real -> Complex) = Complex.ofReal := rfl

-- TODO: Replace `mul_conj` and `conj_mul` once `norm` has replaced `abs`
/--
lemma `mul_conj'` / 引理 `mul_conj'`

English:
lemma mul_conj'
  given: (z : Complex)
  statement: z * conj z = ‖z‖ ^ 2
  proof: RCLike.mul_conj z

中文:
引理 mul_conj'
  条件: (z : Complex)
  结论: z * conj z = ‖z‖ ^ 2
  证明: RCLike.mul_conj z

Depends on / 依赖: RCLike, RCLike.mul_conj, mul_conj
-/
lemma mul_conj' (z : Complex) : z * conj z = ‖z‖ ^ 2 := RCLike.mul_conj z
/--
lemma `conj_mul'` / 引理 `conj_mul'`

English:
lemma conj_mul'
  given: (z : Complex)
  statement: conj z * z = ‖z‖ ^ 2
  proof: RCLike.conj_mul z

中文:
引理 conj_mul'
  条件: (z : Complex)
  结论: conj z * z = ‖z‖ ^ 2
  证明: RCLike.conj_mul z

Depends on / 依赖: RCLike, RCLike.conj_mul, conj_mul
-/
lemma conj_mul' (z : Complex) : conj z * z = ‖z‖ ^ 2 := RCLike.conj_mul z

/--
lemma `inv_eq_conj` / 引理 `inv_eq_conj`

English:
lemma inv_eq_conj
  given: (hz : ‖z‖ = 1)
  statement: z⁻¹ = conj z
  proof: RCLike.inv_eq_conj hz

中文:
引理 inv_eq_conj
  条件: (hz : ‖z‖ = 1)
  结论: z⁻¹ = conj z
  证明: RCLike.inv_eq_conj hz

Depends on / 依赖: RCLike, RCLike.inv_eq_conj, inv_eq_conj
-/
lemma inv_eq_conj (hz : ‖z‖ = 1) : z⁻¹ = conj z := RCLike.inv_eq_conj hz

/--
lemma `exists_norm_eq_mul_self` / 引理 `exists_norm_eq_mul_self`

English:
lemma exists_norm_eq_mul_self
  given: (z : Complex)
  statement: exists c, ‖c‖ = 1 ∧ ‖z‖ = c * z
  proof: RCLike.exists_norm_eq_mul_self _

中文:
引理 exists_norm_eq_mul_self
  条件: (z : Complex)
  结论: 存在 c, ‖c‖ = 1 ∧ ‖z‖ = c * z
  证明: RCLike.exists_norm_eq_mul_self _

Depends on / 依赖: RCLike, RCLike.exists_norm_eq_mul_self, exists_norm_eq_mul_self
-/
lemma exists_norm_eq_mul_self (z : Complex) : exists c, ‖c‖ = 1 ∧ ‖z‖ = c * z :=
  RCLike.exists_norm_eq_mul_self _

/--
lemma `exists_norm_mul_eq_self` / 引理 `exists_norm_mul_eq_self`

English:
lemma exists_norm_mul_eq_self
  given: (z : Complex)
  statement: exists c, ‖c‖ = 1 ∧ c * ‖z‖ = z
  proof: RCLike.exists_norm_mul_eq_self _

中文:
引理 exists_norm_mul_eq_self
  条件: (z : Complex)
  结论: 存在 c, ‖c‖ = 1 ∧ c * ‖z‖ = z
  证明: RCLike.exists_norm_mul_eq_self _

Depends on / 依赖: RCLike, RCLike.exists_norm_mul_eq_self, exists_norm_mul_eq_self
-/
lemma exists_norm_mul_eq_self (z : Complex) : exists c, ‖c‖ = 1 ∧ c * ‖z‖ = z :=
  RCLike.exists_norm_mul_eq_self _

/--
lemma `im_eq_zero_iff_isSelfAdjoint` / 引理 `im_eq_zero_iff_isSelfAdjoint`

English:
lemma im_eq_zero_iff_isSelfAdjoint
  given: (x : Complex)
  statement: Complex.im x = 0 ↔ IsSelfAdjoint x
  proof: by
  rw [← RCLike.im_eq_complex_im]
  exact RCLike.im_eq_zero_iff_isSelfAdjoint

中文:
引理 im_eq_zero_iff_isSelfAdjoint
  条件: (x : Complex)
  结论: Complex.im x = 0 ↔ IsSelfAdjoint x
  证明: by
  rw [← RCLike.im_eq_complex_im]
  exact RCLike.im_eq_zero_iff_isSelfAdjoint

Depends on / 依赖: RCLike, RCLike.im_eq_complex_im, RCLike.im_eq_zero_iff_isSelfAdjoint, im_eq_complex_im, im_eq_zero_iff_isSelfAdjoint
-/
lemma im_eq_zero_iff_isSelfAdjoint (x : Complex) : Complex.im x = 0 ↔ IsSelfAdjoint x := by
  rw [← RCLike.im_eq_complex_im]
  exact RCLike.im_eq_zero_iff_isSelfAdjoint

/--
lemma `re_eq_ofReal_of_isSelfAdjoint` / 引理 `re_eq_ofReal_of_isSelfAdjoint`

English:
lemma re_eq_ofReal_of_isSelfAdjoint
  given: {x : Complex} {y : Real} (hx : IsSelfAdjoint x)
  proof: by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.re_eq_ofReal_of_isSelfAdjoint hx

中文:
引理 re_eq_ofReal_of_isSelfAdjoint
  条件: {x : Complex} {y : 实数} (hx : IsSelfAdjoint x)
  证明: by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.re_eq_ofReal_of_isSelfAdjoint hx

Depends on / 依赖: RCLike, RCLike.re_eq_complex_re, RCLike.re_eq_ofReal_of_isSelfAdjoint, re_eq_complex_re, re_eq_ofReal_of_isSelfAdjoint
-/
lemma re_eq_ofReal_of_isSelfAdjoint {x : Complex} {y : Real} (hx : IsSelfAdjoint x) :
    Complex.re x = y ↔ x = y := by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.re_eq_ofReal_of_isSelfAdjoint hx

/--
lemma `ofReal_eq_re_of_isSelfAdjoint` / 引理 `ofReal_eq_re_of_isSelfAdjoint`

English:
lemma ofReal_eq_re_of_isSelfAdjoint
  given: {x : Complex} {y : Real} (hx : IsSelfAdjoint x)
  proof: by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.ofReal_eq_re_of_isSelfAdjoint hx

中文:
引理 ofReal_eq_re_of_isSelfAdjoint
  条件: {x : Complex} {y : 实数} (hx : IsSelfAdjoint x)
  证明: by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.ofReal_eq_re_of_isSelfAdjoint hx

Depends on / 依赖: RCLike, RCLike.ofReal_eq_re_of_isSelfAdjoint, RCLike.re_eq_complex_re, ofReal_eq_re_of_isSelfAdjoint, re_eq_complex_re
-/
lemma ofReal_eq_re_of_isSelfAdjoint {x : Complex} {y : Real} (hx : IsSelfAdjoint x) :
    y = Complex.re x ↔ y = x := by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.ofReal_eq_re_of_isSelfAdjoint hx

/-- The natural isomorphism between `𝕜` satisfying `RCLike 𝕜` and `ℂ` when
`RCLike.im RCLike.I = 1`. -/
@[simps]
/--
Definition of `_root_.RCLike.complexRingEquiv` / `_root_.RCLike.complexRingEquiv` 的定义

English:
definition _root_.RCLike.complexRingEquiv
  signature: {𝕜 : Type*} [RCLike 𝕜]
  body: RCLike.re x + RCLike.im x * I
  invFun x := re x + im x * RCLike.I
  left_inv x := by simp
  right_inv x := by simp [h]
  map_add' x y := by simp only [map_add, ofReal_add]; ring
  map_mul' x y := by
    simp only [RCLike.mul_re, ofReal_sub, ofReal_mul, RCLike.mul_im, ofReal_add]
    ring_nf
    rw 

中文:
定义 _root_.RCLike.complexRingEquiv
  签名: {𝕜 : 类型} [RCLike 𝕜]
  定义体: RCLike.re x + RCLike.im x * I
  invFun x := re x + im x * RCLike.I
  left_inv x := by simp
  right_inv x := by simp [h]
  map_add' x y := by simp only [map_add, ofReal_add]; ring
  map_mul' x y := by
    simp only [RCLike.mul_re, ofReal_sub, ofReal_mul, RCLike.mul_im, ofReal_add]
    ring_nf
    rw 

Depends on / 依赖: RCLike, RCLike.im, RCLike.re
-/
def _root_.RCLike.complexRingEquiv {𝕜 : Type*} [RCLike 𝕜]
    (h : RCLike.im (RCLike.I : 𝕜) = 1) : 𝕜 ≃+* Complex where
  toFun x := RCLike.re x + RCLike.im x * I
  invFun x := re x + im x * RCLike.I
  left_inv x := by simp
  right_inv x := by simp [h]
  map_add' x y := by simp only [map_add, ofReal_add]; ring
  map_mul' x y := by
    simp only [RCLike.mul_re, ofReal_sub, ofReal_mul, RCLike.mul_im, ofReal_add]
    ring_nf
    rw [I_sq]
    ring

open scoped ComplexOrder in
/--
theorem `_root_.RCLike.map_nonneg_iff` / 定理 `_root_.RCLike.map_nonneg_iff`

English:
theorem _root_.RCLike.map_nonneg_iff
  statement: {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜']
  proof: by
  rw [RCLike.nonneg_iff]; rw [RCLike.nonneg_iff (K := 𝕜)]
  simp [h]

中文:
定理 _root_.RCLike.map_nonneg_iff
  结论: {𝕜 𝕜' : 类型} [RCLike 𝕜] [RCLike 𝕜']
  证明: by
  rw [RCLike.nonneg_iff]; rw [RCLike.nonneg_iff (K := 𝕜)]
  simp [h]

Depends on / 依赖: RCLike, RCLike.nonneg_iff, nonneg_iff
-/
theorem _root_.RCLike.map_nonneg_iff {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜']
    (h : RCLike.im (RCLike.I : 𝕜') = 1) {a : 𝕜} :
    0 <= RCLike.map 𝕜 𝕜' a ↔ 0 <= a := by
  rw [RCLike.nonneg_iff]; rw [RCLike.nonneg_iff (K := 𝕜)]
  simp [h]

open scoped ComplexOrder in
/--
theorem `_root_.RCLike.to_complex_nonneg_iff` / 定理 `_root_.RCLike.to_complex_nonneg_iff`

English:
theorem _root_.RCLike.to_complex_nonneg_iff
  given: {𝕜 : Type*} [RCLike 𝕜] {a : 𝕜}
  proof: RCLike.map_nonneg_iff I_im

中文:
定理 _root_.RCLike.to_complex_nonneg_iff
  条件: {𝕜 : 类型} [RCLike 𝕜] {a : 𝕜}
  证明: RCLike.map_nonneg_iff I_im
-/
@[simp] theorem _root_.RCLike.to_complex_nonneg_iff {𝕜 : Type*} [RCLike 𝕜] {a : 𝕜} :
    0 <= RCLike.re a + RCLike.im a * Complex.I ↔ 0 <= a := RCLike.map_nonneg_iff I_im

/-- The natural `ℝ`-linear isometry equivalence between `𝕜` satisfying `RCLike 𝕜` and `ℂ` when
`RCLike.im RCLike.I = 1`. -/
@[simps]
/--
Definition of `_root_.RCLike.complexLinearIsometryEquiv` / `_root_.RCLike.complexLinearIsometryEquiv` 的定义

English:
definition _root_.RCLike.complexLinearIsometryEquiv
  signature: {𝕜 : Type*} [RCLike 𝕜]
  body: by simp [RCLike.smul_re, RCLike.smul_im, ofReal_mul]; ring
  norm_map' _ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]; rw [← normSq_eq_norm_sq]; rw [← RCLike.normSq_eq_def']; rw [RCLike.normSq_apply]
    simp [normSq_add]
  __ := RCLike.complexRingEquiv h

中文:
定义 _root_.RCLike.complexLinearIsometryEquiv
  签名: {𝕜 : 类型} [RCLike 𝕜]
  定义体: by simp [RCLike.smul_re, RCLike.smul_im, ofReal_mul]; ring
  norm_map' _ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]; rw [← normSq_eq_norm_sq]; rw [← RCLike.normSq_eq_def']; rw [RCLike.normSq_apply]
    simp [normSq_add]
  __ := RCLike.complexRingEquiv h

Depends on / 依赖: RCLike, RCLike.complexRingEquiv, RCLike.normSq_apply, RCLike.normSq_eq_def, RCLike.smul_im, RCLike.smul_re, complexRingEquiv, normSq_add, normSq_apply, normSq_eq_def, normSq_eq_norm_sq, norm_map, ofReal_mul, smul_im, smul_re
-/
def _root_.RCLike.complexLinearIsometryEquiv {𝕜 : Type*} [RCLike 𝕜]
    (h : RCLike.im (RCLike.I : 𝕜) = 1) : 𝕜 ≃ₗᵢ[Real] Complex where
  map_smul' _ _ := by simp [RCLike.smul_re, RCLike.smul_im, ofReal_mul]; ring
  norm_map' _ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]; rw [← normSq_eq_norm_sq]; rw [← RCLike.normSq_eq_def']; rw [RCLike.normSq_apply]
    simp [normSq_add]
  __ := RCLike.complexRingEquiv h

/--
theorem `_root_.RCLike.toContinuousLinearMap_complexLinearIsometryEquiv` / 定理 `_root_.RCLike.toContinuousLinearMap_complexLinearIsometryEquiv`

English:
theorem _root_.RCLike.toContinuousLinearMap_complexLinearIsometryEquiv
  proof: rfl

中文:
定理 _root_.RCLike.toContinuousLinearMap_complexLinearIsometryEquiv
  证明: rfl
-/
@[simp] theorem _root_.RCLike.toContinuousLinearMap_complexLinearIsometryEquiv
    {𝕜 : Type*} [RCLike 𝕜] (h : RCLike.im (RCLike.I : 𝕜) = 1) :
    (RCLike.complexLinearIsometryEquiv h : 𝕜 ->L[Real] Complex) = RCLike.map 𝕜 Complex := rfl

/--
theorem `_root_.RCLike.norm_to_complex` / 定理 `_root_.RCLike.norm_to_complex`

English:
theorem _root_.RCLike.norm_to_complex
  given: {𝕜 : Type*} [RCLike 𝕜] (a : 𝕜)
  proof: by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · rw [← RCLike.re_add_im a, RCLike.im_eq_zero h]
    simp
  exact (RCLike.complexLinearIsometryEquiv h).norm_map a

中文:
定理 _root_.RCLike.norm_to_complex
  条件: {𝕜 : 类型} [RCLike 𝕜] (a : 𝕜)
  证明: by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · rw [← RCLike.re_add_im a, RCLike.im_eq_zero h]
    simp
  exact (RCLike.complexLinearIsometryEquiv h).norm_map a
-/
@[simp] theorem _root_.RCLike.norm_to_complex {𝕜 : Type*} [RCLike 𝕜] (a : 𝕜) :
    ‖RCLike.re a + RCLike.im a * Complex.I‖ = ‖a‖ := by
  obtain (h | h) := RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · rw [← RCLike.re_add_im a, RCLike.im_eq_zero h]
    simp
  exact (RCLike.complexLinearIsometryEquiv h).norm_map a

/--
theorem `isometry_intCast` / 定理 `isometry_intCast`

English:
theorem isometry_intCast
  statement: Isometry ((↑) : Int -> Complex)
  proof: Isometry.of_dist_eq by simp_rw [← Complex.ofReal_intCast,
    Complex.isometry_ofReal.dist_eq, Int.dist_cast_real, implies_true]

中文:
定理 isometry_intCast
  结论: Isometry ((↑) : 整数 -> Complex)
  证明: Isometry.of_dist_eq by simp_rw [← Complex.ofReal_intCast,
    Complex.isometry_ofReal.dist_eq, Int.dist_cast_real, implies_true]

Depends on / 依赖: Complex.isometry_ofReal.dist_eq, Complex.ofReal_intCast, Int.dist_cast_real, Isometry, Isometry.of_dist_eq, dist_cast_real, dist_eq, implies_true, isometry_ofReal, ofReal_intCast, of_dist_eq, simp_rw
-/
theorem isometry_intCast : Isometry ((↑) : Int -> Complex) :=
Isometry.of_dist_eq by simp_rw [← Complex.ofReal_intCast,
    Complex.isometry_ofReal.dist_eq, Int.dist_cast_real, implies_true]

/--
theorem `isClosedEmbedding_intCast` / 定理 `isClosedEmbedding_intCast`

English:
theorem isClosedEmbedding_intCast
  statement: IsClosedEmbedding ((↑) : Int -> Complex)
  proof: isometry_intCast.isClosedEmbedding

@[deprecated (since := "2026-04-15")] alias closedEmbedding_intCast := isClosedEmbedding_intCast

中文:
定理 isClosedEmbedding_intCast
  结论: IsClosedEmbedding ((↑) : 整数 -> Complex)
  证明: isometry_intCast.isClosedEmbedding

@[deprecated (since := "2026-04-15")] alias closedEmbedding_intCast := isClosedEmbedding_intCast

Depends on / 依赖: isClosedEmbedding, isometry_intCast, isometry_intCast.isClosedEmbedding
-/
theorem isClosedEmbedding_intCast : IsClosedEmbedding ((↑) : Int -> Complex) :=
  isometry_intCast.isClosedEmbedding

@[deprecated (since := "2026-04-15")] alias closedEmbedding_intCast := isClosedEmbedding_intCast

/--
lemma `isClosed_range_intCast` / 引理 `isClosed_range_intCast`

English:
lemma isClosed_range_intCast
  statement: IsClosed (Set.range ((↑) : Int -> Complex))
  proof: Complex.isClosedEmbedding_intCast.isClosed_range

中文:
引理 isClosed_range_intCast
  结论: IsClosed (Set.range ((↑) : 整数 -> Complex))
  证明: Complex.isClosedEmbedding_intCast.isClosed_range

Depends on / 依赖: Complex.isClosedEmbedding_intCast.isClosed_range, isClosedEmbedding_intCast, isClosed_range
-/
lemma isClosed_range_intCast : IsClosed (Set.range ((↑) : Int -> Complex)) :=
  Complex.isClosedEmbedding_intCast.isClosed_range

/--
lemma `isOpen_compl_range_intCast` / 引理 `isOpen_compl_range_intCast`

English:
lemma isOpen_compl_range_intCast
  statement: IsOpen (Set.range ((↑) : Int -> Complex))ᶜ
  proof: Complex.isClosed_range_intCast.isOpen_compl

中文:
引理 isOpen_compl_range_intCast
  结论: IsOpen (Set.range ((↑) : 整数 -> Complex))ᶜ
  证明: Complex.isClosed_range_intCast.isOpen_compl

Depends on / 依赖: Complex.isClosed_range_intCast.isOpen_compl, isClosed_range_intCast, isOpen_compl
-/
lemma isOpen_compl_range_intCast : IsOpen (Set.range ((↑) : Int -> Complex))ᶜ :=
  Complex.isClosed_range_intCast.isOpen_compl

section ComplexOrder

open ComplexOrder

/--
theorem `eq_coe_norm_of_nonneg` / 定理 `eq_coe_norm_of_nonneg`

English:
theorem eq_coe_norm_of_nonneg
  given: {z : Complex} (hz : 0 <= z)
  statement: z = ↑‖z‖
  proof: by
  lift z to Real using hz.2.symm
  rw [norm_real]; rw [Real.norm_of_nonneg (id hz.1 : 0 <= z)]

中文:
定理 eq_coe_norm_of_nonneg
  条件: {z : Complex} (hz : 0 <= z)
  结论: z = ↑‖z‖
  证明: by
  lift z to Real using hz.2.symm
  rw [norm_real]; rw [Real.norm_of_nonneg (id hz.1 : 0 <= z)]

Depends on / 依赖: Real.norm_of_nonneg, norm_of_nonneg, norm_real
-/
theorem eq_coe_norm_of_nonneg {z : Complex} (hz : 0 <= z) : z = ↑‖z‖ := by
  lift z to Real using hz.2.symm
  rw [norm_real]; rw [Real.norm_of_nonneg (id hz.1 : 0 <= z)]

/--
lemma `orderClosedTopology` / 引理 `orderClosedTopology`

English:
lemma orderClosedTopology
  statement: OrderClosedTopology Complex
  proof: RCLike.instOrderClosedTopology

scoped[ComplexOrder] attribute [instance] Complex.orderClosedTopology

中文:
引理 orderClosedTopology
  结论: OrderClosedTopology Complex
  证明: RCLike.instOrderClosedTopology

scoped[ComplexOrder] attribute [instance] Complex.orderClosedTopology

Depends on / 依赖: RCLike, RCLike.instOrderClosedTopology, instOrderClosedTopology
-/
lemma orderClosedTopology : OrderClosedTopology Complex := RCLike.instOrderClosedTopology

scoped[ComplexOrder] attribute [instance] Complex.orderClosedTopology

/--
theorem `norm_of_nonneg'` / 定理 `norm_of_nonneg'`

English:
theorem norm_of_nonneg'
  given: {x : Complex} (hx : 0 <= x)
  statement: ‖x‖ = x
  proof: by
  rw [← RCLike.ofReal_eq_complex_ofReal]
  exact RCLike.norm_of_nonneg' hx

中文:
定理 norm_of_nonneg'
  条件: {x : Complex} (hx : 0 <= x)
  结论: ‖x‖ = x
  证明: by
  rw [← RCLike.ofReal_eq_complex_ofReal]
  exact RCLike.norm_of_nonneg' hx

Depends on / 依赖: RCLike, RCLike.norm_of_nonneg, RCLike.ofReal_eq_complex_ofReal, norm_of_nonneg, ofReal_eq_complex_ofReal
-/
theorem norm_of_nonneg' {x : Complex} (hx : 0 <= x) : ‖x‖ = x := by
  rw [← RCLike.ofReal_eq_complex_ofReal]
  exact RCLike.norm_of_nonneg' hx

/--
lemma `re_nonneg_iff_nonneg` / 引理 `re_nonneg_iff_nonneg`

English:
lemma re_nonneg_iff_nonneg
  given: {x : Complex} (hx : IsSelfAdjoint x)
  statement: 0 <= re x ↔ 0 <= x
  proof: by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.re_nonneg_of_nonneg hx

@[gcongr]

中文:
引理 re_nonneg_iff_nonneg
  条件: {x : Complex} (hx : IsSelfAdjoint x)
  结论: 0 <= re x ↔ 0 <= x
  证明: by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.re_nonneg_of_nonneg hx

@[gcongr]

Depends on / 依赖: RCLike, RCLike.re_eq_complex_re, RCLike.re_nonneg_of_nonneg, re_eq_complex_re, re_nonneg_of_nonneg
-/
lemma re_nonneg_iff_nonneg {x : Complex} (hx : IsSelfAdjoint x) : 0 <= re x ↔ 0 <= x := by
  rw [← RCLike.re_eq_complex_re]
  exact RCLike.re_nonneg_of_nonneg hx

@[gcongr]
/--
lemma `re_le_re` / 引理 `re_le_re`

English:
lemma re_le_re
  given: {x y : Complex} (h : x <= y)
  statement: re x <= re y
  proof: by
  rw [RCLike.le_iff_re_im] at h
  exact h.1

中文:
引理 re_le_re
  条件: {x y : Complex} (h : x <= y)
  结论: re x <= re y
  证明: by
  rw [RCLike.le_iff_re_im] at h
  exact h.1

Depends on / 依赖: RCLike, RCLike.le_iff_re_im, le_iff_re_im
-/
lemma re_le_re {x y : Complex} (h : x <= y) : re x <= re y := by
  rw [RCLike.le_iff_re_im] at h
  exact h.1

end ComplexOrder

end Complex

namespace RCLike

open ComplexConjugate

local notation "reC" => @RCLike.re Complex _
local notation "imC" => @RCLike.im Complex _
local notation "IC" => @RCLike.I Complex _
local notation "norm_sqC" => @RCLike.normSq Complex _

@[simp]
/--
theorem `re_to_complex` / 定理 `re_to_complex`

English:
theorem re_to_complex
  given: {x : Complex}
  statement: reC x = x.re
  proof: rfl

@[simp]

中文:
定理 re_to_complex
  条件: {x : Complex}
  结论: reC x = x.re
  证明: rfl

@[simp]
-/
theorem re_to_complex {x : Complex} : reC x = x.re :=
  rfl

@[simp]
/--
theorem `im_to_complex` / 定理 `im_to_complex`

English:
theorem im_to_complex
  given: {x : Complex}
  statement: imC x = x.im
  proof: rfl

@[simp]

中文:
定理 im_to_complex
  条件: {x : Complex}
  结论: imC x = x.im
  证明: rfl

@[simp]
-/
theorem im_to_complex {x : Complex} : imC x = x.im :=
  rfl

@[simp]
/--
theorem `I_to_complex` / 定理 `I_to_complex`

English:
theorem I_to_complex
  statement: IC = Complex.I
  proof: rfl

@[simp]

中文:
定理 I_to_complex
  结论: IC = Complex.I
  证明: rfl

@[simp]
-/
theorem I_to_complex : IC = Complex.I :=
  rfl

@[simp]
/--
theorem `normSq_to_complex` / 定理 `normSq_to_complex`

English:
theorem normSq_to_complex
  given: {x : Complex}
  statement: norm_sqC x = Complex.normSq x
  proof: rfl

中文:
定理 normSq_to_complex
  条件: {x : Complex}
  结论: norm_sqC x = Complex.normSq x
  证明: rfl
-/
theorem normSq_to_complex {x : Complex} : norm_sqC x = Complex.normSq x :=
  rfl

section tsum

variable {α : Type*} (𝕜 : Type*) [RCLike 𝕜] {L : SummationFilter α}

@[simp]
/--
theorem `hasSum_conj` / 定理 `hasSum_conj`

English:
theorem hasSum_conj
  given: {f : α -> 𝕜} {x : 𝕜}
  statement: HasSum (fun x => conj (f x)) x L ↔ HasSum f (conj x) L
  proof: conjCLE.hasSum

中文:
定理 hasSum_conj
  条件: {f : α -> 𝕜} {x : 𝕜}
  结论: HasSum (fun x => conj (f x)) x L ↔ HasSum f (conj x) L
  证明: conjCLE.hasSum

Depends on / 依赖: conjCLE, conjCLE.hasSum, hasSum
-/
theorem hasSum_conj {f : α -> 𝕜} {x : 𝕜} : HasSum (fun x => conj (f x)) x L ↔ HasSum f (conj x) L :=
  conjCLE.hasSum

/--
theorem `hasSum_conj'` / 定理 `hasSum_conj'`

English:
theorem hasSum_conj'
  given: {f : α -> 𝕜} {x : 𝕜}
  statement: HasSum (fun x => conj (f x)) (conj x) L ↔ HasSum f x L
  proof: conjCLE.hasSum'

@[simp]

中文:
定理 hasSum_conj'
  条件: {f : α -> 𝕜} {x : 𝕜}
  结论: HasSum (fun x => conj (f x)) (conj x) L ↔ HasSum f x L
  证明: conjCLE.hasSum'

@[simp]

Depends on / 依赖: conjCLE, conjCLE.hasSum, hasSum
-/
theorem hasSum_conj' {f : α -> 𝕜} {x : 𝕜} : HasSum (fun x => conj (f x)) (conj x) L ↔ HasSum f x L :=
  conjCLE.hasSum'

@[simp]
/--
theorem `summable_conj` / 定理 `summable_conj`

English:
theorem summable_conj
  given: {f : α -> 𝕜}
  statement: Summable (fun x => conj (f x)) L ↔ Summable f L
  proof: summable_star_iff

中文:
定理 summable_conj
  条件: {f : α -> 𝕜}
  结论: Summable (fun x => conj (f x)) L ↔ Summable f L
  证明: summable_star_iff

Depends on / 依赖: summable_star_iff
-/
theorem summable_conj {f : α -> 𝕜} : Summable (fun x => conj (f x)) L ↔ Summable f L :=
  summable_star_iff

variable {𝕜} in
/--
theorem `conj_tsum` / 定理 `conj_tsum`

English:
theorem conj_tsum
  given: (f : α -> 𝕜)
  statement: conj (∑'[L] a, f a) = ∑'[L] a, conj (f a)
  proof: tsum_star

@[simp, norm_cast]

中文:
定理 conj_tsum
  条件: (f : α -> 𝕜)
  结论: conj (∑'[L] a, f a) = ∑'[L] a, conj (f a)
  证明: tsum_star

@[simp, norm_cast]

Depends on / 依赖: tsum_star
-/
theorem conj_tsum (f : α -> 𝕜) : conj (∑'[L] a, f a) = ∑'[L] a, conj (f a) :=
  tsum_star

@[simp, norm_cast]
/--
theorem `hasSum_ofReal` / 定理 `hasSum_ofReal`

English:
theorem hasSum_ofReal
  given: {f : α -> Real} {x : Real}
  statement: HasSum (fun x => (f x : 𝕜)) x L ↔ HasSum f x L
  proof: ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.hasSum h,
    ofRealCLM.hasSum⟩

@[simp, norm_cast]

中文:
定理 hasSum_ofReal
  条件: {f : α -> 实数} {x : 实数}
  结论: HasSum (fun x => (f x : 𝕜)) x L ↔ HasSum f x L
  证明: ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.hasSum h,
    ofRealCLM.hasSum⟩

@[simp, norm_cast]

Depends on / 依赖: RCLike, RCLike.ofReal_re, RCLike.reCLM_apply, hasSum, ofRealCLM, ofRealCLM.hasSum, ofReal_re, reCLM.hasSum, reCLM_apply
-/
theorem hasSum_ofReal {f : α -> Real} {x : Real} : HasSum (fun x => (f x : 𝕜)) x L ↔ HasSum f x L :=
  ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.hasSum h,
    ofRealCLM.hasSum⟩

@[simp, norm_cast]
/--
theorem `summable_ofReal` / 定理 `summable_ofReal`

English:
theorem summable_ofReal
  given: {f : α -> Real}
  statement: Summable (fun x => (f x : 𝕜)) L ↔ Summable f L
  proof: ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.summable h,
    ofRealCLM.summable⟩

@[norm_cast]

中文:
定理 summable_ofReal
  条件: {f : α -> 实数}
  结论: Summable (fun x => (f x : 𝕜)) L ↔ Summable f L
  证明: ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.summable h,
    ofRealCLM.summable⟩

@[norm_cast]

Depends on / 依赖: RCLike, RCLike.ofReal_re, RCLike.reCLM_apply, ofRealCLM, ofRealCLM.summable, ofReal_re, reCLM.summable, reCLM_apply, summable
-/
theorem summable_ofReal {f : α -> Real} : Summable (fun x => (f x : 𝕜)) L ↔ Summable f L :=
  ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using reCLM.summable h,
    ofRealCLM.summable⟩

@[norm_cast]
/--
theorem `ofReal_tsum` / 定理 `ofReal_tsum`

English:
theorem ofReal_tsum
  given: (f : α -> Real)
  statement: (↑(∑'[L] a, f a) : 𝕜) = ∑'[L] a, (f a : 𝕜)
  proof: Function.LeftInverse.map_tsum f ofRealCLM.continuous continuous_re (fun _ => by simp)

中文:
定理 ofReal_tsum
  条件: (f : α -> 实数)
  结论: (↑(∑'[L] a, f a) : 𝕜) = ∑'[L] a, (f a : 𝕜)
  证明: Function.LeftInverse.map_tsum f ofRealCLM.continuous continuous_re (fun _ => by simp)

Depends on / 依赖: Function, Function.LeftInverse.map_tsum, LeftInverse, continuous, continuous_re, map_tsum, ofRealCLM, ofRealCLM.continuous
-/
theorem ofReal_tsum (f : α -> Real) : (↑(∑'[L] a, f a) : 𝕜) = ∑'[L] a, (f a : 𝕜) :=
  Function.LeftInverse.map_tsum f ofRealCLM.continuous continuous_re (fun _ => by simp)

/--
theorem `hasSum_re` / 定理 `hasSum_re`

English:
theorem hasSum_re
  given: {f : α -> 𝕜} {x : 𝕜} (h : HasSum f x L)
  statement: HasSum (fun x => re (f x)) (re x) L
  proof: reCLM.hasSum h

中文:
定理 hasSum_re
  条件: {f : α -> 𝕜} {x : 𝕜} (h : HasSum f x L)
  结论: HasSum (fun x => re (f x)) (re x) L
  证明: reCLM.hasSum h

Depends on / 依赖: hasSum, reCLM.hasSum
-/
theorem hasSum_re {f : α -> 𝕜} {x : 𝕜} (h : HasSum f x L) : HasSum (fun x => re (f x)) (re x) L :=
  reCLM.hasSum h

/--
theorem `hasSum_im` / 定理 `hasSum_im`

English:
theorem hasSum_im
  given: {f : α -> 𝕜} {x : 𝕜} (h : HasSum f x L)
  statement: HasSum (fun x => im (f x)) (im x) L
  proof: imCLM.hasSum h

中文:
定理 hasSum_im
  条件: {f : α -> 𝕜} {x : 𝕜} (h : HasSum f x L)
  结论: HasSum (fun x => im (f x)) (im x) L
  证明: imCLM.hasSum h

Depends on / 依赖: hasSum, imCLM.hasSum
-/
theorem hasSum_im {f : α -> 𝕜} {x : 𝕜} (h : HasSum f x L) : HasSum (fun x => im (f x)) (im x) L :=
  imCLM.hasSum h

/--
theorem `re_tsum` / 定理 `re_tsum`

English:
theorem re_tsum
  given: [L.NeBot] {f : α -> 𝕜} (h : Summable f L)
  statement: re (∑'[L] a, f a) = ∑'[L] a, re (f a)
  proof: reCLM.map_tsum h

中文:
定理 re_tsum
  条件: [L.NeBot] {f : α -> 𝕜} (h : Summable f L)
  结论: re (∑'[L] a, f a) = ∑'[L] a, re (f a)
  证明: reCLM.map_tsum h

Depends on / 依赖: map_tsum, reCLM.map_tsum
-/
theorem re_tsum [L.NeBot] {f : α -> 𝕜} (h : Summable f L) : re (∑'[L] a, f a) = ∑'[L] a, re (f a) :=
  reCLM.map_tsum h

/--
theorem `im_tsum` / 定理 `im_tsum`

English:
theorem im_tsum
  given: [L.NeBot] {f : α -> 𝕜} (h : Summable f L)
  statement: im (∑'[L] a, f a) = ∑'[L] a, im (f a)
  proof: imCLM.map_tsum h

中文:
定理 im_tsum
  条件: [L.NeBot] {f : α -> 𝕜} (h : Summable f L)
  结论: im (∑'[L] a, f a) = ∑'[L] a, im (f a)
  证明: imCLM.map_tsum h

Depends on / 依赖: imCLM.map_tsum, map_tsum
-/
theorem im_tsum [L.NeBot] {f : α -> 𝕜} (h : Summable f L) : im (∑'[L] a, f a) = ∑'[L] a, im (f a) :=
  imCLM.map_tsum h

variable {𝕜}

/--
theorem `hasSum_iff` / 定理 `hasSum_iff`

English:
theorem hasSum_iff
  given: (f : α -> 𝕜) (c : 𝕜)
  proof: by
  refine ⟨fun h => ⟨hasSum_re _ h, hasSum_im _ h⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  simpa only [re_add_im] using
    ((hasSum_ofReal 𝕜).mpr h₁).add (((hasSum_ofReal 𝕜).mpr h₂).mul_right I)

中文:
定理 hasSum_iff
  条件: (f : α -> 𝕜) (c : 𝕜)
  证明: by
  refine ⟨fun h => ⟨hasSum_re _ h, hasSum_im _ h⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  simpa only [re_add_im] using
    ((hasSum_ofReal 𝕜).mpr h₁).add (((hasSum_ofReal 𝕜).mpr h₂).mul_right I)

Depends on / 依赖: hasSum_im, hasSum_ofReal, hasSum_re, mul_right, re_add_im
-/
theorem hasSum_iff (f : α -> 𝕜) (c : 𝕜) :
    HasSum f c L ↔ HasSum (fun x => re (f x)) (re c) L ∧ HasSum (fun x => im (f x)) (im c) L := by
  refine ⟨fun h => ⟨hasSum_re _ h, hasSum_im _ h⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  simpa only [re_add_im] using
    ((hasSum_ofReal 𝕜).mpr h₁).add (((hasSum_ofReal 𝕜).mpr h₂).mul_right I)

end tsum

end RCLike

namespace Complex

/-!
We have to repeat the lemmas about `RCLike.re` and `RCLike.im` as they are not syntactic
matches for `Complex.re` and `Complex.im`.

We do not have this problem with `ofReal` and `conj`, although we repeat them anyway for
discoverability and to avoid the need to unify `𝕜`.
-/


section tsum

variable {α : Type*} {L : SummationFilter α}

open ComplexConjugate

/--
theorem `hasSum_conj` / 定理 `hasSum_conj`

English:
theorem hasSum_conj
  given: {f : α -> Complex} {x : Complex}
  statement: HasSum (fun x => conj (f x)) x L ↔ HasSum f (conj x) L
  proof: RCLike.hasSum_conj _

中文:
定理 hasSum_conj
  条件: {f : α -> Complex} {x : Complex}
  结论: HasSum (fun x => conj (f x)) x L ↔ HasSum f (conj x) L
  证明: RCLike.hasSum_conj _

Depends on / 依赖: RCLike, RCLike.hasSum_conj, hasSum_conj
-/
theorem hasSum_conj {f : α -> Complex} {x : Complex} : HasSum (fun x => conj (f x)) x L ↔ HasSum f (conj x) L :=
  RCLike.hasSum_conj _

/--
theorem `hasSum_conj'` / 定理 `hasSum_conj'`

English:
theorem hasSum_conj'
  given: {f : α -> Complex} {x : Complex}
  statement: HasSum (fun x => conj (f x)) (conj x) L ↔ HasSum f x L
  proof: RCLike.hasSum_conj' _

中文:
定理 hasSum_conj'
  条件: {f : α -> Complex} {x : Complex}
  结论: HasSum (fun x => conj (f x)) (conj x) L ↔ HasSum f x L
  证明: RCLike.hasSum_conj' _

Depends on / 依赖: RCLike, RCLike.hasSum_conj, hasSum_conj
-/
theorem hasSum_conj' {f : α -> Complex} {x : Complex} : HasSum (fun x => conj (f x)) (conj x) L ↔ HasSum f x L :=
  RCLike.hasSum_conj' _

/--
theorem `summable_conj` / 定理 `summable_conj`

English:
theorem summable_conj
  given: {f : α -> Complex}
  statement: (Summable fun x => conj (f x)) ↔ Summable f
  proof: RCLike.summable_conj _

中文:
定理 summable_conj
  条件: {f : α -> Complex}
  结论: (Summable fun x => conj (f x)) ↔ Summable f
  证明: RCLike.summable_conj _

Depends on / 依赖: RCLike, RCLike.summable_conj, summable_conj
-/
theorem summable_conj {f : α -> Complex} : (Summable fun x => conj (f x)) ↔ Summable f :=
  RCLike.summable_conj _

/--
theorem `conj_tsum` / 定理 `conj_tsum`

English:
theorem conj_tsum
  given: (f : α -> Complex)
  statement: conj (∑'[L] a, f a) = ∑'[L] a, conj (f a)
  proof: RCLike.conj_tsum _

@[simp, norm_cast]

中文:
定理 conj_tsum
  条件: (f : α -> Complex)
  结论: conj (∑'[L] a, f a) = ∑'[L] a, conj (f a)
  证明: RCLike.conj_tsum _

@[simp, norm_cast]

Depends on / 依赖: RCLike, RCLike.conj_tsum, conj_tsum
-/
theorem conj_tsum (f : α -> Complex) : conj (∑'[L] a, f a) = ∑'[L] a, conj (f a) :=
  RCLike.conj_tsum _

@[simp, norm_cast]
/--
theorem `hasSum_ofReal` / 定理 `hasSum_ofReal`

English:
theorem hasSum_ofReal
  given: {f : α -> Real} {x : Real}
  statement: HasSum (fun x => (f x : Complex)) x L ↔ HasSum f x L
  proof: RCLike.hasSum_ofReal _

@[simp, norm_cast]

中文:
定理 hasSum_ofReal
  条件: {f : α -> 实数} {x : 实数}
  结论: HasSum (fun x => (f x : Complex)) x L ↔ HasSum f x L
  证明: RCLike.hasSum_ofReal _

@[simp, norm_cast]

Depends on / 依赖: RCLike, RCLike.hasSum_ofReal, hasSum_ofReal
-/
theorem hasSum_ofReal {f : α -> Real} {x : Real} : HasSum (fun x => (f x : Complex)) x L ↔ HasSum f x L :=
  RCLike.hasSum_ofReal _

@[simp, norm_cast]
/--
theorem `summable_ofReal` / 定理 `summable_ofReal`

English:
theorem summable_ofReal
  given: {f : α -> Real}
  statement: (Summable (fun x => (f x : Complex)) L) ↔ Summable f L
  proof: RCLike.summable_ofReal _

@[norm_cast]

中文:
定理 summable_ofReal
  条件: {f : α -> 实数}
  结论: (Summable (fun x => (f x : Complex)) L) ↔ Summable f L
  证明: RCLike.summable_ofReal _

@[norm_cast]

Depends on / 依赖: RCLike, RCLike.summable_ofReal, summable_ofReal
-/
theorem summable_ofReal {f : α -> Real} : (Summable (fun x => (f x : Complex)) L) ↔ Summable f L :=
  RCLike.summable_ofReal _

@[norm_cast]
/--
theorem `ofReal_tsum` / 定理 `ofReal_tsum`

English:
theorem ofReal_tsum
  given: (f : α -> Real)
  statement: (↑(∑'[L] a, f a) : Complex) = ∑'[L] a, ↑(f a)
  proof: RCLike.ofReal_tsum _ _

中文:
定理 ofReal_tsum
  条件: (f : α -> 实数)
  结论: (↑(∑'[L] a, f a) : Complex) = ∑'[L] a, ↑(f a)
  证明: RCLike.ofReal_tsum _ _

Depends on / 依赖: RCLike, RCLike.ofReal_tsum, ofReal_tsum
-/
theorem ofReal_tsum (f : α -> Real) : (↑(∑'[L] a, f a) : Complex) = ∑'[L] a, ↑(f a) :=
  RCLike.ofReal_tsum _ _

/--
theorem `hasSum_re` / 定理 `hasSum_re`

English:
theorem hasSum_re
  given: {f : α -> Complex} {x : Complex} (h : HasSum f x L)
  statement: HasSum (fun x => (f x).re) x.re L
  proof: RCLike.hasSum_re Complex h

中文:
定理 hasSum_re
  条件: {f : α -> Complex} {x : Complex} (h : HasSum f x L)
  结论: HasSum (fun x => (f x).re) x.re L
  证明: RCLike.hasSum_re Complex h

Depends on / 依赖: RCLike, RCLike.hasSum_re, hasSum_re
-/
theorem hasSum_re {f : α -> Complex} {x : Complex} (h : HasSum f x L) : HasSum (fun x => (f x).re) x.re L :=
  RCLike.hasSum_re Complex h

/--
theorem `hasSum_im` / 定理 `hasSum_im`

English:
theorem hasSum_im
  given: {f : α -> Complex} {x : Complex} (h : HasSum f x L)
  statement: HasSum (fun x => (f x).im) x.im L
  proof: RCLike.hasSum_im Complex h

中文:
定理 hasSum_im
  条件: {f : α -> Complex} {x : Complex} (h : HasSum f x L)
  结论: HasSum (fun x => (f x).im) x.im L
  证明: RCLike.hasSum_im Complex h

Depends on / 依赖: RCLike, RCLike.hasSum_im, hasSum_im
-/
theorem hasSum_im {f : α -> Complex} {x : Complex} (h : HasSum f x L) : HasSum (fun x => (f x).im) x.im L :=
  RCLike.hasSum_im Complex h

/--
theorem `re_tsum` / 定理 `re_tsum`

English:
theorem re_tsum
  given: [L.NeBot] {f : α -> Complex} (h : Summable f L)
  statement: (∑'[L] a, f a).re = ∑'[L] a, (f a).re
  proof: RCLike.re_tsum _ h

中文:
定理 re_tsum
  条件: [L.NeBot] {f : α -> Complex} (h : Summable f L)
  结论: (∑'[L] a, f a).re = ∑'[L] a, (f a).re
  证明: RCLike.re_tsum _ h

Depends on / 依赖: RCLike, RCLike.re_tsum, re_tsum
-/
theorem re_tsum [L.NeBot] {f : α -> Complex} (h : Summable f L) : (∑'[L] a, f a).re = ∑'[L] a, (f a).re :=
  RCLike.re_tsum _ h

/--
theorem `im_tsum` / 定理 `im_tsum`

English:
theorem im_tsum
  given: [L.NeBot] {f : α -> Complex} (h : Summable f L)
  statement: (∑'[L] a, f a).im = ∑'[L] a, (f a).im
  proof: RCLike.im_tsum _ h

中文:
定理 im_tsum
  条件: [L.NeBot] {f : α -> Complex} (h : Summable f L)
  结论: (∑'[L] a, f a).im = ∑'[L] a, (f a).im
  证明: RCLike.im_tsum _ h

Depends on / 依赖: RCLike, RCLike.im_tsum, im_tsum
-/
theorem im_tsum [L.NeBot] {f : α -> Complex} (h : Summable f L) : (∑'[L] a, f a).im = ∑'[L] a, (f a).im :=
  RCLike.im_tsum _ h

/--
theorem `hasSum_iff` / 定理 `hasSum_iff`

English:
theorem hasSum_iff
  given: (f : α -> Complex) (c : Complex)
  proof: RCLike.hasSum_iff _ _

中文:
定理 hasSum_iff
  条件: (f : α -> Complex) (c : Complex)
  证明: RCLike.hasSum_iff _ _

Depends on / 依赖: RCLike, RCLike.hasSum_iff, hasSum_iff
-/
theorem hasSum_iff (f : α -> Complex) (c : Complex) :
    HasSum f c L ↔ HasSum (fun x => (f x).re) c.re L ∧ HasSum (fun x => (f x).im) c.im L :=
  RCLike.hasSum_iff _ _

end tsum

section slitPlane

/-!
### Define the "slit plane" `ℂ ∖ ℝ≤0` and provide some API
-/

open scoped ComplexOrder

/--
Definition of `slitPlane` / `slitPlane` 的定义

English:
definition slitPlane
  signature: : Set Complex
  body: {z | 0 < z.re ∨ z.im != 0}

中文:
定义 slitPlane
  签名: : Set Complex
  定义体: {z | 0 < z.re ∨ z.im != 0}

Depends on / 依赖: z.im, z.re
-/
def slitPlane : Set Complex := {z | 0 < z.re ∨ z.im != 0}

/--
lemma `mem_slitPlane_iff` / 引理 `mem_slitPlane_iff`

English:
lemma mem_slitPlane_iff
  given: {z : Complex}
  statement: z in slitPlane ↔ 0 < z.re ∨ z.im != 0
  proof: Set.mem_ofPred

中文:
引理 mem_slitPlane_iff
  条件: {z : Complex}
  结论: z in slitPlane ↔ 0 < z.re ∨ z.im != 0
  证明: Set.mem_ofPred

Depends on / 依赖: Set.mem_ofPred, mem_ofPred
-/
lemma mem_slitPlane_iff {z : Complex} : z in slitPlane ↔ 0 < z.re ∨ z.im != 0 := Set.mem_ofPred

/--
lemma `mem_slitPlane_or_neg_mem_slitPlane` / 引理 `mem_slitPlane_or_neg_mem_slitPlane`

English:
lemma mem_slitPlane_or_neg_mem_slitPlane
  given: {z : Complex} (hz : z != 0)
  proof: by
  rw [mem_slitPlane_iff]; rw [mem_slitPlane_iff]
  rw [ne_eq]; rw [Complex.ext_iff] at hz
  push Not at hz
  simp_all only [ne_eq, zero_re, zero_im, neg_re, Left.neg_pos_iff, neg_im, neg_eq_zero]
  by_contra! contra
  exact hz (le_antisymm contra.1.1 contra.2.1) contra.1.2

中文:
引理 mem_slitPlane_or_neg_mem_slitPlane
  条件: {z : Complex} (hz : z != 0)
  证明: by
  rw [mem_slitPlane_iff]; rw [mem_slitPlane_iff]
  rw [ne_eq]; rw [Complex.ext_iff] at hz
  push Not at hz
  simp_all only [ne_eq, zero_re, zero_im, neg_re, Left.neg_pos_iff, neg_im, neg_eq_zero]
  by_contra! contra
  exact hz (le_antisymm contra.1.1 contra.2.1) contra.1.2

Depends on / 依赖: Complex.ext_iff, Left.neg_pos_iff, contra, ext_iff, le_antisymm, mem_slitPlane_iff, ne_eq, neg_eq_zero, neg_im, neg_pos_iff, neg_re, zero_im, zero_re
-/
lemma mem_slitPlane_or_neg_mem_slitPlane {z : Complex} (hz : z != 0) :
    z in slitPlane ∨ -z in slitPlane := by
  rw [mem_slitPlane_iff]; rw [mem_slitPlane_iff]
  rw [ne_eq]; rw [Complex.ext_iff] at hz
  push Not at hz
  simp_all only [ne_eq, zero_re, zero_im, neg_re, Left.neg_pos_iff, neg_im, neg_eq_zero]
  by_contra! contra
  exact hz (le_antisymm contra.1.1 contra.2.1) contra.1.2

/--
lemma `slitPlane_eq_union` / 引理 `slitPlane_eq_union`

English:
lemma slitPlane_eq_union
  statement: slitPlane = {z | 0 < z.re} union {z | z.im != 0}
  proof: Set.ofPred_or.symm

中文:
引理 slitPlane_eq_union
  结论: slitPlane = {z | 0 < z.re} union {z | z.im != 0}
  证明: Set.ofPred_or.symm

Depends on / 依赖: Set.ofPred_or.symm, ofPred_or
-/
lemma slitPlane_eq_union : slitPlane = {z | 0 < z.re} union {z | z.im != 0} := Set.ofPred_or.symm

/--
lemma `isOpen_slitPlane` / 引理 `isOpen_slitPlane`

English:
lemma isOpen_slitPlane
  statement: IsOpen slitPlane
  proof: (isOpen_lt continuous_const continuous_re).union (isOpen_ne_fun continuous_im continuous_const)

@[simp]

中文:
引理 isOpen_slitPlane
  结论: IsOpen slitPlane
  证明: (isOpen_lt continuous_const continuous_re).union (isOpen_ne_fun continuous_im continuous_const)

@[simp]

Depends on / 依赖: continuous_const, continuous_im, continuous_re, isOpen_lt, isOpen_ne_fun
-/
lemma isOpen_slitPlane : IsOpen slitPlane :=
  (isOpen_lt continuous_const continuous_re).union (isOpen_ne_fun continuous_im continuous_const)

@[simp]
/--
lemma `ofReal_mem_slitPlane` / 引理 `ofReal_mem_slitPlane`

English:
lemma ofReal_mem_slitPlane
  given: {x : Real}
  statement: ↑x in slitPlane ↔ 0 < x
  proof: by simp [mem_slitPlane_iff]

@[simp]

中文:
引理 ofReal_mem_slitPlane
  条件: {x : 实数}
  结论: ↑x in slitPlane ↔ 0 < x
  证明: by simp [mem_slitPlane_iff]

@[simp]

Depends on / 依赖: mem_slitPlane_iff
-/
lemma ofReal_mem_slitPlane {x : Real} : ↑x in slitPlane ↔ 0 < x := by simp [mem_slitPlane_iff]

@[simp]
/--
lemma `neg_ofReal_mem_slitPlane` / 引理 `neg_ofReal_mem_slitPlane`

English:
lemma neg_ofReal_mem_slitPlane
  given: {x : Real}
  statement: -↑x in slitPlane ↔ x < 0
  proof: by
  simpa using ofReal_mem_slitPlane (x := -x)

中文:
引理 neg_ofReal_mem_slitPlane
  条件: {x : 实数}
  结论: -↑x in slitPlane ↔ x < 0
  证明: by
  simpa using ofReal_mem_slitPlane (x := -x)

Depends on / 依赖: ofReal_mem_slitPlane
-/
lemma neg_ofReal_mem_slitPlane {x : Real} : -↑x in slitPlane ↔ x < 0 := by
  simpa using ofReal_mem_slitPlane (x := -x)

/--
lemma `one_mem_slitPlane` / 引理 `one_mem_slitPlane`

English:
lemma one_mem_slitPlane
  statement: 1 in slitPlane
  proof: ofReal_mem_slitPlane.2 one_pos

@[simp]

中文:
引理 one_mem_slitPlane
  结论: 1 in slitPlane
  证明: ofReal_mem_slitPlane.2 one_pos

@[simp]
-/
@[simp] lemma one_mem_slitPlane : 1 in slitPlane := ofReal_mem_slitPlane.2 one_pos

@[simp]
/--
lemma `zero_notMem_slitPlane` / 引理 `zero_notMem_slitPlane`

English:
lemma zero_notMem_slitPlane
  statement: 0 ∉ slitPlane
  proof: mt ofReal_mem_slitPlane.1 (lt_irrefl _)

@[simp]

中文:
引理 zero_notMem_slitPlane
  结论: 0 ∉ slitPlane
  证明: mt ofReal_mem_slitPlane.1 (lt_irrefl _)

@[simp]

Depends on / 依赖: lt_irrefl, ofReal_mem_slitPlane
-/
lemma zero_notMem_slitPlane : 0 ∉ slitPlane := mt ofReal_mem_slitPlane.1 (lt_irrefl _)

@[simp]
/--
lemma `natCast_mem_slitPlane` / 引理 `natCast_mem_slitPlane`

English:
lemma natCast_mem_slitPlane
  given: {n : Nat}
  statement: ↑n in slitPlane ↔ n != 0
  proof: by
  simpa [pos_iff_ne_zero] using @ofReal_mem_slitPlane n

@[simp]

中文:
引理 natCast_mem_slitPlane
  条件: {n : 自然数}
  结论: ↑n in slitPlane ↔ n != 0
  证明: by
  simpa [pos_iff_ne_zero] using @ofReal_mem_slitPlane n

@[simp]

Depends on / 依赖: ofReal_mem_slitPlane, pos_iff_ne_zero
-/
lemma natCast_mem_slitPlane {n : Nat} : ↑n in slitPlane ↔ n != 0 := by
  simpa [pos_iff_ne_zero] using @ofReal_mem_slitPlane n

@[simp]
/--
lemma `ofNat_mem_slitPlane` / 引理 `ofNat_mem_slitPlane`

English:
lemma ofNat_mem_slitPlane
  given: (n : Nat) [n.AtLeastTwo]
  statement: ofNat(n) in slitPlane
  proof: natCast_mem_slitPlane.2 (NeZero.ne n)

中文:
引理 ofNat_mem_slitPlane
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: of自然数(n) in slitPlane
  证明: natCast_mem_slitPlane.2 (NeZero.ne n)

Depends on / 依赖: NeZero, NeZero.ne, natCast_mem_slitPlane
-/
lemma ofNat_mem_slitPlane (n : Nat) [n.AtLeastTwo] : ofNat(n) in slitPlane :=
  natCast_mem_slitPlane.2 (NeZero.ne n)

/--
lemma `mem_slitPlane_iff_not_le_zero` / 引理 `mem_slitPlane_iff_not_le_zero`

English:
lemma mem_slitPlane_iff_not_le_zero
  given: {z : Complex}
  statement: z in slitPlane ↔ ¬z <= 0
  proof: mem_slitPlane_iff.trans not_le_zero_iff.symm

中文:
引理 mem_slitPlane_iff_not_le_zero
  条件: {z : Complex}
  结论: z in slitPlane ↔ ¬z <= 0
  证明: mem_slitPlane_iff.trans not_le_zero_iff.symm

Depends on / 依赖: mem_slitPlane_iff, mem_slitPlane_iff.trans, not_le_zero_iff, not_le_zero_iff.symm
-/
lemma mem_slitPlane_iff_not_le_zero {z : Complex} : z in slitPlane ↔ ¬z <= 0 :=
  mem_slitPlane_iff.trans not_le_zero_iff.symm

/--
lemma `compl_Iic_zero` / 引理 `compl_Iic_zero`

English:
lemma compl_Iic_zero
  statement: (Set.Iic 0)ᶜ = slitPlane
  proof: Set.ext fun _ =>
  mem_slitPlane_iff_not_le_zero.symm

中文:
引理 compl_Iic_zero
  结论: (Set.Iic 0)ᶜ = slitPlane
  证明: Set.ext fun _ =>
  mem_slitPlane_iff_not_le_zero.symm
-/
protected lemma compl_Iic_zero : (Set.Iic 0)ᶜ = slitPlane := Set.ext fun _ =>
  mem_slitPlane_iff_not_le_zero.symm

/--
lemma `slitPlane_ne_zero` / 引理 `slitPlane_ne_zero`

English:
lemma slitPlane_ne_zero
  given: {z : Complex} (hz : z in slitPlane)
  statement: z != 0
  proof: ne_of_mem_of_not_mem hz zero_notMem_slitPlane

中文:
引理 slitPlane_ne_zero
  条件: {z : Complex} (hz : z in slitPlane)
  结论: z != 0
  证明: ne_of_mem_of_not_mem hz zero_notMem_slitPlane

Depends on / 依赖: ne_of_mem_of_not_mem, zero_notMem_slitPlane
-/
lemma slitPlane_ne_zero {z : Complex} (hz : z in slitPlane) : z != 0 :=
  ne_of_mem_of_not_mem hz zero_notMem_slitPlane

/--
lemma `ball_one_subset_slitPlane` / 引理 `ball_one_subset_slitPlane`

English:
lemma ball_one_subset_slitPlane
  statement: Metric.ball 1 1 subseteq slitPlane
  proof: by
  intro z hz
  apply Or.inl
  simpa using (re_le_norm _).trans_lt (mem_ball_iff_norm'.1 hz)

中文:
引理 ball_one_subset_slitPlane
  结论: Metric.ball 1 1 subseteq slitPlane
  证明: by
  intro z hz
  apply Or.inl
  simpa using (re_le_norm _).trans_lt (mem_ball_iff_norm'.1 hz)

Depends on / 依赖: Or.inl, mem_ball_iff_norm, re_le_norm, trans_lt
-/
lemma ball_one_subset_slitPlane : Metric.ball 1 1 subseteq slitPlane := by
  intro z hz
  apply Or.inl
  simpa using (re_le_norm _).trans_lt (mem_ball_iff_norm'.1 hz)

/--
lemma `mem_slitPlane_of_norm_lt_one` / 引理 `mem_slitPlane_of_norm_lt_one`

English:
lemma mem_slitPlane_of_norm_lt_one
  given: {z : Complex} (hz : ‖z‖ < 1)
  statement: 1 + z in slitPlane
  proof: ball_one_subset_slitPlane by simpa

中文:
引理 mem_slitPlane_of_norm_lt_one
  条件: {z : Complex} (hz : ‖z‖ < 1)
  结论: 1 + z in slitPlane
  证明: ball_one_subset_slitPlane by simpa

Depends on / 依赖: ball_one_subset_slitPlane
-/
lemma mem_slitPlane_of_norm_lt_one {z : Complex} (hz : ‖z‖ < 1) : 1 + z in slitPlane :=
ball_one_subset_slitPlane by simpa

open Metric in
/--
lemma `subset_slitPlane_iff_of_subset_sphere` / 引理 `subset_slitPlane_iff_of_subset_sphere`

English:
lemma subset_slitPlane_iff_of_subset_sphere
  given: {r : Real} {s : Set Complex} (hs : s subseteq sphere 0 r)
  proof: by
  simp_rw [Set.subset_def, mem_slitPlane_iff_not_le_zero]
  contrapose!
  refine ⟨?_, fun hr => ⟨_, hr, by simpa using hs hr⟩⟩
  rintro ⟨z, hzs, hz⟩
  have : ‖z‖ = r := by simpa using hs hzs
  simpa [← this, ← norm_neg z ▸ eq_coe_norm_of_nonneg (neg_nonneg.mpr hz)]

中文:
引理 subset_slitPlane_iff_of_subset_sphere
  条件: {r : 实数} {s : Set Complex} (hs : s subseteq sphere 0 r)
  证明: by
  simp_rw [Set.subset_def, mem_slitPlane_iff_not_le_zero]
  contrapose!
  refine ⟨?_, fun hr => ⟨_, hr, by simpa using hs hr⟩⟩
  rintro ⟨z, hzs, hz⟩
  have : ‖z‖ = r := by simpa using hs hzs
  simpa [← this, ← norm_neg z ▸ eq_coe_norm_of_nonneg (neg_nonneg.mpr hz)]

Depends on / 依赖: Set.subset_def, contrapose, eq_coe_norm_of_nonneg, mem_slitPlane_iff_not_le_zero, neg_nonneg, neg_nonneg.mpr, norm_neg, simp_rw, subset_def
-/
lemma subset_slitPlane_iff_of_subset_sphere {r : Real} {s : Set Complex} (hs : s subseteq sphere 0 r) :
    s subseteq slitPlane ↔ (-r : Complex) ∉ s := by
  simp_rw [Set.subset_def, mem_slitPlane_iff_not_le_zero]
  contrapose!
  refine ⟨?_, fun hr => ⟨_, hr, by simpa using hs hr⟩⟩
  rintro ⟨z, hzs, hz⟩
  have : ‖z‖ = r := by simpa using hs hzs
  simpa [← this, ← norm_neg z ▸ eq_coe_norm_of_nonneg (neg_nonneg.mpr hz)]

end slitPlane

/--
lemma `_root_.IsCompact.reProdIm` / 引理 `_root_.IsCompact.reProdIm`

English:
lemma _root_.IsCompact.reProdIm
  given: {s t : Set Real} (hs : IsCompact s) (ht : IsCompact t)
  proof: equivRealProdCLM.toHomeomorph.isCompact_preimage.2 (hs.prod ht)

中文:
引理 _root_.IsCompact.reProdIm
  条件: {s t : Set 实数} (hs : IsCompact s) (ht : IsCompact t)
  证明: equivRealProdCLM.toHomeomorph.isCompact_preimage.2 (hs.prod ht)

Depends on / 依赖: equivRealProdCLM, equivRealProdCLM.toHomeomorph.isCompact_preimage, hs.prod, isCompact_preimage, toHomeomorph
-/
lemma _root_.IsCompact.reProdIm {s t : Set Real} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ×Complex t) :=
  equivRealProdCLM.toHomeomorph.isCompact_preimage.2 (hs.prod ht)

end Complex

section realPart_imaginaryPart

variable {A : Type*} [SeminormedAddCommGroup A] [StarAddMonoid A] [NormedSpace Complex A] [StarModule Complex A]
  [NormedStarGroup A]

/--
lemma `realPart.norm_le` / 引理 `realPart.norm_le`

English:
lemma realPart.norm_le
  given: (x : A)
  statement: ‖realPart x‖ <= ‖x‖
  proof: by
  rw [← inv_mul_cancel_left₀ two_ne_zero ‖x‖]; rw [← AddSubgroup.norm_coe]; rw [realPart_apply_coe]; rw [norm_smul]; rw [norm_inv]; rw [Real.norm_ofNat]
  gcongr
.trans by simp [two_mul] exact norm_add_le _ _

中文:
引理 realPart.norm_le
  条件: (x : A)
  结论: ‖realPart x‖ <= ‖x‖
  证明: by
  rw [← inv_mul_cancel_left₀ two_ne_zero ‖x‖]; rw [← AddSubgroup.norm_coe]; rw [realPart_apply_coe]; rw [norm_smul]; rw [norm_inv]; rw [Real.norm_ofNat]
  gcongr
.trans by simp [two_mul] exact norm_add_le _ _

Depends on / 依赖: AddSubgroup, AddSubgroup.norm_coe, Real.norm_ofNat, norm_add_le, norm_coe, norm_inv, norm_ofNat, norm_smul, realPart_apply_coe, two_mul, two_ne_zero
-/
lemma realPart.norm_le (x : A) : ‖realPart x‖ <= ‖x‖ := by
  rw [← inv_mul_cancel_left₀ two_ne_zero ‖x‖]; rw [← AddSubgroup.norm_coe]; rw [realPart_apply_coe]; rw [norm_smul]; rw [norm_inv]; rw [Real.norm_ofNat]
  gcongr
.trans by simp [two_mul] exact norm_add_le _ _

/--
lemma `imaginaryPart.norm_le` / 引理 `imaginaryPart.norm_le`

English:
lemma imaginaryPart.norm_le
  given: (x : A)
  statement: ‖imaginaryPart x‖ <= ‖x‖
  proof: by
  calc ‖imaginaryPart x‖ = ‖realPart (Complex.I • (-x))‖ := by simp
    _ <= ‖x‖ := by simpa only [smul_neg, map_neg, realPart_I_smul, neg_neg,
        AddSubgroupClass.coe_norm, norm_neg, norm_smul, Complex.norm_I, one_mul] using
        realPart.norm_le (Complex.I • (-x))

中文:
引理 imaginaryPart.norm_le
  条件: (x : A)
  结论: ‖imaginaryPart x‖ <= ‖x‖
  证明: by
  calc ‖imaginaryPart x‖ = ‖realPart (Complex.I • (-x))‖ := by simp
    _ <= ‖x‖ := by simpa only [smul_neg, map_neg, realPart_I_smul, neg_neg,
        AddSubgroupClass.coe_norm, norm_neg, norm_smul, Complex.norm_I, one_mul] using
        realPart.norm_le (Complex.I • (-x))

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.coe_norm, Complex.I, Complex.norm_I, coe_norm, imaginaryPart, map_neg, neg_neg, norm_I, norm_le, norm_neg, norm_smul, one_mul, realPart, realPart.norm_le, realPart_I_smul, smul_neg
-/
lemma imaginaryPart.norm_le (x : A) : ‖imaginaryPart x‖ <= ‖x‖ := by
  calc ‖imaginaryPart x‖ = ‖realPart (Complex.I • (-x))‖ := by simp
    _ <= ‖x‖ := by simpa only [smul_neg, map_neg, realPart_I_smul, neg_neg,
        AddSubgroupClass.coe_norm, norm_neg, norm_smul, Complex.norm_I, one_mul] using
        realPart.norm_le (Complex.I • (-x))

end realPart_imaginaryPart
