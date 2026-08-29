/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Algebra

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

We show that the norm on `ℍ[ℝ]` agrees with the Euclidean norm of its components.

## Notation

The following notation is available with `open Quaternion` or `open scoped Quaternion`:

* `ℍ` : quaternions

## Tags

quaternion, normed ring, normed space, normed algebra
-/

@[expose] public noncomputable section


@[inherit_doc] scoped[Quaternion] notation "ℍ" => Quaternion Real

open scoped RealInnerProductSpace

namespace Quaternion

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inner Real ℍ
  body: ⟨fun a b => (a * star b).re⟩

中文:
实例 :
  签名: 内积 实数 ℍ
  定义体: ⟨fun a b => (a * star b).re⟩
-/
instance : Inner Real ℍ :=
  ⟨fun a b => (a * star b).re⟩

/--
theorem `inner_self` / 定理 `inner_self`

English:
theorem inner_self
  given: (a : ℍ)
  statement: ⟪a, a⟫ = normSq a
  proof: rfl

中文:
定理 inner_self
  条件: (a : ℍ)
  结论: ⟪a, a⟫ = normSq a
  证明: rfl
-/
theorem inner_self (a : ℍ) : ⟪a, a⟫ = normSq a :=
  rfl

/--
theorem `inner_def` / 定理 `inner_def`

English:
theorem inner_def
  given: (a b : ℍ)
  statement: ⟪a, b⟫ = (a * star b).re
  proof: rfl

中文:
定理 inner_def
  条件: (a b : ℍ)
  结论: ⟪a, b⟫ = (a * star b).re
  证明: rfl
-/
theorem inner_def (a b : ℍ) : ⟪a, b⟫ = (a * star b).re :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedAddCommGroup ℍ
  body: @InnerProductSpace.Core.toNormedAddCommGroup Real ℍ _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun x y => by simp [inner_def, mul_comm]
      re_inner_nonneg := fun _ => normSq_nonneg
      definite := fun _ => normSq_eq_zero.1
      add_left := fun x y z => by simp only [inner_de

中文:
实例 :
  签名: 赋范交换加群 ℍ
  定义体: @InnerProductSpace.Core.toNormedAddCommGroup Real ℍ _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun x y => by simp [inner_def, mul_comm]
      re_inner_nonneg := fun _ => normSq_nonneg
      definite := fun _ => normSq_eq_zero.1
      add_left := fun x y z => by simp only [inner_de

Depends on / 依赖: Category, InnerProductSpace, InnerProductSpace.Core.toNormedAddCommGroup, IsThin, Quiver, Quiver.IsThin, add_left, add_mul, conj_inner_symm, definite, inner_def, locallySmall_of_thin, mul_comm, normSq_eq_zero, normSq_nonneg, re_add, re_inner_nonneg, smul_left, toInner, toNormedAddCommGroup
-/
instance : NormedAddCommGroup ℍ :=
  @InnerProductSpace.Core.toNormedAddCommGroup Real ℍ _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun x y => by simp [inner_def, mul_comm]
      re_inner_nonneg := fun _ => normSq_nonneg
      definite := fun _ => normSq_eq_zero.1
      add_left := fun x y z => by simp only [inner_def, add_mul, re_add]
      smul_left := fun x y r => by simp [inner_def] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InnerProductSpace Real ℍ
  body: InnerProductSpace.ofCore _

中文:
实例 :
  签名: 内积空间 实数 ℍ
  定义体: InnerProductSpace.ofCore _

Depends on / 依赖: InnerProductSpace, InnerProductSpace.ofCore, ofCore
-/
instance : InnerProductSpace Real ℍ :=
  InnerProductSpace.ofCore _

/--
theorem `normSq_eq_norm_mul_self` / 定理 `normSq_eq_norm_mul_self`

English:
theorem normSq_eq_norm_mul_self
  given: (a : ℍ)
  statement: normSq a = ‖a‖ * ‖a‖
  proof: by
  rw [← inner_self]; rw [real_inner_self_eq_norm_mul_norm]

中文:
定理 normSq_eq_norm_mul_self
  条件: (a : ℍ)
  结论: normSq a = ‖a‖ * ‖a‖
  证明: by
  rw [← inner_self]; rw [real_inner_self_eq_norm_mul_norm]

Depends on / 依赖: inner_self, real_inner_self_eq_norm_mul_norm
-/
theorem normSq_eq_norm_mul_self (a : ℍ) : normSq a = ‖a‖ * ‖a‖ := by
  rw [← inner_self]; rw [real_inner_self_eq_norm_mul_norm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormOneClass ℍ
  body: ⟨by rw [norm_eq_sqrt_real_inner, inner_self, normSq.map_one, Real.sqrt_one]⟩

@[simp, norm_cast]

中文:
实例 :
  签名: NormOne类 ℍ
  定义体: ⟨by rw [norm_eq_sqrt_real_inner, inner_self, normSq.map_one, Real.sqrt_one]⟩

@[simp, norm_cast]

Depends on / 依赖: Real.sqrt_one, inner_self, map_one, normSq, normSq.map_one, norm_eq_sqrt_real_inner, sqrt_one
-/
instance : NormOneClass ℍ :=
  ⟨by rw [norm_eq_sqrt_real_inner, inner_self, normSq.map_one, Real.sqrt_one]⟩

@[simp, norm_cast]
/--
theorem `norm_coe` / 定理 `norm_coe`

English:
theorem norm_coe
  given: (a : Real)
  statement: ‖(a : ℍ)‖ = ‖a‖
  proof: by
  rw [norm_eq_sqrt_real_inner]; rw [inner_self]; rw [normSq_coe]; rw [Real.sqrt_sq_eq_abs]; rw [Real.norm_eq_abs]

@[simp, norm_cast]

中文:
定理 norm_coe
  条件: (a : 实数)
  结论: ‖(a : ℍ)‖ = ‖a‖
  证明: by
  rw [norm_eq_sqrt_real_inner]; rw [inner_self]; rw [normSq_coe]; rw [Real.sqrt_sq_eq_abs]; rw [Real.norm_eq_abs]

@[simp, norm_cast]

Depends on / 依赖: Real.norm_eq_abs, Real.sqrt_sq_eq_abs, inner_self, normSq_coe, norm_eq_abs, norm_eq_sqrt_real_inner, sqrt_sq_eq_abs
-/
theorem norm_coe (a : Real) : ‖(a : ℍ)‖ = ‖a‖ := by
  rw [norm_eq_sqrt_real_inner]; rw [inner_self]; rw [normSq_coe]; rw [Real.sqrt_sq_eq_abs]; rw [Real.norm_eq_abs]

@[simp, norm_cast]
/--
theorem `nnnorm_coe` / 定理 `nnnorm_coe`

English:
theorem nnnorm_coe
  given: (a : Real)
  statement: ‖(a : ℍ)‖₊ = ‖a‖₊
  proof: Subtype.ext norm_coe a

中文:
定理 nnnorm_coe
  条件: (a : 实数)
  结论: ‖(a : ℍ)‖₊ = ‖a‖₊
  证明: Subtype.ext norm_coe a

Depends on / 依赖: NatTrans, NatTrans.app, Subtype, Subtype.ext, norm_coe, small_of_injective
-/
theorem nnnorm_coe (a : Real) : ‖(a : ℍ)‖₊ = ‖a‖₊ :=
Subtype.ext norm_coe a

-- This does not need to be `@[simp]`, as it is a consequence of later simp lemmas.
/--
theorem `norm_star` / 定理 `norm_star`

English:
theorem norm_star
  given: (a : ℍ)
  statement: ‖star a‖ = ‖a‖
  proof: by
  simp_rw [norm_eq_sqrt_real_inner, inner_self, normSq_star]

中文:
定理 norm_star
  条件: (a : ℍ)
  结论: ‖star a‖ = ‖a‖
  证明: by
  simp_rw [norm_eq_sqrt_real_inner, inner_self, normSq_star]

Depends on / 依赖: inner_self, normSq_star, norm_eq_sqrt_real_inner, simp_rw
-/
theorem norm_star (a : ℍ) : ‖star a‖ = ‖a‖ := by
  simp_rw [norm_eq_sqrt_real_inner, inner_self, normSq_star]

-- This does not need to be `@[simp]`, as it is a consequence of later simp lemmas.
/--
theorem `nnnorm_star` / 定理 `nnnorm_star`

English:
theorem nnnorm_star
  given: (a : ℍ)
  statement: ‖star a‖₊ = ‖a‖₊
  proof: Subtype.ext norm_star a

中文:
定理 nnnorm_star
  条件: (a : ℍ)
  结论: ‖star a‖₊ = ‖a‖₊
  证明: Subtype.ext norm_star a

Depends on / 依赖: HasBinaryCoproducts, HasPullbacks, Subtype, Subtype.ext, norm_star
-/
theorem nnnorm_star (a : ℍ) : ‖star a‖₊ = ‖a‖₊ :=
Subtype.ext norm_star a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedDivisionRing ℍ
  body: rfl
  norm_mul _ _ := by simp_rw [norm_eq_sqrt_real_inner, inner_self]; simp

中文:
实例 :
  签名: NormedDivision环 ℍ
  定义体: rfl
  norm_mul _ _ := by simp_rw [norm_eq_sqrt_real_inner, inner_self]; simp
-/
instance : NormedDivisionRing ℍ where
  dist_eq _ _ := rfl
  norm_mul _ _ := by simp_rw [norm_eq_sqrt_real_inner, inner_self]; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedAlgebra Real ℍ
  body: norm_smul_le
  toAlgebra := Quaternion.algebra

中文:
实例 :
  签名: 赋范代数 实数 ℍ
  定义体: norm_smul_le
  toAlgebra := Quaternion.algebra

Depends on / 依赖: norm_smul_le
-/
instance : NormedAlgebra Real ℍ where
  norm_smul_le := norm_smul_le
  toAlgebra := Quaternion.algebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CStarRing ℍ
  body: le_of_eq Eq.symm (norm_mul _ _).trans congr_arg (· * ‖x‖) (norm_star x)

中文:
实例 :
  签名: CStar环 ℍ
  定义体: le_of_eq Eq.symm (norm_mul _ _).trans congr_arg (· * ‖x‖) (norm_star x)

Depends on / 依赖: Eq.symm, congr_arg, le_of_eq, norm_mul, norm_star
-/
instance : CStarRing ℍ where
  norm_mul_self_le x :=
le_of_eq Eq.symm (norm_mul _ _).trans congr_arg (· * ‖x‖) (norm_star x)

/--
Definition of `coeComplex` / `coeComplex` 的定义

English:
definition coeComplex
  signature: (z : Complex)
  body: ⟨z.re, z.im, 0, 0⟩

中文:
定义 coeComplex
  签名: (z : 复形)
  定义体: ⟨z.re, z.im, 0, 0⟩

Depends on / 依赖: PreservesLimitsOfShape, WalkingCospan
-/
@[coe] def coeComplex (z : Complex) : ℍ := ⟨z.re, z.im, 0, 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Complex ℍ
  body: ⟨coeComplex⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Coe 复形 ℍ
  定义体: ⟨coeComplex⟩

@[simp, norm_cast]

Depends on / 依赖: coeComplex
-/
instance : Coe Complex ℍ := ⟨coeComplex⟩

@[simp, norm_cast]
/--
theorem `re_coeComplex` / 定理 `re_coeComplex`

English:
theorem re_coeComplex
  given: (z : Complex)
  statement: (z : ℍ).re = z.re
  proof: rfl

@[simp, norm_cast]

中文:
定理 re_coeComplex
  条件: (z : 复形)
  结论: (z : ℍ).re = z.re
  证明: rfl

@[simp, norm_cast]
-/
theorem re_coeComplex (z : Complex) : (z : ℍ).re = z.re :=
  rfl

@[simp, norm_cast]
/--
theorem `imI_coeComplex` / 定理 `imI_coeComplex`

English:
theorem imI_coeComplex
  given: (z : Complex)
  statement: (z : ℍ).imI = z.im
  proof: rfl

@[simp, norm_cast]

中文:
定理 imI_coeComplex
  条件: (z : 复形)
  结论: (z : ℍ).imI = z.im
  证明: rfl

@[simp, norm_cast]
-/
theorem imI_coeComplex (z : Complex) : (z : ℍ).imI = z.im :=
  rfl

@[simp, norm_cast]
/--
theorem `imJ_coeComplex` / 定理 `imJ_coeComplex`

English:
theorem imJ_coeComplex
  given: (z : Complex)
  statement: (z : ℍ).imJ = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imJ_coeComplex
  条件: (z : 复形)
  结论: (z : ℍ).imJ = 0
  证明: rfl

@[simp, norm_cast]

Depends on / 依赖: FinitaryExtensive, FinitaryExtensive.toFinitaryPreExtensive, toFinitaryPreExtensive
-/
theorem imJ_coeComplex (z : Complex) : (z : ℍ).imJ = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `imK_coeComplex` / 定理 `imK_coeComplex`

English:
theorem imK_coeComplex
  given: (z : Complex)
  statement: (z : ℍ).imK = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 imK_coeComplex
  条件: (z : 复形)
  结论: (z : ℍ).imK = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem imK_coeComplex (z : Complex) : (z : ℍ).imK = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coeComplex_add` / 定理 `coeComplex_add`

English:
theorem coeComplex_add
  given: (z w : Complex)
  statement: ↑(z + w) = (z + w : ℍ)
  proof: by ext <;> simp

@[simp, norm_cast]

中文:
定理 coeComplex_add
  条件: (z w : 复形)
  结论: ↑(z + w) = (z + w : ℍ)
  证明: by ext <;> simp

@[simp, norm_cast]
-/
theorem coeComplex_add (z w : Complex) : ↑(z + w) = (z + w : ℍ) := by ext <;> simp

@[simp, norm_cast]
/--
theorem `coeComplex_mul` / 定理 `coeComplex_mul`

English:
theorem coeComplex_mul
  given: (z w : Complex)
  statement: ↑(z * w) = (z * w : ℍ)
  proof: by ext <;> simp

@[simp, norm_cast]

中文:
定理 coeComplex_mul
  条件: (z w : 复形)
  结论: ↑(z * w) = (z * w : ℍ)
  证明: by ext <;> simp

@[simp, norm_cast]

Depends on / 依赖: FinitaryExtensive, MonoCoprod
-/
theorem coeComplex_mul (z w : Complex) : ↑(z * w) = (z * w : ℍ) := by ext <;> simp

@[simp, norm_cast]
/--
theorem `coeComplex_zero` / 定理 `coeComplex_zero`

English:
theorem coeComplex_zero
  statement: ((0 : Complex) : ℍ) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 coeComplex_zero
  结论: ((0 : 复形) : ℍ) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem coeComplex_zero : ((0 : Complex) : ℍ) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coeComplex_one` / 定理 `coeComplex_one`

English:
theorem coeComplex_one
  statement: ((1 : Complex) : ℍ) = 1
  proof: rfl

@[simp, norm_cast]

中文:
定理 coeComplex_one
  结论: ((1 : 复形) : ℍ) = 1
  证明: rfl

@[simp, norm_cast]

Depends on / 依赖: hasStrictInitialObjects_of_finitaryPreExtensive
-/
theorem coeComplex_one : ((1 : Complex) : ℍ) = 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_real_complex_mul` / 定理 `coe_real_complex_mul`

English:
theorem coe_real_complex_mul
  given: (r : Real) (z : Complex)
  statement: (r • z : ℍ) = ↑r * ↑z
  proof: by ext <;> simp

@[simp, norm_cast]

中文:
定理 coe_real_complex_mul
  条件: (r : 实数) (z : 复形)
  结论: (r • z : ℍ) = ↑r * ↑z
  证明: by ext <;> simp

@[simp, norm_cast]
-/
theorem coe_real_complex_mul (r : Real) (z : Complex) : (r • z : ℍ) = ↑r * ↑z := by ext <;> simp

@[simp, norm_cast]
/--
theorem `coeComplex_coe` / 定理 `coeComplex_coe`

English:
theorem coeComplex_coe
  given: (r : Real)
  statement: ((r : Complex) : ℍ) = r
  proof: rfl

中文:
定理 coeComplex_coe
  条件: (r : 实数)
  结论: ((r : 复形) : ℍ) = r
  证明: rfl
-/
theorem coeComplex_coe (r : Real) : ((r : Complex) : ℍ) = r :=
  rfl

/--
Definition of `ofComplex` / `ofComplex` 的定义

English:
definition ofComplex
  signature: : Complex ->ₐ[Real] ℍ where
  body: (↑)
  map_one' := rfl
  map_zero' := rfl
  map_add' := coeComplex_add
  map_mul' := coeComplex_mul
  commutes' _ := rfl

@[simp]

中文:
定义 ofComplex
  签名: : 复形 ->ₐ[实数] ℍ where
  定义体: (↑)
  map_one' := rfl
  map_zero' := rfl
  map_add' := coeComplex_add
  map_mul' := coeComplex_mul
  commutes' _ := rfl

@[simp]
-/
def ofComplex : Complex ->ₐ[Real] ℍ where
  toFun := (↑)
  map_one' := rfl
  map_zero' := rfl
  map_add' := coeComplex_add
  map_mul' := coeComplex_mul
  commutes' _ := rfl

@[simp]
/--
theorem `coe_ofComplex` / 定理 `coe_ofComplex`

English:
theorem coe_ofComplex
  statement: ⇑ofComplex = coeComplex
  proof: rfl

中文:
定理 coe_ofComplex
  结论: ⇑ofComplex = coeComplex
  证明: rfl
-/
theorem coe_ofComplex : ⇑ofComplex = coeComplex := rfl

/--
lemma `norm_toLp_equivTuple` / 引理 `norm_toLp_equivTuple`

English:
lemma norm_toLp_equivTuple
  given: (x : ℍ)
  statement: ‖WithLp.toLp 2 (equivTuple Real x)‖ = ‖x‖
  proof: by
  rw [norm_eq_sqrt_real_inner]; rw [norm_eq_sqrt_real_inner]; rw [inner_self]; rw [normSq_def']; rw [PiLp.inner_apply]; rw [Fin.sum_univ_four]
  simp_rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, ← sq]
  rfl

中文:
引理 norm_toLp_equivTuple
  条件: (x : ℍ)
  结论: ‖WithLp.toLp 2 (equivTuple 实数 x)‖ = ‖x‖
  证明: by
  rw [norm_eq_sqrt_real_inner]; rw [norm_eq_sqrt_real_inner]; rw [inner_self]; rw [normSq_def']; rw [PiLp.inner_apply]; rw [Fin.sum_univ_four]
  simp_rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, ← sq]
  rfl

Depends on / 依赖: Fin.sum_univ_four, PiLp.inner_apply, RCLike, RCLike.inner_apply, inner_apply, inner_self, normSq_def, norm_eq_sqrt_real_inner, simp_rw, starRingEnd_apply, star_trivial, sum_univ_four
-/
lemma norm_toLp_equivTuple (x : ℍ) : ‖WithLp.toLp 2 (equivTuple Real x)‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner]; rw [norm_eq_sqrt_real_inner]; rw [inner_self]; rw [normSq_def']; rw [PiLp.inner_apply]; rw [Fin.sum_univ_four]
  simp_rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, ← sq]
  rfl

/-- `QuaternionAlgebra.linearEquivTuple` as a `LinearIsometryEquiv`. -/
@[simps apply symm_apply]
/--
Definition of `linearIsometryEquivTuple` / `linearIsometryEquivTuple` 的定义

English:
definition linearIsometryEquivTuple
  signature: : ℍ ≃ₗᵢ[Real] EuclideanSpace Real (Fin 4)
  body: { (QuaternionAlgebra.linearEquivTuple (-1 : Real) (0 : Real) (-1 : Real)).trans
      (WithLp.linearEquiv 2 Real (Fin 4 -> Real)).symm with
    toFun := fun a => !₂[a.1, a.2, a.3, a.4]
    invFun := fun a => ⟨a 0, a 1, a 2, a 3⟩
    norm_map' := norm_toLp_equivTuple }

@[continuity]

中文:
定义 linearIsometryEquivTuple
  签名: : ℍ ≃ₗᵢ[实数] EuclideanSpace 实数 (有限集 4)
  定义体: { (QuaternionAlgebra.linearEquivTuple (-1 : Real) (0 : Real) (-1 : Real)).trans
      (WithLp.linearEquiv 2 Real (Fin 4 -> Real)).symm with
    toFun := fun a => !₂[a.1, a.2, a.3, a.4]
    invFun := fun a => ⟨a 0, a 1, a 2, a 3⟩
    norm_map' := norm_toLp_equivTuple }

@[continuity]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.linearEquivTuple, WithLp, WithLp.linearEquiv, invFun, linearEquiv, linearEquivTuple, norm_map, norm_toLp_equivTuple
-/
def linearIsometryEquivTuple : ℍ ≃ₗᵢ[Real] EuclideanSpace Real (Fin 4) :=
  { (QuaternionAlgebra.linearEquivTuple (-1 : Real) (0 : Real) (-1 : Real)).trans
      (WithLp.linearEquiv 2 Real (Fin 4 -> Real)).symm with
    toFun := fun a => !₂[a.1, a.2, a.3, a.4]
    invFun := fun a => ⟨a 0, a 1, a 2, a 3⟩
    norm_map' := norm_toLp_equivTuple }

@[continuity]
/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous (coe : Real -> ℍ)
  proof: continuous_algebraMap Real ℍ

@[continuity]

中文:
定理 continuous_coe
  结论: 连续 (coe : 实数 -> ℍ)
  证明: continuous_algebraMap Real ℍ

@[continuity]

Depends on / 依赖: F.map_comp, IsPullback, IsPullback.of_hasPullback, IsPullback.of_vert_isIso, condition, continuous_algebraMap, hasPullback_of_left_iso, isLimit, isLimitMapConePullbackConeEquiv, map_comp, of_hasPullback, of_vert_isIso, preservesLimit_of_preserves_limit_cone, pullback, pullback.condition
-/
theorem continuous_coe : Continuous (coe : Real -> ℍ) :=
  continuous_algebraMap Real ℍ

@[continuity]
/--
theorem `continuous_normSq` / 定理 `continuous_normSq`

English:
theorem continuous_normSq
  statement: Continuous (normSq : ℍ -> Real)
  proof: by
  simpa [← normSq_eq_norm_mul_self] using
    (continuous_norm.fun_mul continuous_norm : Continuous fun q : ℍ => ‖q‖ * ‖q‖)

@[continuity]

中文:
定理 continuous_normSq
  结论: 连续 (normSq : ℍ -> 实数)
  证明: by
  simpa [← normSq_eq_norm_mul_self] using
    (continuous_norm.fun_mul continuous_norm : Continuous fun q : ℍ => ‖q‖ * ‖q‖)

@[continuity]

Depends on / 依赖: Continuous, continuous_norm, continuous_norm.fun_mul, fun_mul, normSq_eq_norm_mul_self, preservesPullback_symmetry
-/
theorem continuous_normSq : Continuous (normSq : ℍ -> Real) := by
  simpa [← normSq_eq_norm_mul_self] using
    (continuous_norm.fun_mul continuous_norm : Continuous fun q : ℍ => ‖q‖ * ‖q‖)

@[continuity]
/--
theorem `continuous_re` / 定理 `continuous_re`

English:
theorem continuous_re
  statement: Continuous fun q : ℍ => q.re
  proof: (PiLp.continuous_apply 2 _ 0).comp linearIsometryEquivTuple.continuous

@[continuity]

中文:
定理 continuous_re
  结论: 连续 fun q : ℍ => q.re
  证明: (PiLp.continuous_apply 2 _ 0).comp linearIsometryEquivTuple.continuous

@[continuity]

Depends on / 依赖: PiLp.continuous_apply, continuous, continuous_apply, linearIsometryEquivTuple, linearIsometryEquivTuple.continuous
-/
theorem continuous_re : Continuous fun q : ℍ => q.re :=
  (PiLp.continuous_apply 2 _ 0).comp linearIsometryEquivTuple.continuous

@[continuity]
/--
theorem `continuous_imI` / 定理 `continuous_imI`

English:
theorem continuous_imI
  statement: Continuous fun q : ℍ => q.imI
  proof: (PiLp.continuous_apply 2 _ 1).comp linearIsometryEquivTuple.continuous

@[continuity]

中文:
定理 continuous_imI
  结论: 连续 fun q : ℍ => q.imI
  证明: (PiLp.continuous_apply 2 _ 1).comp linearIsometryEquivTuple.continuous

@[continuity]

Depends on / 依赖: PiLp.continuous_apply, continuous, continuous_apply, linearIsometryEquivTuple, linearIsometryEquivTuple.continuous
-/
theorem continuous_imI : Continuous fun q : ℍ => q.imI :=
  (PiLp.continuous_apply 2 _ 1).comp linearIsometryEquivTuple.continuous

@[continuity]
/--
theorem `continuous_imJ` / 定理 `continuous_imJ`

English:
theorem continuous_imJ
  statement: Continuous fun q : ℍ => q.imJ
  proof: (PiLp.continuous_apply 2 _ 2).comp linearIsometryEquivTuple.continuous

@[continuity]

中文:
定理 continuous_imJ
  结论: 连续 fun q : ℍ => q.imJ
  证明: (PiLp.continuous_apply 2 _ 2).comp linearIsometryEquivTuple.continuous

@[continuity]

Depends on / 依赖: PiLp.continuous_apply, continuous, continuous_apply, linearIsometryEquivTuple, linearIsometryEquivTuple.continuous
-/
theorem continuous_imJ : Continuous fun q : ℍ => q.imJ :=
  (PiLp.continuous_apply 2 _ 2).comp linearIsometryEquivTuple.continuous

@[continuity]
/--
theorem `continuous_imK` / 定理 `continuous_imK`

English:
theorem continuous_imK
  statement: Continuous fun q : ℍ => q.imK
  proof: (PiLp.continuous_apply 2 _ 3).comp linearIsometryEquivTuple.continuous

@[continuity]

中文:
定理 continuous_imK
  结论: 连续 fun q : ℍ => q.imK
  证明: (PiLp.continuous_apply 2 _ 3).comp linearIsometryEquivTuple.continuous

@[continuity]

Depends on / 依赖: PiLp.continuous_apply, continuous, continuous_apply, linearIsometryEquivTuple, linearIsometryEquivTuple.continuous
-/
theorem continuous_imK : Continuous fun q : ℍ => q.imK :=
  (PiLp.continuous_apply 2 _ 3).comp linearIsometryEquivTuple.continuous

@[continuity]
/--
theorem `continuous_im` / 定理 `continuous_im`

English:
theorem continuous_im
  statement: Continuous fun q : ℍ => q.im
  proof: by
  simpa only [← sub_re_self] using! continuous_id.sub (continuous_coe.comp continuous_re)

中文:
定理 continuous_im
  结论: 连续 fun q : ℍ => q.im
  证明: by
  simpa only [← sub_re_self] using! continuous_id.sub (continuous_coe.comp continuous_re)

Depends on / 依赖: continuous_coe, continuous_coe.comp, continuous_id, continuous_id.sub, continuous_re, sub_re_self
-/
theorem continuous_im : Continuous fun q : ℍ => q.im := by
  simpa only [← sub_re_self] using! continuous_id.sub (continuous_coe.comp continuous_re)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSpace ℍ
  body: haveI : IsUniformEmbedding linearIsometryEquivTuple.toLinearEquiv.toEquiv.symm :=
    linearIsometryEquivTuple.toContinuousLinearEquiv.symm.isUniformEmbedding
  (completeSpace_congr this).1 inferInstance

中文:
实例 :
  签名: 完备空间 ℍ
  定义体: haveI : IsUniformEmbedding linearIsometryEquivTuple.toLinearEquiv.toEquiv.symm :=
    linearIsometryEquivTuple.toContinuousLinearEquiv.symm.isUniformEmbedding
  (completeSpace_congr this).1 inferInstance

Depends on / 依赖: IsUniformEmbedding, completeSpace_congr, isUniformEmbedding, linearIsometryEquivTuple, linearIsometryEquivTuple.toContinuousLinearEquiv.symm.isUniformEmbedding, linearIsometryEquivTuple.toLinearEquiv.toEquiv.symm, toContinuousLinearEquiv, toEquiv, toLinearEquiv
-/
instance : CompleteSpace ℍ :=
  haveI : IsUniformEmbedding linearIsometryEquivTuple.toLinearEquiv.toEquiv.symm :=
    linearIsometryEquivTuple.toContinuousLinearEquiv.symm.isUniformEmbedding
  (completeSpace_congr this).1 inferInstance

section infinite_sum

variable {α : Type*} {L : SummationFilter α}

@[simp, norm_cast]
/--
theorem `hasSum_coe` / 定理 `hasSum_coe`

English:
theorem hasSum_coe
  given: {f : α -> Real} {r : Real}
  statement: HasSum (fun a => (f a : ℍ)) (↑r : ℍ) L ↔ HasSum f r L
  proof: ⟨fun h => by
    simpa only using!
    h.map (show ℍ ->ₗ[Real] Real from QuaternionAlgebra.reₗ _ _ _) continuous_re,
    fun h => by simpa only using! h.map (algebraMap Real ℍ) (continuous_algebraMap _ _)⟩

@[simp, norm_cast]

中文:
定理 hasSum_coe
  条件: {f : α -> 实数} {r : 实数}
  结论: HasSum (fun a => (f a : ℍ)) (↑r : ℍ) L ↔ HasSum f r L
  证明: ⟨fun h => by
    simpa only using!
    h.map (show ℍ ->ₗ[Real] Real from QuaternionAlgebra.reₗ _ _ _) continuous_re,
    fun h => by simpa only using! h.map (algebraMap Real ℍ) (continuous_algebraMap _ _)⟩

@[simp, norm_cast]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.re, algebraMap, continuous_algebraMap, continuous_re, h.map
-/
theorem hasSum_coe {f : α -> Real} {r : Real} : HasSum (fun a => (f a : ℍ)) (↑r : ℍ) L ↔ HasSum f r L :=
  ⟨fun h => by
    simpa only using!
    h.map (show ℍ ->ₗ[Real] Real from QuaternionAlgebra.reₗ _ _ _) continuous_re,
    fun h => by simpa only using! h.map (algebraMap Real ℍ) (continuous_algebraMap _ _)⟩

@[simp, norm_cast]
/--
theorem `summable_coe` / 定理 `summable_coe`

English:
theorem summable_coe
  given: {f : α -> Real}
  statement: (Summable (fun a => (f a : ℍ)) L) ↔ Summable f L
  proof: by
  simpa only using!
    Summable.map_iff_of_leftInverse (algebraMap Real ℍ) (show ℍ ->ₗ[Real] Real from
      QuaternionAlgebra.reₗ _ _ _)
      (continuous_algebraMap _ _) continuous_re re_coe

@[norm_cast]

中文:
定理 summable_coe
  条件: {f : α -> 实数}
  结论: (Summable (fun a => (f a : ℍ)) L) ↔ Summable f L
  证明: by
  simpa only using!
    Summable.map_iff_of_leftInverse (algebraMap Real ℍ) (show ℍ ->ₗ[Real] Real from
      QuaternionAlgebra.reₗ _ _ _)
      (continuous_algebraMap _ _) continuous_re re_coe

@[norm_cast]

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.re, Summable, Summable.map_iff_of_leftInverse, algebraMap, continuous_algebraMap, continuous_re, map_iff_of_leftInverse, re_coe
-/
theorem summable_coe {f : α -> Real} : (Summable (fun a => (f a : ℍ)) L) ↔ Summable f L := by
  simpa only using!
    Summable.map_iff_of_leftInverse (algebraMap Real ℍ) (show ℍ ->ₗ[Real] Real from
      QuaternionAlgebra.reₗ _ _ _)
      (continuous_algebraMap _ _) continuous_re re_coe

@[norm_cast]
/--
theorem `tsum_coe` / 定理 `tsum_coe`

English:
theorem tsum_coe
  given: (f : α -> Real)
  statement: (∑'[L] a, (f a : ℍ)) = ↑(∑'[L] a, f a)
  proof: (Function.LeftInverse.map_tsum f (continuous_algebraMap _ _) continuous_re re_coe).symm

中文:
定理 tsum_coe
  条件: (f : α -> 实数)
  结论: (∑'[L] a, (f a : ℍ)) = ↑(∑'[L] a, f a)
  证明: (Function.LeftInverse.map_tsum f (continuous_algebraMap _ _) continuous_re re_coe).symm

Depends on / 依赖: Function, Function.LeftInverse.map_tsum, LeftInverse, continuous_algebraMap, continuous_re, map_tsum, re_coe
-/
theorem tsum_coe (f : α -> Real) : (∑'[L] a, (f a : ℍ)) = ↑(∑'[L] a, f a) :=
  (Function.LeftInverse.map_tsum f (continuous_algebraMap _ _) continuous_re re_coe).symm

end infinite_sum

end Quaternion
