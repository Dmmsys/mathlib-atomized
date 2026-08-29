/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# The GNS (Gelfand-Naimark-Segal) construction

This file contains the constructions and definitions that produce a ⋆-homomorphism from an arbitrary
C⋆-algebra into the algebra of bounded linear operators on an appropriately constructed Hilbert
space.

## Main results

- `f.PreGNS` : a type synonym of `A` that bundles in a fixed positive linear functional `f` so that
  we can construct an inner product and inner product-induced norm.
- `f.GNS` : the Hilbert space completion of `f.preGNS`.
- `f.gnsNonUnitalStarAlgHom` : The non-unital ⋆-homomorphism from a non-unital `A` into the bounded
  linear operators on `f.GNS`.
- `f.gnsStarAlgHom` : The unital ⋆-homomorphism from a unital `A` into the bounded linear operators
  on `f.GNS`.

## TODO

- Explicitly construct a unit norm cyclic vector ζ such that
  a ↦ ⟨(f.gns(NonUnital)StarAlgHom a) \* ζ, ζ⟩ is a state on `A` for both unital and non-unital
  cases.

-/

@[expose] public section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] (f : A ->ₚ[Complex] Complex)

namespace PositiveLinearMap

set_option linter.unusedVariables false in
/-- The Gelfand─Naimark─Segal (GNS) space constructed from a positive linear functional on a
non-unital C⋆-algebra. This is a type synonym of `A`.

This space is only a pre-inner product space. Its Hilbert space completion is
`PositiveLinearMap.GNS`. -/
@[nolint unusedArguments]
/--
Definition of `PreGNS` / `PreGNS` 的定义

English:
definition PreGNS
  signature: (f : A ->ₚ[Complex] Complex)
  body: A

中文:
定义 PreGNS
  签名: (f : A ->ₚ[复形] 复形)
  定义体: A
-/
def PreGNS (f : A ->ₚ[Complex] Complex) := A

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup f.PreGNS
  body: inferInstanceAs (AddCommGroup A)

中文:
实例 :
  签名: 加法交换群 f.PreGNS
  定义体: inferInstanceAs (AddCommGroup A)

Depends on / 依赖: AddCommGroup
-/
instance : AddCommGroup f.PreGNS := inferInstanceAs (AddCommGroup A)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module Complex f.PreGNS
  body: inferInstanceAs (Module Complex A)

中文:
实例 :
  签名: 模 复形 f.PreGNS
  定义体: inferInstanceAs (Module Complex A)

Depends on / 依赖: Module
-/
instance : Module Complex f.PreGNS := inferInstanceAs (Module Complex A)

/--
Definition of `toPreGNS` / `toPreGNS` 的定义

English:
definition toPreGNS
  signature: : A ≃ₗ[Complex] f.PreGNS
  body: LinearEquiv.refl Complex _

中文:
定义 toPreGNS
  签名: : A ≃ₗ[复形] f.PreGNS
  定义体: LinearEquiv.refl Complex _

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def toPreGNS : A ≃ₗ[Complex] f.PreGNS := LinearEquiv.refl Complex _

/--
Definition of `ofPreGNS` / `ofPreGNS` 的定义

English:
definition ofPreGNS
  signature: : f.PreGNS ≃ₗ[Complex] A
  body: f.toPreGNS.symm

@[simp]

中文:
定义 ofPreGNS
  签名: : f.PreGNS ≃ₗ[复形] A
  定义体: f.toPreGNS.symm

@[simp]

Depends on / 依赖: f.toPreGNS.symm, toPreGNS
-/
def ofPreGNS : f.PreGNS ≃ₗ[Complex] A := f.toPreGNS.symm

@[simp]
/--
lemma `toPreGNS_ofPreGNS` / 引理 `toPreGNS_ofPreGNS`

English:
lemma toPreGNS_ofPreGNS
  given: (a : f.PreGNS)
  statement: f.toPreGNS (f.ofPreGNS a) = a
  proof: rfl

@[simp]

中文:
引理 toPreGNS_ofPreGNS
  条件: (a : f.PreGNS)
  结论: f.toPreGNS (f.ofPreGNS a) = a
  证明: rfl

@[simp]
-/
lemma toPreGNS_ofPreGNS (a : f.PreGNS) : f.toPreGNS (f.ofPreGNS a) = a := rfl

@[simp]
/--
lemma `ofPreGNS_toPreGNS` / 引理 `ofPreGNS_toPreGNS`

English:
lemma ofPreGNS_toPreGNS
  given: (a : A)
  statement: f.ofPreGNS (f.toPreGNS a) = a
  proof: rfl

中文:
引理 ofPreGNS_toPreGNS
  条件: (a : A)
  结论: f.ofPreGNS (f.toPreGNS a) = a
  证明: rfl
-/
lemma ofPreGNS_toPreGNS (a : A) : f.ofPreGNS (f.toPreGNS a) = a := rfl

variable [StarOrderedRing A]

/--
Definition of `preGNSpreInnerProdSpace` / `preGNSpreInnerProdSpace` 的定义

English:
abbreviation preGNSpreInnerProdSpace
  signature: : PreInnerProductSpace.Core Complex f.PreGNS where
  body: f (star (f.ofPreGNS a) * f.ofPreGNS b)
  conj_inner_symm := by simp [← Complex.star_def, ← map_star f]
.1 re_inner_nonneg _ := RCLike.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _))
  add_left _ _ _ := by rw [map_add, star_add, add_mul, map_add]
  smul_left := by simp [smul_mul_assoc]

中文:
缩写 preGNSpreInnerProdSpace
  签名: : PreInnerProduct空间.核 复形 f.PreGNS where
  定义体: f (star (f.ofPreGNS a) * f.ofPreGNS b)
  conj_inner_symm := by simp [← Complex.star_def, ← map_star f]
.1 re_inner_nonneg _ := RCLike.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _))
  add_left _ _ _ := by rw [map_add, star_add, add_mul, map_add]
  smul_left := by simp [smul_mul_assoc]

Depends on / 依赖: f.ofPreGNS, ofPreGNS
-/
noncomputable abbrev preGNSpreInnerProdSpace : PreInnerProductSpace.Core Complex f.PreGNS where
  inner a b := f (star (f.ofPreGNS a) * f.ofPreGNS b)
  conj_inner_symm := by simp [← Complex.star_def, ← map_star f]
.1 re_inner_nonneg _ := RCLike.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _))
  add_left _ _ _ := by rw [map_add, star_add, add_mul, map_add]
  smul_left := by simp [smul_mul_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SeminormedAddCommGroup f.PreGNS
  body: InnerProductSpace.Core.toSeminormedAddCommGroup (c := f.preGNSpreInnerProdSpace)

中文:
实例 :
  签名: SeminormedAddComm群 f.PreGNS
  定义体: InnerProductSpace.Core.toSeminormedAddCommGroup (c := f.preGNSpreInnerProdSpace)

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core.toSeminormedAddCommGroup, f.preGNSpreInnerProdSpace, preGNSpreInnerProdSpace, toSeminormedAddCommGroup
-/
noncomputable instance : SeminormedAddCommGroup f.PreGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := f.preGNSpreInnerProdSpace)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InnerProductSpace Complex f.PreGNS
  body: InnerProductSpace.ofCore f.preGNSpreInnerProdSpace

中文:
实例 :
  签名: 内积空间 复形 f.PreGNS
  定义体: InnerProductSpace.ofCore f.preGNSpreInnerProdSpace

Depends on / 依赖: InnerProductSpace, InnerProductSpace.ofCore, f.preGNSpreInnerProdSpace, ofCore, preGNSpreInnerProdSpace
-/
noncomputable instance : InnerProductSpace Complex f.PreGNS :=
  InnerProductSpace.ofCore f.preGNSpreInnerProdSpace

/--
lemma `preGNS_inner_def` / 引理 `preGNS_inner_def`

English:
lemma preGNS_inner_def
  given: (a b : f.PreGNS)
  proof: rfl

中文:
引理 preGNS_inner_def
  条件: (a b : f.PreGNS)
  证明: rfl
-/
lemma preGNS_inner_def (a b : f.PreGNS) :
    ⟪a, b⟫_Complex = f (star (f.ofPreGNS a) * f.ofPreGNS b) := rfl

/--
lemma `preGNS_norm_def` / 引理 `preGNS_norm_def`

English:
lemma preGNS_norm_def
  given: (a : f.PreGNS)
  proof: rfl

中文:
引理 preGNS_norm_def
  条件: (a : f.PreGNS)
  证明: rfl
-/
lemma preGNS_norm_def (a : f.PreGNS) :
    ‖a‖ = √(f (star (f.ofPreGNS a) * f.ofPreGNS a)).re := rfl

/--
lemma `preGNS_norm_sq` / 引理 `preGNS_norm_sq`

English:
lemma preGNS_norm_sq
  given: (a : f.PreGNS)
  proof: by
  have : 0 <= f (star (f.ofPreGNS a) * f.ofPreGNS a) := f.map_nonneg (star_mul_self_nonneg _)
  simp [preGNS_norm_def, ← ofReal_pow, Real.sq_sqrt this.1, conj_eq_iff_re.mp this.star_eq]

中文:
引理 preGNS_norm_sq
  条件: (a : f.PreGNS)
  证明: by
  have : 0 <= f (star (f.ofPreGNS a) * f.ofPreGNS a) := f.map_nonneg (star_mul_self_nonneg _)
  simp [preGNS_norm_def, ← ofReal_pow, Real.sq_sqrt this.1, conj_eq_iff_re.mp this.star_eq]

Depends on / 依赖: Real.sq_sqrt, conj_eq_iff_re, conj_eq_iff_re.mp, f.map_nonneg, f.ofPreGNS, map_nonneg, ofPreGNS, ofReal_pow, preGNS_norm_def, sq_sqrt, star_eq, star_mul_self_nonneg, this.star_eq
-/
lemma preGNS_norm_sq (a : f.PreGNS) :
    ‖a‖ ^ 2 = f (star (f.ofPreGNS a) * f.ofPreGNS a) := by
  have : 0 <= f (star (f.ofPreGNS a) * f.ofPreGNS a) := f.map_nonneg (star_mul_self_nonneg _)
  simp [preGNS_norm_def, ← ofReal_pow, Real.sq_sqrt this.1, conj_eq_iff_re.mp this.star_eq]

/--
Definition of `GNS` / `GNS` 的定义

English:
abbreviation GNS
  body: UniformSpace.Completion f.PreGNS

中文:
缩写 GNS
  定义体: UniformSpace.Completion f.PreGNS

Depends on / 依赖: Completion, PreGNS, UniformSpace, UniformSpace.Completion, f.PreGNS
-/
abbrev GNS := UniformSpace.Completion f.PreGNS

/--
The continuous linear map from a C⋆-algebra `A` to the `PositiveLinearMap.preGNS` space induced by
a positive linear functional `f : A →ₚ[ℂ] ℂ`. This map is given by left-multiplication by `a`:
`x ↦ f.toPreGNS (a * f.ofPreGNS x)`.

This is the map that is lifted to the completion of `f.PreGNS` (i.e. `f.GNS`) in order to define
`gnsNonUnitalStarAlgHom`.
-/
@[simps!]
/--
Definition of `leftMulMapPreGNS` / `leftMulMapPreGNS` 的定义

English:
definition leftMulMapPreGNS
  signature: (a : A)
  body: .mkContinuous ‖a‖ fun x => by f.toPreGNS.toLinearMap ∘ₗ mul Complex A a ∘ₗ f.ofPreGNS.toLinearMap
    rw [← sq_le_sq₀ (by positivity) (by positivity)]; rw [mul_pow]; rw [← RCLike.ofReal_le_ofReal (K := Complex)]; rw [RCLike.ofReal_pow]; rw [RCLike.ofReal_eq_complex_ofReal]; rw [preGNS_norm_sq]
    h

中文:
定义 leftMulMapPreGNS
  签名: (a : A)
  定义体: .mkContinuous ‖a‖ fun x => by f.toPreGNS.toLinearMap ∘ₗ mul Complex A a ∘ₗ f.ofPreGNS.toLinearMap
    rw [← sq_le_sq₀ (by positivity) (by positivity)]; rw [mul_pow]; rw [← RCLike.ofReal_le_ofReal (K := Complex)]; rw [RCLike.ofReal_pow]; rw [RCLike.ofReal_eq_complex_ofReal]; rw [preGNS_norm_sq]
    h

Depends on / 依赖: CStarRing, CStarRing.norm_star_mul_self, RCLike, RCLike.ofReal_eq_complex_ofReal, RCLike.ofReal_le_ofReal, RCLike.ofReal_pow, f.ofPreGNS, f.ofPreGNS.toLinearMap, f.toPreGNS.toLinearMap, mkContinuous, mul_assoc, mul_pow, norm_star_mul_self, ofPreGNS, ofReal_eq_complex_ofReal, ofReal_le_ofReal, ofReal_pow, preGNS_norm_sq, toLinearMap, toPreGNS
-/
noncomputable def leftMulMapPreGNS (a : A) : f.PreGNS ->L[Complex] f.PreGNS :=
.mkContinuous ‖a‖ fun x => by f.toPreGNS.toLinearMap ∘ₗ mul Complex A a ∘ₗ f.ofPreGNS.toLinearMap
    rw [← sq_le_sq₀ (by positivity) (by positivity)]; rw [mul_pow]; rw [← RCLike.ofReal_le_ofReal (K := Complex)]; rw [RCLike.ofReal_pow]; rw [RCLike.ofReal_eq_complex_ofReal]; rw [preGNS_norm_sq]
    have : star (f.ofPreGNS x) * star a * (a * f.ofPreGNS x) <=
        ‖a‖ ^ 2 • star (f.ofPreGNS x) * f.ofPreGNS x := by
      rw [← mul_assoc]; rw [mul_assoc _ (star a)]; rw [sq]; rw [← CStarRing.norm_star_mul_self (x := a)]; rw [smul_mul_assoc]
      exact CStarAlgebra.star_left_conjugate_le_norm_smul
    calc
      _ <= f (‖a‖ ^ 2 • star (f.ofPreGNS x) * f.ofPreGNS x) := by
        simpa using OrderHomClass.mono f this
      _ = _ := by simp [← Complex.coe_smul, preGNS_norm_sq, smul_mul_assoc]

@[simp]
/--
lemma `leftMulMapPreGNS_mul_eq_comp` / 引理 `leftMulMapPreGNS_mul_eq_comp`

English:
lemma leftMulMapPreGNS_mul_eq_comp
  given: (a b : A)
  proof: by
  ext c; simp [mul_assoc]

中文:
引理 leftMulMapPreGNS_mul_eq_comp
  条件: (a b : A)
  证明: by
  ext c; simp [mul_assoc]

Depends on / 依赖: mul_assoc
-/
lemma leftMulMapPreGNS_mul_eq_comp (a b : A) :
    f.leftMulMapPreGNS (a * b) = f.leftMulMapPreGNS a ∘L f.leftMulMapPreGNS b := by
  ext c; simp [mul_assoc]

/--
This proves map_smul' of gnsNonUnitalStarAlgHom so that map_zero' can be proven as a direct
consequence.
-/
@[simp]
/--
lemma `completion_leftMulMapPreGNS_map_smul` / 引理 `completion_leftMulMapPreGNS_map_smul`

English:
lemma completion_leftMulMapPreGNS_map_smul
  given: (m : Complex) (x : A)
  proof: by
  ext a
  induction a using induction_on with
  | hp =>
    exact isClosed_eq (f.leftMulMapPreGNS (m • x)).completion.continuous
      (m • (f.leftMulMapPreGNS x).completion).continuous
  | ih a => simp [smul_mul_assoc]

中文:
引理 completion_leftMulMapPreGNS_map_smul
  条件: (m : 复形) (x : A)
  证明: by
  ext a
  induction a using induction_on with
  | hp =>
    exact isClosed_eq (f.leftMulMapPreGNS (m • x)).completion.continuous
      (m • (f.leftMulMapPreGNS x).completion).continuous
  | ih a => simp [smul_mul_assoc]
-/
private lemma completion_leftMulMapPreGNS_map_smul (m : Complex) (x : A) :
    (f.leftMulMapPreGNS (m • x)).completion = m • (f.leftMulMapPreGNS x).completion := by
  ext a
  induction a using induction_on with
  | hp =>
    exact isClosed_eq (f.leftMulMapPreGNS (m • x)).completion.continuous
      (m • (f.leftMulMapPreGNS x).completion).continuous
  | ih a => simp [smul_mul_assoc]

/--
Definition of `gnsNonUnitalStarAlgHom` / `gnsNonUnitalStarAlgHom` 的定义

English:
definition gnsNonUnitalStarAlgHom
  signature: : A ->⋆ₙₐ[Complex] (f.GNS ->L[Complex] f.GNS) where
  body: (f.leftMulMapPreGNS a).completion
  map_smul' := by simp
  map_zero' := by simpa using f.completion_leftMulMapPreGNS_map_smul 0 0
  map_add' _ _ := by
    ext c
    induction c using induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c => simp [add_mul, Completion.coe_add]
  m

中文:
定义 gnsNonUnitalStarAlgHom
  签名: : A ->⋆ₙₐ[复形] (f.GNS ->L[复形] f.GNS) where
  定义体: (f.leftMulMapPreGNS a).completion
  map_smul' := by simp
  map_zero' := by simpa using f.completion_leftMulMapPreGNS_map_smul 0 0
  map_add' _ _ := by
    ext c
    induction c using induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c => simp [add_mul, Completion.coe_add]
  m

Depends on / 依赖: completion, f.leftMulMapPreGNS, leftMulMapPreGNS
-/
noncomputable def gnsNonUnitalStarAlgHom : A ->⋆ₙₐ[Complex] (f.GNS ->L[Complex] f.GNS) where
  toFun a := (f.leftMulMapPreGNS a).completion
  map_smul' := by simp
  map_zero' := by simpa using f.completion_leftMulMapPreGNS_map_smul 0 0
  map_add' _ _ := by
    ext c
    induction c using induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c => simp [add_mul, Completion.coe_add]
  map_mul' _ _ := by
    ext c
    induction c using induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c => simp
  map_star' a := by
    refine (eq_adjoint_iff (f.leftMulMapPreGNS (star a)).completion
      (f.leftMulMapPreGNS a).completion).mpr ?_
    intro x y
    induction x, y using induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x y => simp [mul_assoc, preGNS_inner_def]

/--
lemma `gnsNonUnitalStarAlgHom_apply` / 引理 `gnsNonUnitalStarAlgHom_apply`

English:
lemma gnsNonUnitalStarAlgHom_apply
  given: {a : A}
  proof: rfl

@[simp]

中文:
引理 gnsNonUnitalStarAlgHom_apply
  条件: {a : A}
  证明: rfl

@[simp]
-/
lemma gnsNonUnitalStarAlgHom_apply {a : A} :
    f.gnsNonUnitalStarAlgHom a = (f.leftMulMapPreGNS a).completion := rfl

@[simp]
/--
lemma `gnsNonUnitalStarAlgHom_apply_coe` / 引理 `gnsNonUnitalStarAlgHom_apply_coe`

English:
lemma gnsNonUnitalStarAlgHom_apply_coe
  given: {a : A} {b : f.PreGNS}
  proof: by
  simp [gnsNonUnitalStarAlgHom_apply]

中文:
引理 gnsNonUnitalStarAlgHom_apply_coe
  条件: {a : A} {b : f.PreGNS}
  证明: by
  simp [gnsNonUnitalStarAlgHom_apply]

Depends on / 依赖: Unitization, WithLp, WithLp.equiv, algebra, gnsNonUnitalStarAlgHom_apply
-/
lemma gnsNonUnitalStarAlgHom_apply_coe {a : A} {b : f.PreGNS} :
    f.gnsNonUnitalStarAlgHom a b = f.leftMulMapPreGNS a b := by
  simp [gnsNonUnitalStarAlgHom_apply]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A ->ₚ[Complex] Complex)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `gnsNonUnitalStarAlgHom_map_one` / 引理 `gnsNonUnitalStarAlgHom_map_one`

English:
lemma gnsNonUnitalStarAlgHom_map_one
  statement: f.gnsNonUnitalStarAlgHom 1 = 1
  proof: by
  ext b
  induction b using induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih b => simp [gnsNonUnitalStarAlgHom]

中文:
引理 gnsNonUnitalStarAlgHom_map_one
  结论: f.gnsNonUnitalStarAlgHom 1 = 1
  证明: by
  ext b
  induction b using induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih b => simp [gnsNonUnitalStarAlgHom]
-/
private lemma gnsNonUnitalStarAlgHom_map_one : f.gnsNonUnitalStarAlgHom 1 = 1 := by
  ext b
  induction b using induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih b => simp [gnsNonUnitalStarAlgHom]

/--
The unital ⋆-homomorphism/⋆-representation of `A` into the algebra of bounded operators on a Hilbert
space that is constructed from a positive linear functional `f` on a unital C⋆-algebra.

This is the unital version of `gnsNonUnitalStarAlgHom`.
-/
@[simps]
/--
Definition of `gnsStarAlgHom` / `gnsStarAlgHom` 的定义

English:
definition gnsStarAlgHom
  signature: : A ->⋆ₐ[Complex] (f.GNS ->L[Complex] f.GNS) where
  body: f.gnsNonUnitalStarAlgHom
  map_one' := by simp
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

中文:
定义 gnsStarAlgHom
  签名: : A ->⋆ₐ[复形] (f.GNS ->L[复形] f.GNS) where
  定义体: f.gnsNonUnitalStarAlgHom
  map_one' := by simp
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

Depends on / 依赖: f.gnsNonUnitalStarAlgHom, gnsNonUnitalStarAlgHom
-/
noncomputable def gnsStarAlgHom : A ->⋆ₐ[Complex] (f.GNS ->L[Complex] f.GNS) where
  __ := f.gnsNonUnitalStarAlgHom
  map_one' := by simp
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

end PositiveLinearMap
