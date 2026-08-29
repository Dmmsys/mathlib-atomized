/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.External
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Tactic.SuppressCompilation

/-!
# Graded tensor products over graded algebras

The graded tensor product $A \hat\otimes_R B$ is imbued with a multiplication defined on homogeneous
tensors by:

$$(a \otimes b) \cdot (a' \otimes b') = (-1)^{\deg a' \deg b} (a \cdot a') \otimes (b \cdot b')$$

where $A$ and $B$ are algebras graded by `ℕ`, `ℤ`, or `ι` (or more generally, any index
that satisfies `Module ι (Additive ℤˣ)`).

## Main results

* `GradedTensorProduct R 𝒜 ℬ`: for families of submodules of `A` and `B` that form a graded algebra,
  this is a type alias for `A ⊗[R] B` with the appropriate multiplication.
* `GradedTensorProduct.instAlgebra`: the ring structure induced by this multiplication.
* `GradedTensorProduct.liftEquiv`: a universal property for graded tensor products

## Notation

* `𝒜 ᵍ⊗[R] ℬ` is notation for `GradedTensorProduct R 𝒜 ℬ`.
* `a ᵍ⊗ₜ b` is notation for `GradedTensorProduct.tmul _ a b`.

## References

* https://math.stackexchange.com/q/202718/1896
* [*Algebra I*, Bourbaki : Chapter III, §4.7, example (2)][bourbaki1989]

## Implementation notes

We cannot put the multiplication on `A ⊗[R] B` directly as it would conflict with the existing
multiplication defined without the $(-1)^{\deg a' \deg b}$ term. Furthermore, the ring `A` may not
have a unique graduation, and so we need the chosen graduation `𝒜` to appear explicitly in the
type.

## TODO

* Show that the tensor product of graded algebras is itself a graded algebra.
* Determine if replacing the synonym with a single-field structure improves performance.
-/

@[expose] public section

suppress_compilation

open scoped TensorProduct

variable {R ι A B : Type*}
variable [CommSemiring ι] [DecidableEq ι]
variable [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable (𝒜 : ι -> Submodule R A) (ℬ : ι -> Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

open DirectSum


variable (R) in
/-- A Type synonym for `A ⊗[R] B`, but with multiplication as `TensorProduct.gradedMul`.

This has notation `𝒜 ᵍ⊗[R] ℬ`. -/
@[nolint unusedArguments]
/--
Definition of `GradedTensorProduct` / `GradedTensorProduct` 的定义

English:
definition GradedTensorProduct
  body: A otimes[R] B
deriving AddCommGroupWithOne, Module R

中文:
定义 GradedTensorProduct
  定义体: A otimes[R] B
deriving AddCommGroupWithOne, Module R

Depends on / 依赖: otimes
-/
def GradedTensorProduct
    (𝒜 : ι -> Submodule R A) (ℬ : ι -> Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] :
    Type _ :=
  A otimes[R] B
deriving AddCommGroupWithOne, Module R

namespace GradedTensorProduct

open TensorProduct

@[inherit_doc GradedTensorProduct]
scoped[TensorProduct] notation:100 𝒜 " ᵍotimes[" R "] " ℬ:100 => GradedTensorProduct R 𝒜 ℬ

variable (R) in
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : A otimes[R] B ≃ₗ[R] 𝒜 ᵍotimes[R] ℬ
  body: LinearEquiv.refl _ _

@[simp]

中文:
定义 of
  签名: : A otimes[R] B ≃ₗ[R] 𝒜 ᵍotimes[R] ℬ
  定义体: LinearEquiv.refl _ _

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def of : A otimes[R] B ≃ₗ[R] 𝒜 ᵍotimes[R] ℬ := LinearEquiv.refl _ _

@[simp]
/--
theorem `of_one` / 定理 `of_one`

English:
theorem of_one
  statement: of R 𝒜 ℬ 1 = 1
  proof: rfl

@[simp]

中文:
定理 of_one
  结论: of R 𝒜 ℬ 1 = 1
  证明: rfl

@[simp]
-/
theorem of_one : of R 𝒜 ℬ 1 = 1 := rfl

@[simp]
/--
theorem `of_symm_one` / 定理 `of_symm_one`

English:
theorem of_symm_one
  statement: (of R 𝒜 ℬ).symm 1 = 1
  proof: rfl

@[simp]

中文:
定理 of_symm_one
  结论: (of R 𝒜 ℬ).symm 1 = 1
  证明: rfl

@[simp]
-/
theorem of_symm_one : (of R 𝒜 ℬ).symm 1 = 1 := rfl

@[simp]
/--
theorem `of_symm_of` / 定理 `of_symm_of`

English:
theorem of_symm_of
  given: (x : A otimes[R] B)
  statement: (of R 𝒜 ℬ).symm (of R 𝒜 ℬ x) = x
  proof: rfl

@[simp]

中文:
定理 of_symm_of
  条件: (x : A otimes[R] B)
  结论: (of R 𝒜 ℬ).symm (of R 𝒜 ℬ x) = x
  证明: rfl

@[simp]
-/
theorem of_symm_of (x : A otimes[R] B) : (of R 𝒜 ℬ).symm (of R 𝒜 ℬ x) = x := rfl

@[simp]
/--
theorem `symm_of_of` / 定理 `symm_of_of`

English:
theorem symm_of_of
  given: (x : 𝒜 ᵍotimes[R] ℬ)
  statement: of R 𝒜 ℬ ((of R 𝒜 ℬ).symm x) = x
  proof: rfl

中文:
定理 symm_of_of
  条件: (x : 𝒜 ᵍotimes[R] ℬ)
  结论: of R 𝒜 ℬ ((of R 𝒜 ℬ).symm x) = x
  证明: rfl
-/
theorem symm_of_of (x : 𝒜 ᵍotimes[R] ℬ) : of R 𝒜 ℬ ((of R 𝒜 ℬ).symm x) = x := rfl

/-- Two linear maps from the graded tensor product agree if they agree on the underlying tensor
product. -/
@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {M} [AddCommMonoid M] [Module R M] ⦃f g
  statement: 𝒜 ᵍotimes[R] ℬ ->ₗ[R] M⦄
  proof: h

中文:
定理 hom_ext
  条件: {M} [加法交换幺半群 M] [模 R M] ⦃f g
  结论: 𝒜 ᵍotimes[R] ℬ ->ₗ[R] M⦄
  证明: h
-/
theorem hom_ext {M} [AddCommMonoid M] [Module R M] ⦃f g : 𝒜 ᵍotimes[R] ℬ ->ₗ[R] M⦄
    (h : f ∘ₗ of R 𝒜 ℬ = (g ∘ₗ of R 𝒜 ℬ : A otimes[R] B ->ₗ[R] M)) :
    f = g :=
  h

variable (R) {𝒜 ℬ} in
/--
Definition of `tmul` / `tmul` 的定义

English:
abbreviation tmul
  signature: (a : A) (b : B)
  body: of R 𝒜 ℬ (a otimesₜ b)

@[inherit_doc]
notation:100 x " ᵍotimesₜ " y:100 => tmul _ x y

@[inherit_doc]
notation:100 x " ᵍotimesₜ[" R "] " y:100 => tmul R x y

中文:
缩写 tmul
  签名: (a : A) (b : B)
  定义体: of R 𝒜 ℬ (a otimesₜ b)

@[inherit_doc]
notation:100 x " ᵍotimesₜ " y:100 => tmul _ x y

@[inherit_doc]
notation:100 x " ᵍotimesₜ[" R "] " y:100 => tmul R x y
-/
abbrev tmul (a : A) (b : B) : 𝒜 ᵍotimes[R] ℬ := of R 𝒜 ℬ (a otimesₜ b)

@[inherit_doc]
notation:100 x " ᵍotimesₜ " y:100 => tmul _ x y

@[inherit_doc]
notation:100 x " ᵍotimesₜ[" R "] " y:100 => tmul R x y

variable (R) in
/--
Definition of `auxEquiv` / `auxEquiv` 的定义

English:
definition auxEquiv
  signature: : (𝒜 ᵍotimes[R] ℬ) ≃ₗ[R] (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)
  body: let fA := (decomposeAlgEquiv 𝒜).toLinearEquiv
  let fB := (decomposeAlgEquiv ℬ).toLinearEquiv
  (of R 𝒜 ℬ).symm.trans (TensorProduct.congr fA fB)

中文:
定义 auxEquiv
  签名: : (𝒜 ᵍotimes[R] ℬ) ≃ₗ[R] (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)
  定义体: let fA := (decomposeAlgEquiv 𝒜).toLinearEquiv
  let fB := (decomposeAlgEquiv ℬ).toLinearEquiv
  (of R 𝒜 ℬ).symm.trans (TensorProduct.congr fA fB)

Depends on / 依赖: TensorProduct, TensorProduct.congr, decomposeAlgEquiv, symm.trans, toLinearEquiv
-/
noncomputable def auxEquiv : (𝒜 ᵍotimes[R] ℬ) ≃ₗ[R] (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i) :=
  let fA := (decomposeAlgEquiv 𝒜).toLinearEquiv
  let fB := (decomposeAlgEquiv ℬ).toLinearEquiv
  (of R 𝒜 ℬ).symm.trans (TensorProduct.congr fA fB)

/--
theorem `auxEquiv_tmul` / 定理 `auxEquiv_tmul`

English:
theorem auxEquiv_tmul
  given: (a : A) (b : B)
  proof: rfl

中文:
定理 auxEquiv_tmul
  条件: (a : A) (b : B)
  证明: rfl
-/
theorem auxEquiv_tmul (a : A) (b : B) :
    auxEquiv R 𝒜 ℬ (a ᵍotimesₜ b) = decompose 𝒜 a otimesₜ decompose ℬ b := rfl

/--
theorem `auxEquiv_one` / 定理 `auxEquiv_one`

English:
theorem auxEquiv_one
  statement: auxEquiv R 𝒜 ℬ 1 = 1
  proof: by
  rw [← of_one]; rw [Algebra.TensorProduct.one_def]; rw [auxEquiv_tmul 𝒜 ℬ]; rw [DirectSum.decompose_one]; rw [DirectSum.decompose_one]; rw [Algebra.TensorProduct.one_def]

中文:
定理 auxEquiv_one
  结论: auxEquiv R 𝒜 ℬ 1 = 1
  证明: by
  rw [← of_one]; rw [Algebra.TensorProduct.one_def]; rw [auxEquiv_tmul 𝒜 ℬ]; rw [DirectSum.decompose_one]; rw [DirectSum.decompose_one]; rw [Algebra.TensorProduct.one_def]

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_def, DirectSum, DirectSum.decompose_one, TensorProduct, auxEquiv_tmul, decompose_one, of_one, one_def
-/
theorem auxEquiv_one : auxEquiv R 𝒜 ℬ 1 = 1 := by
  rw [← of_one]; rw [Algebra.TensorProduct.one_def]; rw [auxEquiv_tmul 𝒜 ℬ]; rw [DirectSum.decompose_one]; rw [DirectSum.decompose_one]; rw [Algebra.TensorProduct.one_def]

/--
theorem `auxEquiv_symm_one` / 定理 `auxEquiv_symm_one`

English:
theorem auxEquiv_symm_one
  statement: (auxEquiv R 𝒜 ℬ).symm 1 = 1
  proof: (LinearEquiv.symm_apply_eq _).mpr (auxEquiv_one _ _).symm

中文:
定理 auxEquiv_symm_one
  结论: (auxEquiv R 𝒜 ℬ).symm 1 = 1
  证明: (LinearEquiv.symm_apply_eq _).mpr (auxEquiv_one _ _).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, auxEquiv_one, symm_apply_eq
-/
theorem auxEquiv_symm_one : (auxEquiv R 𝒜 ℬ).symm 1 = 1 :=
  (LinearEquiv.symm_apply_eq _).mpr (auxEquiv_one _ _).symm

variable [Module ι (Additive Intˣ)]

/--
Definition of `mulHom` / `mulHom` 的定义

English:
definition mulHom
  signature: : (𝒜 ᵍotimes[R] ℬ) ->ₗ[R] (𝒜 ᵍotimes[R] ℬ) ->ₗ[R] (𝒜 ᵍotimes[R] ℬ)
  body: by
  letI fAB1 := auxEquiv R 𝒜 ℬ
  have := ((gradedMul R (𝒜 ·) (ℬ ·)).compl₁₂ fAB1.toLinearMap fAB1.toLinearMap).compr₂
    fAB1.symm.toLinearMap
  exact this

中文:
定义 mulHom
  签名: : (𝒜 ᵍotimes[R] ℬ) ->ₗ[R] (𝒜 ᵍotimes[R] ℬ) ->ₗ[R] (𝒜 ᵍotimes[R] ℬ)
  定义体: by
  letI fAB1 := auxEquiv R 𝒜 ℬ
  have := ((gradedMul R (𝒜 ·) (ℬ ·)).compl₁₂ fAB1.toLinearMap fAB1.toLinearMap).compr₂
    fAB1.symm.toLinearMap
  exact this

Depends on / 依赖: auxEquiv, fAB1.symm.toLinearMap, fAB1.toLinearMap, gradedMul, toLinearMap
-/
noncomputable def mulHom : (𝒜 ᵍotimes[R] ℬ) ->ₗ[R] (𝒜 ᵍotimes[R] ℬ) ->ₗ[R] (𝒜 ᵍotimes[R] ℬ) := by
  letI fAB1 := auxEquiv R 𝒜 ℬ
  have := ((gradedMul R (𝒜 ·) (ℬ ·)).compl₁₂ fAB1.toLinearMap fAB1.toLinearMap).compr₂
    fAB1.symm.toLinearMap
  exact this

/--
theorem `mulHom_apply` / 定理 `mulHom_apply`

English:
theorem mulHom_apply
  given: (x y : 𝒜 ᵍotimes[R] ℬ)
  proof: rfl

中文:
定理 mulHom_apply
  条件: (x y : 𝒜 ᵍotimes[R] ℬ)
  证明: rfl
-/
theorem mulHom_apply (x y : 𝒜 ᵍotimes[R] ℬ) :
    mulHom 𝒜 ℬ x y
      = (auxEquiv R 𝒜 ℬ).symm (gradedMul R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) (auxEquiv R 𝒜 ℬ y)) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (𝒜 ᵍotimes[R] ℬ)
  body: mulHom 𝒜 ℬ x y

中文:
实例 :
  签名: 乘法 (𝒜 ᵍotimes[R] ℬ)
  定义体: mulHom 𝒜 ℬ x y

Depends on / 依赖: mulHom
-/
instance : Mul (𝒜 ᵍotimes[R] ℬ) where mul x y := mulHom 𝒜 ℬ x y

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (x y : 𝒜 ᵍotimes[R] ℬ)
  statement: x * y = mulHom 𝒜 ℬ x y
  proof: rfl

中文:
定理 mul_def
  条件: (x y : 𝒜 ᵍotimes[R] ℬ)
  结论: x * y = mulHom 𝒜 ℬ x y
  证明: rfl
-/
theorem mul_def (x y : 𝒜 ᵍotimes[R] ℬ) : x * y = mulHom 𝒜 ℬ x y := rfl

-- Before https://github.com/leanprover-community/mathlib4/pull/8386 this was `@[simp]` but it times out when we try to apply it.
/--
theorem `auxEquiv_mul` / 定理 `auxEquiv_mul`

English:
theorem auxEquiv_mul
  given: (x y : 𝒜 ᵍotimes[R] ℬ)
  proof: .mp rfl LinearEquiv.eq_symm_apply _

中文:
定理 auxEquiv_mul
  条件: (x y : 𝒜 ᵍotimes[R] ℬ)
  证明: .mp rfl LinearEquiv.eq_symm_apply _

Depends on / 依赖: LinearEquiv, LinearEquiv.eq_symm_apply, eq_symm_apply
-/
theorem auxEquiv_mul (x y : 𝒜 ᵍotimes[R] ℬ) :
    auxEquiv R 𝒜 ℬ (x * y) = gradedMul R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) (auxEquiv R 𝒜 ℬ y) :=
.mp rfl LinearEquiv.eq_symm_apply _

/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (𝒜 ᵍotimes[R] ℬ) where
  body: by
    rw [mul_def]; rw [mulHom_apply]; rw [auxEquiv_one]; rw [gradedMul_one]; rw [LinearEquiv.symm_apply_apply]
  one_mul x := by
    rw [mul_def]; rw [mulHom_apply]; rw [auxEquiv_one]; rw [one_gradedMul]; rw [LinearEquiv.symm_apply_apply]
  mul_assoc x y z := by
    simp_rw [mul_def, mulHom_apply,

中文:
实例 instMonoid
  签名: : 幺半群 (𝒜 ᵍotimes[R] ℬ) where
  定义体: by
    rw [mul_def]; rw [mulHom_apply]; rw [auxEquiv_one]; rw [gradedMul_one]; rw [LinearEquiv.symm_apply_apply]
  one_mul x := by
    rw [mul_def]; rw [mulHom_apply]; rw [auxEquiv_one]; rw [one_gradedMul]; rw [LinearEquiv.symm_apply_apply]
  mul_assoc x y z := by
    simp_rw [mul_def, mulHom_apply,

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, apply_symm_apply, auxEquiv_one, gradedMul_assoc, gradedMul_one, mulHom_apply, mul_assoc, mul_def, one_gradedMul, one_mul, simp_rw, symm_apply_apply
-/
instance instMonoid : Monoid (𝒜 ᵍotimes[R] ℬ) where
  mul_one x := by
    rw [mul_def]; rw [mulHom_apply]; rw [auxEquiv_one]; rw [gradedMul_one]; rw [LinearEquiv.symm_apply_apply]
  one_mul x := by
    rw [mul_def]; rw [mulHom_apply]; rw [auxEquiv_one]; rw [one_gradedMul]; rw [LinearEquiv.symm_apply_apply]
  mul_assoc x y z := by
    simp_rw [mul_def, mulHom_apply, LinearEquiv.apply_symm_apply]
    rw [gradedMul_assoc]

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring (𝒜 ᵍotimes[R] ℬ) where
  body: by simp_rw [mul_def, LinearMap.map_add₂]
  left_distrib x y z := by simp_rw [mul_def, map_add]
  mul_zero x := by simp_rw [mul_def, map_zero]
  zero_mul x := by simp_rw [mul_def, LinearMap.map_zero₂]

中文:
实例 instRing
  签名: : 环 (𝒜 ᵍotimes[R] ℬ) where
  定义体: by simp_rw [mul_def, LinearMap.map_add₂]
  left_distrib x y z := by simp_rw [mul_def, map_add]
  mul_zero x := by simp_rw [mul_def, map_zero]
  zero_mul x := by simp_rw [mul_def, LinearMap.map_zero₂]

Depends on / 依赖: LinearMap, LinearMap.map_add, LinearMap.map_zero, left_distrib, map_add, map_zero, mul_def, mul_zero, simp_rw, zero_mul
-/
instance instRing : Ring (𝒜 ᵍotimes[R] ℬ) where
  right_distrib x y z := by simp_rw [mul_def, LinearMap.map_add₂]
  left_distrib x y z := by simp_rw [mul_def, map_add]
  mul_zero x := by simp_rw [mul_def, map_zero]
  zero_mul x := by simp_rw [mul_def, LinearMap.map_zero₂]

/--
theorem `tmul_coe_mul_coe_tmul` / 定理 `tmul_coe_mul_coe_tmul`

English:
theorem tmul_coe_mul_coe_tmul
  given: {j₁ i₂ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : B)
  proof: by
  dsimp only [mul_def, mulHom_apply, of_symm_of]
  dsimp [auxEquiv, tmul]
  rw [decompose_coe]; rw [decompose_coe]
  simp_rw [← lof_eq_of R]
  rw [tmul_of_gradedMul_of_tmul]
  simp_rw [lof_eq_of R]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_smul` 

中文:
定理 tmul_coe_mul_coe_tmul
  条件: {j₁ i₂ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : B)
  证明: by
  dsimp only [mul_def, mulHom_apply, of_symm_of]
  dsimp [auxEquiv, tmul]
  rw [decompose_coe]; rw [decompose_coe]
  simp_rw [← lof_eq_of R]
  rw [tmul_of_gradedMul_of_tmul]
  simp_rw [lof_eq_of R]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_smul` 

Depends on / 依赖: auxEquiv, decompose_coe, lof_eq_of, mulHom_apply, mul_def, of_symm_of, simp_rw, tmul_of_gradedMul_of_tmul
-/
theorem tmul_coe_mul_coe_tmul {j₁ i₂ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍotimesₜ[R] (b₁ : B) * (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) =
      (-1 : Intˣ) ^ (j₁ * i₂) • ((a₁ * a₂ : A) ᵍotimesₜ (b₁ * b₂ : B)) := by
  dsimp only [mul_def, mulHom_apply, of_symm_of]
  dsimp [auxEquiv, tmul]
  rw [decompose_coe]; rw [decompose_coe]
  simp_rw [← lof_eq_of R]
  rw [tmul_of_gradedMul_of_tmul]
  simp_rw [lof_eq_of R]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_smul` to `LinearEquiv.map_smul`
  rw [@Units.smul_def _ _ (_) (_)]; rw [← Int.cast_smul_eq_zsmul R]; rw [LinearEquiv.map_smul]; rw [map_smul]; rw [Int.cast_smul_eq_zsmul R]; rw [← @Units.smul_def _ _ (_) (_)]
  rw [congr_symm_tmul]
  dsimp
  simp_rw [decompose_symm_mul, decompose_symm_of, Equiv.symm_apply_apply]

/--
theorem `tmul_zero_coe_mul_coe_tmul` / 定理 `tmul_zero_coe_mul_coe_tmul`

English:
theorem tmul_zero_coe_mul_coe_tmul
  given: {i₂ : ι} (a₁ : A) (b₁ : ℬ 0) (a₂ : 𝒜 i₂) (b₂ : B)
  proof: by
  rw [tmul_coe_mul_coe_tmul]; rw [zero_mul]; rw [uzpow_zero]; rw [one_smul]

中文:
定理 tmul_zero_coe_mul_coe_tmul
  条件: {i₂ : ι} (a₁ : A) (b₁ : ℬ 0) (a₂ : 𝒜 i₂) (b₂ : B)
  证明: by
  rw [tmul_coe_mul_coe_tmul]; rw [zero_mul]; rw [uzpow_zero]; rw [one_smul]

Depends on / 依赖: one_smul, tmul_coe_mul_coe_tmul, uzpow_zero, zero_mul
-/
theorem tmul_zero_coe_mul_coe_tmul {i₂ : ι} (a₁ : A) (b₁ : ℬ 0) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍotimesₜ[R] (b₁ : B) * (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) =
      ((a₁ * a₂ : A) ᵍotimesₜ (b₁ * b₂ : B)) := by
  rw [tmul_coe_mul_coe_tmul]; rw [zero_mul]; rw [uzpow_zero]; rw [one_smul]

/--
theorem `tmul_coe_mul_zero_coe_tmul` / 定理 `tmul_coe_mul_zero_coe_tmul`

English:
theorem tmul_coe_mul_zero_coe_tmul
  given: {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 0) (b₂ : B)
  proof: by
  rw [tmul_coe_mul_coe_tmul]; rw [mul_zero]; rw [uzpow_zero]; rw [one_smul]

中文:
定理 tmul_coe_mul_zero_coe_tmul
  条件: {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 0) (b₂ : B)
  证明: by
  rw [tmul_coe_mul_coe_tmul]; rw [mul_zero]; rw [uzpow_zero]; rw [one_smul]

Depends on / 依赖: mul_zero, one_smul, tmul_coe_mul_coe_tmul, uzpow_zero
-/
theorem tmul_coe_mul_zero_coe_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (a₂ : 𝒜 0) (b₂ : B) :
    (a₁ ᵍotimesₜ[R] (b₁ : B) * (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) =
      ((a₁ * a₂ : A) ᵍotimesₜ (b₁ * b₂ : B)) := by
  rw [tmul_coe_mul_coe_tmul]; rw [mul_zero]; rw [uzpow_zero]; rw [one_smul]

/--
theorem `tmul_one_mul_coe_tmul` / 定理 `tmul_one_mul_coe_tmul`

English:
theorem tmul_one_mul_coe_tmul
  given: {i₂ : ι} (a₁ : A) (a₂ : 𝒜 i₂) (b₂ : B)
  proof: by
  convert! tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (@GradedMonoid.GOne.one _ (ℬ ·) _ _) a₂ b₂
  rw [SetLike.coe_gOne]; rw [one_mul]

中文:
定理 tmul_one_mul_coe_tmul
  条件: {i₂ : ι} (a₁ : A) (a₂ : 𝒜 i₂) (b₂ : B)
  证明: by
  convert! tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (@GradedMonoid.GOne.one _ (ℬ ·) _ _) a₂ b₂
  rw [SetLike.coe_gOne]; rw [one_mul]

Depends on / 依赖: GradedMonoid, GradedMonoid.GOne.one, SetLike, SetLike.coe_gOne, coe_gOne, convert, one_mul, tmul_zero_coe_mul_coe_tmul
-/
theorem tmul_one_mul_coe_tmul {i₂ : ι} (a₁ : A) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍotimesₜ[R] (1 : B) * (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) = (a₁ * a₂ : A) ᵍotimesₜ (b₂ : B) := by
  convert! tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (@GradedMonoid.GOne.one _ (ℬ ·) _ _) a₂ b₂
  rw [SetLike.coe_gOne]; rw [one_mul]

/--
theorem `tmul_coe_mul_one_tmul` / 定理 `tmul_coe_mul_one_tmul`

English:
theorem tmul_coe_mul_one_tmul
  given: {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (b₂ : B)
  proof: by
  convert! tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (@GradedMonoid.GOne.one _ (𝒜 ·) _ _) b₂
  rw [SetLike.coe_gOne]; rw [mul_one]

中文:
定理 tmul_coe_mul_one_tmul
  条件: {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (b₂ : B)
  证明: by
  convert! tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (@GradedMonoid.GOne.one _ (𝒜 ·) _ _) b₂
  rw [SetLike.coe_gOne]; rw [mul_one]

Depends on / 依赖: GradedMonoid, GradedMonoid.GOne.one, SetLike, SetLike.coe_gOne, coe_gOne, convert, mul_one, tmul_coe_mul_zero_coe_tmul
-/
theorem tmul_coe_mul_one_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (b₂ : B) :
    (a₁ ᵍotimesₜ[R] (b₁ : B) * (1 : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) = (a₁ : A) ᵍotimesₜ (b₁ * b₂ : B) := by
  convert! tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (@GradedMonoid.GOne.one _ (𝒜 ·) _ _) b₂
  rw [SetLike.coe_gOne]; rw [mul_one]

/--
theorem `tmul_one_mul_one_tmul` / 定理 `tmul_one_mul_one_tmul`

English:
theorem tmul_one_mul_one_tmul
  given: (a₁ : A) (b₂ : B)
  proof: by
  convert!
    tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ (GradedMonoid.GOne.one (A := (ℬ ·)))
      (GradedMonoid.GOne.one (A := (𝒜 ·))) b₂
  · rw [SetLike.coe_gOne, mul_one]
  · rw [SetLike.coe_gOne, one_mul]

中文:
定理 tmul_one_mul_one_tmul
  条件: (a₁ : A) (b₂ : B)
  证明: by
  convert!
    tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ (GradedMonoid.GOne.one (A := (ℬ ·)))
      (GradedMonoid.GOne.one (A := (𝒜 ·))) b₂
  · rw [SetLike.coe_gOne, mul_one]
  · rw [SetLike.coe_gOne, one_mul]

Depends on / 依赖: GradedMonoid, GradedMonoid.GOne.one, SetLike, SetLike.coe_gOne, coe_gOne, convert, mul_one, one_mul, tmul_coe_mul_zero_coe_tmul
-/
theorem tmul_one_mul_one_tmul (a₁ : A) (b₂ : B) :
    (a₁ ᵍotimesₜ[R] (1 : B) * (1 : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ) = (a₁ : A) ᵍotimesₜ (b₂ : B) := by
  convert!
    tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ (GradedMonoid.GOne.one (A := (ℬ ·)))
      (GradedMonoid.GOne.one (A := (𝒜 ·))) b₂
  · rw [SetLike.coe_gOne, mul_one]
  · rw [SetLike.coe_gOne, one_mul]

/-- The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps]
/--
Definition of `includeLeftRingHom` / `includeLeftRingHom` 的定义

English:
definition includeLeftRingHom
  signature: : A ->+* 𝒜 ᵍotimes[R] ℬ where
  body: a ᵍotimesₜ 1
  map_zero' := by simp
  map_add' := by simp [tmul, TensorProduct.add_tmul]
  map_one' := rfl
  map_mul' a₁ a₂ := by
    classical
    rw [← DirectSum.sum_support_decompose 𝒜 a₂]; rw [Finset.mul_sum]
    simp_rw [tmul, sum_tmul, map_sum, Finset.mul_sum]
    congr
    ext i
    rw [← Set

中文:
定义 includeLeftRingHom
  签名: : A ->+* 𝒜 ᵍotimes[R] ℬ where
  定义体: a ᵍotimesₜ 1
  map_zero' := by simp
  map_add' := by simp [tmul, TensorProduct.add_tmul]
  map_one' := rfl
  map_mul' a₁ a₂ := by
    classical
    rw [← DirectSum.sum_support_decompose 𝒜 a₂]; rw [Finset.mul_sum]
    simp_rw [tmul, sum_tmul, map_sum, Finset.mul_sum]
    congr
    ext i
    rw [← Set
-/
def includeLeftRingHom : A ->+* 𝒜 ᵍotimes[R] ℬ where
  toFun a := a ᵍotimesₜ 1
  map_zero' := by simp
  map_add' := by simp [tmul, TensorProduct.add_tmul]
  map_one' := rfl
  map_mul' a₁ a₂ := by
    classical
    rw [← DirectSum.sum_support_decompose 𝒜 a₂]; rw [Finset.mul_sum]
    simp_rw [tmul, sum_tmul, map_sum, Finset.mul_sum]
    congr
    ext i
    rw [← SetLike.coe_gOne ℬ]; rw [tmul_coe_mul_coe_tmul]; rw [zero_mul]; rw [uzpow_zero]; rw [one_smul]; rw [SetLike.coe_gOne]; rw [one_mul]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: : Algebra R (𝒜 ᵍotimes[R] ℬ) where
  body: (includeLeftRingHom 𝒜 ℬ).comp (algebraMap R A)
  commutes' r x := by
    dsimp [mul_def, mulHom_apply, auxEquiv_tmul]
    simp_rw [DirectSum.decompose_algebraMap, DirectSum.decompose_one, algebraMap_gradedMul,
      gradedMul_algebraMap]
  smul_def' r x := by
    dsimp [mul_def, mulHom_apply, auxEqu

中文:
实例 instAlgebra
  签名: : 代数 R (𝒜 ᵍotimes[R] ℬ) where
  定义体: (includeLeftRingHom 𝒜 ℬ).comp (algebraMap R A)
  commutes' r x := by
    dsimp [mul_def, mulHom_apply, auxEquiv_tmul]
    simp_rw [DirectSum.decompose_algebraMap, DirectSum.decompose_one, algebraMap_gradedMul,
      gradedMul_algebraMap]
  smul_def' r x := by
    dsimp [mul_def, mulHom_apply, auxEqu

Depends on / 依赖: algebraMap, includeLeftRingHom
-/
instance instAlgebra : Algebra R (𝒜 ᵍotimes[R] ℬ) where
  algebraMap := (includeLeftRingHom 𝒜 ℬ).comp (algebraMap R A)
  commutes' r x := by
    dsimp [mul_def, mulHom_apply, auxEquiv_tmul]
    simp_rw [DirectSum.decompose_algebraMap, DirectSum.decompose_one, algebraMap_gradedMul,
      gradedMul_algebraMap]
  smul_def' r x := by
    dsimp [mul_def, mulHom_apply, auxEquiv_tmul]
    simp_rw [DirectSum.decompose_algebraMap, DirectSum.decompose_one, algebraMap_gradedMul]
    -- Qualified `map_smul` to avoid a TC timeout https://github.com/leanprover-community/mathlib4/pull/8386
    rw [LinearEquiv.map_smul]
    simp

/--
lemma `algebraMap_def` / 引理 `algebraMap_def`

English:
lemma algebraMap_def
  given: (r : R)
  statement: algebraMap R (𝒜 ᵍotimes[R] ℬ) r = algebraMap R A r ᵍotimesₜ[R] 1
  proof: rfl

中文:
引理 algebraMap_def
  条件: (r : R)
  结论: algebraMap R (𝒜 ᵍotimes[R] ℬ) r = algebraMap R A r ᵍotimesₜ[R] 1
  证明: rfl
-/
lemma algebraMap_def (r : R) : algebraMap R (𝒜 ᵍotimes[R] ℬ) r = algebraMap R A r ᵍotimesₜ[R] 1 := rfl

/--
theorem `tmul_algebraMap_mul_coe_tmul` / 定理 `tmul_algebraMap_mul_coe_tmul`

English:
theorem tmul_algebraMap_mul_coe_tmul
  given: {i₂ : ι} (a₁ : A) (r : R) (a₂ : 𝒜 i₂) (b₂ : B)
  proof: tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (GAlgebra.toFun (A := (ℬ ·)) r) a₂ b₂

中文:
定理 tmul_algebraMap_mul_coe_tmul
  条件: {i₂ : ι} (a₁ : A) (r : R) (a₂ : 𝒜 i₂) (b₂ : B)
  证明: tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (GAlgebra.toFun (A := (ℬ ·)) r) a₂ b₂

Depends on / 依赖: GAlgebra, GAlgebra.toFun, tmul_zero_coe_mul_coe_tmul
-/
theorem tmul_algebraMap_mul_coe_tmul {i₂ : ι} (a₁ : A) (r : R) (a₂ : 𝒜 i₂) (b₂ : B) :
    (a₁ ᵍotimesₜ[R] algebraMap R B r * (a₂ : A) ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ)
      = (a₁ * a₂ : A) ᵍotimesₜ (algebraMap R B r * b₂ : B) :=
  tmul_zero_coe_mul_coe_tmul 𝒜 ℬ a₁ (GAlgebra.toFun (A := (ℬ ·)) r) a₂ b₂

/--
theorem `tmul_coe_mul_algebraMap_tmul` / 定理 `tmul_coe_mul_algebraMap_tmul`

English:
theorem tmul_coe_mul_algebraMap_tmul
  given: {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (r : R) (b₂ : B)
  proof: tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (GAlgebra.toFun (A := (𝒜 ·)) r) b₂

中文:
定理 tmul_coe_mul_algebraMap_tmul
  条件: {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (r : R) (b₂ : B)
  证明: tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (GAlgebra.toFun (A := (𝒜 ·)) r) b₂

Depends on / 依赖: GAlgebra, GAlgebra.toFun, tmul_coe_mul_zero_coe_tmul
-/
theorem tmul_coe_mul_algebraMap_tmul {j₁ : ι} (a₁ : A) (b₁ : ℬ j₁) (r : R) (b₂ : B) :
    (a₁ ᵍotimesₜ[R] (b₁ : B) * algebraMap R A r ᵍotimesₜ[R] b₂ : 𝒜 ᵍotimes[R] ℬ)
      = (a₁ * algebraMap R A r : A) ᵍotimesₜ (b₁ * b₂ : B) :=
  tmul_coe_mul_zero_coe_tmul 𝒜 ℬ a₁ b₁ (GAlgebra.toFun (A := (𝒜 ·)) r) b₂

/-- The algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps!]
/--
Definition of `includeLeft` / `includeLeft` 的定义

English:
definition includeLeft
  signature: : A ->ₐ[R] 𝒜 ᵍotimes[R] ℬ where
  body: includeLeftRingHom 𝒜 ℬ
  commutes' _ := rfl

中文:
定义 includeLeft
  签名: : A ->ₐ[R] 𝒜 ᵍotimes[R] ℬ where
  定义体: includeLeftRingHom 𝒜 ℬ
  commutes' _ := rfl

Depends on / 依赖: includeLeftRingHom
-/
def includeLeft : A ->ₐ[R] 𝒜 ᵍotimes[R] ℬ where
  toRingHom := includeLeftRingHom 𝒜 ℬ
  commutes' _ := rfl

/-- The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`. -/
@[simps!]
/--
Definition of `includeRight` / `includeRight` 的定义

English:
definition includeRight
  signature: : B ->ₐ[R] (𝒜 ᵍotimes[R] ℬ)
  body: AlgHom.ofLinearMap (R := R) (A := B) (B := 𝒜 ᵍotimes[R] ℬ)
    (f := {
       toFun := fun b => 1 ᵍotimesₜ b
       map_add' := by simp [tmul, TensorProduct.tmul_add]
       map_smul' := by simp [tmul, TensorProduct.tmul_smul] })
    (map_one := rfl)
    (map_mul := by
      rw [LinearMap.map_mul_if

中文:
定义 includeRight
  签名: : B ->ₐ[R] (𝒜 ᵍotimes[R] ℬ)
  定义体: AlgHom.ofLinearMap (R := R) (A := B) (B := 𝒜 ᵍotimes[R] ℬ)
    (f := {
       toFun := fun b => 1 ᵍotimesₜ b
       map_add' := by simp [tmul, TensorProduct.tmul_add]
       map_smul' := by simp [tmul, TensorProduct.tmul_smul] })
    (map_one := rfl)
    (map_mul := by
      rw [LinearMap.map_mul_if

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, DirectSum, DirectSum.decompose_lhom_ext, LinearMap, LinearMap.map_mul_iff, TensorProduct, TensorProduct.tmul_add, TensorProduct.tmul_smul, decompose_lhom_ext, map_add, map_mul, map_mul_iff, map_one, map_smul, ofLinearMap, tmul_add, tmul_coe_mul_one_tmul, tmul_smul
-/
def includeRight : B ->ₐ[R] (𝒜 ᵍotimes[R] ℬ) :=
  AlgHom.ofLinearMap (R := R) (A := B) (B := 𝒜 ᵍotimes[R] ℬ)
    (f := {
       toFun := fun b => 1 ᵍotimesₜ b
       map_add' := by simp [tmul, TensorProduct.tmul_add]
       map_smul' := by simp [tmul, TensorProduct.tmul_smul] })
    (map_one := rfl)
    (map_mul := by
      rw [LinearMap.map_mul_iff]
      refine DirectSum.decompose_lhom_ext ℬ fun i₁ => ?_
      ext b₁ b₂ : 2
      dsimp
      rw [tmul_coe_mul_one_tmul])

/--
lemma `algebraMap_def'` / 引理 `algebraMap_def'`

English:
lemma algebraMap_def'
  given: (r : R)
  statement: algebraMap R (𝒜 ᵍotimes[R] ℬ) r = 1 ᵍotimesₜ[R] algebraMap R B r
  proof: .symm (includeRight 𝒜 ℬ).commutes r

中文:
引理 algebraMap_def'
  条件: (r : R)
  结论: algebraMap R (𝒜 ᵍotimes[R] ℬ) r = 1 ᵍotimesₜ[R] algebraMap R B r
  证明: .symm (includeRight 𝒜 ℬ).commutes r

Depends on / 依赖: commutes, includeRight
-/
lemma algebraMap_def' (r : R) : algebraMap R (𝒜 ᵍotimes[R] ℬ) r = 1 ᵍotimesₜ[R] algebraMap R B r :=
.symm (includeRight 𝒜 ℬ).commutes r

variable {C} [Ring C] [Algebra R C]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  body: AlgHom.ofLinearMap
    (LinearMap.mul' R C
      ∘ₗ (TensorProduct.map f.toLinearMap g.toLinearMap)
      ∘ₗ ((of R 𝒜 ℬ).symm : 𝒜 ᵍotimes[R] ℬ ->ₗ[R] A otimes[R] B))
    (by
      dsimp [Algebra.TensorProduct.one_def]
      simp only [map_one, mul_one])
    (by
      rw [LinearMap.map_mul_iff]
     

中文:
定义 lift
  签名: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  定义体: AlgHom.ofLinearMap
    (LinearMap.mul' R C
      ∘ₗ (TensorProduct.map f.toLinearMap g.toLinearMap)
      ∘ₗ ((of R 𝒜 ℬ).symm : 𝒜 ᵍotimes[R] ℬ ->ₗ[R] A otimes[R] B))
    (by
      dsimp [Algebra.TensorProduct.one_def]
      simp only [map_one, mul_one])
    (by
      rw [LinearMap.map_mul_iff]
     

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, Algebra, Algebra.TensorProduct.one_def, DirectSum, DirectSum.decompose_lhom_ext, Int.cast_smul_eq_zsmul, LinearMap, LinearMap.map_mul_iff, LinearMap.mul, TensorProduct, TensorProduct.map, Units.smul_def, cast_smul_eq_zsmul, decompose_lhom_ext, f.toLinearMap, g.toLinearMap, map_mul_iff, map_one, map_s
-/
def lift (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
    (h_anti_commutes : forall ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), f a * g b = (-1 : Intˣ) ^ (j * i) • (g b * f a)) :
    (𝒜 ᵍotimes[R] ℬ) ->ₐ[R] C :=
  AlgHom.ofLinearMap
    (LinearMap.mul' R C
      ∘ₗ (TensorProduct.map f.toLinearMap g.toLinearMap)
      ∘ₗ ((of R 𝒜 ℬ).symm : 𝒜 ᵍotimes[R] ℬ ->ₗ[R] A otimes[R] B))
    (by
      dsimp [Algebra.TensorProduct.one_def]
      simp only [map_one, mul_one])
    (by
      rw [LinearMap.map_mul_iff]
      ext a₁ : 3
      refine DirectSum.decompose_lhom_ext ℬ fun j₁ => ?_
      ext b₁ : 3
      refine DirectSum.decompose_lhom_ext 𝒜 fun i₂ => ?_
      ext a₂ b₂ : 2
      dsimp
      rw [tmul_coe_mul_coe_tmul]
      rw [@Units.smul_def _ _ (_) (_)]; rw [← Int.cast_smul_eq_zsmul R]; rw [map_smul]; rw [map_smul]; rw [map_smul]
      rw [Int.cast_smul_eq_zsmul R]; rw [← @Units.smul_def _ _ (_) (_)]
      rw [of_symm_of]; rw [map_tmul]; rw [LinearMap.mul'_apply]
      simp_rw [AlgHom.toLinearMap_apply, map_mul]
      simp_rw [mul_assoc (f a₁), ← mul_assoc _ _ (g b₂), h_anti_commutes, mul_smul_comm,
        smul_mul_assoc, smul_smul, Int.units_mul_self, one_smul])

@[simp]
/--
theorem `lift_tmul` / 定理 `lift_tmul`

English:
theorem lift_tmul
  statement: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  proof: rfl

中文:
定理 lift_tmul
  结论: (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  证明: rfl
-/
theorem lift_tmul (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
    (h_anti_commutes : forall ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), f a * g b = (-1 : Intˣ) ^ (j * i) • (g b * f a))
    (a : A) (b : B) :
    lift 𝒜 ℬ f g h_anti_commutes (a ᵍotimesₜ b) = f a * g b :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: :
  body: lift 𝒜 ℬ _ _ fg.prop
  invFun F := ⟨(F.comp (includeLeft 𝒜 ℬ), F.comp (includeRight 𝒜 ℬ)), fun i j a b => by
    dsimp
    rw [← map_mul]; rw [← map_mul F]; rw [tmul_coe_mul_coe_tmul]; rw [one_mul]; rw [mul_one]; rw [AlgHom.map_smul_of_tower]; rw [tmul_one_mul_one_tmul]; rw [smul_smul]; rw [Int.unit

中文:
定义 liftEquiv
  签名: :
  定义体: lift 𝒜 ℬ _ _ fg.prop
  invFun F := ⟨(F.comp (includeLeft 𝒜 ℬ), F.comp (includeRight 𝒜 ℬ)), fun i j a b => by
    dsimp
    rw [← map_mul]; rw [← map_mul F]; rw [tmul_coe_mul_coe_tmul]; rw [one_mul]; rw [mul_one]; rw [AlgHom.map_smul_of_tower]; rw [tmul_one_mul_one_tmul]; rw [smul_smul]; rw [Int.unit

Depends on / 依赖: fg.prop
-/
def liftEquiv :
    { fg : (A ->ₐ[R] C) × (B ->ₐ[R] C) //
        forall ⦃i j⦄ (a : 𝒜 i) (b : ℬ j), fg.1 a * fg.2 b = (-1 : Intˣ)^(j * i) • (fg.2 b * fg.1 a)} ≃
      ((𝒜 ᵍotimes[R] ℬ) ->ₐ[R] C) where
  toFun fg := lift 𝒜 ℬ _ _ fg.prop
  invFun F := ⟨(F.comp (includeLeft 𝒜 ℬ), F.comp (includeRight 𝒜 ℬ)), fun i j a b => by
    dsimp
    rw [← map_mul]; rw [← map_mul F]; rw [tmul_coe_mul_coe_tmul]; rw [one_mul]; rw [mul_one]; rw [AlgHom.map_smul_of_tower]; rw [tmul_one_mul_one_tmul]; rw [smul_smul]; rw [Int.units_mul_self]; rw [one_smul]⟩
  left_inv fg := by ext <;> (dsimp; simp only [map_one, mul_one, one_mul])
  right_inv F := by
    apply AlgHom.toLinearMap_injective
    ext
    dsimp
    rw [← map_mul]; rw [tmul_one_mul_one_tmul]

/-- Two algebra morphism from the graded tensor product agree if their compositions with the left
and right inclusions agree. -/
@[ext]
/--
lemma `algHom_ext` / 引理 `algHom_ext`

English:
lemma algHom_ext
  given: ⦃f g
  statement: (𝒜 ᵍotimes[R] ℬ) ->ₐ[R] C⦄
  proof: (liftEquiv 𝒜 ℬ).symm.injective Subtype.ext Prod.ext ha hb

中文:
引理 algHom_ext
  条件: ⦃f g
  结论: (𝒜 ᵍotimes[R] ℬ) ->ₐ[R] C⦄
  证明: (liftEquiv 𝒜 ℬ).symm.injective Subtype.ext Prod.ext ha hb

Depends on / 依赖: Prod.ext, Subtype, Subtype.ext, injective, liftEquiv, symm.injective
-/
lemma algHom_ext ⦃f g : (𝒜 ᵍotimes[R] ℬ) ->ₐ[R] C⦄
    (ha : f.comp (includeLeft 𝒜 ℬ) = g.comp (includeLeft 𝒜 ℬ))
    (hb : f.comp (includeRight 𝒜 ℬ) = g.comp (includeRight 𝒜 ℬ)) : f = g :=
(liftEquiv 𝒜 ℬ).symm.injective Subtype.ext Prod.ext ha hb

/--
Definition of `comm` / `comm` 的定义

English:
definition comm
  signature: : (𝒜 ᵍotimes[R] ℬ) ≃ₐ[R] (ℬ ᵍotimes[R] 𝒜)
  body: AlgEquiv.ofLinearEquiv
    (auxEquiv R 𝒜 ℬ ≪≫ₗ gradedComm R _ _ ≪≫ₗ (auxEquiv R ℬ 𝒜).symm)
    (by
      dsimp
      simp_rw [auxEquiv_one, gradedComm_one, auxEquiv_symm_one])
    (fun x y => by
      dsimp
      simp_rw [auxEquiv_mul, gradedComm_gradedMul, LinearEquiv.symm_apply_eq,
        ← grade

中文:
定义 comm
  签名: : (𝒜 ᵍotimes[R] ℬ) ≃ₐ[R] (ℬ ᵍotimes[R] 𝒜)
  定义体: AlgEquiv.ofLinearEquiv
    (auxEquiv R 𝒜 ℬ ≪≫ₗ gradedComm R _ _ ≪≫ₗ (auxEquiv R ℬ 𝒜).symm)
    (by
      dsimp
      simp_rw [auxEquiv_one, gradedComm_one, auxEquiv_symm_one])
    (fun x y => by
      dsimp
      simp_rw [auxEquiv_mul, gradedComm_gradedMul, LinearEquiv.symm_apply_eq,
        ← grade

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, LinearEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_eq, apply_symm_apply, auxEquiv, auxEquiv_mul, auxEquiv_one, auxEquiv_symm_one, gradedComm, gradedComm_gradedMul, gradedComm_one, ofLinearEquiv, simp_rw, symm_apply_eq
-/
def comm : (𝒜 ᵍotimes[R] ℬ) ≃ₐ[R] (ℬ ᵍotimes[R] 𝒜) :=
  AlgEquiv.ofLinearEquiv
    (auxEquiv R 𝒜 ℬ ≪≫ₗ gradedComm R _ _ ≪≫ₗ (auxEquiv R ℬ 𝒜).symm)
    (by
      dsimp
      simp_rw [auxEquiv_one, gradedComm_one, auxEquiv_symm_one])
    (fun x y => by
      dsimp
      simp_rw [auxEquiv_mul, gradedComm_gradedMul, LinearEquiv.symm_apply_eq,
        ← gradedComm_gradedMul, auxEquiv_mul, LinearEquiv.apply_symm_apply, gradedComm_gradedMul])

/--
lemma `auxEquiv_comm` / 引理 `auxEquiv_comm`

English:
lemma auxEquiv_comm
  given: (x : 𝒜 ᵍotimes[R] ℬ)
  proof: .mp rfl LinearEquiv.eq_symm_apply _

中文:
引理 auxEquiv_comm
  条件: (x : 𝒜 ᵍotimes[R] ℬ)
  证明: .mp rfl LinearEquiv.eq_symm_apply _

Depends on / 依赖: LinearEquiv, LinearEquiv.eq_symm_apply, eq_symm_apply
-/
lemma auxEquiv_comm (x : 𝒜 ᵍotimes[R] ℬ) :
    auxEquiv R ℬ 𝒜 (comm 𝒜 ℬ x) = gradedComm R (𝒜 ·) (ℬ ·) (auxEquiv R 𝒜 ℬ x) :=
.mp rfl LinearEquiv.eq_symm_apply _

/--
lemma `comm_coe_tmul_coe` / 引理 `comm_coe_tmul_coe`

English:
lemma comm_coe_tmul_coe
  given: {i j : ι} (a : 𝒜 i) (b : ℬ j)
  proof: (auxEquiv R ℬ 𝒜).injective by
    simp_rw [auxEquiv_comm, auxEquiv_tmul, decompose_coe, ← lof_eq_of R, gradedComm_of_tmul_of,
      @Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R]
    -- Qualified `map_smul` to avoid a TC timeout https://github.com/leanprover-community/mathlib4/pull/8386
  

中文:
引理 comm_coe_tmul_coe
  条件: {i j : ι} (a : 𝒜 i) (b : ℬ j)
  证明: (auxEquiv R ℬ 𝒜).injective by
    simp_rw [auxEquiv_comm, auxEquiv_tmul, decompose_coe, ← lof_eq_of R, gradedComm_of_tmul_of,
      @Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R]
    -- Qualified `map_smul` to avoid a TC timeout https://github.com/leanprover-community/mathlib4/pull/8386
  
-/
@[simp] lemma comm_coe_tmul_coe {i j : ι} (a : 𝒜 i) (b : ℬ j) :
    comm 𝒜 ℬ (a ᵍotimesₜ b) = (-1 : Intˣ) ^ (j * i) • (b ᵍotimesₜ a : ℬ ᵍotimes[R] 𝒜) :=
(auxEquiv R ℬ 𝒜).injective by
    simp_rw [auxEquiv_comm, auxEquiv_tmul, decompose_coe, ← lof_eq_of R, gradedComm_of_tmul_of,
      @Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R]
    -- Qualified `map_smul` to avoid a TC timeout https://github.com/leanprover-community/mathlib4/pull/8386
    rw [LinearEquiv.map_smul]; rw [auxEquiv_tmul]
    simp_rw [decompose_coe, lof_eq_of]

end GradedTensorProduct
