/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Ideal.Span

/-!
# Linear maps and matrices

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

* `LinearMap.toMatrix`: given bases `v₁ : ι → M₁` and `v₂ : κ → M₂`,
  the `R`-linear equivalence from `M₁ →ₗ[R] M₂` to `Matrix κ ι R`
* `Matrix.toLin`: the inverse of `LinearMap.toMatrix`
* `LinearMap.toMatrix'`: the `R`-linear equivalence from `(m → R) →ₗ[R] (n → R)`
  to `Matrix m n R` (with the standard basis on `m → R` and `n → R`)
* `Matrix.toLin'`: the inverse of `LinearMap.toMatrix'`
* `algEquivMatrix`: given a basis indexed by `n`, the `R`-algebra equivalence between
  `R`-endomorphisms of `M` and `Matrix n n R`

## Issues

This file was originally written without attention to non-commutative rings,
and so mostly only works in the commutative setting. This should be fixed.

In particular, `Matrix.mulVec` gives us a linear equivalence
`Matrix m n R ≃ₗ[R] (n → R) →ₗ[Rᵐᵒᵖ] (m → R)`
while `Matrix.vecMul` gives us a linear equivalence
`Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] (n → R)`.
At present, the first equivalence is developed in detail but only for commutative rings
(and we omit the distinction between `Rᵐᵒᵖ` and `R`),
while the second equivalence is developed only in brief, but for not-necessarily-commutative rings.

Naming is slightly inconsistent between the two developments.
In the original (commutative) development `linear` is abbreviated to `lin`,
although this is not consistent with the rest of mathlib.
In the new (non-commutative) development `linear` is not abbreviated, and declarations use `_right`
to indicate they use the right action of matrices on vectors (via `Matrix.vecMul`).
When the two developments are made uniform, the names should be made uniform, too,
by choosing between `linear` and `lin` consistently,
and (presumably) adding `_left` where necessary.

## Tags

linear_map, matrix, linear_equiv, diagonal, det, trace
-/

@[expose] public section

noncomputable section

open LinearMap Matrix Module Set Submodule

/-!
### Bilinear versions of matrix products

The definitions in this section are stated with two extra rings, to allow for non-commutative rings.
-/

section Bilinear
variable {l m n R S A : Type*}
variable [Semiring R] [Semiring S] [NonUnitalNonAssocSemiring A]
variable [Module R A] [Module S A]
variable [SMulCommClass S R A] [SMulCommClass S A A] [IsScalarTower R A A]

variable (R S)

/--
Definition of `Matrix.vecMulBilin` / `Matrix.vecMulBilin` 的定义

English:
definition Matrix.vecMulBilin
  signature: [Fintype m]
  body: { toFun M := x ᵥ* M
    map_add' _ _ := vecMul_add _ _ _
    map_smul' _ _ := vecMul_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_vecMul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_vecMul _ _ _

@[simp]

中文:
定义 Matrix.vecMulBilin
  签名: [Fintype m]
  定义体: { toFun M := x ᵥ* M
    map_add' _ _ := vecMul_add _ _ _
    map_smul' _ _ := vecMul_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_vecMul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_vecMul _ _ _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, add_vecMul, map_add, map_smul, smul_vecMul, vecMul_add, vecMul_smul
-/
def Matrix.vecMulBilin [Fintype m] : (m -> A) ->ₗ[R] Matrix m n A ->ₗ[S] (n -> A) where
  toFun x :=
  { toFun M := x ᵥ* M
    map_add' _ _ := vecMul_add _ _ _
    map_smul' _ _ := vecMul_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_vecMul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_vecMul _ _ _

@[simp]
/--
theorem `Matrix.vecMulBilin_apply` / 定理 `Matrix.vecMulBilin_apply`

English:
theorem Matrix.vecMulBilin_apply
  given: [Fintype m] (v : m -> A) (M : Matrix m n A)
  proof: rfl

example {A} [Semiring A] [Fintype m] := (vecMulBilin A Aᵐᵒᵖ : _ ->ₗ[_] Matrix m n A ->ₗ[_] _)

中文:
定理 Matrix.vecMulBilin_apply
  条件: [Fintype m] (v : m -> A) (M : Matrix m n A)
  证明: rfl

example {A} [Semiring A] [Fintype m] := (vecMulBilin A Aᵐᵒᵖ : _ ->ₗ[_] Matrix m n A ->ₗ[_] _)
-/
theorem Matrix.vecMulBilin_apply [Fintype m] (v : m -> A) (M : Matrix m n A) :
    Matrix.vecMulBilin R S v M = v ᵥ* M := rfl

example {A} [Semiring A] [Fintype m] := (vecMulBilin A Aᵐᵒᵖ : _ ->ₗ[_] Matrix m n A ->ₗ[_] _)

/--
Definition of `Matrix.mulVecBilin` / `Matrix.mulVecBilin` 的定义

English:
definition Matrix.mulVecBilin
  signature: [Fintype n]
  body: { toFun x := M *ᵥ x
    map_add' _ _ := mulVec_add _ _ _
    map_smul' _ _ := mulVec_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_mulVec _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_mulVec _ _ _

@[simp]

中文:
定义 Matrix.mulVecBilin
  签名: [Fintype n]
  定义体: { toFun x := M *ᵥ x
    map_add' _ _ := mulVec_add _ _ _
    map_smul' _ _ := mulVec_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_mulVec _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_mulVec _ _ _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, add_mulVec, map_add, map_smul, mulVec_add, mulVec_smul, smul_mulVec
-/
def Matrix.mulVecBilin [Fintype n] : Matrix m n A ->ₗ[R] (n -> A) ->ₗ[S] (m -> A) where
  toFun M :=
  { toFun x := M *ᵥ x
    map_add' _ _ := mulVec_add _ _ _
    map_smul' _ _ := mulVec_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_mulVec _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_mulVec _ _ _

@[simp]
/--
theorem `Matrix.mulVecBilin_apply` / 定理 `Matrix.mulVecBilin_apply`

English:
theorem Matrix.mulVecBilin_apply
  given: [Fintype n] (M : Matrix m n A) (v : n -> A)
  proof: rfl

example {A} [Semiring A] [Fintype n] := (mulVecBilin A Aᵐᵒᵖ : Matrix m n A ->ₗ[_] _ ->ₗ[_] _)

中文:
定理 Matrix.mulVecBilin_apply
  条件: [Fintype n] (M : Matrix m n A) (v : n -> A)
  证明: rfl

example {A} [Semiring A] [Fintype n] := (mulVecBilin A Aᵐᵒᵖ : Matrix m n A ->ₗ[_] _ ->ₗ[_] _)
-/
theorem Matrix.mulVecBilin_apply [Fintype n] (M : Matrix m n A) (v : n -> A) :
    Matrix.mulVecBilin R S M v = M *ᵥ v := rfl

example {A} [Semiring A] [Fintype n] := (mulVecBilin A Aᵐᵒᵖ : Matrix m n A ->ₗ[_] _ ->ₗ[_] _)

/-- `vecMulVec` as a bilinear map.

When `A` is noncommutative, `R` and `S` can be instantiated as `vecMulVecBilin A Aᵐᵒᵖ`. -/
@[simps]
/--
Definition of `vecMulVecBilin` / `vecMulVecBilin` 的定义

English:
definition vecMulVecBilin
  signature: : (m -> A) ->ₗ[R] (n -> A) ->ₗ[S] Matrix m n A where
  body: { toFun y := vecMulVec x y
      map_add' _ _ := vecMulVec_add _ _ _
      map_smul' _ _ := vecMulVec_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_vecMulVec _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_vecMulVec _ _ _

example {A} [Semiring A] := (vecMulVecBilin A Aᵐᵒᵖ : (m -> A

中文:
定义 vecMulVecBilin
  签名: : (m -> A) ->ₗ[R] (n -> A) ->ₗ[S] Matrix m n A where
  定义体: { toFun y := vecMulVec x y
      map_add' _ _ := vecMulVec_add _ _ _
      map_smul' _ _ := vecMulVec_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_vecMulVec _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_vecMulVec _ _ _

example {A} [Semiring A] := (vecMulVecBilin A Aᵐᵒᵖ : (m -> A

Depends on / 依赖: LinearMap, LinearMap.ext, add_vecMulVec, map_add, map_smul, smul_vecMulVec, vecMulVec, vecMulVec_add, vecMulVec_smul
-/
def vecMulVecBilin : (m -> A) ->ₗ[R] (n -> A) ->ₗ[S] Matrix m n A where
  toFun x :=
    { toFun y := vecMulVec x y
      map_add' _ _ := vecMulVec_add _ _ _
      map_smul' _ _ := vecMulVec_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_vecMulVec _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_vecMulVec _ _ _

example {A} [Semiring A] := (vecMulVecBilin A Aᵐᵒᵖ : (m -> A) ->ₗ[_] (n -> A) ->ₗ[_] _)

/-- `dotProduct` as a bilinear map.

When `A` is noncommutative, `R` and `S` can be instantiated as `dotProductBilin A Aᵐᵒᵖ`. -/
@[simps]
/--
Definition of `dotProductBilin` / `dotProductBilin` 的定义

English:
definition dotProductBilin
  signature: [Fintype m]
  body: { toFun y := dotProduct x y
      map_add' _ _ := dotProduct_add _ _ _
      map_smul' _ _ := dotProduct_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_dotProduct _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_dotProduct _ _ _

example {A} [Semiring A] [Fintype m] := (dotProductBili

中文:
定义 dotProductBilin
  签名: [Fintype m]
  定义体: { toFun y := dotProduct x y
      map_add' _ _ := dotProduct_add _ _ _
      map_smul' _ _ := dotProduct_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_dotProduct _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_dotProduct _ _ _

example {A} [Semiring A] [Fintype m] := (dotProductBili

Depends on / 依赖: LinearMap, LinearMap.ext, add_dotProduct, dotProduct, dotProduct_add, dotProduct_smul, map_add, map_smul, smul_dotProduct
-/
def dotProductBilin [Fintype m] : (m -> A) ->ₗ[R] (m -> A) ->ₗ[S] A where
  toFun x :=
    { toFun y := dotProduct x y
      map_add' _ _ := dotProduct_add _ _ _
      map_smul' _ _ := dotProduct_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_dotProduct _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_dotProduct _ _ _

example {A} [Semiring A] [Fintype m] := (dotProductBilin A Aᵐᵒᵖ : (m -> A) ->ₗ[_] _ ->ₗ[_] _)

end Bilinear

section ToMatrixRight
variable {R : Type*} [Semiring R]
variable {l m n : Type*}

/--
Definition of `Matrix.vecMulLinear` / `Matrix.vecMulLinear` 的定义

English:
abbreviation Matrix.vecMulLinear
  signature: [Fintype m] (M : Matrix m n R)
  body: .flip M Matrix.vecMulBilin R Rᵐᵒᵖ

中文:
缩写 Matrix.vecMulLinear
  签名: [Fintype m] (M : Matrix m n R)
  定义体: .flip M Matrix.vecMulBilin R Rᵐᵒᵖ

Depends on / 依赖: Matrix, Matrix.vecMulBilin, vecMulBilin
-/
abbrev Matrix.vecMulLinear [Fintype m] (M : Matrix m n R) : (m -> R) ->ₗ[R] n -> R :=
.flip M Matrix.vecMulBilin R Rᵐᵒᵖ

/--
theorem `Matrix.vecMulLinear_apply` / 定理 `Matrix.vecMulLinear_apply`

English:
theorem Matrix.vecMulLinear_apply
  given: [Fintype m] (M : Matrix m n R) (x : m -> R)
  proof: rfl

中文:
定理 Matrix.vecMulLinear_apply
  条件: [Fintype m] (M : Matrix m n R) (x : m -> R)
  证明: rfl
-/
@[simp] theorem Matrix.vecMulLinear_apply [Fintype m] (M : Matrix m n R) (x : m -> R) :
    M.vecMulLinear x = x ᵥ* M := rfl

/--
theorem `Matrix.coe_vecMulLinear` / 定理 `Matrix.coe_vecMulLinear`

English:
theorem Matrix.coe_vecMulLinear
  given: [Fintype m] (M : Matrix m n R)
  proof: rfl

中文:
定理 Matrix.coe_vecMulLinear
  条件: [Fintype m] (M : Matrix m n R)
  证明: rfl
-/
theorem Matrix.coe_vecMulLinear [Fintype m] (M : Matrix m n R) :
    (M.vecMulLinear : _ -> _) = M.vecMul := rfl

variable [Fintype m]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `range_vecMulLinear` / 定理 `range_vecMulLinear`

English:
theorem range_vecMulLinear
  given: (M : Matrix m n R)
  proof: by
  let := Classical.decEq m
  simp_rw [range_eq_map, ← iSup_range_single, Submodule.map_iSup, range_eq_map, ←
    Ideal.span_singleton_one, Ideal.span, Submodule.map_span, image_image, image_singleton,
    Matrix.vecMulLinear_apply, iSup_span, range_eq_iUnion, iUnion_singleton_eq_range,
    Linear

中文:
定理 range_vecMulLinear
  条件: (M : Matrix m n R)
  证明: by
  let := Classical.decEq m
  simp_rw [range_eq_map, ← iSup_range_single, Submodule.map_iSup, range_eq_map, ←
    Ideal.span_singleton_one, Ideal.span, Submodule.map_span, image_image, image_singleton,
    Matrix.vecMulLinear_apply, iSup_span, range_eq_iUnion, iUnion_singleton_eq_range,
    Linear

Depends on / 依赖: AddHom, AddHom.coe_mk, Classical, Classical.decEq, Ideal.span, Ideal.span_singleton_one, LinearMap, LinearMap.coe_mk, LinearMap.single, Matrix, Matrix.vecMulLinear_apply, Submodule, Submodule.map_iSup, Submodule.map_span, coe_mk, iSup_range_single, iSup_span, iUnion_singleton_eq_range, image_image, image_singleton
-/
theorem range_vecMulLinear (M : Matrix m n R) :
    LinearMap.range M.vecMulLinear = span R (range M.row) := by
  let := Classical.decEq m
  simp_rw [range_eq_map, ← iSup_range_single, Submodule.map_iSup, range_eq_map, ←
    Ideal.span_singleton_one, Ideal.span, Submodule.map_span, image_image, image_singleton,
    Matrix.vecMulLinear_apply, iSup_span, range_eq_iUnion, iUnion_singleton_eq_range,
    LinearMap.single, LinearMap.coe_mk, AddHom.coe_mk, row_def]
  unfold vecMul
  simp_rw [single_dotProduct, one_mul]

/--
theorem `Matrix.vecMul_injective_iff` / 定理 `Matrix.vecMul_injective_iff`

English:
theorem Matrix.vecMul_injective_iff
  given: {M : Matrix m n R}
  proof: by
  rw [← coe_vecMulLinear]; rw [linearIndependent_iff_injective_fintypeLinearCombination]
  congr! 1
  exact funext fun _ => Matrix.vecMul_eq_sum _ _

中文:
定理 Matrix.vecMul_injective_iff
  条件: {M : Matrix m n R}
  证明: by
  rw [← coe_vecMulLinear]; rw [linearIndependent_iff_injective_fintypeLinearCombination]
  congr! 1
  exact funext fun _ => Matrix.vecMul_eq_sum _ _

Depends on / 依赖: Function, Function.Injective.module, Injective, Matrix, Matrix.vecMul_eq_sum, coe_vecMulLinear, linearIndependent_iff_injective_fintypeLinearCombination, module, toMeasureAddMonoidHom, toMeasure_injective, toMeasure_smul, vecMul_eq_sum
-/
theorem Matrix.vecMul_injective_iff {M : Matrix m n R} :
    Function.Injective M.vecMul ↔ LinearIndependent R M.row := by
  rw [← coe_vecMulLinear]; rw [linearIndependent_iff_injective_fintypeLinearCombination]
  congr! 1
  exact funext fun _ => Matrix.vecMul_eq_sum _ _

/--
lemma `Matrix.linearIndependent_rows_of_isUnit` / 引理 `Matrix.linearIndependent_rows_of_isUnit`

English:
lemma Matrix.linearIndependent_rows_of_isUnit
  statement: {A : Matrix m m R}
  proof: by
  rw [← Matrix.vecMul_injective_iff]
  exact Matrix.vecMul_injective_of_isUnit ha

中文:
引理 Matrix.linearIndependent_rows_of_isUnit
  结论: {A : Matrix m m R}
  证明: by
  rw [← Matrix.vecMul_injective_iff]
  exact Matrix.vecMul_injective_of_isUnit ha

Depends on / 依赖: Matrix, Matrix.vecMul_injective_iff, Matrix.vecMul_injective_of_isUnit, vecMul_injective_iff, vecMul_injective_of_isUnit
-/
lemma Matrix.linearIndependent_rows_of_isUnit {A : Matrix m m R}
    [DecidableEq m] (ha : IsUnit A) : LinearIndependent R A.row := by
  rw [← Matrix.vecMul_injective_iff]
  exact Matrix.vecMul_injective_of_isUnit ha

section

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `LinearMap.toMatrixRight'` / `LinearMap.toMatrixRight'` 的定义

English:
definition LinearMap.toMatrixRight'
  signature: [DecidableEq m]
  body: f (single R (fun _ => R) i 1) j
  invFun := Matrix.vecMulLinear
  right_inv M := by
    ext i j
    simp
  left_inv f := by
    apply (Pi.basisFun R m).ext
    intro j; ext i
    simp
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, Matrix.add_apply]
  map_smul' c f

中文:
定义 LinearMap.toMatrixRight'
  签名: [DecidableEq m]
  定义体: f (single R (fun _ => R) i 1) j
  invFun := Matrix.vecMulLinear
  right_inv M := by
    ext i j
    simp
  left_inv f := by
    apply (Pi.basisFun R m).ext
    intro j; ext i
    simp
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, Matrix.add_apply]
  map_smul' c f

Depends on / 依赖: single
-/
def LinearMap.toMatrixRight' [DecidableEq m] : ((m -> R) ->ₗ[R] n -> R) ≃ₗ[Rᵐᵒᵖ] Matrix m n R where
  toFun f i j := f (single R (fun _ => R) i 1) j
  invFun := Matrix.vecMulLinear
  right_inv M := by
    ext i j
    simp
  left_inv f := by
    apply (Pi.basisFun R m).ext
    intro j; ext i
    simp
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, Matrix.add_apply]
  map_smul' c f := by
    ext i j
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, Matrix.smul_apply]

/--
Definition of `Matrix.toLinearMapRight'` / `Matrix.toLinearMapRight'` 的定义

English:
abbreviation Matrix.toLinearMapRight'
  signature: [DecidableEq m]
  body: LinearEquiv.symm LinearMap.toMatrixRight'

中文:
缩写 Matrix.toLinearMapRight'
  签名: [DecidableEq m]
  定义体: LinearEquiv.symm LinearMap.toMatrixRight'

Depends on / 依赖: LinearEquiv, LinearEquiv.symm, LinearMap, LinearMap.toMatrixRight, toMatrixRight
-/
abbrev Matrix.toLinearMapRight' [DecidableEq m] : Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m -> R) ->ₗ[R] n -> R :=
  LinearEquiv.symm LinearMap.toMatrixRight'

variable [DecidableEq m]

@[simp]
/--
theorem `Matrix.toLinearMapRight'_apply` / 定理 `Matrix.toLinearMapRight'_apply`

English:
theorem Matrix.toLinearMapRight'_apply
  given: (M : Matrix m n R) (v : m -> R)
  proof: rfl

@[simp]

中文:
定理 Matrix.toLinearMapRight'_apply
  条件: (M : Matrix m n R) (v : m -> R)
  证明: rfl

@[simp]
-/
theorem Matrix.toLinearMapRight'_apply (M : Matrix m n R) (v : m -> R) :
    M.toLinearMapRight' v = v ᵥ* M := rfl

@[simp]
/--
theorem `Matrix.toLinearMapRight'_mul` / 定理 `Matrix.toLinearMapRight'_mul`

English:
theorem Matrix.toLinearMapRight'_mul
  statement: [Fintype l] [DecidableEq l] (M : Matrix l m R)
  proof: LinearMap.ext fun _x => (vecMul_vecMul _ M N).symm

中文:
定理 Matrix.toLinearMapRight'_mul
  结论: [Fintype l] [DecidableEq l] (M : Matrix l m R)
  证明: LinearMap.ext fun _x => (vecMul_vecMul _ M N).symm
-/
theorem Matrix.toLinearMapRight'_mul [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) :
    (M * N).toLinearMapRight' = N.toLinearMapRight' ∘ₗ M.toLinearMapRight' :=
  LinearMap.ext fun _x => (vecMul_vecMul _ M N).symm

/--
theorem `Matrix.toLinearMapRight'_mul_apply` / 定理 `Matrix.toLinearMapRight'_mul_apply`

English:
theorem Matrix.toLinearMapRight'_mul_apply
  statement: [Fintype l] [DecidableEq l] (M : Matrix l m R)
  proof: (vecMul_vecMul _ M N).symm

@[simp]

中文:
定理 Matrix.toLinearMapRight'_mul_apply
  结论: [Fintype l] [DecidableEq l] (M : Matrix l m R)
  证明: (vecMul_vecMul _ M N).symm

@[simp]
-/
theorem Matrix.toLinearMapRight'_mul_apply [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) (x) :
    (M * N).toLinearMapRight' x = N.toLinearMapRight' (M.toLinearMapRight' x) :=
  (vecMul_vecMul _ M N).symm

@[simp]
/--
theorem `LinearMap.toMatrixRight'_comp` / 定理 `LinearMap.toMatrixRight'_comp`

English:
theorem LinearMap.toMatrixRight'_comp
  statement: [Fintype l] [DecidableEq l] (f : (l -> R) ->ₗ[R] m -> R)
  proof: Matrix.toLinearMapRight'.injective by simp

@[simp]

中文:
定理 LinearMap.toMatrixRight'_comp
  结论: [Fintype l] [DecidableEq l] (f : (l -> R) ->ₗ[R] m -> R)
  证明: Matrix.toLinearMapRight'.injective by simp

@[simp]
-/
theorem LinearMap.toMatrixRight'_comp [Fintype l] [DecidableEq l] (f : (l -> R) ->ₗ[R] m -> R)
    (g : (m -> R) ->ₗ[R] n -> R) : (g ∘ₗ f).toMatrixRight' = f.toMatrixRight' * g.toMatrixRight' :=
Matrix.toLinearMapRight'.injective by simp

@[simp]
/--
theorem `Matrix.toLinearMapRight'_one` / 定理 `Matrix.toLinearMapRight'_one`

English:
theorem Matrix.toLinearMapRight'_one
  proof: by
  ext
  simp

中文:
定理 Matrix.toLinearMapRight'_one
  证明: by
  ext
  simp
-/
theorem Matrix.toLinearMapRight'_one :
    (1 : Matrix m m R).toLinearMapRight' = LinearMap.id := by
  ext
  simp

/--
theorem `LinearMap.toMatrixRight'_id` / 定理 `LinearMap.toMatrixRight'_id`

English:
theorem LinearMap.toMatrixRight'_id
  statement: (@LinearMap.id R (m -> R)).toMatrixRight' = 1
  proof: Matrix.toLinearMapRight'.injective by simp

中文:
定理 LinearMap.toMatrixRight'_id
  结论: (@LinearMap.id R (m -> R)).toMatrixRight' = 1
  证明: Matrix.toLinearMapRight'.injective by simp
-/
@[simp] theorem LinearMap.toMatrixRight'_id : (@LinearMap.id R (m -> R)).toMatrixRight' = 1 :=
Matrix.toLinearMapRight'.injective by simp

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `n → A`
and `m → A` corresponding to `M.vecMul` and `M'.vecMul`. -/
@[simps]
/--
Definition of `Matrix.toLinearEquivRight'OfInv` / `Matrix.toLinearEquivRight'OfInv` 的定义

English:
definition Matrix.toLinearEquivRight'OfInv
  signature: [Fintype n] [DecidableEq n] {M : Matrix m n R}
  body: { LinearMap.toMatrixRight'.symm M' with
    toFun := Matrix.toLinearMapRight' M'
    invFun := Matrix.toLinearMapRight' M
    left_inv := fun x => by
      rw [← Matrix.toLinearMapRight'_mul_apply]; rw [hM'M]; rw [Matrix.toLinearMapRight'_one]; rw [id_apply]
    right_inv := fun x => by
      rw [← 

中文:
定义 Matrix.toLinearEquivRight'OfInv
  签名: [Fintype n] [DecidableEq n] {M : Matrix m n R}
  定义体: { LinearMap.toMatrixRight'.symm M' with
    toFun := Matrix.toLinearMapRight' M'
    invFun := Matrix.toLinearMapRight' M
    left_inv := fun x => by
      rw [← Matrix.toLinearMapRight'_mul_apply]; rw [hM'M]; rw [Matrix.toLinearMapRight'_one]; rw [id_apply]
    right_inv := fun x => by
      rw [← 

Depends on / 依赖: LinearMap, LinearMap.toMatrixRight, Matrix, Matrix.toLinearMapRight, _mul_apply, _one, id_apply, invFun, left_inv, right_inv, toLinearMapRight, toMatrixRight
-/
def Matrix.toLinearEquivRight'OfInv [Fintype n] [DecidableEq n] {M : Matrix m n R}
    {M' : Matrix n m R} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : (n -> R) ≃ₗ[R] m -> R :=
  { LinearMap.toMatrixRight'.symm M' with
    toFun := Matrix.toLinearMapRight' M'
    invFun := Matrix.toLinearMapRight' M
    left_inv := fun x => by
      rw [← Matrix.toLinearMapRight'_mul_apply]; rw [hM'M]; rw [Matrix.toLinearMapRight'_one]; rw [id_apply]
    right_inv := fun x => by
      rw [← Matrix.toLinearMapRight'_mul_apply]; rw [hMM']; rw [Matrix.toLinearMapRight'_one]; rw [id_apply] }

end
end ToMatrixRight

/-!
From this point on, we only work with commutative rings,
and fail to distinguish between `Rᵐᵒᵖ` and `R`.
This should eventually be remedied.
-/


section mulVec

variable {R : Type*} [CommSemiring R]
variable {k l m n : Type*}

/--
Definition of `Matrix.mulVecLin` / `Matrix.mulVecLin` 的定义

English:
abbreviation Matrix.mulVecLin
  signature: [Fintype n] (M : Matrix m n R)
  body: mulVecBilin R R M

中文:
缩写 Matrix.mulVecLin
  签名: [Fintype n] (M : Matrix m n R)
  定义体: mulVecBilin R R M

Depends on / 依赖: mulVecBilin
-/
abbrev Matrix.mulVecLin [Fintype n] (M : Matrix m n R) : (n -> R) ->ₗ[R] m -> R := mulVecBilin R R M

/--
theorem `Matrix.coe_mulVecLin` / 定理 `Matrix.coe_mulVecLin`

English:
theorem Matrix.coe_mulVecLin
  given: [Fintype n] (M : Matrix m n R)
  proof: rfl

@[simp]

中文:
定理 Matrix.coe_mulVecLin
  条件: [Fintype n] (M : Matrix m n R)
  证明: rfl

@[simp]
-/
theorem Matrix.coe_mulVecLin [Fintype n] (M : Matrix m n R) :
    (M.mulVecLin : _ -> _) = M.mulVec := rfl

@[simp]
/--
theorem `Matrix.mulVecLin_apply` / 定理 `Matrix.mulVecLin_apply`

English:
theorem Matrix.mulVecLin_apply
  given: [Fintype n] (M : Matrix m n R) (v : n -> R)
  proof: rfl

@[simp]

中文:
定理 Matrix.mulVecLin_apply
  条件: [Fintype n] (M : Matrix m n R) (v : n -> R)
  证明: rfl

@[simp]
-/
theorem Matrix.mulVecLin_apply [Fintype n] (M : Matrix m n R) (v : n -> R) :
    M.mulVecLin v = M *ᵥ v :=
  rfl

@[simp]
/--
theorem `Matrix.mulVecLin_zero` / 定理 `Matrix.mulVecLin_zero`

English:
theorem Matrix.mulVecLin_zero
  given: [Fintype n]
  statement: Matrix.mulVecLin (0 : Matrix m n R) = 0
  proof: LinearMap.ext zero_mulVec

@[simp]

中文:
定理 Matrix.mulVecLin_zero
  条件: [Fintype n]
  结论: Matrix.mulVecLin (0 : Matrix m n R) = 0
  证明: LinearMap.ext zero_mulVec

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, zero_mulVec
-/
theorem Matrix.mulVecLin_zero [Fintype n] : Matrix.mulVecLin (0 : Matrix m n R) = 0 :=
  LinearMap.ext zero_mulVec

@[simp]
/--
theorem `Matrix.mulVecLin_add` / 定理 `Matrix.mulVecLin_add`

English:
theorem Matrix.mulVecLin_add
  given: [Fintype n] (M N : Matrix m n R)
  proof: LinearMap.ext fun _ => add_mulVec _ _ _

中文:
定理 Matrix.mulVecLin_add
  条件: [Fintype n] (M N : Matrix m n R)
  证明: LinearMap.ext fun _ => add_mulVec _ _ _

Depends on / 依赖: LinearMap, LinearMap.ext, add_mulVec
-/
theorem Matrix.mulVecLin_add [Fintype n] (M N : Matrix m n R) :
    (M + N).mulVecLin = M.mulVecLin + N.mulVecLin :=
  LinearMap.ext fun _ => add_mulVec _ _ _

/--
theorem `Matrix.mulVecLin_transpose` / 定理 `Matrix.mulVecLin_transpose`

English:
theorem Matrix.mulVecLin_transpose
  given: [Fintype m] (M : Matrix m n R)
  proof: by
  ext; simp [mulVec_transpose]

中文:
定理 Matrix.mulVecLin_transpose
  条件: [Fintype m] (M : Matrix m n R)
  证明: by
  ext; simp [mulVec_transpose]
-/
@[simp] theorem Matrix.mulVecLin_transpose [Fintype m] (M : Matrix m n R) :
    Mᵀ.mulVecLin = M.vecMulLinear := by
  ext; simp [mulVec_transpose]

/--
theorem `Matrix.vecMulLinear_transpose` / 定理 `Matrix.vecMulLinear_transpose`

English:
theorem Matrix.vecMulLinear_transpose
  given: [Fintype n] (M : Matrix m n R)
  proof: by
  ext; simp [vecMul_transpose]

中文:
定理 Matrix.vecMulLinear_transpose
  条件: [Fintype n] (M : Matrix m n R)
  证明: by
  ext; simp [vecMul_transpose]
-/
@[simp] theorem Matrix.vecMulLinear_transpose [Fintype n] (M : Matrix m n R) :
    Mᵀ.vecMulLinear = M.mulVecLin := by
  ext; simp [vecMul_transpose]

/--
theorem `Matrix.mulVecLin_submatrix` / 定理 `Matrix.mulVecLin_submatrix`

English:
theorem Matrix.mulVecLin_submatrix
  statement: [Fintype n] [Fintype l] (f₁ : m -> k) (e₂ : n ≃ l)
  proof: LinearMap.ext fun _ => submatrix_mulVec_equiv _ _ _ _

中文:
定理 Matrix.mulVecLin_submatrix
  结论: [Fintype n] [Fintype l] (f₁ : m -> k) (e₂ : n ≃ l)
  证明: LinearMap.ext fun _ => submatrix_mulVec_equiv _ _ _ _

Depends on / 依赖: LinearMap, LinearMap.ext, submatrix_mulVec_equiv
-/
theorem Matrix.mulVecLin_submatrix [Fintype n] [Fintype l] (f₁ : m -> k) (e₂ : n ≃ l)
    (M : Matrix k l R) :
    (M.submatrix f₁ e₂).mulVecLin = funLeft R R f₁ ∘ₗ M.mulVecLin ∘ₗ funLeft _ _ e₂.symm :=
  LinearMap.ext fun _ => submatrix_mulVec_equiv _ _ _ _

/--
theorem `Matrix.mulVecLin_reindex` / 定理 `Matrix.mulVecLin_reindex`

English:
theorem Matrix.mulVecLin_reindex
  statement: [Fintype n] [Fintype l] (e₁ : k ≃ m) (e₂ : l ≃ n)
  proof: Matrix.mulVecLin_submatrix _ _ _

中文:
定理 Matrix.mulVecLin_reindex
  结论: [Fintype n] [Fintype l] (e₁ : k ≃ m) (e₂ : l ≃ n)
  证明: Matrix.mulVecLin_submatrix _ _ _

Depends on / 依赖: Matrix, Matrix.mulVecLin_submatrix, mulVecLin_submatrix
-/
theorem Matrix.mulVecLin_reindex [Fintype n] [Fintype l] (e₁ : k ≃ m) (e₂ : l ≃ n)
    (M : Matrix k l R) :
    (reindex e₁ e₂ M).mulVecLin =
      ↑(LinearEquiv.funCongrLeft R R e₁.symm) ∘ₗ
        M.mulVecLin ∘ₗ ↑(LinearEquiv.funCongrLeft R R e₂) :=
  Matrix.mulVecLin_submatrix _ _ _

variable [Fintype n]

@[simp]
/--
theorem `Matrix.mulVecLin_one` / 定理 `Matrix.mulVecLin_one`

English:
theorem Matrix.mulVecLin_one
  given: [DecidableEq n]
  proof: by
  ext; simp [Matrix.one_apply, Pi.single_apply, eq_comm]

@[simp]

中文:
定理 Matrix.mulVecLin_one
  条件: [DecidableEq n]
  证明: by
  ext; simp [Matrix.one_apply, Pi.single_apply, eq_comm]

@[simp]

Depends on / 依赖: Matrix, Matrix.one_apply, Pi.single_apply, eq_comm, one_apply, single_apply
-/
theorem Matrix.mulVecLin_one [DecidableEq n] :
    Matrix.mulVecLin (1 : Matrix n n R) = LinearMap.id := by
  ext; simp [Matrix.one_apply, Pi.single_apply, eq_comm]

@[simp]
/--
theorem `Matrix.mulVecLin_mul` / 定理 `Matrix.mulVecLin_mul`

English:
theorem Matrix.mulVecLin_mul
  given: [Fintype m] (M : Matrix l m R) (N : Matrix m n R)
  proof: LinearMap.ext fun _ => (mulVec_mulVec _ _ _).symm

中文:
定理 Matrix.mulVecLin_mul
  条件: [Fintype m] (M : Matrix l m R) (N : Matrix m n R)
  证明: LinearMap.ext fun _ => (mulVec_mulVec _ _ _).symm

Depends on / 依赖: LinearMap, LinearMap.ext, mulVec_mulVec
-/
theorem Matrix.mulVecLin_mul [Fintype m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.mulVecLin (M * N) = (Matrix.mulVecLin M).comp (Matrix.mulVecLin N) :=
  LinearMap.ext fun _ => (mulVec_mulVec _ _ _).symm

/--
theorem `Matrix.ker_mulVecLin_eq_bot_iff` / 定理 `Matrix.ker_mulVecLin_eq_bot_iff`

English:
theorem Matrix.ker_mulVecLin_eq_bot_iff
  given: {M : Matrix m n R}
  proof: by
  simp only [Submodule.eq_bot_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]

中文:
定理 Matrix.ker_mulVecLin_eq_bot_iff
  条件: {M : Matrix m n R}
  证明: by
  simp only [Submodule.eq_bot_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Matrix, Matrix.mulVecLin_apply, Submodule, Submodule.eq_bot_iff, eq_bot_iff, mem_ker, mulVecLin_apply
-/
theorem Matrix.ker_mulVecLin_eq_bot_iff {M : Matrix m n R} :
    (LinearMap.ker M.mulVecLin) = ⊥ ↔ forall v, M *ᵥ v = 0 -> v = 0 := by
  simp only [Submodule.eq_bot_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]

/--
theorem `Matrix.range_mulVecLin` / 定理 `Matrix.range_mulVecLin`

English:
theorem Matrix.range_mulVecLin
  given: (M : Matrix m n R)
  proof: by
  rw [← vecMulLinear_transpose]; rw [range_vecMulLinear]; rw [row_transpose]

中文:
定理 Matrix.range_mulVecLin
  条件: (M : Matrix m n R)
  证明: by
  rw [← vecMulLinear_transpose]; rw [range_vecMulLinear]; rw [row_transpose]

Depends on / 依赖: range_vecMulLinear, row_transpose, vecMulLinear_transpose
-/
theorem Matrix.range_mulVecLin (M : Matrix m n R) :
    LinearMap.range M.mulVecLin = span R (range M.col) := by
  rw [← vecMulLinear_transpose]; rw [range_vecMulLinear]; rw [row_transpose]

/--
theorem `Matrix.mulVec_injective_iff` / 定理 `Matrix.mulVec_injective_iff`

English:
theorem Matrix.mulVec_injective_iff
  given: {M : Matrix m n R}
  proof: by
  change Function.Injective (fun x => _) ↔ _
  simp_rw [← M.vecMul_transpose, vecMul_injective_iff, row_transpose]

中文:
定理 Matrix.mulVec_injective_iff
  条件: {M : Matrix m n R}
  证明: by
  change Function.Injective (fun x => _) ↔ _
  simp_rw [← M.vecMul_transpose, vecMul_injective_iff, row_transpose]

Depends on / 依赖: Function, Function.Injective, Injective, M.vecMul_transpose, row_transpose, simp_rw, vecMul_injective_iff, vecMul_transpose
-/
theorem Matrix.mulVec_injective_iff {M : Matrix m n R} :
    Function.Injective M.mulVec ↔ LinearIndependent R M.col := by
  change Function.Injective (fun x => _) ↔ _
  simp_rw [← M.vecMul_transpose, vecMul_injective_iff, row_transpose]

/--
lemma `Matrix.linearIndependent_cols_of_isUnit` / 引理 `Matrix.linearIndependent_cols_of_isUnit`

English:
lemma Matrix.linearIndependent_cols_of_isUnit
  statement: [Fintype m]
  proof: by
  rw [← Matrix.mulVec_injective_iff]
  exact Matrix.mulVec_injective_of_isUnit ha

中文:
引理 Matrix.linearIndependent_cols_of_isUnit
  结论: [Fintype m]
  证明: by
  rw [← Matrix.mulVec_injective_iff]
  exact Matrix.mulVec_injective_of_isUnit ha

Depends on / 依赖: Matrix, Matrix.mulVec_injective_iff, Matrix.mulVec_injective_of_isUnit, mulVec_injective_iff, mulVec_injective_of_isUnit
-/
lemma Matrix.linearIndependent_cols_of_isUnit [Fintype m]
    {A : Matrix m m R} [DecidableEq m] (ha : IsUnit A) :
    LinearIndependent R A.col := by
  rw [← Matrix.mulVec_injective_iff]
  exact Matrix.mulVec_injective_of_isUnit ha

end mulVec

section ToMatrix'

variable {R : Type*} [CommSemiring R]
variable {k l m n : Type*} [DecidableEq n] [Fintype n]

/--
Definition of `LinearMap.toMatrix'` / `LinearMap.toMatrix'` 的定义

English:
definition LinearMap.toMatrix'
  signature: : ((n -> R) ->ₗ[R] m -> R) ≃ₗ[R] Matrix m n R where
  body: of fun i j => f (Pi.single j 1) i
  invFun := Matrix.mulVecLin
  right_inv M := by
    ext i j
    simp only [Matrix.mulVec_single_one, col_apply, Matrix.mulVecLin_apply, of_apply]
  left_inv f := by
    apply (Pi.basisFun R n).ext
    intro j; ext i
    simp only [Pi.basisFun_apply, Matrix.mulVec_s

中文:
定义 LinearMap.toMatrix'
  签名: : ((n -> R) ->ₗ[R] m -> R) ≃ₗ[R] Matrix m n R where
  定义体: of fun i j => f (Pi.single j 1) i
  invFun := Matrix.mulVecLin
  right_inv M := by
    ext i j
    simp only [Matrix.mulVec_single_one, col_apply, Matrix.mulVecLin_apply, of_apply]
  left_inv f := by
    apply (Pi.basisFun R n).ext
    intro j; ext i
    simp only [Pi.basisFun_apply, Matrix.mulVec_s
-/
def LinearMap.toMatrix' : ((n -> R) ->ₗ[R] m -> R) ≃ₗ[R] Matrix m n R where
  toFun f := of fun i j => f (Pi.single j 1) i
  invFun := Matrix.mulVecLin
  right_inv M := by
    ext i j
    simp only [Matrix.mulVec_single_one, col_apply, Matrix.mulVecLin_apply, of_apply]
  left_inv f := by
    apply (Pi.basisFun R n).ext
    intro j; ext i
    simp only [Pi.basisFun_apply, Matrix.mulVec_single_one, col_apply,
      Matrix.mulVecLin_apply, of_apply]
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, of_apply, Matrix.add_apply]
  map_smul' c f := by
    ext i j
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, of_apply, Matrix.smul_apply]

/--
Definition of `Matrix.toLin'` / `Matrix.toLin'` 的定义

English:
definition Matrix.toLin'
  signature: : Matrix m n R ≃ₗ[R] (n -> R) ->ₗ[R] m -> R
  body: LinearMap.toMatrix'.symm

中文:
定义 Matrix.toLin'
  签名: : Matrix m n R ≃ₗ[R] (n -> R) ->ₗ[R] m -> R
  定义体: LinearMap.toMatrix'.symm

Depends on / 依赖: LinearMap, LinearMap.toMatrix, toMatrix
-/
def Matrix.toLin' : Matrix m n R ≃ₗ[R] (n -> R) ->ₗ[R] m -> R :=
  LinearMap.toMatrix'.symm

/--
theorem `Matrix.toLin'_apply'` / 定理 `Matrix.toLin'_apply'`

English:
theorem Matrix.toLin'_apply'
  given: (M : Matrix m n R)
  statement: Matrix.toLin' M = M.mulVecLin
  proof: rfl

@[simp]

中文:
定理 Matrix.toLin'_apply'
  条件: (M : Matrix m n R)
  结论: Matrix.toLin' M = M.mulVecLin
  证明: rfl

@[simp]
-/
theorem Matrix.toLin'_apply' (M : Matrix m n R) : Matrix.toLin' M = M.mulVecLin :=
  rfl

@[simp]
/--
theorem `LinearMap.toMatrix'_symm` / 定理 `LinearMap.toMatrix'_symm`

English:
theorem LinearMap.toMatrix'_symm
  proof: rfl

@[simp]

中文:
定理 LinearMap.toMatrix'_symm
  证明: rfl

@[simp]
-/
theorem LinearMap.toMatrix'_symm :
    (LinearMap.toMatrix'.symm : Matrix m n R ≃ₗ[R] _) = Matrix.toLin' :=
  rfl

@[simp]
/--
theorem `Matrix.toLin'_symm` / 定理 `Matrix.toLin'_symm`

English:
theorem Matrix.toLin'_symm
  proof: rfl

@[simp]

中文:
定理 Matrix.toLin'_symm
  证明: rfl

@[simp]
-/
theorem Matrix.toLin'_symm :
    (Matrix.toLin'.symm : ((n -> R) ->ₗ[R] m -> R) ≃ₗ[R] _) = LinearMap.toMatrix' :=
  rfl

@[simp]
/--
theorem `LinearMap.toMatrix'_toLin'` / 定理 `LinearMap.toMatrix'_toLin'`

English:
theorem LinearMap.toMatrix'_toLin'
  given: (M : Matrix m n R)
  statement: LinearMap.toMatrix' (Matrix.toLin' M) = M
  proof: LinearMap.toMatrix'.apply_symm_apply M

@[simp]

中文:
定理 LinearMap.toMatrix'_toLin'
  条件: (M : Matrix m n R)
  结论: LinearMap.toMatrix' (Matrix.toLin' M) = M
  证明: LinearMap.toMatrix'.apply_symm_apply M

@[simp]
-/
theorem LinearMap.toMatrix'_toLin' (M : Matrix m n R) : LinearMap.toMatrix' (Matrix.toLin' M) = M :=
  LinearMap.toMatrix'.apply_symm_apply M

@[simp]
/--
theorem `Matrix.toLin'_toMatrix'` / 定理 `Matrix.toLin'_toMatrix'`

English:
theorem Matrix.toLin'_toMatrix'
  given: (f : (n -> R) ->ₗ[R] m -> R)
  proof: Matrix.toLin'.apply_symm_apply f

@[simp]

中文:
定理 Matrix.toLin'_toMatrix'
  条件: (f : (n -> R) ->ₗ[R] m -> R)
  证明: Matrix.toLin'.apply_symm_apply f

@[simp]
-/
theorem Matrix.toLin'_toMatrix' (f : (n -> R) ->ₗ[R] m -> R) :
    Matrix.toLin' (LinearMap.toMatrix' f) = f :=
  Matrix.toLin'.apply_symm_apply f

@[simp]
/--
theorem `LinearMap.toMatrix'_apply` / 定理 `LinearMap.toMatrix'_apply`

English:
theorem LinearMap.toMatrix'_apply
  given: (f : (n -> R) ->ₗ[R] m -> R) (i j)
  proof: rfl

@[simp]

中文:
定理 LinearMap.toMatrix'_apply
  条件: (f : (n -> R) ->ₗ[R] m -> R) (i j)
  证明: rfl

@[simp]
-/
theorem LinearMap.toMatrix'_apply (f : (n -> R) ->ₗ[R] m -> R) (i j) :
    LinearMap.toMatrix' f i j = f (Pi.single j 1) i :=
  rfl

@[simp]
/--
theorem `Matrix.toLin'_apply` / 定理 `Matrix.toLin'_apply`

English:
theorem Matrix.toLin'_apply
  given: (M : Matrix m n R) (v : n -> R)
  statement: Matrix.toLin' M v = M *ᵥ v
  proof: rfl

@[simp]

中文:
定理 Matrix.toLin'_apply
  条件: (M : Matrix m n R) (v : n -> R)
  结论: Matrix.toLin' M v = M *ᵥ v
  证明: rfl

@[simp]
-/
theorem Matrix.toLin'_apply (M : Matrix m n R) (v : n -> R) : Matrix.toLin' M v = M *ᵥ v :=
  rfl

@[simp]
/--
theorem `LinearMap.toMatrix'_mulVec` / 定理 `LinearMap.toMatrix'_mulVec`

English:
theorem LinearMap.toMatrix'_mulVec
  given: (f : (n -> R) ->ₗ[R] m -> R) (v : n -> R)
  proof: by
  rw [← toLin'_apply]; rw [toLin'_toMatrix']

@[simp]

中文:
定理 LinearMap.toMatrix'_mulVec
  条件: (f : (n -> R) ->ₗ[R] m -> R) (v : n -> R)
  证明: by
  rw [← toLin'_apply]; rw [toLin'_toMatrix']

@[simp]
-/
theorem LinearMap.toMatrix'_mulVec (f : (n -> R) ->ₗ[R] m -> R) (v : n -> R) :
    LinearMap.toMatrix' f *ᵥ v = f v := by
  rw [← toLin'_apply]; rw [toLin'_toMatrix']

@[simp]
/--
theorem `Matrix.toLin'_one` / 定理 `Matrix.toLin'_one`

English:
theorem Matrix.toLin'_one
  statement: Matrix.toLin' (1 : Matrix n n R) = LinearMap.id
  proof: Matrix.mulVecLin_one

@[simp]

中文:
定理 Matrix.toLin'_one
  结论: Matrix.toLin' (1 : Matrix n n R) = LinearMap.id
  证明: Matrix.mulVecLin_one

@[simp]
-/
theorem Matrix.toLin'_one : Matrix.toLin' (1 : Matrix n n R) = LinearMap.id :=
  Matrix.mulVecLin_one

@[simp]
/--
theorem `LinearMap.toMatrix'_id` / 定理 `LinearMap.toMatrix'_id`

English:
theorem LinearMap.toMatrix'_id
  statement: LinearMap.toMatrix' (LinearMap.id : (n -> R) ->ₗ[R] n -> R) = 1
  proof: by
  ext
  rw [Matrix.one_apply]; rw [LinearMap.toMatrix'_apply]; rw [id_apply]; rw [Pi.single_apply]

@[simp]

中文:
定理 LinearMap.toMatrix'_id
  结论: LinearMap.toMatrix' (LinearMap.id : (n -> R) ->ₗ[R] n -> R) = 1
  证明: by
  ext
  rw [Matrix.one_apply]; rw [LinearMap.toMatrix'_apply]; rw [id_apply]; rw [Pi.single_apply]

@[simp]
-/
theorem LinearMap.toMatrix'_id : LinearMap.toMatrix' (LinearMap.id : (n -> R) ->ₗ[R] n -> R) = 1 := by
  ext
  rw [Matrix.one_apply]; rw [LinearMap.toMatrix'_apply]; rw [id_apply]; rw [Pi.single_apply]

@[simp]
/--
theorem `LinearMap.toMatrix'_one` / 定理 `LinearMap.toMatrix'_one`

English:
theorem LinearMap.toMatrix'_one
  statement: LinearMap.toMatrix' (1 : (n -> R) ->ₗ[R] n -> R) = 1
  proof: LinearMap.toMatrix'_id

@[simp]

中文:
定理 LinearMap.toMatrix'_one
  结论: LinearMap.toMatrix' (1 : (n -> R) ->ₗ[R] n -> R) = 1
  证明: LinearMap.toMatrix'_id

@[simp]
-/
theorem LinearMap.toMatrix'_one : LinearMap.toMatrix' (1 : (n -> R) ->ₗ[R] n -> R) = 1 :=
  LinearMap.toMatrix'_id

@[simp]
/--
theorem `Matrix.toLin'_mul` / 定理 `Matrix.toLin'_mul`

English:
theorem Matrix.toLin'_mul
  given: [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R)
  proof: Matrix.mulVecLin_mul _ _

@[simp]

中文:
定理 Matrix.toLin'_mul
  条件: [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R)
  证明: Matrix.mulVecLin_mul _ _

@[simp]
-/
theorem Matrix.toLin'_mul [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.toLin' (M * N) = (Matrix.toLin' M).comp (Matrix.toLin' N) :=
  Matrix.mulVecLin_mul _ _

@[simp]
/--
theorem `Matrix.toLin'_pow` / 定理 `Matrix.toLin'_pow`

English:
theorem Matrix.toLin'_pow
  given: (M : Matrix n n R) (k : Nat)
  proof: by
  induction k with
  | zero => simp [End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin'_mul, ih, Module.End.mul_eq_comp]

@[simp]

中文:
定理 Matrix.toLin'_pow
  条件: (M : Matrix n n R) (k : 自然数)
  证明: by
  induction k with
  | zero => simp [End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin'_mul, ih, Module.End.mul_eq_comp]

@[simp]
-/
theorem Matrix.toLin'_pow (M : Matrix n n R) (k : Nat) :
    (M ^ k).toLin' = M.toLin' ^ k := by
  induction k with
  | zero => simp [End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin'_mul, ih, Module.End.mul_eq_comp]

@[simp]
/--
theorem `Matrix.toLin'_submatrix` / 定理 `Matrix.toLin'_submatrix`

English:
theorem Matrix.toLin'_submatrix
  statement: [Fintype l] [DecidableEq l] (f₁ : m -> k) (e₂ : n ≃ l)
  proof: Matrix.mulVecLin_submatrix _ _ _

中文:
定理 Matrix.toLin'_submatrix
  结论: [Fintype l] [DecidableEq l] (f₁ : m -> k) (e₂ : n ≃ l)
  证明: Matrix.mulVecLin_submatrix _ _ _
-/
theorem Matrix.toLin'_submatrix [Fintype l] [DecidableEq l] (f₁ : m -> k) (e₂ : n ≃ l)
    (M : Matrix k l R) :
    Matrix.toLin' (M.submatrix f₁ e₂) =
      funLeft R R f₁ ∘ₗ (Matrix.toLin' M) ∘ₗ funLeft _ _ e₂.symm :=
  Matrix.mulVecLin_submatrix _ _ _

/--
theorem `Matrix.toLin'_reindex` / 定理 `Matrix.toLin'_reindex`

English:
theorem Matrix.toLin'_reindex
  statement: [Fintype l] [DecidableEq l] (e₁ : k ≃ m) (e₂ : l ≃ n)
  proof: Matrix.mulVecLin_reindex _ _ _

中文:
定理 Matrix.toLin'_reindex
  结论: [Fintype l] [DecidableEq l] (e₁ : k ≃ m) (e₂ : l ≃ n)
  证明: Matrix.mulVecLin_reindex _ _ _
-/
theorem Matrix.toLin'_reindex [Fintype l] [DecidableEq l] (e₁ : k ≃ m) (e₂ : l ≃ n)
    (M : Matrix k l R) :
    Matrix.toLin' (reindex e₁ e₂ M) =
      ↑(LinearEquiv.funCongrLeft R R e₁.symm) ∘ₗ (Matrix.toLin' M) ∘ₗ
        ↑(LinearEquiv.funCongrLeft R R e₂) :=
  Matrix.mulVecLin_reindex _ _ _

/--
theorem `Matrix.toLin'_mul_apply` / 定理 `Matrix.toLin'_mul_apply`

English:
theorem Matrix.toLin'_mul_apply
  statement: [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R)
  proof: by
  rw [Matrix.toLin'_mul]; rw [LinearMap.comp_apply]

中文:
定理 Matrix.toLin'_mul_apply
  结论: [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R)
  证明: by
  rw [Matrix.toLin'_mul]; rw [LinearMap.comp_apply]
-/
theorem Matrix.toLin'_mul_apply [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R)
    (x) : Matrix.toLin' (M * N) x = Matrix.toLin' M (Matrix.toLin' N x) := by
  rw [Matrix.toLin'_mul]; rw [LinearMap.comp_apply]

/--
theorem `LinearMap.toMatrix'_comp` / 定理 `LinearMap.toMatrix'_comp`

English:
theorem LinearMap.toMatrix'_comp
  statement: [Fintype l] [DecidableEq l] (f : (n -> R) ->ₗ[R] m -> R)
  proof: by
  suffices f.comp g = Matrix.toLin' (LinearMap.toMatrix' f * LinearMap.toMatrix' g) by
    rw [this]; rw [LinearMap.toMatrix'_toLin']
  rw [Matrix.toLin'_mul]; rw [Matrix.toLin'_toMatrix']; rw [Matrix.toLin'_toMatrix']

中文:
定理 LinearMap.toMatrix'_comp
  结论: [Fintype l] [DecidableEq l] (f : (n -> R) ->ₗ[R] m -> R)
  证明: by
  suffices f.comp g = Matrix.toLin' (LinearMap.toMatrix' f * LinearMap.toMatrix' g) by
    rw [this]; rw [LinearMap.toMatrix'_toLin']
  rw [Matrix.toLin'_mul]; rw [Matrix.toLin'_toMatrix']; rw [Matrix.toLin'_toMatrix']
-/
theorem LinearMap.toMatrix'_comp [Fintype l] [DecidableEq l] (f : (n -> R) ->ₗ[R] m -> R)
    (g : (l -> R) ->ₗ[R] n -> R) :
    LinearMap.toMatrix' (f.comp g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g := by
  suffices f.comp g = Matrix.toLin' (LinearMap.toMatrix' f * LinearMap.toMatrix' g) by
    rw [this]; rw [LinearMap.toMatrix'_toLin']
  rw [Matrix.toLin'_mul]; rw [Matrix.toLin'_toMatrix']; rw [Matrix.toLin'_toMatrix']

/--
theorem `LinearMap.toMatrix'_mul` / 定理 `LinearMap.toMatrix'_mul`

English:
theorem LinearMap.toMatrix'_mul
  given: [Fintype m] [DecidableEq m] (f g : (m -> R) ->ₗ[R] m -> R)
  proof: LinearMap.toMatrix'_comp f g

中文:
定理 LinearMap.toMatrix'_mul
  条件: [Fintype m] [DecidableEq m] (f g : (m -> R) ->ₗ[R] m -> R)
  证明: LinearMap.toMatrix'_comp f g
-/
theorem LinearMap.toMatrix'_mul [Fintype m] [DecidableEq m] (f g : (m -> R) ->ₗ[R] m -> R) :
    LinearMap.toMatrix' (f * g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g :=
  LinearMap.toMatrix'_comp f g

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `LinearMap.toMatrix'_algebraMap` / 定理 `LinearMap.toMatrix'_algebraMap`

English:
theorem LinearMap.toMatrix'_algebraMap
  given: (x : R)
  proof: by
  simp [Module.algebraMap_end_eq_smul_id, smul_eq_diagonal_mul]

中文:
定理 LinearMap.toMatrix'_algebraMap
  条件: (x : R)
  证明: by
  simp [Module.algebraMap_end_eq_smul_id, smul_eq_diagonal_mul]
-/
theorem LinearMap.toMatrix'_algebraMap (x : R) :
    LinearMap.toMatrix' (algebraMap R (Module.End R (n -> R)) x) = scalar n x := by
  simp [Module.algebraMap_end_eq_smul_id, smul_eq_diagonal_mul]

/--
theorem `Matrix.ker_toLin'_eq_bot_iff` / 定理 `Matrix.ker_toLin'_eq_bot_iff`

English:
theorem Matrix.ker_toLin'_eq_bot_iff
  given: {M : Matrix n n R}
  proof: Matrix.ker_mulVecLin_eq_bot_iff

中文:
定理 Matrix.ker_toLin'_eq_bot_iff
  条件: {M : Matrix n n R}
  证明: Matrix.ker_mulVecLin_eq_bot_iff

Depends on / 依赖: Matrix, Matrix.ker_mulVecLin_eq_bot_iff, ker_mulVecLin_eq_bot_iff
-/
theorem Matrix.ker_toLin'_eq_bot_iff {M : Matrix n n R} :
    LinearMap.ker (Matrix.toLin' M) = ⊥ ↔ forall v, M *ᵥ v = 0 -> v = 0 :=
  Matrix.ker_mulVecLin_eq_bot_iff

/--
theorem `Matrix.range_toLin'` / 定理 `Matrix.range_toLin'`

English:
theorem Matrix.range_toLin'
  given: (M : Matrix m n R)
  proof: Matrix.range_mulVecLin _

中文:
定理 Matrix.range_toLin'
  条件: (M : Matrix m n R)
  证明: Matrix.range_mulVecLin _

Depends on / 依赖: Matrix, Matrix.range_mulVecLin, range_mulVecLin
-/
theorem Matrix.range_toLin' (M : Matrix m n R) :
    LinearMap.range (Matrix.toLin' M) = span R (range M.col) :=
  Matrix.range_mulVecLin _

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `m → A`
and `n → A` corresponding to `M.mulVec` and `M'.mulVec`. -/
@[simps]
/--
Definition of `Matrix.toLin'OfInv` / `Matrix.toLin'OfInv` 的定义

English:
definition Matrix.toLin'OfInv
  signature: [Fintype m] [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R}
  body: { Matrix.toLin' M' with
    toFun := Matrix.toLin' M'
    invFun := Matrix.toLin' M
    left_inv := fun x => by rw [← Matrix.toLin'_mul_apply, hMM', Matrix.toLin'_one, id_apply]
    right_inv := fun x => by
      rw [← Matrix.toLin'_mul_apply]; rw [hM'M]; rw [Matrix.toLin'_one]; rw [id_apply] }

中文:
定义 Matrix.toLin'OfInv
  签名: [Fintype m] [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R}
  定义体: { Matrix.toLin' M' with
    toFun := Matrix.toLin' M'
    invFun := Matrix.toLin' M
    left_inv := fun x => by rw [← Matrix.toLin'_mul_apply, hMM', Matrix.toLin'_one, id_apply]
    right_inv := fun x => by
      rw [← Matrix.toLin'_mul_apply]; rw [hM'M]; rw [Matrix.toLin'_one]; rw [id_apply] }
-/
def Matrix.toLin'OfInv [Fintype m] [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R}
    (hMM' : M * M' = 1) (hM'M : M' * M = 1) : (m -> R) ≃ₗ[R] n -> R :=
  { Matrix.toLin' M' with
    toFun := Matrix.toLin' M'
    invFun := Matrix.toLin' M
    left_inv := fun x => by rw [← Matrix.toLin'_mul_apply, hMM', Matrix.toLin'_one, id_apply]
    right_inv := fun x => by
      rw [← Matrix.toLin'_mul_apply]; rw [hM'M]; rw [Matrix.toLin'_one]; rw [id_apply] }

/--
Definition of `LinearMap.toMatrixAlgEquiv'` / `LinearMap.toMatrixAlgEquiv'` 的定义

English:
definition LinearMap.toMatrixAlgEquiv'
  signature: : ((n -> R) ->ₗ[R] n -> R) ≃ₐ[R] Matrix n n R
  body: AlgEquiv.ofLinearEquiv LinearMap.toMatrix' LinearMap.toMatrix'_one LinearMap.toMatrix'_mul

中文:
定义 LinearMap.toMatrixAlgEquiv'
  签名: : ((n -> R) ->ₗ[R] n -> R) ≃ₐ[R] Matrix n n R
  定义体: AlgEquiv.ofLinearEquiv LinearMap.toMatrix' LinearMap.toMatrix'_one LinearMap.toMatrix'_mul

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, LinearMap, LinearMap.toMatrix, _mul, _one, ofLinearEquiv, toMatrix
-/
def LinearMap.toMatrixAlgEquiv' : ((n -> R) ->ₗ[R] n -> R) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv LinearMap.toMatrix' LinearMap.toMatrix'_one LinearMap.toMatrix'_mul

/--
Definition of `Matrix.toLinAlgEquiv'` / `Matrix.toLinAlgEquiv'` 的定义

English:
definition Matrix.toLinAlgEquiv'
  signature: : Matrix n n R ≃ₐ[R] (n -> R) ->ₗ[R] n -> R
  body: LinearMap.toMatrixAlgEquiv'.symm

@[simp]

中文:
定义 Matrix.toLinAlgEquiv'
  签名: : Matrix n n R ≃ₐ[R] (n -> R) ->ₗ[R] n -> R
  定义体: LinearMap.toMatrixAlgEquiv'.symm

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv, toMatrixAlgEquiv
-/
def Matrix.toLinAlgEquiv' : Matrix n n R ≃ₐ[R] (n -> R) ->ₗ[R] n -> R :=
  LinearMap.toMatrixAlgEquiv'.symm

@[simp]
/--
theorem `LinearMap.toMatrixAlgEquiv'_symm` / 定理 `LinearMap.toMatrixAlgEquiv'_symm`

English:
theorem LinearMap.toMatrixAlgEquiv'_symm
  proof: rfl

@[simp]

中文:
定理 LinearMap.toMatrixAlgEquiv'_symm
  证明: rfl

@[simp]
-/
theorem LinearMap.toMatrixAlgEquiv'_symm :
    (LinearMap.toMatrixAlgEquiv'.symm : Matrix n n R ≃ₐ[R] _) = Matrix.toLinAlgEquiv' :=
  rfl

@[simp]
/--
theorem `Matrix.toLinAlgEquiv'_symm` / 定理 `Matrix.toLinAlgEquiv'_symm`

English:
theorem Matrix.toLinAlgEquiv'_symm
  proof: rfl

@[simp]

中文:
定理 Matrix.toLinAlgEquiv'_symm
  证明: rfl

@[simp]
-/
theorem Matrix.toLinAlgEquiv'_symm :
    (Matrix.toLinAlgEquiv'.symm : ((n -> R) ->ₗ[R] n -> R) ≃ₐ[R] _) = LinearMap.toMatrixAlgEquiv' :=
  rfl

@[simp]
/--
theorem `LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv'` / 定理 `LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv'`

English:
theorem LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv'
  given: (M : Matrix n n R)
  proof: LinearMap.toMatrixAlgEquiv'.apply_symm_apply M

@[simp]

中文:
定理 LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv'
  条件: (M : Matrix n n R)
  证明: LinearMap.toMatrixAlgEquiv'.apply_symm_apply M

@[simp]
-/
theorem LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv' M) = M :=
  LinearMap.toMatrixAlgEquiv'.apply_symm_apply M

@[simp]
/--
theorem `Matrix.toLinAlgEquiv'_toMatrixAlgEquiv'` / 定理 `Matrix.toLinAlgEquiv'_toMatrixAlgEquiv'`

English:
theorem Matrix.toLinAlgEquiv'_toMatrixAlgEquiv'
  given: (f : (n -> R) ->ₗ[R] n -> R)
  proof: Matrix.toLinAlgEquiv'.apply_symm_apply f

@[simp]

中文:
定理 Matrix.toLinAlgEquiv'_toMatrixAlgEquiv'
  条件: (f : (n -> R) ->ₗ[R] n -> R)
  证明: Matrix.toLinAlgEquiv'.apply_symm_apply f

@[simp]
-/
theorem Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' (f : (n -> R) ->ₗ[R] n -> R) :
    Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' f) = f :=
  Matrix.toLinAlgEquiv'.apply_symm_apply f

@[simp]
/--
theorem `LinearMap.toMatrixAlgEquiv'_apply` / 定理 `LinearMap.toMatrixAlgEquiv'_apply`

English:
theorem LinearMap.toMatrixAlgEquiv'_apply
  given: (f : (n -> R) ->ₗ[R] n -> R) (i j)
  proof: rfl

@[simp]

中文:
定理 LinearMap.toMatrixAlgEquiv'_apply
  条件: (f : (n -> R) ->ₗ[R] n -> R) (i j)
  证明: rfl

@[simp]
-/
theorem LinearMap.toMatrixAlgEquiv'_apply (f : (n -> R) ->ₗ[R] n -> R) (i j) :
    LinearMap.toMatrixAlgEquiv' f i j = f (Pi.single j 1) i :=
  rfl

@[simp]
/--
theorem `Matrix.toLinAlgEquiv'_apply` / 定理 `Matrix.toLinAlgEquiv'_apply`

English:
theorem Matrix.toLinAlgEquiv'_apply
  given: (M : Matrix n n R) (v : n -> R)
  proof: rfl

中文:
定理 Matrix.toLinAlgEquiv'_apply
  条件: (M : Matrix n n R) (v : n -> R)
  证明: rfl
-/
theorem Matrix.toLinAlgEquiv'_apply (M : Matrix n n R) (v : n -> R) :
    Matrix.toLinAlgEquiv' M v = M *ᵥ v :=
  rfl

/--
theorem `Matrix.toLinAlgEquiv'_one` / 定理 `Matrix.toLinAlgEquiv'_one`

English:
theorem Matrix.toLinAlgEquiv'_one
  statement: Matrix.toLinAlgEquiv' (1 : Matrix n n R) = LinearMap.id
  proof: Matrix.toLin'_one

@[simp]

中文:
定理 Matrix.toLinAlgEquiv'_one
  结论: Matrix.toLinAlgEquiv' (1 : Matrix n n R) = LinearMap.id
  证明: Matrix.toLin'_one

@[simp]
-/
theorem Matrix.toLinAlgEquiv'_one : Matrix.toLinAlgEquiv' (1 : Matrix n n R) = LinearMap.id :=
  Matrix.toLin'_one

@[simp]
/--
theorem `LinearMap.toMatrixAlgEquiv'_id` / 定理 `LinearMap.toMatrixAlgEquiv'_id`

English:
theorem LinearMap.toMatrixAlgEquiv'_id
  proof: LinearMap.toMatrix'_id

中文:
定理 LinearMap.toMatrixAlgEquiv'_id
  证明: LinearMap.toMatrix'_id
-/
theorem LinearMap.toMatrixAlgEquiv'_id :
    LinearMap.toMatrixAlgEquiv' (LinearMap.id : (n -> R) ->ₗ[R] n -> R) = 1 :=
  LinearMap.toMatrix'_id

/--
theorem `LinearMap.toMatrixAlgEquiv'_comp` / 定理 `LinearMap.toMatrixAlgEquiv'_comp`

English:
theorem LinearMap.toMatrixAlgEquiv'_comp
  given: (f g : (n -> R) ->ₗ[R] n -> R)
  proof: LinearMap.toMatrix'_comp _ _

中文:
定理 LinearMap.toMatrixAlgEquiv'_comp
  条件: (f g : (n -> R) ->ₗ[R] n -> R)
  证明: LinearMap.toMatrix'_comp _ _
-/
theorem LinearMap.toMatrixAlgEquiv'_comp (f g : (n -> R) ->ₗ[R] n -> R) :
    LinearMap.toMatrixAlgEquiv' (f.comp g) =
      LinearMap.toMatrixAlgEquiv' f * LinearMap.toMatrixAlgEquiv' g :=
  LinearMap.toMatrix'_comp _ _

/--
theorem `LinearMap.toMatrixAlgEquiv'_mul` / 定理 `LinearMap.toMatrixAlgEquiv'_mul`

English:
theorem LinearMap.toMatrixAlgEquiv'_mul
  given: (f g : (n -> R) ->ₗ[R] n -> R)
  proof: LinearMap.toMatrixAlgEquiv'_comp f g

@[simp]

中文:
定理 LinearMap.toMatrixAlgEquiv'_mul
  条件: (f g : (n -> R) ->ₗ[R] n -> R)
  证明: LinearMap.toMatrixAlgEquiv'_comp f g

@[simp]
-/
theorem LinearMap.toMatrixAlgEquiv'_mul (f g : (n -> R) ->ₗ[R] n -> R) :
    LinearMap.toMatrixAlgEquiv' (f * g) =
      LinearMap.toMatrixAlgEquiv' f * LinearMap.toMatrixAlgEquiv' g :=
  LinearMap.toMatrixAlgEquiv'_comp f g

@[simp]
/--
theorem `LinearMap.isUnit_toMatrix'_iff` / 定理 `LinearMap.isUnit_toMatrix'_iff`

English:
theorem LinearMap.isUnit_toMatrix'_iff
  given: {f : (n -> R) ->ₗ[R] n -> R}
  statement: IsUnit f.toMatrix' ↔ IsUnit f
  proof: isUnit_map_iff LinearMap.toMatrixAlgEquiv' f

@[simp]

中文:
定理 LinearMap.isUnit_toMatrix'_iff
  条件: {f : (n -> R) ->ₗ[R] n -> R}
  结论: IsUnit f.toMatrix' ↔ IsUnit f
  证明: isUnit_map_iff LinearMap.toMatrixAlgEquiv' f

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv, isUnit_map_iff, toMatrixAlgEquiv
-/
theorem LinearMap.isUnit_toMatrix'_iff {f : (n -> R) ->ₗ[R] n -> R} : IsUnit f.toMatrix' ↔ IsUnit f :=
  isUnit_map_iff LinearMap.toMatrixAlgEquiv' f

@[simp]
/--
theorem `Matrix.isUnit_toLin'_iff` / 定理 `Matrix.isUnit_toLin'_iff`

English:
theorem Matrix.isUnit_toLin'_iff
  given: {M : Matrix n n R}
  statement: IsUnit M.toLin' ↔ IsUnit M
  proof: isUnit_map_iff LinearMap.toMatrixAlgEquiv'.symm M

中文:
定理 Matrix.isUnit_toLin'_iff
  条件: {M : Matrix n n R}
  结论: IsUnit M.toLin' ↔ IsUnit M
  证明: isUnit_map_iff LinearMap.toMatrixAlgEquiv'.symm M

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv, isUnit_map_iff, toMatrixAlgEquiv
-/
theorem Matrix.isUnit_toLin'_iff {M : Matrix n n R} : IsUnit M.toLin' ↔ IsUnit M :=
  isUnit_map_iff LinearMap.toMatrixAlgEquiv'.symm M

end ToMatrix'

section ToMatrix

section Finite

variable {R : Type*} [CommSemiring R]
variable {l m n : Type*} [Fintype n] [Finite m] [DecidableEq n]
variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

/--
Definition of `LinearMap.toMatrix` / `LinearMap.toMatrix` 的定义

English:
definition LinearMap.toMatrix
  signature: : (M₁ ->ₗ[R] M₂) ≃ₗ[R] Matrix m n R
  body: LinearEquiv.trans (LinearEquiv.arrowCongr v₁.equivFun v₂.equivFun) LinearMap.toMatrix'

中文:
定义 LinearMap.toMatrix
  签名: : (M₁ ->ₗ[R] M₂) ≃ₗ[R] Matrix m n R
  定义体: LinearEquiv.trans (LinearEquiv.arrowCongr v₁.equivFun v₂.equivFun) LinearMap.toMatrix'

Depends on / 依赖: LinearEquiv, LinearEquiv.arrowCongr, LinearEquiv.trans, LinearMap, LinearMap.toMatrix, arrowCongr, equivFun, toMatrix
-/
def LinearMap.toMatrix : (M₁ ->ₗ[R] M₂) ≃ₗ[R] Matrix m n R :=
  LinearEquiv.trans (LinearEquiv.arrowCongr v₁.equivFun v₂.equivFun) LinearMap.toMatrix'

/--
theorem `LinearMap.toMatrix_eq_toMatrix'` / 定理 `LinearMap.toMatrix_eq_toMatrix'`

English:
theorem LinearMap.toMatrix_eq_toMatrix'
  proof: rfl

中文:
定理 LinearMap.toMatrix_eq_toMatrix'
  证明: rfl
-/
@[simp] theorem LinearMap.toMatrix_eq_toMatrix' :
    LinearMap.toMatrix (Pi.basisFun R n) (Pi.basisFun R n) = LinearMap.toMatrix' :=
  rfl

/--
Definition of `Matrix.toLin` / `Matrix.toLin` 的定义

English:
definition Matrix.toLin
  signature: : Matrix m n R ≃ₗ[R] M₁ ->ₗ[R] M₂
  body: (LinearMap.toMatrix v₁ v₂).symm

中文:
定义 Matrix.toLin
  签名: : Matrix m n R ≃ₗ[R] M₁ ->ₗ[R] M₂
  定义体: (LinearMap.toMatrix v₁ v₂).symm

Depends on / 依赖: LinearMap, LinearMap.toMatrix, toMatrix
-/
def Matrix.toLin : Matrix m n R ≃ₗ[R] M₁ ->ₗ[R] M₂ :=
  (LinearMap.toMatrix v₁ v₂).symm

/--
theorem `Matrix.toLin_eq_toLin'` / 定理 `Matrix.toLin_eq_toLin'`

English:
theorem Matrix.toLin_eq_toLin'
  statement: Matrix.toLin (Pi.basisFun R n) (Pi.basisFun R m) = Matrix.toLin'
  proof: rfl

@[simp]

中文:
定理 Matrix.toLin_eq_toLin'
  结论: Matrix.toLin (Pi.basisFun R n) (Pi.basisFun R m) = Matrix.toLin'
  证明: rfl

@[simp]
-/
theorem Matrix.toLin_eq_toLin' : Matrix.toLin (Pi.basisFun R n) (Pi.basisFun R m) = Matrix.toLin' :=
  rfl

@[simp]
/--
theorem `LinearMap.toMatrix_symm` / 定理 `LinearMap.toMatrix_symm`

English:
theorem LinearMap.toMatrix_symm
  statement: (LinearMap.toMatrix v₁ v₂).symm = Matrix.toLin v₁ v₂
  proof: rfl

@[simp]

中文:
定理 LinearMap.toMatrix_symm
  结论: (LinearMap.toMatrix v₁ v₂).symm = Matrix.toLin v₁ v₂
  证明: rfl

@[simp]
-/
theorem LinearMap.toMatrix_symm : (LinearMap.toMatrix v₁ v₂).symm = Matrix.toLin v₁ v₂ :=
  rfl

@[simp]
/--
theorem `Matrix.toLin_symm` / 定理 `Matrix.toLin_symm`

English:
theorem Matrix.toLin_symm
  statement: (Matrix.toLin v₁ v₂).symm = LinearMap.toMatrix v₁ v₂
  proof: rfl

@[simp]

中文:
定理 Matrix.toLin_symm
  结论: (Matrix.toLin v₁ v₂).symm = LinearMap.toMatrix v₁ v₂
  证明: rfl

@[simp]
-/
theorem Matrix.toLin_symm : (Matrix.toLin v₁ v₂).symm = LinearMap.toMatrix v₁ v₂ :=
  rfl

@[simp]
/--
theorem `Matrix.toLin_toMatrix` / 定理 `Matrix.toLin_toMatrix`

English:
theorem Matrix.toLin_toMatrix
  given: (f : M₁ ->ₗ[R] M₂)
  proof: by
  rw [← Matrix.toLin_symm]; rw [LinearEquiv.apply_symm_apply]

@[simp]

中文:
定理 Matrix.toLin_toMatrix
  条件: (f : M₁ ->ₗ[R] M₂)
  证明: by
  rw [← Matrix.toLin_symm]; rw [LinearEquiv.apply_symm_apply]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, Matrix, Matrix.toLin_symm, apply_symm_apply, toLin_symm
-/
theorem Matrix.toLin_toMatrix (f : M₁ ->ₗ[R] M₂) :
    Matrix.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f := by
  rw [← Matrix.toLin_symm]; rw [LinearEquiv.apply_symm_apply]

@[simp]
/--
theorem `LinearMap.toMatrix_toLin` / 定理 `LinearMap.toMatrix_toLin`

English:
theorem LinearMap.toMatrix_toLin
  given: (M : Matrix m n R)
  proof: by
  rw [← Matrix.toLin_symm]; rw [LinearEquiv.symm_apply_apply]

中文:
定理 LinearMap.toMatrix_toLin
  条件: (M : Matrix m n R)
  证明: by
  rw [← Matrix.toLin_symm]; rw [LinearEquiv.symm_apply_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_apply, Matrix, Matrix.toLin_symm, symm_apply_apply, toLin_symm
-/
theorem LinearMap.toMatrix_toLin (M : Matrix m n R) :
    LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M := by
  rw [← Matrix.toLin_symm]; rw [LinearEquiv.symm_apply_apply]

/--
theorem `LinearMap.toMatrix_apply` / 定理 `LinearMap.toMatrix_apply`

English:
theorem LinearMap.toMatrix_apply
  given: (f : M₁ ->ₗ[R] M₂) (i : m) (j : n)
  proof: by
  simp [toMatrix]

中文:
定理 LinearMap.toMatrix_apply
  条件: (f : M₁ ->ₗ[R] M₂) (i : m) (j : n)
  证明: by
  simp [toMatrix]

Depends on / 依赖: toMatrix
-/
theorem LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i := by
  simp [toMatrix]

/--
theorem `LinearMap.toMatrix_transpose_apply` / 定理 `LinearMap.toMatrix_transpose_apply`

English:
theorem LinearMap.toMatrix_transpose_apply
  given: (f : M₁ ->ₗ[R] M₂) (j : n)
  proof: funext fun i => f.toMatrix_apply _ _ i j

中文:
定理 LinearMap.toMatrix_transpose_apply
  条件: (f : M₁ ->ₗ[R] M₂) (j : n)
  证明: funext fun i => f.toMatrix_apply _ _ i j

Depends on / 依赖: f.toMatrix_apply, toMatrix_apply
-/
theorem LinearMap.toMatrix_transpose_apply (f : M₁ ->ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  funext fun i => f.toMatrix_apply _ _ i j

/--
theorem `LinearMap.toMatrix_apply'` / 定理 `LinearMap.toMatrix_apply'`

English:
theorem LinearMap.toMatrix_apply'
  given: (f : M₁ ->ₗ[R] M₂) (i : m) (j : n)
  proof: LinearMap.toMatrix_apply v₁ v₂ f i j

中文:
定理 LinearMap.toMatrix_apply'
  条件: (f : M₁ ->ₗ[R] M₂) (i : m) (j : n)
  证明: LinearMap.toMatrix_apply v₁ v₂ f i j

Depends on / 依赖: LinearMap, LinearMap.toMatrix_apply, toMatrix_apply
-/
theorem LinearMap.toMatrix_apply' (f : M₁ ->ₗ[R] M₂) (i : m) (j : n) :
    LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i :=
  LinearMap.toMatrix_apply v₁ v₂ f i j

/--
theorem `LinearMap.toMatrix_transpose_apply'` / 定理 `LinearMap.toMatrix_transpose_apply'`

English:
theorem LinearMap.toMatrix_transpose_apply'
  given: (f : M₁ ->ₗ[R] M₂) (j : n)
  proof: LinearMap.toMatrix_transpose_apply v₁ v₂ f j

中文:
定理 LinearMap.toMatrix_transpose_apply'
  条件: (f : M₁ ->ₗ[R] M₂) (j : n)
  证明: LinearMap.toMatrix_transpose_apply v₁ v₂ f j

Depends on / 依赖: LinearMap, LinearMap.toMatrix_transpose_apply, toMatrix_transpose_apply
-/
theorem LinearMap.toMatrix_transpose_apply' (f : M₁ ->ₗ[R] M₂) (j : n) :
    (LinearMap.toMatrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
  LinearMap.toMatrix_transpose_apply v₁ v₂ f j

/--
theorem `LinearMap.toMatrix_id` / 定理 `LinearMap.toMatrix_id`

English:
theorem LinearMap.toMatrix_id
  statement: LinearMap.toMatrix v₁ v₁ id = 1
  proof: by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]

@[simp]

中文:
定理 LinearMap.toMatrix_id
  结论: LinearMap.toMatrix v₁ v₁ id = 1
  证明: by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_apply, LinearMap, LinearMap.toMatrix_apply, Matrix, Matrix.one_apply, eq_comm, one_apply, single_apply, toMatrix_apply
-/
theorem LinearMap.toMatrix_id : LinearMap.toMatrix v₁ v₁ id = 1 := by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]

@[simp]
/--
theorem `LinearMap.toMatrix_one` / 定理 `LinearMap.toMatrix_one`

English:
theorem LinearMap.toMatrix_one
  statement: LinearMap.toMatrix v₁ v₁ 1 = 1
  proof: LinearMap.toMatrix_id v₁

@[simp]

中文:
定理 LinearMap.toMatrix_one
  结论: LinearMap.toMatrix v₁ v₁ 1 = 1
  证明: LinearMap.toMatrix_id v₁

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrix_id, toMatrix_id
-/
theorem LinearMap.toMatrix_one : LinearMap.toMatrix v₁ v₁ 1 = 1 :=
  LinearMap.toMatrix_id v₁

@[simp]
/--
lemma `LinearMap.toMatrix_singleton` / 引理 `LinearMap.toMatrix_singleton`

English:
lemma LinearMap.toMatrix_singleton
  given: {ι : Type*} [Unique ι] (f : R ->ₗ[R] R) (i j : ι)
  proof: by
  simp [toMatrix, Subsingleton.elim j default]

@[simp]

中文:
引理 LinearMap.toMatrix_singleton
  条件: {ι : 类型} [Unique ι] (f : R ->ₗ[R] R) (i j : ι)
  证明: by
  simp [toMatrix, Subsingleton.elim j default]

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, toMatrix
-/
lemma LinearMap.toMatrix_singleton {ι : Type*} [Unique ι] (f : R ->ₗ[R] R) (i j : ι) :
    f.toMatrix (.singleton ι R) (.singleton ι R) i j = f 1 := by
  simp [toMatrix, Subsingleton.elim j default]

@[simp]
/--
theorem `Matrix.toLin_one` / 定理 `Matrix.toLin_one`

English:
theorem Matrix.toLin_one
  statement: Matrix.toLin v₁ v₁ 1 = LinearMap.id
  proof: by
  rw [← LinearMap.toMatrix_id v₁]; rw [Matrix.toLin_toMatrix]

中文:
定理 Matrix.toLin_one
  结论: Matrix.toLin v₁ v₁ 1 = LinearMap.id
  证明: by
  rw [← LinearMap.toMatrix_id v₁]; rw [Matrix.toLin_toMatrix]

Depends on / 依赖: LinearMap, LinearMap.toMatrix_id, Matrix, Matrix.toLin_toMatrix, toLin_toMatrix, toMatrix_id
-/
theorem Matrix.toLin_one : Matrix.toLin v₁ v₁ 1 = LinearMap.id := by
  rw [← LinearMap.toMatrix_id v₁]; rw [Matrix.toLin_toMatrix]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Matrix.toLin_scalar` / 定理 `Matrix.toLin_scalar`

English:
theorem Matrix.toLin_scalar
  given: (r : R)
  statement: Matrix.toLin v₁ v₁ (scalar n r) = r • LinearMap.id
  proof: (LinearMap.toMatrix v₁ v₁).injective (by simp [toMatrix_id, smul_one_eq_diagonal])

中文:
定理 Matrix.toLin_scalar
  条件: (r : R)
  结论: Matrix.toLin v₁ v₁ (scalar n r) = r • LinearMap.id
  证明: (LinearMap.toMatrix v₁ v₁).injective (by simp [toMatrix_id, smul_one_eq_diagonal])

Depends on / 依赖: LinearMap, LinearMap.toMatrix, injective, smul_one_eq_diagonal, toMatrix, toMatrix_id
-/
theorem Matrix.toLin_scalar (r : R) : Matrix.toLin v₁ v₁ (scalar n r) = r • LinearMap.id :=
  (LinearMap.toMatrix v₁ v₁).injective (by simp [toMatrix_id, smul_one_eq_diagonal])

/--
theorem `LinearMap.toMatrix_reindexRange` / 定理 `LinearMap.toMatrix_reindexRange`

English:
theorem LinearMap.toMatrix_reindexRange
  given: [DecidableEq M₁] (f : M₁ ->ₗ[R] M₂) (k : m) (i : n)
  proof: by
  simp_rw [LinearMap.toMatrix_apply, Basis.reindexRange_self, Basis.reindexRange_repr]

中文:
定理 LinearMap.toMatrix_reindexRange
  条件: [DecidableEq M₁] (f : M₁ ->ₗ[R] M₂) (k : m) (i : n)
  证明: by
  simp_rw [LinearMap.toMatrix_apply, Basis.reindexRange_self, Basis.reindexRange_repr]

Depends on / 依赖: Basis.reindexRange_repr, Basis.reindexRange_self, LinearMap, LinearMap.toMatrix_apply, reindexRange_repr, reindexRange_self, simp_rw, toMatrix_apply
-/
theorem LinearMap.toMatrix_reindexRange [DecidableEq M₁] (f : M₁ ->ₗ[R] M₂) (k : m) (i : n) :
    LinearMap.toMatrix v₁.reindexRange v₂.reindexRange f ⟨v₂ k, Set.mem_range_self k⟩
        ⟨v₁ i, Set.mem_range_self i⟩ =
      LinearMap.toMatrix v₁ v₂ f k i := by
  simp_rw [LinearMap.toMatrix_apply, Basis.reindexRange_self, Basis.reindexRange_repr]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `LinearMap.toMatrix_algebraMap` / 定理 `LinearMap.toMatrix_algebraMap`

English:
theorem LinearMap.toMatrix_algebraMap
  given: (x : R)
  proof: by
  simp [Module.algebraMap_end_eq_smul_id, LinearMap.toMatrix_id, smul_eq_diagonal_mul]

中文:
定理 LinearMap.toMatrix_algebraMap
  条件: (x : R)
  证明: by
  simp [Module.algebraMap_end_eq_smul_id, LinearMap.toMatrix_id, smul_eq_diagonal_mul]

Depends on / 依赖: LinearMap, LinearMap.toMatrix_id, Module, Module.algebraMap_end_eq_smul_id, algebraMap_end_eq_smul_id, smul_eq_diagonal_mul, toMatrix_id
-/
theorem LinearMap.toMatrix_algebraMap (x : R) :
    LinearMap.toMatrix v₁ v₁ (algebraMap R (Module.End R M₁) x) = scalar n x := by
  simp [Module.algebraMap_end_eq_smul_id, LinearMap.toMatrix_id, smul_eq_diagonal_mul]

/--
theorem `LinearMap.toMatrix_mulVec_repr` / 定理 `LinearMap.toMatrix_mulVec_repr`

English:
theorem LinearMap.toMatrix_mulVec_repr
  given: (f : M₁ ->ₗ[R] M₂) (x : M₁)
  proof: by
  ext i
  rw [← Matrix.toLin'_apply]; rw [LinearMap.toMatrix]; rw [LinearEquiv.trans_apply]; rw [Matrix.toLin'_toMatrix']; rw [LinearEquiv.arrowCongr_apply]; rw [v₂.equivFun_apply]
  congr
  exact v₁.equivFun.symm_apply_apply x

中文:
定理 LinearMap.toMatrix_mulVec_repr
  条件: (f : M₁ ->ₗ[R] M₂) (x : M₁)
  证明: by
  ext i
  rw [← Matrix.toLin'_apply]; rw [LinearMap.toMatrix]; rw [LinearEquiv.trans_apply]; rw [Matrix.toLin'_toMatrix']; rw [LinearEquiv.arrowCongr_apply]; rw [v₂.equivFun_apply]
  congr
  exact v₁.equivFun.symm_apply_apply x

Depends on / 依赖: LinearEquiv, LinearEquiv.arrowCongr_apply, LinearEquiv.trans_apply, LinearMap, LinearMap.toMatrix, Matrix, Matrix.toLin, _apply, _toMatrix, arrowCongr_apply, equivFun, equivFun.symm_apply_apply, equivFun_apply, symm_apply_apply, toMatrix, trans_apply
-/
theorem LinearMap.toMatrix_mulVec_repr (f : M₁ ->ₗ[R] M₂) (x : M₁) :
    LinearMap.toMatrix v₁ v₂ f *ᵥ v₁.repr x = v₂.repr (f x) := by
  ext i
  rw [← Matrix.toLin'_apply]; rw [LinearMap.toMatrix]; rw [LinearEquiv.trans_apply]; rw [Matrix.toLin'_toMatrix']; rw [LinearEquiv.arrowCongr_apply]; rw [v₂.equivFun_apply]
  congr
  exact v₁.equivFun.symm_apply_apply x

/--
theorem `Matrix.repr_toLin` / 定理 `Matrix.repr_toLin`

English:
theorem Matrix.repr_toLin
  given: (M : Matrix m n R) (x : M₁)
  proof: by
  rw [← toMatrix_mulVec_repr v₁]; rw [toMatrix_toLin]

@[simp]

中文:
定理 Matrix.repr_toLin
  条件: (M : Matrix m n R) (x : M₁)
  证明: by
  rw [← toMatrix_mulVec_repr v₁]; rw [toMatrix_toLin]

@[simp]

Depends on / 依赖: toMatrix_mulVec_repr, toMatrix_toLin
-/
theorem Matrix.repr_toLin (M : Matrix m n R) (x : M₁) :
    v₂.repr (M.toLin v₁ v₂ x) = M.mulVec (v₁.repr x) := by
  rw [← toMatrix_mulVec_repr v₁]; rw [toMatrix_toLin]

@[simp]
/--
theorem `LinearMap.toMatrix_basis_equiv` / 定理 `LinearMap.toMatrix_basis_equiv`

English:
theorem LinearMap.toMatrix_basis_equiv
  statement: [Fintype l] [DecidableEq l] (b : Basis l R M₁)
  proof: by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]

中文:
定理 LinearMap.toMatrix_basis_equiv
  结论: [Fintype l] [DecidableEq l] (b : Basis l R M₁)
  证明: by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]

Depends on / 依赖: Finsupp, Finsupp.single_apply, LinearMap, LinearMap.toMatrix_apply, Matrix, Matrix.one_apply, eq_comm, one_apply, single_apply, toMatrix_apply
-/
theorem LinearMap.toMatrix_basis_equiv [Fintype l] [DecidableEq l] (b : Basis l R M₁)
    (b' : Basis l R M₂) :
    LinearMap.toMatrix b' b (b'.equiv b (Equiv.refl l) : M₂ ->ₗ[R] M₁) = 1 := by
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]

/--
theorem `LinearMap.toMatrix_smulBasis_left` / 定理 `LinearMap.toMatrix_smulBasis_left`

English:
theorem LinearMap.toMatrix_smulBasis_left
  statement: {G} [Group G] [DistribMulAction G M₁]
  proof: by
  rfl

中文:
定理 LinearMap.toMatrix_smulBasis_left
  结论: {G} [Group G] [DistribMulAction G M₁]
  证明: by
  rfl
-/
theorem LinearMap.toMatrix_smulBasis_left {G} [Group G] [DistribMulAction G M₁]
    [SMulCommClass G R M₁] (g : G) (f : M₁ ->ₗ[R] M₂) :
    LinearMap.toMatrix (g • v₁) v₂ f =
      LinearMap.toMatrix v₁ v₂ (f ∘ₗ DistribSMul.toLinearMap _ _ g) := by
  rfl

/--
theorem `LinearMap.toMatrix_smulBasis_right` / 定理 `LinearMap.toMatrix_smulBasis_right`

English:
theorem LinearMap.toMatrix_smulBasis_right
  statement: {G} [Group G] [DistribMulAction G M₂]
  proof: by
  rfl

中文:
定理 LinearMap.toMatrix_smulBasis_right
  结论: {G} [Group G] [DistribMulAction G M₂]
  证明: by
  rfl
-/
theorem LinearMap.toMatrix_smulBasis_right {G} [Group G] [DistribMulAction G M₂]
    [SMulCommClass G R M₂] (g : G) (f : M₁ ->ₗ[R] M₂) :
    LinearMap.toMatrix v₁ (g • v₂) f =
      LinearMap.toMatrix v₁ v₂ (DistribSMul.toLinearMap _ _ g⁻¹ ∘ₗ f) := by
  rfl

variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃)

/--
theorem `LinearMap.toMatrix_map_left` / 定理 `LinearMap.toMatrix_map_left`

English:
theorem LinearMap.toMatrix_map_left
  given: (f : M₃ ->ₗ[R] M₂) (g : M₁ ≃ₗ[R] M₃)
  proof: by
  rfl

中文:
定理 LinearMap.toMatrix_map_left
  条件: (f : M₃ ->ₗ[R] M₂) (g : M₁ ≃ₗ[R] M₃)
  证明: by
  rfl
-/
theorem LinearMap.toMatrix_map_left (f : M₃ ->ₗ[R] M₂) (g : M₁ ≃ₗ[R] M₃) :
    f.toMatrix (v₁.map g) v₂ = (f ∘ₗ g.toLinearMap).toMatrix v₁ v₂ := by
  rfl

/--
theorem `LinearMap.toMatrix_map_right` / 定理 `LinearMap.toMatrix_map_right`

English:
theorem LinearMap.toMatrix_map_right
  given: (f : M₁ ->ₗ[R] M₃) (g : M₂ ≃ₗ[R] M₃)
  proof: by
  rfl

中文:
定理 LinearMap.toMatrix_map_right
  条件: (f : M₁ ->ₗ[R] M₃) (g : M₂ ≃ₗ[R] M₃)
  证明: by
  rfl
-/
theorem LinearMap.toMatrix_map_right (f : M₁ ->ₗ[R] M₃) (g : M₂ ≃ₗ[R] M₃) :
    f.toMatrix v₁ (v₂.map g) = (g.symm.toLinearMap ∘ₗ f).toMatrix v₁ v₂ := by
  rfl

end Finite

variable {R : Type*} [CommSemiring R]
variable {l m n : Type*} [Fintype n] [DecidableEq n]
variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
variable (v₁ : Basis n R M₁) (v₂ : Basis m R M₂)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `LinearMap.toMatrix_toSpanSingleton` / 定理 `LinearMap.toMatrix_toSpanSingleton`

English:
theorem LinearMap.toMatrix_toSpanSingleton
  statement: [Finite m] (v₁ : Basis n R R) (v₂ : Basis m R M₂)
  proof: by
  ext; simp [toMatrix_apply, vecMulVec_apply, mul_comm]

中文:
定理 LinearMap.toMatrix_toSpanSingleton
  结论: [Finite m] (v₁ : Basis n R R) (v₂ : Basis m R M₂)
  证明: by
  ext; simp [toMatrix_apply, vecMulVec_apply, mul_comm]

Depends on / 依赖: mul_comm, toMatrix_apply, vecMulVec_apply
-/
theorem LinearMap.toMatrix_toSpanSingleton [Finite m] (v₁ : Basis n R R) (v₂ : Basis m R M₂)
    (x : M₂) : (toSpanSingleton R M₂ x).toMatrix v₁ v₂ = vecMulVec (v₂.repr x) v₁ := by
  ext; simp [toMatrix_apply, vecMulVec_apply, mul_comm]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `LinearMap.toMatrix_smulRight` / 引理 `LinearMap.toMatrix_smulRight`

English:
lemma LinearMap.toMatrix_smulRight
  given: [Finite m] (f : M₁ ->ₗ[R] R) (x : M₂)
  proof: by
  ext i j
  simpa [toMatrix_apply, vecMulVec_apply] using mul_comm _ _

中文:
引理 LinearMap.toMatrix_smulRight
  条件: [Finite m] (f : M₁ ->ₗ[R] R) (x : M₂)
  证明: by
  ext i j
  simpa [toMatrix_apply, vecMulVec_apply] using mul_comm _ _

Depends on / 依赖: mul_comm, toMatrix_apply, vecMulVec_apply
-/
lemma LinearMap.toMatrix_smulRight [Finite m] (f : M₁ ->ₗ[R] R) (x : M₂) :
    toMatrix v₁ v₂ (f.smulRight x) = vecMulVec (v₂.repr x) (f ∘ v₁) := by
  ext i j
  simpa [toMatrix_apply, vecMulVec_apply] using mul_comm _ _

/--
theorem `Matrix.toLin_apply` / 定理 `Matrix.toLin_apply`

English:
theorem Matrix.toLin_apply
  given: [Fintype m] (M : Matrix m n R) (v : M₁)
  proof: show v₂.equivFun.symm (Matrix.toLin' M (v₁.repr v)) = _ by
    rw [Matrix.toLin'_apply]; rw [v₂.equivFun_symm_apply]

@[simp]

中文:
定理 Matrix.toLin_apply
  条件: [Fintype m] (M : Matrix m n R) (v : M₁)
  证明: show v₂.equivFun.symm (Matrix.toLin' M (v₁.repr v)) = _ by
    rw [Matrix.toLin'_apply]; rw [v₂.equivFun_symm_apply]

@[simp]

Depends on / 依赖: Matrix, Matrix.toLin, _apply, equivFun, equivFun.symm, equivFun_symm_apply
-/
theorem Matrix.toLin_apply [Fintype m] (M : Matrix m n R) (v : M₁) :
    Matrix.toLin v₁ v₂ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₂ j :=
  show v₂.equivFun.symm (Matrix.toLin' M (v₁.repr v)) = _ by
    rw [Matrix.toLin'_apply]; rw [v₂.equivFun_symm_apply]

@[simp]
/--
theorem `Matrix.toLin_self` / 定理 `Matrix.toLin_self`

English:
theorem Matrix.toLin_self
  given: [Fintype m] (M : Matrix m n R) (i : n)
  proof: by
  rw [Matrix.toLin_apply]; rw [Finset.sum_congr rfl fun j _hj => ?_]
  rw [Basis.repr_self]; rw [Matrix.mulVec]; rw [dotProduct]; rw [Finset.sum_eq_single i]; rw [Finsupp.single_eq_same]; rw [mul_one]
  · intro i' _ i'_ne
    rw [Finsupp.single_eq_of_ne i'_ne]; rw [mul_zero]
  · intros
    have :

中文:
定理 Matrix.toLin_self
  条件: [Fintype m] (M : Matrix m n R) (i : n)
  证明: by
  rw [Matrix.toLin_apply]; rw [Finset.sum_congr rfl fun j _hj => ?_]
  rw [Basis.repr_self]; rw [Matrix.mulVec]; rw [dotProduct]; rw [Finset.sum_eq_single i]; rw [Finsupp.single_eq_same]; rw [mul_one]
  · intro i' _ i'_ne
    rw [Finsupp.single_eq_of_ne i'_ne]; rw [mul_zero]
  · intros
    have :

Depends on / 依赖: Basis.repr_self, Finset, Finset.mem_univ, Finset.sum_congr, Finset.sum_eq_single, Finsupp, Finsupp.single_eq_of_ne, Finsupp.single_eq_same, Matrix, Matrix.mulVec, Matrix.toLin_apply, dotProduct, intros, mem_univ, mulVec, mul_one, mul_zero, repr_self, single_eq_of_ne, single_eq_same
-/
theorem Matrix.toLin_self [Fintype m] (M : Matrix m n R) (i : n) :
    Matrix.toLin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j := by
  rw [Matrix.toLin_apply]; rw [Finset.sum_congr rfl fun j _hj => ?_]
  rw [Basis.repr_self]; rw [Matrix.mulVec]; rw [dotProduct]; rw [Finset.sum_eq_single i]; rw [Finsupp.single_eq_same]; rw [mul_one]
  · intro i' _ i'_ne
    rw [Finsupp.single_eq_of_ne i'_ne]; rw [mul_zero]
  · intros
    have := Finset.mem_univ i
    contradiction

/--
theorem `Matrix.toLin_apply_eq_zero_iff` / 定理 `Matrix.toLin_apply_eq_zero_iff`

English:
theorem Matrix.toLin_apply_eq_zero_iff
  statement: {R M₁ M₂ : Type*} [Finite m] [CommRing R]
  proof: by
  have := Fintype.ofFinite m
  rw [toLin_apply]
  exact ⟨Fintype.linearIndependent_iff.mp v₂.linearIndependent _, fun h => by simp [h]⟩

中文:
定理 Matrix.toLin_apply_eq_zero_iff
  结论: {R M₁ M₂ : 类型} [Finite m] [CommRing R]
  证明: by
  have := Fintype.ofFinite m
  rw [toLin_apply]
  exact ⟨Fintype.linearIndependent_iff.mp v₂.linearIndependent _, fun h => by simp [h]⟩

Depends on / 依赖: Fintype, Fintype.linearIndependent_iff.mp, Fintype.ofFinite, linearIndependent, linearIndependent_iff, ofFinite, toLin_apply
-/
theorem Matrix.toLin_apply_eq_zero_iff {R M₁ M₂ : Type*} [Finite m] [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
    {v₁ : Basis n R M₁} {v₂ : Basis m R M₂} {A : Matrix m n R} {x : M₁} :
    A.toLin v₁ v₂ x = 0 ↔ forall j, (A *ᵥ v₁.repr x) j = 0 := by
  have := Fintype.ofFinite m
  rw [toLin_apply]
  exact ⟨Fintype.linearIndependent_iff.mp v₂.linearIndependent _, fun h => by simp [h]⟩

variable [Fintype m]

variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (v₃ : Basis l R M₃)

/--
theorem `LinearMap.toMatrix_comp` / 定理 `LinearMap.toMatrix_comp`

English:
theorem LinearMap.toMatrix_comp
  given: [Finite l] [DecidableEq m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂)
  proof: by
  simp_rw [LinearMap.toMatrix, LinearEquiv.trans_apply]
  rw [LinearEquiv.arrowCongr_comp _ v₂.equivFun]; rw [LinearMap.toMatrix'_comp]

中文:
定理 LinearMap.toMatrix_comp
  条件: [Finite l] [DecidableEq m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂)
  证明: by
  simp_rw [LinearMap.toMatrix, LinearEquiv.trans_apply]
  rw [LinearEquiv.arrowCongr_comp _ v₂.equivFun]; rw [LinearMap.toMatrix'_comp]

Depends on / 依赖: LinearEquiv, LinearEquiv.arrowCongr_comp, LinearEquiv.trans_apply, LinearMap, LinearMap.toMatrix, _comp, arrowCongr_comp, equivFun, simp_rw, toMatrix, trans_apply
-/
theorem LinearMap.toMatrix_comp [Finite l] [DecidableEq m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) :
    LinearMap.toMatrix v₁ v₃ (f.comp g) =
    LinearMap.toMatrix v₂ v₃ f * LinearMap.toMatrix v₁ v₂ g := by
  simp_rw [LinearMap.toMatrix, LinearEquiv.trans_apply]
  rw [LinearEquiv.arrowCongr_comp _ v₂.equivFun]; rw [LinearMap.toMatrix'_comp]

/--
theorem `LinearMap.toMatrix_mul` / 定理 `LinearMap.toMatrix_mul`

English:
theorem LinearMap.toMatrix_mul
  given: (f g : M₁ ->ₗ[R] M₁)
  proof: by
  rw [Module.End.mul_eq_comp]; rw [LinearMap.toMatrix_comp v₁ v₁ v₁ f g]

中文:
定理 LinearMap.toMatrix_mul
  条件: (f g : M₁ ->ₗ[R] M₁)
  证明: by
  rw [Module.End.mul_eq_comp]; rw [LinearMap.toMatrix_comp v₁ v₁ v₁ f g]

Depends on / 依赖: LinearMap, LinearMap.toMatrix_comp, Module, Module.End.mul_eq_comp, mul_eq_comp, toMatrix_comp
-/
theorem LinearMap.toMatrix_mul (f g : M₁ ->ₗ[R] M₁) :
    LinearMap.toMatrix v₁ v₁ (f * g) = LinearMap.toMatrix v₁ v₁ f * LinearMap.toMatrix v₁ v₁ g := by
  rw [Module.End.mul_eq_comp]; rw [LinearMap.toMatrix_comp v₁ v₁ v₁ f g]

/--
lemma `LinearMap.toMatrix_pow` / 引理 `LinearMap.toMatrix_pow`

English:
lemma LinearMap.toMatrix_pow
  given: (f : M₁ ->ₗ[R] M₁) (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, ih, ← toMatrix_mul]

中文:
引理 LinearMap.toMatrix_pow
  条件: (f : M₁ ->ₗ[R] M₁) (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, ih, ← toMatrix_mul]

Depends on / 依赖: pow_succ, toMatrix_mul
-/
lemma LinearMap.toMatrix_pow (f : M₁ ->ₗ[R] M₁) (k : Nat) :
    (toMatrix v₁ v₁ f) ^ k = toMatrix v₁ v₁ (f ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, ih, ← toMatrix_mul]

/--
theorem `Matrix.toLin_mul` / 定理 `Matrix.toLin_mul`

English:
theorem Matrix.toLin_mul
  given: [Finite l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R)
  proof: by
  apply (LinearMap.toMatrix v₁ v₃).injective
  have : DecidableEq l := fun _ _ => Classical.propDecidable _
  rw [LinearMap.toMatrix_comp v₁ v₂ v₃]
  repeat' rw [LinearMap.toMatrix_toLin]

@[simp]

中文:
定理 Matrix.toLin_mul
  条件: [Finite l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R)
  证明: by
  apply (LinearMap.toMatrix v₁ v₃).injective
  have : DecidableEq l := fun _ _ => Classical.propDecidable _
  rw [LinearMap.toMatrix_comp v₁ v₂ v₃]
  repeat' rw [LinearMap.toMatrix_toLin]

@[simp]

Depends on / 依赖: Classical, Classical.propDecidable, DecidableEq, LinearMap, LinearMap.toMatrix, LinearMap.toMatrix_comp, LinearMap.toMatrix_toLin, injective, propDecidable, repeat, toMatrix, toMatrix_comp, toMatrix_toLin
-/
theorem Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R) :
    Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A).comp (Matrix.toLin v₁ v₂ B) := by
  apply (LinearMap.toMatrix v₁ v₃).injective
  have : DecidableEq l := fun _ _ => Classical.propDecidable _
  rw [LinearMap.toMatrix_comp v₁ v₂ v₃]
  repeat' rw [LinearMap.toMatrix_toLin]

@[simp]
/--
theorem `Matrix.toLin_pow` / 定理 `Matrix.toLin_pow`

English:
theorem Matrix.toLin_pow
  given: (A : Matrix n n R) (k : Nat)
  proof: by
  induction k with
  | zero => simp only [pow_zero, toLin_one, End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin_mul v₁ v₁, ih, Module.End.mul_eq_comp]

中文:
定理 Matrix.toLin_pow
  条件: (A : Matrix n n R) (k : 自然数)
  证明: by
  induction k with
  | zero => simp only [pow_zero, toLin_one, End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin_mul v₁ v₁, ih, Module.End.mul_eq_comp]

Depends on / 依赖: End.one_eq_id, Module, Module.End.mul_eq_comp, mul_eq_comp, one_eq_id, pow_succ, pow_zero, toLin_mul, toLin_one
-/
theorem Matrix.toLin_pow (A : Matrix n n R) (k : Nat) :
    (A ^ k).toLin v₁ v₁ = (A.toLin v₁ v₁) ^ k := by
  induction k with
  | zero => simp only [pow_zero, toLin_one, End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, toLin_mul v₁ v₁, ih, Module.End.mul_eq_comp]

/--
theorem `Matrix.toLin_mul_apply` / 定理 `Matrix.toLin_mul_apply`

English:
theorem Matrix.toLin_mul_apply
  statement: [Finite l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R)
  proof: by
  rw [Matrix.toLin_mul v₁ v₂]; rw [LinearMap.comp_apply]

中文:
定理 Matrix.toLin_mul_apply
  结论: [Finite l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R)
  证明: by
  rw [Matrix.toLin_mul v₁ v₂]; rw [LinearMap.comp_apply]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, Matrix, Matrix.toLin_mul, comp_apply, toLin_mul
-/
theorem Matrix.toLin_mul_apply [Finite l] [DecidableEq m] (A : Matrix l m R) (B : Matrix m n R)
    (x) : Matrix.toLin v₁ v₃ (A * B) x = (Matrix.toLin v₂ v₃ A) (Matrix.toLin v₁ v₂ B x) := by
  rw [Matrix.toLin_mul v₁ v₂]; rw [LinearMap.comp_apply]

/-- If `M` and `M` are each other's inverse matrices, `Matrix.toLin M` and `Matrix.toLin M'`
form a linear equivalence. -/
@[simps]
/--
Definition of `Matrix.toLinOfInv` / `Matrix.toLinOfInv` 的定义

English:
definition Matrix.toLinOfInv
  signature: [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R} (hMM' : M * M' = 1)
  body: { Matrix.toLin v₁ v₂ M with
    toFun := Matrix.toLin v₁ v₂ M
    invFun := Matrix.toLin v₂ v₁ M'
    left_inv := fun x => by rw [← Matrix.toLin_mul_apply, hM'M, Matrix.toLin_one, id_apply]
    right_inv := fun x => by
      rw [← Matrix.toLin_mul_apply]; rw [hMM']; rw [Matrix.toLin_one]; rw [id_app

中文:
定义 Matrix.toLinOfInv
  签名: [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R} (hMM' : M * M' = 1)
  定义体: { Matrix.toLin v₁ v₂ M with
    toFun := Matrix.toLin v₁ v₂ M
    invFun := Matrix.toLin v₂ v₁ M'
    left_inv := fun x => by rw [← Matrix.toLin_mul_apply, hM'M, Matrix.toLin_one, id_apply]
    right_inv := fun x => by
      rw [← Matrix.toLin_mul_apply]; rw [hMM']; rw [Matrix.toLin_one]; rw [id_app

Depends on / 依赖: Matrix, Matrix.toLin, Matrix.toLin_mul_apply, Matrix.toLin_one, id_apply, invFun, left_inv, right_inv, toLin_mul_apply, toLin_one
-/
def Matrix.toLinOfInv [DecidableEq m] {M : Matrix m n R} {M' : Matrix n m R} (hMM' : M * M' = 1)
    (hM'M : M' * M = 1) : M₁ ≃ₗ[R] M₂ :=
  { Matrix.toLin v₁ v₂ M with
    toFun := Matrix.toLin v₁ v₂ M
    invFun := Matrix.toLin v₂ v₁ M'
    left_inv := fun x => by rw [← Matrix.toLin_mul_apply, hM'M, Matrix.toLin_one, id_apply]
    right_inv := fun x => by
      rw [← Matrix.toLin_mul_apply]; rw [hMM']; rw [Matrix.toLin_one]; rw [id_apply] }

/--
Definition of `LinearMap.toMatrixAlgEquiv` / `LinearMap.toMatrixAlgEquiv` 的定义

English:
definition LinearMap.toMatrixAlgEquiv
  signature: : (M₁ ->ₗ[R] M₁) ≃ₐ[R] Matrix n n R
  body: AlgEquiv.ofLinearEquiv
    (LinearMap.toMatrix v₁ v₁) (LinearMap.toMatrix_one v₁) (LinearMap.toMatrix_mul v₁)

中文:
定义 LinearMap.toMatrixAlgEquiv
  签名: : (M₁ ->ₗ[R] M₁) ≃ₐ[R] Matrix n n R
  定义体: AlgEquiv.ofLinearEquiv
    (LinearMap.toMatrix v₁ v₁) (LinearMap.toMatrix_one v₁) (LinearMap.toMatrix_mul v₁)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, LinearMap, LinearMap.toMatrix, LinearMap.toMatrix_mul, LinearMap.toMatrix_one, ofLinearEquiv, toMatrix, toMatrix_mul, toMatrix_one
-/
def LinearMap.toMatrixAlgEquiv : (M₁ ->ₗ[R] M₁) ≃ₐ[R] Matrix n n R :=
  AlgEquiv.ofLinearEquiv
    (LinearMap.toMatrix v₁ v₁) (LinearMap.toMatrix_one v₁) (LinearMap.toMatrix_mul v₁)

/--
Definition of `Matrix.toLinAlgEquiv` / `Matrix.toLinAlgEquiv` 的定义

English:
definition Matrix.toLinAlgEquiv
  signature: : Matrix n n R ≃ₐ[R] M₁ ->ₗ[R] M₁
  body: (LinearMap.toMatrixAlgEquiv v₁).symm

@[simp]

中文:
定义 Matrix.toLinAlgEquiv
  签名: : Matrix n n R ≃ₐ[R] M₁ ->ₗ[R] M₁
  定义体: (LinearMap.toMatrixAlgEquiv v₁).symm

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv, toMatrixAlgEquiv
-/
def Matrix.toLinAlgEquiv : Matrix n n R ≃ₐ[R] M₁ ->ₗ[R] M₁ :=
  (LinearMap.toMatrixAlgEquiv v₁).symm

@[simp]
/--
theorem `LinearMap.toMatrixAlgEquiv_symm` / 定理 `LinearMap.toMatrixAlgEquiv_symm`

English:
theorem LinearMap.toMatrixAlgEquiv_symm
  proof: rfl

@[simp]

中文:
定理 LinearMap.toMatrixAlgEquiv_symm
  证明: rfl

@[simp]
-/
theorem LinearMap.toMatrixAlgEquiv_symm :
    (LinearMap.toMatrixAlgEquiv v₁).symm = Matrix.toLinAlgEquiv v₁ :=
  rfl

@[simp]
/--
theorem `Matrix.toLinAlgEquiv_symm` / 定理 `Matrix.toLinAlgEquiv_symm`

English:
theorem Matrix.toLinAlgEquiv_symm
  proof: rfl

@[simp]

中文:
定理 Matrix.toLinAlgEquiv_symm
  证明: rfl

@[simp]
-/
theorem Matrix.toLinAlgEquiv_symm :
    (Matrix.toLinAlgEquiv v₁).symm = LinearMap.toMatrixAlgEquiv v₁ :=
  rfl

@[simp]
/--
theorem `Matrix.toLinAlgEquiv_toMatrixAlgEquiv` / 定理 `Matrix.toLinAlgEquiv_toMatrixAlgEquiv`

English:
theorem Matrix.toLinAlgEquiv_toMatrixAlgEquiv
  given: (f : M₁ ->ₗ[R] M₁)
  proof: by
  rw [← Matrix.toLinAlgEquiv_symm]; rw [AlgEquiv.apply_symm_apply]

@[simp]

中文:
定理 Matrix.toLinAlgEquiv_toMatrixAlgEquiv
  条件: (f : M₁ ->ₗ[R] M₁)
  证明: by
  rw [← Matrix.toLinAlgEquiv_symm]; rw [AlgEquiv.apply_symm_apply]

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, Matrix, Matrix.toLinAlgEquiv_symm, apply_symm_apply, toLinAlgEquiv_symm
-/
theorem Matrix.toLinAlgEquiv_toMatrixAlgEquiv (f : M₁ ->ₗ[R] M₁) :
    Matrix.toLinAlgEquiv v₁ (LinearMap.toMatrixAlgEquiv v₁ f) = f := by
  rw [← Matrix.toLinAlgEquiv_symm]; rw [AlgEquiv.apply_symm_apply]

@[simp]
/--
theorem `LinearMap.toMatrixAlgEquiv_toLinAlgEquiv` / 定理 `LinearMap.toMatrixAlgEquiv_toLinAlgEquiv`

English:
theorem LinearMap.toMatrixAlgEquiv_toLinAlgEquiv
  given: (M : Matrix n n R)
  proof: by
  rw [← Matrix.toLinAlgEquiv_symm]; rw [AlgEquiv.symm_apply_apply]

中文:
定理 LinearMap.toMatrixAlgEquiv_toLinAlgEquiv
  条件: (M : Matrix n n R)
  证明: by
  rw [← Matrix.toLinAlgEquiv_symm]; rw [AlgEquiv.symm_apply_apply]

Depends on / 依赖: AlgEquiv, AlgEquiv.symm_apply_apply, Matrix, Matrix.toLinAlgEquiv_symm, symm_apply_apply, toLinAlgEquiv_symm
-/
theorem LinearMap.toMatrixAlgEquiv_toLinAlgEquiv (M : Matrix n n R) :
    LinearMap.toMatrixAlgEquiv v₁ (Matrix.toLinAlgEquiv v₁ M) = M := by
  rw [← Matrix.toLinAlgEquiv_symm]; rw [AlgEquiv.symm_apply_apply]

/--
theorem `LinearMap.toMatrixAlgEquiv_apply` / 定理 `LinearMap.toMatrixAlgEquiv_apply`

English:
theorem LinearMap.toMatrixAlgEquiv_apply
  given: (f : M₁ ->ₗ[R] M₁) (i j : n)
  proof: by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_apply]

中文:
定理 LinearMap.toMatrixAlgEquiv_apply
  条件: (f : M₁ ->ₗ[R] M₁) (i j : n)
  证明: by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_apply]

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_apply, toMatrixAlgEquiv, toMatrix_apply
-/
theorem LinearMap.toMatrixAlgEquiv_apply (f : M₁ ->ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i := by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_apply]

/--
theorem `LinearMap.toMatrixAlgEquiv_transpose_apply` / 定理 `LinearMap.toMatrixAlgEquiv_transpose_apply`

English:
theorem LinearMap.toMatrixAlgEquiv_transpose_apply
  given: (f : M₁ ->ₗ[R] M₁) (j : n)
  proof: funext fun i => f.toMatrix_apply _ _ i j

中文:
定理 LinearMap.toMatrixAlgEquiv_transpose_apply
  条件: (f : M₁ ->ₗ[R] M₁) (j : n)
  证明: funext fun i => f.toMatrix_apply _ _ i j

Depends on / 依赖: f.toMatrix_apply, toMatrix_apply
-/
theorem LinearMap.toMatrixAlgEquiv_transpose_apply (f : M₁ ->ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  funext fun i => f.toMatrix_apply _ _ i j

/--
theorem `LinearMap.toMatrixAlgEquiv_apply'` / 定理 `LinearMap.toMatrixAlgEquiv_apply'`

English:
theorem LinearMap.toMatrixAlgEquiv_apply'
  given: (f : M₁ ->ₗ[R] M₁) (i j : n)
  proof: LinearMap.toMatrixAlgEquiv_apply v₁ f i j

中文:
定理 LinearMap.toMatrixAlgEquiv_apply'
  条件: (f : M₁ ->ₗ[R] M₁) (i j : n)
  证明: LinearMap.toMatrixAlgEquiv_apply v₁ f i j

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv_apply, toMatrixAlgEquiv_apply
-/
theorem LinearMap.toMatrixAlgEquiv_apply' (f : M₁ ->ₗ[R] M₁) (i j : n) :
    LinearMap.toMatrixAlgEquiv v₁ f i j = v₁.repr (f (v₁ j)) i :=
  LinearMap.toMatrixAlgEquiv_apply v₁ f i j

/--
theorem `LinearMap.toMatrixAlgEquiv_transpose_apply'` / 定理 `LinearMap.toMatrixAlgEquiv_transpose_apply'`

English:
theorem LinearMap.toMatrixAlgEquiv_transpose_apply'
  given: (f : M₁ ->ₗ[R] M₁) (j : n)
  proof: LinearMap.toMatrixAlgEquiv_transpose_apply v₁ f j

中文:
定理 LinearMap.toMatrixAlgEquiv_transpose_apply'
  条件: (f : M₁ ->ₗ[R] M₁) (j : n)
  证明: LinearMap.toMatrixAlgEquiv_transpose_apply v₁ f j

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv_transpose_apply, toMatrixAlgEquiv_transpose_apply
-/
theorem LinearMap.toMatrixAlgEquiv_transpose_apply' (f : M₁ ->ₗ[R] M₁) (j : n) :
    (LinearMap.toMatrixAlgEquiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
  LinearMap.toMatrixAlgEquiv_transpose_apply v₁ f j

/--
theorem `Matrix.toLinAlgEquiv_apply` / 定理 `Matrix.toLinAlgEquiv_apply`

English:
theorem Matrix.toLinAlgEquiv_apply
  given: (M : Matrix n n R) (v : M₁)
  proof: show v₁.equivFun.symm (Matrix.toLinAlgEquiv' M (v₁.repr v)) = _ by
    rw [Matrix.toLinAlgEquiv'_apply]; rw [v₁.equivFun_symm_apply]

@[simp]

中文:
定理 Matrix.toLinAlgEquiv_apply
  条件: (M : Matrix n n R) (v : M₁)
  证明: show v₁.equivFun.symm (Matrix.toLinAlgEquiv' M (v₁.repr v)) = _ by
    rw [Matrix.toLinAlgEquiv'_apply]; rw [v₁.equivFun_symm_apply]

@[simp]

Depends on / 依赖: Matrix, Matrix.toLinAlgEquiv, _apply, equivFun, equivFun.symm, equivFun_symm_apply, toLinAlgEquiv
-/
theorem Matrix.toLinAlgEquiv_apply (M : Matrix n n R) (v : M₁) :
    Matrix.toLinAlgEquiv v₁ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₁ j :=
  show v₁.equivFun.symm (Matrix.toLinAlgEquiv' M (v₁.repr v)) = _ by
    rw [Matrix.toLinAlgEquiv'_apply]; rw [v₁.equivFun_symm_apply]

@[simp]
/--
theorem `Matrix.toLinAlgEquiv_self` / 定理 `Matrix.toLinAlgEquiv_self`

English:
theorem Matrix.toLinAlgEquiv_self
  given: (M : Matrix n n R) (i : n)
  proof: Matrix.toLin_self _ _ _ _

中文:
定理 Matrix.toLinAlgEquiv_self
  条件: (M : Matrix n n R) (i : n)
  证明: Matrix.toLin_self _ _ _ _

Depends on / 依赖: Matrix, Matrix.toLin_self, toLin_self
-/
theorem Matrix.toLinAlgEquiv_self (M : Matrix n n R) (i : n) :
    Matrix.toLinAlgEquiv v₁ M (v₁ i) = ∑ j, M j i • v₁ j :=
  Matrix.toLin_self _ _ _ _

/--
theorem `LinearMap.toMatrixAlgEquiv_id` / 定理 `LinearMap.toMatrixAlgEquiv_id`

English:
theorem LinearMap.toMatrixAlgEquiv_id
  statement: LinearMap.toMatrixAlgEquiv v₁ id = 1
  proof: by
  simp_rw [LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply, LinearMap.toMatrix_id]

中文:
定理 LinearMap.toMatrixAlgEquiv_id
  结论: LinearMap.toMatrixAlgEquiv v₁ id = 1
  证明: by
  simp_rw [LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply, LinearMap.toMatrix_id]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv_apply, LinearMap, LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_id, ofLinearEquiv_apply, simp_rw, toMatrixAlgEquiv, toMatrix_id
-/
theorem LinearMap.toMatrixAlgEquiv_id : LinearMap.toMatrixAlgEquiv v₁ id = 1 := by
  simp_rw [LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply, LinearMap.toMatrix_id]

/--
theorem `Matrix.toLinAlgEquiv_one` / 定理 `Matrix.toLinAlgEquiv_one`

English:
theorem Matrix.toLinAlgEquiv_one
  statement: Matrix.toLinAlgEquiv v₁ 1 = LinearMap.id
  proof: by
  rw [← LinearMap.toMatrixAlgEquiv_id v₁]; rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv]

中文:
定理 Matrix.toLinAlgEquiv_one
  结论: Matrix.toLinAlgEquiv v₁ 1 = LinearMap.id
  证明: by
  rw [← LinearMap.toMatrixAlgEquiv_id v₁]; rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv]

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv_id, Matrix, Matrix.toLinAlgEquiv_toMatrixAlgEquiv, toLinAlgEquiv_toMatrixAlgEquiv, toMatrixAlgEquiv_id
-/
theorem Matrix.toLinAlgEquiv_one : Matrix.toLinAlgEquiv v₁ 1 = LinearMap.id := by
  rw [← LinearMap.toMatrixAlgEquiv_id v₁]; rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv]

/--
theorem `LinearMap.toMatrixAlgEquiv_reindexRange` / 定理 `LinearMap.toMatrixAlgEquiv_reindexRange`

English:
theorem LinearMap.toMatrixAlgEquiv_reindexRange
  given: [DecidableEq M₁] (f : M₁ ->ₗ[R] M₁) (k i : n)
  proof: by
  simp_rw [LinearMap.toMatrixAlgEquiv_apply, Basis.reindexRange_self, Basis.reindexRange_repr]

中文:
定理 LinearMap.toMatrixAlgEquiv_reindexRange
  条件: [DecidableEq M₁] (f : M₁ ->ₗ[R] M₁) (k i : n)
  证明: by
  simp_rw [LinearMap.toMatrixAlgEquiv_apply, Basis.reindexRange_self, Basis.reindexRange_repr]

Depends on / 依赖: Basis.reindexRange_repr, Basis.reindexRange_self, LinearMap, LinearMap.toMatrixAlgEquiv_apply, reindexRange_repr, reindexRange_self, simp_rw, toMatrixAlgEquiv_apply
-/
theorem LinearMap.toMatrixAlgEquiv_reindexRange [DecidableEq M₁] (f : M₁ ->ₗ[R] M₁) (k i : n) :
    LinearMap.toMatrixAlgEquiv v₁.reindexRange f
        ⟨v₁ k, Set.mem_range_self k⟩ ⟨v₁ i, Set.mem_range_self i⟩ =
      LinearMap.toMatrixAlgEquiv v₁ f k i := by
  simp_rw [LinearMap.toMatrixAlgEquiv_apply, Basis.reindexRange_self, Basis.reindexRange_repr]

/--
theorem `LinearMap.toMatrixAlgEquiv_comp` / 定理 `LinearMap.toMatrixAlgEquiv_comp`

English:
theorem LinearMap.toMatrixAlgEquiv_comp
  given: (f g : M₁ ->ₗ[R] M₁)
  proof: by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_comp v₁ v₁ v₁ f g]

中文:
定理 LinearMap.toMatrixAlgEquiv_comp
  条件: (f g : M₁ ->ₗ[R] M₁)
  证明: by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_comp v₁ v₁ v₁ f g]

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_comp, toMatrixAlgEquiv, toMatrix_comp
-/
theorem LinearMap.toMatrixAlgEquiv_comp (f g : M₁ ->ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f.comp g) =
      LinearMap.toMatrixAlgEquiv v₁ f * LinearMap.toMatrixAlgEquiv v₁ g := by
  simp [LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_comp v₁ v₁ v₁ f g]

/--
theorem `LinearMap.toMatrixAlgEquiv_mul` / 定理 `LinearMap.toMatrixAlgEquiv_mul`

English:
theorem LinearMap.toMatrixAlgEquiv_mul
  given: (f g : M₁ ->ₗ[R] M₁)
  proof: by
  rw [Module.End.mul_eq_comp]; rw [LinearMap.toMatrixAlgEquiv_comp v₁ f g]

中文:
定理 LinearMap.toMatrixAlgEquiv_mul
  条件: (f g : M₁ ->ₗ[R] M₁)
  证明: by
  rw [Module.End.mul_eq_comp]; rw [LinearMap.toMatrixAlgEquiv_comp v₁ f g]

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv_comp, Module, Module.End.mul_eq_comp, mul_eq_comp, toMatrixAlgEquiv_comp
-/
theorem LinearMap.toMatrixAlgEquiv_mul (f g : M₁ ->ₗ[R] M₁) :
    LinearMap.toMatrixAlgEquiv v₁ (f * g) =
      LinearMap.toMatrixAlgEquiv v₁ f * LinearMap.toMatrixAlgEquiv v₁ g := by
  rw [Module.End.mul_eq_comp]; rw [LinearMap.toMatrixAlgEquiv_comp v₁ f g]

/--
theorem `Matrix.toLinAlgEquiv_mul` / 定理 `Matrix.toLinAlgEquiv_mul`

English:
theorem Matrix.toLinAlgEquiv_mul
  given: (A B : Matrix n n R)
  proof: by
  convert! Matrix.toLin_mul v₁ v₁ v₁ A B

@[simp]

中文:
定理 Matrix.toLinAlgEquiv_mul
  条件: (A B : Matrix n n R)
  证明: by
  convert! Matrix.toLin_mul v₁ v₁ v₁ A B

@[simp]

Depends on / 依赖: Matrix, Matrix.toLin_mul, convert, toLin_mul
-/
theorem Matrix.toLinAlgEquiv_mul (A B : Matrix n n R) :
    Matrix.toLinAlgEquiv v₁ (A * B) =
      (Matrix.toLinAlgEquiv v₁ A).comp (Matrix.toLinAlgEquiv v₁ B) := by
  convert! Matrix.toLin_mul v₁ v₁ v₁ A B

@[simp]
/--
theorem `LinearMap.isUnit_toMatrix_iff` / 定理 `LinearMap.isUnit_toMatrix_iff`

English:
theorem LinearMap.isUnit_toMatrix_iff
  given: {f : M₁ ->ₗ[R] M₁}
  statement: IsUnit (f.toMatrix v₁ v₁) ↔ IsUnit f
  proof: isUnit_map_iff (LinearMap.toMatrixAlgEquiv _) f

@[simp]

中文:
定理 LinearMap.isUnit_toMatrix_iff
  条件: {f : M₁ ->ₗ[R] M₁}
  结论: IsUnit (f.toMatrix v₁ v₁) ↔ IsUnit f
  证明: isUnit_map_iff (LinearMap.toMatrixAlgEquiv _) f

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv, isUnit_map_iff, toMatrixAlgEquiv
-/
theorem LinearMap.isUnit_toMatrix_iff {f : M₁ ->ₗ[R] M₁} : IsUnit (f.toMatrix v₁ v₁) ↔ IsUnit f :=
  isUnit_map_iff (LinearMap.toMatrixAlgEquiv _) f

@[simp]
/--
theorem `Matrix.isUnit_toLin_iff` / 定理 `Matrix.isUnit_toLin_iff`

English:
theorem Matrix.isUnit_toLin_iff
  given: {M : Matrix n n R}
  statement: IsUnit (M.toLin v₁ v₁) ↔ IsUnit M
  proof: isUnit_map_iff (LinearMap.toMatrixAlgEquiv _).symm M

@[simp]

中文:
定理 Matrix.isUnit_toLin_iff
  条件: {M : Matrix n n R}
  结论: IsUnit (M.toLin v₁ v₁) ↔ IsUnit M
  证明: isUnit_map_iff (LinearMap.toMatrixAlgEquiv _).symm M

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv, isUnit_map_iff, toMatrixAlgEquiv
-/
theorem Matrix.isUnit_toLin_iff {M : Matrix n n R} : IsUnit (M.toLin v₁ v₁) ↔ IsUnit M :=
  isUnit_map_iff (LinearMap.toMatrixAlgEquiv _).symm M

@[simp]
/--
theorem `Matrix.toLin_finTwoProd_apply` / 定理 `Matrix.toLin_finTwoProd_apply`

English:
theorem Matrix.toLin_finTwoProd_apply
  given: (a b c d : R) (x : R × R)
  proof: by
  simp [Matrix.toLin_apply, Matrix.mulVec, dotProduct]

中文:
定理 Matrix.toLin_finTwoProd_apply
  条件: (a b c d : R) (x : R × R)
  证明: by
  simp [Matrix.toLin_apply, Matrix.mulVec, dotProduct]

Depends on / 依赖: Matrix, Matrix.mulVec, Matrix.toLin_apply, dotProduct, mulVec, toLin_apply
-/
theorem Matrix.toLin_finTwoProd_apply (a b c d : R) (x : R × R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R) !![a, b; c, d] x =
      (a * x.fst + b * x.snd, c * x.fst + d * x.snd) := by
  simp [Matrix.toLin_apply, Matrix.mulVec, dotProduct]

/--
theorem `Matrix.toLin_finTwoProd` / 定理 `Matrix.toLin_finTwoProd`

English:
theorem Matrix.toLin_finTwoProd
  given: (a b c d : R)
  proof: LinearMap.ext Matrix.toLin_finTwoProd_apply _ _ _ _

@[simp]

中文:
定理 Matrix.toLin_finTwoProd
  条件: (a b c d : R)
  证明: LinearMap.ext Matrix.toLin_finTwoProd_apply _ _ _ _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, Matrix, Matrix.toLin_finTwoProd_apply, toLin_finTwoProd_apply
-/
theorem Matrix.toLin_finTwoProd (a b c d : R) :
    Matrix.toLin (Basis.finTwoProd R) (Basis.finTwoProd R) !![a, b; c, d] =
      (a • LinearMap.fst R R R + b • LinearMap.snd R R R).prod
        (c • LinearMap.fst R R R + d • LinearMap.snd R R R) :=
LinearMap.ext Matrix.toLin_finTwoProd_apply _ _ _ _

@[simp]
/--
theorem `toMatrix_distrib_mul_action_toLinearMap` / 定理 `toMatrix_distrib_mul_action_toLinearMap`

English:
theorem toMatrix_distrib_mul_action_toLinearMap
  given: (x : R)
  proof: by
  ext
  rw [LinearMap.toMatrix_apply]; rw [DistribSMul.toLinearMap_apply]; rw [map_smul]; rw [Basis.repr_self]; rw [Finsupp.smul_single_one]; rw [Finsupp.single_eq_pi_single]; rw [Matrix.diagonal_apply]; rw [Pi.single_apply]

中文:
定理 toMatrix_distrib_mul_action_toLinearMap
  条件: (x : R)
  证明: by
  ext
  rw [LinearMap.toMatrix_apply]; rw [DistribSMul.toLinearMap_apply]; rw [map_smul]; rw [Basis.repr_self]; rw [Finsupp.smul_single_one]; rw [Finsupp.single_eq_pi_single]; rw [Matrix.diagonal_apply]; rw [Pi.single_apply]

Depends on / 依赖: Basis.repr_self, DistribSMul, DistribSMul.toLinearMap_apply, Finsupp, Finsupp.single_eq_pi_single, Finsupp.smul_single_one, LinearMap, LinearMap.toMatrix_apply, Matrix, Matrix.diagonal_apply, Pi.single_apply, diagonal_apply, map_smul, repr_self, single_apply, single_eq_pi_single, smul_single_one, toLinearMap_apply, toMatrix_apply
-/
theorem toMatrix_distrib_mul_action_toLinearMap (x : R) :
    LinearMap.toMatrix v₁ v₁ (DistribSMul.toLinearMap R M₁ x) =
    Matrix.diagonal fun _ => x := by
  ext
  rw [LinearMap.toMatrix_apply]; rw [DistribSMul.toLinearMap_apply]; rw [map_smul]; rw [Basis.repr_self]; rw [Finsupp.smul_single_one]; rw [Finsupp.single_eq_pi_single]; rw [Matrix.diagonal_apply]; rw [Pi.single_apply]

/--
lemma `LinearMap.toMatrix_prodMap` / 引理 `LinearMap.toMatrix_prodMap`

English:
lemma LinearMap.toMatrix_prodMap
  statement: [DecidableEq m] [DecidableEq (n oplus m)]
  proof: by
  ext (i | i) (j | j) <;> simp [toMatrix]

中文:
引理 LinearMap.toMatrix_prodMap
  结论: [DecidableEq m] [DecidableEq (n oplus m)]
  证明: by
  ext (i | i) (j | j) <;> simp [toMatrix]

Depends on / 依赖: toMatrix
-/
lemma LinearMap.toMatrix_prodMap [DecidableEq m] [DecidableEq (n oplus m)]
    (φ₁ : Module.End R M₁) (φ₂ : Module.End R M₂) :
    toMatrix (v₁.prod v₂) (v₁.prod v₂) (φ₁.prodMap φ₂) =
      Matrix.fromBlocks (toMatrix v₁ v₁ φ₁) 0 0 (toMatrix v₂ v₂ φ₂) := by
  ext (i | i) (j | j) <;> simp [toMatrix]

end ToMatrix

namespace Algebra

section Lmul

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
variable {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R S)

/--
theorem `toMatrix_lmul'` / 定理 `toMatrix_lmul'`

English:
theorem toMatrix_lmul'
  given: (x : S) (i j)
  proof: by
  simp only [LinearMap.toMatrix_apply', coe_lmul_eq_mul, LinearMap.mul_apply']

@[simp]

中文:
定理 toMatrix_lmul'
  条件: (x : S) (i j)
  证明: by
  simp only [LinearMap.toMatrix_apply', coe_lmul_eq_mul, LinearMap.mul_apply']

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mul_apply, LinearMap.toMatrix_apply, coe_lmul_eq_mul, mul_apply, toMatrix_apply
-/
theorem toMatrix_lmul' (x : S) (i j) :
    LinearMap.toMatrix b b (lmul R S x) i j = b.repr (x * b j) i := by
  simp only [LinearMap.toMatrix_apply', coe_lmul_eq_mul, LinearMap.mul_apply']

@[simp]
/--
theorem `toMatrix_lsmul` / 定理 `toMatrix_lsmul`

English:
theorem toMatrix_lsmul
  given: (x : R)
  proof: toMatrix_distrib_mul_action_toLinearMap b x

中文:
定理 toMatrix_lsmul
  条件: (x : R)
  证明: toMatrix_distrib_mul_action_toLinearMap b x

Depends on / 依赖: toMatrix_distrib_mul_action_toLinearMap
-/
theorem toMatrix_lsmul (x : R) :
    LinearMap.toMatrix b b (Algebra.lsmul R R S x) = Matrix.diagonal fun _ => x :=
  toMatrix_distrib_mul_action_toLinearMap b x

/--
Definition of `leftMulMatrix` / `leftMulMatrix` 的定义

English:
definition leftMulMatrix
  signature: : S ->ₐ[R] Matrix m m R where
  body: LinearMap.toMatrix b b (Algebra.lmul R S x)
  map_zero' := by
    rw [map_zero]; rw [map_zero]
  map_one' := by
    rw [map_one]; rw [LinearMap.toMatrix_one]
  map_add' x y := by
    rw [map_add]; rw [map_add]
  map_mul' x y := by
    rw [map_mul]; rw [LinearMap.toMatrix_mul]
  commutes' r := by
   

中文:
定义 leftMulMatrix
  签名: : S ->ₐ[R] Matrix m m R where
  定义体: LinearMap.toMatrix b b (Algebra.lmul R S x)
  map_zero' := by
    rw [map_zero]; rw [map_zero]
  map_one' := by
    rw [map_one]; rw [LinearMap.toMatrix_one]
  map_add' x y := by
    rw [map_add]; rw [map_add]
  map_mul' x y := by
    rw [map_mul]; rw [LinearMap.toMatrix_mul]
  commutes' r := by
   

Depends on / 依赖: Algebra, Algebra.lmul, LinearMap, LinearMap.toMatrix, toMatrix
-/
noncomputable def leftMulMatrix : S ->ₐ[R] Matrix m m R where
  toFun x := LinearMap.toMatrix b b (Algebra.lmul R S x)
  map_zero' := by
    rw [map_zero]; rw [map_zero]
  map_one' := by
    rw [map_one]; rw [LinearMap.toMatrix_one]
  map_add' x y := by
    rw [map_add]; rw [map_add]
  map_mul' x y := by
    rw [map_mul]; rw [LinearMap.toMatrix_mul]
  commutes' r := by
    ext
    rw [lmul_algebraMap]; rw [toMatrix_lsmul]; rw [algebraMap_eq_diagonal]; rw [Pi.algebraMap_def]; rw [Algebra.algebraMap_self_apply]

/--
theorem `leftMulMatrix_apply` / 定理 `leftMulMatrix_apply`

English:
theorem leftMulMatrix_apply
  given: (x : S)
  statement: leftMulMatrix b x = LinearMap.toMatrix b b (lmul R S x)
  proof: rfl

中文:
定理 leftMulMatrix_apply
  条件: (x : S)
  结论: leftMulMatrix b x = LinearMap.toMatrix b b (lmul R S x)
  证明: rfl
-/
theorem leftMulMatrix_apply (x : S) : leftMulMatrix b x = LinearMap.toMatrix b b (lmul R S x) :=
  rfl

/--
theorem `leftMulMatrix_eq_repr_mul` / 定理 `leftMulMatrix_eq_repr_mul`

English:
theorem leftMulMatrix_eq_repr_mul
  given: (x : S) (i j)
  statement: leftMulMatrix b x i j = b.repr (x * b j) i
  proof: by
  -- This is defeq to just `toMatrix_lmul' b x i j`,
  -- but the unfolding goes a lot faster with this explicit `rw`.
  rw [leftMulMatrix_apply]; rw [toMatrix_lmul' b x i j]

中文:
定理 leftMulMatrix_eq_repr_mul
  条件: (x : S) (i j)
  结论: leftMulMatrix b x i j = b.repr (x * b j) i
  证明: by
  -- This is defeq to just `toMatrix_lmul' b x i j`,
  -- but the unfolding goes a lot faster with this explicit `rw`.
  rw [leftMulMatrix_apply]; rw [toMatrix_lmul' b x i j]
-/
theorem leftMulMatrix_eq_repr_mul (x : S) (i j) : leftMulMatrix b x i j = b.repr (x * b j) i := by
  -- This is defeq to just `toMatrix_lmul' b x i j`,
  -- but the unfolding goes a lot faster with this explicit `rw`.
  rw [leftMulMatrix_apply]; rw [toMatrix_lmul' b x i j]

/--
theorem `leftMulMatrix_mulVec_repr` / 定理 `leftMulMatrix_mulVec_repr`

English:
theorem leftMulMatrix_mulVec_repr
  given: (x y : S)
  proof: (LinearMap.mulLeft R x).toMatrix_mulVec_repr b b y

@[simp]

中文:
定理 leftMulMatrix_mulVec_repr
  条件: (x y : S)
  证明: (LinearMap.mulLeft R x).toMatrix_mulVec_repr b b y

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mulLeft, mulLeft, toMatrix_mulVec_repr
-/
theorem leftMulMatrix_mulVec_repr (x y : S) :
    leftMulMatrix b x *ᵥ b.repr y = b.repr (x * y) :=
  (LinearMap.mulLeft R x).toMatrix_mulVec_repr b b y

@[simp]
/--
theorem `toMatrix_lmul_eq` / 定理 `toMatrix_lmul_eq`

English:
theorem toMatrix_lmul_eq
  given: (x : S)
  proof: rfl

中文:
定理 toMatrix_lmul_eq
  条件: (x : S)
  证明: rfl
-/
theorem toMatrix_lmul_eq (x : S) :
    LinearMap.toMatrix b b (LinearMap.mulLeft R x) = leftMulMatrix b x :=
  rfl

/--
theorem `leftMulMatrix_injective` / 定理 `leftMulMatrix_injective`

English:
theorem leftMulMatrix_injective
  statement: Function.Injective (leftMulMatrix b)
  proof: fun x x' h =>
  calc
    x = Algebra.lmul R S x 1 := (mul_one x).symm
    _ = Algebra.lmul R S x' 1 := by rw [(LinearMap.toMatrix b b).injective h]
    _ = x' := mul_one x'

@[simp]

中文:
定理 leftMulMatrix_injective
  结论: Function.Injective (leftMulMatrix b)
  证明: fun x x' h =>
  calc
    x = Algebra.lmul R S x 1 := (mul_one x).symm
    _ = Algebra.lmul R S x' 1 := by rw [(LinearMap.toMatrix b b).injective h]
    _ = x' := mul_one x'

@[simp]
-/
theorem leftMulMatrix_injective : Function.Injective (leftMulMatrix b) := fun x x' h =>
  calc
    x = Algebra.lmul R S x 1 := (mul_one x).symm
    _ = Algebra.lmul R S x' 1 := by rw [(LinearMap.toMatrix b b).injective h]
    _ = x' := mul_one x'

@[simp]
/--
theorem `smul_leftMulMatrix` / 定理 `smul_leftMulMatrix`

English:
theorem smul_leftMulMatrix
  statement: {G} [Group G] [DistribMulAction G S]
  proof: by
  ext
  simp_rw [leftMulMatrix_apply, LinearMap.toMatrix_apply, coe_lmul_eq_mul, LinearMap.mul_apply',
    Basis.repr_smul, Basis.smul_apply, LinearEquiv.trans_apply,
    DistribMulAction.toLinearEquiv_symm_apply, mul_smul_comm, inv_smul_smul]

中文:
定理 smul_leftMulMatrix
  结论: {G} [Group G] [DistribMulAction G S]
  证明: by
  ext
  simp_rw [leftMulMatrix_apply, LinearMap.toMatrix_apply, coe_lmul_eq_mul, LinearMap.mul_apply',
    Basis.repr_smul, Basis.smul_apply, LinearEquiv.trans_apply,
    DistribMulAction.toLinearEquiv_symm_apply, mul_smul_comm, inv_smul_smul]

Depends on / 依赖: Basis.repr_smul, Basis.smul_apply, DistribMulAction, DistribMulAction.toLinearEquiv_symm_apply, LinearEquiv, LinearEquiv.trans_apply, LinearMap, LinearMap.mul_apply, LinearMap.toMatrix_apply, coe_lmul_eq_mul, inv_smul_smul, leftMulMatrix_apply, mul_apply, mul_smul_comm, repr_smul, simp_rw, smul_apply, toLinearEquiv_symm_apply, toMatrix_apply, trans_apply
-/
theorem smul_leftMulMatrix {G} [Group G] [DistribMulAction G S]
    [SMulCommClass G R S] [SMulCommClass G S S] (g : G) (x) :
    leftMulMatrix (g • b) x = leftMulMatrix b x := by
  ext
  simp_rw [leftMulMatrix_apply, LinearMap.toMatrix_apply, coe_lmul_eq_mul, LinearMap.mul_apply',
    Basis.repr_smul, Basis.smul_apply, LinearEquiv.trans_apply,
    DistribMulAction.toLinearEquiv_symm_apply, mul_smul_comm, inv_smul_smul]

variable {A M n : Type*} [Fintype n] [DecidableEq n]
  [CommSemiring A] [AddCommMonoid M] [Module R M] [Module A M] [Algebra R A] [IsScalarTower R A M]
  (bA : Basis m R A) (bM : Basis n A M)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `_root_.LinearMap.restrictScalars_toMatrix` / 引理 `_root_.LinearMap.restrictScalars_toMatrix`

English:
lemma _root_.LinearMap.restrictScalars_toMatrix
  given: (f : M ->ₗ[A] M)
  proof: by
  ext; simp [toMatrix, Algebra.leftMulMatrix_apply,
    Basis.smulTower'_repr, Basis.smulTower'_apply, mul_comm]

中文:
引理 _root_.LinearMap.restrictScalars_toMatrix
  条件: (f : M ->ₗ[A] M)
  证明: by
  ext; simp [toMatrix, Algebra.leftMulMatrix_apply,
    Basis.smulTower'_repr, Basis.smulTower'_apply, mul_comm]

Depends on / 依赖: Algebra, Algebra.leftMulMatrix_apply, Basis.smulTower, _apply, _repr, leftMulMatrix_apply, mul_comm, smulTower, toMatrix
-/
lemma _root_.LinearMap.restrictScalars_toMatrix (f : M ->ₗ[A] M) :
    (f.restrictScalars R).toMatrix (bA.smulTower' bM) (bA.smulTower' bM) =
      ((f.toMatrix bM bM).map (leftMulMatrix bA)).comp _ _ _ _ _ := by
  ext; simp [toMatrix, Algebra.leftMulMatrix_apply,
    Basis.smulTower'_repr, Basis.smulTower'_apply, mul_comm]

end Lmul

section LmulTower

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [Semiring T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable (b : Basis m R S) (c : Basis n S T)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `smulTower_leftMulMatrix` / 定理 `smulTower_leftMulMatrix`

English:
theorem smulTower_leftMulMatrix
  given: (x) (ik jk)
  proof: by
  simp only [leftMulMatrix_apply, LinearMap.toMatrix_apply, mul_comm, Basis.smulTower_apply,
    Basis.smulTower_repr, Finsupp.smul_apply, smul_eq_mul, map_smul, mul_smul_comm,
    coe_lmul_eq_mul, LinearMap.mul_apply']

中文:
定理 smulTower_leftMulMatrix
  条件: (x) (ik jk)
  证明: by
  simp only [leftMulMatrix_apply, LinearMap.toMatrix_apply, mul_comm, Basis.smulTower_apply,
    Basis.smulTower_repr, Finsupp.smul_apply, smul_eq_mul, map_smul, mul_smul_comm,
    coe_lmul_eq_mul, LinearMap.mul_apply']

Depends on / 依赖: Basis.smulTower_apply, Basis.smulTower_repr, Finsupp, Finsupp.smul_apply, LinearMap, LinearMap.mul_apply, LinearMap.toMatrix_apply, coe_lmul_eq_mul, leftMulMatrix_apply, map_smul, mul_apply, mul_comm, mul_smul_comm, smulTower_apply, smulTower_repr, smul_apply, smul_eq_mul, toMatrix_apply
-/
theorem smulTower_leftMulMatrix (x) (ik jk) :
    leftMulMatrix (b.smulTower c) x ik jk =
      leftMulMatrix b (leftMulMatrix c x ik.2 jk.2) ik.1 jk.1 := by
  simp only [leftMulMatrix_apply, LinearMap.toMatrix_apply, mul_comm, Basis.smulTower_apply,
    Basis.smulTower_repr, Finsupp.smul_apply, smul_eq_mul, map_smul, mul_smul_comm,
    coe_lmul_eq_mul, LinearMap.mul_apply']

/--
theorem `smulTower_leftMulMatrix_algebraMap` / 定理 `smulTower_leftMulMatrix_algebraMap`

English:
theorem smulTower_leftMulMatrix_algebraMap
  given: (x : S)
  proof: by
  ext ⟨i, k⟩ ⟨j, k'⟩
  rw [smulTower_leftMulMatrix]; rw [AlgHom.commutes]; rw [blockDiagonal_apply]; rw [algebraMap_matrix_apply]
  split_ifs with h <;> simp only at h <;> simp

中文:
定理 smulTower_leftMulMatrix_algebraMap
  条件: (x : S)
  证明: by
  ext ⟨i, k⟩ ⟨j, k'⟩
  rw [smulTower_leftMulMatrix]; rw [AlgHom.commutes]; rw [blockDiagonal_apply]; rw [algebraMap_matrix_apply]
  split_ifs with h <;> simp only at h <;> simp

Depends on / 依赖: AlgHom, AlgHom.commutes, algebraMap_matrix_apply, blockDiagonal_apply, commutes, smulTower_leftMulMatrix, split_ifs
-/
theorem smulTower_leftMulMatrix_algebraMap (x : S) :
    leftMulMatrix (b.smulTower c) (algebraMap _ _ x) = blockDiagonal fun _ => leftMulMatrix b x := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  rw [smulTower_leftMulMatrix]; rw [AlgHom.commutes]; rw [blockDiagonal_apply]; rw [algebraMap_matrix_apply]
  split_ifs with h <;> simp only at h <;> simp

/--
theorem `smulTower_leftMulMatrix_algebraMap_eq` / 定理 `smulTower_leftMulMatrix_algebraMap_eq`

English:
theorem smulTower_leftMulMatrix_algebraMap_eq
  given: (x : S) (i j k)
  proof: by
  rw [smulTower_leftMulMatrix_algebraMap]; rw [blockDiagonal_apply_eq]

中文:
定理 smulTower_leftMulMatrix_algebraMap_eq
  条件: (x : S) (i j k)
  证明: by
  rw [smulTower_leftMulMatrix_algebraMap]; rw [blockDiagonal_apply_eq]

Depends on / 依赖: blockDiagonal_apply_eq, smulTower_leftMulMatrix_algebraMap
-/
theorem smulTower_leftMulMatrix_algebraMap_eq (x : S) (i j k) :
    leftMulMatrix (b.smulTower c) (algebraMap _ _ x) (i, k) (j, k) = leftMulMatrix b x i j := by
  rw [smulTower_leftMulMatrix_algebraMap]; rw [blockDiagonal_apply_eq]

/--
theorem `smulTower_leftMulMatrix_algebraMap_ne` / 定理 `smulTower_leftMulMatrix_algebraMap_ne`

English:
theorem smulTower_leftMulMatrix_algebraMap_ne
  given: (x : S) (i j) {k k'} (h : k != k')
  proof: by
  rw [smulTower_leftMulMatrix_algebraMap]; rw [blockDiagonal_apply_ne _ _ _ h]

中文:
定理 smulTower_leftMulMatrix_algebraMap_ne
  条件: (x : S) (i j) {k k'} (h : k != k')
  证明: by
  rw [smulTower_leftMulMatrix_algebraMap]; rw [blockDiagonal_apply_ne _ _ _ h]

Depends on / 依赖: blockDiagonal_apply_ne, smulTower_leftMulMatrix_algebraMap
-/
theorem smulTower_leftMulMatrix_algebraMap_ne (x : S) (i j) {k k'} (h : k != k') :
    leftMulMatrix (b.smulTower c) (algebraMap _ _ x) (i, k) (j, k') = 0 := by
  rw [smulTower_leftMulMatrix_algebraMap]; rw [blockDiagonal_apply_ne _ _ _ h]

end LmulTower

end Algebra

section

variable {R S : Type*} [CommSemiring R] {n : Type*} [DecidableEq n]
variable {M M₁ M₂ : Type*} [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
variable [Semiring S] [Module S M₁] [Module S M₂] [SMulCommClass S R M₁] [SMulCommClass S R M₂]
variable [SMul R S] [IsScalarTower R S M₁] [IsScalarTower R S M₂]

/--
Definition of `algEquivMatrix'` / `algEquivMatrix'` 的定义

English:
definition algEquivMatrix'
  signature: [Fintype n]
  body: LinearMap.toMatrixAlgEquiv'

中文:
定义 algEquivMatrix'
  签名: [Fintype n]
  定义体: LinearMap.toMatrixAlgEquiv'

Depends on / 依赖: LinearMap, LinearMap.toMatrixAlgEquiv, toMatrixAlgEquiv
-/
def algEquivMatrix' [Fintype n] : Module.End R (n -> R) ≃ₐ[R] Matrix n n R :=
  LinearMap.toMatrixAlgEquiv'

/--
Definition of `algEquivMatrix` / `algEquivMatrix` 的定义

English:
definition algEquivMatrix
  signature: [Fintype n] (h : Basis n R M)
  body: (h.equivFun.conjAlgEquiv R).trans algEquivMatrix'

中文:
定义 algEquivMatrix
  签名: [Fintype n] (h : Basis n R M)
  定义体: (h.equivFun.conjAlgEquiv R).trans algEquivMatrix'

Depends on / 依赖: algEquivMatrix, conjAlgEquiv, equivFun, h.equivFun.conjAlgEquiv
-/
def algEquivMatrix [Fintype n] (h : Basis n R M) : Module.End R M ≃ₐ[R] Matrix n n R :=
  (h.equivFun.conjAlgEquiv R).trans algEquivMatrix'

end

namespace Module.Basis

variable {R M M₁ M₂ ι ι₁ ι₂ : Type*} [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M] [Module R M₁] [Module R M₂]
variable [Fintype ι] [Fintype ι₁] [Fintype ι₂]
variable [DecidableEq ι] [DecidableEq ι₁]
variable (b : Basis ι R M) (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

/-- The standard basis of the space linear maps between two modules
induced by a basis of the domain and codomain.

If `M₁` and `M₂` are modules with basis `b₁` and `b₂` respectively indexed
by finite types `ι₁` and `ι₂`,
then `Basis.linearMap b₁ b₂` is the basis of `M₁ →ₗ[R] M₂` indexed by `ι₂ × ι₁`
where `(i, j)` indexes the linear map that sends `b j` to `b i`
and sends all other basis vectors to `0`. -/
@[simps! -isSimp repr_apply repr_symm_apply]
noncomputable
/--
Definition of `linearMap` / `linearMap` 的定义

English:
definition linearMap
  signature: (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)
  body: (Matrix.stdBasis R ι₂ ι₁).map (LinearMap.toMatrix b₁ b₂).symm

中文:
定义 linearMap
  签名: (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)
  定义体: (Matrix.stdBasis R ι₂ ι₁).map (LinearMap.toMatrix b₁ b₂).symm

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Matrix, Matrix.stdBasis, stdBasis, toMatrix
-/
def linearMap (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) :
    Basis (ι₂ × ι₁) R (M₁ ->ₗ[R] M₂) :=
  (Matrix.stdBasis R ι₂ ι₁).map (LinearMap.toMatrix b₁ b₂).symm

attribute [simp] linearMap_repr_apply

/--
lemma `linearMap_apply` / 引理 `linearMap_apply`

English:
lemma linearMap_apply
  given: (ij : ι₂ × ι₁)
  proof: by
  simp [linearMap]

中文:
引理 linearMap_apply
  条件: (ij : ι₂ × ι₁)
  证明: by
  simp [linearMap]

Depends on / 依赖: linearMap
-/
lemma linearMap_apply (ij : ι₂ × ι₁) :
    (b₁.linearMap b₂ ij) = (Matrix.toLin b₁ b₂) (Matrix.stdBasis R ι₂ ι₁ ij) := by
  simp [linearMap]

/--
lemma `linearMap_apply_apply` / 引理 `linearMap_apply_apply`

English:
lemma linearMap_apply_apply
  given: (ij : ι₂ × ι₁) (k : ι₁)
  proof: by
  have := Classical.decEq ι₂
  rw [linearMap_apply]; rw [Matrix.stdBasis_eq_single]; rw [Matrix.toLin_self]
  dsimp only [Matrix.single, of_apply]
  simp_rw [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]

中文:
引理 linearMap_apply_apply
  条件: (ij : ι₂ × ι₁) (k : ι₁)
  证明: by
  have := Classical.decEq ι₂
  rw [linearMap_apply]; rw [Matrix.stdBasis_eq_single]; rw [Matrix.toLin_self]
  dsimp only [Matrix.single, of_apply]
  simp_rw [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.mem_univ, Finset.sum_ite_eq, Matrix, Matrix.single, Matrix.stdBasis_eq_single, Matrix.toLin_self, if_true, ite_and, ite_smul, linearMap_apply, mem_univ, of_apply, one_smul, simp_rw, single, stdBasis_eq_single, sum_ite_eq
-/
lemma linearMap_apply_apply (ij : ι₂ × ι₁) (k : ι₁) :
    (b₁.linearMap b₂ ij) (b₁ k) = if ij.2 = k then b₂ ij.1 else 0 := by
  have := Classical.decEq ι₂
  rw [linearMap_apply]; rw [Matrix.stdBasis_eq_single]; rw [Matrix.toLin_self]
  dsimp only [Matrix.single, of_apply]
  simp_rw [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The standard basis of the endomorphism algebra of a module
induced by a basis of the module.

If `M` is a module with basis `b` indexed by a finite type `ι`,
then `Basis.end b` is the basis of `Module.End R M` indexed by `ι × ι`
where `(i, j)` indexes the linear map that sends `b j` to `b i`
and sends all other basis vectors to `0`. -/
@[simps! -isSimp repr_apply repr_symm_apply]
noncomputable
/--
Definition of `«end»` / `«end»` 的定义

English:
abbreviation «end»
  signature: (b : Basis ι R M)
  body: b.linearMap b

中文:
缩写 «end»
  签名: (b : Basis ι R M)
  定义体: b.linearMap b
-/
abbrev «end» (b : Basis ι R M) : Basis (ι × ι) R (Module.End R M) :=
  b.linearMap b

/--
lemma `end_apply` / 引理 `end_apply`

English:
lemma end_apply
  given: (ij : ι × ι)
  statement: (b.end ij) = (Matrix.toLin b b) (Matrix.stdBasis R ι ι ij)
  proof: linearMap_apply b b ij

中文:
引理 end_apply
  条件: (ij : ι × ι)
  结论: (b.end ij) = (Matrix.toLin b b) (Matrix.stdBasis R ι ι ij)
  证明: linearMap_apply b b ij

Depends on / 依赖: linearMap_apply
-/
lemma end_apply (ij : ι × ι) : (b.end ij) = (Matrix.toLin b b) (Matrix.stdBasis R ι ι ij) :=
  linearMap_apply b b ij

/--
lemma `end_apply_apply` / 引理 `end_apply_apply`

English:
lemma end_apply_apply
  given: (ij : ι × ι) (k : ι)
  statement: (b.end ij) (b k) = if ij.2 = k then b ij.1 else 0
  proof: linearMap_apply_apply b b ij k

中文:
引理 end_apply_apply
  条件: (ij : ι × ι) (k : ι)
  结论: (b.end ij) (b k) = if ij.2 = k then b ij.1 else 0
  证明: linearMap_apply_apply b b ij k

Depends on / 依赖: linearMap_apply_apply
-/
lemma end_apply_apply (ij : ι × ι) (k : ι) : (b.end ij) (b k) = if ij.2 = k then b ij.1 else 0 :=
  linearMap_apply_apply b b ij k

/--
lemma `lie_end_of_apply_eq_smul` / 引理 `lie_end_of_apply_eq_smul`

English:
lemma lie_end_of_apply_eq_smul
  statement: {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  proof: by
  refine b.ext fun k => ?_
  simp only [Ring.lie_def, LinearMap.sub_apply, End.mul_apply, LinearMap.smul_apply,
    Basis.end_apply_apply, smul_ite, smul_zero, sub_smul]
  rcases eq_or_ne j k with rfl | hjk
  · simp [hs, Basis.end_apply_apply]
  · simp [hs, Basis.end_apply_apply, hjk]

中文:
引理 lie_end_of_apply_eq_smul
  结论: {R M : 类型} [CommRing R] [AddCommGroup M] [Module R M]
  证明: by
  refine b.ext fun k => ?_
  simp only [Ring.lie_def, LinearMap.sub_apply, End.mul_apply, LinearMap.smul_apply,
    Basis.end_apply_apply, smul_ite, smul_zero, sub_smul]
  rcases eq_or_ne j k with rfl | hjk
  · simp [hs, Basis.end_apply_apply]
  · simp [hs, Basis.end_apply_apply, hjk]

Depends on / 依赖: Basis.end_apply_apply, End.mul_apply, LinearMap, LinearMap.smul_apply, LinearMap.sub_apply, Ring.lie_def, b.ext, end_apply_apply, eq_or_ne, lie_def, mul_apply, smul_apply, smul_ite, smul_zero, sub_apply, sub_smul
-/
lemma lie_end_of_apply_eq_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Basis ι R M) (a : ι -> R) (s : Module.End R M)
    (hs : forall k, s (b k) = a k • b k) (i j : ι) :
    ⁅s, b.end (i, j)⁆ = (a i - a j) • b.end (i, j) := by
  refine b.ext fun k => ?_
  simp only [Ring.lie_def, LinearMap.sub_apply, End.mul_apply, LinearMap.smul_apply,
    Basis.end_apply_apply, smul_ite, smul_zero, sub_smul]
  rcases eq_or_ne j k with rfl | hjk
  · simp [hs, Basis.end_apply_apply]
  · simp [hs, Basis.end_apply_apply, hjk]

end Module.Basis

section

variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (R : Type*) [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable (M : Type*) [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

set_option backward.isDefEq.respectTransparency false in
/--
Let `M` be an `A`-module. Every `A`-linear map `Mⁿ → Mⁿ` corresponds to a `n×n`-matrix whose entries
are `A`-linear maps `M → M`. In another word, we have `End(Mⁿ) ≅ Matₙₓₙ(End(M))` defined by:
`(f : Mⁿ → Mⁿ) ↦ (x ↦ f (0, ..., x at j-th position, ..., 0) i)ᵢⱼ` and
`m : Matₙₓₙ(End(M)) ↦ (v ↦ ∑ⱼ mᵢⱼ(vⱼ))`.

See also `LinearMap.toMatrix'`
-/
@[simp]
/--
Definition of `endVecRingEquivMatrixEnd` / `endVecRingEquivMatrixEnd` 的定义

English:
definition endVecRingEquivMatrixEnd
  signature: :
  body: { toFun := fun x => f (Pi.single j x) i
    map_add' := fun x y => by simp [Pi.single_add]
    map_smul' := fun x y => by simp [Pi.single_smul] }
  invFun m :=
  { toFun := fun x i => ∑ j, m i j (x j)
    map_add' := by intros; ext; simp [Finset.sum_add_distrib]
    map_smul' := by intros; ext; simp

中文:
定义 endVecRingEquivMatrixEnd
  签名: :
  定义体: { toFun := fun x => f (Pi.single j x) i
    map_add' := fun x y => by simp [Pi.single_add]
    map_smul' := fun x y => by simp [Pi.single_smul] }
  invFun m :=
  { toFun := fun x i => ∑ j, m i j (x j)
    map_add' := by intros; ext; simp [Finset.sum_add_distrib]
    map_smul' := by intros; ext; simp

Depends on / 依赖: AddHom, AddHom.coe_mk, Finset, Finset.smul_sum, Finset.sum_add_distrib, Fintype, Fintype.sum_apply, Function, Function.comp_apply, LinearMap, LinearMap.coe_mk, Pi.single, Pi.single_add, Pi.single_smul, coe_comp, coe_mk, coe_single, comp_apply, intros, invFun
-/
def endVecRingEquivMatrixEnd :
    Module.End A (ι -> M) ≃+* Matrix ι ι (Module.End A M) where
  toFun f i j :=
  { toFun := fun x => f (Pi.single j x) i
    map_add' := fun x y => by simp [Pi.single_add]
    map_smul' := fun x y => by simp [Pi.single_smul] }
  invFun m :=
  { toFun := fun x i => ∑ j, m i j (x j)
    map_add' := by intros; ext; simp [Finset.sum_add_distrib]
    map_smul' := by intros; ext; simp [Finset.smul_sum] }
  left_inv f := by
    ext i x j
    simp only [LinearMap.coe_mk, AddHom.coe_mk, coe_comp, coe_single, Function.comp_apply]
    rw [← Fintype.sum_apply]; rw [← map_sum]
    exact congr_arg₂ _ (by aesop) rfl
  right_inv m := by ext; simp [Pi.single_apply, apply_ite]
  map_mul' f g := by
    ext
    simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply,
      LinearMap.coe_sum, Finset.sum_apply]
    rw [← Fintype.sum_apply]; rw [← map_sum]
    exact congr_arg₂ _ (by aesop) rfl
  map_add' f g := by ext; simp

set_option backward.isDefEq.respectTransparency false in
/--
Let `M` be an `A`-module. Every `A`-linear map `Mⁿ → Mⁿ` corresponds to a `n×n`-matrix whose entries
are `R`-linear maps `M → M`. In another word, we have `End(Mⁿ) ≅ Matₙₓₙ(End(M))` defined by:
`(f : Mⁿ → Mⁿ) ↦ (x ↦ f (0, ..., x at j-th position, ..., 0) i)ᵢⱼ` and
`m : Matₙₓₙ(End(M)) ↦ (v ↦ ∑ⱼ mᵢⱼ(vⱼ))`.

See also `LinearMap.toMatrix'`
-/
@[simps!]
/--
Definition of `endVecAlgEquivMatrixEnd` / `endVecAlgEquivMatrixEnd` 的定义

English:
definition endVecAlgEquivMatrixEnd
  signature: :
  body: endVecRingEquivMatrixEnd ι A M
  commutes' r := by
    ext
    simp only [endVecRingEquivMatrixEnd, RingEquiv.toEquiv_eq_coe, Module.algebraMap_end_eq_smul_id,
      Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, Equiv.coe_fn_mk,
      LinearMap.smul_apply, id_coe, id_eq, Pi.smul_apply, Pi

中文:
定义 endVecAlgEquivMatrixEnd
  签名: :
  定义体: endVecRingEquivMatrixEnd ι A M
  commutes' r := by
    ext
    simp only [endVecRingEquivMatrixEnd, RingEquiv.toEquiv_eq_coe, Module.algebraMap_end_eq_smul_id,
      Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, Equiv.coe_fn_mk,
      LinearMap.smul_apply, id_coe, id_eq, Pi.smul_apply, Pi

Depends on / 依赖: endVecRingEquivMatrixEnd
-/
def endVecAlgEquivMatrixEnd :
    Module.End A (ι -> M) ≃ₐ[R] Matrix ι ι (Module.End A M) where
  __ := endVecRingEquivMatrixEnd ι A M
  commutes' r := by
    ext
    simp only [endVecRingEquivMatrixEnd, RingEquiv.toEquiv_eq_coe, Module.algebraMap_end_eq_smul_id,
      Equiv.toFun_as_coe, EquivLike.coe_coe, RingEquiv.coe_mk, Equiv.coe_fn_mk,
      LinearMap.smul_apply, id_coe, id_eq, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      LinearMap.coe_mk, AddHom.coe_mk, algebraMap_matrix_apply]
    split_ifs <;> rfl

variable {A ι}

/--
Definition of `matrixAlgEquivEndVecMulOpposite` / `matrixAlgEquivEndVecMulOpposite` 的定义

English:
definition matrixAlgEquivEndVecMulOpposite
  signature: : Matrix ι ι A ≃ₐ[R] (Module.End A (ι -> A))ᵐᵒᵖ
  body: .trans (.opOp R _) .op .trans (.symm .mopMatrix) .trans
(.mapMatrix <| .moduleEndSelf _) .symm endVecAlgEquivMatrixEnd ..

中文:
定义 matrixAlgEquivEndVecMulOpposite
  签名: : Matrix ι ι A ≃ₐ[R] (Module.End A (ι -> A))ᵐᵒᵖ
  定义体: .trans (.opOp R _) .op .trans (.symm .mopMatrix) .trans
(.mapMatrix <| .moduleEndSelf _) .symm endVecAlgEquivMatrixEnd ..

Depends on / 依赖: endVecAlgEquivMatrixEnd, mapMatrix, moduleEndSelf, mopMatrix
-/
def matrixAlgEquivEndVecMulOpposite : Matrix ι ι A ≃ₐ[R] (Module.End A (ι -> A))ᵐᵒᵖ :=
.trans (.opOp R _) .op .trans (.symm .mopMatrix) .trans
(.mapMatrix <| .moduleEndSelf _) .symm endVecAlgEquivMatrixEnd ..

/--
Definition of `matrixRingEquivEndVecMulOpposite` / `matrixRingEquivEndVecMulOpposite` 的定义

English:
definition matrixRingEquivEndVecMulOpposite
  signature: : Matrix ι ι A ≃+* (Module.End A (ι -> A))ᵐᵒᵖ
  body: (matrixAlgEquivEndVecMulOpposite Nat).toRingEquiv

中文:
定义 matrixRingEquivEndVecMulOpposite
  签名: : Matrix ι ι A ≃+* (Module.End A (ι -> A))ᵐᵒᵖ
  定义体: (matrixAlgEquivEndVecMulOpposite Nat).toRingEquiv

Depends on / 依赖: matrixAlgEquivEndVecMulOpposite, toRingEquiv
-/
def matrixRingEquivEndVecMulOpposite : Matrix ι ι A ≃+* (Module.End A (ι -> A))ᵐᵒᵖ :=
  (matrixAlgEquivEndVecMulOpposite Nat).toRingEquiv

/--
theorem `isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd` / 定理 `isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd`

English:
theorem isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd
  proof: by
  simp_rw [isStablyFiniteRing_iff, MulEquivClass.isDedekindFiniteMonoid_iff
    (matrixRingEquivEndVecMulOpposite (ι := Fin _) (A := A)),
    MulOpposite.isDedekindFiniteMonoid_iff]

中文:
定理 isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd
  证明: by
  simp_rw [isStablyFiniteRing_iff, MulEquivClass.isDedekindFiniteMonoid_iff
    (matrixRingEquivEndVecMulOpposite (ι := Fin _) (A := A)),
    MulOpposite.isDedekindFiniteMonoid_iff]

Depends on / 依赖: MulEquivClass, MulEquivClass.isDedekindFiniteMonoid_iff, MulOpposite, MulOpposite.isDedekindFiniteMonoid_iff, isDedekindFiniteMonoid_iff, isStablyFiniteRing_iff, matrixRingEquivEndVecMulOpposite, simp_rw
-/
theorem isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd :
    IsStablyFiniteRing A ↔ forall n, IsDedekindFiniteMonoid (Module.End A (Fin n -> A)) := by
  simp_rw [isStablyFiniteRing_iff, MulEquivClass.isDedekindFiniteMonoid_iff
    (matrixRingEquivEndVecMulOpposite (ι := Fin _) (A := A)),
    MulOpposite.isDedekindFiniteMonoid_iff]

instance (ι) [Finite ι] [IsStablyFiniteRing A] : IsStablyFiniteRing (Module.End A (ι -> A)) := by
  have := Fintype.ofFinite ι
  classical rw [← MulOpposite.isStablyFiniteRing_iff,
    ← RingEquiv.isStablyFiniteRing_iff (matrixRingEquivEndVecMulOpposite (ι := ι) (A := A))]
  infer_instance

open Function

/--
theorem `isStablyFiniteRing_iff_injective_of_surjective` / 定理 `isStablyFiniteRing_iff_injective_of_surjective`

English:
theorem isStablyFiniteRing_iff_injective_of_surjective
  proof: by
  simp_rw [isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd, isDedekindFiniteMonoid_iff]
  refine ⟨fun h n f surj => ?_, fun h n f g eq => ?_⟩
  · have ⟨g, eq⟩ := Module.projective_lifting_property _ .id surj
    exact injective_of_comp_eq_id _ _ (h _ eq)
  · have surj := surjective_of_com

中文:
定理 isStablyFiniteRing_iff_injective_of_surjective
  证明: by
  simp_rw [isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd, isDedekindFiniteMonoid_iff]
  refine ⟨fun h n f surj => ?_, fun h n f g eq => ?_⟩
  · have ⟨g, eq⟩ := Module.projective_lifting_property _ .id surj
    exact injective_of_comp_eq_id _ _ (h _ eq)
  · have surj := surjective_of_com

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, Module, Module.projective_lifting_property, injective_of_comp_eq_id, isDedekindFiniteMonoid_iff, isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd, left_inv_eq_right_inv, ofBijective, projective_lifting_property, simp_rw, surjective_of_comp_eq_id, symm_comp
-/
theorem isStablyFiniteRing_iff_injective_of_surjective :
    IsStablyFiniteRing A ↔ forall n (f : Module.End A (Fin n -> A)), Surjective f -> Injective f := by
  simp_rw [isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd, isDedekindFiniteMonoid_iff]
  refine ⟨fun h n f surj => ?_, fun h n f g eq => ?_⟩
  · have ⟨g, eq⟩ := Module.projective_lifting_property _ .id surj
    exact injective_of_comp_eq_id _ _ (h _ eq)
  · have surj := surjective_of_comp_eq_id _ _ eq
    have := (LinearEquiv.ofBijective f ⟨h _ _ surj, surj⟩).symm_comp
    rwa [← left_inv_eq_right_inv this eq]

/--
theorem `Module.End.injective_of_surjective_fin` / 定理 `Module.End.injective_of_surjective_fin`

English:
theorem Module.End.injective_of_surjective_fin
  statement: [IsStablyFiniteRing A] {n}
  proof: isStablyFiniteRing_iff_injective_of_surjective.mp ‹_› n f hf

中文:
定理 Module.End.injective_of_surjective_fin
  结论: [IsStablyFiniteRing A] {n}
  证明: isStablyFiniteRing_iff_injective_of_surjective.mp ‹_› n f hf

Depends on / 依赖: Nat.one_div, Nat.one_div_pos_of_nat, PseudoMetricSpace, TopologicalSpace, TopologicalSpace.pseudoMetrizableSpacePseudoMetric, isStablyFiniteRing_iff_injective_of_surjective, isStablyFiniteRing_iff_injective_of_surjective.mp, one_div, one_div_pos_of_nat, one_le_thickenedIndicator_apply, pseudoMetrizableSpacePseudoMetric, thickenedIndicator, thickenedIndicator_le_one, thickenedIndicator_tendsto_indicator_closure
-/
theorem Module.End.injective_of_surjective_fin [IsStablyFiniteRing A] {n}
    {f : Module.End A (Fin n -> A)} (hf : Surjective f) : Injective f :=
  isStablyFiniteRing_iff_injective_of_surjective.mp ‹_› n f hf

end
