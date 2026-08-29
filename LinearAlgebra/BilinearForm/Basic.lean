/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Bilinear form

This file defines a bilinear form over a module. Basic ideas
such as orthogonality are also introduced, as well as reflexive,
symmetric, non-degenerate and alternating bilinear forms. Adjoints of
linear maps with respect to a bilinear form are also introduced.

A bilinear form on an `R`-(semi)module `M`, is a function from `M × M` to `R`,
that is linear in both arguments. Comments will typically abbreviate
"(semi)module" as just "module", but the definitions should be as general as
possible.

The result that there exists an orthogonal basis with respect to a symmetric,
nondegenerate bilinear form can be found in `QuadraticForm.lean` with
`exists_orthogonal_basis`.

## Notation

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, i.e. `B x y = B.bilin x y`.

In this file we use the following type variables:
- `M`, `M'`, ... are modules over the commutative semiring `R`,
- `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
- `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

@[expose] public section

export LinearMap (BilinForm)

open LinearMap (BilinForm)

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

/--
theorem `add_left` / 定理 `add_left`

English:
theorem add_left
  given: (x y z : M)
  statement: B (x + y) z = B x z + B y z
  proof: map_add₂ _ _ _ _

中文:
定理 add_left
  条件: (x y z : M)
  结论: B (x + y) z = B x z + B y z
  证明: map_add₂ _ _ _ _
-/
theorem add_left (x y z : M) : B (x + y) z = B x z + B y z := map_add₂ _ _ _ _

/--
theorem `smul_left` / 定理 `smul_left`

English:
theorem smul_left
  given: (a : R) (x y : M)
  statement: B (a • x) y = a * B x y
  proof: map_smul₂ _ _ _ _

中文:
定理 smul_left
  条件: (a : R) (x y : M)
  结论: B (a • x) y = a * B x y
  证明: map_smul₂ _ _ _ _
-/
theorem smul_left (a : R) (x y : M) : B (a • x) y = a * B x y := map_smul₂ _ _ _ _

/--
theorem `add_right` / 定理 `add_right`

English:
theorem add_right
  given: (x y z : M)
  statement: B x (y + z) = B x y + B x z
  proof: map_add _ _ _

中文:
定理 add_right
  条件: (x y z : M)
  结论: B x (y + z) = B x y + B x z
  证明: map_add _ _ _

Depends on / 依赖: map_add
-/
theorem add_right (x y z : M) : B x (y + z) = B x y + B x z := map_add _ _ _

/--
theorem `smul_right` / 定理 `smul_right`

English:
theorem smul_right
  given: (a : R) (x y : M)
  statement: B x (a • y) = a * B x y
  proof: map_smul _ _ _

中文:
定理 smul_right
  条件: (a : R) (x y : M)
  结论: B x (a • y) = a * B x y
  证明: map_smul _ _ _

Depends on / 依赖: map_smul
-/
theorem smul_right (a : R) (x y : M) : B x (a • y) = a * B x y := map_smul _ _ _

/--
theorem `zero_left` / 定理 `zero_left`

English:
theorem zero_left
  given: (x : M)
  statement: B 0 x = 0
  proof: map_zero₂ _ _

中文:
定理 zero_left
  条件: (x : M)
  结论: B 0 x = 0
  证明: map_zero₂ _ _
-/
theorem zero_left (x : M) : B 0 x = 0 := map_zero₂ _ _

/--
theorem `zero_right` / 定理 `zero_right`

English:
theorem zero_right
  given: (x : M)
  statement: B x 0 = 0
  proof: map_zero _

中文:
定理 zero_right
  条件: (x : M)
  结论: B x 0 = 0
  证明: map_zero _

Depends on / 依赖: map_zero
-/
theorem zero_right (x : M) : B x 0 = 0 := map_zero _

/--
theorem `neg_left` / 定理 `neg_left`

English:
theorem neg_left
  given: (x y : M₁)
  statement: B₁ (-x) y = -B₁ x y
  proof: map_neg₂ _ _ _

中文:
定理 neg_left
  条件: (x y : M₁)
  结论: B₁ (-x) y = -B₁ x y
  证明: map_neg₂ _ _ _
-/
theorem neg_left (x y : M₁) : B₁ (-x) y = -B₁ x y := map_neg₂ _ _ _

/--
theorem `neg_right` / 定理 `neg_right`

English:
theorem neg_right
  given: (x y : M₁)
  statement: B₁ x (-y) = -B₁ x y
  proof: map_neg _ _

中文:
定理 neg_right
  条件: (x y : M₁)
  结论: B₁ x (-y) = -B₁ x y
  证明: map_neg _ _

Depends on / 依赖: map_neg
-/
theorem neg_right (x y : M₁) : B₁ x (-y) = -B₁ x y := map_neg _ _

/--
theorem `sub_left` / 定理 `sub_left`

English:
theorem sub_left
  given: (x y z : M₁)
  statement: B₁ (x - y) z = B₁ x z - B₁ y z
  proof: map_sub₂ _ _ _ _

中文:
定理 sub_left
  条件: (x y z : M₁)
  结论: B₁ (x - y) z = B₁ x z - B₁ y z
  证明: map_sub₂ _ _ _ _
-/
theorem sub_left (x y z : M₁) : B₁ (x - y) z = B₁ x z - B₁ y z := map_sub₂ _ _ _ _

/--
theorem `sub_right` / 定理 `sub_right`

English:
theorem sub_right
  given: (x y z : M₁)
  statement: B₁ x (y - z) = B₁ x y - B₁ x z
  proof: map_sub _ _ _

中文:
定理 sub_right
  条件: (x y z : M₁)
  结论: B₁ x (y - z) = B₁ x y - B₁ x z
  证明: map_sub _ _ _

Depends on / 依赖: map_sub
-/
theorem sub_right (x y z : M₁) : B₁ x (y - z) = B₁ x y - B₁ x z := map_sub _ _ _

/--
lemma `smul_left_of_tower` / 引理 `smul_left_of_tower`

English:
lemma smul_left_of_tower
  given: (r : S) (x y : M)
  statement: B (r • x) y = r • B x y
  proof: by
  rw [← IsScalarTower.algebraMap_smul R r]; rw [smul_left]; rw [Algebra.smul_def]

中文:
引理 smul_left_of_tower
  条件: (r : S) (x y : M)
  结论: B (r • x) y = r • B x y
  证明: by
  rw [← IsScalarTower.algebraMap_smul R r]; rw [smul_left]; rw [Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, IsScalarTower, IsScalarTower.algebraMap_smul, algebraMap_smul, smul_def, smul_left
-/
lemma smul_left_of_tower (r : S) (x y : M) : B (r • x) y = r • B x y := by
  rw [← IsScalarTower.algebraMap_smul R r]; rw [smul_left]; rw [Algebra.smul_def]

/--
lemma `smul_right_of_tower` / 引理 `smul_right_of_tower`

English:
lemma smul_right_of_tower
  given: (r : S) (x y : M)
  statement: B x (r • y) = r • B x y
  proof: by
  rw [← IsScalarTower.algebraMap_smul R r]; rw [smul_right]; rw [Algebra.smul_def]

中文:
引理 smul_right_of_tower
  条件: (r : S) (x y : M)
  结论: B x (r • y) = r • B x y
  证明: by
  rw [← IsScalarTower.algebraMap_smul R r]; rw [smul_right]; rw [Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, IsScalarTower, IsScalarTower.algebraMap_smul, algebraMap_smul, smul_def, smul_right
-/
lemma smul_right_of_tower (r : S) (x y : M) : B x (r • y) = r • B x y := by
  rw [← IsScalarTower.algebraMap_smul R r]; rw [smul_right]; rw [Algebra.smul_def]

variable {D : BilinForm R M} {D₁ : BilinForm R₁ M₁}

-- TODO: instantiate `FunLike`
/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((fun B x y => B x y) : BilinForm R M -> M -> M -> R)
  proof: fun B D h => by
    ext x y
    apply congrFun₂ h

@[ext]

中文:
定理 coe_injective
  结论: 函数.单射 ((fun B x y => B x y) : BilinForm R M -> M -> M -> R)
  证明: fun B D h => by
    ext x y
    apply congrFun₂ h

@[ext]
-/
theorem coe_injective : Function.Injective ((fun B x y => B x y) : BilinForm R M -> M -> M -> R) :=
  fun B D h => by
    ext x y
    apply congrFun₂ h

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (H : forall x y : M, B x y = D x y)
  statement: B = D
  proof: ext₂ H

中文:
定理 ext
  条件: (H : 对任意 x y : M, B x y = D x y)
  结论: B = D
  证明: ext₂ H
-/
theorem ext (H : forall x y : M, B x y = D x y) : B = D := ext₂ H

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: (h : B = D) (x y : M)
  statement: B x y = D x y
  proof: congr_fun₂ h _ _

@[simp]

中文:
定理 congr_fun
  条件: (h : B = D) (x y : M)
  结论: B x y = D x y
  证明: congr_fun₂ h _ _

@[simp]
-/
theorem congr_fun (h : B = D) (x y : M) : B x y = D x y := congr_fun₂ h _ _

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (x y : M)
  statement: (0 : BilinForm R M) x y = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (x y : M)
  结论: (0 : BilinForm R M) x y = 0
  证明: rfl
-/
theorem zero_apply (x y : M) : (0 : BilinForm R M) x y = 0 :=
  rfl

variable (B D B₁ D₁)

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (x y : M)
  statement: (B + D) x y = B x y + D x y
  proof: rfl

@[simp]

中文:
定理 add_apply
  条件: (x y : M)
  结论: (B + D) x y = B x y + D x y
  证明: rfl

@[simp]
-/
theorem add_apply (x y : M) : (B + D) x y = B x y + D x y :=
  rfl

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (x y : M₁)
  statement: (-B₁) x y = -B₁ x y
  proof: rfl

@[simp]

中文:
定理 neg_apply
  条件: (x y : M₁)
  结论: (-B₁) x y = -B₁ x y
  证明: rfl

@[simp]
-/
theorem neg_apply (x y : M₁) : (-B₁) x y = -B₁ x y :=
  rfl

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (x y : M₁)
  statement: (B₁ - D₁) x y = B₁ x y - D₁ x y
  proof: rfl

中文:
定理 sub_apply
  条件: (x y : M₁)
  结论: (B₁ - D₁) x y = B₁ x y - D₁ x y
  证明: rfl
-/
theorem sub_apply (x y : M₁) : (B₁ - D₁) x y = B₁ x y - D₁ x y :=
  rfl

/-- `coeFn` as an `AddMonoidHom` -/
@[simps]
/--
Definition of `coeFnAddMonoidHom` / `coeFnAddMonoidHom` 的定义

English:
definition coeFnAddMonoidHom
  signature: : BilinForm R M ->+ M -> M -> R where
  body: fun B x y => B x y
  map_zero' := rfl
  map_add' _ _ := rfl

中文:
定义 coeFnAddMonoidHom
  签名: : BilinForm R M ->+ M -> M -> R where
  定义体: fun B x y => B x y
  map_zero' := rfl
  map_add' _ _ := rfl
-/
def coeFnAddMonoidHom : BilinForm R M ->+ M -> M -> R where
  toFun := fun B x y => B x y
  map_zero' := rfl
  map_add' _ _ := rfl

section flip

/--
Definition of `flipHom` / `flipHom` 的定义

English:
definition flipHom
  signature: : BilinForm R M ≃ₗ[R] BilinForm R M
  body: LinearMap.lflip

@[simp]

中文:
定义 flipHom
  签名: : BilinForm R M ≃ₗ[R] BilinForm R M
  定义体: LinearMap.lflip

@[simp]

Depends on / 依赖: LinearMap, LinearMap.lflip
-/
def flipHom : BilinForm R M ≃ₗ[R] BilinForm R M := LinearMap.lflip

@[simp]
/--
theorem `flip_apply` / 定理 `flip_apply`

English:
theorem flip_apply
  given: (A : BilinForm R M) (x y : M)
  statement: flipHom A x y = A y x
  proof: rfl

中文:
定理 flip_apply
  条件: (A : BilinForm R M) (x y : M)
  结论: flipHom A x y = A y x
  证明: rfl
-/
theorem flip_apply (A : BilinForm R M) (x y : M) : flipHom A x y = A y x :=
  rfl

/--
theorem `flip_flip` / 定理 `flip_flip`

English:
theorem flip_flip
  proof: by
  ext A
  simp

中文:
定理 flip_flip
  证明: by
  ext A
  simp
-/
theorem flip_flip :
    flipHom.trans flipHom = LinearEquiv.refl R (BilinForm R M) := by
  ext A
  simp

/--
Definition of `flip` / `flip` 的定义

English:
abbreviation flip
  signature: (B : BilinForm R M)
  body: flipHom B

中文:
缩写 flip
  签名: (B : BilinForm R M)
  定义体: flipHom B

Depends on / 依赖: flipHom
-/
abbrev flip (B : BilinForm R M) :=
  flipHom B

end flip

/-- The restriction of a bilinear form on a submodule. -/
@[simps! apply]
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (B : BilinForm R M) (W : Submodule R M)
  body: LinearMap.domRestrict₁₂ B W W

中文:
定义 restrict
  签名: (B : BilinForm R M) (W : 子模 R M)
  定义体: LinearMap.domRestrict₁₂ B W W

Depends on / 依赖: LinearMap, LinearMap.domRestrict
-/
def restrict (B : BilinForm R M) (W : Submodule R M) : BilinForm R W :=
  LinearMap.domRestrict₁₂ B W W

end BilinForm

@[simp]
/--
theorem `lsmul_flip_apply` / 定理 `lsmul_flip_apply`

English:
theorem lsmul_flip_apply
  given: (m : M)
  statement: (lsmul R M).flip m = toSpanSingleton R M m
  proof: rfl

中文:
定理 lsmul_flip_apply
  条件: (m : M)
  结论: (lsmul R M).flip m = toSpanSingleton R M m
  证明: rfl
-/
theorem lsmul_flip_apply (m : M) : (lsmul R M).flip m = toSpanSingleton R M m := rfl

end LinearMap
