/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Bilinear form and linear maps

This file describes the relation between bilinear forms and linear maps.

## TODO

A lot of this file is now redundant following the replacement of the dedicated `_root_.BilinForm`
structure with `LinearMap.BilinForm`, which is just an alias for `M →ₗ[R] M →ₗ[R] R`. For example
`LinearMap.BilinForm.toLinHom` is now just the identity map. This redundant code should be removed.

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

open LinearMap (BilinForm)
open LinearMap (BilinMap)
open Module

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

section ToLin'

/--
Definition of `toLinHomAux₁` / `toLinHomAux₁` 的定义

English:
definition toLinHomAux₁
  signature: (A : BilinForm R M) (x : M)
  body: A x

中文:
定义 toLinHomAux₁
  签名: (A : BilinForm R M) (x : M)
  定义体: A x
-/
def toLinHomAux₁ (A : BilinForm R M) (x : M) : M ->ₗ[R] R := A x

variable (B)

/--
theorem `sum_left` / 定理 `sum_left`

English:
theorem sum_left
  given: {α} (t : Finset α) (g : α -> M) (w : M)
  proof: B.map_sum₂ t g w

中文:
定理 sum_left
  条件: {α} (t : 有限集 α) (g : α -> M) (w : M)
  证明: B.map_sum₂ t g w

Depends on / 依赖: B.map_sum
-/
theorem sum_left {α} (t : Finset α) (g : α -> M) (w : M) :
    B (∑ i in t, g i) w = ∑ i in t, B (g i) w :=
  B.map_sum₂ t g w

variable (w : M)

/--
theorem `sum_right` / 定理 `sum_right`

English:
theorem sum_right
  given: {α} (t : Finset α) (w : M) (g : α -> M)
  proof: map_sum _ _ _

中文:
定理 sum_right
  条件: {α} (t : 有限集 α) (w : M) (g : α -> M)
  证明: map_sum _ _ _

Depends on / 依赖: map_sum
-/
theorem sum_right {α} (t : Finset α) (w : M) (g : α -> M) :
    B w (∑ i in t, g i) = ∑ i in t, B w (g i) := map_sum _ _ _

/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  given: {α} (t : Finset α) (B : α -> BilinForm R M) (v w : M)
  proof: by
  simp only [coe_sum, Finset.sum_apply]

中文:
定理 sum_apply
  条件: {α} (t : 有限集 α) (B : α -> BilinForm R M) (v w : M)
  证明: by
  simp only [coe_sum, Finset.sum_apply]

Depends on / 依赖: Finset, Finset.sum_apply, coe_sum, sum_apply
-/
theorem sum_apply {α} (t : Finset α) (B : α -> BilinForm R M) (v w : M) :
    (∑ i in t, B i) v w = ∑ i in t, B i v w := by
  simp only [coe_sum, Finset.sum_apply]

variable {B}

/--
Definition of `toLinHomFlip` / `toLinHomFlip` 的定义

English:
definition toLinHomFlip
  signature: : BilinForm R M ->ₗ[R] M ->ₗ[R] M ->ₗ[R] R
  body: flipHom.toLinearMap

中文:
定义 toLinHomFlip
  签名: : BilinForm R M ->ₗ[R] M ->ₗ[R] M ->ₗ[R] R
  定义体: flipHom.toLinearMap

Depends on / 依赖: flipHom, flipHom.toLinearMap, toLinearMap
-/
def toLinHomFlip : BilinForm R M ->ₗ[R] M ->ₗ[R] M ->ₗ[R] R :=
  flipHom.toLinearMap

/--
theorem `toLin'Flip_apply` / 定理 `toLin'Flip_apply`

English:
theorem toLin'Flip_apply
  given: (A : BilinForm R M) (x : M)
  statement: toLinHomFlip (M := M) A x = fun y => A y x
  proof: rfl

中文:
定理 toLin'Flip_apply
  条件: (A : BilinForm R M) (x : M)
  结论: toLinHomFlip (M := M) A x = fun y => A y x
  证明: rfl
-/
theorem toLin'Flip_apply (A : BilinForm R M) (x : M) : toLinHomFlip (M := M) A x = fun y => A y x :=
  rfl

end ToLin'

end BilinForm

end LinearMap

namespace LinearMap

variable {R' : Type*} [CommSemiring R'] [Algebra R' R] [Module R' M] [IsScalarTower R' R M]

/-- Apply a linear map on the output of a bilinear form. -/
@[simps!]
/--
Definition of `compBilinForm` / `compBilinForm` 的定义

English:
definition compBilinForm
  signature: (f : R ->ₗ[R'] R') (B : BilinForm R M)
  body: compr₂ (restrictScalars₁₂ R' R' B) f

中文:
定义 compBilinForm
  签名: (f : R ->ₗ[R'] R') (B : BilinForm R M)
  定义体: compr₂ (restrictScalars₁₂ R' R' B) f
-/
def compBilinForm (f : R ->ₗ[R'] R') (B : BilinForm R M) : BilinForm R' M :=
  compr₂ (restrictScalars₁₂ R' R' B) f

end LinearMap

namespace LinearMap

namespace BilinForm

section Comp

variable {M' : Type w} [AddCommMonoid M'] [Module R M']

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (B : BilinForm R M') (l r : M ->ₗ[R] M')
  body: B.compl₁₂ l r

中文:
定义 comp
  签名: (B : BilinForm R M') (l r : M ->ₗ[R] M')
  定义体: B.compl₁₂ l r

Depends on / 依赖: B.compl
-/
def comp (B : BilinForm R M') (l r : M ->ₗ[R] M') : BilinForm R M := B.compl₁₂ l r

/--
Definition of `compLeft` / `compLeft` 的定义

English:
definition compLeft
  signature: (B : BilinForm R M) (f : M ->ₗ[R] M)
  body: B.comp f LinearMap.id

中文:
定义 compLeft
  签名: (B : BilinForm R M) (f : M ->ₗ[R] M)
  定义体: B.comp f LinearMap.id

Depends on / 依赖: B.comp, LinearMap, LinearMap.id
-/
def compLeft (B : BilinForm R M) (f : M ->ₗ[R] M) : BilinForm R M :=
  B.comp f LinearMap.id

/--
Definition of `compRight` / `compRight` 的定义

English:
definition compRight
  signature: (B : BilinForm R M) (f : M ->ₗ[R] M)
  body: B.comp LinearMap.id f

中文:
定义 compRight
  签名: (B : BilinForm R M) (f : M ->ₗ[R] M)
  定义体: B.comp LinearMap.id f

Depends on / 依赖: B.comp, LinearMap, LinearMap.id
-/
def compRight (B : BilinForm R M) (f : M ->ₗ[R] M) : BilinForm R M :=
  B.comp LinearMap.id f

/--
theorem `comp_comp` / 定理 `comp_comp`

English:
theorem comp_comp
  statement: {M'' : Type*} [AddCommMonoid M''] [Module R M''] (B : BilinForm R M'')
  proof: rfl

@[simp]

中文:
定理 comp_comp
  结论: {M'' : 类型} [加法交换幺半群 M''] [模 R M''] (B : BilinForm R M'')
  证明: rfl

@[simp]
-/
theorem comp_comp {M'' : Type*} [AddCommMonoid M''] [Module R M''] (B : BilinForm R M'')
    (l r : M ->ₗ[R] M') (l' r' : M' ->ₗ[R] M'') :
    (B.comp l' r').comp l r = B.comp (l'.comp l) (r'.comp r) :=
  rfl

@[simp]
/--
theorem `compLeft_compRight` / 定理 `compLeft_compRight`

English:
theorem compLeft_compRight
  given: (B : BilinForm R M) (l r : M ->ₗ[R] M)
  proof: rfl

@[simp]

中文:
定理 compLeft_compRight
  条件: (B : BilinForm R M) (l r : M ->ₗ[R] M)
  证明: rfl

@[simp]
-/
theorem compLeft_compRight (B : BilinForm R M) (l r : M ->ₗ[R] M) :
    (B.compLeft l).compRight r = B.comp l r :=
  rfl

@[simp]
/--
theorem `compRight_compLeft` / 定理 `compRight_compLeft`

English:
theorem compRight_compLeft
  given: (B : BilinForm R M) (l r : M ->ₗ[R] M)
  proof: rfl

@[simp]

中文:
定理 compRight_compLeft
  条件: (B : BilinForm R M) (l r : M ->ₗ[R] M)
  证明: rfl

@[simp]
-/
theorem compRight_compLeft (B : BilinForm R M) (l r : M ->ₗ[R] M) :
    (B.compRight r).compLeft l = B.comp l r :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (B : BilinForm R M') (l r : M ->ₗ[R] M') (v w)
  statement: B.comp l r v w = B (l v) (r w)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (B : BilinForm R M') (l r : M ->ₗ[R] M') (v w)
  结论: B.comp l r v w = B (l v) (r w)
  证明: rfl

@[simp]
-/
theorem comp_apply (B : BilinForm R M') (l r : M ->ₗ[R] M') (v w) : B.comp l r v w = B (l v) (r w) :=
  rfl

@[simp]
/--
theorem `compLeft_apply` / 定理 `compLeft_apply`

English:
theorem compLeft_apply
  given: (B : BilinForm R M) (f : M ->ₗ[R] M) (v w)
  statement: B.compLeft f v w = B (f v) w
  proof: rfl

@[simp]

中文:
定理 compLeft_apply
  条件: (B : BilinForm R M) (f : M ->ₗ[R] M) (v w)
  结论: B.compLeft f v w = B (f v) w
  证明: rfl

@[simp]
-/
theorem compLeft_apply (B : BilinForm R M) (f : M ->ₗ[R] M) (v w) : B.compLeft f v w = B (f v) w :=
  rfl

@[simp]
/--
theorem `compRight_apply` / 定理 `compRight_apply`

English:
theorem compRight_apply
  given: (B : BilinForm R M) (f : M ->ₗ[R] M) (v w)
  statement: B.compRight f v w = B v (f w)
  proof: rfl

@[simp]

中文:
定理 compRight_apply
  条件: (B : BilinForm R M) (f : M ->ₗ[R] M) (v w)
  结论: B.compRight f v w = B v (f w)
  证明: rfl

@[simp]
-/
theorem compRight_apply (B : BilinForm R M) (f : M ->ₗ[R] M) (v w) : B.compRight f v w = B v (f w) :=
  rfl

@[simp]
/--
theorem `comp_id_left` / 定理 `comp_id_left`

English:
theorem comp_id_left
  given: (B : BilinForm R M) (r : M ->ₗ[R] M)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 comp_id_left
  条件: (B : BilinForm R M) (r : M ->ₗ[R] M)
  证明: by
  ext
  rfl

@[simp]
-/
theorem comp_id_left (B : BilinForm R M) (r : M ->ₗ[R] M) :
    B.comp LinearMap.id r = B.compRight r := by
  ext
  rfl

@[simp]
/--
theorem `comp_id_right` / 定理 `comp_id_right`

English:
theorem comp_id_right
  given: (B : BilinForm R M) (l : M ->ₗ[R] M)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 comp_id_right
  条件: (B : BilinForm R M) (l : M ->ₗ[R] M)
  证明: by
  ext
  rfl

@[simp]
-/
theorem comp_id_right (B : BilinForm R M) (l : M ->ₗ[R] M) :
    B.comp l LinearMap.id = B.compLeft l := by
  ext
  rfl

@[simp]
/--
theorem `compLeft_id` / 定理 `compLeft_id`

English:
theorem compLeft_id
  given: (B : BilinForm R M)
  statement: B.compLeft LinearMap.id = B
  proof: by
  ext
  rfl

@[simp]

中文:
定理 compLeft_id
  条件: (B : BilinForm R M)
  结论: B.compLeft 线性映射.id = B
  证明: by
  ext
  rfl

@[simp]
-/
theorem compLeft_id (B : BilinForm R M) : B.compLeft LinearMap.id = B := by
  ext
  rfl

@[simp]
/--
theorem `compRight_id` / 定理 `compRight_id`

English:
theorem compRight_id
  given: (B : BilinForm R M)
  statement: B.compRight LinearMap.id = B
  proof: by
  ext
  rfl

中文:
定理 compRight_id
  条件: (B : BilinForm R M)
  结论: B.compRight 线性映射.id = B
  证明: by
  ext
  rfl
-/
theorem compRight_id (B : BilinForm R M) : B.compRight LinearMap.id = B := by
  ext
  rfl

-- Shortcut for `comp_id_{left,right}` followed by `comp{Right,Left}_id`,
-- Needs higher priority to be applied
@[simp high]
/--
theorem `comp_id_id` / 定理 `comp_id_id`

English:
theorem comp_id_id
  given: (B : BilinForm R M)
  statement: B.comp LinearMap.id LinearMap.id = B
  proof: by
  ext
  rfl

中文:
定理 comp_id_id
  条件: (B : BilinForm R M)
  结论: B.comp 线性映射.id 线性映射.id = B
  证明: by
  ext
  rfl
-/
theorem comp_id_id (B : BilinForm R M) : B.comp LinearMap.id LinearMap.id = B := by
  ext
  rfl

/--
theorem `comp_inj` / 定理 `comp_inj`

English:
theorem comp_inj
  statement: (B₁ B₂ : BilinForm R M') {l r : M ->ₗ[R] M'} (hₗ : Function.Surjective l)
  proof: by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y
    obtain ⟨x', rfl⟩ := hₗ x
    obtain ⟨y', rfl⟩ := hᵣ y
    rw [← comp_apply]; rw [← comp_apply]; rw [h]
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    rw [h]

中文:
定理 comp_inj
  结论: (B₁ B₂ : BilinForm R M') {l r : M ->ₗ[R] M'} (hₗ : 函数.满射 l)
  证明: by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y
    obtain ⟨x', rfl⟩ := hₗ x
    obtain ⟨y', rfl⟩ := hᵣ y
    rw [← comp_apply]; rw [← comp_apply]; rw [h]
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    rw [h]

Depends on / 依赖: comp_apply
-/
theorem comp_inj (B₁ B₂ : BilinForm R M') {l r : M ->ₗ[R] M'} (hₗ : Function.Surjective l)
    (hᵣ : Function.Surjective r) : B₁.comp l r = B₂.comp l r ↔ B₁ = B₂ := by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y
    obtain ⟨x', rfl⟩ := hₗ x
    obtain ⟨y', rfl⟩ := hᵣ y
    rw [← comp_apply]; rw [← comp_apply]; rw [h]
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    rw [h]

end Comp

variable {M' M'' : Type*}
variable [AddCommMonoid M'] [AddCommMonoid M''] [Module R M'] [Module R M'']

section congr

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (e : M ≃ₗ[R] M')
  body: LinearEquiv.congrRight (LinearEquiv.congrLeft _ _ e) ≪≫ₗ LinearEquiv.congrLeft _ _ e

@[simp]

中文:
定义 congr
  签名: (e : M ≃ₗ[R] M')
  定义体: LinearEquiv.congrRight (LinearEquiv.congrLeft _ _ e) ≪≫ₗ LinearEquiv.congrLeft _ _ e

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.congrLeft, LinearEquiv.congrRight, congrLeft, congrRight
-/
def congr (e : M ≃ₗ[R] M') : BilinForm R M ≃ₗ[R] BilinForm R M' :=
  LinearEquiv.congrRight (LinearEquiv.congrLeft _ _ e) ≪≫ₗ LinearEquiv.congrLeft _ _ e

@[simp]
/--
theorem `congr_apply` / 定理 `congr_apply`

English:
theorem congr_apply
  given: (e : M ≃ₗ[R] M') (B : BilinForm R M) (x y : M')
  proof: rfl

@[simp]

中文:
定理 congr_apply
  条件: (e : M ≃ₗ[R] M') (B : BilinForm R M) (x y : M')
  证明: rfl

@[simp]
-/
theorem congr_apply (e : M ≃ₗ[R] M') (B : BilinForm R M) (x y : M') :
    congr e B x y = B (e.symm x) (e.symm y) :=
  rfl

@[simp]
/--
theorem `congr_symm` / 定理 `congr_symm`

English:
theorem congr_symm
  given: (e : M ≃ₗ[R] M')
  statement: (congr e).symm = congr e.symm
  proof: by
  rfl

@[simp]

中文:
定理 congr_symm
  条件: (e : M ≃ₗ[R] M')
  结论: (congr e).symm = congr e.symm
  证明: by
  rfl

@[simp]
-/
theorem congr_symm (e : M ≃ₗ[R] M') : (congr e).symm = congr e.symm := by
  rfl

@[simp]
/--
theorem `congr_refl` / 定理 `congr_refl`

English:
theorem congr_refl
  statement: congr (LinearEquiv.refl R M) = LinearEquiv.refl R _
  proof: LinearEquiv.ext fun _ => ext₂ fun _ _ => rfl

中文:
定理 congr_refl
  结论: congr (线性等价.refl R M) = 线性等价.refl R _
  证明: LinearEquiv.ext fun _ => ext₂ fun _ _ => rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.ext
-/
theorem congr_refl : congr (LinearEquiv.refl R M) = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun _ => ext₂ fun _ _ => rfl

/--
theorem `congr_trans` / 定理 `congr_trans`

English:
theorem congr_trans
  given: (e : M ≃ₗ[R] M') (f : M' ≃ₗ[R] M'')
  proof: rfl

中文:
定理 congr_trans
  条件: (e : M ≃ₗ[R] M') (f : M' ≃ₗ[R] M'')
  证明: rfl
-/
theorem congr_trans (e : M ≃ₗ[R] M') (f : M' ≃ₗ[R] M'') :
    (congr e).trans (congr f) = congr (e.trans f) :=
  rfl

/--
theorem `congr_congr` / 定理 `congr_congr`

English:
theorem congr_congr
  given: (e : M' ≃ₗ[R] M'') (f : M ≃ₗ[R] M') (B : BilinForm R M)
  proof: rfl

中文:
定理 congr_congr
  条件: (e : M' ≃ₗ[R] M'') (f : M ≃ₗ[R] M') (B : BilinForm R M)
  证明: rfl
-/
theorem congr_congr (e : M' ≃ₗ[R] M'') (f : M ≃ₗ[R] M') (B : BilinForm R M) :
    congr e (congr f B) = congr (f.trans e) B :=
  rfl

/--
theorem `congr_comp` / 定理 `congr_comp`

English:
theorem congr_comp
  given: (e : M ≃ₗ[R] M') (B : BilinForm R M) (l r : M'' ->ₗ[R] M')
  proof: rfl

中文:
定理 congr_comp
  条件: (e : M ≃ₗ[R] M') (B : BilinForm R M) (l r : M'' ->ₗ[R] M')
  证明: rfl
-/
theorem congr_comp (e : M ≃ₗ[R] M') (B : BilinForm R M) (l r : M'' ->ₗ[R] M') :
    (congr e B).comp l r =
      B.comp (LinearMap.comp (e.symm : M' ->ₗ[R] M) l)
        (LinearMap.comp (e.symm : M' ->ₗ[R] M) r) :=
  rfl

/--
theorem `comp_congr` / 定理 `comp_congr`

English:
theorem comp_congr
  given: (e : M' ≃ₗ[R] M'') (B : BilinForm R M) (l r : M' ->ₗ[R] M)
  proof: rfl

中文:
定理 comp_congr
  条件: (e : M' ≃ₗ[R] M'') (B : BilinForm R M) (l r : M' ->ₗ[R] M)
  证明: rfl
-/
theorem comp_congr (e : M' ≃ₗ[R] M'') (B : BilinForm R M) (l r : M' ->ₗ[R] M) :
    congr e (B.comp l r) =
      B.comp (l.comp (e.symm : M'' ->ₗ[R] M')) (r.comp (e.symm : M'' ->ₗ[R] M')) :=
  rfl

end congr

section congrRight₂

variable {N₁ N₂ N₃ : Type*}
variable [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
variable [Module R N₁] [Module R N₂] [Module R N₃]

/--
Definition of `_root_.LinearEquiv.congrRight₂` / `_root_.LinearEquiv.congrRight₂` 的定义

English:
definition _root_.LinearEquiv.congrRight₂
  signature: (e : N₁ ≃ₗ[R] N₂)
  body: LinearEquiv.congrRight (LinearEquiv.congrRight e)

@[simp]

中文:
定义 _root_.线性等价.congrRight₂
  签名: (e : N₁ ≃ₗ[R] N₂)
  定义体: LinearEquiv.congrRight (LinearEquiv.congrRight e)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.congrRight, congrRight
-/
def _root_.LinearEquiv.congrRight₂ (e : N₁ ≃ₗ[R] N₂) : BilinMap R M N₁ ≃ₗ[R] BilinMap R M N₂ :=
  LinearEquiv.congrRight (LinearEquiv.congrRight e)

@[simp]
/--
theorem `_root_.LinearEquiv.congrRight₂_apply` / 定理 `_root_.LinearEquiv.congrRight₂_apply`

English:
theorem _root_.LinearEquiv.congrRight₂_apply
  given: (e : N₁ ≃ₗ[R] N₂) (B : BilinMap R M N₁)
  proof: rfl

@[simp]

中文:
定理 _root_.线性等价.congrRight₂_apply
  条件: (e : N₁ ≃ₗ[R] N₂) (B : BilinMap R M N₁)
  证明: rfl

@[simp]
-/
theorem _root_.LinearEquiv.congrRight₂_apply (e : N₁ ≃ₗ[R] N₂) (B : BilinMap R M N₁) :
    LinearEquiv.congrRight₂ e B = compr₂ B e := rfl

@[simp]
/--
theorem `_root_.LinearEquiv.congrRight₂_refl` / 定理 `_root_.LinearEquiv.congrRight₂_refl`

English:
theorem _root_.LinearEquiv.congrRight₂_refl
  proof: rfl

@[simp]

中文:
定理 _root_.线性等价.congrRight₂_refl
  证明: rfl

@[simp]
-/
theorem _root_.LinearEquiv.congrRight₂_refl :
    LinearEquiv.congrRight₂ (.refl R N₁) = .refl R (BilinMap R M N₁) := rfl

@[simp]
/--
theorem `_root_.LinearEquiv.congrRight_symm` / 定理 `_root_.LinearEquiv.congrRight_symm`

English:
theorem _root_.LinearEquiv.congrRight_symm
  given: (e : N₁ ≃ₗ[R] N₂)
  proof: rfl

中文:
定理 _root_.线性等价.congrRight_symm
  条件: (e : N₁ ≃ₗ[R] N₂)
  证明: rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.congrRight, e.symm
-/
theorem _root_.LinearEquiv.congrRight_symm (e : N₁ ≃ₗ[R] N₂) :
    (LinearEquiv.congrRight₂ e (M := M)).symm = LinearEquiv.congrRight₂ e.symm :=
  rfl

/--
theorem `_root_.LinearEquiv.congrRight₂_trans` / 定理 `_root_.LinearEquiv.congrRight₂_trans`

English:
theorem _root_.LinearEquiv.congrRight₂_trans
  given: (e₁₂ : N₁ ≃ₗ[R] N₂) (e₂₃ : N₂ ≃ₗ[R] N₃)
  proof: rfl

中文:
定理 _root_.线性等价.congrRight₂_trans
  条件: (e₁₂ : N₁ ≃ₗ[R] N₂) (e₂₃ : N₂ ≃ₗ[R] N₃)
  证明: rfl
-/
theorem _root_.LinearEquiv.congrRight₂_trans (e₁₂ : N₁ ≃ₗ[R] N₂) (e₂₃ : N₂ ≃ₗ[R] N₃) :
    LinearEquiv.congrRight₂ (M := M) (e₁₂ ≪≫ₗ e₂₃) =
    LinearEquiv.congrRight₂ e₁₂ ≪≫ₗ LinearEquiv.congrRight₂ e₂₃ :=
  rfl

end congrRight₂

section LinMulLin

/--
Definition of `linMulLin` / `linMulLin` 的定义

English:
definition linMulLin
  signature: (f g : M ->ₗ[R] R)
  body: (LinearMap.mul R R).compl₁₂ f g

中文:
定义 linMulLin
  签名: (f g : M ->ₗ[R] R)
  定义体: (LinearMap.mul R R).compl₁₂ f g

Depends on / 依赖: LinearMap, LinearMap.mul
-/
def linMulLin (f g : M ->ₗ[R] R) : BilinForm R M := (LinearMap.mul R R).compl₁₂ f g

variable {f g : M ->ₗ[R] R}

@[simp]
/--
theorem `linMulLin_apply` / 定理 `linMulLin_apply`

English:
theorem linMulLin_apply
  given: (x y)
  statement: linMulLin f g x y = f x * g y
  proof: rfl

@[simp]

中文:
定理 linMulLin_apply
  条件: (x y)
  结论: linMulLin f g x y = f x * g y
  证明: rfl

@[simp]
-/
theorem linMulLin_apply (x y) : linMulLin f g x y = f x * g y :=
  rfl

@[simp]
/--
theorem `linMulLin_comp` / 定理 `linMulLin_comp`

English:
theorem linMulLin_comp
  given: (l r : M' ->ₗ[R] M)
  proof: rfl

@[simp]

中文:
定理 linMulLin_comp
  条件: (l r : M' ->ₗ[R] M)
  证明: rfl

@[simp]
-/
theorem linMulLin_comp (l r : M' ->ₗ[R] M) :
    (linMulLin f g).comp l r = linMulLin (f.comp l) (g.comp r) :=
  rfl

@[simp]
/--
theorem `linMulLin_compLeft` / 定理 `linMulLin_compLeft`

English:
theorem linMulLin_compLeft
  given: (l : M ->ₗ[R] M)
  proof: rfl

@[simp]

中文:
定理 linMulLin_compLeft
  条件: (l : M ->ₗ[R] M)
  证明: rfl

@[simp]
-/
theorem linMulLin_compLeft (l : M ->ₗ[R] M) :
    (linMulLin f g).compLeft l = linMulLin (f.comp l) g :=
  rfl

@[simp]
/--
theorem `linMulLin_compRight` / 定理 `linMulLin_compRight`

English:
theorem linMulLin_compRight
  given: (r : M ->ₗ[R] M)
  proof: rfl

中文:
定理 linMulLin_compRight
  条件: (r : M ->ₗ[R] M)
  证明: rfl
-/
theorem linMulLin_compRight (r : M ->ₗ[R] M) :
    (linMulLin f g).compRight r = linMulLin f (g.comp r) :=
  rfl

end LinMulLin

section Basis

variable {F₂ : BilinForm R M}
variable {ι : Type*} (b : Basis ι R M)

/--
theorem `ext_basis` / 定理 `ext_basis`

English:
theorem ext_basis
  given: (h : forall i j, B (b i) (b j) = F₂ (b i) (b j))
  statement: B = F₂
  proof: b.ext fun i => b.ext fun j => h i j

中文:
定理 ext_basis
  条件: (h : 对任意 i j, B (b i) (b j) = F₂ (b i) (b j))
  结论: B = F₂
  证明: b.ext fun i => b.ext fun j => h i j

Depends on / 依赖: b.ext
-/
theorem ext_basis (h : forall i j, B (b i) (b j) = F₂ (b i) (b j)) : B = F₂ :=
  b.ext fun i => b.ext fun j => h i j

/--
theorem `sum_repr_mul_repr_mul` / 定理 `sum_repr_mul_repr_mul`

English:
theorem sum_repr_mul_repr_mul
  given: (x y : M)
  proof: by
  conv_rhs => rw [← b.linearCombination_repr x, ← b.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, sum_left, sum_right, smul_left, smul_right,
    smul_eq_mul]

中文:
定理 sum_repr_mul_repr_mul
  条件: (x y : M)
  证明: by
  conv_rhs => rw [← b.linearCombination_repr x, ← b.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, sum_left, sum_right, smul_left, smul_right,
    smul_eq_mul]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.sum, b.linearCombination_repr, conv_rhs, linearCombination_apply, linearCombination_repr, simp_rw, smul_eq_mul, smul_left, smul_right, sum_left, sum_right
-/
theorem sum_repr_mul_repr_mul (x y : M) :
    ((b.repr x).sum fun i xi => (b.repr y).sum fun j yj => xi • yj • B (b i) (b j)) = B x y := by
  conv_rhs => rw [← b.linearCombination_repr x, ← b.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, sum_left, sum_right, smul_left, smul_right,
    smul_eq_mul]

end Basis

end BilinForm

end LinearMap
