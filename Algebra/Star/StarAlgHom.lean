/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Star.StarRingHom

/-!
# Morphisms of star algebras

This file defines morphisms between `R`-algebras (unital or non-unital) `A` and `B` where both
`A` and `B` are equipped with a `star` operation. These morphisms, namely `StarAlgHom` and
`NonUnitalStarAlgHom` are direct extensions of their non-`star`red counterparts with a field
`map_star` which guarantees they preserve the star operation. We keep the type classes as generic
as possible, in keeping with the definition of `NonUnitalAlgHom` in the non-unital case. In this
file, we only assume `Star` unless we want to talk about the zero map as a
`NonUnitalStarAlgHom`, in which case we need `StarAddMonoid`. Note that the scalar ring `R`
is not required to have a star operation, nor do we need `StarRing` or `StarModule` structures on
`A` and `B`.

As with `NonUnitalAlgHom`, in the non-unital case the multiplications are not assumed to be
associative or unital, or even to be compatible with the scalar actions. In a typical application,
the operations will satisfy compatibility conditions making them into algebras (albeit possibly
non-associative and/or non-unital) but such conditions are not required here for the definitions.

The primary impetus for defining these types is that they constitute the morphisms in the categories
of unital C⋆-algebras (with `StarAlgHom`s) and of C⋆-algebras (with `NonUnitalStarAlgHom`s).

## Main definitions

  * `NonUnitalStarAlgHom`
  * `StarAlgHom`

## Tags

non-unital, algebra, morphism, star
-/

@[expose] public section

open EquivLike

/-! ### Non-unital star algebra homomorphisms -/


/--
Definition of `NonUnitalStarAlgHom` / `NonUnitalStarAlgHom` 的定义

English:
structure NonUnitalStarAlgHom
  parameters: (R A B : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
  extends: A ->ₙₐ[R] B
  axioms and operations (1):
    - map_star' : forall a : A, toFun (star a) = star (toFun a)

中文:
结构 NonUnitalStarAlgHom
  参数: (R A B : 类型) [Monoid R] [NonUnitalNonAssocSemiring A]
  继承: A ->ₙₐ[R] B
  公理与运算 (1 个):
    - map_star' : 对任意 a : A, toFun (star a) = star (toFun a)
-/
structure NonUnitalStarAlgHom (R A B : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
  [DistribMulAction R A] [Star A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
  [Star B] extends A ->ₙₐ[R] B where
  /-- By definition, a non-unital ⋆-algebra homomorphism preserves the `star` operation. -/
  map_star' : forall a : A, toFun (star a) = star (toFun a)

@[inherit_doc NonUnitalStarAlgHom] infixr:25 " ->⋆ₙₐ " => NonUnitalStarAlgHom _

@[inherit_doc] notation:25 A " ->⋆ₙₐ[" R "] " B => NonUnitalStarAlgHom R A B

/-- Reinterpret a non-unital star algebra homomorphism as a non-unital algebra homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc NonUnitalStarAlgHom.toNonUnitalAlgHom

namespace NonUnitalStarAlgHomClass

variable {F R A B : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

/-- Turn an element of a type `F` satisfying `NonUnitalAlgHomClass F R A B` and `StarHomClass F A B`
into an actual `NonUnitalStarAlgHom`. This is declared as the default coercion from `F` to
`A →⋆ₙₐ[R] B`. -/
@[coe]
/--
Definition of `toNonUnitalStarAlgHom` / `toNonUnitalStarAlgHom` 的定义

English:
definition toNonUnitalStarAlgHom
  signature: [StarHomClass F A B] (f : F)
  body: { (f : A ->ₙₐ[R] B) with
    map_star' := map_star f }

中文:
定义 toNonUnitalStarAlgHom
  签名: [StarHomClass F A B] (f : F)
  定义体: { (f : A ->ₙₐ[R] B) with
    map_star' := map_star f }

Depends on / 依赖: map_star
-/
def toNonUnitalStarAlgHom [StarHomClass F A B] (f : F) : A ->⋆ₙₐ[R] B :=
  { (f : A ->ₙₐ[R] B) with
    map_star' := map_star f }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [StarHomClass
  signature: F A B] : CoeTC F (A ->⋆ₙₐ[R] B)
  body: ⟨toNonUnitalStarAlgHom⟩

中文:
实例 [StarHomClass
  签名: F A B] : CoeTC F (A ->⋆ₙₐ[R] B)
  定义体: ⟨toNonUnitalStarAlgHom⟩

Depends on / 依赖: toNonUnitalStarAlgHom
-/
instance [StarHomClass F A B] : CoeTC F (A ->⋆ₙₐ[R] B) :=
  ⟨toNonUnitalStarAlgHom⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [StarHomClass
  signature: F A B] : NonUnitalStarRingHomClass F A B
  body: NonUnitalStarRingHomClass.mk

中文:
实例 [StarHomClass
  签名: F A B] : NonUnitalStarRingHomClass F A B
  定义体: NonUnitalStarRingHomClass.mk

Depends on / 依赖: NonUnitalStarRingHomClass, NonUnitalStarRingHomClass.mk
-/
instance [StarHomClass F A B] : NonUnitalStarRingHomClass F A B :=
  NonUnitalStarRingHomClass.mk

end NonUnitalStarAlgHomClass

namespace NonUnitalStarAlgHom

section Basic

variable {R A B C D : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]
variable [NonUnitalNonAssocSemiring D] [DistribMulAction R D] [Star D]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ->⋆ₙₐ[R] B) A B
  body: f.toFun
  coe_injective := by rintro ⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩ h; congr

中文:
实例 :
  签名: FunLike (A ->⋆ₙₐ[R] B) A B
  定义体: f.toFun
  coe_injective := by rintro ⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩ h; congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (A ->⋆ₙₐ[R] B) A B where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩ h; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalAlgHomClass (A ->⋆ₙₐ[R] B) R A B
  body: f.map_smul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'

中文:
实例 :
  签名: NonUnitalAlgHomClass (A ->⋆ₙₐ[R] B) R A B
  定义体: f.map_smul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'

Depends on / 依赖: f.map_smul, map_smul
-/
instance : NonUnitalAlgHomClass (A ->⋆ₙₐ[R] B) R A B where
  map_smulₛₗ f := f.map_smul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarHomClass (A ->⋆ₙₐ[R] B) A B
  body: f.map_star'

initialize_simps_projections NonUnitalStarAlgHom
  (toFun -> apply)

@[simp]

中文:
实例 :
  签名: StarHomClass (A ->⋆ₙₐ[R] B) A B
  定义体: f.map_star'

initialize_simps_projections NonUnitalStarAlgHom
  (toFun -> apply)

@[simp]

Depends on / 依赖: f.map_star, map_star
-/
instance : StarHomClass (A ->⋆ₙₐ[R] B) A B where
  map_star f := f.map_star'

initialize_simps_projections NonUnitalStarAlgHom
  (toFun -> apply)

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F R A B]
  proof: rfl

@[simp]

中文:
定理 coe_coe
  结论: {F : 类型} [FunLike F A B] [NonUnitalAlgHomClass F R A B]
  证明: rfl

@[simp]
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F R A B]
    [StarHomClass F A B] (f : F) :
    ⇑(f : A ->⋆ₙₐ[R] B) = f := rfl

@[simp]
/--
theorem `coe_toNonUnitalAlgHom` / 定理 `coe_toNonUnitalAlgHom`

English:
theorem coe_toNonUnitalAlgHom
  given: {f : A ->⋆ₙₐ[R] B}
  statement: (f.toNonUnitalAlgHom : A -> B) = f
  proof: rfl

@[ext]

中文:
定理 coe_toNonUnitalAlgHom
  条件: {f : A ->⋆ₙₐ[R] B}
  结论: (f.toNonUnitalAlgHom : A -> B) = f
  证明: rfl

@[ext]
-/
theorem coe_toNonUnitalAlgHom {f : A ->⋆ₙₐ[R] B} : (f.toNonUnitalAlgHom : A -> B) = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : A ->⋆ₙₐ[R] B} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : A ->⋆ₙₐ[R] B) (f' : A -> B) (h : f' = f)
  body: f'
  map_smul' := h.symm ▸ map_smul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]

中文:
定义 copy
  签名: (f : A ->⋆ₙₐ[R] B) (f' : A -> B) (h : f' = f)
  定义体: f'
  map_smul' := h.symm ▸ map_smul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
-/
protected def copy (f : A ->⋆ₙₐ[R] B) (f' : A -> B) (h : f' = f) : A ->⋆ₙₐ[R] B where
  toFun := f'
  map_smul' := h.symm ▸ map_smul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : A ->⋆ₙₐ[R] B) (f' : A -> B) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : A ->⋆ₙₐ[R] B) (f' : A -> B) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : A ->⋆ₙₐ[R] B) (f' : A -> B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : A ->⋆ₙₐ[R] B) (f' : A -> B) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : A ->⋆ₙₐ[R] B) (f' : A -> B) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : A ->⋆ₙₐ[R] B) (f' : A -> B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : A -> B) (h₁ h₂ h₃ h₄ h₅)
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (f : A -> B) (h₁ h₂ h₃ h₄ h₅)
  证明: rfl

@[simp]
-/
theorem coe_mk (f : A -> B) (h₁ h₂ h₃ h₄ h₅) :
    ((⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅⟩ : A ->⋆ₙₐ[R] B) : A -> B) = f :=
  rfl

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (f : A ->ₙₐ[R] B) (h)
  proof: rfl

@[simp]

中文:
定理 coe_mk'
  条件: (f : A ->ₙₐ[R] B) (h)
  证明: rfl

@[simp]
-/
theorem coe_mk' (f : A ->ₙₐ[R] B) (h) :
    ((⟨f, h⟩ : A ->⋆ₙₐ[R] B) : A -> B) = f :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : A ->⋆ₙₐ[R] B) (h₁ h₂ h₃ h₄ h₅)
  proof: by
  ext
  rfl

中文:
定理 mk_coe
  条件: (f : A ->⋆ₙₐ[R] B) (h₁ h₂ h₃ h₄ h₅)
  证明: by
  ext
  rfl
-/
theorem mk_coe (f : A ->⋆ₙₐ[R] B) (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅⟩ : A ->⋆ₙₐ[R] B) = f := by
  ext
  rfl

section

variable (R A)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : A ->⋆ₙₐ[R] A
  body: { (1 : A ->ₙₐ[R] A) with map_star' := fun _ => rfl }

@[simp, norm_cast]

中文:
定义 id
  签名: : A ->⋆ₙₐ[R] A
  定义体: { (1 : A ->ₙₐ[R] A) with map_star' := fun _ => rfl }

@[simp, norm_cast]
-/
protected def id : A ->⋆ₙₐ[R] A :=
  { (1 : A ->ₙₐ[R] A) with map_star' := fun _ => rfl }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(NonUnitalStarAlgHom.id R A) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(NonUnitalStarAlgHom.id R A) = id
  证明: rfl
-/
theorem coe_id : ⇑(NonUnitalStarAlgHom.id R A) = id :=
  rfl

end

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B)
  body: { f.toNonUnitalAlgHom.comp g.toNonUnitalAlgHom with
    map_star' := by
      simp only [map_star, NonUnitalAlgHom.toFun_eq_coe, NonUnitalAlgHom.coe_comp,
        coe_toNonUnitalAlgHom, Function.comp_apply, forall_const] }

@[simp]

中文:
定义 comp
  签名: (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B)
  定义体: { f.toNonUnitalAlgHom.comp g.toNonUnitalAlgHom with
    map_star' := by
      simp only [map_star, NonUnitalAlgHom.toFun_eq_coe, NonUnitalAlgHom.coe_comp,
        coe_toNonUnitalAlgHom, Function.comp_apply, forall_const] }

@[simp]

Depends on / 依赖: Function, Function.comp_apply, NonUnitalAlgHom, NonUnitalAlgHom.coe_comp, NonUnitalAlgHom.toFun_eq_coe, coe_comp, coe_toNonUnitalAlgHom, comp_apply, f.toNonUnitalAlgHom.comp, forall_const, g.toNonUnitalAlgHom, map_star, toFun_eq_coe, toNonUnitalAlgHom
-/
def comp (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B) : A ->⋆ₙₐ[R] C :=
  { f.toNonUnitalAlgHom.comp g.toNonUnitalAlgHom with
    map_star' := by
      simp only [map_star, NonUnitalAlgHom.toFun_eq_coe, NonUnitalAlgHom.coe_comp,
        coe_toNonUnitalAlgHom, Function.comp_apply, forall_const] }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B)
  statement: ⇑(comp f g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B)
  结论: ⇑(comp f g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B) (a : A)
  statement: comp f g a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B) (a : A)
  结论: comp f g a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : C ->⋆ₙₐ[R] D) (g : B ->⋆ₙₐ[R] C) (h : A ->⋆ₙₐ[R] B)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : C ->⋆ₙₐ[R] D) (g : B ->⋆ₙₐ[R] C) (h : A ->⋆ₙₐ[R] B)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : C ->⋆ₙₐ[R] D) (g : B ->⋆ₙₐ[R] C) (h : A ->⋆ₙₐ[R] B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : A ->⋆ₙₐ[R] B)
  statement: (NonUnitalStarAlgHom.id _ _).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : A ->⋆ₙₐ[R] B)
  结论: (NonUnitalStarAlgHom.id _ _).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : A ->⋆ₙₐ[R] B) : (NonUnitalStarAlgHom.id _ _).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : A ->⋆ₙₐ[R] B)
  statement: f.comp (NonUnitalStarAlgHom.id _ _) = f
  proof: ext fun _ => rfl

中文:
定理 comp_id
  条件: (f : A ->⋆ₙₐ[R] B)
  结论: f.comp (NonUnitalStarAlgHom.id _ _) = f
  证明: ext fun _ => rfl
-/
theorem comp_id (f : A ->⋆ₙₐ[R] B) : f.comp (NonUnitalStarAlgHom.id _ _) = f :=
  ext fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (A ->⋆ₙₐ[R] A)
  body: comp
  mul_assoc := comp_assoc
  one := NonUnitalStarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

@[simp]

中文:
实例 :
  签名: Monoid (A ->⋆ₙₐ[R] A)
  定义体: comp
  mul_assoc := comp_assoc
  one := NonUnitalStarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
-/
instance : Monoid (A ->⋆ₙₐ[R] A) where
  mul := comp
  mul_assoc := comp_assoc
  one := NonUnitalStarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : A ->⋆ₙₐ[R] A) : A -> A) = id
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : A ->⋆ₙₐ[R] A) : A -> A) = id
  证明: rfl
-/
theorem coe_one : ((1 : A ->⋆ₙₐ[R] A) : A -> A) = id :=
  rfl

/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (a : A)
  statement: (1 : A ->⋆ₙₐ[R] A) a = a
  proof: rfl

中文:
定理 one_apply
  条件: (a : A)
  结论: (1 : A ->⋆ₙₐ[R] A) a = a
  证明: rfl
-/
theorem one_apply (a : A) : (1 : A ->⋆ₙₐ[R] A) a = a :=
  rfl

end Basic

section Zero

-- the `zero` requires extra type class assumptions because we need `star_zero`
variable {R A B C D : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [StarAddMonoid A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (A ->⋆ₙₐ[R] B)
  body: ⟨{ (0 : NonUnitalAlgHom (MonoidHom.id R) A B) with map_star' := by simp }⟩

中文:
实例 :
  签名: Zero (A ->⋆ₙₐ[R] B)
  定义体: ⟨{ (0 : NonUnitalAlgHom (MonoidHom.id R) A B) with map_star' := by simp }⟩

Depends on / 依赖: MonoidHom, MonoidHom.id, NonUnitalAlgHom, map_star
-/
instance : Zero (A ->⋆ₙₐ[R] B) :=
  ⟨{ (0 : NonUnitalAlgHom (MonoidHom.id R) A B) with map_star' := by simp }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (A ->⋆ₙₐ[R] B)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (A ->⋆ₙₐ[R] B)
  定义体: ⟨0⟩
-/
instance : Inhabited (A ->⋆ₙₐ[R] B) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidWithZero (A ->⋆ₙₐ[R] A)
  body: { (inferInstance : Monoid (A ->⋆ₙₐ[R] A)),
    (inferInstance : Zero (A ->⋆ₙₐ[R] A)) with
    zero_mul := fun _ => ext fun _ => rfl
    mul_zero := fun f => ext fun _ => map_zero f }

@[simp]

中文:
实例 :
  签名: MonoidWithZero (A ->⋆ₙₐ[R] A)
  定义体: { (inferInstance : Monoid (A ->⋆ₙₐ[R] A)),
    (inferInstance : Zero (A ->⋆ₙₐ[R] A)) with
    zero_mul := fun _ => ext fun _ => rfl
    mul_zero := fun f => ext fun _ => map_zero f }

@[simp]

Depends on / 依赖: Monoid, map_zero, mul_zero, zero_mul
-/
instance : MonoidWithZero (A ->⋆ₙₐ[R] A) :=
  { (inferInstance : Monoid (A ->⋆ₙₐ[R] A)),
    (inferInstance : Zero (A ->⋆ₙₐ[R] A)) with
    zero_mul := fun _ => ext fun _ => rfl
    mul_zero := fun f => ext fun _ => map_zero f }

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : A ->⋆ₙₐ[R] B) : A -> B) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ((0 : A ->⋆ₙₐ[R] B) : A -> B) = 0
  证明: rfl
-/
theorem coe_zero : ((0 : A ->⋆ₙₐ[R] B) : A -> B) = 0 :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (a : A)
  statement: (0 : A ->⋆ₙₐ[R] B) a = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (a : A)
  结论: (0 : A ->⋆ₙₐ[R] B) a = 0
  证明: rfl
-/
theorem zero_apply (a : A) : (0 : A ->⋆ₙₐ[R] B) a = 0 :=
  rfl

end Zero

section RestrictScalars

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S] [Star A] [Star B]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (f : A ->⋆ₙₐ[S] B)
  body: { (f : A ->ₙₐ[S] B).restrictScalars R with
    map_star' := map_star f }

@[simp]

中文:
定义 restrictScalars
  签名: (f : A ->⋆ₙₐ[S] B)
  定义体: { (f : A ->ₙₐ[S] B).restrictScalars R with
    map_star' := map_star f }

@[simp]

Depends on / 依赖: map_star, restrictScalars
-/
def restrictScalars (f : A ->⋆ₙₐ[S] B) : A ->⋆ₙₐ[R] B :=
  { (f : A ->ₙₐ[S] B).restrictScalars R with
    map_star' := map_star f }

@[simp]
/--
lemma `restrictScalars_apply` / 引理 `restrictScalars_apply`

English:
lemma restrictScalars_apply
  given: (f : A ->⋆ₙₐ[S] B) (x : A)
  statement: f.restrictScalars R x = f x
  proof: rfl

中文:
引理 restrictScalars_apply
  条件: (f : A ->⋆ₙₐ[S] B) (x : A)
  结论: f.restrictScalars R x = f x
  证明: rfl
-/
lemma restrictScalars_apply (f : A ->⋆ₙₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl

/--
lemma `coe_restrictScalars` / 引理 `coe_restrictScalars`

English:
lemma coe_restrictScalars
  given: (f : A ->⋆ₙₐ[S] B)
  statement: (f.restrictScalars R : A ->ₙ+* B) = f
  proof: rfl

中文:
引理 coe_restrictScalars
  条件: (f : A ->⋆ₙₐ[S] B)
  结论: (f.restrictScalars R : A ->ₙ+* B) = f
  证明: rfl
-/
lemma coe_restrictScalars (f : A ->⋆ₙₐ[S] B) : (f.restrictScalars R : A ->ₙ+* B) = f := rfl

/--
lemma `coe_restrictScalars'` / 引理 `coe_restrictScalars'`

English:
lemma coe_restrictScalars'
  given: (f : A ->⋆ₙₐ[S] B)
  statement: (f.restrictScalars R : A -> B) = f
  proof: rfl

中文:
引理 coe_restrictScalars'
  条件: (f : A ->⋆ₙₐ[S] B)
  结论: (f.restrictScalars R : A -> B) = f
  证明: rfl
-/
lemma coe_restrictScalars' (f : A ->⋆ₙₐ[S] B) : (f.restrictScalars R : A -> B) = f := rfl

/--
theorem `restrictScalars_injective` / 定理 `restrictScalars_injective`

English:
theorem restrictScalars_injective
  proof: fun _ _ h => ext (DFunLike.congr_fun h :)

中文:
定理 restrictScalars_injective
  证明: fun _ _ h => ext (DFunLike.congr_fun h :)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A ->⋆ₙₐ[S] B) -> A ->⋆ₙₐ[R] B) :=
  fun _ _ h => ext (DFunLike.congr_fun h :)

end RestrictScalars

end NonUnitalStarAlgHom

/-! ### Unital star algebra homomorphisms -/


section Unital

/--
Definition of `StarAlgHom` / `StarAlgHom` 的定义

English:
structure StarAlgHom
  parameters: (R A B : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  extends: AlgHom R A B
  axioms and operations (1):
    - map_star' : forall x : A, toFun (star x) = star (toFun x)

中文:
结构 StarAlgHom
  参数: (R A B : 类型) [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  继承: AlgHom R A B
  公理与运算 (1 个):
    - map_star' : 对任意 x : A, toFun (star x) = star (toFun x)
-/
structure StarAlgHom (R A B : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B] extends AlgHom R A B where
  /-- By definition, a ⋆-algebra homomorphism preserves the `star` operation. -/
  map_star' : forall x : A, toFun (star x) = star (toFun x)

@[inherit_doc StarAlgHom] infixr:25 " ->⋆ₐ " => StarAlgHom _

@[inherit_doc] notation:25 A " ->⋆ₐ[" R "] " B => StarAlgHom R A B

/-- Reinterpret a unital star algebra homomorphism as a unital algebra homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc StarAlgHom.toAlgHom

namespace StarAlgHomClass

variable {F R A B : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
variable [Semiring B] [Algebra R B] [Star B] [FunLike F A B] [AlgHomClass F R A B]
variable [StarHomClass F A B]

/-- Turn an element of a type `F` satisfying `AlgHomClass F R A B` and `StarHomClass F A B` into an
actual `StarAlgHom`. This is declared as the default coercion from `F` to `A →⋆ₐ[R] B`. -/
@[coe]
/--
Definition of `toStarAlgHom` / `toStarAlgHom` 的定义

English:
definition toStarAlgHom
  signature: (f : F)
  body: { (AlgHomClass.toAlgHom f) with
    map_star' := map_star f }

中文:
定义 toStarAlgHom
  签名: (f : F)
  定义体: { (AlgHomClass.toAlgHom f) with
    map_star' := map_star f }

Depends on / 依赖: AlgHomClass, AlgHomClass.toAlgHom, map_star, toAlgHom
-/
def toStarAlgHom (f : F) : A ->⋆ₐ[R] B :=
  { (AlgHomClass.toAlgHom f) with
    map_star' := map_star f }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC F (A ->⋆ₐ[R] B)
  body: ⟨toStarAlgHom⟩

中文:
实例 :
  签名: CoeTC F (A ->⋆ₐ[R] B)
  定义体: ⟨toStarAlgHom⟩

Depends on / 依赖: toStarAlgHom
-/
instance : CoeTC F (A ->⋆ₐ[R] B) :=
  ⟨toStarAlgHom⟩

end StarAlgHomClass

namespace StarAlgHom

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ->⋆ₐ[R] B) A B
  body: f.toFun
  coe_injective := by rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩, _⟩ h; congr

中文:
实例 :
  签名: FunLike (A ->⋆ₐ[R] B) A B
  定义体: f.toFun
  coe_injective := by rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩, _⟩ h; congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (A ->⋆ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩, _⟩ h; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AlgHomClass (A ->⋆ₐ[R] B) R A B
  body: f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  commutes f := f.commutes'

中文:
实例 :
  签名: AlgHomClass (A ->⋆ₐ[R] B) R A B
  定义体: f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  commutes f := f.commutes'

Depends on / 依赖: f.map_mul, map_mul
-/
instance : AlgHomClass (A ->⋆ₐ[R] B) R A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  commutes f := f.commutes'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarHomClass (A ->⋆ₐ[R] B) A B
  body: f.map_star'

@[simp]

中文:
实例 :
  签名: StarHomClass (A ->⋆ₐ[R] B) A B
  定义体: f.map_star'

@[simp]

Depends on / 依赖: f.map_star, map_star
-/
instance : StarHomClass (A ->⋆ₐ[R] B) A B where
  map_star f := f.map_star'

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
  proof: rfl

initialize_simps_projections StarAlgHom (toFun -> apply)

中文:
定理 coe_coe
  结论: {F : 类型} [FunLike F A B] [AlgHomClass F R A B]
  证明: rfl

initialize_simps_projections StarAlgHom (toFun -> apply)
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    [StarHomClass F A B] (f : F) :
    ⇑(f : A ->⋆ₐ[R] B) = f :=
  rfl

initialize_simps_projections StarAlgHom (toFun -> apply)

attribute [coe] StarAlgHom.toAlgHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (A ->⋆ₐ[R] B) (A ->ₐ[R] B)
  body: ⟨toAlgHom⟩

@[simp]

中文:
实例 :
  签名: Coe (A ->⋆ₐ[R] B) (A ->ₐ[R] B)
  定义体: ⟨toAlgHom⟩

@[simp]

Depends on / 依赖: toAlgHom
-/
instance : Coe (A ->⋆ₐ[R] B) (A ->ₐ[R] B) :=
  ⟨toAlgHom⟩

@[simp]
/--
theorem `coe_toAlgHom` / 定理 `coe_toAlgHom`

English:
theorem coe_toAlgHom
  given: {f : A ->⋆ₐ[R] B}
  statement: (f.toAlgHom : A -> B) = f
  proof: rfl

@[ext]

中文:
定理 coe_toAlgHom
  条件: {f : A ->⋆ₐ[R] B}
  结论: (f.toAlgHom : A -> B) = f
  证明: rfl

@[ext]
-/
theorem coe_toAlgHom {f : A ->⋆ₐ[R] B} : (f.toAlgHom : A -> B) = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : A ->⋆ₐ[R] B} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : A ->⋆ₐ[R] B) (f' : A -> B) (h : f' = f)
  body: f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  commutes' := h.symm ▸ AlgHomClass.commutes f
  map_star' := h.symm ▸ map_star f

@[simp]

中文:
定义 copy
  签名: (f : A ->⋆ₐ[R] B) (f' : A -> B) (h : f' = f)
  定义体: f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  commutes' := h.symm ▸ AlgHomClass.commutes f
  map_star' := h.symm ▸ map_star f

@[simp]
-/
protected def copy (f : A ->⋆ₐ[R] B) (f' : A -> B) (h : f' = f) : A ->⋆ₐ[R] B where
  toFun := f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  commutes' := h.symm ▸ AlgHomClass.commutes f
  map_star' := h.symm ▸ map_star f

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : A ->⋆ₐ[R] B) (f' : A -> B) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : A ->⋆ₐ[R] B) (f' : A -> B) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : A ->⋆ₐ[R] B) (f' : A -> B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : A ->⋆ₐ[R] B) (f' : A -> B) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

@[simp]

中文:
定理 copy_eq
  条件: (f : A ->⋆ₐ[R] B) (f' : A -> B) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : A ->⋆ₐ[R] B) (f' : A -> B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : A -> B) (h₁ h₂ h₃ h₄ h₅ h₆)
  proof: rfl

中文:
定理 coe_mk
  条件: (f : A -> B) (h₁ h₂ h₃ h₄ h₅ h₆)
  证明: rfl
-/
theorem coe_mk (f : A -> B) (h₁ h₂ h₃ h₄ h₅ h₆) :
    ((⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A ->⋆ₐ[R] B) : A -> B) = f :=
  rfl

-- this is probably the more useful lemma for Lean 4 and should likely replace `coe_mk` above
@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (f : A ->ₐ[R] B) (h)
  proof: rfl

@[simp]

中文:
定理 coe_mk'
  条件: (f : A ->ₐ[R] B) (h)
  证明: rfl

@[simp]
-/
theorem coe_mk' (f : A ->ₐ[R] B) (h) :
    ((⟨f, h⟩ : A ->⋆ₐ[R] B) : A -> B) = f :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : A ->⋆ₐ[R] B) (h₁ h₂ h₃ h₄ h₅ h₆)
  proof: by
  ext
  rfl

中文:
定理 mk_coe
  条件: (f : A ->⋆ₐ[R] B) (h₁ h₂ h₃ h₄ h₅ h₆)
  证明: by
  ext
  rfl
-/
theorem mk_coe (f : A ->⋆ₐ[R] B) (h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A ->⋆ₐ[R] B) = f := by
  ext
  rfl

section

variable (R A)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : A ->⋆ₐ[R] A
  body: { AlgHom.id _ _ with map_star' := fun _ => rfl }

@[simp, norm_cast]

中文:
定义 id
  签名: : A ->⋆ₐ[R] A
  定义体: { AlgHom.id _ _ with map_star' := fun _ => rfl }

@[simp, norm_cast]
-/
protected def id : A ->⋆ₐ[R] A :=
  { AlgHom.id _ _ with map_star' := fun _ => rfl }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(StarAlgHom.id R A) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(StarAlgHom.id R A) = id
  证明: rfl
-/
theorem coe_id : ⇑(StarAlgHom.id R A) = id :=
  rfl

/-- `algebraMap R A` as a `StarAlgHom` when `A` is a star algebra over `R`. -/
@[simps]
/--
Definition of `ofId` / `ofId` 的定义

English:
definition ofId
  signature: (R A : Type*) [CommSemiring R] [StarRing R] [Semiring A] [StarMul A]
  body: { Algebra.ofId R A with
    toFun := algebraMap R A
    map_star' := by simp [Algebra.algebraMap_eq_smul_one] }

中文:
定义 ofId
  签名: (R A : 类型) [CommSemiring R] [StarRing R] [Semiring A] [StarMul A]
  定义体: { Algebra.ofId R A with
    toFun := algebraMap R A
    map_star' := by simp [Algebra.algebraMap_eq_smul_one] }

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Algebra.ofId, algebraMap, algebraMap_eq_smul_one, map_star
-/
def ofId (R A : Type*) [CommSemiring R] [StarRing R] [Semiring A] [StarMul A]
    [Algebra R A] [StarModule R A] : R ->⋆ₐ[R] A :=
  { Algebra.ofId R A with
    toFun := algebraMap R A
    map_star' := by simp [Algebra.algebraMap_eq_smul_one] }

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (A ->⋆ₐ[R] A)
  body: ⟨StarAlgHom.id R A⟩

中文:
实例 :
  签名: Inhabited (A ->⋆ₐ[R] A)
  定义体: ⟨StarAlgHom.id R A⟩

Depends on / 依赖: StarAlgHom, StarAlgHom.id
-/
instance : Inhabited (A ->⋆ₐ[R] A) :=
  ⟨StarAlgHom.id R A⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B)
  body: { f.toAlgHom.comp g.toAlgHom with
    map_star' := by
      simp only [map_star, AlgHom.toFun_eq_coe, AlgHom.coe_comp, coe_toAlgHom,
        Function.comp_apply, forall_const] }

@[simp]

中文:
定义 comp
  签名: (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B)
  定义体: { f.toAlgHom.comp g.toAlgHom with
    map_star' := by
      simp only [map_star, AlgHom.toFun_eq_coe, AlgHom.coe_comp, coe_toAlgHom,
        Function.comp_apply, forall_const] }

@[simp]

Depends on / 依赖: AlgHom, AlgHom.coe_comp, AlgHom.toFun_eq_coe, Function, Function.comp_apply, coe_comp, coe_toAlgHom, comp_apply, f.toAlgHom.comp, forall_const, g.toAlgHom, map_star, toAlgHom, toFun_eq_coe
-/
def comp (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B) : A ->⋆ₐ[R] C :=
  { f.toAlgHom.comp g.toAlgHom with
    map_star' := by
      simp only [map_star, AlgHom.toFun_eq_coe, AlgHom.coe_comp, coe_toAlgHom,
        Function.comp_apply, forall_const] }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B)
  statement: ⇑(comp f g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B)
  结论: ⇑(comp f g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B) (a : A)
  statement: comp f g a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B) (a : A)
  结论: comp f g a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : C ->⋆ₐ[R] D) (g : B ->⋆ₐ[R] C) (h : A ->⋆ₐ[R] B)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : C ->⋆ₐ[R] D) (g : B ->⋆ₐ[R] C) (h : A ->⋆ₐ[R] B)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : C ->⋆ₐ[R] D) (g : B ->⋆ₐ[R] C) (h : A ->⋆ₐ[R] B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : A ->⋆ₐ[R] B)
  statement: (StarAlgHom.id _ _).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : A ->⋆ₐ[R] B)
  结论: (StarAlgHom.id _ _).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : A ->⋆ₐ[R] B) : (StarAlgHom.id _ _).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : A ->⋆ₐ[R] B)
  statement: f.comp (StarAlgHom.id _ _) = f
  proof: ext fun _ => rfl

中文:
定理 comp_id
  条件: (f : A ->⋆ₐ[R] B)
  结论: f.comp (StarAlgHom.id _ _) = f
  证明: ext fun _ => rfl
-/
theorem comp_id (f : A ->⋆ₐ[R] B) : f.comp (StarAlgHom.id _ _) = f :=
  ext fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (A ->⋆ₐ[R] A)
  body: comp
  mul_assoc := comp_assoc
  one := StarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

中文:
实例 :
  签名: Monoid (A ->⋆ₐ[R] A)
  定义体: comp
  mul_assoc := comp_assoc
  one := StarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id
-/
instance : Monoid (A ->⋆ₐ[R] A) where
  mul := comp
  mul_assoc := comp_assoc
  one := StarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

/--
Definition of `toNonUnitalStarAlgHom` / `toNonUnitalStarAlgHom` 的定义

English:
definition toNonUnitalStarAlgHom
  signature: (f : A ->⋆ₐ[R] B)
  body: { f with map_smul' := map_smul f }

@[simp]

中文:
定义 toNonUnitalStarAlgHom
  签名: (f : A ->⋆ₐ[R] B)
  定义体: { f with map_smul' := map_smul f }

@[simp]

Depends on / 依赖: map_smul
-/
def toNonUnitalStarAlgHom (f : A ->⋆ₐ[R] B) : A ->⋆ₙₐ[R] B :=
  { f with map_smul' := map_smul f }

@[simp]
/--
theorem `coe_toNonUnitalStarAlgHom` / 定理 `coe_toNonUnitalStarAlgHom`

English:
theorem coe_toNonUnitalStarAlgHom
  given: (f : A ->⋆ₐ[R] B)
  statement: (f.toNonUnitalStarAlgHom : A -> B) = f
  proof: rfl

中文:
定理 coe_toNonUnitalStarAlgHom
  条件: (f : A ->⋆ₐ[R] B)
  结论: (f.toNonUnitalStarAlgHom : A -> B) = f
  证明: rfl
-/
theorem coe_toNonUnitalStarAlgHom (f : A ->⋆ₐ[R] B) : (f.toNonUnitalStarAlgHom : A -> B) = f :=
  rfl

end StarAlgHom

end Unital

/-! ### Operations on the product type

Note that this is copied from [`Algebra.Hom.NonUnitalAlg`](../Hom/NonUnitalAlg). -/


namespace NonUnitalStarAlgHom

section Prod

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B] [NonUnitalNonAssocSemiring C]
  [DistribMulAction R C] [Star C]

/-- The first projection of a product is a non-unital ⋆-algebra homomorphism. -/
@[simps!]
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : A × B ->⋆ₙₐ[R] A
  body: { NonUnitalAlgHom.fst R A B with map_star' := fun _ => rfl }

中文:
定义 fst
  签名: : A × B ->⋆ₙₐ[R] A
  定义体: { NonUnitalAlgHom.fst R A B with map_star' := fun _ => rfl }

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.fst, map_star
-/
def fst : A × B ->⋆ₙₐ[R] A :=
  { NonUnitalAlgHom.fst R A B with map_star' := fun _ => rfl }

/-- The second projection of a product is a non-unital ⋆-algebra homomorphism. -/
@[simps!]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : A × B ->⋆ₙₐ[R] B
  body: { NonUnitalAlgHom.snd R A B with map_star' := fun _ => rfl }

中文:
定义 snd
  签名: : A × B ->⋆ₙₐ[R] B
  定义体: { NonUnitalAlgHom.snd R A B with map_star' := fun _ => rfl }

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.snd, map_star
-/
def snd : A × B ->⋆ₙₐ[R] B :=
  { NonUnitalAlgHom.snd R A B with map_star' := fun _ => rfl }

variable {R A B C}

/-- The `Function.prod` of two morphisms is a morphism. -/
@[simps!]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C)
  body: { f.toNonUnitalAlgHom.prod g.toNonUnitalAlgHom with
    map_star' := fun x => by simp [map_star, Prod.ext_iff] }

中文:
定义 prod
  签名: (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C)
  定义体: { f.toNonUnitalAlgHom.prod g.toNonUnitalAlgHom with
    map_star' := fun x => by simp [map_star, Prod.ext_iff] }

Depends on / 依赖: Prod.ext_iff, ext_iff, f.toNonUnitalAlgHom.prod, g.toNonUnitalAlgHom, map_star, toNonUnitalAlgHom
-/
def prod (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C) : A ->⋆ₙₐ[R] B × C :=
  { f.toNonUnitalAlgHom.prod g.toNonUnitalAlgHom with
    map_star' := fun x => by simp [map_star, Prod.ext_iff] }

/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C)
  statement: ⇑(f.prod g) = Function.prod f g
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C)
  结论: ⇑(f.prod g) = Function.prod f g
  证明: rfl

@[simp]
-/
theorem coe_prod (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/--
theorem `fst_prod` / 定理 `fst_prod`

English:
theorem fst_prod
  given: (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C)
  statement: (fst R B C).comp (prod f g) = f
  proof: by
  ext; rfl

@[simp]

中文:
定理 fst_prod
  条件: (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C)
  结论: (fst R B C).comp (prod f g) = f
  证明: by
  ext; rfl

@[simp]
-/
theorem fst_prod (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  ext; rfl

@[simp]
/--
theorem `snd_prod` / 定理 `snd_prod`

English:
theorem snd_prod
  given: (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C)
  statement: (snd R B C).comp (prod f g) = g
  proof: by
  ext; rfl

@[simp]

中文:
定理 snd_prod
  条件: (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C)
  结论: (snd R B C).comp (prod f g) = g
  证明: by
  ext; rfl

@[simp]
-/
theorem snd_prod (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  ext; rfl

@[simp]
/--
theorem `prod_fst_snd` / 定理 `prod_fst_snd`

English:
theorem prod_fst_snd
  statement: prod (fst R A B) (snd R A B) = 1
  proof: DFunLike.coe_injective Function.prod_fst_snd

中文:
定理 prod_fst_snd
  结论: prod (fst R A B) (snd R A B) = 1
  证明: DFunLike.coe_injective Function.prod_fst_snd

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Function, Function.prod_fst_snd, coe_injective, prod_fst_snd
-/
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  DFunLike.coe_injective Function.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: : (A ->⋆ₙₐ[R] B) × (A ->⋆ₙₐ[R] C) ≃ (A ->⋆ₙₐ[R] B × C) where
  body: f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

中文:
定义 prodEquiv
  签名: : (A ->⋆ₙₐ[R] B) × (A ->⋆ₙₐ[R] C) ≃ (A ->⋆ₙₐ[R] B × C) where
  定义体: f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
-/
def prodEquiv : (A ->⋆ₙₐ[R] B) × (A ->⋆ₙₐ[R] C) ≃ (A ->⋆ₙₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

end Prod

section Pi

variable {ι : Type*}

/-- `Function.eval` as a `NonUnitalStarAlgHom`. -/
@[simps]
/--
Definition of `_root_.Pi.evalNonUnitalStarAlgHom` / `_root_.Pi.evalNonUnitalStarAlgHom` 的定义

English:
definition _root_.Pi.evalNonUnitalStarAlgHom
  signature: (R : Type*) (A : ι -> Type*) (j : ι) [Monoid R]
  body: { Pi.evalMulHom A j, Pi.evalAddHom A j with
    map_smul' _ _ := rfl
    map_zero' := rfl
    map_star' _ := rfl }

中文:
定义 _root_.Pi.evalNonUnitalStarAlgHom
  签名: (R : 类型) (A : ι -> 类型) (j : ι) [Monoid R]
  定义体: { Pi.evalMulHom A j, Pi.evalAddHom A j with
    map_smul' _ _ := rfl
    map_zero' := rfl
    map_star' _ := rfl }

Depends on / 依赖: Pi.evalAddHom, Pi.evalMulHom, evalAddHom, evalMulHom, map_smul, map_star, map_zero
-/
def _root_.Pi.evalNonUnitalStarAlgHom (R : Type*) (A : ι -> Type*) (j : ι) [Monoid R]
    [forall i, NonUnitalNonAssocSemiring (A i)] [forall i, DistribMulAction R (A i)] [forall i, Star (A i)] :
    (forall i, A i) ->⋆ₙₐ[R] A j :=
  { Pi.evalMulHom A j, Pi.evalAddHom A j with
    map_smul' _ _ := rfl
    map_zero' := rfl
    map_star' _ := rfl }

/-- `Function.eval` as a `StarAlgHom`. -/
@[simps]
/--
Definition of `_root_.Pi.evalStarAlgHom` / `_root_.Pi.evalStarAlgHom` 的定义

English:
definition _root_.Pi.evalStarAlgHom
  signature: (R : Type*) (A : ι -> Type*) (j : ι) [CommSemiring R]
  body: { Pi.evalNonUnitalStarAlgHom R A j, Pi.evalRingHom A j with
    commutes' _ := rfl }

中文:
定义 _root_.Pi.evalStarAlgHom
  签名: (R : 类型) (A : ι -> 类型) (j : ι) [CommSemiring R]
  定义体: { Pi.evalNonUnitalStarAlgHom R A j, Pi.evalRingHom A j with
    commutes' _ := rfl }

Depends on / 依赖: Pi.evalNonUnitalStarAlgHom, Pi.evalRingHom, commutes, evalNonUnitalStarAlgHom, evalRingHom
-/
def _root_.Pi.evalStarAlgHom (R : Type*) (A : ι -> Type*) (j : ι) [CommSemiring R]
    [forall i, Semiring (A i)] [forall i, Algebra R (A i)] [forall i, Star (A i)] :
    (forall i, A i) ->⋆ₐ[R] A j :=
  { Pi.evalNonUnitalStarAlgHom R A j, Pi.evalRingHom A j with
    commutes' _ := rfl }

end Pi

section InlInr

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
  [StarAddMonoid A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]
  [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [StarAddMonoid C]

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : A ->⋆ₙₐ[R] A × B
  body: prod 1 0

中文:
定义 inl
  签名: : A ->⋆ₙₐ[R] A × B
  定义体: prod 1 0
-/
def inl : A ->⋆ₙₐ[R] A × B :=
  prod 1 0

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : B ->⋆ₙₐ[R] A × B
  body: prod 0 1

中文:
定义 inr
  签名: : B ->⋆ₙₐ[R] A × B
  定义体: prod 0 1

Depends on / 依赖: MorphismProperty, MorphismProperty.of_isPullback, isPullback_morphismRestrict, of_isPullback
-/
def inr : B ->⋆ₙₐ[R] A × B :=
  prod 0 1

variable {R A B}

@[simp]
/--
theorem `coe_inl` / 定理 `coe_inl`

English:
theorem coe_inl
  statement: (inl R A B : A -> A × B) = fun x => (x, 0)
  proof: rfl

中文:
定理 coe_inl
  结论: (inl R A B : A -> A × B) = fun x => (x, 0)
  证明: rfl

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
theorem coe_inl : (inl R A B : A -> A × B) = fun x => (x, 0) :=
  rfl

/--
theorem `inl_apply` / 定理 `inl_apply`

English:
theorem inl_apply
  given: (x : A)
  statement: inl R A B x = (x, 0)
  proof: rfl

@[simp]

中文:
定理 inl_apply
  条件: (x : A)
  结论: inl R A B x = (x, 0)
  证明: rfl

@[simp]

Depends on / 依赖: GeometricallyConnected, GeometricallyConnected.geometrically_connectedSpace, geometrically_connectedSpace, of_hasPullback
-/
theorem inl_apply (x : A) : inl R A B x = (x, 0) :=
  rfl

@[simp]
/--
theorem `coe_inr` / 定理 `coe_inr`

English:
theorem coe_inr
  statement: (inr R A B : B -> A × B) = Prod.mk 0
  proof: rfl

中文:
定理 coe_inr
  结论: (inr R A B : B -> A × B) = Prod.mk 0
  证明: rfl

Depends on / 依赖: GeometricallyConnected, Surjective
-/
theorem coe_inr : (inr R A B : B -> A × B) = Prod.mk 0 :=
  rfl

/--
theorem `inr_apply` / 定理 `inr_apply`

English:
theorem inr_apply
  given: (x : B)
  statement: inr R A B x = (0, x)
  proof: rfl

中文:
定理 inr_apply
  条件: (x : B)
  结论: inr R A B x = (0, x)
  证明: rfl
-/
theorem inr_apply (x : B) : inr R A B x = (0, x) :=
  rfl

end InlInr

end NonUnitalStarAlgHom

namespace StarAlgHom

variable (R A B C : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C]

/-- The first projection of a product is a ⋆-algebra homomorphism. -/
@[simps!]
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : A × B ->⋆ₐ[R] A
  body: { AlgHom.fst R A B with map_star' := fun _ => rfl }

中文:
定义 fst
  签名: : A × B ->⋆ₐ[R] A
  定义体: { AlgHom.fst R A B with map_star' := fun _ => rfl }

Depends on / 依赖: AlgHom, AlgHom.fst, map_star
-/
def fst : A × B ->⋆ₐ[R] A :=
  { AlgHom.fst R A B with map_star' := fun _ => rfl }

/-- The second projection of a product is a ⋆-algebra homomorphism. -/
@[simps!]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : A × B ->⋆ₐ[R] B
  body: { AlgHom.snd R A B with map_star' := fun _ => rfl }

中文:
定义 snd
  签名: : A × B ->⋆ₐ[R] B
  定义体: { AlgHom.snd R A B with map_star' := fun _ => rfl }

Depends on / 依赖: AlgHom, AlgHom.snd, map_star
-/
def snd : A × B ->⋆ₐ[R] B :=
  { AlgHom.snd R A B with map_star' := fun _ => rfl }

variable {R A B C}

/-- The `Function.prod` of two morphisms is a morphism. -/
@[simps!]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C)
  body: { f.toAlgHom.prod g.toAlgHom with map_star' := fun x => by simp [Prod.star_def, map_star] }

中文:
定义 prod
  签名: (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C)
  定义体: { f.toAlgHom.prod g.toAlgHom with map_star' := fun x => by simp [Prod.star_def, map_star] }

Depends on / 依赖: Prod.star_def, f.toAlgHom.prod, g.toAlgHom, map_star, star_def, toAlgHom
-/
def prod (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C) : A ->⋆ₐ[R] B × C :=
  { f.toAlgHom.prod g.toAlgHom with map_star' := fun x => by simp [Prod.star_def, map_star] }

/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C)
  statement: ⇑(f.prod g) = Function.prod f g
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C)
  结论: ⇑(f.prod g) = Function.prod f g
  证明: rfl

@[simp]
-/
theorem coe_prod (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/--
theorem `fst_prod` / 定理 `fst_prod`

English:
theorem fst_prod
  given: (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C)
  statement: (fst R B C).comp (prod f g) = f
  proof: by
  ext; rfl

@[simp]

中文:
定理 fst_prod
  条件: (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C)
  结论: (fst R B C).comp (prod f g) = f
  证明: by
  ext; rfl

@[simp]
-/
theorem fst_prod (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  ext; rfl

@[simp]
/--
theorem `snd_prod` / 定理 `snd_prod`

English:
theorem snd_prod
  given: (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C)
  statement: (snd R B C).comp (prod f g) = g
  proof: by
  ext; rfl

@[simp]

中文:
定理 snd_prod
  条件: (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C)
  结论: (snd R B C).comp (prod f g) = g
  证明: by
  ext; rfl

@[simp]
-/
theorem snd_prod (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  ext; rfl

@[simp]
/--
theorem `prod_fst_snd` / 定理 `prod_fst_snd`

English:
theorem prod_fst_snd
  statement: prod (fst R A B) (snd R A B) = 1
  proof: DFunLike.coe_injective Function.prod_fst_snd

中文:
定理 prod_fst_snd
  结论: prod (fst R A B) (snd R A B) = 1
  证明: DFunLike.coe_injective Function.prod_fst_snd

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Function, Function.prod_fst_snd, coe_injective, prod_fst_snd
-/
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  DFunLike.coe_injective Function.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: : (A ->⋆ₐ[R] B) × (A ->⋆ₐ[R] C) ≃ (A ->⋆ₐ[R] B × C) where
  body: f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

中文:
定义 prodEquiv
  签名: : (A ->⋆ₐ[R] B) × (A ->⋆ₐ[R] C) ≃ (A ->⋆ₐ[R] B × C) where
  定义体: f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
-/
def prodEquiv : (A ->⋆ₐ[R] B) × (A ->⋆ₐ[R] C) ≃ (A ->⋆ₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

end StarAlgHom

/-! ### Star algebra equivalences -/

/--
Definition of `StarAlgEquiv` / `StarAlgEquiv` 的定义

English:
structure StarAlgEquiv
  parameters: (R A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B]
  extends: A ≃⋆+* B
  axioms and operations (1):
    - map_smul' : forall (r : R) (a : A), toFun (r • a) = r • toFun a

中文:
结构 StarAlgEquiv
  参数: (R A B : 类型) [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B]
  继承: A ≃⋆+* B
  公理与运算 (1 个):
    - map_smul' : 对任意 (r : R) (a : A), toFun (r • a) = r • toFun a
-/
structure StarAlgEquiv (R A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B]
  [Star A] [Star B] extends A ≃⋆+* B where
  /-- By definition, a ⋆-algebra equivalence commutes with the action of scalars. -/
  map_smul' : forall (r : R) (a : A), toFun (r • a) = r • toFun a

@[inherit_doc StarAlgEquiv] infixr:25 " ≃⋆ₐ " => StarAlgEquiv _

@[inherit_doc] notation:25 A " ≃⋆ₐ[" R "] " B => StarAlgEquiv R A B

/-- Reinterpret a star algebra equivalence as a `StarRingEquiv` by forgetting the interaction with
the scalar multiplication. -/
add_decl_doc StarAlgEquiv.toStarRingEquiv

/--
Definition of `NonUnitalAlgEquivClass` / `NonUnitalAlgEquivClass` 的定义

English:
class NonUnitalAlgEquivClass
  parameters: (F : Type*) (R A B : outParam Type*)
  extends: RingEquivClass F A B, MulActionSemiHomClass F (@id R) A B
  (no additional axioms)

中文:
类 NonUnitalAlgEquivClass
  参数: (F : 类型) (R A B : outParam 类型)
  继承: RingEquivClass F A B, MulActionSemiHomClass F (@id R) A B
  (无附加公理)
-/
class NonUnitalAlgEquivClass (F : Type*) (R A B : outParam Type*)
  [Add A] [Mul A] [SMul R A] [Add B] [Mul B] [SMul R B] [EquivLike F A B] : Prop
  extends RingEquivClass F A B, MulActionSemiHomClass F (@id R) A B where

-- See note [lower instance priority]
instance (priority := 100) {F R A B : Type*} [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [EquivLike F A B]
    [NonUnitalAlgEquivClass F R A B] :
    NonUnitalAlgHomClass F R A B :=
  { }

set_option backward.isDefEq.respectTransparency false in
-- See note [lower instance priority]
instance (priority := 100) (F R A B : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [Semiring B] [Algebra R B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] :
    AlgEquivClass F R A B :=
  { commutes := fun f r => by simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one] }

namespace StarAlgEquivClass

/-- Turn an element of a type `F` satisfying `AlgEquivClass F R A B` and `StarHomClass F A B` into
an actual `StarAlgEquiv`. This is declared as the default coercion from `F` to `A ≃⋆ₐ[R] B`. -/
@[coe]
/--
Definition of `toStarAlgEquiv` / `toStarAlgEquiv` 的定义

English:
definition toStarAlgEquiv
  signature: {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B] [SMul R B]
  body: { (RingEquivClass.toRingEquiv f : A ≃+* B) with
    map_star' := map_star f
    map_smul' := map_smul f }

中文:
定义 toStarAlgEquiv
  签名: {F R A B : 类型} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B] [SMul R B]
  定义体: { (RingEquivClass.toRingEquiv f : A ≃+* B) with
    map_star' := map_star f
    map_smul' := map_smul f }

Depends on / 依赖: GeometricallyIntegral, GeometricallyReduced, RingEquivClass, RingEquivClass.toRingEquiv, map_smul, map_star, toRingEquiv
-/
def toStarAlgEquiv {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B] [SMul R B]
    [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] [StarHomClass F A B]
    (f : F) : A ≃⋆ₐ[R] B :=
  { (RingEquivClass.toRingEquiv f : A ≃+* B) with
    map_star' := map_star f
    map_smul' := map_smul f }

/--
Instance `instCoeHead` / 实例 `instCoeHead`

English:
instance instCoeHead
  signature: {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B]
  body: ⟨toStarAlgEquiv⟩

中文:
实例 instCoeHead
  签名: {F R A B : 类型} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B]
  定义体: ⟨toStarAlgEquiv⟩

Depends on / 依赖: GeometricallyIntegral, GeometricallyIrreducible, toStarAlgEquiv
-/
instance instCoeHead {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B]
    [SMul R B] [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] [StarHomClass F A B] :
    CoeHead F (A ≃⋆ₐ[R] B) :=
  ⟨toStarAlgEquiv⟩

end StarAlgEquivClass

namespace StarAlgEquiv

section Basic

variable {F R A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B] [Star A]
  [Star B] [Add C] [Mul C] [SMul R C] [Star C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (A ≃⋆ₐ[R] B) A B
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩
    congr

中文:
实例 :
  签名: EquivLike (A ≃⋆ₐ[R] B) A B
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩
    congr

Depends on / 依赖: f.toFun
-/
instance : EquivLike (A ≃⋆ₐ[R] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalAlgEquivClass (A ≃⋆ₐ[R] B) R A B
  body: f.map_mul'
  map_add f := f.map_add'
  map_smulₛₗ := map_smul'

中文:
实例 :
  签名: NonUnitalAlgEquivClass (A ≃⋆ₐ[R] B) R A B
  定义体: f.map_mul'
  map_add f := f.map_add'
  map_smulₛₗ := map_smul'

Depends on / 依赖: f.map_mul, map_mul
-/
instance : NonUnitalAlgEquivClass (A ≃⋆ₐ[R] B) R A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_smulₛₗ := map_smul'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRingEquivClass (A ≃⋆ₐ[R] B) A B
  body: f.map_star'

中文:
实例 :
  签名: StarRingEquivClass (A ≃⋆ₐ[R] B) A B
  定义体: f.map_star'

Depends on / 依赖: f.map_star, map_star
-/
instance : StarRingEquivClass (A ≃⋆ₐ[R] B) A B where
  map_star f := f.map_star'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ≃⋆ₐ[R] B) A B
  body: f.toFun
  coe_injective := DFunLike.coe_injective

@[simp]

中文:
实例 :
  签名: FunLike (A ≃⋆ₐ[R] B) A B
  定义体: f.toFun
  coe_injective := DFunLike.coe_injective

@[simp]

Depends on / 依赖: f.toFun
-/
instance : FunLike (A ≃⋆ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective := DFunLike.coe_injective

@[simp]
/--
theorem `toStarRingEquiv_eq_coe` / 定理 `toStarRingEquiv_eq_coe`

English:
theorem toStarRingEquiv_eq_coe
  given: (e : A ≃⋆ₐ[R] B)
  statement: e.toStarRingEquiv = e
  proof: rfl

中文:
定理 toStarRingEquiv_eq_coe
  条件: (e : A ≃⋆ₐ[R] B)
  结论: e.toStarRingEquiv = e
  证明: rfl

Depends on / 依赖: MorphismProperty, MorphismProperty.of_isPullback, isPullback_morphismRestrict, of_isPullback
-/
theorem toStarRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toStarRingEquiv = e := rfl

/--
theorem `toRingEquiv_eq_coe` / 定理 `toRingEquiv_eq_coe`

English:
theorem toRingEquiv_eq_coe
  given: (e : A ≃⋆ₐ[R] B)
  statement: e.toRingEquiv = e
  proof: rfl

@[ext]

中文:
定理 toRingEquiv_eq_coe
  条件: (e : A ≃⋆ₐ[R] B)
  结论: e.toRingEquiv = e
  证明: rfl

@[ext]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
theorem toRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toRingEquiv = e :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ≃⋆ₐ[R] B} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : A ≃⋆ₐ[R] B} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext, GeometricallyIntegral, GeometricallyIntegral.geometrically_isIntegral, geometrically_isIntegral, of_hasPullback
-/
theorem ext {f g : A ≃⋆ₐ[R] B} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

variable (R A) in
/-- The identity map is a star algebra isomorphism. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : A ≃⋆ₐ[R] A
  body: { StarRingEquiv.refl (A := A) with
    map_smul' := fun _ _ => rfl }

中文:
定义 refl
  签名: : A ≃⋆ₐ[R] A
  定义体: { StarRingEquiv.refl (A := A) with
    map_smul' := fun _ _ => rfl }

Depends on / 依赖: GeometricallyIntegral, Surjective
-/
protected def refl : A ≃⋆ₐ[R] A :=
  { StarRingEquiv.refl (A := A) with
    map_smul' := fun _ _ => rfl }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (A ≃⋆ₐ[R] A)
  body: ⟨.refl R A⟩

@[simp]

中文:
实例 :
  签名: Inhabited (A ≃⋆ₐ[R] A)
  定义体: ⟨.refl R A⟩

@[simp]
-/
instance : Inhabited (A ≃⋆ₐ[R] A) :=
  ⟨.refl R A⟩

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ⇑(StarAlgEquiv.refl R A) = id
  proof: rfl

中文:
定理 coe_refl
  结论: ⇑(StarAlgEquiv.refl R A) = id
  证明: rfl
-/
theorem coe_refl : ⇑(StarAlgEquiv.refl R A) = id :=
  rfl

/-- The inverse of a star algebra isomorphism is a star algebra isomorphism. -/
@[symm]
nonrec def symm (e : A ≃⋆ₐ[R] B) : B ≃⋆ₐ[R] A :=
  { e.symm with
    map_smul' := fun r b => by
      simpa only [apply_inv_apply, inv_apply_apply] using!
        congr_arg (inv e) (map_smul e r (inv e b)).symm }

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : A ≃⋆ₐ[R] B)
  body: e.symm

initialize_simps_projections StarAlgEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]

中文:
定义 Simps.symm_apply
  签名: (e : A ≃⋆ₐ[R] B)
  定义体: e.symm

initialize_simps_projections StarAlgEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
-/
def Simps.symm_apply (e : A ≃⋆ₐ[R] B) : B -> A :=
  e.symm

initialize_simps_projections StarAlgEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
/--
theorem `invFun_eq_symm` / 定理 `invFun_eq_symm`

English:
theorem invFun_eq_symm
  given: {e : A ≃⋆ₐ[R] B}
  statement: EquivLike.inv e = e.symm
  proof: rfl

@[simp]

中文:
定理 invFun_eq_symm
  条件: {e : A ≃⋆ₐ[R] B}
  结论: EquivLike.inv e = e.symm
  证明: rfl

@[simp]
-/
theorem invFun_eq_symm {e : A ≃⋆ₐ[R] B} : EquivLike.inv e = e.symm :=
  rfl

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : A ≃⋆ₐ[R] B)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : A ≃⋆ₐ[R] B)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : A ≃⋆ₐ[R] B) : e.symm.symm = e := rfl

/--
lemma `symm_apply_eq` / 引理 `symm_apply_eq`

English:
lemma symm_apply_eq
  given: (e : A ≃⋆ₐ[R] B) {x y}
  proof: e.toEquiv.symm_apply_eq

中文:
引理 symm_apply_eq
  条件: (e : A ≃⋆ₐ[R] B) {x y}
  证明: e.toEquiv.symm_apply_eq

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
lemma symm_apply_eq (e : A ≃⋆ₐ[R] B) {x y} :
    e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

/--
lemma `eq_symm_apply` / 引理 `eq_symm_apply`

English:
lemma eq_symm_apply
  given: (e : A ≃⋆ₐ[R] B) {x y}
  proof: e.toEquiv.eq_symm_apply

中文:
引理 eq_symm_apply
  条件: (e : A ≃⋆ₐ[R] B) {x y}
  证明: e.toEquiv.eq_symm_apply

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
lemma eq_symm_apply (e : A ≃⋆ₐ[R] B) {x y} :
    y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : (A ≃⋆ₐ[R] B) -> B ≃⋆ₐ[R] A)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: Function.Bijective (symm : (A ≃⋆ₐ[R] B) -> B ≃⋆ₐ[R] A)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : (A ≃⋆ₐ[R] B) -> B ≃⋆ₐ[R] A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e h)
  statement: ⇑(⟨e, h⟩ : A ≃⋆ₐ[R] B) = e
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (e h)
  结论: ⇑(⟨e, h⟩ : A ≃⋆ₐ[R] B) = e
  证明: rfl

@[simp]
-/
theorem coe_mk (e h) : ⇑(⟨e, h⟩ : A ≃⋆ₐ[R] B) = e := rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (e : A ≃⋆ₐ[R] B) (e' h₁ h₂ h₃ h₄ h₅ h₆)
  proof: ext fun _ => rfl

@[simp]

中文:
定理 mk_coe
  条件: (e : A ≃⋆ₐ[R] B) (e' h₁ h₂ h₃ h₄ h₅ h₆)
  证明: ext fun _ => rfl

@[simp]

Depends on / 依赖: MorphismProperty, MorphismProperty.of_isPullback, isPullback_morphismRestrict, of_isPullback
-/
theorem mk_coe (e : A ≃⋆ₐ[R] B) (e' h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A ≃⋆ₐ[R] B) = e := ext fun _ => rfl

@[simp]
/--
theorem `symm_mk` / 定理 `symm_mk`

English:
theorem symm_mk
  given: (e : A ≃⋆+* B) (h₁)
  statement: dsimp%
  proof: rfl

@[simp]

中文:
定理 symm_mk
  条件: (e : A ≃⋆+* B) (h₁)
  结论: dsimp%
  证明: rfl

@[simp]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, e.symm, pullback_snd
-/
theorem symm_mk (e : A ≃⋆+* B) (h₁) : dsimp%
    (⟨e, h₁⟩ : A ≃⋆ₐ[R] B).symm =
      { (⟨e, h₁⟩ : A ≃⋆ₐ[R] B).symm with
        toStarRingEquiv := e.symm } :=
  rfl

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (StarAlgEquiv.refl R A).symm = .refl R A
  proof: rfl

@[simp]

中文:
定理 refl_symm
  结论: (StarAlgEquiv.refl R A).symm = .refl R A
  证明: rfl

@[simp]

Depends on / 依赖: GeometricallyIrreducible, GeometricallyIrreducible.geometrically_irreducibleSpace, geometrically_irreducibleSpace, of_hasPullback
-/
theorem refl_symm : (StarAlgEquiv.refl R A).symm = .refl R A :=
  rfl

@[simp]
/--
theorem `toStarRingEquiv_symm` / 定理 `toStarRingEquiv_symm`

English:
theorem toStarRingEquiv_symm
  given: (e : A ≃⋆ₐ[R] B)
  statement: (e.symm : B ≃⋆+* A) = (e : A ≃⋆+* B).symm
  proof: rfl

@[simp]

中文:
定理 toStarRingEquiv_symm
  条件: (e : A ≃⋆ₐ[R] B)
  结论: (e.symm : B ≃⋆+* A) = (e : A ≃⋆+* B).symm
  证明: rfl

@[simp]

Depends on / 依赖: GeometricallyIrreducible, Surjective
-/
theorem toStarRingEquiv_symm (e : A ≃⋆ₐ[R] B) : (e.symm : B ≃⋆+* A) = (e : A ≃⋆+* B).symm := rfl

@[simp]
/--
theorem `toRingEquiv_symm` / 定理 `toRingEquiv_symm`

English:
theorem toRingEquiv_symm
  given: (e : A ≃⋆ₐ[R] B)
  statement: (e : A ≃⋆+* B).symm = (e : A ≃+* B).symm
  proof: rfl

中文:
定理 toRingEquiv_symm
  条件: (e : A ≃⋆ₐ[R] B)
  结论: (e : A ≃⋆+* B).symm = (e : A ≃+* B).symm
  证明: rfl
-/
theorem toRingEquiv_symm (e : A ≃⋆ₐ[R] B) : (e : A ≃⋆+* B).symm = (e : A ≃+* B).symm := rfl

/-- Transitivity of `StarAlgEquiv`. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C)
  body: { e₁.toStarRingEquiv.trans e₂.toStarRingEquiv with
    map_smul' := fun r a =>
      show e₂.toFun (e₁.toFun (r • a)) = r • e₂.toFun (e₁.toFun a) by
        rw [e₁.map_smul']; rw [e₂.map_smul'] }

@[simp]

中文:
定义 trans
  签名: (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C)
  定义体: { e₁.toStarRingEquiv.trans e₂.toStarRingEquiv with
    map_smul' := fun r a =>
      show e₂.toFun (e₁.toFun (r • a)) = r • e₂.toFun (e₁.toFun a) by
        rw [e₁.map_smul']; rw [e₂.map_smul'] }

@[simp]

Depends on / 依赖: map_smul, toStarRingEquiv, toStarRingEquiv.trans
-/
def trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : A ≃⋆ₐ[R] C :=
  { e₁.toStarRingEquiv.trans e₂.toStarRingEquiv with
    map_smul' := fun r a =>
      show e₂.toFun (e₁.toFun (r • a)) = r • e₂.toFun (e₁.toFun a) by
        rw [e₁.map_smul']; rw [e₂.map_smul'] }

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : A ≃⋆ₐ[R] B)
  statement: forall x, e (e.symm x) = x
  proof: e.toStarRingEquiv.apply_symm_apply

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : A ≃⋆ₐ[R] B)
  结论: 对任意 x, e (e.symm x) = x
  证明: e.toStarRingEquiv.apply_symm_apply

@[simp]

Depends on / 依赖: apply_symm_apply, e.toStarRingEquiv.apply_symm_apply, toStarRingEquiv
-/
theorem apply_symm_apply (e : A ≃⋆ₐ[R] B) : forall x, e (e.symm x) = x :=
  e.toStarRingEquiv.apply_symm_apply

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : A ≃⋆ₐ[R] B)
  statement: forall x, e.symm (e x) = x
  proof: e.toStarRingEquiv.symm_apply_apply

@[simp]

中文:
定理 symm_apply_apply
  条件: (e : A ≃⋆ₐ[R] B)
  结论: 对任意 x, e.symm (e x) = x
  证明: e.toStarRingEquiv.symm_apply_apply

@[simp]

Depends on / 依赖: e.toStarRingEquiv.symm_apply_apply, symm_apply_apply, toStarRingEquiv
-/
theorem symm_apply_apply (e : A ≃⋆ₐ[R] B) : forall x, e.symm (e x) = x :=
  e.toStarRingEquiv.symm_apply_apply

@[simp]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : C)
  proof: rfl

@[simp]

中文:
定理 symm_trans_apply
  条件: (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : C)
  证明: rfl

@[simp]
-/
theorem symm_trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C)
  statement: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  proof: rfl

@[simp]

中文:
定理 coe_trans
  条件: (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C)
  结论: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  证明: rfl

@[simp]
-/
theorem coe_trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : A)
  statement: (e₁.trans e₂) x = e₂ (e₁ x)
  proof: rfl

中文:
定理 trans_apply
  条件: (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : A)
  结论: (e₁.trans e₂) x = e₂ (e₁ x)
  证明: rfl
-/
theorem trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

/--
theorem `leftInverse_symm` / 定理 `leftInverse_symm`

English:
theorem leftInverse_symm
  given: (e : A ≃⋆ₐ[R] B)
  statement: Function.LeftInverse e.symm e
  proof: e.left_inv

中文:
定理 leftInverse_symm
  条件: (e : A ≃⋆ₐ[R] B)
  结论: Function.LeftInverse e.symm e
  证明: e.left_inv

Depends on / 依赖: e.left_inv, left_inv
-/
theorem leftInverse_symm (e : A ≃⋆ₐ[R] B) : Function.LeftInverse e.symm e :=
  e.left_inv

/--
theorem `rightInverse_symm` / 定理 `rightInverse_symm`

English:
theorem rightInverse_symm
  given: (e : A ≃⋆ₐ[R] B)
  statement: Function.RightInverse e.symm e
  proof: e.right_inv

中文:
定理 rightInverse_symm
  条件: (e : A ≃⋆ₐ[R] B)
  结论: Function.RightInverse e.symm e
  证明: e.right_inv

Depends on / 依赖: GeometricallyIrreducible, GeometricallyIrreducible.iff_geometricallyIrreducible_fiber, Nonempty, Scheme, Scheme.Hom.fiberToSpecResidueField, Set.nonempty, e.right_inv, fiberHomeo, fiberToSpecResidueField, g.fiberToSpecResidueField, geometrically_iff_of_isClosedUnderIsomorphisms, geometrically_iff_of_isClosedUnderIsomorphisms.mpr, iff_geometricallyIrreducible_fiber, nonempty, nonempty_congr, pullback, pullback.map, right_inv
-/
theorem rightInverse_symm (e : A ≃⋆ₐ[R] B) : Function.RightInverse e.symm e :=
  e.right_inv

section AlgEquiv
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [Star A] [Star B]

/--
Definition of `toAlgEquiv` / `toAlgEquiv` 的定义

English:
definition toAlgEquiv
  signature: (f : A ≃⋆ₐ[R] B)
  body: f.toRingEquiv
  commutes' r := by simp_rw [Algebra.algebraMap_eq_smul_one', map_smul']; simp

@[simp]

中文:
定义 toAlgEquiv
  签名: (f : A ≃⋆ₐ[R] B)
  定义体: f.toRingEquiv
  commutes' r := by simp_rw [Algebra.algebraMap_eq_smul_one', map_smul']; simp

@[simp]

Depends on / 依赖: f.toRingEquiv, toRingEquiv
-/
def toAlgEquiv (f : A ≃⋆ₐ[R] B) : A ≃ₐ[R] B where
  toRingEquiv := f.toRingEquiv
  commutes' r := by simp_rw [Algebra.algebraMap_eq_smul_one', map_smul']; simp

@[simp]
/--
theorem `toAlgEquiv_symm` / 定理 `toAlgEquiv_symm`

English:
theorem toAlgEquiv_symm
  given: (f : A ≃⋆ₐ[R] B)
  statement: f.symm.toAlgEquiv = f.toAlgEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toAlgEquiv_symm
  条件: (f : A ≃⋆ₐ[R] B)
  结论: f.symm.toAlgEquiv = f.toAlgEquiv.symm
  证明: rfl

@[simp]
-/
theorem toAlgEquiv_symm (f : A ≃⋆ₐ[R] B) : f.symm.toAlgEquiv = f.toAlgEquiv.symm := rfl

@[simp]
/--
theorem `coe_toAlgEquiv` / 定理 `coe_toAlgEquiv`

English:
theorem coe_toAlgEquiv
  given: (f : A ≃⋆ₐ[R] B)
  statement: ⇑f.toAlgEquiv = ⇑f
  proof: rfl

@[simp]

中文:
定理 coe_toAlgEquiv
  条件: (f : A ≃⋆ₐ[R] B)
  结论: ⇑f.toAlgEquiv = ⇑f
  证明: rfl

@[simp]
-/
theorem coe_toAlgEquiv (f : A ≃⋆ₐ[R] B) : ⇑f.toAlgEquiv = ⇑f := rfl

@[simp]
/--
theorem `coe_symm_toAlgEquiv` / 定理 `coe_symm_toAlgEquiv`

English:
theorem coe_symm_toAlgEquiv
  given: (f : A ≃⋆ₐ[R] B)
  statement: ⇑f.toAlgEquiv.symm = ⇑f.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toAlgEquiv
  条件: (f : A ≃⋆ₐ[R] B)
  结论: ⇑f.toAlgEquiv.symm = ⇑f.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toAlgEquiv (f : A ≃⋆ₐ[R] B) : ⇑f.toAlgEquiv.symm = ⇑f.symm := rfl

@[simp]
/--
theorem `toAlgEquiv_trans` / 定理 `toAlgEquiv_trans`

English:
theorem toAlgEquiv_trans
  statement: {C : Type*} [Semiring C] [Algebra R C] [Star C] (f : A ≃⋆ₐ[R] B)
  proof: rfl

中文:
定理 toAlgEquiv_trans
  结论: {C : 类型} [Semiring C] [Algebra R C] [Star C] (f : A ≃⋆ₐ[R] B)
  证明: rfl

Depends on / 依赖: MorphismProperty, MorphismProperty.of_isPullback, isPullback_morphismRestrict, of_isPullback
-/
theorem toAlgEquiv_trans {C : Type*} [Semiring C] [Algebra R C] [Star C] (f : A ≃⋆ₐ[R] B)
    (g : B ≃⋆ₐ[R] C) : (f.trans g).toAlgEquiv = f.toAlgEquiv.trans g.toAlgEquiv := rfl

/--
theorem `toAlgEquiv_injective` / 定理 `toAlgEquiv_injective`

English:
theorem toAlgEquiv_injective
  statement: Function.Injective (toAlgEquiv (R := R) (A := A) (B := B))
  proof: fun _ _ h => ext AlgEquiv.congr_fun h

@[simp]

中文:
定理 toAlgEquiv_injective
  结论: Function.Injective (toAlgEquiv (R := R) (A := A) (B := B))
  证明: fun _ _ h => ext AlgEquiv.congr_fun h

@[simp]

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
theorem toAlgEquiv_injective : Function.Injective (toAlgEquiv (R := R) (A := A) (B := B)) :=
fun _ _ h => ext AlgEquiv.congr_fun h

@[simp]
/--
theorem `toAlgEquiv_refl` / 定理 `toAlgEquiv_refl`

English:
theorem toAlgEquiv_refl
  statement: (StarAlgEquiv.refl R A).toAlgEquiv = AlgEquiv.refl
  proof: rfl

中文:
定理 toAlgEquiv_refl
  结论: (StarAlgEquiv.refl R A).toAlgEquiv = AlgEquiv.refl
  证明: rfl

Depends on / 依赖: GeometricallyReduced, GeometricallyReduced.geometrically_isReduced, geometrically_isReduced, of_hasPullback
-/
theorem toAlgEquiv_refl : (StarAlgEquiv.refl R A).toAlgEquiv = AlgEquiv.refl := rfl

/--
Definition of `ofAlgEquiv` / `ofAlgEquiv` 的定义

English:
definition ofAlgEquiv
  signature: (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = star (f x))
  body: f.toRingEquiv
  map_smul' := f.toLinearEquiv.map_smul
  map_star' := map_star

@[simp]

中文:
定义 ofAlgEquiv
  签名: (f : A ≃ₐ[R] B) (map_star : 对任意 x, f (star x) = star (f x))
  定义体: f.toRingEquiv
  map_smul' := f.toLinearEquiv.map_smul
  map_star' := map_star

@[simp]

Depends on / 依赖: f.toRingEquiv, toRingEquiv
-/
def ofAlgEquiv (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = star (f x)) :
    A ≃⋆ₐ[R] B where
  toRingEquiv := f.toRingEquiv
  map_smul' := f.toLinearEquiv.map_smul
  map_star' := map_star

@[simp]
/--
theorem `ofAlgEquiv_apply` / 定理 `ofAlgEquiv_apply`

English:
theorem ofAlgEquiv_apply
  given: (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = star (f x)) (x : A)
  proof: rfl

@[simp]

中文:
定理 ofAlgEquiv_apply
  条件: (f : A ≃ₐ[R] B) (map_star : 对任意 x, f (star x) = star (f x)) (x : A)
  证明: rfl

@[simp]
-/
theorem ofAlgEquiv_apply (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = star (f x)) (x : A) :
    ofAlgEquiv f map_star x = f x := rfl

@[simp]
/--
theorem `ofAlgEquiv_symm` / 定理 `ofAlgEquiv_symm`

English:
theorem ofAlgEquiv_symm
  given: (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = star (f x))
  proof: rfl

@[simp]

中文:
定理 ofAlgEquiv_symm
  条件: (f : A ≃ₐ[R] B) (map_star : 对任意 x, f (star x) = star (f x))
  证明: rfl

@[simp]
-/
theorem ofAlgEquiv_symm (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = star (f x)) :
    (ofAlgEquiv f map_star).symm = ofAlgEquiv f.symm (ofAlgEquiv f map_star).symm.map_star' :=
  rfl

@[simp]
/--
theorem `toAlgEquiv_ofAlgEquiv` / 定理 `toAlgEquiv_ofAlgEquiv`

English:
theorem toAlgEquiv_ofAlgEquiv
  given: (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = star (f x))
  proof: rfl

@[simp]

中文:
定理 toAlgEquiv_ofAlgEquiv
  条件: (f : A ≃ₐ[R] B) (map_star : 对任意 x, f (star x) = star (f x))
  证明: rfl

@[simp]
-/
theorem toAlgEquiv_ofAlgEquiv (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = star (f x)) :
    (ofAlgEquiv f map_star).toAlgEquiv = f := rfl

@[simp]
/--
theorem `ofAlgEquiv_toAlgEquiv` / 定理 `ofAlgEquiv_toAlgEquiv`

English:
theorem ofAlgEquiv_toAlgEquiv
  given: (f : A ≃⋆ₐ[R] B) (map_star)
  proof: rfl

中文:
定理 ofAlgEquiv_toAlgEquiv
  条件: (f : A ≃⋆ₐ[R] B) (map_star)
  证明: rfl

Depends on / 依赖: G.hom, isClosedImmersion_of_comp_eq_id
-/
theorem ofAlgEquiv_toAlgEquiv (f : A ≃⋆ₐ[R] B) (map_star) :
    ofAlgEquiv f.toAlgEquiv map_star = f := rfl

end AlgEquiv

end Basic

section NonUnitalArrowCongr

variable {R A₁ A₂ A₃ A₁' A₂' A₃' : Type*} [Monoid R]
  [NonUnitalNonAssocSemiring A₁] [DistribMulAction R A₁] [Star A₁]
  [NonUnitalNonAssocSemiring A₂] [DistribMulAction R A₂] [Star A₂]
  [NonUnitalNonAssocSemiring A₃] [DistribMulAction R A₃] [Star A₃]
  [NonUnitalNonAssocSemiring A₁'] [DistribMulAction R A₁'] [Star A₁']
  [NonUnitalNonAssocSemiring A₂'] [DistribMulAction R A₂'] [Star A₂']
  [NonUnitalNonAssocSemiring A₃'] [DistribMulAction R A₃'] [Star A₃']
  (e : A₁ ≃⋆ₐ[R] A₂)

/-- Reintrepret a star algebra equivalence as a non-unital star algebra homomorphism. -/
@[simps]
/--
Definition of `toNonUnitalStarAlgHom` / `toNonUnitalStarAlgHom` 的定义

English:
definition toNonUnitalStarAlgHom
  signature: : A₁ ->⋆ₙₐ[R] A₂
  body: { e with
    toFun := e
    map_zero' := map_zero e }

@[simp]

中文:
定义 toNonUnitalStarAlgHom
  签名: : A₁ ->⋆ₙₐ[R] A₂
  定义体: { e with
    toFun := e
    map_zero' := map_zero e }

@[simp]

Depends on / 依赖: map_zero
-/
def toNonUnitalStarAlgHom : A₁ ->⋆ₙₐ[R] A₂ :=
  { e with
    toFun := e
    map_zero' := map_zero e }

@[simp]
/--
lemma `toNonUnitalStarAlgHom_refl` / 引理 `toNonUnitalStarAlgHom_refl`

English:
lemma toNonUnitalStarAlgHom_refl
  statement: (StarAlgEquiv.refl R A₁).toNonUnitalStarAlgHom = .id R A₁
  proof: rfl

@[simp]

中文:
引理 toNonUnitalStarAlgHom_refl
  结论: (StarAlgEquiv.refl R A₁).toNonUnitalStarAlgHom = .id R A₁
  证明: rfl

@[simp]
-/
lemma toNonUnitalStarAlgHom_refl : (StarAlgEquiv.refl R A₁).toNonUnitalStarAlgHom = .id R A₁ :=
  rfl

@[simp]
/--
lemma `toNonUnitalStarAlgHom_comp` / 引理 `toNonUnitalStarAlgHom_comp`

English:
lemma toNonUnitalStarAlgHom_comp
  given: (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃)
  proof: rfl

中文:
引理 toNonUnitalStarAlgHom_comp
  条件: (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃)
  证明: rfl
-/
lemma toNonUnitalStarAlgHom_comp (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃) :
    e₂.toNonUnitalStarAlgHom.comp e₁.toNonUnitalStarAlgHom =
      (e₁.trans e₂).toNonUnitalStarAlgHom := rfl

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'` as star algebras, then the type
of maps `A₁ →⋆ₙₐ[R] A₂` is equivalent to the type of maps `A₁' →⋆ₙₐ[R] A₂'`.

For unital star algebra homomorphisms, see `StarAlgEquiv.arrowCongr`. -/
@[simps apply]
/--
Definition of `arrowCongr'` / `arrowCongr'` 的定义

English:
definition arrowCongr'
  signature: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  body: (e₂.toNonUnitalStarAlgHom.comp f).comp e₁.symm.toNonUnitalStarAlgHom
  invFun f := (e₂.symm.toNonUnitalStarAlgHom.comp f).comp e₁.toNonUnitalStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

中文:
定义 arrowCongr'
  签名: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  定义体: (e₂.toNonUnitalStarAlgHom.comp f).comp e₁.symm.toNonUnitalStarAlgHom
  invFun f := (e₂.symm.toNonUnitalStarAlgHom.comp f).comp e₁.toNonUnitalStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

Depends on / 依赖: symm.toNonUnitalStarAlgHom, toNonUnitalStarAlgHom, toNonUnitalStarAlgHom.comp
-/
def arrowCongr' (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (A₁ ->⋆ₙₐ[R] A₂) ≃ (A₁' ->⋆ₙₐ[R] A₂') where
  toFun f := (e₂.toNonUnitalStarAlgHom.comp f).comp e₁.symm.toNonUnitalStarAlgHom
  invFun f := (e₂.symm.toNonUnitalStarAlgHom.comp f).comp e₁.toNonUnitalStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

/--
theorem `arrowCongr'_comp` / 定理 `arrowCongr'_comp`

English:
theorem arrowCongr'_comp
  statement: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  proof: by
  ext
  simp

@[simp]

中文:
定理 arrowCongr'_comp
  结论: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  证明: by
  ext
  simp

@[simp]
-/
theorem arrowCongr'_comp (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
    (e₃ : A₃ ≃⋆ₐ[R] A₃') (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₃) :
    arrowCongr' e₁ e₃ (g.comp f) = (arrowCongr' e₂ e₃ g).comp (arrowCongr' e₁ e₂ f) := by
  ext
  simp

@[simp]
/--
theorem `arrowCongr'_refl` / 定理 `arrowCongr'_refl`

English:
theorem arrowCongr'_refl
  statement: arrowCongr' (.refl _ _) (.refl _ _) = Equiv.refl (A₁ ->⋆ₙₐ[R] A₂)
  proof: rfl

@[simp]

中文:
定理 arrowCongr'_refl
  结论: arrowCongr' (.refl _ _) (.refl _ _) = Equiv.refl (A₁ ->⋆ₙₐ[R] A₂)
  证明: rfl

@[simp]
-/
theorem arrowCongr'_refl : arrowCongr' (.refl _ _) (.refl _ _) = Equiv.refl (A₁ ->⋆ₙₐ[R] A₂) :=
  rfl

@[simp]
/--
theorem `arrowCongr'_trans` / 定理 `arrowCongr'_trans`

English:
theorem arrowCongr'_trans
  statement: (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
  proof: rfl

@[simp]

中文:
定理 arrowCongr'_trans
  结论: (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
  证明: rfl

@[simp]
-/
theorem arrowCongr'_trans (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
    (e₂ : A₂ ≃⋆ₐ[R] A₃) (e₂' : A₂' ≃⋆ₐ[R] A₃') :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl

@[simp]
/--
theorem `symm_arrowCongr'` / 定理 `symm_arrowCongr'`

English:
theorem symm_arrowCongr'
  given: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  proof: rfl

中文:
定理 symm_arrowCongr'
  条件: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  证明: rfl
-/
theorem symm_arrowCongr' (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm :=
  rfl

/-- Construct a star algebra equivalence from a pair of non-unital star algebra homomorphisms. -/
@[simps]
/--
Definition of `ofNonUnitalStarAlgHom` / `ofNonUnitalStarAlgHom` 的定义

English:
definition ofNonUnitalStarAlgHom
  signature: (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁) (h₁ : g.comp f = .id R A₁)
  body: { f with
    toFun := f
    invFun := g
    left_inv x := congr($h₁ x)
    right_inv x := congr($h₂ x) }

@[simp]

中文:
定义 ofNonUnitalStarAlgHom
  签名: (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁) (h₁ : g.comp f = .id R A₁)
  定义体: { f with
    toFun := f
    invFun := g
    left_inv x := congr($h₁ x)
    right_inv x := congr($h₂ x) }

@[simp]

Depends on / 依赖: invFun, left_inv, right_inv
-/
def ofNonUnitalStarAlgHom (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁) (h₁ : g.comp f = .id R A₁)
    (h₂ : f.comp g = .id R A₂) : A₁ ≃⋆ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := g
    left_inv x := congr($h₁ x)
    right_inv x := congr($h₂ x) }

@[simp]
/--
lemma `toNonUnitalStarAlgHom_ofNonUnitalStarAlgHom` / 引理 `toNonUnitalStarAlgHom_ofNonUnitalStarAlgHom`

English:
lemma toNonUnitalStarAlgHom_ofNonUnitalStarAlgHom
  statement: (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁)
  proof: rfl

中文:
引理 toNonUnitalStarAlgHom_ofNonUnitalStarAlgHom
  结论: (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁)
  证明: rfl
-/
lemma toNonUnitalStarAlgHom_ofNonUnitalStarAlgHom (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁)
    (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) :
    (ofNonUnitalStarAlgHom f g h₁ h₂).toNonUnitalStarAlgHom = f :=
  rfl

/--
lemma `symm_ofNonUnitalStarAlgHom` / 引理 `symm_ofNonUnitalStarAlgHom`

English:
lemma symm_ofNonUnitalStarAlgHom
  statement: (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁)
  proof: rfl

@[simp]

中文:
引理 symm_ofNonUnitalStarAlgHom
  结论: (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁)
  证明: rfl

@[simp]
-/
lemma symm_ofNonUnitalStarAlgHom (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁)
    (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) :
    (ofNonUnitalStarAlgHom f g h₁ h₂).symm = ofNonUnitalStarAlgHom g f h₂ h₁ :=
  rfl

@[simp]
/--
lemma `toNonUnitalStarAlgHom_symm_ofNonUnitalStarAlgHom` / 引理 `toNonUnitalStarAlgHom_symm_ofNonUnitalStarAlgHom`

English:
lemma toNonUnitalStarAlgHom_symm_ofNonUnitalStarAlgHom
  statement: (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁)
  proof: rfl

中文:
引理 toNonUnitalStarAlgHom_symm_ofNonUnitalStarAlgHom
  结论: (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁)
  证明: rfl
-/
lemma toNonUnitalStarAlgHom_symm_ofNonUnitalStarAlgHom (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁)
    (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) :
    (ofNonUnitalStarAlgHom f g h₁ h₂).symm.toNonUnitalStarAlgHom = g :=
  rfl

end NonUnitalArrowCongr

section Unital

variable {R A₁ A₂ A₃ A₁' A₂' A₃' : Type*}
  [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]
  [Semiring A₁'] [Semiring A₂'] [Semiring A₃']
  [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]
  [Algebra R A₁'] [Algebra R A₂'] [Algebra R A₃']
  [Star A₁] [Star A₂] [Star A₃]
  [Star A₁'] [Star A₂'] [Star A₃']
  (e : A₁ ≃⋆ₐ[R] A₂)

/-- Reintrepret a star algebra equivalence as a star algebra homomorphism. -/
@[simps]
/--
Definition of `toStarAlgHom` / `toStarAlgHom` 的定义

English:
definition toStarAlgHom
  signature: : A₁ ->⋆ₐ[R] A₂
  body: { e with
    toFun := e
    __ := e.toAlgEquiv.toAlgHom }

@[simp]

中文:
定义 toStarAlgHom
  签名: : A₁ ->⋆ₐ[R] A₂
  定义体: { e with
    toFun := e
    __ := e.toAlgEquiv.toAlgHom }

@[simp]

Depends on / 依赖: e.toAlgEquiv.toAlgHom, toAlgEquiv, toAlgHom
-/
def toStarAlgHom : A₁ ->⋆ₐ[R] A₂ :=
  { e with
    toFun := e
    __ := e.toAlgEquiv.toAlgHom }

@[simp]
/--
lemma `toNonUnitalStarAlgHom_toStarAlgHom` / 引理 `toNonUnitalStarAlgHom_toStarAlgHom`

English:
lemma toNonUnitalStarAlgHom_toStarAlgHom
  given: (e : A₁ ≃⋆ₐ[R] A₂)
  proof: rfl

@[simp]

中文:
引理 toNonUnitalStarAlgHom_toStarAlgHom
  条件: (e : A₁ ≃⋆ₐ[R] A₂)
  证明: rfl

@[simp]
-/
lemma toNonUnitalStarAlgHom_toStarAlgHom (e : A₁ ≃⋆ₐ[R] A₂) :
    e.toStarAlgHom.toNonUnitalStarAlgHom = e.toNonUnitalStarAlgHom :=
  rfl

@[simp]
/--
lemma `toStarAlgHom_refl` / 引理 `toStarAlgHom_refl`

English:
lemma toStarAlgHom_refl
  statement: (StarAlgEquiv.refl R A₁).toStarAlgHom = .id R A₁
  proof: rfl

@[simp]

中文:
引理 toStarAlgHom_refl
  结论: (StarAlgEquiv.refl R A₁).toStarAlgHom = .id R A₁
  证明: rfl

@[simp]
-/
lemma toStarAlgHom_refl : (StarAlgEquiv.refl R A₁).toStarAlgHom = .id R A₁ :=
  rfl

@[simp]
/--
lemma `toStarAlgHom_comp` / 引理 `toStarAlgHom_comp`

English:
lemma toStarAlgHom_comp
  given: (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃)
  proof: rfl

中文:
引理 toStarAlgHom_comp
  条件: (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃)
  证明: rfl
-/
lemma toStarAlgHom_comp (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃) :
    e₂.toStarAlgHom.comp e₁.toStarAlgHom = (e₁.trans e₂).toStarAlgHom := rfl

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'` as star algebras, then the type
of maps `A₁ →⋆ₐ[R] A₂` is equivalent to the type of maps `A₁' →⋆ₐ[R] A₂'`.

For non-unital star algebra homomorphisms, see `StarAlgEquiv.arrowCongr'`. -/
@[simps apply]
/--
Definition of `arrowCongr` / `arrowCongr` 的定义

English:
definition arrowCongr
  signature: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  body: (e₂.toStarAlgHom.comp f).comp e₁.symm.toStarAlgHom
  invFun f := (e₂.symm.toStarAlgHom.comp f).comp e₁.toStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

中文:
定义 arrowCongr
  签名: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  定义体: (e₂.toStarAlgHom.comp f).comp e₁.symm.toStarAlgHom
  invFun f := (e₂.symm.toStarAlgHom.comp f).comp e₁.toStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

Depends on / 依赖: symm.toStarAlgHom, toStarAlgHom, toStarAlgHom.comp
-/
def arrowCongr (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') : (A₁ ->⋆ₐ[R] A₂) ≃ (A₁' ->⋆ₐ[R] A₂') where
  toFun f := (e₂.toStarAlgHom.comp f).comp e₁.symm.toStarAlgHom
  invFun f := (e₂.symm.toStarAlgHom.comp f).comp e₁.toStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

/--
theorem `arrowCongr_comp` / 定理 `arrowCongr_comp`

English:
theorem arrowCongr_comp
  statement: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  proof: by
  ext
  simp

@[simp]

中文:
定理 arrowCongr_comp
  结论: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  证明: by
  ext
  simp

@[simp]
-/
theorem arrowCongr_comp (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
    (e₃ : A₃ ≃⋆ₐ[R] A₃') (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp

@[simp]
/--
theorem `arrowCongr_refl` / 定理 `arrowCongr_refl`

English:
theorem arrowCongr_refl
  statement: arrowCongr (.refl _ _) (.refl _ _) = Equiv.refl (A₁ ->⋆ₐ[R] A₂)
  proof: rfl

@[simp]

中文:
定理 arrowCongr_refl
  结论: arrowCongr (.refl _ _) (.refl _ _) = Equiv.refl (A₁ ->⋆ₐ[R] A₂)
  证明: rfl

@[simp]
-/
theorem arrowCongr_refl : arrowCongr (.refl _ _) (.refl _ _) = Equiv.refl (A₁ ->⋆ₐ[R] A₂) :=
  rfl

@[simp]
/--
theorem `arrowCongr_trans` / 定理 `arrowCongr_trans`

English:
theorem arrowCongr_trans
  statement: (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
  proof: rfl

@[simp]

中文:
定理 arrowCongr_trans
  结论: (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
  证明: rfl

@[simp]
-/
theorem arrowCongr_trans (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
    (e₂ : A₂ ≃⋆ₐ[R] A₃) (e₂' : A₂' ≃⋆ₐ[R] A₃') :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl

@[simp]
/--
theorem `symm_arrowCongr` / 定理 `symm_arrowCongr`

English:
theorem symm_arrowCongr
  given: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  proof: rfl

中文:
定理 symm_arrowCongr
  条件: (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
  证明: rfl
-/
theorem symm_arrowCongr (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl

/-- Construct a star algebra equivalence from a pair of star algebra homomorphisms. -/
@[simps]
/--
Definition of `ofStarAlgHom` / `ofStarAlgHom` 的定义

English:
definition ofStarAlgHom
  signature: {R A B : Type*} [CommSemiring R]
  body: { f with
    toFun := f
    invFun := g
    left_inv x := congr($h₁ x)
    right_inv x := congr($h₂ x)
    map_smul' := map_smul f }

@[simp]

中文:
定义 ofStarAlgHom
  签名: {R A B : 类型} [CommSemiring R]
  定义体: { f with
    toFun := f
    invFun := g
    left_inv x := congr($h₁ x)
    right_inv x := congr($h₂ x)
    map_smul' := map_smul f }

@[simp]

Depends on / 依赖: invFun, left_inv, map_smul, right_inv
-/
def ofStarAlgHom {R A B : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    (f : A ->⋆ₐ[R] B) (g : B ->⋆ₐ[R] A) (h₁ : g.comp f = .id R A) (h₂ : f.comp g = .id R B) :
    A ≃⋆ₐ[R] B :=
  { f with
    toFun := f
    invFun := g
    left_inv x := congr($h₁ x)
    right_inv x := congr($h₂ x)
    map_smul' := map_smul f }

@[simp]
/--
lemma `toStarAlgHom_ofStarAlgHom` / 引理 `toStarAlgHom_ofStarAlgHom`

English:
lemma toStarAlgHom_ofStarAlgHom
  statement: (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁)
  proof: rfl

中文:
引理 toStarAlgHom_ofStarAlgHom
  结论: (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁)
  证明: rfl
-/
lemma toStarAlgHom_ofStarAlgHom (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁)
    (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) :
    (ofStarAlgHom f g h₁ h₂).toStarAlgHom = f :=
  rfl

/--
lemma `symm_ofStarAlgHom` / 引理 `symm_ofStarAlgHom`

English:
lemma symm_ofStarAlgHom
  statement: (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁)
  proof: rfl

@[simp]

中文:
引理 symm_ofStarAlgHom
  结论: (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁)
  证明: rfl

@[simp]
-/
lemma symm_ofStarAlgHom (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁)
    (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) :
    (ofStarAlgHom f g h₁ h₂).symm = ofStarAlgHom g f h₂ h₁ :=
  rfl

@[simp]
/--
lemma `toStarAlgHom_symm_ofStarAlgHom` / 引理 `toStarAlgHom_symm_ofStarAlgHom`

English:
lemma toStarAlgHom_symm_ofStarAlgHom
  statement: (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁)
  proof: rfl

中文:
引理 toStarAlgHom_symm_ofStarAlgHom
  结论: (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁)
  证明: rfl
-/
lemma toStarAlgHom_symm_ofStarAlgHom (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁)
    (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) :
    (ofStarAlgHom f g h₁ h₂).symm.toStarAlgHom = g :=
  rfl

end Unital

section Bijective

variable {F G R A B : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]
variable [FunLike G B A] [NonUnitalAlgHomClass G R B A] [StarHomClass G B A]

/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: (f : F) (hf : Function.Bijective f)
  body: {
    RingEquiv.ofBijective f
      (hf : Function.Bijective (f : A -> B)) with
    toFun := f
    map_star' := map_star f
    map_smul' := map_smul f }

@[simp]

中文:
定义 ofBijective
  签名: (f : F) (hf : Function.Bijective f)
  定义体: {
    RingEquiv.ofBijective f
      (hf : Function.Bijective (f : A -> B)) with
    toFun := f
    map_star' := map_star f
    map_smul' := map_smul f }

@[simp]

Depends on / 依赖: Bijective, Function, Function.Bijective, RingEquiv, RingEquiv.ofBijective, map_smul, map_star, ofBijective
-/
noncomputable def ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆ₐ[R] B :=
  {
    RingEquiv.ofBijective f
      (hf : Function.Bijective (f : A -> B)) with
    toFun := f
    map_star' := map_star f
    map_smul' := map_smul f }

@[simp]
/--
theorem `coe_ofBijective` / 定理 `coe_ofBijective`

English:
theorem coe_ofBijective
  given: {f : F} (hf : Function.Bijective f)
  proof: rfl

中文:
定理 coe_ofBijective
  条件: {f : F} (hf : Function.Bijective f)
  证明: rfl
-/
theorem coe_ofBijective {f : F} (hf : Function.Bijective f) :
    (StarAlgEquiv.ofBijective f hf : A -> B) = f :=
  rfl

/--
theorem `ofBijective_apply` / 定理 `ofBijective_apply`

English:
theorem ofBijective_apply
  given: {f : F} (hf : Function.Bijective f) (a : A)
  proof: rfl

中文:
定理 ofBijective_apply
  条件: {f : F} (hf : Function.Bijective f) (a : A)
  证明: rfl

Depends on / 依赖: CommRingCat, CommRingCat.ofHom_comp, Spec.map_comp, map_comp, ofHom_comp, specOverSpec_over
-/
theorem ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) :
    (StarAlgEquiv.ofBijective f hf) a = f a :=
  rfl

end Bijective

section Group
variable {S R : Type*} [Mul R] [Add R] [Star R] [SMul S R]

@[simps -isSimp one mul]
/--
Instance `aut` / 实例 `aut`

English:
instance aut
  signature: : Group (R ≃⋆ₐ[S] R) where
  body: .refl _ _
  mul a b := b.trans a
  one_mul _ := rfl
  mul_one _ := rfl
  mul_assoc _ _ _ := rfl
  inv f := f.symm
inv_mul_cancel f := ext symm_apply_apply f

中文:
实例 aut
  签名: : Group (R ≃⋆ₐ[S] R) where
  定义体: .refl _ _
  mul a b := b.trans a
  one_mul _ := rfl
  mul_one _ := rfl
  mul_assoc _ _ _ := rfl
  inv f := f.symm
inv_mul_cancel f := ext symm_apply_apply f
-/
instance aut : Group (R ≃⋆ₐ[S] R) where
  one := .refl _ _
  mul a b := b.trans a
  one_mul _ := rfl
  mul_one _ := rfl
  mul_assoc _ _ _ := rfl
  inv f := f.symm
inv_mul_cancel f := ext symm_apply_apply f

/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (f g : R ≃⋆ₐ[S] R) (x : R)
  statement: (f * g) x = f (g x)
  proof: rfl

中文:
定理 mul_apply
  条件: (f g : R ≃⋆ₐ[S] R) (x : R)
  结论: (f * g) x = f (g x)
  证明: rfl
-/
@[simp] theorem mul_apply (f g : R ≃⋆ₐ[S] R) (x : R) : (f * g) x = f (g x) := rfl

/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x : R)
  statement: (1 : R ≃⋆ₐ[S] R) x = x
  proof: rfl

中文:
定理 one_apply
  条件: (x : R)
  结论: (1 : R ≃⋆ₐ[S] R) x = x
  证明: rfl
-/
@[simp] theorem one_apply (x : R) : (1 : R ≃⋆ₐ[S] R) x = x := rfl

/--
theorem `aut_inv` / 定理 `aut_inv`

English:
theorem aut_inv
  given: (f : R ≃⋆ₐ[S] R)
  statement: f⁻¹ = f.symm
  proof: rfl

中文:
定理 aut_inv
  条件: (f : R ≃⋆ₐ[S] R)
  结论: f⁻¹ = f.symm
  证明: rfl
-/
theorem aut_inv (f : R ≃⋆ₐ[S] R) : f⁻¹ = f.symm := rfl

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (f : R ≃⋆ₐ[S] R) (n : Nat)
  proof: hom_coe_pow _ (funext one_apply) (fun f g => funext <| mul_apply f g) _ _

中文:
定理 coe_pow
  条件: (f : R ≃⋆ₐ[S] R) (n : 自然数)
  证明: hom_coe_pow _ (funext one_apply) (fun f g => funext <| mul_apply f g) _ _
-/
@[simp] theorem coe_pow (f : R ≃⋆ₐ[S] R) (n : Nat) :
    ⇑(f ^ n) = (⇑f)^[n] :=
  hom_coe_pow _ (funext one_apply) (fun f g => funext <| mul_apply f g) _ _

end Group

end StarAlgEquiv
