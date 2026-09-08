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


/-- A *non-unital ⋆-algebra homomorphism* is a non-unital algebra homomorphism between
non-unital `R`-algebras `A` and `B` equipped with a `star` operation, and this homomorphism is
also `star`-preserving. -/
/-
**NonUnitalStarAlgHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     (B : Type u_3) →       [inst : Mon
oid R] →         [inst_1 : NonUnitalNonAssocSemiring A] →           [DistribMulA
ction R A] →             [Star A] → [inst_4 : NonUnitalNonAssocSemiring B] → [Di
stribMulAction R B] → [Star B] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *non-unital ⋆-algebra homomorphism* is a non-unital algebra homomorphism betwe
en
non-unital `R`-algebras `A` and `B` equipped with a `star` operation, and this h
omomorphism is
also `star`-preserving.
-/
structure NonUnitalStarAlgHom (R A B : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
  [DistribMulAction R A] [Star A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
  [Star B] extends A →ₙₐ[R] B where
  /-- By definition, a non-unital ⋆-algebra homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

@[inherit_doc NonUnitalStarAlgHom] infixr:25 " →⋆ₙₐ " => NonUnitalStarAlgHom _

@[inherit_doc] notation:25 A " →⋆ₙₐ[" R "] " B => NonUnitalStarAlgHom R A B

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
/-
**NonUnitalStarAlgHomClass.toNonUnitalStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `NonU
nitalStarAlgHomClass`。
形式化陈述：toNonUnitalStarAlgHom [StarHomClass F A B] (f : F) : A ->⋆ₙₐ[R] B
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…

--- 原说明 ---
Turn an element of a type `F` satisfying `NonUnitalAlgHomClass F R A B` and `Sta
rHomClass F A B`
into an actual `NonUnitalStarAlgHom`. This is declared as the default coercion f
rom `F` to
`A →⋆ₙₐ[R] B`.
-/
def toNonUnitalStarAlgHom [StarHomClass F A B] (f : F) : A →⋆ₙₐ[R] B :=
  { (f : A →ₙₐ[R] B) with
    map_star' := map_star f }
/-
**NonUnitalStarAlgHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgHomClass`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [StarHomClass F A B] : CoeTC F (A →⋆ₙₐ[R] B) :=
  ⟨toNonUnitalStarAlgHom⟩
/-
**NonUnitalStarAlgHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgHomClass`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**NonUnitalStarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (A →⋆ₙₐ[R] B) A B where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩ h; congr
/-
**NonUnitalStarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonUnitalAlgHomClass (A →⋆ₙₐ[R] B) R A B where
  map_smulₛₗ f := f.map_smul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
/-
**NonUnitalStarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarHomClass (A →⋆ₙₐ[R] B) A B where
  map_star f := f.map_star'

initialize_simps_projections NonUnitalStarAlgHom
  (toFun → apply)

@[simp]
/-
**NonUnitalStarAlgHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : Monoid R] [inst_1 :
 NonUnitalNonAssocSemiring A]   [inst_2 : DistribMulAction R A] [inst_3 : Star A
] [inst_4 : NonUnitalNonAssocSemiring B]   [inst_5 : DistribMulAction R B] [inst
_6 : Star B] {F : Type u_6} [inst_7 : FunLike F A B]   [inst_8 : NonUnitalAlgHom
Class F R A B] [inst_9 : StarHomClass F A B] (f : F), ⇑↑f = ⇑f
参数：f : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F R A B]
    [StarHomClass F A B] (f : F) :
    ⇑(f : A →⋆ₙₐ[R] B) = f := rfl

@[simp]
/-
**NonUnitalStarAlgHom.coe_toNonUnitalAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
StarAlgHom`。
形式化陈述：coe_toNonUnitalAlgHom {f : A ->⋆ₙₐ[R] B} : (f.toNonUnitalAlgHom : A -> B) 
= f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalAlgHom {f : A →⋆ₙₐ[R] B} : (f.toNonUnitalAlgHom : A → B) = f :=
  rfl

@[ext]
/-
**NonUnitalStarAlgHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : A →⋆ₙₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `NonUnitalStarAlgHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
/-
**NonUnitalStarAlgHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     {B : Type u_3} →       [inst : Mon
oid R] →         [inst_1 : NonUnitalNonAssocSemiring A] →           [inst_2 : Di
stribMulAction R A] →             [inst_3 : Star A] →               [inst_4 : No
nUnitalNonAssocSemiring B] →                 [inst_5 : DistribMulAction R B] →  
                 [inst_6 : Star B] → (f : A →⋆ₙₐ[R] B) → (f' : A → B) → f' = ⇑f 
→ A →⋆ₙₐ[R] B
参数：f : A →⋆ₙₐ[R] B；f' : A → B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `NonUnitalStarAlgHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities.
-/
protected def copy (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : A →⋆ₙₐ[R] B where
  toFun := f'
  map_smul' := h.symm ▸ map_smul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
/-
**NonUnitalStarAlgHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：coe_copy (f : A ->⋆ₙₐ[R] B) (f' : A -> B) (h : f' = f) : ⇑(f.copy f' h) = 
f'
参数：f : A ->⋆ₙₐ[R] B；f' : A -> B；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**NonUnitalStarAlgHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：copy_eq (f : A ->⋆ₙₐ[R] B) (f' : A -> B) (h : f' = f) : f.copy f' h = f
参数：f : A ->⋆ₙₐ[R] B；f' : A -> B；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : A →⋆ₙₐ[R] B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

/-- `coe_mk'` below applies in more cases -/
/-
**NonUnitalStarAlgHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：coe_mk (f : A -> B) (h₁ h₂ h₃ h₄ h₅) : ((⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅⟩ : A
 ->⋆ₙₐ[R] B) : A -> B) = f
参数：f : A -> B；h₁ h₂ h₃ h₄ h₅。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`coe_mk'` below applies in more cases
-/
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅) :
    ((⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅⟩ : A →⋆ₙₐ[R] B) : A → B) = f :=
  rfl

@[simp]
/-
**NonUnitalStarAlgHom.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：coe_mk' (f : A ->ₙₐ[R] B) (h) : ((⟨f, h⟩ : A ->⋆ₙₐ[R] B) : A -> B) = f
参数：f : A ->ₙₐ[R] B；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' (f : A →ₙₐ[R] B) (h) :
    ((⟨f, h⟩ : A →⋆ₙₐ[R] B) : A → B) = f :=
  rfl

@[simp]
/-
**NonUnitalStarAlgHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：mk_coe (f : A ->⋆ₙₐ[R] B) (h₁ h₂ h₃ h₄ h₅) : (⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅
⟩ : A ->⋆ₙₐ[R] B) = f
参数：f : A ->⋆ₙₐ[R] B；h₁ h₂ h₃ h₄ h₅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.ext`：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g
 x) : f = g
-/
theorem mk_coe (f : A →⋆ₙₐ[R] B) (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅⟩ : A →⋆ₙₐ[R] B) = f := by
  ext
  rfl

section

variable (R A)

/-- The identity as a non-unital ⋆-algebra homomorphism. -/
/-
**NonUnitalStarAlgHom.id** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     [inst : Monoid R] →       [inst_1 
: NonUnitalNonAssocSemiring A] → [inst_2 : DistribMulAction R A] → [inst_3 : Sta
r A] → A →⋆ₙₐ[R] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a non-unital ⋆-algebra homomorphism.
-/
protected def id : A →⋆ₙₐ[R] A :=
  { (1 : A →ₙₐ[R] A) with map_star' := fun _ => rfl }

@[simp, norm_cast]
/-
**NonUnitalStarAlgHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：coe_id : ⇑(NonUnitalStarAlgHom.id R A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(NonUnitalStarAlgHom.id R A) = id :=
  rfl

end

/-- The composition of non-unital ⋆-algebra homomorphisms, as a non-unital ⋆-algebra
homomorphism. -/
/-
**NonUnitalStarAlgHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：comp (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B) : A ->⋆ₙₐ[R] C
参数：f : B ->⋆ₙₐ[R] C；g : A ->⋆ₙₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of non-unital ⋆-algebra homomorphisms, as a non-unital ⋆-algebra
homomorphism.
-/
def comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : A →⋆ₙₐ[R] C :=
  { f.toNonUnitalAlgHom.comp g.toNonUnitalAlgHom with
    map_star' := by
      simp only [map_star, NonUnitalAlgHom.toFun_eq_coe, NonUnitalAlgHom.coe_comp,
        coe_toNonUnitalAlgHom, Function.comp_apply, forall_const] }

@[simp]
/-
**NonUnitalStarAlgHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：coe_comp (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B) : ⇑(comp f g) = f ∘ g
参数：f : B ->⋆ₙₐ[R] C；g : A ->⋆ₙₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/-
**NonUnitalStarAlgHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`
。
形式化陈述：comp_apply (f : B ->⋆ₙₐ[R] C) (g : A ->⋆ₙₐ[R] B) (a : A) : comp f g a = f 
(g a)
参数：f : B ->⋆ₙₐ[R] C；g : A ->⋆ₙₐ[R] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
/-
**NonUnitalStarAlgHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`
。
形式化陈述：comp_assoc (f : C ->⋆ₙₐ[R] D) (g : B ->⋆ₙₐ[R] C) (h : A ->⋆ₙₐ[R] B) : (f.c
omp g).comp h = f.comp (g.comp h)
参数：f : C ->⋆ₙₐ[R] D；g : B ->⋆ₙₐ[R] C；h : A ->⋆ₙₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : C →⋆ₙₐ[R] D) (g : B →⋆ₙₐ[R] C) (h : A →⋆ₙₐ[R] B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**NonUnitalStarAlgHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：id_comp (f : A ->⋆ₙₐ[R] B) : (NonUnitalStarAlgHom.id _ _).comp f = f
参数：f : A ->⋆ₙₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.ext`：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g
 x) : f = g
-/
theorem id_comp (f : A →⋆ₙₐ[R] B) : (NonUnitalStarAlgHom.id _ _).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**NonUnitalStarAlgHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：comp_id (f : A ->⋆ₙₐ[R] B) : f.comp (NonUnitalStarAlgHom.id _ _) = f
参数：f : A ->⋆ₙₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.ext`：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g
 x) : f = g
-/
theorem comp_id (f : A →⋆ₙₐ[R] B) : f.comp (NonUnitalStarAlgHom.id _ _) = f :=
  ext fun _ => rfl
/-
**NonUnitalStarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (A →⋆ₙₐ[R] A) where
  mul := comp
  mul_assoc := comp_assoc
  one := NonUnitalStarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
/-
**NonUnitalStarAlgHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：coe_one : ((1 : A ->⋆ₙₐ[R] A) : A -> A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : A →⋆ₙₐ[R] A) : A → A) = id :=
  rfl
/-
**NonUnitalStarAlgHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：one_apply (a : A) : (1 : A ->⋆ₙₐ[R] A) a = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (a : A) : (1 : A →⋆ₙₐ[R] A) a = a :=
  rfl

end Basic

section Zero

-- the `zero` requires extra type class assumptions because we need `star_zero`
variable {R A B C D : Type*} [Monoid R]
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [StarAddMonoid A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]

/-
**NonUnitalStarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (A →⋆ₙₐ[R] B) :=
  ⟨{ (0 : NonUnitalAlgHom (MonoidHom.id R) A B) with map_star' := by simp }⟩
/-
**NonUnitalStarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (A →⋆ₙₐ[R] B) :=
  ⟨0⟩
/-
**NonUnitalStarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidWithZero (A →⋆ₙₐ[R] A) :=
  { (inferInstance : Monoid (A →⋆ₙₐ[R] A)),
    (inferInstance : Zero (A →⋆ₙₐ[R] A)) with
    zero_mul := fun _ => ext fun _ => rfl
    mul_zero := fun f => ext fun _ => map_zero f }

@[simp]
/-
**NonUnitalStarAlgHom.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：coe_zero : ((0 : A ->⋆ₙₐ[R] B) : A -> B) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : A →⋆ₙₐ[R] B) : A → B) = 0 :=
  rfl
/-
**NonUnitalStarAlgHom.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`
。
形式化陈述：zero_apply (a : A) : (0 : A ->⋆ₙₐ[R] B) a = 0
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (a : A) : (0 : A →⋆ₙₐ[R] B) a = 0 :=
  rfl

end Zero

section RestrictScalars

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S] [Star A] [Star B]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

/-- If a monoid `R` acts on another monoid `S`, then a non-unital star algebra homomorphism
over `S` can be viewed as a non-unital star algebra homomorphism over `R`. -/
/-
**NonUnitalStarAlgHom.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAl
gHom`。
形式化陈述：restrictScalars (f : A ->⋆ₙₐ[S] B) : A ->⋆ₙₐ[R] B
参数：f : A ->⋆ₙₐ[S] B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…

--- 原说明 ---
If a monoid `R` acts on another monoid `S`, then a non-unital star algebra homom
orphism
over `S` can be viewed as a non-unital star algebra homomorphism over `R`.
-/
def restrictScalars (f : A →⋆ₙₐ[S] B) : A →⋆ₙₐ[R] B :=
  { (f : A →ₙₐ[S] B).restrictScalars R with
    map_star' := map_star f }

@[simp]
/-
**NonUnitalStarAlgHom.restrictScalars_apply** 是 Mathlib 中的一个引理，位于命名空间 `NonUnital
StarAlgHom`。
形式化陈述：restrictScalars_apply (f : A ->⋆ₙₐ[S] B) (x : A) : f.restrictScalars R x =
 f x
参数：f : A ->⋆ₙₐ[S] B；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_apply (f : A →⋆ₙₐ[S] B) (x : A) : f.restrictScalars R x = f x := rfl
/-
**NonUnitalStarAlgHom.coe_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalSt
arAlgHom`。
形式化陈述：coe_restrictScalars (f : A ->⋆ₙₐ[S] B) : (f.restrictScalars R : A ->ₙ+* B)
 = f
参数：f : A ->⋆ₙₐ[S] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
-/
lemma coe_restrictScalars (f : A →⋆ₙₐ[S] B) : (f.restrictScalars R : A →ₙ+* B) = f := rfl
/-
**NonUnitalStarAlgHom.coe_restrictScalars'** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalS
tarAlgHom`。
形式化陈述：coe_restrictScalars' (f : A ->⋆ₙₐ[S] B) : (f.restrictScalars R : A -> B) =
 f
参数：f : A ->⋆ₙₐ[S] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_restrictScalars' (f : A →⋆ₙₐ[S] B) : (f.restrictScalars R : A → B) = f := rfl
/-
**NonUnitalStarAlgHom.restrictScalars_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUn
italStarAlgHom`。
形式化陈述：restrictScalars_injective : Function.Injective (restrictScalars R : (A ->⋆
ₙₐ[S] B) -> A ->⋆ₙₐ[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.ext`：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g
 x) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →⋆ₙₐ[S] B) → A →⋆ₙₐ[R] B) :=
  fun _ _ h ↦ ext (DFunLike.congr_fun h :)

end RestrictScalars

end NonUnitalStarAlgHom

/-! ### Unital star algebra homomorphisms -/


section Unital

/-- A *⋆-algebra homomorphism* is an algebra homomorphism between `R`-algebras `A` and `B`
equipped with a `star` operation, and this homomorphism is also `star`-preserving. -/
/-
**StarAlgHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     (B : Type u_3) →       [inst : Com
mSemiring R] →         [inst_1 : Semiring A] →           [Algebra R A] → [Star A
] → [inst_4 : Semiring B] → [Algebra R B] → [Star B] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *⋆-algebra homomorphism* is an algebra homomorphism between `R`-algebras `A` a
nd `B`
equipped with a `star` operation, and this homomorphism is also `star`-preservin
g.
-/
structure StarAlgHom (R A B : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B] extends AlgHom R A B where
  /-- By definition, a ⋆-algebra homomorphism preserves the `star` operation. -/
  map_star' : ∀ x : A, toFun (star x) = star (toFun x)

@[inherit_doc StarAlgHom] infixr:25 " →⋆ₐ " => StarAlgHom _

@[inherit_doc] notation:25 A " →⋆ₐ[" R "] " B => StarAlgHom R A B

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
/-
**StarAlgHomClass.toStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHomClass`。
形式化陈述：toStarAlgHom (f : F) : A ->⋆ₐ[R] B
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…

--- 原说明 ---
Turn an element of a type `F` satisfying `AlgHomClass F R A B` and `StarHomClass
 F A B` into an
actual `StarAlgHom`. This is declared as the default coercion from `F` to `A →⋆ₐ
[R] B`.
-/
def toStarAlgHom (f : F) : A →⋆ₐ[R] B :=
  { (AlgHomClass.toAlgHom f) with
    map_star' := map_star f }
/-
**StarAlgHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC F (A →⋆ₐ[R] B) :=
  ⟨toStarAlgHom⟩

end StarAlgHomClass

namespace StarAlgHom

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

/-
**StarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (A →⋆ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩, _⟩ h; congr
/-
**StarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AlgHomClass (A →⋆ₐ[R] B) R A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  commutes f := f.commutes'
/-
**StarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarHomClass (A →⋆ₐ[R] B) A B where
  map_star f := f.map_star'

@[simp]
/-
**StarAlgHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：∀ {R : Type u_2} {A : Type u_3} {B : Type u_4} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Star A] [inst_4 : Semiring
 B] [inst_5 : Algebra R B] [inst_6 : Star B] {F : Type u_7}   [inst_7 : FunLike 
F A B] [inst_8 : AlgHomClass F R A B] [inst_9 : StarHomClass F A B] (f : F), ⇑↑f
 = ⇑f
参数：f : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    [StarHomClass F A B] (f : F) :
    ⇑(f : A →⋆ₐ[R] B) = f :=
  rfl

initialize_simps_projections StarAlgHom (toFun → apply)

attribute [coe] StarAlgHom.toAlgHom
/-
**StarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (A →⋆ₐ[R] B) (A →ₐ[R] B) :=
  ⟨toAlgHom⟩

@[simp]
/-
**StarAlgHom.coe_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：coe_toAlgHom {f : A ->⋆ₐ[R] B} : (f.toAlgHom : A -> B) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAlgHom {f : A →⋆ₐ[R] B} : (f.toAlgHom : A → B) = f :=
  rfl

@[ext]
/-
**StarAlgHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : A →⋆ₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `StarAlgHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
/-
**StarAlgHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：{R : Type u_2} →   {A : Type u_3} →     {B : Type u_4} →       [inst : Com
mSemiring R] →         [inst_1 : Semiring A] →           [inst_2 : Algebra R A] 
→             [inst_3 : Star A] →               [inst_4 : Semiring B] →         
        [inst_5 : Algebra R B] → [inst_6 : Star B] → (f : A →⋆ₐ[R] B) → (f' : A 
→ B) → f' = ⇑f → A →⋆ₐ[R] B
参数：f : A →⋆ₐ[R] B；f' : A → B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `StarAlgHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities.
-/
protected def copy (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : A →⋆ₐ[R] B where
  toFun := f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  commutes' := h.symm ▸ AlgHomClass.commutes f
  map_star' := h.symm ▸ map_star f

@[simp]
/-
**StarAlgHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：coe_copy (f : A ->⋆ₐ[R] B) (f' : A -> B) (h : f' = f) : ⇑(f.copy f' h) = f
'
参数：f : A ->⋆ₐ[R] B；f' : A -> B；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**StarAlgHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：copy_eq (f : A ->⋆ₐ[R] B) (f' : A -> B) (h : f' = f) : f.copy f' h = f
参数：f : A ->⋆ₐ[R] B；f' : A -> B；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : A →⋆ₐ[R] B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/-
**StarAlgHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：coe_mk (f : A -> B) (h₁ h₂ h₃ h₄ h₅ h₆) : ((⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩
, h₆⟩ : A ->⋆ₐ[R] B) : A -> B) = f
参数：f : A -> B；h₁ h₂ h₃ h₄ h₅ h₆。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅ h₆) :
    ((⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A →⋆ₐ[R] B) : A → B) = f :=
  rfl

-- this is probably the more useful lemma for Lean 4 and should likely replace `coe_mk` above
@[simp]
/-
**StarAlgHom.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：coe_mk' (f : A ->ₐ[R] B) (h) : ((⟨f, h⟩ : A ->⋆ₐ[R] B) : A -> B) = f
参数：f : A ->ₐ[R] B；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' (f : A →ₐ[R] B) (h) :
    ((⟨f, h⟩ : A →⋆ₐ[R] B) : A → B) = f :=
  rfl

@[simp]
/-
**StarAlgHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：mk_coe (f : A ->⋆ₐ[R] B) (h₁ h₂ h₃ h₄ h₅ h₆) : (⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩,
 h₅⟩, h₆⟩ : A ->⋆ₐ[R] B) = f
参数：f : A ->⋆ₐ[R] B；h₁ h₂ h₃ h₄ h₅ h₆。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.ext`：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = 
g
-/
theorem mk_coe (f : A →⋆ₐ[R] B) (h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A →⋆ₐ[R] B) = f := by
  ext
  rfl

section

variable (R A)

/-- The identity as a `StarAlgHom`. -/
/-
**StarAlgHom.id** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：(R : Type u_2) →   (A : Type u_3) →     [inst : CommSemiring R] → [inst_1 
: Semiring A] → [inst_2 : Algebra R A] → [inst_3 : Star A] → A →⋆ₐ[R] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a `StarAlgHom`.
-/
protected def id : A →⋆ₐ[R] A :=
  { AlgHom.id _ _ with map_star' := fun _ => rfl }

@[simp, norm_cast]
/-
**StarAlgHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：coe_id : ⇑(StarAlgHom.id R A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(StarAlgHom.id R A) = id :=
  rfl

/-- `algebraMap R A` as a `StarAlgHom` when `A` is a star algebra over `R`. -/
@[simps]
/-
**StarAlgHom.ofId** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：ofId (R A : Type*) [CommSemiring R] [StarRing R] [Semiring A] [StarMul A] 
[Algebra R A] [StarModule R A] : R ->⋆ₐ[R] A
参数：R A : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`algebraMap R A` as a `StarAlgHom` when `A` is a star algebra over `R`.
-/
def ofId (R A : Type*) [CommSemiring R] [StarRing R] [Semiring A] [StarMul A]
    [Algebra R A] [StarModule R A] : R →⋆ₐ[R] A :=
  { Algebra.ofId R A with
    toFun := algebraMap R A
    map_star' := by simp [Algebra.algebraMap_eq_smul_one] }

end

/-
**StarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (A →⋆ₐ[R] A) :=
  ⟨StarAlgHom.id R A⟩

/-- The composition of ⋆-algebra homomorphisms, as a ⋆-algebra homomorphism. -/
/-
**StarAlgHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：comp (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B) : A ->⋆ₐ[R] C
参数：f : B ->⋆ₐ[R] C；g : A ->⋆ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of ⋆-algebra homomorphisms, as a ⋆-algebra homomorphism.
-/
def comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : A →⋆ₐ[R] C :=
  { f.toAlgHom.comp g.toAlgHom with
    map_star' := by
      simp only [map_star, AlgHom.toFun_eq_coe, AlgHom.coe_comp, coe_toAlgHom,
        Function.comp_apply, forall_const] }

@[simp]
/-
**StarAlgHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：coe_comp (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B) : ⇑(comp f g) = f ∘ g
参数：f : B ->⋆ₐ[R] C；g : A ->⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/-
**StarAlgHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：comp_apply (f : B ->⋆ₐ[R] C) (g : A ->⋆ₐ[R] B) (a : A) : comp f g a = f (g
 a)
参数：f : B ->⋆ₐ[R] C；g : A ->⋆ₐ[R] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
/-
**StarAlgHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：comp_assoc (f : C ->⋆ₐ[R] D) (g : B ->⋆ₐ[R] C) (h : A ->⋆ₐ[R] B) : (f.comp
 g).comp h = f.comp (g.comp h)
参数：f : C ->⋆ₐ[R] D；g : B ->⋆ₐ[R] C；h : A ->⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : C →⋆ₐ[R] D) (g : B →⋆ₐ[R] C) (h : A →⋆ₐ[R] B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**StarAlgHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：id_comp (f : A ->⋆ₐ[R] B) : (StarAlgHom.id _ _).comp f = f
参数：f : A ->⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.ext`：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = 
g
-/
theorem id_comp (f : A →⋆ₐ[R] B) : (StarAlgHom.id _ _).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**StarAlgHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：comp_id (f : A ->⋆ₐ[R] B) : f.comp (StarAlgHom.id _ _) = f
参数：f : A ->⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.ext`：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = 
g
-/
theorem comp_id (f : A →⋆ₐ[R] B) : f.comp (StarAlgHom.id _ _) = f :=
  ext fun _ => rfl
/-
**StarAlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (A →⋆ₐ[R] A) where
  mul := comp
  mul_assoc := comp_assoc
  one := StarAlgHom.id R A
  one_mul := id_comp
  mul_one := comp_id

/-- A unital morphism of ⋆-algebras is a `NonUnitalStarAlgHom`. -/
/-
**StarAlgHom.toNonUnitalStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：toNonUnitalStarAlgHom (f : A ->⋆ₐ[R] B) : A ->⋆ₙₐ[R] B
参数：f : A ->⋆ₐ[R] B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.map_star'`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [in
st : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : St
ar A] [ins…

--- 原说明 ---
A unital morphism of ⋆-algebras is a `NonUnitalStarAlgHom`.
-/
def toNonUnitalStarAlgHom (f : A →⋆ₐ[R] B) : A →⋆ₙₐ[R] B :=
  { f with map_smul' := map_smul f }

@[simp]
/-
**StarAlgHom.coe_toNonUnitalStarAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：coe_toNonUnitalStarAlgHom (f : A ->⋆ₐ[R] B) : (f.toNonUnitalStarAlgHom : A
 -> B) = f
参数：f : A ->⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalStarAlgHom (f : A →⋆ₐ[R] B) : (f.toNonUnitalStarAlgHom : A → B) = f :=
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
/-
**NonUnitalStarAlgHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：fst : A × B ->⋆ₙₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection of a product is a non-unital ⋆-algebra homomorphism.
-/
def fst : A × B →⋆ₙₐ[R] A :=
  { NonUnitalAlgHom.fst R A B with map_star' := fun _ => rfl }

/-- The second projection of a product is a non-unital ⋆-algebra homomorphism. -/
@[simps!]
/-
**NonUnitalStarAlgHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：snd : A × B ->⋆ₙₐ[R] B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection of a product is a non-unital ⋆-algebra homomorphism.
-/
def snd : A × B →⋆ₙₐ[R] B :=
  { NonUnitalAlgHom.snd R A B with map_star' := fun _ => rfl }

variable {R A B C}

/-- The `Function.prod` of two morphisms is a morphism. -/
@[simps!]
/-
**NonUnitalStarAlgHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：prod (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C) : A ->⋆ₙₐ[R] B × C
参数：f : A ->⋆ₙₐ[R] B；g : A ->⋆ₙₐ[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Function.prod` of two morphisms is a morphism.
-/
def prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : A →⋆ₙₐ[R] B × C :=
  { f.toNonUnitalAlgHom.prod g.toNonUnitalAlgHom with
    map_star' := fun x => by simp [map_star, Prod.ext_iff] }
/-
**NonUnitalStarAlgHom.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：coe_prod (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C) : ⇑(f.prod g) = Function.pr
od f g
参数：f : A ->⋆ₙₐ[R] B；g : A ->⋆ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/-
**NonUnitalStarAlgHom.fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：fst_prod (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C) : (fst R B C).comp (prod f 
g) = f
参数：f : A ->⋆ₙₐ[R] B；g : A ->⋆ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.ext`：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g
 x) : f = g
-/
theorem fst_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  ext; rfl

@[simp]
/-
**NonUnitalStarAlgHom.snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：snd_prod (f : A ->⋆ₙₐ[R] B) (g : A ->⋆ₙₐ[R] C) : (snd R B C).comp (prod f 
g) = g
参数：f : A ->⋆ₙₐ[R] B；g : A ->⋆ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.ext`：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g
 x) : f = g
-/
theorem snd_prod (f : A →⋆ₙₐ[R] B) (g : A →⋆ₙₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  ext; rfl

@[simp]
/-
**NonUnitalStarAlgHom.prod_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHo
m`。
形式化陈述：prod_fst_snd : prod (fst R A B) (snd R A B) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Function.prod_fst_snd`：∀ {α : Type u_1} {β : Type u_2}, Function.prod Pr
od.fst Prod.snd = id
-/
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  DFunLike.coe_injective Function.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
/-
**NonUnitalStarAlgHom.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：prodEquiv : (A ->⋆ₙₐ[R] B) × (A ->⋆ₙₐ[R] C) ≃ (A ->⋆ₙₐ[R] B × C) where toF
un f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the product of two maps with the same domain is equivalent to taking the 
product of
their codomains.
-/
def prodEquiv : (A →⋆ₙₐ[R] B) × (A →⋆ₙₐ[R] C) ≃ (A →⋆ₙₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

end Prod

section Pi

variable {ι : Type*}

/-- `Function.eval` as a `NonUnitalStarAlgHom`. -/
@[simps]
/-
**NonUnitalStarAlgHom._root_.Pi.evalNonUnitalStarAlgHom** 是 Mathlib 中的一个定义，位于命名空
间 `NonUnitalStarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.eval` as a `NonUnitalStarAlgHom`.
-/
def _root_.Pi.evalNonUnitalStarAlgHom (R : Type*) (A : ι → Type*) (j : ι) [Monoid R]
    [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, DistribMulAction R (A i)] [∀ i, Star (A i)] :
    (∀ i, A i) →⋆ₙₐ[R] A j :=
  { Pi.evalMulHom A j, Pi.evalAddHom A j with
    map_smul' _ _ := rfl
    map_zero' := rfl
    map_star' _ := rfl }

/-- `Function.eval` as a `StarAlgHom`. -/
@[simps]
/-
**NonUnitalStarAlgHom._root_.Pi.evalStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `NonUni
talStarAlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.eval` as a `StarAlgHom`.
-/
def _root_.Pi.evalStarAlgHom (R : Type*) (A : ι → Type*) (j : ι) [CommSemiring R]
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] [∀ i, Star (A i)] :
    (∀ i, A i) →⋆ₐ[R] A j :=
  { Pi.evalNonUnitalStarAlgHom R A j, Pi.evalRingHom A j with
    commutes' _ := rfl }

end Pi

section InlInr

variable (R A B C : Type*) [Monoid R] [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
  [StarAddMonoid A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [StarAddMonoid B]
  [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [StarAddMonoid C]

/-- The left injection into a product is a non-unital algebra homomorphism. -/
/-
**NonUnitalStarAlgHom.inl** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：inl : A ->⋆ₙₐ[R] A × B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left injection into a product is a non-unital algebra homomorphism.
-/
def inl : A →⋆ₙₐ[R] A × B :=
  prod 1 0

/-- The right injection into a product is a non-unital algebra homomorphism. -/
/-
**NonUnitalStarAlgHom.inr** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：inr : B ->⋆ₙₐ[R] A × B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right injection into a product is a non-unital algebra homomorphism.
-/
def inr : B →⋆ₙₐ[R] A × B :=
  prod 0 1

variable {R A B}

@[simp]
/-
**NonUnitalStarAlgHom.coe_inl** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：coe_inl : (inl R A B : A -> A × B) = fun x => (x, 0)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inl : (inl R A B : A → A × B) = fun x => (x, 0) :=
  rfl
/-
**NonUnitalStarAlgHom.inl_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：inl_apply (x : A) : inl R A B x = (x, 0)
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_apply (x : A) : inl R A B x = (x, 0) :=
  rfl

@[simp]
/-
**NonUnitalStarAlgHom.coe_inr** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：coe_inr : (inr R A B : B -> A × B) = Prod.mk 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inr : (inr R A B : B → A × B) = Prod.mk 0 :=
  rfl
/-
**NonUnitalStarAlgHom.inr_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：inr_apply (x : B) : inr R A B x = (0, x)
参数：x : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**StarAlgHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：fst : A × B ->⋆ₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection of a product is a ⋆-algebra homomorphism.
-/
def fst : A × B →⋆ₐ[R] A :=
  { AlgHom.fst R A B with map_star' := fun _ => rfl }

/-- The second projection of a product is a ⋆-algebra homomorphism. -/
@[simps!]
/-
**StarAlgHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：snd : A × B ->⋆ₐ[R] B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection of a product is a ⋆-algebra homomorphism.
-/
def snd : A × B →⋆ₐ[R] B :=
  { AlgHom.snd R A B with map_star' := fun _ => rfl }

variable {R A B C}

/-- The `Function.prod` of two morphisms is a morphism. -/
@[simps!]
/-
**StarAlgHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：prod (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C) : A ->⋆ₐ[R] B × C
参数：f : A ->⋆ₐ[R] B；g : A ->⋆ₐ[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Function.prod` of two morphisms is a morphism.
-/
def prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : A →⋆ₐ[R] B × C :=
  { f.toAlgHom.prod g.toAlgHom with map_star' := fun x => by simp [Prod.star_def, map_star] }
/-
**StarAlgHom.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：coe_prod (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C) : ⇑(f.prod g) = Function.prod
 f g
参数：f : A ->⋆ₐ[R] B；g : A ->⋆ₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/-
**StarAlgHom.fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：fst_prod (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C) : (fst R B C).comp (prod f g)
 = f
参数：f : A ->⋆ₐ[R] B；g : A ->⋆ₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.ext`：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = 
g
-/
theorem fst_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : (fst R B C).comp (prod f g) = f := by
  ext; rfl

@[simp]
/-
**StarAlgHom.snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：snd_prod (f : A ->⋆ₐ[R] B) (g : A ->⋆ₐ[R] C) : (snd R B C).comp (prod f g)
 = g
参数：f : A ->⋆ₐ[R] B；g : A ->⋆ₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.ext`：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = 
g
-/
theorem snd_prod (f : A →⋆ₐ[R] B) (g : A →⋆ₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  ext; rfl

@[simp]
/-
**StarAlgHom.prod_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgHom`。
形式化陈述：prod_fst_snd : prod (fst R A B) (snd R A B) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Function.prod_fst_snd`：∀ {α : Type u_1} {β : Type u_2}, Function.prod Pr
od.fst Prod.snd = id
-/
theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
  DFunLike.coe_injective Function.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
/-
**StarAlgHom.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgHom`。
形式化陈述：prodEquiv : (A ->⋆ₐ[R] B) × (A ->⋆ₐ[R] C) ≃ (A ->⋆ₐ[R] B × C) where toFun 
f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the product of two maps with the same domain is equivalent to taking the 
product of
their codomains.
-/
def prodEquiv : (A →⋆ₐ[R] B) × (A →⋆ₐ[R] C) ≃ (A →⋆ₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)

end StarAlgHom

/-! ### Star algebra equivalences -/

/-- A *⋆-algebra* equivalence is an equivalence preserving addition, multiplication, scalar
multiplication and the star operation, which allows for considering both unital and non-unital
equivalences with a single structure. -/
/-
**StarAlgEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     (B : Type u_3) →       [Add A] → [
Add B] → [Mul A] → [Mul B] → [SMul R A] → [SMul R B] → [Star A] → [Star B] → Typ
e (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *⋆-algebra* equivalence is an equivalence preserving addition, multiplication,
 scalar
multiplication and the star operation, which allows for considering both unital 
and non-unital
equivalences with a single structure.
-/
structure StarAlgEquiv (R A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [SMul R A] [SMul R B]
  [Star A] [Star B] extends A ≃⋆+* B where
  /-- By definition, a ⋆-algebra equivalence commutes with the action of scalars. -/
  map_smul' : ∀ (r : R) (a : A), toFun (r • a) = r • toFun a

@[inherit_doc StarAlgEquiv] infixr:25 " ≃⋆ₐ " => StarAlgEquiv _

@[inherit_doc] notation:25 A " ≃⋆ₐ[" R "] " B => StarAlgEquiv R A B

/-- Reinterpret a star algebra equivalence as a `StarRingEquiv` by forgetting the interaction with
the scalar multiplication. -/
add_decl_doc StarAlgEquiv.toStarRingEquiv

/-- The class that directly extends `RingEquivClass` and `SMulHomClass`.

Mostly an implementation detail for the ⋆-algebra equivalence class
which is currently: `[NonUnitalAlgEquivClass]` and `[StarHomClass]`.
-/
/-
**NonUnitalAlgEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (R : outParam (Type u_2)) →     (A : outParam (Type u_3
)) →       (B : outParam (Type u_4)) →         [Add A] → [Mul A] → [SMul R A] → 
[Add B] → [Mul B] → [SMul R B] → [EquivLike F A B] → Prop
参数：Type u_2；Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class that directly extends `RingEquivClass` and `SMulHomClass`.

Mostly an implementation detail for the ⋆-algebra equivalence class
which is currently: `[NonUnitalAlgEquivClass]` and `[StarHomClass]`.
-/
class NonUnitalAlgEquivClass (F : Type*) (R A B : outParam Type*)
  [Add A] [Mul A] [SMul R A] [Add B] [Mul B] [SMul R B] [EquivLike F A B] : Prop
  extends RingEquivClass F A B, MulActionSemiHomClass F (@id R) A B where

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {F R A B : Type*} [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [EquivLike F A B]
    [NonUnitalAlgEquivClass F R A B] :
    NonUnitalAlgHomClass F R A B :=
  { }

set_option backward.isDefEq.respectTransparency false in
-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (F R A B : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [Semiring B] [Algebra R B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] :
    AlgEquivClass F R A B :=
  { commutes := fun f r => by simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one] }

namespace StarAlgEquivClass

/-- Turn an element of a type `F` satisfying `AlgEquivClass F R A B` and `StarHomClass F A B` into
an actual `StarAlgEquiv`. This is declared as the default coercion from `F` to `A ≃⋆ₐ[R] B`. -/
@[coe]
/-
**StarAlgEquivClass.toStarAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquivClass`
。
形式化陈述：toStarAlgEquiv {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add 
B] [Mul B] [SMul R B] [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B
] [StarHomClass F A B] (f : F) : A ≃⋆ₐ[R] B
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam 
(Type u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : Add A}  
 {inst_1 : Mul A} {inst_2 : S…

--- 原说明 ---
Turn an element of a type `F` satisfying `AlgEquivClass F R A B` and `StarHomCla
ss F A B` into
an actual `StarAlgEquiv`. This is declared as the default coercion from `F` to `
A ≃⋆ₐ[R] B`.
-/
def toStarAlgEquiv {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] [Mul B] [SMul R B]
    [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] [StarHomClass F A B]
    (f : F) : A ≃⋆ₐ[R] B :=
  { (RingEquivClass.toRingEquiv f : A ≃+* B) with
    map_star' := map_star f
    map_smul' := map_smul f }

/-- Any type satisfying `AlgEquivClass` and `StarHomClass` can be cast into `StarAlgEquiv` via
`StarAlgEquivClass.toStarAlgEquiv`. -/
/-
**StarAlgEquivClass.instCoeHead** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgEquivClass`。
形式化陈述：instCoeHead {F R A B : Type*} [Add A] [Mul A] [SMul R A] [Star A] [Add B] 
[Mul B] [SMul R B] [Star B] [EquivLike F A B] [NonUnitalAlgEquivClass F R A B] [
StarHomClass F A B] : CoeHead F (A ≃⋆ₐ[R] B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `AlgEquivClass` and `StarHomClass` can be cast into `StarAlg
Equiv` via
`StarAlgEquivClass.toStarAlgEquiv`.
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

/-
**StarAlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**StarAlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonUnitalAlgEquivClass (A ≃⋆ₐ[R] B) R A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_smulₛₗ := map_smul'
/-
**StarAlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarRingEquivClass (A ≃⋆ₐ[R] B) A B where
  map_star f := f.map_star'

/-- Helper instance for cases where the inference via `EquivLike` is too hard. -/
/-
**StarAlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper instance for cases where the inference via `EquivLike` is too hard.
-/
instance : FunLike (A ≃⋆ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective := DFunLike.coe_injective

@[simp]
/-
**StarAlgEquiv.toStarRingEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toStarRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toStarRingEquiv = e
参数：e : A ≃⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toStarRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toStarRingEquiv = e := rfl
/-
**StarAlgEquiv.toRingEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toRingEquiv = e
参数：e : A ≃⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toRingEquiv = e :=
  rfl

@[ext]
/-
**StarAlgEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：ext {f g : A ≃⋆ₐ[R] B} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : A ≃⋆ₐ[R] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

variable (R A) in
/-- The identity map is a star algebra isomorphism. -/
@[refl]
/-
**StarAlgEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：(R : Type u_2) →   (A : Type u_3) → [inst : Add A] → [inst_1 : Mul A] → [i
nst_2 : SMul R A] → [inst_3 : Star A] → A ≃⋆ₐ[R] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map is a star algebra isomorphism.
-/
protected def refl : A ≃⋆ₐ[R] A :=
  { StarRingEquiv.refl (A := A) with
    map_smul' := fun _ _ => rfl }
/-
**StarAlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (A ≃⋆ₐ[R] A) :=
  ⟨.refl R A⟩

@[simp]
/-
**StarAlgEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：coe_refl : ⇑(StarAlgEquiv.refl R A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- See Note [custom simps projection] -/
/-
**StarAlgEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv.Simps`。
形式化陈述：{R : Type u_2} →   {A : Type u_3} →     {B : Type u_4} →       [inst : Add
 A] →         [inst_1 : Add B] →           [inst_2 : Mul A] →             [inst_
3 : Mul B] →               [inst_4 : SMul R A] → [inst_5 : SMul R B] → [inst_6 :
 Star A] → [inst_7 : Star B] → (A ≃⋆ₐ[R] B) → B → A
参数：A ≃⋆ₐ[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : A ≃⋆ₐ[R] B) : B → A :=
  e.symm

initialize_simps_projections StarAlgEquiv (toFun → apply, invFun → symm_apply)

@[simp]
/-
**StarAlgEquiv.invFun_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：invFun_eq_symm {e : A ≃⋆ₐ[R] B} : EquivLike.inv e = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_symm {e : A ≃⋆ₐ[R] B} : EquivLike.inv e = e.symm :=
  rfl

@[simp]
/-
**StarAlgEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：symm_symm (e : A ≃⋆ₐ[R] B) : e.symm.symm = e
参数：e : A ≃⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : A ≃⋆ₐ[R] B) : e.symm.symm = e := rfl
/-
**StarAlgEquiv.symm_apply_eq** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEquiv`。
形式化陈述：symm_apply_eq (e : A ≃⋆ₐ[R] B) {x y} : e.symm x = y ↔ x = e y
参数：e : A ≃⋆ₐ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
lemma symm_apply_eq (e : A ≃⋆ₐ[R] B) {x y} :
    e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
/-
**StarAlgEquiv.eq_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEquiv`。
形式化陈述：eq_symm_apply (e : A ≃⋆ₐ[R] B) {x y} : y = e.symm x ↔ e y = x
参数：e : A ≃⋆ₐ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
lemma eq_symm_apply (e : A ≃⋆ₐ[R] B) {x y} :
    y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply
/-
**StarAlgEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：symm_bijective : Function.Bijective (symm : (A ≃⋆ₐ[R] B) -> B ≃⋆ₐ[R] A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `StarAlgEquiv.symm_symm`：symm_symm (e : A ≃⋆ₐ[R] B) : e.symm.symm = e
-/
theorem symm_bijective : Function.Bijective (symm : (A ≃⋆ₐ[R] B) → B ≃⋆ₐ[R] A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**StarAlgEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：coe_mk (e h) : ⇑(⟨e, h⟩ : A ≃⋆ₐ[R] B) = e
参数：e h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (e h) : ⇑(⟨e, h⟩ : A ≃⋆ₐ[R] B) = e := rfl

@[simp]
/-
**StarAlgEquiv.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：mk_coe (e : A ≃⋆ₐ[R] B) (e' h₁ h₂ h₃ h₄ h₅ h₆) : (⟨⟨⟨⟨e, e', h₁, h₂⟩, h₃, 
h₄⟩, h₅⟩, h₆⟩ : A ≃⋆ₐ[R] B) = e
参数：e : A ≃⋆ₐ[R] B；e' h₁ h₂ h₃ h₄ h₅ h₆。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgEquiv.ext`：ext {f g : A ≃⋆ₐ[R] B} (h : forall a, f a = g a) : f =
 g
-/
theorem mk_coe (e : A ≃⋆ₐ[R] B) (e' h₁ h₂ h₃ h₄ h₅ h₆) :
    (⟨⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A ≃⋆ₐ[R] B) = e := ext fun _ => rfl

@[simp]
/-
**StarAlgEquiv.symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：symm_mk (e : A ≃⋆+* B) (h₁) : dsimp% (⟨e, h₁⟩ : A ≃⋆ₐ[R] B).symm = { (⟨e, 
h₁⟩ : A ≃⋆ₐ[R] B).symm with toStarRingEquiv
参数：e : A ≃⋆+* B；h₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_mk (e : A ≃⋆+* B) (h₁) : dsimp%
    (⟨e, h₁⟩ : A ≃⋆ₐ[R] B).symm =
      { (⟨e, h₁⟩ : A ≃⋆ₐ[R] B).symm with
        toStarRingEquiv := e.symm } :=
  rfl

@[simp]
/-
**StarAlgEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：refl_symm : (StarAlgEquiv.refl R A).symm = .refl R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (StarAlgEquiv.refl R A).symm = .refl R A :=
  rfl

@[simp]
/-
**StarAlgEquiv.toStarRingEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toStarRingEquiv_symm (e : A ≃⋆ₐ[R] B) : (e.symm : B ≃⋆+* A) = (e : A ≃⋆+* 
B).symm
参数：e : A ≃⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgEquiv.instStarRingEquivClass`：∀ {R : Type u_2} {A : Type u_3} {B 
: Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B]   
[inst_4 : SMul R A] [inst…
-/
theorem toStarRingEquiv_symm (e : A ≃⋆ₐ[R] B) : (e.symm : B ≃⋆+* A) = (e : A ≃⋆+* B).symm := rfl

@[simp]
/-
**StarAlgEquiv.toRingEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toRingEquiv_symm (e : A ≃⋆ₐ[R] B) : (e : A ≃⋆+* B).symm = (e : A ≃+* B).sy
mm
参数：e : A ≃⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgEquiv.instStarRingEquivClass`：∀ {R : Type u_2} {A : Type u_3} {B 
: Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B]   
[inst_4 : SMul R A] [inst…
-/
theorem toRingEquiv_symm (e : A ≃⋆ₐ[R] B) : (e : A ≃⋆+* B).symm = (e : A ≃+* B).symm := rfl

/-- Transitivity of `StarAlgEquiv`. -/
@[trans]
/-
**StarAlgEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : A ≃⋆ₐ[R] C
参数：e₁ : A ≃⋆ₐ[R] B；e₂ : B ≃⋆ₐ[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transitivity of `StarAlgEquiv`.
-/
def trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : A ≃⋆ₐ[R] C :=
  { e₁.toStarRingEquiv.trans e₂.toStarRingEquiv with
    map_smul' := fun r a =>
      show e₂.toFun (e₁.toFun (r • a)) = r • e₂.toFun (e₁.toFun a) by
        rw [e₁.map_smul', e₂.map_smul'] }

@[simp]
/-
**StarAlgEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：apply_symm_apply (e : A ≃⋆ₐ[R] B) : forall x, e (e.symm x) = x
参数：e : A ≃⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarRingEquiv.apply_symm_apply`：apply_symm_apply (e : A ≃⋆+* B) : forall
 x, e (e.symm x) = x
-/
theorem apply_symm_apply (e : A ≃⋆ₐ[R] B) : ∀ x, e (e.symm x) = x :=
  e.toStarRingEquiv.apply_symm_apply

@[simp]
/-
**StarAlgEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：symm_apply_apply (e : A ≃⋆ₐ[R] B) : forall x, e.symm (e x) = x
参数：e : A ≃⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarRingEquiv.symm_apply_apply`：symm_apply_apply (e : A ≃⋆+* B) : forall
 x, e.symm (e x) = x
-/
theorem symm_apply_apply (e : A ≃⋆ₐ[R] B) : ∀ x, e.symm (e x) = x :=
  e.toStarRingEquiv.symm_apply_apply

@[simp]
/-
**StarAlgEquiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：symm_trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : C) : (e₁.trans e
₂).symm x = e₁.symm (e₂.symm x)
参数：e₁ : A ≃⋆ₐ[R] B；e₂ : B ≃⋆ₐ[R] C；x : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
/-
**StarAlgEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：coe_trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁
参数：e₁ : A ≃⋆ₐ[R] B；e₂ : B ≃⋆ₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/-
**StarAlgEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : A) : (e₁.trans e₂) x 
= e₂ (e₁ x)
参数：e₁ : A ≃⋆ₐ[R] B；e₂ : B ≃⋆ₐ[R] C；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : A ≃⋆ₐ[R] B) (e₂ : B ≃⋆ₐ[R] C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl
/-
**StarAlgEquiv.leftInverse_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：leftInverse_symm (e : A ≃⋆ₐ[R] B) : Function.LeftInverse e.symm e
参数：e : A ≃⋆ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem leftInverse_symm (e : A ≃⋆ₐ[R] B) : Function.LeftInverse e.symm e :=
  e.left_inv
/-
**StarAlgEquiv.rightInverse_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：rightInverse_symm (e : A ≃⋆ₐ[R] B) : Function.RightInverse e.symm e
参数：e : A ≃⋆ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem rightInverse_symm (e : A ≃⋆ₐ[R] B) : Function.RightInverse e.symm e :=
  e.right_inv

section AlgEquiv
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [Star A] [Star B]

/-- Interpret a ⋆-algebra equivalence as an algebra equivalence. -/
/-
**StarAlgEquiv.toAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：toAlgEquiv (f : A ≃⋆ₐ[R] B) : A ≃ₐ[R] B where toRingEquiv
参数：f : A ≃⋆ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a ⋆-algebra equivalence as an algebra equivalence.
-/
def toAlgEquiv (f : A ≃⋆ₐ[R] B) : A ≃ₐ[R] B where
  toRingEquiv := f.toRingEquiv
  commutes' r := by simp_rw [Algebra.algebraMap_eq_smul_one', map_smul']; simp

@[simp]
/-
**StarAlgEquiv.toAlgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toAlgEquiv_symm (f : A ≃⋆ₐ[R] B) : f.symm.toAlgEquiv = f.toAlgEquiv.symm
参数：f : A ≃⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgEquiv_symm (f : A ≃⋆ₐ[R] B) : f.symm.toAlgEquiv = f.toAlgEquiv.symm := rfl

@[simp]
/-
**StarAlgEquiv.coe_toAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：coe_toAlgEquiv (f : A ≃⋆ₐ[R] B) : ⇑f.toAlgEquiv = ⇑f
参数：f : A ≃⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAlgEquiv (f : A ≃⋆ₐ[R] B) : ⇑f.toAlgEquiv = ⇑f := rfl

@[simp]
/-
**StarAlgEquiv.coe_symm_toAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：coe_symm_toAlgEquiv (f : A ≃⋆ₐ[R] B) : ⇑f.toAlgEquiv.symm = ⇑f.symm
参数：f : A ≃⋆ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toAlgEquiv (f : A ≃⋆ₐ[R] B) : ⇑f.toAlgEquiv.symm = ⇑f.symm := rfl

@[simp]
/-
**StarAlgEquiv.toAlgEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toAlgEquiv_trans {C : Type*} [Semiring C] [Algebra R C] [Star C] (f : A ≃⋆
ₐ[R] B) (g : B ≃⋆ₐ[R] C) : (f.trans g).toAlgEquiv = f.toAlgEquiv.trans g.toAlgEq
uiv
参数：f : A ≃⋆ₐ[R] B；g : B ≃⋆ₐ[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgEquiv_trans {C : Type*} [Semiring C] [Algebra R C] [Star C] (f : A ≃⋆ₐ[R] B)
    (g : B ≃⋆ₐ[R] C) : (f.trans g).toAlgEquiv = f.toAlgEquiv.trans g.toAlgEquiv := rfl
/-
**StarAlgEquiv.toAlgEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toAlgEquiv_injective : Function.Injective (toAlgEquiv (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgEquiv.ext`：ext {f g : A ≃⋆ₐ[R] B} (h : forall a, f a = g a) : f =
 g
· 使用定理 `AlgEquiv.congr_fun`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
theorem toAlgEquiv_injective : Function.Injective (toAlgEquiv (R := R) (A := A) (B := B)) :=
  fun _ _ h => ext <| AlgEquiv.congr_fun h

@[simp]
/-
**StarAlgEquiv.toAlgEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toAlgEquiv_refl : (StarAlgEquiv.refl R A).toAlgEquiv = AlgEquiv.refl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgEquiv_refl : (StarAlgEquiv.refl R A).toAlgEquiv = AlgEquiv.refl := rfl

/-- Upgrade an algebra equivalence to a ⋆-algebra equivalence given that it preserves the
`star` operation. -/
/-
**StarAlgEquiv.ofAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：ofAlgEquiv (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = star (f x)) 
: A ≃⋆ₐ[R] B where toRingEquiv
参数：f : A ≃ₐ[R] B；map_star : forall x, f (star x) = star (f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upgrade an algebra equivalence to a ⋆-algebra equivalence given that it preserve
s the
`star` operation.
-/
def ofAlgEquiv (f : A ≃ₐ[R] B) (map_star : ∀ x, f (star x) = star (f x)) :
    A ≃⋆ₐ[R] B where
  toRingEquiv := f.toRingEquiv
  map_smul' := f.toLinearEquiv.map_smul
  map_star' := map_star

@[simp]
/-
**StarAlgEquiv.ofAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：ofAlgEquiv_apply (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = star (
f x)) (x : A) : ofAlgEquiv f map_star x = f x
参数：f : A ≃ₐ[R] B；map_star : forall x, f (star x) = star (f x)；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAlgEquiv_apply (f : A ≃ₐ[R] B) (map_star : ∀ x, f (star x) = star (f x)) (x : A) :
    ofAlgEquiv f map_star x = f x := rfl

@[simp]
/-
**StarAlgEquiv.ofAlgEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：ofAlgEquiv_symm (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = star (f
 x)) : (ofAlgEquiv f map_star).symm = ofAlgEquiv f.symm (ofAlgEquiv f map_star).
symm.map_star'
参数：f : A ≃ₐ[R] B；map_star : forall x, f (star x) = star (f x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAlgEquiv_symm (f : A ≃ₐ[R] B) (map_star : ∀ x, f (star x) = star (f x)) :
    (ofAlgEquiv f map_star).symm = ofAlgEquiv f.symm (ofAlgEquiv f map_star).symm.map_star' :=
  rfl

@[simp]
/-
**StarAlgEquiv.toAlgEquiv_ofAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toAlgEquiv_ofAlgEquiv (f : A ≃ₐ[R] B) (map_star : forall x, f (star x) = s
tar (f x)) : (ofAlgEquiv f map_star).toAlgEquiv = f
参数：f : A ≃ₐ[R] B；map_star : forall x, f (star x) = star (f x)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgEquiv_ofAlgEquiv (f : A ≃ₐ[R] B) (map_star : ∀ x, f (star x) = star (f x)) :
    (ofAlgEquiv f map_star).toAlgEquiv = f := rfl

@[simp]
/-
**StarAlgEquiv.ofAlgEquiv_toAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：ofAlgEquiv_toAlgEquiv (f : A ≃⋆ₐ[R] B) (map_star) : ofAlgEquiv f.toAlgEqui
v map_star = f
参数：f : A ≃⋆ₐ[R] B；map_star。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**StarAlgEquiv.toNonUnitalStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：toNonUnitalStarAlgHom : A₁ ->⋆ₙₐ[R] A₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reintrepret a star algebra equivalence as a non-unital star algebra homomorphism
.
-/
def toNonUnitalStarAlgHom : A₁ →⋆ₙₐ[R] A₂ :=
  { e with
    toFun := e
    map_zero' := map_zero e }

@[simp]
/-
**StarAlgEquiv.toNonUnitalStarAlgHom_refl** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEqui
v`。
形式化陈述：toNonUnitalStarAlgHom_refl : (StarAlgEquiv.refl R A₁).toNonUnitalStarAlgHo
m = .id R A₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNonUnitalStarAlgHom_refl : (StarAlgEquiv.refl R A₁).toNonUnitalStarAlgHom = .id R A₁ :=
  rfl

@[simp]
/-
**StarAlgEquiv.toNonUnitalStarAlgHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEqui
v`。
形式化陈述：toNonUnitalStarAlgHom_comp (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃) : e₂.to
NonUnitalStarAlgHom.comp e₁.toNonUnitalStarAlgHom = (e₁.trans e₂).toNonUnitalSta
rAlgHom
参数：e₁ : A₁ ≃⋆ₐ[R] A₂；e₂ : A₂ ≃⋆ₐ[R] A₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNonUnitalStarAlgHom_comp (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃) :
    e₂.toNonUnitalStarAlgHom.comp e₁.toNonUnitalStarAlgHom =
      (e₁.trans e₂).toNonUnitalStarAlgHom := rfl

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'` as star algebras, then the type
of maps `A₁ →⋆ₙₐ[R] A₂` is equivalent to the type of maps `A₁' →⋆ₙₐ[R] A₂'`.

For unital star algebra homomorphisms, see `StarAlgEquiv.arrowCongr`. -/
@[simps apply]
/-
**StarAlgEquiv.arrowCongr'** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：arrowCongr' (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') : (A₁ ->⋆ₙₐ[R] A₂) ≃
 (A₁' ->⋆ₙₐ[R] A₂') where toFun f
参数：e₁ : A₁ ≃⋆ₐ[R] A₁'；e₂ : A₂ ≃⋆ₐ[R] A₂'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'` as star algebras,
 then the type
of maps `A₁ →⋆ₙₐ[R] A₂` is equivalent to the type of maps `A₁' →⋆ₙₐ[R] A₂'`.

For unital star algebra homomorphisms, see `StarAlgEquiv.arrowCongr`.
-/
def arrowCongr' (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (A₁ →⋆ₙₐ[R] A₂) ≃ (A₁' →⋆ₙₐ[R] A₂') where
  toFun f := (e₂.toNonUnitalStarAlgHom.comp f).comp e₁.symm.toNonUnitalStarAlgHom
  invFun f := (e₂.symm.toNonUnitalStarAlgHom.comp f).comp e₁.toNonUnitalStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp
/-
**StarAlgEquiv.arrowCongr'_comp** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：∀ {R : Type u_1} {A₁ : Type u_2} {A₂ : Type u_3} {A₃ : Type u_4} {A₁' : Ty
pe u_5} {A₂' : Type u_6} {A₃' : Type u_7}   [inst : Monoid R] [inst_1 : NonUnita
lNonAssocSemiring A₁] [inst_2 : DistribMulAction R A₁] [inst_3 : Star A₁]   [ins
t_4 : NonUnitalNonAssocSemiring A₂] [inst_5 : DistribMulAction R A₂] [inst_6 : S
tar A₂]   [inst_7 : NonUnitalNonAssocSemiring A₃] [inst_8 : DistribMulAction R A
₃] [inst_9 : Star A₃]   [inst_10 : NonUnitalNonAssocSemiring A₁'] [inst_11 : Dis
tribMulAction R A₁'] [inst_12 : Star A₁']   [inst_13 : NonUnitalNonAssocSemiring
 A₂'] [inst_14 : DistribMulAction R A₂'] [inst_15 : Star A₂']   [inst_16 : NonUn
italNonAssocSemiring A₃'] [inst_17 : DistribMulAction R A₃'] [inst_18 : Star A₃'
] (e₁ : A₁ ≃⋆ₐ[R] A₁')   (e₂ : A₂ ≃⋆ₐ[R] A₂') (e₃ : A₃ ≃⋆ₐ[R] A₃') (f : A₁ →⋆ₙₐ[
R] A₂) (g : A₂ →⋆ₙₐ[R] A₃),   (e₁.arrowCongr' e₃) (g.comp f) = ((e₂.arrowCongr' 
e₃) g).comp ((e₁.arrowCongr' e₂) f)
参数：e₁ : A₁ ≃⋆ₐ[R] A₁'；e₂ : A₂ ≃⋆ₐ[R] A₂'；e₃ : A₃ ≃⋆ₐ[R] A₃'；f : A₁ →⋆ₙₐ[R] A₂；g 
: A₂ →⋆ₙₐ[R] A₃；e₁.arrowCongr' e₃；g.comp f；(e₂.arrowCongr' e₃) g；(e₁.arrowCongr'
 e₂) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.ext`：ext {f g : A ->⋆ₙₐ[R] B} (h : forall x, f x = g
 x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarAlgEquiv.arrowCongr'_apply`：∀ {R : Type u_1} {A₁ : Type u_2} {A₂ : T
ype u_3} {A₁' : Type u_5} {A₂' : Type u_6} [inst : Monoid R]   [inst_1 : NonUnit
alNonAssocSemiring A…
· 使用定理 `StarAlgEquiv.toNonUnitalStarAlgHom_apply`：∀ {R : Type u_1} {A₁ : Type u_
2} {A₂ : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A₁]   [
inst_2 : DistribMulAction R A₁…
· 使用定理 `StarAlgEquiv.symm_apply_apply`：symm_apply_apply (e : A ≃⋆ₐ[R] B) : foral
l x, e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arrowCongr'_comp (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
    (e₃ : A₃ ≃⋆ₐ[R] A₃') (f : A₁ →⋆ₙₐ[R] A₂) (g : A₂ →⋆ₙₐ[R] A₃) :
    arrowCongr' e₁ e₃ (g.comp f) = (arrowCongr' e₂ e₃ g).comp (arrowCongr' e₁ e₂ f) := by
  ext
  simp

@[simp]
/-
**StarAlgEquiv.arrowCongr'_refl** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：∀ {R : Type u_1} {A₁ : Type u_2} {A₂ : Type u_3} [inst : Monoid R] [inst_1
 : NonUnitalNonAssocSemiring A₁]   [inst_2 : DistribMulAction R A₁] [inst_3 : St
ar A₁] [inst_4 : NonUnitalNonAssocSemiring A₂]   [inst_5 : DistribMulAction R A₂
] [inst_6 : Star A₂],   (StarAlgEquiv.refl R A₁).arrowCongr' (StarAlgEquiv.refl 
R A₂) = Equiv.refl (A₁ →⋆ₙₐ[R] A₂)
参数：StarAlgEquiv.refl R A₁；StarAlgEquiv.refl R A₂；A₁ →⋆ₙₐ[R] A₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr'_refl : arrowCongr' (.refl _ _) (.refl _ _) = Equiv.refl (A₁ →⋆ₙₐ[R] A₂) :=
  rfl

@[simp]
/-
**StarAlgEquiv.arrowCongr'_trans** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：∀ {R : Type u_1} {A₁ : Type u_2} {A₂ : Type u_3} {A₃ : Type u_4} {A₁' : Ty
pe u_5} {A₂' : Type u_6} {A₃' : Type u_7}   [inst : Monoid R] [inst_1 : NonUnita
lNonAssocSemiring A₁] [inst_2 : DistribMulAction R A₁] [inst_3 : Star A₁]   [ins
t_4 : NonUnitalNonAssocSemiring A₂] [inst_5 : DistribMulAction R A₂] [inst_6 : S
tar A₂]   [inst_7 : NonUnitalNonAssocSemiring A₃] [inst_8 : DistribMulAction R A
₃] [inst_9 : Star A₃]   [inst_10 : NonUnitalNonAssocSemiring A₁'] [inst_11 : Dis
tribMulAction R A₁'] [inst_12 : Star A₁']   [inst_13 : NonUnitalNonAssocSemiring
 A₂'] [inst_14 : DistribMulAction R A₂'] [inst_15 : Star A₂']   [inst_16 : NonUn
italNonAssocSemiring A₃'] [inst_17 : DistribMulAction R A₃'] [inst_18 : Star A₃'
] (e₁ : A₁ ≃⋆ₐ[R] A₂)   (e₁' : A₁' ≃⋆ₐ[R] A₂') (e₂ : A₂ ≃⋆ₐ[R] A₃) (e₂' : A₂' ≃⋆
ₐ[R] A₃'),   (e₁.trans e₂).arrowCongr' (e₁'.trans e₂') = (e₁.arrowCongr' e₁').tr
ans (e₂.arrowCongr' e₂')
参数：e₁ : A₁ ≃⋆ₐ[R] A₂；e₁' : A₁' ≃⋆ₐ[R] A₂'；e₂ : A₂ ≃⋆ₐ[R] A₃；e₂' : A₂' ≃⋆ₐ[R] A₃'
；e₁.trans e₂；e₁'.trans e₂'；e₁.arrowCongr' e₁'；e₂.arrowCongr' e₂'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr'_trans (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
    (e₂ : A₂ ≃⋆ₐ[R] A₃) (e₂' : A₂' ≃⋆ₐ[R] A₃') :
    arrowCongr' (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr' e₁ e₁').trans (arrowCongr' e₂ e₂') :=
  rfl

@[simp]
/-
**StarAlgEquiv.symm_arrowCongr'** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：symm_arrowCongr' (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') : (arrowCongr' 
e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm
参数：e₁ : A₁ ≃⋆ₐ[R] A₁'；e₂ : A₂ ≃⋆ₐ[R] A₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_arrowCongr' (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (arrowCongr' e₁ e₂).symm = arrowCongr' e₁.symm e₂.symm :=
  rfl

/-- Construct a star algebra equivalence from a pair of non-unital star algebra homomorphisms. -/
@[simps]
/-
**StarAlgEquiv.ofNonUnitalStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：ofNonUnitalStarAlgHom (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁) (h₁ : g.co
mp f = .id R A₁) (h₂ : f.comp g = .id R A₂) : A₁ ≃⋆ₐ[R] A₂
参数：f : A₁ ->⋆ₙₐ[R] A₂；g : A₂ ->⋆ₙₐ[R] A₁；h₁ : g.comp f = .id R A₁；h₂ : f.comp g 
= .id R A₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.map_star'`：∀ {R : Type u_1} {A : Type u_2} {B : Type
 u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : Distr
ibMulAction R A] [i…

--- 原说明 ---
Construct a star algebra equivalence from a pair of non-unital star algebra homo
morphisms.
-/
def ofNonUnitalStarAlgHom (f : A₁ →⋆ₙₐ[R] A₂) (g : A₂ →⋆ₙₐ[R] A₁) (h₁ : g.comp f = .id R A₁)
    (h₂ : f.comp g = .id R A₂) : A₁ ≃⋆ₐ[R] A₂ :=
  { f with
    toFun := f
    invFun := g
    left_inv x := congr($h₁ x)
    right_inv x := congr($h₂ x) }

@[simp]
/-
**StarAlgEquiv.toNonUnitalStarAlgHom_ofNonUnitalStarAlgHom** 是 Mathlib 中的一个引理，位于
命名空间 `StarAlgEquiv`。
形式化陈述：toNonUnitalStarAlgHom_ofNonUnitalStarAlgHom (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ -
>⋆ₙₐ[R] A₁) (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) : (ofNonUnital
StarAlgHom f g h₁ h₂).toNonUnitalStarAlgHom = f
参数：f : A₁ ->⋆ₙₐ[R] A₂；g : A₂ ->⋆ₙₐ[R] A₁；h₁ : g.comp f = .id R A₁；h₂ : f.comp g 
= .id R A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNonUnitalStarAlgHom_ofNonUnitalStarAlgHom (f : A₁ →⋆ₙₐ[R] A₂) (g : A₂ →⋆ₙₐ[R] A₁)
    (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) :
    (ofNonUnitalStarAlgHom f g h₁ h₂).toNonUnitalStarAlgHom = f :=
  rfl
/-
**StarAlgEquiv.symm_ofNonUnitalStarAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEqui
v`。
形式化陈述：symm_ofNonUnitalStarAlgHom (f : A₁ ->⋆ₙₐ[R] A₂) (g : A₂ ->⋆ₙₐ[R] A₁) (h₁ :
 g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) : (ofNonUnitalStarAlgHom f g h₁
 h₂).symm = ofNonUnitalStarAlgHom g f h₂ h₁
参数：f : A₁ ->⋆ₙₐ[R] A₂；g : A₂ ->⋆ₙₐ[R] A₁；h₁ : g.comp f = .id R A₁；h₂ : f.comp g 
= .id R A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_ofNonUnitalStarAlgHom (f : A₁ →⋆ₙₐ[R] A₂) (g : A₂ →⋆ₙₐ[R] A₁)
    (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) :
    (ofNonUnitalStarAlgHom f g h₁ h₂).symm = ofNonUnitalStarAlgHom g f h₂ h₁ :=
  rfl

@[simp]
/-
**StarAlgEquiv.toNonUnitalStarAlgHom_symm_ofNonUnitalStarAlgHom** 是 Mathlib 中的一个
引理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toNonUnitalStarAlgHom_symm_ofNonUnitalStarAlgHom (f : A₁ ->⋆ₙₐ[R] A₂) (g :
 A₂ ->⋆ₙₐ[R] A₁) (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) : (ofNonU
nitalStarAlgHom f g h₁ h₂).symm.toNonUnitalStarAlgHom = g
参数：f : A₁ ->⋆ₙₐ[R] A₂；g : A₂ ->⋆ₙₐ[R] A₁；h₁ : g.comp f = .id R A₁；h₂ : f.comp g 
= .id R A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNonUnitalStarAlgHom_symm_ofNonUnitalStarAlgHom (f : A₁ →⋆ₙₐ[R] A₂) (g : A₂ →⋆ₙₐ[R] A₁)
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
/-
**StarAlgEquiv.toStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：toStarAlgHom : A₁ ->⋆ₐ[R] A₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…

--- 原说明 ---
Reintrepret a star algebra equivalence as a star algebra homomorphism.
-/
def toStarAlgHom : A₁ →⋆ₐ[R] A₂ :=
  { e with
    toFun := e
    __ := e.toAlgEquiv.toAlgHom }

@[simp]
/-
**StarAlgEquiv.toNonUnitalStarAlgHom_toStarAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `Sta
rAlgEquiv`。
形式化陈述：toNonUnitalStarAlgHom_toStarAlgHom (e : A₁ ≃⋆ₐ[R] A₂) : e.toStarAlgHom.toN
onUnitalStarAlgHom = e.toNonUnitalStarAlgHom
参数：e : A₁ ≃⋆ₐ[R] A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNonUnitalStarAlgHom_toStarAlgHom (e : A₁ ≃⋆ₐ[R] A₂) :
    e.toStarAlgHom.toNonUnitalStarAlgHom = e.toNonUnitalStarAlgHom :=
  rfl

@[simp]
/-
**StarAlgEquiv.toStarAlgHom_refl** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toStarAlgHom_refl : (StarAlgEquiv.refl R A₁).toStarAlgHom = .id R A₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toStarAlgHom_refl : (StarAlgEquiv.refl R A₁).toStarAlgHom = .id R A₁ :=
  rfl

@[simp]
/-
**StarAlgEquiv.toStarAlgHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEquiv`。
形式化陈述：toStarAlgHom_comp (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃) : e₂.toStarAlgHo
m.comp e₁.toStarAlgHom = (e₁.trans e₂).toStarAlgHom
参数：e₁ : A₁ ≃⋆ₐ[R] A₂；e₂ : A₂ ≃⋆ₐ[R] A₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toStarAlgHom_comp (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₂ : A₂ ≃⋆ₐ[R] A₃) :
    e₂.toStarAlgHom.comp e₁.toStarAlgHom = (e₁.trans e₂).toStarAlgHom := rfl

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'` as star algebras, then the type
of maps `A₁ →⋆ₐ[R] A₂` is equivalent to the type of maps `A₁' →⋆ₐ[R] A₂'`.

For non-unital star algebra homomorphisms, see `StarAlgEquiv.arrowCongr'`. -/
@[simps apply]
/-
**StarAlgEquiv.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：arrowCongr (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') : (A₁ ->⋆ₐ[R] A₂) ≃ (
A₁' ->⋆ₐ[R] A₂') where toFun f
参数：e₁ : A₁ ≃⋆ₐ[R] A₁'；e₂ : A₂ ≃⋆ₐ[R] A₂'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'` as star algebras,
 then the type
of maps `A₁ →⋆ₐ[R] A₂` is equivalent to the type of maps `A₁' →⋆ₐ[R] A₂'`.

For non-unital star algebra homomorphisms, see `StarAlgEquiv.arrowCongr'`.
-/
def arrowCongr (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') : (A₁ →⋆ₐ[R] A₂) ≃ (A₁' →⋆ₐ[R] A₂') where
  toFun f := (e₂.toStarAlgHom.comp f).comp e₁.symm.toStarAlgHom
  invFun f := (e₂.symm.toStarAlgHom.comp f).comp e₁.toStarAlgHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp
/-
**StarAlgEquiv.arrowCongr_comp** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：arrowCongr_comp (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') (e₃ : A₃ ≃⋆ₐ[R] 
A₃') (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₃) : arrowCongr e₁ e₃ (g.comp f) = (ar
rowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f)
参数：e₁ : A₁ ≃⋆ₐ[R] A₁'；e₂ : A₂ ≃⋆ₐ[R] A₂'；e₃ : A₃ ≃⋆ₐ[R] A₃'；f : A₁ ->⋆ₐ[R] A₂；g 
: A₂ ->⋆ₐ[R] A₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.ext`：ext {f g : A ->⋆ₐ[R] B} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarAlgEquiv.arrowCongr_apply`：∀ {R : Type u_1} {A₁ : Type u_2} {A₂ : Ty
pe u_3} {A₁' : Type u_5} {A₂' : Type u_6} [inst : CommSemiring R]   [inst_1 : Se
miring A₁] [inst_2 …
· 使用定理 `StarAlgEquiv.toStarAlgHom_apply`：∀ {R : Type u_1} {A₁ : Type u_2} {A₂ : 
Type u_3} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂] 
  [inst_3 : Algebra R…
· 使用定理 `StarAlgEquiv.symm_apply_apply`：symm_apply_apply (e : A ≃⋆ₐ[R] B) : foral
l x, e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arrowCongr_comp (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂')
    (e₃ : A₃ ≃⋆ₐ[R] A₃') (f : A₁ →⋆ₐ[R] A₂) (g : A₂ →⋆ₐ[R] A₃) :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp

@[simp]
/-
**StarAlgEquiv.arrowCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：arrowCongr_refl : arrowCongr (.refl _ _) (.refl _ _) = Equiv.refl (A₁ ->⋆ₐ
[R] A₂)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr_refl : arrowCongr (.refl _ _) (.refl _ _) = Equiv.refl (A₁ →⋆ₐ[R] A₂) :=
  rfl

@[simp]
/-
**StarAlgEquiv.arrowCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：arrowCongr_trans (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂') (e₂ : A₂ ≃⋆ₐ[R
] A₃) (e₂' : A₂' ≃⋆ₐ[R] A₃') : arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrow
Congr e₁ e₁').trans (arrowCongr e₂ e₂')
参数：e₁ : A₁ ≃⋆ₐ[R] A₂；e₁' : A₁' ≃⋆ₐ[R] A₂'；e₂ : A₂ ≃⋆ₐ[R] A₃；e₂' : A₂' ≃⋆ₐ[R] A₃'
。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr_trans (e₁ : A₁ ≃⋆ₐ[R] A₂) (e₁' : A₁' ≃⋆ₐ[R] A₂')
    (e₂ : A₂ ≃⋆ₐ[R] A₃) (e₂' : A₂' ≃⋆ₐ[R] A₃') :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') :=
  rfl

@[simp]
/-
**StarAlgEquiv.symm_arrowCongr** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：symm_arrowCongr (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') : (arrowCongr e₁
 e₂).symm = arrowCongr e₁.symm e₂.symm
参数：e₁ : A₁ ≃⋆ₐ[R] A₁'；e₂ : A₂ ≃⋆ₐ[R] A₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_arrowCongr (e₁ : A₁ ≃⋆ₐ[R] A₁') (e₂ : A₂ ≃⋆ₐ[R] A₂') :
    (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm :=
  rfl

/-- Construct a star algebra equivalence from a pair of star algebra homomorphisms. -/
@[simps]
/-
**StarAlgEquiv.ofStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：ofStarAlgHom {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [
Star A] [Semiring B] [Algebra R B] [Star B] (f : A ->⋆ₐ[R] B) (g : B ->⋆ₐ[R] A) 
(h₁ : g.comp f = .id R A) (h₂ : f.comp g = .id R B) : A ≃⋆ₐ[R] B
参数：f : A ->⋆ₐ[R] B；g : B ->⋆ₐ[R] A；h₁ : g.comp f = .id R A；h₂ : f.comp g = .id R
 B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgHom.map_star'`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [in
st : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : St
ar A] [ins…

--- 原说明 ---
Construct a star algebra equivalence from a pair of star algebra homomorphisms.
-/
def ofStarAlgHom {R A B : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    (f : A →⋆ₐ[R] B) (g : B →⋆ₐ[R] A) (h₁ : g.comp f = .id R A) (h₂ : f.comp g = .id R B) :
    A ≃⋆ₐ[R] B :=
  { f with
    toFun := f
    invFun := g
    left_inv x := congr($h₁ x)
    right_inv x := congr($h₂ x)
    map_smul' := map_smul f }

@[simp]
/-
**StarAlgEquiv.toStarAlgHom_ofStarAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEquiv
`。
形式化陈述：toStarAlgHom_ofStarAlgHom (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁) (h₁ : g.
comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) : (ofStarAlgHom f g h₁ h₂).toStarA
lgHom = f
参数：f : A₁ ->⋆ₐ[R] A₂；g : A₂ ->⋆ₐ[R] A₁；h₁ : g.comp f = .id R A₁；h₂ : f.comp g = 
.id R A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toStarAlgHom_ofStarAlgHom (f : A₁ →⋆ₐ[R] A₂) (g : A₂ →⋆ₐ[R] A₁)
    (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) :
    (ofStarAlgHom f g h₁ h₂).toStarAlgHom = f :=
  rfl
/-
**StarAlgEquiv.symm_ofStarAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEquiv`。
形式化陈述：symm_ofStarAlgHom (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁) (h₁ : g.comp f =
 .id R A₁) (h₂ : f.comp g = .id R A₂) : (ofStarAlgHom f g h₁ h₂).symm = ofStarAl
gHom g f h₂ h₁
参数：f : A₁ ->⋆ₐ[R] A₂；g : A₂ ->⋆ₐ[R] A₁；h₁ : g.comp f = .id R A₁；h₂ : f.comp g = 
.id R A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_ofStarAlgHom (f : A₁ →⋆ₐ[R] A₂) (g : A₂ →⋆ₐ[R] A₁)
    (h₁ : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) :
    (ofStarAlgHom f g h₁ h₂).symm = ofStarAlgHom g f h₂ h₁ :=
  rfl

@[simp]
/-
**StarAlgEquiv.toStarAlgHom_symm_ofStarAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `StarAlg
Equiv`。
形式化陈述：toStarAlgHom_symm_ofStarAlgHom (f : A₁ ->⋆ₐ[R] A₂) (g : A₂ ->⋆ₐ[R] A₁) (h₁
 : g.comp f = .id R A₁) (h₂ : f.comp g = .id R A₂) : (ofStarAlgHom f g h₁ h₂).sy
mm.toStarAlgHom = g
参数：f : A₁ ->⋆ₐ[R] A₂；g : A₂ ->⋆ₐ[R] A₁；h₁ : g.comp f = .id R A₁；h₂ : f.comp g = 
.id R A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toStarAlgHom_symm_ofStarAlgHom (f : A₁ →⋆ₐ[R] A₂) (g : A₂ →⋆ₐ[R] A₁)
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

/-- Promote a bijective star algebra homomorphism to a star algebra equivalence. -/
/-
**StarAlgEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgEquiv`。
形式化陈述：ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆ₐ[R] B
参数：f : F；hf : Function.Bijective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…

--- 原说明 ---
Promote a bijective star algebra homomorphism to a star algebra equivalence.
-/
noncomputable def ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆ₐ[R] B :=
  {
    RingEquiv.ofBijective f
      (hf : Function.Bijective (f : A → B)) with
    toFun := f
    map_star' := map_star f
    map_smul' := map_smul f }

@[simp]
/-
**StarAlgEquiv.coe_ofBijective** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：coe_ofBijective {f : F} (hf : Function.Bijective f) : (StarAlgEquiv.ofBije
ctive f hf : A -> B) = f
参数：hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofBijective {f : F} (hf : Function.Bijective f) :
    (StarAlgEquiv.ofBijective f hf : A → B) = f :=
  rfl
/-
**StarAlgEquiv.ofBijective_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) : (StarAlgEq
uiv.ofBijective f hf) a = f a
参数：hf : Function.Bijective f；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) :
    (StarAlgEquiv.ofBijective f hf) a = f a :=
  rfl

end Bijective

section Group
variable {S R : Type*} [Mul R] [Add R] [Star R] [SMul S R]

@[simps -isSimp one mul]
/-
**StarAlgEquiv.aut** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgEquiv`。
形式化陈述：aut : Group (R ≃⋆ₐ[S] R) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance aut : Group (R ≃⋆ₐ[S] R) where
  one := .refl _ _
  mul a b := b.trans a
  one_mul _ := rfl
  mul_one _ := rfl
  mul_assoc _ _ _ := rfl
  inv f := f.symm
  inv_mul_cancel f := ext <| symm_apply_apply f
/-
**StarAlgEquiv.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：∀ {S : Type u_1} {R : Type u_2} [inst : Mul R] [inst_1 : Add R] [inst_2 : 
Star R] [inst_3 : SMul S R] (f g : R ≃⋆ₐ[S] R)   (x : R), (f * g) x = f (g x)
参数：f g : R ≃⋆ₐ[S] R；x : R；f * g；g x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mul_apply (f g : R ≃⋆ₐ[S] R) (x : R) : (f * g) x = f (g x) := rfl
/-
**StarAlgEquiv.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：∀ {S : Type u_1} {R : Type u_2} [inst : Mul R] [inst_1 : Add R] [inst_2 : 
Star R] [inst_3 : SMul S R] (x : R), 1 x = x
参数：x : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem one_apply (x : R) : (1 : R ≃⋆ₐ[S] R) x = x := rfl
/-
**StarAlgEquiv.aut_inv** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：aut_inv (f : R ≃⋆ₐ[S] R) : f⁻¹ = f.symm
参数：f : R ≃⋆ₐ[S] R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aut_inv (f : R ≃⋆ₐ[S] R) : f⁻¹ = f.symm := rfl
/-
**StarAlgEquiv.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgEquiv`。
形式化陈述：∀ {S : Type u_1} {R : Type u_2} [inst : Mul R] [inst_1 : Add R] [inst_2 : 
Star R] [inst_3 : SMul S R] (f : R ≃⋆ₐ[S] R)   (n : ℕ), ⇑(f ^ n) = (⇑f)^[n]
参数：f : R ≃⋆ₐ[S] R；n : ℕ；f ^ n；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hom_coe_pow`：∀ {M : Type u_4} {F : Type u_5} [inst : Monoid F] (c : F → 
M → M),   c 1 = id → (∀ (f g : F), c (f * g) = c f ∘ c g) → ∀ (f : F) (n : ℕ), c
 …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `StarAlgEquiv.one_apply`：∀ {S : Type u_1} {R : Type u_2} [inst : Mul R] [
inst_1 : Add R] [inst_2 : Star R] [inst_3 : SMul S R] (x : R), 1 x = x
· 使用定理 `StarAlgEquiv.mul_apply`：∀ {S : Type u_1} {R : Type u_2} [inst : Mul R] [
inst_1 : Add R] [inst_2 : Star R] [inst_3 : SMul S R] (f g : R ≃⋆ₐ[S] R)   (x : 
R), (f * g) …
-/
@[simp] theorem coe_pow (f : R ≃⋆ₐ[S] R) (n : ℕ) :
    ⇑(f ^ n) = (⇑f)^[n] :=
  hom_coe_pow _ (funext one_apply) (fun f g ↦ funext <| mul_apply f g) _ _

end Group

end StarAlgEquiv

