/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic

/-!
# Morphisms of star rings

This file defines a new type of morphism between (non-unital) rings `A` and `B` where both
`A` and `B` are equipped with a `star` operation. This morphism, namely `NonUnitalStarRingHom`, is
a direct extension of its non-`star`red counterpart with a field `map_star` which guarantees it
preserves the star operation.

As with `NonUnitalRingHom`, the multiplications are not assumed to be associative or unital.

## Main definitions

  * `NonUnitalStarRingHom`

## Implementation

This file is heavily inspired by `Mathlib/Algebra/Star/StarAlgHom.lean`.

## Tags

non-unital, ring, morphism, star
-/

@[expose] public section

open EquivLike

/-! ### Non-unital star ring homomorphisms -/

/--
Definition of `NonUnitalStarRingHom` / `NonUnitalStarRingHom` 的定义

English:
structure NonUnitalStarRingHom
  parameters: (A B : Type*) [NonUnitalNonAssocSemiring A]
  extends: A ->ₙ+* B
  axioms and operations (1):
    - map_star' : forall a : A, toFun (star a) = star (toFun a)

中文:
结构 非幺对合环态射
  参数: (A B : 类型) [非幺非结合半环 A]
  继承: A ->ₙ+* B
  公理与运算 (1 个):
    - map_star' : 对任意 a : A, toFun (star a) = star (toFun a)
-/
structure NonUnitalStarRingHom (A B : Type*) [NonUnitalNonAssocSemiring A]
    [Star A] [NonUnitalNonAssocSemiring B] [Star B] extends A ->ₙ+* B where
  /-- By definition, a non-unital ⋆-ring homomorphism preserves the `star` operation. -/
  map_star' : forall a : A, toFun (star a) = star (toFun a)

/-- `α →⋆ₙ+* β` denotes the type of non-unital ring homomorphisms from `α` to `β`. -/
infixr:25 " ->⋆ₙ+* " => NonUnitalStarRingHom

/-- Reinterpret a non-unital star ring homomorphism as a non-unital ring homomorphism
by forgetting the interaction with the star operation.

Users should not make use of this, but instead utilize the coercion obtained through
the `NonUnitalRingHomClass` instance. -/
add_decl_doc NonUnitalStarRingHom.toNonUnitalRingHom

/--
Definition of `NonUnitalStarRingHomClass` / `NonUnitalStarRingHomClass` 的定义

English:
class NonUnitalStarRingHomClass
  parameters: (F : Type*) (A B : outParam Type*)
  extends: StarHomClass F A B
  (no additional axioms)

中文:
类 非幺对合环态射类
  参数: (F : 类型) (A B : outParam 类型)
  继承: 对合态射类 F A B
  (无附加公理)
-/
class NonUnitalStarRingHomClass (F : Type*) (A B : outParam Type*)
    [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] : Prop extends StarHomClass F A B

namespace NonUnitalStarRingHomClass

variable {F A B : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [FunLike F A B] [NonUnitalRingHomClass F A B]

/-- Turn an element of a type `F` satisfying `NonUnitalStarRingHomClass F A B` into an actual
`NonUnitalStarRingHom`. This is declared as the default coercion from `F` to `A →⋆ₙ+ B`. -/
@[coe]
/--
Definition of `toNonUnitalStarRingHom` / `toNonUnitalStarRingHom` 的定义

English:
definition toNonUnitalStarRingHom
  signature: [NonUnitalStarRingHomClass F A B] (f : F)
  body: { (f : A ->ₙ+* B) with
    map_star' := map_star f }

中文:
定义 toNonUnitalStarRingHom
  签名: [非幺对合环态射类 F A B] (f : F)
  定义体: { (f : A ->ₙ+* B) with
    map_star' := map_star f }

Depends on / 依赖: map_star
-/
def toNonUnitalStarRingHom [NonUnitalStarRingHomClass F A B] (f : F) : A ->⋆ₙ+* B :=
  { (f : A ->ₙ+* B) with
    map_star' := map_star f }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalStarRingHomClass
  signature: F A B] : CoeHead F (A ->⋆ₙ+* B)
  body: ⟨toNonUnitalStarRingHom⟩

中文:
实例 [非幺对合环态射类
  签名: F A B] : CoeHead F (A ->⋆ₙ+* B)
  定义体: ⟨toNonUnitalStarRingHom⟩

Depends on / 依赖: toNonUnitalStarRingHom
-/
instance [NonUnitalStarRingHomClass F A B] : CoeHead F (A ->⋆ₙ+* B) :=
  ⟨toNonUnitalStarRingHom⟩

end NonUnitalStarRingHomClass

namespace NonUnitalStarRingHom

section Basic

variable {A B C D : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Star C]
variable [NonUnitalNonAssocSemiring D] [Star D]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ->⋆ₙ+* B) A B
  body: f.toFun
  coe_injective := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

中文:
实例 :
  签名: 函数状 (A ->⋆ₙ+* B) A B
  定义体: f.toFun
  coe_injective := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (A ->⋆ₙ+* B) A B where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalRingHomClass (A ->⋆ₙ+* B) A B
  body: f.map_mul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

中文:
实例 :
  签名: 非幺环态射类 (A ->⋆ₙ+* B) A B
  定义体: f.map_mul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

Depends on / 依赖: f.map_mul, map_mul
-/
instance : NonUnitalRingHomClass (A ->⋆ₙ+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalStarRingHomClass (A ->⋆ₙ+* B) A B
  body: f.map_star'

中文:
实例 :
  签名: 非幺对合环态射类 (A ->⋆ₙ+* B) A B
  定义体: f.map_star'

Depends on / 依赖: f.map_star, map_star
-/
instance : NonUnitalStarRingHomClass (A ->⋆ₙ+* B) A B where
  map_star f := f.map_star'

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (f : A ->⋆ₙ+* B)
  body: f

initialize_simps_projections NonUnitalStarRingHom (toFun -> apply)

@[simp]

中文:
定义 Simps.apply
  签名: (f : A ->⋆ₙ+* B)
  定义体: f

initialize_simps_projections NonUnitalStarRingHom (toFun -> apply)

@[simp]
-/
def Simps.apply (f : A ->⋆ₙ+* B) : A -> B := f

initialize_simps_projections NonUnitalStarRingHom (toFun -> apply)

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B]
  proof: rfl

@[simp]

中文:
定理 coe_coe
  结论: {F : 类型} [函数状 F A B] [非幺环态射类 F A B]
  证明: rfl

@[simp]
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B]
    [NonUnitalStarRingHomClass F A B] (f : F) : ⇑(f : A ->⋆ₙ+* B) = f :=
  rfl

@[simp]
/--
theorem `coe_toNonUnitalRingHom` / 定理 `coe_toNonUnitalRingHom`

English:
theorem coe_toNonUnitalRingHom
  given: (f : A ->⋆ₙ+* B)
  statement: ⇑f.toNonUnitalRingHom = f
  proof: rfl

@[ext]

中文:
定理 coe_toNonUnitalRingHom
  条件: (f : A ->⋆ₙ+* B)
  结论: ⇑f.toNonUnitalRingHom = f
  证明: rfl

@[ext]
-/
theorem coe_toNonUnitalRingHom (f : A ->⋆ₙ+* B) : ⇑f.toNonUnitalRingHom = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ->⋆ₙ+* B} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : A ->⋆ₙ+* B} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : A ->⋆ₙ+* B} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : A ->⋆ₙ+* B) (f' : A -> B) (h : f' = f)
  body: f'
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]

中文:
定义 copy
  签名: (f : A ->⋆ₙ+* B) (f' : A -> B) (h : f' = f)
  定义体: f'
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
-/
protected def copy (f : A ->⋆ₙ+* B) (f' : A -> B) (h : f' = f) : A ->⋆ₙ+* B where
  toFun := f'
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : A ->⋆ₙ+* B) (f' : A -> B) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : A ->⋆ₙ+* B) (f' : A -> B) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : A ->⋆ₙ+* B) (f' : A -> B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : A ->⋆ₙ+* B) (f' : A -> B) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

@[simp]

中文:
定理 copy_eq
  条件: (f : A ->⋆ₙ+* B) (f' : A -> B) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : A ->⋆ₙ+* B) (f' : A -> B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : A ->ₙ+* B) (h)
  statement: ((⟨f, h⟩ : A ->⋆ₙ+* B) : A -> B) = f
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (f : A ->ₙ+* B) (h)
  结论: ((⟨f, h⟩ : A ->⋆ₙ+* B) : A -> B) = f
  证明: rfl

@[simp]
-/
theorem coe_mk (f : A ->ₙ+* B) (h) : ((⟨f, h⟩ : A ->⋆ₙ+* B) : A -> B) = f := rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : A ->⋆ₙ+* B) (h₁ h₂ h₃ h₄)
  proof: by
  ext
  rfl

中文:
定理 mk_coe
  条件: (f : A ->⋆ₙ+* B) (h₁ h₂ h₃ h₄)
  证明: by
  ext
  rfl
-/
theorem mk_coe (f : A ->⋆ₙ+* B) (h₁ h₂ h₃ h₄) :
    (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->⋆ₙ+* B) = f := by
  ext
  rfl

section

variable (A)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : A ->⋆ₙ+* A
  body: { (1 : A ->ₙ+* A) with map_star' := fun _ => rfl }

@[simp, norm_cast]

中文:
定义 id
  签名: : A ->⋆ₙ+* A
  定义体: { (1 : A ->ₙ+* A) with map_star' := fun _ => rfl }

@[simp, norm_cast]
-/
protected def id : A ->⋆ₙ+* A :=
  { (1 : A ->ₙ+* A) with map_star' := fun _ => rfl }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(NonUnitalStarRingHom.id A) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(非幺对合环态射.id A) = id
  证明: rfl
-/
theorem coe_id : ⇑(NonUnitalStarRingHom.id A) = id :=
  rfl

end

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B)
  body: { f.toNonUnitalRingHom.comp g.toNonUnitalRingHom with
    map_star' := fun a => by simp [map_star, map_star] }

@[simp]

中文:
定义 comp
  签名: (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B)
  定义体: { f.toNonUnitalRingHom.comp g.toNonUnitalRingHom with
    map_star' := fun a => by simp [map_star, map_star] }

@[simp]

Depends on / 依赖: f.toNonUnitalRingHom.comp, g.toNonUnitalRingHom, map_star, toNonUnitalRingHom
-/
def comp (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B) : A ->⋆ₙ+* C :=
  { f.toNonUnitalRingHom.comp g.toNonUnitalRingHom with
    map_star' := fun a => by simp [map_star, map_star] }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B)
  statement: ⇑(comp f g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B)
  结论: ⇑(comp f g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B) (a : A)
  statement: comp f g a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B) (a : A)
  结论: comp f g a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : C ->⋆ₙ+* D) (g : B ->⋆ₙ+* C) (h : A ->⋆ₙ+* B)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : C ->⋆ₙ+* D) (g : B ->⋆ₙ+* C) (h : A ->⋆ₙ+* B)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : C ->⋆ₙ+* D) (g : B ->⋆ₙ+* C) (h : A ->⋆ₙ+* B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : A ->⋆ₙ+* B)
  statement: (NonUnitalStarRingHom.id _).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : A ->⋆ₙ+* B)
  结论: (非幺对合环态射.id _).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : A ->⋆ₙ+* B) : (NonUnitalStarRingHom.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : A ->⋆ₙ+* B)
  statement: f.comp (NonUnitalStarRingHom.id _) = f
  proof: ext fun _ => rfl

中文:
定理 comp_id
  条件: (f : A ->⋆ₙ+* B)
  结论: f.comp (非幺对合环态射.id _) = f
  证明: ext fun _ => rfl
-/
theorem comp_id (f : A ->⋆ₙ+* B) : f.comp (NonUnitalStarRingHom.id _) = f :=
  ext fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (A ->⋆ₙ+* A)
  body: comp
  mul_assoc := comp_assoc
  one := NonUnitalStarRingHom.id A
  one_mul := id_comp
  mul_one := comp_id

@[simp]

中文:
实例 :
  签名: 幺半群 (A ->⋆ₙ+* A)
  定义体: comp
  mul_assoc := comp_assoc
  one := NonUnitalStarRingHom.id A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
-/
instance : Monoid (A ->⋆ₙ+* A) where
  mul := comp
  mul_assoc := comp_assoc
  one := NonUnitalStarRingHom.id A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : A ->⋆ₙ+* A) : A -> A) = id
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : A ->⋆ₙ+* A) : A -> A) = id
  证明: rfl
-/
theorem coe_one : ((1 : A ->⋆ₙ+* A) : A -> A) = id :=
  rfl

/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (a : A)
  statement: (1 : A ->⋆ₙ+* A) a = a
  proof: rfl

中文:
定理 one_apply
  条件: (a : A)
  结论: (1 : A ->⋆ₙ+* A) a = a
  证明: rfl
-/
theorem one_apply (a : A) : (1 : A ->⋆ₙ+* A) a = a :=
  rfl

end Basic

section Zero

-- the `zero` requires extra type class assumptions because we need `star_zero`
variable {A B C : Type*}
variable [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
variable [NonUnitalNonAssocSemiring B] [StarAddMonoid B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (A ->⋆ₙ+* B)
  body: ⟨{ (0 : NonUnitalRingHom A B) with map_star' := by simp }⟩

中文:
实例 :
  签名: 零 (A ->⋆ₙ+* B)
  定义体: ⟨{ (0 : NonUnitalRingHom A B) with map_star' := by simp }⟩

Depends on / 依赖: NonUnitalRingHom, map_star
-/
instance : Zero (A ->⋆ₙ+* B) :=
  ⟨{ (0 : NonUnitalRingHom A B) with map_star' := by simp }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (A ->⋆ₙ+* B)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (A ->⋆ₙ+* B)
  定义体: ⟨0⟩
-/
instance : Inhabited (A ->⋆ₙ+* B) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidWithZero (A ->⋆ₙ+* A)
  body: fun _ => ext fun _ => rfl
  mul_zero := fun f => ext fun _ => map_zero f

@[simp]

中文:
实例 :
  签名: 带零幺半群 (A ->⋆ₙ+* A)
  定义体: fun _ => ext fun _ => rfl
  mul_zero := fun f => ext fun _ => map_zero f

@[simp]
-/
instance : MonoidWithZero (A ->⋆ₙ+* A) where
  zero_mul := fun _ => ext fun _ => rfl
  mul_zero := fun f => ext fun _ => map_zero f

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : A ->⋆ₙ+* B) : A -> B) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ((0 : A ->⋆ₙ+* B) : A -> B) = 0
  证明: rfl
-/
theorem coe_zero : ((0 : A ->⋆ₙ+* B) : A -> B) = 0 :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (a : A)
  statement: (0 : A ->⋆ₙ+* B) a = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (a : A)
  结论: (0 : A ->⋆ₙ+* B) a = 0
  证明: rfl
-/
theorem zero_apply (a : A) : (0 : A ->⋆ₙ+* B) a = 0 :=
  rfl

end Zero


end NonUnitalStarRingHom

/-! ### Star ring equivalences -/

/--
Definition of `StarRingEquiv` / `StarRingEquiv` 的定义

English:
structure StarRingEquiv
  parameters: (A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B]
  extends: A ≃+* B
  axioms and operations (1):
    - map_star' : forall a : A, toFun (star a) = star (toFun a)

中文:
结构 对合环等价
  参数: (A B : 类型) [加法 A] [加法 B] [乘法 A] [乘法 B] [对合 A] [对合 B]
  继承: A ≃+* B
  公理与运算 (1 个):
    - map_star' : 对任意 a : A, toFun (star a) = star (toFun a)
-/
structure StarRingEquiv (A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B]
    extends A ≃+* B where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star' : forall a : A, toFun (star a) = star (toFun a)

@[inherit_doc] notation:25 A " ≃⋆+* " B => StarRingEquiv A B

/-- Reinterpret a star ring equivalence as a `RingEquiv` by forgetting the interaction with the star
operation. -/
add_decl_doc StarRingEquiv.toRingEquiv

/--
Definition of `StarRingEquivClass` / `StarRingEquivClass` 的定义

English:
class StarRingEquivClass
  parameters: (F : Type*) (A B : outParam Type*)
  extends: RingEquivClass F A B
  axioms and operations (1):
    - map_star : forall (f : F) (a : A), f (star a) = star (f a)

中文:
类 对合环等价类
  参数: (F : 类型) (A B : outParam 类型)
  继承: 环等价类 F A B
  公理与运算 (1 个):
    - map_star : 对任意 (f : F) (a : A), f (star a) = star (f a)
-/
class StarRingEquivClass (F : Type*) (A B : outParam Type*)
    [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B] [EquivLike F A B] : Prop
    extends RingEquivClass F A B where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star : forall (f : F) (a : A), f (star a) = star (f a)

namespace StarRingEquivClass

-- See note [lower instance priority]
instance (priority := 50) {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [hF : StarRingEquivClass F A B] :
    StarHomClass F A B where
  __ := hF

-- See note [lower instance priority]
instance (priority := 100) {F A B : Type*} [NonUnitalNonAssocSemiring A] [Star A]
    [NonUnitalNonAssocSemiring B] [Star B] [EquivLike F A B] [StarRingEquivClass F A B] :
    NonUnitalStarRingHomClass F A B where

/-- Turn an element of a type `F` satisfying `StarRingEquivClass F A B` into an actual
`StarRingEquiv`. This is declared as the default coercion from `F` to `A ≃⋆+* B`. -/
@[coe]
/--
Definition of `toStarRingEquiv` / `toStarRingEquiv` 的定义

English:
definition toStarRingEquiv
  signature: {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
  body: { (RingEquivClass.toRingEquiv f : A ≃+* B) with
    map_star' := map_star f }

中文:
定义 toStarRingEquiv
  签名: {F A B : 类型} [加法 A] [乘法 A] [对合 A] [加法 B] [乘法 B] [对合 B]
  定义体: { (RingEquivClass.toRingEquiv f : A ≃+* B) with
    map_star' := map_star f }

Depends on / 依赖: RingEquivClass, RingEquivClass.toRingEquiv, map_star, toRingEquiv
-/
def toStarRingEquiv {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [StarRingEquivClass F A B] (f : F) : A ≃⋆+* B :=
  { (RingEquivClass.toRingEquiv f : A ≃+* B) with
    map_star' := map_star f }

/--
Instance `instCoeHead` / 实例 `instCoeHead`

English:
instance instCoeHead
  signature: {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
  body: ⟨toStarRingEquiv⟩

中文:
实例 instCoeHead
  签名: {F A B : 类型} [加法 A] [乘法 A] [对合 A] [加法 B] [乘法 B] [对合 B]
  定义体: ⟨toStarRingEquiv⟩

Depends on / 依赖: toStarRingEquiv
-/
instance instCoeHead {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [StarRingEquivClass F A B] : CoeHead F (A ≃⋆+* B) :=
  ⟨toStarRingEquiv⟩

end StarRingEquivClass

namespace StarRingEquiv

section Basic

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (A ≃⋆+* B) A B
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    congr

中文:
实例 :
  签名: 等价状 (A ≃⋆+* B) A B
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    congr

Depends on / 依赖: f.toFun
-/
instance : EquivLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RingEquivClass (A ≃⋆+* B) A B
  body: f.map_mul'
  map_add f := f.map_add'

中文:
实例 :
  签名: 环等价类 (A ≃⋆+* B) A B
  定义体: f.map_mul'
  map_add f := f.map_add'

Depends on / 依赖: f.map_mul, map_mul
-/
instance : RingEquivClass (A ≃⋆+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRingEquivClass (A ≃⋆+* B) A B
  body: map_star'

中文:
实例 :
  签名: 对合环等价类 (A ≃⋆+* B) A B
  定义体: map_star'

Depends on / 依赖: map_star
-/
instance : StarRingEquivClass (A ≃⋆+* B) A B where
  map_star := map_star'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ≃⋆+* B) A B
  body: f.toFun
  coe_injective := DFunLike.coe_injective

中文:
实例 :
  签名: 函数状 (A ≃⋆+* B) A B
  定义体: f.toFun
  coe_injective := DFunLike.coe_injective

Depends on / 依赖: f.toFun
-/
instance : FunLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  coe_injective := DFunLike.coe_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (A ≃⋆+* B) (A ≃+* B)
  body: toRingEquiv

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]

中文:
实例 :
  签名: CoeOut (A ≃⋆+* B) (A ≃+* B)
  定义体: toRingEquiv

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]

Depends on / 依赖: toRingEquiv
-/
instance : CoeOut (A ≃⋆+* B) (A ≃+* B) where coe := toRingEquiv

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
/--
theorem `toRingEquiv_eq_coe` / 定理 `toRingEquiv_eq_coe`

English:
theorem toRingEquiv_eq_coe
  given: (e : A ≃⋆+* B)
  statement: e.toRingEquiv = e
  proof: rfl

@[ext]

中文:
定理 toRingEquiv_eq_coe
  条件: (e : A ≃⋆+* B)
  结论: e.toRingEquiv = e
  证明: rfl

@[ext]
-/
theorem toRingEquiv_eq_coe (e : A ≃⋆+* B) : e.toRingEquiv = e :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ≃⋆+* B} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : A ≃⋆+* B} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : A ≃⋆+* B} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- The identity map as a star ring isomorphism. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : A ≃⋆+* A
  body: { RingEquiv.refl A with
    map_star' := fun _ => rfl }

中文:
定义 refl
  签名: : A ≃⋆+* A
  定义体: { RingEquiv.refl A with
    map_star' := fun _ => rfl }

Depends on / 依赖: RingEquiv, RingEquiv.refl, map_star
-/
def refl : A ≃⋆+* A :=
  { RingEquiv.refl A with
    map_star' := fun _ => rfl }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (A ≃⋆+* A)
  body: ⟨refl⟩

@[simp]

中文:
实例 :
  签名: 可居 (A ≃⋆+* A)
  定义体: ⟨refl⟩

@[simp]
-/
instance : Inhabited (A ≃⋆+* A) :=
  ⟨refl⟩

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ⇑(refl : A ≃⋆+* A) = id
  proof: rfl

中文:
定理 coe_refl
  结论: ⇑(refl : A ≃⋆+* A) = id
  证明: rfl
-/
theorem coe_refl : ⇑(refl : A ≃⋆+* A) = id :=
  rfl

/-- The inverse of a star ring isomorphism is a star ring isomorphism. -/
@[symm]
nonrec def symm (e : A ≃⋆+* B) : B ≃⋆+* A :=
  { e.symm with
    map_star' := fun b => by
      simpa only [apply_inv_apply, inv_apply_apply] using!
        congr_arg (inv e) (map_star e (inv e b)).symm }

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (e : A ≃⋆+* B)
  body: e

中文:
定义 Simps.apply
  签名: (e : A ≃⋆+* B)
  定义体: e
-/
def Simps.apply (e : A ≃⋆+* B) : A -> B := e

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : A ≃⋆+* B)
  body: e.symm

initialize_simps_projections StarRingEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]

中文:
定义 Simps.symm_apply
  签名: (e : A ≃⋆+* B)
  定义体: e.symm

initialize_simps_projections StarRingEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
-/
def Simps.symm_apply (e : A ≃⋆+* B) : B -> A :=
  e.symm

initialize_simps_projections StarRingEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
/--
theorem `invFun_eq_symm` / 定理 `invFun_eq_symm`

English:
theorem invFun_eq_symm
  given: {e : A ≃⋆+* B}
  statement: EquivLike.inv e = e.symm
  proof: rfl

@[simp]

中文:
定理 invFun_eq_symm
  条件: {e : A ≃⋆+* B}
  结论: 等价状.inv e = e.symm
  证明: rfl

@[simp]
-/
theorem invFun_eq_symm {e : A ≃⋆+* B} : EquivLike.inv e = e.symm :=
  rfl

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : A ≃⋆+* B)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : A ≃⋆+* B)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : A ≃⋆+* B) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : (A ≃⋆+* B) -> B ≃⋆+* A)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  结论: 函数.双射 (symm : (A ≃⋆+* B) -> B ≃⋆+* A)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : (A ≃⋆+* B) -> B ≃⋆+* A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e h₁)
  statement: ⇑(⟨e, h₁⟩ : A ≃⋆+* B) = e
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (e h₁)
  结论: ⇑(⟨e, h₁⟩ : A ≃⋆+* B) = e
  证明: rfl

@[simp]
-/
@[simp] theorem coe_mk (e h₁) : ⇑(⟨e, h₁⟩ : A ≃⋆+* B) = e := rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (e : A ≃⋆+* B) (e' h₁ h₂ h₃ h₄ h₅)
  proof: ext fun _ => rfl

@[simp]

中文:
定理 mk_coe
  条件: (e : A ≃⋆+* B) (e' h₁ h₂ h₃ h₄ h₅)
  证明: ext fun _ => rfl

@[simp]
-/
theorem mk_coe (e : A ≃⋆+* B) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B) = e := ext fun _ => rfl

@[simp]
/--
theorem `symm_mk` / 定理 `symm_mk`

English:
theorem symm_mk
  given: (e : A ≃+* B) (h₁)
  statement: dsimp%
  proof: rfl

@[simp]

中文:
定理 symm_mk
  条件: (e : A ≃+* B) (h₁)
  结论: dsimp%
  证明: rfl

@[simp]

Depends on / 依赖: e.symm
-/
theorem symm_mk (e : A ≃+* B) (h₁) : dsimp%
    (⟨e, h₁⟩ : A ≃⋆+* B).symm =
      { (⟨e, h₁⟩ : A ≃⋆+* B).symm with
        toRingEquiv := e.symm } :=
  rfl

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (StarRingEquiv.refl : A ≃⋆+* A).symm = StarRingEquiv.refl
  proof: rfl

中文:
定理 refl_symm
  结论: (对合环等价.refl : A ≃⋆+* A).symm = 对合环等价.refl
  证明: rfl
-/
theorem refl_symm : (StarRingEquiv.refl : A ≃⋆+* A).symm = StarRingEquiv.refl :=
  rfl

/-- Transitivity of `StarRingEquiv`. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C)
  body: { e₁.toRingEquiv.trans e₂.toRingEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star']; rw [e₂.map_star'] }

@[simp]

中文:
定义 trans
  签名: (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C)
  定义体: { e₁.toRingEquiv.trans e₂.toRingEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star']; rw [e₂.map_star'] }

@[simp]

Depends on / 依赖: map_star, toRingEquiv, toRingEquiv.trans
-/
def trans (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) : A ≃⋆+* C :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star']; rw [e₂.map_star'] }

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : A ≃⋆+* B)
  statement: forall x, e (e.symm x) = x
  proof: e.toRingEquiv.apply_symm_apply

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : A ≃⋆+* B)
  结论: 对任意 x, e (e.symm x) = x
  证明: e.toRingEquiv.apply_symm_apply

@[simp]

Depends on / 依赖: apply_symm_apply, e.toRingEquiv.apply_symm_apply, toRingEquiv
-/
theorem apply_symm_apply (e : A ≃⋆+* B) : forall x, e (e.symm x) = x :=
  e.toRingEquiv.apply_symm_apply

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : A ≃⋆+* B)
  statement: forall x, e.symm (e x) = x
  proof: e.toRingEquiv.symm_apply_apply

@[simp]

中文:
定理 symm_apply_apply
  条件: (e : A ≃⋆+* B)
  结论: 对任意 x, e.symm (e x) = x
  证明: e.toRingEquiv.symm_apply_apply

@[simp]

Depends on / 依赖: e.toRingEquiv.symm_apply_apply, symm_apply_apply, toRingEquiv
-/
theorem symm_apply_apply (e : A ≃⋆+* B) : forall x, e.symm (e x) = x :=
  e.toRingEquiv.symm_apply_apply

@[simp]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : C)
  proof: rfl

@[simp]

中文:
定理 symm_trans_apply
  条件: (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : C)
  证明: rfl

@[simp]
-/
theorem symm_trans_apply (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C)
  statement: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  proof: rfl

@[simp]

中文:
定理 coe_trans
  条件: (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C)
  结论: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  证明: rfl

@[simp]
-/
theorem coe_trans (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : A)
  statement: (e₁.trans e₂) x = e₂ (e₁ x)
  proof: rfl

中文:
定理 trans_apply
  条件: (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : A)
  结论: (e₁.trans e₂) x = e₂ (e₁ x)
  证明: rfl
-/
theorem trans_apply (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

/--
theorem `leftInverse_symm` / 定理 `leftInverse_symm`

English:
theorem leftInverse_symm
  given: (e : A ≃⋆+* B)
  statement: Function.LeftInverse e.symm e
  proof: e.left_inv

中文:
定理 leftInverse_symm
  条件: (e : A ≃⋆+* B)
  结论: 函数.左逆 e.symm e
  证明: e.left_inv

Depends on / 依赖: e.left_inv, left_inv
-/
theorem leftInverse_symm (e : A ≃⋆+* B) : Function.LeftInverse e.symm e :=
  e.left_inv

/--
theorem `rightInverse_symm` / 定理 `rightInverse_symm`

English:
theorem rightInverse_symm
  given: (e : A ≃⋆+* B)
  statement: Function.RightInverse e.symm e
  proof: e.right_inv

中文:
定理 rightInverse_symm
  条件: (e : A ≃⋆+* B)
  结论: 函数.右逆 e.symm e
  证明: e.right_inv

Depends on / 依赖: e.right_inv, right_inv
-/
theorem rightInverse_symm (e : A ≃⋆+* B) : Function.RightInverse e.symm e :=
  e.right_inv

end Basic


section Bijective

variable {F G A B : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [FunLike F A B] [NonUnitalRingHomClass F A B] [NonUnitalStarRingHomClass F A B]
variable [FunLike G B A]

/-- If a (unital or non-unital) star ring morphism has an inverse, it is an isomorphism of
star rings. -/
@[simps]
/--
Definition of `ofStarRingHom` / `ofStarRingHom` 的定义

English:
definition ofStarRingHom
  signature: (f : F) (g : G) (h₁ : forall x, g (f x) = x) (h₂ : forall x, f (g x) = x)
  body: f
  invFun := g
  left_inv := h₁
  right_inv := h₂
  map_add' := map_add f
  map_mul' := map_mul f
  map_star' := map_star f

中文:
定义 ofStarRingHom
  签名: (f : F) (g : G) (h₁ : 对任意 x, g (f x) = x) (h₂ : 对任意 x, f (g x) = x)
  定义体: f
  invFun := g
  left_inv := h₁
  right_inv := h₂
  map_add' := map_add f
  map_mul' := map_mul f
  map_star' := map_star f
-/
def ofStarRingHom (f : F) (g : G) (h₁ : forall x, g (f x) = x) (h₂ : forall x, f (g x) = x) : A ≃⋆+* B where
  toFun := f
  invFun := g
  left_inv := h₁
  right_inv := h₂
  map_add' := map_add f
  map_mul' := map_mul f
  map_star' := map_star f

/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: (f : F) (hf : Function.Bijective f)
  body: { RingEquiv.ofBijective f (hf : Function.Bijective (f : A -> B)) with
    toFun := f
    map_star' := map_star f }

@[simp]

中文:
定义 ofBijective
  签名: (f : F) (hf : 函数.双射 f)
  定义体: { RingEquiv.ofBijective f (hf : Function.Bijective (f : A -> B)) with
    toFun := f
    map_star' := map_star f }

@[simp]

Depends on / 依赖: Bijective, Function, Function.Bijective, RingEquiv, RingEquiv.ofBijective, map_star, ofBijective
-/
noncomputable def ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆+* B :=
  { RingEquiv.ofBijective f (hf : Function.Bijective (f : A -> B)) with
    toFun := f
    map_star' := map_star f }

@[simp]
/--
theorem `coe_ofBijective` / 定理 `coe_ofBijective`

English:
theorem coe_ofBijective
  given: {f : F} (hf : Function.Bijective f)
  proof: rfl

中文:
定理 coe_ofBijective
  条件: {f : F} (hf : 函数.双射 f)
  证明: rfl
-/
theorem coe_ofBijective {f : F} (hf : Function.Bijective f) :
    (StarRingEquiv.ofBijective f hf : A -> B) = f :=
  rfl

/--
theorem `ofBijective_apply` / 定理 `ofBijective_apply`

English:
theorem ofBijective_apply
  given: {f : F} (hf : Function.Bijective f) (a : A)
  proof: rfl

中文:
定理 ofBijective_apply
  条件: {f : F} (hf : 函数.双射 f) (a : A)
  证明: rfl
-/
theorem ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) :
    (StarRingEquiv.ofBijective f hf) a = f a :=
  rfl

end Bijective

end StarRingEquiv
