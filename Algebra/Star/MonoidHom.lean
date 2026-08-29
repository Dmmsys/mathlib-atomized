/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Basic
/-!
# Morphisms of star monoids

This file defines the type of morphisms `StarMonoidHom` between monoids `A` and `B` where both
`A` and `B` are equipped with a `star` operation. These morphisms are star-preserving monoid
homomorphisms and are equipped with the notation `A →⋆* B`.

The primary motivation for these morphisms is to provide a target type for morphisms which induce
a corresponding morphism between the unitary groups in a star monoid.

## Main definitions

  * `StarMonoidHom`
  * `StarMulEquiv`

## Tags

monoid, star
-/

@[expose] public section

variable {F A B C D : Type*}

/-! ### Star monoid homomorphisms -/

/--
Definition of `StarMonoidHom` / `StarMonoidHom` 的定义

English:
structure StarMonoidHom
  parameters: (A B : Type*) [Monoid A] [Star A] [Monoid B] [Star B]
  extends: A ->* B
  axioms and operations (1):
    - map_star' : forall a : A, toFun (star a) = star (toFun a)

中文:
结构 StarMonoidHom
  参数: (A B : 类型) [Monoid A] [Star A] [Monoid B] [Star B]
  继承: A ->* B
  公理与运算 (1 个):
    - map_star' : 对任意 a : A, toFun (star a) = star (toFun a)
-/
structure StarMonoidHom (A B : Type*) [Monoid A] [Star A] [Monoid B] [Star B]
    extends A ->* B where
  /-- By definition, a star monoid homomorphism preserves the `star` operation. -/
  map_star' : forall a : A, toFun (star a) = star (toFun a)

/-- `α →⋆* β` denotes the type of star monoid homomorphisms from `α` to `β`. -/
infixr:25 " ->⋆* " => StarMonoidHom

/-- Reinterpret a star monoid homomorphism as a monoid homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc StarMonoidHom.toMonoidHom

namespace StarMonoidHom

variable [Monoid A] [Star A] [Monoid B] [Star B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ->⋆* B) A B
  body: f.toFun
  coe_injective f g h := by cases f; cases g; simp_all

中文:
实例 :
  签名: FunLike (A ->⋆* B) A B
  定义体: f.toFun
  coe_injective f g h := by cases f; cases g; simp_all

Depends on / 依赖: f.toFun
-/
instance : FunLike (A ->⋆* B) A B where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; simp_all

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidHomClass (A ->⋆* B) A B
  body: f.map_mul'
  map_one f := f.map_one'

中文:
实例 :
  签名: MonoidHomClass (A ->⋆* B) A B
  定义体: f.map_mul'
  map_one f := f.map_one'

Depends on / 依赖: f.map_mul, map_mul
-/
instance : MonoidHomClass (A ->⋆* B) A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarHomClass (A ->⋆* B) A B
  body: f.map_star'

中文:
实例 :
  签名: StarHomClass (A ->⋆* B) A B
  定义体: f.map_star'

Depends on / 依赖: f.map_star, map_star
-/
instance : StarHomClass (A ->⋆* B) A B where
  map_star f := f.map_star'

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (f : A ->⋆* B)
  body: f

initialize_simps_projections StarMonoidHom (toFun -> coe)

中文:
定义 Simps.coe
  签名: (f : A ->⋆* B)
  定义体: f

initialize_simps_projections StarMonoidHom (toFun -> coe)
-/
def Simps.coe (f : A ->⋆* B) : A -> B := f

initialize_simps_projections StarMonoidHom (toFun -> coe)

/-- Construct a `StarMonoidHom` from a morphism in some type which preserves `1`, `*` and `star`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: [FunLike F A B] [MonoidHomClass F A B] [StarHomClass F A B] (f : F)
  body: f
  map_one' := map_one f
  map_mul' := map_mul f
  map_star' := map_star f

@[simp]

中文:
定义 ofClass
  签名: [FunLike F A B] [MonoidHomClass F A B] [StarHomClass F A B] (f : F)
  定义体: f
  map_one' := map_one f
  map_mul' := map_mul f
  map_star' := map_star f

@[simp]
-/
def ofClass [FunLike F A B] [MonoidHomClass F A B] [StarHomClass F A B] (f : F) :
    A ->⋆* B where
  toFun := f
  map_one' := map_one f
  map_mul' := map_mul f
  map_star' := map_star f

@[simp]
/--
theorem `coe_toMonoidHom` / 定理 `coe_toMonoidHom`

English:
theorem coe_toMonoidHom
  given: (f : A ->⋆* B)
  statement: ⇑f.toMonoidHom = f
  proof: rfl

@[ext]

中文:
定理 coe_toMonoidHom
  条件: (f : A ->⋆* B)
  结论: ⇑f.toMonoidHom = f
  证明: rfl

@[ext]
-/
theorem coe_toMonoidHom (f : A ->⋆* B) : ⇑f.toMonoidHom = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ->⋆* B} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {f g : A ->⋆* B} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : A ->⋆* B} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : A ->⋆* B) (f' : A -> B) (h : f' = f)
  body: f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]

中文:
定义 copy
  签名: (f : A ->⋆* B) (f' : A -> B) (h : f' = f)
  定义体: f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
-/
protected def copy (f : A ->⋆* B) (f' : A -> B) (h : f' = f) : A ->⋆* B where
  toFun := f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : A ->⋆* B) (f' : A -> B) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : A ->⋆* B) (f' : A -> B) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : A ->⋆* B) (f' : A -> B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : A ->⋆* B) (f' : A -> B) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

@[simp]

中文:
定理 copy_eq
  条件: (f : A ->⋆* B) (f' : A -> B) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : A ->⋆* B) (f' : A -> B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : A ->* B) (h)
  statement: ((⟨f, h⟩ : A ->⋆* B) : A -> B) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : A ->* B) (h)
  结论: ((⟨f, h⟩ : A ->⋆* B) : A -> B) = f
  证明: rfl
-/
theorem coe_mk (f : A ->* B) (h) : ((⟨f, h⟩ : A ->⋆* B) : A -> B) = f := rfl

section Id

variable (A)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : A ->⋆* A
  body: { (.id A : A ->* A) with map_star' := fun _ => rfl }

@[simp, norm_cast]

中文:
定义 id
  签名: : A ->⋆* A
  定义体: { (.id A : A ->* A) with map_star' := fun _ => rfl }

@[simp, norm_cast]
-/
protected def id : A ->⋆* A :=
  { (.id A : A ->* A) with map_star' := fun _ => rfl }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(StarMonoidHom.id A) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(StarMonoidHom.id A) = id
  证明: rfl
-/
theorem coe_id : ⇑(StarMonoidHom.id A) = id :=
  rfl

end Id

section Comp

variable [Monoid C] [Star C] [Monoid D] [Star D]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : B ->⋆* C) (g : A ->⋆* B)
  body: { f.toMonoidHom.comp g.toMonoidHom with
    map_star' := fun a => by simp [map_star] }

@[simp]

中文:
定义 comp
  签名: (f : B ->⋆* C) (g : A ->⋆* B)
  定义体: { f.toMonoidHom.comp g.toMonoidHom with
    map_star' := fun a => by simp [map_star] }

@[simp]

Depends on / 依赖: f.toMonoidHom.comp, g.toMonoidHom, map_star, toMonoidHom
-/
def comp (f : B ->⋆* C) (g : A ->⋆* B) : A ->⋆* C :=
  { f.toMonoidHom.comp g.toMonoidHom with
    map_star' := fun a => by simp [map_star] }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : B ->⋆* C) (g : A ->⋆* B)
  statement: ⇑(comp f g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : B ->⋆* C) (g : A ->⋆* B)
  结论: ⇑(comp f g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : B ->⋆* C) (g : A ->⋆* B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : B ->⋆* C) (g : A ->⋆* B) (a : A)
  statement: comp f g a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : B ->⋆* C) (g : A ->⋆* B) (a : A)
  结论: comp f g a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : B ->⋆* C) (g : A ->⋆* B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : C ->⋆* D) (g : B ->⋆* C) (h : A ->⋆* B)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : C ->⋆* D) (g : B ->⋆* C) (h : A ->⋆* B)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : C ->⋆* D) (g : B ->⋆* C) (h : A ->⋆* B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : A ->⋆* B)
  statement: (StarMonoidHom.id B).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : A ->⋆* B)
  结论: (StarMonoidHom.id B).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : A ->⋆* B) : (StarMonoidHom.id B).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : A ->⋆* B)
  statement: f.comp (.id _) = f
  proof: ext fun _ => rfl

中文:
定理 comp_id
  条件: (f : A ->⋆* B)
  结论: f.comp (.id _) = f
  证明: ext fun _ => rfl
-/
theorem comp_id (f : A ->⋆* B) : f.comp (.id _) = f :=
  ext fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (A ->⋆* A)
  body: comp
  mul_assoc := comp_assoc
  one := .id A
  one_mul := id_comp
  mul_one := comp_id

@[simp]

中文:
实例 :
  签名: Monoid (A ->⋆* A)
  定义体: comp
  mul_assoc := comp_assoc
  one := .id A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
-/
instance : Monoid (A ->⋆* A) where
  mul := comp
  mul_assoc := comp_assoc
  one := .id A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : A ->⋆* A) : A -> A) = id
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : A ->⋆* A) : A -> A) = id
  证明: rfl
-/
theorem coe_one : ((1 : A ->⋆* A) : A -> A) = id :=
  rfl

/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (a : A)
  statement: (1 : A ->⋆* A) a = a
  proof: rfl

中文:
定理 one_apply
  条件: (a : A)
  结论: (1 : A ->⋆* A) a = a
  证明: rfl
-/
theorem one_apply (a : A) : (1 : A ->⋆* A) a = a :=
  rfl

end Comp

end StarMonoidHom

/-! ### Star monoid equivalences -/

/--
Definition of `StarMulEquiv` / `StarMulEquiv` 的定义

English:
structure StarMulEquiv
  parameters: (A B : Type*) [Mul A] [Mul B] [Star A] [Star B]
  extends: A ≃* B
  axioms and operations (1):
    - map_star' : forall a : A, toFun (star a) = star (toFun a)

中文:
结构 StarMulEquiv
  参数: (A B : 类型) [Mul A] [Mul B] [Star A] [Star B]
  继承: A ≃* B
  公理与运算 (1 个):
    - map_star' : 对任意 a : A, toFun (star a) = star (toFun a)
-/
structure StarMulEquiv (A B : Type*) [Mul A] [Mul B] [Star A] [Star B]
    extends A ≃* B where
  /-- By definition, a star monoid equivalence preserves the `star` operation. -/
  map_star' : forall a : A, toFun (star a) = star (toFun a)

@[inherit_doc] notation:25 A " ≃⋆* " B => StarMulEquiv A B

/-- Reinterpret a star monoid equivalence as a `MulEquiv` by forgetting the interaction with the
star operation. -/
add_decl_doc StarMulEquiv.toMulEquiv

namespace StarMulEquiv

section Basic

variable [Mul A] [Mul B] [Mul C] [Mul D]
variable [Star A] [Star B] [Star C] [Star D]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (A ≃⋆* B) A B
  body: e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' f g h := by cases f; cases g; simp_all

中文:
实例 :
  签名: EquivLike (A ≃⋆* B) A B
  定义体: e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' f g h := by cases f; cases g; simp_all

Depends on / 依赖: e.toFun
-/
instance : EquivLike (A ≃⋆* B) A B where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' f g h := by cases f; cases g; simp_all

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulEquivClass (A ≃⋆* B) A B
  body: f.map_mul'

中文:
实例 :
  签名: MulEquivClass (A ≃⋆* B) A B
  定义体: f.map_mul'

Depends on / 依赖: f.map_mul, map_mul
-/
instance : MulEquivClass (A ≃⋆* B) A B where
  map_mul f := f.map_mul'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarHomClass (A ≃⋆* B) A B
  body: f.map_star'

@[ext]

中文:
实例 :
  签名: StarHomClass (A ≃⋆* B) A B
  定义体: f.map_star'

@[ext]

Depends on / 依赖: f.map_star, map_star
-/
instance : StarHomClass (A ≃⋆* B) A B where
  map_star f := f.map_star'

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ≃⋆* B} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : A ≃⋆* B} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : A ≃⋆* B} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

variable (A) in
/-- The identity map as a star monoid isomorphism. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : A ≃⋆* A
  body: { MulEquiv.refl A with
    map_star' := fun _ => rfl }

中文:
定义 refl
  签名: : A ≃⋆* A
  定义体: { MulEquiv.refl A with
    map_star' := fun _ => rfl }
-/
protected def refl : A ≃⋆* A :=
  { MulEquiv.refl A with
    map_star' := fun _ => rfl }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (A ≃⋆* A)
  body: ⟨.refl A⟩

@[simp]

中文:
实例 :
  签名: Inhabited (A ≃⋆* A)
  定义体: ⟨.refl A⟩

@[simp]
-/
instance : Inhabited (A ≃⋆* A) :=
  ⟨.refl A⟩

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ⇑(.refl A : A ≃⋆* A) = id
  proof: rfl

中文:
定理 coe_refl
  结论: ⇑(.refl A : A ≃⋆* A) = id
  证明: rfl
-/
theorem coe_refl : ⇑(.refl A : A ≃⋆* A) = id :=
  rfl

/-- The inverse of a star monoid isomorphism is a star monoid isomorphism. -/
@[symm]
nonrec def symm (e : A ≃⋆* B) : B ≃⋆* A :=
  { e.symm with
    map_star' := fun b => by
      simpa only [EquivLike.apply_inv_apply, EquivLike.inv_apply_apply] using!
        congr_arg (EquivLike.inv e) (map_star e (EquivLike.inv e b)).symm }

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (e : A ≃⋆* B)
  body: e

中文:
定义 Simps.apply
  签名: (e : A ≃⋆* B)
  定义体: e
-/
def Simps.apply (e : A ≃⋆* B) : A -> B := e

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : A ≃⋆* B)
  body: e.symm

initialize_simps_projections StarMulEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]

中文:
定义 Simps.symm_apply
  签名: (e : A ≃⋆* B)
  定义体: e.symm

initialize_simps_projections StarMulEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
-/
def Simps.symm_apply (e : A ≃⋆* B) : B -> A :=
  e.symm

initialize_simps_projections StarMulEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
/--
theorem `invFun_eq_symm` / 定理 `invFun_eq_symm`

English:
theorem invFun_eq_symm
  given: {e : A ≃⋆* B}
  statement: EquivLike.inv e = e.symm
  proof: rfl

@[simp]

中文:
定理 invFun_eq_symm
  条件: {e : A ≃⋆* B}
  结论: EquivLike.inv e = e.symm
  证明: rfl

@[simp]
-/
theorem invFun_eq_symm {e : A ≃⋆* B} : EquivLike.inv e = e.symm :=
  rfl

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : A ≃⋆* B)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : A ≃⋆* B)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : A ≃⋆* B) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : (A ≃⋆* B) -> B ≃⋆* A)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  结论: Function.Bijective (symm : (A ≃⋆* B) -> B ≃⋆* A)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : (A ≃⋆* B) -> B ≃⋆* A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e h₁)
  statement: ⇑(⟨e, h₁⟩ : A ≃⋆* B) = e
  proof: rfl

中文:
定理 coe_mk
  条件: (e h₁)
  结论: ⇑(⟨e, h₁⟩ : A ≃⋆* B) = e
  证明: rfl
-/
theorem coe_mk (e h₁) : ⇑(⟨e, h₁⟩ : A ≃⋆* B) = e := rfl

/-- Construct a `StarMulEquiv` from an equivalence in some type which preserves `*` and `star`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: [EquivLike F A B] [MulEquivClass F A B] [StarHomClass F A B] (f : F)
  body: f
  invFun := EquivLike.inv f
  left_inv := EquivLike.left_inv f
  right_inv := EquivLike.right_inv f
  map_mul' := map_mul f
  map_star' := map_star f

@[simp]

中文:
定义 ofClass
  签名: [EquivLike F A B] [MulEquivClass F A B] [StarHomClass F A B] (f : F)
  定义体: f
  invFun := EquivLike.inv f
  left_inv := EquivLike.left_inv f
  right_inv := EquivLike.right_inv f
  map_mul' := map_mul f
  map_star' := map_star f

@[simp]
-/
def ofClass [EquivLike F A B] [MulEquivClass F A B] [StarHomClass F A B] (f : F) :
    A ≃⋆* B where
  toFun := f
  invFun := EquivLike.inv f
  left_inv := EquivLike.left_inv f
  right_inv := EquivLike.right_inv f
  map_mul' := map_mul f
  map_star' := map_star f

@[simp]
/--
theorem `coe_toMulEquiv` / 定理 `coe_toMulEquiv`

English:
theorem coe_toMulEquiv
  given: (f : A ≃⋆* B)
  statement: ⇑f.toMulEquiv = f
  proof: rfl

@[simp]

中文:
定理 coe_toMulEquiv
  条件: (f : A ≃⋆* B)
  结论: ⇑f.toMulEquiv = f
  证明: rfl

@[simp]
-/
theorem coe_toMulEquiv (f : A ≃⋆* B) : ⇑f.toMulEquiv = f :=
  rfl

@[simp]
/--
theorem `toMulEquiv_symm` / 定理 `toMulEquiv_symm`

English:
theorem toMulEquiv_symm
  given: (f : A ≃⋆* B)
  statement: f.symm.toMulEquiv = f.toMulEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toMulEquiv_symm
  条件: (f : A ≃⋆* B)
  结论: f.symm.toMulEquiv = f.toMulEquiv.symm
  证明: rfl

@[simp]
-/
theorem toMulEquiv_symm (f : A ≃⋆* B) : f.symm.toMulEquiv = f.toMulEquiv.symm :=
  rfl

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (.refl A : A ≃⋆* A).symm = .refl A
  proof: rfl

中文:
定理 refl_symm
  结论: (.refl A : A ≃⋆* A).symm = .refl A
  证明: rfl
-/
theorem refl_symm : (.refl A : A ≃⋆* A).symm = .refl A :=
  rfl

/-- Transitivity of `StarMulEquiv`. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C)
  body: { e₁.toMulEquiv.trans e₂.toMulEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star']; rw [e₂.map_star'] }

@[simp]

中文:
定义 trans
  签名: (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C)
  定义体: { e₁.toMulEquiv.trans e₂.toMulEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star']; rw [e₂.map_star'] }

@[simp]

Depends on / 依赖: map_star, toMulEquiv, toMulEquiv.trans
-/
def trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) : A ≃⋆* C :=
  { e₁.toMulEquiv.trans e₂.toMulEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star']; rw [e₂.map_star'] }

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : A ≃⋆* B)
  statement: forall x, e (e.symm x) = x
  proof: e.toMulEquiv.apply_symm_apply

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : A ≃⋆* B)
  结论: 对任意 x, e (e.symm x) = x
  证明: e.toMulEquiv.apply_symm_apply

@[simp]

Depends on / 依赖: apply_symm_apply, e.toMulEquiv.apply_symm_apply, toMulEquiv
-/
theorem apply_symm_apply (e : A ≃⋆* B) : forall x, e (e.symm x) = x :=
  e.toMulEquiv.apply_symm_apply

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : A ≃⋆* B)
  statement: forall x, e.symm (e x) = x
  proof: e.toMulEquiv.symm_apply_apply

@[simp]

中文:
定理 symm_apply_apply
  条件: (e : A ≃⋆* B)
  结论: 对任意 x, e.symm (e x) = x
  证明: e.toMulEquiv.symm_apply_apply

@[simp]

Depends on / 依赖: e.toMulEquiv.symm_apply_apply, symm_apply_apply, toMulEquiv
-/
theorem symm_apply_apply (e : A ≃⋆* B) : forall x, e.symm (e x) = x :=
  e.toMulEquiv.symm_apply_apply

@[simp]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : C)
  proof: rfl

@[simp]

中文:
定理 symm_trans_apply
  条件: (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : C)
  证明: rfl

@[simp]
-/
theorem symm_trans_apply (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C)
  statement: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  proof: rfl

@[simp]

中文:
定理 coe_trans
  条件: (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C)
  结论: ⇑(e₁.trans e₂) = e₂ ∘ e₁
  证明: rfl

@[simp]
-/
theorem coe_trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : A)
  statement: (e₁.trans e₂) x = e₂ (e₁ x)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : A)
  结论: (e₁.trans e₂) x = e₂ (e₁ x)
  证明: rfl

@[simp]
-/
theorem trans_apply (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
/--
theorem `toMulEquiv_trans` / 定理 `toMulEquiv_trans`

English:
theorem toMulEquiv_trans
  given: (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C)
  proof: rfl

中文:
定理 toMulEquiv_trans
  条件: (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C)
  证明: rfl
-/
theorem toMulEquiv_trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) :
    (e₁.trans e₂).toMulEquiv = e₁.toMulEquiv.trans e₂.toMulEquiv :=
  rfl

/--
theorem `leftInverse_symm` / 定理 `leftInverse_symm`

English:
theorem leftInverse_symm
  given: (e : A ≃⋆* B)
  statement: Function.LeftInverse e.symm e
  proof: e.left_inv

中文:
定理 leftInverse_symm
  条件: (e : A ≃⋆* B)
  结论: Function.LeftInverse e.symm e
  证明: e.left_inv

Depends on / 依赖: e.left_inv, left_inv
-/
theorem leftInverse_symm (e : A ≃⋆* B) : Function.LeftInverse e.symm e :=
  e.left_inv

/--
theorem `rightInverse_symm` / 定理 `rightInverse_symm`

English:
theorem rightInverse_symm
  given: (e : A ≃⋆* B)
  statement: Function.RightInverse e.symm e
  proof: e.right_inv

中文:
定理 rightInverse_symm
  条件: (e : A ≃⋆* B)
  结论: Function.RightInverse e.symm e
  证明: e.right_inv

Depends on / 依赖: e.right_inv, right_inv
-/
theorem rightInverse_symm (e : A ≃⋆* B) : Function.RightInverse e.symm e :=
  e.right_inv

end Basic

section Bijective

variable [Monoid A] [Monoid B] [Star A] [Star B]

/-- Reinterpret a `StarMulEquiv` as a `StarMonoidHom`. -/
@[simps]
/--
Definition of `toStarMonoidHom` / `toStarMonoidHom` 的定义

English:
definition toStarMonoidHom
  signature: (f : A ≃⋆* B)
  body: f
  map_one' := map_one f
  map_mul' := map_mul f
  map_star' := map_star f

中文:
定义 toStarMonoidHom
  签名: (f : A ≃⋆* B)
  定义体: f
  map_one' := map_one f
  map_mul' := map_mul f
  map_star' := map_star f
-/
def toStarMonoidHom (f : A ≃⋆* B) : A ->⋆* B where
  toFun := f
  map_one' := map_one f
  map_mul' := map_mul f
  map_star' := map_star f

/-- If a star monoid morphism has an inverse, it is an isomorphism of star monoids. -/
@[simps]
/--
Definition of `ofStarMonoidHom` / `ofStarMonoidHom` 的定义

English:
definition ofStarMonoidHom
  signature: (f : A ->⋆* B) (g : B ->⋆* A) (h₁ : g.comp f = .id _) (h₂ : f.comp g = .id _)
  body: f
  invFun := g
  left_inv := DFunLike.ext_iff.mp h₁
  right_inv := DFunLike.ext_iff.mp h₂
  map_mul' := map_mul f
  map_star' := map_star f

中文:
定义 ofStarMonoidHom
  签名: (f : A ->⋆* B) (g : B ->⋆* A) (h₁ : g.comp f = .id _) (h₂ : f.comp g = .id _)
  定义体: f
  invFun := g
  left_inv := DFunLike.ext_iff.mp h₁
  right_inv := DFunLike.ext_iff.mp h₂
  map_mul' := map_mul f
  map_star' := map_star f
-/
def ofStarMonoidHom (f : A ->⋆* B) (g : B ->⋆* A) (h₁ : g.comp f = .id _) (h₂ : f.comp g = .id _) :
    A ≃⋆* B where
  toFun := f
  invFun := g
  left_inv := DFunLike.ext_iff.mp h₁
  right_inv := DFunLike.ext_iff.mp h₂
  map_mul' := map_mul f
  map_star' := map_star f

/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: (f : A ->⋆* B) (hf : Function.Bijective f)
  body: { MulEquiv.ofBijective f (hf : Function.Bijective (f : A -> B)) with
    toFun := f
    map_star' := map_star f }

@[simp]

中文:
定义 ofBijective
  签名: (f : A ->⋆* B) (hf : Function.Bijective f)
  定义体: { MulEquiv.ofBijective f (hf : Function.Bijective (f : A -> B)) with
    toFun := f
    map_star' := map_star f }

@[simp]

Depends on / 依赖: Bijective, Function, Function.Bijective, MulEquiv, MulEquiv.ofBijective, map_star, ofBijective
-/
noncomputable def ofBijective (f : A ->⋆* B) (hf : Function.Bijective f) : A ≃⋆* B :=
  { MulEquiv.ofBijective f (hf : Function.Bijective (f : A -> B)) with
    toFun := f
    map_star' := map_star f }

@[simp]
/--
theorem `coe_ofBijective` / 定理 `coe_ofBijective`

English:
theorem coe_ofBijective
  given: {f : A ->⋆* B} (hf : Function.Bijective f)
  proof: rfl

中文:
定理 coe_ofBijective
  条件: {f : A ->⋆* B} (hf : Function.Bijective f)
  证明: rfl
-/
theorem coe_ofBijective {f : A ->⋆* B} (hf : Function.Bijective f) :
    (StarMulEquiv.ofBijective f hf : A -> B) = f :=
  rfl

/--
theorem `ofBijective_apply` / 定理 `ofBijective_apply`

English:
theorem ofBijective_apply
  given: {f : A ->⋆* B} (hf : Function.Bijective f) (a : A)
  proof: rfl

中文:
定理 ofBijective_apply
  条件: {f : A ->⋆* B} (hf : Function.Bijective f) (a : A)
  证明: rfl
-/
theorem ofBijective_apply {f : A ->⋆* B} (hf : Function.Bijective f) (a : A) :
    StarMulEquiv.ofBijective f hf a = f a :=
  rfl

end Bijective

end StarMulEquiv
