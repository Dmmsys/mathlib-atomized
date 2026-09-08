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

/-- A *star monoid homomorphism* is a monoid homomorphism which is `star`-preserving. -/
/-
**StarMonoidHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_6) → (B : Type u_7) → [Monoid A] → [Star A] → [Monoid B] → [St
ar B] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *star monoid homomorphism* is a monoid homomorphism which is `star`-preserving
.
-/
structure StarMonoidHom (A B : Type*) [Monoid A] [Star A] [Monoid B] [Star B]
    extends A →* B where
  /-- By definition, a star monoid homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

/-- `α →⋆* β` denotes the type of star monoid homomorphisms from `α` to `β`. -/
infixr:25 " →⋆* " => StarMonoidHom

/-- Reinterpret a star monoid homomorphism as a monoid homomorphism
by forgetting the interaction with the star operation. -/
add_decl_doc StarMonoidHom.toMonoidHom

namespace StarMonoidHom

variable [Monoid A] [Star A] [Monoid B] [Star B]

/-
**StarMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `StarMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (A →⋆* B) A B where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; simp_all
/-
**StarMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `StarMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidHomClass (A →⋆* B) A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
/-
**StarMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `StarMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarHomClass (A →⋆* B) A B where
  map_star f := f.map_star'

/-- See Note [custom simps projection] -/
/-
**StarMonoidHom.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `StarMonoidHom.Simps`。
形式化陈述：{A : Type u_2} →   {B : Type u_3} → [inst : Monoid A] → [inst_1 : Star A] 
→ [inst_2 : Monoid B] → [inst_3 : Star B] → (A →⋆* B) → A → B
参数：A →⋆* B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.coe (f : A →⋆* B) : A → B := f

initialize_simps_projections StarMonoidHom (toFun → coe)

/-- Construct a `StarMonoidHom` from a morphism in some type which preserves `1`, `*` and `star`. -/
@[simps]
/-
**StarMonoidHom.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `StarMonoidHom`。
形式化陈述：ofClass [FunLike F A B] [MonoidHomClass F A B] [StarHomClass F A B] (f : F
) : A ->⋆* B where toFun
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…

--- 原说明 ---
Construct a `StarMonoidHom` from a morphism in some type which preserves `1`, `*
` and `star`.
-/
def ofClass [FunLike F A B] [MonoidHomClass F A B] [StarHomClass F A B] (f : F) :
    A →⋆* B where
  toFun := f
  map_one' := map_one f
  map_mul' := map_mul f
  map_star' := map_star f

@[simp]
/-
**StarMonoidHom.coe_toMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：coe_toMonoidHom (f : A ->⋆* B) : ⇑f.toMonoidHom = f
参数：f : A ->⋆* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toMonoidHom (f : A →⋆* B) : ⇑f.toMonoidHom = f :=
  rfl

@[ext]
/-
**StarMonoidHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：ext {f g : A ->⋆* B} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : A →⋆* B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `StarMonoidHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
/-
**StarMonoidHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `StarMonoidHom`。
形式化陈述：{A : Type u_2} →   {B : Type u_3} →     [inst : Monoid A] →       [inst_1 
: Star A] → [inst_2 : Monoid B] → [inst_3 : Star B] → (f : A →⋆* B) → (f' : A → 
B) → f' = ⇑f → A →⋆* B
参数：f : A →⋆* B；f' : A → B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `StarMonoidHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities.
-/
protected def copy (f : A →⋆* B) (f' : A → B) (h : f' = f) : A →⋆* B where
  toFun := f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
/-
**StarMonoidHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：coe_copy (f : A ->⋆* B) (f' : A -> B) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : A ->⋆* B；f' : A -> B；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : A →⋆* B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**StarMonoidHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：copy_eq (f : A ->⋆* B) (f' : A -> B) (h : f' = f) : f.copy f' h = f
参数：f : A ->⋆* B；f' : A -> B；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : A →⋆* B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/-
**StarMonoidHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：coe_mk (f : A ->* B) (h) : ((⟨f, h⟩ : A ->⋆* B) : A -> B) = f
参数：f : A ->* B；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : A →* B) (h) : ((⟨f, h⟩ : A →⋆* B) : A → B) = f := rfl

section Id

variable (A)

/-- The identity as a star monoid homomorphism. -/
/-
**StarMonoidHom.id** 是 Mathlib 中的一个定义，位于命名空间 `StarMonoidHom`。
形式化陈述：(A : Type u_2) → [inst : Monoid A] → [inst_1 : Star A] → A →⋆* A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a star monoid homomorphism.
-/
protected def id : A →⋆* A :=
  { (.id A : A →* A) with map_star' := fun _ ↦ rfl }

@[simp, norm_cast]
/-
**StarMonoidHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：coe_id : ⇑(StarMonoidHom.id A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(StarMonoidHom.id A) = id :=
  rfl

end Id

section Comp

variable [Monoid C] [Star C] [Monoid D] [Star D]

/-- The composition of star monoid homomorphisms, as a star monoid homomorphism. -/
/-
**StarMonoidHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `StarMonoidHom`。
形式化陈述：comp (f : B ->⋆* C) (g : A ->⋆* B) : A ->⋆* C
参数：f : B ->⋆* C；g : A ->⋆* B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of star monoid homomorphisms, as a star monoid homomorphism.
-/
def comp (f : B →⋆* C) (g : A →⋆* B) : A →⋆* C :=
  { f.toMonoidHom.comp g.toMonoidHom with
    map_star' := fun a => by simp [map_star] }

@[simp]
/-
**StarMonoidHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：coe_comp (f : B ->⋆* C) (g : A ->⋆* B) : ⇑(comp f g) = f ∘ g
参数：f : B ->⋆* C；g : A ->⋆* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : B →⋆* C) (g : A →⋆* B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/-
**StarMonoidHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：comp_apply (f : B ->⋆* C) (g : A ->⋆* B) (a : A) : comp f g a = f (g a)
参数：f : B ->⋆* C；g : A ->⋆* B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : B →⋆* C) (g : A →⋆* B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
/-
**StarMonoidHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：comp_assoc (f : C ->⋆* D) (g : B ->⋆* C) (h : A ->⋆* B) : (f.comp g).comp 
h = f.comp (g.comp h)
参数：f : C ->⋆* D；g : B ->⋆* C；h : A ->⋆* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : C →⋆* D) (g : B →⋆* C) (h : A →⋆* B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**StarMonoidHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：id_comp (f : A ->⋆* B) : (StarMonoidHom.id B).comp f = f
参数：f : A ->⋆* B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarMonoidHom.ext`：ext {f g : A ->⋆* B} (h : forall x, f x = g x) : f = 
g
-/
theorem id_comp (f : A →⋆* B) : (StarMonoidHom.id B).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**StarMonoidHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：comp_id (f : A ->⋆* B) : f.comp (.id _) = f
参数：f : A ->⋆* B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarMonoidHom.ext`：ext {f g : A ->⋆* B} (h : forall x, f x = g x) : f = 
g
-/
theorem comp_id (f : A →⋆* B) : f.comp (.id _) = f :=
  ext fun _ => rfl
/-
**StarMonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `StarMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (A →⋆* A) where
  mul := comp
  mul_assoc := comp_assoc
  one := .id A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
/-
**StarMonoidHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：coe_one : ((1 : A ->⋆* A) : A -> A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : A →⋆* A) : A → A) = id :=
  rfl
/-
**StarMonoidHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarMonoidHom`。
形式化陈述：one_apply (a : A) : (1 : A ->⋆* A) a = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (a : A) : (1 : A →⋆* A) a = a :=
  rfl

end Comp

end StarMonoidHom

/-! ### Star monoid equivalences -/

/-- A *star monoid equivalence* is an equivalence preserving multiplication and the star
operation. -/
/-
**StarMulEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_6) → (B : Type u_7) → [Mul A] → [Mul B] → [Star A] → [Star B] 
→ Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *star monoid equivalence* is an equivalence preserving multiplication and the 
star
operation.
-/
structure StarMulEquiv (A B : Type*) [Mul A] [Mul B] [Star A] [Star B]
    extends A ≃* B where
  /-- By definition, a star monoid equivalence preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

@[inherit_doc] notation:25 A " ≃⋆* " B => StarMulEquiv A B

/-- Reinterpret a star monoid equivalence as a `MulEquiv` by forgetting the interaction with the
star operation. -/
add_decl_doc StarMulEquiv.toMulEquiv

namespace StarMulEquiv

section Basic

variable [Mul A] [Mul B] [Mul C] [Mul D]
variable [Star A] [Star B] [Star C] [Star D]

/-
**StarMulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarMulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (A ≃⋆* B) A B where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' f g h := by cases f; cases g; simp_all
/-
**StarMulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarMulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulEquivClass (A ≃⋆* B) A B where
  map_mul f := f.map_mul'
/-
**StarMulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarMulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarHomClass (A ≃⋆* B) A B where
  map_star f := f.map_star'

@[ext]
/-
**StarMulEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：ext {f g : A ≃⋆* B} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : A ≃⋆* B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

variable (A) in
/-- The identity map as a star monoid isomorphism. -/
@[refl]
/-
**StarMulEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `StarMulEquiv`。
形式化陈述：(A : Type u_2) → [inst : Mul A] → [inst_1 : Star A] → A ≃⋆* A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map as a star monoid isomorphism.
-/
protected def refl : A ≃⋆* A :=
  { MulEquiv.refl A with
    map_star' := fun _ => rfl }
/-
**StarMulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarMulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (A ≃⋆* A) :=
  ⟨.refl A⟩

@[simp]
/-
**StarMulEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：coe_refl : ⇑(.refl A : A ≃⋆* A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- See Note [custom simps projection] -/
/-
**StarMulEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `StarMulEquiv.Simps`。
形式化陈述：{A : Type u_2} →   {B : Type u_3} → [inst : Mul A] → [inst_1 : Mul B] → [i
nst_2 : Star A] → [inst_3 : Star B] → (A ≃⋆* B) → A → B
参数：A ≃⋆* B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply (e : A ≃⋆* B) : A → B := e

/-- See Note [custom simps projection] -/
/-
**StarMulEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `StarMulEquiv.Simps`。
形式化陈述：{A : Type u_2} →   {B : Type u_3} → [inst : Mul A] → [inst_1 : Mul B] → [i
nst_2 : Star A] → [inst_3 : Star B] → (A ≃⋆* B) → B → A
参数：A ≃⋆* B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : A ≃⋆* B) : B → A :=
  e.symm

initialize_simps_projections StarMulEquiv (toFun → apply, invFun → symm_apply)

@[simp]
/-
**StarMulEquiv.invFun_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：invFun_eq_symm {e : A ≃⋆* B} : EquivLike.inv e = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_symm {e : A ≃⋆* B} : EquivLike.inv e = e.symm :=
  rfl

@[simp]
/-
**StarMulEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：symm_symm (e : A ≃⋆* B) : e.symm.symm = e
参数：e : A ≃⋆* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : A ≃⋆* B) : e.symm.symm = e := rfl
/-
**StarMulEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：symm_bijective : Function.Bijective (symm : (A ≃⋆* B) -> B ≃⋆* A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `StarMulEquiv.symm_symm`：symm_symm (e : A ≃⋆* B) : e.symm.symm = e
-/
theorem symm_bijective : Function.Bijective (symm : (A ≃⋆* B) → B ≃⋆* A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
/-
**StarMulEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：coe_mk (e h₁) : ⇑(⟨e, h₁⟩ : A ≃⋆* B) = e
参数：e h₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (e h₁) : ⇑(⟨e, h₁⟩ : A ≃⋆* B) = e := rfl

/-- Construct a `StarMulEquiv` from an equivalence in some type which preserves `*` and `star`. -/
@[simps]
/-
**StarMulEquiv.ofClass** 是 Mathlib 中的一个定义，位于命名空间 `StarMulEquiv`。
形式化陈述：ofClass [EquivLike F A B] [MulEquivClass F A B] [StarHomClass F A B] (f : 
F) : A ≃⋆* B where toFun
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.left_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : outP
aram (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.LeftInverse (Equiv
Like.inv…
· 使用定理 `EquivLike.right_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : out
Param (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.RightInverse (Equ
ivLike.in…

--- 原说明 ---
Construct a `StarMulEquiv` from an equivalence in some type which preserves `*` 
and `star`.
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
/-
**StarMulEquiv.coe_toMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：coe_toMulEquiv (f : A ≃⋆* B) : ⇑f.toMulEquiv = f
参数：f : A ≃⋆* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toMulEquiv (f : A ≃⋆* B) : ⇑f.toMulEquiv = f :=
  rfl

@[simp]
/-
**StarMulEquiv.toMulEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：toMulEquiv_symm (f : A ≃⋆* B) : f.symm.toMulEquiv = f.toMulEquiv.symm
参数：f : A ≃⋆* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulEquiv_symm (f : A ≃⋆* B) : f.symm.toMulEquiv = f.toMulEquiv.symm :=
  rfl

@[simp]
/-
**StarMulEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：refl_symm : (.refl A : A ≃⋆* A).symm = .refl A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (.refl A : A ≃⋆* A).symm = .refl A :=
  rfl

/-- Transitivity of `StarMulEquiv`. -/
@[trans]
/-
**StarMulEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `StarMulEquiv`。
形式化陈述：trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) : A ≃⋆* C
参数：e₁ : A ≃⋆* B；e₂ : B ≃⋆* C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transitivity of `StarMulEquiv`.
-/
def trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) : A ≃⋆* C :=
  { e₁.toMulEquiv.trans e₂.toMulEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star', e₂.map_star'] }

@[simp]
/-
**StarMulEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：apply_symm_apply (e : A ≃⋆* B) : forall x, e (e.symm x) = x
参数：e : A ≃⋆* B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem apply_symm_apply (e : A ≃⋆* B) : ∀ x, e (e.symm x) = x :=
  e.toMulEquiv.apply_symm_apply

@[simp]
/-
**StarMulEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：symm_apply_apply (e : A ≃⋆* B) : forall x, e.symm (e x) = x
参数：e : A ≃⋆* B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
-/
theorem symm_apply_apply (e : A ≃⋆* B) : ∀ x, e.symm (e x) = x :=
  e.toMulEquiv.symm_apply_apply

@[simp]
/-
**StarMulEquiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：symm_trans_apply (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : C) : (e₁.trans e₂).sym
m x = e₁.symm (e₂.symm x)
参数：e₁ : A ≃⋆* B；e₂ : B ≃⋆* C；x : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
/-
**StarMulEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：coe_trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁
参数：e₁ : A ≃⋆* B；e₂ : B ≃⋆* C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/-
**StarMulEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：trans_apply (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : A) : (e₁.trans e₂) x = e₂ (
e₁ x)
参数：e₁ : A ≃⋆* B；e₂ : B ≃⋆* C；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
/-
**StarMulEquiv.toMulEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：toMulEquiv_trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) : (e₁.trans e₂).toMulEquiv 
= e₁.toMulEquiv.trans e₂.toMulEquiv
参数：e₁ : A ≃⋆* B；e₂ : B ≃⋆* C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulEquiv_trans (e₁ : A ≃⋆* B) (e₂ : B ≃⋆* C) :
    (e₁.trans e₂).toMulEquiv = e₁.toMulEquiv.trans e₂.toMulEquiv :=
  rfl
/-
**StarMulEquiv.leftInverse_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：leftInverse_symm (e : A ≃⋆* B) : Function.LeftInverse e.symm e
参数：e : A ≃⋆* B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem leftInverse_symm (e : A ≃⋆* B) : Function.LeftInverse e.symm e :=
  e.left_inv
/-
**StarMulEquiv.rightInverse_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：rightInverse_symm (e : A ≃⋆* B) : Function.RightInverse e.symm e
参数：e : A ≃⋆* B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem rightInverse_symm (e : A ≃⋆* B) : Function.RightInverse e.symm e :=
  e.right_inv

end Basic

section Bijective

variable [Monoid A] [Monoid B] [Star A] [Star B]

/-- Reinterpret a `StarMulEquiv` as a `StarMonoidHom`. -/
@[simps]
/-
**StarMulEquiv.toStarMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `StarMulEquiv`。
形式化陈述：toStarMonoidHom (f : A ≃⋆* B) : A ->⋆* B where toFun
参数：f : A ≃⋆* B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `StarMulEquiv` as a `StarMonoidHom`.
-/
def toStarMonoidHom (f : A ≃⋆* B) : A →⋆* B where
  toFun := f
  map_one' := map_one f
  map_mul' := map_mul f
  map_star' := map_star f

/-- If a star monoid morphism has an inverse, it is an isomorphism of star monoids. -/
@[simps]
/-
**StarMulEquiv.ofStarMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `StarMulEquiv`。
形式化陈述：ofStarMonoidHom (f : A ->⋆* B) (g : B ->⋆* A) (h₁ : g.comp f = .id _) (h₂ 
: f.comp g = .id _) : A ≃⋆* B where toFun
参数：f : A ->⋆* B；g : B ->⋆* A；h₁ : g.comp f = .id _；h₂ : f.comp g = .id _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a star monoid morphism has an inverse, it is an isomorphism of star monoids.
-/
def ofStarMonoidHom (f : A →⋆* B) (g : B →⋆* A) (h₁ : g.comp f = .id _) (h₂ : f.comp g = .id _) :
    A ≃⋆* B where
  toFun := f
  invFun := g
  left_inv := DFunLike.ext_iff.mp h₁
  right_inv := DFunLike.ext_iff.mp h₂
  map_mul' := map_mul f
  map_star' := map_star f

/-- Promote a bijective star monoid homomorphism to a star monoid equivalence. -/
/-
**StarMulEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `StarMulEquiv`。
形式化陈述：ofBijective (f : A ->⋆* B) (hf : Function.Bijective f) : A ≃⋆* B
参数：f : A ->⋆* B；hf : Function.Bijective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote a bijective star monoid homomorphism to a star monoid equivalence.
-/
noncomputable def ofBijective (f : A →⋆* B) (hf : Function.Bijective f) : A ≃⋆* B :=
  { MulEquiv.ofBijective f (hf : Function.Bijective (f : A → B)) with
    toFun := f
    map_star' := map_star f }

@[simp]
/-
**StarMulEquiv.coe_ofBijective** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：coe_ofBijective {f : A ->⋆* B} (hf : Function.Bijective f) : (StarMulEquiv
.ofBijective f hf : A -> B) = f
参数：hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofBijective {f : A →⋆* B} (hf : Function.Bijective f) :
    (StarMulEquiv.ofBijective f hf : A → B) = f :=
  rfl
/-
**StarMulEquiv.ofBijective_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarMulEquiv`。
形式化陈述：ofBijective_apply {f : A ->⋆* B} (hf : Function.Bijective f) (a : A) : Sta
rMulEquiv.ofBijective f hf a = f a
参数：hf : Function.Bijective f；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBijective_apply {f : A →⋆* B} (hf : Function.Bijective f) (a : A) :
    StarMulEquiv.ofBijective f hf a = f a :=
  rfl

end Bijective

end StarMulEquiv

