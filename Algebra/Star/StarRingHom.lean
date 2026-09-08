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

/-- A *non-unital ⋆-ring homomorphism* is a non-unital ring homomorphism between non-unital
non-associative semirings `A` and `B` equipped with a `star` operation, and this homomorphism is
also `star`-preserving. -/
/-
**NonUnitalStarRingHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) →   (B : Type u_2) →     [NonUnitalNonAssocSemiring A] → [S
tar A] → [NonUnitalNonAssocSemiring B] → [Star B] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *non-unital ⋆-ring homomorphism* is a non-unital ring homomorphism between non
-unital
non-associative semirings `A` and `B` equipped with a `star` operation, and this
 homomorphism is
also `star`-preserving.
-/
structure NonUnitalStarRingHom (A B : Type*) [NonUnitalNonAssocSemiring A]
    [Star A] [NonUnitalNonAssocSemiring B] [Star B] extends A →ₙ+* B where
  /-- By definition, a non-unital ⋆-ring homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

/-- `α →⋆ₙ+* β` denotes the type of non-unital ring homomorphisms from `α` to `β`. -/
infixr:25 " →⋆ₙ+* " => NonUnitalStarRingHom

/-- Reinterpret a non-unital star ring homomorphism as a non-unital ring homomorphism
by forgetting the interaction with the star operation.

Users should not make use of this, but instead utilize the coercion obtained through
the `NonUnitalRingHomClass` instance. -/
add_decl_doc NonUnitalStarRingHom.toNonUnitalRingHom

/-- `NonUnitalStarRingHomClass F A B` states that `F` is a type of non-unital ⋆-ring homomorphisms.
You should also extend this typeclass when you extend `NonUnitalStarRingHom`. -/
/-
**NonUnitalStarRingHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (A : outParam (Type u_2)) →     (B : outParam (Type u_3
)) →       [inst : NonUnitalNonAssocSemiring A] →         [Star A] →           [
inst_2 : NonUnitalNonAssocSemiring B] →             [Star B] → [inst_4 : FunLike
 F A B] → [NonUnitalRingHomClass F A B] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalStarRingHomClass F A B` states that `F` is a type of non-unital ⋆-ring
 homomorphisms.
You should also extend this typeclass when you extend `NonUnitalStarRingHom`.
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
/-
**NonUnitalStarRingHomClass.toNonUnitalStarRingHom** 是 Mathlib 中的一个定义，位于命名空间 `No
nUnitalStarRingHomClass`。
形式化陈述：toNonUnitalStarRingHom [NonUnitalStarRingHomClass F A B] (f : F) : A ->⋆ₙ+
* B
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an element of a type `F` satisfying `NonUnitalStarRingHomClass F A B` into 
an actual
`NonUnitalStarRingHom`. This is declared as the default coercion from `F` to `A 
→⋆ₙ+ B`.
-/
def toNonUnitalStarRingHom [NonUnitalStarRingHomClass F A B] (f : F) : A →⋆ₙ+* B :=
  { (f : A →ₙ+* B) with
    map_star' := map_star f }
/-
**NonUnitalStarRingHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarRingHomClas
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalStarRingHomClass F A B] : CoeHead F (A →⋆ₙ+* B) :=
  ⟨toNonUnitalStarRingHom⟩

end NonUnitalStarRingHomClass

namespace NonUnitalStarRingHom

section Basic

variable {A B C D : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Star C]
variable [NonUnitalNonAssocSemiring D] [Star D]

/-
**NonUnitalStarRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (A →⋆ₙ+* B) A B where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr
/-
**NonUnitalStarRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonUnitalRingHomClass (A →⋆ₙ+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'
/-
**NonUnitalStarRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonUnitalStarRingHomClass (A →⋆ₙ+* B) A B where
  map_star f := f.map_star'

/-- See Note [custom simps projection] -/
/-
**NonUnitalStarRingHom.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarRingH
om.Simps`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     [inst : NonUnitalNonAssocSemiring 
A] →       [inst_1 : Star A] → [inst_2 : NonUnitalNonAssocSemiring B] → [inst_3 
: Star B] → (A →⋆ₙ+* B) → A → B
参数：A →⋆ₙ+* B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply (f : A →⋆ₙ+* B) : A → B := f

initialize_simps_projections NonUnitalStarRingHom (toFun → apply)

@[simp]
/-
**NonUnitalStarRingHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [inst : NonUnitalNonAssocSemiring A] [inst
_1 : Star A]   [inst_2 : NonUnitalNonAssocSemiring B] [inst_3 : Star B] {F : Typ
e u_5} [inst_4 : FunLike F A B]   [inst_5 : NonUnitalRingHomClass F A B] [inst_6
 : NonUnitalStarRingHomClass F A B] (f : F), ⇑↑f = ⇑f
参数：f : F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_coe {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B]
    [NonUnitalStarRingHomClass F A B] (f : F) : ⇑(f : A →⋆ₙ+* B) = f :=
  rfl

@[simp]
/-
**NonUnitalStarRingHom.coe_toNonUnitalRingHom** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alStarRingHom`。
形式化陈述：coe_toNonUnitalRingHom (f : A ->⋆ₙ+* B) : ⇑f.toNonUnitalRingHom = f
参数：f : A ->⋆ₙ+* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalRingHom (f : A →⋆ₙ+* B) : ⇑f.toNonUnitalRingHom = f :=
  rfl

@[ext]
/-
**NonUnitalStarRingHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：ext {f g : A ->⋆ₙ+* B} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : A →⋆ₙ+* B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `NonUnitalStarRingHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
/-
**NonUnitalStarRingHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     [inst : NonUnitalNonAssocSemiring 
A] →       [inst_1 : Star A] →         [inst_2 : NonUnitalNonAssocSemiring B] → 
          [inst_3 : Star B] → (f : A →⋆ₙ+* B) → (f' : A → B) → f' = ⇑f → A →⋆ₙ+*
 B
参数：f : A →⋆ₙ+* B；f' : A → B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `NonUnitalStarRingHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities.
-/
protected def copy (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : A →⋆ₙ+* B where
  toFun := f'
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[simp]
/-
**NonUnitalStarRingHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`
。
形式化陈述：coe_copy (f : A ->⋆ₙ+* B) (f' : A -> B) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : A ->⋆ₙ+* B；f' : A -> B；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**NonUnitalStarRingHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：copy_eq (f : A ->⋆ₙ+* B) (f' : A -> B) (h : f' = f) : f.copy f' h = f
参数：f : A ->⋆ₙ+* B；f' : A -> B；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
/-
**NonUnitalStarRingHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：coe_mk (f : A ->ₙ+* B) (h) : ((⟨f, h⟩ : A ->⋆ₙ+* B) : A -> B) = f
参数：f : A ->ₙ+* B；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : A →ₙ+* B) (h) : ((⟨f, h⟩ : A →⋆ₙ+* B) : A → B) = f := rfl

@[simp]
/-
**NonUnitalStarRingHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：mk_coe (f : A ->⋆ₙ+* B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A ->⋆ₙ+
* B) = f
参数：f : A ->⋆ₙ+* B；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarRingHom.ext`：ext {f g : A ->⋆ₙ+* B} (h : forall x, f x = g 
x) : f = g
-/
theorem mk_coe (f : A →⋆ₙ+* B) (h₁ h₂ h₃ h₄) :
    (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →⋆ₙ+* B) = f := by
  ext
  rfl

section

variable (A)

/-- The identity as a non-unital ⋆-ring homomorphism. -/
/-
**NonUnitalStarRingHom.id** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：(A : Type u_1) → [inst : NonUnitalNonAssocSemiring A] → [inst_1 : Star A] 
→ A →⋆ₙ+* A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a non-unital ⋆-ring homomorphism.
-/
protected def id : A →⋆ₙ+* A :=
  { (1 : A →ₙ+* A) with map_star' := fun _ => rfl }

@[simp, norm_cast]
/-
**NonUnitalStarRingHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：coe_id : ⇑(NonUnitalStarRingHom.id A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(NonUnitalStarRingHom.id A) = id :=
  rfl

end

/-- The composition of non-unital ⋆-ring homomorphisms, as a non-unital ⋆-ring homomorphism. -/
/-
**NonUnitalStarRingHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：comp (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B) : A ->⋆ₙ+* C
参数：f : B ->⋆ₙ+* C；g : A ->⋆ₙ+* B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of non-unital ⋆-ring homomorphisms, as a non-unital ⋆-ring homom
orphism.
-/
def comp (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) : A →⋆ₙ+* C :=
  { f.toNonUnitalRingHom.comp g.toNonUnitalRingHom with
    map_star' := fun a => by simp [map_star, map_star] }

@[simp]
/-
**NonUnitalStarRingHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`
。
形式化陈述：coe_comp (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B) : ⇑(comp f g) = f ∘ g
参数：f : B ->⋆ₙ+* C；g : A ->⋆ₙ+* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
/-
**NonUnitalStarRingHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHo
m`。
形式化陈述：comp_apply (f : B ->⋆ₙ+* C) (g : A ->⋆ₙ+* B) (a : A) : comp f g a = f (g a
)
参数：f : B ->⋆ₙ+* C；g : A ->⋆ₙ+* B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) (a : A) : comp f g a = f (g a) :=
  rfl

@[simp]
/-
**NonUnitalStarRingHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHo
m`。
形式化陈述：comp_assoc (f : C ->⋆ₙ+* D) (g : B ->⋆ₙ+* C) (h : A ->⋆ₙ+* B) : (f.comp g)
.comp h = f.comp (g.comp h)
参数：f : C ->⋆ₙ+* D；g : B ->⋆ₙ+* C；h : A ->⋆ₙ+* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : C →⋆ₙ+* D) (g : B →⋆ₙ+* C) (h : A →⋆ₙ+* B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**NonUnitalStarRingHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：id_comp (f : A ->⋆ₙ+* B) : (NonUnitalStarRingHom.id _).comp f = f
参数：f : A ->⋆ₙ+* B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarRingHom.ext`：ext {f g : A ->⋆ₙ+* B} (h : forall x, f x = g 
x) : f = g
-/
theorem id_comp (f : A →⋆ₙ+* B) : (NonUnitalStarRingHom.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**NonUnitalStarRingHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：comp_id (f : A ->⋆ₙ+* B) : f.comp (NonUnitalStarRingHom.id _) = f
参数：f : A ->⋆ₙ+* B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarRingHom.ext`：ext {f g : A ->⋆ₙ+* B} (h : forall x, f x = g 
x) : f = g
-/
theorem comp_id (f : A →⋆ₙ+* B) : f.comp (NonUnitalStarRingHom.id _) = f :=
  ext fun _ => rfl
/-
**NonUnitalStarRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (A →⋆ₙ+* A) where
  mul := comp
  mul_assoc := comp_assoc
  one := NonUnitalStarRingHom.id A
  one_mul := id_comp
  mul_one := comp_id

@[simp]
/-
**NonUnitalStarRingHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`。
形式化陈述：coe_one : ((1 : A ->⋆ₙ+* A) : A -> A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : A →⋆ₙ+* A) : A → A) = id :=
  rfl
/-
**NonUnitalStarRingHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom
`。
形式化陈述：one_apply (a : A) : (1 : A ->⋆ₙ+* A) a = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (a : A) : (1 : A →⋆ₙ+* A) a = a :=
  rfl

end Basic

section Zero

-- the `zero` requires extra type class assumptions because we need `star_zero`
variable {A B C : Type*}
variable [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
variable [NonUnitalNonAssocSemiring B] [StarAddMonoid B]

/-
**NonUnitalStarRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (A →⋆ₙ+* B) :=
  ⟨{ (0 : NonUnitalRingHom A B) with map_star' := by simp }⟩
/-
**NonUnitalStarRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (A →⋆ₙ+* B) :=
  ⟨0⟩
/-
**NonUnitalStarRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidWithZero (A →⋆ₙ+* A) where
  zero_mul := fun _ => ext fun _ => rfl
  mul_zero := fun f => ext fun _ => map_zero f

@[simp]
/-
**NonUnitalStarRingHom.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHom`
。
形式化陈述：coe_zero : ((0 : A ->⋆ₙ+* B) : A -> B) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : A →⋆ₙ+* B) : A → B) = 0 :=
  rfl
/-
**NonUnitalStarRingHom.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalStarRingHo
m`。
形式化陈述：zero_apply (a : A) : (0 : A ->⋆ₙ+* B) a = 0
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (a : A) : (0 : A →⋆ₙ+* B) a = 0 :=
  rfl

end Zero


end NonUnitalStarRingHom

/-! ### Star ring equivalences -/

/-- A *⋆-ring* equivalence is an equivalence preserving addition, multiplication, and the star
operation, which allows for considering both unital and non-unital equivalences with a single
structure. -/
/-
**StarRingEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) → (B : Type u_2) → [Add A] → [Add B] → [Mul A] → [Mul B] → 
[Star A] → [Star B] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *⋆-ring* equivalence is an equivalence preserving addition, multiplication, an
d the star
operation, which allows for considering both unital and non-unital equivalences 
with a single
structure.
-/
structure StarRingEquiv (A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B]
    extends A ≃+* B where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

@[inherit_doc] notation:25 A " ≃⋆+* " B => StarRingEquiv A B

/-- Reinterpret a star ring equivalence as a `RingEquiv` by forgetting the interaction with the star
operation. -/
add_decl_doc StarRingEquiv.toRingEquiv

/-- `StarRingEquivClass F A B` asserts `F` is a type of bundled ⋆-ring equivalences between `A` and
`B`.
You should also extend this typeclass when you extend `StarRingEquiv`. -/
/-
**StarRingEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (A : outParam (Type u_2)) →     (B : outParam (Type u_3
)) → [Add A] → [Mul A] → [Star A] → [Add B] → [Mul B] → [Star B] → [EquivLike F 
A B] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`StarRingEquivClass F A B` asserts `F` is a type of bundled ⋆-ring equivalences 
between `A` and
`B`.
You should also extend this typeclass when you extend `StarRingEquiv`.
-/
class StarRingEquivClass (F : Type*) (A B : outParam Type*)
    [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B] [EquivLike F A B] : Prop
    extends RingEquivClass F A B where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star : ∀ (f : F) (a : A), f (star a) = star (f a)

namespace StarRingEquivClass

-- See note [lower instance priority]
/-
**StarRingEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `StarRingEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 50) {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [hF : StarRingEquivClass F A B] :
    StarHomClass F A B where
  __ := hF

-- See note [lower instance priority]
/-
**StarRingEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `StarRingEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {F A B : Type*} [NonUnitalNonAssocSemiring A] [Star A]
    [NonUnitalNonAssocSemiring B] [Star B] [EquivLike F A B] [StarRingEquivClass F A B] :
    NonUnitalStarRingHomClass F A B where

/-- Turn an element of a type `F` satisfying `StarRingEquivClass F A B` into an actual
`StarRingEquiv`. This is declared as the default coercion from `F` to `A ≃⋆+* B`. -/
@[coe]
/-
**StarRingEquivClass.toStarRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `StarRingEquivCla
ss`。
形式化陈述：toStarRingEquiv {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [
Star B] [EquivLike F A B] [StarRingEquivClass F A B] (f : F) : A ≃⋆+* B
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StarRingEquivClass.toRingEquivClass`：∀ {F : Type u_1} {A : outParam (Typ
e u_2)} {B : outParam (Type u_3)} {inst : Add A} {inst_1 : Mul A} {inst_2 : Star
 A}   {inst_3 : Add B} {i…
· 使用定理 `StarRingEquivClass.map_star`：∀ {F : Type u_1} {A : outParam (Type u_2)} 
{B : outParam (Type u_3)} {inst : Add A} {inst_1 : Mul A} {inst_2 : Star A}   {i
nst_3 : Add B} {i…

--- 原说明 ---
Turn an element of a type `F` satisfying `StarRingEquivClass F A B` into an actu
al
`StarRingEquiv`. This is declared as the default coercion from `F` to `A ≃⋆+* B`
.
-/
def toStarRingEquiv {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [StarRingEquivClass F A B] (f : F) : A ≃⋆+* B :=
  { (RingEquivClass.toRingEquiv f : A ≃+* B) with
    map_star' := map_star f }

/-- Any type satisfying `StarRingEquivClass` can be cast into `StarRingEquiv` via
`StarRingEquivClass.toStarRingEquiv`. -/
/-
**StarRingEquivClass.instCoeHead** 是 Mathlib 中的一个实例，位于命名空间 `StarRingEquivClass`。
形式化陈述：instCoeHead {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star
 B] [EquivLike F A B] [StarRingEquivClass F A B] : CoeHead F (A ≃⋆+* B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `StarRingEquivClass` can be cast into `StarRingEquiv` via
`StarRingEquivClass.toStarRingEquiv`.
-/
instance instCoeHead {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [StarRingEquivClass F A B] : CoeHead F (A ≃⋆+* B) :=
  ⟨toStarRingEquiv⟩

end StarRingEquivClass

namespace StarRingEquiv

section Basic

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

/-
**StarRingEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarRingEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**StarRingEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarRingEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RingEquivClass (A ≃⋆+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
/-
**StarRingEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarRingEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarRingEquivClass (A ≃⋆+* B) A B where
  map_star := map_star'

/-- Helper instance for cases where the inference via `EquivLike` is too hard. -/
/-
**StarRingEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarRingEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper instance for cases where the inference via `EquivLike` is too hard.
-/
instance : FunLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  coe_injective := DFunLike.coe_injective
/-
**StarRingEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarRingEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (A ≃⋆+* B) (A ≃+* B) where coe := toRingEquiv

@[deprecated "Now a syntactic equality" (since := "2026-04-09"), nolint synTaut]
/-
**StarRingEquiv.toRingEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：toRingEquiv_eq_coe (e : A ≃⋆+* B) : e.toRingEquiv = e
参数：e : A ≃⋆+* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingEquiv_eq_coe (e : A ≃⋆+* B) : e.toRingEquiv = e :=
  rfl

@[ext]
/-
**StarRingEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：ext {f g : A ≃⋆+* B} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : A ≃⋆+* B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- The identity map as a star ring isomorphism. -/
@[refl]
/-
**StarRingEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `StarRingEquiv`。
形式化陈述：refl : A ≃⋆+* A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map as a star ring isomorphism.
-/
def refl : A ≃⋆+* A :=
  { RingEquiv.refl A with
    map_star' := fun _ => rfl }
/-
**StarRingEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `StarRingEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (A ≃⋆+* A) :=
  ⟨refl⟩

@[simp]
/-
**StarRingEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：coe_refl : ⇑(refl : A ≃⋆+* A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- See Note [custom simps projection] -/
/-
**StarRingEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `StarRingEquiv.Simps`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     [inst : Add A] →       [inst_1 : A
dd B] →         [inst_2 : Mul A] → [inst_3 : Mul B] → [inst_4 : Star A] → [inst_
5 : Star B] → (A ≃⋆+* B) → A → B
参数：A ≃⋆+* B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply (e : A ≃⋆+* B) : A → B := e

/-- See Note [custom simps projection] -/
/-
**StarRingEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `StarRingEquiv.Simps`
。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     [inst : Add A] →       [inst_1 : A
dd B] →         [inst_2 : Mul A] → [inst_3 : Mul B] → [inst_4 : Star A] → [inst_
5 : Star B] → (A ≃⋆+* B) → B → A
参数：A ≃⋆+* B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : A ≃⋆+* B) : B → A :=
  e.symm

initialize_simps_projections StarRingEquiv (toFun → apply, invFun → symm_apply)

@[simp]
/-
**StarRingEquiv.invFun_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：invFun_eq_symm {e : A ≃⋆+* B} : EquivLike.inv e = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_symm {e : A ≃⋆+* B} : EquivLike.inv e = e.symm :=
  rfl

@[simp]
/-
**StarRingEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：symm_symm (e : A ≃⋆+* B) : e.symm.symm = e
参数：e : A ≃⋆+* B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : A ≃⋆+* B) : e.symm.symm = e := rfl
/-
**StarRingEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：symm_bijective : Function.Bijective (symm : (A ≃⋆+* B) -> B ≃⋆+* A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `StarRingEquiv.symm_symm`：symm_symm (e : A ≃⋆+* B) : e.symm.symm = e
-/
theorem symm_bijective : Function.Bijective (symm : (A ≃⋆+* B) → B ≃⋆+* A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
/-
**StarRingEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [inst : Add A] [inst_1 : Add B] [inst_2 : 
Mul A] [inst_3 : Mul B] [inst_4 : Star A]   [inst_5 : Star B] (e : A ≃+* B) (h₁ 
: ∀ (a : A), e.toFun (star a) = star (e.toFun a)),   ⇑{ toRingEquiv := e, map_st
ar' := h₁ } = ⇑e
参数：e : A ≃+* B；h₁ : ∀ (a : A), e.toFun (star a) = star (e.toFun a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mk (e h₁) : ⇑(⟨e, h₁⟩ : A ≃⋆+* B) = e := rfl

@[simp]
/-
**StarRingEquiv.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：mk_coe (e : A ≃⋆+* B) (e' h₁ h₂ h₃ h₄ h₅) : (⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h
₅⟩ : A ≃⋆+* B) = e
参数：e : A ≃⋆+* B；e' h₁ h₂ h₃ h₄ h₅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarRingEquiv.ext`：ext {f g : A ≃⋆+* B} (h : forall a, f a = g a) : f = 
g
-/
theorem mk_coe (e : A ≃⋆+* B) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B) = e := ext fun _ => rfl

@[simp]
/-
**StarRingEquiv.symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：symm_mk (e : A ≃+* B) (h₁) : dsimp% (⟨e, h₁⟩ : A ≃⋆+* B).symm = { (⟨e, h₁⟩
 : A ≃⋆+* B).symm with toRingEquiv
参数：e : A ≃+* B；h₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_mk (e : A ≃+* B) (h₁) : dsimp%
    (⟨e, h₁⟩ : A ≃⋆+* B).symm =
      { (⟨e, h₁⟩ : A ≃⋆+* B).symm with
        toRingEquiv := e.symm } :=
  rfl

@[simp]
/-
**StarRingEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：refl_symm : (StarRingEquiv.refl : A ≃⋆+* A).symm = StarRingEquiv.refl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (StarRingEquiv.refl : A ≃⋆+* A).symm = StarRingEquiv.refl :=
  rfl

/-- Transitivity of `StarRingEquiv`. -/
@[trans]
/-
**StarRingEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `StarRingEquiv`。
形式化陈述：trans (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) : A ≃⋆+* C
参数：e₁ : A ≃⋆+* B；e₂ : B ≃⋆+* C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transitivity of `StarRingEquiv`.
-/
def trans (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) : A ≃⋆+* C :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star', e₂.map_star'] }

@[simp]
/-
**StarRingEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：apply_symm_apply (e : A ≃⋆+* B) : forall x, e (e.symm x) = x
参数：e : A ≃⋆+* B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
-/
theorem apply_symm_apply (e : A ≃⋆+* B) : ∀ x, e (e.symm x) = x :=
  e.toRingEquiv.apply_symm_apply

@[simp]
/-
**StarRingEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：symm_apply_apply (e : A ≃⋆+* B) : forall x, e.symm (e x) = x
参数：e : A ≃⋆+* B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
-/
theorem symm_apply_apply (e : A ≃⋆+* B) : ∀ x, e.symm (e x) = x :=
  e.toRingEquiv.symm_apply_apply

@[simp]
/-
**StarRingEquiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：symm_trans_apply (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : C) : (e₁.trans e₂).s
ymm x = e₁.symm (e₂.symm x)
参数：e₁ : A ≃⋆+* B；e₂ : B ≃⋆+* C；x : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
/-
**StarRingEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：coe_trans (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁
参数：e₁ : A ≃⋆+* B；e₂ : B ≃⋆+* C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
/-
**StarRingEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：trans_apply (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : A) : (e₁.trans e₂) x = e₂
 (e₁ x)
参数：e₁ : A ≃⋆+* B；e₂ : B ≃⋆+* C；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : A ≃⋆+* B) (e₂ : B ≃⋆+* C) (x : A) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl
/-
**StarRingEquiv.leftInverse_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：leftInverse_symm (e : A ≃⋆+* B) : Function.LeftInverse e.symm e
参数：e : A ≃⋆+* B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem leftInverse_symm (e : A ≃⋆+* B) : Function.LeftInverse e.symm e :=
  e.left_inv
/-
**StarRingEquiv.rightInverse_symm** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：rightInverse_symm (e : A ≃⋆+* B) : Function.RightInverse e.symm e
参数：e : A ≃⋆+* B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
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
/-
**StarRingEquiv.ofStarRingHom** 是 Mathlib 中的一个定义，位于命名空间 `StarRingEquiv`。
形式化陈述：ofStarRingHom (f : F) (g : G) (h₁ : forall x, g (f x) = x) (h₂ : forall x,
 f (g x) = x) : A ≃⋆+* B where toFun
参数：f : F；g : G；h₁ : forall x, g (f x) = x；h₂ : forall x, f (g x) = x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a (unital or non-unital) star ring morphism has an inverse, it is an isomorph
ism of
star rings.
-/
def ofStarRingHom (f : F) (g : G) (h₁ : ∀ x, g (f x) = x) (h₂ : ∀ x, f (g x) = x) : A ≃⋆+* B where
  toFun := f
  invFun := g
  left_inv := h₁
  right_inv := h₂
  map_add' := map_add f
  map_mul' := map_mul f
  map_star' := map_star f

/-- Promote a bijective star ring homomorphism to a star ring equivalence. -/
/-
**StarRingEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `StarRingEquiv`。
形式化陈述：ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆+* B
参数：f : F；hf : Function.Bijective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Promote a bijective star ring homomorphism to a star ring equivalence.
-/
noncomputable def ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆+* B :=
  { RingEquiv.ofBijective f (hf : Function.Bijective (f : A → B)) with
    toFun := f
    map_star' := map_star f }

@[simp]
/-
**StarRingEquiv.coe_ofBijective** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：coe_ofBijective {f : F} (hf : Function.Bijective f) : (StarRingEquiv.ofBij
ective f hf : A -> B) = f
参数：hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofBijective {f : F} (hf : Function.Bijective f) :
    (StarRingEquiv.ofBijective f hf : A → B) = f :=
  rfl
/-
**StarRingEquiv.ofBijective_apply** 是 Mathlib 中的一个定理，位于命名空间 `StarRingEquiv`。
形式化陈述：ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) : (StarRingE
quiv.ofBijective f hf) a = f a
参数：hf : Function.Bijective f；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) :
    (StarRingEquiv.ofBijective f hf) a = f a :=
  rfl

end Bijective

end StarRingEquiv

