/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Basic

/-!
# Homomorphisms of semirings and rings

This file defines bundled homomorphisms of (non-unital) semirings and rings. As with monoid and
groups, we use the same structure `RingHom a β`, a.k.a. `α →+* β`, for both types of homomorphisms.

## Main definitions

* `NonUnitalRingHom`: Non-unital (semi)ring homomorphisms. Additive monoid homomorphism which
  preserve multiplication.
* `RingHom`: (Semi)ring homomorphisms. Monoid homomorphisms which are also additive monoid
  homomorphism.

## Notation

* `→ₙ+*`: Non-unital (semi)ring homs
* `→+*`: (Semi)ring homs

## Implementation notes

* There's a coercion from bundled homs to fun, and the canonical notation is to
  use the bundled hom as a function via this coercion.

* There is no `SemiringHom` -- the idea is that `RingHom` is used.
  The constructor for a `RingHom` between semirings needs a proof of `map_zero`,
  `map_one` and `map_add` as well as `map_mul`; a separate constructor
  `RingHom.mk'` will construct ring homs between rings from monoid homs given
  only a proof that addition is preserved.

## Tags

`RingHom`, `SemiringHom`
-/

@[expose] public section

assert_not_exists Function.Injective.mulZeroClass semigroupDvd Units.map

open Function

variable {F α β γ : Type*}

/-- Bundled non-unital semiring homomorphisms `α →ₙ+* β`; use this for bundled non-unital ring
homomorphisms too.

When possible, instead of parametrizing results over `(f : α →ₙ+* β)`,
you should parametrize over `(F : Type*) [NonUnitalRingHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `NonUnitalRingHomClass`. -/
/-
**NonUnitalRingHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_5) → (β : Type u_6) → [NonUnitalNonAssocSemiring α] → [NonUnit
alNonAssocSemiring β] → Type (max u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled non-unital semiring homomorphisms `α →ₙ+* β`; use this for bundled non-u
nital ring
homomorphisms too.

When possible, instead of parametrizing results over `(f : α →ₙ+* β)`,
you should parametrize over `(F : Type*) [NonUnitalRingHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `NonUnitalRingHomClass`.
-/
structure NonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] extends α →ₙ* β, α →+ β

/-- `α →ₙ+* β` denotes the type of non-unital ring homomorphisms from `α` to `β`. -/
infixr:25 " →ₙ+* " => NonUnitalRingHom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as a semigroup
homomorphism `α →ₙ* β`. The `simp`-normal form is `(f : α →ₙ* β)`. -/
add_decl_doc NonUnitalRingHom.toMulHom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as an additive
monoid homomorphism `α →+ β`. The `simp`-normal form is `(f : α →+ β)`. -/
add_decl_doc NonUnitalRingHom.toAddMonoidHom

section NonUnitalRingHomClass

/-- `NonUnitalRingHomClass F α β` states that `F` is a type of non-unital (semi)ring
homomorphisms. You should extend this class when you extend `NonUnitalRingHom`. -/
/-
**NonUnitalRingHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_5) →   (α : outParam (Type u_6)) →     (β : outParam (Type u_7
)) → [NonUnitalNonAssocSemiring α] → [NonUnitalNonAssocSemiring β] → [FunLike F 
α β] → Prop
参数：Type u_6；Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalRingHomClass F α β` states that `F` is a type of non-unital (semi)ring
homomorphisms. You should extend this class when you extend `NonUnitalRingHom`.
-/
class NonUnitalRingHomClass (F : Type*) (α β : outParam Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] [FunLike F α β] : Prop
  extends MulHomClass F α β, AddMonoidHomClass F α β

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [FunLike F α β]
variable [NonUnitalRingHomClass F α β]

/-- Turn an element of a type `F` satisfying `NonUnitalRingHomClass F α β` into an actual
`NonUnitalRingHom`. This is declared as the default coercion from `F` to `α →ₙ+* β`. -/
@[coe]
/-
**NonUnitalRingHomClass.toNonUnitalRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalRingHomClass.toNonUnitalRingHom (f : F) : α ->ₙ+* β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…

--- 原说明 ---
Turn an element of a type `F` satisfying `NonUnitalRingHomClass F α β` into an a
ctual
`NonUnitalRingHom`. This is declared as the default coercion from `F` to `α →ₙ+*
 β`.
-/
def NonUnitalRingHomClass.toNonUnitalRingHom (f : F) : α →ₙ+* β :=
  { (f : α →ₙ* β), (f : α →+ β) with }

/-- Any type satisfying `NonUnitalRingHomClass` can be cast into `NonUnitalRingHom` via
`NonUnitalRingHomClass.toNonUnitalRingHom`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `NonUnitalRingHomClass` can be cast into `NonUnitalRingHom` 
via
`NonUnitalRingHomClass.toNonUnitalRingHom`.
-/
instance : CoeTC F (α →ₙ+* β) :=
  ⟨NonUnitalRingHomClass.toNonUnitalRingHom⟩

end NonUnitalRingHomClass

namespace NonUnitalRingHom

section coe

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

/-
**NonUnitalRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (α →ₙ+* β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h
/-
**NonUnitalRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonUnitalRingHomClass (α →ₙ+* β) α β where
  map_add := NonUnitalRingHom.map_add'
  map_zero := NonUnitalRingHom.map_zero'
  map_mul f := f.map_mul'

initialize_simps_projections NonUnitalRingHom (toFun → apply)

@[simp]
/-
**NonUnitalRingHom.coe_toMulHom** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_toMulHom (f : α ->ₙ+* β) : ⇑f.toMulHom = f
参数：f : α ->ₙ+* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toMulHom (f : α →ₙ+* β) : ⇑f.toMulHom = f :=
  rfl

@[simp]
/-
**NonUnitalRingHom.coe_mulHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_mulHom_mk (f : α -> β) (h₁ h₂ h₃) : ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α ->ₙ+* β) :
 α ->ₙ* β) = ⟨f, h₁⟩
参数：f : α -> β；h₁ h₂ h₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
-/
theorem coe_mulHom_mk (f : α → β) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α →ₙ+* β) : α →ₙ* β) = ⟨f, h₁⟩ :=
  rfl
/-
**NonUnitalRingHom.coe_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHo
m`。
形式化陈述：coe_toAddMonoidHom (f : α ->ₙ+* β) : ⇑f.toAddMonoidHom = f
参数：f : α ->ₙ+* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAddMonoidHom (f : α →ₙ+* β) : ⇑f.toAddMonoidHom = f := rfl

@[simp]
/-
**NonUnitalRingHom.coe_addMonoidHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingH
om`。
形式化陈述：coe_addMonoidHom_mk (f : α -> β) (h₁ h₂ h₃) : ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α ->ₙ+
* β) : α ->+ β) = ⟨⟨f, h₂⟩, h₃⟩
参数：f : α -> β；h₁ h₂ h₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
-/
theorem coe_addMonoidHom_mk (f : α → β) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α →ₙ+* β) : α →+ β) = ⟨⟨f, h₂⟩, h₃⟩ :=
  rfl

/-- Copy of a `RingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**NonUnitalRingHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : NonUnitalNonAssocSemiring 
α] →       [inst_1 : NonUnitalNonAssocSemiring β] → (f : α →ₙ+* β) → (f' : α → β
) → f' = ⇑f → α →ₙ+* β
参数：f : α →ₙ+* β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `RingHom` with a new `toFun` equal to the old one. Useful to fix defin
itional
equalities.
-/
protected def copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : α →ₙ+* β :=
  { f.toMulHom.copy f' h, f.toAddMonoidHom.copy f' h with }

@[simp]
/-
**NonUnitalRingHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_copy (f : α ->ₙ+* β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : α ->ₙ+* β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**NonUnitalRingHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：copy_eq (f : α ->ₙ+* β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : α ->ₙ+* β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

end coe

section

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

@[ext]
/-
**NonUnitalRingHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : α →ₙ+* β⦄ : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

@[simp]
/-
**NonUnitalRingHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：mk_coe (f : α ->ₙ+* β) (h₁ h₂ h₃) : NonUnitalRingHom.mk (MulHom.mk f h₁) h
₂ h₃ = f
参数：f : α ->ₙ+* β；h₁ h₂ h₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
-/
theorem mk_coe (f : α →ₙ+* β) (h₁ h₂ h₃) : NonUnitalRingHom.mk (MulHom.mk f h₁) h₂ h₃ = f :=
  ext fun _ => rfl
/-
**NonUnitalRingHom.coe_addMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alRingHom`。
形式化陈述：coe_addMonoidHom_injective : Injective fun f : α ->ₙ+* β => (f : α ->+ β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_addMonoidHom_injective : Injective fun f : α →ₙ+* β => (f : α →+ β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective
/-
**NonUnitalRingHom.coe_mulHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRing
Hom`。
形式化陈述：coe_mulHom_injective : Injective fun f : α ->ₙ+* β => (f : α ->ₙ* β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_mulHom_injective : Injective fun f : α →ₙ+* β => (f : α →ₙ* β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

end

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

/-- The identity non-unital ring homomorphism from a non-unital semiring to itself. -/
@[instance_reducible]
/-
**NonUnitalRingHom.id** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：(α : Type u_5) → [inst : NonUnitalNonAssocSemiring α] → α →ₙ+* α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity non-unital ring homomorphism from a non-unital semiring to itself.
-/
protected def id (α : Type*) [NonUnitalNonAssocSemiring α] : α →ₙ+* α where
  toFun x := x
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
/-
**NonUnitalRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (α →ₙ+* β) :=
  ⟨{ toFun := 0, map_mul' := fun _ _ => (mul_zero (0 : β)).symm, map_zero' := rfl,
      map_add' := fun _ _ => (add_zero (0 : β)).symm }⟩
/-
**NonUnitalRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α →ₙ+* β) :=
  ⟨0⟩

@[simp]
/-
**NonUnitalRingHom.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_zero : ⇑(0 : α ->ₙ+* β) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : α →ₙ+* β) = 0 :=
  rfl

@[simp]
/-
**NonUnitalRingHom.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：zero_apply (x : α) : (0 : α ->ₙ+* β) x = 0
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (x : α) : (0 : α →ₙ+* β) x = 0 :=
  rfl

@[simp]
/-
**NonUnitalRingHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：id_apply (x : α) : NonUnitalRingHom.id α x = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : α) : NonUnitalRingHom.id α x = x :=
  rfl

@[simp]
/-
**NonUnitalRingHom.coe_addMonoidHom_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingH
om`。
形式化陈述：coe_addMonoidHom_id : (NonUnitalRingHom.id α : α ->+ α) = AddMonoidHom.id 
α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
-/
theorem coe_addMonoidHom_id : (NonUnitalRingHom.id α : α →+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
/-
**NonUnitalRingHom.coe_mulHom_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_mulHom_id : (NonUnitalRingHom.id α : α ->ₙ* α) = MulHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
-/
theorem coe_mulHom_id : (NonUnitalRingHom.id α : α →ₙ* α) = MulHom.id α :=
  rfl

variable [NonUnitalNonAssocSemiring γ]

/-- Composition of non-unital ring homomorphisms is a non-unital ring homomorphism. -/
@[instance_reducible]
/-
**NonUnitalRingHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：comp (g : β ->ₙ+* γ) (f : α ->ₙ+* β) : α ->ₙ+* γ
参数：g : β ->ₙ+* γ；f : α ->ₙ+* β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of non-unital ring homomorphisms is a non-unital ring homomorphism.
-/
def comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : α →ₙ+* γ :=
  { g.toMulHom.comp f.toMulHom, g.toAddMonoidHom.comp f.toAddMonoidHom with }

/-- Composition of non-unital ring homomorphisms is associative. -/
/-
**NonUnitalRingHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：comp_assoc {δ} {_ : NonUnitalNonAssocSemiring δ} (f : α ->ₙ+* β) (g : β ->
ₙ+* γ) (h : γ ->ₙ+* δ) : (h.comp g).comp f = h.comp (g.comp f)
参数：f : α ->ₙ+* β；g : β ->ₙ+* γ；h : γ ->ₙ+* δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of non-unital ring homomorphisms is associative.
-/
theorem comp_assoc {δ} {_ : NonUnitalNonAssocSemiring δ} (f : α →ₙ+* β) (g : β →ₙ+* γ)
    (h : γ →ₙ+* δ) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/-
**NonUnitalRingHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_comp (g : β ->ₙ+* γ) (f : α ->ₙ+* β) : ⇑(g.comp f) = g ∘ f
参数：g : β ->ₙ+* γ；f : α ->ₙ+* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
/-
**NonUnitalRingHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：comp_apply (g : β ->ₙ+* γ) (f : α ->ₙ+* β) (x : α) : g.comp f x = g (f x)
参数：g : β ->ₙ+* γ；f : α ->ₙ+* β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : β →ₙ+* γ) (f : α →ₙ+* β) (x : α) : g.comp f x = g (f x) :=
  rfl

@[simp]
/-
**NonUnitalRingHom.coe_comp_addMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRin
gHom`。
形式化陈述：coe_comp_addMonoidHom (g : β ->ₙ+* γ) (f : α ->ₙ+* β) : AddMonoidHom.mk ⟨g
 ∘ f, (g.comp f).map_zero'⟩ (g.comp f).map_add' = (g : β ->+ γ).comp f
参数：g : β ->ₙ+* γ；f : α ->ₙ+* β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.map_zero'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonU
nitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   (self : α →ₙ+*
 β), self.toFun …
· 使用定理 `NonUnitalRingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonUn
italNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   (self : α →ₙ+* 
β) (x y : α), s…
-/
theorem coe_comp_addMonoidHom (g : β →ₙ+* γ) (f : α →ₙ+* β) :
    AddMonoidHom.mk ⟨g ∘ f, (g.comp f).map_zero'⟩ (g.comp f).map_add' = (g : β →+ γ).comp f :=
  rfl

@[simp]
/-
**NonUnitalRingHom.coe_comp_mulHom** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_comp_mulHom (g : β ->ₙ+* γ) (f : α ->ₙ+* β) : MulHom.mk (g ∘ f) (g.com
p f).map_mul' = (g : β ->ₙ* γ).comp f
参数：g : β ->ₙ+* γ；f : α ->ₙ+* β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : Mul M] [inst_
1 : Mul N] (self : M →ₙ* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toF…
-/
theorem coe_comp_mulHom (g : β →ₙ+* γ) (f : α →ₙ+* β) :
    MulHom.mk (g ∘ f) (g.comp f).map_mul' = (g : β →ₙ* γ).comp f :=
  rfl

@[simp]
/-
**NonUnitalRingHom.comp_zero** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：comp_zero (g : β ->ₙ+* γ) : g.comp (0 : α ->ₙ+* β) = 0
参数：g : β ->ₙ+* γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_zero (g : β →ₙ+* γ) : g.comp (0 : α →ₙ+* β) = 0 := by
  ext
  simp

@[simp]
/-
**NonUnitalRingHom.zero_comp** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：zero_comp (f : α ->ₙ+* β) : (0 : β ->ₙ+* γ).comp f = 0
参数：f : α ->ₙ+* β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
-/
theorem zero_comp (f : α →ₙ+* β) : (0 : β →ₙ+* γ).comp f = 0 := by
  ext
  rfl

@[simp]
/-
**NonUnitalRingHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：comp_id (f : α ->ₙ+* β) : f.comp (NonUnitalRingHom.id α) = f
参数：f : α ->ₙ+* β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
-/
theorem comp_id (f : α →ₙ+* β) : f.comp (NonUnitalRingHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**NonUnitalRingHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：id_comp (f : α ->ₙ+* β) : (NonUnitalRingHom.id β).comp f = f
参数：f : α ->ₙ+* β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
-/
theorem id_comp (f : α →ₙ+* β) : (NonUnitalRingHom.id β).comp f = f :=
  ext fun _ => rfl
/-
**NonUnitalRingHom.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalRingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidWithZero (α →ₙ+* α) where
  one := NonUnitalRingHom.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
  mul_zero := comp_zero
  zero_mul := zero_comp
/-
**NonUnitalRingHom.one_def** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：one_def : (1 : α ->ₙ+* α) = NonUnitalRingHom.id α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : α →ₙ+* α) = NonUnitalRingHom.id α :=
  rfl

@[simp]
/-
**NonUnitalRingHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_one : ⇑(1 : α ->ₙ+* α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : α →ₙ+* α) = id :=
  rfl
/-
**NonUnitalRingHom.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：mul_def (f g : α ->ₙ+* α) : f * g = f.comp g
参数：f g : α ->ₙ+* α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (f g : α →ₙ+* α) : f * g = f.comp g :=
  rfl

@[simp]
/-
**NonUnitalRingHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_mul (f g : α ->ₙ+* α) : ⇑(f * g) = f ∘ g
参数：f g : α ->ₙ+* α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g : α →ₙ+* α) : ⇑(f * g) = f ∘ g :=
  rfl

@[simp]
/-
**NonUnitalRingHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：cancel_right {g₁ g₂ : β ->ₙ+* γ} {f : α ->ₙ+* β} (hf : Surjective f) : g₁.
comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NonUnitalRingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : NonUni
talNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β]   {f g : α →ₙ+* β}
, f = g ↔ ∀ (x…
-/
theorem cancel_right {g₁ g₂ : β →ₙ+* γ} {f : α →ₙ+* β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 (NonUnitalRingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
/-
**NonUnitalRingHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：cancel_left {g : β ->ₙ+* γ} {f₁ f₂ : α ->ₙ+* β} (hg : Injective g) : g.com
p f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalRingHom.comp_apply`：comp_apply (g : β ->ₙ+* γ) (f : α ->ₙ+* β) 
(x : α) : g.comp f x = g (f x)
-/
theorem cancel_left {g : β →ₙ+* γ} {f₁ f₂ : α →ₙ+* β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

end NonUnitalRingHom

/-- Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.

This extends from both `MonoidHom` and `MonoidWithZeroHom` in order to put the fields in a
sensible order, even though `MonoidWithZeroHom` already extends `MonoidHom`. -/
@[wikidata Q1194212]
/-
**RingHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_5) → (β : Type u_6) → [NonAssocSemiring α] → [NonAssocSemiring
 β] → Type (max u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.

This extends from both `MonoidHom` and `MonoidWithZeroHom` in order to put the f
ields in a
sensible order, even though `MonoidWithZeroHom` already extends `MonoidHom`.
-/
structure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β] extends
  α →* β, α →+ β, α →ₙ+* β, α →*₀ β

/-- `α →+* β` denotes the type of ring homomorphisms from `α` to `β`. -/
infixr:25 " →+* " => RingHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a monoid with zero homomorphism `α →*₀ β`.
The `simp`-normal form is `(f : α →*₀ β)`. -/
add_decl_doc RingHom.toMonoidWithZeroHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a monoid homomorphism `α →* β`.
The `simp`-normal form is `(f : α →* β)`. -/
add_decl_doc RingHom.toMonoidHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as an additive monoid homomorphism `α →+ β`.
The `simp`-normal form is `(f : α →+ β)`. -/
add_decl_doc RingHom.toAddMonoidHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a non-unital ring homomorphism `α →ₙ+* β`. The
`simp`-normal form is `(f : α →ₙ+* β)`. -/
add_decl_doc RingHom.toNonUnitalRingHom

section RingHomClass

/-- `RingHomClass F α β` states that `F` is a type of (semi)ring homomorphisms.
You should extend this class when you extend `RingHom`.

This extends from both `MonoidHomClass` and `MonoidWithZeroHomClass` in
order to put the fields in a sensible order, even though
`MonoidWithZeroHomClass` already extends `MonoidHomClass`. -/
/-
**RingHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_5) →   (α : outParam (Type u_6)) →     (β : outParam (Type u_7
)) → [NonAssocSemiring α] → [NonAssocSemiring β] → [FunLike F α β] → Prop
参数：Type u_6；Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RingHomClass F α β` states that `F` is a type of (semi)ring homomorphisms.
You should extend this class when you extend `RingHom`.

This extends from both `MonoidHomClass` and `MonoidWithZeroHomClass` in
order to put the fields in a sensible order, even though
`MonoidWithZeroHomClass` already extends `MonoidHomClass`.
-/
class RingHomClass (F : Type*) (α β : outParam Type*)
    [NonAssocSemiring α] [NonAssocSemiring β] [FunLike F α β] : Prop
  extends MonoidHomClass F α β, AddMonoidHomClass F α β, MonoidWithZeroHomClass F α β

variable [FunLike F α β]

-- See note [implicit instance arguments].
variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} [RingHomClass F α β]

/-- Turn an element of a type `F` satisfying `RingHomClass F α β` into an actual
`RingHom`. This is declared as the default coercion from `F` to `α →+* β`. -/
@[coe]
/-
**RingHomClass.toRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHomClass.toRingHom (f : F) : α ->+* β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
Turn an element of a type `F` satisfying `RingHomClass F α β` into an actual
`RingHom`. This is declared as the default coercion from `F` to `α →+* β`.
-/
def RingHomClass.toRingHom (f : F) : α →+* β :=
  { (f : α →* β), (f : α →+ β) with }

/-- Any type satisfying `RingHomClass` can be cast into `RingHom` via `RingHomClass.toRingHom`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `RingHomClass` can be cast into `RingHom` via `RingHomClass.
toRingHom`.
-/
instance : CoeTC F (α →+* β) :=
  ⟨RingHomClass.toRingHom⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) RingHomClass.toNonUnitalRingHomClass : NonUnitalRingHomClass F α β :=
  { ‹RingHomClass F α β› with }

end RingHomClass

namespace RingHom

section coe

/-!
Throughout this section, some `Semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

/-
**RingHom.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
形式化陈述：instFunLike : FunLike (α ->+* β) α β where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (α →+* β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h
/-
**RingHom.instRingHomClass** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
形式化陈述：instRingHomClass : RingHomClass (α ->+* β) α β where map_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `OneHom.map_one'`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [inst_
1 : One N] (self : OneHom M N), self.toFun 1 = 1
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
· 使用定理 `RingHom.map_zero'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemir
ing α] [inst_1 : NonAssocSemiring β] (self : α →+* β),   (↑↑self).toFun 0 = 0
-/
instance instRingHomClass : RingHomClass (α →+* β) α β where
  map_add := RingHom.map_add'
  map_zero := RingHom.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections RingHom (toFun → apply)
/-
**RingHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：toFun_eq_coe (f : α ->+* β) : f.toFun = f
参数：f : α ->+* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : α →+* β) : f.toFun = f :=
  rfl

@[simp]
/-
**RingHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_mk (f : α ->* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α ->+* β) : α -> β) = f
参数：f : α ->* β；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : α →* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α →+* β) : α → β) = f :=
  rfl

@[simp]
/-
**RingHom.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β] (f : F) : ((f : α
 ->+* β) : α -> β) = f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β] (f : F) :
    ((f : α →+* β) : α → β) = f :=
  rfl

attribute [coe] RingHom.toMonoidHom
/-
**RingHom.coeToMonoidHom** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
形式化陈述：coeToMonoidHom : Coe (α ->+* β) (α ->* β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeToMonoidHom : Coe (α →+* β) (α →* β) :=
  ⟨RingHom.toMonoidHom⟩

@[simp]
/-
**RingHom.toMonoidHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：toMonoidHom_eq_coe (f : α ->+* β) : f.toMonoidHom = f
参数：f : α ->+* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMonoidHom_eq_coe (f : α →+* β) : f.toMonoidHom = f :=
  rfl
/-
**RingHom.toMonoidWithZeroHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：toMonoidWithZeroHom_eq_coe (f : α ->+* β) : (f.toMonoidWithZeroHom : α -> 
β) = f
参数：f : α ->+* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMonoidWithZeroHom_eq_coe (f : α →+* β) : (f.toMonoidWithZeroHom : α → β) = f := by
  rfl

@[simp]
/-
**RingHom.coe_monoidHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_monoidHom_mk (f : α ->* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α ->+* β) : α ->*
 β) = f
参数：f : α ->* β；h₁ h₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_monoidHom_mk (f : α →* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α →+* β) : α →* β) = f :=
  rfl

@[simp]
/-
**RingHom.toAddMonoidHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：toAddMonoidHom_eq_coe (f : α ->+* β) : f.toAddMonoidHom = f
参数：f : α ->+* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddMonoidHom_eq_coe (f : α →+* β) : f.toAddMonoidHom = f :=
  rfl

@[simp]
/-
**RingHom.coe_addMonoidHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_addMonoidHom_mk (f : α -> β) (h₁ h₂ h₃ h₄) : ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩
 : α ->+* β) : α ->+ β) = ⟨⟨f, h₃⟩, h₄⟩
参数：f : α -> β；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem coe_addMonoidHom_mk (f : α → β) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : α →+* β) : α →+ β) = ⟨⟨f, h₃⟩, h₄⟩ :=
  rfl

/-- Copy of a `RingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**RingHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：copy (f : α ->+* β) (f' : α -> β) (h : f' = f) : α ->+* β
参数：f : α ->+* β；f' : α -> β；h : f' = f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `RingHom` with a new `toFun` equal to the old one. Useful to fix defin
itional
equalities.
-/
def copy (f : α →+* β) (f' : α → β) (h : f' = f) : α →+* β :=
  { f.toMonoidWithZeroHom.copy f' h, f.toAddMonoidHom.copy f' h with }

@[simp]
/-
**RingHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_copy (f : α ->+* β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f'
参数：f : α ->+* β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : α →+* β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**RingHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：copy_eq (f : α ->+* β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : α ->+* β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : α →+* β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

end coe

section

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

/-
**RingHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α} {x_1 : NonAssocSe
miring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g x_2
参数：x_2 : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {f g : α →+* β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x
/-
**RingHom.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α} {x_1 : NonAssocSe
miring β} (f : α →+* β) {x_2 y : α},   x_2 = y → f x_2 = f y
参数：f : α →+* β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg (f : α →+* β) {x y : α} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h
/-
**RingHom.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_inj ⦃f g : α ->+* β⦄ (h : (f : α -> β) = g) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_inj ⦃f g : α →+* β⦄ (h : (f : α → β) = g) : f = g :=
  DFunLike.coe_injective h

@[ext]
/-
**RingHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : α →+* β⦄ : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

@[simp]
/-
**RingHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mk_coe (f : α ->+* β) (h₁ h₂ h₃ h₄) : RingHom.mk ⟨⟨f, h₁⟩, h₂⟩ h₃ h₄ = f
参数：f : α ->+* β；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem mk_coe (f : α →+* β) (h₁ h₂ h₃ h₄) : RingHom.mk ⟨⟨f, h₁⟩, h₂⟩ h₃ h₄ = f :=
  ext fun _ => rfl
/-
**RingHom.coe_addMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_addMonoidHom_injective : Injective (fun f : α ->+* β => (f : α ->+ β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem coe_addMonoidHom_injective : Injective (fun f : α →+* β => (f : α →+ β)) := fun _ _ h =>
  ext <| DFunLike.congr_fun (F := α →+ β) h
/-
**RingHom.coe_monoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_monoidHom_injective : Injective (fun f : α ->+* β => (f : α ->* β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_monoidHom_injective : Injective (fun f : α →+* β => (f : α →* β)) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

/-- Ring homomorphisms map zero to zero. -/
/-
**RingHom.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α} {x_1 : NonAssocSe
miring β} (f : α →+* β), f 0 = 0
参数：f : α →+* β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
Ring homomorphisms map zero to zero.
-/
protected theorem map_zero (f : α →+* β) : f 0 = 0 :=
  map_zero f

/-- Ring homomorphisms map one to one. -/
/-
**RingHom.map_one** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α} {x_1 : NonAssocSe
miring β} (f : α →+* β), f 1 = 1
参数：f : α →+* β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
Ring homomorphisms map one to one.
-/
protected theorem map_one (f : α →+* β) : f 1 = 1 :=
  map_one f

/-- Ring homomorphisms preserve addition. -/
/-
**RingHom.map_add** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α} {x_1 : NonAssocSe
miring β} (f : α →+* β) (a b : α),   f (a + b) = f a + f b
参数：f : α →+* β；a b : α；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
Ring homomorphisms preserve addition.
-/
protected theorem map_add (f : α →+* β) : ∀ a b, f (a + b) = f a + f b :=
  map_add f

/-- Ring homomorphisms preserve multiplication. -/
/-
**RingHom.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α} {x_1 : NonAssocSe
miring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
参数：f : α →+* β；a b : α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …

--- 原说明 ---
Ring homomorphisms preserve multiplication.
-/
protected theorem map_mul (f : α →+* β) : ∀ a b, f (a * b) = f a * f b :=
  map_mul f

/-- `f : α →+* β` has a trivial codomain iff `f 1 = 0`. -/
/-
**RingHom.codomain_trivial_iff_map_one_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `RingHo
m`。
形式化陈述：codomain_trivial_iff_map_one_eq_zero : (0 : β) = 1 ↔ f 1 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`f : α →+* β` has a trivial codomain iff `f 1 = 0`.
-/
theorem codomain_trivial_iff_map_one_eq_zero : (0 : β) = 1 ↔ f 1 = 0 := by rw [map_one, eq_comm]

/-- `f : α →+* β` has a trivial codomain iff it has a trivial range. -/
/-
**RingHom.codomain_trivial_iff_range_trivial** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`
。
形式化陈述：codomain_trivial_iff_range_trivial : (0 : β) = 1 ↔ forall x, f x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `RingHom.codomain_trivial_iff_map_one_eq_zero`：codomain_trivial_iff_map_o
ne_eq_zero : (0 : β) = 1 ↔ f 1 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
`f : α →+* β` has a trivial codomain iff it has a trivial range.
-/
theorem codomain_trivial_iff_range_trivial : (0 : β) = 1 ↔ ∀ x, f x = 0 :=
  f.codomain_trivial_iff_map_one_eq_zero.trans
    ⟨fun h x => by rw [← mul_one x, map_mul, h, mul_zero], fun h => h 1⟩

/-- `f : α →+* β` doesn't map `1` to `0` if `β` is nontrivial -/
/-
**RingHom.map_one_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_one_ne_zero [Nontrivial β] : f 1 != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.codomain_trivial_iff_map_one_eq_zero`：codomain_trivial_iff_map_o
ne_eq_zero : (0 : β) = 1 ↔ f 1 = 0
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1

--- 原说明 ---
`f : α →+* β` doesn't map `1` to `0` if `β` is nontrivial
-/
theorem map_one_ne_zero [Nontrivial β] : f 1 ≠ 0 :=
  mt f.codomain_trivial_iff_map_one_eq_zero.mpr zero_ne_one

include f in
/-- If there is a homomorphism `f : α →+* β` and `β` is nontrivial, then `α` is nontrivial. -/
/-
**RingHom.domain_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：domain_nontrivial [Nontrivial β] : Nontrivial α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.map_one_ne_zero`：map_one_ne_zero [Nontrivial β] : f 1 != 0

--- 原说明 ---
If there is a homomorphism `f : α →+* β` and `β` is nontrivial, then `α` is nont
rivial.
-/
theorem domain_nontrivial [Nontrivial β] : Nontrivial α :=
  ⟨⟨1, 0, mt (fun h => show f 1 = 0 by rw [h, map_zero]) f.map_one_ne_zero⟩⟩
/-
**RingHom.codomain_trivial** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：codomain_trivial (f : α ->+* β) [h : Subsingleton α] : Subsingleton β
参数：f : α ->+* β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
-/
theorem codomain_trivial (f : α →+* β) [h : Subsingleton α] : Subsingleton β :=
  (subsingleton_or_nontrivial β).resolve_right fun _ =>
    not_nontrivial_iff_subsingleton.mpr h f.domain_nontrivial

end

/-- Ring homomorphisms preserve additive inverse. -/
/-
**RingHom.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α] [inst_1 : NonAssoc
Ring β] (f : α →+* β) (x : α), f (-x) = -f x
参数：f : α →+* β；x : α；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
Ring homomorphisms preserve additive inverse.
-/
protected theorem map_neg [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x : α) : f (-x) = -f x :=
  map_neg f x

/-- Ring homomorphisms preserve subtraction. -/
/-
**RingHom.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α] [inst_1 : NonAssoc
Ring β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
参数：f : α →+* β；x y : α；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
Ring homomorphisms preserve subtraction.
-/
protected theorem map_sub [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x y : α) :
    f (x - y) = f x - f y :=
  map_sub f x y

/-- Makes a ring homomorphism from a monoid homomorphism of rings which preserves addition. -/
/-
**RingHom.mk'** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：mk' [NonAssocSemiring α] [NonAssocRing β] (f : α ->* β) (map_add : forall 
a b, f (a + b) = f a + f b) : α ->+* β
参数：f : α ->* β；map_add : forall a b, f (a + b) = f a + f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Makes a ring homomorphism from a monoid homomorphism of rings which preserves ad
dition.
-/
def mk' [NonAssocSemiring α] [NonAssocRing β] (f : α →* β)
    (map_add : ∀ a b, f (a + b) = f a + f b) : α →+* β :=
  { AddMonoidHom.mk' f map_add, f with }

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

/-- The identity ring homomorphism from a semiring to itself. -/
@[instance_reducible]
/-
**RingHom.id** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：id (α : Type*) [NonAssocSemiring α] : α ->+* α where toFun x
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity ring homomorphism from a semiring to itself.
-/
def id (α : Type*) [NonAssocSemiring α] : α →+* α where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
/-
**RingHom.** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α →+* α) :=
  ⟨id α⟩

@[simp, norm_cast]
/-
**RingHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_id : ⇑(RingHom.id α) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(RingHom.id α) = _root_.id := rfl

@[simp]
/-
**RingHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：id_apply (x : α) : RingHom.id α x = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : α) : RingHom.id α x = x :=
  rfl

@[simp]
/-
**RingHom.coe_addMonoidHom_id** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_addMonoidHom_id : (id α : α ->+ α) = AddMonoidHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem coe_addMonoidHom_id : (id α : α →+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
/-
**RingHom.coe_monoidHom_id** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_monoidHom_id : (id α : α ->* α) = MonoidHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_monoidHom_id : (id α : α →* α) = MonoidHom.id α :=
  rfl

variable {_ : NonAssocSemiring γ}

/-- Composition of ring homomorphisms is a ring homomorphism. -/
@[instance_reducible]
/-
**RingHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：comp (g : β ->+* γ) (f : α ->+* β) : α ->+* γ
参数：g : β ->+* γ；f : α ->+* β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of ring homomorphisms is a ring homomorphism.
-/
def comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=
  { g.toNonUnitalRingHom.comp f.toNonUnitalRingHom with toFun x := g (f x), map_one' := by simp }

/-- Composition of semiring homomorphisms is associative. -/
/-
**RingHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* β) (g : β ->+* γ) (h :
 γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
参数：f : α ->+* β；g : β ->+* γ；h : γ ->+* δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of semiring homomorphisms is associative.
-/
theorem comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/-
**RingHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp hmn : α -> γ) = hnp
 ∘ hmn
参数：hnp : β ->+* γ；hmn : α ->+* β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (hnp : β →+* γ) (hmn : α →+* β) : (hnp.comp hmn : α → γ) = hnp ∘ hmn :=
  rfl
/-
**RingHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α) : (hnp.comp hmn : α -
> γ) x = hnp (hmn x)
参数：hnp : β ->+* γ；hmn : α ->+* β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) :
    (hnp.comp hmn : α → γ) x = hnp (hmn x) :=
  rfl

@[simp]
/-
**RingHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：comp_id (f : α ->+* β) : f.comp (id α) = f
参数：f : α ->+* β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem comp_id (f : α →+* β) : f.comp (id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**RingHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：id_comp (f : α ->+* β) : (id β).comp f = f
参数：f : α ->+* β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem id_comp (f : α →+* β) : (id β).comp f = f :=
  ext fun _ => rfl
/-
**RingHom.instOne** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
形式化陈述：instOne : One (α ->+* α) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (α →+* α) where one := id _
/-
**RingHom.instMul** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
形式化陈述：instMul : Mul (α ->+* α) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (α →+* α) where mul := comp
/-
**RingHom.one_def** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：one_def : (1 : α ->+* α) = id α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_def : (1 : α →+* α) = id α := rfl
/-
**RingHom.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：mul_def (f g : α ->+* α) : f * g = f.comp g
参数：f g : α ->+* α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def (f g : α →+* α) : f * g = f.comp g := rfl
/-
**RingHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {x : NonAssocSemiring α}, ⇑1 = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_one : ⇑(1 : α →+* α) = _root_.id := rfl
/-
**RingHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {x : NonAssocSemiring α} (f g : α →+* α), ⇑(f * g) = ⇑f ∘
 ⇑g
参数：f g : α →+* α；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mul (f g : α →+* α) : ⇑(f * g) = f ∘ g := rfl
/-
**RingHom.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
形式化陈述：instMonoid : Monoid (α ->+* α) where mul_one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `RingHom.id_comp`：id_comp (f : α ->+* β) : (id β).comp f = f
· 使用定理 `RingHom.comp_id`：comp_id (f : α ->+* β) : f.comp (id α) = f
-/
instance instMonoid : Monoid (α →+* α) where
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
  npow n f := (npowRec n f).copy f^[n] <| by induction n <;> simp [npowRec, *]
  npow_succ _ _ := DFunLike.coe_injective <| Function.iterate_succ _ _
/-
**RingHom.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {x : NonAssocSemiring α} (f : α →+* α) (n : ℕ), ⇑(f ^ n) 
= (⇑f)^[n]
参数：f : α →+* α；n : ℕ；f ^ n；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_pow (f : α →+* α) (n : ℕ) : ⇑(f ^ n) = f^[n] := rfl

@[simp]
/-
**RingHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：cancel_right {g₁ g₂ : β ->+* γ} {f : α ->+* β} (hf : Surjective f) : g₁.co
mp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
-/
theorem cancel_right {g₁ g₂ : β →+* γ} {f : α →+* β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => RingHom.ext <| hf.forall.2 (RingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
/-
**RingHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：cancel_left {g : β ->+* γ} {f₁ f₂ : α ->+* β} (hg : Injective g) : g.comp 
f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
-/
theorem cancel_left {g : β →+* γ} {f₁ f₂ : α →+* β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => RingHom.ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

end RingHom

section Semiring
variable [Semiring α] [Semiring β]

/-
**RingHom.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [inst_1 : Semiring β] 
(f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
参数：f : α →+* β；a : α；n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
protected lemma RingHom.map_pow (f : α →+* β) (a) : ∀ n : ℕ, f (a ^ n) = f a ^ n := map_pow f a

end Semiring

namespace AddMonoidHom

variable [CommRing α] [IsDomain α] [CommRing β] (f : β →+ α)

/-- Make a ring homomorphism from an additive group homomorphism from a commutative ring to an
integral domain that commutes with self multiplication, assumes that two is nonzero and `1` is sent
to `1`. -/
/-
**AddMonoidHom.mkRingHomOfMulSelfOfTwoNeZero** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoi
dHom`。
形式化陈述：mkRingHomOfMulSelfOfTwoNeZero (h : forall x, f (x * x) = f x * f x) (h_two
 : (2 : α) != 0) (h_one : f 1 = 1) : β ->+* α
参数：h : forall x, f (x * x) = f x * f x；h_two : (2 : α) != 0；h_one : f 1 = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a ring homomorphism from an additive group homomorphism from a commutative 
ring to an
integral domain that commutes with self multiplication, assumes that two is nonz
ero and `1` is sent
to `1`.
-/
def mkRingHomOfMulSelfOfTwoNeZero (h : ∀ x, f (x * x) = f x * f x) (h_two : (2 : α) ≠ 0)
    (h_one : f 1 = 1) : β →+* α :=
  { f with
    map_one' := h_one,
    map_mul' := fun x y => by
      have hxy := h (x + y)
      rw [mul_add, add_mul, add_mul, f.map_add, f.map_add, f.map_add, f.map_add, h x, h y, add_mul,
        mul_add, mul_add, ← sub_eq_zero, add_comm (f x * f x + f (y * x)), ← sub_sub, ← sub_sub,
        ← sub_sub, mul_comm y x, mul_comm (f y) (f x)] at hxy
      simp only [add_assoc, add_sub_assoc, add_sub_cancel] at hxy
      rw [sub_sub, ← two_mul, ← add_sub_assoc, ← two_mul, ← mul_sub, mul_eq_zero (M₀ := α),
        sub_eq_zero, or_iff_not_imp_left] at hxy
      exact hxy h_two }

@[simp]
/-
**AddMonoidHom.coe_fn_mkRingHomOfMulSelfOfTwoNeZero** 是 Mathlib 中的一个定理，位于命名空间 `A
ddMonoidHom`。
形式化陈述：coe_fn_mkRingHomOfMulSelfOfTwoNeZero (h h_two h_one) : (f.mkRingHomOfMulSe
lfOfTwoNeZero h h_two h_one : β -> α) = f
参数：h h_two h_one。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem coe_fn_mkRingHomOfMulSelfOfTwoNeZero (h h_two h_one) :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β → α) = f :=
  rfl

@[simp]
/-
**AddMonoidHom.coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero** 是 Mathlib 中的一个定理
，位于命名空间 `AddMonoidHom`。
形式化陈述：coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero (h h_two h_one) : (f.mkRing
HomOfMulSelfOfTwoNeZero h h_two h_one : β ->+ α) = f
参数：h h_two h_one。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero (h h_two h_one) :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β →+ α) = f := by
  ext
  rfl

end AddMonoidHom

