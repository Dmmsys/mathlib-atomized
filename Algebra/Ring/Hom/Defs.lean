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

/--
Definition of `NonUnitalRingHom` / `NonUnitalRingHom` 的定义

English:
structure NonUnitalRingHom
  parameters: (α β : Type*) [NonUnitalNonAssocSemiring α]
  extends: α ->ₙ* β, α ->+ β
  (no additional axioms)

中文:
结构 非幺环态射
  参数: (α β : 类型) [非幺非结合半环 α]
  继承: α ->ₙ* β, α ->+ β
  (无附加公理)
-/
structure NonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] extends α ->ₙ* β, α ->+ β

/-- `α →ₙ+* β` denotes the type of non-unital ring homomorphisms from `α` to `β`. -/
infixr:25 " ->ₙ+* " => NonUnitalRingHom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as a semigroup
homomorphism `α →ₙ* β`. The `simp`-normal form is `(f : α →ₙ* β)`. -/
add_decl_doc NonUnitalRingHom.toMulHom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as an additive
monoid homomorphism `α →+ β`. The `simp`-normal form is `(f : α →+ β)`. -/
add_decl_doc NonUnitalRingHom.toAddMonoidHom

section NonUnitalRingHomClass

/--
Definition of `NonUnitalRingHomClass` / `NonUnitalRingHomClass` 的定义

English:
class NonUnitalRingHomClass
  parameters: (F : Type*) (α β : outParam Type*) [NonUnitalNonAssocSemiring α]
  extends: MulHomClass F α β, AddMonoidHomClass F α β
  (no additional axioms)

中文:
类 非幺环态射类
  参数: (F : 类型) (α β : outParam 类型) [非幺非结合半环 α]
  继承: 乘法态射类 F α β, 加法幺半群态射类 F α β
  (无附加公理)
-/
class NonUnitalRingHomClass (F : Type*) (α β : outParam Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] [FunLike F α β] : Prop
  extends MulHomClass F α β, AddMonoidHomClass F α β

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [FunLike F α β]
variable [NonUnitalRingHomClass F α β]

/-- Turn an element of a type `F` satisfying `NonUnitalRingHomClass F α β` into an actual
`NonUnitalRingHom`. This is declared as the default coercion from `F` to `α →ₙ+* β`. -/
@[coe]
/--
Definition of `NonUnitalRingHomClass.toNonUnitalRingHom` / `NonUnitalRingHomClass.toNonUnitalRingHom` 的定义

English:
definition NonUnitalRingHomClass.toNonUnitalRingHom
  signature: (f : F)
  body: { (f : α ->ₙ* β), (f : α ->+ β) with }

中文:
定义 非幺环态射类.toNonUnitalRingHom
  签名: (f : F)
  定义体: { (f : α ->ₙ* β), (f : α ->+ β) with }
-/
def NonUnitalRingHomClass.toNonUnitalRingHom (f : F) : α ->ₙ+* β :=
  { (f : α ->ₙ* β), (f : α ->+ β) with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC F (α ->ₙ+* β)
  body: ⟨NonUnitalRingHomClass.toNonUnitalRingHom⟩

中文:
实例 :
  签名: CoeTC F (α ->ₙ+* β)
  定义体: ⟨NonUnitalRingHomClass.toNonUnitalRingHom⟩
-/
instance : CoeTC F (α ->ₙ+* β) :=
  ⟨NonUnitalRingHomClass.toNonUnitalRingHom⟩

end NonUnitalRingHomClass

namespace NonUnitalRingHom

section coe

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (α ->ₙ+* β) α β
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

中文:
实例 :
  签名: 函数状 (α ->ₙ+* β) α β
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

Depends on / 依赖: f.toFun
-/
instance : FunLike (α ->ₙ+* β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalRingHomClass (α ->ₙ+* β) α β
  body: NonUnitalRingHom.map_add'
  map_zero := NonUnitalRingHom.map_zero'
  map_mul f := f.map_mul'

initialize_simps_projections NonUnitalRingHom (toFun -> apply)

@[simp]

中文:
实例 :
  签名: 非幺环态射类 (α ->ₙ+* β) α β
  定义体: NonUnitalRingHom.map_add'
  map_zero := NonUnitalRingHom.map_zero'
  map_mul f := f.map_mul'

initialize_simps_projections NonUnitalRingHom (toFun -> apply)

@[simp]

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.map_add, map_add
-/
instance : NonUnitalRingHomClass (α ->ₙ+* β) α β where
  map_add := NonUnitalRingHom.map_add'
  map_zero := NonUnitalRingHom.map_zero'
  map_mul f := f.map_mul'

initialize_simps_projections NonUnitalRingHom (toFun -> apply)

@[simp]
/--
theorem `coe_toMulHom` / 定理 `coe_toMulHom`

English:
theorem coe_toMulHom
  given: (f : α ->ₙ+* β)
  statement: ⇑f.toMulHom = f
  proof: rfl

@[simp]

中文:
定理 coe_toMulHom
  条件: (f : α ->ₙ+* β)
  结论: ⇑f.toMulHom = f
  证明: rfl

@[simp]
-/
theorem coe_toMulHom (f : α ->ₙ+* β) : ⇑f.toMulHom = f :=
  rfl

@[simp]
/--
theorem `coe_mulHom_mk` / 定理 `coe_mulHom_mk`

English:
theorem coe_mulHom_mk
  given: (f : α -> β) (h₁ h₂ h₃)
  proof: rfl

中文:
定理 coe_mulHom_mk
  条件: (f : α -> β) (h₁ h₂ h₃)
  证明: rfl
-/
theorem coe_mulHom_mk (f : α -> β) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α ->ₙ+* β) : α ->ₙ* β) = ⟨f, h₁⟩ :=
  rfl

/--
theorem `coe_toAddMonoidHom` / 定理 `coe_toAddMonoidHom`

English:
theorem coe_toAddMonoidHom
  given: (f : α ->ₙ+* β)
  statement: ⇑f.toAddMonoidHom = f
  proof: rfl

@[simp]

中文:
定理 coe_toAddMonoidHom
  条件: (f : α ->ₙ+* β)
  结论: ⇑f.toAddMonoidHom = f
  证明: rfl

@[simp]
-/
theorem coe_toAddMonoidHom (f : α ->ₙ+* β) : ⇑f.toAddMonoidHom = f := rfl

@[simp]
/--
theorem `coe_addMonoidHom_mk` / 定理 `coe_addMonoidHom_mk`

English:
theorem coe_addMonoidHom_mk
  given: (f : α -> β) (h₁ h₂ h₃)
  proof: rfl

中文:
定理 coe_addMonoidHom_mk
  条件: (f : α -> β) (h₁ h₂ h₃)
  证明: rfl

Depends on / 依赖: GlueData, GlueData.f_open, f_open
-/
theorem coe_addMonoidHom_mk (f : α -> β) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α ->ₙ+* β) : α ->+ β) = ⟨⟨f, h₂⟩, h₃⟩ :=
  rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : α ->ₙ+* β) (f' : α -> β) (h : f' = f)
  body: { f.toMulHom.copy f' h, f.toAddMonoidHom.copy f' h with }

@[simp]

中文:
定义 copy
  签名: (f : α ->ₙ+* β) (f' : α -> β) (h : f' = f)
  定义体: { f.toMulHom.copy f' h, f.toAddMonoidHom.copy f' h with }

@[simp]

Depends on / 依赖: GlueData, GlueData.f_open, f_open
-/
protected def copy (f : α ->ₙ+* β) (f' : α -> β) (h : f' = f) : α ->ₙ+* β :=
  { f.toMulHom.copy f' h, f.toAddMonoidHom.copy f' h with }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : α ->ₙ+* β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : α ->ₙ+* β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl

Depends on / 依赖: GlueData, GlueData.f_open, f_open
-/
theorem coe_copy (f : α ->ₙ+* β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : α ->ₙ+* β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : α ->ₙ+* β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext, GlueData, LocallyRingedSpace, LocallyRingedSpace.GlueData
-/
theorem copy_eq (f : α ->ₙ+* β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

end coe

section

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: α ->ₙ+* β⦄ : (forall x, f x = g x) -> f = g
  proof: DFunLike.ext _ _

@[simp]

中文:
定理 ext
  条件: ⦃f g
  结论: α ->ₙ+* β⦄ : (对任意 x, f x = g x) -> f = g
  证明: DFunLike.ext _ _

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f = g :=
  DFunLike.ext _ _

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : α ->ₙ+* β) (h₁ h₂ h₃)
  statement: NonUnitalRingHom.mk (MulHom.mk f h₁) h₂ h₃ = f
  proof: ext fun _ => rfl

中文:
定理 mk_coe
  条件: (f : α ->ₙ+* β) (h₁ h₂ h₃)
  结论: 非幺环态射.mk (乘法半群态射.mk f h₁) h₂ h₃ = f
  证明: ext fun _ => rfl
-/
theorem mk_coe (f : α ->ₙ+* β) (h₁ h₂ h₃) : NonUnitalRingHom.mk (MulHom.mk f h₁) h₂ h₃ = f :=
  ext fun _ => rfl

/--
theorem `coe_addMonoidHom_injective` / 定理 `coe_addMonoidHom_injective`

English:
theorem coe_addMonoidHom_injective
  statement: Injective fun f : α ->ₙ+* β => (f : α ->+ β)
  proof: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

中文:
定理 coe_addMonoidHom_injective
  结论: 单射 fun f : α ->ₙ+* β => (f : α ->+ β)
  证明: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Injective, Injective.of_comp, coe_injective, of_comp
-/
theorem coe_addMonoidHom_injective : Injective fun f : α ->ₙ+* β => (f : α ->+ β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

/--
theorem `coe_mulHom_injective` / 定理 `coe_mulHom_injective`

English:
theorem coe_mulHom_injective
  statement: Injective fun f : α ->ₙ+* β => (f : α ->ₙ* β)
  proof: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

中文:
定理 coe_mulHom_injective
  结论: 单射 fun f : α ->ₙ+* β => (f : α ->ₙ* β)
  证明: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Injective, Injective.of_comp, coe_injective, of_comp
-/
theorem coe_mulHom_injective : Injective fun f : α ->ₙ+* β => (f : α ->ₙ* β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

end

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

/-- The identity non-unital ring homomorphism from a non-unital semiring to itself. -/
@[instance_reducible]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (α : Type*) [NonUnitalNonAssocSemiring α]
  body: x
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

中文:
定义 id
  签名: (α : 类型) [非幺非结合半环 α]
  定义体: x
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
-/
protected def id (α : Type*) [NonUnitalNonAssocSemiring α] : α ->ₙ+* α where
  toFun x := x
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (α ->ₙ+* β)
  body: ⟨{ toFun := 0, map_mul' := fun _ _ => (mul_zero (0 : β)).symm, map_zero' := rfl,
      map_add' := fun _ _ => (add_zero (0 : β)).symm }⟩

中文:
实例 :
  签名: 零 (α ->ₙ+* β)
  定义体: ⟨{ toFun := 0, map_mul' := fun _ _ => (mul_zero (0 : β)).symm, map_zero' := rfl,
      map_add' := fun _ _ => (add_zero (0 : β)).symm }⟩

Depends on / 依赖: add_zero, map_add, map_mul, map_zero, mul_zero
-/
instance : Zero (α ->ₙ+* β) :=
  ⟨{ toFun := 0, map_mul' := fun _ _ => (mul_zero (0 : β)).symm, map_zero' := rfl,
      map_add' := fun _ _ => (add_zero (0 : β)).symm }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ->ₙ+* β)
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: 可居 (α ->ₙ+* β)
  定义体: ⟨0⟩

@[simp]
-/
instance : Inhabited (α ->ₙ+* β) :=
  ⟨0⟩

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : α ->ₙ+* β) = 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ⇑(0 : α ->ₙ+* β) = 0
  证明: rfl

@[simp]
-/
theorem coe_zero : ⇑(0 : α ->ₙ+* β) = 0 :=
  rfl

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (x : α)
  statement: (0 : α ->ₙ+* β) x = 0
  proof: rfl

@[simp]

中文:
定理 zero_apply
  条件: (x : α)
  结论: (0 : α ->ₙ+* β) x = 0
  证明: rfl

@[simp]
-/
theorem zero_apply (x : α) : (0 : α ->ₙ+* β) x = 0 :=
  rfl

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : α)
  statement: NonUnitalRingHom.id α x = x
  proof: rfl

@[simp]

中文:
定理 id_apply
  条件: (x : α)
  结论: 非幺环态射.id α x = x
  证明: rfl

@[simp]
-/
theorem id_apply (x : α) : NonUnitalRingHom.id α x = x :=
  rfl

@[simp]
/--
theorem `coe_addMonoidHom_id` / 定理 `coe_addMonoidHom_id`

English:
theorem coe_addMonoidHom_id
  statement: (NonUnitalRingHom.id α : α ->+ α) = AddMonoidHom.id α
  proof: rfl

@[simp]

中文:
定理 coe_addMonoidHom_id
  结论: (非幺环态射.id α : α ->+ α) = 加法幺半群态射.id α
  证明: rfl

@[simp]
-/
theorem coe_addMonoidHom_id : (NonUnitalRingHom.id α : α ->+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
/--
theorem `coe_mulHom_id` / 定理 `coe_mulHom_id`

English:
theorem coe_mulHom_id
  statement: (NonUnitalRingHom.id α : α ->ₙ* α) = MulHom.id α
  proof: rfl

中文:
定理 coe_mulHom_id
  结论: (非幺环态射.id α : α ->ₙ* α) = 乘法半群态射.id α
  证明: rfl
-/
theorem coe_mulHom_id : (NonUnitalRingHom.id α : α ->ₙ* α) = MulHom.id α :=
  rfl

variable [NonUnitalNonAssocSemiring γ]

/-- Composition of non-unital ring homomorphisms is a non-unital ring homomorphism. -/
@[instance_reducible]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : β ->ₙ+* γ) (f : α ->ₙ+* β)
  body: { g.toMulHom.comp f.toMulHom, g.toAddMonoidHom.comp f.toAddMonoidHom with }

中文:
定义 comp
  签名: (g : β ->ₙ+* γ) (f : α ->ₙ+* β)
  定义体: { g.toMulHom.comp f.toMulHom, g.toAddMonoidHom.comp f.toAddMonoidHom with }

Depends on / 依赖: f.toAddMonoidHom, f.toMulHom, g.toAddMonoidHom.comp, g.toMulHom.comp, toAddMonoidHom, toMulHom
-/
def comp (g : β ->ₙ+* γ) (f : α ->ₙ+* β) : α ->ₙ+* γ :=
  { g.toMulHom.comp f.toMulHom, g.toAddMonoidHom.comp f.toAddMonoidHom with }

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {δ} {_ : NonUnitalNonAssocSemiring δ} (f : α ->ₙ+* β) (g : β ->ₙ+* γ)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  结论: {δ} {_ : 非幺非结合半环 δ} (f : α ->ₙ+* β) (g : β ->ₙ+* γ)
  证明: rfl

@[simp]
-/
theorem comp_assoc {δ} {_ : NonUnitalNonAssocSemiring δ} (f : α ->ₙ+* β) (g : β ->ₙ+* γ)
    (h : γ ->ₙ+* δ) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (g : β ->ₙ+* γ) (f : α ->ₙ+* β)
  statement: ⇑(g.comp f) = g ∘ f
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (g : β ->ₙ+* γ) (f : α ->ₙ+* β)
  结论: ⇑(g.comp f) = g ∘ f
  证明: rfl

@[simp]
-/
theorem coe_comp (g : β ->ₙ+* γ) (f : α ->ₙ+* β) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : β ->ₙ+* γ) (f : α ->ₙ+* β) (x : α)
  statement: g.comp f x = g (f x)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (g : β ->ₙ+* γ) (f : α ->ₙ+* β) (x : α)
  结论: g.comp f x = g (f x)
  证明: rfl

@[simp]
-/
theorem comp_apply (g : β ->ₙ+* γ) (f : α ->ₙ+* β) (x : α) : g.comp f x = g (f x) :=
  rfl

@[simp]
/--
theorem `coe_comp_addMonoidHom` / 定理 `coe_comp_addMonoidHom`

English:
theorem coe_comp_addMonoidHom
  given: (g : β ->ₙ+* γ) (f : α ->ₙ+* β)
  proof: rfl

@[simp]

中文:
定理 coe_comp_addMonoidHom
  条件: (g : β ->ₙ+* γ) (f : α ->ₙ+* β)
  证明: rfl

@[simp]
-/
theorem coe_comp_addMonoidHom (g : β ->ₙ+* γ) (f : α ->ₙ+* β) :
    AddMonoidHom.mk ⟨g ∘ f, (g.comp f).map_zero'⟩ (g.comp f).map_add' = (g : β ->+ γ).comp f :=
  rfl

@[simp]
/--
theorem `coe_comp_mulHom` / 定理 `coe_comp_mulHom`

English:
theorem coe_comp_mulHom
  given: (g : β ->ₙ+* γ) (f : α ->ₙ+* β)
  proof: rfl

@[simp]

中文:
定理 coe_comp_mulHom
  条件: (g : β ->ₙ+* γ) (f : α ->ₙ+* β)
  证明: rfl

@[simp]
-/
theorem coe_comp_mulHom (g : β ->ₙ+* γ) (f : α ->ₙ+* β) :
    MulHom.mk (g ∘ f) (g.comp f).map_mul' = (g : β ->ₙ* γ).comp f :=
  rfl

@[simp]
/--
theorem `comp_zero` / 定理 `comp_zero`

English:
theorem comp_zero
  given: (g : β ->ₙ+* γ)
  statement: g.comp (0 : α ->ₙ+* β) = 0
  proof: by
  ext
  simp

@[simp]

中文:
定理 comp_zero
  条件: (g : β ->ₙ+* γ)
  结论: g.comp (0 : α ->ₙ+* β) = 0
  证明: by
  ext
  simp

@[simp]
-/
theorem comp_zero (g : β ->ₙ+* γ) : g.comp (0 : α ->ₙ+* β) = 0 := by
  ext
  simp

@[simp]
/--
theorem `zero_comp` / 定理 `zero_comp`

English:
theorem zero_comp
  given: (f : α ->ₙ+* β)
  statement: (0 : β ->ₙ+* γ).comp f = 0
  proof: by
  ext
  rfl

@[simp]

中文:
定理 zero_comp
  条件: (f : α ->ₙ+* β)
  结论: (0 : β ->ₙ+* γ).comp f = 0
  证明: by
  ext
  rfl

@[simp]
-/
theorem zero_comp (f : α ->ₙ+* β) : (0 : β ->ₙ+* γ).comp f = 0 := by
  ext
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ->ₙ+* β)
  statement: f.comp (NonUnitalRingHom.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : α ->ₙ+* β)
  结论: f.comp (非幺环态射.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : α ->ₙ+* β) : f.comp (NonUnitalRingHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ->ₙ+* β)
  statement: (NonUnitalRingHom.id β).comp f = f
  proof: ext fun _ => rfl

中文:
定理 id_comp
  条件: (f : α ->ₙ+* β)
  结论: (非幺环态射.id β).comp f = f
  证明: ext fun _ => rfl

Depends on / 依赖: gluedCoverT
-/
theorem id_comp (f : α ->ₙ+* β) : (NonUnitalRingHom.id β).comp f = f :=
  ext fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidWithZero (α ->ₙ+* α)
  body: NonUnitalRingHom.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
  mul_zero := comp_zero
  zero_mul := zero_comp

中文:
实例 :
  签名: 带零幺半群 (α ->ₙ+* α)
  定义体: NonUnitalRingHom.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
  mul_zero := comp_zero
  zero_mul := zero_comp

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.id, gluedCoverT
-/
instance : MonoidWithZero (α ->ₙ+* α) where
  one := NonUnitalRingHom.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
  mul_zero := comp_zero
  zero_mul := zero_comp

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : α ->ₙ+* α) = NonUnitalRingHom.id α
  proof: rfl

@[simp]

中文:
定理 one_def
  结论: (1 : α ->ₙ+* α) = 非幺环态射.id α
  证明: rfl

@[simp]

Depends on / 依赖: gluedCoverT
-/
theorem one_def : (1 : α ->ₙ+* α) = NonUnitalRingHom.id α :=
  rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : α ->ₙ+* α) = id
  proof: rfl

中文:
定理 coe_one
  结论: ⇑(1 : α ->ₙ+* α) = id
  证明: rfl

Depends on / 依赖: gluedCoverT
-/
theorem coe_one : ⇑(1 : α ->ₙ+* α) = id :=
  rfl

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (f g : α ->ₙ+* α)
  statement: f * g = f.comp g
  proof: rfl

@[simp]

中文:
定理 mul_def
  条件: (f g : α ->ₙ+* α)
  结论: f * g = f.comp g
  证明: rfl

@[simp]
-/
theorem mul_def (f g : α ->ₙ+* α) : f * g = f.comp g :=
  rfl

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : α ->ₙ+* α)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_mul
  条件: (f g : α ->ₙ+* α)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_mul (f g : α ->ₙ+* α) : ⇑(f * g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : β ->ₙ+* γ} {f : α ->ₙ+* β} (hf : Surjective f)
  proof: ⟨fun h => ext hf.forall.2 (NonUnitalRingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : β ->ₙ+* γ} {f : α ->ₙ+* β} (hf : 满射 f)
  证明: ⟨fun h => ext hf.forall.2 (NonUnitalRingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : β ->ₙ+* γ} {f : α ->ₙ+* β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 (NonUnitalRingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : β ->ₙ+* γ} {f₁ f₂ : α ->ₙ+* β} (hg : Injective g)
  proof: ⟨fun h => ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

中文:
定理 cancel_left
  条件: {g : β ->ₙ+* γ} {f₁ f₂ : α ->ₙ+* β} (hg : 单射 g)
  证明: ⟨fun h => ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

Depends on / 依赖: comp_apply
-/
theorem cancel_left {g : β ->ₙ+* γ} {f₁ f₂ : α ->ₙ+* β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

end NonUnitalRingHom

/-- Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.

This extends from both `MonoidHom` and `MonoidWithZeroHom` in order to put the fields in a
sensible order, even though `MonoidWithZeroHom` already extends `MonoidHom`. -/
@[wikidata Q1194212]
/--
Definition of `RingHom` / `RingHom` 的定义

English:
structure RingHom
  parameters: (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β]
  (no additional axioms)

中文:
结构 环态射
  参数: (α : 类型) (β : 类型) [非结合半环 α] [非结合半环 β]
  (无附加公理)
-/
structure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β] extends
  α ->* β, α ->+ β, α ->ₙ+* β, α ->*₀ β

/-- `α →+* β` denotes the type of ring homomorphisms from `α` to `β`. -/
infixr:25 " ->+* " => RingHom

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

/--
Definition of `RingHomClass` / `RingHomClass` 的定义

English:
class RingHomClass
  parameters: (F : Type*) (α β : outParam Type*)
  extends: MonoidHomClass F α β, AddMonoidHomClass F α β, MonoidWithZeroHomClass F α β
  (no additional axioms)

中文:
类 环态射类
  参数: (F : 类型) (α β : outParam 类型)
  继承: 幺半群态射类 F α β, 加法幺半群态射类 F α β, 带零幺半群态射类 F α β
  (无附加公理)
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
/--
Definition of `RingHomClass.toRingHom` / `RingHomClass.toRingHom` 的定义

English:
definition RingHomClass.toRingHom
  signature: (f : F)
  body: { (f : α ->* β), (f : α ->+ β) with }

中文:
定义 环态射类.toRingHom
  签名: (f : F)
  定义体: { (f : α ->* β), (f : α ->+ β) with }
-/
def RingHomClass.toRingHom (f : F) : α ->+* β :=
  { (f : α ->* β), (f : α ->+ β) with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC F (α ->+* β)
  body: ⟨RingHomClass.toRingHom⟩

中文:
实例 :
  签名: CoeTC F (α ->+* β)
  定义体: ⟨RingHomClass.toRingHom⟩

Depends on / 依赖: Hom.stalkMap_comp, Hom.stalkMap_congr_hom, IsIso.eq_comp_inv, eq_comp_inv, gluedCover, infer_instance, stalkMap_comp, stalkMap_congr_hom
-/
instance : CoeTC F (α ->+* β) :=
  ⟨RingHomClass.toRingHom⟩

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

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (α ->+* β) α β where
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

中文:
实例 instFunLike
  签名: : 函数状 (α ->+* β) α β where
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (α ->+* β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

/--
Instance `instRingHomClass` / 实例 `instRingHomClass`

English:
instance instRingHomClass
  signature: : RingHomClass (α ->+* β) α β where
  body: RingHom.map_add'
  map_zero := RingHom.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections RingHom (toFun -> apply)

中文:
实例 instRingHomClass
  签名: : 环态射类 (α ->+* β) α β where
  定义体: RingHom.map_add'
  map_zero := RingHom.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections RingHom (toFun -> apply)

Depends on / 依赖: RingHom, RingHom.map_add, map_add
-/
instance instRingHomClass : RingHomClass (α ->+* β) α β where
  map_add := RingHom.map_add'
  map_zero := RingHom.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections RingHom (toFun -> apply)

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : α ->+* β)
  statement: f.toFun = f
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  条件: (f : α ->+* β)
  结论: f.toFun = f
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe (f : α ->+* β) : f.toFun = f :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : α ->* β) (h₁ h₂)
  statement: ((⟨f, h₁, h₂⟩ : α ->+* β) : α -> β) = f
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (f : α ->* β) (h₁ h₂)
  结论: ((⟨f, h₁, h₂⟩ : α ->+* β) : α -> β) = f
  证明: rfl

@[simp]
-/
theorem coe_mk (f : α ->* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α ->+* β) : α -> β) = f :=
  rfl

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: {F : Type*} [FunLike F α β] [RingHomClass F α β] (f : F)
  proof: rfl

中文:
定理 coe_coe
  条件: {F : 类型} [函数状 F α β] [环态射类 F α β] (f : F)
  证明: rfl
-/
theorem coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β] (f : F) :
    ((f : α ->+* β) : α -> β) = f :=
  rfl

attribute [coe] RingHom.toMonoidHom

/--
Instance `coeToMonoidHom` / 实例 `coeToMonoidHom`

English:
instance coeToMonoidHom
  signature: : Coe (α ->+* β) (α ->* β)
  body: ⟨RingHom.toMonoidHom⟩

@[simp]

中文:
实例 coeToMonoidHom
  签名: : Coe (α ->+* β) (α ->* β)
  定义体: ⟨RingHom.toMonoidHom⟩

@[simp]

Depends on / 依赖: RingHom, RingHom.toMonoidHom, toMonoidHom
-/
instance coeToMonoidHom : Coe (α ->+* β) (α ->* β) :=
  ⟨RingHom.toMonoidHom⟩

@[simp]
/--
theorem `toMonoidHom_eq_coe` / 定理 `toMonoidHom_eq_coe`

English:
theorem toMonoidHom_eq_coe
  given: (f : α ->+* β)
  statement: f.toMonoidHom = f
  proof: rfl

中文:
定理 toMonoidHom_eq_coe
  条件: (f : α ->+* β)
  结论: f.toMonoidHom = f
  证明: rfl
-/
theorem toMonoidHom_eq_coe (f : α ->+* β) : f.toMonoidHom = f :=
  rfl

/--
theorem `toMonoidWithZeroHom_eq_coe` / 定理 `toMonoidWithZeroHom_eq_coe`

English:
theorem toMonoidWithZeroHom_eq_coe
  given: (f : α ->+* β)
  statement: (f.toMonoidWithZeroHom : α -> β) = f
  proof: by
  rfl

@[simp]

中文:
定理 toMonoidWithZeroHom_eq_coe
  条件: (f : α ->+* β)
  结论: (f.toMonoidWithZeroHom : α -> β) = f
  证明: by
  rfl

@[simp]
-/
theorem toMonoidWithZeroHom_eq_coe (f : α ->+* β) : (f.toMonoidWithZeroHom : α -> β) = f := by
  rfl

@[simp]
/--
theorem `coe_monoidHom_mk` / 定理 `coe_monoidHom_mk`

English:
theorem coe_monoidHom_mk
  given: (f : α ->* β) (h₁ h₂)
  statement: ((⟨f, h₁, h₂⟩ : α ->+* β) : α ->* β) = f
  proof: rfl

@[simp]

中文:
定理 coe_monoidHom_mk
  条件: (f : α ->* β) (h₁ h₂)
  结论: ((⟨f, h₁, h₂⟩ : α ->+* β) : α ->* β) = f
  证明: rfl

@[simp]
-/
theorem coe_monoidHom_mk (f : α ->* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α ->+* β) : α ->* β) = f :=
  rfl

@[simp]
/--
theorem `toAddMonoidHom_eq_coe` / 定理 `toAddMonoidHom_eq_coe`

English:
theorem toAddMonoidHom_eq_coe
  given: (f : α ->+* β)
  statement: f.toAddMonoidHom = f
  proof: rfl

@[simp]

中文:
定理 toAddMonoidHom_eq_coe
  条件: (f : α ->+* β)
  结论: f.toAddMonoidHom = f
  证明: rfl

@[simp]
-/
theorem toAddMonoidHom_eq_coe (f : α ->+* β) : f.toAddMonoidHom = f :=
  rfl

@[simp]
/--
theorem `coe_addMonoidHom_mk` / 定理 `coe_addMonoidHom_mk`

English:
theorem coe_addMonoidHom_mk
  given: (f : α -> β) (h₁ h₂ h₃ h₄)
  proof: rfl

中文:
定理 coe_addMonoidHom_mk
  条件: (f : α -> β) (h₁ h₂ h₃ h₄)
  证明: rfl
-/
theorem coe_addMonoidHom_mk (f : α -> β) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : α ->+* β) : α ->+ β) = ⟨⟨f, h₃⟩, h₄⟩ :=
  rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : α ->+* β) (f' : α -> β) (h : f' = f)
  body: { f.toMonoidWithZeroHom.copy f' h, f.toAddMonoidHom.copy f' h with }

@[simp]

中文:
定义 copy
  签名: (f : α ->+* β) (f' : α -> β) (h : f' = f)
  定义体: { f.toMonoidWithZeroHom.copy f' h, f.toAddMonoidHom.copy f' h with }

@[simp]

Depends on / 依赖: f.toAddMonoidHom.copy, f.toMonoidWithZeroHom.copy, toAddMonoidHom, toMonoidWithZeroHom
-/
def copy (f : α ->+* β) (f' : α -> β) (h : f' = f) : α ->+* β :=
  { f.toMonoidWithZeroHom.copy f' h, f.toAddMonoidHom.copy f' h with }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : α ->+* β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : α ->+* β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : α ->+* β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : α ->+* β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : α ->+* β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : α ->+* β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

end coe

section

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α ->+* β)

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : α ->+* β} (h : f = g) (x : α)
  statement: f x = g x
  proof: DFunLike.congr_fun h x

中文:
定理 congr_fun
  条件: {f g : α ->+* β} (h : f = g) (x : α)
  结论: f x = g x
  证明: DFunLike.congr_fun h x
-/
protected theorem congr_fun {f g : α ->+* β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (f : α ->+* β) {x y : α} (h : x = y)
  statement: f x = f y
  proof: DFunLike.congr_arg f h

中文:
定理 congr_arg
  条件: (f : α ->+* β) {x y : α} (h : x = y)
  结论: f x = f y
  证明: DFunLike.congr_arg f h
-/
protected theorem congr_arg (f : α ->+* β) {x y : α} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: ⦃f g
  statement: α ->+* β⦄ (h : (f : α -> β) = g) : f = g
  proof: DFunLike.coe_injective h

@[ext]

中文:
定理 coe_inj
  条件: ⦃f g
  结论: α ->+* β⦄ (h : (f : α -> β) = g) : f = g
  证明: DFunLike.coe_injective h

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_inj ⦃f g : α ->+* β⦄ (h : (f : α -> β) = g) : f = g :=
  DFunLike.coe_injective h

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: α ->+* β⦄ : (forall x, f x = g x) -> f = g
  proof: DFunLike.ext _ _

@[simp]

中文:
定理 ext
  条件: ⦃f g
  结论: α ->+* β⦄ : (对任意 x, f x = g x) -> f = g
  证明: DFunLike.ext _ _

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g :=
  DFunLike.ext _ _

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : α ->+* β) (h₁ h₂ h₃ h₄)
  statement: RingHom.mk ⟨⟨f, h₁⟩, h₂⟩ h₃ h₄ = f
  proof: ext fun _ => rfl

中文:
定理 mk_coe
  条件: (f : α ->+* β) (h₁ h₂ h₃ h₄)
  结论: 环态射.mk ⟨⟨f, h₁⟩, h₂⟩ h₃ h₄ = f
  证明: ext fun _ => rfl
-/
theorem mk_coe (f : α ->+* β) (h₁ h₂ h₃ h₄) : RingHom.mk ⟨⟨f, h₁⟩, h₂⟩ h₃ h₄ = f :=
  ext fun _ => rfl

/--
theorem `coe_addMonoidHom_injective` / 定理 `coe_addMonoidHom_injective`

English:
theorem coe_addMonoidHom_injective
  statement: Injective (fun f : α ->+* β => (f : α ->+ β))
  proof: fun _ _ h =>
ext DFunLike.congr_fun (F := α ->+ β) h

中文:
定理 coe_addMonoidHom_injective
  结论: 单射 (fun f : α ->+* β => (f : α ->+ β))
  证明: fun _ _ h =>
ext DFunLike.congr_fun (F := α ->+ β) h
-/
theorem coe_addMonoidHom_injective : Injective (fun f : α ->+* β => (f : α ->+ β)) := fun _ _ h =>
ext DFunLike.congr_fun (F := α ->+ β) h

/--
theorem `coe_monoidHom_injective` / 定理 `coe_monoidHom_injective`

English:
theorem coe_monoidHom_injective
  statement: Injective (fun f : α ->+* β => (f : α ->* β))
  proof: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

中文:
定理 coe_monoidHom_injective
  结论: 单射 (fun f : α ->+* β => (f : α ->* β))
  证明: Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Injective, Injective.of_comp, coe_injective, of_comp
-/
theorem coe_monoidHom_injective : Injective (fun f : α ->+* β => (f : α ->* β)) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : α ->+* β)
  statement: f 0 = 0
  proof: map_zero f

中文:
定理 map_zero
  条件: (f : α ->+* β)
  结论: f 0 = 0
  证明: map_zero f
-/
protected theorem map_zero (f : α ->+* β) : f 0 = 0 :=
  map_zero f

/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: (f : α ->+* β)
  statement: f 1 = 1
  proof: map_one f

中文:
定理 map_one
  条件: (f : α ->+* β)
  结论: f 1 = 1
  证明: map_one f
-/
protected theorem map_one (f : α ->+* β) : f 1 = 1 :=
  map_one f

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (f : α ->+* β)
  statement: forall a b, f (a + b) = f a + f b
  proof: map_add f

中文:
定理 map_add
  条件: (f : α ->+* β)
  结论: 对任意 a b, f (a + b) = f a + f b
  证明: map_add f
-/
protected theorem map_add (f : α ->+* β) : forall a b, f (a + b) = f a + f b :=
  map_add f

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (f : α ->+* β)
  statement: forall a b, f (a * b) = f a * f b
  proof: map_mul f

中文:
定理 map_mul
  条件: (f : α ->+* β)
  结论: 对任意 a b, f (a * b) = f a * f b
  证明: map_mul f
-/
protected theorem map_mul (f : α ->+* β) : forall a b, f (a * b) = f a * f b :=
  map_mul f

/--
theorem `codomain_trivial_iff_map_one_eq_zero` / 定理 `codomain_trivial_iff_map_one_eq_zero`

English:
theorem codomain_trivial_iff_map_one_eq_zero
  statement: (0 : β) = 1 ↔ f 1 = 0
  proof: by rw [map_one, eq_comm]

中文:
定理 codomain_trivial_iff_map_one_eq_zero
  结论: (0 : β) = 1 ↔ f 1 = 0
  证明: by rw [map_one, eq_comm]

Depends on / 依赖: eq_comm, map_one
-/
theorem codomain_trivial_iff_map_one_eq_zero : (0 : β) = 1 ↔ f 1 = 0 := by rw [map_one, eq_comm]

/--
theorem `codomain_trivial_iff_range_trivial` / 定理 `codomain_trivial_iff_range_trivial`

English:
theorem codomain_trivial_iff_range_trivial
  statement: (0 : β) = 1 ↔ forall x, f x = 0
  proof: f.codomain_trivial_iff_map_one_eq_zero.trans
    ⟨fun h x => by rw [← mul_one x, map_mul, h, mul_zero], fun h => h 1⟩

中文:
定理 codomain_trivial_iff_range_trivial
  结论: (0 : β) = 1 ↔ 对任意 x, f x = 0
  证明: f.codomain_trivial_iff_map_one_eq_zero.trans
    ⟨fun h x => by rw [← mul_one x, map_mul, h, mul_zero], fun h => h 1⟩

Depends on / 依赖: codomain_trivial_iff_map_one_eq_zero, f.codomain_trivial_iff_map_one_eq_zero.trans, map_mul, mul_one, mul_zero
-/
theorem codomain_trivial_iff_range_trivial : (0 : β) = 1 ↔ forall x, f x = 0 :=
  f.codomain_trivial_iff_map_one_eq_zero.trans
    ⟨fun h x => by rw [← mul_one x, map_mul, h, mul_zero], fun h => h 1⟩

/--
theorem `map_one_ne_zero` / 定理 `map_one_ne_zero`

English:
theorem map_one_ne_zero
  given: [Nontrivial β]
  statement: f 1 != 0
  proof: mt f.codomain_trivial_iff_map_one_eq_zero.mpr zero_ne_one

include f in

中文:
定理 map_one_ne_zero
  条件: [非平凡 β]
  结论: f 1 != 0
  证明: mt f.codomain_trivial_iff_map_one_eq_zero.mpr zero_ne_one

include f in

Depends on / 依赖: IsOpenImmersion, codomain_trivial_iff_map_one_eq_zero, f.codomain_trivial_iff_map_one_eq_zero.mpr, openCover, zero_ne_one
-/
theorem map_one_ne_zero [Nontrivial β] : f 1 != 0 :=
  mt f.codomain_trivial_iff_map_one_eq_zero.mpr zero_ne_one

include f in
/--
theorem `domain_nontrivial` / 定理 `domain_nontrivial`

English:
theorem domain_nontrivial
  given: [Nontrivial β]
  statement: Nontrivial α
  proof: ⟨⟨1, 0, mt (fun h => show f 1 = 0 by rw [h, map_zero]) f.map_one_ne_zero⟩⟩

中文:
定理 domain_nontrivial
  条件: [非平凡 β]
  结论: 非平凡 α
  证明: ⟨⟨1, 0, mt (fun h => show f 1 = 0 by rw [h, map_zero]) f.map_one_ne_zero⟩⟩

Depends on / 依赖: f.map_one_ne_zero, map_one_ne_zero, map_zero
-/
theorem domain_nontrivial [Nontrivial β] : Nontrivial α :=
  ⟨⟨1, 0, mt (fun h => show f 1 = 0 by rw [h, map_zero]) f.map_one_ne_zero⟩⟩

/--
theorem `codomain_trivial` / 定理 `codomain_trivial`

English:
theorem codomain_trivial
  given: (f : α ->+* β) [h : Subsingleton α]
  statement: Subsingleton β
  proof: (subsingleton_or_nontrivial β).resolve_right fun _ =>
    not_nontrivial_iff_subsingleton.mpr h f.domain_nontrivial

中文:
定理 codomain_trivial
  条件: (f : α ->+* β) [h : 子单例 α]
  结论: 子单例 β
  证明: (subsingleton_or_nontrivial β).resolve_right fun _ =>
    not_nontrivial_iff_subsingleton.mpr h f.domain_nontrivial

Depends on / 依赖: domain_nontrivial, f.domain_nontrivial, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton.mpr, resolve_right, subsingleton_or_nontrivial
-/
theorem codomain_trivial (f : α ->+* β) [h : Subsingleton α] : Subsingleton β :=
  (subsingleton_or_nontrivial β).resolve_right fun _ =>
    not_nontrivial_iff_subsingleton.mpr h f.domain_nontrivial

end

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: [NonAssocRing α] [NonAssocRing β] (f : α ->+* β) (x : α)
  statement: f (-x) = -f x
  proof: map_neg f x

中文:
定理 map_neg
  条件: [非结合环 α] [非结合环 β] (f : α ->+* β) (x : α)
  结论: f (-x) = -f x
  证明: map_neg f x

Depends on / 依赖: F.map, forget, injective, isOpenEmbedding, isOpenEmbedding.injective, mono_iff_injective
-/
protected theorem map_neg [NonAssocRing α] [NonAssocRing β] (f : α ->+* β) (x : α) : f (-x) = -f x :=
  map_neg f x

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: [NonAssocRing α] [NonAssocRing β] (f : α ->+* β) (x y : α)
  proof: map_sub f x y

中文:
定理 map_sub
  条件: [非结合环 α] [非结合环 β] (f : α ->+* β) (x y : α)
  证明: map_sub f x y
-/
protected theorem map_sub [NonAssocRing α] [NonAssocRing β] (f : α ->+* β) (x y : α) :
    f (x - y) = f x - f y :=
  map_sub f x y

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: [NonAssocSemiring α] [NonAssocRing β] (f : α ->* β)
  body: { AddMonoidHom.mk' f map_add, f with }

中文:
定义 mk'
  签名: [非结合半环 α] [非结合环 β] (f : α ->* β)
  定义体: { AddMonoidHom.mk' f map_add, f with }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, map_add
-/
def mk' [NonAssocSemiring α] [NonAssocRing β] (f : α ->* β)
    (map_add : forall a b, f (a + b) = f a + f b) : α ->+* β :=
  { AddMonoidHom.mk' f map_add, f with }

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

/-- The identity ring homomorphism from a semiring to itself. -/
@[instance_reducible]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (α : Type*) [NonAssocSemiring α]
  body: x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

中文:
定义 id
  签名: (α : 类型) [非结合半环 α]
  定义体: x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
-/
def id (α : Type*) [NonAssocSemiring α] : α ->+* α where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (α ->+* α)
  body: ⟨id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 可居 (α ->+* α)
  定义体: ⟨id α⟩

@[simp, norm_cast]
-/
instance : Inhabited (α ->+* α) :=
  ⟨id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(RingHom.id α) = _root_.id
  proof: rfl

@[simp]

中文:
定理 coe_id
  结论: ⇑(环态射.id α) = _root_.id
  证明: rfl

@[simp]
-/
theorem coe_id : ⇑(RingHom.id α) = _root_.id := rfl

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : α)
  statement: RingHom.id α x = x
  proof: rfl

@[simp]

中文:
定理 id_apply
  条件: (x : α)
  结论: 环态射.id α x = x
  证明: rfl

@[simp]
-/
theorem id_apply (x : α) : RingHom.id α x = x :=
  rfl

@[simp]
/--
theorem `coe_addMonoidHom_id` / 定理 `coe_addMonoidHom_id`

English:
theorem coe_addMonoidHom_id
  statement: (id α : α ->+ α) = AddMonoidHom.id α
  proof: rfl

@[simp]

中文:
定理 coe_addMonoidHom_id
  结论: (id α : α ->+ α) = 加法幺半群态射.id α
  证明: rfl

@[simp]
-/
theorem coe_addMonoidHom_id : (id α : α ->+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
/--
theorem `coe_monoidHom_id` / 定理 `coe_monoidHom_id`

English:
theorem coe_monoidHom_id
  statement: (id α : α ->* α) = MonoidHom.id α
  proof: rfl

中文:
定理 coe_monoidHom_id
  结论: (id α : α ->* α) = 幺半群态射.id α
  证明: rfl
-/
theorem coe_monoidHom_id : (id α : α ->* α) = MonoidHom.id α :=
  rfl

variable {_ : NonAssocSemiring γ}

/-- Composition of ring homomorphisms is a ring homomorphism. -/
@[instance_reducible]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : β ->+* γ) (f : α ->+* β)
  body: { g.toNonUnitalRingHom.comp f.toNonUnitalRingHom with toFun x := g (f x), map_one' := by simp }

中文:
定义 comp
  签名: (g : β ->+* γ) (f : α ->+* β)
  定义体: { g.toNonUnitalRingHom.comp f.toNonUnitalRingHom with toFun x := g (f x), map_one' := by simp }

Depends on / 依赖: f.toNonUnitalRingHom, g.toNonUnitalRingHom.comp, map_one, terminal, terminal.from, toNonUnitalRingHom
-/
def comp (g : β ->+* γ) (f : α ->+* β) : α ->+* γ :=
  { g.toNonUnitalRingHom.comp f.toNonUnitalRingHom with toFun x := g (f x), map_one' := by simp }

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: {δ} {_ : NonAssocSemiring δ} (f : α ->+* β) (g : β ->+* γ) (h : γ ->+* δ)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: {δ} {_ : 非结合半环 δ} (f : α ->+* β) (g : β ->+* γ) (h : γ ->+* δ)
  证明: rfl

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* β) (g : β ->+* γ) (h : γ ->+* δ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (hnp : β ->+* γ) (hmn : α ->+* β)
  statement: (hnp.comp hmn : α -> γ) = hnp ∘ hmn
  proof: rfl

中文:
定理 coe_comp
  条件: (hnp : β ->+* γ) (hmn : α ->+* β)
  结论: (hnp.comp hmn : α -> γ) = hnp ∘ hmn
  证明: rfl

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem coe_comp (hnp : β ->+* γ) (hmn : α ->+* β) : (hnp.comp hmn : α -> γ) = hnp ∘ hmn :=
  rfl

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
  证明: rfl

@[simp]
-/
theorem comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α) :
    (hnp.comp hmn : α -> γ) x = hnp (hmn x) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ->+* β)
  statement: f.comp (id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : α ->+* β)
  结论: f.comp (id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : α ->+* β) : f.comp (id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ->+* β)
  statement: (id β).comp f = f
  proof: ext fun _ => rfl

中文:
定理 id_comp
  条件: (f : α ->+* β)
  结论: (id β).comp f = f
  证明: ext fun _ => rfl
-/
theorem id_comp (f : α ->+* β) : (id β).comp f = f :=
  ext fun _ => rfl

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (α ->+* α) where one
  body: id _

中文:
实例 instOne
  签名: : 幺 (α ->+* α) where one
  定义体: id _
-/
instance instOne : One (α ->+* α) where one := id _
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (α ->+* α) where mul
  body: comp

中文:
实例 instMul
  签名: : 乘法 (α ->+* α) where mul
  定义体: comp
-/
instance instMul : Mul (α ->+* α) where mul := comp

/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  statement: (1 : α ->+* α) = id α
  proof: rfl

中文:
引理 one_def
  结论: (1 : α ->+* α) = id α
  证明: rfl
-/
lemma one_def : (1 : α ->+* α) = id α := rfl

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (f g : α ->+* α)
  statement: f * g = f.comp g
  proof: rfl

中文:
引理 mul_def
  条件: (f g : α ->+* α)
  结论: f * g = f.comp g
  证明: rfl
-/
lemma mul_def (f g : α ->+* α) : f * g = f.comp g := rfl

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ⇑(1 : α ->+* α) = _root_.id
  proof: rfl

中文:
引理 coe_one
  结论: ⇑(1 : α ->+* α) = _root_.id
  证明: rfl
-/
@[simp, norm_cast] lemma coe_one : ⇑(1 : α ->+* α) = _root_.id := rfl

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (f g : α ->+* α)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
引理 coe_mul
  条件: (f g : α ->+* α)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl

Depends on / 依赖: Scheme, isOpenImmersion_of_isEmpty
-/
@[simp, norm_cast] lemma coe_mul (f g : α ->+* α) : ⇑(f * g) = f ∘ g := rfl

/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: : Monoid (α ->+* α) where
  body: comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
npow n f := (npowRec n f).copy f^[n] by induction n <;> simp [npowRec, *]
npow_succ _ _ := DFunLike.coe_injective Function.iterate_succ _ _

中文:
实例 instMonoid
  签名: : 幺半群 (α ->+* α) where
  定义体: comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
npow n f := (npowRec n f).copy f^[n] by induction n <;> simp [npowRec, *]
npow_succ _ _ := DFunLike.coe_injective Function.iterate_succ _ _

Depends on / 依赖: IsEmpty, Scheme, comp_id, isIso_of_isEmpty
-/
instance instMonoid : Monoid (α ->+* α) where
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
npow n f := (npowRec n f).copy f^[n] by induction n <;> simp [npowRec, *]
npow_succ _ _ := DFunLike.coe_injective Function.iterate_succ _ _

/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: (f : α ->+* α) (n : Nat)
  statement: ⇑(f ^ n) = f^[n]
  proof: rfl

@[simp]

中文:
引理 coe_pow
  条件: (f : α ->+* α) (n : 自然数)
  结论: ⇑(f ^ n) = f^[n]
  证明: rfl

@[simp]
-/
@[simp, norm_cast] lemma coe_pow (f : α ->+* α) (n : Nat) : ⇑(f ^ n) = f^[n] := rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : β ->+* γ} {f : α ->+* β} (hf : Surjective f)
  proof: ⟨fun h => RingHom.ext hf.forall.2 (RingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : β ->+* γ} {f : α ->+* β} (hf : 满射 f)
  证明: ⟨fun h => RingHom.ext hf.forall.2 (RingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]

Depends on / 依赖: RingHom, RingHom.ext, RingHom.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : β ->+* γ} {f : α ->+* β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => RingHom.ext hf.forall.2 (RingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : β ->+* γ} {f₁ f₂ : α ->+* β} (hg : Injective g)
  proof: ⟨fun h => RingHom.ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

中文:
定理 cancel_left
  条件: {g : β ->+* γ} {f₁ f₂ : α ->+* β} (hg : 单射 g)
  证明: ⟨fun h => RingHom.ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

Depends on / 依赖: RingHom, RingHom.ext, comp_apply
-/
theorem cancel_left {g : β ->+* γ} {f₁ f₂ : α ->+* β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => RingHom.ext fun x => hg by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

end RingHom

section Semiring
variable [Semiring α] [Semiring β]

/--
lemma `RingHom.map_pow` / 引理 `RingHom.map_pow`

English:
lemma RingHom.map_pow
  given: (f : α ->+* β) (a)
  statement: forall n : Nat, f (a ^ n) = f a ^ n
  proof: map_pow f a

中文:
引理 环态射.map_pow
  条件: (f : α ->+* β) (a)
  结论: 对任意 n : 自然数, f (a ^ n) = f a ^ n
  证明: map_pow f a

Depends on / 依赖: IsAffine, IsEmpty, Scheme, isAffine_of_isEmpty
-/
protected lemma RingHom.map_pow (f : α ->+* β) (a) : forall n : Nat, f (a ^ n) = f a ^ n := map_pow f a

end Semiring

namespace AddMonoidHom

variable [CommRing α] [IsDomain α] [CommRing β] (f : β ->+ α)

/--
Definition of `mkRingHomOfMulSelfOfTwoNeZero` / `mkRingHomOfMulSelfOfTwoNeZero` 的定义

English:
definition mkRingHomOfMulSelfOfTwoNeZero
  signature: (h : forall x, f (x * x) = f x * f x) (h_two : (2 : α) != 0)
  body: { f with
    map_one' := h_one,
    map_mul' := fun x y => by
      have hxy := h (x + y)
      rw [mul_add]; rw [add_mul]; rw [add_mul]; rw [f.map_add]; rw [f.map_add]; rw [f.map_add]; rw [f.map_add]; rw [h x]; rw [h y]; rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [← sub_eq_zero]; rw [add_comm (f 

中文:
定义 mkRingHomOfMulSelfOfTwoNeZero
  签名: (h : 对任意 x, f (x * x) = f x * f x) (h_two : (2 : α) != 0)
  定义体: { f with
    map_one' := h_one,
    map_mul' := fun x y => by
      have hxy := h (x + y)
      rw [mul_add]; rw [add_mul]; rw [add_mul]; rw [f.map_add]; rw [f.map_add]; rw [f.map_add]; rw [f.map_add]; rw [h x]; rw [h y]; rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [← sub_eq_zero]; rw [add_comm (f 

Depends on / 依赖: add_assoc, add_comm, add_mul, add_sub_assoc, add_sub_cancel, f.map_add, h_one, map_add, map_mul, map_one, mul_add, mul_comm, sub_eq_zero, sub_sub, two_mul
-/
def mkRingHomOfMulSelfOfTwoNeZero (h : forall x, f (x * x) = f x * f x) (h_two : (2 : α) != 0)
    (h_one : f 1 = 1) : β ->+* α :=
  { f with
    map_one' := h_one,
    map_mul' := fun x y => by
      have hxy := h (x + y)
      rw [mul_add]; rw [add_mul]; rw [add_mul]; rw [f.map_add]; rw [f.map_add]; rw [f.map_add]; rw [f.map_add]; rw [h x]; rw [h y]; rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [← sub_eq_zero]; rw [add_comm (f x * f x + f (y * x))]; rw [← sub_sub]; rw [← sub_sub]; rw [← sub_sub]; rw [mul_comm y x]; rw [mul_comm (f y) (f x)] at hxy
      simp only [add_assoc, add_sub_assoc, add_sub_cancel] at hxy
      rw [sub_sub]; rw [← two_mul]; rw [← add_sub_assoc]; rw [← two_mul]; rw [← mul_sub]; rw [mul_eq_zero (M₀ := α)]; rw [sub_eq_zero]; rw [or_iff_not_imp_left] at hxy
      exact hxy h_two }

@[simp]
/--
theorem `coe_fn_mkRingHomOfMulSelfOfTwoNeZero` / 定理 `coe_fn_mkRingHomOfMulSelfOfTwoNeZero`

English:
theorem coe_fn_mkRingHomOfMulSelfOfTwoNeZero
  given: (h h_two h_one)
  proof: rfl

@[simp]

中文:
定理 coe_fn_mkRingHomOfMulSelfOfTwoNeZero
  条件: (h h_two h_one)
  证明: rfl

@[simp]
-/
theorem coe_fn_mkRingHomOfMulSelfOfTwoNeZero (h h_two h_one) :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β -> α) = f :=
  rfl

@[simp]
/--
theorem `coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero` / 定理 `coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero`

English:
theorem coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero
  given: (h h_two h_one)
  proof: by
  ext
  rfl

中文:
定理 coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero
  条件: (h h_two h_one)
  证明: by
  ext
  rfl
-/
theorem coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero (h h_two h_one) :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β ->+ α) = f := by
  ext
  rfl

end AddMonoidHom
