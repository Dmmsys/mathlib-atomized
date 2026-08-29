/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christopher Hoskin
-/
module

public import Mathlib.Algebra.Algebra.Defs -- shake: keep (`example` dependency)
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Module.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.NonUnitalSubsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Centroid homomorphisms

Let `A` be a (nonunital, non-associative) algebra. The centroid of `A` is the set of linear maps
`T` on `A` such that `T` commutes with left and right multiplication, that is to say, for all `a`
and `b` in `A`,
$$
T(ab) = (Ta)b, T(ab) = a(Tb).
$$
In mathlib we call elements of the centroid "centroid homomorphisms" (`CentroidHom`) in keeping
with `AddMonoidHom` etc.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `CentroidHom`: Maps which preserve left and right multiplication.

## Typeclasses

* `CentroidHomClass`

## References

* [Jacobson, Structure of Rings][Jacobson1956]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

## Tags

centroid
-/

@[expose] public section

assert_not_exists Field

open Function

variable {F M N R α : Type*}

/--
Definition of `CentroidHom` / `CentroidHom` 的定义

English:
structure CentroidHom
  parameters: (α : Type*) [NonUnitalNonAssocSemiring α]
  extends: α ->+ α
  axioms and operations (2):
    - map_mul_left'((a b : α)) : toFun (a * b) = a * toFun b
    - map_mul_right'((a b : α)) : toFun (a * b) = toFun a * b

中文:
结构 CentroidHom
  参数: (α : 类型) [NonUnitalNonAssocSemiring α]
  继承: α ->+ α
  公理与运算 (2 个):
    - map_mul_left'((a b : α)) : toFun (a * b) = a * toFun b
    - map_mul_right'((a b : α)) : toFun (a * b) = toFun a * b
-/
structure CentroidHom (α : Type*) [NonUnitalNonAssocSemiring α] extends α ->+ α where
  /-- Commutativity of centroid homomorphisms with left multiplication. -/
  map_mul_left' (a b : α) : toFun (a * b) = a * toFun b
  /-- Commutativity of centroid homomorphisms with right multiplication. -/
  map_mul_right' (a b : α) : toFun (a * b) = toFun a * b

attribute [nolint docBlame] CentroidHom.toAddMonoidHom

/--
Definition of `CentroidHomClass` / `CentroidHomClass` 的定义

English:
class CentroidHomClass
  parameters: (F : Type*) (α : outParam Type*)
  extends: AddMonoidHomClass F α α
  axioms and operations (2):
    - map_mul_left((f : F) (a b : α)) : f (a * b) = a * f b
    - map_mul_right((f : F) (a b : α)) : f (a * b) = f a * b

中文:
类 CentroidHomClass
  参数: (F : 类型) (α : outParam 类型)
  继承: AddMonoidHomClass F α α
  公理与运算 (2 个):
    - map_mul_left((f : F) (a b : α)) : f (a * b) = a * f b
    - map_mul_right((f : F) (a b : α)) : f (a * b) = f a * b
-/
class CentroidHomClass (F : Type*) (α : outParam Type*)
    [NonUnitalNonAssocSemiring α] [FunLike F α α] : Prop extends AddMonoidHomClass F α α where
  /-- Commutativity of centroid homomorphisms with left multiplication. -/
  map_mul_left (f : F) (a b : α) : f (a * b) = a * f b
  /-- Commutativity of centroid homomorphisms with right multiplication. -/
  map_mul_right (f : F) (a b : α) : f (a * b) = f a * b


export CentroidHomClass (map_mul_left map_mul_right)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: α] [FunLike F α α] [CentroidHomClass F α] :
  body: ⟨fun f =>
    { (f : α ->+ α) with
      toFun := f
      map_mul_left' := map_mul_left f
      map_mul_right' := map_mul_right f }⟩

中文:
实例 [NonUnitalNonAssocSemiring
  签名: α] [FunLike F α α] [CentroidHomClass F α] :
  定义体: ⟨fun f =>
    { (f : α ->+ α) with
      toFun := f
      map_mul_left' := map_mul_left f
      map_mul_right' := map_mul_right f }⟩

Depends on / 依赖: map_mul_left, map_mul_right
-/
instance [NonUnitalNonAssocSemiring α] [FunLike F α α] [CentroidHomClass F α] :
    CoeTC F (CentroidHom α) :=
  ⟨fun f =>
    { (f : α ->+ α) with
      toFun := f
      map_mul_left' := map_mul_left f
      map_mul_right' := map_mul_right f }⟩

/-! ### Centroid homomorphisms -/

namespace CentroidHom

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (CentroidHom α) α α
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x

中文:
实例 :
  签名: FunLike (CentroidHom α) α α
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x

Depends on / 依赖: f.toFun
-/
instance : FunLike (CentroidHom α) α α where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CentroidHomClass (CentroidHom α) α
  body: f.map_zero'
  map_add f := f.map_add'
  map_mul_left f := f.map_mul_left'
  map_mul_right f := f.map_mul_right'

中文:
实例 :
  签名: CentroidHomClass (CentroidHom α) α
  定义体: f.map_zero'
  map_add f := f.map_add'
  map_mul_left f := f.map_mul_left'
  map_mul_right f := f.map_mul_right'

Depends on / 依赖: f.map_zero, map_zero
-/
instance : CentroidHomClass (CentroidHom α) α where
  map_zero f := f.map_zero'
  map_add f := f.map_add'
  map_mul_left f := f.map_mul_left'
  map_mul_right f := f.map_mul_right'

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : CentroidHom α}
  statement: f.toFun = f
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: {f : CentroidHom α}
  结论: f.toFun = f
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe {f : CentroidHom α} : f.toFun = f := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : CentroidHom α} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

@[simp, norm_cast]

中文:
定理 ext
  条件: {f g : CentroidHom α} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

@[simp, norm_cast]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : CentroidHom α} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[simp, norm_cast]
/--
theorem `coe_toAddMonoidHom` / 定理 `coe_toAddMonoidHom`

English:
theorem coe_toAddMonoidHom
  given: (f : CentroidHom α)
  statement: ⇑(f : α ->+ α) = f
  proof: rfl

@[simp]

中文:
定理 coe_toAddMonoidHom
  条件: (f : CentroidHom α)
  结论: ⇑(f : α ->+ α) = f
  证明: rfl

@[simp]
-/
theorem coe_toAddMonoidHom (f : CentroidHom α) : ⇑(f : α ->+ α) = f :=
  rfl

@[simp]
/--
theorem `toAddMonoidHom_eq_coe` / 定理 `toAddMonoidHom_eq_coe`

English:
theorem toAddMonoidHom_eq_coe
  given: (f : CentroidHom α)
  statement: f.toAddMonoidHom = f
  proof: rfl

中文:
定理 toAddMonoidHom_eq_coe
  条件: (f : CentroidHom α)
  结论: f.toAddMonoidHom = f
  证明: rfl
-/
theorem toAddMonoidHom_eq_coe (f : CentroidHom α) : f.toAddMonoidHom = f :=
  rfl

/--
theorem `coe_toAddMonoidHom_injective` / 定理 `coe_toAddMonoidHom_injective`

English:
theorem coe_toAddMonoidHom_injective
  statement: Injective ((↑) : CentroidHom α -> α ->+ α)
  proof: fun _f _g h => ext fun a =>
    haveI := DFunLike.congr_fun h a
    this

中文:
定理 coe_toAddMonoidHom_injective
  结论: Injective ((↑) : CentroidHom α -> α ->+ α)
  证明: fun _f _g h => ext fun a =>
    haveI := DFunLike.congr_fun h a
    this

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem coe_toAddMonoidHom_injective : Injective ((↑) : CentroidHom α -> α ->+ α) :=
  fun _f _g h => ext fun a =>
    haveI := DFunLike.congr_fun h a
    this

/--
Definition of `toEnd` / `toEnd` 的定义

English:
definition toEnd
  signature: (f : CentroidHom α)
  body: (f : α ->+ α)

中文:
定义 toEnd
  签名: (f : CentroidHom α)
  定义体: (f : α ->+ α)
-/
def toEnd (f : CentroidHom α) : AddMonoid.End α :=
  (f : α ->+ α)

/--
theorem `toEnd_injective` / 定理 `toEnd_injective`

English:
theorem toEnd_injective
  statement: Injective (CentroidHom.toEnd : CentroidHom α -> AddMonoid.End α)
  proof: coe_toAddMonoidHom_injective

中文:
定理 toEnd_injective
  结论: Injective (CentroidHom.toEnd : CentroidHom α -> AddMonoid.End α)
  证明: coe_toAddMonoidHom_injective

Depends on / 依赖: coe_toAddMonoidHom_injective
-/
theorem toEnd_injective : Injective (CentroidHom.toEnd : CentroidHom α -> AddMonoid.End α) :=
  coe_toAddMonoidHom_injective

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : CentroidHom α) (f' : α -> α) (h : f' = f)
  body: { f.toAddMonoidHom.copy f' <| h with
    toFun := f'
    map_mul_left' := fun a b => by simp_rw [h, map_mul_left]
    map_mul_right' := fun a b => by simp_rw [h, map_mul_right] }

@[simp]

中文:
定义 copy
  签名: (f : CentroidHom α) (f' : α -> α) (h : f' = f)
  定义体: { f.toAddMonoidHom.copy f' <| h with
    toFun := f'
    map_mul_left' := fun a b => by simp_rw [h, map_mul_left]
    map_mul_right' := fun a b => by simp_rw [h, map_mul_right] }

@[simp]
-/
protected def copy (f : CentroidHom α) (f' : α -> α) (h : f' = f) : CentroidHom α :=
  { f.toAddMonoidHom.copy f' <| h with
    toFun := f'
    map_mul_left' := fun a b => by simp_rw [h, map_mul_left]
    map_mul_right' := fun a b => by simp_rw [h, map_mul_right] }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : CentroidHom α) (f' : α -> α) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : CentroidHom α) (f' : α -> α) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : CentroidHom α) (f' : α -> α) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : CentroidHom α) (f' : α -> α) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : CentroidHom α) (f' : α -> α) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : CentroidHom α) (f' : α -> α) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : CentroidHom α
  body: { AddMonoidHom.id α with
    map_mul_left' := fun _ _ => rfl
    map_mul_right' := fun _ _ => rfl }

中文:
定义 id
  签名: : CentroidHom α
  定义体: { AddMonoidHom.id α with
    map_mul_left' := fun _ _ => rfl
    map_mul_right' := fun _ _ => rfl }
-/
protected def id : CentroidHom α :=
  { AddMonoidHom.id α with
    map_mul_left' := fun _ _ => rfl
    map_mul_right' := fun _ _ => rfl }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CentroidHom α)
  body: ⟨CentroidHom.id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Inhabited (CentroidHom α)
  定义体: ⟨CentroidHom.id α⟩

@[simp, norm_cast]

Depends on / 依赖: CentroidHom, CentroidHom.id
-/
instance : Inhabited (CentroidHom α) :=
  ⟨CentroidHom.id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(CentroidHom.id α) = id
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_id
  结论: ⇑(CentroidHom.id α) = id
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_id : ⇑(CentroidHom.id α) = id :=
  rfl

@[simp, norm_cast]
/--
theorem `toAddMonoidHom_id` / 定理 `toAddMonoidHom_id`

English:
theorem toAddMonoidHom_id
  statement: (CentroidHom.id α : α ->+ α) = AddMonoidHom.id α
  proof: rfl

中文:
定理 toAddMonoidHom_id
  结论: (CentroidHom.id α : α ->+ α) = AddMonoidHom.id α
  证明: rfl
-/
theorem toAddMonoidHom_id : (CentroidHom.id α : α ->+ α) = AddMonoidHom.id α :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: CentroidHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: CentroidHom.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : CentroidHom.id α a = a :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g f : CentroidHom α)
  body: { g.toAddMonoidHom.comp f.toAddMonoidHom with
map_mul_left' := fun _a _b => (congr_arg g <| f.map_mul_left' _ _).trans g.map_mul_left' _ _
    map_mul_right' := fun _a _b =>
(congr_arg g <| f.map_mul_right' _ _).trans g.map_mul_right' _ _ }

@[simp, norm_cast]

中文:
定义 comp
  签名: (g f : CentroidHom α)
  定义体: { g.toAddMonoidHom.comp f.toAddMonoidHom with
map_mul_left' := fun _a _b => (congr_arg g <| f.map_mul_left' _ _).trans g.map_mul_left' _ _
    map_mul_right' := fun _a _b =>
(congr_arg g <| f.map_mul_right' _ _).trans g.map_mul_right' _ _ }

@[simp, norm_cast]

Depends on / 依赖: congr_arg, f.map_mul_left, f.map_mul_right, f.toAddMonoidHom, g.map_mul_left, g.map_mul_right, g.toAddMonoidHom.comp, map_mul_left, map_mul_right, toAddMonoidHom
-/
def comp (g f : CentroidHom α) : CentroidHom α :=
  { g.toAddMonoidHom.comp f.toAddMonoidHom with
map_mul_left' := fun _a _b => (congr_arg g <| f.map_mul_left' _ _).trans g.map_mul_left' _ _
    map_mul_right' := fun _a _b =>
(congr_arg g <| f.map_mul_right' _ _).trans g.map_mul_right' _ _ }

@[simp, norm_cast]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (g f : CentroidHom α)
  statement: ⇑(g.comp f) = g ∘ f
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (g f : CentroidHom α)
  结论: ⇑(g.comp f) = g ∘ f
  证明: rfl

@[simp]
-/
theorem coe_comp (g f : CentroidHom α) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g f : CentroidHom α) (a : α)
  statement: g.comp f a = g (f a)
  proof: rfl

@[simp, norm_cast]

中文:
定理 comp_apply
  条件: (g f : CentroidHom α) (a : α)
  结论: g.comp f a = g (f a)
  证明: rfl

@[simp, norm_cast]
-/
theorem comp_apply (g f : CentroidHom α) (a : α) : g.comp f a = g (f a) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_comp_addMonoidHom` / 定理 `coe_comp_addMonoidHom`

English:
theorem coe_comp_addMonoidHom
  given: (g f : CentroidHom α)
  statement: (g.comp f : α ->+ α) = (g : α ->+ α).comp f
  proof: rfl

@[simp]

中文:
定理 coe_comp_addMonoidHom
  条件: (g f : CentroidHom α)
  结论: (g.comp f : α ->+ α) = (g : α ->+ α).comp f
  证明: rfl

@[simp]
-/
theorem coe_comp_addMonoidHom (g f : CentroidHom α) : (g.comp f : α ->+ α) = (g : α ->+ α).comp f :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (h g f : CentroidHom α)
  statement: (h.comp g).comp f = h.comp (g.comp f)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (h g f : CentroidHom α)
  结论: (h.comp g).comp f = h.comp (g.comp f)
  证明: rfl

@[simp]
-/
theorem comp_assoc (h g f : CentroidHom α) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : CentroidHom α)
  statement: f.comp (CentroidHom.id α) = f
  proof: rfl

@[simp]

中文:
定理 comp_id
  条件: (f : CentroidHom α)
  结论: f.comp (CentroidHom.id α) = f
  证明: rfl

@[simp]
-/
theorem comp_id (f : CentroidHom α) : f.comp (CentroidHom.id α) = f :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : CentroidHom α)
  statement: (CentroidHom.id α).comp f = f
  proof: rfl

@[simp]

中文:
定理 id_comp
  条件: (f : CentroidHom α)
  结论: (CentroidHom.id α).comp f = f
  证明: rfl

@[simp]
-/
theorem id_comp (f : CentroidHom α) : (CentroidHom.id α).comp f = f :=
  rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ f : CentroidHom α} (hf : Surjective f)
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun a => congrFun (congrArg comp a) f⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ f : CentroidHom α} (hf : Surjective f)
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun a => congrFun (congrArg comp a) f⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ f : CentroidHom α} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun a => congrFun (congrArg comp a) f⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g f₁ f₂ : CentroidHom α} (hg : Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g f₁ f₂ : CentroidHom α} (hg : Injective g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g f₁ f₂ : CentroidHom α} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (CentroidHom α)
  body: ⟨{ (0 : α ->+ α) with
      map_mul_left' := fun _a _b => (mul_zero _).symm
      map_mul_right' := fun _a _b => (zero_mul _).symm }⟩

中文:
实例 :
  签名: Zero (CentroidHom α)
  定义体: ⟨{ (0 : α ->+ α) with
      map_mul_left' := fun _a _b => (mul_zero _).symm
      map_mul_right' := fun _a _b => (zero_mul _).symm }⟩

Depends on / 依赖: map_mul_left, map_mul_right, mul_zero, zero_mul
-/
instance : Zero (CentroidHom α) :=
  ⟨{ (0 : α ->+ α) with
      map_mul_left' := fun _a _b => (mul_zero _).symm
      map_mul_right' := fun _a _b => (zero_mul _).symm }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (CentroidHom α)
  body: ⟨CentroidHom.id α⟩

中文:
实例 :
  签名: One (CentroidHom α)
  定义体: ⟨CentroidHom.id α⟩

Depends on / 依赖: CentroidHom, CentroidHom.id
-/
instance : One (CentroidHom α) :=
  ⟨CentroidHom.id α⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (CentroidHom α)
  body: ⟨fun f g =>
    { (f + g : α ->+ α) with
      map_mul_left' := fun a b => by
        simp [map_mul_left, mul_add]
      map_mul_right' := fun a b => by
        simp [map_mul_right, add_mul] }⟩

中文:
实例 :
  签名: Add (CentroidHom α)
  定义体: ⟨fun f g =>
    { (f + g : α ->+ α) with
      map_mul_left' := fun a b => by
        simp [map_mul_left, mul_add]
      map_mul_right' := fun a b => by
        simp [map_mul_right, add_mul] }⟩

Depends on / 依赖: add_mul, map_mul_left, map_mul_right, mul_add
-/
instance : Add (CentroidHom α) :=
  ⟨fun f g =>
    { (f + g : α ->+ α) with
      map_mul_left' := fun a b => by
        simp [map_mul_left, mul_add]
      map_mul_right' := fun a b => by
        simp [map_mul_right, add_mul] }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (CentroidHom α)
  body: ⟨comp⟩

中文:
实例 :
  签名: Mul (CentroidHom α)
  定义体: ⟨comp⟩
-/
instance : Mul (CentroidHom α) :=
  ⟨comp⟩

variable [Monoid M] [Monoid N] [Semiring R]
variable [DistribMulAction M α] [SMulCommClass M α α] [IsScalarTower M α α]
variable [DistribMulAction N α] [SMulCommClass N α α] [IsScalarTower N α α]
variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul M (CentroidHom α) where
  body: { (n • f : α ->+ α) with
      map_mul_left' := fun a b => by
        change n • f (a * b) = a * n • f b
        rw [map_mul_left f]; rw [← mul_smul_comm]
      map_mul_right' := fun a b => by
        change n • f (a * b) = n • f a * b
        rw [map_mul_right f]; rw [← smul_mul_assoc] }

中文:
实例 instSMul
  签名: : SMul M (CentroidHom α) where
  定义体: { (n • f : α ->+ α) with
      map_mul_left' := fun a b => by
        change n • f (a * b) = a * n • f b
        rw [map_mul_left f]; rw [← mul_smul_comm]
      map_mul_right' := fun a b => by
        change n • f (a * b) = n • f a * b
        rw [map_mul_right f]; rw [← smul_mul_assoc] }

Depends on / 依赖: map_mul_left, map_mul_right, mul_smul_comm, smul_mul_assoc
-/
instance instSMul : SMul M (CentroidHom α) where
  smul n f :=
    { (n • f : α ->+ α) with
      map_mul_left' := fun a b => by
        change n • f (a * b) = a * n • f b
        rw [map_mul_left f]; rw [← mul_smul_comm]
      map_mul_right' := fun a b => by
        change n • f (a * b) = n • f a * b
        rw [map_mul_right f]; rw [← smul_mul_assoc] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M N] [IsScalarTower M N α] : IsScalarTower M N (CentroidHom α) where
  body: ext fun _ => smul_assoc _ _ _

中文:
实例 [SMul
  签名: M N] [IsScalarTower M N α] : IsScalarTower M N (CentroidHom α) where
  定义体: ext fun _ => smul_assoc _ _ _

Depends on / 依赖: smul_assoc
-/
instance [SMul M N] [IsScalarTower M N α] : IsScalarTower M N (CentroidHom α) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: M N α] : SMulCommClass M N (CentroidHom α) where
  body: ext fun _ => smul_comm _ _ _

中文:
实例 [SMulCommClass
  签名: M N α] : SMulCommClass M N (CentroidHom α) where
  定义体: ext fun _ => smul_comm _ _ _

Depends on / 依赖: smul_comm
-/
instance [SMulCommClass M N α] : SMulCommClass M N (CentroidHom α) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribMulAction
  signature: Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (CentroidHom α) where
  body: ext fun _ => op_smul_eq_smul _ _

中文:
实例 [DistribMulAction
  签名: Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (CentroidHom α) where
  定义体: ext fun _ => op_smul_eq_smul _ _

Depends on / 依赖: op_smul_eq_smul, untrop
-/
instance [DistribMulAction Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (CentroidHom α) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

/--
Instance `isScalarTowerRight` / 实例 `isScalarTowerRight`

English:
instance isScalarTowerRight
  signature: : IsScalarTower M (CentroidHom α) (CentroidHom α) where
  body: rfl

中文:
实例 isScalarTowerRight
  签名: : IsScalarTower M (CentroidHom α) (CentroidHom α) where
  定义体: rfl
-/
instance isScalarTowerRight : IsScalarTower M (CentroidHom α) (CentroidHom α) where
  smul_assoc _ _ _ := rfl

/--
Instance `hasNPowNat` / 实例 `hasNPowNat`

English:
instance hasNPowNat
  signature: : Pow (CentroidHom α) Nat
  body: ⟨fun f n =>
    { toAddMonoidHom := (f.toEnd ^ n : AddMonoid.End α)
      map_mul_left' := fun a b => by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ']
          exact (congr_arg f.toEnd ih).trans (f.map_mul_left' _ _)
      map_mul_right' := fun a b =

中文:
实例 hasNPowNat
  签名: : Pow (CentroidHom α) 自然数
  定义体: ⟨fun f n =>
    { toAddMonoidHom := (f.toEnd ^ n : AddMonoid.End α)
      map_mul_left' := fun a b => by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ']
          exact (congr_arg f.toEnd ih).trans (f.map_mul_left' _ _)
      map_mul_right' := fun a b =

Depends on / 依赖: AddMonoid, AddMonoid.End, congr_arg, f.map_mul_left, f.map_mul_right, f.toEnd, map_mul_left, map_mul_right, pow_succ, toAddMonoidHom
-/
instance hasNPowNat : Pow (CentroidHom α) Nat :=
  ⟨fun f n =>
    { toAddMonoidHom := (f.toEnd ^ n : AddMonoid.End α)
      map_mul_left' := fun a b => by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ']
          exact (congr_arg f.toEnd ih).trans (f.map_mul_left' _ _)
      map_mul_right' := fun a b => by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ']
          exact (congr_arg f.toEnd ih).trans (f.map_mul_right' _ _)}⟩

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : CentroidHom α) = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ⇑(0 : CentroidHom α) = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ⇑(0 : CentroidHom α) = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : CentroidHom α) = id
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_one
  结论: ⇑(1 : CentroidHom α) = id
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_one : ⇑(1 : CentroidHom α) = id :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (f g : CentroidHom α)
  statement: ⇑(f + g) = f + g
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (f g : CentroidHom α)
  结论: ⇑(f + g) = f + g
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (f g : CentroidHom α) : ⇑(f + g) = f + g :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : CentroidHom α)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (f g : CentroidHom α)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mul (f g : CentroidHom α) : ⇑(f * g) = f ∘ g :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (n : M) (f : CentroidHom α)
  statement: ⇑(n • f) = n • ⇑f
  proof: rfl

@[simp]

中文:
定理 coe_smul
  条件: (n : M) (f : CentroidHom α)
  结论: ⇑(n • f) = n • ⇑f
  证明: rfl

@[simp]
-/
theorem coe_smul (n : M) (f : CentroidHom α) : ⇑(n • f) = n • ⇑f :=
  rfl

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (a : α)
  statement: (0 : CentroidHom α) a = 0
  proof: rfl

@[simp]

中文:
定理 zero_apply
  条件: (a : α)
  结论: (0 : CentroidHom α) a = 0
  证明: rfl

@[simp]
-/
theorem zero_apply (a : α) : (0 : CentroidHom α) a = 0 :=
  rfl

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (a : α)
  statement: (1 : CentroidHom α) a = a
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: (a : α)
  结论: (1 : CentroidHom α) a = a
  证明: rfl

@[simp]
-/
theorem one_apply (a : α) : (1 : CentroidHom α) a = a :=
  rfl

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (f g : CentroidHom α) (a : α)
  statement: (f + g) a = f a + g a
  proof: rfl

@[simp]

中文:
定理 add_apply
  条件: (f g : CentroidHom α) (a : α)
  结论: (f + g) a = f a + g a
  证明: rfl

@[simp]
-/
theorem add_apply (f g : CentroidHom α) (a : α) : (f + g) a = f a + g a :=
  rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (f g : CentroidHom α) (a : α)
  statement: (f * g) a = f (g a)
  proof: rfl

@[simp]

中文:
定理 mul_apply
  条件: (f g : CentroidHom α) (a : α)
  结论: (f * g) a = f (g a)
  证明: rfl

@[simp]
-/
theorem mul_apply (f g : CentroidHom α) (a : α) : (f * g) a = f (g a) :=
  rfl

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (n : M) (f : CentroidHom α) (a : α)
  statement: (n • f) a = n • f a
  proof: rfl

example : SMul Nat (CentroidHom α) := instSMul

@[simp]

中文:
定理 smul_apply
  条件: (n : M) (f : CentroidHom α) (a : α)
  结论: (n • f) a = n • f a
  证明: rfl

example : SMul Nat (CentroidHom α) := instSMul

@[simp]
-/
theorem smul_apply (n : M) (f : CentroidHom α) (a : α) : (n • f) a = n • f a :=
  rfl

example : SMul Nat (CentroidHom α) := instSMul

@[simp]
/--
theorem `toEnd_zero` / 定理 `toEnd_zero`

English:
theorem toEnd_zero
  statement: (0 : CentroidHom α).toEnd = 0
  proof: rfl

@[simp]

中文:
定理 toEnd_zero
  结论: (0 : CentroidHom α).toEnd = 0
  证明: rfl

@[simp]
-/
theorem toEnd_zero : (0 : CentroidHom α).toEnd = 0 :=
  rfl

@[simp]
/--
theorem `toEnd_add` / 定理 `toEnd_add`

English:
theorem toEnd_add
  given: (x y : CentroidHom α)
  statement: (x + y).toEnd = x.toEnd + y.toEnd
  proof: rfl

中文:
定理 toEnd_add
  条件: (x y : CentroidHom α)
  结论: (x + y).toEnd = x.toEnd + y.toEnd
  证明: rfl
-/
theorem toEnd_add (x y : CentroidHom α) : (x + y).toEnd = x.toEnd + y.toEnd :=
  rfl

/--
theorem `toEnd_smul` / 定理 `toEnd_smul`

English:
theorem toEnd_smul
  given: (m : M) (x : CentroidHom α)
  statement: (m • x).toEnd = m • x.toEnd
  proof: rfl

中文:
定理 toEnd_smul
  条件: (m : M) (x : CentroidHom α)
  结论: (m • x).toEnd = m • x.toEnd
  证明: rfl
-/
theorem toEnd_smul (m : M) (x : CentroidHom α) : (m • x).toEnd = m • x.toEnd :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (CentroidHom α)
  body: coe_toAddMonoidHom_injective.addCommMonoid _ toEnd_zero toEnd_add (swap toEnd_smul)

中文:
实例 :
  签名: AddCommMonoid (CentroidHom α)
  定义体: coe_toAddMonoidHom_injective.addCommMonoid _ toEnd_zero toEnd_add (swap toEnd_smul)

Depends on / 依赖: addCommMonoid, coe_toAddMonoidHom_injective, coe_toAddMonoidHom_injective.addCommMonoid, toEnd_add, toEnd_smul, toEnd_zero
-/
instance : AddCommMonoid (CentroidHom α) :=
  coe_toAddMonoidHom_injective.addCommMonoid _ toEnd_zero toEnd_add (swap toEnd_smul)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (CentroidHom α)
  body: n • (1 : CentroidHom α)

@[simp, norm_cast]

中文:
实例 :
  签名: 自然数Cast (CentroidHom α)
  定义体: n • (1 : CentroidHom α)

@[simp, norm_cast]

Depends on / 依赖: CentroidHom
-/
instance : NatCast (CentroidHom α) where natCast n := n • (1 : CentroidHom α)

@[simp, norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: ⇑(n : CentroidHom α) = n • (CentroidHom.id α)
  proof: rfl

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: ⇑(n : CentroidHom α) = n • (CentroidHom.id α)
  证明: rfl
-/
theorem coe_natCast (n : Nat) : ⇑(n : CentroidHom α) = n • (CentroidHom.id α) :=
  rfl

/--
theorem `natCast_apply` / 定理 `natCast_apply`

English:
theorem natCast_apply
  given: (n : Nat) (m : α)
  statement: (n : CentroidHom α) m = n • m
  proof: rfl

@[simp]

中文:
定理 natCast_apply
  条件: (n : 自然数) (m : α)
  结论: (n : CentroidHom α) m = n • m
  证明: rfl

@[simp]
-/
theorem natCast_apply (n : Nat) (m : α) : (n : CentroidHom α) m = n • m :=
  rfl

@[simp]
/--
theorem `toEnd_one` / 定理 `toEnd_one`

English:
theorem toEnd_one
  statement: (1 : CentroidHom α).toEnd = 1
  proof: rfl

@[simp]

中文:
定理 toEnd_one
  结论: (1 : CentroidHom α).toEnd = 1
  证明: rfl

@[simp]
-/
theorem toEnd_one : (1 : CentroidHom α).toEnd = 1 :=
  rfl

@[simp]
/--
theorem `toEnd_mul` / 定理 `toEnd_mul`

English:
theorem toEnd_mul
  given: (x y : CentroidHom α)
  statement: (x * y).toEnd = x.toEnd * y.toEnd
  proof: rfl

@[simp]

中文:
定理 toEnd_mul
  条件: (x y : CentroidHom α)
  结论: (x * y).toEnd = x.toEnd * y.toEnd
  证明: rfl

@[simp]

Depends on / 依赖: mul_eq_zero_iff, mul_eq_zero_iff.mp
-/
theorem toEnd_mul (x y : CentroidHom α) : (x * y).toEnd = x.toEnd * y.toEnd :=
  rfl

@[simp]
/--
theorem `toEnd_pow` / 定理 `toEnd_pow`

English:
theorem toEnd_pow
  given: (x : CentroidHom α) (n : Nat)
  statement: (x ^ n).toEnd = x.toEnd ^ n
  proof: rfl

@[simp, norm_cast]

中文:
定理 toEnd_pow
  条件: (x : CentroidHom α) (n : 自然数)
  结论: (x ^ n).toEnd = x.toEnd ^ n
  证明: rfl

@[simp, norm_cast]
-/
theorem toEnd_pow (x : CentroidHom α) (n : Nat) : (x ^ n).toEnd = x.toEnd ^ n :=
  rfl

@[simp, norm_cast]
/--
theorem `toEnd_natCast` / 定理 `toEnd_natCast`

English:
theorem toEnd_natCast
  given: (n : Nat)
  statement: (n : CentroidHom α).toEnd = ↑n
  proof: rfl

中文:
定理 toEnd_natCast
  条件: (n : 自然数)
  结论: (n : CentroidHom α).toEnd = ↑n
  证明: rfl
-/
theorem toEnd_natCast (n : Nat) : (n : CentroidHom α).toEnd = ↑n :=
  rfl

-- cf `add_monoid.End.semiring`
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semiring (CentroidHom α)
  body: toEnd_injective.semiring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_smul toEnd_pow
    toEnd_natCast

中文:
实例 :
  签名: Semiring (CentroidHom α)
  定义体: toEnd_injective.semiring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_smul toEnd_pow
    toEnd_natCast

Depends on / 依赖: semiring, toEnd_add, toEnd_injective, toEnd_injective.semiring, toEnd_mul, toEnd_natCast, toEnd_one, toEnd_pow, toEnd_smul, toEnd_zero
-/
instance : Semiring (CentroidHom α) :=
  toEnd_injective.semiring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_smul toEnd_pow
    toEnd_natCast

variable (α) in
/-- `CentroidHom.toEnd` as a `RingHom`. -/
@[simps]
/--
Definition of `toEndRingHom` / `toEndRingHom` 的定义

English:
definition toEndRingHom
  signature: : CentroidHom α ->+* AddMonoid.End α where
  body: toEnd
  map_zero' := toEnd_zero
  map_one' := toEnd_one
  map_add' := toEnd_add
  map_mul' := toEnd_mul

中文:
定义 toEndRingHom
  签名: : CentroidHom α ->+* AddMonoid.End α where
  定义体: toEnd
  map_zero' := toEnd_zero
  map_one' := toEnd_one
  map_add' := toEnd_add
  map_mul' := toEnd_mul
-/
def toEndRingHom : CentroidHom α ->+* AddMonoid.End α where
  toFun := toEnd
  map_zero' := toEnd_zero
  map_one' := toEnd_one
  map_add' := toEnd_add
  map_mul' := toEnd_mul

/--
theorem `comp_mul_comm` / 定理 `comp_mul_comm`

English:
theorem comp_mul_comm
  given: (T S : CentroidHom α) (a b : α)
  statement: (T ∘ S) (a * b) = (S ∘ T) (a * b)
  proof: by
  simp only [Function.comp_apply]
  rw [map_mul_right]; rw [map_mul_left]; rw [← map_mul_right]; rw [← map_mul_left]

中文:
定理 comp_mul_comm
  条件: (T S : CentroidHom α) (a b : α)
  结论: (T ∘ S) (a * b) = (S ∘ T) (a * b)
  证明: by
  simp only [Function.comp_apply]
  rw [map_mul_right]; rw [map_mul_left]; rw [← map_mul_right]; rw [← map_mul_left]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, map_mul_left, map_mul_right
-/
theorem comp_mul_comm (T S : CentroidHom α) (a b : α) : (T ∘ S) (a * b) = (S ∘ T) (a * b) := by
  simp only [Function.comp_apply]
  rw [map_mul_right]; rw [map_mul_left]; rw [← map_mul_right]; rw [← map_mul_left]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction M (CentroidHom α)
  body: toEnd_injective.distribMulAction (toEndRingHom α).toAddMonoidHom toEnd_smul

中文:
实例 :
  签名: DistribMulAction M (CentroidHom α)
  定义体: toEnd_injective.distribMulAction (toEndRingHom α).toAddMonoidHom toEnd_smul

Depends on / 依赖: distribMulAction, toAddMonoidHom, toEndRingHom, toEnd_injective, toEnd_injective.distribMulAction, toEnd_smul
-/
instance : DistribMulAction M (CentroidHom α) :=
  toEnd_injective.distribMulAction (toEndRingHom α).toAddMonoidHom toEnd_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (CentroidHom α)
  body: toEnd_injective.module R (toEndRingHom α).toAddMonoidHom toEnd_smul

中文:
实例 :
  签名: Module R (CentroidHom α)
  定义体: toEnd_injective.module R (toEndRingHom α).toAddMonoidHom toEnd_smul

Depends on / 依赖: module, toAddMonoidHom, toEndRingHom, toEnd_injective, toEnd_injective.module, toEnd_smul
-/
instance : Module R (CentroidHom α) :=
  toEnd_injective.module R (toEndRingHom α).toAddMonoidHom toEnd_smul

/-!
The following instances show that `α` is a non-unital and non-associative algebra over
`CentroidHom α`.
-/

/--
Instance `applyModule` / 实例 `applyModule`

English:
instance applyModule
  signature: : Module (CentroidHom α) α where
  body: T a
  add_smul _ _ _ := rfl
  zero_smul _ := rfl
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := map_zero
  smul_add := map_add

@[simp]

中文:
实例 applyModule
  签名: : Module (CentroidHom α) α where
  定义体: T a
  add_smul _ _ _ := rfl
  zero_smul _ := rfl
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := map_zero
  smul_add := map_add

@[simp]
-/
instance applyModule : Module (CentroidHom α) α where
  smul T a := T a
  add_smul _ _ _ := rfl
  zero_smul _ := rfl
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := map_zero
  smul_add := map_add

@[simp]
/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (T : CentroidHom α) (a : α)
  statement: T • a = T a
  proof: rfl

中文:
引理 smul_def
  条件: (T : CentroidHom α) (a : α)
  结论: T • a = T a
  证明: rfl
-/
lemma smul_def (T : CentroidHom α) (a : α) : T • a = T a := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass (CentroidHom α) α α
  body: map_mul_left _ _ _

中文:
实例 :
  签名: SMulCommClass (CentroidHom α) α α
  定义体: map_mul_left _ _ _

Depends on / 依赖: map_mul_left
-/
instance : SMulCommClass (CentroidHom α) α α where
  smul_comm _ _ _ := map_mul_left _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass α (CentroidHom α) α
  body: SMulCommClass.symm _ _ _

中文:
实例 :
  签名: SMulCommClass α (CentroidHom α) α
  定义体: SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance : SMulCommClass α (CentroidHom α) α := SMulCommClass.symm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower (CentroidHom α) α α
  body: (map_mul_right _ _ _).symm

中文:
实例 :
  签名: IsScalarTower (CentroidHom α) α α
  定义体: (map_mul_right _ _ _).symm

Depends on / 依赖: map_mul_right
-/
instance : IsScalarTower (CentroidHom α) α α where
  smul_assoc _ _ _ := (map_mul_right _ _ _).symm

/-!
Let `α` be an algebra over `R`, such that the canonical ring homomorphism of `R` into
`CentroidHom α` lies in the center of `CentroidHom α`. Then `CentroidHom α` is an algebra over `R`
-/

variable {R : Type*}
variable [CommSemiring R]
variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]

/-- The natural ring homomorphism from `R` into `CentroidHom α`.

This is a stronger version of `Module.toAddMonoidEnd`. -/
@[simps! apply_toFun]
/--
Definition of `_root_.Module.toCentroidHom` / `_root_.Module.toCentroidHom` 的定义

English:
definition _root_.Module.toCentroidHom
  signature: : R ->+* CentroidHom α
  body: RingHom.smulOneHom

中文:
定义 _root_.Module.toCentroidHom
  签名: : R ->+* CentroidHom α
  定义体: RingHom.smulOneHom

Depends on / 依赖: RingHom, RingHom.smulOneHom, smulOneHom
-/
def _root_.Module.toCentroidHom : R ->+* CentroidHom α := RingHom.smulOneHom

open Module in
/-- `CentroidHom α` as an algebra over `R`. -/
example (h : forall (r : R) (T : CentroidHom α), toCentroidHom r * T = T * toCentroidHom r) :
    Algebra R (CentroidHom α) := toCentroidHom.toAlgebra' h

local notation "L" => AddMonoid.End.mulLeft
local notation "R" => AddMonoid.End.mulRight

/--
lemma `centroid_eq_centralizer_mulLeftRight` / 引理 `centroid_eq_centralizer_mulLeftRight`

English:
lemma centroid_eq_centralizer_mulLeftRight
  proof: by
  ext T
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, rfl⟩ S (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact AddMonoidHom.ext fun b => (map_mul_left f a b).symm
    · exact AddMonoidHom.ext fun a => (map_mul_right f a b).symm
  · rw [Subsemiring.mem_centralizer_iff] at h
    refine ⟨⟨T, fun a b => ?_, fun a b => ?

中文:
引理 centroid_eq_centralizer_mulLeftRight
  证明: by
  ext T
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, rfl⟩ S (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact AddMonoidHom.ext fun b => (map_mul_left f a b).symm
    · exact AddMonoidHom.ext fun a => (map_mul_right f a b).symm
  · rw [Subsemiring.mem_centralizer_iff] at h
    refine ⟨⟨T, fun a b => ?_, fun a b => ?

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, Subsemiring, Subsemiring.mem_centralizer_iff, map_mul_left, map_mul_right, mem_centralizer_iff
-/
lemma centroid_eq_centralizer_mulLeftRight :
    RingHom.rangeS (toEndRingHom α) = Subsemiring.centralizer (Set.range L union Set.range R) := by
  ext T
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, rfl⟩ S (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact AddMonoidHom.ext fun b => (map_mul_left f a b).symm
    · exact AddMonoidHom.ext fun a => (map_mul_right f a b).symm
  · rw [Subsemiring.mem_centralizer_iff] at h
    refine ⟨⟨T, fun a b => ?_, fun a b => ?_⟩, rfl⟩
    · exact congr($(h (L a) (.inl ⟨a, rfl⟩)) b).symm
    · exact congr($(h (R b) (.inr ⟨b, rfl⟩)) a).symm

/--
Definition of `centerToCentroidCenter` / `centerToCentroidCenter` 的定义

English:
definition centerToCentroidCenter
  signature: :
  body: { L (z : α) with
      val := ⟨L z, z.prop.left_comm, z.prop.left_assoc ⟩
      property := by
        rw [Subsemiring.mem_center_iff]
        intro g
        ext a
        exact map_mul_left g (↑z) a }
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact rfl
  map_add' := fun

中文:
定义 centerToCentroidCenter
  签名: :
  定义体: { L (z : α) with
      val := ⟨L z, z.prop.left_comm, z.prop.left_assoc ⟩
      property := by
        rw [Subsemiring.mem_center_iff]
        intro g
        ext a
        exact map_mul_left g (↑z) a }
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact rfl
  map_add' := fun

Depends on / 依赖: Subsemiring, Subsemiring.mem_center_iff, ZeroMemClass, ZeroMemClass.coe_zero, coe_zero, left_assoc, left_comm, map_add, map_mul, map_mul_left, map_zero, mem_center_iff, prop.left_assoc, property, z.prop.left_assoc, z.prop.left_comm
-/
def centerToCentroidCenter :
    NonUnitalSubsemiring.center α ->ₙ+* Subsemiring.center (CentroidHom α) where
  toFun z :=
    { L (z : α) with
      val := ⟨L z, z.prop.left_comm, z.prop.left_assoc ⟩
      property := by
        rw [Subsemiring.mem_center_iff]
        intro g
        ext a
        exact map_mul_left g (↑z) a }
  map_zero' := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact rfl
  map_add' := fun _ _ => by
    dsimp
    simp only [map_add]
    rfl
  map_mul' z₁ z₂ := by ext a; exact (z₁.prop.left_assoc z₂ a).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (Subsemiring.center (CentroidHom α)) α α
  body: f.val.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x

中文:
实例 :
  签名: FunLike (Subsemiring.center (CentroidHom α)) α α
  定义体: f.val.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x

Depends on / 依赖: f.val.toFun
-/
instance : FunLike (Subsemiring.center (CentroidHom α)) α α where
  coe f := f.val.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x

/--
lemma `centerToCentroidCenter_apply` / 引理 `centerToCentroidCenter_apply`

English:
lemma centerToCentroidCenter_apply
  given: (z : NonUnitalSubsemiring.center α) (a : α)
  proof: rfl

中文:
引理 centerToCentroidCenter_apply
  条件: (z : NonUnitalSubsemiring.center α) (a : α)
  证明: rfl
-/
lemma centerToCentroidCenter_apply (z : NonUnitalSubsemiring.center α) (a : α) :
    (centerToCentroidCenter z) a = z * a := rfl

/--
Definition of `centerToCentroid` / `centerToCentroid` 的定义

English:
definition centerToCentroid
  signature: : NonUnitalSubsemiring.center α ->ₙ+* CentroidHom α
  body: NonUnitalRingHom.comp
    (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
    centerToCentroidCenter

中文:
定义 centerToCentroid
  签名: : NonUnitalSubsemiring.center α ->ₙ+* CentroidHom α
  定义体: NonUnitalRingHom.comp
    (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
    centerToCentroidCenter

Depends on / 依赖: CentroidHom, NonUnitalRingHom, NonUnitalRingHom.comp, Subsemiring, Subsemiring.center, SubsemiringClass, SubsemiringClass.subtype, center, centerToCentroidCenter, subtype, toNonUnitalRingHom
-/
def centerToCentroid : NonUnitalSubsemiring.center α ->ₙ+* CentroidHom α :=
  NonUnitalRingHom.comp
    (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
    centerToCentroidCenter

/--
lemma `centerToCentroid_apply` / 引理 `centerToCentroid_apply`

English:
lemma centerToCentroid_apply
  given: (z : NonUnitalSubsemiring.center α) (a : α)
  proof: rfl

中文:
引理 centerToCentroid_apply
  条件: (z : NonUnitalSubsemiring.center α) (a : α)
  证明: rfl
-/
lemma centerToCentroid_apply (z : NonUnitalSubsemiring.center α) (a : α) :
    (centerToCentroid z) a = z * a := rfl

/--
lemma `_root_.NonUnitalNonAssocSemiring.mem_center_iff` / 引理 `_root_.NonUnitalNonAssocSemiring.mem_center_iff`

English:
lemma _root_.NonUnitalNonAssocSemiring.mem_center_iff
  given: (a : α)
  proof: by
  constructor
· exact fun ha => ⟨AddMonoidHom.ext fun _ => (IsMulCentral.comm ha _).symm,
      ⟨centerToCentroid ⟨a, ha⟩, rfl⟩⟩
  · rintro ⟨hc, ⟨T, hT⟩⟩
    have e1 (d : α) : T d = a * d := congr($hT d)
    have e2 (d : α) : T d = d * a := congr($(hT.trans hc.symm) d)
    constructor
    case co

中文:
引理 _root_.NonUnitalNonAssocSemiring.mem_center_iff
  条件: (a : α)
  证明: by
  constructor
· exact fun ha => ⟨AddMonoidHom.ext fun _ => (IsMulCentral.comm ha _).symm,
      ⟨centerToCentroid ⟨a, ha⟩, rfl⟩⟩
  · rintro ⟨hc, ⟨T, hT⟩⟩
    have e1 (d : α) : T d = a * d := congr($hT d)
    have e2 (d : α) : T d = d * a := congr($(hT.trans hc.symm) d)
    constructor
    case co

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, IsMulCentral, IsMulCentral.comm, centerToCentroid, hT.trans, hc.symm, left_assoc, map_mul_left, map_mul_right, right_assoc
-/
lemma _root_.NonUnitalNonAssocSemiring.mem_center_iff (a : α) :
    a in NonUnitalSubsemiring.center α ↔ R a = L a ∧ (L a) in RingHom.rangeS (toEndRingHom α) := by
  constructor
· exact fun ha => ⟨AddMonoidHom.ext fun _ => (IsMulCentral.comm ha _).symm,
      ⟨centerToCentroid ⟨a, ha⟩, rfl⟩⟩
  · rintro ⟨hc, ⟨T, hT⟩⟩
    have e1 (d : α) : T d = a * d := congr($hT d)
    have e2 (d : α) : T d = d * a := congr($(hT.trans hc.symm) d)
    constructor
    case comm => exact (congr($hc.symm ·))
    case left_assoc => simpa [e1] using (map_mul_right T · ·)
    case right_assoc => simpa [e2] using (map_mul_left T · ·)

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocCommSemiring

variable [NonUnitalNonAssocCommSemiring α]

/-
Left and right multiplication coincide as α is commutative
-/
local notation "L" => AddMonoid.End.mulLeft

/--
lemma `_root_.NonUnitalNonAssocCommSemiring.mem_center_iff` / 引理 `_root_.NonUnitalNonAssocCommSemiring.mem_center_iff`

English:
lemma _root_.NonUnitalNonAssocCommSemiring.mem_center_iff
  given: (a : α)
  proof: by
  rw [NonUnitalNonAssocSemiring.mem_center_iff]; rw [CentroidHom.centroid_eq_centralizer_mulLeftRight]; rw [Subsemiring.mem_centralizer_iff]; rw [AddMonoid.End.mulRight_eq_mulLeft]; rw [Set.union_self]
  aesop

中文:
引理 _root_.NonUnitalNonAssocCommSemiring.mem_center_iff
  条件: (a : α)
  证明: by
  rw [NonUnitalNonAssocSemiring.mem_center_iff]; rw [CentroidHom.centroid_eq_centralizer_mulLeftRight]; rw [Subsemiring.mem_centralizer_iff]; rw [AddMonoid.End.mulRight_eq_mulLeft]; rw [Set.union_self]
  aesop

Depends on / 依赖: AddMonoid, AddMonoid.End.mulRight_eq_mulLeft, CentroidHom, CentroidHom.centroid_eq_centralizer_mulLeftRight, NonUnitalNonAssocSemiring, NonUnitalNonAssocSemiring.mem_center_iff, Set.union_self, Subsemiring, Subsemiring.mem_centralizer_iff, centroid_eq_centralizer_mulLeftRight, mem_center_iff, mem_centralizer_iff, mulRight_eq_mulLeft, union_self
-/
lemma _root_.NonUnitalNonAssocCommSemiring.mem_center_iff (a : α) :
    a in NonUnitalSubsemiring.center α ↔ forall b : α, Commute (L b) (L a) := by
  rw [NonUnitalNonAssocSemiring.mem_center_iff]; rw [CentroidHom.centroid_eq_centralizer_mulLeftRight]; rw [Subsemiring.mem_centralizer_iff]; rw [AddMonoid.End.mulRight_eq_mulLeft]; rw [Set.union_self]
  aesop

end NonUnitalNonAssocCommSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `centerIsoCentroid` / `centerIsoCentroid` 的定义

English:
definition centerIsoCentroid
  signature: : Subsemiring.center α ≃+* CentroidHom α
  body: { centerToCentroid with
    invFun := fun T =>
      ⟨T 1, by constructor <;> simp [commute_iff_eq, ← map_mul_left, ← map_mul_right]⟩
left_inv := fun z => Subtype.ext by simp only [MulHom.toFun_eq_coe,
      NonUnitalRingHom.coe_toMulHom, centerToCentroid_apply, mul_one]
right_inv := fun T => Centro

中文:
定义 centerIsoCentroid
  签名: : Subsemiring.center α ≃+* CentroidHom α
  定义体: { centerToCentroid with
    invFun := fun T =>
      ⟨T 1, by constructor <;> simp [commute_iff_eq, ← map_mul_left, ← map_mul_right]⟩
left_inv := fun z => Subtype.ext by simp only [MulHom.toFun_eq_coe,
      NonUnitalRingHom.coe_toMulHom, centerToCentroid_apply, mul_one]
right_inv := fun T => Centro

Depends on / 依赖: CentroidHom, CentroidHom.ext, MulHom, MulHom.toFun_eq_coe, NonUnitalRingHom, NonUnitalRingHom.coe_toMulHom, Subtype, Subtype.ext, centerToCentroid, centerToCentroid_apply, coe_toMulHom, commute_iff_eq, invFun, left_inv, map_mul_left, map_mul_right, mul_one, one_mul, right_inv, toFun_eq_coe
-/
def centerIsoCentroid : Subsemiring.center α ≃+* CentroidHom α :=
  { centerToCentroid with
    invFun := fun T =>
      ⟨T 1, by constructor <;> simp [commute_iff_eq, ← map_mul_left, ← map_mul_right]⟩
left_inv := fun z => Subtype.ext by simp only [MulHom.toFun_eq_coe,
      NonUnitalRingHom.coe_toMulHom, centerToCentroid_apply, mul_one]
right_inv := fun T => CentroidHom.ext fun _ => by rw [MulHom.toFun_eq_coe,
      NonUnitalRingHom.coe_toMulHom, centerToCentroid_apply, ← map_mul_right, one_mul] }

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (CentroidHom α)
  body: ⟨fun f =>
    { (-f : α ->+ α) with
      map_mul_left' := fun a b => by
        simp [map_mul_left]
      map_mul_right' := fun a b => by
        simp [map_mul_right] }⟩

中文:
实例 :
  签名: Neg (CentroidHom α)
  定义体: ⟨fun f =>
    { (-f : α ->+ α) with
      map_mul_left' := fun a b => by
        simp [map_mul_left]
      map_mul_right' := fun a b => by
        simp [map_mul_right] }⟩

Depends on / 依赖: map_mul_left, map_mul_right
-/
instance : Neg (CentroidHom α) :=
  ⟨fun f =>
    { (-f : α ->+ α) with
      map_mul_left' := fun a b => by
        simp [map_mul_left]
      map_mul_right' := fun a b => by
        simp [map_mul_right] }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (CentroidHom α)
  body: ⟨fun f g =>
    { (f - g : α ->+ α) with
      map_mul_left' := fun a b => by
        simp [map_mul_left, mul_sub]
      map_mul_right' := fun a b => by
        simp [map_mul_right, sub_mul] }⟩

中文:
实例 :
  签名: Sub (CentroidHom α)
  定义体: ⟨fun f g =>
    { (f - g : α ->+ α) with
      map_mul_left' := fun a b => by
        simp [map_mul_left, mul_sub]
      map_mul_right' := fun a b => by
        simp [map_mul_right, sub_mul] }⟩

Depends on / 依赖: map_mul_left, map_mul_right, mul_sub, sub_mul
-/
instance : Sub (CentroidHom α) :=
  ⟨fun f g =>
    { (f - g : α ->+ α) with
      map_mul_left' := fun a b => by
        simp [map_mul_left, mul_sub]
      map_mul_right' := fun a b => by
        simp [map_mul_right, sub_mul] }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast (CentroidHom α)
  body: z • (1 : CentroidHom α)

@[simp, norm_cast]

中文:
实例 :
  签名: 整数Cast (CentroidHom α)
  定义体: z • (1 : CentroidHom α)

@[simp, norm_cast]

Depends on / 依赖: CentroidHom
-/
instance : IntCast (CentroidHom α) where intCast z := z • (1 : CentroidHom α)

@[simp, norm_cast]
/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: (z : Int)
  statement: ⇑(z : CentroidHom α) = z • (CentroidHom.id α)
  proof: rfl

中文:
定理 coe_intCast
  条件: (z : 整数)
  结论: ⇑(z : CentroidHom α) = z • (CentroidHom.id α)
  证明: rfl
-/
theorem coe_intCast (z : Int) : ⇑(z : CentroidHom α) = z • (CentroidHom.id α) :=
  rfl

/--
theorem `intCast_apply` / 定理 `intCast_apply`

English:
theorem intCast_apply
  given: (z : Int) (m : α)
  statement: (z : CentroidHom α) m = z • m
  proof: rfl

@[simp]

中文:
定理 intCast_apply
  条件: (z : 整数) (m : α)
  结论: (z : CentroidHom α) m = z • m
  证明: rfl

@[simp]
-/
theorem intCast_apply (z : Int) (m : α) : (z : CentroidHom α) m = z • m :=
  rfl

@[simp]
/--
theorem `toEnd_neg` / 定理 `toEnd_neg`

English:
theorem toEnd_neg
  given: (x : CentroidHom α)
  statement: (-x).toEnd = -x.toEnd
  proof: rfl

@[simp]

中文:
定理 toEnd_neg
  条件: (x : CentroidHom α)
  结论: (-x).toEnd = -x.toEnd
  证明: rfl

@[simp]
-/
theorem toEnd_neg (x : CentroidHom α) : (-x).toEnd = -x.toEnd :=
  rfl

@[simp]
/--
theorem `toEnd_sub` / 定理 `toEnd_sub`

English:
theorem toEnd_sub
  given: (x y : CentroidHom α)
  statement: (x - y).toEnd = x.toEnd - y.toEnd
  proof: rfl

中文:
定理 toEnd_sub
  条件: (x y : CentroidHom α)
  结论: (x - y).toEnd = x.toEnd - y.toEnd
  证明: rfl
-/
theorem toEnd_sub (x y : CentroidHom α) : (x - y).toEnd = x.toEnd - y.toEnd :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (CentroidHom α)
  body: toEnd_injective.addCommGroup _
    toEnd_zero toEnd_add toEnd_neg toEnd_sub (swap toEnd_smul) (swap toEnd_smul)

@[simp, norm_cast]

中文:
实例 :
  签名: AddCommGroup (CentroidHom α)
  定义体: toEnd_injective.addCommGroup _
    toEnd_zero toEnd_add toEnd_neg toEnd_sub (swap toEnd_smul) (swap toEnd_smul)

@[simp, norm_cast]

Depends on / 依赖: addCommGroup, toEnd_add, toEnd_injective, toEnd_injective.addCommGroup, toEnd_neg, toEnd_smul, toEnd_sub, toEnd_zero
-/
instance : AddCommGroup (CentroidHom α) :=
  toEnd_injective.addCommGroup _
    toEnd_zero toEnd_add toEnd_neg toEnd_sub (swap toEnd_smul) (swap toEnd_smul)

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (f : CentroidHom α)
  statement: ⇑(-f) = -f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_neg
  条件: (f : CentroidHom α)
  结论: ⇑(-f) = -f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_neg (f : CentroidHom α) : ⇑(-f) = -f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (f g : CentroidHom α)
  statement: ⇑(f - g) = f - g
  proof: rfl

@[simp]

中文:
定理 coe_sub
  条件: (f g : CentroidHom α)
  结论: ⇑(f - g) = f - g
  证明: rfl

@[simp]
-/
theorem coe_sub (f g : CentroidHom α) : ⇑(f - g) = f - g :=
  rfl

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (f : CentroidHom α) (a : α)
  statement: (-f) a = -f a
  proof: rfl

@[simp]

中文:
定理 neg_apply
  条件: (f : CentroidHom α) (a : α)
  结论: (-f) a = -f a
  证明: rfl

@[simp]
-/
theorem neg_apply (f : CentroidHom α) (a : α) : (-f) a = -f a :=
  rfl

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (f g : CentroidHom α) (a : α)
  statement: (f - g) a = f a - g a
  proof: rfl

@[simp, norm_cast]

中文:
定理 sub_apply
  条件: (f g : CentroidHom α) (a : α)
  结论: (f - g) a = f a - g a
  证明: rfl

@[simp, norm_cast]
-/
theorem sub_apply (f g : CentroidHom α) (a : α) : (f - g) a = f a - g a :=
  rfl

@[simp, norm_cast]
/--
theorem `toEnd_intCast` / 定理 `toEnd_intCast`

English:
theorem toEnd_intCast
  given: (z : Int)
  statement: (z : CentroidHom α).toEnd = ↑z
  proof: rfl

中文:
定理 toEnd_intCast
  条件: (z : 整数)
  结论: (z : CentroidHom α).toEnd = ↑z
  证明: rfl
-/
theorem toEnd_intCast (z : Int) : (z : CentroidHom α).toEnd = ↑z :=
  rfl

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring (CentroidHom α)
  body: toEnd_injective.ring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_neg toEnd_sub
    toEnd_smul toEnd_smul toEnd_pow toEnd_natCast toEnd_intCast

中文:
实例 instRing
  签名: : Ring (CentroidHom α)
  定义体: toEnd_injective.ring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_neg toEnd_sub
    toEnd_smul toEnd_smul toEnd_pow toEnd_natCast toEnd_intCast

Depends on / 依赖: toEnd_add, toEnd_injective, toEnd_injective.ring, toEnd_intCast, toEnd_mul, toEnd_natCast, toEnd_neg, toEnd_one, toEnd_pow, toEnd_smul, toEnd_sub, toEnd_zero
-/
instance instRing : Ring (CentroidHom α) :=
  toEnd_injective.ring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_neg toEnd_sub
    toEnd_smul toEnd_smul toEnd_pow toEnd_natCast toEnd_intCast

end NonUnitalNonAssocRing

section NonUnitalRing

variable [NonUnitalRing α]

-- See note [reducible non-instances]
/--
Definition of `commRing` / `commRing` 的定义

English:
abbreviation commRing
  body: { CentroidHom.instRing with
    mul_comm := fun f g => by
      ext
      refine sub_eq_zero.1 (or_self_iff.1 <| (h _ _) fun r => ?_)
      rw [mul_assoc]; rw [sub_mul]; rw [sub_eq_zero]; rw [← map_mul_right]; rw [← map_mul_right]; rw [coe_mul]; rw [coe_mul]; rw [comp_mul_comm] }

中文:
缩写 commRing
  定义体: { CentroidHom.instRing with
    mul_comm := fun f g => by
      ext
      refine sub_eq_zero.1 (or_self_iff.1 <| (h _ _) fun r => ?_)
      rw [mul_assoc]; rw [sub_mul]; rw [sub_eq_zero]; rw [← map_mul_right]; rw [← map_mul_right]; rw [coe_mul]; rw [coe_mul]; rw [comp_mul_comm] }

Depends on / 依赖: CentroidHom, CentroidHom.instRing, coe_mul, comp_mul_comm, instRing, map_mul_right, mul_assoc, mul_comm, or_self_iff, sub_eq_zero, sub_mul
-/
abbrev commRing
    (h : forall a b : α, (forall r : α, a * r * b = 0) -> a = 0 ∨ b = 0) : CommRing (CentroidHom α) :=
  { CentroidHom.instRing with
    mul_comm := fun f g => by
      ext
      refine sub_eq_zero.1 (or_self_iff.1 <| (h _ _) fun r => ?_)
      rw [mul_assoc]; rw [sub_mul]; rw [sub_eq_zero]; rw [← map_mul_right]; rw [← map_mul_right]; rw [coe_mul]; rw [coe_mul]; rw [comp_mul_comm] }

end NonUnitalRing

end CentroidHom
