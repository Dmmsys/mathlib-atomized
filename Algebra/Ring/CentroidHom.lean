/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christopher Hoskin
-/
module

public import Mathlib.Algebra.Algebra.Defs  -- shake: keep (`example` dependency)
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

/-- The type of centroid homomorphisms from `α` to `α`. -/
/-
**CentroidHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → [NonUnitalNonAssocSemiring α] → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of centroid homomorphisms from `α` to `α`.
-/
structure CentroidHom (α : Type*) [NonUnitalNonAssocSemiring α] extends α →+ α where
  /-- Commutativity of centroid homomorphisms with left multiplication. -/
  map_mul_left' (a b : α) : toFun (a * b) = a * toFun b
  /-- Commutativity of centroid homomorphisms with right multiplication. -/
  map_mul_right' (a b : α) : toFun (a * b) = toFun a * b

attribute [nolint docBlame] CentroidHom.toAddMonoidHom

/-- `CentroidHomClass F α` states that `F` is a type of centroid homomorphisms.

You should extend this class when you extend `CentroidHom`. -/
/-
**CentroidHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : outParam (Type u_7)) → [NonUnitalNonAssocSemiring α]
 → [FunLike F α α] → Prop
参数：Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CentroidHomClass F α` states that `F` is a type of centroid homomorphisms.

You should extend this class when you extend `CentroidHom`.
-/
class CentroidHomClass (F : Type*) (α : outParam Type*)
    [NonUnitalNonAssocSemiring α] [FunLike F α α] : Prop extends AddMonoidHomClass F α α where
  /-- Commutativity of centroid homomorphisms with left multiplication. -/
  map_mul_left (f : F) (a b : α) : f (a * b) = a * f b
  /-- Commutativity of centroid homomorphisms with right multiplication. -/
  map_mul_right (f : F) (a b : α) : f (a * b) = f a * b


export CentroidHomClass (map_mul_left map_mul_right)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring α] [FunLike F α α] [CentroidHomClass F α] :
    CoeTC F (CentroidHom α) :=
  ⟨fun f ↦
    { (f : α →+ α) with
      toFun := f
      map_mul_left' := map_mul_left f
      map_mul_right' := map_mul_right f }⟩

/-! ### Centroid homomorphisms -/

namespace CentroidHom

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (CentroidHom α) α α where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CentroidHomClass (CentroidHom α) α where
  map_zero f := f.map_zero'
  map_add f := f.map_add'
  map_mul_left f := f.map_mul_left'
  map_mul_right f := f.map_mul_right'
/-
**CentroidHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toFun_eq_coe {f : CentroidHom α} : f.toFun = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : CentroidHom α} : f.toFun = f := rfl

@[ext]
/-
**CentroidHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：ext {f g : CentroidHom α} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : CentroidHom α} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[simp, norm_cast]
/-
**CentroidHom.coe_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_toAddMonoidHom (f : CentroidHom α) : ⇑(f : α ->+ α) = f
参数：f : CentroidHom α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CentroidHomClass.toAddMonoidHomClass`：∀ {F : Type u_6} {α : outParam (Ty
pe u_7)} {inst : NonUnitalNonAssocSemiring α} {inst_1 : FunLike F α α}   [self :
 CentroidHomClass F α], Ad…
· 使用定理 `CentroidHom.instCentroidHomClass`：∀ {α : Type u_5} [inst : NonUnitalNonA
ssocSemiring α], CentroidHomClass (CentroidHom α) α
-/
theorem coe_toAddMonoidHom (f : CentroidHom α) : ⇑(f : α →+ α) = f :=
  rfl

@[simp]
/-
**CentroidHom.toAddMonoidHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toAddMonoidHom_eq_coe (f : CentroidHom α) : f.toAddMonoidHom = f
参数：f : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddMonoidHom_eq_coe (f : CentroidHom α) : f.toAddMonoidHom = f :=
  rfl
/-
**CentroidHom.coe_toAddMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHo
m`。
形式化陈述：coe_toAddMonoidHom_injective : Injective ((↑) : CentroidHom α -> α ->+ α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CentroidHomClass.toAddMonoidHomClass`：∀ {F : Type u_6} {α : outParam (Ty
pe u_7)} {inst : NonUnitalNonAssocSemiring α} {inst_1 : FunLike F α α}   [self :
 CentroidHomClass F α], Ad…
· 使用定理 `CentroidHom.instCentroidHomClass`：∀ {α : Type u_5} [inst : NonUnitalNonA
ssocSemiring α], CentroidHomClass (CentroidHom α) α
· 使用定理 `CentroidHom.ext`：ext {f g : CentroidHom α} (h : forall a, f a = g a) : f
 = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem coe_toAddMonoidHom_injective : Injective ((↑) : CentroidHom α → α →+ α) :=
  fun _f _g h => ext fun a ↦
    haveI := DFunLike.congr_fun h a
    this

/-- Turn a centroid homomorphism into an additive monoid endomorphism. -/
/-
**CentroidHom.toEnd** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：toEnd (f : CentroidHom α) : AddMonoid.End α
参数：f : CentroidHom α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a centroid homomorphism into an additive monoid endomorphism.
-/
def toEnd (f : CentroidHom α) : AddMonoid.End α :=
  (f : α →+ α)
/-
**CentroidHom.toEnd_injective** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toEnd_injective : Injective (CentroidHom.toEnd : CentroidHom α -> AddMonoi
d.End α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CentroidHom.coe_toAddMonoidHom_injective`：coe_toAddMonoidHom_injective :
 Injective ((↑) : CentroidHom α -> α ->+ α)
-/
theorem toEnd_injective : Injective (CentroidHom.toEnd : CentroidHom α → AddMonoid.End α) :=
  coe_toAddMonoidHom_injective

/-- Copy of a `CentroidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**CentroidHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：{α : Type u_5} → [inst : NonUnitalNonAssocSemiring α] → (f : CentroidHom α
) → (f' : α → α) → f' = ⇑f → CentroidHom α
参数：f : CentroidHom α；f' : α → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `CentroidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities.
-/
protected def copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : CentroidHom α :=
  { f.toAddMonoidHom.copy f' <| h with
    toFun := f'
    map_mul_left' := fun a b ↦ by simp_rw [h, map_mul_left]
    map_mul_right' := fun a b ↦ by simp_rw [h, map_mul_right] }

@[simp]
/-
**CentroidHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_copy (f : CentroidHom α) (f' : α -> α) (h : f' = f) : ⇑(f.copy f' h) =
 f'
参数：f : CentroidHom α；f' : α -> α；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**CentroidHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：copy_eq (f : CentroidHom α) (f' : α -> α) (h : f' = f) : f.copy f' h = f
参数：f : CentroidHom α；f' : α -> α；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : CentroidHom α) (f' : α → α) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `CentroidHom`. -/
/-
**CentroidHom.id** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：(α : Type u_5) → [inst : NonUnitalNonAssocSemiring α] → CentroidHom α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `CentroidHom`.
-/
protected def id : CentroidHom α :=
  { AddMonoidHom.id α with
    map_mul_left' := fun _ _ ↦ rfl
    map_mul_right' := fun _ _ ↦ rfl }
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CentroidHom α) :=
  ⟨CentroidHom.id α⟩

@[simp, norm_cast]
/-
**CentroidHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_id : ⇑(CentroidHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(CentroidHom.id α) = id :=
  rfl

@[simp, norm_cast]
/-
**CentroidHom.toAddMonoidHom_id** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toAddMonoidHom_id : (CentroidHom.id α : α ->+ α) = AddMonoidHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CentroidHomClass.toAddMonoidHomClass`：∀ {F : Type u_6} {α : outParam (Ty
pe u_7)} {inst : NonUnitalNonAssocSemiring α} {inst_1 : FunLike F α α}   [self :
 CentroidHomClass F α], Ad…
· 使用定理 `CentroidHom.instCentroidHomClass`：∀ {α : Type u_5} [inst : NonUnitalNonA
ssocSemiring α], CentroidHomClass (CentroidHom α) α
-/
theorem toAddMonoidHom_id : (CentroidHom.id α : α →+ α) = AddMonoidHom.id α :=
  rfl

variable {α}

@[simp]
/-
**CentroidHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：id_apply (a : α) : CentroidHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : CentroidHom.id α a = a :=
  rfl

/-- Composition of `CentroidHom`s as a `CentroidHom`. -/
/-
**CentroidHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：comp (g f : CentroidHom α) : CentroidHom α
参数：g f : CentroidHom α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `CentroidHom`s as a `CentroidHom`.
-/
def comp (g f : CentroidHom α) : CentroidHom α :=
  { g.toAddMonoidHom.comp f.toAddMonoidHom with
    map_mul_left' := fun _a _b ↦ (congr_arg g <| f.map_mul_left' _ _).trans <| g.map_mul_left' _ _
    map_mul_right' := fun _a _b ↦
      (congr_arg g <| f.map_mul_right' _ _).trans <| g.map_mul_right' _ _ }

@[simp, norm_cast]
/-
**CentroidHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_comp (g f : CentroidHom α) : ⇑(g.comp f) = g ∘ f
参数：g f : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (g f : CentroidHom α) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
/-
**CentroidHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：comp_apply (g f : CentroidHom α) (a : α) : g.comp f a = g (f a)
参数：g f : CentroidHom α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g f : CentroidHom α) (a : α) : g.comp f a = g (f a) :=
  rfl

@[simp, norm_cast]
/-
**CentroidHom.coe_comp_addMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_comp_addMonoidHom (g f : CentroidHom α) : (g.comp f : α ->+ α) = (g : 
α ->+ α).comp f
参数：g f : CentroidHom α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CentroidHomClass.toAddMonoidHomClass`：∀ {F : Type u_6} {α : outParam (Ty
pe u_7)} {inst : NonUnitalNonAssocSemiring α} {inst_1 : FunLike F α α}   [self :
 CentroidHomClass F α], Ad…
· 使用定理 `CentroidHom.instCentroidHomClass`：∀ {α : Type u_5} [inst : NonUnitalNonA
ssocSemiring α], CentroidHomClass (CentroidHom α) α
-/
theorem coe_comp_addMonoidHom (g f : CentroidHom α) : (g.comp f : α →+ α) = (g : α →+ α).comp f :=
  rfl

@[simp]
/-
**CentroidHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：comp_assoc (h g f : CentroidHom α) : (h.comp g).comp f = h.comp (g.comp f)
参数：h g f : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (h g f : CentroidHom α) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/-
**CentroidHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：comp_id (f : CentroidHom α) : f.comp (CentroidHom.id α) = f
参数：f : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id (f : CentroidHom α) : f.comp (CentroidHom.id α) = f :=
  rfl

@[simp]
/-
**CentroidHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：id_comp (f : CentroidHom α) : (CentroidHom.id α).comp f = f
参数：f : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp (f : CentroidHom α) : (CentroidHom.id α).comp f = f :=
  rfl

@[simp]
/-
**CentroidHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：cancel_right {g₁ g₂ f : CentroidHom α} (hf : Surjective f) : g₁.comp f = g
₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CentroidHom.ext`：ext {f g : CentroidHom α} (h : forall a, f a = g a) : f
 = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem cancel_right {g₁ g₂ f : CentroidHom α} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h ↦ ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun a ↦ congrFun (congrArg comp a) f⟩

@[simp]
/-
**CentroidHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：cancel_left {g f₁ f₂ : CentroidHom α} (hg : Injective g) : g.comp f₁ = g.c
omp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CentroidHom.ext`：ext {f g : CentroidHom α} (h : forall a, f a = g a) : f
 = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CentroidHom.comp_apply`：comp_apply (g f : CentroidHom α) (a : α) : g.com
p f a = g (f a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g f₁ f₂ : CentroidHom α} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h ↦ ext fun a ↦ hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (CentroidHom α) :=
  ⟨{ (0 : α →+ α) with
      map_mul_left' := fun _a _b ↦ (mul_zero _).symm
      map_mul_right' := fun _a _b ↦ (zero_mul _).symm }⟩
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (CentroidHom α) :=
  ⟨CentroidHom.id α⟩
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (CentroidHom α) :=
  ⟨fun f g ↦
    { (f + g : α →+ α) with
      map_mul_left' := fun a b ↦ by
        simp [map_mul_left, mul_add]
      map_mul_right' := fun a b ↦ by
        simp [map_mul_right, add_mul] }⟩
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (CentroidHom α) :=
  ⟨comp⟩

variable [Monoid M] [Monoid N] [Semiring R]
variable [DistribMulAction M α] [SMulCommClass M α α] [IsScalarTower M α α]
variable [DistribMulAction N α] [SMulCommClass N α α] [IsScalarTower N α α]
variable [Module R α] [SMulCommClass R α α] [IsScalarTower R α α]
/-
**CentroidHom.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
形式化陈述：instSMul : SMul M (CentroidHom α) where smul n f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul M (CentroidHom α) where
  smul n f :=
    { (n • f : α →+ α) with
      map_mul_left' := fun a b ↦ by
        change n • f (a * b) = a * n • f b
        rw [map_mul_left f, ← mul_smul_comm]
      map_mul_right' := fun a b ↦ by
        change n • f (a * b) = n • f a * b
        rw [map_mul_right f, ← smul_mul_assoc] }
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M N] [IsScalarTower M N α] : IsScalarTower M N (CentroidHom α) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass M N α] : SMulCommClass M N (CentroidHom α) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribMulAction Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (CentroidHom α) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _
/-
**CentroidHom.isScalarTowerRight** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
形式化陈述：isScalarTowerRight : IsScalarTower M (CentroidHom α) (CentroidHom α) where
 smul_assoc _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isScalarTowerRight : IsScalarTower M (CentroidHom α) (CentroidHom α) where
  smul_assoc _ _ _ := rfl
/-
**CentroidHom.hasNPowNat** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
形式化陈述：hasNPowNat : Pow (CentroidHom α) Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasNPowNat : Pow (CentroidHom α) ℕ :=
  ⟨fun f n ↦
    { toAddMonoidHom := (f.toEnd ^ n : AddMonoid.End α)
      map_mul_left' := fun a b ↦ by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ']
          exact (congr_arg f.toEnd ih).trans (f.map_mul_left' _ _)
      map_mul_right' := fun a b ↦ by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ']
          exact (congr_arg f.toEnd ih).trans (f.map_mul_right' _ _)}⟩

@[simp, norm_cast]
/-
**CentroidHom.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_zero : ⇑(0 : CentroidHom α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : CentroidHom α) = 0 :=
  rfl

@[simp, norm_cast]
/-
**CentroidHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_one : ⇑(1 : CentroidHom α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : CentroidHom α) = id :=
  rfl

@[simp, norm_cast]
/-
**CentroidHom.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_add (f g : CentroidHom α) : ⇑(f + g) = f + g
参数：f g : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (f g : CentroidHom α) : ⇑(f + g) = f + g :=
  rfl

@[simp, norm_cast]
/-
**CentroidHom.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_mul (f g : CentroidHom α) : ⇑(f * g) = f ∘ g
参数：f g : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g : CentroidHom α) : ⇑(f * g) = f ∘ g :=
  rfl

@[simp, norm_cast]
/-
**CentroidHom.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_smul (n : M) (f : CentroidHom α) : ⇑(n • f) = n • ⇑f
参数：n : M；f : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (n : M) (f : CentroidHom α) : ⇑(n • f) = n • ⇑f :=
  rfl

@[simp]
/-
**CentroidHom.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：zero_apply (a : α) : (0 : CentroidHom α) a = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (a : α) : (0 : CentroidHom α) a = 0 :=
  rfl

@[simp]
/-
**CentroidHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：one_apply (a : α) : (1 : CentroidHom α) a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (a : α) : (1 : CentroidHom α) a = a :=
  rfl

@[simp]
/-
**CentroidHom.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：add_apply (f g : CentroidHom α) (a : α) : (f + g) a = f a + g a
参数：f g : CentroidHom α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (f g : CentroidHom α) (a : α) : (f + g) a = f a + g a :=
  rfl

@[simp]
/-
**CentroidHom.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：mul_apply (f g : CentroidHom α) (a : α) : (f * g) a = f (g a)
参数：f g : CentroidHom α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (f g : CentroidHom α) (a : α) : (f * g) a = f (g a) :=
  rfl

@[simp]
/-
**CentroidHom.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：smul_apply (n : M) (f : CentroidHom α) (a : α) : (n • f) a = n • f a
参数：n : M；f : CentroidHom α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (n : M) (f : CentroidHom α) (a : α) : (n • f) a = n • f a :=
  rfl
/-
**CentroidHom.** 是 Mathlib 中的一个示例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : SMul ℕ (CentroidHom α) := instSMul

@[simp]
/-
**CentroidHom.toEnd_zero** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toEnd_zero : (0 : CentroidHom α).toEnd = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_zero : (0 : CentroidHom α).toEnd = 0 :=
  rfl

@[simp]
/-
**CentroidHom.toEnd_add** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toEnd_add (x y : CentroidHom α) : (x + y).toEnd = x.toEnd + y.toEnd
参数：x y : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_add (x y : CentroidHom α) : (x + y).toEnd = x.toEnd + y.toEnd :=
  rfl
/-
**CentroidHom.toEnd_smul** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toEnd_smul (m : M) (x : CentroidHom α) : (m • x).toEnd = m • x.toEnd
参数：m : M；x : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_smul (m : M) (x : CentroidHom α) : (m • x).toEnd = m • x.toEnd :=
  rfl
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (CentroidHom α) :=
  coe_toAddMonoidHom_injective.addCommMonoid _ toEnd_zero toEnd_add (swap toEnd_smul)
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (CentroidHom α) where natCast n := n • (1 : CentroidHom α)

@[simp, norm_cast]
/-
**CentroidHom.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_natCast (n : Nat) : ⇑(n : CentroidHom α) = n • (CentroidHom.id α)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natCast (n : ℕ) : ⇑(n : CentroidHom α) = n • (CentroidHom.id α) :=
  rfl
/-
**CentroidHom.natCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：natCast_apply (n : Nat) (m : α) : (n : CentroidHom α) m = n • m
参数：n : Nat；m : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_apply (n : ℕ) (m : α) : (n : CentroidHom α) m = n • m :=
  rfl

@[simp]
/-
**CentroidHom.toEnd_one** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toEnd_one : (1 : CentroidHom α).toEnd = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_one : (1 : CentroidHom α).toEnd = 1 :=
  rfl

@[simp]
/-
**CentroidHom.toEnd_mul** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toEnd_mul (x y : CentroidHom α) : (x * y).toEnd = x.toEnd * y.toEnd
参数：x y : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_mul (x y : CentroidHom α) : (x * y).toEnd = x.toEnd * y.toEnd :=
  rfl

@[simp]
/-
**CentroidHom.toEnd_pow** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toEnd_pow (x : CentroidHom α) (n : Nat) : (x ^ n).toEnd = x.toEnd ^ n
参数：x : CentroidHom α；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_pow (x : CentroidHom α) (n : ℕ) : (x ^ n).toEnd = x.toEnd ^ n :=
  rfl

@[simp, norm_cast]
/-
**CentroidHom.toEnd_natCast** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toEnd_natCast (n : Nat) : (n : CentroidHom α).toEnd = ↑n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_natCast (n : ℕ) : (n : CentroidHom α).toEnd = ↑n :=
  rfl

-- cf `add_monoid.End.semiring`
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semiring (CentroidHom α) :=
  toEnd_injective.semiring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_smul toEnd_pow
    toEnd_natCast

variable (α) in
/-- `CentroidHom.toEnd` as a `RingHom`. -/
@[simps]
/-
**CentroidHom.toEndRingHom** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：toEndRingHom : CentroidHom α ->+* AddMonoid.End α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CentroidHom.toEnd_one`：toEnd_one : (1 : CentroidHom α).toEnd = 1
· 使用定理 `CentroidHom.toEnd_mul`：toEnd_mul (x y : CentroidHom α) : (x * y).toEnd =
 x.toEnd * y.toEnd
· 使用定理 `CentroidHom.toEnd_zero`：toEnd_zero : (0 : CentroidHom α).toEnd = 0
· 使用定理 `CentroidHom.toEnd_add`：toEnd_add (x y : CentroidHom α) : (x + y).toEnd =
 x.toEnd + y.toEnd

--- 原说明 ---
`CentroidHom.toEnd` as a `RingHom`.
-/
def toEndRingHom : CentroidHom α →+* AddMonoid.End α where
  toFun := toEnd
  map_zero' := toEnd_zero
  map_one' := toEnd_one
  map_add' := toEnd_add
  map_mul' := toEnd_mul
/-
**CentroidHom.comp_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：comp_mul_comm (T S : CentroidHom α) (a b : α) : (T ∘ S) (a * b) = (S ∘ T) 
(a * b)
参数：T S : CentroidHom α；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CentroidHomClass.map_mul_right`：∀ {F : Type u_6} {α : outParam (Type u_7
)} {inst : NonUnitalNonAssocSemiring α} {inst_1 : FunLike F α α}   [self : Centr
oidHomClass F α] (f …
· 使用定理 `CentroidHom.instCentroidHomClass`：∀ {α : Type u_5} [inst : NonUnitalNonA
ssocSemiring α], CentroidHomClass (CentroidHom α) α
· 使用定理 `CentroidHomClass.map_mul_left`：∀ {F : Type u_6} {α : outParam (Type u_7)
} {inst : NonUnitalNonAssocSemiring α} {inst_1 : FunLike F α α}   [self : Centro
idHomClass F α] (f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem comp_mul_comm (T S : CentroidHom α) (a b : α) : (T ∘ S) (a * b) = (S ∘ T) (a * b) := by
  simp only [Function.comp_apply]
  rw [map_mul_right, map_mul_left, ← map_mul_right, ← map_mul_left]
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction M (CentroidHom α) :=
  toEnd_injective.distribMulAction (toEndRingHom α).toAddMonoidHom toEnd_smul
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (CentroidHom α) :=
  toEnd_injective.module R (toEndRingHom α).toAddMonoidHom toEnd_smul

/-!
The following instances show that `α` is a non-unital and non-associative algebra over
`CentroidHom α`.
-/

/-- The tautological action by `CentroidHom α` on `α`.

This generalizes `Function.End.applyMulAction`. -/
/-
**CentroidHom.applyModule** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
形式化陈述：applyModule : Module (CentroidHom α) α where smul T a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `CentroidHom α` on `α`.

This generalizes `Function.End.applyMulAction`.
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
/-
**CentroidHom.smul_def** 是 Mathlib 中的一个引理，位于命名空间 `CentroidHom`。
形式化陈述：smul_def (T : CentroidHom α) (a : α) : T • a = T a
参数：T : CentroidHom α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_def (T : CentroidHom α) (a : α) : T • a = T a := rfl
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass (CentroidHom α) α α where
  smul_comm _ _ _ := map_mul_left _ _ _
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass α (CentroidHom α) α := SMulCommClass.symm _ _ _
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CentroidHom._root_.Module.toCentroidHom** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural ring homomorphism from `R` into `CentroidHom α`.

This is a stronger version of `Module.toAddMonoidEnd`.
-/
def _root_.Module.toCentroidHom : R →+* CentroidHom α := RingHom.smulOneHom

open Module in
/-- `CentroidHom α` as an algebra over `R`. -/
/-
**CentroidHom.** 是 Mathlib 中的一个示例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CentroidHom α` as an algebra over `R`.
-/
example (h : ∀ (r : R) (T : CentroidHom α), toCentroidHom r * T = T * toCentroidHom r) :
    Algebra R (CentroidHom α) := toCentroidHom.toAlgebra' h

local notation "L" => AddMonoid.End.mulLeft
local notation "R" => AddMonoid.End.mulRight
/-
**CentroidHom.centroid_eq_centralizer_mulLeftRight** 是 Mathlib 中的一个引理，位于命名空间 `Ce
ntroidHom`。
形式化陈述：centroid_eq_centralizer_mulLeftRight : RingHom.rangeS (toEndRingHom α) = S
ubsemiring.centralizer (Set.range L union Set.range R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.ext`：ext {S T : Subsemiring R} (h : forall x, x in S ↔ x in 
T) : S = T
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CentroidHomClass.map_mul_left`：∀ {F : Type u_6} {α : outParam (Type u_7)
} {inst : NonUnitalNonAssocSemiring α} {inst_1 : FunLike F α α}   [self : Centro
idHomClass F α] (f …
· 使用定理 `CentroidHom.instCentroidHomClass`：∀ {α : Type u_5} [inst : NonUnitalNonA
ssocSemiring α], CentroidHomClass (CentroidHom α) α
· 使用定理 `CentroidHomClass.map_mul_right`：∀ {F : Type u_6} {α : outParam (Type u_7
)} {inst : NonUnitalNonAssocSemiring α} {inst_1 : FunLike F α α}   [self : Centr
oidHomClass F α] (f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemiring.mem_centralizer_iff`：mem_centralizer_iff {R} [Semiring R] {s
 : Set R} {z : R} : z in centralizer s ↔ forall g in s, g * z = z * g
-/
lemma centroid_eq_centralizer_mulLeftRight :
    RingHom.rangeS (toEndRingHom α) = Subsemiring.centralizer (Set.range L ∪ Set.range R) := by
  ext T
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨f, rfl⟩ S (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact AddMonoidHom.ext fun b ↦ (map_mul_left f a b).symm
    · exact AddMonoidHom.ext fun a ↦ (map_mul_right f a b).symm
  · rw [Subsemiring.mem_centralizer_iff] at h
    refine ⟨⟨T, fun a b ↦ ?_, fun a b ↦ ?_⟩, rfl⟩
    · exact congr($(h (L a) (.inl ⟨a, rfl⟩)) b).symm
    · exact congr($(h (R b) (.inr ⟨b, rfl⟩)) a).symm

/-- The canonical homomorphism from the center into the center of the centroid -/
/-
**CentroidHom.centerToCentroidCenter** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：centerToCentroidCenter : NonUnitalSubsemiring.center α ->ₙ+* Subsemiring.c
enter (CentroidHom α) where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical homomorphism from the center into the center of the centroid
-/
def centerToCentroidCenter :
    NonUnitalSubsemiring.center α →ₙ+* Subsemiring.center (CentroidHom α) where
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
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (Subsemiring.center (CentroidHom α)) α α where
  coe f := f.val.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr with x
    exact congrFun h x
/-
**CentroidHom.centerToCentroidCenter_apply** 是 Mathlib 中的一个引理，位于命名空间 `CentroidHo
m`。
形式化陈述：centerToCentroidCenter_apply (z : NonUnitalSubsemiring.center α) (a : α) :
 (centerToCentroidCenter z) a = z * a
参数：z : NonUnitalSubsemiring.center α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma centerToCentroidCenter_apply (z : NonUnitalSubsemiring.center α) (a : α) :
    (centerToCentroidCenter z) a = z * a := rfl

/-- The canonical homomorphism from the center into the centroid -/
/-
**CentroidHom.centerToCentroid** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：centerToCentroid : NonUnitalSubsemiring.center α ->ₙ+* CentroidHom α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical homomorphism from the center into the centroid
-/
def centerToCentroid : NonUnitalSubsemiring.center α →ₙ+* CentroidHom α :=
  NonUnitalRingHom.comp
    (SubsemiringClass.subtype (Subsemiring.center (CentroidHom α))).toNonUnitalRingHom
    centerToCentroidCenter
/-
**CentroidHom.centerToCentroid_apply** 是 Mathlib 中的一个引理，位于命名空间 `CentroidHom`。
形式化陈述：centerToCentroid_apply (z : NonUnitalSubsemiring.center α) (a : α) : (cent
erToCentroid z) a = z * a
参数：z : NonUnitalSubsemiring.center α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma centerToCentroid_apply (z : NonUnitalSubsemiring.center α) (a : α) :
    (centerToCentroid z) a = z * a := rfl
/-
**CentroidHom._root_.NonUnitalNonAssocSemiring.mem_center_iff** 是 Mathlib 中的一个引理
，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NonUnitalNonAssocSemiring.mem_center_iff (a : α) :
    a ∈ NonUnitalSubsemiring.center α ↔ R a = L a ∧ (L a) ∈ RingHom.rangeS (toEndRingHom α) := by
  constructor
  · exact fun ha ↦ ⟨AddMonoidHom.ext <| fun _ => (IsMulCentral.comm ha _).symm,
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

/-
**CentroidHom._root_.NonUnitalNonAssocCommSemiring.mem_center_iff** 是 Mathlib 中的
一个引理，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NonUnitalNonAssocCommSemiring.mem_center_iff (a : α) :
    a ∈ NonUnitalSubsemiring.center α ↔ ∀ b : α, Commute (L b) (L a) := by
  rw [NonUnitalNonAssocSemiring.mem_center_iff, CentroidHom.centroid_eq_centralizer_mulLeftRight,
    Subsemiring.mem_centralizer_iff, AddMonoid.End.mulRight_eq_mulLeft, Set.union_self]
  aesop

end NonUnitalNonAssocCommSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism from the center of a (non-associative) semiring onto its centroid. -/
/-
**CentroidHom.centerIsoCentroid** 是 Mathlib 中的一个定义，位于命名空间 `CentroidHom`。
形式化陈述：centerIsoCentroid : Subsemiring.center α ≃+* CentroidHom α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism from the center of a (non-associative) semiring onto i
ts centroid.
-/
def centerIsoCentroid : Subsemiring.center α ≃+* CentroidHom α :=
  { centerToCentroid with
    invFun := fun T ↦
      ⟨T 1, by constructor <;> simp [commute_iff_eq, ← map_mul_left, ← map_mul_right]⟩
    left_inv := fun z ↦ Subtype.ext <| by simp only [MulHom.toFun_eq_coe,
      NonUnitalRingHom.coe_toMulHom, centerToCentroid_apply, mul_one]
    right_inv := fun T ↦ CentroidHom.ext <| fun _ => by rw [MulHom.toFun_eq_coe,
      NonUnitalRingHom.coe_toMulHom, centerToCentroid_apply, ← map_mul_right, one_mul] }

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/-- Negation of `CentroidHom`s as a `CentroidHom`. -/
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negation of `CentroidHom`s as a `CentroidHom`.
-/
instance : Neg (CentroidHom α) :=
  ⟨fun f ↦
    { (-f : α →+ α) with
      map_mul_left' := fun a b ↦ by
        simp [map_mul_left]
      map_mul_right' := fun a b ↦ by
        simp [map_mul_right] }⟩
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (CentroidHom α) :=
  ⟨fun f g ↦
    { (f - g : α →+ α) with
      map_mul_left' := fun a b ↦ by
        simp [map_mul_left, mul_sub]
      map_mul_right' := fun a b ↦ by
        simp [map_mul_right, sub_mul] }⟩
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast (CentroidHom α) where intCast z := z • (1 : CentroidHom α)

@[simp, norm_cast]
/-
**CentroidHom.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_intCast (z : Int) : ⇑(z : CentroidHom α) = z • (CentroidHom.id α)
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_intCast (z : ℤ) : ⇑(z : CentroidHom α) = z • (CentroidHom.id α) :=
  rfl
/-
**CentroidHom.intCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：intCast_apply (z : Int) (m : α) : (z : CentroidHom α) m = z • m
参数：z : Int；m : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intCast_apply (z : ℤ) (m : α) : (z : CentroidHom α) m = z • m :=
  rfl

@[simp]
/-
**CentroidHom.toEnd_neg** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toEnd_neg (x : CentroidHom α) : (-x).toEnd = -x.toEnd
参数：x : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_neg (x : CentroidHom α) : (-x).toEnd = -x.toEnd :=
  rfl

@[simp]
/-
**CentroidHom.toEnd_sub** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toEnd_sub (x y : CentroidHom α) : (x - y).toEnd = x.toEnd - y.toEnd
参数：x y : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_sub (x y : CentroidHom α) : (x - y).toEnd = x.toEnd - y.toEnd :=
  rfl
/-
**CentroidHom.** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (CentroidHom α) :=
  toEnd_injective.addCommGroup _
    toEnd_zero toEnd_add toEnd_neg toEnd_sub (swap toEnd_smul) (swap toEnd_smul)

@[simp, norm_cast]
/-
**CentroidHom.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_neg (f : CentroidHom α) : ⇑(-f) = -f
参数：f : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (f : CentroidHom α) : ⇑(-f) = -f :=
  rfl

@[simp, norm_cast]
/-
**CentroidHom.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：coe_sub (f g : CentroidHom α) : ⇑(f - g) = f - g
参数：f g : CentroidHom α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (f g : CentroidHom α) : ⇑(f - g) = f - g :=
  rfl

@[simp]
/-
**CentroidHom.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：neg_apply (f : CentroidHom α) (a : α) : (-f) a = -f a
参数：f : CentroidHom α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply (f : CentroidHom α) (a : α) : (-f) a = -f a :=
  rfl

@[simp]
/-
**CentroidHom.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：sub_apply (f g : CentroidHom α) (a : α) : (f - g) a = f a - g a
参数：f g : CentroidHom α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (f g : CentroidHom α) (a : α) : (f - g) a = f a - g a :=
  rfl

@[simp, norm_cast]
/-
**CentroidHom.toEnd_intCast** 是 Mathlib 中的一个定理，位于命名空间 `CentroidHom`。
形式化陈述：toEnd_intCast (z : Int) : (z : CentroidHom α).toEnd = ↑z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_intCast (z : ℤ) : (z : CentroidHom α).toEnd = ↑z :=
  rfl
/-
**CentroidHom.instRing** 是 Mathlib 中的一个实例，位于命名空间 `CentroidHom`。
形式化陈述：instRing : Ring (CentroidHom α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CentroidHom.toEnd_neg`：toEnd_neg (x : CentroidHom α) : (-x).toEnd = -x.t
oEnd
· 使用定理 `CentroidHom.toEnd_sub`：toEnd_sub (x y : CentroidHom α) : (x - y).toEnd =
 x.toEnd - y.toEnd
· 使用定理 `CentroidHom.toEnd_intCast`：toEnd_intCast (z : Int) : (z : CentroidHom α)
.toEnd = ↑z
-/
instance instRing : Ring (CentroidHom α) :=
  toEnd_injective.ring _ toEnd_zero toEnd_one toEnd_add toEnd_mul toEnd_neg toEnd_sub
    toEnd_smul toEnd_smul toEnd_pow toEnd_natCast toEnd_intCast

end NonUnitalNonAssocRing

section NonUnitalRing

variable [NonUnitalRing α]

-- See note [reducible non-instances]
/-- A prime associative ring has commutative centroid. -/
/-
**CentroidHom.commRing** 是 Mathlib 中的一个缩写定义，位于命名空间 `CentroidHom`。
形式化陈述：commRing (h : forall a b : α, (forall r : α, a * r * b = 0) -> a = 0 ∨ b =
 0) : CommRing (CentroidHom α)
参数：h : forall a b : α, (forall r : α, a * r * b = 0) -> a = 0 ∨ b = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prime associative ring has commutative centroid.
-/
abbrev commRing
    (h : ∀ a b : α, (∀ r : α, a * r * b = 0) → a = 0 ∨ b = 0) : CommRing (CentroidHom α) :=
  { CentroidHom.instRing with
    mul_comm := fun f g ↦ by
      ext
      refine sub_eq_zero.1 (or_self_iff.1 <| (h _ _) fun r ↦ ?_)
      rw [mul_assoc, sub_mul, sub_eq_zero, ← map_mul_right, ← map_mul_right, coe_mul, coe_mul,
        comp_mul_comm] }

end NonUnitalRing

end CentroidHom

