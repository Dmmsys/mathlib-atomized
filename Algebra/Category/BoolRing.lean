/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Order.Category.BoolAlg

/-!
# The category of Boolean rings

This file defines `BoolRing`, the category of Boolean rings.

## TODO

Finish the equivalence with `BoolAlg`.
-/

@[expose] public section


universe u

open CategoryTheory Order

/-- The category of Boolean rings. -/
/-
**BoolRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of Boolean rings.
-/
structure BoolRing where
  /-- Construct a bundled `BoolRing` from a `BooleanRing`. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [booleanRing : BooleanRing carrier]

namespace BoolRing

initialize_simps_projections BoolRing (-booleanRing)

/-
**BoolRing.** 是 Mathlib 中的一个实例，位于命名空间 `BoolRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort BoolRing Type* :=
  ⟨carrier⟩

attribute [coe] carrier

attribute [instance] booleanRing
/-
**BoolRing.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `BoolRing`。
形式化陈述：coe_of (α : Type*) [BooleanRing α] : ↥(of α) = α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (α : Type*) [BooleanRing α] : ↥(of α) = α :=
  rfl
/-
**BoolRing.** 是 Mathlib 中的一个实例，位于命名空间 `BoolRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited BoolRing :=
  ⟨of PUnit⟩

variable {R} in
/-- The type of morphisms in `BoolRing`. -/
@[ext]
/-
**BoolRing.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `BoolRing`。
形式化陈述：BoolRing → BoolRing → Type (max u_1 u_2)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `BoolRing`.
-/
structure Hom (R S : BoolRing) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R →+* S

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**BoolRing.** 是 Mathlib 中的一个实例，位于命名空间 `BoolRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category BoolRing where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**BoolRing.** 是 Mathlib 中的一个实例，位于命名空间 `BoolRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory BoolRing (· →+* ·) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `BoolRing` back into a `RingHom`. -/
/-
**BoolRing.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `BoolRing.Hom`。
形式化陈述：{X Y : BoolRing} → X.Hom Y → ↑X →+* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `BoolRing` back into a `RingHom`.
-/
abbrev Hom.hom {X Y : BoolRing} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BoolRing) f

/-- Typecheck a `RingHom` as a morphism in `BoolRing`. -/
/-
**BoolRing.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `BoolRing`。
形式化陈述：ofHom {R S : Type u} [BooleanRing R] [BooleanRing S] (f : R ->+* S) : of R
 ⟶ of S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `RingHom` as a morphism in `BoolRing`.
-/
abbrev ofHom {R S : Type u} [BooleanRing R] [BooleanRing S] (f : R →+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom f

@[ext]
/-
**BoolRing.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `BoolRing`。
形式化陈述：hom_ext {R S : BoolRing} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoolRing.Hom.ext`：∀ {R : BoolRing} {S : BoolRing} {x y : R.Hom S}, x.hom
' = y.hom' → x = y
-/
lemma hom_ext {R S : BoolRing} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf
/-
**BoolRing.hasForgetToCommRing** 是 Mathlib 中的一个实例，位于命名空间 `BoolRing`。
形式化陈述：hasForgetToCommRing : HasForget₂ BoolRing CommRingCat where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToCommRing : HasForget₂ BoolRing CommRingCat where
  forget₂ :=
    { obj := fun R ↦ CommRingCat.of R
      map := fun f ↦ CommRingCat.ofHom f.hom }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Constructs an isomorphism of Boolean rings from a ring isomorphism between them. -/
@[simps]
/-
**BoolRing.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `BoolRing.Iso`。
形式化陈述：{α β : BoolRing} → ↑α ≃+* ↑β → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an isomorphism of Boolean rings from a ring isomorphism between them.
-/
def Iso.mk {α β : BoolRing.{u}} (e : α ≃+* β) : α ≅ β where
  hom := ⟨e⟩
  inv := ⟨e.symm⟩
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

end BoolRing

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/

-- We have to add this instance since Lean doesn't see through `X.toBddDistLat`.
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : BoolAlg} :
    BooleanAlgebra ↑(BddDistLat.toBddLat (X.toBddDistLat)).toLat :=
  BoolAlg.str _

-- We have to add this instance since Lean doesn't see through `R.toBddDistLat`.
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u} [BooleanRing R] :
    BooleanRing (BoolAlg.of (AsBoolAlg ↑R)).toBddDistLat.toBddLat.toLat :=
  inferInstanceAs <| BooleanRing R

@[simps]
/-
**BoolRing.hasForgetToBoolAlg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：BoolRing.hasForgetToBoolAlg : HasForget₂ BoolRing BoolAlg where forget₂.ob
j X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance BoolRing.hasForgetToBoolAlg : HasForget₂ BoolRing BoolAlg where
  forget₂.obj X := .of (AsBoolAlg X)
  forget₂.map f := BoolAlg.ofHom f.hom.asBoolAlg

@[simps]
/-
**BoolAlg.hasForgetToBoolRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：BoolAlg.hasForgetToBoolRing : HasForget₂ BoolAlg BoolRing where forget₂.ob
j X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance BoolAlg.hasForgetToBoolRing : HasForget₂ BoolAlg BoolRing where
  forget₂.obj X := .of (AsBoolRing X)
  forget₂.map f := BoolRing.ofHom <| BoundedLatticeHom.asBoolRing f.hom

/-- The equivalence between Boolean rings and Boolean algebras. This is actually an isomorphism. -/
@[simps functor inverse]
/-
**boolRingCatEquivBoolAlg** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：boolRingCatEquivBoolAlg : BoolRing ≌ BoolAlg where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between Boolean rings and Boolean algebras. This is actually an 
isomorphism.
-/
def boolRingCatEquivBoolAlg : BoolRing ≌ BoolAlg where
  functor := forget₂ BoolRing BoolAlg
  inverse := forget₂ BoolAlg BoolRing
  unitIso := NatIso.ofComponents (fun X => BoolRing.Iso.mk <|
    (RingEquiv.asBoolRingAsBoolAlg X).symm) fun {_ _} _ => rfl
  counitIso := NatIso.ofComponents (fun X => BoolAlg.Iso.mk <|
    OrderIso.asBoolAlgAsBoolRing X) fun {_ _} _ => rfl
