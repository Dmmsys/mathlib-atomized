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

/--
Definition of `BoolRing` / `BoolRing` 的定义

English:
structure BoolRing
  parameters: where
  axioms and operations (3):
    - of : :
    - carrier : Type u
    - [booleanRing : BooleanRing carrier]

中文:
结构 布尔值环
  参数: where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型u
    - [booleanRing : 布尔ean环 carrier]
-/
structure BoolRing where
  /-- Construct a bundled `BoolRing` from a `BooleanRing`. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [booleanRing : BooleanRing carrier]

namespace BoolRing

initialize_simps_projections BoolRing (-booleanRing)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort BoolRing Type*
  body: ⟨carrier⟩

中文:
实例 :
  签名: CoeSort 布尔值环 类型
  定义体: ⟨carrier⟩

Depends on / 依赖: carrier
-/
instance : CoeSort BoolRing Type* :=
  ⟨carrier⟩

attribute [coe] carrier

attribute [instance] booleanRing

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (α : Type*) [BooleanRing α]
  statement: ↥(of α) = α
  proof: rfl

中文:
定理 coe_of
  条件: (α : 类型) [布尔ean环 α]
  结论: ↥(of α) = α
  证明: rfl
-/
theorem coe_of (α : Type*) [BooleanRing α] : ↥(of α) = α :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited BoolRing
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 布尔值环
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited BoolRing :=
  ⟨of PUnit⟩

variable {R} in
/-- The type of morphisms in `BoolRing`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (R S : BoolRing)
  axioms and operations (2):
    - private(mk) : :
    - hom' : R ->+* S

中文:
结构 态射
  参数: (R S : 布尔值环)
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : R ->+* S
-/
structure Hom (R S : BoolRing) where
  private mk ::
  /-- The underlying ring hom. -/
  hom' : R ->+* S

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category BoolRing
  body: Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 布尔值环
  定义体: Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category BoolRing where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory BoolRing (· ->+* ·)
  body: f.hom'
  ofHom f := ⟨f⟩

中文:
实例 :
  签名: 余ncrete范畴 布尔值环 (· ->+* ·)
  定义体: f.hom'
  ofHom f := ⟨f⟩

Depends on / 依赖: f.hom
-/
instance : ConcreteCategory BoolRing (· ->+* ·) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : BoolRing} (f : Hom X Y)
  body: ConcreteCategory.hom (C := BoolRing) f

中文:
缩写 态射.hom
  签名: {X Y : 布尔值环} (f : 态射 X Y)
  定义体: ConcreteCategory.hom (C := BoolRing) f

Depends on / 依赖: BoolRing, ConcreteCategory, ConcreteCategory.hom
-/
abbrev Hom.hom {X Y : BoolRing} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BoolRing) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {R S : Type u} [BooleanRing R] [BooleanRing S] (f : R ->+* S)
  body: ConcreteCategory.ofHom f

@[ext]

中文:
缩写 ofHom
  签名: {R S : 类型u} [布尔ean环 R] [布尔ean环 S] (f : R ->+* S)
  定义体: ConcreteCategory.ofHom f

@[ext]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {R S : Type u} [BooleanRing R] [BooleanRing S] (f : R ->+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom f

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {R S : BoolRing} {f g : R ⟶ S} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

中文:
引理 hom_ext
  条件: {R S : 布尔值环} {f g : R ⟶ S} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {R S : BoolRing} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

/--
Instance `hasForgetToCommRing` / 实例 `hasForgetToCommRing`

English:
instance hasForgetToCommRing
  signature: : HasForget₂ BoolRing CommRingCat where
  body: { obj := fun R => CommRingCat.of R
      map := fun f => CommRingCat.ofHom f.hom }

中文:
实例 hasForgetToCommRing
  签名: : 有Forget₂ 布尔值环 交换环范畴 where
  定义体: { obj := fun R => CommRingCat.of R
      map := fun f => CommRingCat.ofHom f.hom }

Depends on / 依赖: CommRingCat, CommRingCat.of, CommRingCat.ofHom, f.hom
-/
instance hasForgetToCommRing : HasForget₂ BoolRing CommRingCat where
  forget₂ :=
    { obj := fun R => CommRingCat.of R
      map := fun f => CommRingCat.ofHom f.hom }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Constructs an isomorphism of Boolean rings from a ring isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : BoolRing.{u}} (e : α ≃+* β)
  body: ⟨e⟩
  inv := ⟨e.symm⟩
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

中文:
定义 同构.mk
  签名: {α β : 布尔值环.{u}} (e : α ≃+* β)
  定义体: ⟨e⟩
  inv := ⟨e.symm⟩
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
-/
def Iso.mk {α β : BoolRing.{u}} (e : α ≃+* β) : α ≅ β where
  hom := ⟨e⟩
  inv := ⟨e.symm⟩
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

end BoolRing

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/

-- We have to add this instance since Lean doesn't see through `X.toBddDistLat`.
instance {X : BoolAlg} :
    BooleanAlgebra ↑(BddDistLat.toBddLat (X.toBddDistLat)).toLat :=
  BoolAlg.str _

-- We have to add this instance since Lean doesn't see through `R.toBddDistLat`.
instance {R : Type u} [BooleanRing R] :
    BooleanRing (BoolAlg.of (AsBoolAlg ↑R)).toBddDistLat.toBddLat.toLat :=
inferInstanceAs BooleanRing R

@[simps]
/--
Instance `BoolRing.hasForgetToBoolAlg` / 实例 `BoolRing.hasForgetToBoolAlg`

English:
instance BoolRing.hasForgetToBoolAlg
  signature: : HasForget₂ BoolRing BoolAlg where
  body: .of (AsBoolAlg X)
  forget₂.map f := BoolAlg.ofHom f.hom.asBoolAlg

@[simps]

中文:
实例 布尔值环.hasForgetTo布尔Alg
  签名: : 有Forget₂ 布尔值环 布尔Alg where
  定义体: .of (AsBoolAlg X)
  forget₂.map f := BoolAlg.ofHom f.hom.asBoolAlg

@[simps]

Depends on / 依赖: AsBoolAlg
-/
instance BoolRing.hasForgetToBoolAlg : HasForget₂ BoolRing BoolAlg where
  forget₂.obj X := .of (AsBoolAlg X)
  forget₂.map f := BoolAlg.ofHom f.hom.asBoolAlg

@[simps]
/--
Instance `BoolAlg.hasForgetToBoolRing` / 实例 `BoolAlg.hasForgetToBoolRing`

English:
instance BoolAlg.hasForgetToBoolRing
  signature: : HasForget₂ BoolAlg BoolRing where
  body: .of (AsBoolRing X)
forget₂.map f := BoolRing.ofHom BoundedLatticeHom.asBoolRing f.hom

中文:
实例 布尔Alg.hasForgetTo布尔Ring
  签名: : 有Forget₂ 布尔Alg 布尔值环 where
  定义体: .of (AsBoolRing X)
forget₂.map f := BoolRing.ofHom BoundedLatticeHom.asBoolRing f.hom

Depends on / 依赖: AsBoolRing
-/
instance BoolAlg.hasForgetToBoolRing : HasForget₂ BoolAlg BoolRing where
  forget₂.obj X := .of (AsBoolRing X)
forget₂.map f := BoolRing.ofHom BoundedLatticeHom.asBoolRing f.hom

/-- The equivalence between Boolean rings and Boolean algebras. This is actually an isomorphism. -/
@[simps functor inverse]
/--
Definition of `boolRingCatEquivBoolAlg` / `boolRingCatEquivBoolAlg` 的定义

English:
definition boolRingCatEquivBoolAlg
  signature: : BoolRing ≌ BoolAlg where
  body: forget₂ BoolRing BoolAlg
  inverse := forget₂ BoolAlg BoolRing
  unitIso := NatIso.ofComponents (fun X => BoolRing.Iso.mk <|
    (RingEquiv.asBoolRingAsBoolAlg X).symm) fun {_ _} _ => rfl
  counitIso := NatIso.ofComponents (fun X => BoolAlg.Iso.mk <|
    OrderIso.asBoolAlgAsBoolRing X) fun {_ _} _ => rfl

中文:
定义 boolRingCatEquiv布尔Alg
  签名: : 布尔值环 ≌ 布尔Alg where
  定义体: forget₂ BoolRing BoolAlg
  inverse := forget₂ BoolAlg BoolRing
  unitIso := NatIso.ofComponents (fun X => BoolRing.Iso.mk <|
    (RingEquiv.asBoolRingAsBoolAlg X).symm) fun {_ _} _ => rfl
  counitIso := NatIso.ofComponents (fun X => BoolAlg.Iso.mk <|
    OrderIso.asBoolAlgAsBoolRing X) fun {_ _} _ => rfl

Depends on / 依赖: BoolAlg, BoolRing
-/
def boolRingCatEquivBoolAlg : BoolRing ≌ BoolAlg where
  functor := forget₂ BoolRing BoolAlg
  inverse := forget₂ BoolAlg BoolRing
  unitIso := NatIso.ofComponents (fun X => BoolRing.Iso.mk <|
    (RingEquiv.asBoolRingAsBoolAlg X).symm) fun {_ _} _ => rfl
  counitIso := NatIso.ofComponents (fun X => BoolAlg.Iso.mk <|
    OrderIso.asBoolAlgAsBoolRing X) fun {_ _} _ => rfl
