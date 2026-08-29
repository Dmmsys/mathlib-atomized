/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Order.Category.BddOrd
public import Mathlib.Order.Category.Lat
public import Mathlib.Order.Category.Semilat
public import Mathlib.Order.Hom.WithTopBot

/-!
# The category of bounded lattices

This file defines `BddLat`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/

@[expose] public section


universe u

open CategoryTheory

/--
Definition of `BddLat` / `BddLat` 的定义

English:
structure BddLat
  parameters: extends Lat
  extends: Lat
  axioms and operations (1):
    - [isBoundedOrder : BoundedOrder toLat]

中文:
结构 有界格
  参数: extends 格
  继承: 格
  公理与运算 (1 个):
    - [isBoundedOrder : 有界序 toLat]
-/
structure BddLat extends Lat where
  [isBoundedOrder : BoundedOrder toLat]

/-- The underlying lattice of a bounded lattice. -/
add_decl_doc BddLat.toLat

namespace BddLat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort BddLat Type*
  body: ⟨fun X => X.toLat⟩

中文:
实例 :
  签名: CoeSort 有界格 类型
  定义体: ⟨fun X => X.toLat⟩

Depends on / 依赖: X.toLat
-/
instance : CoeSort BddLat Type* :=
  ⟨fun X => X.toLat⟩

attribute [instance] BddLat.isBoundedOrder

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (α : Type*) [Lattice α] [BoundedOrder α]
  body: α

中文:
缩写 of
  签名: (α : 类型) [格 α] [有界序 α]
  定义体: α
-/
abbrev of (α : Type*) [Lattice α] [BoundedOrder α] : BddLat where
  carrier := α

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (α : Type*) [Lattice α] [BoundedOrder α]
  statement: ↥(of α) = α
  proof: rfl

中文:
定理 coe_of
  条件: (α : 类型) [格 α] [有界序 α]
  结论: ↥(of α) = α
  证明: rfl
-/
theorem coe_of (α : Type*) [Lattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

/-- The type of morphisms in `BddLat`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : BddLat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : BoundedLatticeHom X Y

中文:
结构 态射
  参数: (X Y : 有界格.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : 有界格态射 X Y
-/
structure Hom (X Y : BddLat.{u}) where
  private mk ::
  /-- The underlying `BoundedLatticeHom`. -/
  hom' : BoundedLatticeHom X Y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited BddLat
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 有界格
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited BddLat :=
  ⟨of PUnit⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory.{u} BddLat
  body: Hom
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 大范畴.{u} 有界格
  定义体: Hom
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : LargeCategory.{u} BddLat where
  Hom := Hom
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory BddLat (BoundedLatticeHom · ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴 有界格 (有界格态射 · ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory BddLat (BoundedLatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : BddLat.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := BddLat) f

中文:
缩写 态射.hom
  签名: {X Y : 有界格.{u}} (f : 态射 X Y)
  定义体: ConcreteCategory.hom (C := BddLat) f
-/
abbrev Hom.hom {X Y : BddLat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BddLat) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [Lattice X] [BoundedOrder X] [Lattice Y] [BoundedOrder Y]
  body: ConcreteCategory.ofHom (C := BddLat) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [格 X] [有界序 X] [格 Y] [有界序 Y]
  定义体: ConcreteCategory.ofHom (C := BddLat) f

Depends on / 依赖: BddLat, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type u} [Lattice X] [BoundedOrder X] [Lattice Y] [BoundedOrder Y]
    (f : BoundedLatticeHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := BddLat) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : BddLat.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

@[simp]

中文:
定义 态射.Simps.hom
  签名: (X Y : 有界格.{u}) (f : 态射 X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)

@[simp]
-/
def Hom.Simps.hom (X Y : BddLat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : Lat}
  statement: (𝟙 X : X ⟶ X).hom = LatticeHom.id _
  proof: rfl

中文:
引理 hom_id
  条件: {X : 格}
  结论: (𝟙 X : X ⟶ X).hom = 格态射.id _
  证明: rfl
-/
lemma hom_id {X : Lat} : (𝟙 X : X ⟶ X).hom = LatticeHom.id _ := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : Lat) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : 格) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : Lat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : 格} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_comp {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {X Y Z : 格} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp

@[ext]
-/
lemma comp_apply {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : BddLat} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

@[ext]

中文:
引理 ext
  条件: {X Y : 有界格} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

@[ext]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : BddLat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : BddLat} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

中文:
引理 hom_ext
  条件: {X Y : 有界格} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : BddLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

/--
Instance `hasForgetToBddOrd` / 实例 `hasForgetToBddOrd`

English:
instance hasForgetToBddOrd
  signature: : HasForget₂ BddLat BddOrd where
  body: .of X
  forget₂.map f := BddOrd.ofHom f.hom.toBoundedOrderHom

中文:
实例 hasForgetToBddOrd
  签名: : 有Forget₂ 有界格 有界序 where
  定义体: .of X
  forget₂.map f := BddOrd.ofHom f.hom.toBoundedOrderHom
-/
instance hasForgetToBddOrd : HasForget₂ BddLat BddOrd where
  forget₂.obj X := .of X
  forget₂.map f := BddOrd.ofHom f.hom.toBoundedOrderHom

/--
Instance `hasForgetToLat` / 实例 `hasForgetToLat`

English:
instance hasForgetToLat
  signature: : HasForget₂ BddLat Lat where
  body: .of X
  forget₂.map f := Lat.ofHom f.hom.toLatticeHom

中文:
实例 hasForgetToLat
  签名: : 有Forget₂ 有界格 格 where
  定义体: .of X
  forget₂.map f := Lat.ofHom f.hom.toLatticeHom
-/
instance hasForgetToLat : HasForget₂ BddLat Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom f.hom.toLatticeHom

/--
Instance `hasForgetToSemilatSup` / 实例 `hasForgetToSemilatSup`

English:
instance hasForgetToSemilatSup
  signature: : HasForget₂ BddLat SemilatSupCat where
  body: .of X
  forget₂.map f := f.hom.toSupBotHom

中文:
实例 hasForgetToSemilatSup
  签名: : 有Forget₂ 有界格 SemilatSup范畴 where
  定义体: .of X
  forget₂.map f := f.hom.toSupBotHom
-/
instance hasForgetToSemilatSup : HasForget₂ BddLat SemilatSupCat where
  forget₂.obj X := .of X
  forget₂.map f := f.hom.toSupBotHom

/--
Instance `hasForgetToSemilatInf` / 实例 `hasForgetToSemilatInf`

English:
instance hasForgetToSemilatInf
  signature: : HasForget₂ BddLat SemilatInfCat where
  body: .of X
  forget₂.map f := f.hom.toInfTopHom

@[simp]

中文:
实例 hasForgetToSemilatInf
  签名: : 有Forget₂ 有界格 SemilatInf范畴 where
  定义体: .of X
  forget₂.map f := f.hom.toInfTopHom

@[simp]
-/
instance hasForgetToSemilatInf : HasForget₂ BddLat SemilatInfCat where
  forget₂.obj X := .of X
  forget₂.map f := f.hom.toInfTopHom

@[simp]
/--
theorem `coe_forget_to_bddOrd` / 定理 `coe_forget_to_bddOrd`

English:
theorem coe_forget_to_bddOrd
  given: (X : BddLat)
  statement: ↥((forget₂ BddLat BddOrd).obj X) = ↥X
  proof: rfl

@[simp]

中文:
定理 coe_forget_to_bddOrd
  条件: (X : 有界格)
  结论: ↥((forget₂ 有界格 有界序).obj X) = ↥X
  证明: rfl

@[simp]
-/
theorem coe_forget_to_bddOrd (X : BddLat) : ↥((forget₂ BddLat BddOrd).obj X) = ↥X :=
  rfl

@[simp]
/--
theorem `coe_forget_to_lat` / 定理 `coe_forget_to_lat`

English:
theorem coe_forget_to_lat
  given: (X : BddLat)
  statement: ↥((forget₂ BddLat Lat).obj X) = ↥X
  proof: rfl

@[simp]

中文:
定理 coe_forget_to_lat
  条件: (X : 有界格)
  结论: ↥((forget₂ 有界格 格).obj X) = ↥X
  证明: rfl

@[simp]
-/
theorem coe_forget_to_lat (X : BddLat) : ↥((forget₂ BddLat Lat).obj X) = ↥X :=
  rfl

@[simp]
/--
theorem `coe_forget_to_semilatSup` / 定理 `coe_forget_to_semilatSup`

English:
theorem coe_forget_to_semilatSup
  given: (X : BddLat)
  proof: rfl

@[simp]

中文:
定理 coe_forget_to_semilatSup
  条件: (X : 有界格)
  证明: rfl

@[simp]
-/
theorem coe_forget_to_semilatSup (X : BddLat) :
    ↥((forget₂ BddLat SemilatSupCat).obj X) = ↥X :=
  rfl

@[simp]
/--
theorem `coe_forget_to_semilatInf` / 定理 `coe_forget_to_semilatInf`

English:
theorem coe_forget_to_semilatInf
  given: (X : BddLat)
  proof: rfl

中文:
定理 coe_forget_to_semilatInf
  条件: (X : 有界格)
  证明: rfl
-/
theorem coe_forget_to_semilatInf (X : BddLat) :
    ↥((forget₂ BddLat SemilatInfCat).obj X) = ↥X :=
  rfl

/--
theorem `forget_lat_partOrd_eq_forget_bddOrd_partOrd` / 定理 `forget_lat_partOrd_eq_forget_bddOrd_partOrd`

English:
theorem forget_lat_partOrd_eq_forget_bddOrd_partOrd
  proof: rfl

中文:
定理 forget_lat_partOrd_eq_forget_bddOrd_partOrd
  证明: rfl
-/
theorem forget_lat_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat Lat ⋙ forget₂ Lat PartOrd =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl

/--
theorem `forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd` / 定理 `forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd`

English:
theorem forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd
  proof: rfl

中文:
定理 forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd
  证明: rfl
-/
theorem forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat SemilatSupCat ⋙ forget₂ SemilatSupCat PartOrd =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl

/--
theorem `forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd` / 定理 `forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd`

English:
theorem forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd
  proof: rfl

中文:
定理 forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd
  证明: rfl
-/
theorem forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat SemilatInfCat ⋙ forget₂ SemilatInfCat PartOrd =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : BddLat.{u}} (e : α ≃o β)
  body: ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

中文:
定义 同构.mk
  签名: {α β : 有界格.{u}} (e : α ≃o β)
  定义体: ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
-/
def Iso.mk {α β : BddLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : BddLat ⥤ BddLat where
  body: of Xᵒᵈ
  map f := ofHom f.hom.dual

中文:
定义 dual
  签名: : 有界格 ⥤ 有界格 where
  定义体: of Xᵒᵈ
  map f := ofHom f.hom.dual
-/
def dual : BddLat ⥤ BddLat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `BddLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : BddLat ≌ BddLat where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : 有界格 ≌ 有界格 where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
-/
def dualEquiv : BddLat ≌ BddLat where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

end BddLat

/--
theorem `bddLat_dual_comp_forget_to_bddOrd` / 定理 `bddLat_dual_comp_forget_to_bddOrd`

English:
theorem bddLat_dual_comp_forget_to_bddOrd
  proof: rfl

中文:
定理 bddLat_dual_comp_forget_to_bddOrd
  证明: rfl
-/
theorem bddLat_dual_comp_forget_to_bddOrd :
    BddLat.dual ⋙ forget₂ BddLat BddOrd =
    forget₂ BddLat BddOrd ⋙ BddOrd.dual :=
  rfl

/--
theorem `bddLat_dual_comp_forget_to_lat` / 定理 `bddLat_dual_comp_forget_to_lat`

English:
theorem bddLat_dual_comp_forget_to_lat
  proof: rfl

中文:
定理 bddLat_dual_comp_forget_to_lat
  证明: rfl
-/
theorem bddLat_dual_comp_forget_to_lat :
    BddLat.dual ⋙ forget₂ BddLat Lat = forget₂ BddLat Lat ⋙ Lat.dual :=
  rfl

/--
theorem `bddLat_dual_comp_forget_to_semilatSupCat` / 定理 `bddLat_dual_comp_forget_to_semilatSupCat`

English:
theorem bddLat_dual_comp_forget_to_semilatSupCat
  proof: rfl

中文:
定理 bddLat_dual_comp_forget_to_semilatSupCat
  证明: rfl
-/
theorem bddLat_dual_comp_forget_to_semilatSupCat :
    BddLat.dual ⋙ forget₂ BddLat SemilatSupCat =
    forget₂ BddLat SemilatInfCat ⋙ SemilatInfCat.dual :=
  rfl

/--
theorem `bddLat_dual_comp_forget_to_semilatInfCat` / 定理 `bddLat_dual_comp_forget_to_semilatInfCat`

English:
theorem bddLat_dual_comp_forget_to_semilatInfCat
  proof: rfl

中文:
定理 bddLat_dual_comp_forget_to_semilatInfCat
  证明: rfl
-/
theorem bddLat_dual_comp_forget_to_semilatInfCat :
    BddLat.dual ⋙ forget₂ BddLat SemilatInfCat =
    forget₂ BddLat SemilatSupCat ⋙ SemilatSupCat.dual :=
  rfl

/--
Definition of `latToBddLat` / `latToBddLat` 的定义

English:
definition latToBddLat
  signature: : Lat.{u} ⥤ BddLat where
  body: .of WithTop WithBot X
map f := BddLat.ofHom LatticeHom.withTopWithBot f.hom

中文:
定义 latToBddLat
  签名: : 格.{u} ⥤ 有界格 where
  定义体: .of WithTop WithBot X
map f := BddLat.ofHom LatticeHom.withTopWithBot f.hom

Depends on / 依赖: WithBot, WithTop
-/
def latToBddLat : Lat.{u} ⥤ BddLat where
obj X := .of WithTop WithBot X
map f := BddLat.ofHom LatticeHom.withTopWithBot f.hom

/--
Definition of `latToBddLatForgetAdjunction` / `latToBddLatForgetAdjunction` 的定义

English:
definition latToBddLatForgetAdjunction
  signature: : latToBddLat.{u} ⊣ forget₂ BddLat Lat
  body: Adjunction.mkOfHomEquiv
    { homEquiv X _ :=
        { toFun f := Lat.ofHom
            { toFun := f ∘ some ∘ some
              map_sup' := fun a b => (congr_arg f <| by rfl).trans (f.hom.map_sup' _ _)
              map_inf' := fun a b => (congr_arg f <| by rfl).trans (f.hom.map_inf' _ _) }
invFun f := BddLat.ofHom LatticeHom.withTopWithBot' f.hom
          left_inv := fun f =>
            BddLat.ext fun a =>
              match a with
              | none => f.hom.map_top'.symm
              | some none => f.hom.map_bot'.symm
              | some (some _) => rfl }
      homEquiv_naturality_left_symm := fun _ _ =>
        BddLat.ext fun a =>
          match a with
          | none => rfl
          | some none => rfl
          | some (some _) => rfl
      homEquiv_naturality_right := fun _ _ => Lat.ext fun _ => rfl }

中文:
定义 latToBddLatForgetAdjunction
  签名: : latToBddLat.{u} ⊣ forget₂ 有界格 格
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv X _ :=
        { toFun f := Lat.ofHom
            { toFun := f ∘ some ∘ some
              map_sup' := fun a b => (congr_arg f <| by rfl).trans (f.hom.map_sup' _ _)
              map_inf' := fun a b => (congr_arg f <| by rfl).trans (f.hom.map_inf' _ _) }
invFun f := BddLat.ofHom LatticeHom.withTopWithBot' f.hom
          left_inv := fun f =>
            BddLat.ext fun a =>
              match a with
              | none => f.hom.map_top'.symm
              | some none => f.hom.map_bot'.symm
              | some (some _) => rfl }
      homEquiv_naturality_left_symm := fun _ _ =>
        BddLat.ext fun a =>
          match a with
          | none => rfl
          | some none => rfl
          | some (some _) => rfl
      homEquiv_naturality_right := fun _ _ => Lat.ext fun _ => rfl }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, BddLat, BddLat.ext, BddLat.ofHom, Lat.ofHom, LatticeHom, LatticeHom.withTopWithBot, congr_arg, f.hom, f.hom.map_bot, f.hom.map_inf, f.hom.map_sup, f.hom.map_top, homEquiv, homEquiv_naturality_left_symm, invFun, left_inv, map_bot, map_inf
-/
def latToBddLatForgetAdjunction : latToBddLat.{u} ⊣ forget₂ BddLat Lat :=
  Adjunction.mkOfHomEquiv
    { homEquiv X _ :=
        { toFun f := Lat.ofHom
            { toFun := f ∘ some ∘ some
              map_sup' := fun a b => (congr_arg f <| by rfl).trans (f.hom.map_sup' _ _)
              map_inf' := fun a b => (congr_arg f <| by rfl).trans (f.hom.map_inf' _ _) }
invFun f := BddLat.ofHom LatticeHom.withTopWithBot' f.hom
          left_inv := fun f =>
            BddLat.ext fun a =>
              match a with
              | none => f.hom.map_top'.symm
              | some none => f.hom.map_bot'.symm
              | some (some _) => rfl }
      homEquiv_naturality_left_symm := fun _ _ =>
        BddLat.ext fun a =>
          match a with
          | none => rfl
          | some none => rfl
          | some (some _) => rfl
      homEquiv_naturality_right := fun _ _ => Lat.ext fun _ => rfl }

/--
Definition of `latToBddLatCompDualIsoDualCompLatToBddLat` / `latToBddLatCompDualIsoDualCompLatToBddLat` 的定义

English:
definition latToBddLatCompDualIsoDualCompLatToBddLat
  signature: :
  body: Adjunction.leftAdjointUniq (latToBddLatForgetAdjunction.comp BddLat.dualEquiv.toAdjunction)
    (Lat.dualEquiv.toAdjunction.comp latToBddLatForgetAdjunction)

中文:
定义 latToBddLatCompDualIsoDualCompLatToBddLat
  签名: :
  定义体: Adjunction.leftAdjointUniq (latToBddLatForgetAdjunction.comp BddLat.dualEquiv.toAdjunction)
    (Lat.dualEquiv.toAdjunction.comp latToBddLatForgetAdjunction)

Depends on / 依赖: Adjunction, Adjunction.leftAdjointUniq, BddLat, BddLat.dualEquiv.toAdjunction, Lat.dualEquiv.toAdjunction.comp, dualEquiv, latToBddLatForgetAdjunction, latToBddLatForgetAdjunction.comp, leftAdjointUniq, toAdjunction
-/
def latToBddLatCompDualIsoDualCompLatToBddLat :
    latToBddLat.{u} ⋙ BddLat.dual ≅ Lat.dual ⋙ latToBddLat :=
  Adjunction.leftAdjointUniq (latToBddLatForgetAdjunction.comp BddLat.dualEquiv.toAdjunction)
    (Lat.dualEquiv.toAdjunction.comp latToBddLatForgetAdjunction)
