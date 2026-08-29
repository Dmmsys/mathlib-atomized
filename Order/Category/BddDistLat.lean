/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.BddLat
public import Mathlib.Order.Category.DistLat

/-!
# The category of bounded distributive lattices

This defines `BddDistLat`, the category of bounded distributive lattices.

Note that this category is sometimes called [`DistLat`](https://ncatlab.org/nlab/show/DistLat) when
being a lattice is understood to entail having a bottom and a top element.
-/

@[expose] public section


universe u

open CategoryTheory

/--
Definition of `BddDistLat` / `BddDistLat` 的定义

English:
structure BddDistLat
  parameters: extends DistLat
  extends: DistLat
  axioms and operations (1):
    - [isBoundedOrder : BoundedOrder toDistLat]

中文:
结构 BddDistLat
  参数: extends DistLat
  继承: DistLat
  公理与运算 (1 个):
    - [isBoundedOrder : BoundedOrder toDistLat]
-/
structure BddDistLat extends DistLat where
  [isBoundedOrder : BoundedOrder toDistLat]

/-- The underlying distrib lattice of a bounded distributive lattice. -/
add_decl_doc BddDistLat.toDistLat

namespace BddDistLat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort BddDistLat Type*
  body: ⟨fun X => X.toDistLat⟩

中文:
实例 :
  签名: CoeSort BddDistLat 类型
  定义体: ⟨fun X => X.toDistLat⟩

Depends on / 依赖: X.toDistLat, toDistLat
-/
instance : CoeSort BddDistLat Type* :=
  ⟨fun X => X.toDistLat⟩

instance (X : BddDistLat) : DistribLattice X :=
  X.toDistLat.str

attribute [instance] BddDistLat.isBoundedOrder

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (α : Type*) [DistribLattice α] [BoundedOrder α]
  body: α

中文:
缩写 of
  签名: (α : 类型) [DistribLattice α] [BoundedOrder α]
  定义体: α
-/
abbrev of (α : Type*) [DistribLattice α] [BoundedOrder α] : BddDistLat where
  carrier := α

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (α : Type*) [DistribLattice α] [BoundedOrder α]
  statement: ↥(of α) = α
  proof: rfl

中文:
定理 coe_of
  条件: (α : 类型) [DistribLattice α] [BoundedOrder α]
  结论: ↥(of α) = α
  证明: rfl
-/
theorem coe_of (α : Type*) [DistribLattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

/-- The type of morphisms in `BddDistLat R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : BddDistLat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : BoundedLatticeHom X Y

中文:
结构 Hom
  参数: (X Y : BddDistLat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : BoundedLatticeHom X Y
-/
structure Hom (X Y : BddDistLat.{u}) where
  private mk ::
  /-- The underlying `BoundedLatticeHom`. -/
  hom' : BoundedLatticeHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category BddDistLat.{u}
  body: Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category BddDistLat.{u}
  定义体: Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category BddDistLat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory BddDistLat (BoundedLatticeHom · ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory BddDistLat (BoundedLatticeHom · ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory BddDistLat (BoundedLatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : BddDistLat.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := BddDistLat) f

中文:
缩写 Hom.hom
  签名: {X Y : BddDistLat.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := BddDistLat) f
-/
abbrev Hom.hom {X Y : BddDistLat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BddDistLat) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y] [BoundedOrder Y]
  body: ConcreteCategory.ofHom (C := BddDistLat) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y] [BoundedOrder Y]
  定义体: ConcreteCategory.ofHom (C := BddDistLat) f

Depends on / 依赖: BddDistLat, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y] [BoundedOrder Y]
    (f : BoundedLatticeHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := BddDistLat) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : BddDistLat.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : BddDistLat.{u}) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : BddDistLat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: {X : BddDistLat}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[simp]

中文:
引理 coe_id
  条件: {X : BddDistLat}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[simp]
-/
lemma coe_id {X : BddDistLat} : (𝟙 X : X -> X) = id := rfl

@[simp]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : BddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[simp]

中文:
引理 coe_comp
  条件: {X Y Z : BddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[simp]
-/
lemma coe_comp {X Y Z : BddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[simp]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y : BddDistLat} (f : X ⟶ Y)
  proof: rfl

@[ext]

中文:
引理 forget_map
  条件: {X Y : BddDistLat} (f : X ⟶ Y)
  证明: rfl

@[ext]
-/
lemma forget_map {X Y : BddDistLat} (f : X ⟶ Y) :
    (forget BddDistLat).map f = (f : _ -> _) := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : BddDistLat} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

@[simp]

中文:
引理 ext
  条件: {X Y : BddDistLat} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : BddDistLat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : BddDistLat}
  statement: (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _
  proof: rfl

中文:
引理 hom_id
  条件: {X : BddDistLat}
  结论: (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _
  证明: rfl
-/
lemma hom_id {X : BddDistLat} : (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _ := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : BddDistLat) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : BddDistLat) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : BddDistLat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_comp {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp

@[ext]
-/
lemma comp_apply {X Y Z : BddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : BddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {X Y : BddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : BddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  statement: {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  结论: {X Y : 类型u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
    [BoundedOrder Y] (f : BoundedLatticeHom X Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : BddDistLat} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : BddDistLat} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : BddDistLat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [DistribLattice X] [BoundedOrder X]
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型u} [DistribLattice X] [BoundedOrder X]
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type u} [DistribLattice X] [BoundedOrder X] :
    ofHom (BoundedLatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
    [BoundedOrder Y] [DistribLattice Z] [BoundedOrder Z]
    (f : BoundedLatticeHom X Y) (g : BoundedLatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {X Y : 类型u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [DistribLattice X] [BoundedOrder X] [DistribLattice Y]
    [BoundedOrder Y]
    (f : BoundedLatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : BddDistLat} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : BddDistLat} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : BddDistLat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : BddDistLat} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {X Y : BddDistLat} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {X Y : BddDistLat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited BddDistLat
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: Inhabited BddDistLat
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited BddDistLat :=
  ⟨of PUnit⟩

/--
Definition of `toBddLat` / `toBddLat` 的定义

English:
definition toBddLat
  signature: (X : BddDistLat)
  body: .of X

@[simp]

中文:
定义 toBddLat
  签名: (X : BddDistLat)
  定义体: .of X

@[simp]
-/
def toBddLat (X : BddDistLat) : BddLat :=
  .of X

@[simp]
/--
theorem `coe_toBddLat` / 定理 `coe_toBddLat`

English:
theorem coe_toBddLat
  given: (X : BddDistLat)
  statement: ↥X.toBddLat = ↥X
  proof: rfl

中文:
定理 coe_toBddLat
  条件: (X : BddDistLat)
  结论: ↥X.toBddLat = ↥X
  证明: rfl
-/
theorem coe_toBddLat (X : BddDistLat) : ↥X.toBddLat = ↥X :=
  rfl

/--
Instance `hasForgetToDistLat` / 实例 `hasForgetToDistLat`

English:
instance hasForgetToDistLat
  signature: : HasForget₂ BddDistLat DistLat where
  body: .of X
  forget₂.map f := DistLat.ofHom f.hom.toLatticeHom

中文:
实例 hasForgetToDistLat
  签名: : HasForget₂ BddDistLat DistLat where
  定义体: .of X
  forget₂.map f := DistLat.ofHom f.hom.toLatticeHom
-/
instance hasForgetToDistLat : HasForget₂ BddDistLat DistLat where
  forget₂.obj X := .of X
  forget₂.map f := DistLat.ofHom f.hom.toLatticeHom

/--
Instance `hasForgetToBddLat` / 实例 `hasForgetToBddLat`

English:
instance hasForgetToBddLat
  signature: : HasForget₂ BddDistLat BddLat where
  body: .of X
  forget₂.map f := BddLat.ofHom f.hom

中文:
实例 hasForgetToBddLat
  签名: : HasForget₂ BddDistLat BddLat where
  定义体: .of X
  forget₂.map f := BddLat.ofHom f.hom
-/
instance hasForgetToBddLat : HasForget₂ BddDistLat BddLat where
  forget₂.obj X := .of X
  forget₂.map f := BddLat.ofHom f.hom

/--
theorem `forget_bddLat_lat_eq_forget_distLat_lat` / 定理 `forget_bddLat_lat_eq_forget_distLat_lat`

English:
theorem forget_bddLat_lat_eq_forget_distLat_lat
  proof: rfl

中文:
定理 forget_bddLat_lat_eq_forget_distLat_lat
  证明: rfl
-/
theorem forget_bddLat_lat_eq_forget_distLat_lat :
    forget₂ BddDistLat BddLat ⋙ forget₂ BddLat Lat =
      forget₂ BddDistLat DistLat ⋙ forget₂ DistLat Lat :=
  rfl

/-- Constructs an equivalence between bounded distributive lattices from an order isomorphism
between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : BddDistLat.{u}} (e : α ≃o β)
  body: BddDistLat.ofHom e
  inv := BddDistLat.ofHom e.symm

中文:
定义 Iso.mk
  签名: {α β : BddDistLat.{u}} (e : α ≃o β)
  定义体: BddDistLat.ofHom e
  inv := BddDistLat.ofHom e.symm
-/
def Iso.mk {α β : BddDistLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := BddDistLat.ofHom e
  inv := BddDistLat.ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : BddDistLat ⥤ BddDistLat where
  body: of Xᵒᵈ
  map f := BddDistLat.ofHom f.hom.dual

中文:
定义 dual
  签名: : BddDistLat ⥤ BddDistLat where
  定义体: of Xᵒᵈ
  map f := BddDistLat.ofHom f.hom.dual
-/
def dual : BddDistLat ⥤ BddDistLat where
  obj X := of Xᵒᵈ
  map f := BddDistLat.ofHom f.hom.dual

/-- The equivalence between `BddDistLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : BddDistLat ≌ BddDistLat where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : BddDistLat ≌ BddDistLat where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
-/
def dualEquiv : BddDistLat ≌ BddDistLat where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

end BddDistLat

/--
theorem `bddDistLat_dual_comp_forget_to_distLat` / 定理 `bddDistLat_dual_comp_forget_to_distLat`

English:
theorem bddDistLat_dual_comp_forget_to_distLat
  proof: rfl

中文:
定理 bddDistLat_dual_comp_forget_to_distLat
  证明: rfl
-/
theorem bddDistLat_dual_comp_forget_to_distLat :
    BddDistLat.dual ⋙ forget₂ BddDistLat DistLat =
      forget₂ BddDistLat DistLat ⋙ DistLat.dual :=
  rfl
