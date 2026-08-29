/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Category.BddDistLat
public import Mathlib.Order.Category.FinPartOrd

/-!
# The category of finite bounded distributive lattices

This file defines `FinBddDistLat`, the category of finite distributive lattices with
bounded lattice homomorphisms.
-/

@[expose] public section


universe u

open CategoryTheory

/--
Definition of `FinBddDistLat` / `FinBddDistLat` 的定义

English:
structure FinBddDistLat
  parameters: extends BddDistLat
  extends: BddDistLat
  axioms and operations (1):
    - [isFintype : Fintype carrier]

中文:
结构 FinBddDistLat
  参数: extends BddDistLat
  继承: BddDistLat
  公理与运算 (1 个):
    - [isFintype : Fintype carrier]
-/
structure FinBddDistLat extends BddDistLat where
  [isFintype : Fintype carrier]

namespace FinBddDistLat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort FinBddDistLat Type*
  body: ⟨fun X => X.carrier⟩

中文:
实例 :
  签名: CoeSort FinBddDistLat 类型
  定义体: ⟨fun X => X.carrier⟩

Depends on / 依赖: X.carrier, carrier
-/
instance : CoeSort FinBddDistLat Type* :=
  ⟨fun X => X.carrier⟩

instance (X : FinBddDistLat) : DistribLattice X :=
  X.str

instance (X : FinBddDistLat) : BoundedOrder X :=
  X.isBoundedOrder

attribute [instance] FinBddDistLat.isFintype

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (α : Type*) [DistribLattice α] [BoundedOrder α] [Fintype α]
  body: α

中文:
缩写 of
  签名: (α : 类型) [DistribLattice α] [BoundedOrder α] [Fintype α]
  定义体: α
-/
abbrev of (α : Type*) [DistribLattice α] [BoundedOrder α] [Fintype α] : FinBddDistLat where
  carrier := α

/--
Definition of `of'` / `of'` 的定义

English:
abbreviation of'
  signature: (α : Type*) [DistribLattice α] [Fintype α] [Nonempty α]
  body: α
  isBoundedOrder := Fintype.toBoundedOrder α

中文:
缩写 of'
  签名: (α : 类型) [DistribLattice α] [Fintype α] [Nonempty α]
  定义体: α
  isBoundedOrder := Fintype.toBoundedOrder α
-/
abbrev of' (α : Type*) [DistribLattice α] [Fintype α] [Nonempty α] : FinBddDistLat where
  carrier := α
  isBoundedOrder := Fintype.toBoundedOrder α

/-- The type of morphisms in `FinBddDistLat R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : FinBddDistLat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : BoundedLatticeHom X Y

中文:
结构 Hom
  参数: (X Y : FinBddDistLat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : BoundedLatticeHom X Y
-/
structure Hom (X Y : FinBddDistLat.{u}) where
  private mk ::
  /-- The underlying `BoundedLatticeHom`. -/
  hom' : BoundedLatticeHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category FinBddDistLat.{u}
  body: Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category FinBddDistLat.{u}
  定义体: Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category FinBddDistLat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory FinBddDistLat (BoundedLatticeHom · ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory FinBddDistLat (BoundedLatticeHom · ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory FinBddDistLat (BoundedLatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : FinBddDistLat.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := FinBddDistLat) f

中文:
缩写 Hom.hom
  签名: {X Y : FinBddDistLat.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := FinBddDistLat) f
-/
abbrev Hom.hom {X Y : FinBddDistLat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := FinBddDistLat) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
  body: ConcreteCategory.ofHom (C := FinBddDistLat) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
  定义体: ConcreteCategory.ofHom (C := FinBddDistLat) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, FinBddDistLat
-/
abbrev ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y]
    (f : BoundedLatticeHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := FinBddDistLat) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : FinBddDistLat.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : FinBddDistLat.{u}) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : FinBddDistLat.{u}) (f : Hom X Y) :=
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
  given: {X : FinBddDistLat}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[simp]

中文:
引理 coe_id
  条件: {X : FinBddDistLat}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[simp]
-/
lemma coe_id {X : FinBddDistLat} : (𝟙 X : X -> X) = id := rfl

@[simp]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : FinBddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[simp]

中文:
引理 coe_comp
  条件: {X Y Z : FinBddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[simp]
-/
lemma coe_comp {X Y Z : FinBddDistLat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[simp]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y : FinBddDistLat} (f : X ⟶ Y)
  proof: rfl

@[ext]

中文:
引理 forget_map
  条件: {X Y : FinBddDistLat} (f : X ⟶ Y)
  证明: rfl

@[ext]
-/
lemma forget_map {X Y : FinBddDistLat} (f : X ⟶ Y) :
    (forget FinBddDistLat).map f = (f : _ -> _) := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : FinBddDistLat} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

@[simp]

中文:
引理 ext
  条件: {X Y : FinBddDistLat} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : FinBddDistLat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : FinBddDistLat}
  statement: (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _
  proof: rfl

中文:
引理 hom_id
  条件: {X : FinBddDistLat}
  结论: (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _
  证明: rfl
-/
lemma hom_id {X : FinBddDistLat} : (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _ := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : FinBddDistLat) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : FinBddDistLat) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : FinBddDistLat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_comp {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp

@[ext]
-/
lemma comp_apply {X Y Z : FinBddDistLat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : FinBddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {X Y : FinBddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : FinBddDistLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  statement: {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  结论: {X Y : 类型u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y] (f : BoundedLatticeHom X Y) : (ofHom f).hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : FinBddDistLat} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : FinBddDistLat} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : FinBddDistLat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X]
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型u} [DistribLattice X] [BoundedOrder X] [Fintype X]
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] :
    ofHom (BoundedLatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y] [DistribLattice Z] [BoundedOrder Z] [Fintype Z]
    (f : BoundedLatticeHom X Y) (g : BoundedLatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {X Y : 类型u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [DistribLattice X] [BoundedOrder X] [Fintype X] [DistribLattice Y]
    [BoundedOrder Y] [Fintype Y]
    (f : BoundedLatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : FinBddDistLat} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : FinBddDistLat} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : FinBddDistLat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : FinBddDistLat} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {X Y : FinBddDistLat} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {X Y : FinBddDistLat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited FinBddDistLat
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: Inhabited FinBddDistLat
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited FinBddDistLat :=
  ⟨of PUnit⟩

/--
Instance `hasForgetToBddDistLat` / 实例 `hasForgetToBddDistLat`

English:
instance hasForgetToBddDistLat
  signature: : HasForget₂ FinBddDistLat BddDistLat where
  body: .of X
  forget₂.map f := BddDistLat.ofHom f.hom

中文:
实例 hasForgetToBddDistLat
  签名: : HasForget₂ FinBddDistLat BddDistLat where
  定义体: .of X
  forget₂.map f := BddDistLat.ofHom f.hom
-/
instance hasForgetToBddDistLat : HasForget₂ FinBddDistLat BddDistLat where
  forget₂.obj X := .of X
  forget₂.map f := BddDistLat.ofHom f.hom

/--
Instance `hasForgetToFinPartOrd` / 实例 `hasForgetToFinPartOrd`

English:
instance hasForgetToFinPartOrd
  signature: : HasForget₂ FinBddDistLat FinPartOrd where
  body: .of X
  forget₂.map f := ConcreteCategory.ofHom (OrderHomClass.toOrderHom f.hom)

中文:
实例 hasForgetToFinPartOrd
  签名: : HasForget₂ FinBddDistLat FinPartOrd where
  定义体: .of X
  forget₂.map f := ConcreteCategory.ofHom (OrderHomClass.toOrderHom f.hom)
-/
instance hasForgetToFinPartOrd : HasForget₂ FinBddDistLat FinPartOrd where
  forget₂.obj X := .of X
  forget₂.map f := ConcreteCategory.ofHom (OrderHomClass.toOrderHom f.hom)

/-- Constructs an equivalence between finite distributive lattices from an order isomorphism
between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : FinBddDistLat.{u}} (e : α.carrier ≃o β.carrier)
  body: ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

中文:
定义 Iso.mk
  签名: {α β : FinBddDistLat.{u}} (e : α.carrier ≃o β.carrier)
  定义体: ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
-/
def Iso.mk {α β : FinBddDistLat.{u}} (e : α.carrier ≃o β.carrier) : α ≅ β where
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
  signature: : FinBddDistLat ⥤ FinBddDistLat where
  body: of Xᵒᵈ
  map f := ofHom f.hom.dual

中文:
定义 dual
  签名: : FinBddDistLat ⥤ FinBddDistLat where
  定义体: of Xᵒᵈ
  map f := ofHom f.hom.dual
-/
def dual : FinBddDistLat ⥤ FinBddDistLat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `FinBddDistLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : FinBddDistLat ≌ FinBddDistLat where
  body: dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk (α := X) <| OrderIso.dualDual X)
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X)

中文:
定义 dualEquiv
  签名: : FinBddDistLat ≌ FinBddDistLat where
  定义体: dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk (α := X) <| OrderIso.dualDual X)
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X)
-/
def dualEquiv : FinBddDistLat ≌ FinBddDistLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents (fun X => Iso.mk (α := X) <| OrderIso.dualDual X)
  counitIso := NatIso.ofComponents (fun X => Iso.mk <| OrderIso.dualDual X)

end FinBddDistLat

/--
theorem `finBddDistLat_dual_comp_forget_to_bddDistLat` / 定理 `finBddDistLat_dual_comp_forget_to_bddDistLat`

English:
theorem finBddDistLat_dual_comp_forget_to_bddDistLat
  proof: rfl

中文:
定理 finBddDistLat_dual_comp_forget_to_bddDistLat
  证明: rfl
-/
theorem finBddDistLat_dual_comp_forget_to_bddDistLat :
    FinBddDistLat.dual ⋙ forget₂ FinBddDistLat BddDistLat =
      forget₂ FinBddDistLat BddDistLat ⋙ BddDistLat.dual :=
  rfl
