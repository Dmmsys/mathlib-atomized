/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Order.Category.Lat

/-!
# Category of linear orders

This defines `LinOrd`, the category of linear orders with monotone maps.
-/

@[expose] public section


open CategoryTheory

universe u

namespace LinOrd

/-- The type of morphisms in `LinOrd R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : LinOrd.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : X ->o Y

中文:
结构 态射
  参数: (X Y : 线性序.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : X ->o Y
-/
structure Hom (X Y : LinOrd.{u}) where
  private mk ::
  /-- The underlying `OrderHom`. -/
  hom' : X ->o Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category LinOrd.{u}
  body: Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 线性序.{u}
  定义体: Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category LinOrd.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory LinOrd (· ->o ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴 线性序 (· ->o ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory LinOrd (· ->o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : LinOrd.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := LinOrd) f

中文:
缩写 态射.hom
  签名: {X Y : 线性序.{u}} (f : 态射 X Y)
  定义体: ConcreteCategory.hom (C := LinOrd) f
-/
abbrev Hom.hom {X Y : LinOrd.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := LinOrd) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X ->o Y)
  body: ConcreteCategory.ofHom (C := LinOrd) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [线性序 X] [线性序 Y] (f : X ->o Y)
  定义体: ConcreteCategory.ofHom (C := LinOrd) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, LinOrd
-/
abbrev ofHom {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X ->o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := LinOrd) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : LinOrd.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (X Y : 线性序.{u}) (f : 态射 X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : LinOrd.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)


/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: {X : LinOrd}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

中文:
引理 coe_id
  条件: {X : 线性序}
  结论: (𝟙 X : X -> X) = id
  证明: rfl
-/
lemma coe_id {X : LinOrd} : (𝟙 X : X -> X) = id := rfl

/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : LinOrd} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[simp]

中文:
引理 coe_comp
  条件: {X Y Z : 线性序} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[simp]
-/
lemma coe_comp {X Y Z : LinOrd} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[simp]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y : LinOrd} (f : X ⟶ Y)
  proof: rfl

@[ext]

中文:
引理 forget_map
  条件: {X Y : 线性序} (f : X ⟶ Y)
  证明: rfl

@[ext]
-/
lemma forget_map {X Y : LinOrd} (f : X ⟶ Y) :
    (forget LinOrd).map f = (f : _ -> _) := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : LinOrd} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

中文:
引理 ext
  条件: {X Y : 线性序} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : LinOrd} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [LinearOrder X]
  statement: (LinOrd.of X : Type u) = X
  proof: rfl

@[simp]

中文:
定理 coe_of
  条件: (X : 类型u) [线性序 X]
  结论: (线性序.of X : 类型u) = X
  证明: rfl

@[simp]
-/
theorem coe_of (X : Type u) [LinearOrder X] : (LinOrd.of X : Type u) = X := rfl

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : LinOrd}
  statement: (𝟙 X : X ⟶ X).hom = OrderHom.id
  proof: rfl

中文:
引理 hom_id
  条件: {X : 线性序}
  结论: (𝟙 X : X ⟶ X).hom = 序态射.id
  证明: rfl
-/
lemma hom_id {X : LinOrd} : (𝟙 X : X ⟶ X).hom = OrderHom.id := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : LinOrd) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : 线性序) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : LinOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : 线性序} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_comp {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {X Y Z : 线性序} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp

@[ext]
-/
lemma comp_apply {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : LinOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {X Y : 线性序} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : LinOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X ->o Y)
  statement: (ofHom f).hom = f
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {X Y : 类型u} [线性序 X] [线性序 Y] (f : X ->o Y)
  结论: (ofHom f).hom = f
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X ->o Y) : (ofHom f).hom = f :=
  rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : LinOrd} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : 线性序} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : LinOrd} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [LinearOrder X]
  statement: ofHom OrderHom.id = 𝟙 (of X)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型u} [线性序 X]
  结论: ofHom 序态射.id = 𝟙 (of X)
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type u} [LinearOrder X] : ofHom OrderHom.id = 𝟙 (of X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [LinearOrder X] [LinearOrder Y] [LinearOrder Z]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [线性序 X] [线性序 Y] [线性序 Z]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type u} [LinearOrder X] [LinearOrder Y] [LinearOrder Z]
    (f : X ->o Y) (g : Y ->o Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X ->o Y) (x : X)
  proof: rfl

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [线性序 X] [线性序 Y] (f : X ->o Y) (x : X)
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X ->o Y) (x : X) :
    (ofHom f) x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : LinOrd} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : 线性序} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : LinOrd} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : LinOrd} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {X Y : 线性序} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {X Y : LinOrd} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited LinOrd
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 线性序
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited LinOrd :=
  ⟨of PUnit⟩

/--
Instance `hasForgetToLat` / 实例 `hasForgetToLat`

English:
instance hasForgetToLat
  signature: : HasForget₂ LinOrd Lat where
  body: .of X
  forget₂.map f := Lat.ofHom (OrderHomClass.toLatticeHom _ _ f.hom)

中文:
实例 hasForgetToLat
  签名: : 有Forget₂ 线性序 格 where
  定义体: .of X
  forget₂.map f := Lat.ofHom (OrderHomClass.toLatticeHom _ _ f.hom)
-/
instance hasForgetToLat : HasForget₂ LinOrd Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom (OrderHomClass.toLatticeHom _ _ f.hom)

/-- Constructs an equivalence between linear orders from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : LinOrd.{u}} (e : α ≃o β)
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 同构.mk
  签名: {α β : 线性序.{u}} (e : α ≃o β)
  定义体: ofHom e
  inv := ofHom e.symm
-/
def Iso.mk {α β : LinOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : LinOrd ⥤ LinOrd where
  body: of Xᵒᵈ
  map f := ofHom f.hom.dual

中文:
定义 dual
  签名: : 线性序 ⥤ 线性序 where
  定义体: of Xᵒᵈ
  map f := ofHom f.hom.dual

Depends on / 依赖: FGModuleCat, FiniteDimensional, FiniteDimensional.of_injective, Functor, Functor.map_injective, mapLinearMap, map_injective, of_injective
-/
def dual : LinOrd ⥤ LinOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `LinOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : LinOrd ≌ LinOrd where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : 线性序 ≌ 线性序 where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
-/
def dualEquiv : LinOrd ≌ LinOrd where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

end LinOrd

/--
theorem `linOrd_dual_comp_forget_to_Lat` / 定理 `linOrd_dual_comp_forget_to_Lat`

English:
theorem linOrd_dual_comp_forget_to_Lat
  proof: rfl

中文:
定理 linOrd_dual_comp_forget_to_Lat
  证明: rfl
-/
theorem linOrd_dual_comp_forget_to_Lat :
    LinOrd.dual ⋙ forget₂ LinOrd Lat = forget₂ LinOrd Lat ⋙ Lat.dual :=
  rfl
