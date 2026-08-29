/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.Category.Bipointed
public import Mathlib.Order.Category.PartOrd
public import Mathlib.Order.Hom.Bounded

/-!
# The category of bounded orders

This defines `BddOrd`, the category of bounded orders.
-/

@[expose] public section


universe u v

open CategoryTheory

/--
Definition of `BddOrd` / `BddOrd` 的定义

English:
structure BddOrd
  parameters: extends PartOrd
  extends: PartOrd
  axioms and operations (1):
    - [isBoundedOrder : BoundedOrder toPartOrd]

中文:
结构 有界序
  参数: extends 偏序
  继承: 偏序
  公理与运算 (1 个):
    - [isBoundedOrder : 有界序 toPartOrd]
-/
structure BddOrd extends PartOrd where
  [isBoundedOrder : BoundedOrder toPartOrd]

/-- The underlying object in the category of partial orders. -/
add_decl_doc BddOrd.toPartOrd

attribute [instance] BddOrd.isBoundedOrder

initialize_simps_projections BddOrd (carrier -> coe, -str)

namespace BddOrd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort BddOrd Type*
  body: InducedCategory.hasCoeToSort toPartOrd

中文:
实例 :
  签名: CoeSort 有界序 类型
  定义体: InducedCategory.hasCoeToSort toPartOrd

Depends on / 依赖: InducedCategory, InducedCategory.hasCoeToSort, hasCoeToSort, toPartOrd
-/
instance : CoeSort BddOrd Type* :=
  InducedCategory.hasCoeToSort toPartOrd

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type*) [PartialOrder X] [BoundedOrder X]
  body: X

中文:
缩写 of
  签名: (X : 类型) [偏序 X] [有界序 X]
  定义体: X
-/
abbrev of (X : Type*) [PartialOrder X] [BoundedOrder X] : BddOrd where
  carrier := X

/-- The type of morphisms in `BddOrd R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : BddOrd.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : BoundedOrderHom X Y

中文:
结构 态射
  参数: (X Y : 有界序.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : 有界序态射 X Y
-/
structure Hom (X Y : BddOrd.{u}) where
  private mk ::
  /-- The underlying `BoundedOrderHom`. -/
  hom' : BoundedOrderHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category BddOrd.{u}
  body: Hom X Y
  id _ := ⟨BoundedOrderHom.id _⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 有界序.{u}
  定义体: Hom X Y
  id _ := ⟨BoundedOrderHom.id _⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category BddOrd.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨BoundedOrderHom.id _⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory BddOrd (BoundedOrderHom · ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴 有界序 (有界序态射 · ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory BddOrd (BoundedOrderHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : BddOrd.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := BddOrd) f

中文:
缩写 态射.hom
  签名: {X Y : 有界序.{u}} (f : 态射 X Y)
  定义体: ConcreteCategory.hom (C := BddOrd) f
-/
abbrev Hom.hom {X Y : BddOrd.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BddOrd) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y] [BoundedOrder Y]
  body: ConcreteCategory.ofHom (C := BddOrd) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [偏序 X] [有界序 X] [偏序 Y] [有界序 Y]
  定义体: ConcreteCategory.ofHom (C := BddOrd) f

Depends on / 依赖: BddOrd, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y] [BoundedOrder Y]
    (f : BoundedOrderHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := BddOrd) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : BddOrd.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (X Y : 有界序.{u}) (f : 态射 X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : BddOrd.{u}) (f : Hom X Y) :=
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
  given: {X : BddOrd}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[simp]

中文:
引理 coe_id
  条件: {X : 有界序}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[simp]
-/
lemma coe_id {X : BddOrd} : (𝟙 X : X -> X) = id := rfl

@[simp]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : BddOrd} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[simp]

中文:
引理 coe_comp
  条件: {X Y Z : 有界序} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[simp]
-/
lemma coe_comp {X Y Z : BddOrd} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[simp]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y : BddOrd} (f : X ⟶ Y)
  proof: rfl

@[ext]

中文:
引理 forget_map
  条件: {X Y : 有界序} (f : X ⟶ Y)
  证明: rfl

@[ext]
-/
lemma forget_map {X Y : BddOrd} (f : X ⟶ Y) :
    (forget BddOrd).map f = (f : _ -> _) := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : BddOrd} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

中文:
引理 ext
  条件: {X Y : 有界序} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : BddOrd} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [PartialOrder X] [BoundedOrder X]
  statement: (BddOrd.of X : Type u) = X
  proof: rfl

@[simp]

中文:
定理 coe_of
  条件: (X : 类型u) [偏序 X] [有界序 X]
  结论: (有界序.of X : 类型u) = X
  证明: rfl

@[simp]
-/
theorem coe_of (X : Type u) [PartialOrder X] [BoundedOrder X] : (BddOrd.of X : Type u) = X := rfl

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : BddOrd}
  statement: (𝟙 X : X ⟶ X).hom = BoundedOrderHom.id _
  proof: rfl

中文:
引理 hom_id
  条件: {X : 有界序}
  结论: (𝟙 X : X ⟶ X).hom = 有界序态射.id _
  证明: rfl
-/
lemma hom_id {X : BddOrd} : (𝟙 X : X ⟶ X).hom = BoundedOrderHom.id _ := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : BddOrd) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : 有界序) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : BddOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : BddOrd} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : 有界序} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_comp {X Y Z : BddOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : BddOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {X Y Z : 有界序} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp

@[ext]
-/
lemma comp_apply {X Y Z : BddOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : BddOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {X Y : 有界序} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : BddOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  statement: {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y] [BoundedOrder Y]
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  结论: {X Y : 类型u} [偏序 X] [有界序 X] [偏序 Y] [有界序 Y]
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y] [BoundedOrder Y]
    (f : BoundedOrderHom X Y) :
    (ofHom f).hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : BddOrd} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : 有界序} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : BddOrd} (f : X ⟶ Y) :
    ofHom f.hom = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [PartialOrder X] [BoundedOrder X]
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型u} [偏序 X] [有界序 X]
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type u} [PartialOrder X] [BoundedOrder X] :
    ofHom (BoundedOrderHom.id _) = 𝟙 (of X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [偏序 X] [有界序 X] [偏序 Y]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y]
    [BoundedOrder Y] [PartialOrder Z] [BoundedOrder Z]
    (f : BoundedOrderHom X Y) (g : BoundedOrderHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y] [BoundedOrder Y]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {X Y : 类型u} [偏序 X] [有界序 X] [偏序 Y] [有界序 Y]
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y] [BoundedOrder Y]
    (f : BoundedOrderHom X Y) (x : X) :
    ofHom f x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : BddOrd} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : 有界序} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : BddOrd} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : BddOrd} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {X Y : 有界序} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {X Y : BddOrd} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited BddOrd
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 有界序
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited BddOrd :=
  ⟨of PUnit⟩

/--
Instance `hasForgetToPartOrd` / 实例 `hasForgetToPartOrd`

English:
instance hasForgetToPartOrd
  signature: : HasForget₂ BddOrd PartOrd where
  body: X.toPartOrd
  forget₂.map f := PartOrd.ofHom f.hom.toOrderHom

中文:
实例 hasForgetToPartOrd
  签名: : 有Forget₂ 有界序 偏序 where
  定义体: X.toPartOrd
  forget₂.map f := PartOrd.ofHom f.hom.toOrderHom

Depends on / 依赖: X.toPartOrd, toPartOrd
-/
instance hasForgetToPartOrd : HasForget₂ BddOrd PartOrd where
  forget₂.obj X := X.toPartOrd
  forget₂.map f := PartOrd.ofHom f.hom.toOrderHom

/--
Instance `hasForgetToBipointed` / 实例 `hasForgetToBipointed`

English:
instance hasForgetToBipointed
  signature: : HasForget₂ BddOrd Bipointed where
  body: { obj := fun X => ⟨X, ⊥, ⊤⟩
      map := fun f => ⟨f, f.hom.map_bot', f.hom.map_top'⟩ }
  forget_comp := rfl

中文:
实例 hasForgetToBipointed
  签名: : 有Forget₂ 有界序 Bipointed where
  定义体: { obj := fun X => ⟨X, ⊥, ⊤⟩
      map := fun f => ⟨f, f.hom.map_bot', f.hom.map_top'⟩ }
  forget_comp := rfl

Depends on / 依赖: f.hom.map_bot, f.hom.map_top, forget_comp, map_bot, map_top
-/
instance hasForgetToBipointed : HasForget₂ BddOrd Bipointed where
  forget₂ :=
    { obj := fun X => ⟨X, ⊥, ⊤⟩
      map := fun f => ⟨f, f.hom.map_bot', f.hom.map_top'⟩ }
  forget_comp := rfl

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : BddOrd ⥤ BddOrd where
  body: of Xᵒᵈ
  map f := ofHom f.hom.dual

中文:
定义 dual
  签名: : 有界序 ⥤ 有界序 where
  定义体: of Xᵒᵈ
  map f := ofHom f.hom.dual
-/
def dual : BddOrd ⥤ BddOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- Constructs an equivalence between bounded orders from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : BddOrd.{u}} (e : α ≃o β)
  body: ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

中文:
定义 同构.mk
  签名: {α β : 有界序.{u}} (e : α ≃o β)
  定义体: ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
-/
def Iso.mk {α β : BddOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- The equivalence between `BddOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : BddOrd ≌ BddOrd where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : 有界序 ≌ 有界序 where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
-/
def dualEquiv : BddOrd ≌ BddOrd where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

end BddOrd

/--
theorem `bddOrd_dual_comp_forget_to_partOrd` / 定理 `bddOrd_dual_comp_forget_to_partOrd`

English:
theorem bddOrd_dual_comp_forget_to_partOrd
  proof: rfl

中文:
定理 bddOrd_dual_comp_forget_to_partOrd
  证明: rfl
-/
theorem bddOrd_dual_comp_forget_to_partOrd :
    BddOrd.dual ⋙ forget₂ BddOrd PartOrd =
    forget₂ BddOrd PartOrd ⋙ PartOrd.dual :=
  rfl

/--
theorem `bddOrd_dual_comp_forget_to_bipointed` / 定理 `bddOrd_dual_comp_forget_to_bipointed`

English:
theorem bddOrd_dual_comp_forget_to_bipointed
  proof: rfl

中文:
定理 bddOrd_dual_comp_forget_to_bipointed
  证明: rfl
-/
theorem bddOrd_dual_comp_forget_to_bipointed :
    BddOrd.dual ⋙ forget₂ BddOrd Bipointed =
    forget₂ BddOrd Bipointed ⋙ Bipointed.swap :=
  rfl
