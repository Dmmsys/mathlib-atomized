/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.PartOrd
public import Mathlib.Order.Hom.Lattice

/-!
# The category of lattices

This defines `Lat`, the category of lattices.

Note that `Lat` doesn't correspond to the literature definition of [`Lat`]
(https://ncatlab.org/nlab/show/Lat) as we don't require bottom or top elements. Instead, `Lat`
corresponds to `BddLat`.

## TODO

The free functor from `Lat` to `BddLat` is `X → WithTop (WithBot X)`.
-/

@[expose] public section

universe u

open CategoryTheory

/--
Definition of `Lat` / `Lat` 的定义

English:
structure Lat
  parameters: where
  axioms and operations (2):
    - (carrier : Type*)
    - [str : Lattice carrier]

中文:
结构 格
  参数: where
  公理与运算 (2 个):
    - (carrier : 类型)
    - [str : 格 carrier]
-/
structure Lat where
  /-- The underlying lattices. -/
  (carrier : Type*)
  [str : Lattice carrier]

attribute [instance] Lat.str

initialize_simps_projections Lat (carrier -> coe, -str)

namespace Lat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Lat (Type _)
  body: ⟨Lat.carrier⟩

中文:
实例 :
  签名: CoeSort 格 (类型 _)
  定义体: ⟨Lat.carrier⟩

Depends on / 依赖: Lat.carrier, carrier
-/
instance : CoeSort Lat (Type _) :=
  ⟨Lat.carrier⟩

attribute [coe] Lat.carrier

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type*) [Lattice X]
  body: ⟨X⟩

中文:
缩写 of
  签名: (X : 类型) [格 X]
  定义体: ⟨X⟩
-/
abbrev of (X : Type*) [Lattice X] : Lat := ⟨X⟩

/-- The type of morphisms in `Lat R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : Lat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : LatticeHom X Y

中文:
结构 态射
  参数: (X Y : 格.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : 格态射 X Y
-/
structure Hom (X Y : Lat.{u}) where
  private mk ::
  /-- The underlying `LatticeHom`. -/
  hom' : LatticeHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category Lat.{u}
  body: Hom X Y
  id X := ⟨LatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 格.{u}
  定义体: Hom X Y
  id X := ⟨LatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category Lat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨LatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory Lat (LatticeHom · ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴 格 (格态射 · ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory Lat (LatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : Lat.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := Lat) f

中文:
缩写 态射.hom
  签名: {X Y : 格.{u}} (f : 态射 X Y)
  定义体: ConcreteCategory.hom (C := Lat) f
-/
abbrev Hom.hom {X Y : Lat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Lat) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y)
  body: ConcreteCategory.ofHom (C := Lat) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [格 X] [格 Y] (f : 格态射 X Y)
  定义体: ConcreteCategory.ofHom (C := Lat) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Lat) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : Lat.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (X Y : 格.{u}) (f : 态射 X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : Lat.{u}) (f : Hom X Y) :=
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
  given: {X : Lat}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[simp]

中文:
引理 coe_id
  条件: {X : 格}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[simp]
-/
lemma coe_id {X : Lat} : (𝟙 X : X -> X) = id := rfl

@[simp]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : Lat} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[simp]

中文:
引理 coe_comp
  条件: {X Y Z : 格} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[simp]
-/
lemma coe_comp {X Y Z : Lat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[simp]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y : Lat} (f : X ⟶ Y)
  proof: rfl

@[ext]

中文:
引理 forget_map
  条件: {X Y : 格} (f : X ⟶ Y)
  证明: rfl

@[ext]
-/
lemma forget_map {X Y : Lat} (f : X ⟶ Y) :
    (forget Lat).map f = (f : _ -> _) := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : Lat} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

中文:
引理 ext
  条件: {X Y : 格} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : Lat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [Lattice X]
  statement: (Lat.of X : Type u) = X
  proof: rfl

@[simp]

中文:
定理 coe_of
  条件: (X : 类型u) [格 X]
  结论: (格.of X : 类型u) = X
  证明: rfl

@[simp]
-/
theorem coe_of (X : Type u) [Lattice X] : (Lat.of X : Type u) = X := rfl

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

Depends on / 依赖: Coinvariants, ModuleCat, ModuleCat.epi_iff_surjective, Representation, Representation.Coinvariants.mk_surjective, epi_iff_surjective, mk_surjective
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
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : Lat} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {X Y : 格} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : Lat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y)
  statement: (ofHom f).hom = f
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {X Y : 类型u} [格 X] [格 Y] (f : 格态射 X Y)
  结论: (ofHom f).hom = f
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) : (ofHom f).hom = f :=
  rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : Lat} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : 格} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : Lat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [Lattice X]
  statement: ofHom (LatticeHom.id _) = 𝟙 (of X)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型u} [格 X]
  结论: ofHom (格态射.id _) = 𝟙 (of X)
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type u} [Lattice X] : ofHom (LatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [Lattice X] [Lattice Y] [Lattice Z]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [格 X] [格 Y] [格 Z]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type u} [Lattice X] [Lattice Y] [Lattice Z]
    (f : LatticeHom X Y) (g : LatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) (x : X)
  proof: rfl

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [格 X] [格 Y] (f : 格态射 X Y) (x : X)
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [Lattice X] [Lattice Y] (f : LatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : Lat} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : 格} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : Lat} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : Lat} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {X Y : 格} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {X Y : Lat} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

/--
Instance `hasForgetToPartOrd` / 实例 `hasForgetToPartOrd`

English:
instance hasForgetToPartOrd
  signature: : HasForget₂ Lat PartOrd where
  body: .of X
  forget₂.map f := PartOrd.ofHom f.hom

中文:
实例 hasForgetToPartOrd
  签名: : 有Forget₂ 格 偏序 where
  定义体: .of X
  forget₂.map f := PartOrd.ofHom f.hom
-/
instance hasForgetToPartOrd : HasForget₂ Lat PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom f.hom

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : Lat.{u}} (e : α ≃o β)
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 同构.mk
  签名: {α β : 格.{u}} (e : α ≃o β)
  定义体: ofHom e
  inv := ofHom e.symm
-/
def Iso.mk {α β : Lat.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : Lat ⥤ Lat where
  body: of Xᵒᵈ
  map f := ofHom f.hom.dual

中文:
定义 dual
  签名: : 格 ⥤ 格 where
  定义体: of Xᵒᵈ
  map f := ofHom f.hom.dual
-/
def dual : Lat ⥤ Lat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `Lat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : Lat ≌ Lat where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : 格 ≌ 格 where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
-/
def dualEquiv : Lat ≌ Lat where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

end Lat

/--
theorem `Lat_dual_comp_forget_to_partOrd` / 定理 `Lat_dual_comp_forget_to_partOrd`

English:
theorem Lat_dual_comp_forget_to_partOrd
  proof: rfl

中文:
定理 Lat_dual_comp_forget_to_partOrd
  证明: rfl
-/
theorem Lat_dual_comp_forget_to_partOrd :
    Lat.dual ⋙ forget₂ Lat PartOrd = forget₂ Lat PartOrd ⋙ PartOrd.dual :=
  rfl
