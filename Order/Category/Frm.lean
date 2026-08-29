/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.Lat
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# The category of frames

This file defines `Frm`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/

@[expose] public section


universe u

open CategoryTheory Order

/--
Definition of `Frm` / `Frm` 的定义

English:
structure Frm
  parameters: where
  axioms and operations (3):
    - of : :
    - (carrier : Type*)
    - [str : Frame carrier]

中文:
结构 框架
  参数: where
  公理与运算 (3 个):
    - of : :
    - (carrier : 类型)
    - [str : 框架 carrier]
-/
structure Frm where
  /-- Construct a bundled `Frm` from the underlying type and typeclass. -/
  of ::
  /-- The underlying frame. -/
  (carrier : Type*)
  [str : Frame carrier]

attribute [instance] Frm.str

initialize_simps_projections Frm (carrier -> coe, -str)

namespace Frm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Frm (Type _)
  body: ⟨Frm.carrier⟩

中文:
实例 :
  签名: CoeSort 框架 (类型 _)
  定义体: ⟨Frm.carrier⟩

Depends on / 依赖: Frm.carrier, carrier
-/
instance : CoeSort Frm (Type _) :=
  ⟨Frm.carrier⟩

attribute [coe] Frm.carrier

/-- The type of morphisms in `Frm R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : Frm.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : FrameHom X Y

中文:
结构 态射
  参数: (X Y : 框架.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : 框架态射 X Y
-/
structure Hom (X Y : Frm.{u}) where
  private mk ::
  /-- The underlying `FrameHom`. -/
  hom' : FrameHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category Frm.{u}
  body: Hom X Y
  id X := ⟨FrameHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 框架.{u}
  定义体: Hom X Y
  id X := ⟨FrameHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category Frm.{u} where
  Hom X Y := Hom X Y
  id X := ⟨FrameHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory Frm (FrameHom · ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴 框架 (框架态射 · ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory Frm (FrameHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : Frm.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := Frm) f

中文:
缩写 态射.hom
  签名: {X Y : 框架.{u}} (f : 态射 X Y)
  定义体: ConcreteCategory.hom (C := Frm) f
-/
abbrev Hom.hom {X Y : Frm.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Frm) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y)
  body: ConcreteCategory.ofHom (C := Frm) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [框架 X] [框架 Y] (f : 框架态射 X Y)
  定义体: ConcreteCategory.ofHom (C := Frm) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Frm) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : Frm.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (X Y : 框架.{u}) (f : 态射 X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)

Depends on / 依赖: Quotient, Quotient.eq, Quotient.mk, QuotientGroup, QuotientGroup.rightRel, QuotientGroup.rightRel_apply, Rep.epi_iff_surjective, _surjective, epi_iff_surjective, mul_assoc, rightRel, rightRel_apply
-/
def Hom.Simps.hom (X Y : Frm.{u}) (f : Hom X Y) :=
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
  given: {X : Frm}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[simp]

中文:
引理 coe_id
  条件: {X : 框架}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[simp]
-/
lemma coe_id {X : Frm} : (𝟙 X : X -> X) = id := rfl

@[simp]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : Frm} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[simp]

中文:
引理 coe_comp
  条件: {X Y Z : 框架} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[simp]
-/
lemma coe_comp {X Y Z : Frm} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[simp]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y : Frm} (f : X ⟶ Y)
  proof: rfl

@[ext]

中文:
引理 forget_map
  条件: {X Y : 框架} (f : X ⟶ Y)
  证明: rfl

@[ext]

Depends on / 依赖: Rep.hom_ext, hom_ext
-/
lemma forget_map {X Y : Frm} (f : X ⟶ Y) :
    (forget Frm).map f = (f : _ -> _) := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : Frm} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

中文:
引理 ext
  条件: {X Y : 框架} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : Frm} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [Frame X]
  statement: (Frm.of X : Type u) = X
  proof: rfl

@[simp]

中文:
定理 coe_of
  条件: (X : 类型u) [框架 X]
  结论: (框架.of X : 类型u) = X
  证明: rfl

@[simp]
-/
theorem coe_of (X : Type u) [Frame X] : (Frm.of X : Type u) = X := rfl

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : Frm}
  statement: (𝟙 X : X ⟶ X).hom = FrameHom.id _
  proof: rfl

中文:
引理 hom_id
  条件: {X : 框架}
  结论: (𝟙 X : X ⟶ X).hom = 框架态射.id _
  证明: rfl
-/
lemma hom_id {X : Frm} : (𝟙 X : X ⟶ X).hom = FrameHom.id _ := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : Frm) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : 框架) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : Frm) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : 框架} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_comp {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {X Y Z : 框架} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp

@[ext]
-/
lemma comp_apply {X Y Z : Frm} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : Frm} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {X Y : 框架} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : Frm} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y)
  statement: (ofHom f).hom = f
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {X Y : 类型u} [框架 X] [框架 Y] (f : 框架态射 X Y)
  结论: (ofHom f).hom = f
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) : (ofHom f).hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : Frm} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : 框架} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : Frm} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [Frame X]
  statement: ofHom (FrameHom.id _) = 𝟙 (of X)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型u} [框架 X]
  结论: ofHom (框架态射.id _) = 𝟙 (of X)
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type u} [Frame X] : ofHom (FrameHom.id _) = 𝟙 (of X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [Frame X] [Frame Y] [Frame Z]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [框架 X] [框架 Y] [框架 Z]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type u} [Frame X] [Frame Y] [Frame Z]
    (f : FrameHom X Y) (g : FrameHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) (x : X)
  proof: rfl

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [框架 X] [框架 Y] (f : 框架态射 X Y) (x : X)
  证明: rfl

Depends on / 依赖: PreservesProjectiveObjects, S.subtype, subtype
-/
lemma ofHom_apply {X Y : Type u} [Frame X] [Frame Y] (f : FrameHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : Frm} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : 框架} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : Frm} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : Frm} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {X Y : 框架} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {X Y : Frm} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Frm
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 框架
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited Frm :=
  ⟨of PUnit⟩

/--
Instance `hasForgetToLat` / 实例 `hasForgetToLat`

English:
instance hasForgetToLat
  signature: : HasForget₂ Frm Lat where
  body: .of X
  forget₂.map f := Lat.ofHom f.hom

中文:
实例 hasForgetToLat
  签名: : 有Forget₂ 框架 格 where
  定义体: .of X
  forget₂.map f := Lat.ofHom f.hom
-/
instance hasForgetToLat : HasForget₂ Frm Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom f.hom

/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : Frm.{u}} (e : α ≃o β)
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 同构.mk
  签名: {α β : 框架.{u}} (e : α ≃o β)
  定义体: ofHom e
  inv := ofHom e.symm
-/
def Iso.mk {α β : Frm.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

end Frm
