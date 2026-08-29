/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.Category.Pointed

/-!
# The category of bipointed types

This defines `Bipointed`, the category of bipointed types.

## TODO

Monoidal structure
-/

@[expose] public section


open CategoryTheory

universe u

/--
Definition of `Bipointed` / `Bipointed` 的定义

English:
structure Bipointed
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - X : Type u
    - toProd : X × X

中文:
结构 Bipointed
  参数: : Type (u + 1) where
  公理与运算 (2 个):
    - X : 类型u
    - toProd : X × X
-/
structure Bipointed : Type (u + 1) where
  /-- The underlying type of a bipointed type. -/
  protected X : Type u
  /-- The two points of a bipointed type, bundled together as a pair. -/
  toProd : X × X

namespace Bipointed

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Bipointed Type*
  body: ⟨Bipointed.X⟩

中文:
实例 :
  签名: CoeSort Bipointed 类型
  定义体: ⟨Bipointed.X⟩

Depends on / 依赖: Bipointed, Bipointed.X
-/
instance : CoeSort Bipointed Type* := ⟨Bipointed.X⟩

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: {X : Type*} (to_prod : X × X)
  body: ⟨X, to_prod⟩

中文:
缩写 of
  签名: {X : 类型} (to_prod : X × X)
  定义体: ⟨X, to_prod⟩

Depends on / 依赖: to_prod
-/
abbrev of {X : Type*} (to_prod : X × X) : Bipointed :=
  ⟨X, to_prod⟩

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: {X : Type*} (to_prod : X × X)
  statement: ↥(of to_prod) = X
  proof: rfl

alias _root_.Prod.Bipointed := of

中文:
定理 coe_of
  条件: {X : 类型} (to_prod : X × X)
  结论: ↥(of to_prod) = X
  证明: rfl

alias _root_.Prod.Bipointed := of
-/
theorem coe_of {X : Type*} (to_prod : X × X) : ↥(of to_prod) = X :=
  rfl

alias _root_.Prod.Bipointed := of

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Bipointed
  body: ⟨of ((), ())⟩

中文:
实例 :
  签名: Inhabited Bipointed
  定义体: ⟨of ((), ())⟩
-/
instance : Inhabited Bipointed :=
  ⟨of ((), ())⟩

/-- Morphisms in `Bipointed`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : Bipointed.{u})
  axioms and operations (3):
    - toFun : X -> Y
    - map_fst : toFun X.toProd.1 = Y.toProd.1
    - map_snd : toFun X.toProd.2 = Y.toProd.2

中文:
结构 Hom
  参数: (X Y : Bipointed.{u})
  公理与运算 (3 个):
    - toFun : X -> Y
    - map_fst : toFun X.toProd.1 = Y.toProd.1
    - map_snd : toFun X.toProd.2 = Y.toProd.2
-/
protected structure Hom (X Y : Bipointed.{u}) : Type u where
  /-- The underlying function of a morphism of bipointed types. -/
  toFun : X -> Y
  map_fst : toFun X.toProd.1 = Y.toProd.1
  map_snd : toFun X.toProd.2 = Y.toProd.2

namespace Hom

/-- The identity morphism of `X : Bipointed`. -/
@[simps]
nonrec def id (X : Bipointed) : Bipointed.Hom X X :=
  ⟨id, rfl, rfl⟩

instance (X : Bipointed) : Inhabited (Bipointed.Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `Bipointed`. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {X Y Z : Bipointed.{u}} (f : Bipointed.Hom X Y) (g : Bipointed.Hom Y Z)
  body: ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_fst, g.map_fst], by
    rw [Function.comp_apply]; rw [f.map_snd]; rw [g.map_snd]⟩

中文:
定义 comp
  签名: {X Y Z : Bipointed.{u}} (f : Bipointed.Hom X Y) (g : Bipointed.Hom Y Z)
  定义体: ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_fst, g.map_fst], by
    rw [Function.comp_apply]; rw [f.map_snd]; rw [g.map_snd]⟩

Depends on / 依赖: Function, Function.comp_apply, comp_apply, f.map_fst, f.map_snd, f.toFun, g.map_fst, g.map_snd, g.toFun, map_fst, map_snd
-/
def comp {X Y Z : Bipointed.{u}} (f : Bipointed.Hom X Y) (g : Bipointed.Hom Y Z) :
    Bipointed.Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_fst, g.map_fst], by
    rw [Function.comp_apply]; rw [f.map_snd]; rw [g.map_snd]⟩

end Hom

/--
Instance `largeCategory` / 实例 `largeCategory`

English:
instance largeCategory
  signature: : LargeCategory Bipointed where
  body: Bipointed.Hom
  id := Hom.id
  comp := @Hom.comp

中文:
实例 largeCategory
  签名: : LargeCategory Bipointed where
  定义体: Bipointed.Hom
  id := Hom.id
  comp := @Hom.comp

Depends on / 依赖: Bipointed, Bipointed.Hom
-/
instance largeCategory : LargeCategory Bipointed where
  Hom := Bipointed.Hom
  id := Hom.id
  comp := @Hom.comp

/--
Definition of `HomSubtype` / `HomSubtype` 的定义

English:
abbreviation HomSubtype
  signature: (X Y : Bipointed)
  body: { f : X -> Y // f X.toProd.1 = Y.toProd.1 ∧ f X.toProd.2 = Y.toProd.2 }

中文:
缩写 HomSubtype
  签名: (X Y : Bipointed)
  定义体: { f : X -> Y // f X.toProd.1 = Y.toProd.1 ∧ f X.toProd.2 = Y.toProd.2 }

Depends on / 依赖: X.toProd, Y.toProd, toProd
-/
abbrev HomSubtype (X Y : Bipointed) :=
  { f : X -> Y // f X.toProd.1 = Y.toProd.1 ∧ f X.toProd.2 = Y.toProd.2 }

instance (X Y : Bipointed) : FunLike (HomSubtype X Y) X Y where
  coe f := f
  coe_injective _ _ := Subtype.ext

/--
Instance `hasForget` / 实例 `hasForget`

English:
instance hasForget
  signature: : ConcreteCategory Bipointed HomSubtype where
  body: ⟨f.1, ⟨f.2, f.3⟩⟩
  ofHom f := ⟨f.1, f.2.1, f.2.2⟩

中文:
实例 hasForget
  签名: : ConcreteCategory Bipointed HomSubtype where
  定义体: ⟨f.1, ⟨f.2, f.3⟩⟩
  ofHom f := ⟨f.1, f.2.1, f.2.2⟩
-/
instance hasForget : ConcreteCategory Bipointed HomSubtype where
  hom f := ⟨f.1, ⟨f.2, f.3⟩⟩
  ofHom f := ⟨f.1, f.2.1, f.2.2⟩

/-- Swaps the pointed elements of a bipointed type. `Prod.swap` as a functor. -/
@[simps]
/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: : Bipointed ⥤ Bipointed where
  body: ⟨X, X.toProd.swap⟩
  map f := ⟨f.toFun, f.map_snd, f.map_fst⟩

#adaptation_note

中文:
定义 swap
  签名: : Bipointed ⥤ Bipointed where
  定义体: ⟨X, X.toProd.swap⟩
  map f := ⟨f.toFun, f.map_snd, f.map_fst⟩

#adaptation_note

Depends on / 依赖: X.toProd.swap, toProd
-/
def swap : Bipointed ⥤ Bipointed where
  obj X := ⟨X, X.toProd.swap⟩
  map f := ⟨f.toFun, f.map_snd, f.map_fst⟩

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence between `Bipointed` and itself induced by `Prod.swap` both ways. -/
@[simps!]
/--
Definition of `swapEquiv` / `swapEquiv` 的定义

English:
definition swapEquiv
  signature: : Bipointed ≌ Bipointed where
  body: swap
  inverse := swap
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]

中文:
定义 swapEquiv
  签名: : Bipointed ≌ Bipointed where
  定义体: swap
  inverse := swap
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
-/
def swapEquiv : Bipointed ≌ Bipointed where
  functor := swap
  inverse := swap
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
/--
theorem `swapEquiv_symm` / 定理 `swapEquiv_symm`

English:
theorem swapEquiv_symm
  statement: swapEquiv.symm = swapEquiv
  proof: rfl

中文:
定理 swapEquiv_symm
  结论: swapEquiv.symm = swapEquiv
  证明: rfl
-/
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl

end Bipointed

/--
Definition of `bipointedToPointedFst` / `bipointedToPointedFst` 的定义

English:
definition bipointedToPointedFst
  signature: : Bipointed ⥤ Pointed where
  body: ⟨X, X.toProd.1⟩
  map f := ⟨f.toFun, f.map_fst⟩

中文:
定义 bipointedToPointedFst
  签名: : Bipointed ⥤ Pointed where
  定义体: ⟨X, X.toProd.1⟩
  map f := ⟨f.toFun, f.map_fst⟩

Depends on / 依赖: X.toProd, toProd
-/
def bipointedToPointedFst : Bipointed ⥤ Pointed where
  obj X := ⟨X, X.toProd.1⟩
  map f := ⟨f.toFun, f.map_fst⟩

/--
Definition of `bipointedToPointedSnd` / `bipointedToPointedSnd` 的定义

English:
definition bipointedToPointedSnd
  signature: : Bipointed ⥤ Pointed where
  body: ⟨X, X.toProd.2⟩
  map f := ⟨f.toFun, f.map_snd⟩

@[simp]

中文:
定义 bipointedToPointedSnd
  签名: : Bipointed ⥤ Pointed where
  定义体: ⟨X, X.toProd.2⟩
  map f := ⟨f.toFun, f.map_snd⟩

@[simp]

Depends on / 依赖: X.toProd, toProd
-/
def bipointedToPointedSnd : Bipointed ⥤ Pointed where
  obj X := ⟨X, X.toProd.2⟩
  map f := ⟨f.toFun, f.map_snd⟩

@[simp]
/--
theorem `bipointedToPointedFst_comp_forget` / 定理 `bipointedToPointedFst_comp_forget`

English:
theorem bipointedToPointedFst_comp_forget
  proof: rfl

@[simp]

中文:
定理 bipointedToPointedFst_comp_forget
  证明: rfl

@[simp]
-/
theorem bipointedToPointedFst_comp_forget :
    bipointedToPointedFst ⋙ forget Pointed = forget Bipointed :=
  rfl

@[simp]
/--
theorem `bipointedToPointedSnd_comp_forget` / 定理 `bipointedToPointedSnd_comp_forget`

English:
theorem bipointedToPointedSnd_comp_forget
  proof: rfl

@[simp]

中文:
定理 bipointedToPointedSnd_comp_forget
  证明: rfl

@[simp]
-/
theorem bipointedToPointedSnd_comp_forget :
    bipointedToPointedSnd ⋙ forget Pointed = forget Bipointed :=
  rfl

@[simp]
/--
theorem `swap_comp_bipointedToPointedFst` / 定理 `swap_comp_bipointedToPointedFst`

English:
theorem swap_comp_bipointedToPointedFst
  proof: rfl

@[simp]

中文:
定理 swap_comp_bipointedToPointedFst
  证明: rfl

@[simp]
-/
theorem swap_comp_bipointedToPointedFst :
    Bipointed.swap ⋙ bipointedToPointedFst = bipointedToPointedSnd :=
  rfl

@[simp]
/--
theorem `swap_comp_bipointedToPointedSnd` / 定理 `swap_comp_bipointedToPointedSnd`

English:
theorem swap_comp_bipointedToPointedSnd
  proof: rfl

中文:
定理 swap_comp_bipointedToPointedSnd
  证明: rfl
-/
theorem swap_comp_bipointedToPointedSnd :
    Bipointed.swap ⋙ bipointedToPointedSnd = bipointedToPointedFst :=
  rfl

/--
Definition of `pointedToBipointed` / `pointedToBipointed` 的定义

English:
definition pointedToBipointed
  signature: : Pointed.{u} ⥤ Bipointed where
  body: ⟨X, X.point, X.point⟩
  map f := ⟨f.toFun, f.map_point, f.map_point⟩

中文:
定义 pointedToBipointed
  签名: : Pointed.{u} ⥤ Bipointed where
  定义体: ⟨X, X.point, X.point⟩
  map f := ⟨f.toFun, f.map_point, f.map_point⟩

Depends on / 依赖: X.point
-/
def pointedToBipointed : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨X, X.point, X.point⟩
  map f := ⟨f.toFun, f.map_point, f.map_point⟩

/--
Definition of `pointedToBipointedFst` / `pointedToBipointedFst` 的定义

English:
definition pointedToBipointedFst
  signature: : Pointed.{u} ⥤ Bipointed where
  body: ⟨Option X, X.point, none⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

中文:
定义 pointedToBipointedFst
  签名: : Pointed.{u} ⥤ Bipointed where
  定义体: ⟨Option X, X.point, none⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

Depends on / 依赖: X.point
-/
def pointedToBipointedFst : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨Option X, X.point, none⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

/--
Definition of `pointedToBipointedSnd` / `pointedToBipointedSnd` 的定义

English:
definition pointedToBipointedSnd
  signature: : Pointed.{u} ⥤ Bipointed where
  body: ⟨Option X, none, X.point⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

@[simp]

中文:
定义 pointedToBipointedSnd
  签名: : Pointed.{u} ⥤ Bipointed where
  定义体: ⟨Option X, none, X.point⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

@[simp]

Depends on / 依赖: X.point
-/
def pointedToBipointedSnd : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨Option X, none, X.point⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

@[simp]
/--
theorem `pointedToBipointedFst_comp_swap` / 定理 `pointedToBipointedFst_comp_swap`

English:
theorem pointedToBipointedFst_comp_swap
  proof: rfl

@[simp]

中文:
定理 pointedToBipointedFst_comp_swap
  证明: rfl

@[simp]
-/
theorem pointedToBipointedFst_comp_swap :
    pointedToBipointedFst ⋙ Bipointed.swap = pointedToBipointedSnd :=
  rfl

@[simp]
/--
theorem `pointedToBipointedSnd_comp_swap` / 定理 `pointedToBipointedSnd_comp_swap`

English:
theorem pointedToBipointedSnd_comp_swap
  proof: rfl

中文:
定理 pointedToBipointedSnd_comp_swap
  证明: rfl
-/
theorem pointedToBipointedSnd_comp_swap :
    pointedToBipointedSnd ⋙ Bipointed.swap = pointedToBipointedFst :=
  rfl

/-- `BipointedToPointed_fst` is inverse to `PointedToBipointed`. -/
@[simps!]
/--
Definition of `pointedToBipointedCompBipointedToPointedFst` / `pointedToBipointedCompBipointedToPointedFst` 的定义

English:
definition pointedToBipointedCompBipointedToPointedFst
  signature: :
  body: NatIso.ofComponents fun X =>
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

中文:
定义 pointedToBipointedCompBipointedToPointedFst
  签名: :
  定义体: NatIso.ofComponents fun X =>
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def pointedToBipointedCompBipointedToPointedFst :
    pointedToBipointed ⋙ bipointedToPointedFst ≅ 𝟭 _ :=
  NatIso.ofComponents fun X =>
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

/-- `BipointedToPointed_snd` is inverse to `PointedToBipointed`. -/
@[simps!]
/--
Definition of `pointedToBipointedCompBipointedToPointedSnd` / `pointedToBipointedCompBipointedToPointedSnd` 的定义

English:
definition pointedToBipointedCompBipointedToPointedSnd
  signature: :
  body: NatIso.ofComponents fun X =>
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

中文:
定义 pointedToBipointedCompBipointedToPointedSnd
  签名: :
  定义体: NatIso.ofComponents fun X =>
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def pointedToBipointedCompBipointedToPointedSnd :
    pointedToBipointed ⋙ bipointedToPointedSnd ≅ 𝟭 _ :=
  NatIso.ofComponents fun X =>
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

/--
Definition of `pointedToBipointedFstBipointedToPointedFstAdjunction` / `pointedToBipointedFstBipointedToPointedFstAdjunction` 的定义

English:
definition pointedToBipointedFstBipointedToPointedFstAdjunction
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            funext x
         

中文:
定义 pointedToBipointedFstBipointedToPointedFstAdjunction
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            funext x
         

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Bipointed, Bipointed.Hom.ext, Option.some, Y.toProd, f.map_fst, f.map_point, f.map_snd.symm, f.toFun, homEquiv, homEquiv_naturality_left_symm, invFun, left_inv, map_fst, map_point, map_snd, mkOfHomEquiv, o.elim, toProd
-/
def pointedToBipointedFstBipointedToPointedFstAdjunction :
    pointedToBipointedFst ⊣ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            funext x
            cases x
            · exact f.map_snd.symm
            · rfl }
      homEquiv_naturality_left_symm := fun f g => by
        apply Bipointed.Hom.ext
        funext x
        cases x <;> rfl }

/--
Definition of `pointedToBipointedSndBipointedToPointedSndAdjunction` / `pointedToBipointedSndBipointedToPointedSndAdjunction` 的定义

English:
definition pointedToBipointedSndBipointedToPointedSndAdjunction
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            funext x
         

中文:
定义 pointedToBipointedSndBipointedToPointedSndAdjunction
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            funext x
         

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Bipointed, Bipointed.Hom.ext, Option.some, Y.toProd, f.map_fst.symm, f.map_point, f.map_snd, f.toFun, homEquiv, homEquiv_naturality_left_symm, invFun, left_inv, map_fst, map_point, map_snd, mkOfHomEquiv, o.elim, toProd
-/
def pointedToBipointedSndBipointedToPointedSndAdjunction :
    pointedToBipointedSnd ⊣ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            apply Bipointed.Hom.ext
            funext x
            cases x
            · exact f.map_fst.symm
            · rfl }
      homEquiv_naturality_left_symm := fun f g => by
        apply Bipointed.Hom.ext
        funext x
        cases x <;> rfl }
