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

/-- The category of bipointed types. -/
/-
**Bipointed** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of bipointed types.
-/
structure Bipointed : Type (u + 1) where
  /-- The underlying type of a bipointed type. -/
  protected X : Type u
  /-- The two points of a bipointed type, bundled together as a pair. -/
  toProd : X × X

namespace Bipointed

/-
**Bipointed.** 是 Mathlib 中的一个实例，位于命名空间 `Bipointed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Bipointed Type* := ⟨Bipointed.X⟩

/-- Turns a bipointing into a bipointed type. -/
/-
**Bipointed.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `Bipointed`。
形式化陈述：of {X : Type*} (to_prod : X × X) : Bipointed
参数：to_prod : X × X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a bipointing into a bipointed type.
-/
abbrev of {X : Type*} (to_prod : X × X) : Bipointed :=
  ⟨X, to_prod⟩
/-
**Bipointed.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `Bipointed`。
形式化陈述：coe_of {X : Type*} (to_prod : X × X) : ↥(of to_prod) = X
参数：to_prod : X × X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of {X : Type*} (to_prod : X × X) : ↥(of to_prod) = X :=
  rfl

alias _root_.Prod.Bipointed := of
/-
**Bipointed.** 是 Mathlib 中的一个实例，位于命名空间 `Bipointed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Bipointed :=
  ⟨of ((), ())⟩

/-- Morphisms in `Bipointed`. -/
@[ext]
/-
**Bipointed.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Bipointed`。
形式化陈述：Bipointed → Bipointed → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms in `Bipointed`.
-/
protected structure Hom (X Y : Bipointed.{u}) : Type u where
  /-- The underlying function of a morphism of bipointed types. -/
  toFun : X → Y
  map_fst : toFun X.toProd.1 = Y.toProd.1
  map_snd : toFun X.toProd.2 = Y.toProd.2

namespace Hom

/-- The identity morphism of `X : Bipointed`. -/
@[simps]
nonrec def id (X : Bipointed) : Bipointed.Hom X X :=
  ⟨id, rfl, rfl⟩

/-
**Bipointed.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `Bipointed.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Bipointed) : Inhabited (Bipointed.Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `Bipointed`. -/
@[simps]
/-
**Bipointed.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `Bipointed.Hom`。
形式化陈述：comp {X Y Z : Bipointed.{u}} (f : Bipointed.Hom X Y) (g : Bipointed.Hom Y 
Z) : Bipointed.Hom X Z
参数：f : Bipointed.Hom X Y；g : Bipointed.Hom Y Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms of `Bipointed`.
-/
def comp {X Y Z : Bipointed.{u}} (f : Bipointed.Hom X Y) (g : Bipointed.Hom Y Z) :
    Bipointed.Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_fst, g.map_fst], by
    rw [Function.comp_apply, f.map_snd, g.map_snd]⟩

end Hom

/-
**Bipointed.largeCategory** 是 Mathlib 中的一个实例，位于命名空间 `Bipointed`。
形式化陈述：largeCategory : LargeCategory Bipointed where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance largeCategory : LargeCategory Bipointed where
  Hom := Bipointed.Hom
  id := Hom.id
  comp := @Hom.comp

/-- The subtype of functions corresponding to the morphisms in `Bipointed`. -/
/-
**Bipointed.HomSubtype** 是 Mathlib 中的一个缩写定义，位于命名空间 `Bipointed`。
形式化陈述：HomSubtype (X Y : Bipointed)
参数：X Y : Bipointed。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subtype of functions corresponding to the morphisms in `Bipointed`.
-/
abbrev HomSubtype (X Y : Bipointed) :=
  { f : X → Y // f X.toProd.1 = Y.toProd.1 ∧ f X.toProd.2 = Y.toProd.2 }
/-
**Bipointed.** 是 Mathlib 中的一个实例，位于命名空间 `Bipointed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : Bipointed) : FunLike (HomSubtype X Y) X Y where
  coe f := f
  coe_injective _ _ := Subtype.ext
/-
**Bipointed.hasForget** 是 Mathlib 中的一个实例，位于命名空间 `Bipointed`。
形式化陈述：hasForget : ConcreteCategory Bipointed HomSubtype where hom f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForget : ConcreteCategory Bipointed HomSubtype where
  hom f := ⟨f.1, ⟨f.2, f.3⟩⟩
  ofHom f := ⟨f.1, f.2.1, f.2.2⟩

/-- Swaps the pointed elements of a bipointed type. `Prod.swap` as a functor. -/
@[simps]
/-
**Bipointed.swap** 是 Mathlib 中的一个定义，位于命名空间 `Bipointed`。
形式化陈述：swap : Bipointed ⥤ Bipointed where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bipointed.Hom.map_snd`：∀ {X Y : Bipointed} (self : X.Hom Y), self.toFun 
X.toProd.2 = Y.toProd.2
· 使用定理 `Bipointed.Hom.map_fst`：∀ {X Y : Bipointed} (self : X.Hom Y), self.toFun 
X.toProd.1 = Y.toProd.1

--- 原说明 ---
Swaps the pointed elements of a bipointed type. `Prod.swap` as a functor.
-/
def swap : Bipointed ⥤ Bipointed where
  obj X := ⟨X, X.toProd.swap⟩
  map f := ⟨f.toFun, f.map_snd, f.map_fst⟩

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence between `Bipointed` and itself induced by `Prod.swap` both ways. -/
@[simps!]
/-
**Bipointed.swapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Bipointed`。
形式化陈述：swapEquiv : Bipointed ≌ Bipointed where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `Bipointed` and itself induced by `Prod.swap` both ways.
-/
def swapEquiv : Bipointed ≌ Bipointed where
  functor := swap
  inverse := swap
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
/-
**Bipointed.swapEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Bipointed`。
形式化陈述：swapEquiv_symm : swapEquiv.symm = swapEquiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl

end Bipointed

/-- The forgetful functor from `Bipointed` to `Pointed` which forgets about the second point. -/
/-
**bipointedToPointedFst** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：bipointedToPointedFst : Bipointed ⥤ Pointed where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bipointed.Hom.map_fst`：∀ {X Y : Bipointed} (self : X.Hom Y), self.toFun 
X.toProd.1 = Y.toProd.1

--- 原说明 ---
The forgetful functor from `Bipointed` to `Pointed` which forgets about the seco
nd point.
-/
def bipointedToPointedFst : Bipointed ⥤ Pointed where
  obj X := ⟨X, X.toProd.1⟩
  map f := ⟨f.toFun, f.map_fst⟩

/-- The forgetful functor from `Bipointed` to `Pointed` which forgets about the first point. -/
/-
**bipointedToPointedSnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：bipointedToPointedSnd : Bipointed ⥤ Pointed where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bipointed.Hom.map_snd`：∀ {X Y : Bipointed} (self : X.Hom Y), self.toFun 
X.toProd.2 = Y.toProd.2

--- 原说明 ---
The forgetful functor from `Bipointed` to `Pointed` which forgets about the firs
t point.
-/
def bipointedToPointedSnd : Bipointed ⥤ Pointed where
  obj X := ⟨X, X.toProd.2⟩
  map f := ⟨f.toFun, f.map_snd⟩

@[simp]
/-
**bipointedToPointedFst_comp_forget** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bipointedToPointedFst_comp_forget : bipointedToPointedFst ⋙ forget Pointed
 = forget Bipointed
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bipointedToPointedFst_comp_forget :
    bipointedToPointedFst ⋙ forget Pointed = forget Bipointed :=
  rfl

@[simp]
/-
**bipointedToPointedSnd_comp_forget** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bipointedToPointedSnd_comp_forget : bipointedToPointedSnd ⋙ forget Pointed
 = forget Bipointed
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bipointedToPointedSnd_comp_forget :
    bipointedToPointedSnd ⋙ forget Pointed = forget Bipointed :=
  rfl

@[simp]
/-
**swap_comp_bipointedToPointedFst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：swap_comp_bipointedToPointedFst : Bipointed.swap ⋙ bipointedToPointedFst =
 bipointedToPointedSnd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_comp_bipointedToPointedFst :
    Bipointed.swap ⋙ bipointedToPointedFst = bipointedToPointedSnd :=
  rfl

@[simp]
/-
**swap_comp_bipointedToPointedSnd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：swap_comp_bipointedToPointedSnd : Bipointed.swap ⋙ bipointedToPointedSnd =
 bipointedToPointedFst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_comp_bipointedToPointedSnd :
    Bipointed.swap ⋙ bipointedToPointedSnd = bipointedToPointedFst :=
  rfl

/-- The functor from `Pointed` to `Bipointed` which bipoints the point. -/
/-
**pointedToBipointed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pointedToBipointed : Pointed.{u} ⥤ Bipointed where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Pointed.Hom.map_point`：∀ {X Y : Pointed} (self : X.Hom Y), self.toFun X.
point = Y.point

--- 原说明 ---
The functor from `Pointed` to `Bipointed` which bipoints the point.
-/
def pointedToBipointed : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨X, X.point, X.point⟩
  map f := ⟨f.toFun, f.map_point, f.map_point⟩

/-- The functor from `Pointed` to `Bipointed` which adds a second point. -/
/-
**pointedToBipointedFst** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pointedToBipointedFst : Pointed.{u} ⥤ Bipointed where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `Pointed` to `Bipointed` which adds a second point.
-/
def pointedToBipointedFst : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨Option X, X.point, none⟩
  map f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

/-- The functor from `Pointed` to `Bipointed` which adds a first point. -/
/-
**pointedToBipointedSnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pointedToBipointedSnd : Pointed.{u} ⥤ Bipointed where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `Pointed` to `Bipointed` which adds a first point.
-/
def pointedToBipointedSnd : Pointed.{u} ⥤ Bipointed where
  obj X := ⟨Option X, none, X.point⟩
  map f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id _ := Bipointed.Hom.ext Option.map_id
  map_comp f g := Bipointed.Hom.ext (Option.map_comp_map f.1 g.1).symm

@[simp]
/-
**pointedToBipointedFst_comp_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pointedToBipointedFst_comp_swap : pointedToBipointedFst ⋙ Bipointed.swap =
 pointedToBipointedSnd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointedToBipointedFst_comp_swap :
    pointedToBipointedFst ⋙ Bipointed.swap = pointedToBipointedSnd :=
  rfl

@[simp]
/-
**pointedToBipointedSnd_comp_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pointedToBipointedSnd_comp_swap : pointedToBipointedSnd ⋙ Bipointed.swap =
 pointedToBipointedFst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointedToBipointedSnd_comp_swap :
    pointedToBipointedSnd ⋙ Bipointed.swap = pointedToBipointedFst :=
  rfl

/-- `BipointedToPointed_fst` is inverse to `PointedToBipointed`. -/
@[simps!]
/-
**pointedToBipointedCompBipointedToPointedFst** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pointedToBipointedCompBipointedToPointedFst : pointedToBipointed ⋙ bipoint
edToPointedFst ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BipointedToPointed_fst` is inverse to `PointedToBipointed`.
-/
def pointedToBipointedCompBipointedToPointedFst :
    pointedToBipointed ⋙ bipointedToPointedFst ≅ 𝟭 _ :=
  NatIso.ofComponents fun X =>
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

/-- `BipointedToPointed_snd` is inverse to `PointedToBipointed`. -/
@[simps!]
/-
**pointedToBipointedCompBipointedToPointedSnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pointedToBipointedCompBipointedToPointedSnd : pointedToBipointed ⋙ bipoint
edToPointedSnd ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BipointedToPointed_snd` is inverse to `PointedToBipointed`.
-/
def pointedToBipointedCompBipointedToPointedSnd :
    pointedToBipointed ⋙ bipointedToPointedSnd ≅ 𝟭 _ :=
  NatIso.ofComponents fun X =>
    { hom := ⟨id, rfl⟩
      inv := ⟨id, rfl⟩ }

/-- The free/forgetful adjunction between `PointedToBipointed_fst` and `BipointedToPointed_fst`.
-/
/-
**pointedToBipointedFstBipointedToPointedFstAdjunction** 是 Mathlib 中的一个定义，位于命名空间
 ``。
形式化陈述：pointedToBipointedFstBipointedToPointedFstAdjunction : pointedToBipointedF
st ⊣ bipointedToPointedFst
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free/forgetful adjunction between `PointedToBipointed_fst` and `BipointedToP
ointed_fst`.
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

/-- The free/forgetful adjunction between `PointedToBipointed_snd` and `BipointedToPointed_snd`.
-/
/-
**pointedToBipointedSndBipointedToPointedSndAdjunction** 是 Mathlib 中的一个定义，位于命名空间
 ``。
形式化陈述：pointedToBipointedSndBipointedToPointedSndAdjunction : pointedToBipointedS
nd ⊣ bipointedToPointedSnd
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free/forgetful adjunction between `PointedToBipointed_snd` and `BipointedToP
ointed_snd`.
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
