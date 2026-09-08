/-
Copyright (c) 2026 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
# 2-Yoneda embedding

In this file we define the bicategorical Yoneda embedding.

-/

@[expose] public section

namespace CategoryTheory

open Bicategory.Opposite Opposite Pseudofunctor StrongTrans

universe w v u

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- Version of `Bicategory.precomposing` viewed in the bicategory `Cat`. -/
@[simps]
/-
**CategoryTheory.Bicategory.precomposingCat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：precomposingCat (a b c : B) : (a ⟶ b) ⥤ (Cat.of (b ⟶ c) ⟶ Cat.of (a ⟶ c)) 
where obj f
参数：a b c : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of `Bicategory.precomposing` viewed in the bicategory `Cat`.
-/
def precomposingCat (a b c : B) :
    (a ⟶ b) ⥤ (Cat.of (b ⟶ c) ⟶ Cat.of (a ⟶ c)) where
  obj f := (precomp c f).toCatHom
  map η := NatTrans.toCatHom₂ ((precomposing a b c).map η)

/-- Version of `Bicategory.postcomposing` viewed in the bicategory `Cat`. -/
@[simps]
/-
**CategoryTheory.Bicategory.postcomposingCat** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：postcomposingCat (a b c : B) : (b ⟶ c) ⥤ (Cat.of (a ⟶ b) ⟶ Cat.of (a ⟶ c))
 where obj f
参数：a b c : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Version of `Bicategory.postcomposing` viewed in the bicategory `Cat`.
-/
def postcomposingCat (a b c : B) : (b ⟶ c) ⥤ (Cat.of (a ⟶ b) ⟶ Cat.of (a ⟶ c)) where
  obj f := (postcomp a f).toCatHom
  map η := NatTrans.toCatHom₂ ((postcomposing a b c).map η)

set_option backward.defeqAttrib.useBackward true in
/-- Left unitor as a 2-isomorphism in `Cat`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.leftUnitorNatIsoCat** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Bicategory`。
形式化陈述：leftUnitorNatIsoCat (a b : B) : (precomposingCat _ _ b).obj (𝟙 a) ≅ 𝟙 (Cat
.of (a ⟶ b))
参数：a b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left unitor as a 2-isomorphism in `Cat`.
-/
def leftUnitorNatIsoCat (a b : B) : (precomposingCat _ _ b).obj (𝟙 a) ≅ 𝟙 (Cat.of (a ⟶ b)) :=
  Cat.Hom.isoMk <| NatIso.ofComponents (λ_ ·)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Right component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.associatorNatIsoRightCat** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bicategory`。
形式化陈述：associatorNatIsoRightCat {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (d : B) : (pr
ecomposingCat _ _ d).obj (f ≫ g) ≅ (precomposingCat ..).obj g ≫ (precomposingCat
 ..).obj f
参数：f : a ⟶ b；g : b ⟶ c；d : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right component of the associator as a 2-isomorphism in `Cat`.
-/
def associatorNatIsoRightCat {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (d : B) :
    (precomposingCat _ _ d).obj (f ≫ g) ≅
      (precomposingCat ..).obj g ≫ (precomposingCat ..).obj f :=
  Cat.Hom.isoMk <| NatIso.ofComponents (α_ f g ·)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Middle component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.associatorNatIsoMiddleCat** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Bicategory`。
形式化陈述：associatorNatIsoMiddleCat {a b c d : B} (f : a ⟶ b) (h : c ⟶ d) : (precomp
osingCat ..).obj f ≫ (postcomposingCat ..).obj h ≅ (postcomposingCat ..).obj h ≫
 (precomposingCat ..).obj f
参数：f : a ⟶ b；h : c ⟶ d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Middle component of the associator as a 2-isomorphism in `Cat`.
-/
def associatorNatIsoMiddleCat {a b c d : B} (f : a ⟶ b) (h : c ⟶ d) :
    (precomposingCat ..).obj f ≫ (postcomposingCat ..).obj h ≅
      (postcomposingCat ..).obj h ≫ (precomposingCat ..).obj f :=
  Cat.Hom.isoMk <| NatIso.ofComponents (α_ f · h)

set_option backward.defeqAttrib.useBackward true in
/-- Right unitor as a 2-isomorphism in `Cat`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.rightUnitorNatIsoCat** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：rightUnitorNatIsoCat (a b : B) : (postcomposingCat a _ _).obj (𝟙 b) ≅ 𝟙 (C
at.of (a ⟶ b))
参数：a b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right unitor as a 2-isomorphism in `Cat`.
-/
def rightUnitorNatIsoCat (a b : B) : (postcomposingCat a _ _).obj (𝟙 b) ≅ 𝟙 (Cat.of (a ⟶ b)) :=
  Cat.Hom.isoMk <| NatIso.ofComponents (ρ_ ·)

set_option backward.isDefEq.respectTransparency false in
/-- Left component of the associator as a 2-isomorphism in `Cat`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.associatorNatIsoLeftCat** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Bicategory`。
形式化陈述：associatorNatIsoLeftCat (a : B) {b c d : B} (g : b ⟶ c) (h : c ⟶ d) : (pos
tcomposingCat a ..).obj g ≫ (postcomposingCat ..).obj h ≅ (postcomposingCat ..).
obj (g ≫ h)
参数：a : B；g : b ⟶ c；h : c ⟶ d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left component of the associator as a 2-isomorphism in `Cat`.
-/
def associatorNatIsoLeftCat (a : B) {b c d : B} (g : b ⟶ c) (h : c ⟶ d) :
    (postcomposingCat a ..).obj g ≫ (postcomposingCat ..).obj h ≅
      (postcomposingCat ..).obj (g ≫ h) :=
  Cat.Hom.isoMk <| NatIso.ofComponents (α_ · g h)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The map on objects underlying the Yoneda embedding. It sends an object `x` to
the pseudofunctor defined by:
* Objects: `a ↦ (a ⟶ x)`
* Higher morphisms get sent to the corresponding "precomposing" operation.

This is only used for defining `yoneda`, after which `Bicategory.yoneda.obj` should be preferred. -/
@[simps!]
/-
**CategoryTheory.Bicategory.yoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bic
ategory`。
形式化陈述：yoneda : B ⥤ᵖ Bᵒᵖ ⥤ᵖ Cat.{w, v} where toPrelaxFunctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map on objects underlying the Yoneda embedding. It sends an object `x` to
the pseudofunctor defined by:
* Objects: `a ↦ (a ⟶ x)`
* Higher morphisms get sent to the corresponding "precomposing" operation.

This is only used for defining `yoneda`, after which `Bicategory.yoneda.obj` sho
uld be preferred.
-/
def yoneda₀ (x : B) : Pseudofunctor Bᵒᵖ Cat.{w, v} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (fun y => Cat.of (unop y ⟶ x))
    (fun a b => unopFunctor a b ⋙ precomposingCat (unop b) (unop a) x)
  mapId a := leftUnitorNatIsoCat (unop a) x
  mapComp f g := associatorNatIsoRightCat g.unop f.unop x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing of a 1-morphism seen as a strong transformation between pseudofunctors. -/
@[simps!]
/-
**CategoryTheory.Bicategory.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.B
icategory`。
形式化陈述：postcomp (a : B) (f : b ⟶ c) : (a ⟶ b) ⥤ (a ⟶ c) where obj
参数：a : B；f : b ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Postcomposing of a 1-morphism seen as a strong transformation between pseudofunc
tors.
-/
def postcomp₂ {a b : B} (f : a ⟶ b) : yoneda₀ a ⟶ yoneda₀ b where
  app x := (postcomposingCat (unop x) a b).obj f
  naturality g := associatorNatIsoMiddleCat g.unop f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing of `1`-morphisms seen as a functor from `a ⟶ b` to the hom-category of the
corresponding pseudofunctors.

This is an implementation detail, and `Bicategory.yoneda.map` should be preferred. -/
@[simps!]
/-
**CategoryTheory.Bicategory.postcomposing** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Bicategory`。
形式化陈述：postcomposing (a b c : B) : (b ⟶ c) ⥤ (a ⟶ b) ⥤ (a ⟶ c) where obj f
参数：a b c : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Postcomposing of `1`-morphisms seen as a functor from `a ⟶ b` to the hom-categor
y of the
corresponding pseudofunctors.

This is an implementation detail, and `Bicategory.yoneda.map` should be preferre
d.
-/
def postcomposing₂ (a b : B) : (a ⟶ b) ⥤ (yoneda₀ a ⟶ yoneda₀ b) where
  obj := postcomp₂
  map η := { as := { app x := (postcomposingCat (unop x) a b).map η } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda pseudofunctor from `B` to `Bᵒᵖ ⥤ᵖ Cat`.

It consists of the following:
* On objects: sends `x : B` to the pseudofunctor `Bᵒᵖ ⥤ᵖ Cat` given by
  `a ↦ (a ⟶ x)` on objects and on 1- and 2-morphisms given by "precomposing"
* On 1- and 2-morphisms it is given by "postcomposing" -/
@[simps!]
/-
**CategoryTheory.Bicategory.yoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bic
ategory`。
形式化陈述：yoneda : B ⥤ᵖ Bᵒᵖ ⥤ᵖ Cat.{w, v} where toPrelaxFunctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Yoneda pseudofunctor from `B` to `Bᵒᵖ ⥤ᵖ Cat`.

It consists of the following:
* On objects: sends `x : B` to the pseudofunctor `Bᵒᵖ ⥤ᵖ Cat` given by
  `a ↦ (a ⟶ x)` on objects and on 1- and 2-morphisms given by "precomposing"
* On 1- and 2-morphisms it is given by "postcomposing"
-/
def yoneda : B ⥤ᵖ Bᵒᵖ ⥤ᵖ Cat.{w, v} where
  toPrelaxFunctor := PrelaxFunctor.mkOfHomFunctors (yoneda₀ ·) postcomposing₂
  mapId a := isoMk (fun b => rightUnitorNatIsoCat (unop b) a)
  mapComp f g := (isoMk (fun b ↦ associatorNatIsoLeftCat (unop b) f g)).symm

end Bicategory

end CategoryTheory

