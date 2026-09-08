/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

/-!

# Strong transformations of pseudofunctors

There are three types of transformations between pseudofunctors, depending on the direction
or invertibility of the 2-morphism witnessing the naturality condition.

In this file we define strong transformations, which require the 2-morphism to be invertible.

## Main definitions

* `Pseudofunctor.StrongTrans F G`: strong transformations between pseudofunctors `F` and `G`.
* `Pseudofunctor.StrongTrans.mkOfOplax η`: given a strong transformation `η` between the
  underlying oplax functors, `mkOfOplax` lifts this to a strong transformation between the
  pseudofunctors.
* `Pseudofunctor.StrongTrans.vcomp η θ`: the vertical composition of strong transformations `η`
  and `θ`.

Using this, we obtain a (scoped) `CategoryStruct` on pseudofunctors, where the arrows are given by
strong transformations. To access this instance, run `open scoped Pseudofunctor.StrongTrans`.
See `Pseudofunctor.StrongTrans.categoryStruct`.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055)

-/

@[expose] public section

namespace CategoryTheory.Pseudofunctor

open Category Bicategory Oplax

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- A strong transformation between pseudofunctors `F` and `G` is a natural transformation
that is "natural up to 2-isomorphisms".
More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : F.map f ≫ app b ≅ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identities and the
  compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
/-
**CategoryTheory.Pseudofunctor.StrongTrans** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTh
eory.Pseudofunctor`。
形式化陈述：StrongTrans (F G : Pseudofunctor B C) where /-- The component 1-morphisms 
of a strong transformation. -/ app (a : B) : F.obj a ⟶ G.obj a /-- The 2-isomorp
hisms underlying the strong naturality constraint. -/ naturality {a b : B} (f : 
a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f /-- Naturality of the strong naturali
ty constraint. -/ naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : F.
map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η
参数：F G : Pseudofunctor B C；a : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strong transformation between pseudofunctors `F` and `G` is a natural transfor
mation
that is "natural up to 2-isomorphisms".
More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : F.map f ≫ app b ≅ app a ≫ G.map f` for each 
1-morphism
  `f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identi
ties and the
  compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure StrongTrans (F G : Pseudofunctor B C) where
  /-- The component 1-morphisms of a strong transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-isomorphisms underlying the strong naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f
  /-- Naturality of the strong naturality constraint. -/
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    cat_disch
  /-- Oplax unity. -/
  naturality_id (a : B) :
      (naturality (𝟙 a)).hom ≫ app a ◁ (G.mapId a).hom =
        (F.mapId a).hom ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    cat_disch
  /-- Oplax functoriality. -/
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      (naturality (f ≫ g)).hom ≫ app a ◁ (G.mapComp f g).hom =
        (F.mapComp f g).hom ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
    cat_disch

attribute [reassoc (attr := simp)] StrongTrans.naturality_naturality
  StrongTrans.naturality_id StrongTrans.naturality_comp

namespace StrongTrans

variable {F G : B ⥤ᵖ C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The strong transformation of oplax functors induced by a strong transformation of
pseudofunctors. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.toOplax** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：toOplax (η : StrongTrans F G) : Oplax.StrongTrans F.toOplax G.toOplax wher
e app
参数：η : StrongTrans F G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The strong transformation of oplax functors induced by a strong transformation o
f
pseudofunctors.
-/
def toOplax (η : StrongTrans F G) : Oplax.StrongTrans F.toOplax G.toOplax where
  app := η.app
  naturality f := η.naturality f
/-
**CategoryTheory.Pseudofunctor.StrongTrans.hasCoeToOplax** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：hasCoeToOplax : Coe (StrongTrans F G) (Oplax.StrongTrans F.toOplax G.toOpl
ax)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToOplax : Coe (StrongTrans F G) (Oplax.StrongTrans F.toOplax G.toOplax) :=
  ⟨toOplax⟩

/-- Construct a strong transformation of pseudofunctors from a strong transformation of the
underlying oplax functors. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.mkOfOplax** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：mkOfOplax (η : Oplax.StrongTrans F.toOplax G.toOplax) : StrongTrans F G wh
ere app
参数：η : Oplax.StrongTrans F.toOplax G.toOplax。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a strong transformation of pseudofunctors from a strong transformation
 of the
underlying oplax functors.
-/
def mkOfOplax (η : Oplax.StrongTrans F.toOplax G.toOplax) :
    StrongTrans F G where
  app := η.app
  naturality := η.naturality
  naturality_naturality θ := η.naturality_naturality θ
  naturality_id a := η.naturality_id a
  naturality_comp f g := η.naturality_comp f g

variable (F) in
/-- The identity strong transformation. -/
/-
**CategoryTheory.Pseudofunctor.StrongTrans.id** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Pseudofunctor.StrongTrans`。
形式化陈述：id : StrongTrans F F where app a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity strong transformation.
-/
def id : StrongTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {a b} f := (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm
/-
**CategoryTheory.Pseudofunctor.StrongTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Pseudofunctor.StrongTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (StrongTrans F F) :=
  ⟨id F⟩

variable {H : B ⥤ᵖ C}

/-- Vertical composition of strong transformations. -/
/-
**CategoryTheory.Pseudofunctor.StrongTrans.vcomp** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：vcomp (η : StrongTrans F G) (θ : StrongTrans G H) : StrongTrans F H
参数：η : StrongTrans F G；θ : StrongTrans G H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Vertical composition of strong transformations.
-/
def vcomp (η : StrongTrans F G) (θ : StrongTrans G H) : StrongTrans F H :=
  mkOfOplax (Oplax.StrongTrans.vcomp η.toOplax θ.toOplax)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- `CategoryStruct` on `B ⥤ᵖ C` where the (1-)morphisms are given by strong
transformations. -/
@[simps! id_app id_naturality_hom id_naturality_inv comp_naturality_hom
comp_naturality_inv]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.categoryStruct** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {C : Type u₂}
 →       [inst_1 : CategoryTheory.Bicategory C] →         CategoryTheory.Categor
yStruct.{max (max (max u₁ v₂) v₁) w₂, max (max (max (max (max u₂ u₁) v₂) v₁) w₂)
 w₁}           (CategoryTheory.Pseudofunctor B C)
参数：max (max u₁ v₂) v₁；max (max (max (max u₂ u₁) v₂) v₁) w₂；CategoryTheory.Pseudo
functor B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance categoryStruct : CategoryStruct (B ⥤ᵖ C) where
  Hom F G := StrongTrans F G
  id F := StrongTrans.id F
  comp := StrongTrans.vcomp

variable (η : F ⟶ G) (θ : G ⟶ H)

@[simp]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.comp_app** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：comp_app (η : F ⟶ G) (θ : G ⟶ H) (a : B) : (η ≫ θ).app a = η.app a ≫ θ.app
 a
参数：η : F ⟶ G；θ : G ⟶ H；a : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_app (η : F ⟶ G) (θ : G ⟶ H) (a : B) :
    (η ≫ θ).app a = η.app a ≫ θ.app a :=
  rfl

variable (F) in
@[simp]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.id.toOplax** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Pseudofunctor.StrongTrans.id`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1
 : CategoryTheory.Bicategory C]   (F : CategoryTheory.Pseudofunctor B C),   Cate
goryTheory.Oplax.StrongTrans.id F.toOplax =     CategoryTheory.Pseudofunctor.Str
ongTrans.toOplax (CategoryTheory.CategoryStruct.id F)
参数：F : CategoryTheory.Pseudofunctor B C；CategoryTheory.CategoryStruct.id F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id.toOplax : Oplax.StrongTrans.id F.toOplax = 𝟙 F :=
  rfl

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.whiskerLeft_naturality_naturality** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g 
⟶ h) : f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom = f ◁ (θ.naturality g).
hom ≫ f ◁ θ.app a ◁ H.map₂ β
参数：f : a' ⟶ G.obj a；β : g ⟶ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.StrongTrans.whiskerLeft_naturality_naturality`：whis
kerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) : f ◁
 G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom = f ◁ (θ.…
-/
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom =
      f ◁ (θ.naturality g).hom ≫ f ◁ θ.app a ◁ H.map₂ β :=
  θ.toOplax.whiskerLeft_naturality_naturality _ _

@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.whiskerRight_naturality_naturality** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b 
⟶ a') : F.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h = (η.naturality f).hom
 ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv
参数：β : f ⟶ g；h : G.obj b ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.StrongTrans.whiskerRight_naturality_naturality`：whi
skerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') : F
.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h = (η.nat…
-/
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h =
      (η.naturality f).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv :=
  η.toOplax.whiskerRight_naturality_naturality _ _

@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.whiskerLeft_naturality_comp** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) : f
 ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ (H.mapComp g h).hom = f ◁ (G.mapCo
mp g h).hom ▷ θ.app c ≫ f ◁ (α_ _ _ _).hom ≫ f ◁ G.map g ◁ (θ.naturality h).hom 
≫ f ◁ (α_ _ _ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom
参数：f : a' ⟶ G.obj a；g : a ⟶ b；h : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.StrongTrans.whiskerLeft_naturality_comp`：whiskerLef
t_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) : f ◁ (θ.naturality
 (g ≫ h)).hom ≫ f ◁ θ.app a ◁ H.mapComp g h = f ◁ …
-/
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ (H.mapComp g h).hom =
      f ◁ (G.mapComp g h).hom ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ (θ.naturality h).hom ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom :=
  θ.toOplax.whiskerLeft_naturality_comp _ _ _

@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.whiskerRight_naturality_comp** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') : 
(η.naturality (f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ (G.mapComp f g).hom 
▷ h = (F.mapComp f g).hom ▷ η.app c ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom ≫ 
F.map f ◁ (η.naturality g).hom ▷ h ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).inv ▷ h ≫ (η.na
turality f).hom ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom
参数：f : a ⟶ b；g : b ⟶ c；h : G.obj c ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.StrongTrans.whiskerRight_naturality_comp`：whiskerRi
ght_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') : (η.naturality (
f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapC…
-/
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (η.naturality (f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ (G.mapComp f g).hom ▷ h =
      (F.mapComp f g).hom ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ (η.naturality g).hom ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                 (η.naturality f).hom ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom :=
  η.toOplax.whiskerRight_naturality_comp _ _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.whiskerLeft_naturality_id** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：whiskerLeft_naturality_id (f : a' ⟶ G.obj a) : f ◁ (θ.naturality (𝟙 a)).ho
m ≫ f ◁ θ.app a ◁ (H.mapId a).hom = f ◁ (G.mapId a).hom ▷ θ.app a ≫ f ◁ (fun_ (θ
.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv
参数：f : a' ⟶ G.obj a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.StrongTrans.whiskerLeft_naturality_id`：whiskerLeft_
naturality_id (f : a' ⟶ G.obj a) : f ◁ (θ.naturality (𝟙 a)).hom ≫ f ◁ θ.app a ◁ 
H.mapId a = f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (fun_ …

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ (θ.naturality (𝟙 a)).hom ≫ f ◁ θ.app a ◁ (H.mapId a).hom =
      f ◁ (G.mapId a).hom ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv :=
  θ.toOplax.whiskerLeft_naturality_id _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp), to_app]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.whiskerRight_naturality_id** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：whiskerRight_naturality_id (f : G.obj a ⟶ a') : (η.naturality (𝟙 a)).hom ▷
 f ≫ (α_ _ _ _).hom ≫ η.app a ◁ (G.mapId a).hom ▷ f = (F.mapId a).hom ▷ η.app a 
▷ f ≫ (fun_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫ (α_ _ _ _).hom
参数：f : G.obj a ⟶ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Oplax.StrongTrans.whiskerRight_naturality_id`：whiskerRigh
t_naturality_id (f : G.obj a ⟶ a') : (η.naturality (𝟙 a)).hom ▷ f ≫ (α_ _ _ _).h
om ≫ η.app a ◁ G.mapId a ▷ f = F.mapId a ▷ η.app …

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (η.naturality (𝟙 a)).hom ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ (G.mapId a).hom ▷ f =
    (F.mapId a).hom ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫
    (α_ _ _ _).hom :=
  η.toOplax.whiskerRight_naturality_id _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.naturality_id_hom** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：naturality_id_hom (α : F ⟶ G) (a : B) : (α.naturality (𝟙 a)).hom = (F.mapI
d a).hom ▷ α.app a ≫ (fun_ (α.app a)).hom ≫ (ρ_ (α.app a)).inv ≫ α.app a ◁ (G.ma
pId a).inv
参数：α : F ⟶ G；a : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerLeft`：inv_whiskerLeft (f : a ⟶ b) {
g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : inv (f ◁ η) = f ◁ inv η
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Pseudofunctor.StrongTrans.naturality_id`：∀ {B : Type u₁} 
[inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bica
tegory C]   {F G : CategoryTheory.Pseudofunc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma naturality_id_hom (α : F ⟶ G) (a : B) :
    (α.naturality (𝟙 a)).hom = (F.mapId a).hom ▷ α.app a ≫
      (λ_ (α.app a)).hom ≫ (ρ_ (α.app a)).inv ≫ α.app a ◁ (G.mapId a).inv := by
  simp [← assoc, ← IsIso.comp_inv_eq]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.naturality_id_iso** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：naturality_id_iso (α : F ⟶ G) (a : B) : α.naturality (𝟙 a) = whiskerRightI
so (F.mapId a) (α.app a) ≪≫ (fun_ (α.app a)) ≪≫ (ρ_ (α.app a)).symm ≪≫ whiskerLe
ftIso (α.app a) (G.mapId a).symm
参数：α : F ⟶ G；a : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.StrongTrans.naturality_id_hom`：naturality_i
d_hom (α : F ⟶ G) (a : B) : (α.naturality (𝟙 a)).hom = (F.mapId a).hom ▷ α.app a
 ≫ (fun_ (α.app a)).hom ≫ (ρ_ (α.app a)).inv ≫ α…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma naturality_id_iso (α : F ⟶ G) (a : B) :
    α.naturality (𝟙 a) = whiskerRightIso (F.mapId a) (α.app a) ≪≫
      (λ_ (α.app a)) ≪≫ (ρ_ (α.app a)).symm ≪≫ whiskerLeftIso (α.app a) (G.mapId a).symm := by
  ext
  simp [naturality_id_hom]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.naturality_id_inv** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：naturality_id_inv (α : F ⟶ G) (a : B) : (α.naturality (𝟙 a)).inv = α.app a
 ◁ (G.mapId a).hom ≫ (ρ_ (α.app a)).hom ≫ (fun_ (α.app a)).inv ≫ (F.mapId a).inv
 ▷ α.app a
参数：α : F ⟶ G；a : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.StrongTrans.naturality_id_iso`：naturality_i
d_iso (α : F ⟶ G) (a : B) : α.naturality (𝟙 a) = whiskerRightIso (F.mapId a) (α.
app a) ≪≫ (fun_ (α.app a)) ≪≫ (ρ_ (α.app a)).sym…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_inv`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_inv`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma naturality_id_inv (α : F ⟶ G) (a : B) :
    (α.naturality (𝟙 a)).inv = α.app a ◁ (G.mapId a).hom ≫ (ρ_ (α.app a)).hom ≫
      (λ_ (α.app a)).inv ≫ (F.mapId a).inv ▷ α.app a := by
  simp [naturality_id_iso]

@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality_hom** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：naturality_naturality_hom (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) 
: (α.naturality g).hom = (F.map₂ η.inv) ▷ α.app b ≫ (α.naturality f).hom ≫ α.app
 a ◁ G.map₂ η.hom
参数：α : F ⟶ G；η : f ≅ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality_assoc`：∀ 
{B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : Categ
oryTheory.Bicategory C]   {F G : CategoryTheory.Pseudofunc…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerLeft`：inv_whiskerLeft (f : a ⟶ b) {
g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : inv (f ◁ η) = f ◁ inv η
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.PrelaxFunctor.map₂_inv`：map₂_inv {f g : a ⟶ b} (η : f ⟶ g
) [IsIso η] : F.map₂ (inv η) = inv (F.map₂ η)
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma naturality_naturality_hom (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) :
    (α.naturality g).hom =
     (F.map₂ η.inv) ▷ α.app b ≫ (α.naturality f).hom ≫ α.app a ◁ G.map₂ η.hom := by
  simp [← IsIso.inv_comp_eq, ← G.map₂_inv η.inv]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality_iso** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：naturality_naturality_iso (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) 
: α.naturality g = whiskerRightIso (F.map₂Iso η.symm) (α.app b) ≪≫ (α.naturality
 f) ≪≫ whiskerLeftIso (α.app a) (G.map₂Iso η)
参数：α : F ⟶ G；η : f ≅ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality_hom`：natu
rality_naturality_hom (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) : (α.natur
ality g).hom = (F.map₂ η.inv) ▷ α.app b ≫ (α.naturality …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality_assoc`：∀ 
{B : Type u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : Categ
oryTheory.Bicategory C]   {F G : CategoryTheory.Pseudofunc…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.PrelaxFunctor.mapFunctor_map`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (F : CategoryTheory.PrelaxFuncto…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma naturality_naturality_iso (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) :
    α.naturality g = whiskerRightIso (F.map₂Iso η.symm) (α.app b) ≪≫
      (α.naturality f) ≪≫ whiskerLeftIso (α.app a) (G.map₂Iso η) := by
  ext
  rw [naturality_naturality_hom α η]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality_inv** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：naturality_naturality_inv (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) 
: (α.naturality g).inv = α.app a ◁ G.map₂ η.inv ≫ (α.naturality f).inv ≫ F.map₂ 
η.hom ▷ α.app b
参数：α : F ⟶ G；η : f ≅ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.StrongTrans.naturality_naturality_iso`：natu
rality_naturality_iso (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) : α.natura
lity g = whiskerRightIso (F.map₂Iso η.symm) (α.app b) ≪≫…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_inv`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.PrelaxFunctor.mapFunctor_map`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (F : CategoryTheory.PrelaxFuncto…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_inv`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma naturality_naturality_inv (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) :
    (α.naturality g).inv =
      α.app a ◁ G.map₂ η.inv ≫ (α.naturality f).inv ≫ F.map₂ η.hom ▷ α.app b := by
  simp [naturality_naturality_iso α η]

@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.naturality_comp_hom** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：naturality_comp_hom (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : (α.n
aturality (f ≫ g)).hom = (F.mapComp f g).hom ▷ α.app c ≫ (α_ _ _ _).hom ≫ F.map 
f ◁ (α.naturality g).hom ≫ (α_ _ _ _).inv ≫ (α.naturality f).hom ▷ G.map g ≫ (α_
 _ _ _).hom ≫ α.app a ◁ (G.mapComp f g).inv
参数：α : F ⟶ G；f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerLeft`：inv_whiskerLeft (f : a ⟶ b) {
g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : inv (f ◁ η) = f ◁ inv η
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Pseudofunctor.StrongTrans.naturality_comp`：∀ {B : Type u₁
} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bi
category C]   {F G : CategoryTheory.Pseudofunc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma naturality_comp_hom (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (α.naturality (f ≫ g)).hom =
      (F.mapComp f g).hom ▷ α.app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (α.naturality g).hom ≫
      (α_ _ _ _).inv ≫ (α.naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom ≫
      α.app a ◁ (G.mapComp f g).inv := by
  simp [← assoc, ← IsIso.comp_inv_eq]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.naturality_comp_iso** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：naturality_comp_iso (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : α.na
turality (f ≫ g) = whiskerRightIso (F.mapComp f g) (α.app c) ≪≫ (α_ _ _ _) ≪≫ wh
iskerLeftIso (F.map f) (α.naturality g) ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso (α
.naturality f) (G.map g) ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso (α.app a) (G.mapComp f g)
.symm
参数：α : F ⟶ G；f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.StrongTrans.naturality_comp_hom`：naturality
_comp_hom (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : (α.naturality (f ≫ g
)).hom = (F.mapComp f g).hom ▷ α.app c ≫ (α_ _ _ _…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_hom`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma naturality_comp_iso (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    α.naturality (f ≫ g) = whiskerRightIso (F.mapComp f g) (α.app c) ≪≫ (α_ _ _ _) ≪≫
      whiskerLeftIso (F.map f) (α.naturality g) ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso (α.naturality f) (G.map g) ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso (α.app a) (G.mapComp f g).symm := by
  ext
  simp [naturality_comp_hom α f g]

@[to_app (attr := reassoc)]
/-
**CategoryTheory.Pseudofunctor.StrongTrans.naturality_comp_inv** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Pseudofunctor.StrongTrans`。
形式化陈述：naturality_comp_inv (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : (α.n
aturality (f ≫ g)).inv = α.app a ◁ (G.mapComp f g).hom ≫ (α_ _ _ _).inv ≫ (α.nat
urality f).inv ▷ G.map g ≫ (α_ _ _ _).hom ≫ F.map f ◁ (α.naturality g).inv ≫ (α_
 _ _ _).inv ≫ (F.mapComp f g).inv ▷ α.app c
参数：α : F ⟶ G；f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Pseudofunctor.StrongTrans.naturality_comp_iso`：naturality
_comp_iso (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : α.naturality (f ≫ g)
 = whiskerRightIso (F.mapComp f g) (α.app c) ≪≫ (α…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_inv`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_inv`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma naturality_comp_inv (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (α.naturality (f ≫ g)).inv =
      α.app a ◁ (G.mapComp f g).hom ≫ (α_ _ _ _).inv ≫ (α.naturality f).inv ▷ G.map g ≫
      (α_ _ _ _).hom ≫ F.map f ◁ (α.naturality g).inv ≫ (α_ _ _ _).inv ≫
      (F.mapComp f g).inv ▷ α.app c := by
  simp [naturality_comp_iso α f g]

end

end CategoryTheory.Pseudofunctor.StrongTrans

