/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Oplax
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Transformations between oplax functors

Just as there are natural transformations between functors, there are transformations
between oplax functors. The equality in the naturality condition of a natural transformation gets
replaced by a specified 2-morphism. Now, there are three possible types of transformations (between
oplax functors):
* oplax natural transformations;
* lax natural transformations;
* strong natural transformations.

These differ in the direction (and invertibility) of the 2-morphisms involved in the naturality
condition.

## Main definitions

* `Oplax.LaxTrans F G`: lax transformations between oplax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `app a ≫ G.map f ⟶ F.map f ≫ app b` for each 1-morphism
  `f : a ⟶ b`.
* `Oplax.OplaxTrans F G`: oplax transformations between oplax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.
* `Oplax.StrongTrans F G`: strong transformations between oplax functors `F` and `G`. The naturality
  condition is given by a 2-isomorphism `F.map f ≫ app b ≅ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.

Using these, we define three (scoped) `CategoryStruct` instances on `B ⥤ᵒᵖᴸ C`, in the
`Oplax.LaxTrans`, `Oplax.OplaxTrans`, and `Oplax.StrongTrans` namespaces. The arrows in these
`CategoryStruct` instances are given by lax transformations, oplax transformations, and strong
transformations respectively.

We also provide API for going between oplax transformations and strong transformations:
* `OplaxTrans.StrongCore η`: a structure on an oplax transformation between oplax functors that
  promotes it to a strong transformation.
* `StrongTrans.mkOfOplax η η'`: given an oplax transformation `η` such that each component
  2-morphism is an isomorphism, `mkOfOplax` gives the corresponding strong transformation.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055)

-/

@[expose] public section

namespace CategoryTheory.Oplax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/--
Definition of `LaxTrans` / `LaxTrans` 的定义

English:
structure LaxTrans
  parameters: (F G : OplaxFunctor B C)
  axioms and operations (5):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : app a ≫ G.map f ⟶ F.map f ≫ app b
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g  [default: by cat_disch]
    - naturality_id((a : B)) : naturality (𝟙 a) ≫ F.mapId a ▷ app a = app a ◁ G.mapId a ≫ (ρ_ (app a)).hom ≫ (fun_ (app a)).inv  [default: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : naturality (f ≫ g) ≫ F.mapComp f g ▷ app c = app a ◁ G.mapComp f g ≫ (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫ (α_ _ _ _).inv  [default: by cat_disch]

中文:
结构 LaxTrans
  参数: (F G : OplaxFunctor B C)
  公理与运算 (5 个):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : app a ≫ G.map f ⟶ F.map f ≫ app b
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g  [默认: by cat_disch]
    - naturality_id((a : B)) : naturality (𝟙 a) ≫ F.mapId a ▷ app a = app a ◁ G.mapId a ≫ (ρ_ (app a)).hom ≫ (fun_ (app a)).inv  [默认: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : naturality (f ≫ g) ≫ F.mapComp f g ▷ app c = app a ◁ G.mapComp f g ≫ (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫ (α_ _ _ _).inv  [默认: by cat_disch]

Depends on / 依赖: F.map, F.mapComp, F.mapId, G.map, G.mapComp, G.mapId, cat_disch, fun_, mapComp, naturality, naturality_comp, naturality_id
-/
structure LaxTrans (F G : OplaxFunctor B C) where
  /-- The component 1-morphisms of a lax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the lax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map f ⟶ F.map f ≫ app b
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g := by
    cat_disch
  naturality_id (a : B) :
      naturality (𝟙 a) ≫ F.mapId a ▷ app a =
        app a ◁ G.mapId a ≫ (ρ_ (app a)).hom ≫ (fun_ (app a)).inv := by
    cat_disch
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      naturality (f ≫ g) ≫ F.mapComp f g ▷ app c =
        app a ◁ G.mapComp f g ≫ (α_ _ _ _).inv ≫
          naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫
            F.map f ◁ naturality g ≫ (α_ _ _ _).inv := by
    cat_disch

namespace LaxTrans

attribute [reassoc (attr := simp)] naturality_naturality naturality_id naturality_comp

variable {F G H : OplaxFunctor B C}
variable (η : LaxTrans F G) (θ : LaxTrans G H)

variable (F) in
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : LaxTrans F F where
  body: 𝟙 (F.obj a)
  naturality {_ _} f := (fun_ (F.map f)).hom ≫ (ρ_ (F.map f)).inv

中文:
定义 id
  签名: : LaxTrans F F where
  定义体: 𝟙 (F.obj a)
  naturality {_ _} f := (fun_ (F.map f)).hom ≫ (ρ_ (F.map f)).inv

Depends on / 依赖: F.obj
-/
def id : LaxTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (fun_ (F.map f)).hom ≫ (ρ_ (F.map f)).inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (LaxTrans F F)
  body: ⟨id F⟩

中文:
实例 :
  签名: Inhabited (LaxTrans F F)
  定义体: ⟨id F⟩
-/
instance : Inhabited (LaxTrans F F) :=
  ⟨id F⟩

/--
Definition of `vCompApp` / `vCompApp` 的定义

English:
abbreviation vCompApp
  signature: (a : B)
  body: η.app a ≫ θ.app a

中文:
缩写 vCompApp
  签名: (a : B)
  定义体: η.app a ≫ θ.app a
-/
abbrev vCompApp (a : B) : F.obj a ⟶ H.obj a :=
  η.app a ≫ θ.app a

/--
Definition of `vCompNaturality` / `vCompNaturality` 的定义

English:
abbreviation vCompNaturality
  signature: {a b : B} (f : a ⟶ b)
  body: (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv ≫
    η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom

中文:
缩写 vCompNaturality
  签名: {a b : B} (f : a ⟶ b)
  定义体: (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv ≫
    η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom

Depends on / 依赖: naturality
-/
abbrev vCompNaturality {a b : B} (f : a ⟶ b) :
    (η.app a ≫ θ.app a) ≫ H.map f ⟶ F.map f ≫ η.app b ≫ θ.app b :=
  (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv ≫
    η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom

/--
theorem `vComp_naturality_naturality` / 定理 `vComp_naturality_naturality`

English:
theorem vComp_naturality_naturality
  given: {a b : B} {f g : a ⟶ b} (β : f ⟶ g)
  proof: calc
    _ = 𝟙 _ otimes≫ η.app a ◁ θ.naturality f otimes≫
          (η.naturality f ≫ F.map₂ β ▷ η.app b) ▷ θ.app b otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality f ≫ G.map₂ β ▷ θ.app b) otimes≫
          η.naturality g ▷ θ.app b otimes≫ 𝟙 _ := by
      rw [naturality

中文:
定理 vComp_naturality_naturality
  条件: {a b : B} {f g : a ⟶ b} (β : f ⟶ g)
  证明: calc
    _ = 𝟙 _ otimes≫ η.app a ◁ θ.naturality f otimes≫
          (η.naturality f ≫ F.map₂ β ▷ η.app b) ▷ θ.app b otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality f ≫ G.map₂ β ▷ θ.app b) otimes≫
          η.naturality g ▷ θ.app b otimes≫ 𝟙 _ := by
      rw [naturality

Depends on / 依赖: F.map, G.map, bicategory, naturality, naturality_naturality, otimes
-/
theorem vComp_naturality_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) :
    η.vCompNaturality θ f ≫ F.map₂ β ▷ η.vCompApp θ b =
      η.vCompApp θ a ◁ H.map₂ β ≫ η.vCompNaturality θ g :=
  calc
    _ = 𝟙 _ otimes≫ η.app a ◁ θ.naturality f otimes≫
          (η.naturality f ≫ F.map₂ β ▷ η.app b) ▷ θ.app b otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality f ≫ G.map₂ β ▷ θ.app b) otimes≫
          η.naturality g ▷ θ.app b otimes≫ 𝟙 _ := by
      rw [naturality_naturality]
      bicategory
    _ = _ := by
      rw [naturality_naturality]
      bicategory

/--
theorem `vComp_naturality_id` / 定理 `vComp_naturality_id`

English:
theorem vComp_naturality_id
  given: (a : B)
  proof: by
  calc
    _ = 𝟙 _ otimes≫ η.app a ◁ θ.naturality (𝟙 a) otimes≫
          (η.naturality (𝟙 a) ≫ F.mapId a ▷ η.app a) ▷ θ.app a otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality (𝟙 a) ≫ G.mapId a ▷ θ.app a) otimes≫ 𝟙 _ := by
      rw [η.naturality_id]
      bicategory


中文:
定理 vComp_naturality_id
  条件: (a : B)
  证明: by
  calc
    _ = 𝟙 _ otimes≫ η.app a ◁ θ.naturality (𝟙 a) otimes≫
          (η.naturality (𝟙 a) ≫ F.mapId a ▷ η.app a) ▷ θ.app a otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality (𝟙 a) ≫ G.mapId a ▷ θ.app a) otimes≫ 𝟙 _ := by
      rw [η.naturality_id]
      bicategory


Depends on / 依赖: F.mapId, G.mapId, bicategory, naturality, naturality_id, otimes
-/
theorem vComp_naturality_id (a : B) :
    η.vCompNaturality θ (𝟙 a) ≫ F.mapId a ▷ η.vCompApp θ a =
      η.vCompApp θ a ◁ H.mapId a ≫ (ρ_ (η.vCompApp θ a)).hom ≫ (fun_ (η.vCompApp θ a)).inv := by
  calc
    _ = 𝟙 _ otimes≫ η.app a ◁ θ.naturality (𝟙 a) otimes≫
          (η.naturality (𝟙 a) ≫ F.mapId a ▷ η.app a) ▷ θ.app a otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality (𝟙 a) ≫ G.mapId a ▷ θ.app a) otimes≫ 𝟙 _ := by
      rw [η.naturality_id]
      bicategory
    _ = _ := by
      rw [θ.naturality_id]
      bicategory

/--
theorem `vComp_naturality_comp` / 定理 `vComp_naturality_comp`

English:
theorem vComp_naturality_comp
  given: {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
  proof: by
  calc
    _ = 𝟙 _ otimes≫ η.app a ◁ θ.naturality (f ≫ g) otimes≫
          (η.naturality (f ≫ g) ≫ F.mapComp f g ▷ η.app c) ▷ θ.app c otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality (f ≫ g) ≫ G.mapComp f g ▷ θ.app c) otimes≫
          (η.naturality f ▷ G.map g otim

中文:
定理 vComp_naturality_comp
  条件: {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
  证明: by
  calc
    _ = 𝟙 _ otimes≫ η.app a ◁ θ.naturality (f ≫ g) otimes≫
          (η.naturality (f ≫ g) ≫ F.mapComp f g ▷ η.app c) ▷ θ.app c otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality (f ≫ g) ≫ G.mapComp f g ▷ θ.app c) otimes≫
          (η.naturality f ▷ G.map g otim

Depends on / 依赖: F.map, F.mapComp, G.map, G.mapComp, H.map, H.mapComp, bicategory, mapComp, naturalit, naturality, naturality_comp, otimes
-/
theorem vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    η.vCompNaturality θ (f ≫ g) ≫ F.mapComp f g ▷ η.vCompApp θ c =
      η.vCompApp θ a ◁ H.mapComp f g ≫
        (α_ (η.vCompApp θ a) (H.map f) (H.map g)).inv ≫
          η.vCompNaturality θ f ▷ H.map g ≫
            (α_ (F.map f) (η.vCompApp θ b) (H.map g)).hom ≫
              F.map f ◁ η.vCompNaturality θ g ≫ (α_ (F.map f) (F.map g) (η.vCompApp θ c)).inv := by
  calc
    _ = 𝟙 _ otimes≫ η.app a ◁ θ.naturality (f ≫ g) otimes≫
          (η.naturality (f ≫ g) ≫ F.mapComp f g ▷ η.app c) ▷ θ.app c otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality (f ≫ g) ≫ G.mapComp f g ▷ θ.app c) otimes≫
          (η.naturality f ▷ G.map g otimes≫ F.map f ◁ η.naturality g) ▷ θ.app c otimes≫ 𝟙 _ := by
      rw [η.naturality_comp]
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.app a ◁ H.mapComp f g otimes≫ θ.naturality f ▷ H.map g) otimes≫
          ((η.app a ≫ G.map f) ◁ θ.naturality g ≫ η.naturality f ▷ (G.map g ≫ θ.app c)) otimes≫
            F.map f ◁ η.naturality g ▷ θ.app c otimes≫ 𝟙 _ := by
      rw [θ.naturality_comp]
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

/--
Definition of `vComp` / `vComp` 的定义

English:
definition vComp
  signature: (η : LaxTrans F G) (θ : LaxTrans G H)
  body: vCompApp η θ a
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

中文:
定义 vComp
  签名: (η : LaxTrans F G) (θ : LaxTrans G H)
  定义体: vCompApp η θ a
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

Depends on / 依赖: vCompApp
-/
def vComp (η : LaxTrans F G) (θ : LaxTrans G H) : LaxTrans F H where
  app a := vCompApp η θ a
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

attribute [local simp] vCompApp vCompNaturality in
/-- `CategoryStruct` on `OplaxFunctor B C` where the (1-)morphisms are given by lax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance : CategoryStruct (OplaxFunctor B C) where
  Hom := LaxTrans
  id := LaxTrans.id
  comp := LaxTrans.vComp

end LaxTrans

/--
Definition of `OplaxTrans` / `OplaxTrans` 的定义

English:
structure OplaxTrans
  parameters: (F G : B ⥤ᵒᵖᴸ C)
  axioms and operations (5):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ≫ app b ⟶ app a ≫ G.map f
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η  [default: by cat_disch]
    - naturality_id((a : B)) : naturality (𝟙 a) ≫ app a ◁ G.mapId a = F.mapId a ▷ app a ≫ (fun_ (app a)).hom ≫ (ρ_ (app a)).inv  [default: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : naturality (f ≫ g) ≫ app a ◁ G.mapComp f g = F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom  [default: by cat_disch]

中文:
结构 OplaxTrans
  参数: (F G : B ⥤ᵒᵖᴸ C)
  公理与运算 (5 个):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ≫ app b ⟶ app a ≫ G.map f
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η  [默认: by cat_disch]
    - naturality_id((a : B)) : naturality (𝟙 a) ≫ app a ◁ G.mapId a = F.mapId a ▷ app a ≫ (fun_ (app a)).hom ≫ (ρ_ (app a)).inv  [默认: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : naturality (f ≫ g) ≫ app a ◁ G.mapComp f g = F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom  [默认: by cat_disch]

Depends on / 依赖: F.map, F.mapComp, F.mapId, G.map, G.mapComp, G.mapId, cat_disch, fun_, mapComp, naturality, naturality_comp, naturality_id
-/
structure OplaxTrans (F G : B ⥤ᵒᵖᴸ C) where
  /-- The component 1-morphisms of an oplax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the oplax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η := by
    cat_disch
  naturality_id (a : B) :
      naturality (𝟙 a) ≫ app a ◁ G.mapId a =
        F.mapId a ▷ app a ≫ (fun_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    cat_disch
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      naturality (f ≫ g) ≫ app a ◁ G.mapComp f g =
        F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫
          (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom := by
    cat_disch

attribute [reassoc (attr := simp)] OplaxTrans.naturality_naturality OplaxTrans.naturality_id
  OplaxTrans.naturality_comp

namespace OplaxTrans

variable {F : B ⥤ᵒᵖᴸ C} {G H : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G) (θ : OplaxTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_naturality_naturality` / 定理 `whiskerLeft_naturality_naturality`

English:
theorem whiskerLeft_naturality_naturality
  given: (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h)
  proof: by
  simp_rw [← whiskerLeft_comp, naturality_naturality]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_naturality_naturality
  条件: (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h)
  证明: by
  simp_rw [← whiskerLeft_comp, naturality_naturality]

@[reassoc (attr := simp)]

Depends on / 依赖: naturality_naturality, simp_rw, whiskerLeft_comp
-/
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ θ.naturality h =
      f ◁ θ.naturality g ≫ f ◁ θ.app a ◁ H.map₂ β := by
  simp_rw [← whiskerLeft_comp, naturality_naturality]

@[reassoc (attr := simp)]
/--
theorem `whiskerRight_naturality_naturality` / 定理 `whiskerRight_naturality_naturality`

English:
theorem whiskerRight_naturality_naturality
  given: {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a')
  proof: by
  rw [← comp_whiskerRight]; rw [naturality_naturality]; rw [comp_whiskerRight]; rw [whisker_assoc]

@[reassoc (attr := simp)]

中文:
定理 whiskerRight_naturality_naturality
  条件: {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a')
  证明: by
  rw [← comp_whiskerRight]; rw [naturality_naturality]; rw [comp_whiskerRight]; rw [whisker_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight, naturality_naturality, whisker_assoc
-/
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ η.naturality g ▷ h =
      η.naturality f ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv := by
  rw [← comp_whiskerRight]; rw [naturality_naturality]; rw [comp_whiskerRight]; rw [whisker_assoc]

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_naturality_comp` / 定理 `whiskerLeft_naturality_comp`

English:
theorem whiskerLeft_naturality_comp
  given: (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c)
  proof: by
  simp_rw [← whiskerLeft_comp, naturality_comp]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_naturality_comp
  条件: (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c)
  证明: by
  simp_rw [← whiskerLeft_comp, naturality_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: naturality_comp, simp_rw, whiskerLeft_comp
-/
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ θ.naturality (g ≫ h) ≫ f ◁ θ.app a ◁ H.mapComp g h =
      f ◁ G.mapComp g h ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ θ.naturality h ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ θ.naturality g ▷ H.map h ≫ f ◁ (α_ _ _ _).hom := by
  simp_rw [← whiskerLeft_comp, naturality_comp]

@[reassoc (attr := simp)]
/--
theorem `whiskerRight_naturality_comp` / 定理 `whiskerRight_naturality_comp`

English:
theorem whiskerRight_naturality_comp
  given: (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a')
  proof: by
  rw [← associator_naturality_middle]; rw [← comp_whiskerRight_assoc]; rw [naturality_comp]; simp

@[reassoc (attr := simp)]

中文:
定理 whiskerRight_naturality_comp
  条件: (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a')
  证明: by
  rw [← associator_naturality_middle]; rw [← comp_whiskerRight_assoc]; rw [naturality_comp]; simp

@[reassoc (attr := simp)]

Depends on / 依赖: associator_naturality_middle, comp_whiskerRight_assoc, naturality_comp
-/
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    η.naturality (f ≫ g) ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h =
      F.mapComp f g ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ η.naturality g ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                  η.naturality f ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle]; rw [← comp_whiskerRight_assoc]; rw [naturality_comp]; simp

@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_naturality_id` / 定理 `whiskerLeft_naturality_id`

English:
theorem whiskerLeft_naturality_id
  given: (f : a' ⟶ G.obj a)
  proof: by
  simp_rw [← whiskerLeft_comp, naturality_id]

@[reassoc (attr := simp)]

中文:
定理 whiskerLeft_naturality_id
  条件: (f : a' ⟶ G.obj a)
  证明: by
  simp_rw [← whiskerLeft_comp, naturality_id]

@[reassoc (attr := simp)]

Depends on / 依赖: naturality_id, simp_rw, whiskerLeft_comp
-/
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ θ.naturality (𝟙 a) ≫ f ◁ θ.app a ◁ H.mapId a =
      f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (fun_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv := by
  simp_rw [← whiskerLeft_comp, naturality_id]

@[reassoc (attr := simp)]
/--
theorem `whiskerRight_naturality_id` / 定理 `whiskerRight_naturality_id`

English:
theorem whiskerRight_naturality_id
  given: (f : G.obj a ⟶ a')
  proof: by
  rw [← associator_naturality_middle]; rw [← comp_whiskerRight_assoc]; rw [naturality_id]; simp

中文:
定理 whiskerRight_naturality_id
  条件: (f : G.obj a ⟶ a')
  证明: by
  rw [← associator_naturality_middle]; rw [← comp_whiskerRight_assoc]; rw [naturality_id]; simp

Depends on / 依赖: associator_naturality_middle, comp_whiskerRight_assoc, naturality_id
-/
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    η.naturality (𝟙 a) ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f =
    F.mapId a ▷ η.app a ▷ f ≫ (fun_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle]; rw [← comp_whiskerRight_assoc]; rw [naturality_id]; simp

end

variable (F) in
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : OplaxTrans F F where
  body: 𝟙 (F.obj a)
  naturality {_ _} f := (ρ_ (F.map f)).hom ≫ (fun_ (F.map f)).inv

中文:
定义 id
  签名: : OplaxTrans F F where
  定义体: 𝟙 (F.obj a)
  naturality {_ _} f := (ρ_ (F.map f)).hom ≫ (fun_ (F.map f)).inv

Depends on / 依赖: F.obj
-/
def id : OplaxTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (ρ_ (F.map f)).hom ≫ (fun_ (F.map f)).inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (OplaxTrans F F)
  body: ⟨id F⟩

中文:
实例 :
  签名: Inhabited (OplaxTrans F F)
  定义体: ⟨id F⟩
-/
instance : Inhabited (OplaxTrans F F) :=
  ⟨id F⟩

/--
Definition of `vcomp` / `vcomp` 的定义

English:
definition vcomp
  signature: : OplaxTrans F H where
  body: η.app a ≫ θ.app a
  naturality {a b} f :=
    (α_ _ _ _).inv ≫
      η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv
  naturality_comp {a b c} f g :=
    calc
      _ =
        (α_ _ _ _).inv ≫
          F.mapComp f g ▷ η.app c ▷ θ.app c ≫
            (α_ _ _ _)

中文:
定义 vcomp
  签名: : OplaxTrans F H where
  定义体: η.app a ≫ θ.app a
  naturality {a b} f :=
    (α_ _ _ _).inv ≫
      η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv
  naturality_comp {a b c} f g :=
    calc
      _ =
        (α_ _ _ _).inv ≫
          F.mapComp f g ▷ η.app c ▷ θ.app c ≫
            (α_ _ _ _)
-/
def vcomp : OplaxTrans F H where
  app a := η.app a ≫ θ.app a
  naturality {a b} f :=
    (α_ _ _ _).inv ≫
      η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv
  naturality_comp {a b c} f g :=
    calc
      _ =
        (α_ _ _ _).inv ≫
          F.mapComp f g ▷ η.app c ▷ θ.app c ≫
            (α_ _ _ _).hom ▷ _ ≫ (α_ _ _ _).hom ≫
              F.map f ◁ η.naturality g ▷ θ.app c ≫
                _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫
                  (F.map f ≫ η.app b) ◁ θ.naturality g ≫
                    η.naturality f ▷ (θ.app b ≫ H.map g) ≫
                      (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv ≫
                        η.app a ◁ θ.naturality f ▷ H.map g ≫
                          _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv := by
        rw [whisker_exchange_assoc]; simp
      _ = _ := by simp

/-- `CategoryStruct` on `B ⥤ᵒᵖᴸ C` where the (1-)morphisms are given by oplax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance categoryStruct : CategoryStruct (B ⥤ᵒᵖᴸ C) where
  Hom := OplaxTrans
  id := OplaxTrans.id
  comp := OplaxTrans.vcomp

end OplaxTrans

/--
Definition of `StrongTrans` / `StrongTrans` 的定义

English:
structure StrongTrans
  parameters: (F G : B ⥤ᵒᵖᴸ C)
  axioms and operations (5):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ≫ app b ≅ app a ≫ G.map f
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η  [default: by cat_disch]
    - naturality_id((a : B)) : (naturality (𝟙 a)).hom ≫ app a ◁ G.mapId a = F.mapId a ▷ app a ≫ (fun_ (app a)).hom ≫ (ρ_ (app a)).inv  [default: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : (naturality (f ≫ g)).hom ≫ app a ◁ G.mapComp f g = F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫ (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom  [default: by cat_disch]

中文:
结构 StrongTrans
  参数: (F G : B ⥤ᵒᵖᴸ C)
  公理与运算 (5 个):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ≫ app b ≅ app a ≫ G.map f
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η  [默认: by cat_disch]
    - naturality_id((a : B)) : (naturality (𝟙 a)).hom ≫ app a ◁ G.mapId a = F.mapId a ▷ app a ≫ (fun_ (app a)).hom ≫ (ρ_ (app a)).inv  [默认: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : (naturality (f ≫ g)).hom ≫ app a ◁ G.mapComp f g = F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫ (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom  [默认: by cat_disch]

Depends on / 依赖: F.map, F.mapComp, F.mapId, G.map, G.mapComp, G.mapId, cat_disch, fun_, mapComp, naturality, naturality_comp, naturality_id
-/
structure StrongTrans (F G : B ⥤ᵒᵖᴸ C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    cat_disch
  naturality_id (a : B) :
      (naturality (𝟙 a)).hom ≫ app a ◁ G.mapId a =
        F.mapId a ▷ app a ≫ (fun_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    cat_disch
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      (naturality (f ≫ g)).hom ≫ app a ◁ G.mapComp f g =
        F.mapComp f g ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
    cat_disch

attribute [nolint docBlame] CategoryTheory.Oplax.StrongTrans.app
  CategoryTheory.Oplax.StrongTrans.naturality

attribute [reassoc (attr := simp)] StrongTrans.naturality_naturality
  StrongTrans.naturality_id StrongTrans.naturality_comp

/--
Definition of `OplaxTrans.StrongCore` / `OplaxTrans.StrongCore` 的定义

English:
structure OplaxTrans.StrongCore
  parameters: {F G : B ⥤ᵒᵖᴸ C} (η : F ⟶ G)
  axioms and operations (2):
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ≫ η.app b ≅ η.app a ≫ G.map f
    - naturality_hom({a b : B} (f : a ⟶ b)) : (naturality f).hom = η.naturality f  [default: by cat_disch]

中文:
结构 OplaxTrans.StrongCore
  参数: {F G : B ⥤ᵒᵖᴸ C} (η : F ⟶ G)
  公理与运算 (2 个):
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ≫ η.app b ≅ η.app a ≫ G.map f
    - naturality_hom({a b : B} (f : a ⟶ b)) : (naturality f).hom = η.naturality f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure OplaxTrans.StrongCore {F G : B ⥤ᵒᵖᴸ C} (η : F ⟶ G) where
  /-- The underlying 2-isomorphisms of the naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ η.app b ≅ η.app a ≫ G.map f
  /-- The 2-isomorphisms agree with the underlying 2-morphism of the oplax transformation. -/
  naturality_hom {a b : B} (f : a ⟶ b) : (naturality f).hom = η.naturality f := by cat_disch

attribute [simp] OplaxTrans.StrongCore.naturality_hom

namespace StrongTrans

/-- The underlying oplax natural transformation of a strong natural transformation. -/
@[simps]
/--
Definition of `toOplax` / `toOplax` 的定义

English:
definition toOplax
  signature: {F G : B ⥤ᵒᵖᴸ C} (η : StrongTrans F G)
  body: η.app
  naturality f := (η.naturality f).hom

中文:
定义 toOplax
  签名: {F G : B ⥤ᵒᵖᴸ C} (η : StrongTrans F G)
  定义体: η.app
  naturality f := (η.naturality f).hom
-/
def toOplax {F G : B ⥤ᵒᵖᴸ C} (η : StrongTrans F G) : OplaxTrans F G where
  app := η.app
  naturality f := (η.naturality f).hom

/--
Definition of `mkOfOplax` / `mkOfOplax` 的定义

English:
definition mkOfOplax
  signature: {F G : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G) (η' : OplaxTrans.StrongCore η)
  body: η.app
  naturality := η'.naturality

中文:
定义 mkOfOplax
  签名: {F G : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G) (η' : OplaxTrans.StrongCore η)
  定义体: η.app
  naturality := η'.naturality
-/
def mkOfOplax {F G : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G) (η' : OplaxTrans.StrongCore η) :
    StrongTrans F G where
  app := η.app
  naturality := η'.naturality

/--
Definition of `mkOfOplax'` / `mkOfOplax'` 的定义

English:
definition mkOfOplax'
  signature: {F G : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G)
  body: η.app
  naturality _ := asIso (η.naturality _)

中文:
定义 mkOfOplax'
  签名: {F G : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G)
  定义体: η.app
  naturality _ := asIso (η.naturality _)
-/
noncomputable def mkOfOplax' {F G : B ⥤ᵒᵖᴸ C} (η : OplaxTrans F G)
    [forall a b (f : a ⟶ b), IsIso (η.naturality f)] : StrongTrans F G where
  app := η.app
  naturality _ := asIso (η.naturality _)

variable (F : B ⥤ᵒᵖᴸ C)


/-- The identity strong natural transformation. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : StrongTrans F F
  body: mkOfOplax (OplaxTrans.id F) { naturality := fun f => (ρ_ (F.map f)) ≪≫ (fun_ (F.map f)).symm }

@[simp]

中文:
定义 id
  签名: : StrongTrans F F
  定义体: mkOfOplax (OplaxTrans.id F) { naturality := fun f => (ρ_ (F.map f)) ≪≫ (fun_ (F.map f)).symm }

@[simp]

Depends on / 依赖: F.map, F.op, OplaxTrans, OplaxTrans.id, fun_, functor, mkOfOplax, naturality, opOpEquivalence
-/
def id : StrongTrans F F :=
  mkOfOplax (OplaxTrans.id F) { naturality := fun f => (ρ_ (F.map f)) ≪≫ (fun_ (F.map f)).symm }

@[simp]
/--
lemma `id.toOplax` / 引理 `id.toOplax`

English:
lemma id.toOplax
  statement: (id F).toOplax = OplaxTrans.id F
  proof: rfl

中文:
引理 id.toOplax
  结论: (id F).toOplax = OplaxTrans.id F
  证明: rfl

Depends on / 依赖: F.op, Initial, functor, opOpEquivalence
-/
lemma id.toOplax : (id F).toOplax = OplaxTrans.id F :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (StrongTrans F F)
  body: ⟨id F⟩

中文:
实例 :
  签名: Inhabited (StrongTrans F F)
  定义体: ⟨id F⟩

Depends on / 依赖: F.op, inverse, opOpEquivalence
-/
instance : Inhabited (StrongTrans F F) :=
  ⟨id F⟩


variable {F} {G H : B ⥤ᵒᵖᴸ C} (η : StrongTrans F G) (θ : StrongTrans G H)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Vertical composition of strong natural transformations. -/
@[simps!]
/--
Definition of `vcomp` / `vcomp` 的定义

English:
definition vcomp
  signature: : StrongTrans F H
  body: mkOfOplax (OplaxTrans.vcomp η.toOplax θ.toOplax)
    { naturality := fun {a b} f =>
        (α_ _ _ _).symm ≪≫ whiskerRightIso (η.naturality f) (θ.app b) ≪≫
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm }

中文:
定义 vcomp
  签名: : StrongTrans F H
  定义体: mkOfOplax (OplaxTrans.vcomp η.toOplax θ.toOplax)
    { naturality := fun {a b} f =>
        (α_ _ _ _).symm ≪≫ whiskerRightIso (η.naturality f) (θ.app b) ≪≫
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm }

Depends on / 依赖: F.op, Initial, OplaxTrans, OplaxTrans.vcomp, inverse, mkOfOplax, naturality, opOpEquivalence, toOplax, whiskerLeftIso, whiskerRightIso
-/
def vcomp : StrongTrans F H :=
  mkOfOplax (OplaxTrans.vcomp η.toOplax θ.toOplax)
    { naturality := fun {a b} f =>
        (α_ _ _ _).symm ≪≫ whiskerRightIso (η.naturality f) (θ.app b) ≪≫
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm }

/-- `CategoryStruct` on `B ⥤ᵒᵖᴸ C` where the (1-)morphisms are given by strong
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance categoryStruct : CategoryStruct (B ⥤ᵒᵖᴸ C) where
  Hom := StrongTrans
  id := StrongTrans.id
  comp := StrongTrans.vcomp

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp), to_app]
/--
theorem `whiskerLeft_naturality_naturality` / 定理 `whiskerLeft_naturality_naturality`

English:
theorem whiskerLeft_naturality_naturality
  given: (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h)
  proof: by
  apply θ.toOplax.whiskerLeft_naturality_naturality

@[reassoc (attr := simp), to_app]

中文:
定理 whiskerLeft_naturality_naturality
  条件: (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h)
  证明: by
  apply θ.toOplax.whiskerLeft_naturality_naturality

@[reassoc (attr := simp), to_app]

Depends on / 依赖: toOplax, toOplax.whiskerLeft_naturality_naturality, whiskerLeft_naturality_naturality
-/
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom =
      f ◁ (θ.naturality g).hom ≫ f ◁ θ.app a ◁ H.map₂ β := by
  apply θ.toOplax.whiskerLeft_naturality_naturality

@[reassoc (attr := simp), to_app]
/--
theorem `whiskerRight_naturality_naturality` / 定理 `whiskerRight_naturality_naturality`

English:
theorem whiskerRight_naturality_naturality
  given: {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a')
  proof: η.toOplax.whiskerRight_naturality_naturality _ _

@[reassoc (attr := simp), to_app]

中文:
定理 whiskerRight_naturality_naturality
  条件: {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a')
  证明: η.toOplax.whiskerRight_naturality_naturality _ _

@[reassoc (attr := simp), to_app]

Depends on / 依赖: toOplax, toOplax.whiskerRight_naturality_naturality, whiskerRight_naturality_naturality
-/
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h =
      (η.naturality f).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv :=
  η.toOplax.whiskerRight_naturality_naturality _ _

@[reassoc (attr := simp), to_app]
/--
theorem `whiskerLeft_naturality_comp` / 定理 `whiskerLeft_naturality_comp`

English:
theorem whiskerLeft_naturality_comp
  given: (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c)
  proof: θ.toOplax.whiskerLeft_naturality_comp _ _ _

@[reassoc (attr := simp), to_app]

中文:
定理 whiskerLeft_naturality_comp
  条件: (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c)
  证明: θ.toOplax.whiskerLeft_naturality_comp _ _ _

@[reassoc (attr := simp), to_app]

Depends on / 依赖: toOplax, toOplax.whiskerLeft_naturality_comp, whiskerLeft_naturality_comp
-/
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ H.mapComp g h =
      f ◁ G.mapComp g h ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ (θ.naturality h).hom ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom :=
  θ.toOplax.whiskerLeft_naturality_comp _ _ _

@[reassoc (attr := simp), to_app]
/--
theorem `whiskerRight_naturality_comp` / 定理 `whiskerRight_naturality_comp`

English:
theorem whiskerRight_naturality_comp
  given: (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a')
  proof: η.toOplax.whiskerRight_naturality_comp _ _ _

#adaptation_note

中文:
定理 whiskerRight_naturality_comp
  条件: (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a')
  证明: η.toOplax.whiskerRight_naturality_comp _ _ _

#adaptation_note

Depends on / 依赖: toOplax, toOplax.whiskerRight_naturality_comp, whiskerRight_naturality_comp
-/
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (η.naturality (f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h =
      F.mapComp f g ▷ η.app c ▷ h ≫
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
/--
theorem `whiskerLeft_naturality_id` / 定理 `whiskerLeft_naturality_id`

English:
theorem whiskerLeft_naturality_id
  given: (f : a' ⟶ G.obj a)
  proof: θ.toOplax.whiskerLeft_naturality_id _

#adaptation_note

中文:
定理 whiskerLeft_naturality_id
  条件: (f : a' ⟶ G.obj a)
  证明: θ.toOplax.whiskerLeft_naturality_id _

#adaptation_note

Depends on / 依赖: toOplax, toOplax.whiskerLeft_naturality_id, whiskerLeft_naturality_id
-/
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ (θ.naturality (𝟙 a)).hom ≫ f ◁ θ.app a ◁ H.mapId a =
      f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (fun_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv :=
  θ.toOplax.whiskerLeft_naturality_id _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp), to_app]
/--
theorem `whiskerRight_naturality_id` / 定理 `whiskerRight_naturality_id`

English:
theorem whiskerRight_naturality_id
  given: (f : G.obj a ⟶ a')
  proof: η.toOplax.whiskerRight_naturality_id _

中文:
定理 whiskerRight_naturality_id
  条件: (f : G.obj a ⟶ a')
  证明: η.toOplax.whiskerRight_naturality_id _

Depends on / 依赖: toOplax, toOplax.whiskerRight_naturality_id, whiskerRight_naturality_id
-/
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (η.naturality (𝟙 a)).hom ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f =
    F.mapId a ▷ η.app a ▷ f ≫ (fun_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫
    (α_ _ _ _).hom :=
  η.toOplax.whiskerRight_naturality_id _

end

end StrongTrans

end CategoryTheory.Oplax
