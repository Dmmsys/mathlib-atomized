/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Lax
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Transformations between lax functors

Just as there are natural transformations between functors, there are transformations
between lax functors. The equality in the naturality condition of a natural transformation gets
replaced by a specified 2-morphism. Now, there are three possible types of transformations (between
lax functors):
* lax natural transformations;
* oplax natural transformations;
* strong natural transformations.

These differ in the direction (and invertibility) of the 2-morphisms involved in the naturality
condition.

## Main definitions

* `Lax.LaxTrans F G`: lax transformations between lax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `app a ≫ G.map f ⟶ F.map f ≫ app b` for each 1-morphism
  `f : a ⟶ b`.
* `Lax.OplaxTrans F G`: oplax transformations between lax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.
* `Lax.StrongTrans F G`: strong transformations between lax functors `F` and `G`. The naturality
  condition is given by a 2-isomorphism `app a ≫ G.map f ≅ F.map f ≫ app b` for each 1-morphism
  `f : a ⟶ b`.

Using these, we define three (scoped) `CategoryStruct` instances on `B ⥤ᴸ C`, in the
`Lax.LaxTrans`, `Lax.OplaxTrans`, and `Lax.StrongTrans` namespaces. The arrows in these
`CategoryStruct` instances are given by lax transformations, oplax transformations, and strong
transformations respectively.

We also provide API for going between lax transformations and strong transformations:
* `LaxTrans.StrongCore η`: a structure on a lax transformation between lax functors that
  promotes it to a strong transformation.
* `StrongTrans.mkOfLax η η'`: given a lax transformation `η` such that each component
  2-morphism is an isomorphism, `mkOfLax` gives the corresponding strong transformation.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055),
  section 4.2.

-/

@[expose] public section

namespace CategoryTheory.Lax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/--
Definition of `LaxTrans` / `LaxTrans` 的定义

English:
structure LaxTrans
  parameters: (F G : B ⥤ᴸ C)
  axioms and operations (5):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : app a ≫ G.map f ⟶ F.map f ≫ app b
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g  [default: by cat_disch]
    - naturality_id((a : B)) : app a ◁ G.mapId a ≫ naturality (𝟙 a) = (ρ_ (app a)).hom ≫ (fun_ (app a)).inv ≫ F.mapId a ▷ app a  [default: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : app a ◁ G.mapComp f g ≫ naturality (f ≫ g) = (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c  [default: by cat_disch]

中文:
结构 LaxTrans
  参数: (F G : B ⥤ᴸ C)
  公理与运算 (5 个):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : app a ≫ G.map f ⟶ F.map f ≫ app b
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g  [默认: by cat_disch]
    - naturality_id((a : B)) : app a ◁ G.mapId a ≫ naturality (𝟙 a) = (ρ_ (app a)).hom ≫ (fun_ (app a)).inv ≫ F.mapId a ▷ app a  [默认: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : app a ◁ G.mapComp f g ≫ naturality (f ≫ g) = (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure LaxTrans (F G : B ⥤ᴸ C) where
  /-- The component 1-morphisms of a lax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the lax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map f ⟶ F.map f ≫ app b
  /-- Naturality of the lax naturality constraint. -/
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g := by
    cat_disch
  /-- Lax unity. -/
  naturality_id (a : B) :
      app a ◁ G.mapId a ≫ naturality (𝟙 a) =
        (ρ_ (app a)).hom ≫ (fun_ (app a)).inv ≫ F.mapId a ▷ app a := by
    cat_disch
  /-- Lax functoriality. -/
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      app a ◁ G.mapComp f g ≫ naturality (f ≫ g) =
      (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫
        F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c := by
    cat_disch

attribute [reassoc (attr := simp)] LaxTrans.naturality_naturality LaxTrans.naturality_id
  LaxTrans.naturality_comp

namespace LaxTrans

variable {F G H : B ⥤ᴸ C} (η : LaxTrans F G) (θ : LaxTrans G H)

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
  签名: 可居 (LaxTrans F F)
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
缩写 vComp自然数urality
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
  proof: calc
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.app a ◁ H.mapId a ≫ θ.naturality (𝟙 a)) otimes≫
          η.naturality (𝟙 a) ▷ θ.app a otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ (η.app a ◁ G.mapId a ≫ η.naturality (𝟙 a)) ▷ θ.app a otimes≫ 𝟙 _ := by
      rw [naturality_id]
      bicategory
    _ =

中文:
定理 vComp_naturality_id
  条件: (a : B)
  证明: calc
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.app a ◁ H.mapId a ≫ θ.naturality (𝟙 a)) otimes≫
          η.naturality (𝟙 a) ▷ θ.app a otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ (η.app a ◁ G.mapId a ≫ η.naturality (𝟙 a)) ▷ θ.app a otimes≫ 𝟙 _ := by
      rw [naturality_id]
      bicategory
    _ =

Depends on / 依赖: G.mapId, H.mapId, bicategory, naturality, naturality_id, otimes
-/
theorem vComp_naturality_id (a : B) :
    η.vCompApp θ a ◁ H.mapId a ≫ η.vCompNaturality θ (𝟙 a) =
      (ρ_ (η.vCompApp θ a)).hom ≫ (fun_ (η.vCompApp θ a)).inv ≫ F.mapId a ▷ η.vCompApp θ a :=
  calc
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.app a ◁ H.mapId a ≫ θ.naturality (𝟙 a)) otimes≫
          η.naturality (𝟙 a) ▷ θ.app a otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ (η.app a ◁ G.mapId a ≫ η.naturality (𝟙 a)) ▷ θ.app a otimes≫ 𝟙 _ := by
      rw [naturality_id]
      bicategory
    _ = _ := by
      rw [naturality_id]
      bicategory

/--
theorem `vComp_naturality_comp` / 定理 `vComp_naturality_comp`

English:
theorem vComp_naturality_comp
  given: {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
  proof: calc
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.app a ◁ H.mapComp f g ≫ θ.naturality (f ≫ g)) otimes≫
          η.naturality (f ≫ g) ▷ θ.app c otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality f ▷ (H.map g) otimes≫ G.map f ◁ θ.naturality g) otimes≫
          (η.app a ◁ G.mapComp f

中文:
定理 vComp_naturality_comp
  条件: {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
  证明: calc
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.app a ◁ H.mapComp f g ≫ θ.naturality (f ≫ g)) otimes≫
          η.naturality (f ≫ g) ▷ θ.app c otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality f ▷ (H.map g) otimes≫ G.map f ◁ θ.naturality g) otimes≫
          (η.app a ◁ G.mapComp f

Depends on / 依赖: G.map, G.mapComp, H.map, H.mapComp, bicategory, mapComp, naturality, naturality_comp, otimes
-/
theorem vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    η.vCompApp θ a ◁ H.mapComp f g ≫ η.vCompNaturality θ (f ≫ g) =
      (α_ (η.vCompApp θ a) (H.map f) (H.map g)).inv ≫
        η.vCompNaturality θ f ▷ H.map g ≫
          (α_ (F.map f) (η.vCompApp θ b) (H.map g)).hom ≫
            F.map f ◁ η.vCompNaturality θ g ≫
              (α_ (F.map f) (F.map g) (η.vCompApp θ c)).inv ≫ F.mapComp f g ▷ η.vCompApp θ c :=
  calc
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.app a ◁ H.mapComp f g ≫ θ.naturality (f ≫ g)) otimes≫
          η.naturality (f ≫ g) ▷ θ.app c otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (θ.naturality f ▷ (H.map g) otimes≫ G.map f ◁ θ.naturality g) otimes≫
          (η.app a ◁ G.mapComp f g ≫ η.naturality (f ≫ g)) ▷ θ.app c otimes≫ 𝟙 _ := by
      rw [naturality_comp θ]
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ θ.naturality f ▷ H.map g otimes≫
          ((η.app a ≫ G.map f) ◁ θ.naturality g ≫ η.naturality f ▷ (G.map g ≫ θ.app c)) otimes≫
            F.map f ◁ η.naturality g ▷ θ.app c otimes≫
              F.mapComp f g ▷ η.app c ▷ θ.app c otimes≫ 𝟙 _ := by
      rw [naturality_comp η]
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

Depends on / 依赖: HasLimit, comp_hasLimit, vCompApp
-/
def vComp (η : LaxTrans F G) (θ : LaxTrans G H) : LaxTrans F H where
  app a := vCompApp η θ a
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

attribute [local simp] vCompApp vCompNaturality in
/-- `CategoryStruct` on `B ⥤ᴸ C` where the (1-)morphisms are given by lax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance : CategoryStruct (B ⥤ᴸ C) where
  Hom := LaxTrans
  id := LaxTrans.id
  comp := LaxTrans.vComp

@[deprecated (since := "2026-03-16")] alias vComp_app := comp_app
@[deprecated (since := "2026-03-16")] alias vComp_naturality := comp_naturality

end LaxTrans

/--
Definition of `OplaxTrans` / `OplaxTrans` 的定义

English:
structure OplaxTrans
  parameters: (F G : B ⥤ᴸ C)
  axioms and operations (5):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ≫ app b ⟶ app a ≫ G.map f
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η  [default: by cat_disch]
    - naturality_id((a : B)) : F.mapId a ▷ app a ≫ naturality (𝟙 a) = (fun_ (app a)).hom ≫ (ρ_ (app a)).inv ≫ app a ◁ G.mapId a  [default: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : F.mapComp f g ▷ app c ≫ naturality (f ≫ g) = (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫ app a ◁ G.mapComp f g  [default: by cat_disch]

中文:
结构 OplaxTrans
  参数: (F G : B ⥤ᴸ C)
  公理与运算 (5 个):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ≫ app b ⟶ app a ≫ G.map f
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η  [默认: by cat_disch]
    - naturality_id((a : B)) : F.mapId a ▷ app a ≫ naturality (𝟙 a) = (fun_ (app a)).hom ≫ (ρ_ (app a)).inv ≫ app a ◁ G.mapId a  [默认: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : F.mapComp f g ▷ app c ≫ naturality (f ≫ g) = (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫ app a ◁ G.mapComp f g  [默认: by cat_disch]

Depends on / 依赖: Category, F.map, F.mapComp, F.mapId, G.map, G.mapComp, G.mapId, cat_disch, comp_preservesLimit, fun_, mapComp, naturality, naturality_comp, naturality_id
-/
structure OplaxTrans (F G : B ⥤ᴸ C) where
  /-- The component 1-morphisms of an oplax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the oplax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f
  /-- Naturality of the oplax naturality constraint. -/
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η := by
    cat_disch
  naturality_id (a : B) :
      F.mapId a ▷ app a ≫ naturality (𝟙 a) =
        (fun_ (app a)).hom ≫ (ρ_ (app a)).inv ≫ app a ◁ G.mapId a := by
    cat_disch
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      F.mapComp f g ▷ app c ≫ naturality (f ≫ g) =
        (α_ _ _ _).hom ≫ F.map f ◁ naturality g ≫
          (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫
            app a ◁ G.mapComp f g := by
    cat_disch

namespace OplaxTrans

attribute [reassoc (attr := simp)] naturality_naturality naturality_id naturality_comp

variable {F G H : B ⥤ᴸ C} (η : OplaxTrans F G) (θ : OplaxTrans G H)

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

Depends on / 依赖: Category, F.obj, comp_reflectsLimit
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
  签名: 可居 (OplaxTrans F F)
  定义体: ⟨id F⟩

Depends on / 依赖: Category, compCreatesLimit
-/
instance : Inhabited (OplaxTrans F F) :=
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
abbrev vCompApp (a : B) : F.obj a ⟶ H.obj a := η.app a ≫ θ.app a

/--
Definition of `vCompNaturality` / `vCompNaturality` 的定义

English:
abbreviation vCompNaturality
  signature: {a b : B} (f : a ⟶ b)
  body: (α_ _ _ _).inv ≫ η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫
    η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv

中文:
缩写 vComp自然数urality
  签名: {a b : B} (f : a ⟶ b)
  定义体: (α_ _ _ _).inv ≫ η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫
    η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv

Depends on / 依赖: naturality
-/
abbrev vCompNaturality {a b : B} (f : a ⟶ b) :
    F.map f ≫ η.app b ≫ θ.app b ⟶ (η.app a ≫ θ.app a) ≫ H.map f :=
  (α_ _ _ _).inv ≫ η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫
    η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv

/--
theorem `vComp_naturality_naturality` / 定理 `vComp_naturality_naturality`

English:
theorem vComp_naturality_naturality
  given: {a b : B} {f g : a ⟶ b} (β : f ⟶ g)
  proof: by
  calc
    _ = 𝟙 _ otimes≫ (F.map₂ β ▷ η.app b ≫ η.naturality g) ▷ θ.app b otimes≫
          η.app a ◁ θ.naturality g otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.naturality f ▷ θ.app b otimes≫
          η.app a ◁ (G.map₂ β ▷ θ.app b ≫ θ.naturality g) otimes≫ 𝟙 _ := by
      rw [η.nat

中文:
定理 vComp_naturality_naturality
  条件: {a b : B} {f g : a ⟶ b} (β : f ⟶ g)
  证明: by
  calc
    _ = 𝟙 _ otimes≫ (F.map₂ β ▷ η.app b ≫ η.naturality g) ▷ θ.app b otimes≫
          η.app a ◁ θ.naturality g otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.naturality f ▷ θ.app b otimes≫
          η.app a ◁ (G.map₂ β ▷ θ.app b ≫ θ.naturality g) otimes≫ 𝟙 _ := by
      rw [η.nat

Depends on / 依赖: F.map, G.map, bicategory, naturality, naturality_naturality, otimes
-/
theorem vComp_naturality_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) :
    F.map₂ β ▷ η.vCompApp θ b ≫ η.vCompNaturality θ g =
      η.vCompNaturality θ f ≫ η.vCompApp θ a ◁ H.map₂ β := by
  calc
    _ = 𝟙 _ otimes≫ (F.map₂ β ▷ η.app b ≫ η.naturality g) ▷ θ.app b otimes≫
          η.app a ◁ θ.naturality g otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.naturality f ▷ θ.app b otimes≫
          η.app a ◁ (G.map₂ β ▷ θ.app b ≫ θ.naturality g) otimes≫ 𝟙 _ := by
      rw [η.naturality_naturality]
      bicategory
    _ = _ := by
      rw [θ.naturality_naturality]
      bicategory

/--
theorem `vComp_naturality_id` / 定理 `vComp_naturality_id`

English:
theorem vComp_naturality_id
  given: (a : B)
  proof: by
  calc
    _ = 𝟙 _ otimes≫ (F.mapId a ▷ η.app a ≫ η.naturality (𝟙 a)) ▷ θ.app a otimes≫
          η.app a ◁ θ.naturality (𝟙 a) otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (G.mapId a ▷ θ.app a ≫ θ.naturality (𝟙 a)) otimes≫ 𝟙 _ := by
      rw [η.naturality_id]
      bicategory


中文:
定理 vComp_naturality_id
  条件: (a : B)
  证明: by
  calc
    _ = 𝟙 _ otimes≫ (F.mapId a ▷ η.app a ≫ η.naturality (𝟙 a)) ▷ θ.app a otimes≫
          η.app a ◁ θ.naturality (𝟙 a) otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (G.mapId a ▷ θ.app a ≫ θ.naturality (𝟙 a)) otimes≫ 𝟙 _ := by
      rw [η.naturality_id]
      bicategory


Depends on / 依赖: F.mapId, G.mapId, bicategory, naturality, naturality_id, otimes
-/
theorem vComp_naturality_id (a : B) :
    F.mapId a ▷ η.vCompApp θ a ≫ η.vCompNaturality θ (𝟙 a) =
      (fun_ (η.vCompApp θ a)).hom ≫ (ρ_ (η.vCompApp θ a)).inv ≫ η.vCompApp θ a ◁ H.mapId a := by
  calc
    _ = 𝟙 _ otimes≫ (F.mapId a ▷ η.app a ≫ η.naturality (𝟙 a)) ▷ θ.app a otimes≫
          η.app a ◁ θ.naturality (𝟙 a) otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ η.app a ◁ (G.mapId a ▷ θ.app a ≫ θ.naturality (𝟙 a)) otimes≫ 𝟙 _ := by
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
    _ = 𝟙 _ otimes≫ (F.mapComp f g ▷ η.app c ≫ η.naturality (f ≫ g)) ▷ θ.app c otimes≫
          η.app a ◁ θ.naturality (f ≫ g) otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ (F.map f ◁ η.naturality g otimes≫ η.naturality f ▷ G.map g) ▷ θ.app c otimes≫
          η.app a ◁ (G.mapCom

中文:
定理 vComp_naturality_comp
  条件: {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
  证明: by
  calc
    _ = 𝟙 _ otimes≫ (F.mapComp f g ▷ η.app c ≫ η.naturality (f ≫ g)) ▷ θ.app c otimes≫
          η.app a ◁ θ.naturality (f ≫ g) otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ (F.map f ◁ η.naturality g otimes≫ η.naturality f ▷ G.map g) ▷ θ.app c otimes≫
          η.app a ◁ (G.mapCom

Depends on / 依赖: F.map, F.mapComp, G.map, G.mapComp, bicategory, mapComp, naturality, naturality_comp, otimes
-/
theorem vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    F.mapComp f g ▷ η.vCompApp θ c ≫ η.vCompNaturality θ (f ≫ g) =
      (α_ (F.map f) (F.map g) (η.vCompApp θ c)).hom ≫
        F.map f ◁ η.vCompNaturality θ g ≫
          (α_ (F.map f) (η.vCompApp θ b) (H.map g)).inv ≫
            η.vCompNaturality θ f ▷ H.map g ≫
              (α_ (η.vCompApp θ a) (H.map f) (H.map g)).hom ≫ η.vCompApp θ a ◁ H.mapComp f g := by
  calc
    _ = 𝟙 _ otimes≫ (F.mapComp f g ▷ η.app c ≫ η.naturality (f ≫ g)) ▷ θ.app c otimes≫
          η.app a ◁ θ.naturality (f ≫ g) otimes≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ otimes≫ (F.map f ◁ η.naturality g otimes≫ η.naturality f ▷ G.map g) ▷ θ.app c otimes≫
          η.app a ◁ (G.mapComp f g ▷ θ.app c ≫ θ.naturality (f ≫ g)) otimes≫ 𝟙 _ := by
      rw [η.naturality_comp]
      bicategory
    _ = 𝟙 _ otimes≫ F.map f ◁ η.naturality g ▷ θ.app c otimes≫
          (η.naturality f ▷ (G.map g ≫ θ.app c) ≫ (η.app a ≫ G.map f) ◁ θ.naturality g) otimes≫
            η.app a ◁ (θ.naturality f ▷ H.map g otimes≫ θ.app a ◁ H.mapComp f g) otimes≫ 𝟙 _ := by
      rw [θ.naturality_comp]
      bicategory
    _ = _ := by
      rw [← whisker_exchange]
      bicategory

/--
Definition of `vComp` / `vComp` 的定义

English:
definition vComp
  signature: (η : OplaxTrans F G) (θ : OplaxTrans G H)
  body: vCompApp η θ
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

中文:
定义 vComp
  签名: (η : OplaxTrans F G) (θ : OplaxTrans G H)
  定义体: vCompApp η θ
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

Depends on / 依赖: vCompApp
-/
def vComp (η : OplaxTrans F G) (θ : OplaxTrans G H) : OplaxTrans F H where
  app := vCompApp η θ
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

attribute [local simp] vCompApp vCompNaturality in
/-- `CategoryStruct` on `B ⥤ᴸ C` where the (1-)morphisms are given by oplax
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance : CategoryStruct (B ⥤ᴸ C) where
  Hom := OplaxTrans
  id := OplaxTrans.id
  comp := OplaxTrans.vComp

end OplaxTrans

/--
Definition of `StrongTrans` / `StrongTrans` 的定义

English:
structure StrongTrans
  parameters: (F G : B ⥤ᴸ C)
  axioms and operations (5):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : app a ≫ G.map f ≅ F.map f ≫ app b
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : (naturality f).hom ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ (naturality g).hom  [default: by cat_disch]
    - naturality_id((a : B)) : app a ◁ G.mapId a ≫ (naturality (𝟙 a)).hom = (ρ_ (app a)).hom ≫ (fun_ (app a)).inv ≫ F.mapId a ▷ app a  [default: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : app a ◁ G.mapComp f g ≫ (naturality (f ≫ g)).hom = (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫ (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c  [default: by cat_disch]

中文:
结构 StrongTrans
  参数: (F G : B ⥤ᴸ C)
  公理与运算 (5 个):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : app a ≫ G.map f ≅ F.map f ≫ app b
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : (naturality f).hom ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ (naturality g).hom  [默认: by cat_disch]
    - naturality_id((a : B)) : app a ◁ G.mapId a ≫ (naturality (𝟙 a)).hom = (ρ_ (app a)).hom ≫ (fun_ (app a)).inv ≫ F.mapId a ▷ app a  [默认: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : app a ◁ G.mapComp f g ≫ (naturality (f ≫ g)).hom = (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫ (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure StrongTrans (F G : B ⥤ᴸ C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map f ≅ F.map f ≫ app b
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      (naturality f).hom ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ (naturality g).hom := by
    cat_disch
  /-- Lax unity. -/
  naturality_id (a : B) :
      app a ◁ G.mapId a ≫ (naturality (𝟙 a)).hom =
        (ρ_ (app a)).hom ≫ (fun_ (app a)).inv ≫ F.mapId a ▷ app a := by
    cat_disch
  /-- Lax functoriality. -/
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      app a ◁ G.mapComp f g ≫ (naturality (f ≫ g)).hom =
      (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom ≫
        F.map f ◁ (naturality g).hom ≫ (α_ _ _ _).inv ≫ F.mapComp f g ▷ app c := by
    cat_disch

attribute [nolint docBlame] CategoryTheory.Lax.StrongTrans.app
  CategoryTheory.Lax.StrongTrans.naturality

attribute [reassoc (attr := simp)] StrongTrans.naturality_naturality
  StrongTrans.naturality_id StrongTrans.naturality_comp

/--
Definition of `LaxTrans.StrongCore` / `LaxTrans.StrongCore` 的定义

English:
structure LaxTrans.StrongCore
  parameters: {F G : B ⥤ᴸ C} (η : F ⟶ G)
  axioms and operations (2):
    - naturality({a b : B} (f : a ⟶ b)) : η.app a ≫ G.map f ≅ F.map f ≫ η.app b
    - naturality_hom({a b : B} (f : a ⟶ b)) : (naturality f).hom = η.naturality f  [default: by cat_disch]

中文:
结构 LaxTrans.StrongCore
  参数: {F G : B ⥤ᴸ C} (η : F ⟶ G)
  公理与运算 (2 个):
    - naturality({a b : B} (f : a ⟶ b)) : η.app a ≫ G.map f ≅ F.map f ≫ η.app b
    - naturality_hom({a b : B} (f : a ⟶ b)) : (naturality f).hom = η.naturality f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure LaxTrans.StrongCore {F G : B ⥤ᴸ C} (η : F ⟶ G) where
  /-- The underlying 2-isomorphisms of the naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : η.app a ≫ G.map f ≅ F.map f ≫ η.app b
  /-- The 2-isomorphisms agree with the underlying 2-morphism of the lax transformation. -/
  naturality_hom {a b : B} (f : a ⟶ b) : (naturality f).hom = η.naturality f := by cat_disch

attribute [simp] LaxTrans.StrongCore.naturality_hom

namespace StrongTrans

/-- The underlying lax natural transformation of a strong natural transformation. -/
@[simps]
/--
Definition of `toLax` / `toLax` 的定义

English:
definition toLax
  signature: {F G : B ⥤ᴸ C} (η : StrongTrans F G)
  body: η.app
  naturality f := (η.naturality f).hom

中文:
定义 toLax
  签名: {F G : B ⥤ᴸ C} (η : StrongTrans F G)
  定义体: η.app
  naturality f := (η.naturality f).hom
-/
def toLax {F G : B ⥤ᴸ C} (η : StrongTrans F G) : LaxTrans F G where
  app := η.app
  naturality f := (η.naturality f).hom

/--
Definition of `mkOfLax` / `mkOfLax` 的定义

English:
definition mkOfLax
  signature: {F G : B ⥤ᴸ C} (η : LaxTrans F G) (η' : LaxTrans.StrongCore η)
  body: η.app
  naturality := η'.naturality

中文:
定义 mkOfLax
  签名: {F G : B ⥤ᴸ C} (η : LaxTrans F G) (η' : LaxTrans.StrongCore η)
  定义体: η.app
  naturality := η'.naturality
-/
def mkOfLax {F G : B ⥤ᴸ C} (η : LaxTrans F G) (η' : LaxTrans.StrongCore η) :
    StrongTrans F G where
  app := η.app
  naturality := η'.naturality

/--
Definition of `mkOfLax'` / `mkOfLax'` 的定义

English:
definition mkOfLax'
  signature: {F G : B ⥤ᴸ C} (η : LaxTrans F G)
  body: η.app
  naturality _ := asIso (η.naturality _)

中文:
定义 mkOfLax'
  签名: {F G : B ⥤ᴸ C} (η : LaxTrans F G)
  定义体: η.app
  naturality _ := asIso (η.naturality _)
-/
noncomputable def mkOfLax' {F G : B ⥤ᴸ C} (η : LaxTrans F G)
    [forall a b (f : a ⟶ b), IsIso (η.naturality f)] : StrongTrans F G where
  app := η.app
  naturality _ := asIso (η.naturality _)

variable (F : B ⥤ᴸ C)

/-- The identity strong natural transformation. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : StrongTrans F F
  body: mkOfLax (LaxTrans.id F) { naturality := fun f => (fun_ (F.map f)) ≪≫ (ρ_ (F.map f)).symm }

@[simp]

中文:
定义 id
  签名: : StrongTrans F F
  定义体: mkOfLax (LaxTrans.id F) { naturality := fun f => (fun_ (F.map f)) ≪≫ (ρ_ (F.map f)).symm }

@[simp]

Depends on / 依赖: F.map, LaxTrans, LaxTrans.id, fun_, mkOfLax, naturality
-/
def id : StrongTrans F F :=
  mkOfLax (LaxTrans.id F) { naturality := fun f => (fun_ (F.map f)) ≪≫ (ρ_ (F.map f)).symm }

@[simp]
/--
lemma `id.toLax` / 引理 `id.toLax`

English:
lemma id.toLax
  statement: (id F).toLax = LaxTrans.id F
  proof: rfl

中文:
引理 id.toLax
  结论: (id F).toLax = LaxTrans.id F
  证明: rfl
-/
lemma id.toLax : (id F).toLax = LaxTrans.id F :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (StrongTrans F F)
  body: ⟨id F⟩

中文:
实例 :
  签名: 可居 (StrongTrans F F)
  定义体: ⟨id F⟩
-/
instance : Inhabited (StrongTrans F F) :=
  ⟨id F⟩

variable {F} {G H : B ⥤ᴸ C} (η : StrongTrans F G) (θ : StrongTrans G H)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Vertical composition of strong natural transformations. -/
@[simps!]
/--
Definition of `vComp` / `vComp` 的定义

English:
definition vComp
  signature: : StrongTrans F H
  body: mkOfLax (LaxTrans.vComp η.toLax θ.toLax)
    { naturality := fun {a b} f =>
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm ≪≫
        whiskerRightIso (η.naturality f) (θ.app b) ≪≫ (α_ _ _ _) }

中文:
定义 vComp
  签名: : StrongTrans F H
  定义体: mkOfLax (LaxTrans.vComp η.toLax θ.toLax)
    { naturality := fun {a b} f =>
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm ≪≫
        whiskerRightIso (η.naturality f) (θ.app b) ≪≫ (α_ _ _ _) }

Depends on / 依赖: LaxTrans, LaxTrans.vComp, mkOfLax, naturality, whiskerLeftIso, whiskerRightIso
-/
def vComp : StrongTrans F H :=
  mkOfLax (LaxTrans.vComp η.toLax θ.toLax)
    { naturality := fun {a b} f =>
        (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm ≪≫
        whiskerRightIso (η.naturality f) (θ.app b) ≪≫ (α_ _ _ _) }

/-- `CategoryStruct` on `B ⥤ᴸ C` where the (1-)morphisms are given by strong
transformations. -/
@[simps! id_app id_naturality comp_app comp_naturality]
scoped instance categoryStruct : CategoryStruct (B ⥤ᴸ C) where
  Hom := StrongTrans
  id := StrongTrans.id
  comp := StrongTrans.vComp

end StrongTrans

end CategoryTheory.Lax
