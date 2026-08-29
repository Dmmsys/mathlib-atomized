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

/--
Definition of `StrongTrans` / `StrongTrans` 的定义

English:
structure StrongTrans
  parameters: (F G : Pseudofunctor B C)
  axioms and operations (5):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ≫ app b ≅ app a ≫ G.map f
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η  [default: by cat_disch]
    - naturality_id((a : B)) : (naturality (𝟙 a)).hom ≫ app a ◁ (G.mapId a).hom = (F.mapId a).hom ▷ app a ≫ (fun_ (app a)).hom ≫ (ρ_ (app a)).inv  [default: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : (naturality (f ≫ g)).hom ≫ app a ◁ (G.mapComp f g).hom = (F.mapComp f g).hom ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫ (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom  [default: by cat_disch]

中文:
结构 StrongTrans
  参数: (F G : Pseudofunctor B C)
  公理与运算 (5 个):
    - app((a : B)) : F.obj a ⟶ G.obj a
    - naturality({a b : B} (f : a ⟶ b)) : F.map f ≫ app b ≅ app a ≫ G.map f
    - naturality_naturality({a b : B} {f g : a ⟶ b} (η : f ⟶ g)) : F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η  [默认: by cat_disch]
    - naturality_id((a : B)) : (naturality (𝟙 a)).hom ≫ app a ◁ (G.mapId a).hom = (F.mapId a).hom ▷ app a ≫ (fun_ (app a)).hom ≫ (ρ_ (app a)).inv  [默认: by cat_disch]
    - naturality_comp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : (naturality (f ≫ g)).hom ≫ app a ◁ (G.mapComp f g).hom = (F.mapComp f g).hom ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫ (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch
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
        (F.mapId a).hom ▷ app a ≫ (fun_ (app a)).hom ≫ (ρ_ (app a)).inv := by
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
/--
Definition of `toOplax` / `toOplax` 的定义

English:
definition toOplax
  signature: (η : StrongTrans F G)
  body: η.app
  naturality f := η.naturality f

中文:
定义 toOplax
  签名: (η : StrongTrans F G)
  定义体: η.app
  naturality f := η.naturality f
-/
def toOplax (η : StrongTrans F G) : Oplax.StrongTrans F.toOplax G.toOplax where
  app := η.app
  naturality f := η.naturality f

/--
Instance `hasCoeToOplax` / 实例 `hasCoeToOplax`

English:
instance hasCoeToOplax
  signature: : Coe (StrongTrans F G) (Oplax.StrongTrans F.toOplax G.toOplax)
  body: ⟨toOplax⟩

中文:
实例 hasCoeToOplax
  签名: : Coe (StrongTrans F G) (Oplax.StrongTrans F.toOplax G.toOplax)
  定义体: ⟨toOplax⟩

Depends on / 依赖: toOplax
-/
instance hasCoeToOplax : Coe (StrongTrans F G) (Oplax.StrongTrans F.toOplax G.toOplax) :=
  ⟨toOplax⟩

/-- Construct a strong transformation of pseudofunctors from a strong transformation of the
underlying oplax functors. -/
@[simps]
/--
Definition of `mkOfOplax` / `mkOfOplax` 的定义

English:
definition mkOfOplax
  signature: (η : Oplax.StrongTrans F.toOplax G.toOplax)
  body: η.app
  naturality := η.naturality
  naturality_naturality θ := η.naturality_naturality θ
  naturality_id a := η.naturality_id a
  naturality_comp f g := η.naturality_comp f g

中文:
定义 mkOfOplax
  签名: (η : Oplax.StrongTrans F.toOplax G.toOplax)
  定义体: η.app
  naturality := η.naturality
  naturality_naturality θ := η.naturality_naturality θ
  naturality_id a := η.naturality_id a
  naturality_comp f g := η.naturality_comp f g
-/
def mkOfOplax (η : Oplax.StrongTrans F.toOplax G.toOplax) :
    StrongTrans F G where
  app := η.app
  naturality := η.naturality
  naturality_naturality θ := η.naturality_naturality θ
  naturality_id a := η.naturality_id a
  naturality_comp f g := η.naturality_comp f g

variable (F) in
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : StrongTrans F F where
  body: 𝟙 (F.obj a)
  naturality {a b} f := (ρ_ (F.map f)) ≪≫ (fun_ (F.map f)).symm

中文:
定义 id
  签名: : StrongTrans F F where
  定义体: 𝟙 (F.obj a)
  naturality {a b} f := (ρ_ (F.map f)) ≪≫ (fun_ (F.map f)).symm

Depends on / 依赖: F.obj
-/
def id : StrongTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {a b} f := (ρ_ (F.map f)) ≪≫ (fun_ (F.map f)).symm

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

variable {H : B ⥤ᵖ C}

/--
Definition of `vcomp` / `vcomp` 的定义

English:
definition vcomp
  signature: (η : StrongTrans F G) (θ : StrongTrans G H)
  body: mkOfOplax (Oplax.StrongTrans.vcomp η.toOplax θ.toOplax)

#adaptation_note

中文:
定义 vcomp
  签名: (η : StrongTrans F G) (θ : StrongTrans G H)
  定义体: mkOfOplax (Oplax.StrongTrans.vcomp η.toOplax θ.toOplax)

#adaptation_note

Depends on / 依赖: Oplax.StrongTrans.vcomp, StrongTrans, mkOfOplax, toOplax
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
scoped instance categoryStruct : CategoryStruct (B ⥤ᵖ C) where
  Hom F G := StrongTrans F G
  id F := StrongTrans.id F
  comp := StrongTrans.vcomp

variable (η : F ⟶ G) (θ : G ⟶ H)

@[simp]
/--
lemma `comp_app` / 引理 `comp_app`

English:
lemma comp_app
  given: (η : F ⟶ G) (θ : G ⟶ H) (a : B)
  proof: rfl

中文:
引理 comp_app
  条件: (η : F ⟶ G) (θ : G ⟶ H) (a : B)
  证明: rfl
-/
lemma comp_app (η : F ⟶ G) (θ : G ⟶ H) (a : B) :
    (η ≫ θ).app a = η.app a ≫ θ.app a :=
  rfl

variable (F) in
@[simp]
/--
lemma `id.toOplax` / 引理 `id.toOplax`

English:
lemma id.toOplax
  statement: Oplax.StrongTrans.id F.toOplax = 𝟙 F
  proof: rfl

中文:
引理 id.toOplax
  结论: Oplax.StrongTrans.id F.toOplax = 𝟙 F
  证明: rfl
-/
lemma id.toOplax : Oplax.StrongTrans.id F.toOplax = 𝟙 F :=
  rfl

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp), to_app]
/--
theorem `whiskerLeft_naturality_naturality` / 定理 `whiskerLeft_naturality_naturality`

English:
theorem whiskerLeft_naturality_naturality
  given: (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h)
  proof: θ.toOplax.whiskerLeft_naturality_naturality _ _

@[reassoc (attr := simp), to_app]

中文:
定理 whiskerLeft_naturality_naturality
  条件: (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h)
  证明: θ.toOplax.whiskerLeft_naturality_naturality _ _

@[reassoc (attr := simp), to_app]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.costructuredArrowToOverEquivalence, costructuredArrowToOverEquivalence, infer_instance, isConnected_iff_of_equivalence, toOplax, toOplax.whiskerLeft_naturality_naturality, whiskerLeft_naturality_naturality
-/
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom =
      f ◁ (θ.naturality g).hom ≫ f ◁ θ.app a ◁ H.map₂ β :=
  θ.toOplax.whiskerLeft_naturality_naturality _ _

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
    f ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ (H.mapComp g h).hom =
      f ◁ (G.mapComp g h).hom ▷ θ.app c ≫
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
    f ◁ (θ.naturality (𝟙 a)).hom ≫ f ◁ θ.app a ◁ (H.mapId a).hom =
      f ◁ (G.mapId a).hom ▷ θ.app a ≫ f ◁ (fun_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv :=
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

#adaptation_note

中文:
定理 whiskerRight_naturality_id
  条件: (f : G.obj a ⟶ a')
  证明: η.toOplax.whiskerRight_naturality_id _

#adaptation_note

Depends on / 依赖: toOplax, toOplax.whiskerRight_naturality_id, whiskerRight_naturality_id
-/
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (η.naturality (𝟙 a)).hom ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ (G.mapId a).hom ▷ f =
    (F.mapId a).hom ▷ η.app a ▷ f ≫ (fun_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫
    (α_ _ _ _).hom :=
  η.toOplax.whiskerRight_naturality_id _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `naturality_id_hom` / 引理 `naturality_id_hom`

English:
lemma naturality_id_hom
  given: (α : F ⟶ G) (a : B)
  proof: by
  simp [← assoc, ← IsIso.comp_inv_eq]

中文:
引理 naturality_id_hom
  条件: (α : F ⟶ G) (a : B)
  证明: by
  simp [← assoc, ← IsIso.comp_inv_eq]

Depends on / 依赖: IsIso.comp_inv_eq, comp_inv_eq
-/
lemma naturality_id_hom (α : F ⟶ G) (a : B) :
    (α.naturality (𝟙 a)).hom = (F.mapId a).hom ▷ α.app a ≫
      (fun_ (α.app a)).hom ≫ (ρ_ (α.app a)).inv ≫ α.app a ◁ (G.mapId a).inv := by
  simp [← assoc, ← IsIso.comp_inv_eq]

/--
lemma `naturality_id_iso` / 引理 `naturality_id_iso`

English:
lemma naturality_id_iso
  given: (α : F ⟶ G) (a : B)
  proof: by
  ext
  simp [naturality_id_hom]

#adaptation_note

中文:
引理 naturality_id_iso
  条件: (α : F ⟶ G) (a : B)
  证明: by
  ext
  simp [naturality_id_hom]

#adaptation_note

Depends on / 依赖: naturality_id_hom
-/
lemma naturality_id_iso (α : F ⟶ G) (a : B) :
    α.naturality (𝟙 a) = whiskerRightIso (F.mapId a) (α.app a) ≪≫
      (fun_ (α.app a)) ≪≫ (ρ_ (α.app a)).symm ≪≫ whiskerLeftIso (α.app a) (G.mapId a).symm := by
  ext
  simp [naturality_id_hom]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `naturality_id_inv` / 引理 `naturality_id_inv`

English:
lemma naturality_id_inv
  given: (α : F ⟶ G) (a : B)
  proof: by
  simp [naturality_id_iso]

@[to_app (attr := reassoc)]

中文:
引理 naturality_id_inv
  条件: (α : F ⟶ G) (a : B)
  证明: by
  simp [naturality_id_iso]

@[to_app (attr := reassoc)]

Depends on / 依赖: naturality_id_iso
-/
lemma naturality_id_inv (α : F ⟶ G) (a : B) :
    (α.naturality (𝟙 a)).inv = α.app a ◁ (G.mapId a).hom ≫ (ρ_ (α.app a)).hom ≫
      (fun_ (α.app a)).inv ≫ (F.mapId a).inv ▷ α.app a := by
  simp [naturality_id_iso]

@[to_app (attr := reassoc)]
/--
lemma `naturality_naturality_hom` / 引理 `naturality_naturality_hom`

English:
lemma naturality_naturality_hom
  given: (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g)
  proof: by
  simp [← IsIso.inv_comp_eq, ← G.map₂_inv η.inv]

中文:
引理 naturality_naturality_hom
  条件: (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g)
  证明: by
  simp [← IsIso.inv_comp_eq, ← G.map₂_inv η.inv]

Depends on / 依赖: G.map, IsIso.inv_comp_eq, inv_comp_eq
-/
lemma naturality_naturality_hom (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) :
    (α.naturality g).hom =
     (F.map₂ η.inv) ▷ α.app b ≫ (α.naturality f).hom ≫ α.app a ◁ G.map₂ η.hom := by
  simp [← IsIso.inv_comp_eq, ← G.map₂_inv η.inv]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `naturality_naturality_iso` / 引理 `naturality_naturality_iso`

English:
lemma naturality_naturality_iso
  given: (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g)
  proof: by
  ext
  rw [naturality_naturality_hom α η]
  simp

中文:
引理 naturality_naturality_iso
  条件: (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g)
  证明: by
  ext
  rw [naturality_naturality_hom α η]
  simp

Depends on / 依赖: finallySmall_of_final_of_essentiallySmall, fromFinalModel, naturality_naturality_hom
-/
lemma naturality_naturality_iso (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) :
    α.naturality g = whiskerRightIso (F.map₂Iso η.symm) (α.app b) ≪≫
      (α.naturality f) ≪≫ whiskerLeftIso (α.app a) (G.map₂Iso η) := by
  ext
  rw [naturality_naturality_hom α η]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `naturality_naturality_inv` / 引理 `naturality_naturality_inv`

English:
lemma naturality_naturality_inv
  given: (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g)
  proof: by
  simp [naturality_naturality_iso α η]

@[to_app (attr := reassoc)]

中文:
引理 naturality_naturality_inv
  条件: (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g)
  证明: by
  simp [naturality_naturality_iso α η]

@[to_app (attr := reassoc)]

Depends on / 依赖: naturality_naturality_iso
-/
lemma naturality_naturality_inv (α : F ⟶ G) {a b : B} {f g : a ⟶ b} (η : f ≅ g) :
    (α.naturality g).inv =
      α.app a ◁ G.map₂ η.inv ≫ (α.naturality f).inv ≫ F.map₂ η.hom ▷ α.app b := by
  simp [naturality_naturality_iso α η]

@[to_app (attr := reassoc)]
/--
lemma `naturality_comp_hom` / 引理 `naturality_comp_hom`

English:
lemma naturality_comp_hom
  given: (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
  proof: by
  simp [← assoc, ← IsIso.comp_inv_eq]

中文:
引理 naturality_comp_hom
  条件: (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
  证明: by
  simp [← assoc, ← IsIso.comp_inv_eq]

Depends on / 依赖: IsIso.comp_inv_eq, comp_inv_eq
-/
lemma naturality_comp_hom (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (α.naturality (f ≫ g)).hom =
      (F.mapComp f g).hom ▷ α.app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (α.naturality g).hom ≫
      (α_ _ _ _).inv ≫ (α.naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom ≫
      α.app a ◁ (G.mapComp f g).inv := by
  simp [← assoc, ← IsIso.comp_inv_eq]

/--
lemma `naturality_comp_iso` / 引理 `naturality_comp_iso`

English:
lemma naturality_comp_iso
  given: (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
  proof: by
  ext
  simp [naturality_comp_hom α f g]

@[to_app (attr := reassoc)]

中文:
引理 naturality_comp_iso
  条件: (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
  证明: by
  ext
  simp [naturality_comp_hom α f g]

@[to_app (attr := reassoc)]

Depends on / 依赖: naturality_comp_hom
-/
lemma naturality_comp_iso (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    α.naturality (f ≫ g) = whiskerRightIso (F.mapComp f g) (α.app c) ≪≫ (α_ _ _ _) ≪≫
      whiskerLeftIso (F.map f) (α.naturality g) ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso (α.naturality f) (G.map g) ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso (α.app a) (G.mapComp f g).symm := by
  ext
  simp [naturality_comp_hom α f g]

@[to_app (attr := reassoc)]
/--
lemma `naturality_comp_inv` / 引理 `naturality_comp_inv`

English:
lemma naturality_comp_inv
  given: (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
  proof: by
  simp [naturality_comp_iso α f g]

中文:
引理 naturality_comp_inv
  条件: (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
  证明: by
  simp [naturality_comp_iso α f g]

Depends on / 依赖: naturality_comp_iso
-/
lemma naturality_comp_inv (α : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (α.naturality (f ≫ g)).inv =
      α.app a ◁ (G.mapComp f g).hom ≫ (α_ _ _ _).inv ≫ (α.naturality f).inv ▷ G.map g ≫
      (α_ _ _ _).hom ≫ F.map f ◁ (α.naturality g).inv ≫ (α_ _ _ _).inv ≫
      (F.mapComp f g).inv ▷ α.app c := by
  simp [naturality_comp_iso α f g]

end

end CategoryTheory.Pseudofunctor.StrongTrans
