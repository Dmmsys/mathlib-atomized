/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.KanExtension
public import Mathlib.CategoryTheory.Products.Associator

/-!
# Day convolution monoidal structure

Given functors `F G : C ⥤ V` between two monoidal categories,
this file defines a typeclass `DayConvolution` on functors `F` `G` that contains
a functor `F ⊛ G`, as well as the required data to exhibit `F ⊛ G` as a pointwise
left Kan extension of `F ⊠ G` (see `Mathlib/CategoryTheory/Monoidal/ExternalProduct/Basic.lean`
for the definition) along the tensor product of `C`.
Such a functor is called a Day convolution of `F` and `G`, and
although we do not show it yet, this operation defines a monoidal structure on `C ⥤ V`.

We also define a typeclass `DayConvolutionUnit` on a functor `U : C ⥤ V` that bundles the data
required to make it a unit for the Day convolution monoidal structure: said data is that of
a map `𝟙_ V ⟶ U.obj (𝟙_ C)` that exhibits `U` as a pointwise left Kan extension of
`fromPUnit (𝟙_ V)` along `fromPUnit (𝟙_ C)`.

The main way to assert that a given monoidal category structure on a category `D`
arises as a "Day convolution monoidal structure" is given by the typeclass
`LawfulDayConvolutionMonoidalCategoryStruct C V D`, which bundles the data and
equations needed to exhibit `D` as a monoidal full subcategory of `C ⥤ V` if
the latter were to have the Day convolution monoidal structure. The definition
`monoidalOfLawfulDayConvolutionMonoidalCategoryStruct` promotes (under suitable
assumptions on `V`) a `LawfulDayConvolutionMonoidalCategoryStruct C V D` to
a monoidal structure.


## References
- [nLab page: Day convolution](https://ncatlab.org/nlab/show/Day+convolution)

## TODOs (@robin-carlier)
- Type alias for `C ⥤ V` with a `LawfulDayConvolutionMonoidalCategoryStruct`.
- Characterization of lax monoidal functors out of a Day convolution monoidal category.
- Case `V = Type u` and its universal property.
- Fix the abuse of functor associativity that causes `erw [id_apply]` in a few places in this file.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.MonoidalCategory
open scoped ExternalProduct

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V]

/--
Definition of `DayConvolution` / `DayConvolution` 的定义

English:
class DayConvolution
  parameters: (F G : C ⥤ V)
  axioms and operations (3):
    - convolution : C ⥤ V
    - unit((F) (G)) : F ⊠ G ⟶ tensor C ⋙ convolution
    - isPointwiseLeftKanExtensionUnit((F G)) : (Functor.LeftExtension.mk (convolution) unit).IsPointwiseLeftKanExtension

中文:
类 Day卷积
  参数: (F G : C ⥤ V)
  公理与运算 (3 个):
    - convolution : C ⥤ V
    - unit((F) (G)) : F ⊠ G ⟶ tensor C ⋙ convolution
    - isPointwiseLeftKanExtensionUnit((F G)) : (函子.LeftExtension.mk (convolution) unit).IsPointwiseLeftKanExtension
-/
class DayConvolution (F G : C ⥤ V) where
  /-- The chosen convolution between the functors. Denoted `F ⊛ G`. -/
  convolution : C ⥤ V
  /-- The chosen convolution between the functors. -/
  unit (F) (G) : F ⊠ G ⟶ tensor C ⋙ convolution
  /-- The transformation `unit` exhibits `F ⊛ G` as a pointwise left Kan extension
  of `F ⊠ G` along `tensor C`. -/
  isPointwiseLeftKanExtensionUnit (F G) :
    (Functor.LeftExtension.mk (convolution) unit).IsPointwiseLeftKanExtension

namespace DayConvolution

open scoped CategoryTheory.Prod

section

/-- A notation for the Day convolution of two functors. -/
scoped infixr:80 " ⊛ " => convolution

variable (F G : C ⥤ V)

/--
Instance `leftKanExtension` / 实例 `leftKanExtension`

English:
instance leftKanExtension
  signature: [DayConvolution F G]
  body: .isLeftKanExtension isPointwiseLeftKanExtensionUnit F G

中文:
实例 leftKanExtension
  签名: [Day卷积 F G]
  定义体: .isLeftKanExtension isPointwiseLeftKanExtensionUnit F G

Depends on / 依赖: isLeftKanExtension, isPointwiseLeftKanExtensionUnit
-/
instance leftKanExtension [DayConvolution F G] :
    (F ⊛ G).IsLeftKanExtension (unit F G) :=
.isLeftKanExtension isPointwiseLeftKanExtensionUnit F G

variable {F G}

/--
Definition of `uniqueUpToIso` / `uniqueUpToIso` 的定义

English:
definition uniqueUpToIso
  signature: (h : DayConvolution F G) (h' : DayConvolution F G)
  body: Functor.leftKanExtensionUnique h.convolution h.unit h'.convolution h'.unit

@[reassoc (attr := simp)]

中文:
定义 uniqueUpToIso
  签名: (h : Day卷积 F G) (h' : Day卷积 F G)
  定义体: Functor.leftKanExtensionUnique h.convolution h.unit h'.convolution h'.unit

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.leftKanExtensionUnique, convolution, h.convolution, h.unit, leftKanExtensionUnique
-/
def uniqueUpToIso (h : DayConvolution F G) (h' : DayConvolution F G) :
    h.convolution ≅ h'.convolution :=
  Functor.leftKanExtensionUnique h.convolution h.unit h'.convolution h'.unit

@[reassoc (attr := simp)]
/--
lemma `unit_uniqueUpToIso_hom` / 引理 `unit_uniqueUpToIso_hom`

English:
lemma unit_uniqueUpToIso_hom
  given: (h : DayConvolution F G) (h' : DayConvolution F G)
  proof: by
  simp [uniqueUpToIso]

@[reassoc (attr := simp)]

中文:
引理 unit_uniqueUpToIso_hom
  条件: (h : Day卷积 F G) (h' : Day卷积 F G)
  证明: by
  simp [uniqueUpToIso]

@[reassoc (attr := simp)]

Depends on / 依赖: uniqueUpToIso
-/
lemma unit_uniqueUpToIso_hom (h : DayConvolution F G) (h' : DayConvolution F G) :
    h.unit ≫ Functor.whiskerLeft (tensor C) (h.uniqueUpToIso h').hom = h'.unit := by
  simp [uniqueUpToIso]

@[reassoc (attr := simp)]
/--
lemma `unit_uniqueUpToIso_inv` / 引理 `unit_uniqueUpToIso_inv`

English:
lemma unit_uniqueUpToIso_inv
  given: (h : DayConvolution F G) (h' : DayConvolution F G)
  proof: by
  simp [uniqueUpToIso]

中文:
引理 unit_uniqueUpToIso_inv
  条件: (h : Day卷积 F G) (h' : Day卷积 F G)
  证明: by
  simp [uniqueUpToIso]

Depends on / 依赖: uniqueUpToIso
-/
lemma unit_uniqueUpToIso_inv (h : DayConvolution F G) (h' : DayConvolution F G) :
    h'.unit ≫ Functor.whiskerLeft (tensor C) (h.uniqueUpToIso h').inv = h.unit := by
  simp [uniqueUpToIso]

variable (F G) [DayConvolution F G]

section unit

variable {x x' y y' : C}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `unit_naturality` / 引理 `unit_naturality`

English:
lemma unit_naturality
  given: (f : x ⟶ x') (g : y ⟶ y')
  proof: by
  simpa [tensorHom_def] using (unit F G).naturality (f ×ₘ g)

中文:
引理 unit_naturality
  条件: (f : x ⟶ x') (g : y ⟶ y')
  证明: by
  simpa [tensorHom_def] using (unit F G).naturality (f ×ₘ g)

Depends on / 依赖: naturality, tensorHom_def
-/
lemma unit_naturality (f : x ⟶ x') (g : y ⟶ y') :
    (F.map f otimesₘ G.map g) ≫ (unit F G).app (x', y') =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (f otimesₘ g) := by
  simpa [tensorHom_def] using (unit F G).naturality (f ×ₘ g)

set_option backward.defeqAttrib.useBackward true in
variable (y) in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `whiskerRight_comp_unit_app` / 引理 `whiskerRight_comp_unit_app`

English:
lemma whiskerRight_comp_unit_app
  given: (f : x ⟶ x')
  proof: by
  simpa [tensorHom_def] using (unit F G).naturality (f ×ₘ 𝟙 _)

#adaptation_note

中文:
引理 whiskerRight_comp_unit_app
  条件: (f : x ⟶ x')
  证明: by
  simpa [tensorHom_def] using (unit F G).naturality (f ×ₘ 𝟙 _)

#adaptation_note

Depends on / 依赖: naturality, tensorHom_def
-/
lemma whiskerRight_comp_unit_app (f : x ⟶ x') :
    F.map f ▷ G.obj y ≫ (unit F G).app (x', y) =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (f ▷ y) := by
  simpa [tensorHom_def] using (unit F G).naturality (f ×ₘ 𝟙 _)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (x) in
@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_comp_unit_app` / 引理 `whiskerLeft_comp_unit_app`

English:
lemma whiskerLeft_comp_unit_app
  given: (g : y ⟶ y')
  proof: by
  simpa [tensorHom_def] using (unit F G).naturality (𝟙 _ ×ₘ g)

中文:
引理 whiskerLeft_comp_unit_app
  条件: (g : y ⟶ y')
  证明: by
  simpa [tensorHom_def] using (unit F G).naturality (𝟙 _ ×ₘ g)

Depends on / 依赖: naturality, tensorHom_def
-/
lemma whiskerLeft_comp_unit_app (g : y ⟶ y') :
    F.obj x ◁ G.map g ≫ (unit F G).app (x, y') =
    (unit F G).app (x, y) ≫ (F ⊛ G).map (x ◁ g) := by
  simpa [tensorHom_def] using (unit F G).naturality (𝟙 _ ×ₘ g)

end unit

variable {F G}

section map

variable {F' G' : C ⥤ V} [DayConvolution F' G']

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : F ⟶ F') (g : G ⟶ G')
  body: Functor.descOfIsLeftKanExtension (F ⊛ G) (unit F G) (F' ⊛ G')
    (externalProductBifunctor C C V).map (f ×ₘ g) ≫ unit F' G'

中文:
定义 map
  签名: (f : F ⟶ F') (g : G ⟶ G')
  定义体: Functor.descOfIsLeftKanExtension (F ⊛ G) (unit F G) (F' ⊛ G')
    (externalProductBifunctor C C V).map (f ×ₘ g) ≫ unit F' G'

Depends on / 依赖: Functor, Functor.descOfIsLeftKanExtension, descOfIsLeftKanExtension, externalProductBifunctor
-/
def map (f : F ⟶ F') (g : G ⟶ G') : F ⊛ G ⟶ F' ⊛ G' :=
Functor.descOfIsLeftKanExtension (F ⊛ G) (unit F G) (F' ⊛ G')
    (externalProductBifunctor C C V).map (f ×ₘ g) ≫ unit F' G'

variable (f : F ⟶ F') (g : G ⟶ G') (x y : C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in -- Needed in DayConvolution.lean
@[reassoc (attr := simp)]
/--
lemma `unit_app_map_app` / 引理 `unit_app_map_app`

English:
lemma unit_app_map_app
  proof: by
  simpa [tensorHom_def] using!
    (Functor.descOfIsLeftKanExtension_fac_app (F ⊛ G) (unit F G) (F' ⊛ G') <|
      (externalProductBifunctor C C V).map (f ×ₘ g) ≫ unit F' G') (x, y)

中文:
引理 unit_app_map_app
  证明: by
  simpa [tensorHom_def] using!
    (Functor.descOfIsLeftKanExtension_fac_app (F ⊛ G) (unit F G) (F' ⊛ G') <|
      (externalProductBifunctor C C V).map (f ×ₘ g) ≫ unit F' G') (x, y)

Depends on / 依赖: Functor, Functor.descOfIsLeftKanExtension_fac_app, descOfIsLeftKanExtension_fac_app, externalProductBifunctor, tensorHom_def
-/
lemma unit_app_map_app :
    (unit F G).app (x, y) ≫ (map f g).app (x otimes y : C) =
    (f.app x otimesₘ g.app y) ≫ (unit F' G').app (x, y) := by
  simpa [tensorHom_def] using!
    (Functor.descOfIsLeftKanExtension_fac_app (F ⊛ G) (unit F G) (F' ⊛ G') <|
      (externalProductBifunctor C C V).map (f ×ₘ g) ≫ unit F' G') (x, y)

end map

variable (F G)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The universal property of left Kan extensions characterizes the functor
corepresented by `F ⊛ G`. -/
@[simps!]
/--
Definition of `corepresentableBy` / `corepresentableBy` 的定义

English:
definition corepresentableBy
  signature: :
  body: Functor.homEquivOfIsLeftKanExtension _ (unit F G) _
  homEquiv_comp := by aesop

中文:
定义 corepresentableBy
  签名: :
  定义体: Functor.homEquivOfIsLeftKanExtension _ (unit F G) _
  homEquiv_comp := by aesop

Depends on / 依赖: Functor, Functor.homEquivOfIsLeftKanExtension, homEquivOfIsLeftKanExtension
-/
def corepresentableBy :
.CorepresentableBy (Functor.whiskeringLeft _ _ _).obj (tensor C) ⋙ coyoneda.obj (.op <| F ⊠ G)
      (F ⊛ G) where
  homEquiv := Functor.homEquivOfIsLeftKanExtension _ (unit F G) _
  homEquiv_comp := by aesop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `convolution_hom_ext_at` / 定理 `convolution_hom_ext_at`

English:
theorem convolution_hom_ext_at
  statement: (c : C) {v : V} {f g : (F ⊛ G).obj c ⟶ v}
  proof: ((isPointwiseLeftKanExtensionUnit F G) c).hom_ext (fun j => by simpa using h j.hom)

中文:
定理 convolution_hom_ext_at
  结论: (c : C) {v : V} {f g : (F ⊛ G).obj c ⟶ v}
  证明: ((isPointwiseLeftKanExtensionUnit F G) c).hom_ext (fun j => by simpa using h j.hom)

Depends on / 依赖: hom_ext, isPointwiseLeftKanExtensionUnit, j.hom
-/
theorem convolution_hom_ext_at (c : C) {v : V} {f g : (F ⊛ G).obj c ⟶ v}
    (h : forall {x y : C} (u : x otimes y ⟶ c),
      (unit F G).app (x, y) ≫ (F ⊛ G).map u ≫ f = (unit F G).app (x, y) ≫ (F ⊛ G).map u ≫ g) :
    f = g :=
  ((isPointwiseLeftKanExtensionUnit F G) c).hom_ext (fun j => by simpa using h j.hom)

section associator

open CategoryTheory.Functor

variable (H : C ⥤ V) [DayConvolution G H] [DayConvolution F (G ⊛ H)] [DayConvolution (F ⊛ G) H]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]

open MonoidalCategory.ExternalProduct

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (F ⊠ G ⊛ H).IsLeftKanExtension
  body: (isPointwiseLeftKanExtensionExtensionUnitRight _ _ _ <|
    isPointwiseLeftKanExtensionUnit G H).isLeftKanExtension

中文:
实例 :
  签名: (F ⊠ G ⊛ H).是LeftKanExtension
  定义体: (isPointwiseLeftKanExtensionExtensionUnitRight _ _ _ <|
    isPointwiseLeftKanExtensionUnit G H).isLeftKanExtension

Depends on / 依赖: isLeftKanExtension, isPointwiseLeftKanExtensionExtensionUnitRight, isPointwiseLeftKanExtensionUnit
-/
instance : (F ⊠ G ⊛ H).IsLeftKanExtension
    extensionUnitRight (G ⊛ H) (unit G H) F :=
  (isPointwiseLeftKanExtensionExtensionUnitRight _ _ _ <|
    isPointwiseLeftKanExtensionUnit G H).isLeftKanExtension

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((F ⊛ G) ⊠ H).IsLeftKanExtension
  body: (isPointwiseLeftKanExtensionExtensionUnitLeft _ _ _ <|
    isPointwiseLeftKanExtensionUnit F G).isLeftKanExtension

中文:
实例 :
  签名: ((F ⊛ G) ⊠ H).是LeftKanExtension
  定义体: (isPointwiseLeftKanExtensionExtensionUnitLeft _ _ _ <|
    isPointwiseLeftKanExtensionUnit F G).isLeftKanExtension

Depends on / 依赖: isLeftKanExtension, isPointwiseLeftKanExtensionExtensionUnitLeft, isPointwiseLeftKanExtensionUnit
-/
instance : ((F ⊛ G) ⊠ H).IsLeftKanExtension
    extensionUnitLeft (F ⊛ G) (unit F G) H :=
  (isPointwiseLeftKanExtensionExtensionUnitLeft _ _ _ <|
    isPointwiseLeftKanExtensionUnit F G).isLeftKanExtension

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `CorepresentableBy` structure asserting that the Type-valued functor
`Y ↦ (F ⊠ G ⊠ H ⟶ (𝟭 C).prod (tensor C) ⋙ tensor C ⋙ Y)` is corepresented by
`F ⊛ G ⊛ H`. -/
@[simps]
/--
Definition of `corepresentableBy₂` / `corepresentableBy₂` 的定义

English:
definition corepresentableBy₂
  signature: :
  body: (corepresentableBy F (G ⊛ H)).homEquiv.trans
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitRight (G ⊛ H) (unit G H) F) _
  homEquiv_comp := by aesop

中文:
定义 corepresentableBy₂
  签名: :
  定义体: (corepresentableBy F (G ⊛ H)).homEquiv.trans
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitRight (G ⊛ H) (unit G H) F) _
  homEquiv_comp := by aesop

Depends on / 依赖: Functor, Functor.homEquivOfIsLeftKanExtension, corepresentableBy, extensionUnitRight, homEquiv, homEquiv.trans, homEquivOfIsLeftKanExtension, homEquiv_comp
-/
def corepresentableBy₂ :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C)) ⋙
.CorepresentableBy (F ⊛ G ⊛ H) where coyoneda.obj (.op <| F ⊠ G ⊠ H)
  homEquiv :=
(corepresentableBy F (G ⊛ H)).homEquiv.trans
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitRight (G ⊛ H) (unit G H) F) _
  homEquiv_comp := by aesop

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `CorepresentableBy` structure asserting that the Type-valued functor
`Y ↦ ((F ⊠ G) ⊠ H ⟶ (tensor C).prod (𝟭 C) ⋙ tensor C ⋙ Y)` is corepresented by
`(F ⊛ G) ⊛ H`. -/
@[simps]
/--
Definition of `corepresentableBy₂'` / `corepresentableBy₂'` 的定义

English:
definition corepresentableBy₂'
  signature: :
  body: (corepresentableBy (F ⊛ G) H).homEquiv.trans
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitLeft (F ⊛ G) (unit F G) H) _
  homEquiv_comp := by aesop

#adaptation_note

中文:
定义 corepresentableBy₂'
  签名: :
  定义体: (corepresentableBy (F ⊛ G) H).homEquiv.trans
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitLeft (F ⊛ G) (unit F G) H) _
  homEquiv_comp := by aesop

#adaptation_note

Depends on / 依赖: Functor, Functor.homEquivOfIsLeftKanExtension, corepresentableBy, extensionUnitLeft, homEquiv, homEquiv.trans, homEquivOfIsLeftKanExtension, homEquiv_comp
-/
def corepresentableBy₂' :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
.CorepresentableBy ((F ⊛ G) ⊛ H) where coyoneda.obj (.op <| (F ⊠ G) ⊠ H)
  homEquiv :=
(corepresentableBy (F ⊛ G) H).homEquiv.trans
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitLeft (F ⊛ G) (unit F G) H) _
  homEquiv_comp := by aesop

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism of functors between
`((F ⊠ G) ⊠ H ⟶ (tensor C).prod (𝟭 C) ⋙ tensor C ⋙ -)` and
`(F ⊠ G ⊠ H ⟶ (𝟭 C).prod (tensor C) ⋙ tensor C ⋙ -)` that corresponds to the associator
isomorphism for Day convolution through `corepresentableBy₂` and `corepresentableBy₂`. -/
@[simps! +dsimpLhs]
/--
Definition of `associatorCorepresentingIso` / `associatorCorepresentingIso` 的定义

English:
definition associatorCorepresentingIso
  signature: :
  body: calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
          (whiskeringLeft _ _ _).obj (prod.associativity C C C).inverse ⋙
          coyoneda.obj (.op <| (prod.associativity C C C).inverse ⋙ (F ⊠ G) ⊠ H) :=
      isoWhiskerLeft _ (is

中文:
定义 associatorCorepresentingIso
  签名: :
  定义体: calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
          (whiskeringLeft _ _ _).obj (prod.associativity C C C).inverse ⋙
          coyoneda.obj (.op <| (prod.associativity C C C).inverse ⋙ (F ⊠ G) ⊠ H) :=
      isoWhiskerLeft _ (is

Depends on / 依赖: Equiv.toIso, NatIso, NatIso.ofComponents, associativity, congrLeft, congrLeft.fullyFaithfulFunctor.homEquiv, coyone, coyoneda, coyoneda.obj, fullyFaithfulFunctor, homEquiv, inverse, isoWhiskerLeft, ofComponents, prod.associativity, tensor, whiskeringLeft
-/
def associatorCorepresentingIso :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| (F ⊠ G) ⊠ H) ≅
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C)) ⋙
      coyoneda.obj (.op <| F ⊠ G ⊠ H) :=
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((tensor C).prod (𝟭 C)) ⋙
          (whiskeringLeft _ _ _).obj (prod.associativity C C C).inverse ⋙
          coyoneda.obj (.op <| (prod.associativity C C C).inverse ⋙ (F ⊠ G) ⊠ H) :=
      isoWhiskerLeft _ (isoWhiskerLeft _
        (NatIso.ofComponents fun _ => Equiv.toIso <|
          (prod.associativity C C C).congrLeft.fullyFaithfulFunctor.homEquiv))
    _ ≅ (whiskeringLeft _ _ _).obj
            ((prod.associativity C C C).inverse ⋙ (tensor C).prod (𝟭 C) ⋙ tensor C) ⋙
          coyoneda.obj (.op <| (prod.associativity C C C).inverse ⋙ (F ⊠ G) ⊠ H) :=
      .refl _
    _ ≅ (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C) ⋙ tensor C) ⋙
          coyoneda.obj (.op <| (prod.associativity C C C).inverse ⋙ (F ⊠ G) ⊠ H) :=
      isoWhiskerRight ((whiskeringLeft _ _ _).mapIso <| NatIso.ofComponents (fun _ => α_ _ _ _)) _
    _ ≅ (whiskeringLeft _ _ _).obj ((𝟭 C).prod (tensor C) ⋙ tensor C) ⋙
          coyoneda.obj (.op <| F ⊠ G ⊠ H) :=
isoWhiskerLeft _
coyoneda.mapIso Iso.op NatIso.ofComponents (fun _ => α_ _ _ _ |>.symm)

/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: : (F ⊛ G) ⊛ H ≅ F ⊛ G ⊛ H
  body: .uniqueUpToIso .ofIso (associatorCorepresentingIso F G H) corepresentableBy₂' F G H
    corepresentableBy₂ F G H

中文:
定义 associator
  签名: : (F ⊛ G) ⊛ H ≅ F ⊛ G ⊛ H
  定义体: .uniqueUpToIso .ofIso (associatorCorepresentingIso F G H) corepresentableBy₂' F G H
    corepresentableBy₂ F G H

Depends on / 依赖: associatorCorepresentingIso, uniqueUpToIso
-/
def associator : (F ⊛ G) ⊛ H ≅ F ⊛ G ⊛ H :=
.uniqueUpToIso .ofIso (associatorCorepresentingIso F G H) corepresentableBy₂' F G H
    corepresentableBy₂ F G H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Characterizing the forward direction of the associator isomorphism
with respect to the unit transformations. -/
@[reassoc (attr := simp)]
/--
lemma `associator_hom_unit_unit` / 引理 `associator_hom_unit_unit`

English:
lemma associator_hom_unit_unit
  given: (x y z : C)
  proof: by
have := congrArg (fun t => t.app ((x, y), z))
(corepresentableBy₂' F G H).homEquiv.rightInverse_symm
        (corepresentableBy₂ F G H |>.ofIso
.homEquiv (𝟙 _)) (associatorCorepresentingIso F G H).symm
  dsimp [associator, Coyoneda.fullyFaithful, corepresentableBy₂,
    corepresentableBy₂', Funct

中文:
引理 associator_hom_unit_unit
  条件: (x y z : C)
  证明: by
have := congrArg (fun t => t.app ((x, y), z))
(corepresentableBy₂' F G H).homEquiv.rightInverse_symm
        (corepresentableBy₂ F G H |>.ofIso
.homEquiv (𝟙 _)) (associatorCorepresentingIso F G H).symm
  dsimp [associator, Coyoneda.fullyFaithful, corepresentableBy₂,
    corepresentableBy₂', Funct

Depends on / 依赖: Category, Category.assoc, Category.comp_id, CorepresentableBy, Coyoneda, Coyoneda.fullyFaithful, Functor, Functor.CorepresentableBy.ofIso, Functor.corepresentableByEquiv, associator, associatorCorepresentingIso, comp_id, corepresentableByEquiv, fullyFaithful, homEquiv, homEquiv.rightInverse_symm, rightInverse_symm, t.app, whiskerLeft_id
-/
lemma associator_hom_unit_unit (x y z : C) :
    (unit F G).app (x, y) ▷ (H.obj z) ≫
      (unit (F ⊛ G) H).app (x otimes y, z) ≫
      (associator F G H).hom.app ((x otimes y) otimes z) =
    (α_ _ _ _).hom ≫
      (F.obj x ◁ (unit G H).app (y, z)) ≫
      (unit F (G ⊛ H)).app (x, y otimes z) ≫
      (F ⊛ G ⊛ H).map (α_ _ _ _).inv := by
have := congrArg (fun t => t.app ((x, y), z))
(corepresentableBy₂' F G H).homEquiv.rightInverse_symm
        (corepresentableBy₂ F G H |>.ofIso
.homEquiv (𝟙 _)) (associatorCorepresentingIso F G H).symm
  dsimp [associator, Coyoneda.fullyFaithful, corepresentableBy₂,
    corepresentableBy₂', Functor.CorepresentableBy.ofIso, corepresentableBy₂,
    Functor.corepresentableByEquiv, associatorCorepresentingIso] at this ⊢
  simp only [whiskerLeft_id, Category.comp_id, Category.assoc] at this
  simp only [Category.assoc, this]
  dsimp [Functor.FullyFaithful.homEquiv, Equivalence.fullyFaithfulFunctor, prod.associativity]
  erw [id_apply] -- TODO: remove this `erw` (introduced in #36613)
  simp


set_option backward.isDefEq.respectTransparency false in
/-- Characterizing the inverse direction of the associator
with respect to the unit transformations -/
@[reassoc (attr := simp)]
/--
lemma `associator_inv_unit_unit` / 引理 `associator_inv_unit_unit`

English:
lemma associator_inv_unit_unit
  given: (x y z : C)
  proof: by
have := congrArg (fun t => t.app (x, y, z))
(corepresentableBy₂ F G H).homEquiv.rightInverse_symm
        (corepresentableBy₂' F G H |>.ofIso
.homEquiv (𝟙 _)) (associatorCorepresentingIso F G H)
  dsimp [associator, Coyoneda.fullyFaithful, corepresentableBy₂,
    corepresentableBy₂', Functor.Core

中文:
引理 associator_inv_unit_unit
  条件: (x y z : C)
  证明: by
have := congrArg (fun t => t.app (x, y, z))
(corepresentableBy₂ F G H).homEquiv.rightInverse_symm
        (corepresentableBy₂' F G H |>.ofIso
.homEquiv (𝟙 _)) (associatorCorepresentingIso F G H)
  dsimp [associator, Coyoneda.fullyFaithful, corepresentableBy₂,
    corepresentableBy₂', Functor.Core

Depends on / 依赖: Category, Category.id_comp, CorepresentableBy, Coyoneda, Coyoneda.fullyFaithful, Functor, Functor.CorepresentableBy.ofIso, Functor.corepresentableByEquiv, Iso.inv_hom_id, associator, associatorCorepresentingIso, corepresentableByEquiv, fullyFaithful, homEquiv, homEquiv.rightInverse_symm, id_comp, id_whiskerRight, inv_hom_id, rightInverse_symm, t.app
-/
lemma associator_inv_unit_unit (x y z : C) :
    F.obj x ◁ (unit G H).app (y, z) ≫
      (unit F (G ⊛ H)).app (x, y otimes z) ≫
      (associator F G H).inv.app (x otimes y otimes z) =
    (α_ (F.obj x) (G.obj y) (H.obj z)).inv ≫ (unit F G).app (x, y) ▷ H.obj z ≫
      (unit (F ⊛ G) H).app (x otimes y, z) ≫
      ((F ⊛ G) ⊛ H).map (α_ x y z).hom := by
have := congrArg (fun t => t.app (x, y, z))
(corepresentableBy₂ F G H).homEquiv.rightInverse_symm
        (corepresentableBy₂' F G H |>.ofIso
.homEquiv (𝟙 _)) (associatorCorepresentingIso F G H)
  dsimp [associator, Coyoneda.fullyFaithful, corepresentableBy₂,
    corepresentableBy₂', Functor.CorepresentableBy.ofIso, corepresentableBy₂,
    Functor.corepresentableByEquiv, associatorCorepresentingIso] at this ⊢
  simp only [whiskerRight_tensor, id_whiskerRight, Category.id_comp, Iso.inv_hom_id] at this
  simp only [this]
  dsimp [Functor.FullyFaithful.homEquiv, Equivalence.fullyFaithfulFunctor, prod.associativity]
  erw [id_apply] -- TODO: remove this `erw` (introduced in #36613)
  simp


set_option backward.isDefEq.respectTransparency false in
variable {F G H} in
/--
theorem `associator_naturality` / 定理 `associator_naturality`

English:
theorem associator_naturality
  statement: {F' G' H' : C ⥤ V}
  proof: by
.homEquiv.injective apply (corepresentableBy₂' F G H)
  dsimp
  ext
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, Functor.prod_obj, tensor_obj,
    Functor.id_obj, Functor.homEquivOfIsLeftKanExtension_apply_app,
    externalProductBifunctor_map_app, Functor.leftUnitor_inv_app, 

中文:
定理 associator_naturality
  结论: {F' G' H' : C ⥤ V}
  证明: by
.homEquiv.injective apply (corepresentableBy₂' F G H)
  dsimp
  ext
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, Functor.prod_obj, tensor_obj,
    Functor.id_obj, Functor.homEquivOfIsLeftKanExtension_apply_app,
    externalProductBifunctor_map_app, Functor.leftUnitor_inv_app, 

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Functor, Functor.comp_obj, Functor.homEquivOfIsLeftKanExtension_apply_app, Functor.id_obj, Functor.leftUnitor_inv_app, Functor.prod_obj, NatTrans, NatTrans.comp_app, associator_hom_unit_unit_assoc, comp_app, comp_id, comp_obj, corepresentableBy_homEquiv_apply_app, externalProductBifunc, externalProductBifunctor_map_app, externalProductBifunctor_obj_obj, homEquiv
-/
theorem associator_naturality {F' G' H' : C ⥤ V}
    [DayConvolution F' G'] [DayConvolution G' H']
    [DayConvolution F' (G' ⊛ H')] [DayConvolution (F' ⊛ G') H']
    (f : F ⟶ F') (g : G ⟶ G') (h : H ⟶ H') :
      map (map f g) h ≫
        (associator F' G' H').hom =
      (associator F G H).hom ≫ map f (map g h) := by
.homEquiv.injective apply (corepresentableBy₂' F G H)
  dsimp
  ext
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, Functor.prod_obj, tensor_obj,
    Functor.id_obj, Functor.homEquivOfIsLeftKanExtension_apply_app,
    externalProductBifunctor_map_app, Functor.leftUnitor_inv_app, whiskerLeft_id, Category.comp_id,
    corepresentableBy_homEquiv_apply_app, NatTrans.comp_app, unit_app_map_app_assoc]
  rw [associator_hom_unit_unit_assoc]
  simp only [tensorHom_def, Category.assoc, externalProductBifunctor_obj_obj, tensor_obj,
    NatTrans.naturality, unit_app_map_app_assoc]
  rw [← comp_whiskerRight_assoc]; rw [unit_app_map_app]
  simp only [Functor.comp_obj, tensor_obj, comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc]; rw [associator_hom_unit_unit]; rw [whisker_exchange_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [unit_app_map_app]
  simp [tensorHom_def]

section pentagon

variable [forall (v : V) (d : C × C),
    Limits.PreservesColimitsOfShape (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `pentagon` / 引理 `pentagon`

English:
lemma pentagon
  statement: (H K : C ⥤ V)
  proof: by
  -- We repeatedly apply the fact that the functors are left Kan extensions
  apply Functor.hom_ext_of_isLeftKanExtension (α := unit ((F ⊛ G) ⊛ H) K)
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft ((F ⊛ G) ⊛ H) (unit (F ⊛ G) H) K)
  have : (((F ⊛ G) ⊠ H) ⊠ K).IsLeftKanE

中文:
引理 pentagon
  结论: (H K : C ⥤ V)
  证明: by
  -- We repeatedly apply the fact that the functors are left Kan extensions
  apply Functor.hom_ext_of_isLeftKanExtension (α := unit ((F ⊛ G) ⊛ H) K)
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft ((F ⊛ G) ⊛ H) (unit (F ⊛ G) H) K)
  have : (((F ⊛ G) ⊠ H) ⊠ K).IsLeftKanE
-/
lemma pentagon (H K : C ⥤ V)
    [DayConvolution G H] [DayConvolution (F ⊛ G) H] [DayConvolution F (G ⊛ H)]
    [DayConvolution H K] [DayConvolution G (H ⊛ K)] [DayConvolution (G ⊛ H) K]
    [DayConvolution ((F ⊛ G) ⊛ H) K] [DayConvolution (F ⊛ G) (H ⊛ K)]
    [DayConvolution (F ⊛ G ⊛ H) K] [DayConvolution F (G ⊛ H ⊛ K)]
    [DayConvolution F ((G ⊛ H) ⊛ K)] :
    map (associator F G H).hom (𝟙 K) ≫
        (associator F (G ⊛ H) K).hom ≫ map (𝟙 F) (associator G H K).hom =
      (associator (F ⊛ G) H K).hom ≫ (associator F G (H ⊛ K)).hom := by
  -- We repeatedly apply the fact that the functors are left Kan extensions
  apply Functor.hom_ext_of_isLeftKanExtension (α := unit ((F ⊛ G) ⊛ H) K)
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft ((F ⊛ G) ⊛ H) (unit (F ⊛ G) H) K)
  have : (((F ⊛ G) ⊠ H) ⊠ K).IsLeftKanExtension
    (α := extensionUnitLeft ((F ⊛ G) ⊠ H)
      (extensionUnitLeft _ (unit F G) H) K) :=
    isPointwiseLeftKanExtensionExtensionUnitLeft _ _ _
      (isPointwiseLeftKanExtensionExtensionUnitLeft _ _ _
        (isPointwiseLeftKanExtensionUnit F G)) |>.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension (α := extensionUnitLeft ((F ⊛ G) ⊠ H)
      (extensionUnitLeft _ (unit F G) H) K)
  -- And then we compute...
  ext ⟨⟨⟨i, j⟩, k⟩, l⟩
  have aux :
      ((unit F G).app (i, j) otimesₘ (unit H K).app (k, l)) ≫
        (unit (F ⊛ G) (H ⊛ K)).app ((i otimes j), (k otimes l)) =
      (α_ (F.obj i) (G.obj j) (H.obj k otimes K.obj l)).hom ≫
        F.obj i ◁ G.obj j ◁ (unit H K).app (k, l) ≫ F.obj i ◁ (unit G (H ⊛ K)).app (j, (k otimes l)) ≫
        (unit F (G ⊛ H ⊛ K)).app (i, (j otimes k otimes l)) ≫ (F ⊛ G ⊛ H ⊛ K).map (α_ i j (k otimes l)).inv ≫
        (associator F G (H ⊛ K)).inv.app ((i otimes j) otimes k otimes l) := by
    conv_rhs => simp only [Functor.comp_obj, tensor_obj, NatTrans.naturality,
      associator_inv_unit_unit_assoc, externalProductBifunctor_obj_obj, Iso.map_hom_inv_id,
      Category.comp_id]
    simp only [tensor_whiskerLeft_symm, Category.assoc, Iso.hom_inv_id_assoc,
    ← tensorHom_def'_assoc]
  dsimp
  simp only [MonoidalCategory.whiskerLeft_id, Category.comp_id, unit_app_map_app_assoc,
    externalProductBifunctor_obj_obj, NatTrans.id_app, tensorHom_id, associator_hom_unit_unit_assoc,
    tensor_obj, NatTrans.naturality]
  conv_rhs =>
    simp only [whiskerRight_tensor_symm_assoc, Iso.inv_hom_id_assoc, ← tensorHom_def_assoc]
    rw [reassoc_of% aux]
  simp only [Iso.inv_hom_id_app_assoc, ← comp_whiskerRight_assoc, associator_hom_unit_unit F G H]
  simp only [Functor.comp_obj, tensor_obj, comp_whiskerRight, whisker_assoc, Category.assoc,
    whiskerRight_comp_unit_app_assoc (F ⊛ G ⊛ H) K l (α_ i j k).inv,
    NatTrans.naturality_assoc, NatTrans.naturality, associator_hom_unit_unit_assoc,
    externalProductBifunctor_obj_obj, unit_app_map_app_assoc, NatTrans.id_app, id_tensorHom,
    Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, associator_hom_unit_unit]
  simp [← Functor.map_comp, pentagon_inv, pentagon_assoc]

end pentagon

end associator

end

end DayConvolution

/--
Definition of `DayConvolutionUnit` / `DayConvolutionUnit` 的定义

English:
class DayConvolutionUnit
  parameters: (F : C ⥤ V)
  axioms and operations (2):
    - can : 𝟙_ V ⟶ F.obj (𝟙_ C)
    - isPointwiseLeftKanExtensionCan : Functor.LeftExtension.mk F ({ app _ := can } : Functor.fromPUnit.{0} (𝟙_ V) ⟶ Functor.fromPUnit.{0} (𝟙_ C) ⋙ F) |>.IsPointwiseLeftKanExtension

中文:
类 DayConvolutionUnit
  参数: (F : C ⥤ V)
  公理与运算 (2 个):
    - can : 𝟙_ V ⟶ F.obj (𝟙_ C)
    - isPointwiseLeftKanExtensionCan : 函子.LeftExtension.mk F ({ app _ := can } : 函子.fromPUnit.{0} (𝟙_ V) ⟶ 函子.fromPUnit.{0} (𝟙_ C) ⋙ F) |>.IsPointwiseLeftKanExtension

Depends on / 依赖: Functor, Functor.fromPUnit, fromPUnit
-/
class DayConvolutionUnit (F : C ⥤ V) where
  /-- A "canonical" structure map `𝟙_ V ⟶ F.obj (𝟙_ C)` that defines a natural transformation
  `fromPUnit (𝟙_ V) ⟶ fromPUnit (𝟙_ C) ⋙ F`. -/
  can : 𝟙_ V ⟶ F.obj (𝟙_ C)
  /-- The canonical map `𝟙_ V ⟶ F.obj (𝟙_ C)` exhibits `F` as a pointwise left Kan extension
  of `fromPUnit.{0} 𝟙_ V` along `fromPUnit.{0} 𝟙_ C`. -/
  isPointwiseLeftKanExtensionCan : Functor.LeftExtension.mk F
    ({ app _ := can } : Functor.fromPUnit.{0} (𝟙_ V) ⟶
      Functor.fromPUnit.{0} (𝟙_ C) ⋙ F) |>.IsPointwiseLeftKanExtension

namespace DayConvolutionUnit

variable (U : C ⥤ V) [DayConvolutionUnit U]
open scoped DayConvolution
open ExternalProduct CategoryTheory.Functor

/--
Definition of `φ` / `φ` 的定义

English:
abbreviation φ
  signature: : Functor.fromPUnit.{0} (𝟙_ V) ⟶ Functor.fromPUnit.{0} (𝟙_ C) ⋙ U where
  body: can

中文:
缩写 φ
  签名: : 函子.fromPUnit.{0} (𝟙_ V) ⟶ 函子.fromPUnit.{0} (𝟙_ C) ⋙ U where
  定义体: can

Depends on / 依赖: cat_disch, hom_ext, isPullback, isPullback.hom_ext, isPullback.lift, pullHom
-/
abbrev φ : Functor.fromPUnit.{0} (𝟙_ V) ⟶ Functor.fromPUnit.{0} (𝟙_ C) ⋙ U where
  app _ := can

/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {c : C} {v : V} {g h : U.obj c ⟶ v}
  proof: by
  apply (isPointwiseLeftKanExtensionCan c).hom_ext
  intro j
  simpa using e j.hom

中文:
引理 hom_ext
  结论: {c : C} {v : V} {g h : U.obj c ⟶ v}
  证明: by
  apply (isPointwiseLeftKanExtensionCan c).hom_ext
  intro j
  simpa using e j.hom

Depends on / 依赖: _eq_pullHom, hom_ext, isPointwiseLeftKanExtensionCan, j.hom, pullHom
-/
lemma hom_ext {c : C} {v : V} {g h : U.obj c ⟶ v}
    (e : forall f : 𝟙_ C ⟶ c, can ≫ U.map f ≫ g = can ≫ U.map f ≫ h) :
    g = h := by
  apply (isPointwiseLeftKanExtensionCan c).hom_ext
  intro j
  simpa using e j.hom

variable (F : C ⥤ V)
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorLeft v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorRight v)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (F ⊠ U).IsLeftKanExtension extensionUnitRight U (φ U) F
  body: isPointwiseLeftKanExtensionExtensionUnitRight
.isLeftKanExtension U (φ U) F isPointwiseLeftKanExtensionCan

中文:
实例 :
  签名: (F ⊠ U).是LeftKanExtension extensionUnitRight U (φ U) F
  定义体: isPointwiseLeftKanExtensionExtensionUnitRight
.isLeftKanExtension U (φ U) F isPointwiseLeftKanExtensionCan

Depends on / 依赖: _eq_pullHom, isLeftKanExtension, isPointwiseLeftKanExtensionCan, isPointwiseLeftKanExtensionExtensionUnitRight, pullHom
-/
instance : (F ⊠ U).IsLeftKanExtension extensionUnitRight U (φ U) F :=
  isPointwiseLeftKanExtensionExtensionUnitRight
.isLeftKanExtension U (φ U) F isPointwiseLeftKanExtensionCan

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (U ⊠ F).IsLeftKanExtension extensionUnitLeft U (φ U) F
  body: isPointwiseLeftKanExtensionExtensionUnitLeft
.isLeftKanExtension U (φ U) F isPointwiseLeftKanExtensionCan

中文:
实例 :
  签名: (U ⊠ F).是LeftKanExtension extensionUnitLeft U (φ U) F
  定义体: isPointwiseLeftKanExtensionExtensionUnitLeft
.isLeftKanExtension U (φ U) F isPointwiseLeftKanExtensionCan

Depends on / 依赖: _eq_pullHom, isLeftKanExtension, isPointwiseLeftKanExtensionCan, isPointwiseLeftKanExtensionExtensionUnitLeft, pullHom
-/
instance : (U ⊠ F).IsLeftKanExtension extensionUnitLeft U (φ U) F :=
  isPointwiseLeftKanExtensionExtensionUnitLeft
.isLeftKanExtension U (φ U) F isPointwiseLeftKanExtensionCan

set_option backward.isDefEq.respectTransparency false in
/-- A `CorepresentableBy` structure that characterizes maps out of `U ⊛ F`
by leveraging the fact that `U ⊠ F` is a left Kan extension of `(fromPUnit 𝟙_ V) ⊠ F`. -/
@[simps]
/--
Definition of `corepresentableByLeft` / `corepresentableByLeft` 的定义

English:
definition corepresentableByLeft
  signature: [DayConvolution U F]
  body: .trans Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit U F) _
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitLeft U (φ U) F) _
  homEquiv_comp := by aesop

中文:
定义 corepresentableByLeft
  签名: [Day卷积 U F]
  定义体: .trans Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit U F) _
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitLeft U (φ U) F) _
  homEquiv_comp := by aesop

Depends on / 依赖: DayConvolution, DayConvolution.unit, Functor, Functor.homEquivOfIsLeftKanExtension, extensionUnitLeft, homEquivOfIsLeftKanExtension, homEquiv_comp
-/
def corepresentableByLeft [DayConvolution U F] :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
.CorepresentableBy (U ⊛ F) where coyoneda.obj (.op <| Functor.fromPUnit.{0} (𝟙_ V) ⊠ F)
  homEquiv :=
.trans Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit U F) _
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitLeft U (φ U) F) _
  homEquiv_comp := by aesop

set_option backward.isDefEq.respectTransparency false in
/-- A `CorepresentableBy` structure that characterizes maps out of `F ⊛ U` by
leveraging the fact that `F ⊠ U` is a left Kan extension of `F ⊠ (fromPUnit 𝟙_ V)`. -/
@[simps]
/--
Definition of `corepresentableByRight` / `corepresentableByRight` 的定义

English:
definition corepresentableByRight
  signature: [DayConvolution F U]
  body: .trans Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit F U) _
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitRight U (φ U) F) _
  homEquiv_comp := by aesop

#adaptation_note

中文:
定义 corepresentableByRight
  签名: [Day卷积 F U]
  定义体: .trans Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit F U) _
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitRight U (φ U) F) _
  homEquiv_comp := by aesop

#adaptation_note

Depends on / 依赖: DayConvolution, DayConvolution.unit, Functor, Functor.homEquivOfIsLeftKanExtension, _eq_pullHom, extensionUnitRight, homEquivOfIsLeftKanExtension, homEquiv_comp, pullHom
-/
def corepresentableByRight [DayConvolution F U] :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
.CorepresentableBy (F ⊛ U) where coyoneda.obj (.op <| F ⊠ Functor.fromPUnit.{0} (𝟙_ V))
  homEquiv :=
.trans Functor.homEquivOfIsLeftKanExtension _ (DayConvolution.unit F U) _
      Functor.homEquivOfIsLeftKanExtension _ (extensionUnitRight U (φ U) F) _
  homEquiv_comp := by aesop

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism of corepresentable functors that defines the left unitor for
Day convolution. -/
@[simps! +dsimpLhs]
/--
Definition of `leftUnitorCorepresentingIso` / `leftUnitorCorepresentingIso` 的定义

English:
definition leftUnitorCorepresentingIso
  signature: :
  body: by
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
          (whiskeringLeft _ _ _).obj (prod.leftUnitorEquivalence C).inverse ⋙
          coyoneda.obj (.op <|
           (prod.leftUnitorEquivalence C).inverse 

中文:
定义 leftUnitorCorepresentingIso
  签名: :
  定义体: by
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
          (whiskeringLeft _ _ _).obj (prod.leftUnitorEquivalence C).inverse ⋙
          coyoneda.obj (.op <|
           (prod.leftUnitorEquivalence C).inverse 

Depends on / 依赖: Equiv.toIso, Functor, Functor.fromPUnit, NatIso, NatIso.ofComponents, cat_disch, congrLeft, congrLeft.fullyFaithfulFunctor.homEquiv, coyoneda, coyoneda.obj, fromPUnit, fullyFaithfulFunctor, homEquiv, hom_self, inverse, isoWhiskerLeft, leftUnitorEquival, leftUnitorEquivalence, ofComponents, prod.leftUnitorEquival
-/
def leftUnitorCorepresentingIso :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
      coyoneda.obj (.op <| Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) ≅
    coyoneda.obj (.op <| F) := by
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C)) ⋙
          (whiskeringLeft _ _ _).obj (prod.leftUnitorEquivalence C).inverse ⋙
          coyoneda.obj (.op <|
           (prod.leftUnitorEquivalence C).inverse ⋙ Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) :=
      isoWhiskerLeft _ (isoWhiskerLeft _
        (NatIso.ofComponents fun _ => Equiv.toIso <|
          (prod.leftUnitorEquivalence C).congrLeft.fullyFaithfulFunctor.homEquiv))
    _ ≅ (whiskeringLeft _ _ _).obj
            ((prod.leftUnitorEquivalence C).inverse ⋙ (Functor.fromPUnit.{0} (𝟙_ C)).prod (𝟭 C) ⋙
              tensor C) ⋙
          coyoneda.obj (.op <|
            (prod.leftUnitorEquivalence C).inverse ⋙ Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) :=
      .refl _
    _ ≅ (whiskeringLeft _ _ _).obj (𝟭 _) ⋙ coyoneda.obj (.op <|
          (prod.leftUnitorEquivalence C).inverse ⋙ Functor.fromPUnit.{0} (𝟙_ V) ⊠ F) :=
      isoWhiskerRight ((whiskeringLeft _ _ _).mapIso <| NatIso.ofComponents fun _ => fun_ _) _
_ ≅ _ := coyoneda.mapIso Iso.op NatIso.ofComponents fun _ => (fun_ _).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism of corepresentable functors that defines the right unitor for
Day convolution. -/
@[simps! +dsimpLhs]
/--
Definition of `rightUnitorCorepresentingIso` / `rightUnitorCorepresentingIso` 的定义

English:
definition rightUnitorCorepresentingIso
  signature: :
  body: by
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
          (whiskeringLeft _ _ _).obj (prod.rightUnitorEquivalence C).inverse ⋙
          coyoneda.obj (.op <|
           (prod.rightUnitorEquivalence C).invers

中文:
定义 rightUnitorCorepresentingIso
  签名: :
  定义体: by
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
          (whiskeringLeft _ _ _).obj (prod.rightUnitorEquivalence C).inverse ⋙
          coyoneda.obj (.op <|
           (prod.rightUnitorEquivalence C).invers

Depends on / 依赖: Equiv.toIso, Functor, Functor.fromPUnit, NatIso, NatIso.ofComponents, congrLeft, congrLeft.fullyFaithfulFunctor.homEquiv, coyoneda, coyoneda.obj, fromPUnit, fullyFaithfulFunctor, homEquiv, inverse, isoWhiskerLeft, ofComponents, prod.rightUnitorEqu, prod.rightUnitorEquivalence, rightUnitorEqu, rightUnitorEquivalence, tensor
-/
def rightUnitorCorepresentingIso :
    (whiskeringLeft _ _ _).obj (tensor C) ⋙
      (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
      coyoneda.obj (.op <| F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) ≅
    coyoneda.obj (.op <| F) := by
  calc
    _ ≅ (whiskeringLeft _ _ _).obj (tensor C) ⋙
          (whiskeringLeft _ _ _).obj ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙
          (whiskeringLeft _ _ _).obj (prod.rightUnitorEquivalence C).inverse ⋙
          coyoneda.obj (.op <|
           (prod.rightUnitorEquivalence C).inverse ⋙ F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
      isoWhiskerLeft _ (isoWhiskerLeft _
        (NatIso.ofComponents fun _ => Equiv.toIso <|
          (prod.rightUnitorEquivalence C).congrLeft.fullyFaithfulFunctor.homEquiv))
    _ ≅ (whiskeringLeft _ _ _).obj
            ((prod.rightUnitorEquivalence C).inverse ⋙
              ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) ⋙ tensor C) ⋙
          coyoneda.obj (.op <|
            (prod.rightUnitorEquivalence C).inverse ⋙ F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
      .refl _
    _ ≅ (whiskeringLeft _ _ _).obj (𝟭 _) ⋙ coyoneda.obj (.op <|
          (prod.rightUnitorEquivalence C).inverse ⋙ F ⊠ Functor.fromPUnit.{0} (𝟙_ V)) :=
      isoWhiskerRight ((whiskeringLeft _ _ _).mapIso <| NatIso.ofComponents fun _ => ρ_ _) _
_ ≅ _ := coyoneda.mapIso Iso.op NatIso.ofComponents fun _ => (ρ_ _).symm

/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: [DayConvolution U F]
  body: .uniqueUpToIso .ofIso (leftUnitorCorepresentingIso F) corepresentableByLeft U F
 Functor.corepresentableByEquiv.symm (.refl _)

中文:
定义 leftUnitor
  签名: [Day卷积 U F]
  定义体: .uniqueUpToIso .ofIso (leftUnitorCorepresentingIso F) corepresentableByLeft U F
 Functor.corepresentableByEquiv.symm (.refl _)

Depends on / 依赖: D.hom, D.pullHom, Functor, Functor.corepresentableByEquiv.symm, _hom_self, _self, cat_disch, corepresentableByEquiv, corepresentableByLeft, leftUnitorCorepresentingIso, pullHom, uniqueUpToIso
-/
def leftUnitor [DayConvolution U F] : U ⊛ F ≅ F :=
.uniqueUpToIso .ofIso (leftUnitorCorepresentingIso F) corepresentableByLeft U F
 Functor.corepresentableByEquiv.symm (.refl _)

/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: [DayConvolution F U]
  body: .uniqueUpToIso .ofIso (rightUnitorCorepresentingIso F) corepresentableByRight U F
 Functor.corepresentableByEquiv.symm (.refl _)

中文:
定义 rightUnitor
  签名: [Day卷积 F U]
  定义体: .uniqueUpToIso .ofIso (rightUnitorCorepresentingIso F) corepresentableByRight U F
 Functor.corepresentableByEquiv.symm (.refl _)

Depends on / 依赖: Functor, Functor.corepresentableByEquiv.symm, corepresentableByEquiv, corepresentableByRight, rightUnitorCorepresentingIso, uniqueUpToIso
-/
def rightUnitor [DayConvolution F U] : F ⊛ U ≅ F :=
.uniqueUpToIso .ofIso (rightUnitorCorepresentingIso F) corepresentableByRight U F
 Functor.corepresentableByEquiv.symm (.refl _)

section

omit [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
  (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorLeft v)]
variable [DayConvolution U F]

set_option backward.isDefEq.respectTransparency false in
/-- Characterizing the forward direction of `leftUnitor` via the universal maps. -/
@[reassoc (attr := simp)]
/--
lemma `leftUnitor_hom_unit_app` / 引理 `leftUnitor_hom_unit_app`

English:
lemma leftUnitor_hom_unit_app
  given: (y : C)
  proof: by
have := congrArg (fun t => t.app (.mk PUnit.unit, y))
(corepresentableByLeft U F).homEquiv.rightInverse_symm
        ((leftUnitorCorepresentingIso F).symm.hom.app F) (𝟙 _)
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableByLeft,
    leftUnitorCorepresentingIso, Functor.CorepresentableB

中文:
引理 leftUnitor_hom_unit_app
  条件: (y : C)
  证明: by
have := congrArg (fun t => t.app (.mk PUnit.unit, y))
(corepresentableByLeft U F).homEquiv.rightInverse_symm
        ((leftUnitorCorepresentingIso F).symm.hom.app F) (𝟙 _)
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableByLeft,
    leftUnitorCorepresentingIso, Functor.CorepresentableB

Depends on / 依赖: Category, Category.comp_id, CorepresentableBy, Coyoneda, Coyoneda.fullyFaithful, D.hom, Equivalence, Equivalence.congrLeft, Equivalence.fullyF, Functor, Functor.CorepresentableBy.ofIso, Functor.corepresentableByEquiv, PUnit.unit, comp_id, congrLeft, corepresentableByEquiv, corepresentableByLeft, fullyF, fullyFaithful, homEquiv
-/
lemma leftUnitor_hom_unit_app (y : C) :
    can ▷ F.obj y ≫ (DayConvolution.unit U F).app (𝟙_ C, y) ≫
      (leftUnitor U F).hom.app (𝟙_ C otimes y) =
    (fun_ (F.obj y)).hom ≫ F.map (fun_ y).inv := by
have := congrArg (fun t => t.app (.mk PUnit.unit, y))
(corepresentableByLeft U F).homEquiv.rightInverse_symm
        ((leftUnitorCorepresentingIso F).symm.hom.app F) (𝟙 _)
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableByLeft,
    leftUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv] at this ⊢
  simp only [whiskerLeft_id, Category.comp_id] at this
  simp only [Category.comp_id, this]
  simp [prod.leftUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
lemma `leftUnitor_inv_app` / 引理 `leftUnitor_inv_app`

English:
lemma leftUnitor_inv_app
  given: (x : C)
  proof: by
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableByLeft,
    leftUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv]
  dsimp [prod.leftUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEqui

中文:
引理 leftUnitor_inv_app
  条件: (x : C)
  证明: by
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableByLeft,
    leftUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv]
  dsimp [prod.leftUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEqui

Depends on / 依赖: CorepresentableBy, Coyoneda, Coyoneda.fullyFaithful, Equivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor, FullyFaithful, Functor, Functor.CorepresentableBy.ofIso, Functor.FullyFaithful.homEquiv, Functor.corepresentableByEquiv, congrLeft, corepresentableByEquiv, corepresentableByLeft, fullyFaithful, fullyFaithfulFunctor, homEquiv, id_apply, introduced, leftUnitor
-/
lemma leftUnitor_inv_app (x : C) :
    (leftUnitor U F).inv.app x =
    (fun_ (F.obj x)).inv ≫ can ▷ F.obj x ≫ (DayConvolution.unit U F).app (𝟙_ C, x) ≫
      (U ⊛ F).map (fun_ x).hom := by
  dsimp [leftUnitor, Coyoneda.fullyFaithful, corepresentableByLeft,
    leftUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv]
  dsimp [prod.leftUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]
  erw [id_apply] -- TODO: remove this `erw` (introduced in #36613)
  simp

set_option backward.isDefEq.respectTransparency false in
variable {F} in
@[reassoc (attr := simp)]
/--
lemma `leftUnitor_naturality` / 引理 `leftUnitor_naturality`

English:
lemma leftUnitor_naturality
  given: {G : C ⥤ V} [DayConvolution U G] (f : F ⟶ G)
  proof: by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension _ (extensionUnitLeft U (φ U) F) _
  ext
  simp [← whisker_exchange_assoc]

中文:
引理 leftUnitor_naturality
  条件: {G : C ⥤ V} [Day卷积 U G] (f : F ⟶ G)
  证明: by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension _ (extensionUnitLeft U (φ U) F) _
  ext
  simp [← whisker_exchange_assoc]

Depends on / 依赖: D.hom, DayConvolution, DayConvolution.unit, Functor, Functor.hom_ext_of_isLeftKanExtension, extensionUnitLeft, hom_ext_of_isLeftKanExtension, pullHom, whisker_exchange_assoc
-/
lemma leftUnitor_naturality {G : C ⥤ V} [DayConvolution U G] (f : F ⟶ G) :
    DayConvolution.map (𝟙 _) f ≫ (leftUnitor U G).hom =
    (leftUnitor U F).hom ≫ f := by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension _ (extensionUnitLeft U (φ U) F) _
  ext
  simp [← whisker_exchange_assoc]

end

section

omit [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
  (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorRight v)]
variable [DayConvolution F U]

set_option backward.isDefEq.respectTransparency false in
/-- Characterizing the forward direction of `rightUnitor` via the universal maps. -/
@[reassoc (attr := simp)]
/--
lemma `rightUnitor_hom_unit_app` / 引理 `rightUnitor_hom_unit_app`

English:
lemma rightUnitor_hom_unit_app
  given: (x : C)
  proof: by
have := congrArg (fun t => t.app (x, .mk PUnit.unit))
(corepresentableByRight U F).homEquiv.rightInverse_symm
        ((rightUnitorCorepresentingIso F).symm.hom.app F) (𝟙 _)
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableByRight,
    rightUnitorCorepresentingIso, Functor.Corepresent

中文:
引理 rightUnitor_hom_unit_app
  条件: (x : C)
  证明: by
have := congrArg (fun t => t.app (x, .mk PUnit.unit))
(corepresentableByRight U F).homEquiv.rightInverse_symm
        ((rightUnitorCorepresentingIso F).symm.hom.app F) (𝟙 _)
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableByRight,
    rightUnitorCorepresentingIso, Functor.Corepresent

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, CorepresentableBy, Coyoneda, Coyoneda.fullyFaithful, Functor, Functor.CorepresentableBy.ofIso, Functor.corepresentableByEquiv, Iso.hom_inv_id, MonoidalCategory, MonoidalCategory.whiskerRight_id, PUnit.unit, comp_id, corepresentableByEquiv, corepresentableByRight, fullyFaithful, homEquiv, homEquiv.rightInverse_symm, hom_inv_id
-/
lemma rightUnitor_hom_unit_app (x : C) :
    F.obj x ◁ can ≫ (DayConvolution.unit F U).app (x, 𝟙_ C) ≫
      (rightUnitor U F).hom.app (x otimes 𝟙_ C) =
    (ρ_ _).hom ≫ F.map (ρ_ x).inv := by
have := congrArg (fun t => t.app (x, .mk PUnit.unit))
(corepresentableByRight U F).homEquiv.rightInverse_symm
        ((rightUnitorCorepresentingIso F).symm.hom.app F) (𝟙 _)
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableByRight,
    rightUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv] at this ⊢
  simp only [MonoidalCategory.whiskerRight_id, Category.id_comp, Iso.hom_inv_id,
    Category.comp_id] at this
  simp only [Category.comp_id, this]
  simp [prod.rightUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
lemma `rightUnitor_inv_app` / 引理 `rightUnitor_inv_app`

English:
lemma rightUnitor_inv_app
  given: (x : C)
  proof: by
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableByRight,
    rightUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv, Iso.toEquiv, Equiv.toIso]
  dsimp [prod.rightUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
   

中文:
引理 rightUnitor_inv_app
  条件: (x : C)
  证明: by
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableByRight,
    rightUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv, Iso.toEquiv, Equiv.toIso]
  dsimp [prod.rightUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
   

Depends on / 依赖: CorepresentableBy, Coyoneda, Coyoneda.fullyFaithful, Equiv.toIso, Equivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor, FullyFaithful, Functor, Functor.CorepresentableBy.ofIso, Functor.FullyFaithful.homEquiv, Functor.corepresentableByEquiv, Iso.toEquiv, congrLeft, corepresentableByEquiv, corepresentableByRight, fullyFaithful, fullyFaithfulFunctor, homEquiv, id_apply
-/
lemma rightUnitor_inv_app (x : C) :
    (rightUnitor U F).inv.app x =
    (ρ_ (F.obj x)).inv ≫ F.obj x ◁ can ≫ (DayConvolution.unit F U).app (x, 𝟙_ C) ≫
      (F ⊛ U).map (ρ_ x).hom := by
  dsimp [rightUnitor, Coyoneda.fullyFaithful, corepresentableByRight,
    rightUnitorCorepresentingIso, Functor.CorepresentableBy.ofIso,
    Functor.corepresentableByEquiv, Iso.toEquiv, Equiv.toIso]
  dsimp [prod.rightUnitorEquivalence, Equivalence.congrLeft, Equivalence.fullyFaithfulFunctor,
    Functor.FullyFaithful.homEquiv]
  erw [id_apply] -- TODO: remove this `erw` (introduced in #36613)
  simp

set_option backward.isDefEq.respectTransparency false in
variable {F} in
@[reassoc (attr := simp)]
/--
lemma `rightUnitor_naturality` / 引理 `rightUnitor_naturality`

English:
lemma rightUnitor_naturality
  given: {G : C ⥤ V} [DayConvolution G U] (f : F ⟶ G)
  proof: by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension _ (extensionUnitRight U (φ U) F) _
  ext
  simp [whisker_exchange_assoc]

中文:
引理 rightUnitor_naturality
  条件: {G : C ⥤ V} [Day卷积 G U] (f : F ⟶ G)
  证明: by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension _ (extensionUnitRight U (φ U) F) _
  ext
  simp [whisker_exchange_assoc]

Depends on / 依赖: DayConvolution, DayConvolution.unit, Functor, Functor.hom_ext_of_isLeftKanExtension, extensionUnitRight, hom_ext_of_isLeftKanExtension, whisker_exchange_assoc
-/
lemma rightUnitor_naturality {G : C ⥤ V} [DayConvolution G U] (f : F ⟶ G) :
    DayConvolution.map f (𝟙 _) ≫ (rightUnitor U G).hom =
    (rightUnitor U F).hom ≫ f := by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension _ (extensionUnitRight U (φ U) F) _
  ext
  simp [whisker_exchange_assoc]

end

end DayConvolutionUnit

section triangle

open DayConvolution
open DayConvolutionUnit
open ExternalProduct

variable [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (tensor C) d) (tensorLeft v)]
  [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (tensor C) d) (tensorRight v)]
  [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
  [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
  [forall (v : V) (d : C × C), Limits.PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `DayConvolution.triangle` / 引理 `DayConvolution.triangle`

English:
lemma DayConvolution.triangle
  statement: (F G U : C ⥤ V) [DayConvolutionUnit U]
  proof: by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft (F ⊛ U) (DayConvolution.unit F U) G)
.IsLeftKanExtension have : (F ⊠ U) ⊠ G
      (α := extensionUnitLeft (F ⊠ U) (extensionUnitRight U (DayConvolu

中文:
引理 Day卷积.triangle
  结论: (F G U : C ⥤ V) [DayConvolutionUnit U]
  证明: by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft (F ⊛ U) (DayConvolution.unit F U) G)
.IsLeftKanExtension have : (F ⊠ U) ⊠ G
      (α := extensionUnitLeft (F ⊠ U) (extensionUnitRight U (DayConvolu

Depends on / 依赖: DayConvolution, DayConvolution.unit, DayConvolutionUnit, DayConvolutionUnit.isPointwiseLeftKanExtensionCan, Functor, Functor.hom_ext_of_isLeftKanExtension, IsLeftKanExtension, extensionUnitLeft, extensionUnitRight, hom_ext_of_isLeftKanExtension, isPointwiseLeftKanExtensionCan, isPointwiseLeftKanExtensionExtensionUnitLeft, isPointwiseLeftKanExtensionExtensionUnitRight
-/
lemma DayConvolution.triangle (F G U : C ⥤ V) [DayConvolutionUnit U]
    [DayConvolution F U] [DayConvolution U G]
    [DayConvolution F (U ⊛ G)] [DayConvolution (F ⊛ U) G] [DayConvolution F G] :
    (DayConvolution.associator F U G).hom ≫
      DayConvolution.map (𝟙 F) (DayConvolutionUnit.leftUnitor U G).hom =
    DayConvolution.map (DayConvolutionUnit.rightUnitor U F).hom (𝟙 G) := by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit _ _) _
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft (F ⊛ U) (DayConvolution.unit F U) G)
.IsLeftKanExtension have : (F ⊠ U) ⊠ G
      (α := extensionUnitLeft (F ⊠ U) (extensionUnitRight U (DayConvolutionUnit.φ U) F) G) :=
    isPointwiseLeftKanExtensionExtensionUnitLeft (F ⊠ U) _ G
      (isPointwiseLeftKanExtensionExtensionUnitRight U (DayConvolutionUnit.φ U) F <|
        DayConvolutionUnit.isPointwiseLeftKanExtensionCan (F := U)) |>.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension
    (α := extensionUnitLeft (F ⊠ U) (extensionUnitRight U (DayConvolutionUnit.φ U) F) G)
  ext
  dsimp
  simp only [MonoidalCategory.whiskerRight_id, Category.id_comp, Iso.hom_inv_id, whisker_assoc,
    MonoidalCategory.whiskerLeft_id, Category.comp_id,
    DayConvolution.associator_hom_unit_unit_assoc, externalProductBifunctor_obj_obj, tensor_obj,
    NatTrans.naturality, unit_app_map_app_assoc, NatTrans.id_app, id_tensorHom,
    Category.assoc, Iso.inv_hom_id_assoc, unit_app_map_app, Functor.comp_obj,
    tensorHom_id, Iso.cancel_iso_hom_left]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc, leftUnitor_hom_unit_app,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, rightUnitor_hom_unit_app]
  simp [← Functor.map_comp]

end triangle

section

variable (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]

/--
Definition of `LawfulDayConvolutionMonoidalCategoryStruct` / `LawfulDayConvolutionMonoidalCategoryStruct` 的定义

English:
class LawfulDayConvolutionMonoidalCategoryStruct
  axioms and operations (12):
    - ι((C V D)) : D ⥤ C ⥤ V
    - convolutionExtensionUnit((C) (V) (d d' : D)) : ι.obj d ⊠ ι.obj d' ⟶ tensor C ⋙ ι.obj (d otimes d')
    - isPointwiseLeftKanExtensionConvolutionExtensionUnit((d d' : D)) : (Functor.LeftExtension.mk _ <| convolutionExtensionUnit d d').IsPointwiseLeftKanExtension
    - unitUnit((C) (V) (D)) : 𝟙_ V ⟶ (ι.obj <| 𝟙_ D).obj (𝟙_ C)
    - isPointwiseLeftKanExtensionUnitUnit((C) (V) (D)) : Functor.LeftExtension.mk _ ({ app _ := unitUnit } : Functor.fromPUnit.{0} (𝟙_ V) ⟶ Functor.fromPUnit.{0} (𝟙_ C) ⋙ (ι.obj <| 𝟙_ D)) |>.IsPointwiseLeftKanExtension
    - faithful_ι : ι.Faithful  [default: by infer_instance]
    - convolutionExtensionUnit_comp_ι_map_tensorHom_app((C) (V) {d₁ d₂ d₁' d₂' : D} (f₁ : d₁ ⟶ d₁') (f₂ : d₂ ⟶ d₂') (x y : C)) : (convolutionExtensionUnit d₁ d₂).app (x, y) ≫ (ι.map (f₁ otimesₘ f₂)).app (x otimes y) = ((ι.map f₁).app x otimesₘ (ι.map f₂).app y) ≫ (convolutionExtensionUnit d₁' d₂').app (x, y)
    - convolutionExtensionUnit_comp_ι_map_whiskerLeft_app((V) (d₁ : D) {d₂ d₂' : D} (f₂ : d₂ ⟶ d₂') (x y : C)) : (convolutionExtensionUnit d₁ d₂).app (x, y) ≫ (ι.map (d₁ ◁ f₂)).app (x otimes y) = ((ι.obj d₁).obj x ◁ (ι.map f₂).app y) ≫ (convolutionExtensionUnit d₁ d₂').app (x, y)
    - convolutionExtensionUnit_comp_ι_map_whiskerRight_app((C) (V) {d₁ d₁' : D} (f₁ : d₁ ⟶ d₁') (d₂ : D) (x y : C)) : (convolutionExtensionUnit d₁ d₂).app (x, y) ≫ (ι.map (f₁ ▷ d₂)).app (x otimes y) = ((ι.map f₁).app x ▷ (ι.obj d₂).obj y) ≫ (convolutionExtensionUnit d₁' d₂).app (x, y)
    - associator_hom_unit_unit((V) (d d' d'' : D) (x y z : C)) : (convolutionExtensionUnit d d').app (x, y) ▷ (ι.obj d'').obj z ≫ (convolutionExtensionUnit (d otimes d') d'').app (x otimes y, z) ≫ (ι.map (α_ d d' d'').hom).app ((x otimes y) otimes z) = (α_ _ _ _).hom ≫ ((ι.obj d).obj x ◁ (convolutionExtensionUnit d' d'').app (y, z)) ≫ (convolutionExtensionUnit d (d' otimes d'')).app (x, y otimes z) ≫ (ι.obj (d otimes d' otimes d'')).map (α_ _ _ _).inv
    - leftUnitor_hom_unit_app((V) (d : D) (y : C)) : unitUnit ▷ (ι.obj d).obj y ≫ (convolutionExtensionUnit (𝟙_ D) d).app (𝟙_ C, y) ≫ (ι.map (fun_ d).hom).app (𝟙_ C otimes y) = (fun_ ((ι.obj d).obj y)).hom ≫ (ι.obj d).map (fun_ y).inv
    - rightUnitor_hom_unit_app((V) (d : D) (y : C)) : (ι.obj d).obj y ◁ unitUnit ≫ (convolutionExtensionUnit d (𝟙_ D)).app (y, 𝟙_ C) ≫ (ι.map (ρ_ d).hom).app (y otimes 𝟙_ C) = (ρ_ _).hom ≫ (ι.obj d).map (ρ_ y).inv

中文:
类 LawfulDayConvolutionMonoidalCategoryStruct
  公理与运算 (12 个):
    - ι((C V D)) : D ⥤ C ⥤ V
    - convolutionExtensionUnit((C) (V) (d d' : D)) : ι.obj d ⊠ ι.obj d' ⟶ tensor C ⋙ ι.obj (d otimes d')
    - isPointwiseLeftKanExtensionConvolutionExtensionUnit((d d' : D)) : (函子.LeftExtension.mk _ <| convolutionExtensionUnit d d').IsPointwiseLeftKanExtension
    - unitUnit((C) (V) (D)) : 𝟙_ V ⟶ (ι.obj <| 𝟙_ D).obj (𝟙_ C)
    - isPointwiseLeftKanExtensionUnitUnit((C) (V) (D)) : 函子.LeftExtension.mk _ ({ app _ := unitUnit } : 函子.fromPUnit.{0} (𝟙_ V) ⟶ 函子.fromPUnit.{0} (𝟙_ C) ⋙ (ι.obj <| 𝟙_ D)) |>.IsPointwiseLeftKanExtension
    - faithful_ι : ι.忠实  [默认: by infer_instance]
    - convolutionExtensionUnit_comp_ι_map_tensorHom_app((C) (V) {d₁ d₂ d₁' d₂' : D} (f₁ : d₁ ⟶ d₁') (f₂ : d₂ ⟶ d₂') (x y : C)) : (convolutionExtensionUnit d₁ d₂).app (x, y) ≫ (ι.map (f₁ otimesₘ f₂)).app (x otimes y) = ((ι.map f₁).app x otimesₘ (ι.map f₂).app y) ≫ (convolutionExtensionUnit d₁' d₂').app (x, y)
    - convolutionExtensionUnit_comp_ι_map_whiskerLeft_app((V) (d₁ : D) {d₂ d₂' : D} (f₂ : d₂ ⟶ d₂') (x y : C)) : (convolutionExtensionUnit d₁ d₂).app (x, y) ≫ (ι.map (d₁ ◁ f₂)).app (x otimes y) = ((ι.obj d₁).obj x ◁ (ι.map f₂).app y) ≫ (convolutionExtensionUnit d₁ d₂').app (x, y)
    - convolutionExtensionUnit_comp_ι_map_whiskerRight_app((C) (V) {d₁ d₁' : D} (f₁ : d₁ ⟶ d₁') (d₂ : D) (x y : C)) : (convolutionExtensionUnit d₁ d₂).app (x, y) ≫ (ι.map (f₁ ▷ d₂)).app (x otimes y) = ((ι.map f₁).app x ▷ (ι.obj d₂).obj y) ≫ (convolutionExtensionUnit d₁' d₂).app (x, y)
    - associator_hom_unit_unit((V) (d d' d'' : D) (x y z : C)) : (convolutionExtensionUnit d d').app (x, y) ▷ (ι.obj d'').obj z ≫ (convolutionExtensionUnit (d otimes d') d'').app (x otimes y, z) ≫ (ι.map (α_ d d' d'').hom).app ((x otimes y) otimes z) = (α_ _ _ _).hom ≫ ((ι.obj d).obj x ◁ (convolutionExtensionUnit d' d'').app (y, z)) ≫ (convolutionExtensionUnit d (d' otimes d'')).app (x, y otimes z) ≫ (ι.obj (d otimes d' otimes d'')).map (α_ _ _ _).inv
    - leftUnitor_hom_unit_app((V) (d : D) (y : C)) : unitUnit ▷ (ι.obj d).obj y ≫ (convolutionExtensionUnit (𝟙_ D) d).app (𝟙_ C, y) ≫ (ι.map (fun_ d).hom).app (𝟙_ C otimes y) = (fun_ ((ι.obj d).obj y)).hom ≫ (ι.obj d).map (fun_ y).inv
    - rightUnitor_hom_unit_app((V) (d : D) (y : C)) : (ι.obj d).obj y ◁ unitUnit ≫ (convolutionExtensionUnit d (𝟙_ D)).app (y, 𝟙_ C) ≫ (ι.map (ρ_ d).hom).app (y otimes 𝟙_ C) = (ρ_ _).hom ≫ (ι.obj d).map (ρ_ y).inv

Depends on / 依赖: Functor, Functor.fromPUnit, fromPUnit, unitUnit
-/
class LawfulDayConvolutionMonoidalCategoryStruct
    (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    (D : Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D] where
  /-- a functor that interprets element of `D` as functors `C ⥤ V` -/
  ι (C V D) : D ⥤ C ⥤ V
  /-- a natural transformation `ι.obj d ⊠ ι.obj d' ⟶ tensor C ⋙ ι.obj (d ⊗ d')` -/
  convolutionExtensionUnit (C) (V) (d d' : D) :
    ι.obj d ⊠ ι.obj d' ⟶ tensor C ⋙ ι.obj (d otimes d')
  /-- `convolutionUnitUnit` exhibits `ι.obj (d ⊗ d')` as a left Ken extension of
  `ι.obj d ⊠ ι.obj d'` along `tensor C`. -/
  isPointwiseLeftKanExtensionConvolutionExtensionUnit (d d' : D) :
    (Functor.LeftExtension.mk _ <|
      convolutionExtensionUnit d d').IsPointwiseLeftKanExtension
  /-- a map `𝟙_ V ⟶ (ι.obj <| 𝟙_ D).obj (𝟙_ C)`, that we think of as defining a
  natural transformation
  `fromPUnit.{0} (𝟙_ V) ⟶ Functor.fromPUnit.{0} (𝟙_ C) ⋙ (ι.obj <| 𝟙_ D)`. -/
  unitUnit (C) (V) (D) : 𝟙_ V ⟶ (ι.obj <| 𝟙_ D).obj (𝟙_ C)
  /-- the natural transformation induced by `unitUnit` exhibits
  `(ι.obj <| 𝟙_ D).obj (𝟙_ C)` as a left Kan extension of `fromPUnit.{0} (𝟙_ V)` as a
  along `fromPUnit.{0} (𝟙_ C)`. -/
  isPointwiseLeftKanExtensionUnitUnit (C) (V) (D) :
    Functor.LeftExtension.mk _
      ({ app _ := unitUnit } : Functor.fromPUnit.{0} (𝟙_ V) ⟶
        Functor.fromPUnit.{0} (𝟙_ C) ⋙ (ι.obj <| 𝟙_ D)) |>.IsPointwiseLeftKanExtension
  /-- The field `ι` interprets an element of `D` as a functor `C ⥤ V`. -/
  faithful_ι : ι.Faithful := by infer_instance
  convolutionExtensionUnit_comp_ι_map_tensorHom_app (C) (V) {d₁ d₂ d₁' d₂' : D}
    (f₁ : d₁ ⟶ d₁') (f₂ : d₂ ⟶ d₂') (x y : C) :
    (convolutionExtensionUnit d₁ d₂).app (x, y) ≫
      (ι.map (f₁ otimesₘ f₂)).app (x otimes y) =
    ((ι.map f₁).app x otimesₘ (ι.map f₂).app y) ≫
      (convolutionExtensionUnit d₁' d₂').app (x, y)
  convolutionExtensionUnit_comp_ι_map_whiskerLeft_app (V)
    (d₁ : D) {d₂ d₂' : D}
    (f₂ : d₂ ⟶ d₂') (x y : C) :
    (convolutionExtensionUnit d₁ d₂).app (x, y) ≫
      (ι.map (d₁ ◁ f₂)).app (x otimes y) =
    ((ι.obj d₁).obj x ◁ (ι.map f₂).app y) ≫
      (convolutionExtensionUnit d₁ d₂').app (x, y)
  convolutionExtensionUnit_comp_ι_map_whiskerRight_app (C) (V)
    {d₁ d₁' : D} (f₁ : d₁ ⟶ d₁') (d₂ : D) (x y : C) :
    (convolutionExtensionUnit d₁ d₂).app (x, y) ≫
      (ι.map (f₁ ▷ d₂)).app (x otimes y) =
    ((ι.map f₁).app x ▷ (ι.obj d₂).obj y) ≫
      (convolutionExtensionUnit d₁' d₂).app (x, y)
  associator_hom_unit_unit (V) (d d' d'' : D) (x y z : C) :
    (convolutionExtensionUnit d d').app (x, y) ▷ (ι.obj d'').obj z ≫
      (convolutionExtensionUnit (d otimes d') d'').app (x otimes y, z) ≫
      (ι.map (α_ d d' d'').hom).app ((x otimes y) otimes z) =
    (α_ _ _ _).hom ≫
      ((ι.obj d).obj x ◁ (convolutionExtensionUnit d' d'').app (y, z)) ≫
      (convolutionExtensionUnit d (d' otimes d'')).app (x, y otimes z) ≫
      (ι.obj (d otimes d' otimes d'')).map (α_ _ _ _).inv
  leftUnitor_hom_unit_app (V) (d : D) (y : C) :
    unitUnit ▷ (ι.obj d).obj y ≫
      (convolutionExtensionUnit (𝟙_ D) d).app
        (𝟙_ C, y) ≫
      (ι.map (fun_ d).hom).app (𝟙_ C otimes y) =
    (fun_ ((ι.obj d).obj y)).hom ≫ (ι.obj d).map (fun_ y).inv
  rightUnitor_hom_unit_app (V) (d : D) (y : C) :
    (ι.obj d).obj y ◁ unitUnit ≫
      (convolutionExtensionUnit d (𝟙_ D)).app (y, 𝟙_ C) ≫
      (ι.map (ρ_ d).hom).app (y otimes 𝟙_ C) =
    (ρ_ _).hom ≫ (ι.obj d).map (ρ_ y).inv

namespace LawfulDayConvolutionMonoidalCategoryStruct

attribute [instance] faithful_ι

variable (D : Type u₃) [Category.{v₃} D] [MonoidalCategoryStruct D]
  [LawfulDayConvolutionMonoidalCategoryStruct C V D]

open scoped DayConvolution

/-- In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj (d ⊗ d')` is a
Day convolution of `(ι C V).obj d` and `(ι C V).d'`. -/
@[instance_reducible]
/--
Definition of `convolution` / `convolution` 的定义

English:
definition convolution
  signature: (d d' : D)
  body: (ι C V D).obj (d otimes d')
  unit := convolutionExtensionUnit C V d d'
  isPointwiseLeftKanExtensionUnit :=
    isPointwiseLeftKanExtensionConvolutionExtensionUnit d d'

中文:
定义 convolution
  签名: (d d' : D)
  定义体: (ι C V D).obj (d otimes d')
  unit := convolutionExtensionUnit C V d d'
  isPointwiseLeftKanExtensionUnit :=
    isPointwiseLeftKanExtensionConvolutionExtensionUnit d d'

Depends on / 依赖: otimes
-/
def convolution (d d' : D) :
    DayConvolution (ι C V D |>.obj d) (ι C V D |>.obj d') where
  convolution := (ι C V D).obj (d otimes d')
  unit := convolutionExtensionUnit C V d d'
  isPointwiseLeftKanExtensionUnit :=
    isPointwiseLeftKanExtensionConvolutionExtensionUnit d d'

attribute [local instance] convolution

/-- In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj (d ⊗ d' ⊗ d'')`
is a (triple) Day convolution of `(ι C V).obj d`, `(ι C V).obj d'` and
`(ι C V).obj d''`. -/
@[instance_reducible]
/--
Definition of `convolution₂` / `convolution₂` 的定义

English:
definition convolution₂
  signature: (d d' d'' : D)
  body: convolution C V D _ _

中文:
定义 convolution₂
  签名: (d d' d'' : D)
  定义体: convolution C V D _ _

Depends on / 依赖: convolution
-/
def convolution₂ (d d' d'' : D) :
    DayConvolution (ι C V D |>.obj d) ((ι C V D |>.obj d') ⊛ (ι C V D |>.obj d'')) :=
  convolution C V D _ _

/-- In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj ((d ⊗ d') ⊗ d'')`
is a (triple) Day convolution of `(ι C V).obj d`, `(ι C V).obj d'` and
`(ι C V).obj d''`. -/
@[instance_reducible]
/--
Definition of `convolution₂'` / `convolution₂'` 的定义

English:
definition convolution₂'
  signature: (d d' d'' : D)
  body: convolution C V D _ _

中文:
定义 convolution₂'
  签名: (d d' d'' : D)
  定义体: convolution C V D _ _

Depends on / 依赖: convolution
-/
def convolution₂' (d d' d'' : D) :
    DayConvolution ((ι C V D |>.obj d) ⊛ (ι C V D |>.obj d')) (ι C V D |>.obj d'') :=
  convolution C V D _ _

attribute [local instance] convolution₂ convolution₂'

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ι_map_tensorHom_hom_eq_tensorHom` / 引理 `ι_map_tensorHom_hom_eq_tensorHom`

English:
lemma ι_map_tensorHom_hom_eq_tensorHom
  proof: by
  apply DayConvolution.corepresentableBy
.homEquiv.injective (ι C V D |>.obj d₁) (ι C V D |>.obj d₁')
  dsimp
  ext ⟨x, y⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
    DayConvolution.corepresentableBy_homEquiv_apply_app,
    DayConvolution.unit_app_map_app]
  e

中文:
引理 ι_map_tensorHom_hom_eq_tensorHom
  证明: by
  apply DayConvolution.corepresentableBy
.homEquiv.injective (ι C V D |>.obj d₁) (ι C V D |>.obj d₁')
  dsimp
  ext ⟨x, y⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
    DayConvolution.corepresentableBy_homEquiv_apply_app,
    DayConvolution.unit_app_map_app]
  e

Depends on / 依赖: D.hom, D.pullHom_hom, DayConvolution, DayConvolution.corepresentableBy, DayConvolution.corepresentableBy_homEquiv_apply_app, DayConvolution.unit_app_map_app, Functor, Functor.comp_obj, _eq_pullHom, cat_disch, comp_obj, corepresentableBy, corepresentableBy_homEquiv_apply_app, exists_lift, externalProductBifunctor_obj_obj, homEquiv, homEquiv.injective, injective, isPullback, isPullback.exists_lift
-/
lemma ι_map_tensorHom_hom_eq_tensorHom
    {d₁ d₂ : D} {d₁' d₂' : D}
    (f : d₁ ⟶ d₂) (f' : d₁' ⟶ d₂') :
    (ι C V D).map (f otimesₘ f') =
    DayConvolution.map (ι C V D |>.map f) (ι C V D |>.map f') := by
  apply DayConvolution.corepresentableBy
.homEquiv.injective (ι C V D |>.obj d₁) (ι C V D |>.obj d₁')
  dsimp
  ext ⟨x, y⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
    DayConvolution.corepresentableBy_homEquiv_apply_app,
    DayConvolution.unit_app_map_app]
  exact convolutionExtensionUnit_comp_ι_map_tensorHom_app C V _ _ _ _

set_option backward.isDefEq.respectTransparency false in
open DayConvolution in
/--
lemma `ι_map_associator_hom_eq_associator_hom` / 引理 `ι_map_associator_hom_eq_associator_hom`

English:
lemma ι_map_associator_hom_eq_associator_hom
  statement: (d d' d'')
  proof: by
  apply corepresentableBy₂'
.homEquiv.injective (ι C V D |>.obj d) (ι C V D |>.obj d') (ι C V D |>.obj d'')
  dsimp
  ext ⟨⟨x, y⟩, z⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, Functor.prod_obj,
    tensor_obj, Functor.id_obj, Functor.homEquivOfIsLeftKanExtension_apply_app,


中文:
引理 ι_map_associator_hom_eq_associator_hom
  结论: (d d' d'')
  证明: by
  apply corepresentableBy₂'
.homEquiv.injective (ι C V D |>.obj d) (ι C V D |>.obj d') (ι C V D |>.obj d'')
  dsimp
  ext ⟨⟨x, y⟩, z⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, Functor.prod_obj,
    tensor_obj, Functor.id_obj, Functor.homEquivOfIsLeftKanExtension_apply_app,


Depends on / 依赖: Category, Category.comp_id, DayConvolution, DayConvolution.associator_hom_unit_unit, Functor, Functor.comp_obj, Functor.homEquivOfIsLeftKanExtension_apply_app, Functor.id_obj, Functor.leftUnitor_inv_app, Functor.prod_obj, associator_hom_unit_unit, comp_id, comp_obj, corepresentableBy_homEquiv_apply_app, externalProductBifunctor_map_app, externalProductBifunctor_obj_obj, homEquiv, homEquiv.injective, homEquivOfIsLeftKanExtension_apply_app, id_obj
-/
lemma ι_map_associator_hom_eq_associator_hom (d d' d'')
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)] :
    (ι C V D).map (α_ d d' d'').hom =
    (DayConvolution.associator
      (ι C V D |>.obj d) (ι C V D |>.obj d') (ι C V D |>.obj d'')).hom := by
  apply corepresentableBy₂'
.homEquiv.injective (ι C V D |>.obj d) (ι C V D |>.obj d') (ι C V D |>.obj d'')
  dsimp
  ext ⟨⟨x, y⟩, z⟩
  simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, Functor.prod_obj,
    tensor_obj, Functor.id_obj, Functor.homEquivOfIsLeftKanExtension_apply_app,
    externalProductBifunctor_map_app, Functor.leftUnitor_inv_app, whiskerLeft_id,
    Category.comp_id, corepresentableBy_homEquiv_apply_app,
    DayConvolution.associator_hom_unit_unit]
  exact associator_hom_unit_unit V _ _ _ _ _ _

/-- In a `LawfulDayConvolutionMonoidalCategoryStruct`, `ι.obj (𝟙_ D)`
is a Day convolution unit. -/
@[instance_reducible]
/--
Definition of `convolutionUnit` / `convolutionUnit` 的定义

English:
definition convolutionUnit
  signature: : DayConvolutionUnit (ι C V D |>.obj <| 𝟙_ D) where
  body: unitUnit _ _ _
  isPointwiseLeftKanExtensionCan := isPointwiseLeftKanExtensionUnitUnit _ _ _

中文:
定义 convolutionUnit
  签名: : DayConvolutionUnit (ι C V D |>.obj <| 𝟙_ D) where
  定义体: unitUnit _ _ _
  isPointwiseLeftKanExtensionCan := isPointwiseLeftKanExtensionUnitUnit _ _ _

Depends on / 依赖: unitUnit
-/
def convolutionUnit : DayConvolutionUnit (ι C V D |>.obj <| 𝟙_ D) where
  can := unitUnit _ _ _
  isPointwiseLeftKanExtensionCan := isPointwiseLeftKanExtensionUnitUnit _ _ _

attribute [local instance] convolutionUnit

set_option backward.isDefEq.respectTransparency false in
open DayConvolutionUnit in
/--
lemma `ι_map_leftUnitor_hom_eq_leftUnitor_hom` / 引理 `ι_map_leftUnitor_hom_eq_leftUnitor_hom`

English:
lemma ι_map_leftUnitor_hom_eq_leftUnitor_hom
  statement: (d : D)
  proof: by
  apply corepresentableByLeft
.homEquiv.injective (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d)
  dsimp
  ext ⟨_, x⟩
  dsimp [corepresentableByLeft]
  simp only [whiskerLeft_id, Category.comp_id,
    DayConvolutionUnit.leftUnitor_hom_unit_app]
  exact leftUnitor_hom_unit_app V d x

中文:
引理 ι_map_leftUnitor_hom_eq_leftUnitor_hom
  结论: (d : D)
  证明: by
  apply corepresentableByLeft
.homEquiv.injective (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d)
  dsimp
  ext ⟨_, x⟩
  dsimp [corepresentableByLeft]
  simp only [whiskerLeft_id, Category.comp_id,
    DayConvolutionUnit.leftUnitor_hom_unit_app]
  exact leftUnitor_hom_unit_app V d x

Depends on / 依赖: Category, Category.comp_id, DayConvolutionUnit, DayConvolutionUnit.leftUnitor_hom_unit_app, comp_id, corepresentableByLeft, homEquiv, homEquiv.injective, injective, leftUnitor_hom_unit_app, whiskerLeft_id
-/
lemma ι_map_leftUnitor_hom_eq_leftUnitor_hom (d : D)
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)] :
    (ι C V D).map (fun_ d).hom =
    (DayConvolutionUnit.leftUnitor
      (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d)).hom := by
  apply corepresentableByLeft
.homEquiv.injective (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d)
  dsimp
  ext ⟨_, x⟩
  dsimp [corepresentableByLeft]
  simp only [whiskerLeft_id, Category.comp_id,
    DayConvolutionUnit.leftUnitor_hom_unit_app]
  exact leftUnitor_hom_unit_app V d x

set_option backward.isDefEq.respectTransparency false in
open DayConvolutionUnit in
/--
lemma `ι_map_rightUnitor_hom_eq_rightUnitor_hom` / 引理 `ι_map_rightUnitor_hom_eq_rightUnitor_hom`

English:
lemma ι_map_rightUnitor_hom_eq_rightUnitor_hom
  statement: (d : D)
  proof: by
  apply corepresentableByRight
.homEquiv.injective (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d)
  dsimp
  ext ⟨x, _⟩
  dsimp [corepresentableByRight]
  simp only [id_whiskerRight, Category.id_comp,
    DayConvolutionUnit.rightUnitor_hom_unit_app]
  exact rightUnitor_hom_unit_app V d x

中文:
引理 ι_map_rightUnitor_hom_eq_rightUnitor_hom
  结论: (d : D)
  证明: by
  apply corepresentableByRight
.homEquiv.injective (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d)
  dsimp
  ext ⟨x, _⟩
  dsimp [corepresentableByRight]
  simp only [id_whiskerRight, Category.id_comp,
    DayConvolutionUnit.rightUnitor_hom_unit_app]
  exact rightUnitor_hom_unit_app V d x

Depends on / 依赖: Category, Category.id_comp, DayConvolutionUnit, DayConvolutionUnit.rightUnitor_hom_unit_app, corepresentableByRight, homEquiv, homEquiv.injective, id_comp, id_whiskerRight, injective, rightUnitor_hom_unit_app
-/
lemma ι_map_rightUnitor_hom_eq_rightUnitor_hom (d : D)
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)] :
    (ι C V D).map (ρ_ d).hom =
    (DayConvolutionUnit.rightUnitor
      (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d)).hom := by
  apply corepresentableByRight
.homEquiv.injective (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.obj d)
  dsimp
  ext ⟨x, _⟩
  dsimp [corepresentableByRight]
  simp only [id_whiskerRight, Category.id_comp,
    DayConvolutionUnit.rightUnitor_hom_unit_app]
  exact rightUnitor_hom_unit_app V d x

end LawfulDayConvolutionMonoidalCategoryStruct

set_option backward.isDefEq.respectTransparency false in
open LawfulDayConvolutionMonoidalCategoryStruct in
attribute [local instance] convolution convolution₂ convolution₂' convolutionUnit in
open DayConvolution DayConvolutionUnit in
/-- We can promote a `LawfulDayConvolutionMonoidalCategoryStruct` to a monoidal category,
note that every non-prop data is already here, so this is just about showing that they
satisfy the axioms of a monoidal category. -/
@[instance_reducible]
/--
Definition of `monoidalOfLawfulDayConvolutionMonoidalCategoryStruct` / `monoidalOfLawfulDayConvolutionMonoidalCategoryStruct` 的定义

English:
definition monoidalOfLawfulDayConvolutionMonoidalCategoryStruct
  body: MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun x y => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [ι_map_tensorHom_hom_eq_tensorHom, Functor.map_id]
      apply (DayConvolution.corepresentableBy
        (ι C V D |>.obj _) (ι C V D |>.obj _)).homEquiv.inject

中文:
定义 monoidalOfLawfulDayConvolutionMonoidalCategoryStruct
  定义体: MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun x y => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [ι_map_tensorHom_hom_eq_tensorHom, Functor.map_id]
      apply (DayConvolution.corepresentableBy
        (ι C V D |>.obj _) (ι C V D |>.obj _)).homEquiv.inject

Depends on / 依赖: Category, Category.id_comp, DayConvolution, DayConvolution.corepresentableBy, Faithful, Functor, Functor.Faithful.map_injective, Functor.comp_obj, Functor.map_id, MonoidalCategory, MonoidalCategory.ofTensorHom, NatTrans, NatTrans.id_app, comp_obj, corepresentableBy, corepresentableBy_homEquiv_apply_app, externalProductBifunctor_obj_obj, homEquiv, homEquiv.injective, id_app
-/
def monoidalOfLawfulDayConvolutionMonoidalCategoryStruct
    (D : Type u₃) [Category.{v₃} D]
    [MonoidalCategoryStruct D]
    [LawfulDayConvolutionMonoidalCategoryStruct C V D]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [forall (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d)
        (tensorRight v)]
    [forall (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)] :
    MonoidalCategory D :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun x y => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [ι_map_tensorHom_hom_eq_tensorHom, Functor.map_id]
      apply (DayConvolution.corepresentableBy
        (ι C V D |>.obj _) (ι C V D |>.obj _)).homEquiv.injective
      dsimp
      ext ⟨_, _⟩
      simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj,
        corepresentableBy_homEquiv_apply_app, unit_app_map_app, NatTrans.id_app,
        tensorHom_id, id_whiskerRight, Category.id_comp]
      dsimp [DayConvolution.convolution]
      simp)
    (tensorHom_comp_tensorHom := fun _ _ _ _ => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [ι_map_tensorHom_hom_eq_tensorHom, Functor.map_comp]
      apply (corepresentableBy (ι C V D |>.obj _) (ι C V D |>.obj _)).homEquiv.injective
      dsimp
      ext ⟨_, _⟩
      simp)
    (id_tensorHom := fun x {y₁ y₂} f => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [ι_map_tensorHom_hom_eq_tensorHom]
      apply (corepresentableBy (ι C V D |>.obj _) (ι C V D |>.obj _)).homEquiv.injective
      dsimp
      ext ⟨x, y⟩
      dsimp
      simp only [Functor.map_id, unit_app_map_app, Functor.comp_obj, tensor_obj,
        NatTrans.id_app, id_tensorHom]
      dsimp [unit]
      rw [convolutionExtensionUnit_comp_ι_map_whiskerLeft_app])
    (tensorHom_id := fun x {y₁ y₂} f => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [ι_map_tensorHom_hom_eq_tensorHom]
      apply (corepresentableBy (ι C V D |>.obj _) (ι C V D |>.obj _)).homEquiv.injective
      dsimp
      ext ⟨x, y⟩
      dsimp
      simp only [Functor.map_id, DayConvolution.unit_app_map_app, Functor.comp_obj,
        tensor_obj, NatTrans.id_app, tensorHom_id]
      dsimp [DayConvolution.unit]
      rw [convolutionExtensionUnit_comp_ι_map_whiskerRight_app])
    (associator_naturality := fun f₁ f₂ f₃ => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [Functor.map_comp, ι_map_associator_hom_eq_associator_hom,
        ι_map_tensorHom_hom_eq_tensorHom]
      exact DayConvolution.associator_naturality
        ((ι C V D).map f₁) ((ι C V D).map f₂) ((ι C V D).map f₃))
    (leftUnitor_naturality := fun f => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [Functor.map_comp, ι_map_tensorHom_hom_eq_tensorHom, Functor.map_id]
      rw [ι_map_leftUnitor_hom_eq_leftUnitor_hom]; rw [ι_map_leftUnitor_hom_eq_leftUnitor_hom]
      exact DayConvolutionUnit.leftUnitor_naturality
        (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.map f))
    (rightUnitor_naturality := fun f => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [Functor.map_comp, ι_map_tensorHom_hom_eq_tensorHom, Functor.map_id]
      rw [ι_map_rightUnitor_hom_eq_rightUnitor_hom]; rw [ι_map_rightUnitor_hom_eq_rightUnitor_hom]
      exact DayConvolutionUnit.rightUnitor_naturality
        (ι C V D |>.obj <| 𝟙_ D) (ι C V D |>.map f))
    (pentagon := fun a b c d => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [Functor.map_comp, Functor.map_id, ι_map_tensorHom_hom_eq_tensorHom,
        ι_map_associator_hom_eq_associator_hom]
      -- this is a bit painful...
      let : DayConvolution
          (((ι C V D |>.obj a) ⊛ (ι C V D |>.obj b)) ⊛ (ι C V D |>.obj c))
          (ι C V D |>.obj d) :=
        convolution C V D _ _
      let : DayConvolution
          ((ι C V D |>.obj a) ⊛ (ι C V D |>.obj b))
          ((ι C V D |>.obj c) ⊛ (ι C V D |>.obj d)) :=
        convolution C V D _ _
      let : DayConvolution
          ((ι C V D |>.obj a) ⊛ ((ι C V D |>.obj b) ⊛ (ι C V D |>.obj c)))
          (ι C V D |>.obj d) :=
        convolution C V D _ _
      let : DayConvolution
          (ι C V D |>.obj a)
          ((ι C V D |>.obj b) ⊛ ((ι C V D |>.obj c) ⊛ (ι C V D |>.obj d))) :=
        convolution C V D _ _
      let : DayConvolution
          (ι C V D |>.obj a)
          (((ι C V D |>.obj b) ⊛ (ι C V D |>.obj c)) ⊛ (ι C V D |>.obj d)) :=
        convolution C V D _ _
      exact DayConvolution.pentagon
        (ι C V D |>.obj a) (ι C V D |>.obj b) (ι C V D |>.obj c) (ι C V D |>.obj d))
    (triangle := fun a b => by
      apply Functor.Faithful.map_injective (F := ι C V D)
      simp only [Functor.map_comp, Functor.map_id, ι_map_tensorHom_hom_eq_tensorHom,
        ι_map_associator_hom_eq_associator_hom, ι_map_leftUnitor_hom_eq_leftUnitor_hom,
        ι_map_rightUnitor_hom_eq_rightUnitor_hom]
      exact DayConvolution.triangle
        (ι C V D |>.obj a) (ι C V D |>.obj b) (ι C V D |>.obj <| 𝟙_ D))

/-! In what follows, we give a constructor for `LawfulDayConvolutionMonoidalCategoryStruct`
that does not assume a pre-existing `MonoidalCategoryStruct` and builds one from
the data of suitable convolutions, while giving definitional control over
as many parameters as we can. -/

/--
Definition of `InducedLawfulDayConvolutionMonoidalCategoryStructCore` / `InducedLawfulDayConvolutionMonoidalCategoryStructCore` 的定义

English:
class InducedLawfulDayConvolutionMonoidalCategoryStructCore
  axioms and operations (8):
    - ι((C V D)) : D ⥤ C ⥤ V
    - fullyFaithulι : ι.FullyFaithful
    - tensorObj((C) (V)) : D -> D -> D
    - convolutions' : forall (d d' : D), DayConvolution (ι.obj d) (ι.obj d')
    - tensorObjIsoConvolution((C) (V)) : forall (d d' : D), ι.obj (tensorObj d d') ≅ (convolutions' d d').convolution
    - convolutionUnitApp((V)) : forall (d d' : D) (x y : C), (ι.obj d).obj x otimes (ι.obj d').obj y ⟶ (ι.obj (tensorObj d d')).obj (x otimes y)  [default: fun d d' x y => (convolutions' d d').unit.app (x, y) ≫ (tens]
    - convolutionUnitApp_eq((V)) : forall (d d' : D) (x y : C), convolutionUnitApp d d' x y = (convolutions' d d').unit.app (x, y) ≫ (tensorObjIsoConvolution d d').inv.app (x otimes y)  [default: by cat_disch]
    - tensorHom : forall {d₁ d₂ : D} {d₁' d₂' : D}, (d₁ ⟶ d₂) -> (d₁' ⟶ d₂') -> (tensorObj d₁ d₁' ⟶ tensorObj d₂ d₂')

中文:
类 InducedLawfulDayConvolutionMonoidalCategoryStructCore
  公理与运算 (8 个):
    - ι((C V D)) : D ⥤ C ⥤ V
    - fullyFaithulι : ι.满忠实
    - tensorObj((C) (V)) : D -> D -> D
    - convolutions' : 对任意 (d d' : D), Day卷积 (ι.obj d) (ι.obj d')
    - tensorObjIsoConvolution((C) (V)) : 对任意 (d d' : D), ι.obj (tensorObj d d') ≅ (convolutions' d d').convolution
    - convolutionUnitApp((V)) : 对任意 (d d' : D) (x y : C), (ι.obj d).obj x otimes (ι.obj d').obj y ⟶ (ι.obj (tensorObj d d')).obj (x otimes y)  [默认: fun d d' x y => (convolutions' d d').unit.app (x, y) ≫ (tens]
    - convolutionUnitApp_eq((V)) : 对任意 (d d' : D) (x y : C), convolutionUnitApp d d' x y = (convolutions' d d').unit.app (x, y) ≫ (tensorObjIsoConvolution d d').inv.app (x otimes y)  [默认: by cat_disch]
    - tensorHom : 对任意 {d₁ d₂ : D} {d₁' d₂' : D}, (d₁ ⟶ d₂) -> (d₁' ⟶ d₂') -> (tensorObj d₁ d₁' ⟶ tensorObj d₂ d₂')

Depends on / 依赖: convolutions, inv.app, otimes, tensorObjIsoConvolution, unit.app
-/
class InducedLawfulDayConvolutionMonoidalCategoryStructCore
    (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    (D : Type u₃) [Category.{v₃} D] where
  /-- A functor that interprets elements of `D` as functors `C ⥤ V`. -/
  ι (C V D) : D ⥤ C ⥤ V
  /-- The functor `ι` is fully faithful. -/
  fullyFaithulι : ι.FullyFaithful
  /-- Candidate function for the tensor product of objects. -/
  tensorObj (C) (V) : D -> D -> D
  /-- First candidate Day convolutions between objects.
  Note that the name here is primed as in fact, we will use the other fields
  in this class to produce convolutions with more controlled defeq properties. -/
  convolutions' : forall (d d' : D), DayConvolution (ι.obj d) (ι.obj d')
  /-- Isomorphisms that exhibits the essential image of `ι` as closed under day
  convolution. -/
  tensorObjIsoConvolution (C) (V) : forall (d d' : D),
    ι.obj (tensorObj d d') ≅ (convolutions' d d').convolution
  /-- Candidate component of units for the `LawfulDayConvolutionMonoidalCategoryStruct`,
  this defaults to the ones deduced by `convolutions'` and `tensorObjIsoConvolution`. -/
  convolutionUnitApp (V) :
      forall (d d' : D) (x y : C),
        (ι.obj d).obj x otimes (ι.obj d').obj y ⟶ (ι.obj (tensorObj d d')).obj (x otimes y) :=
    fun d d' x y =>
      (convolutions' d d').unit.app (x, y) ≫
        (tensorObjIsoConvolution d d').inv.app (x otimes y)
  /-- Lawfulness of `convolutionUnitApp`. -/
  convolutionUnitApp_eq (V) :
      forall (d d' : D) (x y : C),
        convolutionUnitApp d d' x y =
        (convolutions' d d').unit.app (x, y) ≫
          (tensorObjIsoConvolution d d').inv.app (x otimes y) := by
    cat_disch
  /-- Candidate `tensorHom`. This defaults to the one that corresponds to
  `DayConvolution.map` through `convolutions'`. -/
  tensorHom :
      forall {d₁ d₂ : D} {d₁' d₂' : D},
        (d₁ ⟶ d₂) -> (d₁' ⟶ d₂') -> (tensorObj d₁ d₁' ⟶ tensorObj d₂ d₂') :=
fun {d₁ d₂} {d₁' d₂' : D} f f' => fullyFaithulι.preimage
      (tensorObjIsoConvolution d₁ d₁').hom ≫
        (DayConvolution.map (ι.map f) (ι.map f')) ≫ (tensorObjIsoConvolution d₂ d₂').inv
  /-- Lawfulness of `tensorHom`. -/
  tensorHom_eq :
      forall {d₁ d₂ : D} {d₁' d₂' : D} (f : d₁ ⟶ d₂) (f' : d₁' ⟶ d₂'),
        ι.map (tensorHom f f') = (tensorObjIsoConvolution d₁ d₁').hom ≫
          (DayConvolution.map (ι.map f) (ι.map f')) ≫
          (tensorObjIsoConvolution d₂ d₂').inv := by
    cat_disch
  /-- Candidate tensor unit. -/
  tensorUnit (C) (V) (D) : D
  /-- DayConvolutionUnit structure on the candidate. -/
  tensorUnitConvolutionUnit : DayConvolutionUnit (ι.obj tensorUnit)

namespace InducedLawfulDayConvolutionMonoidalCategoryStructCore

attribute [instance_reducible, local instance] tensorUnitConvolutionUnit

section

variable (D : Type u₃) [Category.{v₃} D]
    [InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D]

set_option backward.isDefEq.respectTransparency false in
variable {D} in
/-- With the data of chosen isomorphic objects to given day convolutions,
and provably equal unit maps through these isomorphisms,
we can transform a given family of Day convolutions to one with
convolutions definitionally equals to the given objects, and component of units
definitionally equal to the provided map family. -/
@[instance_reducible]
/--
Definition of `convolutions` / `convolutions` 的定义

English:
definition convolutions
  signature: (d d' : D)
  body: (ι C V D).obj (tensorObj C V d d')
  unit :=
    { app x := convolutionUnitApp V d d' x.1 x.2
      naturality := by
        intros
        simp only [convolutionUnitApp_eq, Category.assoc, NatTrans.naturality_assoc]
        simp }
  isPointwiseLeftKanExtensionUnit :=
    Functor.LeftExtension.isPoi

中文:
定义 convolutions
  签名: (d d' : D)
  定义体: (ι C V D).obj (tensorObj C V d d')
  unit :=
    { app x := convolutionUnitApp V d d' x.1 x.2
      naturality := by
        intros
        simp only [convolutionUnitApp_eq, Category.assoc, NatTrans.naturality_assoc]
        simp }
  isPointwiseLeftKanExtensionUnit :=
    Functor.LeftExtension.isPoi

Depends on / 依赖: tensorObj
-/
def convolutions (d d' : D) :
    DayConvolution ((ι C V D).obj d) ((ι C V D).obj d') where
  convolution := (ι C V D).obj (tensorObj C V d d')
  unit :=
    { app x := convolutionUnitApp V d d' x.1 x.2
      naturality := by
        intros
        simp only [convolutionUnitApp_eq, Category.assoc, NatTrans.naturality_assoc]
        simp }
  isPointwiseLeftKanExtensionUnit :=
    Functor.LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
      (StructuredArrow.isoMk
        (tensorObjIsoConvolution C V d d').symm
        (by
          ext ⟨x, y⟩
          simp [convolutionUnitApp_eq V d d' x y]))
      (convolutions' d d' |>.isPointwiseLeftKanExtensionUnit)

attribute [local instance] convolutions

variable
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]

open scoped DayConvolution

/--
Definition of `mkMonoidalCategoryStruct` / `mkMonoidalCategoryStruct` 的定义

English:
abbreviation mkMonoidalCategoryStruct
  signature: : MonoidalCategoryStruct D where
  body: tensorObj C V
  tensorHom := tensorHom
  tensorUnit := tensorUnit C V D
  whiskerLeft x {_ _} f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)
  associator x y z :=
    -- To make this work we use the better instance `convolutions`
    letI : DayConvolution (ι C V D |>.obj x) ((ι C V D

中文:
缩写 mkMonoidalCategoryStruct
  签名: : 幺半群范畴结构 D where
  定义体: tensorObj C V
  tensorHom := tensorHom
  tensorUnit := tensorUnit C V D
  whiskerLeft x {_ _} f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)
  associator x y z :=
    -- To make this work we use the better instance `convolutions`
    letI : DayConvolution (ι C V D |>.obj x) ((ι C V D

Depends on / 依赖: tensorObj
-/
abbrev mkMonoidalCategoryStruct : MonoidalCategoryStruct D where
  tensorObj := tensorObj C V
  tensorHom := tensorHom
  tensorUnit := tensorUnit C V D
  whiskerLeft x {_ _} f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)
  associator x y z :=
    -- To make this work we use the better instance `convolutions`
    letI : DayConvolution (ι C V D |>.obj x) ((ι C V D |>.obj y) ⊛ (ι C V D |>.obj z)) :=
      convolutions C V _ _
    letI : DayConvolution ((ι C V D |>.obj x) ⊛ (ι C V D |>.obj y)) (ι C V D |>.obj z) :=
      convolutions C V _ _
fullyFaithulι.preimageIso
      DayConvolution.associator (ι C V D |>.obj x) (ι C V D |>.obj y) (ι C V D |>.obj z)
  leftUnitor x :=
    letI : DayConvolution (ι C V D |>.obj <| tensorUnit C V D) (ι C V D |>.obj x) :=
      convolutions C V _ _
fullyFaithulι.preimageIso
      DayConvolutionUnit.leftUnitor (ι C V D |>.obj <| tensorUnit C V D) (ι C V D |>.obj x)
  rightUnitor x :=
    letI : DayConvolution (ι C V D |>.obj x) (ι C V D |>.obj <| tensorUnit C V D) :=
      convolutions C V _ _
fullyFaithulι.preimageIso
      DayConvolutionUnit.rightUnitor (ι C V D |>.obj <| tensorUnit C V D) (ι C V D |>.obj x)

/--
lemma `id_tensorHom` / 引理 `id_tensorHom`

English:
lemma id_tensorHom
  given: (x : D) {y y' : D} (f : y ⟶ y')
  proof: mkMonoidalCategoryStruct C V D
    (𝟙 x) otimesₘ f = x ◁ f :=
  rfl

中文:
引理 id_tensorHom
  条件: (x : D) {y y' : D} (f : y ⟶ y')
  证明: mkMonoidalCategoryStruct C V D
    (𝟙 x) otimesₘ f = x ◁ f :=
  rfl

Depends on / 依赖: mkMonoidalCategoryStruct
-/
lemma id_tensorHom (x : D) {y y' : D} (f : y ⟶ y') :
    letI := mkMonoidalCategoryStruct C V D
    (𝟙 x) otimesₘ f = x ◁ f :=
  rfl

/--
lemma `tensorHom_id` / 引理 `tensorHom_id`

English:
lemma tensorHom_id
  given: {x x' : D} (f : x ⟶ x') (y : D)
  proof: mkMonoidalCategoryStruct C V D
    f otimesₘ (𝟙 y) = f ▷ y :=
  rfl

中文:
引理 tensorHom_id
  条件: {x x' : D} (f : x ⟶ x') (y : D)
  证明: mkMonoidalCategoryStruct C V D
    f otimesₘ (𝟙 y) = f ▷ y :=
  rfl

Depends on / 依赖: mkMonoidalCategoryStruct
-/
lemma tensorHom_id {x x' : D} (f : x ⟶ x') (y : D) :
    letI := mkMonoidalCategoryStruct C V D
    f otimesₘ (𝟙 y) = f ▷ y :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ι_map_tensorHom_eq` / 引理 `ι_map_tensorHom_eq`

English:
lemma ι_map_tensorHom_eq
  given: {d₁ d₁' d₂ d₂' : D} (f : d₁ ⟶ d₂) (f' : d₁' ⟶ d₂')
  proof: mkMonoidalCategoryStruct C V D
    (ι C V D).map (f otimesₘ f') =
    DayConvolution.map ((ι C V D).map f) ((ι C V D).map f') := by
  dsimp +instances [mkMonoidalCategoryStruct]
  rw [tensorHom_eq]
  apply (convolutions C V d₁ d₁').corepresentableBy.homEquiv.injective
  dsimp
  ext ⟨u₁, u₂⟩
  dsimp


中文:
引理 ι_map_tensorHom_eq
  条件: {d₁ d₁' d₂ d₂' : D} (f : d₁ ⟶ d₂) (f' : d₁' ⟶ d₂')
  证明: mkMonoidalCategoryStruct C V D
    (ι C V D).map (f otimesₘ f') =
    DayConvolution.map ((ι C V D).map f) ((ι C V D).map f') := by
  dsimp +instances [mkMonoidalCategoryStruct]
  rw [tensorHom_eq]
  apply (convolutions C V d₁ d₁').corepresentableBy.homEquiv.injective
  dsimp
  ext ⟨u₁, u₂⟩
  dsimp


Depends on / 依赖: mkMonoidalCategoryStruct
-/
lemma ι_map_tensorHom_eq {d₁ d₁' d₂ d₂' : D} (f : d₁ ⟶ d₂) (f' : d₁' ⟶ d₂') :
    letI := mkMonoidalCategoryStruct C V D
    (ι C V D).map (f otimesₘ f') =
    DayConvolution.map ((ι C V D).map f) ((ι C V D).map f') := by
  dsimp +instances [mkMonoidalCategoryStruct]
  rw [tensorHom_eq]
  apply (convolutions C V d₁ d₁').corepresentableBy.homEquiv.injective
  dsimp
  ext ⟨u₁, u₂⟩
  dsimp
  simp only [DayConvolution.unit_app_map_app, Functor.comp_obj, tensor_obj]
  simp +instances [convolutions, convolutionUnitApp_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The monoidal category struct constructed in `DayConvolution.mkMonoidalCategoryStruct` extends
to a `LawfulDayConvolutionMonoidalCategoryStruct`. -/
@[instance_reducible]
/--
Definition of `mkLawfulDayConvolutionMonoidalCategoryStruct` / `mkLawfulDayConvolutionMonoidalCategoryStruct` 的定义

English:
definition mkLawfulDayConvolutionMonoidalCategoryStruct
  signature: :
  body: mkMonoidalCategoryStruct C V D
    LawfulDayConvolutionMonoidalCategoryStruct C V D :=
  letI : MonoidalCategoryStruct D := mkMonoidalCategoryStruct C V D
  { ι := ι C V D
    faithful_ι := fullyFaithulι.faithful
    convolutionExtensionUnit d d' :=
      (convolutions C V d d').unit
    isPointwise

中文:
定义 mkLawfulDayConvolutionMonoidalCategoryStruct
  签名: :
  定义体: mkMonoidalCategoryStruct C V D
    LawfulDayConvolutionMonoidalCategoryStruct C V D :=
  letI : MonoidalCategoryStruct D := mkMonoidalCategoryStruct C V D
  { ι := ι C V D
    faithful_ι := fullyFaithulι.faithful
    convolutionExtensionUnit d d' :=
      (convolutions C V d d').unit
    isPointwise

Depends on / 依赖: mkMonoidalCategoryStruct
-/
def mkLawfulDayConvolutionMonoidalCategoryStruct :
    letI : MonoidalCategoryStruct D := mkMonoidalCategoryStruct C V D
    LawfulDayConvolutionMonoidalCategoryStruct C V D :=
  letI : MonoidalCategoryStruct D := mkMonoidalCategoryStruct C V D
  { ι := ι C V D
    faithful_ι := fullyFaithulι.faithful
    convolutionExtensionUnit d d' :=
      (convolutions C V d d').unit
    isPointwiseLeftKanExtensionConvolutionExtensionUnit d d' :=
      (convolutions C V d d').isPointwiseLeftKanExtensionUnit
    unitUnit := tensorUnitConvolutionUnit.can
    isPointwiseLeftKanExtensionUnitUnit :=
      tensorUnitConvolutionUnit.isPointwiseLeftKanExtensionCan
    convolutionExtensionUnit_comp_ι_map_tensorHom_app := by
      intros d₁ d₁' d₂ d₂' f f' x y
      simp [ι_map_tensorHom_eq C V D f f']
    convolutionExtensionUnit_comp_ι_map_whiskerLeft_app := by
      intros d₁ d₂ d₂' f x y
      simp [← id_tensorHom, ι_map_tensorHom_eq C V D]
    convolutionExtensionUnit_comp_ι_map_whiskerRight_app := by
      intros
      simp [← tensorHom_id, ι_map_tensorHom_eq C V D]
    associator_hom_unit_unit d₁ d₂ d₃ x₁ x₂ x₃ := by
      simp only [externalProductBifunctor_obj_obj, Functor.comp_obj, tensor_obj, associator,
        Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
      let : DayConvolution (ι C V D |>.obj d₁) ((ι C V D |>.obj d₂) ⊛ (ι C V D |>.obj d₃)) :=
        convolutions C V _ _
      let : DayConvolution ((ι C V D |>.obj d₁) ⊛ (ι C V D |>.obj d₂)) (ι C V D |>.obj d₃) :=
        convolutions C V _ _
      apply DayConvolution.associator_hom_unit_unit
    leftUnitor_hom_unit_app _ _ := by
      simp only [Functor.comp_obj, tensor_obj, leftUnitor,
        Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
      apply DayConvolutionUnit.leftUnitor_hom_unit_app
    rightUnitor_hom_unit_app _ _ := by
      simp only [Functor.comp_obj, tensor_obj, rightUnitor,
        Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
      apply DayConvolutionUnit.rightUnitor_hom_unit_app }

end

variable {C V} in
/-- Given a fully faithful functor `ι : D ⥤ C ⥤ V` and mere existence of Day convolutions of
`ι.obj d` and `ι.obj d'` such that the convolution remains in the essential image of `ι`,
construct an `InducedLawfulDayConvolutionMonoidalCategoryStructCore` by letting all other
data be the generic ones from the `HasPointwiseLeftKanExtension` API. -/
@[instance_reducible]
/--
Definition of `ofHasDayConvolutions` / `ofHasDayConvolutions` 的定义

English:
definition ofHasDayConvolutions
  body: ι
  fullyFaithulι := ffι
.witness tensorObj := fun d d' => essImageDayConvolution d d'
  convolutions' := fun d d' =>
    { convolution := (tensor C).pointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d')
      unit := (tensor C).pointwiseLeftKanExtensionUnit (ι.obj d ⊠ ι.obj d')
      isPointwiseLeftKanExt

中文:
定义 ofHasDayConvolutions
  定义体: ι
  fullyFaithulι := ffι
.witness tensorObj := fun d d' => essImageDayConvolution d d'
  convolutions' := fun d d' =>
    { convolution := (tensor C).pointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d')
      unit := (tensor C).pointwiseLeftKanExtensionUnit (ι.obj d ⊠ ι.obj d')
      isPointwiseLeftKanExt
-/
noncomputable def ofHasDayConvolutions
    {D : Type u₃} [Category.{v₃} D]
    (ι : D ⥤ C ⥤ V)
    (ffι : ι.FullyFaithful)
    [hasDayConvolution : forall (d d' : D),
      (tensor C).HasPointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d')]
    (essImageDayConvolution : forall (d d' : D),
ι.essImage (tensor C).pointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d'))
    [hasDayConvolutionUnit :
      (Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
        (Functor.fromPUnit.{0} <| 𝟙_ V)]
    (essImageDayConvolutionUnit :
ι.essImage
        (Functor.fromPUnit.{0} <| 𝟙_ C).pointwiseLeftKanExtension
          (Functor.fromPUnit.{0} <| 𝟙_ V)) :
    InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D where
  ι := ι
  fullyFaithulι := ffι
.witness tensorObj := fun d d' => essImageDayConvolution d d'
  convolutions' := fun d d' =>
    { convolution := (tensor C).pointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d')
      unit := (tensor C).pointwiseLeftKanExtensionUnit (ι.obj d ⊠ ι.obj d')
      isPointwiseLeftKanExtensionUnit :=
        (tensor C).pointwiseLeftKanExtensionIsPointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d') }
  tensorObjIsoConvolution := fun d d' => Functor.essImage.getIso _
  tensorUnit := essImageDayConvolutionUnit.witness
  tensorUnitConvolutionUnit :=
    { can :=
        ((Functor.fromPUnit.{0} <| 𝟙_ C).pointwiseLeftKanExtensionUnit
            (Functor.fromPUnit.{0} <| 𝟙_ V)).app (.mk PUnit.unit) ≫
          (essImageDayConvolutionUnit.getIso.inv.app (𝟙_ C))
      isPointwiseLeftKanExtensionCan :=
        Functor.LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
        (StructuredArrow.isoMk
          (essImageDayConvolutionUnit.getIso).symm)
        (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
          (Functor.fromPUnit.{0} <| 𝟙_ C)
          (Functor.fromPUnit.{0} <| 𝟙_ V)) }

end InducedLawfulDayConvolutionMonoidalCategoryStructCore

section

variable {C V}
    {D : Type u₃} [Category.{v₃} D]
    (ι : D ⥤ C ⥤ V)
    (ffι : ι.FullyFaithful)
    [hasDayConvolution : forall (d d' : D),
      (tensor C).HasPointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d')]
    (essImageDayConvolution : forall (d d' : D),
ι.essImage (tensor C).pointwiseLeftKanExtension (ι.obj d ⊠ ι.obj d'))
    [hasDayConvolutionUnit :
      (Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
        (Functor.fromPUnit.{0} <| 𝟙_ V)]
    (essImageDayConvolutionUnit :
ι.essImage
        (Functor.fromPUnit.{0} <| 𝟙_ C).pointwiseLeftKanExtension
          (Functor.fromPUnit.{0} <| 𝟙_ V))
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [forall (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [forall (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d)
        (tensorRight v)]
    [forall (v : V) (d : C × C),
      Limits.PreservesColimitsOfShape
        (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

/-- Under suitable assumptions on existence of relevant Kan extensions and preservation
of relevant colimits by the tensor product of `V`, we can define a `MonoidalCategory D`
from the data of a fully faithful functor `ι : D ⥤ C ⥤ V` whose essential image
contains a Day convolution unit and is stable under binary Day convolutions. -/
@[instance_reducible]
/--
Definition of `monoidalOfHasDayConvolutions` / `monoidalOfHasDayConvolutions` 的定义

English:
definition monoidalOfHasDayConvolutions
  signature: : MonoidalCategory D
  body: letI induced : InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D :=
    .ofHasDayConvolutions ι ffι essImageDayConvolution essImageDayConvolutionUnit
  letI := induced.mkMonoidalCategoryStruct
  letI : LawfulDayConvolutionMonoidalCategoryStruct C V D :=
    induced.mkLawfulDayConvolutionMo

中文:
定义 monoidalOfHasDayConvolutions
  签名: : 幺半群范畴 D
  定义体: letI induced : InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D :=
    .ofHasDayConvolutions ι ffι essImageDayConvolution essImageDayConvolutionUnit
  letI := induced.mkMonoidalCategoryStruct
  letI : LawfulDayConvolutionMonoidalCategoryStruct C V D :=
    induced.mkLawfulDayConvolutionMo

Depends on / 依赖: InducedLawfulDayConvolutionMonoidalCategoryStructCore, LawfulDayConvolutionMonoidalCategoryStruct, essImageDayConvolution, essImageDayConvolutionUnit, induced, induced.mkLawfulDayConvolutionMonoidalCategoryStruct, induced.mkMonoidalCategoryStruct, mkLawfulDayConvolutionMonoidalCategoryStruct, mkMonoidalCategoryStruct, monoidalOfLawfulDayConvolutionMonoidalCategoryStruct, ofHasDayConvolutions
-/
noncomputable def monoidalOfHasDayConvolutions : MonoidalCategory D :=
  letI induced : InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D :=
    .ofHasDayConvolutions ι ffι essImageDayConvolution essImageDayConvolutionUnit
  letI := induced.mkMonoidalCategoryStruct
  letI : LawfulDayConvolutionMonoidalCategoryStruct C V D :=
    induced.mkLawfulDayConvolutionMonoidalCategoryStruct
  monoidalOfLawfulDayConvolutionMonoidalCategoryStruct C V D

open InducedLawfulDayConvolutionMonoidalCategoryStructCore in
/-- The monoidal category constructed via `monoidalOfHasDayConvolutions` has a canonical
`LawfulDayConvolutionMonoidalCategoryStruct C V D`. -/
@[instance_reducible]
/--
Definition of `lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions` / `lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions` 的定义

English:
definition lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions
  signature: :
  body: monoidalOfHasDayConvolutions
      ι ffι essImageDayConvolution essImageDayConvolutionUnit
    LawfulDayConvolutionMonoidalCategoryStruct C V D :=
  letI : InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D :=
    .ofHasDayConvolutions ι ffι essImageDayConvolution essImageDayConvolutionUnit

中文:
定义 lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions
  签名: :
  定义体: monoidalOfHasDayConvolutions
      ι ffι essImageDayConvolution essImageDayConvolutionUnit
    LawfulDayConvolutionMonoidalCategoryStruct C V D :=
  letI : InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D :=
    .ofHasDayConvolutions ι ffι essImageDayConvolution essImageDayConvolutionUnit

Depends on / 依赖: monoidalOfHasDayConvolutions
-/
noncomputable def lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions :
    letI := monoidalOfHasDayConvolutions
      ι ffι essImageDayConvolution essImageDayConvolutionUnit
    LawfulDayConvolutionMonoidalCategoryStruct C V D :=
  letI : InducedLawfulDayConvolutionMonoidalCategoryStructCore C V D :=
    .ofHasDayConvolutions ι ffι essImageDayConvolution essImageDayConvolutionUnit
  letI := monoidalOfHasDayConvolutions
    ι ffι essImageDayConvolution essImageDayConvolutionUnit
  mkLawfulDayConvolutionMonoidalCategoryStruct C V D

end

end

end

end CategoryTheory.MonoidalCategory
