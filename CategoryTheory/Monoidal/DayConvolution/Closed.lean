/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.DayConvolution
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.End

/-! # Internal homs for day convolution

Given a category `V` that is monoidal closed, a category `C` that
is monoidal, a functor `C ⥤ V`, and given the data of suitable day convolutions
and suitable ends of profunctors `c c₁ c₂ ↦ ihom (F c₁) (·.obj (c₂ ⊗ c))`,
we prove that the data of the units of the left Kan extensions that define
day convolutions and the data of the canonical morphisms to the aforementioned
ends can be organised as data that exhibit `F` as monoidal closed in `C ⥤ V` for
the Day convolution monoidal structure.

## TODOs
* When `LawfulDayConvolutionMonoidalStruct` (https://github.com/leanprover-community/mathlib4/issues/26820) lands, transport the
  constructions here to produce actual `CategoryTheory.MonoidalClosed` instances.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MonoidalCategory
open scoped ExternalProduct
open Opposite Limits

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V] [MonoidalClosed V]

/-- Given `F : C ⥤ V`, this is the functor
`G ↦ c c₁ c₂ ↦ ihom (F c₁) (G.obj (c₂ ⊗ c))`.
The internal hom functor for Day convolution `[F, -]` is naturally isomorphic
to the functor `G ↦ c ↦ end_ (c₁ c₂ ↦ ihom (F c₁) (G.obj (c₂ ⊗ c)))`, hence
this definition. -/
@[simps!]
/--
Definition of `dayConvolutionInternalHomDiagramFunctor` / `dayConvolutionInternalHomDiagramFunctor` 的定义

English:
definition dayConvolutionInternalHomDiagramFunctor
  signature: (F : C ⥤ V)
  body: { obj c := Functor.whiskeringLeft₂ _ |>.obj F.op |>.obj
.obj MonoidalClosed.internalHom (tensorRight c ⋙ G)
.map .obj F.op map {c c'} f := Functor.whiskeringLeft₂ _
.app (Functor.whiskerRight (curriedTensor C |>.flip.map f) G)
          MonoidalClosed.internalHom }
  map {G G'} η :=
    { app c := F

中文:
定义 dayConvolution整数ernalHomDiagramFunctor
  签名: (F : C ⥤ V)
  定义体: { obj c := Functor.whiskeringLeft₂ _ |>.obj F.op |>.obj
.obj MonoidalClosed.internalHom (tensorRight c ⋙ G)
.map .obj F.op map {c c'} f := Functor.whiskeringLeft₂ _
.app (Functor.whiskerRight (curriedTensor C |>.flip.map f) G)
          MonoidalClosed.internalHom }
  map {G G'} η :=
    { app c := F

Depends on / 依赖: F.obj, F.op, Functor, Functor.whiskerLeft, Functor.whiskerRight, Functor.whiskeringLeft, MonoidalClosed, MonoidalClosed.internalHom, NatTrans, NatTrans.naturality, congr_arg, curriedTensor, flip.map, internalHom, naturality, tensorRight, whiskerLeft, whiskerRight
-/
def dayConvolutionInternalHomDiagramFunctor (F : C ⥤ V) :
    (C ⥤ V) ⥤ C ⥤ Cᵒᵖ ⥤ C ⥤ V where
  obj G :=
    { obj c := Functor.whiskeringLeft₂ _ |>.obj F.op |>.obj
.obj MonoidalClosed.internalHom (tensorRight c ⋙ G)
.map .obj F.op map {c c'} f := Functor.whiskeringLeft₂ _
.app (Functor.whiskerRight (curriedTensor C |>.flip.map f) G)
          MonoidalClosed.internalHom }
  map {G G'} η :=
    { app c := Functor.whiskeringLeft₂ _ |>.obj F.op |>.map
.app MonoidalClosed.internalHom (Functor.whiskerLeft _ η)
      naturality {c c'} f := by
        ext j k
        dsimp
        simpa [-NatTrans.naturality] using!
          congr_arg (ihom <| F.obj <| unop j).map (η.naturality <| k ◁ f) }

/--
Definition of `DayConvolutionInternalHom` / `DayConvolutionInternalHom` 的定义

English:
structure DayConvolutionInternalHom
  parameters: (F : C ⥤ V) (G : C ⥤ V) (H : C ⥤ V)
  axioms and operations (3):
    - π((c j : C)) : H.obj c ⟶ (ihom <| F.obj j).obj (G.obj <| j otimes c)
    - hπ((c : C) ⦃i j) : C⦄ (f : i ⟶ j) : π c i ≫ (ihom (F.obj i)).map (G.map <| f ▷ c) = π c j ≫ (MonoidalClosed.pre <| F.map f).app (G.obj <| j otimes c)
    - isLimitWedge((c : C))

中文:
结构 DayConvolution整数ernal态射
  参数: (F : C ⥤ V) (G : C ⥤ V) (H : C ⥤ V)
  公理与运算 (3 个):
    - π((c j : C)) : H.obj c ⟶ (ihom <| F.obj j).obj (G.obj <| j otimes c)
    - hπ((c : C) ⦃i j) : C⦄ (f : i ⟶ j) : π c i ≫ (ihom (F.obj i)).map (G.map <| f ▷ c) = π c j ≫ (幺半群闭.pre <| F.map f).app (G.obj <| j otimes c)
    - isLimitWedge((c : C))

Depends on / 依赖: dayConvolutionInternalHomDiagramFunctor
-/
structure DayConvolutionInternalHom (F : C ⥤ V) (G : C ⥤ V) (H : C ⥤ V) where
  /-- The canonical projections maps -/
  π (c j : C) : H.obj c ⟶ (ihom <| F.obj j).obj (G.obj <| j otimes c)
  /-- The projections maps assemble into a wedge. -/
  hπ (c : C) ⦃i j : C⦄ (f : i ⟶ j) :
    π c i ≫ (ihom (F.obj i)).map (G.map <| f ▷ c) =
    π c j ≫ (MonoidalClosed.pre <| F.map f).app (G.obj <| j otimes c)
  /-- The wedge defined by `π` and `hπ` is a limit wedge, i.e `H.obj c` is
  an end of `internalHomDiagramFunctor F G|>.obj c`. -/
  isLimitWedge (c : C) :
IsLimit Wedge.mk
      (F := dayConvolutionInternalHomDiagramFunctor F |>.obj G |>.obj c)
      (H.obj c) (π c) (hπ c)
  /-- The functoriality of `H.obj G` identifies (through
  `Wedge.IsLimit.hom_ext`) with the functoriality on ends induced by
  functoriality of `internalHomDiagramFunctor F|>.obj G`. -/
  map_comp_π {c c' : C} (f : c ⟶ c') (j : C) :
    H.map f ≫ π c' j = π c j ≫ (ihom <| F.obj j).map (G.map <| j ◁ f)

namespace DayConvolutionInternalHom

open scoped DayConvolution

attribute [reassoc (attr := simp)] map_comp_π
attribute [reassoc] hπ

variable {F : C ⥤ V} {G : C ⥤ V} {H : C ⥤ V}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (ℌ : DayConvolutionInternalHom F G H) {G' : C ⥤ V} {H' : C ⥤ V}
  body: Wedge.IsLimit.lift (ℌ'.isLimitWedge c)
    (fun j => (ℌ.π c j) ≫
      (dayConvolutionInternalHomDiagramFunctor
.app j)) .app (op j) .app c .map f F
    (fun ⦃j j'⦄ φ => by
have := congrArg (fun t => t.app j')
        dayConvolutionInternalHomDiagramFunctor
.naturality φ.op .app c .map f F
      dsi

中文:
定义 map
  签名: (ℌ : DayConvolution整数ernal态射 F G H) {G' : C ⥤ V} {H' : C ⥤ V}
  定义体: Wedge.IsLimit.lift (ℌ'.isLimitWedge c)
    (fun j => (ℌ.π c j) ≫
      (dayConvolutionInternalHomDiagramFunctor
.app j)) .app (op j) .app c .map f F
    (fun ⦃j j'⦄ φ => by
have := congrArg (fun t => t.app j')
        dayConvolutionInternalHomDiagramFunctor
.naturality φ.op .app c .map f F
      dsi

Depends on / 依赖: IsLimit, NatTrans, NatTrans.isIso_iff_isIso_app, ReflectsIsomorphisms, ReflectsIsomorphisms.reflects, Wedge.IsLimit.lift, allowSynthFailures, isIso_iff_isIso_app, isIso_ranCounit_app_of_isDenseSubsite, isLimitWedge, reflects, sheafAdjunctionCocontinuous_counit_app_hom, sheafToPresheaf, yoneda
-/
def map (ℌ : DayConvolutionInternalHom F G H) {G' : C ⥤ V} {H' : C ⥤ V}
    (f : G ⟶ G') (ℌ' : DayConvolutionInternalHom F G' H') :
    H ⟶ H' where
  app c := Wedge.IsLimit.lift (ℌ'.isLimitWedge c)
    (fun j => (ℌ.π c j) ≫
      (dayConvolutionInternalHomDiagramFunctor
.app j)) .app (op j) .app c .map f F
    (fun ⦃j j'⦄ φ => by
have := congrArg (fun t => t.app j')
        dayConvolutionInternalHomDiagramFunctor
.naturality φ.op .app c .map f F
      dsimp at this ⊢
      rw [Category.assoc]; rw [← (ihom (F.obj j)).map_comp]; rw [← f.naturality]; rw [Functor.map_comp]; rw [reassoc_of% ℌ.hπ]
      simp)
  naturality {c c'} f := by
    apply Wedge.IsLimit.hom_ext (ℌ'.isLimitWedge c')
    intro j
    dsimp
    simp only [Category.assoc, map_comp_π]
    rw [← Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c')
        (H'.obj c') (ℌ'.π c') (ℌ'.hπ c')]; rw [← Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
        (H'.obj c) (ℌ'.π c) (ℌ'.hπ c)]; rw [Wedge.IsLimit.lift_ι (ℌ'.isLimitWedge c')]; rw [Wedge.IsLimit.lift_ι_assoc (ℌ'.isLimitWedge c)]
    simp [← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `map_app_comp_π` / 引理 `map_app_comp_π`

English:
lemma map_app_comp_π
  statement: (ℌ : DayConvolutionInternalHom F G H)
  proof: by
  dsimp [map]
  rw [← Wedge.mk_ι
      (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
      (H'.obj c) (ℌ'.π c) (ℌ'.hπ c)]; rw [Wedge.IsLimit.lift_ι (ℌ'.isLimitWedge c)]

中文:
引理 map_app_comp_π
  结论: (ℌ : DayConvolution整数ernal态射 F G H)
  证明: by
  dsimp [map]
  rw [← Wedge.mk_ι
      (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
      (H'.obj c) (ℌ'.π c) (ℌ'.hπ c)]; rw [Wedge.IsLimit.lift_ι (ℌ'.isLimitWedge c)]

Depends on / 依赖: IsLimit, Wedge.IsLimit.lift_, Wedge.mk_, dayConvolutionInternalHomDiagramFunctor, isLimitWedge
-/
lemma map_app_comp_π (ℌ : DayConvolutionInternalHom F G H)
    {G' : C ⥤ V} {H' : C ⥤ V} (f : G ⟶ G')
    (ℌ' : DayConvolutionInternalHom F G' H') (c : C) (j : C) :
    (ℌ.map f ℌ').app c ≫ ℌ'.π c j =
    ℌ.π c j ≫ (ihom <| F.obj j).map (f.app <| j otimes c) := by
  dsimp [map]
  rw [← Wedge.mk_ι
      (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
      (H'.obj c) (ℌ'.π c) (ℌ'.hπ c)]; rw [Wedge.IsLimit.lift_ι (ℌ'.isLimitWedge c)]

section ev

variable [DayConvolution F H] (ℌ : DayConvolutionInternalHom F G H)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ev_app` / `ev_app` 的定义

English:
definition ev_app
  signature: : F ⊛ H ⟶ G
  body: .homEquiv.symm DayConvolution.corepresentableBy F H
    { app x := MonoidalClosed.uncurry <| ℌ.π x.2 x.1
      naturality {x y} f := by
have := congrArg (fun t => F.obj x.1 ◁ t) ℌ.hπ x.2 f.1
        dsimp at this ⊢
        simp only [whiskerLeft_comp] at this
        simp only [Category.assoc, Monoi

中文:
定义 ev_app
  签名: : F ⊛ H ⟶ G
  定义体: .homEquiv.symm DayConvolution.corepresentableBy F H
    { app x := MonoidalClosed.uncurry <| ℌ.π x.2 x.1
      naturality {x y} f := by
have := congrArg (fun t => F.obj x.1 ◁ t) ℌ.hπ x.2 f.1
        dsimp at this ⊢
        simp only [whiskerLeft_comp] at this
        simp only [Category.assoc, Monoi

Depends on / 依赖: Category, Category.assoc, DayConvolution, DayConvolution.corepresentableBy, F.obj, Functor, Functor.comp_obj, Functor.id_obj, MonoidalClosed, MonoidalClosed.uncurry, MonoidalClosed.uncurry_eq, comp_obj, corepresentableBy, curriedTensor_obj_obj, ev_naturality, homEquiv, homEquiv.symm, id_obj, ihom.ev_naturality, naturality
-/
def ev_app : F ⊛ H ⟶ G :=
.homEquiv.symm DayConvolution.corepresentableBy F H
    { app x := MonoidalClosed.uncurry <| ℌ.π x.2 x.1
      naturality {x y} f := by
have := congrArg (fun t => F.obj x.1 ◁ t) ℌ.hπ x.2 f.1
        dsimp at this ⊢
        simp only [whiskerLeft_comp] at this
        simp only [Category.assoc, MonoidalClosed.uncurry_eq, Functor.id_obj,
          ← whiskerLeft_comp_assoc, map_comp_π]
        simp only [whiskerLeft_comp, Category.assoc, ihom.ev_naturality,
          Functor.comp_obj, curriedTensor_obj_obj, Functor.id_obj,
          ← whisker_exchange_assoc, tensorHom_def, Functor.map_comp,
          ← ihom.ev_naturality_assoc]
        rw [reassoc_of% this]
        simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `unit_app_ev_app_app` / 引理 `unit_app_ev_app_app`

English:
lemma unit_app_ev_app_app
  given: (x y : C)
  proof: by
  have := Functor.descOfIsLeftKanExtension_fac_app (F ⊛ H)
    (DayConvolution.unit F H) G
  dsimp at this
  simp [this, ev_app]

中文:
引理 unit_app_ev_app_app
  条件: (x y : C)
  证明: by
  have := Functor.descOfIsLeftKanExtension_fac_app (F ⊛ H)
    (DayConvolution.unit F H) G
  dsimp at this
  simp [this, ev_app]

Depends on / 依赖: DayConvolution, DayConvolution.unit, Functor, Functor.descOfIsLeftKanExtension_fac_app, descOfIsLeftKanExtension_fac_app, ev_app
-/
lemma unit_app_ev_app_app (x y : C) :
    ((DayConvolution.unit F H).app (x, y) ≫ (ℌ.ev_app).app (x otimes y)) =
    MonoidalClosed.uncurry (ℌ.π y x) := by
  have := Functor.descOfIsLeftKanExtension_fac_app (F ⊛ H)
    (DayConvolution.unit F H) G
  dsimp at this
  simp [this, ev_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ev_naturality_app` / 引理 `ev_naturality_app`

English:
lemma ev_naturality_app
  statement: {G' H' : C ⥤ V} (ℌ' : DayConvolutionInternalHom F G' H')
  proof: by
.homEquiv.injective apply DayConvolution.corepresentableBy F H
  dsimp
  ext ⟨x, y⟩
  simp [MonoidalClosed.uncurry_eq, ← whiskerLeft_comp_assoc]

中文:
引理 ev_naturality_app
  结论: {G' H' : C ⥤ V} (ℌ' : DayConvolution整数ernal态射 F G' H')
  证明: by
.homEquiv.injective apply DayConvolution.corepresentableBy F H
  dsimp
  ext ⟨x, y⟩
  simp [MonoidalClosed.uncurry_eq, ← whiskerLeft_comp_assoc]

Depends on / 依赖: D.iso, DayConvolution, DayConvolution.corepresentableBy, MonoidalClosed, MonoidalClosed.uncurry_eq, corepresentableBy, homEquiv, homEquiv.injective, injective, isIso_hom, uncurry_eq, whiskerLeft_comp_assoc
-/
lemma ev_naturality_app {G' H' : C ⥤ V} (ℌ' : DayConvolutionInternalHom F G' H')
    [DayConvolution F H'] (η : G ⟶ G') :
    DayConvolution.map (𝟙 F) (ℌ.map η ℌ') ≫ ℌ'.ev_app = ℌ.ev_app ≫ η := by
.homEquiv.injective apply DayConvolution.corepresentableBy F H
  dsimp
  ext ⟨x, y⟩
  simp [MonoidalClosed.uncurry_eq, ← whiskerLeft_comp_assoc]

end ev

section coev

variable {G : C ⥤ V} [DayConvolution F G]
    (ℌ : DayConvolutionInternalHom F (F ⊛ G) H)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coev_app` / `coev_app` 的定义

English:
definition coev_app
  signature: : G ⟶ H where
  body: Wedge.IsLimit.lift (ℌ.isLimitWedge c)
      (fun c' => MonoidalClosed.curry <|
        (DayConvolution.unit F G).app (c', c))
        (fun {c' c''} f => by
          have := DayConvolution.unit_naturality F G f (𝟙 c)
          simp only [Functor.map_id, tensorHom_id] at this
          replace this :

中文:
定义 coev_app
  签名: : G ⟶ H where
  定义体: Wedge.IsLimit.lift (ℌ.isLimitWedge c)
      (fun c' => MonoidalClosed.curry <|
        (DayConvolution.unit F G).app (c', c))
        (fun {c' c''} f => by
          have := DayConvolution.unit_naturality F G f (𝟙 c)
          simp only [Functor.map_id, tensorHom_id] at this
          replace this :

Depends on / 依赖: DayConvolution, DayConvolution.unit, DayConvolution.unit_naturality, Functor, Functor.map_id, IsLimit, MonoidalClosed, MonoidalClosed.curry, MonoidalClosed.curry_eq, MonoidalClosed.curry_natural_right, Wedge.IsLimit.hom_ext, Wedge.IsLimit.lift, curry_eq, curry_natural_right, hom_ext, isLimitWedge, map_id, multico, naturality, replace
-/
def coev_app : G ⟶ H where
  app c :=
    Wedge.IsLimit.lift (ℌ.isLimitWedge c)
      (fun c' => MonoidalClosed.curry <|
        (DayConvolution.unit F G).app (c', c))
        (fun {c' c''} f => by
          have := DayConvolution.unit_naturality F G f (𝟙 c)
          simp only [Functor.map_id, tensorHom_id] at this
          replace this := congrArg MonoidalClosed.curry this
          simp only [MonoidalClosed.curry_natural_right] at this
          dsimp
          rw [← this]
          simp [MonoidalClosed.curry_eq])
  naturality {c c'} f := by
    dsimp
apply Wedge.IsLimit.hom_ext ℌ.isLimitWedge c'
    intro (j : C)
    simp only [multicospanIndexEnd_left,
      dayConvolutionInternalHomDiagramFunctor_obj_obj_obj_obj, Multifork.ofι_pt,
      Wedge.mk_ι, Category.assoc, map_comp_π]
    rw [← Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
        (H.obj c) (ℌ.π c) (ℌ.hπ c)]; rw [← Wedge.mk_ι
        (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c')
        (H.obj c') (ℌ.π c') (ℌ.hπ c')]; rw [Wedge.IsLimit.lift_ι_assoc]; rw [Wedge.IsLimit.lift_ι]
    have := DayConvolution.unit_naturality F G (𝟙 j) f
    simp only [Functor.map_id, id_tensorHom] at this
    replace this := congrArg MonoidalClosed.curry this
    simp only [MonoidalClosed.curry_natural_right] at this
    rw [← this]
    simp [MonoidalClosed.curry_eq]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `coev_app_π` / 引理 `coev_app_π`

English:
lemma coev_app_π
  given: (c j : C)
  proof: by
  dsimp [coev_app]
  rw [← Wedge.mk_ι
      (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
      (H.obj c) (ℌ.π c) (ℌ.hπ c)]; rw [Wedge.IsLimit.lift_ι]

中文:
引理 coev_app_π
  条件: (c j : C)
  证明: by
  dsimp [coev_app]
  rw [← Wedge.mk_ι
      (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
      (H.obj c) (ℌ.π c) (ℌ.hπ c)]; rw [Wedge.IsLimit.lift_ι]

Depends on / 依赖: H.obj, IsLimit, Wedge.IsLimit.lift_, Wedge.mk_, coev_app, dayConvolutionInternalHomDiagramFunctor
-/
lemma coev_app_π (c j : C) :
    ℌ.coev_app.app c ≫ ℌ.π c j =
    MonoidalClosed.curry ((DayConvolution.unit F G).app (j, c)) := by
  dsimp [coev_app]
  rw [← Wedge.mk_ι
      (F := dayConvolutionInternalHomDiagramFunctor F |>.obj _ |>.obj c)
      (H.obj c) (ℌ.π c) (ℌ.hπ c)]; rw [Wedge.IsLimit.lift_ι]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `coev_naturality_app` / 引理 `coev_naturality_app`

English:
lemma coev_naturality_app
  statement: {G' H' : C ⥤ V} [DayConvolution F G'] (η : G ⟶ G')
  proof: by
  ext c
  dsimp
apply Wedge.IsLimit.hom_ext ℌ'.isLimitWedge c
  intro j
  apply MonoidalClosed.uncurry_injective
  dsimp
  simp only [Category.assoc, coev_app_π, Functor.comp_obj, tensor_obj,
    map_app_comp_π, coev_app_π_assoc, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_cu

中文:
引理 coev_naturality_app
  结论: {G' H' : C ⥤ V} [Day卷积 F G'] (η : G ⟶ G')
  证明: by
  ext c
  dsimp
apply Wedge.IsLimit.hom_ext ℌ'.isLimitWedge c
  intro j
  apply MonoidalClosed.uncurry_injective
  dsimp
  simp only [Category.assoc, coev_app_π, Functor.comp_obj, tensor_obj,
    map_app_comp_π, coev_app_π_assoc, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_cu

Depends on / 依赖: Category, Category.assoc, DayConvolution, DayConvolution.unit_app_map_app, Functor, Functor.comp_obj, IsLimit, MonoidalClosed, MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_injective, MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right, NatTrans, NatTrans.id_app, Wedge.IsLimit.hom_ext, comp_obj, hom_ext, id_app, id_tensorHom, isLimitWedge
-/
lemma coev_naturality_app {G' H' : C ⥤ V} [DayConvolution F G'] (η : G ⟶ G')
    (ℌ' : DayConvolutionInternalHom F (F ⊛ G') H') :
    η ≫ ℌ'.coev_app =
    ℌ.coev_app ≫ ℌ.map (DayConvolution.map (𝟙 _) η) ℌ' := by
  ext c
  dsimp
apply Wedge.IsLimit.hom_ext ℌ'.isLimitWedge c
  intro j
  apply MonoidalClosed.uncurry_injective
  dsimp
  simp only [Category.assoc, coev_app_π, Functor.comp_obj, tensor_obj,
    map_app_comp_π, coev_app_π_assoc, MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.uncurry_curry, DayConvolution.unit_app_map_app,
    NatTrans.id_app, id_tensorHom]
  simp [MonoidalClosed.uncurry_natural_left]

end coev

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `left_triangle_components` / 定理 `left_triangle_components`

English:
theorem left_triangle_components
  statement: (G : C ⥤ V) [DayConvolution F G]
  proof: by
.homEquiv.injective apply DayConvolution.corepresentableBy F G
  dsimp
  ext ⟨x, y⟩
  apply MonoidalClosed.curry_injective
  simp [MonoidalClosed.curry_natural_left]

中文:
定理 left_triangle_components
  结论: (G : C ⥤ V) [Day卷积 F G]
  证明: by
.homEquiv.injective apply DayConvolution.corepresentableBy F G
  dsimp
  ext ⟨x, y⟩
  apply MonoidalClosed.curry_injective
  simp [MonoidalClosed.curry_natural_left]

Depends on / 依赖: DayConvolution, DayConvolution.corepresentableBy, MonoidalClosed, MonoidalClosed.curry_injective, MonoidalClosed.curry_natural_left, corepresentableBy, curry_injective, curry_natural_left, homEquiv, homEquiv.injective, injective
-/
theorem left_triangle_components (G : C ⥤ V) [DayConvolution F G]
    (ℌ : DayConvolutionInternalHom F (F ⊛ G) H) [DayConvolution F H] :
    DayConvolution.map (𝟙 F) ℌ.coev_app ≫ ℌ.ev_app = 𝟙 (F ⊛ G) := by
.homEquiv.injective apply DayConvolution.corepresentableBy F G
  dsimp
  ext ⟨x, y⟩
  apply MonoidalClosed.curry_injective
  simp [MonoidalClosed.curry_natural_left]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `right_triangle_components` / 定理 `right_triangle_components`

English:
theorem right_triangle_components
  statement: (G : C ⥤ V) [DayConvolution F H]
  proof: by
  ext c
apply Wedge.IsLimit.hom_ext ℌ.isLimitWedge c
  intro j
  apply MonoidalClosed.uncurry_injective
  simp [MonoidalClosed.uncurry_natural_right]

中文:
定理 right_triangle_components
  结论: (G : C ⥤ V) [Day卷积 F H]
  证明: by
  ext c
apply Wedge.IsLimit.hom_ext ℌ.isLimitWedge c
  intro j
  apply MonoidalClosed.uncurry_injective
  simp [MonoidalClosed.uncurry_natural_right]

Depends on / 依赖: IsLimit, MonoidalClosed, MonoidalClosed.uncurry_injective, MonoidalClosed.uncurry_natural_right, Wedge.IsLimit.hom_ext, hom_ext, isLimitWedge, uncurry_injective, uncurry_natural_right
-/
theorem right_triangle_components (G : C ⥤ V) [DayConvolution F H]
    (ℌ : DayConvolutionInternalHom F G H) {H' : C ⥤ V}
    (ℌ' : DayConvolutionInternalHom F (F ⊛ H) H') :
    ℌ'.coev_app ≫ ℌ'.map ℌ.ev_app ℌ = 𝟙 H := by
  ext c
apply Wedge.IsLimit.hom_ext ℌ.isLimitWedge c
  intro j
  apply MonoidalClosed.uncurry_injective
  simp [MonoidalClosed.uncurry_natural_right]

end DayConvolutionInternalHom

end

end CategoryTheory.MonoidalCategory
