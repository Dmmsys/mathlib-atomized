/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.DayConvolution

/-!
# Day functors

In this file, given a monoidal category `C` and a monoidal category `V`,
we define a basic type synonym `DayFunctor C V` (denoted `C ⊛⥤ D`)
for the category `C ⥤ V` and endow it with the monoidal structure coming
from Day convolution. Such a setup is necessary as by default,
the `MonoidalCategory` instance on `C ⥤ V` is the "pointwise" one,
where the tensor product of `F` and `G` is the functor `x ↦ F.obj x ⊗ G.obj x`.

## TODOs
- Given a `LawfulDayConvolutionMonoidalCategoryStruct C V D`, show that
  ι induces a monoidal functor `D ⥤ (C ⊛⥤ V)`.
- Specialize to the case `V := Type _`, and prove a universal property stating
  that for every monoidal category `W` with suitable colimits,
  colimit-preserving monoidal functors `(Cᵒᵖ ⊛⥤ Type u) ⥤ W` are equivalent to
  monoidal functors `C ⥤ W`. Show that the Yoneda embedding is monoidal.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.MonoidalCategory
open scoped ExternalProduct

noncomputable section

/--
Definition of `DayFunctor` / `DayFunctor` 的定义

English:
structure DayFunctor
  axioms and operations (1):
    - functor : C ⥤ V

中文:
结构 DayFunctor
  公理与运算 (1 个):
    - functor : C ⥤ V
-/
structure DayFunctor
    (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V] where
  /-- the underlying functor. -/
  functor : C ⥤ V

namespace DayFunctor

/-- Notation for `DayFunctor`. -/
scoped infixr:26 " ⊛⥤ " => DayFunctor

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]

/--
lemma `mk_functor` / 引理 `mk_functor`

English:
lemma mk_functor
  given: (F : C ⥤ V)
  statement: (mk F).functor = F
  proof: rfl

@[simp]

中文:
引理 mk_functor
  条件: (F : C ⥤ V)
  结论: (mk F).functor = F
  证明: rfl

@[simp]
-/
lemma mk_functor (F : C ⥤ V) : (mk F).functor = F := rfl

@[simp]
/--
lemma `functor_mk` / 引理 `functor_mk`

English:
lemma functor_mk
  given: (F : C ⊛⥤ V)
  statement: mk F.functor = F
  proof: rfl

中文:
引理 functor_mk
  条件: (F : C ⊛⥤ V)
  结论: mk F.functor = F
  证明: rfl
-/
lemma functor_mk (F : C ⊛⥤ V) : mk F.functor = F := rfl

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (F G : C ⊛⥤ V)
  axioms and operations (1):
    - natTrans : F.functor ⟶ G.functor

中文:
结构 Hom
  参数: (F G : C ⊛⥤ V)
  公理与运算 (1 个):
    - natTrans : F.functor ⟶ G.functor
-/
structure Hom (F G : C ⊛⥤ V) where
  /-- the underlying natural transformation -/
  natTrans : F.functor ⟶ G.functor

@[simps id_natTrans comp_natTrans]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (C ⊛⥤ V)
  body: Hom
id x := .mk 𝟙 x.functor
comp α β := .mk α.natTrans ≫ β.natTrans

@[ext]

中文:
实例 :
  签名: Category (C ⊛⥤ V)
  定义体: Hom
id x := .mk 𝟙 x.functor
comp α β := .mk α.natTrans ≫ β.natTrans

@[ext]
-/
instance : Category (C ⊛⥤ V) where
  Hom := Hom
id x := .mk 𝟙 x.functor
comp α β := .mk α.natTrans ≫ β.natTrans

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {F G : C ⊛⥤ V} {α β : F ⟶ G} (h : α.natTrans = β.natTrans)
  proof: by
  cases α
  cases β
  grind

中文:
引理 hom_ext
  条件: {F G : C ⊛⥤ V} {α β : F ⟶ G} (h : α.natTrans = β.natTrans)
  证明: by
  cases α
  cases β
  grind
-/
lemma hom_ext {F G : C ⊛⥤ V} {α β : F ⟶ G} (h : α.natTrans = β.natTrans) :
    α = β := by
  cases α
  cases β
  grind

variable (C V) in
/-- The tautological equivalence of categories between `C ⥤ V` and `C ⊛⥤ V`. -/
@[simps! functor_obj functor_map inverse_obj_functor inverse_map_natTrans
  unitIso_hom_app unitIso_inv_app counitIso_hom_app counitIso_inv_app]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : (C ⊛⥤ V) ≌ (C ⥤ V) where
  body: { obj F := F.functor
      map α := α.natTrans }
  inverse :=
    { obj F := .mk F
      map α := .mk α }
  unitIso := .refl _
  counitIso := .refl _

中文:
定义 equiv
  签名: : (C ⊛⥤ V) ≌ (C ⥤ V) where
  定义体: { obj F := F.functor
      map α := α.natTrans }
  inverse :=
    { obj F := .mk F
      map α := .mk α }
  unitIso := .refl _
  counitIso := .refl _

Depends on / 依赖: F.functor, counitIso, functor, inverse, natTrans, unitIso
-/
def equiv : (C ⊛⥤ V) ≌ (C ⥤ V) where
  functor :=
    { obj F := F.functor
      map α := α.natTrans }
  inverse :=
    { obj F := .mk F
      map α := .mk α }
  unitIso := .refl _
  counitIso := .refl _

variable
    [hasDayConvolution : forall (F G : C ⥤ V),
      (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [hasDayConvolutionUnit :
      (Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
        (Functor.fromPUnit.{0} <| 𝟙_ V)]
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategory (C ⊛⥤ V)
  body: monoidalOfHasDayConvolutions
    (equiv C V).functor
    (equiv C V).fullyFaithfulFunctor
    (fun _ _ => ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)
.counitIso.app _⟩⟩ ⟨_, ⟨equiv C V

@[simps! ι_obj ι_map]

中文:
实例 :
  签名: MonoidalCategory (C ⊛⥤ V)
  定义体: monoidalOfHasDayConvolutions
    (equiv C V).functor
    (equiv C V).fullyFaithfulFunctor
    (fun _ _ => ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)
.counitIso.app _⟩⟩ ⟨_, ⟨equiv C V

@[simps! ι_obj ι_map]

Depends on / 依赖: counitIso, counitIso.app, fullyFaithfulFunctor, functor, monoidalOfHasDayConvolutions
-/
instance : MonoidalCategory (C ⊛⥤ V) :=
  monoidalOfHasDayConvolutions
    (equiv C V).functor
    (equiv C V).fullyFaithfulFunctor
    (fun _ _ => ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)
.counitIso.app _⟩⟩ ⟨_, ⟨equiv C V

@[simps! ι_obj ι_map]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulDayConvolutionMonoidalCategoryStruct C V (C ⊛⥤ V)
  body: lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions
    (equiv C V).functor
    (equiv C V).fullyFaithfulFunctor
    (fun _ _ => ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)
.counitIso.app _⟩⟩ ⟨_, ⟨equiv C V

中文:
实例 :
  签名: LawfulDayConvolutionMonoidalCategoryStruct C V (C ⊛⥤ V)
  定义体: lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions
    (equiv C V).functor
    (equiv C V).fullyFaithfulFunctor
    (fun _ _ => ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)
.counitIso.app _⟩⟩ ⟨_, ⟨equiv C V

Depends on / 依赖: counitIso, counitIso.app, fullyFaithfulFunctor, functor, lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions
-/
instance : LawfulDayConvolutionMonoidalCategoryStruct C V (C ⊛⥤ V) :=
  lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions
    (equiv C V).functor
    (equiv C V).fullyFaithfulFunctor
    (fun _ _ => ⟨_, ⟨equiv C V|>.counitIso.app _⟩⟩)
.counitIso.app _⟩⟩ ⟨_, ⟨equiv C V

/--
Definition of `η` / `η` 的定义

English:
definition η
  signature: (F G : C ⊛⥤ V)
  body: LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit
    C V F G

中文:
定义 η
  签名: (F G : C ⊛⥤ V)
  定义体: LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit
    C V F G

Depends on / 依赖: LawfulDayConvolutionMonoidalCategoryStruct, LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit, convolutionExtensionUnit
-/
def η (F G : C ⊛⥤ V) :
    F.functor ⊠ G.functor ⟶ tensor C ⋙ (F otimes G).functor :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit
    C V F G

open LawfulDayConvolutionMonoidalCategoryStruct in
instance (F G : C ⊛⥤ V) : (F otimes G).functor.IsLeftKanExtension (η F G) :=
  (isPointwiseLeftKanExtensionConvolutionExtensionUnit F G).isLeftKanExtension

open LawfulDayConvolutionMonoidalCategoryStruct in
/--
theorem `tensor_hom_ext` / 定理 `tensor_hom_ext`

English:
theorem tensor_hom_ext
  statement: {F G H : C ⊛⥤ V} {α β : F otimes G ⟶ H}
  proof: by
  ext : 1
  apply Functor.hom_ext_of_isLeftKanExtension
    (F otimes G).functor (η F G) _
  ext ⟨x, y⟩
  exact h x y

中文:
定理 tensor_hom_ext
  结论: {F G H : C ⊛⥤ V} {α β : F otimes G ⟶ H}
  证明: by
  ext : 1
  apply Functor.hom_ext_of_isLeftKanExtension
    (F otimes G).functor (η F G) _
  ext ⟨x, y⟩
  exact h x y

Depends on / 依赖: Functor, Functor.hom_ext_of_isLeftKanExtension, functor, hom_ext_of_isLeftKanExtension, otimes
-/
theorem tensor_hom_ext {F G H : C ⊛⥤ V} {α β : F otimes G ⟶ H}
    (h : forall (x y : C),
      (η F G).app (x, y) ≫ α.natTrans.app (x otimes y) =
      (η F G).app (x, y) ≫ β.natTrans.app (x otimes y)) :
    α = β := by
  ext : 1
  apply Functor.hom_ext_of_isLeftKanExtension
    (F otimes G).functor (η F G) _
  ext ⟨x, y⟩
  exact h x y

/--
Definition of `tensorDesc` / `tensorDesc` 的定义

English:
definition tensorDesc
  signature: {F G H : C ⊛⥤ V}
  body: .mk (F otimes G).functor.descOfIsLeftKanExtension (η F G) H.functor α

中文:
定义 tensorDesc
  签名: {F G H : C ⊛⥤ V}
  定义体: .mk (F otimes G).functor.descOfIsLeftKanExtension (η F G) H.functor α

Depends on / 依赖: H.functor, descOfIsLeftKanExtension, functor, functor.descOfIsLeftKanExtension, otimes
-/
def tensorDesc {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor) :
    F otimes G ⟶ H :=
.mk (F otimes G).functor.descOfIsLeftKanExtension (η F G) H.functor α

/--
lemma `η_comp_tensorDec` / 引理 `η_comp_tensorDec`

English:
lemma η_comp_tensorDec
  statement: {F G H : C ⊛⥤ V}
  proof: Functor.descOfIsLeftKanExtension_fac _ _ _ _

@[reassoc (attr := simp)]

中文:
引理 η_comp_tensorDec
  结论: {F G H : C ⊛⥤ V}
  证明: Functor.descOfIsLeftKanExtension_fac _ _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.descOfIsLeftKanExtension_fac, descOfIsLeftKanExtension_fac
-/
lemma η_comp_tensorDec {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor) :
    η F G ≫ Functor.whiskerLeft _ (tensorDesc α).natTrans = α :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

@[reassoc (attr := simp)]
/--
lemma `η_comp_tensorDesc_app` / 引理 `η_comp_tensorDesc_app`

English:
lemma η_comp_tensorDesc_app
  statement: {F G H : C ⊛⥤ V}
  proof: Functor.descOfIsLeftKanExtension_fac_app _ _ _ _ _

中文:
引理 η_comp_tensorDesc_app
  结论: {F G H : C ⊛⥤ V}
  证明: Functor.descOfIsLeftKanExtension_fac_app _ _ _ _ _

Depends on / 依赖: Functor, Functor.descOfIsLeftKanExtension_fac_app, descOfIsLeftKanExtension_fac_app
-/
lemma η_comp_tensorDesc_app {F G H : C ⊛⥤ V}
    (α : F.functor ⊠ G.functor ⟶ tensor C ⋙ H.functor) (x y : C) :
    (η F G).app (x, y) ≫ (tensorDesc α).natTrans.app (x otimes y) = α.app (x, y) :=
  Functor.descOfIsLeftKanExtension_fac_app _ _ _ _ _

open LawfulDayConvolutionMonoidalCategoryStruct
/--
Definition of `isoPointwiseLeftKanExtension` / `isoPointwiseLeftKanExtension` 的定义

English:
definition isoPointwiseLeftKanExtension
  signature: (F G : C ⊛⥤ V)
  body: Functor.leftKanExtensionUnique
    (F otimes G).functor (η F G) _
    ((tensor C).pointwiseLeftKanExtensionUnit (F.functor ⊠ G.functor))

中文:
定义 isoPointwiseLeftKanExtension
  签名: (F G : C ⊛⥤ V)
  定义体: Functor.leftKanExtensionUnique
    (F otimes G).functor (η F G) _
    ((tensor C).pointwiseLeftKanExtensionUnit (F.functor ⊠ G.functor))

Depends on / 依赖: F.functor, Functor, Functor.leftKanExtensionUnique, G.functor, functor, leftKanExtensionUnique, otimes, pointwiseLeftKanExtensionUnit, tensor
-/
def isoPointwiseLeftKanExtension (F G : C ⊛⥤ V) :
    (F otimes G).functor ≅
    (tensor C).pointwiseLeftKanExtension (F.functor ⊠ G.functor) :=
  Functor.leftKanExtensionUnique
    (F otimes G).functor (η F G) _
    ((tensor C).pointwiseLeftKanExtensionUnit (F.functor ⊠ G.functor))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `η_comp_isoPointwiseLeftKanExtension_hom` / 引理 `η_comp_isoPointwiseLeftKanExtension_hom`

English:
lemma η_comp_isoPointwiseLeftKanExtension_hom
  given: (F G : C ⊛⥤ V) (x y : C)
  proof: by
  simpa [η, isoPointwiseLeftKanExtension] using!
    Functor.descOfIsLeftKanExtension_fac_app
      (F otimes G).functor (η F G) _
      ((tensor C).pointwiseLeftKanExtensionUnit (F.functor ⊠ G.functor)) (x, y)

中文:
引理 η_comp_isoPointwiseLeftKanExtension_hom
  条件: (F G : C ⊛⥤ V) (x y : C)
  证明: by
  simpa [η, isoPointwiseLeftKanExtension] using!
    Functor.descOfIsLeftKanExtension_fac_app
      (F otimes G).functor (η F G) _
      ((tensor C).pointwiseLeftKanExtensionUnit (F.functor ⊠ G.functor)) (x, y)

Depends on / 依赖: F.functor, Functor, Functor.descOfIsLeftKanExtension_fac_app, G.functor, descOfIsLeftKanExtension_fac_app, functor, isoPointwiseLeftKanExtension, otimes, pointwiseLeftKanExtensionUnit, tensor
-/
lemma η_comp_isoPointwiseLeftKanExtension_hom (F G : C ⊛⥤ V) (x y : C) :
    (η F G).app (x, y) ≫ (isoPointwiseLeftKanExtension F G).hom.app (x otimes y) =
    Limits.colimit.ι
      (CostructuredArrow.proj (tensor C) (x otimes y) ⋙ F.functor ⊠ G.functor)
      (.mk (Y := (x, y)) <| 𝟙 (x otimes y)) := by
  simpa [η, isoPointwiseLeftKanExtension] using!
    Functor.descOfIsLeftKanExtension_fac_app
      (F otimes G).functor (η F G) _
      ((tensor C).pointwiseLeftKanExtensionUnit (F.functor ⊠ G.functor)) (x, y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `ι_comp_isoPointwiseLeftKanExtension_inv` / 引理 `ι_comp_isoPointwiseLeftKanExtension_inv`

English:
lemma ι_comp_isoPointwiseLeftKanExtension_inv
  given: (F G : C ⊛⥤ V) (x y : C)
  proof: by
  simp [η, isoPointwiseLeftKanExtension]

中文:
引理 ι_comp_isoPointwiseLeftKanExtension_inv
  条件: (F G : C ⊛⥤ V) (x y : C)
  证明: by
  simp [η, isoPointwiseLeftKanExtension]

Depends on / 依赖: otimes
-/
lemma ι_comp_isoPointwiseLeftKanExtension_inv (F G : C ⊛⥤ V) (x y : C) :
    Limits.colimit.ι
      (CostructuredArrow.proj (tensor C) (x otimes y) ⋙ F.functor ⊠ G.functor)
        (.mk (Y := (x, y)) <| 𝟙 (x otimes y)) ≫
      (isoPointwiseLeftKanExtension F G).inv.app (x otimes y) =
    (η F G).app (x, y) := by
  simp [η, isoPointwiseLeftKanExtension]

variable (C V) in
/--
Definition of `ν` / `ν` 的定义

English:
definition ν
  signature: : 𝟙_ V ⟶ (𝟙_ (C ⊛⥤ V)).functor.obj (𝟙_ C)
  body: LawfulDayConvolutionMonoidalCategoryStruct.unitUnit C V (C ⊛⥤ V)

中文:
定义 ν
  签名: : 𝟙_ V ⟶ (𝟙_ (C ⊛⥤ V)).functor.obj (𝟙_ C)
  定义体: LawfulDayConvolutionMonoidalCategoryStruct.unitUnit C V (C ⊛⥤ V)

Depends on / 依赖: LawfulDayConvolutionMonoidalCategoryStruct, LawfulDayConvolutionMonoidalCategoryStruct.unitUnit, unitUnit
-/
def ν : 𝟙_ V ⟶ (𝟙_ (C ⊛⥤ V)).functor.obj (𝟙_ C) :=
  LawfulDayConvolutionMonoidalCategoryStruct.unitUnit C V (C ⊛⥤ V)

set_option backward.defeqAttrib.useBackward true in
variable (C V) in
/-- The reinterpretation of `ν` as a natural transformation. -/
@[simps]
/--
Definition of `νNatTrans` / `νNatTrans` 的定义

English:
definition νNatTrans
  signature: :
  body: ν C V

中文:
定义 νNatTrans
  签名: :
  定义体: ν C V
-/
def νNatTrans :
    Functor.fromPUnit.{0} (𝟙_ V) ⟶
      Functor.fromPUnit.{0} (𝟙_ C) ⋙ (𝟙_ (C ⊛⥤ V)).functor where
  app _ := ν C V

open LawfulDayConvolutionMonoidalCategoryStruct in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝟙_ (C ⊛⥤ V)).functor.IsLeftKanExtension (νNatTrans C V)
  body: .isLeftKanExtension isPointwiseLeftKanExtensionUnitUnit C V (C ⊛⥤ V)

中文:
实例 :
  签名: (𝟙_ (C ⊛⥤ V)).functor.IsLeftKanExtension (ν自然数Trans C V)
  定义体: .isLeftKanExtension isPointwiseLeftKanExtensionUnitUnit C V (C ⊛⥤ V)

Depends on / 依赖: isLeftKanExtension, isPointwiseLeftKanExtensionUnitUnit
-/
instance : (𝟙_ (C ⊛⥤ V)).functor.IsLeftKanExtension (νNatTrans C V) :=
.isLeftKanExtension isPointwiseLeftKanExtensionUnitUnit C V (C ⊛⥤ V)

/--
lemma `unit_hom_ext` / 引理 `unit_hom_ext`

English:
lemma unit_hom_ext
  statement: {F : C ⊛⥤ V} {α β : 𝟙_ (C ⊛⥤ V) ⟶ F}
  proof: by
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension
    (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
  ext
  exact h

中文:
引理 unit_hom_ext
  结论: {F : C ⊛⥤ V} {α β : 𝟙_ (C ⊛⥤ V) ⟶ F}
  证明: by
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension
    (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
  ext
  exact h

Depends on / 依赖: Functor, Functor.hom_ext_of_isLeftKanExtension, functor, hom_ext_of_isLeftKanExtension
-/
lemma unit_hom_ext {F : C ⊛⥤ V} {α β : 𝟙_ (C ⊛⥤ V) ⟶ F}
    (h : ν C V ≫ α.natTrans.app (𝟙_ C) = ν C V ≫ β.natTrans.app (𝟙_ C)) :
    α = β := by
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension
    (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
  ext
  exact h

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `unitDesc` / `unitDesc` 的定义

English:
definition unitDesc
  signature: {F : C ⊛⥤ V} (φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C))
  body: .mk Functor.descOfIsLeftKanExtension (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
    F.functor { app _ := φ }

中文:
定义 unitDesc
  签名: {F : C ⊛⥤ V} (φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C))
  定义体: .mk Functor.descOfIsLeftKanExtension (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
    F.functor { app _ := φ }

Depends on / 依赖: F.functor, Functor, Functor.descOfIsLeftKanExtension, descOfIsLeftKanExtension, functor
-/
def unitDesc {F : C ⊛⥤ V} (φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C)) :
    𝟙_ (C ⊛⥤ V) ⟶ F :=
.mk Functor.descOfIsLeftKanExtension (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
    F.functor { app _ := φ }

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `ν_comp_unitDesc` / 引理 `ν_comp_unitDesc`

English:
lemma ν_comp_unitDesc
  given: {F : C ⊛⥤ V} (φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C))
  proof: Functor.descOfIsLeftKanExtension_fac_app (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
    F.functor { app _ := φ } default

中文:
引理 ν_comp_unitDesc
  条件: {F : C ⊛⥤ V} (φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C))
  证明: Functor.descOfIsLeftKanExtension_fac_app (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
    F.functor { app _ := φ } default

Depends on / 依赖: F.functor, Functor, Functor.descOfIsLeftKanExtension_fac_app, descOfIsLeftKanExtension_fac_app, functor
-/
lemma ν_comp_unitDesc {F : C ⊛⥤ V} (φ : 𝟙_ V ⟶ F.functor.obj (𝟙_ C)) :
    ν C V ≫ (unitDesc φ).natTrans.app (𝟙_ C) = φ :=
  Functor.descOfIsLeftKanExtension_fac_app (𝟙_ (C ⊛⥤ V)).functor (νNatTrans C V)
    F.functor { app _ := φ } default

end DayFunctor

end

end CategoryTheory.MonoidalCategory
