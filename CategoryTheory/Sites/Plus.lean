/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf

/-!

# The plus construction for presheaves.

This file contains the construction of `P⁺`, for a presheaf `P : Cᵒᵖ ⥤ D`
where `C` is endowed with a Grothendieck topology `J`.

See <https://stacks.math.columbia.edu/tag/00W1> for details.

-/

@[expose] public section


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w' w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type w} [Category.{w'} D]

noncomputable section

variable [forall (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
variable (P : Cᵒᵖ ⥤ D)

set_option backward.isDefEq.respectTransparency false in
/-- The diagram whose colimit defines the values of `plus`. -/
@[simps]
/--
Definition of `diagram` / `diagram` 的定义

English:
definition diagram
  signature: (X : C)
  body: multiequalizer (S.unop.index P)
  map {S _} f :=
    Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) (I.map f.unop))
      (fun I => Multiequalizer.condition (S.unop.index P) (Cover.Relation.mk' (I.r.map f.unop)))

中文:
定义 diagram
  签名: (X : C)
  定义体: multiequalizer (S.unop.index P)
  map {S _} f :=
    Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) (I.map f.unop))
      (fun I => Multiequalizer.condition (S.unop.index P) (Cover.Relation.mk' (I.r.map f.unop)))

Depends on / 依赖: DecidableRel, G.deleteEdges, G.incidenceSet, S.unop.index, deleteEdges, incidenceSet, multiequalizer
-/
def diagram (X : C) : (J.Cover X)ᵒᵖ ⥤ D where
  obj S := multiequalizer (S.unop.index P)
  map {S _} f :=
    Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) (I.map f.unop))
      (fun I => Multiequalizer.condition (S.unop.index P) (Cover.Relation.mk' (I.r.map f.unop)))

set_option backward.isDefEq.respectTransparency false in
/-- A helper definition used to define the morphisms for `plus`. -/
@[simps]
/--
Definition of `diagramPullback` / `diagramPullback` 的定义

English:
definition diagramPullback
  signature: {X Y : C} (f : X ⟶ Y)
  body: Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) I.base) fun I =>
      Multiequalizer.condition (S.unop.index P) (Cover.Relation.mk' I.r.base)
  naturality S T f := Multiequalizer.hom_ext _ _ _ (fun I => by simp; rfl)

中文:
定义 diagramPullback
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) I.base) fun I =>
      Multiequalizer.condition (S.unop.index P) (Cover.Relation.mk' I.r.base)
  naturality S T f := Multiequalizer.hom_ext _ _ _ (fun I => by simp; rfl)

Depends on / 依赖: Cover.Relation.mk, I.base, I.r.base, Multiequalizer, Multiequalizer.condition, Multiequalizer.hom_ext, Multiequalizer.lift, Relation, S.unop.index, condition, hom_ext, naturality
-/
def diagramPullback {X Y : C} (f : X ⟶ Y) : J.diagram P Y ⟶ (J.pullback f).op ⋙ J.diagram P X where
  app S :=
    Multiequalizer.lift _ _ (fun I => Multiequalizer.ι (S.unop.index P) I.base) fun I =>
      Multiequalizer.condition (S.unop.index P) (Cover.Relation.mk' I.r.base)
  naturality S T f := Multiequalizer.hom_ext _ _ _ (fun I => by simp; rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation `P ⟶ Q` induces a natural transformation
between diagrams whose colimits define the values of `plus`. -/
@[simps]
/--
Definition of `diagramNatTrans` / `diagramNatTrans` 的定义

English:
definition diagramNatTrans
  signature: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C)
  body: Multiequalizer.lift _ _ (fun _ => Multiequalizer.ι _ _ ≫ η.app _) (fun i => by
      erw [Category.assoc, Category.assoc, ← η.naturality, ← η.naturality,
        Multiequalizer.condition_assoc]
      rfl)

中文:
定义 diagram自然数Trans
  签名: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C)
  定义体: Multiequalizer.lift _ _ (fun _ => Multiequalizer.ι _ _ ≫ η.app _) (fun i => by
      erw [Category.assoc, Category.assoc, ← η.naturality, ← η.naturality,
        Multiequalizer.condition_assoc]
      rfl)

Depends on / 依赖: Category, Category.assoc, Multiequalizer, Multiequalizer.condition_assoc, Multiequalizer.lift, condition_assoc, naturality
-/
def diagramNatTrans {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (X : C) : J.diagram P X ⟶ J.diagram Q X where
  app W :=
    Multiequalizer.lift _ _ (fun _ => Multiequalizer.ι _ _ ≫ η.app _) (fun i => by
      erw [Category.assoc, Category.assoc, ← η.naturality, ← η.naturality,
        Multiequalizer.condition_assoc]
      rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `diagramNatTrans_id` / 定理 `diagramNatTrans_id`

English:
theorem diagramNatTrans_id
  given: (X : C) (P : Cᵒᵖ ⥤ D)
  proof: by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

中文:
定理 diagram自然数Trans_id
  条件: (X : C) (P : Cᵒᵖ ⥤ D)
  证明: by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

Depends on / 依赖: Multiequalizer, Multiequalizer.hom_ext, hom_ext
-/
theorem diagramNatTrans_id (X : C) (P : Cᵒᵖ ⥤ D) :
    J.diagramNatTrans (𝟙 P) X = 𝟙 (J.diagram P X) := by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `diagramNatTrans_zero` / 定理 `diagramNatTrans_zero`

English:
theorem diagramNatTrans_zero
  given: [Preadditive D] (X : C) (P Q : Cᵒᵖ ⥤ D)
  proof: by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

中文:
定理 diagram自然数Trans_zero
  条件: [预加性 D] (X : C) (P Q : Cᵒᵖ ⥤ D)
  证明: by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

Depends on / 依赖: Multiequalizer, Multiequalizer.hom_ext, hom_ext
-/
theorem diagramNatTrans_zero [Preadditive D] (X : C) (P Q : Cᵒᵖ ⥤ D) :
    J.diagramNatTrans (0 : P ⟶ Q) X = 0 := by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `diagramNatTrans_comp` / 定理 `diagramNatTrans_comp`

English:
theorem diagramNatTrans_comp
  given: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (X : C)
  proof: by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

中文:
定理 diagram自然数Trans_comp
  条件: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (X : C)
  证明: by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

Depends on / 依赖: Multiequalizer, Multiequalizer.hom_ext, hom_ext
-/
theorem diagramNatTrans_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (X : C) :
    J.diagramNatTrans (η ≫ γ) X = J.diagramNatTrans η X ≫ J.diagramNatTrans γ X := by
  ext : 2
  refine Multiequalizer.hom_ext _ _ _ (fun i => ?_)
  simp

variable (D) in
/-- `J.diagram P`, as a functor in `P`. -/
@[simps]
/--
Definition of `diagramFunctor` / `diagramFunctor` 的定义

English:
definition diagramFunctor
  signature: (X : C)
  body: J.diagram P X
  map η := J.diagramNatTrans η X

中文:
定义 diagramFunctor
  签名: (X : C)
  定义体: J.diagram P X
  map η := J.diagramNatTrans η X

Depends on / 依赖: J.diagram, diagram
-/
def diagramFunctor (X : C) : (Cᵒᵖ ⥤ D) ⥤ (J.Cover X)ᵒᵖ ⥤ D where
  obj P := J.diagram P X
  map η := J.diagramNatTrans η X

variable [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `plusObj` / `plusObj` 的定义

English:
definition plusObj
  signature: : Cᵒᵖ ⥤ D where
  body: colimit (J.diagram P X.unop)
  map f := colimMap (J.diagramPullback P f.unop) ≫ colimit.pre _ _
  map_id := by
    intro X
    refine colimit.hom_ext (fun S => ?_)
    dsimp
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.comp_id]
    let e := S.unop.pullbackId
    dsim

中文:
定义 plusObj
  签名: : Cᵒᵖ ⥤ D where
  定义体: colimit (J.diagram P X.unop)
  map f := colimMap (J.diagramPullback P f.unop) ≫ colimit.pre _ _
  map_id := by
    intro X
    refine colimit.hom_ext (fun S => ?_)
    dsimp
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.comp_id]
    let e := S.unop.pullbackId
    dsim

Depends on / 依赖: J.diagram, X.unop, colimit, diagram
-/
def plusObj : Cᵒᵖ ⥤ D where
  obj X := colimit (J.diagram P X.unop)
  map f := colimMap (J.diagramPullback P f.unop) ≫ colimit.pre _ _
  map_id := by
    intro X
    refine colimit.hom_ext (fun S => ?_)
    dsimp
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.comp_id]
    let e := S.unop.pullbackId
    dsimp only [Functor.op, pullback_obj]
    rw [← colimit.w _ e.inv.op]; rw [← Category.assoc]
    convert! Category.id_comp (colimit.ι (diagram J P (unop X)) S)
    refine Multiequalizer.hom_ext _ _ _ (fun I => ?_)
    dsimp
    simp only [Multiequalizer.lift_ι, Category.id_comp, Category.assoc]
    dsimp [Cover.Arrow.map, Cover.Arrow.base]
    cases I
    congr
    simp
  map_comp := by
    intro X Y Z f g
    refine colimit.hom_ext (fun S => ?_)
    dsimp
    simp only [diagramPullback_app, colimit.ι_pre_assoc, colimit.ι_pre, ι_colimMap_assoc,
      Category.assoc]
    let e := S.unop.pullbackComp g.unop f.unop
    dsimp only [Functor.op, pullback_obj]
    rw [← colimit.w _ e.inv.op]; rw [← Category.assoc]; rw [← Category.assoc]
    congr 1
    refine Multiequalizer.hom_ext _ _ _ (fun I => ?_)
    dsimp
    simp only [Multiequalizer.lift_ι, Category.assoc]
    cases I
    dsimp only [Cover.Arrow.base, Cover.Arrow.map]
    congr 2
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `plusMap` / `plusMap` 的定义

English:
definition plusMap
  signature: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  body: colimMap (J.diagramNatTrans η X.unop)
  naturality := by
    intro X Y f
    dsimp [plusObj]
    ext
    simp only [diagramPullback_app, ι_colimMap, colimit.ι_pre_assoc, colimit.ι_pre,
      ι_colimMap_assoc, Category.assoc]
    simp_rw [← Category.assoc]
    congr 1
    exact Multiequalizer.hom_ext

中文:
定义 plusMap
  签名: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  定义体: colimMap (J.diagramNatTrans η X.unop)
  naturality := by
    intro X Y f
    dsimp [plusObj]
    ext
    simp only [diagramPullback_app, ι_colimMap, colimit.ι_pre_assoc, colimit.ι_pre,
      ι_colimMap_assoc, Category.assoc]
    simp_rw [← Category.assoc]
    congr 1
    exact Multiequalizer.hom_ext

Depends on / 依赖: J.diagramNatTrans, X.unop, colimMap, diagramNatTrans
-/
def plusMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.plusObj P ⟶ J.plusObj Q where
  app X := colimMap (J.diagramNatTrans η X.unop)
  naturality := by
    intro X Y f
    dsimp [plusObj]
    ext
    simp only [diagramPullback_app, ι_colimMap, colimit.ι_pre_assoc, colimit.ι_pre,
      ι_colimMap_assoc, Category.assoc]
    simp_rw [← Category.assoc]
    congr 1
    exact Multiequalizer.hom_ext _ _ _ (fun I => by simp)

@[simp]
/--
theorem `plusMap_id` / 定理 `plusMap_id`

English:
theorem plusMap_id
  given: (P : Cᵒᵖ ⥤ D)
  statement: J.plusMap (𝟙 P) = 𝟙 _
  proof: by
  ext : 2
  dsimp only [plusMap, plusObj]
  rw [J.diagramNatTrans_id]; rw [NatTrans.id_app]
  ext
  simp

中文:
定理 plusMap_id
  条件: (P : Cᵒᵖ ⥤ D)
  结论: J.plusMap (𝟙 P) = 𝟙 _
  证明: by
  ext : 2
  dsimp only [plusMap, plusObj]
  rw [J.diagramNatTrans_id]; rw [NatTrans.id_app]
  ext
  simp

Depends on / 依赖: J.diagramNatTrans_id, NatTrans, NatTrans.id_app, diagramNatTrans_id, id_app, plusMap, plusObj
-/
theorem plusMap_id (P : Cᵒᵖ ⥤ D) : J.plusMap (𝟙 P) = 𝟙 _ := by
  ext : 2
  dsimp only [plusMap, plusObj]
  rw [J.diagramNatTrans_id]; rw [NatTrans.id_app]
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `plusMap_zero` / 定理 `plusMap_zero`

English:
theorem plusMap_zero
  given: [Preadditive D] (P Q : Cᵒᵖ ⥤ D)
  statement: J.plusMap (0 : P ⟶ Q) = 0
  proof: by
  ext : 2
  refine colimit.hom_ext (fun S => ?_)
  simp [plusMap]

中文:
定理 plusMap_zero
  条件: [预加性 D] (P Q : Cᵒᵖ ⥤ D)
  结论: J.plusMap (0 : P ⟶ Q) = 0
  证明: by
  ext : 2
  refine colimit.hom_ext (fun S => ?_)
  simp [plusMap]

Depends on / 依赖: colimit, colimit.hom_ext, hom_ext, plusMap
-/
theorem plusMap_zero [Preadditive D] (P Q : Cᵒᵖ ⥤ D) : J.plusMap (0 : P ⟶ Q) = 0 := by
  ext : 2
  refine colimit.hom_ext (fun S => ?_)
  simp [plusMap]

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `plusMap_comp` / 定理 `plusMap_comp`

English:
theorem plusMap_comp
  given: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
  proof: by
  ext : 2
  refine colimit.hom_ext (fun S => ?_)
  simp [plusMap, J.diagramNatTrans_comp]

中文:
定理 plusMap_comp
  条件: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
  证明: by
  ext : 2
  refine colimit.hom_ext (fun S => ?_)
  simp [plusMap, J.diagramNatTrans_comp]

Depends on / 依赖: J.diagramNatTrans_comp, colimit, colimit.hom_ext, diagramNatTrans_comp, hom_ext, plusMap
-/
theorem plusMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    J.plusMap (η ≫ γ) = J.plusMap η ≫ J.plusMap γ := by
  ext : 2
  refine colimit.hom_ext (fun S => ?_)
  simp [plusMap, J.diagramNatTrans_comp]

variable (D) in
/-- The plus construction, a functor sending `P` to `J.plusObj P`. -/
@[simps]
/--
Definition of `plusFunctor` / `plusFunctor` 的定义

English:
definition plusFunctor
  signature: : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D where
  body: J.plusObj P
  map η := J.plusMap η

中文:
定义 plusFunctor
  签名: : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D where
  定义体: J.plusObj P
  map η := J.plusMap η

Depends on / 依赖: J.plusObj, plusObj
-/
def plusFunctor : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D where
  obj P := J.plusObj P
  map η := J.plusMap η

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toPlus` / `toPlus` 的定义

English:
definition toPlus
  signature: : P ⟶ J.plusObj P where
  body: Cover.toMultiequalizer (⊤ : J.Cover X.unop) P ≫ colimit.ι (J.diagram P X.unop) (op ⊤)
  naturality := by
    intro X Y f
    dsimp [plusObj]
    delta Cover.toMultiequalizer
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.assoc]
    dsimp only [Functor.op, unop_op]
    

中文:
定义 toPlus
  签名: : P ⟶ J.plusObj P where
  定义体: Cover.toMultiequalizer (⊤ : J.Cover X.unop) P ≫ colimit.ι (J.diagram P X.unop) (op ⊤)
  naturality := by
    intro X Y f
    dsimp [plusObj]
    delta Cover.toMultiequalizer
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.assoc]
    dsimp only [Functor.op, unop_op]
    

Depends on / 依赖: Cover.toMultiequalizer, J.Cover, J.diagram, X.unop, colimit, diagram, toMultiequalizer
-/
def toPlus : P ⟶ J.plusObj P where
  app X := Cover.toMultiequalizer (⊤ : J.Cover X.unop) P ≫ colimit.ι (J.diagram P X.unop) (op ⊤)
  naturality := by
    intro X Y f
    dsimp [plusObj]
    delta Cover.toMultiequalizer
    simp only [diagramPullback_app, colimit.ι_pre, ι_colimMap_assoc, Category.assoc]
    dsimp only [Functor.op, unop_op]
    let e : (J.pullback f.unop).obj ⊤ ⟶ ⊤ := homOfLE (OrderTop.le_top _)
    rw [← colimit.w _ e.op]; rw [← Category.assoc]; rw [← Category.assoc]; rw [← Category.assoc]
    congr 1
    refine Multiequalizer.hom_ext _ _ _ (fun I => ?_)
    simp only [Category.assoc]
    dsimp [Cover.Arrow.base]
    simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `toPlus_naturality` / 定理 `toPlus_naturality`

English:
theorem toPlus_naturality
  given: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  proof: by
  ext
  dsimp [toPlus, plusMap]
  delta Cover.toMultiequalizer
  simp only [ι_colimMap, Category.assoc]
  simp_rw [← Category.assoc]
  congr 1
  exact Multiequalizer.hom_ext _ _ _ (fun I => by simp)

中文:
定理 toPlus_naturality
  条件: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  证明: by
  ext
  dsimp [toPlus, plusMap]
  delta Cover.toMultiequalizer
  simp only [ι_colimMap, Category.assoc]
  simp_rw [← Category.assoc]
  congr 1
  exact Multiequalizer.hom_ext _ _ _ (fun I => by simp)

Depends on / 依赖: Category, Category.assoc, Cover.toMultiequalizer, Multiequalizer, Multiequalizer.hom_ext, hom_ext, plusMap, simp_rw, toMultiequalizer, toPlus
-/
theorem toPlus_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ J.toPlus Q = J.toPlus _ ≫ J.plusMap η := by
  ext
  dsimp [toPlus, plusMap]
  delta Cover.toMultiequalizer
  simp only [ι_colimMap, Category.assoc]
  simp_rw [← Category.assoc]
  congr 1
  exact Multiequalizer.hom_ext _ _ _ (fun I => by simp)

set_option backward.defeqAttrib.useBackward true in
variable (D) in
/-- The natural transformation from the identity functor to `plus`. -/
@[simps]
/--
Definition of `toPlusNatTrans` / `toPlusNatTrans` 的定义

English:
definition toPlusNatTrans
  signature: : 𝟭 (Cᵒᵖ ⥤ D) ⟶ J.plusFunctor D where
  body: J.toPlus P

中文:
定义 toPlus自然数Trans
  签名: : 𝟭 (Cᵒᵖ ⥤ D) ⟶ J.plusFunctor D where
  定义体: J.toPlus P

Depends on / 依赖: J.toPlus, toPlus
-/
def toPlusNatTrans : 𝟭 (Cᵒᵖ ⥤ D) ⟶ J.plusFunctor D where
  app P := J.toPlus P

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺` -/
@[simp]
/--
theorem `plusMap_toPlus` / 定理 `plusMap_toPlus`

English:
theorem plusMap_toPlus
  statement: J.plusMap (J.toPlus P) = J.toPlus (J.plusObj P)
  proof: by
  ext X : 2
  refine colimit.hom_ext (fun S => ?_)
  dsimp only [plusMap, toPlus]
  let e : S.unop ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [ι_colimMap]; rw [← colimit.w _ e.op]; rw [← Category.assoc]; rw [← Category.assoc]
  congr 1
  refine Multiequalizer.hom_ext _ _ _ (fun I => ?_)
  erw [Multi

中文:
定理 plusMap_toPlus
  结论: J.plusMap (J.toPlus P) = J.toPlus (J.plusObj P)
  证明: by
  ext X : 2
  refine colimit.hom_ext (fun S => ?_)
  dsimp only [plusMap, toPlus]
  let e : S.unop ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [ι_colimMap]; rw [← colimit.w _ e.op]; rw [← Category.assoc]; rw [← Category.assoc]
  congr 1
  refine Multiequalizer.hom_ext _ _ _ (fun I => ?_)
  erw [Multi

Depends on / 依赖: Category, Category.assoc, I.map, J.pullback, Multiequalizer, Multiequalizer.hom_ext, Multiequalizer.lift_, Multifork, Multifork.of, OrderTop, OrderTop.le_top, S.unop, colimit, colimit.hom_ext, colimit.w, diagram_map, e.op, ee.op, homOfLE, hom_ext
-/
theorem plusMap_toPlus : J.plusMap (J.toPlus P) = J.toPlus (J.plusObj P) := by
  ext X : 2
  refine colimit.hom_ext (fun S => ?_)
  dsimp only [plusMap, toPlus]
  let e : S.unop ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  rw [ι_colimMap]; rw [← colimit.w _ e.op]; rw [← Category.assoc]; rw [← Category.assoc]
  congr 1
  refine Multiequalizer.hom_ext _ _ _ (fun I => ?_)
  erw [Multiequalizer.lift_ι]
  simp only [unop_op, op_unop, diagram_map, Category.assoc, limit.lift_π,
    Multifork.ofι_π_app]
  let ee : (J.pullback (I.map e).f).obj S.unop ⟶ ⊤ := homOfLE (OrderTop.le_top _)
  erw [← colimit.w _ ee.op, ι_colimMap_assoc, colimit.ι_pre, diagramPullback_app,
    ← Category.assoc, ← Category.assoc]
  congr 1
  refine Multiequalizer.hom_ext _ _ _ (fun II => ?_)
  convert!
    Multiequalizer.condition (S.unop.index P)
      { fst := I, snd := II.base, r.Z := II.Y, r.g₁ := II.f, r.g₂ := 𝟙 II.Y } using 1
  all_goals simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isIso_toPlus_of_isSheaf` / 定理 `isIso_toPlus_of_isSheaf`

English:
theorem isIso_toPlus_of_isSheaf
  given: (hP : Presheaf.IsSheaf J P)
  statement: IsIso (J.toPlus P)
  proof: by
  rw [Presheaf.isSheaf_iff_multiequalizer] at hP
  suffices forall X, IsIso ((J.toPlus P).app X) from NatIso.isIso_of_isIso_app _
  intro X
  refine IsIso.comp_isIso' inferInstance ?_
  suffices forall (S T : (J.Cover X.unop)ᵒᵖ) (f : S ⟶ T), IsIso ((J.diagram P X.unop).map f) from
    isIso_ι_of_

中文:
定理 isIso_toPlus_of_isSheaf
  条件: (hP : 预层.是层 J P)
  结论: 是同构 (J.toPlus P)
  证明: by
  rw [Presheaf.isSheaf_iff_multiequalizer] at hP
  suffices forall X, IsIso ((J.toPlus P).app X) from NatIso.isIso_of_isIso_app _
  intro X
  refine IsIso.comp_isIso' inferInstance ?_
  suffices forall (S T : (J.Cover X.unop)ᵒᵖ) (f : S ⟶ T), IsIso ((J.diagram P X.unop).map f) from
    isIso_ι_of_

Depends on / 依赖: IsIso.comp_isIso, J.Cover, J.diagram, J.toPlus, Multiequalizer, Multiequalizer.hom_ext, NatIso, NatIso.isIso_of_isIso_app, Presheaf, Presheaf.isSheaf_iff_multiequalizer, S.unop.toMultiequalizer, T.unop.toMultiequalizer, X.unop, comp_isIso, diagram, hom_ext, initialOpOfTerminal, isIso_of_isIso_app, isSheaf_iff_multiequalizer, isTerminalTop
-/
theorem isIso_toPlus_of_isSheaf (hP : Presheaf.IsSheaf J P) : IsIso (J.toPlus P) := by
  rw [Presheaf.isSheaf_iff_multiequalizer] at hP
  suffices forall X, IsIso ((J.toPlus P).app X) from NatIso.isIso_of_isIso_app _
  intro X
  refine IsIso.comp_isIso' inferInstance ?_
  suffices forall (S T : (J.Cover X.unop)ᵒᵖ) (f : S ⟶ T), IsIso ((J.diagram P X.unop).map f) from
    isIso_ι_of_isInitial (initialOpOfTerminal isTerminalTop) _
  intro S T e
  have : S.unop.toMultiequalizer P ≫ (J.diagram P X.unop).map e = T.unop.toMultiequalizer P :=
    Multiequalizer.hom_ext _ _ _ (fun II => by simp)
  exact IsIso.of_isIso_fac_left this

/--
Definition of `isoToPlus` / `isoToPlus` 的定义

English:
definition isoToPlus
  signature: (hP : Presheaf.IsSheaf J P)
  body: letI := isIso_toPlus_of_isSheaf J P hP
  asIso (J.toPlus P)

@[simp]

中文:
定义 isoToPlus
  签名: (hP : 预层.是层 J P)
  定义体: letI := isIso_toPlus_of_isSheaf J P hP
  asIso (J.toPlus P)

@[simp]

Depends on / 依赖: J.toPlus, isIso_toPlus_of_isSheaf, toPlus
-/
def isoToPlus (hP : Presheaf.IsSheaf J P) : P ≅ J.plusObj P :=
  letI := isIso_toPlus_of_isSheaf J P hP
  asIso (J.toPlus P)

@[simp]
/--
theorem `isoToPlus_hom` / 定理 `isoToPlus_hom`

English:
theorem isoToPlus_hom
  given: (hP : Presheaf.IsSheaf J P)
  statement: (J.isoToPlus P hP).hom = J.toPlus P
  proof: rfl

中文:
定理 isoToPlus_hom
  条件: (hP : 预层.是层 J P)
  结论: (J.isoToPlus P hP).hom = J.toPlus P
  证明: rfl
-/
theorem isoToPlus_hom (hP : Presheaf.IsSheaf J P) : (J.isoToPlus P hP).hom = J.toPlus P :=
  rfl

/--
Definition of `plusLift` / `plusLift` 的定义

English:
definition plusLift
  signature: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  body: J.plusMap η ≫ (J.isoToPlus Q hQ).inv

@[reassoc (attr := simp)]

中文:
定义 plusLift
  签名: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : 预层.是层 J Q)
  定义体: J.plusMap η ≫ (J.isoToPlus Q hQ).inv

@[reassoc (attr := simp)]

Depends on / 依赖: J.isoToPlus, J.plusMap, isoToPlus, plusMap
-/
def plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.plusObj P ⟶ Q :=
  J.plusMap η ≫ (J.isoToPlus Q hQ).inv

@[reassoc (attr := simp)]
/--
theorem `toPlus_plusLift` / 定理 `toPlus_plusLift`

English:
theorem toPlus_plusLift
  given: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  proof: by
  dsimp [plusLift]
  rw [← Category.assoc]
  rw [Iso.comp_inv_eq]
  dsimp only [isoToPlus, asIso]
  rw [toPlus_naturality]

中文:
定理 toPlus_plusLift
  条件: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : 预层.是层 J Q)
  证明: by
  dsimp [plusLift]
  rw [← Category.assoc]
  rw [Iso.comp_inv_eq]
  dsimp only [isoToPlus, asIso]
  rw [toPlus_naturality]

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, comp_inv_eq, isoToPlus, plusLift, toPlus_naturality
-/
theorem toPlus_plusLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.toPlus P ≫ J.plusLift η hQ = η := by
  dsimp [plusLift]
  rw [← Category.assoc]
  rw [Iso.comp_inv_eq]
  dsimp only [isoToPlus, asIso]
  rw [toPlus_naturality]

/--
theorem `plusLift_unique` / 定理 `plusLift_unique`

English:
theorem plusLift_unique
  statement: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  proof: by
  dsimp only [plusLift]
  rw [Iso.eq_comp_inv]; rw [← hγ]; rw [plusMap_comp]
  simp

中文:
定理 plusLift_unique
  结论: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : 预层.是层 J Q)
  证明: by
  dsimp only [plusLift]
  rw [Iso.eq_comp_inv]; rw [← hγ]; rw [plusMap_comp]
  simp

Depends on / 依赖: Iso.eq_comp_inv, eq_comp_inv, plusLift, plusMap_comp
-/
theorem plusLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : J.plusObj P ⟶ Q) (hγ : J.toPlus P ≫ γ = η) : γ = J.plusLift η hQ := by
  dsimp only [plusLift]
  rw [Iso.eq_comp_inv]; rw [← hγ]; rw [plusMap_comp]
  simp

/--
theorem `plus_hom_ext` / 定理 `plus_hom_ext`

English:
theorem plus_hom_ext
  statement: {P Q : Cᵒᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  proof: by
  have : γ = J.plusLift (J.toPlus P ≫ γ) hQ := by
    apply plusLift_unique
    rfl
  rw [this]
  apply plusLift_unique
  exact h

@[simp]

中文:
定理 plus_hom_ext
  结论: {P Q : Cᵒᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q) (hQ : 预层.是层 J Q)
  证明: by
  have : γ = J.plusLift (J.toPlus P ≫ γ) hQ := by
    apply plusLift_unique
    rfl
  rw [this]
  apply plusLift_unique
  exact h

@[simp]

Depends on / 依赖: J.plusLift, J.toPlus, plusLift, plusLift_unique, toPlus
-/
theorem plus_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : J.toPlus P ≫ η = J.toPlus P ≫ γ) : η = γ := by
  have : γ = J.plusLift (J.toPlus P ≫ γ) hQ := by
    apply plusLift_unique
    rfl
  rw [this]
  apply plusLift_unique
  exact h

@[simp]
/--
theorem `isoToPlus_inv` / 定理 `isoToPlus_inv`

English:
theorem isoToPlus_inv
  given: (hP : Presheaf.IsSheaf J P)
  proof: by
  apply J.plusLift_unique
  rw [Iso.comp_inv_eq]; rw [Category.id_comp]
  rfl

@[simp]

中文:
定理 isoToPlus_inv
  条件: (hP : 预层.是层 J P)
  证明: by
  apply J.plusLift_unique
  rw [Iso.comp_inv_eq]; rw [Category.id_comp]
  rfl

@[simp]

Depends on / 依赖: Category, Category.id_comp, Iso.comp_inv_eq, J.plusLift_unique, comp_inv_eq, id_comp, plusLift_unique
-/
theorem isoToPlus_inv (hP : Presheaf.IsSheaf J P) :
    (J.isoToPlus P hP).inv = J.plusLift (𝟙 _) hP := by
  apply J.plusLift_unique
  rw [Iso.comp_inv_eq]; rw [Category.id_comp]
  rfl

@[simp]
/--
theorem `plusMap_plusLift` / 定理 `plusMap_plusLift`

English:
theorem plusMap_plusLift
  given: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.IsSheaf J R)
  proof: by
  apply J.plusLift_unique
  rw [← Category.assoc]; rw [← J.toPlus_naturality]; rw [Category.assoc]; rw [J.toPlus_plusLift]

中文:
定理 plusMap_plusLift
  条件: {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : 预层.是层 J R)
  证明: by
  apply J.plusLift_unique
  rw [← Category.assoc]; rw [← J.toPlus_naturality]; rw [Category.assoc]; rw [J.toPlus_plusLift]

Depends on / 依赖: Category, Category.assoc, J.plusLift_unique, J.toPlus_naturality, J.toPlus_plusLift, plusLift_unique, toPlus_naturality, toPlus_plusLift
-/
theorem plusMap_plusLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) (hR : Presheaf.IsSheaf J R) :
    J.plusMap η ≫ J.plusLift γ hR = J.plusLift (η ≫ γ) hR := by
  apply J.plusLift_unique
  rw [← Category.assoc]; rw [← J.toPlus_naturality]; rw [Category.assoc]; rw [J.toPlus_plusLift]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `plusFunctor_preservesZeroMorphisms` / 实例 `plusFunctor_preservesZeroMorphisms`

English:
instance plusFunctor_preservesZeroMorphisms
  signature: [Preadditive D]
  body: by
    ext
    dsimp
    rw [J.plusMap_zero]; rw [NatTrans.app_zero]

中文:
实例 plusFunctor_preservesZeroMorphisms
  签名: [预加性 D]
  定义体: by
    ext
    dsimp
    rw [J.plusMap_zero]; rw [NatTrans.app_zero]

Depends on / 依赖: J.plusMap_zero, NatTrans, NatTrans.app_zero, app_zero, plusMap_zero
-/
instance plusFunctor_preservesZeroMorphisms [Preadditive D] :
    (plusFunctor J D).PreservesZeroMorphisms where
  map_zero F G := by
    ext
    dsimp
    rw [J.plusMap_zero]; rw [NatTrans.app_zero]

end

end CategoryTheory.GrothendieckTopology
