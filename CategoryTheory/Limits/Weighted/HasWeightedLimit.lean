/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Yun Liu, Christian Merten, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Weighted limits

In this file, we define weighted limits (in the non enriched case).
Given a weight `W : J ⥤ Type w` and a functor `F : J ⥤ C`,
the `W`-weighted limit of `J` is the limit of the functor
`CategoryOfElements.π W ⋙ F : W.Elements ⥤ C`.

## References
* https://ncatlab.org/nlab/show/weighted+limit

-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Limits Opposite

namespace Limits

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]

/--
Definition of `WeightedCone` / `WeightedCone` 的定义

English:
abbreviation WeightedCone
  signature: (W : J ⥤ Type w) (F : J ⥤ C)
  body: Cone (CategoryOfElements.π W ⋙ F)

中文:
缩写 WeightedCone
  签名: (W : J ⥤ Type w) (F : J ⥤ C)
  定义体: Cone (CategoryOfElements.π W ⋙ F)

Depends on / 依赖: CategoryOfElements, CoconePt, Limits, Limits.CoconePt.isCardinalFiltered_pt, Limits.isColimitCocone, PartOrdEmb, coconePointUniqueUpToIso, colimit, colimit.isColimit, forget, isCardinalFiltered, isCardinalFiltered_iff, isCardinalFiltered_pt, isColimit, isColimitCocone, isFiltered_of_isCardinalFiltered, p.diag, p.isColimit.coconePointUniqueUpToIso, p.prop_diag_obj, prop_diag_obj
-/
abbrev WeightedCone (W : J ⥤ Type w) (F : J ⥤ C) :=
  Cone (CategoryOfElements.π W ⋙ F)

/--
Definition of `HasWeightedLimit` / `HasWeightedLimit` 的定义

English:
abbreviation HasWeightedLimit
  signature: (W : J ⥤ Type w) (F : J ⥤ C)
  body: HasLimit (CategoryOfElements.π W ⋙ F)

中文:
缩写 HasWeightedLimit
  签名: (W : J ⥤ Type w) (F : J ⥤ C)
  定义体: HasLimit (CategoryOfElements.π W ⋙ F)

Depends on / 依赖: CategoryOfElements, HasLimit
-/
abbrev HasWeightedLimit (W : J ⥤ Type w) (F : J ⥤ C) : Prop :=
  HasLimit (CategoryOfElements.π W ⋙ F)

namespace WeightedCone

variable {W : J ⥤ Type w} {F : J ⥤ C}

/--
Definition of `π` / `π` 的定义

English:
abbreviation π
  signature: (c : WeightedCone W F) {j : J} (x : W.obj j)
  body: (Cone.π c).app (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]

中文:
缩写 π
  签名: (c : WeightedCone W F) {j : J} (x : W.obj j)
  定义体: (Cone.π c).app (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]
-/
protected abbrev π (c : WeightedCone W F) {j : J} (x : W.obj j) :
    c.pt ⟶ F.obj j :=
  (Cone.π c).app (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]
/--
lemma `w` / 引理 `w`

English:
lemma w
  given: (c : WeightedCone W F) {i j : J} (x : W.obj i) (f : i ⟶ j)
  proof: Cone.w c (CategoryOfElements.homMk (Functor.elementsMk _ _ x)
    (Functor.elementsMk _ _ (W.map f x)) f rfl)

中文:
引理 w
  条件: (c : WeightedCone W F) {i j : J} (x : W.obj i) (f : i ⟶ j)
  证明: Cone.w c (CategoryOfElements.homMk (Functor.elementsMk _ _ x)
    (Functor.elementsMk _ _ (W.map f x)) f rfl)
-/
protected lemma w (c : WeightedCone W F) {i j : J} (x : W.obj i) (f : i ⟶ j) :
    c.π x ≫ F.map f = c.π (W.map f x) :=
  Cone.w c (CategoryOfElements.homMk (Functor.elementsMk _ _ x)
    (Functor.elementsMk _ _ (W.map f x)) f rfl)

variable (pt : C) (π : forall ⦃j : J⦄ (_ : W.obj j), pt ⟶ F.obj j)
  (hπ : forall ⦃j₁ j₂ : J⦄ (x : W.obj j₁) (f : j₁ ⟶ j₂),
    π x ≫ F.map f = π (W.map f x))

set_option backward.defeqAttrib.useBackward true in
/-- Constructor for weighted cones. -/
@[simps pt]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : WeightedCone W F where
  body: pt
  π.app x := π x.snd
  π.naturality x₁ x₂ f := by simpa using (hπ x₁.snd f.val).symm

@[simp]

中文:
定义 mk
  签名: : WeightedCone W F where
  定义体: pt
  π.app x := π x.snd
  π.naturality x₁ x₂ f := by simpa using (hπ x₁.snd f.val).symm

@[simp]
-/
def mk : WeightedCone W F where
  pt := pt
  π.app x := π x.snd
  π.naturality x₁ x₂ f := by simpa using (hπ x₁.snd f.val).symm

@[simp]
/--
lemma `mk_π` / 引理 `mk_π`

English:
lemma mk_π
  given: {j : J} (x : W.obj j)
  proof: rfl

中文:
引理 mk_π
  条件: {j : J} (x : W.obj j)
  证明: rfl
-/
lemma mk_π {j : J} (x : W.obj j) :
    (mk pt π hπ).π x = π x := rfl

/--
Definition of `IsLimit` / `IsLimit` 的定义

English:
abbreviation IsLimit
  signature: (c : WeightedCone W F)
  body: Limits.IsLimit c

中文:
缩写 IsLimit
  签名: (c : WeightedCone W F)
  定义体: Limits.IsLimit c

Depends on / 依赖: J.property, property
-/
protected abbrev IsLimit (c : WeightedCone W F) := Limits.IsLimit c

namespace IsLimit

variable {c : WeightedCone W F} (hc : c.IsLimit) {Z : C}

include hc in
/--
lemma `hasWeightedLimit` / 引理 `hasWeightedLimit`

English:
lemma hasWeightedLimit
  statement: HasWeightedLimit W F
  proof: ⟨_, hc⟩

中文:
引理 hasWeightedLimit
  结论: HasWeightedLimit W F
  证明: ⟨_, hc⟩

Depends on / 依赖: isFiltered_of_isCardinalFiltered
-/
lemma hasWeightedLimit : HasWeightedLimit W F := ⟨_, hc⟩

section

variable
  (π : forall ⦃j : J⦄ (_ : W.obj j), Z ⟶ F.obj j)
  (hπ : forall ⦃j₁ j₂ : J⦄ (x : W.obj j₁) (f : j₁ ⟶ j₂),
    π x ≫ F.map f = π (W.map f x))

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : Z ⟶ c.pt
  body: Limits.IsLimit.lift hc (WeightedCone.mk Z π hπ)

@[reassoc (attr := simp)]

中文:
定义 lift
  签名: : Z ⟶ c.pt
  定义体: Limits.IsLimit.lift hc (WeightedCone.mk Z π hπ)

@[reassoc (attr := simp)]

Depends on / 依赖: IsFiltered, IsFiltered.nonempty, IsLimit, Limits, Limits.IsLimit.lift, WeightedCone, WeightedCone.mk, nonempty
-/
def lift : Z ⟶ c.pt :=
  Limits.IsLimit.lift hc (WeightedCone.mk Z π hπ)

@[reassoc (attr := simp)]
/--
lemma `fac` / 引理 `fac`

English:
lemma fac
  given: {j : J} (x : W.obj j)
  proof: Limits.IsLimit.fac hc (WeightedCone.mk Z π hπ) (Functor.elementsMk _ _ x)

中文:
引理 fac
  条件: {j : J} (x : W.obj j)
  证明: Limits.IsLimit.fac hc (WeightedCone.mk Z π hπ) (Functor.elementsMk _ _ x)

Depends on / 依赖: Functor, Functor.elementsMk, IsLimit, Limits, Limits.IsLimit.fac, WeightedCone, WeightedCone.mk, elementsMk
-/
lemma fac {j : J} (x : W.obj j) :
    hc.lift π hπ ≫ c.π x = π x :=
  Limits.IsLimit.fac hc (WeightedCone.mk Z π hπ) (Functor.elementsMk _ _ x)

end

include hc in
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {f g : Z ⟶ c.pt} (h : forall {j : J} (x : W.obj j), f ≫ c.π x = g ≫ c.π x)
  proof: Limits.IsLimit.hom_ext hc (fun _ => h _)

中文:
引理 hom_ext
  条件: {f g : Z ⟶ c.pt} (h : 对任意 {j : J} (x : W.obj j), f ≫ c.π x = g ≫ c.π x)
  证明: Limits.IsLimit.hom_ext hc (fun _ => h _)

Depends on / 依赖: CardinalDirectedPoset, IsLimit, Limits, Limits.IsLimit.hom_ext, PreservesColimitsOfShape, forget, hom_ext, infer_instance, isFiltered_of_isCardinalFiltered
-/
lemma hom_ext {f g : Z ⟶ c.pt} (h : forall {j : J} (x : W.obj j), f ≫ c.π x = g ≫ c.π x) :
    f = g :=
  Limits.IsLimit.hom_ext hc (fun _ => h _)

end IsLimit

open Opposite in
set_option backward.defeqAttrib.useBackward true in
/-- If the weight is `coyoneda.obj (op j) : J ⥤ Type _`, this is the limit
weighted cone for `F : J ⥤ C` with point `F.obj j`. -/
@[simps]
/--
Definition of `coyoneda` / `coyoneda` 的定义

English:
abbreviation coyoneda
  signature: (F : J ⥤ C) (j : J)
  body: F.obj j
  π.app u := F.map u.snd
  π.naturality _ _ f := by simp [← Functor.map_comp, Category.id_comp, f.prop.symm]

中文:
缩写 coyoneda
  签名: (F : J ⥤ C) (j : J)
  定义体: F.obj j
  π.app u := F.map u.snd
  π.naturality _ _ f := by simp [← Functor.map_comp, Category.id_comp, f.prop.symm]

Depends on / 依赖: isCardinalFiltered_of_hasTerminal
-/
protected abbrev coyoneda (F : J ⥤ C) (j : J) :
    WeightedCone (coyoneda.obj (op j)) F where
  pt := F.obj j
  π.app u := F.map u.snd
  π.naturality _ _ f := by simp [← Functor.map_comp, Category.id_comp, f.prop.symm]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitCoyoneda` / `isLimitCoyoneda` 的定义

English:
definition isLimitCoyoneda
  signature: (F : J ⥤ C) (j : J)
  body: WeightedCone.π s (𝟙 j)
  fac s x := by
    simpa using s.w (CategoryOfElements.homMk (Functor.elementsMk _ j (𝟙 j)) x x.snd (by simp))
  uniq s m hm := by
    simpa using hm (Functor.elementsMk _ j (𝟙 j))

中文:
定义 isLimitCoyoneda
  签名: (F : J ⥤ C) (j : J)
  定义体: WeightedCone.π s (𝟙 j)
  fac s x := by
    simpa using s.w (CategoryOfElements.homMk (Functor.elementsMk _ j (𝟙 j)) x x.snd (by simp))
  uniq s m hm := by
    simpa using hm (Functor.elementsMk _ j (𝟙 j))

Depends on / 依赖: WeightedCone
-/
def isLimitCoyoneda (F : J ⥤ C) (j : J) : (WeightedCone.coyoneda F j).IsLimit where
  lift s := WeightedCone.π s (𝟙 j)
  fac s x := by
    simpa using s.w (CategoryOfElements.homMk (Functor.elementsMk _ j (𝟙 j)) x x.snd (by simp))
  uniq s m hm := by
    simpa using hm (Functor.elementsMk _ j (𝟙 j))

end WeightedCone

end Limits

namespace Functor

section

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  (W W' W'' : J ⥤ Type w) (g : W ⟶ W') (g' : W' ⟶ W'') (F : J ⥤ C)
  [HasWeightedLimit W F] [HasWeightedLimit W' F] [HasWeightedLimit W'' F]

/--
Definition of `weightedLimObjObj` / `weightedLimObjObj` 的定义

English:
definition weightedLimObjObj
  signature: : C
  body: limit (CategoryOfElements.π W ⋙ F)

中文:
定义 weightedLimObjObj
  签名: : C
  定义体: limit (CategoryOfElements.π W ⋙ F)

Depends on / 依赖: CategoryOfElements
-/
noncomputable def weightedLimObjObj : C :=
  limit (CategoryOfElements.π W ⋙ F)

/-- The projections from the weighted limit. -/
@[no_expose]
/--
Definition of `weightedLimObjObjπ` / `weightedLimObjObjπ` 的定义

English:
definition weightedLimObjObjπ
  signature: ⦃j
  body: limit.π (CategoryOfElements.π W ⋙ F) (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]

中文:
定义 weightedLimObjObjπ
  签名: ⦃j
  定义体: limit.π (CategoryOfElements.π W ⋙ F) (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]

Depends on / 依赖: CategoryOfElements, Functor, Functor.elementsMk, elementsMk
-/
noncomputable def weightedLimObjObjπ ⦃j : J⦄ (x : W.obj j) :
    W.weightedLimObjObj F ⟶ F.obj j :=
  limit.π (CategoryOfElements.π W ⋙ F) (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]
/--
lemma `weightedLimObjObj_w` / 引理 `weightedLimObjObj_w`

English:
lemma weightedLimObjObj_w
  given: ⦃j₁ j₂
  statement: J⦄ (x : W.obj j₁)
  proof: limit.w (CategoryOfElements.π W ⋙ F)
    (CategoryOfElements.homMk (Functor.elementsMk _ _ x) (Functor.elementsMk _ _
      (W.map f x)) f rfl)

中文:
引理 weightedLimObjObj_w
  条件: ⦃j₁ j₂
  结论: J⦄ (x : W.obj j₁)
  证明: limit.w (CategoryOfElements.π W ⋙ F)
    (CategoryOfElements.homMk (Functor.elementsMk _ _ x) (Functor.elementsMk _ _
      (W.map f x)) f rfl)

Depends on / 依赖: CategoryOfElements, CategoryOfElements.homMk, Functor, Functor.elementsMk, W.map, elementsMk, limit.w
-/
lemma weightedLimObjObj_w ⦃j₁ j₂ : J⦄ (x : W.obj j₁)
    (f : j₁ ⟶ j₂) :
    W.weightedLimObjObjπ F x ≫ F.map f =
      W.weightedLimObjObjπ F (W.map f x) :=
  limit.w (CategoryOfElements.π W ⋙ F)
    (CategoryOfElements.homMk (Functor.elementsMk _ _ x) (Functor.elementsMk _ _
      (W.map f x)) f rfl)

/--
Definition of `weightedLimCone` / `weightedLimCone` 的定义

English:
abbreviation weightedLimCone
  signature: :
  body: WeightedCone.mk (W.weightedLimObjObj F)
    (fun j x => W.weightedLimObjObjπ F x)
    (fun j₁ j₂ x f => by simp)

中文:
缩写 weightedLimCone
  签名: :
  定义体: WeightedCone.mk (W.weightedLimObjObj F)
    (fun j x => W.weightedLimObjObjπ F x)
    (fun j₁ j₂ x f => by simp)

Depends on / 依赖: W.weightedLimObjObj, WeightedCone, WeightedCone.mk, weightedLimObjObj
-/
noncomputable abbrev weightedLimCone :
    WeightedCone W F :=
  WeightedCone.mk (W.weightedLimObjObj F)
    (fun j x => W.weightedLimObjObjπ F x)
    (fun j₁ j₂ x f => by simp)

/-- The weighted cone `W.weightedLimCone F` is a limit. -/
@[no_expose]
/--
Definition of `isLimitWeightedLimCone` / `isLimitWeightedLimCone` 的定义

English:
definition isLimitWeightedLimCone
  signature: :
  body: limit.isLimit _

@[reassoc, simp] -- `simp` can prove the `reassoc` version

中文:
定义 isLimitWeightedLimCone
  签名: :
  定义体: limit.isLimit _

@[reassoc, simp] -- `simp` can prove the `reassoc` version

Depends on / 依赖: isLimit, limit.isLimit
-/
noncomputable def isLimitWeightedLimCone :
    (W.weightedLimCone F).IsLimit :=
  limit.isLimit _

@[reassoc, simp] -- `simp` can prove the `reassoc` version
/--
lemma `isLimitWeightedLimCone_fac` / 引理 `isLimitWeightedLimCone_fac`

English:
lemma isLimitWeightedLimCone_fac
  given: {Z} (π) (hπ) ⦃j
  statement: J⦄ (x : W.obj j) :
  proof: (W.isLimitWeightedLimCone F).fac ..

中文:
引理 isLimitWeightedLimCone_fac
  条件: {Z} (π) (hπ) ⦃j
  结论: J⦄ (x : W.obj j) :
  证明: (W.isLimitWeightedLimCone F).fac ..

Depends on / 依赖: W.weightedLimObjObj
-/
lemma isLimitWeightedLimCone_fac {Z} (π) (hπ) ⦃j : J⦄ (x : W.obj j) :
    (W.isLimitWeightedLimCone F).lift (Z := Z) π hπ ≫ W.weightedLimObjObjπ F x = π x :=
  (W.isLimitWeightedLimCone F).fac ..

variable {W F} in
@[ext]
/--
lemma `weightedLimObjObj.hom_ext` / 引理 `weightedLimObjObj.hom_ext`

English:
lemma weightedLimObjObj.hom_ext
  statement: {Z : C} {f g : Z ⟶ W.weightedLimObjObj F}
  proof: (W.isLimitWeightedLimCone F).hom_ext h

中文:
引理 weightedLimObjObj.hom_ext
  结论: {Z : C} {f g : Z ⟶ W.weightedLimObjObj F}
  证明: (W.isLimitWeightedLimCone F).hom_ext h

Depends on / 依赖: W.isLimitWeightedLimCone, hom_ext, isLimitWeightedLimCone
-/
lemma weightedLimObjObj.hom_ext {Z : C} {f g : Z ⟶ W.weightedLimObjObj F}
    (h : forall {j : J} (x : W.obj j),
      f ≫ W.weightedLimObjObjπ F x = g ≫ W.weightedLimObjObjπ F x) :
    f = g :=
  (W.isLimitWeightedLimCone F).hom_ext h

/-- Functoriality of the weighted limits with fixed weight `W : J ⥤ Type w`
with respect to the functor in `J ⥤ C`. -/
@[no_expose]
/--
Definition of `weightedLimObjMap` / `weightedLimObjMap` 的定义

English:
definition weightedLimObjMap
  signature: {F₁ F₂ : J ⥤ C}
  body: limMap (whiskerLeft _ f)

@[reassoc (attr := simp)]

中文:
定义 weightedLimObjMap
  签名: {F₁ F₂ : J ⥤ C}
  定义体: limMap (whiskerLeft _ f)

@[reassoc (attr := simp)]

Depends on / 依赖: IsTerminal, IsTerminal.hasTerminal, IsTerminal.ofUniqueHom, Subtype, Subtype.mk_le_mk, hasTerminal, homOfLE, le_top, limMap, mk_le_mk, ofUniqueHom, whiskerLeft
-/
noncomputable def weightedLimObjMap {F₁ F₂ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] (f : F₁ ⟶ F₂) :
    W.weightedLimObjObj F₁ ⟶ W.weightedLimObjObj F₂ :=
  limMap (whiskerLeft _ f)

@[reassoc (attr := simp)]
/--
lemma `weightedLimObjMap_π` / 引理 `weightedLimObjMap_π`

English:
lemma weightedLimObjMap_π
  statement: {F₁ F₂ : J ⥤ C}
  proof: limit.lift_π ..

@[simp]

中文:
引理 weightedLimObjMap_π
  结论: {F₁ F₂ : J ⥤ C}
  证明: limit.lift_π ..

@[simp]

Depends on / 依赖: isCardinalFiltered_of_hasTerminal, limit.lift_
-/
lemma weightedLimObjMap_π {F₁ F₂ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] (f : F₁ ⟶ F₂)
    ⦃j : J⦄ (x : W.obj j) :
    W.weightedLimObjMap f ≫ W.weightedLimObjObjπ F₂ x =
      W.weightedLimObjObjπ F₁ x ≫ f.app j :=
  limit.lift_π ..

@[simp]
/--
lemma `weightedLimObjMap_id` / 引理 `weightedLimObjMap_id`

English:
lemma weightedLimObjMap_id
  given: (F : J ⥤ C) [HasWeightedLimit W F]
  proof: by
  cat_disch

@[reassoc]

中文:
引理 weightedLimObjMap_id
  条件: (F : J ⥤ C) [HasWeightedLimit W F]
  证明: by
  cat_disch

@[reassoc]

Depends on / 依赖: cat_disch
-/
lemma weightedLimObjMap_id (F : J ⥤ C) [HasWeightedLimit W F] :
    W.weightedLimObjMap (𝟙 F) = 𝟙 _ := by
  cat_disch

@[reassoc]
/--
lemma `weightedLimObjMap_comp` / 引理 `weightedLimObjMap_comp`

English:
lemma weightedLimObjMap_comp
  statement: {F₁ F₂ F₃ : J ⥤ C}
  proof: by
  cat_disch

中文:
引理 weightedLimObjMap_comp
  结论: {F₁ F₂ F₃ : J ⥤ C}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma weightedLimObjMap_comp {F₁ F₂ F₃ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] [HasWeightedLimit W F₃]
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    W.weightedLimObjMap (f ≫ g) = W.weightedLimObjMap f ≫ W.weightedLimObjMap g := by
  cat_disch

section

variable {W W' W''}

/--
Definition of `weightedLimFlipObjMap` / `weightedLimFlipObjMap` 的定义

English:
definition weightedLimFlipObjMap
  signature: :
  body: (W.isLimitWeightedLimCone F).lift
    (fun j x => W'.weightedLimObjObjπ F (g.app j x)) (by simp)

@[reassoc (attr := simp)]

中文:
定义 weightedLimFlipObjMap
  签名: :
  定义体: (W.isLimitWeightedLimCone F).lift
    (fun j x => W'.weightedLimObjObjπ F (g.app j x)) (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: W.isLimitWeightedLimCone, g.app, isLimitWeightedLimCone
-/
noncomputable def weightedLimFlipObjMap :
    W'.weightedLimObjObj F ⟶ W.weightedLimObjObj F :=
  (W.isLimitWeightedLimCone F).lift
    (fun j x => W'.weightedLimObjObjπ F (g.app j x)) (by simp)

@[reassoc (attr := simp)]
/--
lemma `weightedLimObjObjMap_π` / 引理 `weightedLimObjObjMap_π`

English:
lemma weightedLimObjObjMap_π
  given: ⦃j
  statement: J⦄ (x : W.obj j) :
  proof: (W.isLimitWeightedLimCone F).fac ..

@[simp]

中文:
引理 weightedLimObjObjMap_π
  条件: ⦃j
  结论: J⦄ (x : W.obj j) :
  证明: (W.isLimitWeightedLimCone F).fac ..

@[simp]

Depends on / 依赖: W.isLimitWeightedLimCone, isLimitWeightedLimCone
-/
lemma weightedLimObjObjMap_π ⦃j : J⦄ (x : W.obj j) :
    weightedLimFlipObjMap g F ≫ W.weightedLimObjObjπ F x =
      W'.weightedLimObjObjπ F (g.app j x) :=
  (W.isLimitWeightedLimCone F).fac ..

@[simp]
/--
lemma `weightedLimFlipObjMap_id` / 引理 `weightedLimFlipObjMap_id`

English:
lemma weightedLimFlipObjMap_id
  proof: by
  cat_disch

@[reassoc]

中文:
引理 weightedLimFlipObjMap_id
  证明: by
  cat_disch

@[reassoc]

Depends on / 依赖: cat_disch
-/
lemma weightedLimFlipObjMap_id :
    weightedLimFlipObjMap (𝟙 W) F = 𝟙 _ := by
  cat_disch

@[reassoc]
/--
lemma `weightedLimFlipObjMap_comp` / 引理 `weightedLimFlipObjMap_comp`

English:
lemma weightedLimFlipObjMap_comp
  proof: by
  cat_disch

中文:
引理 weightedLimFlipObjMap_comp
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma weightedLimFlipObjMap_comp :
    weightedLimFlipObjMap g' F ≫ weightedLimFlipObjMap g F =
    weightedLimFlipObjMap (g ≫ g') F := by
  cat_disch

end

end

end Functor

end CategoryTheory
