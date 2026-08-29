/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Limits and colimits in the over and under categories

Show that the forgetful functor `forget X : Over X ⥤ C` creates colimits, and hence `Over X` has
any colimits that `C` has (as well as the dual that `forget X : Under X ⟶ C` creates limits).

Note that the folder `CategoryTheory.Limits.Shapes.Constructions.Over` further shows that
`forget X : Over X ⥤ C` creates connected limits (so `Over X` has connected limits), and that
`Over X` has `J`-indexed products if `C` has `J`-indexed wide pullbacks.
-/

@[expose] public section


noncomputable section

-- morphism levels before object levels. See note [category_theory universes].
universe w' w v u

open CategoryTheory CategoryTheory.Limits

variable {J : Type w} [Category.{w'} J]
variable {C : Type u} [Category.{v} C]
variable {X : C}

namespace CategoryTheory.Over

/--
Instance `hasColimit_of_hasColimit_comp_forget` / 实例 `hasColimit_of_hasColimit_comp_forget`

English:
instance hasColimit_of_hasColimit_comp_forget
  signature: (F : J ⥤ Over X) [i : HasColimit (F ⋙ forget X)]
  body: CostructuredArrow.hasColimit (i₁ := i)

中文:
实例 hasColimit_of_hasColimit_comp_forget
  签名: (F : J ⥤ Over X) [i : HasColimit (F ⋙ forget X)]
  定义体: CostructuredArrow.hasColimit (i₁ := i)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.hasColimit, hasColimit
-/
instance hasColimit_of_hasColimit_comp_forget (F : J ⥤ Over X) [i : HasColimit (F ⋙ forget X)] :
    HasColimit F :=
  CostructuredArrow.hasColimit (i₁ := i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfShape
  signature: J C] : HasColimitsOfShape J (Over X) where

中文:
实例 [HasColimitsOfShape
  签名: J C] : HasColimitsOfShape J (Over X) where
-/
instance [HasColimitsOfShape J C] : HasColimitsOfShape J (Over X) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: C] : HasFiniteColimits (Over X) where
  body: inferInstance

中文:
实例 [HasFiniteColimits
  签名: C] : HasFiniteColimits (Over X) where
  定义体: inferInstance
-/
instance [HasFiniteColimits C] : HasFiniteColimits (Over X) where
  out _ _ _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimits
  signature: C] : HasColimits (Over X)
  body: ⟨inferInstance⟩

中文:
实例 [HasColimits
  签名: C] : HasColimits (Over X)
  定义体: ⟨inferInstance⟩
-/
instance [HasColimits C] : HasColimits (Over X) :=
  ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteCoproducts
  signature: C] : HasFiniteCoproducts (Over X) where
  body: inferInstance

中文:
实例 [HasFiniteCoproducts
  签名: C] : HasFiniteCoproducts (Over X) where
  定义体: inferInstance
-/
instance [HasFiniteCoproducts C] : HasFiniteCoproducts (Over X) where
  out := inferInstance

/--
Instance `createsColimitsOfSize` / 实例 `createsColimitsOfSize`

English:
instance createsColimitsOfSize
  signature: : CreatesColimitsOfSize.{w, w'} (forget X)
  body: CostructuredArrow.createsColimitsOfSize

中文:
实例 createsColimitsOfSize
  签名: : CreatesColimitsOfSize.{w, w'} (forget X)
  定义体: CostructuredArrow.createsColimitsOfSize

Depends on / 依赖: CostructuredArrow, CostructuredArrow.createsColimitsOfSize, createsColimitsOfSize
-/
instance createsColimitsOfSize : CreatesColimitsOfSize.{w, w'} (forget X) :=
  CostructuredArrow.createsColimitsOfSize

-- We can automatically infer that the forgetful functor preserves and reflects colimits.
example [HasColimits C] : PreservesColimits (forget X) :=
  inferInstance

example : ReflectsColimits (forget X) :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
/--
theorem `epi_left_of_epi` / 定理 `epi_left_of_epi`

English:
theorem epi_left_of_epi
  given: [HasPushouts C] {f g : Over X} (h : f ⟶ g) [Epi h]
  statement: Epi h.left
  proof: CostructuredArrow.epi_left_of_epi _

中文:
定理 epi_left_of_epi
  条件: [HasPushouts C] {f g : Over X} (h : f ⟶ g) [Epi h]
  结论: Epi h.left
  证明: CostructuredArrow.epi_left_of_epi _

Depends on / 依赖: CostructuredArrow, CostructuredArrow.epi_left_of_epi, epi_left_of_epi
-/
theorem epi_left_of_epi [HasPushouts C] {f g : Over X} (h : f ⟶ g) [Epi h] : Epi h.left :=
  CostructuredArrow.epi_left_of_epi _

/--
theorem `epi_iff_epi_left` / 定理 `epi_iff_epi_left`

English:
theorem epi_iff_epi_left
  given: [HasPushouts C] {f g : Over X} (h : f ⟶ g)
  statement: Epi h ↔ Epi h.left
  proof: CostructuredArrow.epi_iff_epi_left _

中文:
定理 epi_iff_epi_left
  条件: [HasPushouts C] {f g : Over X} (h : f ⟶ g)
  结论: Epi h ↔ Epi h.left
  证明: CostructuredArrow.epi_iff_epi_left _

Depends on / 依赖: CostructuredArrow, CostructuredArrow.epi_iff_epi_left, epi_iff_epi_left
-/
theorem epi_iff_epi_left [HasPushouts C] {f g : Over X} (h : f ⟶ g) : Epi h ↔ Epi h.left :=
  CostructuredArrow.epi_iff_epi_left _

/--
Instance `createsColimitsOfSizeMapCompForget` / 实例 `createsColimitsOfSizeMapCompForget`

English:
instance createsColimitsOfSizeMapCompForget
  signature: {Y : C} (f : X ⟶ Y)
  body: show CreatesColimitsOfSize.{w, w'} (forget X) from inferInstance

中文:
实例 createsColimitsOfSizeMapCompForget
  签名: {Y : C} (f : X ⟶ Y)
  定义体: show CreatesColimitsOfSize.{w, w'} (forget X) from inferInstance

Depends on / 依赖: CreatesColimitsOfSize, forget
-/
instance createsColimitsOfSizeMapCompForget {Y : C} (f : X ⟶ Y) :
    CreatesColimitsOfSize.{w, w'} (map f ⋙ forget Y) :=
  show CreatesColimitsOfSize.{w, w'} (forget X) from inferInstance

/--
Instance `preservesColimitsOfSize_map` / 实例 `preservesColimitsOfSize_map`

English:
instance preservesColimitsOfSize_map
  signature: [HasColimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶ Y)
  body: preservesColimits_of_reflects_of_preserves (map f) (forget Y)

中文:
实例 preservesColimitsOfSize_map
  签名: [HasColimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶ Y)
  定义体: preservesColimits_of_reflects_of_preserves (map f) (forget Y)

Depends on / 依赖: forget, preservesColimits_of_reflects_of_preserves
-/
instance preservesColimitsOfSize_map [HasColimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶ Y) :
    PreservesColimitsOfSize.{w, w'} (map f) :=
  preservesColimits_of_reflects_of_preserves (map f) (forget Y)

/--
Definition of `isColimitToOver` / `isColimitToOver` 的定义

English:
definition isColimitToOver
  signature: {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
  body: isColimitOfReflects (forget c.pt) IsColimit.equivIsoColimit c.mapCoconeToOver.symm hc

中文:
定义 isColimitToOver
  签名: {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
  定义体: isColimitOfReflects (forget c.pt) IsColimit.equivIsoColimit c.mapCoconeToOver.symm hc

Depends on / 依赖: IsColimit, IsColimit.equivIsoColimit, c.mapCoconeToOver.symm, c.pt, equivIsoColimit, forget, isColimitOfReflects, mapCoconeToOver
-/
def isColimitToOver {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsColimit c.toOver :=
isColimitOfReflects (forget c.pt) IsColimit.equivIsoColimit c.mapCoconeToOver.symm hc

/--
Definition of `_root_.CategoryTheory.Limits.colimit.isColimitToOver` / `_root_.CategoryTheory.Limits.colimit.isColimitToOver` 的定义

English:
definition _root_.CategoryTheory.Limits.colimit.isColimitToOver
  signature: (F : J ⥤ C) [HasColimit F]
  body: Over.isColimitToOver (colimit.isColimit F)

中文:
定义 _root_.CategoryTheory.Limits.colimit.isColimitToOver
  签名: (F : J ⥤ C) [HasColimit F]
  定义体: Over.isColimitToOver (colimit.isColimit F)

Depends on / 依赖: Over.isColimitToOver, colimit, colimit.isColimit, isColimit, isColimitToOver
-/
def _root_.CategoryTheory.Limits.colimit.isColimitToOver (F : J ⥤ C) [HasColimit F] :
    IsColimit (colimit.toOver F) :=
  Over.isColimitToOver (colimit.isColimit F)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `liftCocone` / `liftCocone` 的定义

English:
definition liftCocone
  signature: {F : J ⥤ C} (c : Cocone F) {X : C} (f : c.pt ⟶ X)
  body: Over.mk f
  ι.app j := Over.homMk (c.ι.app j)

中文:
定义 liftCocone
  签名: {F : J ⥤ C} (c : Cocone F) {X : C} (f : c.pt ⟶ X)
  定义体: Over.mk f
  ι.app j := Over.homMk (c.ι.app j)
-/
@[simps] def liftCocone {F : J ⥤ C} (c : Cocone F) {X : C} (f : c.pt ⟶ X) :
    Cocone (Over.lift F (c.ι ≫ (Functor.const J).map f)) where
  pt := Over.mk f
  ι.app j := Over.homMk (c.ι.app j)

/--
Definition of `isColimitLiftCocone` / `isColimitLiftCocone` 的定义

English:
definition isColimitLiftCocone
  signature: {F : J ⥤ C} (c : Cocone F) {X : C} (f : c.pt ⟶ X)
  body: isColimitOfReflects (Over.forget _) hc

中文:
定义 isColimitLiftCocone
  签名: {F : J ⥤ C} (c : Cocone F) {X : C} (f : c.pt ⟶ X)
  定义体: isColimitOfReflects (Over.forget _) hc

Depends on / 依赖: Over.forget, forget, isColimitOfReflects
-/
noncomputable def isColimitLiftCocone {F : J ⥤ C} (c : Cocone F) {X : C} (f : c.pt ⟶ X)
    (hc : IsColimit c) : IsColimit (liftCocone c f) :=
  isColimitOfReflects (Over.forget _) hc

end CategoryTheory.Over

namespace CategoryTheory.Under

/--
Instance `hasLimit_of_hasLimit_comp_forget` / 实例 `hasLimit_of_hasLimit_comp_forget`

English:
instance hasLimit_of_hasLimit_comp_forget
  signature: (F : J ⥤ Under X) [i : HasLimit (F ⋙ forget X)]
  body: StructuredArrow.hasLimit (i₁ := i)

中文:
实例 hasLimit_of_hasLimit_comp_forget
  签名: (F : J ⥤ Under X) [i : HasLimit (F ⋙ forget X)]
  定义体: StructuredArrow.hasLimit (i₁ := i)

Depends on / 依赖: StructuredArrow, StructuredArrow.hasLimit, hasLimit
-/
instance hasLimit_of_hasLimit_comp_forget (F : J ⥤ Under X) [i : HasLimit (F ⋙ forget X)] :
    HasLimit F :=
  StructuredArrow.hasLimit (i₁ := i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: J C] : HasLimitsOfShape J (Under X) where

中文:
实例 [HasLimitsOfShape
  签名: J C] : HasLimitsOfShape J (Under X) where
-/
instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Under X) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] : HasLimits (Under X)
  body: ⟨inferInstance⟩

中文:
实例 [HasLimits
  签名: C] : HasLimits (Under X)
  定义体: ⟨inferInstance⟩
-/
instance [HasLimits C] : HasLimits (Under X) :=
  ⟨inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mono_right_of_mono` / 定理 `mono_right_of_mono`

English:
theorem mono_right_of_mono
  given: [HasPullbacks C] {f g : Under X} (h : f ⟶ g) [Mono h]
  statement: Mono h.right
  proof: StructuredArrow.mono_right_of_mono _

中文:
定理 mono_right_of_mono
  条件: [HasPullbacks C] {f g : Under X} (h : f ⟶ g) [Mono h]
  结论: Mono h.right
  证明: StructuredArrow.mono_right_of_mono _

Depends on / 依赖: StructuredArrow, StructuredArrow.mono_right_of_mono, mono_right_of_mono
-/
theorem mono_right_of_mono [HasPullbacks C] {f g : Under X} (h : f ⟶ g) [Mono h] : Mono h.right :=
  StructuredArrow.mono_right_of_mono _

/--
theorem `mono_iff_mono_right` / 定理 `mono_iff_mono_right`

English:
theorem mono_iff_mono_right
  given: [HasPullbacks C] {f g : Under X} (h : f ⟶ g)
  statement: Mono h ↔ Mono h.right
  proof: StructuredArrow.mono_iff_mono_right _

中文:
定理 mono_iff_mono_right
  条件: [HasPullbacks C] {f g : Under X} (h : f ⟶ g)
  结论: Mono h ↔ Mono h.right
  证明: StructuredArrow.mono_iff_mono_right _

Depends on / 依赖: StructuredArrow, StructuredArrow.mono_iff_mono_right, mono_iff_mono_right
-/
theorem mono_iff_mono_right [HasPullbacks C] {f g : Under X} (h : f ⟶ g) : Mono h ↔ Mono h.right :=
  StructuredArrow.mono_iff_mono_right _

/--
Instance `createsLimitsOfSize` / 实例 `createsLimitsOfSize`

English:
instance createsLimitsOfSize
  signature: : CreatesLimitsOfSize.{w, w'} (forget X)
  body: StructuredArrow.createsLimitsOfSize

中文:
实例 createsLimitsOfSize
  签名: : CreatesLimitsOfSize.{w, w'} (forget X)
  定义体: StructuredArrow.createsLimitsOfSize

Depends on / 依赖: StructuredArrow, StructuredArrow.createsLimitsOfSize, createsLimitsOfSize
-/
instance createsLimitsOfSize : CreatesLimitsOfSize.{w, w'} (forget X) :=
  StructuredArrow.createsLimitsOfSize

-- We can automatically infer that the forgetful functor preserves and reflects limits.
example [HasLimits C] : PreservesLimits (forget X) :=
  inferInstance

example : ReflectsLimits (forget X) :=
  inferInstance

/--
Instance `createLimitsOfSizeMapCompForget` / 实例 `createLimitsOfSizeMapCompForget`

English:
instance createLimitsOfSizeMapCompForget
  signature: {Y : C} (f : X ⟶ Y)
  body: show CreatesLimitsOfSize.{w, w'} (forget Y) from inferInstance

中文:
实例 createLimitsOfSizeMapCompForget
  签名: {Y : C} (f : X ⟶ Y)
  定义体: show CreatesLimitsOfSize.{w, w'} (forget Y) from inferInstance

Depends on / 依赖: CreatesLimitsOfSize, forget
-/
instance createLimitsOfSizeMapCompForget {Y : C} (f : X ⟶ Y) :
    CreatesLimitsOfSize.{w, w'} (map f ⋙ forget X) :=
  show CreatesLimitsOfSize.{w, w'} (forget Y) from inferInstance

/--
Instance `preservesLimitsOfSize_map` / 实例 `preservesLimitsOfSize_map`

English:
instance preservesLimitsOfSize_map
  signature: [HasLimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶ Y)
  body: preservesLimits_of_reflects_of_preserves (map f) (forget X)

中文:
实例 preservesLimitsOfSize_map
  签名: [HasLimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶ Y)
  定义体: preservesLimits_of_reflects_of_preserves (map f) (forget X)

Depends on / 依赖: forget, preservesLimits_of_reflects_of_preserves
-/
instance preservesLimitsOfSize_map [HasLimitsOfSize.{w, w'} C] {Y : C} (f : X ⟶ Y) :
    PreservesLimitsOfSize.{w, w'} (map f) :=
  preservesLimits_of_reflects_of_preserves (map f) (forget X)

/--
Definition of `isLimitToUnder` / `isLimitToUnder` 的定义

English:
definition isLimitToUnder
  signature: {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
  body: isLimitOfReflects (forget c.pt) (IsLimit.equivIsoLimit c.mapConeToUnder.symm hc)

中文:
定义 isLimitToUnder
  签名: {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
  定义体: isLimitOfReflects (forget c.pt) (IsLimit.equivIsoLimit c.mapConeToUnder.symm hc)

Depends on / 依赖: IsLimit, IsLimit.equivIsoLimit, c.mapConeToUnder.symm, c.pt, equivIsoLimit, forget, isLimitOfReflects, mapConeToUnder
-/
def isLimitToUnder {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) : IsLimit c.toUnder :=
  isLimitOfReflects (forget c.pt) (IsLimit.equivIsoLimit c.mapConeToUnder.symm hc)

/--
Definition of `_root_.CategoryTheory.Limits.limit.isLimitToOver` / `_root_.CategoryTheory.Limits.limit.isLimitToOver` 的定义

English:
definition _root_.CategoryTheory.Limits.limit.isLimitToOver
  signature: (F : J ⥤ C) [HasLimit F]
  body: Under.isLimitToUnder (limit.isLimit F)

中文:
定义 _root_.CategoryTheory.Limits.limit.isLimitToOver
  签名: (F : J ⥤ C) [HasLimit F]
  定义体: Under.isLimitToUnder (limit.isLimit F)

Depends on / 依赖: Under.isLimitToUnder, isLimit, isLimitToUnder, limit.isLimit
-/
def _root_.CategoryTheory.Limits.limit.isLimitToOver (F : J ⥤ C) [HasLimit F] :
    IsLimit (limit.toUnder F) :=
  Under.isLimitToUnder (limit.isLimit F)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `liftCone` / `liftCone` 的定义

English:
definition liftCone
  signature: {F : J ⥤ C} (c : Cone F) {X : C} (f : X ⟶ c.pt)
  body: Under.mk f
  π.app j := Under.homMk (c.π.app j)

中文:
定义 liftCone
  签名: {F : J ⥤ C} (c : Cone F) {X : C} (f : X ⟶ c.pt)
  定义体: Under.mk f
  π.app j := Under.homMk (c.π.app j)
-/
@[simps] def liftCone {F : J ⥤ C} (c : Cone F) {X : C} (f : X ⟶ c.pt) :
    Cone (Under.lift F ((Functor.const J).map f ≫ c.π)) where
  pt := Under.mk f
  π.app j := Under.homMk (c.π.app j)

/--
Definition of `isLimitLiftCone` / `isLimitLiftCone` 的定义

English:
definition isLimitLiftCone
  signature: {F : J ⥤ C} (c : Cone F) {X : C}
  body: isLimitOfReflects (Under.forget _) hc

中文:
定义 isLimitLiftCone
  签名: {F : J ⥤ C} (c : Cone F) {X : C}
  定义体: isLimitOfReflects (Under.forget _) hc

Depends on / 依赖: Under.forget, forget, isLimitOfReflects
-/
noncomputable def isLimitLiftCone {F : J ⥤ C} (c : Cone F) {X : C}
    (f : X ⟶ c.pt) (hc : IsLimit c) : IsLimit (liftCone c f) :=
  isLimitOfReflects (Under.forget _) hc

end CategoryTheory.Under
