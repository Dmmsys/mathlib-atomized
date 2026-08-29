/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Fubini
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preservations of limits for bifunctors

Let `G : C₁ ⥤ C₂ ⥤ C` a functor. We introduce a class `PreservesLimit₂ K₁ K₂ G` that encodes
the hypothesis that the curried functor `F : C₁ × C₂ ⥤ C` preserves limits of the diagram
`K₁ × K₂ : J₁ × J₂ ⥤ C₁ × C₂`. We give a basic API to extract isomorphisms
$\lim_{(j_1,j_2)} G(K_1(j_1), K_2(j_2)) \simeq G(\lim K_1, \lim K_2)$
out of this typeclass.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits CategoryTheory.Functor

variable {J₁ J₂ : Type*} [Category* J₁] [Category* J₂]
  {C₁ C₂ C : Type*} [Category* C₁] [Category* C₂] [Category* C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a bifunctor `G : C₁ ⥤ C₂ ⥤ C`, diagrams `K₁ : J₁ ⥤ C₁` and `K₂ : J₂ ⥤ C₂`, and cocones
over these diagrams, `G.mapCocone₂ c₁ c₂` is the cocone over the diagram `J₁ × J₂ ⥤ C` obtained
by applying `G` to both `c₁` and `c₂`. -/
@[simps!]
/--
Definition of `Functor.mapCocone₂` / `Functor.mapCocone₂` 的定义

English:
definition Functor.mapCocone₂
  signature: (G : C₁ ⥤ C₂ ⥤ C) {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂}
  body: (G.obj c₁.pt).obj c₂.pt
  ι :=
    { app := fun ⟨j₁, j₂⟩ => (G.map <| c₁.ι.app j₁).app _ ≫ (G.obj _).map (c₂.ι.app j₂)
      naturality := by
        rintro ⟨j₁, j₂⟩ ⟨k₁, k₂⟩ ⟨f₁, f₂⟩
        dsimp
        simp only [assoc, comp_id, NatTrans.naturality_assoc,
          ← Functor.map_comp, NatTrans.naturality, const_obj_map, const_obj_obj,
          ← NatTrans.comp_app_assoc, c₁.w] }

中文:
定义 函子.mapCocone₂
  签名: (G : C₁ ⥤ C₂ ⥤ C) {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂}
  定义体: (G.obj c₁.pt).obj c₂.pt
  ι :=
    { app := fun ⟨j₁, j₂⟩ => (G.map <| c₁.ι.app j₁).app _ ≫ (G.obj _).map (c₂.ι.app j₂)
      naturality := by
        rintro ⟨j₁, j₂⟩ ⟨k₁, k₂⟩ ⟨f₁, f₂⟩
        dsimp
        simp only [assoc, comp_id, NatTrans.naturality_assoc,
          ← Functor.map_comp, NatTrans.naturality, const_obj_map, const_obj_obj,
          ← NatTrans.comp_app_assoc, c₁.w] }

Depends on / 依赖: G.obj
-/
def Functor.mapCocone₂ (G : C₁ ⥤ C₂ ⥤ C) {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂}
    (c₁ : Cocone K₁) (c₂ : Cocone K₂) :
Cocone uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) where
  pt := (G.obj c₁.pt).obj c₂.pt
  ι :=
    { app := fun ⟨j₁, j₂⟩ => (G.map <| c₁.ι.app j₁).app _ ≫ (G.obj _).map (c₂.ι.app j₂)
      naturality := by
        rintro ⟨j₁, j₂⟩ ⟨k₁, k₂⟩ ⟨f₁, f₂⟩
        dsimp
        simp only [assoc, comp_id, NatTrans.naturality_assoc,
          ← Functor.map_comp, NatTrans.naturality, const_obj_map, const_obj_obj,
          ← NatTrans.comp_app_assoc, c₁.w] }

set_option backward.defeqAttrib.useBackward true in
/-- Given a bifunctor `G : C₁ ⥤ C₂ ⥤ C`, diagrams `K₁ : J₁ ⥤ C₁` and `K₂ : J₂ ⥤ C₂`, and cones
over these diagrams, `G.mapCone₂ c₁ c₂` is the cone over the diagram `J₁ × J₂ ⥤ C` obtained
by applying `G` to both `c₁` and `c₂`. -/
@[simps!]
/--
Definition of `Functor.mapCone₂` / `Functor.mapCone₂` 的定义

English:
definition Functor.mapCone₂
  signature: (G : C₁ ⥤ C₂ ⥤ C) {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂}
  body: (G.obj c₁.pt).obj c₂.pt
  π :=
    { app := fun ⟨j₁, j₂⟩ => (G.map <| c₁.π.app j₁).app _ ≫ (G.obj _).map (c₂.π.app j₂)
      naturality := by
        rintro ⟨j₁, j₂⟩ ⟨k₁, k₂⟩ ⟨f₁, f₂⟩
        dsimp
        simp only [assoc, id_comp, NatTrans.naturality_assoc,
          ← Functor.map_comp,
          ← NatTrans.comp_app_assoc, c₁.w, c₂.w] }

中文:
定义 函子.mapCone₂
  签名: (G : C₁ ⥤ C₂ ⥤ C) {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂}
  定义体: (G.obj c₁.pt).obj c₂.pt
  π :=
    { app := fun ⟨j₁, j₂⟩ => (G.map <| c₁.π.app j₁).app _ ≫ (G.obj _).map (c₂.π.app j₂)
      naturality := by
        rintro ⟨j₁, j₂⟩ ⟨k₁, k₂⟩ ⟨f₁, f₂⟩
        dsimp
        simp only [assoc, id_comp, NatTrans.naturality_assoc,
          ← Functor.map_comp,
          ← NatTrans.comp_app_assoc, c₁.w, c₂.w] }

Depends on / 依赖: G.obj
-/
def Functor.mapCone₂ (G : C₁ ⥤ C₂ ⥤ C) {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂}
    (c₁ : Cone K₁) (c₂ : Cone K₂) :
Cone uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) where
  pt := (G.obj c₁.pt).obj c₂.pt
  π :=
    { app := fun ⟨j₁, j₂⟩ => (G.map <| c₁.π.app j₁).app _ ≫ (G.obj _).map (c₂.π.app j₂)
      naturality := by
        rintro ⟨j₁, j₂⟩ ⟨k₁, k₂⟩ ⟨f₁, f₂⟩
        dsimp
        simp only [assoc, id_comp, NatTrans.naturality_assoc,
          ← Functor.map_comp,
          ← NatTrans.comp_app_assoc, c₁.w, c₂.w] }

namespace Limits

/--
Definition of `PreservesColimit₂` / `PreservesColimit₂` 的定义

English:
class PreservesColimit₂
  parameters: (K₁ : J₁ ⥤ C₁) (K₂ : J₂ ⥤ C₂) (G : C₁ ⥤ C₂ ⥤ C)
  axioms and operations (1):
    - nonempty_isColimit_mapCocone₂({c₁ : Cocone K₁} (hc₁ : IsColimit c₁) {c₂ : Cocone K₂} (hc₂ : IsColimit c₂))

中文:
类 保持余limit₂
  参数: (K₁ : J₁ ⥤ C₁) (K₂ : J₂ ⥤ C₂) (G : C₁ ⥤ C₂ ⥤ C)
  公理与运算 (1 个):
    - nonempty_isColimit_mapCocone₂({c₁ : 余锥 K₁} (hc₁ : 是余极限 c₁) {c₂ : 余锥 K₂} (hc₂ : 是余极限 c₂))
-/
class PreservesColimit₂ (K₁ : J₁ ⥤ C₁) (K₂ : J₂ ⥤ C₂) (G : C₁ ⥤ C₂ ⥤ C) : Prop where
  nonempty_isColimit_mapCocone₂ {c₁ : Cocone K₁} (hc₁ : IsColimit c₁)
      {c₂ : Cocone K₂} (hc₂ : IsColimit c₂) :
Nonempty IsColimit G.mapCocone₂ c₁ c₂

/--
Definition of `PreservesLimit₂` / `PreservesLimit₂` 的定义

English:
class PreservesLimit₂
  parameters: (K₁ : J₁ ⥤ C₁) (K₂ : J₂ ⥤ C₂) (G : C₁ ⥤ C₂ ⥤ C)
  axioms and operations (1):
    - nonempty_isLimit_mapCone₂({c₁ : Cone K₁} (hc₁ : IsLimit c₁) {c₂ : Cone K₂} (hc₂ : IsLimit c₂))

中文:
类 保持Limit₂
  参数: (K₁ : J₁ ⥤ C₁) (K₂ : J₂ ⥤ C₂) (G : C₁ ⥤ C₂ ⥤ C)
  公理与运算 (1 个):
    - nonempty_isLimit_mapCone₂({c₁ : 锥 K₁} (hc₁ : 是极限 c₁) {c₂ : 锥 K₂} (hc₂ : 是极限 c₂))
-/
class PreservesLimit₂ (K₁ : J₁ ⥤ C₁) (K₂ : J₂ ⥤ C₂) (G : C₁ ⥤ C₂ ⥤ C) : Prop where
  nonempty_isLimit_mapCone₂ {c₁ : Cone K₁} (hc₁ : IsLimit c₁)
      {c₂ : Cone K₂} (hc₂ : IsLimit c₂) :
Nonempty IsLimit G.mapCone₂ c₁ c₂

variable {K₁ : J₁ ⥤ C₁} {K₂ : J₂ ⥤ C₂} (G : C₁ ⥤ C₂ ⥤ C)

/--
Definition of `isColimitOfPreserves₂` / `isColimitOfPreserves₂` 的定义

English:
definition isColimitOfPreserves₂
  signature: [PreservesColimit₂ K₁ K₂ G]
  body: .some PreservesColimit₂.nonempty_isColimit_mapCocone₂ hc₁ hc₂

中文:
定义 isColimitOfPreserves₂
  签名: [保持余limit₂ K₁ K₂ G]
  定义体: .some PreservesColimit₂.nonempty_isColimit_mapCocone₂ hc₁ hc₂
-/
noncomputable def isColimitOfPreserves₂ [PreservesColimit₂ K₁ K₂ G]
    {c₁ : Cocone K₁} (hc₁ : IsColimit c₁)
    {c₂ : Cocone K₂} (hc₂ : IsColimit c₂) :
    IsColimit (G.mapCocone₂ c₁ c₂) :=
.some PreservesColimit₂.nonempty_isColimit_mapCocone₂ hc₁ hc₂

/--
Definition of `isLimitOfPreserves₂` / `isLimitOfPreserves₂` 的定义

English:
definition isLimitOfPreserves₂
  signature: [PreservesLimit₂ K₁ K₂ G]
  body: .some PreservesLimit₂.nonempty_isLimit_mapCone₂ hc₁ hc₂

中文:
定义 isLimitOfPreserves₂
  签名: [保持Limit₂ K₁ K₂ G]
  定义体: .some PreservesLimit₂.nonempty_isLimit_mapCone₂ hc₁ hc₂
-/
noncomputable def isLimitOfPreserves₂ [PreservesLimit₂ K₁ K₂ G]
    {c₁ : Cone K₁} (hc₁ : IsLimit c₁)
    {c₂ : Cone K₂} (hc₂ : IsLimit c₂) :
    IsLimit (G.mapCone₂ c₁ c₂) :=
.some PreservesLimit₂.nonempty_isLimit_mapCone₂ hc₁ hc₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimit
  signature: K₁] [HasColimit K₂] [PreservesColimit₂ K₁ K₂ G] :
  body: ⟨{
    cocone := _
    isColimit :=
      PreservesColimit₂.nonempty_isColimit_mapCocone₂
        (getColimitCocone K₁).isColimit
.some }⟩ (getColimitCocone K₂).isColimit

中文:
实例 [有余极限
  签名: K₁] [有余极限 K₂] [保持余limit₂ K₁ K₂ G] :
  定义体: ⟨{
    cocone := _
    isColimit :=
      PreservesColimit₂.nonempty_isColimit_mapCocone₂
        (getColimitCocone K₁).isColimit
.some }⟩ (getColimitCocone K₂).isColimit
-/
instance [HasColimit K₁] [HasColimit K₂] [PreservesColimit₂ K₁ K₂ G] :
HasColimit uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) where
  exists_colimit := ⟨{
    cocone := _
    isColimit :=
      PreservesColimit₂.nonempty_isColimit_mapCocone₂
        (getColimitCocone K₁).isColimit
.some }⟩ (getColimitCocone K₂).isColimit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimit
  signature: K₁] [HasLimit K₂] [PreservesLimit₂ K₁ K₂ G] :
  body: ⟨{
    cone := _
    isLimit :=
      PreservesLimit₂.nonempty_isLimit_mapCone₂
        (getLimitCone K₁).isLimit
.some }⟩ (getLimitCone K₂).isLimit

中文:
实例 [有极限
  签名: K₁] [有极限 K₂] [保持Limit₂ K₁ K₂ G] :
  定义体: ⟨{
    cone := _
    isLimit :=
      PreservesLimit₂.nonempty_isLimit_mapCone₂
        (getLimitCone K₁).isLimit
.some }⟩ (getLimitCone K₂).isLimit
-/
instance [HasLimit K₁] [HasLimit K₂] [PreservesLimit₂ K₁ K₂ G] :
HasLimit uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) where
  exists_limit := ⟨{
    cone := _
    isLimit :=
      PreservesLimit₂.nonempty_isLimit_mapCone₂
        (getLimitCone K₁).isLimit
.some }⟩ (getLimitCone K₂).isLimit

namespace PreservesColimit₂

variable [PreservesColimit₂ K₁ K₂ G]

/--
Definition of `isoObjCoconePointsOfIsColimit` / `isoObjCoconePointsOfIsColimit` 的定义

English:
definition isoObjCoconePointsOfIsColimit
  body: IsColimit.coconePointUniqueUpToIso (isColimitOfPreserves₂ G hc₁ hc₂) hc₃

中文:
定义 isoObjCoconePointsOfIsColimit
  定义体: IsColimit.coconePointUniqueUpToIso (isColimitOfPreserves₂ G hc₁ hc₂) hc₃

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso
-/
noncomputable def isoObjCoconePointsOfIsColimit
    {c₁ : Cocone K₁} (hc₁ : IsColimit c₁)
    {c₂ : Cocone K₂} (hc₂ : IsColimit c₂)
    {c₃ : Cocone <| uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G)}
    (hc₃ : IsColimit c₃) :
    (G.obj c₁.pt).obj c₂.pt ≅ c₃.pt :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfPreserves₂ G hc₁ hc₂) hc₃

section

variable {c₁ : Cocone K₁} (hc₁ : IsColimit c₁)
  {c₂ : Cocone K₂} (hc₂ : IsColimit c₂)
  {c₃ : Cocone <| uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G)}
  (hc₃ : IsColimit c₃)

set_option backward.isDefEq.respectTransparency.types false in
/-- Characterize the inverse direction of the isomorphism
`PreservesColimit₂.isoObjCoconePointsOfIsColimit` w.r.t. the canonical maps to the colimit. -/
@[reassoc (attr := simp)]
/--
lemma `ι_comp_isoObjConePointsOfIsColimit_inv` / 引理 `ι_comp_isoObjConePointsOfIsColimit_inv`

English:
lemma ι_comp_isoObjConePointsOfIsColimit_inv
  given: (j : J₁ × J₂)
  proof: by
  dsimp [isoObjCoconePointsOfIsColimit, Functor.mapCocone₂]
  cat_disch

中文:
引理 ι_comp_isoObjConePointsOfIsColimit_inv
  条件: (j : J₁ × J₂)
  证明: by
  dsimp [isoObjCoconePointsOfIsColimit, Functor.mapCocone₂]
  cat_disch

Depends on / 依赖: Functor, Functor.mapCocone, cat_disch, isoObjCoconePointsOfIsColimit
-/
lemma ι_comp_isoObjConePointsOfIsColimit_inv (j : J₁ × J₂) :
    c₃.ι.app j ≫
      (isoObjCoconePointsOfIsColimit G hc₁ hc₂ hc₃).inv =
    (G.map <| c₁.ι.app j.1).app (K₂.obj j.2) ≫ (G.obj c₁.pt).map (c₂.ι.app j.2) := by
  dsimp [isoObjCoconePointsOfIsColimit, Functor.mapCocone₂]
  cat_disch

set_option backward.isDefEq.respectTransparency false in
/-- Characterize the forward direction of the isomorphism
`PreservesColimit₂.isoObjCoconePointsOfIsColimit` w.r.t. the canonical maps to the colimit. -/
@[reassoc (attr := simp)]
/--
lemma `map_ι_comp_isoObjConePointsOfIsColimit_hom` / 引理 `map_ι_comp_isoObjConePointsOfIsColimit_hom`

English:
lemma map_ι_comp_isoObjConePointsOfIsColimit_hom
  given: (j : J₁ × J₂)
  proof: by
  rw [← Category.assoc]; rw [← Iso.eq_comp_inv]
  simp

中文:
引理 map_ι_comp_isoObjConePointsOfIsColimit_hom
  条件: (j : J₁ × J₂)
  证明: by
  rw [← Category.assoc]; rw [← Iso.eq_comp_inv]
  simp

Depends on / 依赖: Category, Category.assoc, Iso.eq_comp_inv, eq_comp_inv
-/
lemma map_ι_comp_isoObjConePointsOfIsColimit_hom (j : J₁ × J₂) :
    (G.map (c₁.ι.app j.1)).app (K₂.obj j.2) ≫ (G.obj c₁.pt).map (c₂.ι.app j.2) ≫
      (isoObjCoconePointsOfIsColimit G hc₁ hc₂ hc₃).hom =
    c₃.ι.app j := by
  rw [← Category.assoc]; rw [← Iso.eq_comp_inv]
  simp

end

section

variable (K₁ K₂) [HasColimit K₁] [HasColimit K₂]

/--
Definition of `isoColimitUncurryWhiskeringLeft₂` / `isoColimitUncurryWhiskeringLeft₂` 的定义

English:
definition isoColimitUncurryWhiskeringLeft₂
  signature: :
  body: isoObjCoconePointsOfIsColimit G
.symm (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)

#adaptation_note

中文:
定义 isoColimitUncurryWhiskeringLeft₂
  签名: :
  定义体: isoObjCoconePointsOfIsColimit G
.symm (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)

#adaptation_note

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isoObjCoconePointsOfIsColimit
-/
noncomputable def isoColimitUncurryWhiskeringLeft₂ :
    colimit (uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G)) ≅
    (G.obj <| colimit K₁).obj (colimit K₂) :=
  isoObjCoconePointsOfIsColimit G
.symm (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Characterize the forward direction of the isomorphism
`PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂` w.r.t. the canonical maps to the colimit. -/
@[reassoc (attr := simp)]
/--
lemma `ι_comp_isoColimitUncurryWhiskeringLeft₂_hom` / 引理 `ι_comp_isoColimitUncurryWhiskeringLeft₂_hom`

English:
lemma ι_comp_isoColimitUncurryWhiskeringLeft₂_hom
  given: (j : J₁ × J₂)
  proof: ι_comp_isoObjConePointsOfIsColimit_inv G
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _) j

中文:
引理 ι_comp_isoColimitUncurryWhiskeringLeft₂_hom
  条件: (j : J₁ × J₂)
  证明: ι_comp_isoObjConePointsOfIsColimit_inv G
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _) j

Depends on / 依赖: colimit, colimit.isColimit, isColimit
-/
lemma ι_comp_isoColimitUncurryWhiskeringLeft₂_hom (j : J₁ × J₂) :
    colimit.ι (uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G)) j ≫
      (PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂ K₁ K₂ G).hom =
    (G.map <| colimit.ι K₁ j.1).app (K₂.obj j.2) ≫ (G.obj <| colimit K₁).map (colimit.ι K₂ j.2) :=
  ι_comp_isoObjConePointsOfIsColimit_inv G
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _) j

/-- Characterize the forward direction of the isomorphism
`PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂` w.r.t. the canonical maps to the colimit. -/
@[reassoc (attr := simp)]
/--
lemma `map_ι_comp_isoColimitUncurryWhiskeringLeft₂_inv` / 引理 `map_ι_comp_isoColimitUncurryWhiskeringLeft₂_inv`

English:
lemma map_ι_comp_isoColimitUncurryWhiskeringLeft₂_inv
  given: (j : J₁ × J₂)
  proof: map_ι_comp_isoObjConePointsOfIsColimit_hom G
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _) j

中文:
引理 map_ι_comp_isoColimitUncurryWhiskeringLeft₂_inv
  条件: (j : J₁ × J₂)
  证明: map_ι_comp_isoObjConePointsOfIsColimit_hom G
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _) j

Depends on / 依赖: colimit, colimit.isColimit, isColimit
-/
lemma map_ι_comp_isoColimitUncurryWhiskeringLeft₂_inv (j : J₁ × J₂) :
    (G.map (colimit.ι K₁ j.1)).app (K₂.obj j.2) ≫ (G.obj <| colimit K₁).map (colimit.ι K₂ j.2) ≫
      (PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂ K₁ K₂ G).inv =
    colimit.ι (uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G)) j :=
  map_ι_comp_isoObjConePointsOfIsColimit_hom G
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _) j

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `of_preservesColimits_in_each_variable` / 实例 `of_preservesColimits_in_each_variable`

English:
instance of_preservesColimits_in_each_variable
  body: let Q₀ : DiagramOfCocones (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      { obj j₁ := G.obj (K₁.obj j₁) |>.mapCocone c₂
        map f := { hom := G.map (K₁.map f) |>.app c₂.pt } }
    let P : forall j₁, IsColimit (Q₀.obj j₁) := fun j => isColimitOfPreserves _ hc₂
    let E₀ : Q₀.coconePoints ≅ K₁ ⋙ G.flip.obj c₂.pt := NatIso.ofComponents (fun _ => Iso.refl _)
    let E₁ : (Cocone.precompose E₀.hom).obj (coconeOfCoconeUncurry P <| G.mapCocone₂ c₁ c₂) ≅
        (G.flip.obj c₂.pt).mapCocone c₁ :=
      Cocone.ext
        (Iso.refl _)
        (fun j₁ => by
          dsimp [E₀, Q₀]
          simp only [id_comp, comp_id]
          let s : Cocone (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G |>.obj j₁) := ?_
          change (P j₁).desc s = _
          symm
          apply (P j₁).hom_ext
          intro j₂
          have := (P j₁).fac s j₂
          simp only [Functor.mapCocone_pt, Functor.mapCocone_ι_app, Q₀, s] at this
          simp only [Functor.mapCocone_pt,
            Functor.mapCocone_ι_app, NatTrans.naturality, this, Q₀, s])
⟨IsColimit.ofCoconeUncurry P IsColimit.precomposeHomEquiv E₀ _
      IsColimit.ofIsoColimit (isColimitOfPreserves _ hc₁) E₁.symm⟩

中文:
实例 of_preservesColimits_in_each_variable
  定义体: let Q₀ : DiagramOfCocones (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      { obj j₁ := G.obj (K₁.obj j₁) |>.mapCocone c₂
        map f := { hom := G.map (K₁.map f) |>.app c₂.pt } }
    let P : forall j₁, IsColimit (Q₀.obj j₁) := fun j => isColimitOfPreserves _ hc₂
    let E₀ : Q₀.coconePoints ≅ K₁ ⋙ G.flip.obj c₂.pt := NatIso.ofComponents (fun _ => Iso.refl _)
    let E₁ : (Cocone.precompose E₀.hom).obj (coconeOfCoconeUncurry P <| G.mapCocone₂ c₁ c₂) ≅
        (G.flip.obj c₂.pt).mapCocone c₁ :=
      Cocone.ext
        (Iso.refl _)
        (fun j₁ => by
          dsimp [E₀, Q₀]
          simp only [id_comp, comp_id]
          let s : Cocone (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G |>.obj j₁) := ?_
          change (P j₁).desc s = _
          symm
          apply (P j₁).hom_ext
          intro j₂
          have := (P j₁).fac s j₂
          simp only [Functor.mapCocone_pt, Functor.mapCocone_ι_app, Q₀, s] at this
          simp only [Functor.mapCocone_pt,
            Functor.mapCocone_ι_app, NatTrans.naturality, this, Q₀, s])
⟨IsColimit.ofCoconeUncurry P IsColimit.precomposeHomEquiv E₀ _
      IsColimit.ofIsoColimit (isColimitOfPreserves _ hc₁) E₁.symm⟩

Depends on / 依赖: Cocone, Cocone.ext, Cocone.precompose, DiagramOfCocones, G.flip.obj, G.map, G.mapCocone, G.obj, IsColimit, Iso.refl, NatIso, NatIso.ofComponents, coconeOfCoconeUncurry, coconePoints, isColimitOfPreserves, mapCocone, ofComponents, precompose
-/
instance of_preservesColimits_in_each_variable
    [forall x : C₂, PreservesColimit K₁ (G.flip.obj x)] [forall x : C₁, PreservesColimit K₂ (G.obj x)] :
    PreservesColimit₂ K₁ K₂ G where
  nonempty_isColimit_mapCocone₂ {c₁} hc₁ {c₂} hc₂ :=
    let Q₀ : DiagramOfCocones (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      { obj j₁ := G.obj (K₁.obj j₁) |>.mapCocone c₂
        map f := { hom := G.map (K₁.map f) |>.app c₂.pt } }
    let P : forall j₁, IsColimit (Q₀.obj j₁) := fun j => isColimitOfPreserves _ hc₂
    let E₀ : Q₀.coconePoints ≅ K₁ ⋙ G.flip.obj c₂.pt := NatIso.ofComponents (fun _ => Iso.refl _)
    let E₁ : (Cocone.precompose E₀.hom).obj (coconeOfCoconeUncurry P <| G.mapCocone₂ c₁ c₂) ≅
        (G.flip.obj c₂.pt).mapCocone c₁ :=
      Cocone.ext
        (Iso.refl _)
        (fun j₁ => by
          dsimp [E₀, Q₀]
          simp only [id_comp, comp_id]
          let s : Cocone (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G |>.obj j₁) := ?_
          change (P j₁).desc s = _
          symm
          apply (P j₁).hom_ext
          intro j₂
          have := (P j₁).fac s j₂
          simp only [Functor.mapCocone_pt, Functor.mapCocone_ι_app, Q₀, s] at this
          simp only [Functor.mapCocone_pt,
            Functor.mapCocone_ι_app, NatTrans.naturality, this, Q₀, s])
⟨IsColimit.ofCoconeUncurry P IsColimit.precomposeHomEquiv E₀ _
      IsColimit.ofIsoColimit (isColimitOfPreserves _ hc₁) E₁.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `of_preservesColimit₂_flip` / 定理 `of_preservesColimit₂_flip`

English:
theorem of_preservesColimit₂_flip
  statement: PreservesColimit₂ K₂ K₁ G.flip where
  proof: by
    constructor
    let E₀ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G).flip :=
      Iso.refl _
    let E₁ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        Prod.swap _ _ ⋙ uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      E₀ ≪≫ uncurryObjFlip _
    refine IsColimit.precomposeInvEquiv E₁ _ ?_
    apply IsColimit.ofWhiskerEquivalence (e := Prod.braiding _ _)
.toFun refine IsColimit.equivOfNatIsoOfIso (Iso.refl _) (G.mapCocone₂ c₂ c₁) _ ?_
      isColimitOfPreserves₂ G hc₂ hc₁
    exact Cocone.ext (Iso.refl _) (fun ⟨j₁, j₂⟩ => by simp [E₁, E₀])

中文:
定理 of_preservesColimit₂_flip
  结论: 保持余limit₂ K₂ K₁ G.flip where
  证明: by
    constructor
    let E₀ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G).flip :=
      Iso.refl _
    let E₁ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        Prod.swap _ _ ⋙ uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      E₀ ≪≫ uncurryObjFlip _
    refine IsColimit.precomposeInvEquiv E₁ _ ?_
    apply IsColimit.ofWhiskerEquivalence (e := Prod.braiding _ _)
.toFun refine IsColimit.equivOfNatIsoOfIso (Iso.refl _) (G.mapCocone₂ c₂ c₁) _ ?_
      isColimitOfPreserves₂ G hc₂ hc₁
    exact Cocone.ext (Iso.refl _) (fun ⟨j₁, j₂⟩ => by simp [E₁, E₀])

Depends on / 依赖: G.flip, IsColimit, IsColimit.equivOfNatIsoOfIso, IsColimit.ofWhiskerEquivalence, IsColimit.precomposeInvEquiv, Iso.refl, Prod.braiding, Prod.swap, braiding, equivOfNatIsoOfIso, ofWhiskerEquivalence, precomposeInvEquiv, uncurry, uncurry.obj, uncurryObjFlip
-/
theorem of_preservesColimit₂_flip : PreservesColimit₂ K₂ K₁ G.flip where
  nonempty_isColimit_mapCocone₂ {c₁} hc₁ {c₂} hc₂ := by
    constructor
    let E₀ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G).flip :=
      Iso.refl _
    let E₁ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        Prod.swap _ _ ⋙ uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      E₀ ≪≫ uncurryObjFlip _
    refine IsColimit.precomposeInvEquiv E₁ _ ?_
    apply IsColimit.ofWhiskerEquivalence (e := Prod.braiding _ _)
.toFun refine IsColimit.equivOfNatIsoOfIso (Iso.refl _) (G.mapCocone₂ c₂ c₁) _ ?_
      isColimitOfPreserves₂ G hc₂ hc₁
    exact Cocone.ext (Iso.refl _) (fun ⟨j₁, j₂⟩ => by simp [E₁, E₀])

end PreservesColimit₂

namespace PreservesLimit₂

variable [PreservesLimit₂ K₁ K₂ G]

/--
Definition of `isoObjConePointsOfIsLimit` / `isoObjConePointsOfIsLimit` 的定义

English:
definition isoObjConePointsOfIsLimit
  body: IsLimit.conePointUniqueUpToIso (isLimitOfPreserves₂ G hc₁ hc₂) hc₃

中文:
定义 isoObjConePointsOfIsLimit
  定义体: IsLimit.conePointUniqueUpToIso (isLimitOfPreserves₂ G hc₁ hc₂) hc₃

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso
-/
noncomputable def isoObjConePointsOfIsLimit
    {c₁ : Cone K₁} (hc₁ : IsLimit c₁)
    {c₂ : Cone K₂} (hc₂ : IsLimit c₂)
    {c₃ : Cone <| uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G)}
    (hc₃ : IsLimit c₃) :
    (G.obj c₁.pt).obj c₂.pt ≅ c₃.pt :=
  IsLimit.conePointUniqueUpToIso (isLimitOfPreserves₂ G hc₁ hc₂) hc₃

section

variable {c₁ : Cone K₁} (hc₁ : IsLimit c₁)
  {c₂ : Cone K₂} (hc₂ : IsLimit c₂)
  {c₃ : Cone <| uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G)}
  (hc₃ : IsLimit c₃)

set_option backward.isDefEq.respectTransparency false in
/-- Characterize the forward direction of the isomorphism
`PreservesLimit₂.isoObjConePointsOfIsLimit` w.r.t. the canonical maps to the limit. -/
@[reassoc (attr := simp)]
/--
lemma `isoObjConePointsOfIsLimit_hom_comp_π` / 引理 `isoObjConePointsOfIsLimit_hom_comp_π`

English:
lemma isoObjConePointsOfIsLimit_hom_comp_π
  given: (j : J₁ × J₂)
  proof: by
  dsimp [isoObjConePointsOfIsLimit, Functor.mapCocone₂]
  cat_disch

中文:
引理 isoObjConePointsOfIsLimit_hom_comp_π
  条件: (j : J₁ × J₂)
  证明: by
  dsimp [isoObjConePointsOfIsLimit, Functor.mapCocone₂]
  cat_disch

Depends on / 依赖: Functor, Functor.mapCocone, cat_disch, isoObjConePointsOfIsLimit
-/
lemma isoObjConePointsOfIsLimit_hom_comp_π (j : J₁ × J₂) :
    (isoObjConePointsOfIsLimit G hc₁ hc₂ hc₃).hom ≫ c₃.π.app j =
    (G.map <| c₁.π.app j.1).app c₂.pt ≫ (G.obj <| K₁.obj j.1).map (c₂.π.app j.2) := by
  dsimp [isoObjConePointsOfIsLimit, Functor.mapCocone₂]
  cat_disch

set_option backward.isDefEq.respectTransparency false in
/-- Characterize the inverse direction of the isomorphism
`PreservesLimit₂.isoObjConePointsOfIsLimit` w.r.t. the canonical maps to the limit. -/
@[reassoc (attr := simp)]
/--
lemma `isoObjConePointsOfIsColimit_inv_comp_map_π` / 引理 `isoObjConePointsOfIsColimit_inv_comp_map_π`

English:
lemma isoObjConePointsOfIsColimit_inv_comp_map_π
  given: (j : J₁ × J₂)
  proof: by
  rw [Iso.inv_comp_eq]
  simp

中文:
引理 isoObjConePointsOfIsColimit_inv_comp_map_π
  条件: (j : J₁ × J₂)
  证明: by
  rw [Iso.inv_comp_eq]
  simp

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
lemma isoObjConePointsOfIsColimit_inv_comp_map_π (j : J₁ × J₂) :
    (isoObjConePointsOfIsLimit G hc₁ hc₂ hc₃).inv ≫
      (G.map (c₁.π.app j.1)).app c₂.pt ≫ (G.obj <| K₁.obj j.1).map (c₂.π.app j.2) =
    c₃.π.app j := by
  rw [Iso.inv_comp_eq]
  simp

end

section

variable (K₁) (K₂) [HasLimit K₁] [HasLimit K₂]

/--
Definition of `isoLimitUncurryWhiskeringLeft₂` / `isoLimitUncurryWhiskeringLeft₂` 的定义

English:
definition isoLimitUncurryWhiskeringLeft₂
  signature: :
  body: isoObjConePointsOfIsLimit G
.symm (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)

#adaptation_note

中文:
定义 isoLimitUncurryWhiskeringLeft₂
  签名: :
  定义体: isoObjConePointsOfIsLimit G
.symm (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)

#adaptation_note

Depends on / 依赖: isLimit, isoObjConePointsOfIsLimit, limit.isLimit
-/
noncomputable def isoLimitUncurryWhiskeringLeft₂ :
    limit (uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G)) ≅
    (G.obj <| limit K₁).obj (limit K₂) :=
  isoObjConePointsOfIsLimit G
.symm (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Characterize the inverse direction of the isomorphism
`PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂` w.r.t. the canonical maps to the limit. -/
@[reassoc (attr := simp)]
/--
lemma `isoLimitUncurryWhiskeringLeft₂_inv_comp_π` / 引理 `isoLimitUncurryWhiskeringLeft₂_inv_comp_π`

English:
lemma isoLimitUncurryWhiskeringLeft₂_inv_comp_π
  given: (j : J₁ × J₂)
  proof: isoObjConePointsOfIsLimit_hom_comp_π G
    (limit.isLimit _) (limit.isLimit _) (limit.isLimit _) _

中文:
引理 isoLimitUncurryWhiskeringLeft₂_inv_comp_π
  条件: (j : J₁ × J₂)
  证明: isoObjConePointsOfIsLimit_hom_comp_π G
    (limit.isLimit _) (limit.isLimit _) (limit.isLimit _) _

Depends on / 依赖: isLimit, limit.isLimit
-/
lemma isoLimitUncurryWhiskeringLeft₂_inv_comp_π (j : J₁ × J₂) :
    (PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂ K₁ K₂ G).inv ≫
      limit.π (uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G)) j =
    (G.map <| limit.π K₁ j.1).app (limit K₂) ≫ (G.obj <| K₁.obj j.1).map (limit.π K₂ j.2) :=
  isoObjConePointsOfIsLimit_hom_comp_π G
    (limit.isLimit _) (limit.isLimit _) (limit.isLimit _) _

/-- Characterize the forward direction of the isomorphism
`PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂` w.r.t. the canonical maps to the limit. -/
@[reassoc (attr := simp)]
/--
lemma `isoLimitUncurryWhiskeringLeft₂_hom_comp_map_π` / 引理 `isoLimitUncurryWhiskeringLeft₂_hom_comp_map_π`

English:
lemma isoLimitUncurryWhiskeringLeft₂_hom_comp_map_π
  given: (j : J₁ × J₂)
  proof: isoObjConePointsOfIsColimit_inv_comp_map_π G
    (limit.isLimit _) (limit.isLimit _) (limit.isLimit _) _

中文:
引理 isoLimitUncurryWhiskeringLeft₂_hom_comp_map_π
  条件: (j : J₁ × J₂)
  证明: isoObjConePointsOfIsColimit_inv_comp_map_π G
    (limit.isLimit _) (limit.isLimit _) (limit.isLimit _) _

Depends on / 依赖: isLimit, limit.isLimit
-/
lemma isoLimitUncurryWhiskeringLeft₂_hom_comp_map_π (j : J₁ × J₂) :
    (PreservesLimit₂.isoLimitUncurryWhiskeringLeft₂ K₁ K₂ G).hom ≫
      (G.map (limit.π K₁ j.1)).app (limit K₂) ≫ (G.obj <| K₁.obj j.1).map (limit.π K₂ j.2) =
    limit.π (uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G)) j :=
  isoObjConePointsOfIsColimit_inv_comp_map_π G
    (limit.isLimit _) (limit.isLimit _) (limit.isLimit _) _

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `of_preservesLimits_in_each_variable` / 实例 `of_preservesLimits_in_each_variable`

English:
instance of_preservesLimits_in_each_variable
  body: let Q₀ : DiagramOfCones (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      { obj j₁ := G.obj (K₁.obj j₁) |>.mapCone c₂
        map f := { hom := G.map (K₁.map f) |>.app c₂.pt } }
    let P : forall j₁, IsLimit (Q₀.obj j₁) := fun _ => isLimitOfPreserves _ hc₂
    let E₀ : Q₀.conePoints ≅ K₁ ⋙ G.flip.obj c₂.pt := NatIso.ofComponents (fun _ => Iso.refl _)
    let E₁ : (Cone.postcompose E₀.hom).obj (coneOfConeUncurry P <| G.mapCone₂ c₁ c₂) ≅
        (G.flip.obj c₂.pt).mapCone c₁ :=
      Cone.ext
        (Iso.refl _)
        (fun j₁ => by
          dsimp [E₀, Q₀]
          simp only [id_comp, comp_id]
          let s : Cone (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G |>.obj j₁) := ?_
          change (P j₁).lift s = _
          symm
          apply (P j₁).hom_ext
          intro j₂
          have := (P j₁).fac s j₂
          simp only [whiskeringLeft₂_obj_obj_obj_obj_obj,
            Functor.mapCone_pt, Functor.mapCone_π_app, s, Q₀] at this
          simp only [whiskeringLeft₂_obj_obj_obj_obj_obj,
            Functor.mapCone_pt, Functor.mapCone_π_app, this, Q₀, s])
⟨IsLimit.ofConeOfConeUncurry P IsLimit.postcomposeHomEquiv E₀ _
      IsLimit.ofIsoLimit (isLimitOfPreserves _ hc₁) E₁.symm⟩

中文:
实例 of_preservesLimits_in_each_variable
  定义体: let Q₀ : DiagramOfCones (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      { obj j₁ := G.obj (K₁.obj j₁) |>.mapCone c₂
        map f := { hom := G.map (K₁.map f) |>.app c₂.pt } }
    let P : forall j₁, IsLimit (Q₀.obj j₁) := fun _ => isLimitOfPreserves _ hc₂
    let E₀ : Q₀.conePoints ≅ K₁ ⋙ G.flip.obj c₂.pt := NatIso.ofComponents (fun _ => Iso.refl _)
    let E₁ : (Cone.postcompose E₀.hom).obj (coneOfConeUncurry P <| G.mapCone₂ c₁ c₂) ≅
        (G.flip.obj c₂.pt).mapCone c₁ :=
      Cone.ext
        (Iso.refl _)
        (fun j₁ => by
          dsimp [E₀, Q₀]
          simp only [id_comp, comp_id]
          let s : Cone (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G |>.obj j₁) := ?_
          change (P j₁).lift s = _
          symm
          apply (P j₁).hom_ext
          intro j₂
          have := (P j₁).fac s j₂
          simp only [whiskeringLeft₂_obj_obj_obj_obj_obj,
            Functor.mapCone_pt, Functor.mapCone_π_app, s, Q₀] at this
          simp only [whiskeringLeft₂_obj_obj_obj_obj_obj,
            Functor.mapCone_pt, Functor.mapCone_π_app, this, Q₀, s])
⟨IsLimit.ofConeOfConeUncurry P IsLimit.postcomposeHomEquiv E₀ _
      IsLimit.ofIsoLimit (isLimitOfPreserves _ hc₁) E₁.symm⟩

Depends on / 依赖: Cone.ext, Cone.postcompose, DiagramOfCones, G.flip.obj, G.map, G.mapCone, G.obj, IsLimit, Iso.refl, NatIso, NatIso.ofComponents, coneOfConeUncurry, conePoints, isLimitOfPreserves, mapCone, ofComponents, postcompose
-/
instance of_preservesLimits_in_each_variable
    [forall x : C₂, PreservesLimit K₁ (G.flip.obj x)] [forall x : C₁, PreservesLimit K₂ (G.obj x)] :
    PreservesLimit₂ K₁ K₂ G where
  nonempty_isLimit_mapCone₂ {c₁} hc₁ {c₂} hc₂ :=
    let Q₀ : DiagramOfCones (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      { obj j₁ := G.obj (K₁.obj j₁) |>.mapCone c₂
        map f := { hom := G.map (K₁.map f) |>.app c₂.pt } }
    let P : forall j₁, IsLimit (Q₀.obj j₁) := fun _ => isLimitOfPreserves _ hc₂
    let E₀ : Q₀.conePoints ≅ K₁ ⋙ G.flip.obj c₂.pt := NatIso.ofComponents (fun _ => Iso.refl _)
    let E₁ : (Cone.postcompose E₀.hom).obj (coneOfConeUncurry P <| G.mapCone₂ c₁ c₂) ≅
        (G.flip.obj c₂.pt).mapCone c₁ :=
      Cone.ext
        (Iso.refl _)
        (fun j₁ => by
          dsimp [E₀, Q₀]
          simp only [id_comp, comp_id]
          let s : Cone (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G |>.obj j₁) := ?_
          change (P j₁).lift s = _
          symm
          apply (P j₁).hom_ext
          intro j₂
          have := (P j₁).fac s j₂
          simp only [whiskeringLeft₂_obj_obj_obj_obj_obj,
            Functor.mapCone_pt, Functor.mapCone_π_app, s, Q₀] at this
          simp only [whiskeringLeft₂_obj_obj_obj_obj_obj,
            Functor.mapCone_pt, Functor.mapCone_π_app, this, Q₀, s])
⟨IsLimit.ofConeOfConeUncurry P IsLimit.postcomposeHomEquiv E₀ _
      IsLimit.ofIsoLimit (isLimitOfPreserves _ hc₁) E₁.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `of_preservesLimit₂_flip` / 定理 `of_preservesLimit₂_flip`

English:
theorem of_preservesLimit₂_flip
  statement: PreservesLimit₂ K₂ K₁ G.flip where
  proof: by
    constructor
    let E₀ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G).flip :=
      Iso.refl _
    let E₁ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        Prod.swap _ _ ⋙ uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      E₀ ≪≫ uncurryObjFlip _
    refine IsLimit.postcomposeHomEquiv E₁ _ ?_
    apply IsLimit.ofWhiskerEquivalence (e := Prod.braiding _ _)
.toFun refine IsLimit.equivOfNatIsoOfIso (Iso.refl _) (G.mapCone₂ c₂ c₁) _ ?_
      isLimitOfPreserves₂ G hc₂ hc₁
    exact Cone.ext (Iso.refl _) (fun ⟨j₁, j₂⟩ => by simp [E₁, E₀])

中文:
定理 of_preservesLimit₂_flip
  结论: 保持Limit₂ K₂ K₁ G.flip where
  证明: by
    constructor
    let E₀ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G).flip :=
      Iso.refl _
    let E₁ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        Prod.swap _ _ ⋙ uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      E₀ ≪≫ uncurryObjFlip _
    refine IsLimit.postcomposeHomEquiv E₁ _ ?_
    apply IsLimit.ofWhiskerEquivalence (e := Prod.braiding _ _)
.toFun refine IsLimit.equivOfNatIsoOfIso (Iso.refl _) (G.mapCone₂ c₂ c₁) _ ?_
      isLimitOfPreserves₂ G hc₂ hc₁
    exact Cone.ext (Iso.refl _) (fun ⟨j₁, j₂⟩ => by simp [E₁, E₀])

Depends on / 依赖: G.flip, IsLimit, IsLimit.equivOfNatIsoOfIso, IsLimit.ofWhiskerEquivalence, IsLimit.postcomposeHomEquiv, Iso.refl, Prod.braiding, Prod.swap, braiding, equivOfNatIsoOfIso, ofWhiskerEquivalence, postcomposeHomEquiv, uncurry, uncurry.obj, uncurryObjFlip
-/
theorem of_preservesLimit₂_flip : PreservesLimit₂ K₂ K₁ G.flip where
  nonempty_isLimit_mapCone₂ {c₁} hc₁ {c₂} hc₂ := by
    constructor
    let E₀ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G).flip :=
      Iso.refl _
    let E₁ : uncurry.obj (whiskeringLeft₂ C |>.obj K₂ |>.obj K₁ |>.obj G.flip) ≅
        Prod.swap _ _ ⋙ uncurry.obj (whiskeringLeft₂ C |>.obj K₁ |>.obj K₂ |>.obj G) :=
      E₀ ≪≫ uncurryObjFlip _
    refine IsLimit.postcomposeHomEquiv E₁ _ ?_
    apply IsLimit.ofWhiskerEquivalence (e := Prod.braiding _ _)
.toFun refine IsLimit.equivOfNatIsoOfIso (Iso.refl _) (G.mapCone₂ c₂ c₁) _ ?_
      isLimitOfPreserves₂ G hc₂ hc₁
    exact Cone.ext (Iso.refl _) (fun ⟨j₁, j₂⟩ => by simp [E₁, E₀])

end PreservesLimit₂

end Limits

end CategoryTheory
