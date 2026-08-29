/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Isomorphisms about functors which preserve (co)limits

If `G` preserves limits, and `C` and `D` have limits, then for any diagram `F : J ⥤ C` we have a
canonical isomorphism `preservesLimitsIso : G.obj (Limit F) ≅ Limit (F ⋙ G)`.
We also show that we can commute `IsLimit.lift` of a preserved limit with `Functor.mapCone`:
`(PreservesLimit.preserves t).lift (G.mapCone c₂) = G.map (t.lift c₂)`.

The duals of these are also given. For functors which preserve (co)limits of specific shapes, see
the files in the directory `Mathlib/CategoryTheory/Limits/Preserves/Shapes/`.
-/

@[expose] public section


universe w' w v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
variable {J : Type w} [Category.{w'} J]
variable (F : J ⥤ C)

section

variable [PreservesLimit F G]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `preserves_lift_mapCone` / 定理 `preserves_lift_mapCone`

English:
theorem preserves_lift_mapCone
  given: (c₁ c₂ : Cone F) (t : IsLimit c₁)
  proof: ((isLimitOfPreserves G t).uniq (G.mapCone c₂) _ (by simp [← G.map_comp])).symm

中文:
定理 preserves_lift_mapCone
  条件: (c₁ c₂ : 锥 F) (t : 是极限 c₁)
  证明: ((isLimitOfPreserves G t).uniq (G.mapCone c₂) _ (by simp [← G.map_comp])).symm

Depends on / 依赖: G.mapCone, G.map_comp, isLimitOfPreserves, mapCone, map_comp
-/
theorem preserves_lift_mapCone (c₁ c₂ : Cone F) (t : IsLimit c₁) :
    (isLimitOfPreserves G t).lift (G.mapCone c₂) = G.map (t.lift c₂) :=
  ((isLimitOfPreserves G t).uniq (G.mapCone c₂) _ (by simp [← G.map_comp])).symm

variable [HasLimit F]

/--
Definition of `preservesLimitIso` / `preservesLimitIso` 的定义

English:
definition preservesLimitIso
  signature: : G.obj (limit F) ≅ limit (F ⋙ G)
  body: (isLimitOfPreserves G (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]

中文:
定义 preservesLimitIso
  签名: : G.obj (limit F) ≅ limit (F ⋙ G)
  定义体: (isLimitOfPreserves G (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]

Depends on / 依赖: conePointUniqueUpToIso, isLimit, isLimitOfPreserves, limit.isLimit
-/
def preservesLimitIso : G.obj (limit F) ≅ limit (F ⋙ G) :=
  (isLimitOfPreserves G (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
/--
theorem `preservesLimitIso_hom_π` / 定理 `preservesLimitIso_hom_π`

English:
theorem preservesLimitIso_hom_π
  given: (j)
  proof: IsLimit.conePointUniqueUpToIso_hom_comp _ _ j

@[reassoc (attr := simp)]

中文:
定理 preservesLimitIso_hom_π
  条件: (j)
  证明: IsLimit.conePointUniqueUpToIso_hom_comp _ _ j

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, conePointUniqueUpToIso_hom_comp
-/
theorem preservesLimitIso_hom_π (j) :
    (preservesLimitIso G F).hom ≫ limit.π _ j = G.map (limit.π F j) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ j

@[reassoc (attr := simp)]
/--
theorem `preservesLimitIso_inv_π` / 定理 `preservesLimitIso_inv_π`

English:
theorem preservesLimitIso_inv_π
  given: (j)
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ _ j

中文:
定理 preservesLimitIso_inv_π
  条件: (j)
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ _ j

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp
-/
theorem preservesLimitIso_inv_π (j) :
    (preservesLimitIso G F).inv ≫ G.map (limit.π F j) = limit.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ j

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `lift_comp_preservesLimitIso_hom` / 定理 `lift_comp_preservesLimitIso_hom`

English:
theorem lift_comp_preservesLimitIso_hom
  given: (t : Cone F)
  proof: by
  ext
  simp [← G.map_comp]

中文:
定理 lift_comp_preservesLimitIso_hom
  条件: (t : 锥 F)
  证明: by
  ext
  simp [← G.map_comp]

Depends on / 依赖: G.map_comp, map_comp
-/
theorem lift_comp_preservesLimitIso_hom (t : Cone F) :
    G.map (limit.lift _ t) ≫ (preservesLimitIso G F).hom =
    limit.lift (F ⋙ G) (G.mapCone _) := by
  ext
  simp [← G.map_comp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (limit.post F G)
  body: show IsIso (preservesLimitIso G F).hom from inferInstance

中文:
实例 :
  签名: 是同构 (limit.post F G)
  定义体: show IsIso (preservesLimitIso G F).hom from inferInstance
-/
instance : IsIso (limit.post F G) :=
  show IsIso (preservesLimitIso G F).hom from inferInstance

variable [PreservesLimitsOfShape J G] [HasLimitsOfShape J D] [HasLimitsOfShape J C]

set_option backward.defeqAttrib.useBackward true in
/-- If `C, D` has all limits of shape `J`, and `G` preserves them, then `preservesLimitsIso` is
functorial w.r.t. `F`. -/
@[simps!]
/--
Definition of `preservesLimitNatIso` / `preservesLimitNatIso` 的定义

English:
definition preservesLimitNatIso
  signature: : lim ⋙ G ≅ (Functor.whiskeringRight J C D).obj G ⋙ lim
  body: NatIso.ofComponents (fun F => preservesLimitIso G F)
    (by
      intro _ _ f
      apply limit.hom_ext; intro j
      dsimp
      simp only [preservesLimitIso_hom_π, Functor.whiskerRight_app, limMap_π, Category.assoc,
        preservesLimitIso_hom_π_assoc, ← G.map_comp])

中文:
定义 preservesLimit自然数Iso
  签名: : lim ⋙ G ≅ (函子.whiskeringRight J C D).obj G ⋙ lim
  定义体: NatIso.ofComponents (fun F => preservesLimitIso G F)
    (by
      intro _ _ f
      apply limit.hom_ext; intro j
      dsimp
      simp only [preservesLimitIso_hom_π, Functor.whiskerRight_app, limMap_π, Category.assoc,
        preservesLimitIso_hom_π_assoc, ← G.map_comp])

Depends on / 依赖: Category, Category.assoc, Functor, Functor.whiskerRight_app, G.map_comp, NatIso, NatIso.ofComponents, hom_ext, limit.hom_ext, map_comp, ofComponents, preservesLimitIso, whiskerRight_app
-/
def preservesLimitNatIso : lim ⋙ G ≅ (Functor.whiskeringRight J C D).obj G ⋙ lim :=
  NatIso.ofComponents (fun F => preservesLimitIso G F)
    (by
      intro _ _ f
      apply limit.hom_ext; intro j
      dsimp
      simp only [preservesLimitIso_hom_π, Functor.whiskerRight_app, limMap_π, Category.assoc,
        preservesLimitIso_hom_π_assoc, ← G.map_comp])

end

section

variable [HasLimit F] [HasLimit (F ⋙ G)]

/--
lemma `preservesLimit_of_isIso_post` / 引理 `preservesLimit_of_isIso_post`

English:
lemma preservesLimit_of_isIso_post
  given: [IsIso (limit.post F G)]
  statement: PreservesLimit F G
  proof: preservesLimit_of_preserves_limit_cone (limit.isLimit F) (by
    convert! IsLimit.ofPointIso (limit.isLimit (F ⋙ G))
    assumption)

中文:
引理 preservesLimit_of_isIso_post
  条件: [是同构 (limit.post F G)]
  结论: 保持极限 F G
  证明: preservesLimit_of_preserves_limit_cone (limit.isLimit F) (by
    convert! IsLimit.ofPointIso (limit.isLimit (F ⋙ G))
    assumption)

Depends on / 依赖: IsLimit, IsLimit.ofPointIso, convert, isLimit, limit.isLimit, ofPointIso, preservesLimit_of_preserves_limit_cone
-/
lemma preservesLimit_of_isIso_post [IsIso (limit.post F G)] : PreservesLimit F G :=
  preservesLimit_of_preserves_limit_cone (limit.isLimit F) (by
    convert! IsLimit.ofPointIso (limit.isLimit (F ⋙ G))
    assumption)

end

section

variable [PreservesColimit F G]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `preserves_desc_mapCocone` / 定理 `preserves_desc_mapCocone`

English:
theorem preserves_desc_mapCocone
  given: (c₁ c₂ : Cocone F) (t : IsColimit c₁)
  proof: ((isColimitOfPreserves G t).uniq (G.mapCocone _) _ (by simp [← G.map_comp])).symm

中文:
定理 preserves_desc_mapCocone
  条件: (c₁ c₂ : 余锥 F) (t : 是余极限 c₁)
  证明: ((isColimitOfPreserves G t).uniq (G.mapCocone _) _ (by simp [← G.map_comp])).symm

Depends on / 依赖: G.mapCocone, G.map_comp, isColimitOfPreserves, mapCocone, map_comp
-/
theorem preserves_desc_mapCocone (c₁ c₂ : Cocone F) (t : IsColimit c₁) :
    (isColimitOfPreserves G t).desc (G.mapCocone _) = G.map (t.desc c₂) :=
  ((isColimitOfPreserves G t).uniq (G.mapCocone _) _ (by simp [← G.map_comp])).symm

variable [HasColimit F]

-- TODO: think about swapping the order here
/--
Definition of `preservesColimitIso` / `preservesColimitIso` 的定义

English:
definition preservesColimitIso
  signature: : G.obj (colimit F) ≅ colimit (F ⋙ G)
  body: (isColimitOfPreserves G (colimit.isColimit _)).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]

中文:
定义 preservesColimitIso
  签名: : G.obj (colimit F) ≅ colimit (F ⋙ G)
  定义体: (isColimitOfPreserves G (colimit.isColimit _)).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]

Depends on / 依赖: coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, isColimitOfPreserves
-/
def preservesColimitIso : G.obj (colimit F) ≅ colimit (F ⋙ G) :=
  (isColimitOfPreserves G (colimit.isColimit _)).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]
/--
theorem `ι_preservesColimitIso_inv` / 定理 `ι_preservesColimitIso_inv`

English:
theorem ι_preservesColimitIso_inv
  given: (j : J)
  proof: IsColimit.comp_coconePointUniqueUpToIso_inv _ (colimit.isColimit (F ⋙ G)) j

@[reassoc (attr := simp)]

中文:
定理 ι_preservesColimitIso_inv
  条件: (j : J)
  证明: IsColimit.comp_coconePointUniqueUpToIso_inv _ (colimit.isColimit (F ⋙ G)) j

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_inv, colimit, colimit.isColimit, comp_coconePointUniqueUpToIso_inv, isColimit
-/
theorem ι_preservesColimitIso_inv (j : J) :
    colimit.ι _ j ≫ (preservesColimitIso G F).inv = G.map (colimit.ι F j) :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ (colimit.isColimit (F ⋙ G)) j

@[reassoc (attr := simp)]
/--
theorem `ι_preservesColimitIso_hom` / 定理 `ι_preservesColimitIso_hom`

English:
theorem ι_preservesColimitIso_hom
  given: (j : J)
  proof: (isColimitOfPreserves G (colimit.isColimit _)).comp_coconePointUniqueUpToIso_hom _ j

中文:
定理 ι_preservesColimitIso_hom
  条件: (j : J)
  证明: (isColimitOfPreserves G (colimit.isColimit _)).comp_coconePointUniqueUpToIso_hom _ j

Depends on / 依赖: colimit, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, isColimit, isColimitOfPreserves
-/
theorem ι_preservesColimitIso_hom (j : J) :
    G.map (colimit.ι F j) ≫ (preservesColimitIso G F).hom = colimit.ι (F ⋙ G) j :=
  (isColimitOfPreserves G (colimit.isColimit _)).comp_coconePointUniqueUpToIso_hom _ j

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `preservesColimitIso_inv_comp_desc` / 定理 `preservesColimitIso_inv_comp_desc`

English:
theorem preservesColimitIso_inv_comp_desc
  given: (t : Cocone F)
  proof: by
  ext
  simp [← G.map_comp]

中文:
定理 preservesColimitIso_inv_comp_desc
  条件: (t : 余锥 F)
  证明: by
  ext
  simp [← G.map_comp]

Depends on / 依赖: G.map_comp, map_comp
-/
theorem preservesColimitIso_inv_comp_desc (t : Cocone F) :
    (preservesColimitIso G F).inv ≫ G.map (colimit.desc _ t) =
    colimit.desc _ (G.mapCocone t) := by
  ext
  simp [← G.map_comp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (colimit.post F G)
  body: show IsIso (preservesColimitIso G F).inv from inferInstance

中文:
实例 :
  签名: 是同构 (colimit.post F G)
  定义体: show IsIso (preservesColimitIso G F).inv from inferInstance

Depends on / 依赖: preservesColimitIso
-/
instance : IsIso (colimit.post F G) :=
  show IsIso (preservesColimitIso G F).inv from inferInstance

variable [PreservesColimitsOfShape J G] [HasColimitsOfShape J D] [HasColimitsOfShape J C]

set_option backward.defeqAttrib.useBackward true in
/-- If `C, D` has all colimits of shape `J`, and `G` preserves them, then `preservesColimitIso`
is functorial w.r.t. `F`. -/
@[simps!]
/--
Definition of `preservesColimitNatIso` / `preservesColimitNatIso` 的定义

English:
definition preservesColimitNatIso
  signature: : colim ⋙ G ≅ (Functor.whiskeringRight J C D).obj G ⋙ colim
  body: NatIso.ofComponents (fun F => preservesColimitIso G F)
    (by
      intro _ _ f
      rw [← Iso.inv_comp_eq]; rw [← Category.assoc]; rw [← Iso.eq_comp_inv]
      apply colimit.hom_ext; intro j
      dsimp
      rw [ι_colimMap_assoc]
      simp only [ι_preservesColimitIso_inv, Functor.whiskerRight_a

中文:
定义 preservesColimit自然数Iso
  签名: : colim ⋙ G ≅ (函子.whiskeringRight J C D).obj G ⋙ colim
  定义体: NatIso.ofComponents (fun F => preservesColimitIso G F)
    (by
      intro _ _ f
      rw [← Iso.inv_comp_eq]; rw [← Category.assoc]; rw [← Iso.eq_comp_inv]
      apply colimit.hom_ext; intro j
      dsimp
      rw [ι_colimMap_assoc]
      simp only [ι_preservesColimitIso_inv, Functor.whiskerRight_a

Depends on / 依赖: Category, Category.assoc, Functor, Functor.whiskerRight_app, G.map_comp, Iso.eq_comp_inv, Iso.inv_comp_eq, NatIso, NatIso.ofComponents, colimit, colimit.hom_ext, eq_comp_inv, hom_ext, inv_comp_eq, map_comp, ofComponents, preservesColimitIso, whiskerRight_app
-/
def preservesColimitNatIso : colim ⋙ G ≅ (Functor.whiskeringRight J C D).obj G ⋙ colim :=
  NatIso.ofComponents (fun F => preservesColimitIso G F)
    (by
      intro _ _ f
      rw [← Iso.inv_comp_eq]; rw [← Category.assoc]; rw [← Iso.eq_comp_inv]
      apply colimit.hom_ext; intro j
      dsimp
      rw [ι_colimMap_assoc]
      simp only [ι_preservesColimitIso_inv, Functor.whiskerRight_app,
        ι_preservesColimitIso_inv_assoc, ← G.map_comp]
      rw [ι_colimMap])

end

section

variable [HasColimit F] [HasColimit (F ⋙ G)]

/--
lemma `preservesColimit_of_isIso_post` / 引理 `preservesColimit_of_isIso_post`

English:
lemma preservesColimit_of_isIso_post
  given: [IsIso (colimit.post F G)]
  statement: PreservesColimit F G
  proof: preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) (by
    convert! IsColimit.ofPointIso (colimit.isColimit (F ⋙ G))
    assumption)

中文:
引理 preservesColimit_of_isIso_post
  条件: [是同构 (colimit.post F G)]
  结论: 保持余极限 F G
  证明: preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) (by
    convert! IsColimit.ofPointIso (colimit.isColimit (F ⋙ G))
    assumption)

Depends on / 依赖: IsColimit, IsColimit.ofPointIso, colimit, colimit.isColimit, convert, isColimit, ofPointIso, preservesColimit_of_preserves_colimit_cocone
-/
lemma preservesColimit_of_isIso_post [IsIso (colimit.post F G)] : PreservesColimit F G :=
  preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) (by
    convert! IsColimit.ofPointIso (colimit.isColimit (F ⋙ G))
    assumption)

end

end CategoryTheory
