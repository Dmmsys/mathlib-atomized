/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Connected limits

A connected limit is a limit whose shape is a connected category.

We show that constant functors from a connected category have a limit
and a colimit. From this we deduce that a cocone `c` over a connected diagram
is a colimit cocone if and only if `colimMap c.ι` is an isomorphism (where
`c.ι : F ⟶ const c.pt` is the natural transformation that defines the
cocone).

We give examples of connected categories, and prove
that the functor given by `(X × -)` preserves any connected limit.
That is, any limit of shape `J` where `J` is a connected category is
preserved by the functor `(X × -)`.
-/

@[expose] public section


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

section Const

namespace Limits

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C] (X : C)

section

variable (J)

/-- The obvious cone of a constant functor. -/
@[simps]
/--
Definition of `constCone` / `constCone` 的定义

English:
definition constCone
  signature: : Cone ((Functor.const J).obj X) where
  body: X
  π := 𝟙 _

中文:
定义 constCone
  签名: : 锥 ((函子.const J).obj X) where
  定义体: X
  π := 𝟙 _
-/
def constCone : Cone ((Functor.const J).obj X) where
  pt := X
  π := 𝟙 _

/-- The obvious cocone of a constant functor. -/
@[simps]
/--
Definition of `constCocone` / `constCocone` 的定义

English:
definition constCocone
  signature: : Cocone ((Functor.const J).obj X) where
  body: X
  ι := 𝟙 _

中文:
定义 constCocone
  签名: : 余锥 ((函子.const J).obj X) where
  定义体: X
  ι := 𝟙 _
-/
def constCocone : Cocone ((Functor.const J).obj X) where
  pt := X
  ι := 𝟙 _

variable [IsConnected J]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitConstCone` / `isLimitConstCone` 的定义

English:
definition isLimitConstCone
  signature: : IsLimit (constCone J X) where
  body: s.π.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [comp_id]
    exact constant_of_preserves_morphisms _
      (fun _ _ f => by simpa using s.w f) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)

中文:
定义 isLimitConstCone
  签名: : 是极限 (constCone J X) where
  定义体: s.π.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [comp_id]
    exact constant_of_preserves_morphisms _
      (fun _ _ f => by simpa using s.w f) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
def isLimitConstCone : IsLimit (constCone J X) where
  lift s := s.π.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [comp_id]
    exact constant_of_preserves_morphisms _
      (fun _ _ f => by simpa using s.w f) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitConstCocone` / `isColimitConstCocone` 的定义

English:
definition isColimitConstCocone
  signature: : IsColimit (constCocone J X) where
  body: s.ι.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [id_comp]
    exact constant_of_preserves_morphisms _
      (fun _ _ f => by simpa using (s.w f).symm) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)

中文:
定义 isColimitConstCocone
  签名: : 是余极限 (constCocone J X) where
  定义体: s.ι.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [id_comp]
    exact constant_of_preserves_morphisms _
      (fun _ _ f => by simpa using (s.w f).symm) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
def isColimitConstCocone : IsColimit (constCocone J X) where
  desc s := s.ι.app (Classical.arbitrary _)
  fac s j := by
    dsimp
    rw [id_comp]
    exact constant_of_preserves_morphisms _
      (fun _ _ f => by simpa using (s.w f).symm) _ _
  uniq s m hm := by simpa using hm (Classical.arbitrary _)

/--
Instance `hasLimit_const_of_isConnected` / 实例 `hasLimit_const_of_isConnected`

English:
instance hasLimit_const_of_isConnected
  signature: : HasLimit ((Functor.const J).obj X)
  body: ⟨_, isLimitConstCone J X⟩

中文:
实例 hasLimit_const_of_isConnected
  签名: : 有极限 ((函子.const J).obj X)
  定义体: ⟨_, isLimitConstCone J X⟩

Depends on / 依赖: isLimitConstCone
-/
instance hasLimit_const_of_isConnected : HasLimit ((Functor.const J).obj X) :=
  ⟨_, isLimitConstCone J X⟩

/--
Instance `hasColimit_const_of_isConnected` / 实例 `hasColimit_const_of_isConnected`

English:
instance hasColimit_const_of_isConnected
  signature: : HasColimit ((Functor.const J).obj X)
  body: ⟨_, isColimitConstCocone J X⟩

中文:
实例 hasColimit_const_of_isConnected
  签名: : 有余极限 ((函子.const J).obj X)
  定义体: ⟨_, isColimitConstCocone J X⟩

Depends on / 依赖: isColimitConstCocone
-/
instance hasColimit_const_of_isConnected : HasColimit ((Functor.const J).obj X) :=
  ⟨_, isColimitConstCocone J X⟩

end

section

variable [IsConnected J]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Cone.isLimitOfIsIsoLimMapπ` / `Cone.isLimitOfIsIsoLimMapπ` 的定义

English:
definition Cone.isLimitOfIsIsoLimMapπ
  signature: {F : J ⥤ C} [HasLimit F] (c : Cone F)
  body: by
  refine IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext ((asIso (limMap c.π)).symm ≪≫
    (limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone J c.pt)) ?_)
  intro j
  simp only [limit.cone_x, limit.cone_π, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, assoc, IsIso.eq_inv_comp, limMap_π]
  congr 1
  simp [← Iso.inv_comp_eq_id]

中文:
定义 锥.isLimitOfIsIsoLimMapπ
  签名: {F : J ⥤ C} [有极限 F] (c : 锥 F)
  定义体: by
  refine IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext ((asIso (limMap c.π)).symm ≪≫
    (limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone J c.pt)) ?_)
  intro j
  simp only [limit.cone_x, limit.cone_π, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, assoc, IsIso.eq_inv_comp, limMap_π]
  congr 1
  simp [← Iso.inv_comp_eq_id]

Depends on / 依赖: Cone.ext, IsIso.eq_inv_comp, IsLimit, IsLimit.ofIsoLimit, Iso.inv_comp_eq_id, Iso.symm_hom, Iso.trans_hom, asIso_inv, c.pt, conePointUniqueUpToIso, cone_x, eq_inv_comp, inv_comp_eq_id, isLimit, isLimitConstCone, limMap, limit.cone_, limit.cone_x, limit.isLimit, ofIsoLimit
-/
def Cone.isLimitOfIsIsoLimMapπ {F : J ⥤ C} [HasLimit F] (c : Cone F)
    [IsIso (limMap c.π)] : IsLimit c := by
  refine IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext ((asIso (limMap c.π)).symm ≪≫
    (limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone J c.pt)) ?_)
  intro j
  simp only [limit.cone_x, limit.cone_π, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, assoc, IsIso.eq_inv_comp, limMap_π]
  congr 1
  simp [← Iso.inv_comp_eq_id]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsLimit.isIso_limMap_π` / 定理 `IsLimit.isIso_limMap_π`

English:
theorem IsLimit.isIso_limMap_π
  given: {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
  proof: by
  suffices limMap c.π = ((limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone J c.pt) ≪≫
      hc.conePointUniqueUpToIso (limit.isLimit _)).hom by
    rw [this]; infer_instance
  ext j
  simp only [limMap_π, limit.cone_x, Iso.trans_hom, assoc,
    limit.conePointUniqueUpToIso_hom_comp]
  congr 1
  simp [← Iso.inv_comp_eq_id]

中文:
定理 是极限.isIso_limMap_π
  条件: {F : J ⥤ C} [有极限 F] {c : 锥 F} (hc : 是极限 c)
  证明: by
  suffices limMap c.π = ((limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone J c.pt) ≪≫
      hc.conePointUniqueUpToIso (limit.isLimit _)).hom by
    rw [this]; infer_instance
  ext j
  simp only [limMap_π, limit.cone_x, Iso.trans_hom, assoc,
    limit.conePointUniqueUpToIso_hom_comp]
  congr 1
  simp [← Iso.inv_comp_eq_id]

Depends on / 依赖: Iso.inv_comp_eq_id, Iso.trans_hom, c.pt, conePointUniqueUpToIso, conePointUniqueUpToIso_hom_comp, cone_x, hc.conePointUniqueUpToIso, infer_instance, inv_comp_eq_id, isLimit, isLimitConstCone, limMap, limit.conePointUniqueUpToIso_hom_comp, limit.cone_x, limit.isLimit, trans_hom
-/
theorem IsLimit.isIso_limMap_π {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c) :
    IsIso (limMap c.π) := by
  suffices limMap c.π = ((limit.isLimit _).conePointUniqueUpToIso (isLimitConstCone J c.pt) ≪≫
      hc.conePointUniqueUpToIso (limit.isLimit _)).hom by
    rw [this]; infer_instance
  ext j
  simp only [limMap_π, limit.cone_x, Iso.trans_hom, assoc,
    limit.conePointUniqueUpToIso_hom_comp]
  congr 1
  simp [← Iso.inv_comp_eq_id]

/--
theorem `Cone.isLimit_iff_isIso_limMap_π` / 定理 `Cone.isLimit_iff_isIso_limMap_π`

English:
theorem Cone.isLimit_iff_isIso_limMap_π
  given: {F : J ⥤ C} [HasLimit F] (c : Cone F)
  proof: ⟨fun ⟨h⟩ => IsLimit.isIso_limMap_π h, fun _ => ⟨c.isLimitOfIsIsoLimMapπ⟩⟩

中文:
定理 锥.isLimit_iff_isIso_limMap_π
  条件: {F : J ⥤ C} [有极限 F] (c : 锥 F)
  证明: ⟨fun ⟨h⟩ => IsLimit.isIso_limMap_π h, fun _ => ⟨c.isLimitOfIsIsoLimMapπ⟩⟩

Depends on / 依赖: IsLimit, IsLimit.isIso_limMap_, c.isLimitOfIsIsoLimMap
-/
theorem Cone.isLimit_iff_isIso_limMap_π {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    Nonempty (IsLimit c) ↔ IsIso (limMap c.π) :=
  ⟨fun ⟨h⟩ => IsLimit.isIso_limMap_π h, fun _ => ⟨c.isLimitOfIsIsoLimMapπ⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Cocone.isColimitOfIsIsoColimMapι` / `Cocone.isColimitOfIsIsoColimMapι` 的定义

English:
definition Cocone.isColimitOfIsIsoColimMapι
  signature: {F : J ⥤ C} [HasColimit F] (c : Cocone F)
  body: IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (asIso (colimMap c.ι) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J c.pt)) (by simp))

中文:
定义 余锥.isColimitOfIsIsoColimMapι
  签名: {F : J ⥤ C} [有余极限 F] (c : 余锥 F)
  定义体: IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (asIso (colimMap c.ι) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J c.pt)) (by simp))

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, c.pt, coconePointUniqueUpToIso, colimMap, colimit, colimit.isColimit, isColimit, isColimitConstCocone, ofIsoColimit
-/
def Cocone.isColimitOfIsIsoColimMapι {F : J ⥤ C} [HasColimit F] (c : Cocone F)
    [IsIso (colimMap c.ι)] : IsColimit c :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (asIso (colimMap c.ι) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J c.pt)) (by simp))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsColimit.isIso_colimMap_ι` / 定理 `IsColimit.isIso_colimMap_ι`

English:
theorem IsColimit.isIso_colimMap_ι
  given: {F : J ⥤ C} [HasColimit F] {c : Cocone F} (hc : IsColimit c)
  proof: by
  suffices colimMap c.ι = ((colimit.isColimit _).coconePointUniqueUpToIso hc ≪≫
      (isColimitConstCocone J c.pt).coconePointUniqueUpToIso (colimit.isColimit _)).hom by
    rw [this]; infer_instance
  ext j
  simp only [ι_colimMap, colimit.cocone_x, Iso.trans_hom,
    colimit.comp_coconePointUniqueUpToIso_hom_assoc]
  congr 1
  simp [← Iso.comp_inv_eq_id]

中文:
定理 是余极限.isIso_colimMap_ι
  条件: {F : J ⥤ C} [有余极限 F] {c : 余锥 F} (hc : 是余极限 c)
  证明: by
  suffices colimMap c.ι = ((colimit.isColimit _).coconePointUniqueUpToIso hc ≪≫
      (isColimitConstCocone J c.pt).coconePointUniqueUpToIso (colimit.isColimit _)).hom by
    rw [this]; infer_instance
  ext j
  simp only [ι_colimMap, colimit.cocone_x, Iso.trans_hom,
    colimit.comp_coconePointUniqueUpToIso_hom_assoc]
  congr 1
  simp [← Iso.comp_inv_eq_id]

Depends on / 依赖: Iso.comp_inv_eq_id, Iso.trans_hom, c.pt, coconePointUniqueUpToIso, cocone_x, colimMap, colimit, colimit.cocone_x, colimit.comp_coconePointUniqueUpToIso_hom_assoc, colimit.isColimit, comp_coconePointUniqueUpToIso_hom_assoc, comp_inv_eq_id, infer_instance, isColimit, isColimitConstCocone, trans_hom
-/
theorem IsColimit.isIso_colimMap_ι {F : J ⥤ C} [HasColimit F] {c : Cocone F} (hc : IsColimit c) :
    IsIso (colimMap c.ι) := by
  suffices colimMap c.ι = ((colimit.isColimit _).coconePointUniqueUpToIso hc ≪≫
      (isColimitConstCocone J c.pt).coconePointUniqueUpToIso (colimit.isColimit _)).hom by
    rw [this]; infer_instance
  ext j
  simp only [ι_colimMap, colimit.cocone_x, Iso.trans_hom,
    colimit.comp_coconePointUniqueUpToIso_hom_assoc]
  congr 1
  simp [← Iso.comp_inv_eq_id]

/--
theorem `Cocone.isColimit_iff_isIso_colimMap_ι` / 定理 `Cocone.isColimit_iff_isIso_colimMap_ι`

English:
theorem Cocone.isColimit_iff_isIso_colimMap_ι
  given: {F : J ⥤ C} [HasColimit F] (c : Cocone F)
  proof: ⟨fun ⟨h⟩ => IsColimit.isIso_colimMap_ι h, fun _ => ⟨c.isColimitOfIsIsoColimMapι⟩⟩

中文:
定理 余锥.isColimit_iff_isIso_colimMap_ι
  条件: {F : J ⥤ C} [有余极限 F] (c : 余锥 F)
  证明: ⟨fun ⟨h⟩ => IsColimit.isIso_colimMap_ι h, fun _ => ⟨c.isColimitOfIsIsoColimMapι⟩⟩

Depends on / 依赖: IsColimit, IsColimit.isIso_colimMap_, c.isColimitOfIsIsoColimMap
-/
theorem Cocone.isColimit_iff_isIso_colimMap_ι {F : J ⥤ C} [HasColimit F] (c : Cocone F) :
    Nonempty (IsColimit c) ↔ IsIso (colimMap c.ι) :=
  ⟨fun ⟨h⟩ => IsColimit.isIso_colimMap_ι h, fun _ => ⟨c.isColimitOfIsIsoColimMapι⟩⟩

end

end Limits

end Const

section Examples

/--
Instance `widePullbackShape_connected` / 实例 `widePullbackShape_connected`

English:
instance widePullbackShape_connected
  signature: (J : Type v₁)
  body: by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [t (WidePullbackShape.Hom.term _)]

中文:
实例 widePullbackShape_connected
  签名: (J : 类型v₁)
  定义体: by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [t (WidePullbackShape.Hom.term _)]

Depends on / 依赖: IsConnected, IsConnected.of_induct, WidePullbackShape, WidePullbackShape.Hom.term, introv, of_induct
-/
instance widePullbackShape_connected (J : Type v₁) : IsConnected (WidePullbackShape J) := by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [t (WidePullbackShape.Hom.term _)]

/--
Instance `widePushoutShape_connected` / 实例 `widePushoutShape_connected`

English:
instance widePushoutShape_connected
  signature: (J : Type v₁)
  body: by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [← t (WidePushoutShape.Hom.init _)]

中文:
实例 widePushoutShape_connected
  签名: (J : 类型v₁)
  定义体: by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [← t (WidePushoutShape.Hom.init _)]

Depends on / 依赖: IsConnected, IsConnected.of_induct, WidePushoutShape, WidePushoutShape.Hom.init, introv, of_induct
-/
instance widePushoutShape_connected (J : Type v₁) : IsConnected (WidePushoutShape J) := by
  apply IsConnected.of_induct
  · introv hp t
    cases j
    · exact hp
    · rwa [← t (WidePushoutShape.Hom.init _)]

/--
Instance `parallelPairInhabited` / 实例 `parallelPairInhabited`

English:
instance parallelPairInhabited
  signature: : Inhabited WalkingParallelPair
  body: ⟨WalkingParallelPair.one⟩

中文:
实例 parallelPairInhabited
  签名: : 可居 WalkingParallelPair
  定义体: ⟨WalkingParallelPair.one⟩

Depends on / 依赖: WalkingParallelPair, WalkingParallelPair.one
-/
instance parallelPairInhabited : Inhabited WalkingParallelPair :=
  ⟨WalkingParallelPair.one⟩

/--
Instance `parallel_pair_connected` / 实例 `parallel_pair_connected`

English:
instance parallel_pair_connected
  signature: : IsConnected WalkingParallelPair
  body: by
  apply IsConnected.of_induct
  · introv _ t
    cases j
    · rwa [t WalkingParallelPairHom.left]
    · assumption

中文:
实例 parallel_pair_connected
  签名: : 是连通 WalkingParallelPair
  定义体: by
  apply IsConnected.of_induct
  · introv _ t
    cases j
    · rwa [t WalkingParallelPairHom.left]
    · assumption

Depends on / 依赖: IsConnected, IsConnected.of_induct, WalkingParallelPairHom, WalkingParallelPairHom.left, introv, of_induct
-/
instance parallel_pair_connected : IsConnected WalkingParallelPair := by
  apply IsConnected.of_induct
  · introv _ t
    cases j
    · rwa [t WalkingParallelPairHom.left]
    · assumption

end Examples

variable {C : Type u₂} [Category.{v₂} C]
variable [HasBinaryProducts C]
variable {J : Type v₂} [SmallCategory J]

namespace ProdPreservesConnectedLimits

set_option backward.defeqAttrib.useBackward true in
/-- (Impl). The obvious natural transformation from (X × K -) to K. -/
@[simps]
/--
Definition of `γ₂` / `γ₂` 的定义

English:
definition γ₂
  signature: {K : J ⥤ C} (X : C)
  body: Limits.prod.snd

中文:
定义 γ₂
  签名: {K : J ⥤ C} (X : C)
  定义体: Limits.prod.snd

Depends on / 依赖: Limits, Limits.prod.snd
-/
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ K where app _ := Limits.prod.snd

set_option backward.defeqAttrib.useBackward true in
/-- (Impl). The obvious natural transformation from (X × K -) to X -/
@[simps]
/--
Definition of `γ₁` / `γ₁` 的定义

English:
definition γ₁
  signature: {K : J ⥤ C} (X : C)
  body: Limits.prod.fst

中文:
定义 γ₁
  签名: {K : J ⥤ C} (X : C)
  定义体: Limits.prod.fst

Depends on / 依赖: Limits, Limits.prod.fst
-/
def γ₁ {K : J ⥤ C} (X : C) : K ⋙ prod.functor.obj X ⟶ (Functor.const J).obj X where
  app _ := Limits.prod.fst

/-- (Impl).
Given a cone for (X × K -), produce a cone for K using the natural transformation `γ₂` -/
@[simps]
/--
Definition of `forgetCone` / `forgetCone` 的定义

English:
definition forgetCone
  signature: {X : C} {K : J ⥤ C} (s : Cone (K ⋙ prod.functor.obj X))
  body: s.pt
  π := s.π ≫ γ₂ X

中文:
定义 forgetCone
  签名: {X : C} {K : J ⥤ C} (s : 锥 (K ⋙ 乘积.functor.obj X))
  定义体: s.pt
  π := s.π ≫ γ₂ X

Depends on / 依赖: s.pt
-/
def forgetCone {X : C} {K : J ⥤ C} (s : Cone (K ⋙ prod.functor.obj X)) : Cone K where
  pt := s.pt
  π := s.π ≫ γ₂ X

end ProdPreservesConnectedLimits

open ProdPreservesConnectedLimits

set_option backward.isDefEq.respectTransparency false in
/--
lemma `prod_preservesConnectedLimits` / 引理 `prod_preservesConnectedLimits`

English:
lemma prod_preservesConnectedLimits
  given: [IsConnected J] (X : C)
  proof: { preserves := fun {c} l => ⟨{
          lift := fun s =>
            prod.lift (s.π.app (Classical.arbitrary _) ≫ Limits.prod.fst) (l.lift (forgetCone s))
          fac := fun s j => by
            apply Limits.prod.hom_ext
            · erw [assoc, limMap_π, comp_id, limit.lift_π]
              exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (Classical.arbitrary _)).symm
            · simp
          uniq := fun s m L => by
            apply Limits.prod.hom_ext
            · simp [← L]
            · rw [limit.lift_π]
              apply l.uniq (forgetCone s)
              intro j
              simp [← L j] }⟩ }

中文:
引理 prod_preservesConnectedLimits
  条件: [是连通 J] (X : C)
  证明: { preserves := fun {c} l => ⟨{
          lift := fun s =>
            prod.lift (s.π.app (Classical.arbitrary _) ≫ Limits.prod.fst) (l.lift (forgetCone s))
          fac := fun s j => by
            apply Limits.prod.hom_ext
            · erw [assoc, limMap_π, comp_id, limit.lift_π]
              exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (Classical.arbitrary _)).symm
            · simp
          uniq := fun s m L => by
            apply Limits.prod.hom_ext
            · simp [← L]
            · rw [limit.lift_π]
              apply l.uniq (forgetCone s)
              intro j
              simp [← L j] }⟩ }

Depends on / 依赖: Classical, Classical.arbitrary, Limits, Limits.prod.fst, Limits.prod.hom_ext, arbitrary, comp_id, forgetCone, hom_ext, l.lift, l.uniq, limit.lift_, nat_trans_from_is_connected, preserves, prod.lift
-/
lemma prod_preservesConnectedLimits [IsConnected J] (X : C) :
    PreservesLimitsOfShape J (prod.functor.obj X) where
  preservesLimit {K} :=
    { preserves := fun {c} l => ⟨{
          lift := fun s =>
            prod.lift (s.π.app (Classical.arbitrary _) ≫ Limits.prod.fst) (l.lift (forgetCone s))
          fac := fun s j => by
            apply Limits.prod.hom_ext
            · erw [assoc, limMap_π, comp_id, limit.lift_π]
              exact (nat_trans_from_is_connected (s.π ≫ γ₁ X) j (Classical.arbitrary _)).symm
            · simp
          uniq := fun s m L => by
            apply Limits.prod.hom_ext
            · simp [← L]
            · rw [limit.lift_π]
              apply l.uniq (forgetCone s)
              intro j
              simp [← L j] }⟩ }

end CategoryTheory
