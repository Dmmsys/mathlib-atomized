/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving (co)equalizers

Constructions to relate the notions of preserving (co)equalizers and reflecting (co)equalizers
to concrete (co)forks.

In particular, we show that `equalizerComparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,g`, as well as the dual result.
-/

@[expose] public section


noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section Equalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitMapConeForkEquiv` / `isLimitMapConeForkEquiv` 的定义

English:
definition isLimitMapConeForkEquiv
  signature: :
  body: (IsLimit.postcomposeHomEquiv (diagramIsoParallelPair _) _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) (by simp [Fork.ι])))

中文:
定义 isLimitMapConeForkEquiv
  签名: :
  定义体: (IsLimit.postcomposeHomEquiv (diagramIsoParallelPair _) _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) (by simp [Fork.ι])))

Depends on / 依赖: Fork.ext, IsLimit, IsLimit.equivIsoLimit, IsLimit.postcomposeHomEquiv, Iso.refl, diagramIsoParallelPair, equivIsoLimit, postcomposeHomEquiv, symm.trans
-/
def isLimitMapConeForkEquiv :
    IsLimit (G.mapCone (Fork.ofι h w)) ≃
      IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g)) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoParallelPair _) _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) (by simp [Fork.ι])))

/--
Definition of `isLimitForkMapOfIsLimit` / `isLimitForkMapOfIsLimit` 的定义

English:
definition isLimitForkMapOfIsLimit
  signature: [PreservesLimit (parallelPair f g) G] (l : IsLimit (Fork.ofι h w))
  body: isLimitMapConeForkEquiv G w (isLimitOfPreserves G l)

中文:
定义 isLimitForkMapOfIsLimit
  签名: [保持极限 (parallelPair f g) G] (l : 是极限 (叉.ofι h w))
  定义体: isLimitMapConeForkEquiv G w (isLimitOfPreserves G l)

Depends on / 依赖: isLimitMapConeForkEquiv, isLimitOfPreserves
-/
def isLimitForkMapOfIsLimit [PreservesLimit (parallelPair f g) G] (l : IsLimit (Fork.ofι h w)) :
    IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g)) :=
  isLimitMapConeForkEquiv G w (isLimitOfPreserves G l)

/--
Definition of `isLimitOfIsLimitForkMap` / `isLimitOfIsLimitForkMap` 的定义

English:
definition isLimitOfIsLimitForkMap
  signature: [ReflectsLimit (parallelPair f g) G]
  body: isLimitOfReflects G ((isLimitMapConeForkEquiv G w).symm l)

中文:
定义 isLimitOfIsLimitForkMap
  签名: [反映极限 (parallelPair f g) G]
  定义体: isLimitOfReflects G ((isLimitMapConeForkEquiv G w).symm l)

Depends on / 依赖: isLimitMapConeForkEquiv, isLimitOfReflects
-/
def isLimitOfIsLimitForkMap [ReflectsLimit (parallelPair f g) G]
    (l : IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g))) :
    IsLimit (Fork.ofι h w) :=
  isLimitOfReflects G ((isLimitMapConeForkEquiv G w).symm l)

variable (f g)
variable [HasEqualizer f g]

/--
Definition of `isLimitOfHasEqualizerOfPreservesLimit` / `isLimitOfHasEqualizerOfPreservesLimit` 的定义

English:
definition isLimitOfHasEqualizerOfPreservesLimit
  signature: [PreservesLimit (parallelPair f g) G]
  body: isLimitForkMapOfIsLimit G _ (equalizerIsEqualizer f g)

中文:
定义 isLimitOfHasEqualizerOfPreservesLimit
  签名: [保持极限 (parallelPair f g) G]
  定义体: isLimitForkMapOfIsLimit G _ (equalizerIsEqualizer f g)

Depends on / 依赖: equalizerIsEqualizer, isLimitForkMapOfIsLimit
-/
def isLimitOfHasEqualizerOfPreservesLimit [PreservesLimit (parallelPair f g) G] :
    IsLimit (Fork.ofι
      (G.map (equalizer.ι f g)) (by simp only [← G.map_comp]; rw [equalizer.condition]) :
      Fork (G.map f) (G.map g)) :=
  isLimitForkMapOfIsLimit G _ (equalizerIsEqualizer f g)

variable [HasEqualizer (G.map f) (G.map g)]

/--
lemma `PreservesEqualizer.of_iso_comparison` / 引理 `PreservesEqualizer.of_iso_comparison`

English:
lemma PreservesEqualizer.of_iso_comparison
  given: [i : IsIso (equalizerComparison f g G)]
  proof: by
  apply preservesLimit_of_preserves_limit_cone (equalizerIsEqualizer f g)
  apply (isLimitMapConeForkEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (parallelPair (G.map f) (G.map g))) i

中文:
引理 PreservesEqualizer.of_iso_comparison
  条件: [i : 是同构 (equalizerComparison f g G)]
  证明: by
  apply preservesLimit_of_preserves_limit_cone (equalizerIsEqualizer f g)
  apply (isLimitMapConeForkEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (parallelPair (G.map f) (G.map g))) i

Depends on / 依赖: G.map, IsLimit, IsLimit.ofPointIso, equalizerIsEqualizer, isLimit, isLimitMapConeForkEquiv, limit.isLimit, ofPointIso, parallelPair, preservesLimit_of_preserves_limit_cone
-/
lemma PreservesEqualizer.of_iso_comparison [i : IsIso (equalizerComparison f g G)] :
    PreservesLimit (parallelPair f g) G := by
  apply preservesLimit_of_preserves_limit_cone (equalizerIsEqualizer f g)
  apply (isLimitMapConeForkEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (parallelPair (G.map f) (G.map g))) i

variable [PreservesLimit (parallelPair f g) G]

/--
Definition of `PreservesEqualizer.iso` / `PreservesEqualizer.iso` 的定义

English:
definition PreservesEqualizer.iso
  signature: : G.obj (equalizer f g) ≅ equalizer (G.map f) (G.map g)
  body: IsLimit.conePointUniqueUpToIso (isLimitOfHasEqualizerOfPreservesLimit G f g) (limit.isLimit _)

@[simp]

中文:
定义 PreservesEqualizer.iso
  签名: : G.obj (equalizer f g) ≅ equalizer (G.map f) (G.map g)
  定义体: IsLimit.conePointUniqueUpToIso (isLimitOfHasEqualizerOfPreservesLimit G f g) (limit.isLimit _)

@[simp]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, isLimitOfHasEqualizerOfPreservesLimit, limit.isLimit
-/
def PreservesEqualizer.iso : G.obj (equalizer f g) ≅ equalizer (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasEqualizerOfPreservesLimit G f g) (limit.isLimit _)

@[simp]
/--
theorem `PreservesEqualizer.iso_hom` / 定理 `PreservesEqualizer.iso_hom`

English:
theorem PreservesEqualizer.iso_hom
  proof: rfl

@[simp]

中文:
定理 PreservesEqualizer.iso_hom
  证明: rfl

@[simp]
-/
theorem PreservesEqualizer.iso_hom :
    (PreservesEqualizer.iso G f g).hom = equalizerComparison f g G :=
  rfl

@[simp]
/--
theorem `PreservesEqualizer.iso_inv_ι` / 定理 `PreservesEqualizer.iso_inv_ι`

English:
theorem PreservesEqualizer.iso_inv_ι
  proof: by
  rw [← Iso.cancel_iso_hom_left (PreservesEqualizer.iso G f g)]; rw [← Category.assoc]; rw [Iso.hom_inv_id]
  simp

中文:
定理 PreservesEqualizer.iso_inv_ι
  证明: by
  rw [← Iso.cancel_iso_hom_left (PreservesEqualizer.iso G f g)]; rw [← Category.assoc]; rw [Iso.hom_inv_id]
  simp

Depends on / 依赖: Category, Category.assoc, Iso.cancel_iso_hom_left, Iso.hom_inv_id, PreservesEqualizer, PreservesEqualizer.iso, cancel_iso_hom_left, hom_inv_id
-/
theorem PreservesEqualizer.iso_inv_ι :
    (PreservesEqualizer.iso G f g).inv ≫ G.map (equalizer.ι f g) =
      equalizer.ι (G.map f) (G.map g) := by
  rw [← Iso.cancel_iso_hom_left (PreservesEqualizer.iso G f g)]; rw [← Category.assoc]; rw [Iso.hom_inv_id]
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (equalizerComparison f g G)
  body: by
  rw [← PreservesEqualizer.iso_hom]
  infer_instance

中文:
实例 :
  签名: 是同构 (equalizerComparison f g G)
  定义体: by
  rw [← PreservesEqualizer.iso_hom]
  infer_instance

Depends on / 依赖: PreservesEqualizer, PreservesEqualizer.iso_hom, infer_instance, iso_hom
-/
instance : IsIso (equalizerComparison f g G) := by
  rw [← PreservesEqualizer.iso_hom]
  infer_instance

end Equalizers

section Coequalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitMapCoconeCoforkEquiv` / `isColimitMapCoconeCoforkEquiv` 的定义

English:
definition isColimitMapCoconeCoforkEquiv
  signature: :
  body: (IsColimit.precomposeInvEquiv (diagramIsoParallelPair _) _).symm.trans
IsColimit.equivIsoColimit
Cofork.ext (Iso.refl _) by
        dsimp only [Cofork.π, Cofork.ofπ_ι_app]
        dsimp; rw [Category.comp_id, Category.id_comp]

中文:
定义 isColimitMapCoconeCoforkEquiv
  签名: :
  定义体: (IsColimit.precomposeInvEquiv (diagramIsoParallelPair _) _).symm.trans
IsColimit.equivIsoColimit
Cofork.ext (Iso.refl _) by
        dsimp only [Cofork.π, Cofork.ofπ_ι_app]
        dsimp; rw [Category.comp_id, Category.id_comp]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Cofork, Cofork.ext, Cofork.of, IsColimit, IsColimit.equivIsoColimit, IsColimit.precomposeInvEquiv, Iso.refl, comp_id, diagramIsoParallelPair, equivIsoColimit, id_comp, precomposeInvEquiv, symm.trans
-/
def isColimitMapCoconeCoforkEquiv :
    IsColimit (G.mapCocone (Cofork.ofπ h w)) ≃
      IsColimit
        (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g)) :=
(IsColimit.precomposeInvEquiv (diagramIsoParallelPair _) _).symm.trans
IsColimit.equivIsoColimit
Cofork.ext (Iso.refl _) by
        dsimp only [Cofork.π, Cofork.ofπ_ι_app]
        dsimp; rw [Category.comp_id, Category.id_comp]

/--
Definition of `isColimitCoforkMapOfIsColimit` / `isColimitCoforkMapOfIsColimit` 的定义

English:
definition isColimitCoforkMapOfIsColimit
  signature: [PreservesColimit (parallelPair f g) G]
  body: isColimitMapCoconeCoforkEquiv G w (isColimitOfPreserves G l)

中文:
定义 isColimitCoforkMapOfIsColimit
  签名: [保持余极限 (parallelPair f g) G]
  定义体: isColimitMapCoconeCoforkEquiv G w (isColimitOfPreserves G l)

Depends on / 依赖: isColimitMapCoconeCoforkEquiv, isColimitOfPreserves
-/
def isColimitCoforkMapOfIsColimit [PreservesColimit (parallelPair f g) G]
    (l : IsColimit (Cofork.ofπ h w)) :
    IsColimit
      (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g)) :=
  isColimitMapCoconeCoforkEquiv G w (isColimitOfPreserves G l)

/--
Definition of `isColimitOfIsColimitCoforkMap` / `isColimitOfIsColimitCoforkMap` 的定义

English:
definition isColimitOfIsColimitCoforkMap
  signature: [ReflectsColimit (parallelPair f g) G]
  body: isColimitOfReflects G ((isColimitMapCoconeCoforkEquiv G w).symm l)

中文:
定义 isColimitOfIsColimitCoforkMap
  签名: [反映余极限 (parallelPair f g) G]
  定义体: isColimitOfReflects G ((isColimitMapCoconeCoforkEquiv G w).symm l)

Depends on / 依赖: isColimitMapCoconeCoforkEquiv, isColimitOfReflects
-/
def isColimitOfIsColimitCoforkMap [ReflectsColimit (parallelPair f g) G]
    (l :
      IsColimit
        (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g))) :
    IsColimit (Cofork.ofπ h w) :=
  isColimitOfReflects G ((isColimitMapCoconeCoforkEquiv G w).symm l)

variable (f g)
variable [HasCoequalizer f g]

/--
Definition of `isColimitOfHasCoequalizerOfPreservesColimit` / `isColimitOfHasCoequalizerOfPreservesColimit` 的定义

English:
definition isColimitOfHasCoequalizerOfPreservesColimit
  signature: [PreservesColimit (parallelPair f g) G]
  body: isColimitCoforkMapOfIsColimit G _ (coequalizerIsCoequalizer f g)

中文:
定义 isColimitOfHasCoequalizerOfPreservesColimit
  签名: [保持余极限 (parallelPair f g) G]
  定义体: isColimitCoforkMapOfIsColimit G _ (coequalizerIsCoequalizer f g)

Depends on / 依赖: coequalizerIsCoequalizer, isColimitCoforkMapOfIsColimit
-/
def isColimitOfHasCoequalizerOfPreservesColimit [PreservesColimit (parallelPair f g) G] :
    IsColimit (Cofork.ofπ (G.map (coequalizer.π f g)) (by
      simp only [← G.map_comp]; rw [coequalizer.condition]) : Cofork (G.map f) (G.map g)) :=
  isColimitCoforkMapOfIsColimit G _ (coequalizerIsCoequalizer f g)

variable [HasCoequalizer (G.map f) (G.map g)]

/--
lemma `of_iso_comparison` / 引理 `of_iso_comparison`

English:
lemma of_iso_comparison
  given: [i : IsIso (coequalizerComparison f g G)]
  proof: by
  apply preservesColimit_of_preserves_colimit_cocone (coequalizerIsCoequalizer f g)
  apply (isColimitMapCoconeCoforkEquiv _ _).symm _
  exact
    @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (parallelPair (G.map f) (G.map g))) i

中文:
引理 of_iso_comparison
  条件: [i : 是同构 (coequalizerComparison f g G)]
  证明: by
  apply preservesColimit_of_preserves_colimit_cocone (coequalizerIsCoequalizer f g)
  apply (isColimitMapCoconeCoforkEquiv _ _).symm _
  exact
    @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (parallelPair (G.map f) (G.map g))) i

Depends on / 依赖: G.map, IsColimit, IsColimit.ofPointIso, coequalizerIsCoequalizer, colimit, colimit.isColimit, isColimit, isColimitMapCoconeCoforkEquiv, ofPointIso, parallelPair, preservesColimit_of_preserves_colimit_cocone
-/
lemma of_iso_comparison [i : IsIso (coequalizerComparison f g G)] :
    PreservesColimit (parallelPair f g) G := by
  apply preservesColimit_of_preserves_colimit_cocone (coequalizerIsCoequalizer f g)
  apply (isColimitMapCoconeCoforkEquiv _ _).symm _
  exact
    @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (parallelPair (G.map f) (G.map g))) i

variable [PreservesColimit (parallelPair f g) G]

/--
Definition of `PreservesCoequalizer.iso` / `PreservesCoequalizer.iso` 的定义

English:
definition PreservesCoequalizer.iso
  signature: : coequalizer (G.map f) (G.map g) ≅ G.obj (coequalizer f g)
  body: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasCoequalizerOfPreservesColimit G f g)

@[simp]

中文:
定义 PreservesCoequalizer.iso
  签名: : coequalizer (G.map f) (G.map g) ≅ G.obj (coequalizer f g)
  定义体: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasCoequalizerOfPreservesColimit G f g)

@[simp]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, isColimitOfHasCoequalizerOfPreservesColimit
-/
def PreservesCoequalizer.iso : coequalizer (G.map f) (G.map g) ≅ G.obj (coequalizer f g) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasCoequalizerOfPreservesColimit G f g)

@[simp]
/--
theorem `PreservesCoequalizer.iso_hom` / 定理 `PreservesCoequalizer.iso_hom`

English:
theorem PreservesCoequalizer.iso_hom
  proof: rfl

中文:
定理 PreservesCoequalizer.iso_hom
  证明: rfl
-/
theorem PreservesCoequalizer.iso_hom :
    (PreservesCoequalizer.iso G f g).hom = coequalizerComparison f g G :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (coequalizerComparison f g G)
  body: by
  rw [← PreservesCoequalizer.iso_hom]
  infer_instance

中文:
实例 :
  签名: 是同构 (coequalizerComparison f g G)
  定义体: by
  rw [← PreservesCoequalizer.iso_hom]
  infer_instance

Depends on / 依赖: PreservesCoequalizer, PreservesCoequalizer.iso_hom, infer_instance, iso_hom
-/
instance : IsIso (coequalizerComparison f g G) := by
  rw [← PreservesCoequalizer.iso_hom]
  infer_instance

/--
Instance `map_π_epi` / 实例 `map_π_epi`

English:
instance map_π_epi
  signature: : Epi (G.map (coequalizer.π f g))
  body: ⟨fun {W} h k => by
    rw [← ι_comp_coequalizerComparison]
    have : Epi (coequalizer.π (G.map f) (G.map g) ≫ coequalizerComparison f g G) := by
      apply epi_comp
    apply (cancel_epi _).1⟩

@[reassoc]

中文:
实例 map_π_epi
  签名: : 满态射 (G.map (coequalizer.π f g))
  定义体: ⟨fun {W} h k => by
    rw [← ι_comp_coequalizerComparison]
    have : Epi (coequalizer.π (G.map f) (G.map g) ≫ coequalizerComparison f g G) := by
      apply epi_comp
    apply (cancel_epi _).1⟩

@[reassoc]

Depends on / 依赖: G.map, Grp.forget, cancel_epi, coequalizer, coequalizerComparison, epi_comp
-/
instance map_π_epi : Epi (G.map (coequalizer.π f g)) :=
  ⟨fun {W} h k => by
    rw [← ι_comp_coequalizerComparison]
    have : Epi (coequalizer.π (G.map f) (G.map g) ≫ coequalizerComparison f g G) := by
      apply epi_comp
    apply (cancel_epi _).1⟩

@[reassoc]
/--
theorem `map_π_preserves_coequalizer_inv` / 定理 `map_π_preserves_coequalizer_inv`

English:
theorem map_π_preserves_coequalizer_inv
  proof: by
  rw [← ι_comp_coequalizerComparison_assoc]; rw [← PreservesCoequalizer.iso_hom]; rw [Iso.hom_inv_id]; rw [comp_id]

@[reassoc]

中文:
定理 map_π_preserves_coequalizer_inv
  证明: by
  rw [← ι_comp_coequalizerComparison_assoc]; rw [← PreservesCoequalizer.iso_hom]; rw [Iso.hom_inv_id]; rw [comp_id]

@[reassoc]

Depends on / 依赖: Iso.hom_inv_id, PreservesCoequalizer, PreservesCoequalizer.iso_hom, comp_id, hom_inv_id, iso_hom
-/
theorem map_π_preserves_coequalizer_inv :
    G.map (coequalizer.π f g) ≫ (PreservesCoequalizer.iso G f g).inv =
      coequalizer.π (G.map f) (G.map g) := by
  rw [← ι_comp_coequalizerComparison_assoc]; rw [← PreservesCoequalizer.iso_hom]; rw [Iso.hom_inv_id]; rw [comp_id]

@[reassoc]
/--
theorem `map_π_preserves_coequalizer_inv_desc` / 定理 `map_π_preserves_coequalizer_inv_desc`

English:
theorem map_π_preserves_coequalizer_inv_desc
  statement: {W : D} (k : G.obj Y ⟶ W)
  proof: by
  rw [← Category.assoc]; rw [map_π_preserves_coequalizer_inv]; rw [coequalizer.π_desc]

中文:
定理 map_π_preserves_coequalizer_inv_desc
  结论: {W : D} (k : G.obj Y ⟶ W)
  证明: by
  rw [← Category.assoc]; rw [map_π_preserves_coequalizer_inv]; rw [coequalizer.π_desc]

Depends on / 依赖: Category, Category.assoc, coequalizer
-/
theorem map_π_preserves_coequalizer_inv_desc {W : D} (k : G.obj Y ⟶ W)
    (wk : G.map f ≫ k = G.map g ≫ k) : G.map (coequalizer.π f g) ≫
      (PreservesCoequalizer.iso G f g).inv ≫ coequalizer.desc k wk = k := by
  rw [← Category.assoc]; rw [map_π_preserves_coequalizer_inv]; rw [coequalizer.π_desc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `map_π_preserves_coequalizer_inv_colimMap` / 定理 `map_π_preserves_coequalizer_inv_colimMap`

English:
theorem map_π_preserves_coequalizer_inv_colimMap
  statement: {X' Y' : D} (f' g' : X' ⟶ Y')
  proof: by
  rw [← Category.assoc]; rw [map_π_preserves_coequalizer_inv]; rw [ι_colimMap]; rw [parallelPairHom_app_one]

@[reassoc]

中文:
定理 map_π_preserves_coequalizer_inv_colimMap
  结论: {X' Y' : D} (f' g' : X' ⟶ Y')
  证明: by
  rw [← Category.assoc]; rw [map_π_preserves_coequalizer_inv]; rw [ι_colimMap]; rw [parallelPairHom_app_one]

@[reassoc]

Depends on / 依赖: Category, Category.assoc, parallelPairHom_app_one
-/
theorem map_π_preserves_coequalizer_inv_colimMap {X' Y' : D} (f' g' : X' ⟶ Y')
    [HasCoequalizer f' g'] (p : G.obj X ⟶ X') (q : G.obj Y ⟶ Y') (wf : G.map f ≫ q = p ≫ f')
    (wg : G.map g ≫ q = p ≫ g') :
    G.map (coequalizer.π f g) ≫
        (PreservesCoequalizer.iso G f g).inv ≫
          colimMap (parallelPairHom (G.map f) (G.map g) f' g' p q wf wg) =
      q ≫ coequalizer.π f' g' := by
  rw [← Category.assoc]; rw [map_π_preserves_coequalizer_inv]; rw [ι_colimMap]; rw [parallelPairHom_app_one]

@[reassoc]
/--
theorem `map_π_preserves_coequalizer_inv_colimMap_desc` / 定理 `map_π_preserves_coequalizer_inv_colimMap_desc`

English:
theorem map_π_preserves_coequalizer_inv_colimMap_desc
  statement: {X' Y' : D} (f' g' : X' ⟶ Y')
  proof: by
  slice_lhs 1 3 => rw [map_π_preserves_coequalizer_inv_colimMap]
  slice_lhs 2 3 => rw [coequalizer.π_desc]

中文:
定理 map_π_preserves_coequalizer_inv_colimMap_desc
  结论: {X' Y' : D} (f' g' : X' ⟶ Y')
  证明: by
  slice_lhs 1 3 => rw [map_π_preserves_coequalizer_inv_colimMap]
  slice_lhs 2 3 => rw [coequalizer.π_desc]

Depends on / 依赖: coequalizer, slice_lhs
-/
theorem map_π_preserves_coequalizer_inv_colimMap_desc {X' Y' : D} (f' g' : X' ⟶ Y')
    [HasCoequalizer f' g'] (p : G.obj X ⟶ X') (q : G.obj Y ⟶ Y') (wf : G.map f ≫ q = p ≫ f')
    (wg : G.map g ≫ q = p ≫ g') {Z' : D} (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    G.map (coequalizer.π f g) ≫
        (PreservesCoequalizer.iso G f g).inv ≫
          colimMap (parallelPairHom (G.map f) (G.map g) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h := by
  slice_lhs 1 3 => rw [map_π_preserves_coequalizer_inv_colimMap]
  slice_lhs 2 3 => rw [coequalizer.π_desc]

/-- Any functor preserves coequalizers of split pairs. -/
instance (priority := 1) preservesSplitCoequalizers (f g : X ⟶ Y) [HasSplitCoequalizer f g] :
    PreservesColimit (parallelPair f g) G := by
  apply
    preservesColimit_of_preserves_colimit_cocone
      (HasSplitCoequalizer.isSplitCoequalizer f g).isCoequalizer
  apply
    (isColimitMapCoconeCoforkEquiv G _).symm
      ((HasSplitCoequalizer.isSplitCoequalizer f g).map G).isCoequalizer

instance (priority := 1) preservesSplitEqualizers (f g : X ⟶ Y) [HasSplitEqualizer f g] :
    PreservesLimit (parallelPair f g) G := by
  apply
    preservesLimit_of_preserves_limit_cone
      (HasSplitEqualizer.isSplitEqualizer f g).isEqualizer
  apply
    (isLimitMapConeForkEquiv G _).symm
      ((HasSplitEqualizer.isSplitEqualizer f g).map G).isEqualizer

end Coequalizers

end CategoryTheory.Limits
