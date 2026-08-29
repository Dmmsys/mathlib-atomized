/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Free sheaves of modules

In this file, we construct the functor
`SheafOfModules.freeFunctor : Type u ⥤ SheafOfModules.{u} R` which sends
a type `I` to the coproduct of copies indexed by `I` of `unit R`.

## TODO

* In case the category `C` has a terminal object `X`, promote `freeHomEquiv`
  into an adjunction between `freeFunctor` and the evaluation functor at `X`.
  (Alternatively, assuming specific universe parameters, we could show that
  `freeFunctor` is a left adjoint to `SheafOfModules.sectionsFunctor`.)

-/

@[expose] public section

universe u v₁ v₂ u₁ u₂
open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: (I : Type u)
  body: ∐ (fun (_ : I) => unit R)

中文:
定义 free
  签名: (I : 类型u)
  定义体: ∐ (fun (_ : I) => unit R)

Depends on / 依赖: cat_disch, epi_iff_surjective, freeDesc, freeMk, hasRightInverse, hp.hasRightInverse
-/
noncomputable def free (I : Type u) : SheafOfModules.{u} R := ∐ (fun (_ : I) => unit R)

/--
Definition of `ιFree` / `ιFree` 的定义

English:
definition ιFree
  signature: {I : Type u} (i : I)
  body: Sigma.ι (fun (_ : I) => unit R) i

中文:
定义 ιFree
  签名: {I : 类型u} (i : I)
  定义体: Sigma.ι (fun (_ : I) => unit R) i
-/
noncomputable def ιFree {I : Type u} (i : I) : unit R ⟶ free I :=
  Sigma.ι (fun (_ : I) => unit R) i

/--
Definition of `freeCofan` / `freeCofan` 的定义

English:
definition freeCofan
  signature: (I : Type u)
  body: Cofan.mk (P := free I) ιFree

@[simp]

中文:
定义 freeCofan
  签名: (I : 类型u)
  定义体: Cofan.mk (P := free I) ιFree

@[simp]

Depends on / 依赖: Cofan.mk
-/
noncomputable def freeCofan (I : Type u) : Cofan (fun (_ : I) => unit R) :=
  Cofan.mk (P := free I) ιFree

@[simp]
/--
lemma `freeCofan_inj` / 引理 `freeCofan_inj`

English:
lemma freeCofan_inj
  given: {I : Type u} (i : I)
  proof: rfl

中文:
引理 freeCofan_inj
  条件: {I : 类型u} (i : I)
  证明: rfl
-/
lemma freeCofan_inj {I : Type u} (i : I) :
    (freeCofan (R := R) I).inj i = ιFree i := rfl

/--
Definition of `isColimitFreeCofan` / `isColimitFreeCofan` 的定义

English:
definition isColimitFreeCofan
  signature: (I : Type u)
  body: coproductIsCoproduct _

中文:
定义 isColimitFreeCofan
  签名: (I : 类型u)
  定义体: coproductIsCoproduct _
-/
noncomputable def isColimitFreeCofan (I : Type u) :
    IsColimit (freeCofan (R := R) I) :=
  coproductIsCoproduct _

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `freeHomEquiv` / `freeHomEquiv` 的定义

English:
definition freeHomEquiv
  signature: (M : SheafOfModules.{u} R) {I : Type u}
  body: M.unitHomEquiv (ιFree i ≫ f)
  invFun s := Cofan.IsColimit.desc (isColimitFreeCofan I) (fun i => M.unitHomEquiv.symm (s i))
  left_inv s := Cofan.IsColimit.hom_ext (isColimitFreeCofan I) _ _
    (fun i => by simp [← freeCofan_inj])
  right_inv f := by ext1 i; simp [← freeCofan_inj]

中文:
定义 freeHomEquiv
  签名: (M : 模层.{u} R) {I : 类型u}
  定义体: M.unitHomEquiv (ιFree i ≫ f)
  invFun s := Cofan.IsColimit.desc (isColimitFreeCofan I) (fun i => M.unitHomEquiv.symm (s i))
  left_inv s := Cofan.IsColimit.hom_ext (isColimitFreeCofan I) _ _
    (fun i => by simp [← freeCofan_inj])
  right_inv f := by ext1 i; simp [← freeCofan_inj]

Depends on / 依赖: M.unitHomEquiv, unitHomEquiv
-/
noncomputable def freeHomEquiv (M : SheafOfModules.{u} R) {I : Type u} :
    (free I ⟶ M) ≃ (I -> M.sections) where
  toFun f i := M.unitHomEquiv (ιFree i ≫ f)
  invFun s := Cofan.IsColimit.desc (isColimitFreeCofan I) (fun i => M.unitHomEquiv.symm (s i))
  left_inv s := Cofan.IsColimit.hom_ext (isColimitFreeCofan I) _ _
    (fun i => by simp [← freeCofan_inj])
  right_inv f := by ext1 i; simp [← freeCofan_inj]

/--
lemma `freeHomEquiv_comp_apply` / 引理 `freeHomEquiv_comp_apply`

English:
lemma freeHomEquiv_comp_apply
  statement: {M N : SheafOfModules.{u} R} {I : Type u}
  proof: rfl

中文:
引理 freeHomEquiv_comp_apply
  结论: {M N : 模层.{u} R} {I : 类型u}
  证明: rfl
-/
lemma freeHomEquiv_comp_apply {M N : SheafOfModules.{u} R} {I : Type u}
    (f : free I ⟶ M) (p : M ⟶ N) (i : I) :
    N.freeHomEquiv (f ≫ p) i = sectionsMap p (M.freeHomEquiv f i) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `freeHomEquiv_symm_comp` / 引理 `freeHomEquiv_symm_comp`

English:
lemma freeHomEquiv_symm_comp
  statement: {M N : SheafOfModules.{u} R} {I : Type u} (s : I -> M.sections)
  proof: N.freeHomEquiv.injective (by ext; simp [freeHomEquiv_comp_apply])

中文:
引理 freeHomEquiv_symm_comp
  结论: {M N : 模层.{u} R} {I : 类型u} (s : I -> M.sections)
  证明: N.freeHomEquiv.injective (by ext; simp [freeHomEquiv_comp_apply])

Depends on / 依赖: N.freeHomEquiv.injective, freeHomEquiv, freeHomEquiv_comp_apply, injective
-/
lemma freeHomEquiv_symm_comp {M N : SheafOfModules.{u} R} {I : Type u} (s : I -> M.sections)
    (p : M ⟶ N) :
    M.freeHomEquiv.symm s ≫ p = N.freeHomEquiv.symm (fun i => sectionsMap p (s i)) :=
  N.freeHomEquiv.injective (by ext; simp [freeHomEquiv_comp_apply])

/--
Definition of `freeSection` / `freeSection` 的定义

English:
abbreviation freeSection
  signature: {I : Type u} (i : I)
  body: (free (R := R) I).freeHomEquiv (𝟙 (free I)) i

中文:
缩写 freeSection
  签名: {I : 类型u} (i : I)
  定义体: (free (R := R) I).freeHomEquiv (𝟙 (free I)) i

Depends on / 依赖: sections
-/
noncomputable abbrev freeSection {I : Type u} (i : I) : (free (R := R) I).sections :=
  (free (R := R) I).freeHomEquiv (𝟙 (free I)) i

/--
lemma `freeHomEquiv_apply` / 引理 `freeHomEquiv_apply`

English:
lemma freeHomEquiv_apply
  statement: {M : SheafOfModules.{u} R} {I : Type u}
  proof: rfl

中文:
引理 freeHomEquiv_apply
  结论: {M : 模层.{u} R} {I : 类型u}
  证明: rfl
-/
lemma freeHomEquiv_apply {M : SheafOfModules.{u} R} {I : Type u}
    (f : free I ⟶ M) (i : I) :
    freeHomEquiv M f i = sectionsMap f (freeSection i) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `unitHomEquiv_symm_freeHomEquiv_apply` / 引理 `unitHomEquiv_symm_freeHomEquiv_apply`

English:
lemma unitHomEquiv_symm_freeHomEquiv_apply
  proof: by
  simp [freeHomEquiv]

中文:
引理 unitHomEquiv_symm_freeHomEquiv_apply
  证明: by
  simp [freeHomEquiv]

Depends on / 依赖: freeHomEquiv
-/
lemma unitHomEquiv_symm_freeHomEquiv_apply
    {I : Type u} {M : SheafOfModules.{u} R} (f : free I ⟶ M) (i : I) :
    M.unitHomEquiv.symm (M.freeHomEquiv f i) = ιFree i ≫ f := by
  simp [freeHomEquiv]

section

variable {I J : Type u} (f : I -> J)

/--
Definition of `freeMap` / `freeMap` 的定义

English:
definition freeMap
  signature: : free (R := R) I ⟶ free J
  body: (freeHomEquiv _).symm (fun i => freeSection (f i))

@[simp]

中文:
定义 freeMap
  签名: : free (R := R) I ⟶ free J
  定义体: (freeHomEquiv _).symm (fun i => freeSection (f i))

@[simp]
-/
noncomputable def freeMap : free (R := R) I ⟶ free J :=
  (freeHomEquiv _).symm (fun i => freeSection (f i))

@[simp]
/--
lemma `freeHomEquiv_freeMap` / 引理 `freeHomEquiv_freeMap`

English:
lemma freeHomEquiv_freeMap
  proof: (freeHomEquiv _).symm.injective (by simp; rfl)

@[simp]

中文:
引理 freeHomEquiv_freeMap
  证明: (freeHomEquiv _).symm.injective (by simp; rfl)

@[simp]

Depends on / 依赖: freeSection, freeSection.comp
-/
lemma freeHomEquiv_freeMap :
    (freeHomEquiv _ (freeMap (R := R) f)) = freeSection.comp f :=
  (freeHomEquiv _).symm.injective (by simp; rfl)

@[simp]
/--
lemma `sectionMap_freeMap_freeSection` / 引理 `sectionMap_freeMap_freeSection`

English:
lemma sectionMap_freeMap_freeSection
  given: (i : I)
  proof: by
  simp [← freeHomEquiv_comp_apply]

中文:
引理 sectionMap_freeMap_freeSection
  条件: (i : I)
  证明: by
  simp [← freeHomEquiv_comp_apply]
-/
lemma sectionMap_freeMap_freeSection (i : I) :
    sectionsMap (freeMap (R := R) f) (freeSection i) = freeSection (f i) := by
  simp [← freeHomEquiv_comp_apply]

/--
lemma `sectionsMap_freeHomEquiv_symm_freeSection` / 引理 `sectionsMap_freeHomEquiv_symm_freeSection`

English:
lemma sectionsMap_freeHomEquiv_symm_freeSection
  proof: by
  obtain ⟨f, rfl⟩ := (freeHomEquiv M).surjective f
  cat_disch

@[reassoc (attr := simp)]

中文:
引理 sectionsMap_freeHomEquiv_symm_freeSection
  证明: by
  obtain ⟨f, rfl⟩ := (freeHomEquiv M).surjective f
  cat_disch

@[reassoc (attr := simp)]
-/
lemma sectionsMap_freeHomEquiv_symm_freeSection
    {M : SheafOfModules.{u} R} (f : I -> M.sections) (i : I) :
    sectionsMap ((freeHomEquiv M).symm f) (freeSection i) = f i := by
  obtain ⟨f, rfl⟩ := (freeHomEquiv M).surjective f
  cat_disch

@[reassoc (attr := simp)]
/--
lemma `ιFree_freeMap` / 引理 `ιFree_freeMap`

English:
lemma ιFree_freeMap
  given: (i : I)
  proof: by
  rw [← unitHomEquiv_symm_freeHomEquiv_apply]; rw [freeHomEquiv_freeMap]
  dsimp [freeSection]
  rw [unitHomEquiv_symm_freeHomEquiv_apply]; rw [Category.comp_id]

中文:
引理 ιFree_freeMap
  条件: (i : I)
  证明: by
  rw [← unitHomEquiv_symm_freeHomEquiv_apply]; rw [freeHomEquiv_freeMap]
  dsimp [freeSection]
  rw [unitHomEquiv_symm_freeHomEquiv_apply]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, comp_id, freeHomEquiv_freeMap, freeMap, freeSection, unitHomEquiv_symm_freeHomEquiv_apply
-/
lemma ιFree_freeMap (i : I) :
    ιFree (R := R) i ≫ freeMap f = ιFree (f i) := by
  rw [← unitHomEquiv_symm_freeHomEquiv_apply]; rw [freeHomEquiv_freeMap]
  dsimp [freeSection]
  rw [unitHomEquiv_symm_freeHomEquiv_apply]; rw [Category.comp_id]

end

/--
Definition of `freeFunctor` / `freeFunctor` 的定义

English:
definition freeFunctor
  signature: : Type u ⥤ SheafOfModules.{u} R
  body: sigmaConst.obj (unit R)

@[simp]

中文:
定义 freeFunctor
  签名: : 类型u ⥤ 模层.{u} R
  定义体: sigmaConst.obj (unit R)

@[simp]

Depends on / 依赖: sigmaConst, sigmaConst.obj
-/
noncomputable def freeFunctor : Type u ⥤ SheafOfModules.{u} R :=
  sigmaConst.obj (unit R)

@[simp]
/--
lemma `freeFunctor_obj` / 引理 `freeFunctor_obj`

English:
lemma freeFunctor_obj
  given: (X : Type u)
  proof: rfl

@[simp]

中文:
引理 freeFunctor_obj
  条件: (X : 类型u)
  证明: rfl

@[simp]

Depends on / 依赖: HasLimits, ModuleCat, hasLimits
-/
lemma freeFunctor_obj (X : Type u) :
    (freeFunctor (R := R)).obj X = free X := rfl

@[simp]
/--
lemma `freeFunctor_map` / 引理 `freeFunctor_map`

English:
lemma freeFunctor_map
  given: {X Y : Type u} (f : X ⟶ Y)
  proof: Cofan.IsColimit.hom_ext (isColimitFreeCofan _) _ _
    (fun i => (Sigma.ι_desc _ _).trans (ιFree_freeMap f i).symm)

中文:
引理 freeFunctor_map
  条件: {X Y : 类型u} (f : X ⟶ Y)
  证明: Cofan.IsColimit.hom_ext (isColimitFreeCofan _) _ _
    (fun i => (Sigma.ι_desc _ _).trans (ιFree_freeMap f i).symm)

Depends on / 依赖: freeMap
-/
lemma freeFunctor_map {X Y : Type u} (f : X ⟶ Y) :
    dsimp% (freeFunctor (R := R)).map f = freeMap f :=
  Cofan.IsColimit.hom_ext (isColimitFreeCofan _) _ _
    (fun i => (Sigma.ι_desc _ _).trans (ιFree_freeMap f i).symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfSize.{v₂, u₂} (freeFunctor (R := R))
  body: inferInstanceAs (PreservesColimitsOfSize.{v₂, u₂} (sigmaConst.obj _))

中文:
实例 :
  签名: 保持余limitsOfSize.{v₂, u₂} (freeFunctor (R := R))
  定义体: inferInstanceAs (PreservesColimitsOfSize.{v₂, u₂} (sigmaConst.obj _))
-/
instance : PreservesColimitsOfSize.{v₂, u₂} (freeFunctor (R := R)) :=
  inferInstanceAs (PreservesColimitsOfSize.{v₂, u₂} (sigmaConst.obj _))

section

variable (I J : Type u)

/--
Definition of `freeSumIso` / `freeSumIso` 的定义

English:
definition freeSumIso
  signature: : free I ⨿ free J ≅ free (R := R) (I oplus J)
  body: IsColimit.coconePointUniqueUpToIso
    (coprodIsCoprod (free (R := R) I) (free J))
    (mapIsColimitOfPreservesOfIsColimit (freeFunctor (R := R)) _ _
      (Types.binaryCoproductColimit I J))

@[reassoc (attr := simp)]

中文:
定义 freeSumIso
  签名: : free I ⨿ free J ≅ free (R := R) (I oplus J)
  定义体: IsColimit.coconePointUniqueUpToIso
    (coprodIsCoprod (free (R := R) I) (free J))
    (mapIsColimitOfPreservesOfIsColimit (freeFunctor (R := R)) _ _
      (Types.binaryCoproductColimit I J))

@[reassoc (attr := simp)]
-/
noncomputable def freeSumIso : free I ⨿ free J ≅ free (R := R) (I oplus J) :=
  IsColimit.coconePointUniqueUpToIso
    (coprodIsCoprod (free (R := R) I) (free J))
    (mapIsColimitOfPreservesOfIsColimit (freeFunctor (R := R)) _ _
      (Types.binaryCoproductColimit I J))

@[reassoc (attr := simp)]
/--
lemma `inl_freeSumIso_hom` / 引理 `inl_freeSumIso_hom`

English:
lemma inl_freeSumIso_hom
  proof: by
  rw [← dsimp% freeFunctor_map (↾(Sum.inl : I -> I oplus J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .left)

@[reassoc (attr := simp)]

中文:
引理 inl_freeSumIso_hom
  证明: by
  rw [← dsimp% freeFunctor_map (↾(Sum.inl : I -> I oplus J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .left)

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, Sum.inl, comp_coconePointUniqueUpToIso_hom, coprodIsCoprod, freeFunctor_map, freeMap
-/
lemma inl_freeSumIso_hom :
    coprod.inl ≫ (freeSumIso (R := R) I J).hom = freeMap Sum.inl := by
  rw [← dsimp% freeFunctor_map (↾(Sum.inl : I -> I oplus J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .left)

@[reassoc (attr := simp)]
/--
lemma `inr_freeSumIso_hom` / 引理 `inr_freeSumIso_hom`

English:
lemma inr_freeSumIso_hom
  proof: by
  rw [← dsimp% freeFunctor_map (↾(Sum.inr : J -> I oplus J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .right)

中文:
引理 inr_freeSumIso_hom
  证明: by
  rw [← dsimp% freeFunctor_map (↾(Sum.inr : J -> I oplus J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .right)

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, Sum.inr, comp_coconePointUniqueUpToIso_hom, coprodIsCoprod, freeFunctor_map, freeMap
-/
lemma inr_freeSumIso_hom :
    coprod.inr ≫ (freeSumIso (R := R) I J).hom = freeMap Sum.inr := by
  rw [← dsimp% freeFunctor_map (↾(Sum.inr : J -> I oplus J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .right)

end

section

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) (I : Type u)

/--
Definition of `mapFree` / `mapFree` 的定义

English:
definition mapFree
  signature: (η : unit S ⟶ F.obj (unit R))
  body: (isColimitFreeCofan I).map (F.mapCocone (freeCofan I)) (Discrete.natTrans fun _ => η)

@[reassoc (attr := simp)]

中文:
定义 mapFree
  签名: (η : unit S ⟶ F.obj (unit R))
  定义体: (isColimitFreeCofan I).map (F.mapCocone (freeCofan I)) (Discrete.natTrans fun _ => η)

@[reassoc (attr := simp)]

Depends on / 依赖: F.obj
-/
noncomputable def mapFree (η : unit S ⟶ F.obj (unit R)) : free (R := S) I ⟶ F.obj (free I) :=
  (isColimitFreeCofan I).map (F.mapCocone (freeCofan I)) (Discrete.natTrans fun _ => η)

@[reassoc (attr := simp)]
/--
lemma `ιFree_mapFree` / 引理 `ιFree_mapFree`

English:
lemma ιFree_mapFree
  given: (η : unit S ⟶ F.obj (unit R)) (i : I)
  proof: IsColimit.ι_map (isColimitFreeCofan I) (F.mapCocone (freeCofan I))
    (Discrete.natTrans fun _ => η) (Discrete.mk i)

中文:
引理 ιFree_mapFree
  条件: (η : unit S ⟶ F.obj (unit R)) (i : I)
  证明: IsColimit.ι_map (isColimitFreeCofan I) (F.mapCocone (freeCofan I))
    (Discrete.natTrans fun _ => η) (Discrete.mk i)

Depends on / 依赖: Discrete, Discrete.mk, Discrete.natTrans, F.mapCocone, IsColimit, freeCofan, isColimitFreeCofan, mapCocone, natTrans
-/
lemma ιFree_mapFree (η : unit S ⟶ F.obj (unit R)) (i : I) :
    ιFree i ≫ mapFree F I η = η ≫ F.map (ιFree i) :=
  IsColimit.ι_map (isColimitFreeCofan I) (F.mapCocone (freeCofan I))
    (Discrete.natTrans fun _ => η) (Discrete.mk i)

variable [PreservesColimitsOfShape (Discrete I) F]

/--
Definition of `mapFreeIso` / `mapFreeIso` 的定义

English:
definition mapFreeIso
  signature: (η : unit S ≅ F.obj (unit R))
  body: (isColimitFreeCofan I).coconePointsIsoOfNatIso (isColimitOfPreserves F (isColimitFreeCofan I))
    (Discrete.natIso fun _ => η)

中文:
定义 mapFreeIso
  签名: (η : unit S ≅ F.obj (unit R))
  定义体: (isColimitFreeCofan I).coconePointsIsoOfNatIso (isColimitOfPreserves F (isColimitFreeCofan I))
    (Discrete.natIso fun _ => η)

Depends on / 依赖: F.obj
-/
noncomputable def mapFreeIso (η : unit S ≅ F.obj (unit R)) : free (R := S) I ≅ F.obj (free I) :=
  (isColimitFreeCofan I).coconePointsIsoOfNatIso (isColimitOfPreserves F (isColimitFreeCofan I))
    (Discrete.natIso fun _ => η)

/--
lemma `mapFreeIso_hom` / 引理 `mapFreeIso_hom`

English:
lemma mapFreeIso_hom
  given: (η : unit S ≅ F.obj (unit R))
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 mapFreeIso_hom
  条件: (η : unit S ≅ F.obj (unit R))
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma mapFreeIso_hom (η : unit S ≅ F.obj (unit R)) :
    (mapFreeIso F I η).hom = mapFree F I η.hom := rfl

@[reassoc (attr := simp)]
/--
lemma `ιFree_mapFreeIso_hom` / 引理 `ιFree_mapFreeIso_hom`

English:
lemma ιFree_mapFreeIso_hom
  given: (η : unit S ≅ F.obj (unit R)) (i : I)
  proof: ιFree_mapFree _ _ _ _

@[deprecated (since := "2026-04-21")] alias ιFree_mapFree_inv := ιFree_mapFreeIso_hom

@[reassoc (attr := simp)]

中文:
引理 ιFree_mapFreeIso_hom
  条件: (η : unit S ≅ F.obj (unit R)) (i : I)
  证明: ιFree_mapFree _ _ _ _

@[deprecated (since := "2026-04-21")] alias ιFree_mapFree_inv := ιFree_mapFreeIso_hom

@[reassoc (attr := simp)]
-/
lemma ιFree_mapFreeIso_hom (η : unit S ≅ F.obj (unit R)) (i : I) :
    ιFree i ≫ (mapFreeIso F I η).hom = η.hom ≫ F.map (ιFree i) :=
  ιFree_mapFree _ _ _ _

@[deprecated (since := "2026-04-21")] alias ιFree_mapFree_inv := ιFree_mapFreeIso_hom

@[reassoc (attr := simp)]
/--
lemma `map_ιFree_mapFreeIso_inv` / 引理 `map_ιFree_mapFreeIso_inv`

English:
lemma map_ιFree_mapFreeIso_inv
  given: (η : unit S ≅ F.obj (unit R)) (i : I)
  proof: IsColimit.ι_map (isColimitOfPreserves F (isColimitFreeCofan I)) (freeCofan I)
    (Discrete.natTrans fun _ => η.inv) (Discrete.mk i)

@[deprecated (since := "2026-04-21")] alias map_ιFree_mapFree_hom := map_ιFree_mapFreeIso_inv

中文:
引理 map_ιFree_mapFreeIso_inv
  条件: (η : unit S ≅ F.obj (unit R)) (i : I)
  证明: IsColimit.ι_map (isColimitOfPreserves F (isColimitFreeCofan I)) (freeCofan I)
    (Discrete.natTrans fun _ => η.inv) (Discrete.mk i)

@[deprecated (since := "2026-04-21")] alias map_ιFree_mapFree_hom := map_ιFree_mapFreeIso_inv

Depends on / 依赖: Discrete, Discrete.mk, Discrete.natTrans, IsColimit, freeCofan, isColimitFreeCofan, isColimitOfPreserves, natTrans
-/
lemma map_ιFree_mapFreeIso_inv (η : unit S ≅ F.obj (unit R)) (i : I) :
    F.map (ιFree i) ≫ (mapFreeIso F I η).inv = η.inv ≫ ιFree i :=
  IsColimit.ι_map (isColimitOfPreserves F (isColimitFreeCofan I)) (freeCofan I)
    (Discrete.natTrans fun _ => η.inv) (Discrete.mk i)

@[deprecated (since := "2026-04-21")] alias map_ιFree_mapFree_hom := map_ιFree_mapFreeIso_inv

end

end SheafOfModules
