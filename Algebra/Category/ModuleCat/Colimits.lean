/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# The category of R-modules has all colimits.

From the existence of colimits in `AddCommGrpCat`, we deduce the existence of colimits
in `ModuleCat R`. This way, we get for free that the functor
`forget₂ (ModuleCat R) AddCommGrpCat` commutes with colimits.

Note that finite colimits can already be obtained from the instance `Abelian (Module R)`.

TODO:
In fact, in `ModuleCat R` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well.
-/

@[expose] public section

universe w' w u v

open CategoryTheory Category Limits

variable {R : Type w} [Ring R]

namespace ModuleCat

variable {J : Type u} [Category.{v} J] (F : J ⥤ ModuleCat.{w'} R)

namespace HasColimit

variable [HasColimit (F ⋙ forget₂ _ AddCommGrpCat)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The induced scalar multiplication on
`colimit (F ⋙ forget₂ _ AddCommGrpCat)`. -/
@[simps]
/--
Definition of `coconePointSMul` / `coconePointSMul` 的定义

English:
definition coconePointSMul
  signature: :
  body: colimMap
    { app := fun j => (F.obj j).smul r
      naturality := fun _ _ _ => smul_naturality _ _ }
  map_zero' := colimit.hom_ext (by simp +instances)
  map_one' := colimit.hom_ext (by simp +instances)
  map_add' r s := colimit.hom_ext (fun j => by
    simp +instances only [Functor.comp_obj, for

中文:
定义 coconePointSMul
  签名: :
  定义体: colimMap
    { app := fun j => (F.obj j).smul r
      naturality := fun _ _ _ => smul_naturality _ _ }
  map_zero' := colimit.hom_ext (by simp +instances)
  map_one' := colimit.hom_ext (by simp +instances)
  map_add' r s := colimit.hom_ext (fun j => by
    simp +instances only [Functor.comp_obj, for

Depends on / 依赖: colimMap
-/
noncomputable def coconePointSMul :
    R ->+* End (colimit (F ⋙ forget₂ _ AddCommGrpCat)) where
  toFun r := colimMap
    { app := fun j => (F.obj j).smul r
      naturality := fun _ _ _ => smul_naturality _ _ }
  map_zero' := colimit.hom_ext (by simp +instances)
  map_one' := colimit.hom_ext (by simp +instances)
  map_add' r s := colimit.hom_ext (fun j => by
    simp +instances only [Functor.comp_obj, forget₂_obj, map_add, ι_colimMap]
    rw [Preadditive.add_comp]; rw [Preadditive.comp_add]
    simp only [ι_colimMap, Functor.comp_obj, forget₂_obj])
  map_mul' r s := colimit.hom_ext (fun j => by simp +instances)

set_option backward.isDefEq.respectTransparency false in
/-- The cocone for `F` constructed from the colimit of
`(F ⋙ forget₂ (ModuleCat R) AddCommGrpCat)`. -/
@[simps]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: mkOfSMul (coconePointSMul F)
  ι :=
    { app := fun j => homMk (colimit.ι (F ⋙ forget₂ _ AddCommGrpCat) j) (fun r => by
        dsimp
        -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
        erw [mkOfSMul_smul]
        simp)
      naturality := 

中文:
定义 colimitCocone
  签名: : Cocone F where
  定义体: mkOfSMul (coconePointSMul F)
  ι :=
    { app := fun j => homMk (colimit.ι (F ⋙ forget₂ _ AddCommGrpCat) j) (fun r => by
        dsimp
        -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
        erw [mkOfSMul_smul]
        simp)
      naturality := 

Depends on / 依赖: coconePointSMul, f.hom, mkOfSMul
-/
noncomputable def colimitCocone : Cocone F where
  pt := mkOfSMul (coconePointSMul F)
  ι :=
    { app := fun j => homMk (colimit.ι (F ⋙ forget₂ _ AddCommGrpCat) j) (fun r => by
        dsimp
        -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
        erw [mkOfSMul_smul]
        simp)
      naturality := fun i j f => by
        apply (forget₂ _ AddCommGrpCat).map_injective
        simp only [Functor.map_comp, forget₂_map_homMk]
        dsimp
        erw [colimit.w (F ⋙ forget₂ _ AddCommGrpCat), comp_id] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitColimitCocone` / `isColimitColimitCocone` 的定义

English:
definition isColimitColimitCocone
  signature: : IsColimit (colimitCocone F) where
  body: homMk (colimit.desc _ ((forget₂ _ AddCommGrpCat).mapCocone s)) (fun r => by
    apply colimit.hom_ext
    intro j
    dsimp
    rw [colimit.ι_desc_assoc]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [mkOfSMul_smul]
    dsimp
    simp only

中文:
定义 isColimitColimitCocone
  签名: : IsColimit (colimitCocone F) where
  定义体: homMk (colimit.desc _ ((forget₂ _ AddCommGrpCat).mapCocone s)) (fun r => by
    apply colimit.hom_ext
    intro j
    dsimp
    rw [colimit.ι_desc_assoc]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [mkOfSMul_smul]
    dsimp
    simp only

Depends on / 依赖: AddCommGrpCat, colimit, colimit.desc, colimit.hom_ext, hom_ext, mapCocone
-/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) where
  desc s := homMk (colimit.desc _ ((forget₂ _ AddCommGrpCat).mapCocone s)) (fun r => by
    apply colimit.hom_ext
    intro j
    dsimp
    rw [colimit.ι_desc_assoc]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [mkOfSMul_smul]
    dsimp
    simp only [ι_colimMap_assoc, Functor.comp_obj, forget₂_obj, colimit.ι_desc,
      Functor.mapCocone_pt, Functor.mapCocone_ι_app, forget₂_map]
    exact smul_naturality (s.ι.app j) r)
  fac s j := by
    apply (forget₂ _ AddCommGrpCat).map_injective
    exact colimit.ι_desc ((forget₂ _ AddCommGrpCat).mapCocone s) j
  uniq s m hm := by
    apply (forget₂ _ AddCommGrpCat).map_injective
    apply colimit.hom_ext
    intro j
    erw [colimit.ι_desc ((forget₂ _ AddCommGrpCat).mapCocone s) j]
    dsimp
    rw [← hm]
    rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimit F
  body: ⟨_, isColimitColimitCocone F⟩

中文:
实例 :
  签名: HasColimit F
  定义体: ⟨_, isColimitColimitCocone F⟩

Depends on / 依赖: isColimitColimitCocone
-/
instance : HasColimit F := ⟨_, isColimitColimitCocone F⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimit F (forget₂ _ AddCommGrpCat)
  body: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F) (colimit.isColimit _)

中文:
实例 :
  签名: PreservesColimit F (forget₂ _ AddCommGrpCat)
  定义体: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F) (colimit.isColimit _)

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isColimitColimitCocone, preservesColimit_of_preserves_colimit_cocone
-/
noncomputable instance : PreservesColimit F (forget₂ _ AddCommGrpCat) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F) (colimit.isColimit _)

/--
Instance `reflectsColimit` / 实例 `reflectsColimit`

English:
instance reflectsColimit
  signature: :
  body: reflectsColimit_of_reflectsIsomorphisms _ _

中文:
实例 reflectsColimit
  签名: :
  定义体: reflectsColimit_of_reflectsIsomorphisms _ _

Depends on / 依赖: reflectsColimit_of_reflectsIsomorphisms
-/
noncomputable instance reflectsColimit :
    ReflectsColimit F (forget₂ (ModuleCat.{w'} R) AddCommGrpCat) :=
  reflectsColimit_of_reflectsIsomorphisms _ _

end HasColimit

variable (J R)

/--
Instance `hasColimitsOfShape` / 实例 `hasColimitsOfShape`

English:
instance hasColimitsOfShape
  signature: [HasColimitsOfShape J AddCommGrpCat.{w'}]

中文:
实例 hasColimitsOfShape
  签名: [HasColimitsOfShape J AddCommGrpCat.{w'}]
-/
instance hasColimitsOfShape [HasColimitsOfShape J AddCommGrpCat.{w'}] :
    HasColimitsOfShape J (ModuleCat.{w'} R) where

/--
Instance `reflectsColimitsOfShape` / 实例 `reflectsColimitsOfShape`

English:
instance reflectsColimitsOfShape
  signature: [HasColimitsOfShape J AddCommGrpCat.{w'}]

中文:
实例 reflectsColimitsOfShape
  签名: [HasColimitsOfShape J AddCommGrpCat.{w'}]
-/
noncomputable instance reflectsColimitsOfShape [HasColimitsOfShape J AddCommGrpCat.{w'}] :
    ReflectsColimitsOfShape J (forget₂ (ModuleCat.{w'} R) AddCommGrpCat) where

/--
Instance `hasColimitsOfSize` / 实例 `hasColimitsOfSize`

English:
instance hasColimitsOfSize
  signature: [HasColimitsOfSize.{v, u} AddCommGrpCat.{w'}]

中文:
实例 hasColimitsOfSize
  签名: [HasColimitsOfSize.{v, u} AddCommGrpCat.{w'}]
-/
instance hasColimitsOfSize [HasColimitsOfSize.{v, u} AddCommGrpCat.{w'}] :
    HasColimitsOfSize.{v, u} (ModuleCat.{w'} R) where

/--
Instance `forget₂PreservesColimitsOfShape` / 实例 `forget₂PreservesColimitsOfShape`

English:
instance forget₂PreservesColimitsOfShape

中文:
实例 forget₂PreservesColimitsOfShape
-/
noncomputable instance forget₂PreservesColimitsOfShape
    [HasColimitsOfShape J AddCommGrpCat.{w'}] :
    PreservesColimitsOfShape J (forget₂ (ModuleCat.{w'} R) AddCommGrpCat) where

/--
Instance `forget₂PreservesColimitsOfSize` / 实例 `forget₂PreservesColimitsOfSize`

English:
instance forget₂PreservesColimitsOfSize

中文:
实例 forget₂PreservesColimitsOfSize
-/
noncomputable instance forget₂PreservesColimitsOfSize
    [HasColimitsOfSize.{u, v} AddCommGrpCat.{w'}] :
    PreservesColimitsOfSize.{u, v} (forget₂ (ModuleCat.{w'} R) AddCommGrpCat) where

noncomputable instance
    [HasColimitsOfSize.{u, v} AddCommGrpMax.{w, w'}] :
    PreservesColimitsOfSize.{u, v} (forget₂ (ModuleCat.{max w w'} R) AddCommGrpCat) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteColimits (ModuleCat.{w'} R)
  body: inferInstance

中文:
实例 :
  签名: HasFiniteColimits (ModuleCat.{w'} R)
  定义体: inferInstance
-/
instance : HasFiniteColimits (ModuleCat.{w'} R) := inferInstance

-- Sanity checks, just to make sure typeclass search can find the instances we want.
example (R : Type u) [Ring R] : HasColimits (ModuleCat.{max v u} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasColimits (ModuleCat.{max u v} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasColimits (ModuleCat.{u} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasCoequalizers (ModuleCat.{u} R) := by
  infer_instance

-- for some reason, this instance is not found automatically later on
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCoequalizers (ModuleCat.{v} R)
  body: inferInstance

中文:
实例 :
  签名: HasCoequalizers (ModuleCat.{v} R)
  定义体: inferInstance
-/
instance : HasCoequalizers (ModuleCat.{v} R) where

noncomputable example (R : Type u) [Ring R] :
    PreservesColimits (forget₂ (ModuleCat.{u} R) AddCommGrpCat) := inferInstance

section

variable (R : Type w) [CommRing R] (M ι : Type u) [AddCommGroup M] [Module R M]

/-- The coproduct cone induced by the concrete coproduct. -/
noncomputable
/--
Definition of `finsuppCocone` / `finsuppCocone` 的定义

English:
definition finsuppCocone
  signature: : Cofan fun _ : ι => ModuleCat.of R M
  body: Cofan.mk (ModuleCat.of R (ι ->₀ M)) fun i =>
    ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := ModuleCat.of R M))

中文:
定义 finsuppCocone
  签名: : Cofan fun _ : ι => ModuleCat.of R M
  定义体: Cofan.mk (ModuleCat.of R (ι ->₀ M)) fun i =>
    ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := ModuleCat.of R M))

Depends on / 依赖: Cofan.mk, Finsupp, Finsupp.lsingle, ModuleCat, ModuleCat.of, ModuleCat.ofHom, lsingle
-/
def finsuppCocone : Cofan fun _ : ι => ModuleCat.of R M :=
  Cofan.mk (ModuleCat.of R (ι ->₀ M)) fun i =>
    ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := ModuleCat.of R M))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The concrete coproduct cone is colimiting. -/
noncomputable
/--
Definition of `finsuppCoconeIsColimit` / `finsuppCoconeIsColimit` 的定义

English:
definition finsuppCoconeIsColimit
  signature: : IsColimit (finsuppCocone R M ι) where
  body: ModuleCat.ofHom Finsupp.lsum R (N := s.pt) (fun i => (s.ι.app ⟨i⟩).hom)
  fac := by aesop (add simp finsuppCocone)
  uniq s f h := by
    ext : 1
    exact Finsupp.lhom_ext' fun i => LinearMap.ext fun x => by simpa using! congr($(h ⟨i⟩) (x : M))

中文:
定义 finsuppCoconeIsColimit
  签名: : IsColimit (finsuppCocone R M ι) where
  定义体: ModuleCat.ofHom Finsupp.lsum R (N := s.pt) (fun i => (s.ι.app ⟨i⟩).hom)
  fac := by aesop (add simp finsuppCocone)
  uniq s f h := by
    ext : 1
    exact Finsupp.lhom_ext' fun i => LinearMap.ext fun x => by simpa using! congr($(h ⟨i⟩) (x : M))

Depends on / 依赖: Finsupp, Finsupp.lsum, ModuleCat, ModuleCat.ofHom, s.pt
-/
def finsuppCoconeIsColimit : IsColimit (finsuppCocone R M ι) where
desc s := ModuleCat.ofHom Finsupp.lsum R (N := s.pt) (fun i => (s.ι.app ⟨i⟩).hom)
  fac := by aesop (add simp finsuppCocone)
  uniq s f h := by
    ext : 1
    exact Finsupp.lhom_ext' fun i => LinearMap.ext fun x => by simpa using! congr($(h ⟨i⟩) (x : M))

end

end ModuleCat
