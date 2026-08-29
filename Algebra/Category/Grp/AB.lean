/-
Copyright (c) 2023 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Moritz Firsching, Nikolas Kuhn, Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# AB axioms for the category of abelian groups

This file proves that the category of abelian groups satisfies Grothendieck's axioms AB5, AB4, and
AB4\*.
-/

public section

universe u

open CategoryTheory Limits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance {J C : Type*} [Category* J] [Category* C] [HasColimitsOfShape J C] [Preadditive C] :
    (colim (J := J) (C := C)).Additive where

variable {J : Type u} [SmallCategory J] [IsFiltered J]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: Functor.preservesHomology_of_map_exact _ (fun S hS => by
    replace hS := fun j => hS.map ((evaluation _ _).obj j)
    simp only [ShortComplex.ab_exact_iff_ker_le_range] at hS ⊢
    intro x (hx : _ = _)
    dsimp at hx
    rcases Concrete.colimit_exists_rep S.X₂ x with ⟨j, y, rfl⟩
    rw [← Concret

中文:
实例 :
  定义体: Functor.preservesHomology_of_map_exact _ (fun S hS => by
    replace hS := fun j => hS.map ((evaluation _ _).obj j)
    simp only [ShortComplex.ab_exact_iff_ker_le_range] at hS ⊢
    intro x (hx : _ = _)
    dsimp at hx
    rcases Concrete.colimit_exists_rep S.X₂ x with ⟨j, y, rfl⟩
    rw [← Concret

Depends on / 依赖: AddCommGrpCat, PreservesHomology
-/
noncomputable instance :
    (colim (J := J) (C := AddCommGrpCat.{u})).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (fun S hS => by
    replace hS := fun j => hS.map ((evaluation _ _).obj j)
    simp only [ShortComplex.ab_exact_iff_ker_le_range] at hS ⊢
    intro x (hx : _ = _)
    dsimp at hx
    rcases Concrete.colimit_exists_rep S.X₂ x with ⟨j, y, rfl⟩
    rw [← ConcreteCategory.comp_apply]; rw [colimMap_eq]; rw [colimit.ι_map]; rw [ConcreteCategory.comp_apply]; rw [← map_zero (colimit.ι S.X₃ j).hom] at hx
    rcases Concrete.colimit_exists_of_rep_eq.{u, u, u} S.X₃ _ _ hx with ⟨k, e₁, e₂, hk⟩
    rw [map_zero]; rw [← ConcreteCategory.comp_apply]; rw [← NatTrans.naturality]; rw [ConcreteCategory.comp_apply]
      at hk
    rcases hS k hk with ⟨t, ht⟩
    use colimit.ι S.X₁ k t
    erw [← ConcreteCategory.comp_apply, colimit.ι_map, ConcreteCategory.comp_apply, ht]
    exact colimit.w_apply S.X₂ e₁ y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: by
  apply Functor.preservesFiniteLimits_of_preservesHomology

中文:
实例 :
  定义体: by
  apply Functor.preservesFiniteLimits_of_preservesHomology

Depends on / 依赖: AddCommGrpCat, Functor, Functor.preservesFiniteLimits_of_preservesHomology, preservesFiniteLimits_of_preservesHomology
-/
noncomputable instance :
PreservesFiniteLimits colim (J := J) (C := AddCommGrpCat.{u}) := by
  apply Functor.preservesFiniteLimits_of_preservesHomology

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFilteredColimits (AddCommGrpCat.{u})
  body: inferInstance

中文:
实例 :
  签名: HasFilteredColimits (AddCommGrpCat.{u})
  定义体: inferInstance
-/
instance : HasFilteredColimits (AddCommGrpCat.{u}) where
  HasColimitsOfShape := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AB5 (AddCommGrpCat.{u})
  body: { preservesFiniteLimits := inferInstance }

中文:
实例 :
  签名: AB5 (AddCommGrpCat.{u})
  定义体: { preservesFiniteLimits := inferInstance }

Depends on / 依赖: preservesFiniteLimits
-/
noncomputable instance : AB5 (AddCommGrpCat.{u}) where
  ofShape _ := { preservesFiniteLimits := inferInstance }

attribute [local instance] Abelian.hasFiniteBiproducts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AB4 AddCommGrpCat.{u}
  body: AB4.of_AB5 _

中文:
实例 :
  签名: AB4 AddCommGrpCat.{u}
  定义体: AB4.of_AB5 _

Depends on / 依赖: AB4.of_AB5, of_AB5
-/
instance : AB4 AddCommGrpCat.{u} := AB4.of_AB5 _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasExactLimitsOfShape (Discrete J) (AddCommGrpCat.{u})
  body: by
  apply +allowSynthFailures hasExactLimitsOfShape_of_preservesEpi
  exact {
    preserves {X Y} f hf := by
      let iX : limit X ≅ AddCommGrpCat.of ((i : J) -> X.obj ⟨i⟩) := (Pi.isoLimit X).symm ≪≫
        (limit.isLimit _).conePointUniqueUpToIso (AddCommGrpCat.HasLimit.productLimitCone _).isLim

中文:
实例 :
  签名: HasExactLimitsOfShape (Discrete J) (AddCommGrpCat.{u})
  定义体: by
  apply +allowSynthFailures hasExactLimitsOfShape_of_preservesEpi
  exact {
    preserves {X Y} f hf := by
      let iX : limit X ≅ AddCommGrpCat.of ((i : J) -> X.obj ⟨i⟩) := (Pi.isoLimit X).symm ≪≫
        (limit.isLimit _).conePointUniqueUpToIso (AddCommGrpCat.HasLimit.productLimitCone _).isLim

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.HasLimit.productLimitCone, AddCommGrpCat.of, HasLimit, Pi.isoLimit, Pi.map, X.obj, Y.obj, allowSynthFailures, conePointUniqueUpToIso, f.app, hasExactLimitsOfShape_of_preservesEpi, isLimit, isoLimit, limit.isLimit, preserves, productLimitCone
-/
instance : HasExactLimitsOfShape (Discrete J) (AddCommGrpCat.{u}) := by
  apply +allowSynthFailures hasExactLimitsOfShape_of_preservesEpi
  exact {
    preserves {X Y} f hf := by
      let iX : limit X ≅ AddCommGrpCat.of ((i : J) -> X.obj ⟨i⟩) := (Pi.isoLimit X).symm ≪≫
        (limit.isLimit _).conePointUniqueUpToIso (AddCommGrpCat.HasLimit.productLimitCone _).isLimit
      let iY : limit Y ≅ AddCommGrpCat.of ((i : J) -> Y.obj ⟨i⟩) := (Pi.isoLimit Y).symm ≪≫
        (limit.isLimit _).conePointUniqueUpToIso (AddCommGrpCat.HasLimit.productLimitCone _).isLimit
      have : Pi.map (fun i => f.app ⟨i⟩) = iX.inv ≫ lim.map f ≫ iY.hom := by
        simp only [Discrete.functor_obj_eq_as, Discrete.mk_as, Pi.isoLimit,
          IsLimit.conePointUniqueUpToIso, limit.cone, AddCommGrpCat.HasLimit.productLimitCone,
          Iso.trans_inv, Functor.mapIso_inv, IsLimit.uniqueUpToIso_inv, Cone.forget_map,
          IsLimit.liftConeMorphism_hom, limit.isLimit_lift, Iso.symm_inv, Functor.mapIso_hom,
          IsLimit.uniqueUpToIso_hom, lim_map, Iso.trans_hom, Iso.symm_hom,
          AddCommGrpCat.HasLimit.lift, Category.assoc, limit.lift_map_assoc, iX, iY]
        ext g j
        change _ = (_ ≫ limit.π (Discrete.functor fun j => Y.obj { as := j }) ⟨j⟩) _
        simp only [Discrete.functor_obj_eq_as, productIsProduct', limit.lift_π,
          Fan.mk_π_app, Pi.map_apply]
        change _ = (_ ≫ _ ≫ limit.π Y ⟨j⟩) _
        simp
      suffices Epi (iX.hom ≫ (iX.inv ≫ lim.map f ≫ iY.hom) ≫ iY.inv) by simpa using this
      suffices Epi (iX.inv ≫ lim.map f ≫ iY.hom) from inferInstance
      rw [AddCommGrpCat.epi_iff_surjective]; rw [← this]
      simp_rw [CategoryTheory.NatTrans.epi_iff_epi_app, AddCommGrpCat.epi_iff_surjective] at hf
      refine fun b => ⟨fun i => (hf ⟨i⟩ (b i)).choose, ?_⟩
      funext i
      exact (hf ⟨i⟩ (b i)).choose_spec }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AB4Star AddCommGrpCat.{u}
  body: inferInstance

中文:
实例 :
  签名: AB4Star AddCommGrpCat.{u}
  定义体: inferInstance
-/
instance : AB4Star AddCommGrpCat.{u} where
  ofShape _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSeparator AddCommGrpCat.{u}
  body: by
    use AddCommGrpCat.of (ULift Int)
    intro A B f g h; simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq', ULift.forall]
    (intro x; specialize h (AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (

中文:
实例 :
  签名: HasSeparator AddCommGrpCat.{u}
  定义体: by
    use AddCommGrpCat.of (ULift Int)
    intro A B f g h; simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq', ULift.forall]
    (intro x; specialize h (AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.ext_iff, AddCommGrpCat.hom_comp, AddCommGrpCat.of, AddCommGrpCat.ofHom, AddMonoidHom, AddMonoidHom.coe_comp, AddMonoidHom.mk, Function, Function.comp_apply, ObjectProperty, ObjectProperty.singleton_iff, ULift.forall, add_smul, coe_comp, comp_apply, ext_iff, forall_eq, hom_comp, singleton_iff
-/
instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift Int)
    intro A B f g h; simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq', ULift.forall]
    (intro x; specialize h (AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1; aesop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsGrothendieckAbelian.{u} AddCommGrpCat.{u}

中文:
实例 :
  签名: IsGrothendieckAbelian.{u} AddCommGrpCat.{u}
-/
instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where
