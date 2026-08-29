/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.Grp.CartesianMonoidal
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.CommGrp_

/-!
# The forgetful functor `(C ⥤ₗ AddCommGroup) ⥤ (C ⥤ₗ Type v)` is an equivalence

This is true as long as `C` is additive.

Here, `C ⥤ₗ D` is the category of finite-limits-preserving functors from `C` to `D`.

To construct a functor from `C ⥤ₗ Type v` to `C ⥤ₗ AddCommGrpCat.{v}`, notice that a left-exact
functor `F : C ⥤ Type v` induces a functor `CommGrp C ⥤ CommGrp (Type v)`. But `CommGrp C` is
equivalent to `C`, and `CommGrp (Type v)` is equivalent to `AddCommGrpCat.{v}`, so we turn this
into a functor `C ⥤ AddCommGrpCat.{v}`. By construction, composing with the forgetful
functor recovers the functor we started with, so since the forgetful functor reflects finite
limits and `F` preserves finite limits, our constructed functor also preserves finite limits. It
can be shown that this construction gives a quasi-inverse to the whiskering operation
`(C ⥤ₗ AddCommGrpCat.{v}) ⥤ (C ⥤ₗ Type v)`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits


universe v v' u u'

namespace AddCommGrpCat

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

namespace leftExactFunctorForgetEquivalence

attribute [local instance] hasFiniteProducts_of_hasFiniteBiproducts

attribute [local instance] AddCommGrpCat.cartesianMonoidalCategory

set_option backward.privateInPublic true in
private noncomputable local instance : CartesianMonoidalCategory C := .ofHasFiniteProducts

set_option backward.privateInPublic true in
private noncomputable local instance : BraidedCategory C := .ofCartesianMonoidalCategory

/--
Definition of `inverseAux` / `inverseAux` 的定义

English:
definition inverseAux
  signature: : (C ⥤ₗ Type v) ⥤ C ⥤ AddCommGrpCat.{v}
  body: Functor.mapCommGrpFunctor ⋙
    (Functor.whiskeringLeft _ _ _).obj Preadditive.commGrpEquivalence.functor ⋙
      (Functor.whiskeringRight _ _ _).obj
        (commGrpTypeEquivalenceCommGrp.functor ⋙ commGroupAddCommGroupEquivalence.functor)

中文:
定义 inverseAux
  签名: : (C ⥤ₗ 类型v) ⥤ C ⥤ 加法交换群范畴.{v}
  定义体: Functor.mapCommGrpFunctor ⋙
    (Functor.whiskeringLeft _ _ _).obj Preadditive.commGrpEquivalence.functor ⋙
      (Functor.whiskeringRight _ _ _).obj
        (commGrpTypeEquivalenceCommGrp.functor ⋙ commGroupAddCommGroupEquivalence.functor)

Depends on / 依赖: Functor, Functor.mapCommGrpFunctor, Functor.whiskeringLeft, Functor.whiskeringRight, Preadditive, Preadditive.commGrpEquivalence.functor, commGroupAddCommGroupEquivalence, commGroupAddCommGroupEquivalence.functor, commGrpEquivalence, commGrpTypeEquivalenceCommGrp, commGrpTypeEquivalenceCommGrp.functor, functor, mapCommGrpFunctor, whiskeringLeft, whiskeringRight
-/
noncomputable def inverseAux : (C ⥤ₗ Type v) ⥤ C ⥤ AddCommGrpCat.{v} :=
  Functor.mapCommGrpFunctor ⋙
    (Functor.whiskeringLeft _ _ _).obj Preadditive.commGrpEquivalence.functor ⋙
      (Functor.whiskeringRight _ _ _).obj
        (commGrpTypeEquivalenceCommGrp.functor ⋙ commGroupAddCommGroupEquivalence.functor)

instance (F : C ⥤ₗ Type v) : PreservesFiniteLimits (inverseAux.obj F) where
  preservesFiniteLimits J _ _ :=
    have : PreservesLimitsOfShape J (inverseAux.obj F ⋙ forget AddCommGrpCat) :=
      inferInstanceAs (PreservesLimitsOfShape J F.1)
    preservesLimitsOfShape_of_reflects_of_preserves _ (forget AddCommGrpCat)

/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : (C ⥤ₗ Type v) ⥤ (C ⥤ₗ AddCommGrpCat.{v})
  body: ObjectProperty.lift _ inverseAux (by simp only [leftExactFunctor_iff]; infer_instance)

中文:
定义 inverse
  签名: : (C ⥤ₗ 类型v) ⥤ (C ⥤ₗ 加法交换群范畴.{v})
  定义体: ObjectProperty.lift _ inverseAux (by simp only [leftExactFunctor_iff]; infer_instance)

Depends on / 依赖: ObjectProperty, ObjectProperty.lift, infer_instance, inverseAux, leftExactFunctor_iff
-/
noncomputable def inverse : (C ⥤ₗ Type v) ⥤ (C ⥤ₗ AddCommGrpCat.{v}) :=
  ObjectProperty.lift _ inverseAux (by simp only [leftExactFunctor_iff]; infer_instance)

open scoped MonObj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Functor.LaxMonoidal.comp Functor.Monoidal.instComp in
/--
Definition of `unitIsoAux` / `unitIsoAux` 的定义

English:
definition unitIsoAux
  signature: (F : C ⥤ AddCommGrpCat.{v}) [PreservesFiniteLimits F] (X : C)
  body: .ofChosenFiniteProducts _
    commGrpTypeEquivalenceCommGrp.inverse.obj (AddCommGrpCat.toCommGrp.obj (F.obj X)) ≅
      (F ⋙ forget AddCommGrpCat).mapCommGrp.obj (Preadditive.commGrpEquivalence.functor.obj X) := by
  letI : (F ⋙ forget AddCommGrpCat).Braided := .ofChosenFiniteProducts _
  letI : F.M

中文:
定义 unitIsoAux
  签名: (F : C ⥤ 加法交换群范畴.{v}) [保持FiniteLimits F] (X : C)
  定义体: .ofChosenFiniteProducts _
    commGrpTypeEquivalenceCommGrp.inverse.obj (AddCommGrpCat.toCommGrp.obj (F.obj X)) ≅
      (F ⋙ forget AddCommGrpCat).mapCommGrp.obj (Preadditive.commGrpEquivalence.functor.obj X) := by
  letI : (F ⋙ forget AddCommGrpCat).Braided := .ofChosenFiniteProducts _
  letI : F.M

Depends on / 依赖: ofChosenFiniteProducts
-/
noncomputable def unitIsoAux (F : C ⥤ AddCommGrpCat.{v}) [PreservesFiniteLimits F] (X : C) :
    letI : (F ⋙ forget AddCommGrpCat).Braided := .ofChosenFiniteProducts _
    commGrpTypeEquivalenceCommGrp.inverse.obj (AddCommGrpCat.toCommGrp.obj (F.obj X)) ≅
      (F ⋙ forget AddCommGrpCat).mapCommGrp.obj (Preadditive.commGrpEquivalence.functor.obj X) := by
  letI : (F ⋙ forget AddCommGrpCat).Braided := .ofChosenFiniteProducts _
  letI : F.Monoidal := .ofChosenFiniteProducts _
  refine CommGrp.mkIso Multiplicative.toAdd.toIso (by
    rw [Functor.obj.η_def X (F := F ⋙ forget AddCommGrpCat)]
    cat_disch) ?_
  dsimp [-Functor.comp_map, -ConcreteCategory.forget_map_eq_ofHom]
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  simp only [Category.id_comp]
  rw [Functor.obj.μ_def X (F := F ⋙ forget AddCommGrpCat)]; rw [Preadditive.mul_def X]; rw [Functor.comp_map]; rw [F.map_add]; rw [Functor.Monoidal.μ_comp F (forget AddCommGrpCat) X X]; rw [Category.assoc]; rw [← Functor.map_comp]; rw [Preadditive.comp_add]; rw [Functor.Monoidal.μ_fst]; rw [Functor.Monoidal.μ_snd]
  ext
  -- `simp [types_tensorObj_def]` says
  simp only [types_tensorObj_def, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
    Equiv.toIso_hom_hom_apply, Functor.comp_obj, hom_add, tensor_apply, TypeCat.hom_ofHom,
    TypeCat.Fun.coe_mk, AddMonoidHom.add_apply]
  rw [dsimp% [types_tensorObj_def]; rw [types_tensorUnit_def] μ_forget_apply]
  rfl

/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: : 𝟭 (C ⥤ₗ AddCommGrpCat) ≅
  body: NatIso.ofComponents (fun F => InducedCategory.isoMk (NatIso.ofComponents (fun X =>
    commGroupAddCommGroupEquivalence.counitIso.app _ ≪≫
      (CommGrpCat.toAddCommGrp.mapIso (commGrpTypeEquivalenceCommGrp.counitIso.app
        (AddCommGrpCat.toCommGrp.obj (F.obj.obj X)))).symm ≪≫
      CommGrpCat

中文:
定义 unitIso
  签名: : 𝟭 (C ⥤ₗ 加法交换群范畴) ≅
  定义体: NatIso.ofComponents (fun F => InducedCategory.isoMk (NatIso.ofComponents (fun X =>
    commGroupAddCommGroupEquivalence.counitIso.app _ ≪≫
      (CommGrpCat.toAddCommGrp.mapIso (commGrpTypeEquivalenceCommGrp.counitIso.app
        (AddCommGrpCat.toCommGrp.obj (F.obj.obj X)))).symm ≪≫
      CommGrpCat

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.toCommGrp.obj, BoolAlg, BoolAlg.str, CommGrpCat, CommGrpCat.toAddCommGrp.mapIso, CommGrpTypeEquivalenceCommGrp, CommGrpTypeEquivalenceCommGrp.functor.mapIso, F.obj, F.obj.obj, InducedCategory, InducedCategory.isoMk, NatIso, NatIso.ofComponents, commGroupAddCommGroupEquivalence, commGroupAddCommGroupEquivalence.counitIso.app, commGrpTypeEquivalenceCommGrp, commGrpTypeEquivalenceCommGrp.counitIso.app, counitIso, functor
-/
noncomputable def unitIso : 𝟭 (C ⥤ₗ AddCommGrpCat) ≅
    (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _)) ⋙ inverse :=
  NatIso.ofComponents (fun F => InducedCategory.isoMk (NatIso.ofComponents (fun X =>
    commGroupAddCommGroupEquivalence.counitIso.app _ ≪≫
      (CommGrpCat.toAddCommGrp.mapIso (commGrpTypeEquivalenceCommGrp.counitIso.app
        (AddCommGrpCat.toCommGrp.obj (F.obj.obj X)))).symm ≪≫
      CommGrpCat.toAddCommGrp.mapIso
        (CommGrpTypeEquivalenceCommGrp.functor.mapIso (unitIsoAux F.obj X)))))

end leftExactFunctorForgetEquivalence

variable (C) in
/--
Definition of `leftExactFunctorForgetEquivalence` / `leftExactFunctorForgetEquivalence` 的定义

English:
definition leftExactFunctorForgetEquivalence
  signature: :
  body: (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _))
  inverse := leftExactFunctorForgetEquivalence.inverse
  unitIso := leftExactFunctorForgetEquivalence.unitIso
  counitIso := Iso.refl _

中文:
定义 leftExactFunctorForgetEquivalence
  签名: :
  定义体: (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _))
  inverse := leftExactFunctorForgetEquivalence.inverse
  unitIso := leftExactFunctorForgetEquivalence.unitIso
  counitIso := Iso.refl _

Depends on / 依赖: BooleanRing, LeftExactFunctor, LeftExactFunctor.of, LeftExactFunctor.whiskeringRight, forget, whiskeringRight
-/
noncomputable def leftExactFunctorForgetEquivalence :
    (C ⥤ₗ AddCommGrpCat.{v}) ≌ (C ⥤ₗ Type v) where
  functor := (LeftExactFunctor.whiskeringRight _ _ _).obj (LeftExactFunctor.of (forget _))
  inverse := leftExactFunctorForgetEquivalence.inverse
  unitIso := leftExactFunctorForgetEquivalence.unitIso
  counitIso := Iso.refl _

end

end AddCommGrpCat
