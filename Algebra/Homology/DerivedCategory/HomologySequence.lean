/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# The homology sequence

In this file, we construct `homologyFunctor C n : DerivedCategory C ⥤ C` for all `n : ℤ`,
show that they are homological functors which form a shift sequence, and construct
the long exact homology sequences associated to distinguished triangles in the
derived category.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace DerivedCategory

/--
Definition of `homologyFunctor` / `homologyFunctor` 的定义

English:
definition homologyFunctor
  signature: (n : Int)
  body: HomologicalComplexUpToQuasiIso.homologyFunctor C (ComplexShape.up Int) n

中文:
定义 homologyFunctor
  签名: (n : 整数)
  定义体: HomologicalComplexUpToQuasiIso.homologyFunctor C (ComplexShape.up Int) n

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.homologyFunctor, homologyFunctor
-/
noncomputable def homologyFunctor (n : Int) : DerivedCategory C ⥤ C :=
  HomologicalComplexUpToQuasiIso.homologyFunctor C (ComplexShape.up Int) n

/--
Definition of `homologyFunctorFactors` / `homologyFunctorFactors` 的定义

English:
definition homologyFunctorFactors
  signature: (n : Int)
  body: HomologicalComplexUpToQuasiIso.homologyFunctorFactors C (ComplexShape.up Int) n

中文:
定义 homologyFunctorFactors
  签名: (n : 整数)
  定义体: HomologicalComplexUpToQuasiIso.homologyFunctorFactors C (ComplexShape.up Int) n

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.homologyFunctorFactors, homologyFunctorFactors
-/
noncomputable def homologyFunctorFactors (n : Int) : Q ⋙ homologyFunctor C n ≅
    HomologicalComplex.homologyFunctor _ _ n :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactors C (ComplexShape.up Int) n

-- needed in `homologyMap_comp_eq_zero_of_distTriang`
set_option backward.isDefEq.respectTransparency false in
variable {C} in
@[reassoc (attr := simp)]
/--
lemma `homologyFunctorFactors_hom_naturality` / 引理 `homologyFunctorFactors_hom_naturality`

English:
lemma homologyFunctorFactors_hom_naturality
  proof: (homologyFunctorFactors C n).hom.naturality f

中文:
引理 homologyFunctorFactors_hom_naturality
  证明: (homologyFunctorFactors C n).hom.naturality f

Depends on / 依赖: hom.naturality, homologyFunctorFactors, naturality
-/
lemma homologyFunctorFactors_hom_naturality
    {K L : CochainComplex C Int} (f : K ⟶ L) (n : Int) :
    (homologyFunctor C n).map (Q.map f) ≫ (homologyFunctorFactors C n).hom.app L =
    (homologyFunctorFactors C n).hom.app K ≫ HomologicalComplex.homologyMap f n :=
  (homologyFunctorFactors C n).hom.naturality f

/--
Definition of `homologyFunctorFactorsh` / `homologyFunctorFactorsh` 的定义

English:
definition homologyFunctorFactorsh
  signature: (n : Int)
  body: HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh C (ComplexShape.up Int) n

@[reassoc]

中文:
定义 homologyFunctorFactorsh
  签名: (n : 整数)
  定义体: HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh C (ComplexShape.up Int) n

@[reassoc]

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh, homologyFunctorFactorsh
-/
noncomputable def homologyFunctorFactorsh (n : Int) : Qh ⋙ homologyFunctor C n ≅
    HomotopyCategory.homologyFunctor _ _ n :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh C (ComplexShape.up Int) n

@[reassoc]
/--
lemma `homologyFunctorFactorsh_hom_app_quotient_obj` / 引理 `homologyFunctorFactorsh_hom_app_quotient_obj`

English:
lemma homologyFunctorFactorsh_hom_app_quotient_obj
  given: (K : CochainComplex C Int) (n : Int)
  proof: HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_hom_app_quotient_obj ..

@[reassoc]

中文:
引理 homologyFunctorFactorsh_hom_app_quotient_obj
  条件: (K : 上链复形 C 整数) (n : 整数)
  证明: HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_hom_app_quotient_obj ..

@[reassoc]

Depends on / 依赖: HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_hom_app_quotient_obj, homologyFunctorFactorsh_hom_app_quotient_obj
-/
lemma homologyFunctorFactorsh_hom_app_quotient_obj (K : CochainComplex C Int) (n : Int) :
    (homologyFunctorFactorsh C n).hom.app ((HomotopyCategory.quotient _ _).obj K) =
    (homologyFunctor C n).map ((quotientCompQhIso C).hom.app K) ≫
      (homologyFunctorFactors C n).hom.app K ≫
        (HomotopyCategory.homologyFunctorFactors C (.up Int) n).inv.app _ :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_hom_app_quotient_obj ..

@[reassoc]
/--
lemma `homologyFunctorFactorsh_inv_app_quotient_obj` / 引理 `homologyFunctorFactorsh_inv_app_quotient_obj`

English:
lemma homologyFunctorFactorsh_inv_app_quotient_obj
  given: (K : CochainComplex C Int) (n : Int)
  proof: HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_inv_app_quotient_obj ..

中文:
引理 homologyFunctorFactorsh_inv_app_quotient_obj
  条件: (K : 上链复形 C 整数) (n : 整数)
  证明: HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_inv_app_quotient_obj ..

Depends on / 依赖: HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_inv_app_quotient_obj, homologyFunctorFactorsh_inv_app_quotient_obj
-/
lemma homologyFunctorFactorsh_inv_app_quotient_obj (K : CochainComplex C Int) (n : Int) :
    (homologyFunctorFactorsh C n).inv.app ((HomotopyCategory.quotient _ _).obj K) =
    (HomotopyCategory.homologyFunctorFactors C (.up Int) n).hom.app _ ≫
      (homologyFunctorFactors C n).inv.app K ≫
        (homologyFunctor C n).map ((quotientCompQhIso C).inv.app K) :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_inv_app_quotient_obj ..

set_option backward.defeqAttrib.useBackward true in
variable {C} in
/--
lemma `isIso_Qh_map_iff` / 引理 `isIso_Qh_map_iff`

English:
lemma isIso_Qh_map_iff
  given: {X Y : HomotopyCategory C (ComplexShape.up Int)} (f : X ⟶ Y)
  proof: by
  constructor
  · intro hf
    rw [HomotopyCategory.mem_quasiIso_iff]
    intro n
    rw [← NatIso.isIso_map_iff (homologyFunctorFactorsh C n) f]
    dsimp
    infer_instance
  · exact Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _

中文:
引理 isIso_Qh_map_iff
  条件: {X Y : HomotopyCategory C (余mplexShape.up 整数)} (f : X ⟶ Y)
  证明: by
  constructor
  · intro hf
    rw [HomotopyCategory.mem_quasiIso_iff]
    intro n
    rw [← NatIso.isIso_map_iff (homologyFunctorFactorsh C n) f]
    dsimp
    infer_instance
  · exact Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _

Depends on / 依赖: HomotopyCategory, HomotopyCategory.mem_quasiIso_iff, HomotopyCategory.quasiIso, Localization, Localization.inverts, NatIso, NatIso.isIso_map_iff, homologyFunctorFactorsh, infer_instance, inverts, isIso_map_iff, mem_quasiIso_iff, quasiIso
-/
lemma isIso_Qh_map_iff {X Y : HomotopyCategory C (ComplexShape.up Int)} (f : X ⟶ Y) :
    IsIso (Qh.map f) ↔ HomotopyCategory.quasiIso C _ f := by
  constructor
  · intro hf
    rw [HomotopyCategory.mem_quasiIso_iff]
    intro n
    rw [← NatIso.isIso_map_iff (homologyFunctorFactorsh C n) f]
    dsimp
    infer_instance
  · exact Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _

/--
lemma `isIso_iff` / 引理 `isIso_iff`

English:
lemma isIso_iff
  given: {K L : DerivedCategory C} (f : K ⟶ L)
  proof: by
  refine ⟨fun hf n => inferInstance, fun hf => ?_⟩
  refine ((MorphismProperty.isomorphisms (DerivedCategory C)).arrow_iso_iff
    (Qh.mapArrow.objObjPreimageIso (Arrow.mk f))).1 ?_
  let g := Qh.mapArrow.objPreimage (Arrow.mk f)
  change IsIso (Qh.map g.hom)
  rw [isIso_Qh_map_iff]; rw [Homotopy

中文:
引理 isIso_iff
  条件: {K L : 导出范畴 C} (f : K ⟶ L)
  证明: by
  refine ⟨fun hf n => inferInstance, fun hf => ?_⟩
  refine ((MorphismProperty.isomorphisms (DerivedCategory C)).arrow_iso_iff
    (Qh.mapArrow.objObjPreimageIso (Arrow.mk f))).1 ?_
  let g := Qh.mapArrow.objPreimage (Arrow.mk f)
  change IsIso (Qh.map g.hom)
  rw [isIso_Qh_map_iff]; rw [Homotopy

Depends on / 依赖: Arrow.mk, DerivedCategory, HomotopyCategory, HomotopyCategory.homologyFunctor, HomotopyCategory.mem_quasiIso_iff, MorphismProperty, MorphismProperty.isomorphisms, Qh.map, Qh.mapArrow.objObjPreim, Qh.mapArrow.objObjPreimageIso, Qh.mapArrow.objPreimage, arrow_iso_iff, g.hom, homologyFunctor, isIso_Qh_map_iff, isomorphisms, mapArrow, mapArrow.mapIso, mapIso, mem_quasiIso_iff
-/
lemma isIso_iff {K L : DerivedCategory C} (f : K ⟶ L) :
    IsIso f ↔ forall (n : Int), IsIso ((homologyFunctor C n).map f) := by
  refine ⟨fun hf n => inferInstance, fun hf => ?_⟩
  refine ((MorphismProperty.isomorphisms (DerivedCategory C)).arrow_iso_iff
    (Qh.mapArrow.objObjPreimageIso (Arrow.mk f))).1 ?_
  let g := Qh.mapArrow.objPreimage (Arrow.mk f)
  change IsIso (Qh.map g.hom)
  rw [isIso_Qh_map_iff]; rw [HomotopyCategory.mem_quasiIso_iff]
  intro n
  have e : Arrow.mk ((homologyFunctor C n).map f) ≅
      Arrow.mk ((HomotopyCategory.homologyFunctor _ _ n).map g.hom) :=
    ((homologyFunctor C n).mapArrow.mapIso
      ((Qh.mapArrow.objObjPreimageIso (Arrow.mk f)).symm)) ≪≫
      ((Functor.mapArrowFunctor _ _).mapIso (homologyFunctorFactorsh C n)).app (Arrow.mk g.hom)
  exact ((MorphismProperty.isomorphisms C).arrow_iso_iff e).1 (hf n)

instance (n : Int) : (homologyFunctor C n).IsHomological :=
  Functor.isHomological_of_localization Qh
    (homologyFunctor C n) _ (homologyFunctorFactorsh C n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (homologyFunctor C 0).ShiftSequence Int
  body: Functor.ShiftSequence.induced (homologyFunctorFactorsh C 0) Int
    (homologyFunctor C) (homologyFunctorFactorsh C)

中文:
实例 :
  签名: (homologyFunctor C 0).ShiftSequence 整数
  定义体: Functor.ShiftSequence.induced (homologyFunctorFactorsh C 0) Int
    (homologyFunctor C) (homologyFunctorFactorsh C)

Depends on / 依赖: Functor, Functor.ShiftSequence.induced, ShiftSequence, homologyFunctor, homologyFunctorFactorsh, induced
-/
noncomputable instance : (homologyFunctor C 0).ShiftSequence Int :=
  Functor.ShiftSequence.induced (homologyFunctorFactorsh C 0) Int
    (homologyFunctor C) (homologyFunctorFactorsh C)

/--
lemma `shift_homologyFunctor` / 引理 `shift_homologyFunctor`

English:
lemma shift_homologyFunctor
  given: (n : Int)
  proof: rfl

中文:
引理 shift_homologyFunctor
  条件: (n : 整数)
  证明: rfl

Depends on / 依赖: isZero_extend_X
-/
lemma shift_homologyFunctor (n : Int) :
    (homologyFunctor C 0).shift n = homologyFunctor C n := rfl

variable {C}

@[reassoc]
/--
lemma `shiftMap_homologyFunctor_map_Qh` / 引理 `shiftMap_homologyFunctor_map_Qh`

English:
lemma shiftMap_homologyFunctor_map_Qh
  proof: Functor.ShiftSequence.induced_shiftMap ..

中文:
引理 shiftMap_homologyFunctor_map_Qh
  证明: Functor.ShiftSequence.induced_shiftMap ..

Depends on / 依赖: Functor, Functor.ShiftSequence.induced_shiftMap, HomotopyCategory, HomotopyCategory.homologyFunctor, ShiftSequence, ShiftedHom, ShiftedHom.map, hom.app, homologyFunctor, homologyFunctorFactorsh, induced_shiftMap, inv.app, isZero_extend_X, shiftMap
-/
lemma shiftMap_homologyFunctor_map_Qh
    {K L : HomotopyCategory C (.up Int)} {n : Int} (f : K ⟶ L⟦n⟧)
    (a a' : Int) (h : n + a = a' := by lia) :
    (homologyFunctor C 0).shiftMap (ShiftedHom.map f Qh) a a' h =
    (homologyFunctorFactorsh C a).hom.app _ ≫
      (HomotopyCategory.homologyFunctor C (.up Int) 0).shiftMap f a a' h ≫
        (homologyFunctorFactorsh C a').inv.app _ :=
  Functor.ShiftSequence.induced_shiftMap ..

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `shiftMap_homologyFunctor_map_Q` / 引理 `shiftMap_homologyFunctor_map_Q`

English:
lemma shiftMap_homologyFunctor_map_Q
  proof: by
  rw [← ShiftedHom.map_naturality_1 f (quotientCompQhIso C)]; rw [ShiftedHom.mk₀_comp]; rw [ShiftedHom.comp_mk₀]; rw [Functor.shiftMap_comp']; rw [Functor.shiftMap_comp]; rw [ShiftedHom.comp_map]; rw [shiftMap_homologyFunctor_map_Qh ..]; rw [homologyFunctorFactorsh_hom_app_quotient_obj]; rw [homo

中文:
引理 shiftMap_homologyFunctor_map_Q
  证明: by
  rw [← ShiftedHom.map_naturality_1 f (quotientCompQhIso C)]; rw [ShiftedHom.mk₀_comp]; rw [ShiftedHom.comp_mk₀]; rw [Functor.shiftMap_comp']; rw [Functor.shiftMap_comp]; rw [ShiftedHom.comp_map]; rw [shiftMap_homologyFunctor_map_Qh ..]; rw [homologyFunctorFactorsh_hom_app_quotient_obj]; rw [homo

Depends on / 依赖: Functor, Functor.shiftMap_comp, HomologicalComplex, HomologicalComplex.homologyFunctor, ShiftedHom, ShiftedHom.comp_map, ShiftedHom.comp_mk, ShiftedHom.map, ShiftedHom.map_naturality_1, ShiftedHom.mk, comp_map, hom.app, homologyFunctor, homologyFunctorFactors, homologyFunctorFactorsh_hom_app, inv.app, map_naturality_1, quotientCompQhIso, shiftMap, shiftMap_comp
-/
lemma shiftMap_homologyFunctor_map_Q
    {K L : CochainComplex C Int} {n : Int} (f : K ⟶ L⟦n⟧)
    (a a' : Int) (h : n + a = a' := by lia) :
    (homologyFunctor C 0).shiftMap (ShiftedHom.map f Q) a a' h =
    (homologyFunctorFactors C a).hom.app _ ≫
      (HomologicalComplex.homologyFunctor C (.up Int) 0).shiftMap f a a' h ≫
        (homologyFunctorFactors C a').inv.app _ := by
  rw [← ShiftedHom.map_naturality_1 f (quotientCompQhIso C)]; rw [ShiftedHom.mk₀_comp]; rw [ShiftedHom.comp_mk₀]; rw [Functor.shiftMap_comp']; rw [Functor.shiftMap_comp]; rw [ShiftedHom.comp_map]; rw [shiftMap_homologyFunctor_map_Qh ..]; rw [homologyFunctorFactorsh_hom_app_quotient_obj]; rw [homologyFunctorFactorsh_inv_app_quotient_obj]; rw [HomotopyCategory.homologyFunctor_shiftMap]
  simp [shift_homologyFunctor, ← Functor.map_comp, ← Functor.map_comp_assoc]

namespace HomologySequence

/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: (T : Triangle (DerivedCategory C))
  body: (homologyFunctor C 0).shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

中文:
定义 δ
  签名: (T : Triangle (导出范畴 C))
  定义体: (homologyFunctor C 0).shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

Depends on / 依赖: T.mor, T.obj, add_comm, homologyFunctor, isStrictlyGE_iff, isZero_single_obj_X, shiftMap
-/
noncomputable def δ (T : Triangle (DerivedCategory C))
    (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia) :
    (homologyFunctor C n₀).obj T.obj₃ ⟶ (homologyFunctor C n₁).obj T.obj₁ :=
  (homologyFunctor C 0).shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

variable (T : Triangle (DerivedCategory C)) (hT : T in distTriang _) (n₀ n₁ : Int)

include hT

@[reassoc (attr := simp)]
/--
lemma `comp_δ` / 引理 `comp_δ`

English:
lemma comp_δ
  given: (h : n₀ + 1 = n₁ := by lia)
  proof: (homologyFunctor C 0).comp_homologySequenceδ _ hT _ _ h

@[reassoc (attr := simp)]

中文:
引理 comp_δ
  条件: (h : n₀ + 1 = n₁ := by lia)
  证明: (homologyFunctor C 0).comp_homologySequenceδ _ hT _ _ h

@[reassoc (attr := simp)]

Depends on / 依赖: T.mor, homologyFunctor, isStrictlyLE_iff, isZero_single_obj_X
-/
lemma comp_δ (h : n₀ + 1 = n₁ := by lia) :
    (homologyFunctor C n₀).map T.mor₂ ≫ δ T n₀ n₁ h = 0 :=
  (homologyFunctor C 0).comp_homologySequenceδ _ hT _ _ h

@[reassoc (attr := simp)]
/--
lemma `δ_comp` / 引理 `δ_comp`

English:
lemma δ_comp
  given: (h : n₀ + 1 = n₁ := by lia)
  proof: (homologyFunctor C 0).homologySequenceδ_comp _ hT _ _ h

中文:
引理 δ_comp
  条件: (h : n₀ + 1 = n₁ := by lia)
  证明: (homologyFunctor C 0).homologySequenceδ_comp _ hT _ _ h

Depends on / 依赖: T.mor, homologyFunctor
-/
lemma δ_comp (h : n₀ + 1 = n₁ := by lia) :
    δ T n₀ n₁ h ≫ (homologyFunctor C n₁).map T.mor₁ = 0 :=
  (homologyFunctor C 0).homologySequenceδ_comp _ hT _ _ h

/--
lemma `exact₂` / 引理 `exact₂`

English:
lemma exact₂
  proof: (homologyFunctor C 0).homologySequence_exact₂ _ hT _

中文:
引理 exact₂
  证明: (homologyFunctor C 0).homologySequence_exact₂ _ hT _

Depends on / 依赖: homologyFunctor
-/
lemma exact₂ :
    (ShortComplex.mk ((homologyFunctor C n₀).map T.mor₁) ((homologyFunctor C n₀).map T.mor₂)
      (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT,
        Functor.map_zero])).Exact :=
  (homologyFunctor C 0).homologySequence_exact₂ _ hT _

/--
lemma `exact₃` / 引理 `exact₃`

English:
lemma exact₃
  given: (h : n₀ + 1 = n₁ := by lia)
  proof: (homologyFunctor C 0).homologySequence_exact₃ _ hT _ _ h

中文:
引理 exact₃
  条件: (h : n₀ + 1 = n₁ := by lia)
  证明: (homologyFunctor C 0).homologySequence_exact₃ _ hT _ _ h

Depends on / 依赖: ShortComplex, ShortComplex.mk, homologyFunctor
-/
lemma exact₃ (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (comp_δ T hT n₀ n₁ h)).Exact :=
  (homologyFunctor C 0).homologySequence_exact₃ _ hT _ _ h

/--
lemma `exact₁` / 引理 `exact₁`

English:
lemma exact₁
  given: (h : n₀ + 1 = n₁ := by lia)
  proof: (homologyFunctor C 0).homologySequence_exact₁ _ hT _ _ h

中文:
引理 exact₁
  条件: (h : n₀ + 1 = n₁ := by lia)
  证明: (homologyFunctor C 0).homologySequence_exact₁ _ hT _ _ h

Depends on / 依赖: ShortComplex, ShortComplex.mk, homologyFunctor
-/
lemma exact₁ (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (δ_comp T hT n₀ n₁ h)).Exact :=
  (homologyFunctor C 0).homologySequence_exact₁ _ hT _ _ h

/--
lemma `epi_homologyMap_mor₁_iff` / 引理 `epi_homologyMap_mor₁_iff`

English:
lemma epi_homologyMap_mor₁_iff
  proof: (homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT _

中文:
引理 epi_homologyMap_mor₁_iff
  证明: (homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT _

Depends on / 依赖: homologyFunctor
-/
lemma epi_homologyMap_mor₁_iff :
    Epi ((homologyFunctor C n₀).map T.mor₁) ↔ (homologyFunctor C n₀).map T.mor₂ = 0 :=
  (homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT _

/--
lemma `mono_homologyMap_mor₁_iff` / 引理 `mono_homologyMap_mor₁_iff`

English:
lemma mono_homologyMap_mor₁_iff
  given: (h : n₀ + 1 = n₁ := by lia)
  proof: (homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT _ _ h

中文:
引理 mono_homologyMap_mor₁_iff
  条件: (h : n₀ + 1 = n₁ := by lia)
  证明: (homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT _ _ h

Depends on / 依赖: T.mor, homologyFunctor
-/
lemma mono_homologyMap_mor₁_iff (h : n₀ + 1 = n₁ := by lia) :
    Mono ((homologyFunctor C n₁).map T.mor₁) ↔ δ T n₀ n₁ h = 0 :=
  (homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT _ _ h

/--
lemma `epi_homologyMap_mor₂_iff` / 引理 `epi_homologyMap_mor₂_iff`

English:
lemma epi_homologyMap_mor₂_iff
  given: (h : n₀ + 1 = n₁ := by lia)
  proof: (homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT _ _ h

中文:
引理 epi_homologyMap_mor₂_iff
  条件: (h : n₀ + 1 = n₁ := by lia)
  证明: (homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT _ _ h

Depends on / 依赖: T.mor, homologyFunctor
-/
lemma epi_homologyMap_mor₂_iff (h : n₀ + 1 = n₁ := by lia) :
    Epi ((homologyFunctor C n₀).map T.mor₂) ↔ δ T n₀ n₁ h = 0 :=
  (homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT _ _ h

/--
lemma `mono_homologyMap_mor₂_iff` / 引理 `mono_homologyMap_mor₂_iff`

English:
lemma mono_homologyMap_mor₂_iff
  proof: (homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _ hT n₀

中文:
引理 mono_homologyMap_mor₂_iff
  证明: (homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _ hT n₀

Depends on / 依赖: homologyFunctor
-/
lemma mono_homologyMap_mor₂_iff :
    Mono ((homologyFunctor C n₀).map T.mor₂) ↔ (homologyFunctor C n₀).map T.mor₁ = 0 :=
  (homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _ hT n₀

end HomologySequence

end DerivedCategory

namespace CochainComplex

open HomologicalComplex

variable {C} (T : Triangle (CochainComplex C Int))

/--
Definition of `homologyδOfTriangle` / `homologyδOfTriangle` 的定义

English:
definition homologyδOfTriangle
  signature: (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia)
  body: homologyMap T.mor₃ n₀ ≫
    ((homologyFunctor C (.up Int) 0).shiftIso 1 n₀ n₁ (by lia)).hom.app _

中文:
定义 homologyδOfTriangle
  签名: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁ := by lia)
  定义体: homologyMap T.mor₃ n₀ ≫
    ((homologyFunctor C (.up Int) 0).shiftIso 1 n₀ n₁ (by lia)).hom.app _

Depends on / 依赖: T.mor, T.obj, hom.app, homology, homologyFunctor, homologyMap, shiftIso
-/
noncomputable def homologyδOfTriangle (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia) :
    T.obj₃.homology n₀ ⟶ T.obj₁.homology n₁ :=
  homologyMap T.mor₃ n₀ ≫
    ((homologyFunctor C (.up Int) 0).shiftIso 1 n₀ n₁ (by lia)).hom.app _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `homologyFunctorFactors_hom_app_homologyδOfTriangle` / 引理 `homologyFunctorFactors_hom_app_homologyδOfTriangle`

English:
lemma homologyFunctorFactors_hom_app_homologyδOfTriangle
  proof: by
  dsimp [DerivedCategory.HomologySequence.δ]
  rw [dsimp% [ShiftedHom.map]
      DerivedCategory.shiftMap_homologyFunctor_map_Q T.mor₃ n₀ n₁ (by lia)]
  simp [Functor.shiftMap, homologyFunctor_shift, homologyδOfTriangle]

中文:
引理 homologyFunctorFactors_hom_app_homologyδOfTriangle
  证明: by
  dsimp [DerivedCategory.HomologySequence.δ]
  rw [dsimp% [ShiftedHom.map]
      DerivedCategory.shiftMap_homologyFunctor_map_Q T.mor₃ n₀ n₁ (by lia)]
  simp [Functor.shiftMap, homologyFunctor_shift, homologyδOfTriangle]

Depends on / 依赖: DerivedCategory, DerivedCategory.HomologySequence, DerivedCategory.Q.mapTriangle.obj, DerivedCategory.homologyFunctorFactors, DerivedCategory.shiftMap_homologyFunctor_map_Q, Functor, Functor.shiftMap, HomologySequence, ShiftedHom, ShiftedHom.map, T.mor, T.obj, hom.app, homologyFunctorFactors, homologyFunctor_shift, mapTriangle, shiftMap, shiftMap_homologyFunctor_map_Q
-/
lemma homologyFunctorFactors_hom_app_homologyδOfTriangle
    (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia) :
    (DerivedCategory.homologyFunctorFactors C n₀).hom.app T.obj₃ ≫
      homologyδOfTriangle T n₀ n₁ h =
    DerivedCategory.HomologySequence.δ
      (DerivedCategory.Q.mapTriangle.obj T) n₀ n₁ h ≫
        (DerivedCategory.homologyFunctorFactors C n₁).hom.app T.obj₁ := by
  dsimp [DerivedCategory.HomologySequence.δ]
  rw [dsimp% [ShiftedHom.map]
      DerivedCategory.shiftMap_homologyFunctor_map_Q T.mor₃ n₀ n₁ (by lia)]
  simp [Functor.shiftMap, homologyFunctor_shift, homologyδOfTriangle]

variable (hT : DerivedCategory.Q.mapTriangle.obj T in distTriang _)

include hT

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `homologyMap_comp_eq_zero_of_distTriang` / 引理 `homologyMap_comp_eq_zero_of_distTriang`

English:
lemma homologyMap_comp_eq_zero_of_distTriang
  given: (n : Int)
  proof: by
  rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _)]; rw [← DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]; rw [← DerivedCategory.homologyFunctorFactors_hom_naturality]; rw [← Functor.map_comp_assoc]; rw [dsimp% comp_distTriang_mor_zero₁₂ _ hT]; rw [Functor.m

中文:
引理 homologyMap_comp_eq_zero_of_distTriang
  条件: (n : 整数)
  证明: by
  rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _)]; rw [← DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]; rw [← DerivedCategory.homologyFunctorFactors_hom_naturality]; rw [← Functor.map_comp_assoc]; rw [dsimp% comp_distTriang_mor_zero₁₂ _ hT]; rw [Functor.m

Depends on / 依赖: DerivedCategory, DerivedCategory.homologyFunctorFactors, DerivedCategory.homologyFunctorFactors_hom_naturality, DerivedCategory.homologyFunctorFactors_hom_naturality_assoc, Functor, Functor.map_comp_assoc, Functor.map_zero, Limits, Limits.comp_zero, Limits.zero_comp, cancel_epi, comp_zero, hom.app, homologyFunctorFactors, homologyFunctorFactors_hom_naturality, homologyFunctorFactors_hom_naturality_assoc, map_comp_assoc, map_zero, zero_comp
-/
lemma homologyMap_comp_eq_zero_of_distTriang (n : Int) :
    homologyMap T.mor₁ n ≫ homologyMap T.mor₂ n = 0 := by
  rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _)]; rw [← DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]; rw [← DerivedCategory.homologyFunctorFactors_hom_naturality]; rw [← Functor.map_comp_assoc]; rw [dsimp% comp_distTriang_mor_zero₁₂ _ hT]; rw [Functor.map_zero]; rw [Limits.zero_comp]; rw [Limits.comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `homologyδOfTriangle_homologyMap` / 引理 `homologyδOfTriangle_homologyMap`

English:
lemma homologyδOfTriangle_homologyMap
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia)
  proof: by
  rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _)]; rw [homologyFunctorFactors_hom_app_homologyδOfTriangle_assoc ..]; rw [← DerivedCategory.homologyFunctorFactors_hom_naturality]
  dsimp
  rw [reassoc_of% dsimp% DerivedCategory.HomologySequence.δ_comp _ hT n₀ n₁ h]
  sim

中文:
引理 homologyδOfTriangle_homologyMap
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁ := by lia)
  证明: by
  rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _)]; rw [homologyFunctorFactors_hom_app_homologyδOfTriangle_assoc ..]; rw [← DerivedCategory.homologyFunctorFactors_hom_naturality]
  dsimp
  rw [reassoc_of% dsimp% DerivedCategory.HomologySequence.δ_comp _ hT n₀ n₁ h]
  sim

Depends on / 依赖: DerivedCategory, DerivedCategory.HomologySequence, DerivedCategory.homologyFunctorFactors, DerivedCategory.homologyFunctorFactors_hom_naturality, HomologySequence, T.mor, cancel_epi, hom.app, homologyFunctorFactors, homologyFunctorFactors_hom_naturality, homologyMap, reassoc_of
-/
lemma homologyδOfTriangle_homologyMap (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia) :
    homologyδOfTriangle T n₀ n₁ h ≫ homologyMap T.mor₁ n₁ = 0 := by
  rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _)]; rw [homologyFunctorFactors_hom_app_homologyδOfTriangle_assoc ..]; rw [← DerivedCategory.homologyFunctorFactors_hom_naturality]
  dsimp
  rw [reassoc_of% dsimp% DerivedCategory.HomologySequence.δ_comp _ hT n₀ n₁ h]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `homologyMap_homologyδOfTriangle` / 引理 `homologyMap_homologyδOfTriangle`

English:
lemma homologyMap_homologyδOfTriangle
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia)
  proof: by
  simp [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _),
    ← DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
    reassoc_of% dsimp% DerivedCategory.HomologySequence.comp_δ _ hT n₀ n₁ h]

中文:
引理 homologyMap_homologyδOfTriangle
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁ := by lia)
  证明: by
  simp [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _),
    ← DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
    reassoc_of% dsimp% DerivedCategory.HomologySequence.comp_δ _ hT n₀ n₁ h]

Depends on / 依赖: DerivedCategory, DerivedCategory.HomologySequence.comp_, DerivedCategory.homologyFunctorFactors, DerivedCategory.homologyFunctorFactors_hom_naturality_assoc, HomologySequence, T.mor, cancel_epi, hom.app, homologyFunctorFactors, homologyFunctorFactors_hom_naturality_assoc, homologyMap, reassoc_of
-/
lemma homologyMap_homologyδOfTriangle (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia) :
    homologyMap T.mor₂ n₀ ≫ homologyδOfTriangle T n₀ n₁ h = 0 := by
  simp [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _),
    ← DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
    reassoc_of% dsimp% DerivedCategory.HomologySequence.comp_δ _ hT n₀ n₁ h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `homologyMap_exact₁_of_distTriang` / 引理 `homologyMap_exact₁_of_distTriang`

English:
lemma homologyMap_exact₁_of_distTriang
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia)
  proof: by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₁ _ hT n₀ n₁ h)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

中文:
引理 homologyMap_exact₁_of_distTriang
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁ := by lia)
  证明: by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₁ _ hT n₀ n₁ h)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

Depends on / 依赖: DerivedCategory, DerivedCategory.HomologySequence.exact, DerivedCategory.homologyFunctorFactors, HomologySequence, ShortComplex, ShortComplex.exact_of_iso, ShortComplex.isoMk, ShortComplex.mk, exact_of_iso, homologyFunctorFactors
-/
lemma homologyMap_exact₁_of_distTriang (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (homologyδOfTriangle_homologyMap T hT n₀ n₁ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₁ _ hT n₀ n₁ h)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `homologyMap_exact₂_of_distTriang` / 引理 `homologyMap_exact₂_of_distTriang`

English:
lemma homologyMap_exact₂_of_distTriang
  given: (n : Int)
  proof: by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₂ _ hT n)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

中文:
引理 homologyMap_exact₂_of_distTriang
  条件: (n : 整数)
  证明: by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₂ _ hT n)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

Depends on / 依赖: DerivedCategory, DerivedCategory.HomologySequence.exact, DerivedCategory.homologyFunctorFactors, HomologySequence, ShortComplex, ShortComplex.exact_of_iso, ShortComplex.isoMk, exact_of_iso, homologyFunctorFactors
-/
lemma homologyMap_exact₂_of_distTriang (n : Int) :
    (ShortComplex.mk _ _ (homologyMap_comp_eq_zero_of_distTriang T hT n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₂ _ hT n)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `homologyMap_exact₃_of_distTriang` / 引理 `homologyMap_exact₃_of_distTriang`

English:
lemma homologyMap_exact₃_of_distTriang
  given: (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia)
  proof: by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₃ _ hT n₀ n₁ h)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

中文:
引理 homologyMap_exact₃_of_distTriang
  条件: (n₀ n₁ : 整数) (h : n₀ + 1 = n₁ := by lia)
  证明: by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₃ _ hT n₀ n₁ h)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

Depends on / 依赖: DerivedCategory, DerivedCategory.HomologySequence.exact, DerivedCategory.homologyFunctorFactors, HomologySequence, ShortComplex, ShortComplex.exact_of_iso, ShortComplex.isoMk, ShortComplex.mk, exact_of_iso, homologyFunctorFactors
-/
lemma homologyMap_exact₃_of_distTriang (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (homologyMap_homologyδOfTriangle T hT n₀ n₁ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₃ _ hT n₀ n₁ h)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)

end CochainComplex
