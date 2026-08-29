/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
/-!
# The homology of single complexes

The main definition in this file is `HomologicalComplex.homologyFunctorSingleIso`
which is a natural isomorphism `single C c j ⋙ homologyFunctor C c j ≅ 𝟭 C`.

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

namespace HomologicalComplex

variable (A : C)

instance (i : ι) : ((single C c j).obj A).HasHomology i := by
  apply ShortComplex.hasHomology_of_zeros

/--
lemma `exactAt_single_obj` / 引理 `exactAt_single_obj`

English:
lemma exactAt_single_obj
  given: (A : C) (i : ι) (hi : i != j)
  proof: ShortComplex.exact_of_isZero_X₂ _ (isZero_single_obj_X c _ _ _ hi)

中文:
引理 exactAt_single_obj
  条件: (A : C) (i : ι) (hi : i != j)
  证明: ShortComplex.exact_of_isZero_X₂ _ (isZero_single_obj_X c _ _ _ hi)

Depends on / 依赖: ShortComplex, ShortComplex.exact_of_isZero_X, isZero_single_obj_X
-/
lemma exactAt_single_obj (A : C) (i : ι) (hi : i != j) :
    ExactAt ((single C c j).obj A) i :=
  ShortComplex.exact_of_isZero_X₂ _ (isZero_single_obj_X c _ _ _ hi)

/--
lemma `isZero_single_obj_homology` / 引理 `isZero_single_obj_homology`

English:
lemma isZero_single_obj_homology
  given: (A : C) (i : ι) (hi : i != j)
  proof: by
  simpa only [← exactAt_iff_isZero_homology]
    using exactAt_single_obj c j A i hi

中文:
引理 isZero_single_obj_homology
  条件: (A : C) (i : ι) (hi : i != j)
  证明: by
  simpa only [← exactAt_iff_isZero_homology]
    using exactAt_single_obj c j A i hi

Depends on / 依赖: exactAt_iff_isZero_homology, exactAt_single_obj
-/
lemma isZero_single_obj_homology (A : C) (i : ι) (hi : i != j) :
    IsZero (((single C c j).obj A).homology i) := by
  simpa only [← exactAt_iff_isZero_homology]
    using exactAt_single_obj c j A i hi

/--
Definition of `singleObjCyclesSelfIso` / `singleObjCyclesSelfIso` 的定义

English:
definition singleObjCyclesSelfIso
  signature: :
  body: ((single C c j).obj A).iCyclesIso j _ rfl rfl ≪≫ singleObjXSelf c j A

@[reassoc]

中文:
定义 singleObjCyclesSelfIso
  签名: :
  定义体: ((single C c j).obj A).iCyclesIso j _ rfl rfl ≪≫ singleObjXSelf c j A

@[reassoc]

Depends on / 依赖: iCyclesIso, single, singleObjXSelf
-/
noncomputable def singleObjCyclesSelfIso :
    ((single C c j).obj A).cycles j ≅ A :=
  ((single C c j).obj A).iCyclesIso j _ rfl rfl ≪≫ singleObjXSelf c j A

@[reassoc]
/--
lemma `singleObjCyclesSelfIso_hom` / 引理 `singleObjCyclesSelfIso_hom`

English:
lemma singleObjCyclesSelfIso_hom
  proof: rfl

中文:
引理 singleObjCyclesSelfIso_hom
  证明: rfl
-/
lemma singleObjCyclesSelfIso_hom :
    (singleObjCyclesSelfIso c j A).hom =
      ((single C c j).obj A).iCycles j ≫ (singleObjXSelf c j A).hom := rfl

/--
Definition of `singleObjOpcyclesSelfIso` / `singleObjOpcyclesSelfIso` 的定义

English:
definition singleObjOpcyclesSelfIso
  signature: :
  body: (singleObjXSelf c j A).symm ≪≫ ((single C c j).obj A).pOpcyclesIso _ j rfl rfl

@[reassoc]

中文:
定义 singleObjOpcyclesSelfIso
  签名: :
  定义体: (singleObjXSelf c j A).symm ≪≫ ((single C c j).obj A).pOpcyclesIso _ j rfl rfl

@[reassoc]

Depends on / 依赖: pOpcyclesIso, single, singleObjXSelf
-/
noncomputable def singleObjOpcyclesSelfIso :
    A ≅ ((single C c j).obj A).opcycles j :=
  (singleObjXSelf c j A).symm ≪≫ ((single C c j).obj A).pOpcyclesIso _ j rfl rfl

@[reassoc]
/--
lemma `singleObjOpcyclesSelfIso_hom` / 引理 `singleObjOpcyclesSelfIso_hom`

English:
lemma singleObjOpcyclesSelfIso_hom
  proof: rfl

中文:
引理 singleObjOpcyclesSelfIso_hom
  证明: rfl
-/
lemma singleObjOpcyclesSelfIso_hom :
    (singleObjOpcyclesSelfIso c j A).hom =
      (singleObjXSelf c j A).inv ≫ ((single C c j).obj A).pOpcycles j := rfl

/--
Definition of `singleObjHomologySelfIso` / `singleObjHomologySelfIso` 的定义

English:
definition singleObjHomologySelfIso
  signature: :
  body: (((single C c j).obj A).isoHomologyπ _ j rfl rfl).symm ≪≫ singleObjCyclesSelfIso c j A

中文:
定义 singleObjHomologySelfIso
  签名: :
  定义体: (((single C c j).obj A).isoHomologyπ _ j rfl rfl).symm ≪≫ singleObjCyclesSelfIso c j A

Depends on / 依赖: single, singleObjCyclesSelfIso
-/
noncomputable def singleObjHomologySelfIso :
    ((single C c j).obj A).homology j ≅ A :=
  (((single C c j).obj A).isoHomologyπ _ j rfl rfl).symm ≪≫ singleObjCyclesSelfIso c j A

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `singleObjCyclesSelfIso_inv_iCycles` / 引理 `singleObjCyclesSelfIso_inv_iCycles`

English:
lemma singleObjCyclesSelfIso_inv_iCycles
  proof: by
  simp [singleObjCyclesSelfIso]

中文:
引理 singleObjCyclesSelfIso_inv_iCycles
  证明: by
  simp [singleObjCyclesSelfIso]

Depends on / 依赖: singleObjCyclesSelfIso
-/
lemma singleObjCyclesSelfIso_inv_iCycles :
    (singleObjCyclesSelfIso _ _ _).inv ≫ ((single C c j).obj A).iCycles j =
      (singleObjXSelf c j A).inv := by
  simp [singleObjCyclesSelfIso]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `homologyπ_singleObjHomologySelfIso_hom` / 引理 `homologyπ_singleObjHomologySelfIso_hom`

English:
lemma homologyπ_singleObjHomologySelfIso_hom
  proof: by
  simp [singleObjCyclesSelfIso, singleObjHomologySelfIso]

@[reassoc (attr := simp)]

中文:
引理 homologyπ_singleObjHomologySelfIso_hom
  证明: by
  simp [singleObjCyclesSelfIso, singleObjHomologySelfIso]

@[reassoc (attr := simp)]

Depends on / 依赖: singleObjCyclesSelfIso, singleObjHomologySelfIso
-/
lemma homologyπ_singleObjHomologySelfIso_hom :
    ((single C c j).obj A).homologyπ j ≫ (singleObjHomologySelfIso _ _ _).hom =
      (singleObjCyclesSelfIso _ _ _).hom := by
  simp [singleObjCyclesSelfIso, singleObjHomologySelfIso]

@[reassoc (attr := simp)]
/--
lemma `singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv` / 引理 `singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv`

English:
lemma singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv
  proof: by
  simp only [← cancel_mono (singleObjHomologySelfIso _ _ _).hom, assoc,
    Iso.inv_hom_id, comp_id, homologyπ_singleObjHomologySelfIso_hom]

中文:
引理 singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv
  证明: by
  simp only [← cancel_mono (singleObjHomologySelfIso _ _ _).hom, assoc,
    Iso.inv_hom_id, comp_id, homologyπ_singleObjHomologySelfIso_hom]

Depends on / 依赖: Iso.inv_hom_id, cancel_mono, comp_id, inv_hom_id, singleObjHomologySelfIso
-/
lemma singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv :
    (singleObjCyclesSelfIso c j A).hom ≫ (singleObjHomologySelfIso c j A).inv =
      ((single C c j).obj A).homologyπ j := by
  simp only [← cancel_mono (singleObjHomologySelfIso _ _ _).hom, assoc,
    Iso.inv_hom_id, comp_id, homologyπ_singleObjHomologySelfIso_hom]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom` / 引理 `singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom`

English:
lemma singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom
  proof: by
  simp [singleObjCyclesSelfIso, singleObjOpcyclesSelfIso]

中文:
引理 singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom
  证明: by
  simp [singleObjCyclesSelfIso, singleObjOpcyclesSelfIso]

Depends on / 依赖: singleObjCyclesSelfIso, singleObjOpcyclesSelfIso
-/
lemma singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom :
    (singleObjCyclesSelfIso c j A).hom ≫ (singleObjOpcyclesSelfIso c j A).hom =
      ((single C c j).obj A).iCycles j ≫ ((single C c j).obj A).pOpcycles j := by
  simp [singleObjCyclesSelfIso, singleObjOpcyclesSelfIso]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `singleObjCyclesSelfIso_inv_homologyπ` / 引理 `singleObjCyclesSelfIso_inv_homologyπ`

English:
lemma singleObjCyclesSelfIso_inv_homologyπ
  proof: by
  simp [singleObjCyclesSelfIso, singleObjHomologySelfIso]

@[reassoc (attr := simp)]

中文:
引理 singleObjCyclesSelfIso_inv_homologyπ
  证明: by
  simp [singleObjCyclesSelfIso, singleObjHomologySelfIso]

@[reassoc (attr := simp)]

Depends on / 依赖: singleObjCyclesSelfIso, singleObjHomologySelfIso
-/
lemma singleObjCyclesSelfIso_inv_homologyπ :
    (singleObjCyclesSelfIso _ _ _).inv ≫ ((single C c j).obj A).homologyπ j =
      (singleObjHomologySelfIso _ _ _).inv := by
  simp [singleObjCyclesSelfIso, singleObjHomologySelfIso]

@[reassoc (attr := simp)]
/--
lemma `singleObjHomologySelfIso_inv_homologyι` / 引理 `singleObjHomologySelfIso_inv_homologyι`

English:
lemma singleObjHomologySelfIso_inv_homologyι
  proof: by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom]; rw [singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv_assoc]; rw [homology_π_ι]; rw [singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom]

@[reassoc (attr := simp)]

中文:
引理 singleObjHomologySelfIso_inv_homologyι
  证明: by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom]; rw [singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv_assoc]; rw [homology_π_ι]; rw [singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi, singleObjCyclesSelfIso, singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom, singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv_assoc
-/
lemma singleObjHomologySelfIso_inv_homologyι :
    (singleObjHomologySelfIso _ _ _).inv ≫ ((single C c j).obj A).homologyι j =
      (singleObjOpcyclesSelfIso _ _ _).hom := by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom]; rw [singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv_assoc]; rw [homology_π_ι]; rw [singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom]

@[reassoc (attr := simp)]
/--
lemma `homologyι_singleObjOpcyclesSelfIso_inv` / 引理 `homologyι_singleObjOpcyclesSelfIso_inv`

English:
lemma homologyι_singleObjOpcyclesSelfIso_inv
  proof: by
  rw [← cancel_epi (singleObjHomologySelfIso _ _ _).inv]; rw [singleObjHomologySelfIso_inv_homologyι_assoc]; rw [Iso.hom_inv_id]; rw [Iso.inv_hom_id]

@[reassoc (attr := simp)]

中文:
引理 homologyι_singleObjOpcyclesSelfIso_inv
  证明: by
  rw [← cancel_epi (singleObjHomologySelfIso _ _ _).inv]; rw [singleObjHomologySelfIso_inv_homologyι_assoc]; rw [Iso.hom_inv_id]; rw [Iso.inv_hom_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, Iso.inv_hom_id, cancel_epi, hom_inv_id, inv_hom_id, singleObjHomologySelfIso
-/
lemma homologyι_singleObjOpcyclesSelfIso_inv :
    ((single C c j).obj A).homologyι j ≫ (singleObjOpcyclesSelfIso _ _ _).inv =
      (singleObjHomologySelfIso _ _ _).hom := by
  rw [← cancel_epi (singleObjHomologySelfIso _ _ _).inv]; rw [singleObjHomologySelfIso_inv_homologyι_assoc]; rw [Iso.hom_inv_id]; rw [Iso.inv_hom_id]

@[reassoc (attr := simp)]
/--
lemma `singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom` / 引理 `singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom`

English:
lemma singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom
  proof: by
  rw [← cancel_epi (singleObjHomologySelfIso _ _ _).inv]; rw [Iso.inv_hom_id_assoc]; rw [singleObjHomologySelfIso_inv_homologyι]

@[reassoc (attr := simp)]

中文:
引理 singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom
  证明: by
  rw [← cancel_epi (singleObjHomologySelfIso _ _ _).inv]; rw [Iso.inv_hom_id_assoc]; rw [singleObjHomologySelfIso_inv_homologyι]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_hom_id_assoc, cancel_epi, inv_hom_id_assoc, singleObjHomologySelfIso
-/
lemma singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom :
    (singleObjHomologySelfIso _ _ _).hom ≫ (singleObjOpcyclesSelfIso _ _ _).hom =
      ((single C c j).obj A).homologyι j := by
  rw [← cancel_epi (singleObjHomologySelfIso _ _ _).inv]; rw [Iso.inv_hom_id_assoc]; rw [singleObjHomologySelfIso_inv_homologyι]

@[reassoc (attr := simp)]
/--
lemma `pOpcycles_singleObjOpcyclesSelfIso_inv` / 引理 `pOpcycles_singleObjOpcyclesSelfIso_inv`

English:
lemma pOpcycles_singleObjOpcyclesSelfIso_inv
  proof: by
  have := ((single C c j).obj A).isIso_iCycles j _ rfl (by simp)
  rw [← cancel_epi (((single C c j).obj A).iCycles j)]; rw [← HomologicalComplex.homology_π_ι_assoc]; rw [homologyι_singleObjOpcyclesSelfIso_inv]; rw [homologyπ_singleObjHomologySelfIso_hom]; rw [singleObjCyclesSelfIso_hom]

中文:
引理 pOpcycles_singleObjOpcyclesSelfIso_inv
  证明: by
  have := ((single C c j).obj A).isIso_iCycles j _ rfl (by simp)
  rw [← cancel_epi (((single C c j).obj A).iCycles j)]; rw [← HomologicalComplex.homology_π_ι_assoc]; rw [homologyι_singleObjOpcyclesSelfIso_inv]; rw [homologyπ_singleObjHomologySelfIso_hom]; rw [singleObjCyclesSelfIso_hom]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homology_, cancel_epi, iCycles, isIso_iCycles, single, singleObjCyclesSelfIso_hom
-/
lemma pOpcycles_singleObjOpcyclesSelfIso_inv :
    ((single C c j).obj A).pOpcycles j ≫ (singleObjOpcyclesSelfIso _ _ _).inv =
      (singleObjXSelf c j A).hom := by
  have := ((single C c j).obj A).isIso_iCycles j _ rfl (by simp)
  rw [← cancel_epi (((single C c j).obj A).iCycles j)]; rw [← HomologicalComplex.homology_π_ι_assoc]; rw [homologyι_singleObjOpcyclesSelfIso_inv]; rw [homologyπ_singleObjHomologySelfIso_hom]; rw [singleObjCyclesSelfIso_hom]

variable {A}
variable {B : C} (f : A ⟶ B)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `singleObjCyclesSelfIso_hom_naturality` / 引理 `singleObjCyclesSelfIso_hom_naturality`

English:
lemma singleObjCyclesSelfIso_hom_naturality
  proof: by
  rw [← cancel_mono (singleObjCyclesSelfIso c j B).inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← cancel_mono (iCycles _ _)]
  simp only [cyclesMap_i, singleObjCyclesSelfIso, Iso.trans_hom, iCyclesIso_hom, Iso.trans_inv,
    assoc, iCyclesIso_inv_hom_id, comp_id, single_ma

中文:
引理 singleObjCyclesSelfIso_hom_naturality
  证明: by
  rw [← cancel_mono (singleObjCyclesSelfIso c j B).inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← cancel_mono (iCycles _ _)]
  simp only [cyclesMap_i, singleObjCyclesSelfIso, Iso.trans_hom, iCyclesIso_hom, Iso.trans_inv,
    assoc, iCyclesIso_inv_hom_id, comp_id, single_ma

Depends on / 依赖: Iso.hom_inv_id, Iso.trans_hom, Iso.trans_inv, cancel_mono, comp_id, cyclesMap_i, hom_inv_id, iCycles, iCyclesIso_hom, iCyclesIso_inv_hom_id, singleObjCyclesSelfIso, single_map_f_self, trans_hom, trans_inv
-/
lemma singleObjCyclesSelfIso_hom_naturality :
    cyclesMap ((single C c j).map f) j ≫ (singleObjCyclesSelfIso c j B).hom =
      (singleObjCyclesSelfIso c j A).hom ≫ f := by
  rw [← cancel_mono (singleObjCyclesSelfIso c j B).inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [← cancel_mono (iCycles _ _)]
  simp only [cyclesMap_i, singleObjCyclesSelfIso, Iso.trans_hom, iCyclesIso_hom, Iso.trans_inv,
    assoc, iCyclesIso_inv_hom_id, comp_id, single_map_f_self]

@[reassoc (attr := simp)]
/--
lemma `singleObjCyclesSelfIso_inv_naturality` / 引理 `singleObjCyclesSelfIso_inv_naturality`

English:
lemma singleObjCyclesSelfIso_inv_naturality
  proof: by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom]; rw [Iso.hom_inv_id_assoc]; rw [← singleObjCyclesSelfIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

@[reassoc (attr := simp)]

中文:
引理 singleObjCyclesSelfIso_inv_naturality
  证明: by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom]; rw [Iso.hom_inv_id_assoc]; rw [← singleObjCyclesSelfIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, cancel_epi, comp_id, hom_inv_id, hom_inv_id_assoc, singleObjCyclesSelfIso, singleObjCyclesSelfIso_hom_naturality_assoc
-/
lemma singleObjCyclesSelfIso_inv_naturality :
    (singleObjCyclesSelfIso c j A).inv ≫ cyclesMap ((single C c j).map f) j =
      f ≫ (singleObjCyclesSelfIso c j B).inv := by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom]; rw [Iso.hom_inv_id_assoc]; rw [← singleObjCyclesSelfIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

@[reassoc (attr := simp)]
/--
lemma `singleObjHomologySelfIso_hom_naturality` / 引理 `singleObjHomologySelfIso_hom_naturality`

English:
lemma singleObjHomologySelfIso_hom_naturality
  proof: by
  rw [← cancel_epi (((single C c j).obj A).homologyπ j)]; rw [homologyπ_naturality_assoc]; rw [homologyπ_singleObjHomologySelfIso_hom]; rw [singleObjCyclesSelfIso_hom_naturality]; rw [homologyπ_singleObjHomologySelfIso_hom_assoc]

@[reassoc (attr := simp)]

中文:
引理 singleObjHomologySelfIso_hom_naturality
  证明: by
  rw [← cancel_epi (((single C c j).obj A).homologyπ j)]; rw [homologyπ_naturality_assoc]; rw [homologyπ_singleObjHomologySelfIso_hom]; rw [singleObjCyclesSelfIso_hom_naturality]; rw [homologyπ_singleObjHomologySelfIso_hom_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi, single, singleObjCyclesSelfIso_hom_naturality
-/
lemma singleObjHomologySelfIso_hom_naturality :
    homologyMap ((single C c j).map f) j ≫ (singleObjHomologySelfIso c j B).hom =
      (singleObjHomologySelfIso c j A).hom ≫ f := by
  rw [← cancel_epi (((single C c j).obj A).homologyπ j)]; rw [homologyπ_naturality_assoc]; rw [homologyπ_singleObjHomologySelfIso_hom]; rw [singleObjCyclesSelfIso_hom_naturality]; rw [homologyπ_singleObjHomologySelfIso_hom_assoc]

@[reassoc (attr := simp)]
/--
lemma `singleObjHomologySelfIso_inv_naturality` / 引理 `singleObjHomologySelfIso_inv_naturality`

English:
lemma singleObjHomologySelfIso_inv_naturality
  proof: by
  rw [← cancel_mono (singleObjHomologySelfIso c j B).hom]; rw [assoc]; rw [assoc]; rw [singleObjHomologySelfIso_hom_naturality]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

@[reassoc (attr := simp)]

中文:
引理 singleObjHomologySelfIso_inv_naturality
  证明: by
  rw [← cancel_mono (singleObjHomologySelfIso c j B).hom]; rw [assoc]; rw [assoc]; rw [singleObjHomologySelfIso_hom_naturality]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, cancel_mono, comp_id, inv_hom_id, inv_hom_id_assoc, singleObjHomologySelfIso, singleObjHomologySelfIso_hom_naturality
-/
lemma singleObjHomologySelfIso_inv_naturality :
    (singleObjHomologySelfIso c j A).inv ≫ homologyMap ((single C c j).map f) j =
      f ≫ (singleObjHomologySelfIso c j B).inv := by
  rw [← cancel_mono (singleObjHomologySelfIso c j B).hom]; rw [assoc]; rw [assoc]; rw [singleObjHomologySelfIso_hom_naturality]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

@[reassoc (attr := simp)]
/--
lemma `singleObjOpcyclesSelfIso_hom_naturality` / 引理 `singleObjOpcyclesSelfIso_hom_naturality`

English:
lemma singleObjOpcyclesSelfIso_hom_naturality
  proof: by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom]; rw [singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom_assoc]; rw [p_opcyclesMap]; rw [single_map_f_self]; rw [assoc]; rw [assoc]; rw [singleObjCyclesSelfIso_hom]; rw [singleObjOpcyclesSelfIso_hom]; rw [assoc]

@[reassoc (attr := simp)]

中文:
引理 singleObjOpcyclesSelfIso_hom_naturality
  证明: by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom]; rw [singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom_assoc]; rw [p_opcyclesMap]; rw [single_map_f_self]; rw [assoc]; rw [assoc]; rw [singleObjCyclesSelfIso_hom]; rw [singleObjOpcyclesSelfIso_hom]; rw [assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi, p_opcyclesMap, singleObjCyclesSelfIso, singleObjCyclesSelfIso_hom, singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom_assoc, singleObjOpcyclesSelfIso_hom, single_map_f_self
-/
lemma singleObjOpcyclesSelfIso_hom_naturality :
    (singleObjOpcyclesSelfIso c j A).hom ≫ opcyclesMap ((single C c j).map f) j =
      f ≫ (singleObjOpcyclesSelfIso c j B).hom := by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom]; rw [singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom_assoc]; rw [p_opcyclesMap]; rw [single_map_f_self]; rw [assoc]; rw [assoc]; rw [singleObjCyclesSelfIso_hom]; rw [singleObjOpcyclesSelfIso_hom]; rw [assoc]

@[reassoc (attr := simp)]
/--
lemma `singleObjOpcyclesSelfIso_inv_naturality` / 引理 `singleObjOpcyclesSelfIso_inv_naturality`

English:
lemma singleObjOpcyclesSelfIso_inv_naturality
  proof: by
  rw [← cancel_mono (singleObjOpcyclesSelfIso c j B).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [← singleObjOpcyclesSelfIso_hom_naturality]; rw [Iso.inv_hom_id_assoc]

中文:
引理 singleObjOpcyclesSelfIso_inv_naturality
  证明: by
  rw [← cancel_mono (singleObjOpcyclesSelfIso c j B).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [← singleObjOpcyclesSelfIso_hom_naturality]; rw [Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, cancel_mono, comp_id, inv_hom_id, inv_hom_id_assoc, singleObjOpcyclesSelfIso, singleObjOpcyclesSelfIso_hom_naturality
-/
lemma singleObjOpcyclesSelfIso_inv_naturality :
    opcyclesMap ((single C c j).map f) j ≫ (singleObjOpcyclesSelfIso c j B).inv =
      (singleObjOpcyclesSelfIso c j A).inv ≫ f := by
  rw [← cancel_mono (singleObjOpcyclesSelfIso c j B).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [← singleObjOpcyclesSelfIso_hom_naturality]; rw [Iso.inv_hom_id_assoc]

variable (C)

/-- The computation of the homology of single complexes, as a natural isomorphism
`single C c j ⋙ homologyFunctor C c j ≅ 𝟭 C`. -/
@[simps!]
/--
Definition of `homologyFunctorSingleIso` / `homologyFunctorSingleIso` 的定义

English:
definition homologyFunctorSingleIso
  signature: [CategoryWithHomology C]
  body: NatIso.ofComponents (fun A => (singleObjHomologySelfIso c j A))
    (fun f => singleObjHomologySelfIso_hom_naturality c j f)

中文:
定义 homologyFunctorSingleIso
  签名: [CategoryWithHomology C]
  定义体: NatIso.ofComponents (fun A => (singleObjHomologySelfIso c j A))
    (fun f => singleObjHomologySelfIso_hom_naturality c j f)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, singleObjHomologySelfIso, singleObjHomologySelfIso_hom_naturality
-/
noncomputable def homologyFunctorSingleIso [CategoryWithHomology C] :
    single C c j ⋙ homologyFunctor C c j ≅ 𝟭 _ :=
  NatIso.ofComponents (fun A => (singleObjHomologySelfIso c j A))
    (fun f => singleObjHomologySelfIso_hom_naturality c j f)

end HomologicalComplex

open HomologicalComplex

/--
lemma `ChainComplex.exactAt_succ_single_obj` / 引理 `ChainComplex.exactAt_succ_single_obj`

English:
lemma ChainComplex.exactAt_succ_single_obj
  given: (A : C) (n : Nat)
  proof: exactAt_single_obj _ _ _ _ (by simp)

中文:
引理 ChainComplex.exactAt_succ_single_obj
  条件: (A : C) (n : 自然数)
  证明: exactAt_single_obj _ _ _ _ (by simp)

Depends on / 依赖: exactAt_single_obj
-/
lemma ChainComplex.exactAt_succ_single_obj (A : C) (n : Nat) :
    ExactAt ((single₀ C).obj A) (n + 1) :=
  exactAt_single_obj _ _ _ _ (by simp)

/--
lemma `CochainComplex.exactAt_succ_single_obj` / 引理 `CochainComplex.exactAt_succ_single_obj`

English:
lemma CochainComplex.exactAt_succ_single_obj
  given: (A : C) (n : Nat)
  proof: exactAt_single_obj _ _ _ _ (by simp)

中文:
引理 CochainComplex.exactAt_succ_single_obj
  条件: (A : C) (n : 自然数)
  证明: exactAt_single_obj _ _ _ _ (by simp)

Depends on / 依赖: exactAt_single_obj
-/
lemma CochainComplex.exactAt_succ_single_obj (A : C) (n : Nat) :
    ExactAt ((single₀ C).obj A) (n + 1) :=
  exactAt_single_obj _ _ _ _ (by simp)
