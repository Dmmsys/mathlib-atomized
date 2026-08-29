/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.BifunctorAssociator
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The monoidal category structure on homological complexes

Let `c : ComplexShape I` with `I` an additive monoid. If `c` is equipped
with the data and axioms `c.TensorSigns`, then the category
`HomologicalComplex C c` can be equipped with a monoidal category
structure if `C` is a monoidal category such that `C` has certain
coproducts and both left/right tensoring commute with these.

In particular, we obtain a monoidal category structure on
`ChainComplex C ℕ` when `C` is an additive monoidal category.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Limits MonoidalCategory Category

namespace HomologicalComplex

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [forall (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]

/--
Definition of `HasTensor` / `HasTensor` 的定义

English:
abbreviation HasTensor
  signature: (K₁ K₂ : HomologicalComplex C c)
  body: HasMapBifunctor K₁ K₂ (curriedTensor C) c

中文:
缩写 HasTensor
  签名: (K₁ K₂ : 同调复形 C c)
  定义体: HasMapBifunctor K₁ K₂ (curriedTensor C) c

Depends on / 依赖: HasMapBifunctor, curriedTensor
-/
abbrev HasTensor (K₁ K₂ : HomologicalComplex C c) := HasMapBifunctor K₁ K₂ (curriedTensor C) c

section

variable [DecidableEq I]

/--
Definition of `tensorObj` / `tensorObj` 的定义

English:
abbreviation tensorObj
  signature: (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂]
  body: mapBifunctor K₁ K₂ (curriedTensor C) c

中文:
缩写 tensorObj
  签名: (K₁ K₂ : 同调复形 C c) [HasTensor K₁ K₂]
  定义体: mapBifunctor K₁ K₂ (curriedTensor C) c

Depends on / 依赖: curriedTensor, mapBifunctor
-/
noncomputable abbrev tensorObj (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂] :
    HomologicalComplex C c :=
  mapBifunctor K₁ K₂ (curriedTensor C) c

/--
Definition of `ιTensorObj` / `ιTensorObj` 的定义

English:
abbreviation ιTensorObj
  signature: (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂]
  body: ιMapBifunctor K₁ K₂ (curriedTensor C) c i₁ i₂ j h

中文:
缩写 ιTensorObj
  签名: (K₁ K₂ : 同调复形 C c) [HasTensor K₁ K₂]
  定义体: ιMapBifunctor K₁ K₂ (curriedTensor C) c i₁ i₂ j h

Depends on / 依赖: curriedTensor
-/
noncomputable abbrev ιTensorObj (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂]
    (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    K₁.X i₁ otimes K₂.X i₂ ⟶ (tensorObj K₁ K₂).X j :=
  ιMapBifunctor K₁ K₂ (curriedTensor C) c i₁ i₂ j h

/--
Definition of `tensorHom` / `tensorHom` 的定义

English:
abbreviation tensorHom
  signature: {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
  body: mapBifunctorMap f g _ _

中文:
缩写 tensorHom
  签名: {K₁ K₂ L₁ L₂ : 同调复形 C c}
  定义体: mapBifunctorMap f g _ _

Depends on / 依赖: mapBifunctorMap
-/
noncomputable abbrev tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
    tensorObj K₁ K₂ ⟶ tensorObj L₁ L₂ :=
  mapBifunctorMap f g _ _

/--
Definition of `HasGoodTensor₁₂` / `HasGoodTensor₁₂` 的定义

English:
abbreviation HasGoodTensor₁₂
  signature: (K₁ K₂ K₃ : HomologicalComplex C c)
  body: HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c

中文:
缩写 HasGoodTensor₁₂
  签名: (K₁ K₂ K₃ : 同调复形 C c)
  定义体: HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c

Depends on / 依赖: curriedTensor
-/
abbrev HasGoodTensor₁₂ (K₁ K₂ K₃ : HomologicalComplex C c) :=
  HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c

/--
Definition of `HasGoodTensor₂₃` / `HasGoodTensor₂₃` 的定义

English:
abbreviation HasGoodTensor₂₃
  signature: (K₁ K₂ K₃ : HomologicalComplex C c)
  body: HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c c

中文:
缩写 HasGoodTensor₂₃
  签名: (K₁ K₂ K₃ : 同调复形 C c)
  定义体: HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c c

Depends on / 依赖: curriedTensor
-/
abbrev HasGoodTensor₂₃ (K₁ K₂ K₃ : HomologicalComplex C c) :=
  HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c c

/--
Definition of `associator` / `associator` 的定义

English:
abbreviation associator
  signature: (K₁ K₂ K₃ : HomologicalComplex C c)
  body: mapBifunctorAssociator (curriedAssociatorNatIso C) K₁ K₂ K₃ c c c

中文:
缩写 associator
  签名: (K₁ K₂ K₃ : 同调复形 C c)
  定义体: mapBifunctorAssociator (curriedAssociatorNatIso C) K₁ K₂ K₃ c c c

Depends on / 依赖: curriedAssociatorNatIso, mapBifunctorAssociator
-/
noncomputable abbrev associator (K₁ K₂ K₃ : HomologicalComplex C c)
    [HasTensor K₁ K₂] [HasTensor K₂ K₃]
    [HasTensor (tensorObj K₁ K₂) K₃] [HasTensor K₁ (tensorObj K₂ K₃)]
    [HasGoodTensor₁₂ K₁ K₂ K₃] [HasGoodTensor₂₃ K₁ K₂ K₃] :
    tensorObj (tensorObj K₁ K₂) K₃ ≅ tensorObj K₁ (tensorObj K₂ K₃) :=
  mapBifunctorAssociator (curriedAssociatorNatIso C) K₁ K₂ K₃ c c c

variable (C c) in
/--
Definition of `tensorUnit` / `tensorUnit` 的定义

English:
abbreviation tensorUnit
  signature: : HomologicalComplex C c
  body: (single C c 0).obj (𝟙_ C)

中文:
缩写 tensorUnit
  签名: : 同调复形 C c
  定义体: (single C c 0).obj (𝟙_ C)

Depends on / 依赖: single
-/
noncomputable abbrev tensorUnit : HomologicalComplex C c := (single C c 0).obj (𝟙_ C)

variable (C c) in
/--
Definition of `tensorUnitIso` / `tensorUnitIso` 的定义

English:
definition tensorUnitIso
  signature: :
  body: GradedObject.isoMk _ _ (fun i =>
    if hi : i = 0 then
      (GradedObject.singleObjApplyIsoOfEq (0 : I) (𝟙_ C) i hi).trans
        (singleObjXIsoOfEq c 0 (𝟙_ C) i hi).symm
    else
      { hom := 0
        inv := 0
        hom_inv_id := (GradedObject.isInitialSingleObjApply 0 (𝟙_ C) i hi).hom_ext _ _
        inv_hom_id := (isZero_single_obj_X c 0 (𝟙_ C) i hi).eq_of_src _ _ })

中文:
定义 tensorUnitIso
  签名: :
  定义体: GradedObject.isoMk _ _ (fun i =>
    if hi : i = 0 then
      (GradedObject.singleObjApplyIsoOfEq (0 : I) (𝟙_ C) i hi).trans
        (singleObjXIsoOfEq c 0 (𝟙_ C) i hi).symm
    else
      { hom := 0
        inv := 0
        hom_inv_id := (GradedObject.isInitialSingleObjApply 0 (𝟙_ C) i hi).hom_ext _ _
        inv_hom_id := (isZero_single_obj_X c 0 (𝟙_ C) i hi).eq_of_src _ _ })

Depends on / 依赖: GradedObject, GradedObject.isInitialSingleObjApply, GradedObject.isoMk, GradedObject.singleObjApplyIsoOfEq, eq_of_src, hom_ext, hom_inv_id, inv_hom_id, isInitialSingleObjApply, isZero_single_obj_X, singleObjApplyIsoOfEq, singleObjXIsoOfEq
-/
noncomputable def tensorUnitIso :
    (GradedObject.single₀ I).obj (𝟙_ C) ≅ (tensorUnit C c).X :=
  GradedObject.isoMk _ _ (fun i =>
    if hi : i = 0 then
      (GradedObject.singleObjApplyIsoOfEq (0 : I) (𝟙_ C) i hi).trans
        (singleObjXIsoOfEq c 0 (𝟙_ C) i hi).symm
    else
      { hom := 0
        inv := 0
        hom_inv_id := (GradedObject.isInitialSingleObjApply 0 (𝟙_ C) i hi).hom_ext _ _
        inv_hom_id := (isZero_single_obj_X c 0 (𝟙_ C) i hi).eq_of_src _ _ })

end

instance (K₁ K₂ : HomologicalComplex C c) [GradedObject.HasTensor K₁.X K₂.X] :
    HasTensor K₁ K₂ := by
  assumption

instance (K₁ K₂ K₃ : HomologicalComplex C c)
    [GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X] :
    HasGoodTensor₁₂ K₁ K₂ K₃ :=
  inferInstanceAs (GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X)

instance (K₁ K₂ K₃ : HomologicalComplex C c)
    [GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X] :
    HasGoodTensor₂₃ K₁ K₂ K₃ :=
  inferInstanceAs (GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X)

section

variable (K : HomologicalComplex C c) [DecidableEq I]

section

variable [forall X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GradedObject.HasTensor (tensorUnit C c).X K.X
  body: GradedObject.hasTensor_of_iso (tensorUnitIso C c) (Iso.refl _)

中文:
实例 :
  签名: GradedObject.HasTensor (tensorUnit C c).X K.X
  定义体: GradedObject.hasTensor_of_iso (tensorUnitIso C c) (Iso.refl _)

Depends on / 依赖: GradedObject, GradedObject.hasTensor_of_iso, Iso.refl, hasTensor_of_iso, tensorUnitIso
-/
instance : GradedObject.HasTensor (tensorUnit C c).X K.X :=
  GradedObject.hasTensor_of_iso (tensorUnitIso C c) (Iso.refl _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasTensor (tensorUnit C c) K
  body: inferInstanceAs (GradedObject.HasTensor (tensorUnit C c).X K.X)

@[simp]

中文:
实例 :
  签名: HasTensor (tensorUnit C c) K
  定义体: inferInstanceAs (GradedObject.HasTensor (tensorUnit C c).X K.X)

@[simp]

Depends on / 依赖: GradedObject, GradedObject.HasTensor, HasTensor, tensorUnit
-/
instance : HasTensor (tensorUnit C c) K :=
  inferInstanceAs (GradedObject.HasTensor (tensorUnit C c).X K.X)

@[simp]
/--
lemma `unit_tensor_d₁` / 引理 `unit_tensor_d₁`

English:
lemma unit_tensor_d₁
  given: (i₁ i₂ j : I)
  proof: by
  by_cases h₁ : c.Rel i₁ (c.next i₁)
  · by_cases h₂ : ComplexShape.π c c c (c.next i₁, i₂) = j
    · rw [mapBifunctor.d₁_eq _ _ _ _ h₁ _ _ h₂, single_obj_d, Functor.map_zero,
        zero_app, zero_comp, smul_zero]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂]
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁]

中文:
引理 unit_tensor_d₁
  条件: (i₁ i₂ j : I)
  证明: by
  by_cases h₁ : c.Rel i₁ (c.next i₁)
  · by_cases h₂ : ComplexShape.π c c c (c.next i₁, i₂) = j
    · rw [mapBifunctor.d₁_eq _ _ _ _ h₁ _ _ h₂, single_obj_d, Functor.map_zero,
        zero_app, zero_comp, smul_zero]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂]
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁]

Depends on / 依赖: ComplexShape, Functor, Functor.map_zero, c.Rel, c.next, mapBifunctor, mapBifunctor.d, map_zero, single_obj_d, smul_zero, zero_app, zero_comp
-/
lemma unit_tensor_d₁ (i₁ i₂ j : I) :
    mapBifunctor.d₁ (tensorUnit C c) K (curriedTensor C) c i₁ i₂ j = 0 := by
  by_cases h₁ : c.Rel i₁ (c.next i₁)
  · by_cases h₂ : ComplexShape.π c c c (c.next i₁, i₂) = j
    · rw [mapBifunctor.d₁_eq _ _ _ _ h₁ _ _ h₂, single_obj_d, Functor.map_zero,
        zero_app, zero_comp, smul_zero]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂]
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁]

end

section

variable [forall X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GradedObject.HasTensor K.X (tensorUnit C c).X
  body: GradedObject.hasTensor_of_iso (Iso.refl _) (tensorUnitIso C c)

中文:
实例 :
  签名: GradedObject.HasTensor K.X (tensorUnit C c).X
  定义体: GradedObject.hasTensor_of_iso (Iso.refl _) (tensorUnitIso C c)

Depends on / 依赖: GradedObject, GradedObject.hasTensor_of_iso, Iso.refl, hasTensor_of_iso, tensorUnitIso
-/
instance : GradedObject.HasTensor K.X (tensorUnit C c).X :=
  GradedObject.hasTensor_of_iso (Iso.refl _) (tensorUnitIso C c)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasTensor K (tensorUnit C c)
  body: inferInstanceAs (GradedObject.HasTensor K.X (tensorUnit C c).X)

@[simp]

中文:
实例 :
  签名: HasTensor K (tensorUnit C c)
  定义体: inferInstanceAs (GradedObject.HasTensor K.X (tensorUnit C c).X)

@[simp]

Depends on / 依赖: GradedObject, GradedObject.HasTensor, HasTensor, tensorUnit
-/
instance : HasTensor K (tensorUnit C c) :=
  inferInstanceAs (GradedObject.HasTensor K.X (tensorUnit C c).X)

@[simp]
/--
lemma `tensor_unit_d₂` / 引理 `tensor_unit_d₂`

English:
lemma tensor_unit_d₂
  given: (i₁ i₂ j : I)
  proof: by
  by_cases h₁ : c.Rel i₂ (c.next i₂)
  · by_cases h₂ : ComplexShape.π c c c (i₁, c.next i₂) = j
    · rw [mapBifunctor.d₂_eq _ _ _ _ _ h₁ _ h₂, single_obj_d, Functor.map_zero,
        zero_comp, smul_zero]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂]
  · rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₁]

中文:
引理 tensor_unit_d₂
  条件: (i₁ i₂ j : I)
  证明: by
  by_cases h₁ : c.Rel i₂ (c.next i₂)
  · by_cases h₂ : ComplexShape.π c c c (i₁, c.next i₂) = j
    · rw [mapBifunctor.d₂_eq _ _ _ _ _ h₁ _ h₂, single_obj_d, Functor.map_zero,
        zero_comp, smul_zero]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂]
  · rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₁]

Depends on / 依赖: ComplexShape, Functor, Functor.map_zero, c.Rel, c.next, mapBifunctor, mapBifunctor.d, map_zero, single_obj_d, smul_zero, zero_comp
-/
lemma tensor_unit_d₂ (i₁ i₂ j : I) :
    mapBifunctor.d₂ K (tensorUnit C c) (curriedTensor C) c i₁ i₂ j = 0 := by
  by_cases h₁ : c.Rel i₂ (c.next i₂)
  · by_cases h₂ : ComplexShape.π c c c (i₁, c.next i₂) = j
    · rw [mapBifunctor.d₂_eq _ _ _ _ _ h₁ _ h₂, single_obj_d, Functor.map_zero,
        zero_comp, smul_zero]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂]
  · rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₁]

end

end

section Unitor

variable (K : HomologicalComplex C c) [DecidableEq I]

section LeftUnitor

variable [forall X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `leftUnitor'` / `leftUnitor'` 的定义

English:
definition leftUnitor'
  signature: :
  body: GradedObject.Monoidal.tensorIso ((tensorUnitIso C c).symm) (Iso.refl _) ≪≫
    GradedObject.Monoidal.leftUnitor K.X

中文:
定义 leftUnitor'
  签名: :
  定义体: GradedObject.Monoidal.tensorIso ((tensorUnitIso C c).symm) (Iso.refl _) ≪≫
    GradedObject.Monoidal.leftUnitor K.X

Depends on / 依赖: GradedObject, GradedObject.Monoidal.leftUnitor, GradedObject.Monoidal.tensorIso, Iso.refl, Monoidal, leftUnitor, tensorIso, tensorUnitIso
-/
noncomputable def leftUnitor' :
    (tensorObj (tensorUnit C c) K).X ≅ K.X :=
  GradedObject.Monoidal.tensorIso ((tensorUnitIso C c).symm) (Iso.refl _) ≪≫
    GradedObject.Monoidal.leftUnitor K.X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `leftUnitor'_inv` / 引理 `leftUnitor'_inv`

English:
lemma leftUnitor'_inv
  given: (i : I)
  proof: by
  dsimp [leftUnitor']
  rw [GradedObject.Monoidal.leftUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [Iso.cancel_iso_inv_left]; rw [GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [tensorHom_id]; rw [← comp_whiskerRight_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom]; rw [Iso.hom_inv_id_assoc]
  dsimp [tensorUnitIso]
  rw [dif_pos rfl]
  rfl

中文:
引理 leftUnitor'_inv
  条件: (i : I)
  证明: by
  dsimp [leftUnitor']
  rw [GradedObject.Monoidal.leftUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [Iso.cancel_iso_inv_left]; rw [GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [tensorHom_id]; rw [← comp_whiskerRight_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom]; rw [Iso.hom_inv_id_assoc]
  dsimp [tensorUnitIso]
  rw [dif_pos rfl]
  rfl
-/
lemma leftUnitor'_inv (i : I) :
    (leftUnitor' K).inv i = (fun_ (K.X i)).inv ≫ ((singleObjXSelf c 0 (𝟙_ C)).inv ▷ (K.X i)) ≫
      ιTensorObj (tensorUnit C c) K 0 i i (zero_add i) := by
  dsimp [leftUnitor']
  rw [GradedObject.Monoidal.leftUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [Iso.cancel_iso_inv_left]; rw [GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [tensorHom_id]; rw [← comp_whiskerRight_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom]; rw [Iso.hom_inv_id_assoc]
  dsimp [tensorUnitIso]
  rw [dif_pos rfl]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `leftUnitor'_inv_comm` / 引理 `leftUnitor'_inv_comm`

English:
lemma leftUnitor'_inv_comm
  given: (i j : I)
  proof: by
  by_cases hij : c.Rel i j
  · simp only [leftUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      unit_tensor_d₁, comp_zero, zero_add]
    rw [mapBifunctor.d₂_eq _ _ _ _ _ hij _ (by simp)]
    dsimp
    simp only [ComplexShape.ε_zero, one_smul, ← whisker_exchange_assoc,
      id_whiskerLeft, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]

中文:
引理 leftUnitor'_inv_comm
  条件: (i j : I)
  证明: by
  by_cases hij : c.Rel i j
  · simp only [leftUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      unit_tensor_d₁, comp_zero, zero_add]
    rw [mapBifunctor.d₂_eq _ _ _ _ _ hij _ (by simp)]
    dsimp
    simp only [ComplexShape.ε_zero, one_smul, ← whisker_exchange_assoc,
      id_whiskerLeft, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]
-/
lemma leftUnitor'_inv_comm (i j : I) :
    (leftUnitor' K).inv i ≫ (tensorObj (tensorUnit C c) K).d i j =
      K.d i j ≫ (leftUnitor' K).inv j := by
  by_cases hij : c.Rel i j
  · simp only [leftUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      unit_tensor_d₁, comp_zero, zero_add]
    rw [mapBifunctor.d₂_eq _ _ _ _ _ hij _ (by simp)]
    dsimp
    simp only [ComplexShape.ε_zero, one_smul, ← whisker_exchange_assoc,
      id_whiskerLeft, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]

/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: :
  body: Iso.symm (Hom.isoOfComponents (fun i => (GradedObject.eval i).mapIso (leftUnitor' K).symm)
    (fun _ _ _ => leftUnitor'_inv_comm _ _ _))

中文:
定义 leftUnitor
  签名: :
  定义体: Iso.symm (Hom.isoOfComponents (fun i => (GradedObject.eval i).mapIso (leftUnitor' K).symm)
    (fun _ _ _ => leftUnitor'_inv_comm _ _ _))

Depends on / 依赖: GradedObject, GradedObject.eval, Hom.isoOfComponents, Iso.symm, _inv_comm, isoOfComponents, leftUnitor, mapIso
-/
noncomputable def leftUnitor :
    tensorObj (tensorUnit C c) K ≅ K :=
  Iso.symm (Hom.isoOfComponents (fun i => (GradedObject.eval i).mapIso (leftUnitor' K).symm)
    (fun _ _ _ => leftUnitor'_inv_comm _ _ _))

end LeftUnitor

section RightUnitor

variable [forall X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `rightUnitor'` / `rightUnitor'` 的定义

English:
definition rightUnitor'
  signature: :
  body: GradedObject.Monoidal.tensorIso (Iso.refl _) ((tensorUnitIso C c).symm) ≪≫
    GradedObject.Monoidal.rightUnitor K.X

中文:
定义 rightUnitor'
  签名: :
  定义体: GradedObject.Monoidal.tensorIso (Iso.refl _) ((tensorUnitIso C c).symm) ≪≫
    GradedObject.Monoidal.rightUnitor K.X

Depends on / 依赖: GradedObject, GradedObject.Monoidal.rightUnitor, GradedObject.Monoidal.tensorIso, Iso.refl, Monoidal, rightUnitor, tensorIso, tensorUnitIso
-/
noncomputable def rightUnitor' :
    (tensorObj K (tensorUnit C c)).X ≅ K.X :=
  GradedObject.Monoidal.tensorIso (Iso.refl _) ((tensorUnitIso C c).symm) ≪≫
    GradedObject.Monoidal.rightUnitor K.X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `rightUnitor'_inv` / 引理 `rightUnitor'_inv`

English:
lemma rightUnitor'_inv
  given: (i : I)
  proof: by
  dsimp [rightUnitor']
  rw [GradedObject.Monoidal.rightUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [Iso.cancel_iso_inv_left]; rw [GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [id_tensorHom]; rw [← whiskerLeft_comp_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom]; rw [Iso.hom_inv_id_assoc]
  dsimp [tensorUnitIso]
  rw [dif_pos rfl]
  rfl

中文:
引理 rightUnitor'_inv
  条件: (i : I)
  证明: by
  dsimp [rightUnitor']
  rw [GradedObject.Monoidal.rightUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [Iso.cancel_iso_inv_left]; rw [GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [id_tensorHom]; rw [← whiskerLeft_comp_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom]; rw [Iso.hom_inv_id_assoc]
  dsimp [tensorUnitIso]
  rw [dif_pos rfl]
  rfl
-/
lemma rightUnitor'_inv (i : I) :
    (rightUnitor' K).inv i = (ρ_ (K.X i)).inv ≫ ((K.X i) ◁ (singleObjXSelf c 0 (𝟙_ C)).inv) ≫
      ιTensorObj K (tensorUnit C c) i 0 i (add_zero i) := by
  dsimp [rightUnitor']
  rw [GradedObject.Monoidal.rightUnitor_inv_apply]; rw [assoc]; rw [assoc]; rw [Iso.cancel_iso_inv_left]; rw [GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [id_tensorHom]; rw [← whiskerLeft_comp_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom]; rw [Iso.hom_inv_id_assoc]
  dsimp [tensorUnitIso]
  rw [dif_pos rfl]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `rightUnitor'_inv_comm` / 引理 `rightUnitor'_inv_comm`

English:
lemma rightUnitor'_inv_comm
  given: (i j : I)
  proof: by
  by_cases hij : c.Rel i j
  · simp only [rightUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      tensor_unit_d₂, comp_zero, add_zero]
    rw [mapBifunctor.d₁_eq _ _ _ _ hij _ _ (by simp)]
    dsimp
    simp only [one_smul, whisker_exchange_assoc, whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]

中文:
引理 rightUnitor'_inv_comm
  条件: (i j : I)
  证明: by
  by_cases hij : c.Rel i j
  · simp only [rightUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      tensor_unit_d₂, comp_zero, add_zero]
    rw [mapBifunctor.d₁_eq _ _ _ _ hij _ _ (by simp)]
    dsimp
    simp only [one_smul, whisker_exchange_assoc, whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]
-/
lemma rightUnitor'_inv_comm (i j : I) :
    (rightUnitor' K).inv i ≫ (tensorObj K (tensorUnit C c)).d i j =
      K.d i j ≫ (rightUnitor' K).inv j := by
  by_cases hij : c.Rel i j
  · simp only [rightUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      tensor_unit_d₂, comp_zero, add_zero]
    rw [mapBifunctor.d₁_eq _ _ _ _ hij _ _ (by simp)]
    dsimp
    simp only [one_smul, whisker_exchange_assoc, whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]

/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: :
  body: Iso.symm (Hom.isoOfComponents (fun i => (GradedObject.eval i).mapIso (rightUnitor' K).symm)
    (fun _ _ _ => rightUnitor'_inv_comm _ _ _))

中文:
定义 rightUnitor
  签名: :
  定义体: Iso.symm (Hom.isoOfComponents (fun i => (GradedObject.eval i).mapIso (rightUnitor' K).symm)
    (fun _ _ _ => rightUnitor'_inv_comm _ _ _))

Depends on / 依赖: GradedObject, GradedObject.eval, Hom.isoOfComponents, Iso.symm, _inv_comm, isoOfComponents, mapIso, rightUnitor
-/
noncomputable def rightUnitor :
    tensorObj K (tensorUnit C c) ≅ K :=
  Iso.symm (Hom.isoOfComponents (fun i => (GradedObject.eval i).mapIso (rightUnitor' K).symm)
    (fun _ _ _ => rightUnitor'_inv_comm _ _ _))

end RightUnitor

end Unitor

variable (C c) [forall (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [forall X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [forall X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [forall (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [forall (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [forall (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `monoidalCategoryStruct` / 实例 `monoidalCategoryStruct`

English:
instance monoidalCategoryStruct
  signature: :
  body: tensorObj K₁ K₂
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom f g := tensorHom f g
  tensorUnit := tensorUnit C c
  associator K₁ K₂ K₃ := associator K₁ K₂ K₃
  leftUnitor K := leftUnitor K
  rightUnitor K := rightUnitor K

中文:
实例 monoidalCategoryStruct
  签名: :
  定义体: tensorObj K₁ K₂
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom f g := tensorHom f g
  tensorUnit := tensorUnit C c
  associator K₁ K₂ K₃ := associator K₁ K₂ K₃
  leftUnitor K := leftUnitor K
  rightUnitor K := rightUnitor K

Depends on / 依赖: tensorObj
-/
noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (HomologicalComplex C c) where
  tensorObj K₁ K₂ := tensorObj K₁ K₂
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom f g := tensorHom f g
  tensorUnit := tensorUnit C c
  associator K₁ K₂ K₃ := associator K₁ K₂ K₃
  leftUnitor K := leftUnitor K
  rightUnitor K := rightUnitor K

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Monoidal.inducingFunctorData` / `Monoidal.inducingFunctorData` 的定义

English:
definition Monoidal.inducingFunctorData
  signature: :
  body: Iso.refl _
  εIso := tensorUnitIso C c
  whiskerLeft_eq K₁ K₂ L₂ g := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  whiskerRight_eq {K₁ L₁} f K₂ := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  tensorHom_eq {K₁ L₁ K₂ L₂} f g := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  associator_eq K₁ K₂ K₃ := by
    dsimp [forget]
    simp only [tensorHom_id, whiskerRight_tensor, id_whiskerRight,
      id_comp, Iso.inv_hom_id, comp_id, assoc]
    erw [id_whiskerRight]
    rw [id_comp]
    erw [id_comp]
    rfl
  leftUnitor_eq K := by
    dsimp
    erw [id_comp]
    rfl
  rightUnitor_eq K := by
    dsimp
    rw [assoc]
    erw [id_comp]
    rfl

中文:
定义 幺半群.inducingFunctorData
  签名: :
  定义体: Iso.refl _
  εIso := tensorUnitIso C c
  whiskerLeft_eq K₁ K₂ L₂ g := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  whiskerRight_eq {K₁ L₁} f K₂ := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  tensorHom_eq {K₁ L₁ K₂ L₂} f g := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  associator_eq K₁ K₂ K₃ := by
    dsimp [forget]
    simp only [tensorHom_id, whiskerRight_tensor, id_whiskerRight,
      id_comp, Iso.inv_hom_id, comp_id, assoc]
    erw [id_whiskerRight]
    rw [id_comp]
    erw [id_comp]
    rfl
  leftUnitor_eq K := by
    dsimp
    erw [id_comp]
    rfl
  rightUnitor_eq K := by
    dsimp
    rw [assoc]
    erw [id_comp]
    rfl

Depends on / 依赖: Iso.refl
-/
noncomputable def Monoidal.inducingFunctorData :
    Monoidal.InducingFunctorData (forget C c) where
  μIso _ _ := Iso.refl _
  εIso := tensorUnitIso C c
  whiskerLeft_eq K₁ K₂ L₂ g := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  whiskerRight_eq {K₁ L₁} f K₂ := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  tensorHom_eq {K₁ L₁ K₂ L₂} f g := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  associator_eq K₁ K₂ K₃ := by
    dsimp [forget]
    simp only [tensorHom_id, whiskerRight_tensor, id_whiskerRight,
      id_comp, Iso.inv_hom_id, comp_id, assoc]
    erw [id_whiskerRight]
    rw [id_comp]
    erw [id_comp]
    rfl
  leftUnitor_eq K := by
    dsimp
    erw [id_comp]
    rfl
  rightUnitor_eq K := by
    dsimp
    rw [assoc]
    erw [id_comp]
    rfl

/--
Instance `monoidalCategory` / 实例 `monoidalCategory`

English:
instance monoidalCategory
  signature: : MonoidalCategory (HomologicalComplex C c)
  body: Monoidal.induced _ (Monoidal.inducingFunctorData C c)

中文:
实例 monoidalCategory
  签名: : 幺半群范畴 (同调复形 C c)
  定义体: Monoidal.induced _ (Monoidal.inducingFunctorData C c)

Depends on / 依赖: Monoidal, Monoidal.induced, Monoidal.inducingFunctorData, induced, inducingFunctorData
-/
noncomputable instance monoidalCategory : MonoidalCategory (HomologicalComplex C c) :=
  Monoidal.induced _ (Monoidal.inducingFunctorData C c)

set_option backward.isDefEq.respectTransparency.types false in
noncomputable example {D : Type*} [Category* D] [Preadditive D] [MonoidalCategory D]
    [HasZeroObject D] [HasFiniteCoproducts D] [((curriedTensor D).Additive)]
    [forall (X : D), (((curriedTensor D).obj X).Additive)]
    [forall (X : D), PreservesFiniteCoproducts ((curriedTensor D).obj X)]
    [forall (X : D), PreservesFiniteCoproducts ((curriedTensor D).flip.obj X)] :
    MonoidalCategory (ChainComplex D Nat) := inferInstance

end HomologicalComplex
