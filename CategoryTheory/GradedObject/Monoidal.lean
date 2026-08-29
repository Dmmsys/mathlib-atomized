/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.GradedObject.Unitor
public import Mathlib.Data.Fintype.Prod

/-!
# The monoidal category structures on graded objects

Assuming that `C` is a monoidal category and that `I` is an additive monoid,
we introduce a partially defined tensor product on the category `GradedObject I C`:
given `X₁` and `X₂` two objects in `GradedObject I C`, we define
`GradedObject.Monoidal.tensorObj X₁ X₂` under the assumption `HasTensor X₁ X₂`
that the coproduct of `X₁ i ⊗ X₂ j` for `i + j = n` exists for any `n : I`.

Under suitable assumptions about the existence of coproducts and the
preservation of certain coproducts by the tensor products in `C`, we
obtain a monoidal category structure on `GradedObject I C`.
In particular, if `C` has finite coproducts to which the tensor
product commutes, we obtain a monoidal category structure on `GradedObject ℕ C`.

-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits MonoidalCategory Category

variable {I : Type u} [AddMonoid I] {C : Type*} [Category* C] [MonoidalCategory C]

namespace GradedObject

/--
Definition of `HasTensor` / `HasTensor` 的定义

English:
abbreviation HasTensor
  signature: (X₁ X₂ : GradedObject I C)
  body: HasMap (((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂) (fun ⟨i, j⟩ => i + j)

中文:
缩写 HasTensor
  签名: (X₁ X₂ : GradedObject I C)
  定义体: HasMap (((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂) (fun ⟨i, j⟩ => i + j)

Depends on / 依赖: HasMap, curriedTensor, mapBifunctor
-/
abbrev HasTensor (X₁ X₂ : GradedObject I C) : Prop :=
  HasMap (((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂) (fun ⟨i, j⟩ => i + j)

/--
lemma `hasTensor_of_iso` / 引理 `hasTensor_of_iso`

English:
lemma hasTensor_of_iso
  statement: {X₁ X₂ Y₁ Y₂ : GradedObject I C}
  proof: by
  let e : ((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂ ≅
    ((mapBifunctor (curriedTensor C) I I).obj Y₁).obj Y₂ := isoMk _ _
      (fun ⟨i, j⟩ => (eval i).mapIso e₁ otimesᵢ (eval j).mapIso e₂)
  exact hasMap_of_iso e _

中文:
引理 hasTensor_of_iso
  结论: {X₁ X₂ Y₁ Y₂ : GradedObject I C}
  证明: by
  let e : ((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂ ≅
    ((mapBifunctor (curriedTensor C) I I).obj Y₁).obj Y₂ := isoMk _ _
      (fun ⟨i, j⟩ => (eval i).mapIso e₁ otimesᵢ (eval j).mapIso e₂)
  exact hasMap_of_iso e _

Depends on / 依赖: curriedTensor, hasMap_of_iso, mapBifunctor, mapIso
-/
lemma hasTensor_of_iso {X₁ X₂ Y₁ Y₂ : GradedObject I C}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) [HasTensor X₁ X₂] :
    HasTensor Y₁ Y₂ := by
  let e : ((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂ ≅
    ((mapBifunctor (curriedTensor C) I I).obj Y₁).obj Y₂ := isoMk _ _
      (fun ⟨i, j⟩ => (eval i).mapIso e₁ otimesᵢ (eval j).mapIso e₂)
  exact hasMap_of_iso e _

namespace Monoidal

/--
Definition of `tensorObj` / `tensorObj` 的定义

English:
abbreviation tensorObj
  signature: (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂]
  body: mapBifunctorMapObj (curriedTensor C) (fun ⟨i, j⟩ => i + j) X₁ X₂

中文:
缩写 tensorObj
  签名: (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂]
  定义体: mapBifunctorMapObj (curriedTensor C) (fun ⟨i, j⟩ => i + j) X₁ X₂

Depends on / 依赖: curriedTensor, mapBifunctorMapObj
-/
noncomputable abbrev tensorObj (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] :
    GradedObject I C :=
  mapBifunctorMapObj (curriedTensor C) (fun ⟨i, j⟩ => i + j) X₁ X₂

section

variable (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂]

/--
Definition of `ιTensorObj` / `ιTensorObj` 的定义

English:
definition ιTensorObj
  signature: (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂)
  body: ιMapBifunctorMapObj (curriedTensor C) _ _ _ _ _ _ h

中文:
定义 ιTensorObj
  签名: (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂)
  定义体: ιMapBifunctorMapObj (curriedTensor C) _ _ _ _ _ _ h

Depends on / 依赖: curriedTensor
-/
noncomputable def ιTensorObj (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    X₁ i₁ otimes X₂ i₂ ⟶ tensorObj X₁ X₂ i₁₂ :=
  ιMapBifunctorMapObj (curriedTensor C) _ _ _ _ _ _ h

variable {X₁ X₂}

@[ext]
/--
lemma `tensorObj_ext` / 引理 `tensorObj_ext`

English:
lemma tensorObj_ext
  statement: {A : C} {j : I} (f g : tensorObj X₁ X₂ j ⟶ A)
  proof: by
  apply mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

中文:
引理 tensorObj_ext
  结论: {A : C} {j : I} (f g : tensorObj X₁ X₂ j ⟶ A)
  证明: by
  apply mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

Depends on / 依赖: mapObj_ext
-/
lemma tensorObj_ext {A : C} {j : I} (f g : tensorObj X₁ X₂ j ⟶ A)
    (h : forall (i₁ i₂ : I) (hi : i₁ + i₂ = j),
      ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ f = ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ g) : f = g := by
  apply mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

/--
Definition of `tensorObjDesc` / `tensorObjDesc` 的定义

English:
definition tensorObjDesc
  signature: {A : C} {k : I}
  body: mapBifunctorMapObjDesc f

@[reassoc (attr := simp)]

中文:
定义 tensorObjDesc
  签名: {A : C} {k : I}
  定义体: mapBifunctorMapObjDesc f

@[reassoc (attr := simp)]

Depends on / 依赖: mapBifunctorMapObjDesc
-/
noncomputable def tensorObjDesc {A : C} {k : I}
    (f : forall (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ otimes X₂ i₂ ⟶ A) : tensorObj X₁ X₂ k ⟶ A :=
  mapBifunctorMapObjDesc f

@[reassoc (attr := simp)]
/--
lemma `ι_tensorObjDesc` / 引理 `ι_tensorObjDesc`

English:
lemma ι_tensorObjDesc
  statement: {A : C} {k : I}
  proof: by
  apply ι_mapBifunctorMapObjDesc

中文:
引理 ι_tensorObjDesc
  结论: {A : C} {k : I}
  证明: by
  apply ι_mapBifunctorMapObjDesc

Depends on / 依赖: Hom.id
-/
lemma ι_tensorObjDesc {A : C} {k : I}
    (f : forall (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ otimes X₂ i₂ ⟶ A) (i₁ i₂ : I) (hi : i₁ + i₂ = k) :
    ιTensorObj X₁ X₂ i₁ i₂ k hi ≫ tensorObjDesc f = f i₁ i₂ hi := by
  apply ι_mapBifunctorMapObjDesc

end

/--
Definition of `tensorHom` / `tensorHom` 的定义

English:
definition tensorHom
  signature: {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  body: mapBifunctorMapMap _ _ f g

@[reassoc (attr := simp)]

中文:
定义 tensorHom
  签名: {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  定义体: mapBifunctorMapMap _ _ f g

@[reassoc (attr := simp)]

Depends on / 依赖: mapBifunctorMapMap
-/
noncomputable def tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] :
    tensorObj X₁ Y₁ ⟶ tensorObj X₂ Y₂ :=
  mapBifunctorMapMap _ _ f g

@[reassoc (attr := simp)]
/--
lemma `ι_tensorHom` / 引理 `ι_tensorHom`

English:
lemma ι_tensorHom
  statement: {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  proof: by
  rw [tensorHom_def]; rw [assoc]
  apply ι_mapBifunctorMapMap

中文:
引理 ι_tensorHom
  结论: {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  证明: by
  rw [tensorHom_def]; rw [assoc]
  apply ι_mapBifunctorMapMap

Depends on / 依赖: tensorHom_def
-/
lemma ι_tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    ιTensorObj X₁ Y₁ i₁ i₂ i₁₂ h ≫ tensorHom f g i₁₂ =
      (f i₁ otimesₘ g i₂) ≫ ιTensorObj X₂ Y₂ i₁ i₂ i₁₂ h := by
  rw [tensorHom_def]; rw [assoc]
  apply ι_mapBifunctorMapMap

/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
abbreviation whiskerLeft
  signature: (X : GradedObject I C) {Y₁ Y₂ : GradedObject I C} (φ : Y₁ ⟶ Y₂)
  body: tensorHom (𝟙 X) φ

中文:
缩写 whiskerLeft
  签名: (X : GradedObject I C) {Y₁ Y₂ : GradedObject I C} (φ : Y₁ ⟶ Y₂)
  定义体: tensorHom (𝟙 X) φ

Depends on / 依赖: tensorHom
-/
noncomputable abbrev whiskerLeft (X : GradedObject I C) {Y₁ Y₂ : GradedObject I C} (φ : Y₁ ⟶ Y₂)
    [HasTensor X Y₁] [HasTensor X Y₂] : tensorObj X Y₁ ⟶ tensorObj X Y₂ :=
  tensorHom (𝟙 X) φ

/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
abbreviation whiskerRight
  signature: {X₁ X₂ : GradedObject I C} (φ : X₁ ⟶ X₂) (Y : GradedObject I C)
  body: tensorHom φ (𝟙 Y)

@[simp]

中文:
缩写 whiskerRight
  签名: {X₁ X₂ : GradedObject I C} (φ : X₁ ⟶ X₂) (Y : GradedObject I C)
  定义体: tensorHom φ (𝟙 Y)

@[simp]

Depends on / 依赖: tensorHom
-/
noncomputable abbrev whiskerRight {X₁ X₂ : GradedObject I C} (φ : X₁ ⟶ X₂) (Y : GradedObject I C)
    [HasTensor X₁ Y] [HasTensor X₂ Y] : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom φ (𝟙 Y)

@[simp]
/--
lemma `id_tensorHom_id` / 引理 `id_tensorHom_id`

English:
lemma id_tensorHom_id
  given: (X Y : GradedObject I C) [HasTensor X Y]
  proof: by
  dsimp [tensorHom, mapBifunctorMapMap]
  simp only [Functor.map_id, NatTrans.id_app, comp_id, mapMap_id]
  rfl

中文:
引理 id_tensorHom_id
  条件: (X Y : GradedObject I C) [HasTensor X Y]
  证明: by
  dsimp [tensorHom, mapBifunctorMapMap]
  simp only [Functor.map_id, NatTrans.id_app, comp_id, mapMap_id]
  rfl

Depends on / 依赖: Functor, Functor.map_id, NatTrans, NatTrans.id_app, comp_id, id_app, mapBifunctorMapMap, mapMap_id, map_id, tensorHom
-/
lemma id_tensorHom_id (X Y : GradedObject I C) [HasTensor X Y] :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  dsimp [tensorHom, mapBifunctorMapMap]
  simp only [Functor.map_id, NatTrans.id_app, comp_id, mapMap_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `tensorHom_comp_tensorHom` / 引理 `tensorHom_comp_tensorHom`

English:
lemma tensorHom_comp_tensorHom
  statement: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedObject I C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
  proof: by
  ext
  simp

中文:
引理 tensorHom_comp_tensorHom
  结论: {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedObject I C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
  证明: by
  ext
  simp
-/
lemma tensorHom_comp_tensorHom {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedObject I C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] [HasTensor X₃ Y₃] :
    tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ = tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  ext
  simp

/-- The isomorphism `tensorObj X₁ Y₁ ≅ tensorObj X₂ Y₂` induced by isomorphisms of graded
objects `e : X₁ ≅ X₂` and `e' : Y₁ ≅ Y₂`. -/
@[simps]
/--
Definition of `tensorIso` / `tensorIso` 的定义

English:
definition tensorIso
  signature: {X₁ X₂ Y₁ Y₂ : GradedObject I C} (e : X₁ ≅ X₂) (e' : Y₁ ≅ Y₂)
  body: tensorHom e.hom e'.hom
  inv := tensorHom e.inv e'.inv
  hom_inv_id := by simp [tensorHom_comp_tensorHom]
  inv_hom_id := by simp [tensorHom_comp_tensorHom]

中文:
定义 tensorIso
  签名: {X₁ X₂ Y₁ Y₂ : GradedObject I C} (e : X₁ ≅ X₂) (e' : Y₁ ≅ Y₂)
  定义体: tensorHom e.hom e'.hom
  inv := tensorHom e.inv e'.inv
  hom_inv_id := by simp [tensorHom_comp_tensorHom]
  inv_hom_id := by simp [tensorHom_comp_tensorHom]

Depends on / 依赖: e.hom, tensorHom
-/
noncomputable def tensorIso {X₁ X₂ Y₁ Y₂ : GradedObject I C} (e : X₁ ≅ X₂) (e' : Y₁ ≅ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] :
    tensorObj X₁ Y₁ ≅ tensorObj X₂ Y₂ where
  hom := tensorHom e.hom e'.hom
  inv := tensorHom e.inv e'.inv
  hom_inv_id := by simp [tensorHom_comp_tensorHom]
  inv_hom_id := by simp [tensorHom_comp_tensorHom]

/--
lemma `tensorHom_def` / 引理 `tensorHom_def`

English:
lemma tensorHom_def
  statement: {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  proof: by
  rw [tensorHom_comp_tensorHom]; rw [id_comp]; rw [comp_id]

中文:
引理 tensorHom_def
  结论: {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  证明: by
  rw [tensorHom_comp_tensorHom]; rw [id_comp]; rw [comp_id]

Depends on / 依赖: comp_id, id_comp, tensorHom_comp_tensorHom
-/
lemma tensorHom_def {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] [HasTensor X₂ Y₁] :
    tensorHom f g = whiskerRight f Y₁ ≫ whiskerLeft X₂ g := by
  rw [tensorHom_comp_tensorHom]; rw [id_comp]; rw [comp_id]

/--
Definition of `r₁₂₃` / `r₁₂₃` 的定义

English:
definition r₁₂₃
  signature: : I × I × I -> I
  body: fun ⟨i, j, k⟩ => i + j + k

中文:
定义 r₁₂₃
  签名: : I × I × I -> I
  定义体: fun ⟨i, j, k⟩ => i + j + k
-/
def r₁₂₃ : I × I × I -> I := fun ⟨i, j, k⟩ => i + j + k

/--
Definition of `ρ₁₂` / `ρ₁₂` 的定义

English:
definition ρ₁₂
  signature: : BifunctorComp₁₂IndexData (r₁₂₃ : _ -> I) where
  body: I
  p := fun ⟨i₁, i₂⟩ => i₁ + i₂
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq := fun _ => rfl

中文:
定义 ρ₁₂
  签名: : BifunctorComp₁₂IndexData (r₁₂₃ : _ -> I) where
  定义体: I
  p := fun ⟨i₁, i₂⟩ => i₁ + i₂
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq := fun _ => rfl
-/
@[reducible] def ρ₁₂ : BifunctorComp₁₂IndexData (r₁₂₃ : _ -> I) where
  I₁₂ := I
  p := fun ⟨i₁, i₂⟩ => i₁ + i₂
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq := fun _ => rfl

/--
Definition of `ρ₂₃` / `ρ₂₃` 的定义

English:
definition ρ₂₃
  signature: : BifunctorComp₂₃IndexData (r₁₂₃ : _ -> I) where
  body: I
  p := fun ⟨i₂, i₃⟩ => i₂ + i₃
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq _ := (add_assoc _ _ _).symm

中文:
定义 ρ₂₃
  签名: : BifunctorComp₂₃IndexData (r₁₂₃ : _ -> I) where
  定义体: I
  p := fun ⟨i₂, i₃⟩ => i₂ + i₃
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq _ := (add_assoc _ _ _).symm
-/
@[reducible] def ρ₂₃ : BifunctorComp₂₃IndexData (r₁₂₃ : _ -> I) where
  I₂₃ := I
  p := fun ⟨i₂, i₃⟩ => i₂ + i₃
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq _ := (add_assoc _ _ _).symm

variable (I) in
/-- Auxiliary definition for `associator`. -/
@[reducible]
/--
Definition of `triangleIndexData` / `triangleIndexData` 的定义

English:
definition triangleIndexData
  signature: : TriangleIndexData (r₁₂₃ : _ -> I) (fun ⟨i₁, i₃⟩ => i₁ + i₃) where
  body: fun ⟨i₁, i₂⟩ => i₁ + i₂
  p₂₃ := fun ⟨i₂, i₃⟩ => i₂ + i₃
  hp₁₂ := fun _ => rfl
  hp₂₃ := fun _ => (add_assoc _ _ _).symm
  h₁ := add_zero
  h₃ := zero_add

中文:
定义 triangleIndexData
  签名: : TriangleIndexData (r₁₂₃ : _ -> I) (fun ⟨i₁, i₃⟩ => i₁ + i₃) where
  定义体: fun ⟨i₁, i₂⟩ => i₁ + i₂
  p₂₃ := fun ⟨i₂, i₃⟩ => i₂ + i₃
  hp₁₂ := fun _ => rfl
  hp₂₃ := fun _ => (add_assoc _ _ _).symm
  h₁ := add_zero
  h₃ := zero_add
-/
def triangleIndexData : TriangleIndexData (r₁₂₃ : _ -> I) (fun ⟨i₁, i₃⟩ => i₁ + i₃) where
  p₁₂ := fun ⟨i₁, i₂⟩ => i₁ + i₂
  p₂₃ := fun ⟨i₂, i₃⟩ => i₂ + i₃
  hp₁₂ := fun _ => rfl
  hp₂₃ := fun _ => (add_assoc _ _ _).symm
  h₁ := add_zero
  h₃ := zero_add

/--
Definition of `_root_.CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor` / `_root_.CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor` 的定义

English:
abbreviation _root_.CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor
  signature: (X₁ X₂ X₃ : GradedObject I C)
  body: HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) ρ₁₂ X₁ X₂ X₃

中文:
缩写 _root_.范畴论.GradedObject.HasGoodTensor₁₂Tensor
  签名: (X₁ X₂ X₃ : GradedObject I C)
  定义体: HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) ρ₁₂ X₁ X₂ X₃

Depends on / 依赖: curriedTensor
-/
abbrev _root_.CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor (X₁ X₂ X₃ : GradedObject I C) :=
  HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) ρ₁₂ X₁ X₂ X₃

/--
Definition of `_root_.CategoryTheory.GradedObject.HasGoodTensorTensor₂₃` / `_root_.CategoryTheory.GradedObject.HasGoodTensorTensor₂₃` 的定义

English:
abbreviation _root_.CategoryTheory.GradedObject.HasGoodTensorTensor₂₃
  signature: (X₁ X₂ X₃ : GradedObject I C)
  body: HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) ρ₂₃ X₁ X₂ X₃

中文:
缩写 _root_.范畴论.GradedObject.HasGoodTensorTensor₂₃
  签名: (X₁ X₂ X₃ : GradedObject I C)
  定义体: HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) ρ₂₃ X₁ X₂ X₃

Depends on / 依赖: curriedTensor
-/
abbrev _root_.CategoryTheory.GradedObject.HasGoodTensorTensor₂₃ (X₁ X₂ X₃ : GradedObject I C) :=
  HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) ρ₂₃ X₁ X₂ X₃

section

variable (Z : C) (X₁ X₂ X₃ : GradedObject I C)
  {Y₁ Y₂ Y₃ : GradedObject I C}

section
variable [HasTensor X₂ X₃] [HasTensor X₁ (tensorObj X₂ X₃)] [HasTensor Y₂ Y₃]
  [HasTensor Y₁ (tensorObj Y₂ Y₃)]

/--
Definition of `ιTensorObj₃` / `ιTensorObj₃` 的定义

English:
definition ιTensorObj₃
  signature: (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j)
  body: X₁ i₁ ◁ ιTensorObj X₂ X₃ i₂ i₃ _ rfl ≫ ιTensorObj X₁ (tensorObj X₂ X₃) i₁ (i₂ + i₃) j
    (by rw [← add_assoc, h])

@[reassoc]

中文:
定义 ιTensorObj₃
  签名: (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j)
  定义体: X₁ i₁ ◁ ιTensorObj X₂ X₃ i₂ i₃ _ rfl ≫ ιTensorObj X₁ (tensorObj X₂ X₃) i₁ (i₂ + i₃) j
    (by rw [← add_assoc, h])

@[reassoc]

Depends on / 依赖: add_assoc, tensorObj
-/
noncomputable def ιTensorObj₃ (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    X₁ i₁ otimes X₂ i₂ otimes X₃ i₃ ⟶ tensorObj X₁ (tensorObj X₂ X₃) j :=
  X₁ i₁ ◁ ιTensorObj X₂ X₃ i₂ i₃ _ rfl ≫ ιTensorObj X₁ (tensorObj X₂ X₃) i₁ (i₂ + i₃) j
    (by rw [← add_assoc, h])

@[reassoc]
/--
lemma `ιTensorObj₃_eq` / 引理 `ιTensorObj₃_eq`

English:
lemma ιTensorObj₃_eq
  given: (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₂₃ : I) (h' : i₂ + i₃ = i₂₃)
  proof: by
  subst h'
  rfl

中文:
引理 ιTensorObj₃_eq
  条件: (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₂₃ : I) (h' : i₂ + i₃ = i₂₃)
  证明: by
  subst h'
  rfl
-/
lemma ιTensorObj₃_eq (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₂₃ : I) (h' : i₂ + i₃ = i₂₃) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h =
      (X₁ i₁ ◁ ιTensorObj X₂ X₃ i₂ i₃ i₂₃ h') ≫
        ιTensorObj X₁ (tensorObj X₂ X₃) i₁ i₂₃ j (by rw [← h', ← add_assoc, h]) := by
  subst h'
  rfl

variable {X₁ X₂ X₃}

@[reassoc (attr := simp)]
/--
lemma `ιTensorObj₃_tensorHom` / 引理 `ιTensorObj₃_tensorHom`

English:
lemma ιTensorObj₃_tensorHom
  statement: (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
  proof: by
  rw [ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [assoc]; rw [ι_tensorHom]; rw [← id_tensorHom]; rw [← id_tensorHom]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [ι_tensorHom]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [id_comp]; rw [comp_id]

@[ext (iff := false)]

中文:
引理 ιTensorObj₃_tensorHom
  结论: (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
  证明: by
  rw [ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [assoc]; rw [ι_tensorHom]; rw [← id_tensorHom]; rw [← id_tensorHom]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [ι_tensorHom]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [id_comp]; rw [comp_id]

@[ext (iff := false)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.tensorHom_comp_tensorHom_assoc, comp_id, id_comp, id_tensorHom, tensorHom_comp_tensorHom_assoc
-/
lemma ιTensorObj₃_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ tensorHom f₁ (tensorHom f₂ f₃) j =
      (f₁ i₁ otimesₘ f₂ i₂ otimesₘ f₃ i₃) ≫ ιTensorObj₃ Y₁ Y₂ Y₃ i₁ i₂ i₃ j h := by
  rw [ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [assoc]; rw [ι_tensorHom]; rw [← id_tensorHom]; rw [← id_tensorHom]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [ι_tensorHom]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [id_comp]; rw [comp_id]

@[ext (iff := false)]
/--
lemma `tensorObj₃_ext` / 引理 `tensorObj₃_ext`

English:
lemma tensorObj₃_ext
  statement: {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
  proof: by
  apply mapBifunctorBifunctor₂₃MapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

中文:
引理 tensorObj₃_ext
  结论: {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
  证明: by
  apply mapBifunctorBifunctor₂₃MapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi
-/
lemma tensorObj₃_ext {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
    [H : HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (h : forall (i₁ i₂ i₃ : I) (hi : i₁ + i₂ + i₃ = j),
      ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi ≫ f = ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi ≫ g) :
      f = g := by
  apply mapBifunctorBifunctor₂₃MapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

end

section
variable [HasTensor X₁ X₂] [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor Y₁ Y₂]
  [HasTensor (tensorObj Y₁ Y₂) Y₃]

/--
Definition of `ιTensorObj₃'` / `ιTensorObj₃'` 的定义

English:
definition ιTensorObj₃'
  signature: (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j)
  body: (ιTensorObj X₁ X₂ i₁ i₂ (i₁ + i₂) rfl ▷ X₃ i₃) ≫
    ιTensorObj (tensorObj X₁ X₂) X₃ (i₁ + i₂) i₃ j h

@[reassoc]

中文:
定义 ιTensorObj₃'
  签名: (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j)
  定义体: (ιTensorObj X₁ X₂ i₁ i₂ (i₁ + i₂) rfl ▷ X₃ i₃) ≫
    ιTensorObj (tensorObj X₁ X₂) X₃ (i₁ + i₂) i₃ j h

@[reassoc]

Depends on / 依赖: tensorObj
-/
noncomputable def ιTensorObj₃' (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    (X₁ i₁ otimes X₂ i₂) otimes X₃ i₃ ⟶ tensorObj (tensorObj X₁ X₂) X₃ j :=
  (ιTensorObj X₁ X₂ i₁ i₂ (i₁ + i₂) rfl ▷ X₃ i₃) ≫
    ιTensorObj (tensorObj X₁ X₂) X₃ (i₁ + i₂) i₃ j h

@[reassoc]
/--
lemma `ιTensorObj₃'_eq` / 引理 `ιTensorObj₃'_eq`

English:
lemma ιTensorObj₃'_eq
  statement: (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₁₂ : I)
  proof: by
  subst h'
  rfl

中文:
引理 ιTensorObj₃'_eq
  结论: (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₁₂ : I)
  证明: by
  subst h'
  rfl
-/
lemma ιTensorObj₃'_eq (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₁₂ : I)
    (h' : i₁ + i₂ = i₁₂) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h =
      (ιTensorObj X₁ X₂ i₁ i₂ i₁₂ h' ▷ X₃ i₃) ≫
        ιTensorObj (tensorObj X₁ X₂) X₃ i₁₂ i₃ j (by rw [← h', h]) := by
  subst h'
  rfl

variable {X₁ X₂ X₃}

@[reassoc (attr := simp)]
/--
lemma `ιTensorObj₃'_tensorHom` / 引理 `ιTensorObj₃'_tensorHom`

English:
lemma ιTensorObj₃'_tensorHom
  statement: (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
  proof: by
  rw [ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [assoc]; rw [ι_tensorHom]; rw [← tensorHom_id]; rw [← tensorHom_id]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [id_comp]; rw [ι_tensorHom]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [comp_id]

@[ext (iff := false)]

中文:
引理 ιTensorObj₃'_tensorHom
  结论: (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
  证明: by
  rw [ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [assoc]; rw [ι_tensorHom]; rw [← tensorHom_id]; rw [← tensorHom_id]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [id_comp]; rw [ι_tensorHom]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [comp_id]

@[ext (iff := false)]
-/
lemma ιTensorObj₃'_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ tensorHom (tensorHom f₁ f₂) f₃ j =
      ((f₁ i₁ otimesₘ f₂ i₂) otimesₘ f₃ i₃) ≫ ιTensorObj₃' Y₁ Y₂ Y₃ i₁ i₂ i₃ j h := by
  rw [ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _ rfl]; rw [assoc]; rw [ι_tensorHom]; rw [← tensorHom_id]; rw [← tensorHom_id]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [id_comp]; rw [ι_tensorHom]; rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]; rw [comp_id]

@[ext (iff := false)]
/--
lemma `tensorObj₃'_ext` / 引理 `tensorObj₃'_ext`

English:
lemma tensorObj₃'_ext
  statement: {j : I} {A : C} (f g : tensorObj (tensorObj X₁ X₂) X₃ j ⟶ A)
  proof: by
  apply mapBifunctor₁₂BifunctorMapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

中文:
引理 tensorObj₃'_ext
  结论: {j : I} {A : C} (f g : tensorObj (tensorObj X₁ X₂) X₃ j ⟶ A)
  证明: by
  apply mapBifunctor₁₂BifunctorMapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi
-/
lemma tensorObj₃'_ext {j : I} {A : C} (f g : tensorObj (tensorObj X₁ X₂) X₃ j ⟶ A)
    [H : HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    (h : forall (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f = ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) :
      f = g := by
  apply mapBifunctor₁₂BifunctorMapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

end

section
variable [HasTensor X₁ X₂] [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₂ X₃]
  [HasTensor X₁ (tensorObj X₂ X₃)]

/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  body: mapBifunctorAssociator (MonoidalCategory.curriedAssociatorNatIso C) ρ₁₂ ρ₂₃ X₁ X₂ X₃

@[reassoc (attr := simp)]

中文:
定义 associator
  签名: [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  定义体: mapBifunctorAssociator (MonoidalCategory.curriedAssociatorNatIso C) ρ₁₂ ρ₂₃ X₁ X₂ X₃

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.curriedAssociatorNatIso, curriedAssociatorNatIso, mapBifunctorAssociator
-/
noncomputable def associator [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃] :
    tensorObj (tensorObj X₁ X₂) X₃ ≅ tensorObj X₁ (tensorObj X₂ X₃) :=
  mapBifunctorAssociator (MonoidalCategory.curriedAssociatorNatIso C) ρ₁₂ ρ₂₃ X₁ X₂ X₃

@[reassoc (attr := simp)]
/--
lemma `ιTensorObj₃'_associator_hom` / 引理 `ιTensorObj₃'_associator_hom`

English:
lemma ιTensorObj₃'_associator_hom
  proof: ι_mapBifunctorAssociator_hom (MonoidalCategory.curriedAssociatorNatIso C)
    ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

@[reassoc (attr := simp)]

中文:
引理 ιTensorObj₃'_associator_hom
  证明: ι_mapBifunctorAssociator_hom (MonoidalCategory.curriedAssociatorNatIso C)
    ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

@[reassoc (attr := simp)]
-/
lemma ιTensorObj₃'_associator_hom
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (associator X₁ X₂ X₃).hom j =
      (α_ _ _ _).hom ≫ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h :=
  ι_mapBifunctorAssociator_hom (MonoidalCategory.curriedAssociatorNatIso C)
    ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

@[reassoc (attr := simp)]
/--
lemma `ιTensorObj₃_associator_inv` / 引理 `ιTensorObj₃_associator_inv`

English:
lemma ιTensorObj₃_associator_inv
  proof: ι_mapBifunctorAssociator_inv (MonoidalCategory.curriedAssociatorNatIso C)
    ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

中文:
引理 ιTensorObj₃_associator_inv
  证明: ι_mapBifunctorAssociator_inv (MonoidalCategory.curriedAssociatorNatIso C)
    ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

Depends on / 依赖: MonoidalCategory, MonoidalCategory.curriedAssociatorNatIso, curriedAssociatorNatIso
-/
lemma ιTensorObj₃_associator_inv
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (associator X₁ X₂ X₃).inv j =
      (α_ _ _ _).inv ≫ ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h :=
  ι_mapBifunctorAssociator_inv (MonoidalCategory.curriedAssociatorNatIso C)
    ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

variable {X₁ X₂ X₃}

set_option backward.isDefEq.respectTransparency.types false in
variable [HasTensor Y₁ Y₂] [HasTensor (tensorObj Y₁ Y₂) Y₃] [HasTensor Y₂ Y₃]
  [HasTensor Y₁ (tensorObj Y₂ Y₃)] in
/--
lemma `associator_naturality` / 引理 `associator_naturality`

English:
lemma associator_naturality
  statement: (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
  proof: by
        cat_disch

中文:
引理 associator_naturality
  结论: (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
  证明: by
        cat_disch

Depends on / 依赖: cat_disch
-/
lemma associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasGoodTensor₁₂Tensor Y₁ Y₂ Y₃] [HasGoodTensorTensor₂₃ Y₁ Y₂ Y₃] :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
        cat_disch

end

/--
Definition of `_root_.CategoryTheory.GradedObject.HasLeftTensor₃ObjExt` / `_root_.CategoryTheory.GradedObject.HasLeftTensor₃ObjExt` 的定义

English:
abbreviation _root_.CategoryTheory.GradedObject.HasLeftTensor₃ObjExt
  signature: (j : I)
  body: PreservesColimit
  (Discrete.functor fun (i : { i : (I × I × I) | i.1 + i.2.1 + i.2.2 = j }) =>
    (((mapTrifunctor (bifunctorComp₂₃ (curriedTensor C)
      (curriedTensor C)) I I I).obj X₁).obj X₂).obj X₃ i)
    ((curriedTensor C).obj Z)

中文:
缩写 _root_.范畴论.GradedObject.HasLeftTensor₃ObjExt
  签名: (j : I)
  定义体: PreservesColimit
  (Discrete.functor fun (i : { i : (I × I × I) | i.1 + i.2.1 + i.2.2 = j }) =>
    (((mapTrifunctor (bifunctorComp₂₃ (curriedTensor C)
      (curriedTensor C)) I I I).obj X₁).obj X₂).obj X₃ i)
    ((curriedTensor C).obj Z)

Depends on / 依赖: PreservesColimit
-/
abbrev _root_.CategoryTheory.GradedObject.HasLeftTensor₃ObjExt (j : I) := PreservesColimit
  (Discrete.functor fun (i : { i : (I × I × I) | i.1 + i.2.1 + i.2.2 = j }) =>
    (((mapTrifunctor (bifunctorComp₂₃ (curriedTensor C)
      (curriedTensor C)) I I I).obj X₁).obj X₂).obj X₃ i)
    ((curriedTensor C).obj Z)

variable {X₁ X₂ X₃}
variable [HasTensor X₂ X₃] [HasTensor X₁ (tensorObj X₂ X₃)]

@[ext (iff := false)]
/--
lemma `left_tensor_tensorObj₃_ext` / 引理 `left_tensor_tensorObj₃_ext`

English:
lemma left_tensor_tensorObj₃_ext
  statement: {j : I} {A : C} (Z : C)
  proof: by
    refine (@isColimitOfPreserves C _ C _ _ _ _ ((curriedTensor C).obj Z) _
      (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj (H := H) (j := j)) hZ).hom_ext ?_
    intro ⟨⟨i₁, i₂, i₃⟩, hi⟩
    exact h _ _ _ hi

中文:
引理 left_tensor_tensorObj₃_ext
  结论: {j : I} {A : C} (Z : C)
  证明: by
    refine (@isColimitOfPreserves C _ C _ _ _ _ ((curriedTensor C).obj Z) _
      (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj (H := H) (j := j)) hZ).hom_ext ?_
    intro ⟨⟨i₁, i₂, i₃⟩, hi⟩
    exact h _ _ _ hi

Depends on / 依赖: curriedTensor, hom_ext, isColimitOfPreserves
-/
lemma left_tensor_tensorObj₃_ext {j : I} {A : C} (Z : C)
    (f g : Z otimes tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
    [H : HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [hZ : HasLeftTensor₃ObjExt Z X₁ X₂ X₃ j]
    (h : forall (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      (_ ◁ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) ≫ f =
        (_ ◁ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) ≫ g) : f = g := by
    refine (@isColimitOfPreserves C _ C _ _ _ _ ((curriedTensor C).obj Z) _
      (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj (H := H) (j := j)) hZ).hom_ext ?_
    intro ⟨⟨i₁, i₂, i₃⟩, hi⟩
    exact h _ _ _ hi

end

section

variable (X₁ X₂ X₃ X₄ : GradedObject I C)
  [HasTensor X₃ X₄] [HasTensor X₂ (tensorObj X₃ X₄)]
  [HasTensor X₁ (tensorObj X₂ (tensorObj X₃ X₄))]

/--
Definition of `ιTensorObj₄` / `ιTensorObj₄` 的定义

English:
definition ιTensorObj₄
  signature: (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j)
  body: (_ ◁ ιTensorObj₃ X₂ X₃ X₄ i₂ i₃ i₄ _ rfl) ≫
    ιTensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) i₁ (i₂ + i₃ + i₄) j
      (by rw [← h, ← add_assoc, ← add_assoc])

中文:
定义 ιTensorObj₄
  签名: (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j)
  定义体: (_ ◁ ιTensorObj₃ X₂ X₃ X₄ i₂ i₃ i₄ _ rfl) ≫
    ιTensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) i₁ (i₂ + i₃ + i₄) j
      (by rw [← h, ← add_assoc, ← add_assoc])

Depends on / 依赖: add_assoc, tensorObj
-/
noncomputable def ιTensorObj₄ (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j) :
    X₁ i₁ otimes X₂ i₂ otimes X₃ i₃ otimes X₄ i₄ ⟶ tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j :=
  (_ ◁ ιTensorObj₃ X₂ X₃ X₄ i₂ i₃ i₄ _ rfl) ≫
    ιTensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) i₁ (i₂ + i₃ + i₄) j
      (by rw [← h, ← add_assoc, ← add_assoc])

/--
lemma `ιTensorObj₄_eq` / 引理 `ιTensorObj₄_eq`

English:
lemma ιTensorObj₄_eq
  statement: (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j) (i₂₃₄ : I)
  proof: by
  subst hi
  rfl

中文:
引理 ιTensorObj₄_eq
  结论: (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j) (i₂₃₄ : I)
  证明: by
  subst hi
  rfl
-/
lemma ιTensorObj₄_eq (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j) (i₂₃₄ : I)
    (hi : i₂ + i₃ + i₄ = i₂₃₄) :
    ιTensorObj₄ X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h =
      (_ ◁ ιTensorObj₃ X₂ X₃ X₄ i₂ i₃ i₄ _ hi) ≫
        ιTensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) i₁ i₂₃₄ j
          (by rw [← hi, ← add_assoc, ← add_assoc, h]) := by
  subst hi
  rfl

/--
Definition of `_root_.CategoryTheory.GradedObject.HasTensor₄ObjExt` / `_root_.CategoryTheory.GradedObject.HasTensor₄ObjExt` 的定义

English:
abbreviation _root_.CategoryTheory.GradedObject.HasTensor₄ObjExt
  body: forall (i₁ i₂₃₄ : I), HasLeftTensor₃ObjExt (X₁ i₁) X₂ X₃ X₄ i₂₃₄

中文:
缩写 _root_.范畴论.GradedObject.HasTensor₄ObjExt
  定义体: forall (i₁ i₂₃₄ : I), HasLeftTensor₃ObjExt (X₁ i₁) X₂ X₃ X₄ i₂₃₄
-/
abbrev _root_.CategoryTheory.GradedObject.HasTensor₄ObjExt :=
  forall (i₁ i₂₃₄ : I), HasLeftTensor₃ObjExt (X₁ i₁) X₂ X₃ X₄ i₂₃₄

variable {X₁ X₂ X₃ X₄}

@[ext (iff := false)]
/--
lemma `tensorObj₄_ext` / 引理 `tensorObj₄_ext`

English:
lemma tensorObj₄_ext
  statement: {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j ⟶ A)
  proof: by
  apply tensorObj_ext
  intro i₁ i₂₃₄ h'
  apply left_tensor_tensorObj₃_ext
  intro i₂ i₃ i₄ h''
  have hj : i₁ + i₂ + i₃ + i₄ = j := by simp only [← h', ← h'', add_assoc]
  simpa only [assoc, ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j hj i₂₃₄ h''] using h i₁ i₂ i₃ i₄ hj

中文:
引理 tensorObj₄_ext
  结论: {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j ⟶ A)
  证明: by
  apply tensorObj_ext
  intro i₁ i₂₃₄ h'
  apply left_tensor_tensorObj₃_ext
  intro i₂ i₃ i₄ h''
  have hj : i₁ + i₂ + i₃ + i₄ = j := by simp only [← h', ← h'', add_assoc]
  simpa only [assoc, ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j hj i₂₃₄ h''] using h i₁ i₂ i₃ i₄ hj

Depends on / 依赖: add_assoc, tensorObj_ext
-/
lemma tensorObj₄_ext {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j ⟶ A)
    [HasGoodTensorTensor₂₃ X₂ X₃ X₄]
    [H : HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    (h : forall (i₁ i₂ i₃ i₄ : I) (h : i₁ + i₂ + i₃ + i₄ = j),
      ιTensorObj₄ X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h ≫ f =
        ιTensorObj₄ X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h ≫ g) : f = g := by
  apply tensorObj_ext
  intro i₁ i₂₃₄ h'
  apply left_tensor_tensorObj₃_ext
  intro i₂ i₃ i₄ h''
  have hj : i₁ + i₂ + i₃ + i₄ = j := by simp only [← h', ← h'', add_assoc]
  simpa only [assoc, ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j hj i₂₃₄ h''] using h i₁ i₂ i₃ i₄ hj

end

section Pentagon

variable (X₁ X₂ X₃ X₄ : GradedObject I C)
  [HasTensor X₁ X₂] [HasTensor X₂ X₃] [HasTensor X₃ X₄]
  [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₁ (tensorObj X₂ X₃)]
  [HasTensor (tensorObj X₂ X₃) X₄] [HasTensor X₂ (tensorObj X₃ X₄)]
  [HasTensor (tensorObj (tensorObj X₁ X₂) X₃) X₄]
  [HasTensor (tensorObj X₁ (tensorObj X₂ X₃)) X₄]
  [HasTensor X₁ (tensorObj (tensorObj X₂ X₃) X₄)]
  [HasTensor X₁ (tensorObj X₂ (tensorObj X₃ X₄))]
  [HasTensor (tensorObj X₁ X₂) (tensorObj X₃ X₄)]
  [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasGoodTensor₁₂Tensor X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensorTensor₂₃ X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensor₁₂Tensor X₂ X₃ X₄] [HasGoodTensorTensor₂₃ X₂ X₃ X₄]
  [HasGoodTensor₁₂Tensor (tensorObj X₁ X₂) X₃ X₄]
  [HasGoodTensorTensor₂₃ (tensorObj X₁ X₂) X₃ X₄]
  [HasGoodTensor₁₂Tensor X₁ X₂ (tensorObj X₃ X₄)]
  [HasGoodTensorTensor₂₃ X₁ X₂ (tensorObj X₃ X₄)]
  [HasTensor₄ObjExt X₁ X₂ X₃ X₄]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `pentagon_inv` / 引理 `pentagon_inv`

English:
lemma pentagon_inv
  proof: by
  ext j i₁ i₂ i₃ i₄ h
  dsimp only [categoryOfGradedObjects_comp]
  conv_lhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h _ rfl]; rw [assoc]; rw [ι_tensorHom_assoc]
    dsimp only [categoryOfGradedObjects_id, id_eq, eq_mpr_eq_cast, cast_eq]
    rw [id_tensorHom]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [ιTensorObj₃_associator_inv]; rw [ιTensorObj₃'_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [← ιTensorObj₃_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc]; rw [h]) _ rfl, ιTensorObj₃_associator_inv_assoc,
      ιTensorObj₃'_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc, h]) (i₁ + i₂ + i₃) (by rw [add_assoc]), ι_tensorHom]
    dsimp only [id_eq, eq_mpr_eq_cast, categoryOfGradedObjects_id]
    rw [tensorHom_id]; rw [whisker_assoc_symm_assoc]; rw [Iso.hom_inv_id_assoc]; rw [← MonoidalCategory.comp_whiskerRight_assoc]; rw [← MonoidalCategory.comp_whiskerRight_assoc]; rw [← ιTensorObj₃_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]; rw [ιTensorObj₃_associator_inv]; rw [MonoidalCategory.comp_whiskerRight_assoc]; rw [MonoidalCategory.pentagon_inv_assoc]
  conv_rhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ _ _ _ rfl]; rw [ιTensorObj₃_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl]; rw [assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [← ιTensorObj₃_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc]; rw [h]) (i₂ + i₃ + i₄) (by rw [add_assoc]),
      ιTensorObj₃_associator_inv_assoc, associator_inv_naturality_right_assoc,
      ιTensorObj₃'_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc, h]) _ rfl, whisker_exchange_assoc,
      ← ιTensorObj₃_eq_assoc (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ιTensorObj₃_associator_inv, whiskerRight_tensor_assoc, Iso.hom_inv_id_assoc,
      ιTensorObj₃'_eq (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃'_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]

中文:
引理 pentagon_inv
  证明: by
  ext j i₁ i₂ i₃ i₄ h
  dsimp only [categoryOfGradedObjects_comp]
  conv_lhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h _ rfl]; rw [assoc]; rw [ι_tensorHom_assoc]
    dsimp only [categoryOfGradedObjects_id, id_eq, eq_mpr_eq_cast, cast_eq]
    rw [id_tensorHom]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [ιTensorObj₃_associator_inv]; rw [ιTensorObj₃'_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [← ιTensorObj₃_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc]; rw [h]) _ rfl, ιTensorObj₃_associator_inv_assoc,
      ιTensorObj₃'_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc, h]) (i₁ + i₂ + i₃) (by rw [add_assoc]), ι_tensorHom]
    dsimp only [id_eq, eq_mpr_eq_cast, categoryOfGradedObjects_id]
    rw [tensorHom_id]; rw [whisker_assoc_symm_assoc]; rw [Iso.hom_inv_id_assoc]; rw [← MonoidalCategory.comp_whiskerRight_assoc]; rw [← MonoidalCategory.comp_whiskerRight_assoc]; rw [← ιTensorObj₃_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]; rw [ιTensorObj₃_associator_inv]; rw [MonoidalCategory.comp_whiskerRight_assoc]; rw [MonoidalCategory.pentagon_inv_assoc]
  conv_rhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ _ _ _ rfl]; rw [ιTensorObj₃_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl]; rw [assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [← ιTensorObj₃_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc]; rw [h]) (i₂ + i₃ + i₄) (by rw [add_assoc]),
      ιTensorObj₃_associator_inv_assoc, associator_inv_naturality_right_assoc,
      ιTensorObj₃'_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc, h]) _ rfl, whisker_exchange_assoc,
      ← ιTensorObj₃_eq_assoc (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ιTensorObj₃_associator_inv, whiskerRight_tensor_assoc, Iso.hom_inv_id_assoc,
      ιTensorObj₃'_eq (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃'_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp_assoc, cast_eq, categoryOfGradedObjects_comp, categoryOfGradedObjects_id, conv_lhs, eq_mpr_eq_cast, id_eq, id_tensorHom, whiskerLeft_comp_assoc
-/
lemma pentagon_inv :
    tensorHom (𝟙 X₁) (associator X₂ X₃ X₄).inv ≫ (associator X₁ (tensorObj X₂ X₃) X₄).inv ≫
        tensorHom (associator X₁ X₂ X₃).inv (𝟙 X₄) =
    (associator X₁ X₂ (tensorObj X₃ X₄)).inv ≫ (associator (tensorObj X₁ X₂) X₃ X₄).inv := by
  ext j i₁ i₂ i₃ i₄ h
  dsimp only [categoryOfGradedObjects_comp]
  conv_lhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h _ rfl]; rw [assoc]; rw [ι_tensorHom_assoc]
    dsimp only [categoryOfGradedObjects_id, id_eq, eq_mpr_eq_cast, cast_eq]
    rw [id_tensorHom]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [ιTensorObj₃_associator_inv]; rw [ιTensorObj₃'_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [← ιTensorObj₃_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc]; rw [h]) _ rfl, ιTensorObj₃_associator_inv_assoc,
      ιTensorObj₃'_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc, h]) (i₁ + i₂ + i₃) (by rw [add_assoc]), ι_tensorHom]
    dsimp only [id_eq, eq_mpr_eq_cast, categoryOfGradedObjects_id]
    rw [tensorHom_id]; rw [whisker_assoc_symm_assoc]; rw [Iso.hom_inv_id_assoc]; rw [← MonoidalCategory.comp_whiskerRight_assoc]; rw [← MonoidalCategory.comp_whiskerRight_assoc]; rw [← ιTensorObj₃_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]; rw [ιTensorObj₃_associator_inv]; rw [MonoidalCategory.comp_whiskerRight_assoc]; rw [MonoidalCategory.pentagon_inv_assoc]
  conv_rhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ _ _ _ rfl]; rw [ιTensorObj₃_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl]; rw [assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [← ιTensorObj₃_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc]; rw [h]) (i₂ + i₃ + i₄) (by rw [add_assoc]),
      ιTensorObj₃_associator_inv_assoc, associator_inv_naturality_right_assoc,
      ιTensorObj₃'_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc, h]) _ rfl, whisker_exchange_assoc,
      ← ιTensorObj₃_eq_assoc (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ιTensorObj₃_associator_inv, whiskerRight_tensor_assoc, Iso.hom_inv_id_assoc,
      ιTensorObj₃'_eq (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃'_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]

/--
lemma `pentagon` / 引理 `pentagon`

English:
lemma pentagon
  statement: tensorHom (associator X₁ X₂ X₃).hom (𝟙 X₄) ≫
  proof: by
  rw [← cancel_epi (associator (tensorObj X₁ X₂) X₃ X₄).inv]; rw [← cancel_epi (associator X₁ X₂ (tensorObj X₃ X₄)).inv]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [← pentagon_inv_assoc]
  simp [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc]

中文:
引理 pentagon
  结论: tensorHom (associator X₁ X₂ X₃).hom (𝟙 X₄) ≫
  证明: by
  rw [← cancel_epi (associator (tensorObj X₁ X₂) X₃ X₄).inv]; rw [← cancel_epi (associator X₁ X₂ (tensorObj X₃ X₄)).inv]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [← pentagon_inv_assoc]
  simp [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, associator, cancel_epi, inv_hom_id, inv_hom_id_assoc, pentagon_inv_assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc, tensorObj
-/
lemma pentagon : tensorHom (associator X₁ X₂ X₃).hom (𝟙 X₄) ≫
    (associator X₁ (tensorObj X₂ X₃) X₄).hom ≫ tensorHom (𝟙 X₁) (associator X₂ X₃ X₄).hom =
    (associator (tensorObj X₁ X₂) X₃ X₄).hom ≫ (associator X₁ X₂ (tensorObj X₃ X₄)).hom := by
  rw [← cancel_epi (associator (tensorObj X₁ X₂) X₃ X₄).inv]; rw [← cancel_epi (associator X₁ X₂ (tensorObj X₃ X₄)).inv]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [← pentagon_inv_assoc]
  simp [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc]

end Pentagon

section TensorUnit

variable [DecidableEq I] [HasInitial C]

/--
Definition of `tensorUnit` / `tensorUnit` 的定义

English:
definition tensorUnit
  signature: : GradedObject I C
  body: (single₀ I).obj (𝟙_ C)

中文:
定义 tensorUnit
  签名: : GradedObject I C
  定义体: (single₀ I).obj (𝟙_ C)
-/
noncomputable def tensorUnit : GradedObject I C := (single₀ I).obj (𝟙_ C)

/--
Definition of `tensorUnit₀` / `tensorUnit₀` 的定义

English:
definition tensorUnit₀
  signature: : (tensorUnit : GradedObject I C) 0 ≅ 𝟙_ C
  body: singleObjApplyIso (0 : I) (𝟙_ C)

中文:
定义 tensorUnit₀
  签名: : (tensorUnit : GradedObject I C) 0 ≅ 𝟙_ C
  定义体: singleObjApplyIso (0 : I) (𝟙_ C)

Depends on / 依赖: singleObjApplyIso
-/
noncomputable def tensorUnit₀ : (tensorUnit : GradedObject I C) 0 ≅ 𝟙_ C :=
  singleObjApplyIso (0 : I) (𝟙_ C)

/--
Definition of `isInitialTensorUnitApply` / `isInitialTensorUnitApply` 的定义

English:
definition isInitialTensorUnitApply
  signature: (i : I) (hi : i != 0)
  body: isInitialSingleObjApply _ _ _ hi

中文:
定义 isInitialTensorUnitApply
  签名: (i : I) (hi : i != 0)
  定义体: isInitialSingleObjApply _ _ _ hi

Depends on / 依赖: isInitialSingleObjApply
-/
noncomputable def isInitialTensorUnitApply (i : I) (hi : i != 0) :
    IsInitial ((tensorUnit : GradedObject I C) i) :=
  isInitialSingleObjApply _ _ _ hi

end TensorUnit

section LeftUnitor

variable [DecidableEq I] [HasInitial C]
  [forall X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  (X X' : GradedObject I C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasTensor tensorUnit X
  body: mapBifunctorLeftUnitor_hasMap _ _ (leftUnitorNatIso C) _ zero_add _

中文:
实例 :
  签名: HasTensor tensorUnit X
  定义体: mapBifunctorLeftUnitor_hasMap _ _ (leftUnitorNatIso C) _ zero_add _

Depends on / 依赖: leftUnitorNatIso, mapBifunctorLeftUnitor_hasMap, zero_add
-/
instance : HasTensor tensorUnit X :=
  mapBifunctorLeftUnitor_hasMap _ _ (leftUnitorNatIso C) _ zero_add _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasMap (((mapBifunctor (curriedTensor C) I I).obj
  body: inferInstanceAs HasTensor tensorUnit X

中文:
实例 :
  签名: HasMap (((mapBifunctor (curriedTensor C) I I).obj
  定义体: inferInstanceAs HasTensor tensorUnit X

Depends on / 依赖: HasTensor, tensorUnit
-/
instance : HasMap (((mapBifunctor (curriedTensor C) I I).obj
    ((single₀ I).obj (𝟙_ C))).obj X) (fun ⟨i₁, i₂⟩ => i₁ + i₂) :=
inferInstanceAs HasTensor tensorUnit X

/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: : tensorObj tensorUnit X ≅ X
  body: mapBifunctorLeftUnitor (curriedTensor C) (𝟙_ C)
      (leftUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) zero_add X

中文:
定义 leftUnitor
  签名: : tensorObj tensorUnit X ≅ X
  定义体: mapBifunctorLeftUnitor (curriedTensor C) (𝟙_ C)
      (leftUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) zero_add X

Depends on / 依赖: curriedTensor, leftUnitorNatIso, mapBifunctorLeftUnitor, zero_add
-/
noncomputable def leftUnitor : tensorObj tensorUnit X ≅ X :=
    mapBifunctorLeftUnitor (curriedTensor C) (𝟙_ C)
      (leftUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) zero_add X

/--
lemma `leftUnitor_inv_apply` / 引理 `leftUnitor_inv_apply`

English:
lemma leftUnitor_inv_apply
  given: (i : I)
  proof: rfl

中文:
引理 leftUnitor_inv_apply
  条件: (i : I)
  证明: rfl
-/
lemma leftUnitor_inv_apply (i : I) :
    (leftUnitor X).inv i = (fun_ (X i)).inv ≫ tensorUnit₀.inv ▷ (X i) ≫
      ιTensorObj tensorUnit X 0 i i (zero_add i) := rfl

variable {X X'}

@[reassoc (attr := simp)]
/--
lemma `leftUnitor_naturality` / 引理 `leftUnitor_naturality`

English:
lemma leftUnitor_naturality
  given: (φ : X ⟶ X')
  proof: by
  apply mapBifunctorLeftUnitor_naturality

中文:
引理 leftUnitor_naturality
  条件: (φ : X ⟶ X')
  证明: by
  apply mapBifunctorLeftUnitor_naturality

Depends on / 依赖: mapBifunctorLeftUnitor_naturality
-/
lemma leftUnitor_naturality (φ : X ⟶ X') :
    tensorHom (𝟙 (tensorUnit)) φ ≫ (leftUnitor X').hom =
      (leftUnitor X).hom ≫ φ := by
  apply mapBifunctorLeftUnitor_naturality

end LeftUnitor

section RightUnitor

variable [DecidableEq I] [HasInitial C]
  [forall X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  (X X' : GradedObject I C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasTensor X tensorUnit
  body: mapBifunctorRightUnitor_hasMap (curriedTensor C) _
    (rightUnitorNatIso C) _ add_zero _

中文:
实例 :
  签名: HasTensor X tensorUnit
  定义体: mapBifunctorRightUnitor_hasMap (curriedTensor C) _
    (rightUnitorNatIso C) _ add_zero _

Depends on / 依赖: add_zero, curriedTensor, mapBifunctorRightUnitor_hasMap, rightUnitorNatIso
-/
instance : HasTensor X tensorUnit :=
  mapBifunctorRightUnitor_hasMap (curriedTensor C) _
    (rightUnitorNatIso C) _ add_zero _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasMap (((mapBifunctor (curriedTensor C) I I).obj X).obj
  body: inferInstanceAs HasTensor X tensorUnit

中文:
实例 :
  签名: HasMap (((mapBifunctor (curriedTensor C) I I).obj X).obj
  定义体: inferInstanceAs HasTensor X tensorUnit

Depends on / 依赖: HasTensor, tensorUnit
-/
instance : HasMap (((mapBifunctor (curriedTensor C) I I).obj X).obj
    ((single₀ I).obj (𝟙_ C))) (fun ⟨i₁, i₂⟩ => i₁ + i₂) :=
inferInstanceAs HasTensor X tensorUnit

/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: : tensorObj X tensorUnit ≅ X
  body: mapBifunctorRightUnitor (curriedTensor C) (𝟙_ C)
      (rightUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) add_zero X

中文:
定义 rightUnitor
  签名: : tensorObj X tensorUnit ≅ X
  定义体: mapBifunctorRightUnitor (curriedTensor C) (𝟙_ C)
      (rightUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) add_zero X

Depends on / 依赖: add_zero, curriedTensor, mapBifunctorRightUnitor, rightUnitorNatIso
-/
noncomputable def rightUnitor : tensorObj X tensorUnit ≅ X :=
    mapBifunctorRightUnitor (curriedTensor C) (𝟙_ C)
      (rightUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) add_zero X

/--
lemma `rightUnitor_inv_apply` / 引理 `rightUnitor_inv_apply`

English:
lemma rightUnitor_inv_apply
  given: (i : I)
  proof: rfl

中文:
引理 rightUnitor_inv_apply
  条件: (i : I)
  证明: rfl
-/
lemma rightUnitor_inv_apply (i : I) :
    (rightUnitor X).inv i = (ρ_ (X i)).inv ≫ (X i) ◁ tensorUnit₀.inv ≫
      ιTensorObj X tensorUnit i 0 i (add_zero i) := rfl

variable {X X'}

@[reassoc (attr := simp)]
/--
lemma `rightUnitor_naturality` / 引理 `rightUnitor_naturality`

English:
lemma rightUnitor_naturality
  given: (φ : X ⟶ X')
  proof: by
  apply mapBifunctorRightUnitor_naturality

中文:
引理 rightUnitor_naturality
  条件: (φ : X ⟶ X')
  证明: by
  apply mapBifunctorRightUnitor_naturality

Depends on / 依赖: mapBifunctorRightUnitor_naturality
-/
lemma rightUnitor_naturality (φ : X ⟶ X') :
    tensorHom φ (𝟙 (tensorUnit)) ≫ (rightUnitor X').hom =
      (rightUnitor X).hom ≫ φ := by
  apply mapBifunctorRightUnitor_naturality

end RightUnitor

section Triangle

variable [DecidableEq I] [HasInitial C]
  [forall X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [forall X₂, PreservesColimit (Functor.empty.{0} C)
    ((curriedTensor C).flip.obj X₂)]
  (X₁ X₃ : GradedObject I C) [HasTensor X₁ X₃]
  [HasTensor (tensorObj X₁ tensorUnit) X₃] [HasTensor X₁ (tensorObj tensorUnit X₃)]
  [HasGoodTensor₁₂Tensor X₁ tensorUnit X₃] [HasGoodTensorTensor₂₃ X₁ tensorUnit X₃]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `triangle` / 引理 `triangle`

English:
lemma triangle
  proof: by
  convert!
    mapBifunctor_triangle (curriedAssociatorNatIso C) (𝟙_ C) (rightUnitorNatIso C)
      (leftUnitorNatIso C) (triangleIndexData I) X₁ X₃ (by simp)
  all_goals assumption

中文:
引理 triangle
  证明: by
  convert!
    mapBifunctor_triangle (curriedAssociatorNatIso C) (𝟙_ C) (rightUnitorNatIso C)
      (leftUnitorNatIso C) (triangleIndexData I) X₁ X₃ (by simp)
  all_goals assumption

Depends on / 依赖: all_goals, convert, curriedAssociatorNatIso, leftUnitorNatIso, mapBifunctor_triangle, rightUnitorNatIso, triangleIndexData
-/
lemma triangle :
    (associator X₁ tensorUnit X₃).hom ≫ tensorHom (𝟙 X₁) (leftUnitor X₃).hom =
      tensorHom (rightUnitor X₁).hom (𝟙 X₃) := by
  convert!
    mapBifunctor_triangle (curriedAssociatorNatIso C) (𝟙_ C) (rightUnitorNatIso C)
      (leftUnitorNatIso C) (triangleIndexData I) X₁ X₃ (by simp)
  all_goals assumption

end Triangle

end Monoidal

section

variable
  [forall (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [forall (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [forall (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [forall X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [forall X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [forall (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/--
Instance `monoidalCategory` / 实例 `monoidalCategory`

English:
instance monoidalCategory
  signature: : MonoidalCategory (GradedObject I C) where
  body: Monoidal.tensorObj X Y
  tensorHom f g := Monoidal.tensorHom f g
  tensorHom_def f g := Monoidal.tensorHom_def f g
  whiskerLeft X _ _ φ := Monoidal.whiskerLeft X φ
  whiskerRight {_ _ φ Y} := Monoidal.whiskerRight φ Y
  tensorUnit := Monoidal.tensorUnit
  associator X₁ X₂ X₃ := Monoidal.associator X₁ X₂ X₃
  associator_naturality f₁ f₂ f₃ := Monoidal.associator_naturality f₁ f₂ f₃
  leftUnitor X := Monoidal.leftUnitor X
  leftUnitor_naturality := Monoidal.leftUnitor_naturality
  rightUnitor X := Monoidal.rightUnitor X
  rightUnitor_naturality := Monoidal.rightUnitor_naturality
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := Monoidal.tensorHom_comp_tensorHom f₁ g₁ f₂ g₂
  pentagon X₁ X₂ X₃ X₄ := Monoidal.pentagon X₁ X₂ X₃ X₄
  triangle X₁ X₂ := Monoidal.triangle X₁ X₂

中文:
实例 monoidalCategory
  签名: : 幺半群范畴 (GradedObject I C) where
  定义体: Monoidal.tensorObj X Y
  tensorHom f g := Monoidal.tensorHom f g
  tensorHom_def f g := Monoidal.tensorHom_def f g
  whiskerLeft X _ _ φ := Monoidal.whiskerLeft X φ
  whiskerRight {_ _ φ Y} := Monoidal.whiskerRight φ Y
  tensorUnit := Monoidal.tensorUnit
  associator X₁ X₂ X₃ := Monoidal.associator X₁ X₂ X₃
  associator_naturality f₁ f₂ f₃ := Monoidal.associator_naturality f₁ f₂ f₃
  leftUnitor X := Monoidal.leftUnitor X
  leftUnitor_naturality := Monoidal.leftUnitor_naturality
  rightUnitor X := Monoidal.rightUnitor X
  rightUnitor_naturality := Monoidal.rightUnitor_naturality
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := Monoidal.tensorHom_comp_tensorHom f₁ g₁ f₂ g₂
  pentagon X₁ X₂ X₃ X₄ := Monoidal.pentagon X₁ X₂ X₃ X₄
  triangle X₁ X₂ := Monoidal.triangle X₁ X₂

Depends on / 依赖: Monoidal, Monoidal.tensorObj, tensorObj
-/
noncomputable instance monoidalCategory : MonoidalCategory (GradedObject I C) where
  tensorObj X Y := Monoidal.tensorObj X Y
  tensorHom f g := Monoidal.tensorHom f g
  tensorHom_def f g := Monoidal.tensorHom_def f g
  whiskerLeft X _ _ φ := Monoidal.whiskerLeft X φ
  whiskerRight {_ _ φ Y} := Monoidal.whiskerRight φ Y
  tensorUnit := Monoidal.tensorUnit
  associator X₁ X₂ X₃ := Monoidal.associator X₁ X₂ X₃
  associator_naturality f₁ f₂ f₃ := Monoidal.associator_naturality f₁ f₂ f₃
  leftUnitor X := Monoidal.leftUnitor X
  leftUnitor_naturality := Monoidal.leftUnitor_naturality
  rightUnitor X := Monoidal.rightUnitor X
  rightUnitor_naturality := Monoidal.rightUnitor_naturality
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := Monoidal.tensorHom_comp_tensorHom f₁ g₁ f₂ g₂
  pentagon X₁ X₂ X₃ X₄ := Monoidal.pentagon X₁ X₂ X₃ X₄
  triangle X₁ X₂ := Monoidal.triangle X₁ X₂

end

section

instance (n : Nat) : Finite ((fun (i : Nat × Nat) => i.1 + i.2) ⁻¹' {n}) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂⟩, (hi : i₁ + i₂ = n)⟩ =>
    ((⟨i₁, by lia⟩, ⟨i₂, by lia⟩) : Fin (n + 1) × Fin (n + 1))) ?_
  rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h
  simpa using h

set_option backward.isDefEq.respectTransparency.types false in
instance (n : Nat) : Finite ({ i : (Nat × Nat × Nat) | i.1 + i.2.1 + i.2.2 = n }) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂, i₃⟩, (hi : i₁ + i₂ + i₃ = n)⟩ =>
    (⟨⟨i₁, by lia⟩, ⟨i₂, by lia⟩, ⟨i₃, by lia⟩⟩ :
      Fin (n + 1) × Fin (n + 1) × Fin (n + 1))) ?_
  intro _ _ h
  exact Subtype.ext (congrArg (fun x => (x.1.1, x.2.1.1, x.2.2.1)) h)

/-!
The monoidal category structure on `GradedObject ℕ C` can be inferred
from the assumptions `[HasFiniteCoproducts C]`,
`[∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).obj X)]` and
`[∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).flip.obj X)]`.
This requires importing `Mathlib/CategoryTheory/Limits/Preserves/Finite.lean`.
-/

end

end GradedObject

end CategoryTheory
