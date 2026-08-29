/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jack McKoen, Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# The monoidal category structure on presheaves of modules

Given a presheaf of commutative rings `R : Cᵒᵖ ⥤ CommRingCat`, we construct
the monoidal category structure on the category of presheaves of modules
`PresheafOfModules (R ⋙ forget₂ _ _)`. The tensor product `M₁ ⊗ M₂` is defined
as the presheaf of modules which sends `X : Cᵒᵖ` to `M₁.obj X ⊗ M₂.obj X`.

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.

-/

@[expose] public section

open CategoryTheory MonoidalCategory BraidedCategory Category Limits

universe v u v₁ u₁

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

instance (X : Cᵒᵖ) : CommRing ((R ⋙ forget₂ _ RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

namespace PresheafOfModules

namespace Monoidal

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `tensorObjMap` / `tensorObjMap` 的定义

English:
definition tensorObjMap
  signature: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  body: ModuleCat.MonoidalCategory.tensorLift (fun m₁ m₂ => M₁.map f m₁ otimesₜ M₂.map f m₂)
    (by
      intro m₁ m₁' m₂
      dsimp +instances
      rw [map_add]; rw [TensorProduct.add_tmul])
    (by intro a m₁ m₂; dsimp; erw [M₁.map_smul]; rfl)
    (by
      intro m₁ m₂ m₂'
      dsimp +instances
      

中文:
定义 tensorObjMap
  签名: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  定义体: ModuleCat.MonoidalCategory.tensorLift (fun m₁ m₂ => M₁.map f m₁ otimesₜ M₂.map f m₂)
    (by
      intro m₁ m₁' m₂
      dsimp +instances
      rw [map_add]; rw [TensorProduct.add_tmul])
    (by intro a m₁ m₂; dsimp; erw [M₁.map_smul]; rfl)
    (by
      intro m₁ m₂ m₂'
      dsimp +instances
      

Depends on / 依赖: ModuleCat, ModuleCat.MonoidalCategory.tensorLift, MonoidalCategory, R.map, TensorProduct, TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_smul, add_tmul, instances, map_add, map_smul, tensorLift, tmul_add, tmul_smul
-/
noncomputable def tensorObjMap {X Y : Cᵒᵖ} (f : X ⟶ Y) : M₁.obj X otimes M₂.obj X ⟶
    (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y otimes M₂.obj Y) :=
  ModuleCat.MonoidalCategory.tensorLift (fun m₁ m₂ => M₁.map f m₁ otimesₜ M₂.map f m₂)
    (by
      intro m₁ m₁' m₂
      dsimp +instances
      rw [map_add]; rw [TensorProduct.add_tmul])
    (by intro a m₁ m₂; dsimp; erw [M₁.map_smul]; rfl)
    (by
      intro m₁ m₂ m₂'
      dsimp +instances
      rw [map_add]; rw [TensorProduct.tmul_add])
    (by intro a m₁ m₂; dsimp; erw [M₂.map_smul, TensorProduct.tmul_smul (r := R.map f a)]; rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two presheaves of modules. -/
@[simps obj]
/--
Definition of `tensorObj` / `tensorObj` 的定义

English:
definition tensorObj
  signature: : PresheafOfModules (R ⋙ forget₂ _ _) where
  body: M₁.obj X otimes M₂.obj X
  map f := tensorObjMap M₁ M₂ f
  map_id X := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m₁ m₂
    dsimp [tensorObjMap]
    simp
    rfl) -- `ModuleCat.restrictScalarsId'App_inv_apply` doesn't get picked up due to type mismatch
  map_comp f g := ModuleCat.MonoidalCa

中文:
定义 tensorObj
  签名: : PresheafOfModules (R ⋙ forget₂ _ _) where
  定义体: M₁.obj X otimes M₂.obj X
  map f := tensorObjMap M₁ M₂ f
  map_id X := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m₁ m₂
    dsimp [tensorObjMap]
    simp
    rfl) -- `ModuleCat.restrictScalarsId'App_inv_apply` doesn't get picked up due to type mismatch
  map_comp f g := ModuleCat.MonoidalCa

Depends on / 依赖: otimes
-/
noncomputable def tensorObj : PresheafOfModules (R ⋙ forget₂ _ _) where
  obj X := M₁.obj X otimes M₂.obj X
  map f := tensorObjMap M₁ M₂ f
  map_id X := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m₁ m₂
    dsimp [tensorObjMap]
    simp
    rfl) -- `ModuleCat.restrictScalarsId'App_inv_apply` doesn't get picked up due to type mismatch
  map_comp f g := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m₁ m₂
    dsimp [tensorObjMap]
    simp +instances)

variable {M₁ M₂ M₃ M₄}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `tensorObj_map_tmul` / 引理 `tensorObj_map_tmul`

English:
lemma tensorObj_map_tmul
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y) (m₁ : M₁.obj X) (m₂ : M₂.obj X)
  proof: rfl

中文:
引理 tensorObj_map_tmul
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y) (m₁ : M₁.obj X) (m₂ : M₂.obj X)
  证明: rfl

Depends on / 依赖: otimes
-/
lemma tensorObj_map_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) (m₁ : M₁.obj X) (m₂ : M₂.obj X) :
    DFunLike.coe (α := (M₁.obj X otimes M₂.obj X :))
      (β := fun _ => (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y otimes M₂.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((tensorObj M₁ M₂).map f)) (m₁ otimesₜ[R.obj X] m₂) =
    M₁.map f m₁ otimesₜ[R.obj Y] M₂.map f m₂ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two morphisms of presheaves of modules. -/
@[simps]
/--
Definition of `tensorHom` / `tensorHom` 的定义

English:
definition tensorHom
  signature: (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄)
  body: f.app X otimesₘ g.app X
  naturality {X Y} φ := ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₃ => by
    dsimp
    rw [tensorObj_map_tmul]
    -- Need `erw` because of the type mismatch in `map` and the tensor product.
    erw [ModuleCat.MonoidalCategory.tensorHom_tmul, tensorObj_map_tmul]
    rw 

中文:
定义 tensorHom
  签名: (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄)
  定义体: f.app X otimesₘ g.app X
  naturality {X Y} φ := ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₃ => by
    dsimp
    rw [tensorObj_map_tmul]
    -- Need `erw` because of the type mismatch in `map` and the tensor product.
    erw [ModuleCat.MonoidalCategory.tensorHom_tmul, tensorObj_map_tmul]
    rw 

Depends on / 依赖: f.app, g.app
-/
noncomputable def tensorHom (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) : tensorObj M₁ M₃ ⟶ tensorObj M₂ M₄ where
  app X := f.app X otimesₘ g.app X
  naturality {X Y} φ := ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₃ => by
    dsimp
    rw [tensorObj_map_tmul]
    -- Need `erw` because of the type mismatch in `map` and the tensor product.
    erw [ModuleCat.MonoidalCategory.tensorHom_tmul, tensorObj_map_tmul]
    rw [naturality_apply]; rw [naturality_apply]
    simp)

end Monoidal

open Monoidal

open ModuleCat.MonoidalCategory in
/--
Instance `monoidalCategoryStruct` / 实例 `monoidalCategoryStruct`

English:
instance monoidalCategoryStruct
  signature: :
  body: tensorObj
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom := tensorHom
  tensorUnit := unit _
  associator M₁ M₂ M₃ := isoMk (fun _ => α_ _ _ _)
    (fun _ _ _ => ModuleCat.MonoidalCategory.tensor_ext₃' (by intros; rfl))
  leftUnitor M := Iso.symm (isoM

中文:
实例 monoidalCategoryStruct
  签名: :
  定义体: tensorObj
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom := tensorHom
  tensorUnit := unit _
  associator M₁ M₂ M₃ := isoMk (fun _ => α_ _ _ _)
    (fun _ _ _ => ModuleCat.MonoidalCategory.tensor_ext₃' (by intros; rfl))
  leftUnitor M := Iso.symm (isoM

Depends on / 依赖: tensorObj
-/
noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  tensorObj := tensorObj
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom := tensorHom
  tensorUnit := unit _
  associator M₁ M₂ M₃ := isoMk (fun _ => α_ _ _ _)
    (fun _ _ _ => ModuleCat.MonoidalCategory.tensor_ext₃' (by intros; rfl))
  leftUnitor M := Iso.symm (isoMk (fun _ => (fun_ _).symm) (fun X Y f => by
    ext m
    dsimp [CommRingCat.forgetToRingCat_obj]
    erw [leftUnitor_inv_apply, leftUnitor_inv_apply, tensorObj_map_tmul, (R.map f).hom.map_one]
    rfl))
  rightUnitor M := Iso.symm (isoMk (fun _ => (ρ_ _).symm) (fun X Y f => by
    ext m
    dsimp [CommRingCat.forgetToRingCat_obj]
    erw [rightUnitor_inv_apply, rightUnitor_inv_apply, tensorObj_map_tmul, (R.map f).hom.map_one]
    rfl))

/--
Instance `monoidalCategory` / 实例 `monoidalCategory`

English:
instance monoidalCategory
  signature: :
  body: by ext1; apply tensorHom_def
  id_tensorHom_id _ _ := by ext1; apply id_tensorHom_id
  tensorHom_comp_tensorHom _ _ _ _ := by ext1; apply tensorHom_comp_tensorHom
  whiskerLeft_id M₁ M₂ := by
    ext1 X
    apply MonoidalCategory.whiskerLeft_id (C := ModuleCat (R.obj X))
  id_whiskerRight _ _ := by


中文:
实例 monoidalCategory
  签名: :
  定义体: by ext1; apply tensorHom_def
  id_tensorHom_id _ _ := by ext1; apply id_tensorHom_id
  tensorHom_comp_tensorHom _ _ _ _ := by ext1; apply tensorHom_comp_tensorHom
  whiskerLeft_id M₁ M₂ := by
    ext1 X
    apply MonoidalCategory.whiskerLeft_id (C := ModuleCat (R.obj X))
  id_whiskerRight _ _ := by


Depends on / 依赖: ModuleCat, MonoidalCategory, MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id, R.obj, associator_naturality, id_tensorHom_id, id_whiskerRight, leftUnitor_naturality, rightUnitor, tensorHom_comp_tensorHom, tensorHom_def, whiskerLeft_id
-/
noncomputable instance monoidalCategory :
    MonoidalCategory (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  tensorHom_def _ _ := by ext1; apply tensorHom_def
  id_tensorHom_id _ _ := by ext1; apply id_tensorHom_id
  tensorHom_comp_tensorHom _ _ _ _ := by ext1; apply tensorHom_comp_tensorHom
  whiskerLeft_id M₁ M₂ := by
    ext1 X
    apply MonoidalCategory.whiskerLeft_id (C := ModuleCat (R.obj X))
  id_whiskerRight _ _ := by
    ext1 X
    apply MonoidalCategory.id_whiskerRight (C := ModuleCat (R.obj X))
  associator_naturality _ _ _ := by ext1; apply associator_naturality
  leftUnitor_naturality _ := by ext1; apply leftUnitor_naturality
  rightUnitor_naturality _ := by ext1; apply rightUnitor_naturality
  pentagon _ _ _ _ := by ext1; apply pentagon
  triangle _ _ := by ext1; apply triangle

open BraidedCategory

/--
Instance `symmetricCategory` / 实例 `symmetricCategory`

English:
instance symmetricCategory
  signature: :
  body: isoMk (fun X => braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X))
      (fun _ _ f => ModuleCat.MonoidalCategory.tensor_ext (fun _ _ => rfl))
  braiding_naturality_right _ _ _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ => rfl)
  braiding_naturality_left _ _

中文:
实例 symmetricCategory
  签名: :
  定义体: isoMk (fun X => braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X))
      (fun _ _ f => ModuleCat.MonoidalCategory.tensor_ext (fun _ _ => rfl))
  braiding_naturality_right _ _ _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ => rfl)
  braiding_naturality_left _ _

Depends on / 依赖: ModuleCat, ModuleCat.MonoidalCategory.tensor_ext, MonoidalCategory, R.obj, braiding, braiding_naturality_left, braiding_naturality_right, hexagon_forward, hexagon_reverse, tensor_ext
-/
noncomputable instance symmetricCategory :
    SymmetricCategory (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  braiding M₁ M₂ :=
    isoMk (fun X => braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X))
      (fun _ _ f => ModuleCat.MonoidalCategory.tensor_ext (fun _ _ => rfl))
  braiding_naturality_right _ _ _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ => rfl)
  braiding_naturality_left _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ => rfl)
  hexagon_forward _ _ _ := by
    ext : 1
    apply hexagon_forward (C := ModuleCat (R.obj _))
  hexagon_reverse _ _ _ := by
    ext : 1
    apply hexagon_reverse (C := ModuleCat (R.obj _))
  symmetry _ _ := by
    ext : 1
    apply SymmetricCategory.symmetry (C := ModuleCat (R.obj _))

section

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

/--
lemma `tensorObj_obj` / 引理 `tensorObj_obj`

English:
lemma tensorObj_obj
  given: (X : Cᵒᵖ)
  proof: rfl

中文:
引理 tensorObj_obj
  条件: (X : Cᵒᵖ)
  证明: rfl

Depends on / 依赖: ModuleCat, R.obj
-/
lemma tensorObj_obj (X : Cᵒᵖ) :
    (M₁ otimes M₂).obj X =
      MonoidalCategory.tensorObj (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) := rfl

attribute [local simp] tensorObj_obj

variable {M₂ M₃} in
@[simp]
/--
lemma `whiskerLeft_app` / 引理 `whiskerLeft_app`

English:
lemma whiskerLeft_app
  given: (f : M₂ ⟶ M₃) (X : Cᵒᵖ)
  proof: rfl

中文:
引理 whiskerLeft_app
  条件: (f : M₂ ⟶ M₃) (X : Cᵒᵖ)
  证明: rfl

Depends on / 依赖: ModuleCat, R.obj, f.app
-/
lemma whiskerLeft_app (f : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    dsimp% (M₁ ◁ f).app X = whiskerLeft (C := ModuleCat (R.obj X)) (M₁.obj X) (f.app X) :=
  rfl

variable {M₁ M₂} in
@[simp]
/--
lemma `whiskerRight_app` / 引理 `whiskerRight_app`

English:
lemma whiskerRight_app
  given: (f : M₁ ⟶ M₂) (M₃ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ)
  proof: rfl

中文:
引理 whiskerRight_app
  条件: (f : M₁ ⟶ M₂) (M₃ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ)
  证明: rfl

Depends on / 依赖: ModuleCat, R.obj, f.app
-/
lemma whiskerRight_app (f : M₁ ⟶ M₂) (M₃ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) :
    dsimp% (f ▷ M₃).app X = whiskerRight (C := ModuleCat (R.obj X)) (f.app X) (M₃.obj X) := rfl

variable {M₁ M₂ M₃ M₄} in
@[simp]
/--
lemma `tensorHom_app` / 引理 `tensorHom_app`

English:
lemma tensorHom_app
  given: (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ)
  proof: rfl

@[simp]

中文:
引理 tensorHom_app
  条件: (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ)
  证明: rfl

@[simp]

Depends on / 依赖: ModuleCat, R.obj, f.app, g.app
-/
lemma tensorHom_app (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ) :
    dsimp% (f otimesₘ g).app X =
      MonoidalCategory.tensorHom (C := ModuleCat (R.obj X)) (f.app X) (g.app X) := rfl

@[simp]
/--
lemma `leftUnitor_hom_app` / 引理 `leftUnitor_hom_app`

English:
lemma leftUnitor_hom_app
  given: (X : Cᵒᵖ)
  proof: rfl

@[simp]

中文:
引理 leftUnitor_hom_app
  条件: (X : Cᵒᵖ)
  证明: rfl

@[simp]

Depends on / 依赖: ModuleCat, R.obj
-/
lemma leftUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (fun_ M₁).hom.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

@[simp]
/--
lemma `leftUnitor_inv_app` / 引理 `leftUnitor_inv_app`

English:
lemma leftUnitor_inv_app
  given: (X : Cᵒᵖ)
  proof: by
  rfl

@[simp]

中文:
引理 leftUnitor_inv_app
  条件: (X : Cᵒᵖ)
  证明: by
  rfl

@[simp]

Depends on / 依赖: ModuleCat, R.obj
-/
lemma leftUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (fun_ M₁).inv.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv := by
  rfl

@[simp]
/--
lemma `rightUnitor_hom_app` / 引理 `rightUnitor_hom_app`

English:
lemma rightUnitor_hom_app
  given: (X : Cᵒᵖ)
  proof: rfl

@[simp]

中文:
引理 rightUnitor_hom_app
  条件: (X : Cᵒᵖ)
  证明: rfl

@[simp]

Depends on / 依赖: ModuleCat, R.obj
-/
lemma rightUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).hom.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

@[simp]
/--
lemma `rightUnitor_inv_app` / 引理 `rightUnitor_inv_app`

English:
lemma rightUnitor_inv_app
  given: (X : Cᵒᵖ)
  proof: rfl

@[simp]

中文:
引理 rightUnitor_inv_app
  条件: (X : Cᵒᵖ)
  证明: rfl

@[simp]

Depends on / 依赖: ModuleCat, R.obj
-/
lemma rightUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).inv.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv :=
  rfl

@[simp]
/--
lemma `associator_hom_app` / 引理 `associator_hom_app`

English:
lemma associator_hom_app
  given: (X : Cᵒᵖ)
  proof: rfl

@[simp]

中文:
引理 associator_hom_app
  条件: (X : Cᵒᵖ)
  证明: rfl

@[simp]

Depends on / 依赖: ModuleCat, R.obj
-/
lemma associator_hom_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).hom.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).hom :=
  rfl

@[simp]
/--
lemma `associator_inv_app` / 引理 `associator_inv_app`

English:
lemma associator_inv_app
  given: (X : Cᵒᵖ)
  proof: rfl

@[simp]

中文:
引理 associator_inv_app
  条件: (X : Cᵒᵖ)
  证明: rfl

@[simp]

Depends on / 依赖: ModuleCat, R.obj
-/
lemma associator_inv_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).inv.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).inv :=
  rfl

@[simp]
/--
lemma `braiding_hom_app` / 引理 `braiding_hom_app`

English:
lemma braiding_hom_app
  given: (X : Cᵒᵖ)
  proof: by
  rfl

@[simp]

中文:
引理 braiding_hom_app
  条件: (X : Cᵒᵖ)
  证明: by
  rfl

@[simp]

Depends on / 依赖: ModuleCat, R.obj
-/
lemma braiding_hom_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).hom.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).hom := by
  rfl

@[simp]
/--
lemma `braiding_inv_app` / 引理 `braiding_inv_app`

English:
lemma braiding_inv_app
  given: (X : Cᵒᵖ)
  proof: rfl

中文:
引理 braiding_inv_app
  条件: (X : Cᵒᵖ)
  证明: rfl

Depends on / 依赖: ModuleCat, R.obj
-/
lemma braiding_inv_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).inv.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).inv := rfl

end

instance (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    PreservesColimitsOfSize.{u, u} (tensorLeft F) where
  preservesColimitsOfShape := ⟨⟨fun hc => ⟨evaluationJointlyReflectsColimits _ _
      (fun X => isColimitOfPreserves (tensorLeft (show ModuleCat (R.obj X) from F.obj X))
        (isColimitOfPreserves (evaluation _ X) hc))⟩⟩⟩

instance (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    PreservesColimitsOfSize.{u, u} (tensorRight F) :=
  preservesColimits_of_natIso (tensorLeftIsoTensorRight F)

end PresheafOfModules
