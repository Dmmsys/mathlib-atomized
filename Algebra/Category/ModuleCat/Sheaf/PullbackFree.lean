/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Final.Type

/-!
# Pullbacks of free sheaves of modules

Let `S` (resp.`R`) be a sheaf of rings on a category `C` (resp. `D`)
equipped with a Grothendieck topology `J` (resp. `K`).
Let `F : C ⥤ D` be a continuous functor.
Let `φ` be a morphism from `S` to the direct image of `R`.

We introduce `unitToPushforwardObjUnit φ` which is the morphism
in the category `SheafOfModules S` which corresponds to `φ`, and
show that the adjoint morphism
`pullbackObjUnitToUnit φ : (pullback.{u} φ).obj (unit S) ⟶ unit R`
is an isomorphism when `F` is a final functor.
More generally, the functor `pullback φ` sends the free sheaf
of modules `free I` to `free I`, see `pullbackObjFreeIso` and
`freeFunctorCompPullbackIso`.
-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The canonical map from the (global) sections of a sheaf of modules
to the (global) sections of its pushforward. -/
@[simps]
/--
Definition of `pushforwardSections` / `pushforwardSections` 的定义

English:
definition pushforwardSections
  signature: {M : SheafOfModules.{v} R} (s : M.sections)
  body: s.val _
  property _ := s.property _

中文:
定义 pushforwardSections
  签名: {M : 模层.{v} R} (s : M.sections)
  定义体: s.val _
  property _ := s.property _

Depends on / 依赖: s.val
-/
def pushforwardSections {M : SheafOfModules.{v} R} (s : M.sections) :
    ((pushforward φ).obj M).sections where
  val _ := s.val _
  property _ := s.property _

variable (M) in
/--
lemma `bijective_pushforwardSections` / 引理 `bijective_pushforwardSections`

English:
lemma bijective_pushforwardSections
  given: [F.Final]
  proof: Functor.bijective_sectionsPrecomp _ _

中文:
引理 bijective_pushforwardSections
  条件: [F.终]
  证明: Functor.bijective_sectionsPrecomp _ _
-/
lemma bijective_pushforwardSections [F.Final] :
    Function.Bijective (pushforwardSections φ (M := M)) :=
  Functor.bijective_sectionsPrecomp _ _

/--
Definition of `unitToPushforwardObjUnit` / `unitToPushforwardObjUnit` 的定义

English:
definition unitToPushforwardObjUnit
  signature: : unit S ⟶ (pushforward.{u} φ).obj (unit R) where
  body: ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (φ.hom.app X)) (fun r => by
    ext m
    exact ((φ.hom.app X).hom.map_mul _ _).symm)
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom (φ.hom.naturality f) _

中文:
定义 unitToPushforwardObjUnit
  签名: : unit S ⟶ (pushforward.{u} φ).obj (unit R) where
  定义体: ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (φ.hom.app X)) (fun r => by
    ext m
    exact ((φ.hom.app X).hom.map_mul _ _).symm)
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom (φ.hom.naturality f) _

Depends on / 依赖: AddCommGrpCat, ConcreteCategory, ConcreteCategory.congr_hom, ModuleCat, ModuleCat.homMk, RingCat, congr_hom, hom.app, hom.map_mul, hom.naturality, map_mul, naturality, val.naturality
-/
noncomputable def unitToPushforwardObjUnit : unit S ⟶ (pushforward.{u} φ).obj (unit R) where
  val.app X := ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (φ.hom.app X)) (fun r => by
    ext m
    exact ((φ.hom.app X).hom.map_mul _ _).symm)
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom (φ.hom.naturality f) _

/--
lemma `unitToPushforwardObjUnit_val_app_apply` / 引理 `unitToPushforwardObjUnit_val_app_apply`

English:
lemma unitToPushforwardObjUnit_val_app_apply
  given: {X : Cᵒᵖ} (a : S.obj.obj X)
  proof: rfl

中文:
引理 unitToPushforwardObjUnit_val_app_apply
  条件: {X : Cᵒᵖ} (a : S.obj.obj X)
  证明: rfl
-/
lemma unitToPushforwardObjUnit_val_app_apply {X : Cᵒᵖ} (a : S.obj.obj X) :
    (unitToPushforwardObjUnit φ).val.app X a = φ.hom.app X a := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `pushforwardSections_unitHomEquiv` / 引理 `pushforwardSections_unitHomEquiv`

English:
lemma pushforwardSections_unitHomEquiv
  proof: by
  ext X
  have := unitToPushforwardObjUnit_val_app_apply φ (X := X) 1
  simp [this, map_one]
  rfl

中文:
引理 pushforwardSections_unitHomEquiv
  证明: by
  ext X
  have := unitToPushforwardObjUnit_val_app_apply φ (X := X) 1
  simp [this, map_one]
  rfl

Depends on / 依赖: map_one, unitToPushforwardObjUnit_val_app_apply
-/
lemma pushforwardSections_unitHomEquiv
    {M : SheafOfModules.{u} R} (f : unit R ⟶ M) :
    pushforwardSections φ (M.unitHomEquiv f) =
      ((pushforward φ).obj M).unitHomEquiv
        (unitToPushforwardObjUnit φ ≫ (pushforward φ).map f) := by
  ext X
  have := unitToPushforwardObjUnit_val_app_apply φ (X := X) 1
  simp [this, map_one]
  rfl

variable [(pushforward.{u} φ).IsRightAdjoint]

/--
Definition of `pullbackObjUnitToUnit` / `pullbackObjUnitToUnit` 的定义

English:
definition pullbackObjUnitToUnit
  signature: :
  body: ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm (unitToPushforwardObjUnit φ)

@[simp]

中文:
定义 pullbackObjUnitToUnit
  签名: :
  定义体: ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm (unitToPushforwardObjUnit φ)

@[simp]

Depends on / 依赖: homEquiv, pullbackPushforwardAdjunction, unitToPushforwardObjUnit
-/
noncomputable def pullbackObjUnitToUnit :
    (pullback.{u} φ).obj (unit S) ⟶ unit R :=
  ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm (unitToPushforwardObjUnit φ)

@[simp]
/--
lemma `pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit` / 引理 `pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit`

English:
lemma pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit
  proof: rfl

@[simp]

中文:
引理 pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit
  证明: rfl

@[simp]
-/
lemma pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit :
    ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm (unitToPushforwardObjUnit φ) =
      pullbackObjUnitToUnit φ := rfl

@[simp]
/--
lemma `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit` / 引理 `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`

English:
lemma pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
  proof: Equiv.apply_symm_apply _ _

中文:
引理 pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
  证明: Equiv.apply_symm_apply _ _

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply
-/
lemma pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit :
    (pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (pullbackObjUnitToUnit φ) =
      unitToPushforwardObjUnit φ :=
  Equiv.apply_symm_apply _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Final]
  signature: : IsIso (pullbackObjUnitToUnit φ)
  body: by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).bijective.of_comp_iff']; rw [← (unitHomEquiv _).bijective.of_comp_iff']
  convert! (bijective_pushforwardSections φ M).comp (unitHomEquiv _).bijective
  ext f : 1
  dsimp
  rw [pushforwardSections_unitHomEquiv]; rw [EmbeddingLike.apply_eq_iff_eq]; rw [Adjunction.homEquiv_naturality_right]; rw [pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

中文:
实例 [F.终]
  签名: : 是同构 (pullbackObjUnitToUnit φ)
  定义体: by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).bijective.of_comp_iff']; rw [← (unitHomEquiv _).bijective.of_comp_iff']
  convert! (bijective_pushforwardSections φ M).comp (unitHomEquiv _).bijective
  ext f : 1
  dsimp
  rw [pushforwardSections_unitHomEquiv]; rw [EmbeddingLike.apply_eq_iff_eq]; rw [Adjunction.homEquiv_naturality_right]; rw [pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_right, EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, apply_eq_iff_eq, bijective, bijective.of_comp_iff, bijective_pushforwardSections, convert, homEquiv, homEquiv_naturality_right, isIso_iff_coyoneda_map_bijective, of_comp_iff, pullbackPushforwardAdjunction, pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit, pushforwardSections_unitHomEquiv, unitHomEquiv
-/
instance [F.Final] : IsIso (pullbackObjUnitToUnit φ) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).bijective.of_comp_iff']; rw [← (unitHomEquiv _).bijective.of_comp_iff']
  convert! (bijective_pushforwardSections φ M).comp (unitHomEquiv _).bijective
  ext f : 1
  dsimp
  rw [pushforwardSections_unitHomEquiv]; rw [EmbeddingLike.apply_eq_iff_eq]; rw [Adjunction.homEquiv_naturality_right]; rw [pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

variable [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.Final]

/--
Definition of `pullbackObjFreeIso` / `pullbackObjFreeIso` 的定义

English:
definition pullbackObjFreeIso
  signature: (I : Type u)
  body: (asIso (sigmaComparison _ _)).symm ≪≫
    Sigma.mapIso (fun _ => asIso (pullbackObjUnitToUnit φ))

中文:
定义 pullbackObjFreeIso
  签名: (I : 类型u)
  定义体: (asIso (sigmaComparison _ _)).symm ≪≫
    Sigma.mapIso (fun _ => asIso (pullbackObjUnitToUnit φ))

Depends on / 依赖: Sigma.mapIso, mapIso, pullbackObjUnitToUnit, sigmaComparison
-/
noncomputable def pullbackObjFreeIso (I : Type u) :
    (pullback φ).obj (free I) ≅ free I :=
  (asIso (sigmaComparison _ _)).symm ≪≫
    Sigma.mapIso (fun _ => asIso (pullbackObjUnitToUnit φ))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pullback_map_ιFree_comp_pullbackObjFreeIso_hom` / 引理 `pullback_map_ιFree_comp_pullbackObjFreeIso_hom`

English:
lemma pullback_map_ιFree_comp_pullbackObjFreeIso_hom
  given: {I : Type u} (i : I)
  proof: by
  simp [pullbackObjFreeIso, ιFree]

中文:
引理 pullback_map_ιFree_comp_pullbackObjFreeIso_hom
  条件: {I : 类型u} (i : I)
  证明: by
  simp [pullbackObjFreeIso, ιFree]

Depends on / 依赖: pullbackObjFreeIso
-/
lemma pullback_map_ιFree_comp_pullbackObjFreeIso_hom {I : Type u} (i : I) :
    (pullback φ).map (ιFree i) ≫ (pullbackObjFreeIso φ I).hom =
      pullbackObjUnitToUnit φ ≫ ιFree i := by
  simp [pullbackObjFreeIso, ιFree]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `pullbackObjFreeIso_hom_naturality` / 引理 `pullbackObjFreeIso_hom_naturality`

English:
lemma pullbackObjFreeIso_hom_naturality
  given: {I J : Type u} (f : I -> J)
  proof: Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (pullback φ) _ _
    (isColimitFreeCofan (R := S) I)) _ _ (fun i => by simp [← Functor.map_comp_assoc])

中文:
引理 pullbackObjFreeIso_hom_naturality
  条件: {I J : 类型u} (f : I -> J)
  证明: Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (pullback φ) _ _
    (isColimitFreeCofan (R := S) I)) _ _ (fun i => by simp [← Functor.map_comp_assoc])

Depends on / 依赖: Cofan.IsColimit.hom_ext, Functor, Functor.map_comp_assoc, IsColimit, hom_ext, isColimitCofanMkObjOfIsColimit, isColimitFreeCofan, map_comp_assoc, pullback
-/
lemma pullbackObjFreeIso_hom_naturality {I J : Type u} (f : I -> J) :
    (pullback φ).map (freeMap f) ≫ (pullbackObjFreeIso φ J).hom =
      (pullbackObjFreeIso φ I).hom ≫ freeMap f :=
  Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (pullback φ) _ _
    (isColimitFreeCofan (R := S) I)) _ _ (fun i => by simp [← Functor.map_comp_assoc])

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `freeFunctorCompPullbackIso` / `freeFunctorCompPullbackIso` 的定义

English:
definition freeFunctorCompPullbackIso
  signature: : freeFunctor ⋙ pullback φ ≅ freeFunctor
  body: NatIso.ofComponents (fun X => pullbackObjFreeIso φ X)

中文:
定义 freeFunctorCompPullbackIso
  签名: : freeFunctor ⋙ pullback φ ≅ freeFunctor
  定义体: NatIso.ofComponents (fun X => pullbackObjFreeIso φ X)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, pullbackObjFreeIso
-/
noncomputable def freeFunctorCompPullbackIso : freeFunctor ⋙ pullback φ ≅ freeFunctor :=
  NatIso.ofComponents (fun X => pullbackObjFreeIso φ X)

end SheafOfModules
