/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

/-!
# Pushforward of presheaves of modules

If `F : C ⥤ D`, the precomposition `F.op ⋙ _` induces a functor from presheaves
over `D` to presheaves over `C`. When `R : Dᵒᵖ ⥤ RingCat`, we define the
induced functor `pushforward₀ : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R)`
on presheaves of modules.

In case we have a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, we also construct
a functor `pushforward : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S`, and
we show that they interact with the composition of morphisms similarly as pseudofunctors.

-/

@[expose] public section

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

namespace PresheafOfModules

variable (F : C ⥤ D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `pushforward₀`. -/
@[simps]
/--
Definition of `pushforward₀Obj` / `pushforward₀Obj` 的定义

English:
definition pushforward₀Obj
  signature: (R : Dᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules R)
  body: { obj X := ModuleCat.of _ (M.obj (F.op.obj X))
    map {X Y} f := M.map (F.op.map f)
    map_id X := by
      refine ModuleCat.hom_ext
        -- Work around an instance diamond for `restrictScalarsId'`
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
      exact (M.congr_map_app

中文:
定义 pushforward₀Obj
  签名: (R : Dᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules R)
  定义体: { obj X := ModuleCat.of _ (M.obj (F.op.obj X))
    map {X Y} f := M.map (F.op.map f)
    map_id X := by
      refine ModuleCat.hom_ext
        -- Work around an instance diamond for `restrictScalarsId'`
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
      exact (M.congr_map_app

Depends on / 依赖: F.op.map, F.op.obj, M.map, M.obj, ModuleCat, ModuleCat.hom_ext, ModuleCat.of, hom_ext, map_id
-/
def pushforward₀Obj (R : Dᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules R) :
    PresheafOfModules (F.op ⋙ R) :=
  { obj X := ModuleCat.of _ (M.obj (F.op.obj X))
    map {X Y} f := M.map (F.op.map f)
    map_id X := by
      refine ModuleCat.hom_ext
        -- Work around an instance diamond for `restrictScalarsId'`
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
      exact (M.congr_map_apply (F.op.map_id X) x).trans (by simp)
    map_comp := fun f g => by
      refine ModuleCat.hom_ext
        -- Work around an instance diamond for `restrictScalarsId'`
        (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
      exact (M.congr_map_apply (F.op.map_comp f g) x).trans (by simp) }

@[deprecated (since := "2026-04-27")] alias pushforward₀_obj := pushforward₀Obj

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pushforward₀` / `pushforward₀` 的定义

English:
definition pushforward₀
  signature: (R : Dᵒᵖ ⥤ RingCat.{u})
  body: pushforward₀Obj F R M
  map {M₁ M₂} φ := { app X := φ.app _ }

中文:
定义 pushforward₀
  签名: (R : Dᵒᵖ ⥤ RingCat.{u})
  定义体: pushforward₀Obj F R M
  map {M₁ M₂} φ := { app X := φ.app _ }
-/
def pushforward₀ (R : Dᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R) where
  obj M := pushforward₀Obj F R M
  map {M₁ M₂} φ := { app X := φ.app _ }

/--
Definition of `pushforward₀OfCommRingCat` / `pushforward₀OfCommRingCat` 的定义

English:
abbreviation pushforward₀OfCommRingCat
  signature: (R : Dᵒᵖ ⥤ CommRingCat.{u})
  body: pushforward₀ F (R ⋙ forget₂ _ _)

中文:
缩写 pushforward₀OfCommRingCat
  签名: (R : Dᵒᵖ ⥤ CommRingCat.{u})
  定义体: pushforward₀ F (R ⋙ forget₂ _ _)
-/
abbrev pushforward₀OfCommRingCat (R : Dᵒᵖ ⥤ CommRingCat.{u}) :
    PresheafOfModules.{v} (R ⋙ forget₂ _ _) ⥤
      PresheafOfModules.{v} ((F.op ⋙ R) ⋙ forget₂ _ _) :=
  pushforward₀ F (R ⋙ forget₂ _ _)

/--
Definition of `pushforward₀CompToPresheaf` / `pushforward₀CompToPresheaf` 的定义

English:
definition pushforward₀CompToPresheaf
  signature: (R : Dᵒᵖ ⥤ RingCat.{u})
  body: Iso.refl _

中文:
定义 pushforward₀CompToPresheaf
  签名: (R : Dᵒᵖ ⥤ RingCat.{u})
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def pushforward₀CompToPresheaf (R : Dᵒᵖ ⥤ RingCat.{u}) :
    pushforward₀.{v} F R ⋙ toPresheaf _ ≅ toPresheaf _ ⋙ (whiskeringLeft _ _ _).obj F.op :=
  Iso.refl _

variable {F}
variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

attribute [local simp] pushforward₀ in
/-- The pushforward functor `PresheafOfModules R ⥤ PresheafOfModules S` induced by
a morphism of presheaves of rings `S ⟶ F.op ⋙ R`. -/
@[simps! obj_obj]
/--
Definition of `pushforward` / `pushforward` 的定义

English:
definition pushforward
  signature: : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S
  body: pushforward₀ F R ⋙ restrictScalars φ

中文:
定义 pushforward
  签名: : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S
  定义体: pushforward₀ F R ⋙ restrictScalars φ

Depends on / 依赖: restrictScalars
-/
noncomputable def pushforward : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S :=
  pushforward₀ F R ⋙ restrictScalars φ

/--
lemma `forget₂_map_pushforward_obj_map` / 引理 `forget₂_map_pushforward_obj_map`

English:
lemma forget₂_map_pushforward_obj_map
  given: {U V : Cᵒᵖ} (f : U ⟶ V) (M : PresheafOfModules R)
  proof: rfl

中文:
引理 forget₂_map_pushforward_obj_map
  条件: {U V : Cᵒᵖ} (f : U ⟶ V) (M : PresheafOfModules R)
  证明: rfl
-/
lemma forget₂_map_pushforward_obj_map {U V : Cᵒᵖ} (f : U ⟶ V) (M : PresheafOfModules R) :
    (forget₂ _ Ab).map (((PresheafOfModules.pushforward φ).obj M).map f) =
      M.presheaf.map (F.map f.unop).op :=
  rfl

/--
lemma `forget₂_map_pushforward_map_app` / 引理 `forget₂_map_pushforward_map_app`

English:
lemma forget₂_map_pushforward_map_app
  given: {U : Cᵒᵖ} {M N : PresheafOfModules _} (g : M ⟶ N)
  proof: rfl

中文:
引理 forget₂_map_pushforward_map_app
  条件: {U : Cᵒᵖ} {M N : PresheafOfModules _} (g : M ⟶ N)
  证明: rfl
-/
lemma forget₂_map_pushforward_map_app {U : Cᵒᵖ} {M N : PresheafOfModules _} (g : M ⟶ N) :
    (forget₂ _ Ab).map (((pushforward φ).map g).app U) = (forget₂ _ Ab).map (g.app _) :=
  rfl

/--
Definition of `pushforwardCompToPresheaf` / `pushforwardCompToPresheaf` 的定义

English:
definition pushforwardCompToPresheaf
  signature: :
  body: Iso.refl _

中文:
定义 pushforwardCompToPresheaf
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def pushforwardCompToPresheaf :
    pushforward.{v} φ ⋙ toPresheaf _ ≅ toPresheaf _ ⋙ (whiskeringLeft _ _ _).obj F.op :=
  Iso.refl _

/--
lemma `pushforward_obj_map_apply` / 引理 `pushforward_obj_map_apply`

English:
lemma pushforward_obj_map_apply
  statement: (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: rfl

中文:
引理 pushforward_obj_map_apply
  结论: (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: rfl
-/
lemma pushforward_obj_map_apply (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      (((pushforward φ).obj M).map f).hom m = M.map (F.map f.unop).op m := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `@[simp]`-normal form of `pushforward_obj_map_apply`. -/
@[simp]
/--
lemma `pushforward_obj_map_apply'` / 引理 `pushforward_obj_map_apply'`

English:
lemma pushforward_obj_map_apply'
  statement: (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: rfl

中文:
引理 pushforward_obj_map_apply'
  结论: (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: rfl

Depends on / 依赖: F.obj, IsZero, IsZero.of_full_of_faithful_of_isZero, ModuleCat, ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_of_subsingleton, ModuleCat.restrictScalars, isZero_iff_subsingleton, isZero_of_subsingleton, not_iff_not, not_subsingleton_iff_nontrivial, of_full_of_faithful_of_isZero, restrictScalars
-/
lemma pushforward_obj_map_apply' (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      DFunLike.coe
        (F := ↑((ModuleCat.restrictScalars _).obj _) ->ₗ[_]
          ↑((ModuleCat.restrictScalars (S.map f).hom).obj ((ModuleCat.restrictScalars _).obj _)))
        (((pushforward φ).obj M).map f).hom m = M.map (F.map f.unop).op m := rfl

/--
lemma `pushforward_map_app_apply` / 引理 `pushforward_map_app_apply`

English:
lemma pushforward_map_app_apply
  statement: {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
  proof: rfl

中文:
引理 pushforward_map_app_apply
  结论: {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
  证明: rfl
-/
lemma pushforward_map_app_apply {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    (((pushforward φ).map α).app X).hom m = α.app (Opposite.op (F.obj X.unop)) m := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `@[simp]`-normal form of `pushforward_map_app_apply`. -/
@[simp]
/--
lemma `pushforward_map_app_apply'` / 引理 `pushforward_map_app_apply'`

English:
lemma pushforward_map_app_apply'
  statement: {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
  proof: rfl

中文:
引理 pushforward_map_app_apply'
  结论: {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
  证明: rfl

Depends on / 依赖: ModuleCat, ModuleCat.restrictScalars, restrictScalars
-/
lemma pushforward_map_app_apply' {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    DFunLike.coe
      (F := ↑((ModuleCat.restrictScalars _).obj _) ->ₗ[_] ↑((ModuleCat.restrictScalars _).obj _))
      (((pushforward φ).map α).app X).hom m = α.app (Opposite.op (F.obj X.unop)) m := rfl

section

variable (R) in
/--
Definition of `pushforwardId` / `pushforwardId` 的定义

English:
definition pushforwardId
  signature: :
  body: Iso.refl _

中文:
定义 pushforwardId
  签名: :
  定义体: Iso.refl _
-/
noncomputable def pushforwardId :
    pushforward.{v} (S := R) (F := 𝟭 _) (𝟙 R) ≅ 𝟭 _ :=
  Iso.refl _

section

variable {T : Eᵒᵖ ⥤ RingCat.{u}} {G : D ⥤ E} (ψ : R ⟶ G.op ⋙ T)

/--
Definition of `pushforwardComp` / `pushforwardComp` 的定义

English:
definition pushforwardComp
  signature: :
  body: Iso.refl _

中文:
定义 pushforwardComp
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: F.op, whiskerLeft
-/
noncomputable def pushforwardComp :
    pushforward.{v} ψ ⋙ pushforward.{v} φ ≅
      pushforward.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) :=
  Iso.refl _

variable {T' : E'ᵒᵖ ⥤ RingCat.{u}} {G' : E ⥤ E'} (ψ' : T ⟶ G'.op ⋙ T')

/--
lemma `pushforward_assoc` / 引理 `pushforward_assoc`

English:
lemma pushforward_assoc
  proof: by ext; rfl

中文:
引理 pushforward_assoc
  证明: by ext; rfl

Depends on / 依赖: F.op.whiskerLeft, whiskerLeft
-/
lemma pushforward_assoc :
    (pushforward ψ').isoWhiskerLeft (pushforwardComp φ ψ) ≪≫
      pushforwardComp (F := F ⋙ G) (φ ≫ F.op.whiskerLeft ψ) ψ' =
    ((pushforward ψ').associator (pushforward ψ) (pushforward φ)).symm ≪≫
      isoWhiskerRight (pushforwardComp ψ ψ') (pushforward φ) ≪≫
        pushforwardComp (G := G ⋙ G') φ (ψ ≫ G.op.whiskerLeft ψ') := by ext; rfl

end

/--
lemma `pushforward_comp_id` / 引理 `pushforward_comp_id`

English:
lemma pushforward_comp_id
  proof: by ext; rfl

中文:
引理 pushforward_comp_id
  证明: by ext; rfl
-/
lemma pushforward_comp_id :
    pushforwardComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerLeft (pushforward.{v} φ) (pushforwardId S) ≪≫ rightUnitor _ := by ext; rfl

/--
lemma `pushforward_id_comp` / 引理 `pushforward_id_comp`

English:
lemma pushforward_id_comp
  proof: by ext; rfl

中文:
引理 pushforward_id_comp
  证明: by ext; rfl
-/
lemma pushforward_id_comp :
    pushforwardComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      isoWhiskerRight (pushforwardId R) (pushforward.{v} φ) ≪≫ leftUnitor _ := by ext; rfl

end

end PresheafOfModules
