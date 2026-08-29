/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Pullback of presheaves of modules

Let `F : C ⥤ D` be a functor, `R : Dᵒᵖ ⥤ RingCat` and `S : Cᵒᵖ ⥤ RingCat` be presheaves
of rings, and `φ : S ⟶ F.op ⋙ R` be a morphism of presheaves of rings,
we introduce the pullback functor `pullback : PresheafOfModules S ⥤ PresheafOfModules R`
as the left adjoint of `pushforward : PresheafOfModules R ⥤ PresheafOfModules S`.
The existence of this left adjoint functor is obtained under suitable universe assumptions.

From the compatibility of `pushforward` with respect to composition, we deduce
similar pseudofunctor-like properties of the `pullback` functors.

-/

@[expose] public section

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Limits Opposite Functor

namespace PresheafOfModules

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  [(pushforward.{v} φ).IsRightAdjoint]

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: : PresheafOfModules.{v} S ⥤ PresheafOfModules.{v} R
  body: (pushforward.{v} φ).leftAdjoint

中文:
定义 pullback
  签名: : 预模层.{v} S ⥤ 预模层.{v} R
  定义体: (pushforward.{v} φ).leftAdjoint

Depends on / 依赖: leftAdjoint, pushforward
-/
noncomputable def pullback : PresheafOfModules.{v} S ⥤ PresheafOfModules.{v} R :=
  (pushforward.{v} φ).leftAdjoint

/--
Definition of `pullbackPushforwardAdjunction` / `pullbackPushforwardAdjunction` 的定义

English:
definition pullbackPushforwardAdjunction
  signature: : pullback.{v} φ ⊣ pushforward.{v} φ
  body: Adjunction.ofIsRightAdjoint (pushforward φ)

中文:
定义 pullbackPushforwardAdjunction
  签名: : pullback.{v} φ ⊣ pushforward.{v} φ
  定义体: Adjunction.ofIsRightAdjoint (pushforward φ)

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, ofIsRightAdjoint, pushforward
-/
noncomputable def pullbackPushforwardAdjunction : pullback.{v} φ ⊣ pushforward.{v} φ :=
  Adjunction.ofIsRightAdjoint (pushforward φ)

/--
Definition of `pullbackObjIsDefined` / `pullbackObjIsDefined` 的定义

English:
abbreviation pullbackObjIsDefined
  signature: : ObjectProperty (PresheafOfModules.{v} S)
  body: (pushforward φ).leftAdjointObjIsDefined

中文:
缩写 pullbackObjIsDefined
  签名: : ObjectProperty (预模层.{v} S)
  定义体: (pushforward φ).leftAdjointObjIsDefined

Depends on / 依赖: leftAdjointObjIsDefined, pushforward
-/
abbrev pullbackObjIsDefined : ObjectProperty (PresheafOfModules.{v} S) :=
  (pushforward φ).leftAdjointObjIsDefined

end

section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/--
Definition of `pushforwardCompCoyonedaFreeYonedaCorepresentableBy` / `pushforwardCompCoyonedaFreeYonedaCorepresentableBy` 的定义

English:
definition pushforwardCompCoyonedaFreeYonedaCorepresentableBy
  signature: (X : C)
  body: freeYonedaEquiv.trans
    (freeYonedaEquiv (M := (pushforward φ).obj M)).symm
  homEquiv_comp {M N} g f := freeYonedaEquiv.injective (by
    dsimp
    erw [Equiv.apply_symm_apply, freeYonedaEquiv_comp]
    conv_rhs => erw [freeYonedaEquiv_comp]
    erw [Equiv.apply_symm_apply]
    rfl)

中文:
定义 pushforwardCompCoyonedaFreeYonedaCorepresentableBy
  签名: (X : C)
  定义体: freeYonedaEquiv.trans
    (freeYonedaEquiv (M := (pushforward φ).obj M)).symm
  homEquiv_comp {M N} g f := freeYonedaEquiv.injective (by
    dsimp
    erw [Equiv.apply_symm_apply, freeYonedaEquiv_comp]
    conv_rhs => erw [freeYonedaEquiv_comp]
    erw [Equiv.apply_symm_apply]
    rfl)

Depends on / 依赖: freeYonedaEquiv, freeYonedaEquiv.trans
-/
noncomputable def pushforwardCompCoyonedaFreeYonedaCorepresentableBy (X : C) :
    (pushforward φ ⋙ coyoneda.obj (op ((free S).obj (yoneda.obj X)))).CorepresentableBy
      ((free R).obj (yoneda.obj (F.obj X))) where
  homEquiv {M} := freeYonedaEquiv.trans
    (freeYonedaEquiv (M := (pushforward φ).obj M)).symm
  homEquiv_comp {M N} g f := freeYonedaEquiv.injective (by
    dsimp
    erw [Equiv.apply_symm_apply, freeYonedaEquiv_comp]
    conv_rhs => erw [freeYonedaEquiv_comp]
    erw [Equiv.apply_symm_apply]
    rfl)

/--
lemma `pullbackObjIsDefined_free_yoneda` / 引理 `pullbackObjIsDefined_free_yoneda`

English:
lemma pullbackObjIsDefined_free_yoneda
  given: (X : C)
  proof: (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).isCorepresentable

中文:
引理 pullbackObjIsDefined_free_yoneda
  条件: (X : C)
  证明: (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).isCorepresentable

Depends on / 依赖: isCorepresentable, pushforwardCompCoyonedaFreeYonedaCorepresentableBy
-/
lemma pullbackObjIsDefined_free_yoneda (X : C) :
    pullbackObjIsDefined φ ((free S).obj (yoneda.obj X)) :=
  (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).isCorepresentable

/--
lemma `pullbackObjIsDefined_eq_top` / 引理 `pullbackObjIsDefined_eq_top`

English:
lemma pullbackObjIsDefined_eq_top
  proof: by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply leftAdjointObjIsDefined_of_isColimit
    M.isColimitFreeYonedaCoproductsCokernelCofork
  rintro (_ | _)
  all_goals
    apply leftAdjointObjIsDefined_colimit _
      (fun _ => pullbackObjIsDefined_free_yoneda _ _)

中文:
引理 pullbackObjIsDefined_eq_top
  证明: by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply leftAdjointObjIsDefined_of_isColimit
    M.isColimitFreeYonedaCoproductsCokernelCofork
  rintro (_ | _)
  all_goals
    apply leftAdjointObjIsDefined_colimit _
      (fun _ => pullbackObjIsDefined_free_yoneda _ _)

Depends on / 依赖: M.isColimitFreeYonedaCoproductsCokernelCofork, Pi.top_apply, Prop.top_eq_true, all_goals, iff_true, isColimitFreeYonedaCoproductsCokernelCofork, leftAdjointObjIsDefined_colimit, leftAdjointObjIsDefined_of_isColimit, pullbackObjIsDefined_free_yoneda, top_apply, top_eq_true
-/
lemma pullbackObjIsDefined_eq_top :
    pullbackObjIsDefined.{u} φ = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply leftAdjointObjIsDefined_of_isColimit
    M.isColimitFreeYonedaCoproductsCokernelCofork
  rintro (_ | _)
  all_goals
    apply leftAdjointObjIsDefined_colimit _
      (fun _ => pullbackObjIsDefined_free_yoneda _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pushforward.{u} φ).IsRightAdjoint
  body: isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (pullbackObjIsDefined_eq_top φ)

中文:
实例 :
  签名: (pushforward.{u} φ).是右伴随
  定义体: isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (pullbackObjIsDefined_eq_top φ)

Depends on / 依赖: isRightAdjoint_of_leftAdjointObjIsDefined_eq_top, pullbackObjIsDefined_eq_top
-/
instance : (pushforward.{u} φ).IsRightAdjoint :=
  isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (pullbackObjIsDefined_eq_top φ)

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  {G : D ⥤ E} {T : Eᵒᵖ ⥤ RingCat.{u}} (ψ : R ⟶ G.op ⋙ T)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pushforward.{v} (F := 𝟭 C) (𝟙 S)).IsRightAdjoint
  body: isRightAdjoint_of_iso (pushforwardId.{v} S).symm

中文:
实例 :
  签名: (pushforward.{v} (F := 𝟭 C) (𝟙 S)).是右伴随
  定义体: isRightAdjoint_of_iso (pushforwardId.{v} S).symm

Depends on / 依赖: IsRightAdjoint
-/
instance : (pushforward.{v} (F := 𝟭 C) (𝟙 S)).IsRightAdjoint :=
  isRightAdjoint_of_iso (pushforwardId.{v} S).symm

variable (S) in
/--
Definition of `pullbackId` / `pullbackId` 的定义

English:
definition pullbackId
  signature: : pullback.{v} (F := 𝟭 C) (𝟙 S) ≅ 𝟭 _
  body: ((pullbackPushforwardAdjunction.{v} (F := 𝟭 C) (𝟙 S))).leftAdjointIdIso (pushforwardId S)

中文:
定义 pullbackId
  签名: : pullback.{v} (F := 𝟭 C) (𝟙 S) ≅ 𝟭 _
  定义体: ((pullbackPushforwardAdjunction.{v} (F := 𝟭 C) (𝟙 S))).leftAdjointIdIso (pushforwardId S)
-/
noncomputable def pullbackId : pullback.{v} (F := 𝟭 C) (𝟙 S) ≅ 𝟭 _ :=
  ((pullbackPushforwardAdjunction.{v} (F := 𝟭 C) (𝟙 S))).leftAdjointIdIso (pushforwardId S)

variable [(pushforward.{v} φ).IsRightAdjoint]

section

variable [(pushforward.{v} ψ).IsRightAdjoint]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pushforward.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ)).IsRightAdjoint
  body: isRightAdjoint_of_iso (pushforwardComp.{v} φ ψ)

中文:
实例 :
  签名: (pushforward.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ)).是右伴随
  定义体: isRightAdjoint_of_iso (pushforwardComp.{v} φ ψ)

Depends on / 依赖: F.op, IsRightAdjoint, whiskerLeft
-/
instance : (pushforward.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ)).IsRightAdjoint :=
  isRightAdjoint_of_iso (pushforwardComp.{v} φ ψ)

/--
Definition of `pullbackComp` / `pullbackComp` 的定义

English:
definition pullbackComp
  signature: :
  body: Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction.{v} φ) (pullbackPushforwardAdjunction.{v} ψ)
    (pullbackPushforwardAdjunction.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ))
    (pushforwardComp φ ψ)

中文:
定义 pullbackComp
  签名: :
  定义体: Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction.{v} φ) (pullbackPushforwardAdjunction.{v} ψ)
    (pullbackPushforwardAdjunction.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ))
    (pushforwardComp φ ψ)

Depends on / 依赖: F.op, whiskerLeft
-/
noncomputable def pullbackComp :
    pullback.{v} φ ⋙ pullback.{v} ψ ≅
      pullback.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) :=
  Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction.{v} φ) (pullbackPushforwardAdjunction.{v} ψ)
    (pullbackPushforwardAdjunction.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ))
    (pushforwardComp φ ψ)

variable {T' : E'ᵒᵖ ⥤ RingCat.{u}} {G' : E ⥤ E'} (ψ' : T ⟶ G'.op ⋙ T')
  [(pushforward.{v} ψ').IsRightAdjoint]

/--
lemma `pullback_assoc` / 引理 `pullback_assoc`

English:
lemma pullback_assoc
  proof: Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (pushforward_assoc φ ψ ψ')

中文:
引理 pullback_assoc
  证明: Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (pushforward_assoc φ ψ ψ')

Depends on / 依赖: G.op, whiskerLeft
-/
lemma pullback_assoc :
    isoWhiskerLeft _ (pullbackComp.{v} ψ ψ') ≪≫
      pullbackComp.{v} (G := G ⋙ G') φ (ψ ≫ whiskerLeft G.op ψ') =
    (associator _ _ _).symm ≪≫ isoWhiskerRight (pullbackComp.{v} φ ψ) _ ≪≫
        pullbackComp.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) ψ' :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (pushforward_assoc φ ψ ψ')

end

/--
lemma `pullback_id_comp` / 引理 `pullback_id_comp`

English:
lemma pullback_id_comp
  proof: Adjunction.leftAdjointCompIso_id_comp _ _ _ _ (pushforward_comp_id φ)

中文:
引理 pullback_id_comp
  证明: Adjunction.leftAdjointCompIso_id_comp _ _ _ _ (pushforward_comp_id φ)
-/
lemma pullback_id_comp :
    pullbackComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerRight (pullbackId S) (pullback φ) ≪≫ Functor.leftUnitor _ :=
  Adjunction.leftAdjointCompIso_id_comp _ _ _ _ (pushforward_comp_id φ)

/--
lemma `pullback_comp_id` / 引理 `pullback_comp_id`

English:
lemma pullback_comp_id
  proof: Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (pushforward_id_comp φ)

中文:
引理 pullback_comp_id
  证明: Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (pushforward_id_comp φ)
-/
lemma pullback_comp_id :
    pullbackComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      isoWhiskerLeft _ (pullbackId R) ≪≫ Functor.rightUnitor _ :=
  Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (pushforward_id_comp φ)

end

end PresheafOfModules
