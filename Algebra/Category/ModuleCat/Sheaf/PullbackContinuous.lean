/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Pullback of sheaves of modules

Let `S` and `R` be sheaves of rings over sites `(C, J)` and `(D, K)` respectively.
Let `F : C ⥤ D` be a continuous functor between these sites, and
let `φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R` be a morphism
of sheaves of rings.

In this file, we define the pullback functor for sheaves of modules
`pullback.{v} φ : SheafOfModules.{v} S ⥤ SheafOfModules.{v} R`
that is left adjoint to `pushforward.{v} φ`. We show that it exists
under suitable assumptions, and prove that the pullback of (pre)sheaves of
modules commutes with the sheafification.

From the compatibility of `pushforward` with respect to composition, we deduce
similar pseudofunctor-like properties of the `pullback` functors.

-/

@[expose] public section

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Functor

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

section

variable [(pushforward.{v} φ).IsRightAdjoint]

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: : SheafOfModules.{v} S ⥤ SheafOfModules.{v} R
  body: (pushforward.{v} φ).leftAdjoint

中文:
定义 pullback
  签名: : 模层.{v} S ⥤ 模层.{v} R
  定义体: (pushforward.{v} φ).leftAdjoint

Depends on / 依赖: leftAdjoint, pushforward
-/
noncomputable def pullback : SheafOfModules.{v} S ⥤ SheafOfModules.{v} R :=
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
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pullback.{v} φ).IsLeftAdjoint
  body: (pullbackPushforwardAdjunction φ).isLeftAdjoint

中文:
实例 :
  签名: (pullback.{v} φ).是左伴随
  定义体: (pullbackPushforwardAdjunction φ).isLeftAdjoint

Depends on / 依赖: isLeftAdjoint, pullbackPushforwardAdjunction
-/
instance : (pullback.{v} φ).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction φ).isLeftAdjoint

end

section

variable [(PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

namespace PullbackConstruction

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `adjunction` / `adjunction` 的定义

English:
definition adjunction
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun F G =>
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).trans
            (((PresheafOfModules.pullbackPushforwardAdjunction φ.hom).homEquiv F.val G.val).trans
              ((fullyFaithfulForget S).homEquiv (Y := (pushforward φ).obj G)).symm)
      homEquiv_naturality_left_symm := by
        intros
        dsimp [Functor.FullyFaithful.homEquiv]
        -- these erw seem difficult to remove
        erw [Adjunction.homEquiv_naturality_left_symm,
          Adjunction.homEquiv_naturality_left_symm]
        dsimp [pushforward_obj_val]
        simp only [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        tauto }

中文:
定义 adjunction
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun F G =>
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).trans
            (((PresheafOfModules.pullbackPushforwardAdjunction φ.hom).homEquiv F.val G.val).trans
              ((fullyFaithfulForget S).homEquiv (Y := (pushforward φ).obj G)).symm)
      homEquiv_naturality_left_symm := by
        intros
        dsimp [Functor.FullyFaithful.homEquiv]
        -- these erw seem difficult to remove
        erw [Adjunction.homEquiv_naturality_left_symm,
          Adjunction.homEquiv_naturality_left_symm]
        dsimp [pushforward_obj_val]
        simp only [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        tauto }

Depends on / 依赖: R.obj, pushforward
-/
noncomputable def adjunction :
    (forget S ⋙ PresheafOfModules.pullback.{v} φ.hom ⋙
      PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)) ⊣ pushforward.{v} φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G =>
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).trans
            (((PresheafOfModules.pullbackPushforwardAdjunction φ.hom).homEquiv F.val G.val).trans
              ((fullyFaithfulForget S).homEquiv (Y := (pushforward φ).obj G)).symm)
      homEquiv_naturality_left_symm := by
        intros
        dsimp [Functor.FullyFaithful.homEquiv]
        -- these erw seem difficult to remove
        erw [Adjunction.homEquiv_naturality_left_symm,
          Adjunction.homEquiv_naturality_left_symm]
        dsimp [pushforward_obj_val]
        simp only [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        tauto }

end PullbackConstruction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pushforward.{v} φ).IsRightAdjoint
  body: (PullbackConstruction.adjunction.{v} φ).isRightAdjoint

中文:
实例 :
  签名: (pushforward.{v} φ).是右伴随
  定义体: (PullbackConstruction.adjunction.{v} φ).isRightAdjoint

Depends on / 依赖: PullbackConstruction, PullbackConstruction.adjunction, adjunction, isRightAdjoint
-/
instance : (pushforward.{v} φ).IsRightAdjoint :=
  (PullbackConstruction.adjunction.{v} φ).isRightAdjoint

/--
Definition of `pullbackIso` / `pullbackIso` 的定义

English:
definition pullbackIso
  signature: :
  body: Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction φ)
    (PullbackConstruction.adjunction φ)

中文:
定义 pullbackIso
  签名: :
  定义体: Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction φ)
    (PullbackConstruction.adjunction φ)

Depends on / 依赖: R.obj
-/
noncomputable def pullbackIso :
    pullback.{v} φ ≅
      forget S ⋙ PresheafOfModules.pullback.{v} φ.hom ⋙
        PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj) :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction φ)
    (PullbackConstruction.adjunction φ)

section

variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/--
Definition of `sheafificationCompPullback` / `sheafificationCompPullback` 的定义

English:
definition sheafificationCompPullback
  signature: :
  body: Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).comp
      (pullbackPushforwardAdjunction φ))
    ((PresheafOfModules.pullbackPushforwardAdjunction φ.hom).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)))

中文:
定义 sheafificationCompPullback
  签名: :
  定义体: Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).comp
      (pullbackPushforwardAdjunction φ))
    ((PresheafOfModules.pullbackPushforwardAdjunction φ.hom).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)))

Depends on / 依赖: R.obj
-/
noncomputable def sheafificationCompPullback :
    PresheafOfModules.sheafification (𝟙 S.obj) ⋙ pullback.{v} φ ≅
      PresheafOfModules.pullback.{v} φ.hom ⋙
        PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj) :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).comp
      (pullbackPushforwardAdjunction φ))
    ((PresheafOfModules.pullbackPushforwardAdjunction φ.hom).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)))

end

end


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pushforward.{v} (F := 𝟭 C) (𝟙 S)).IsRightAdjoint
  body: Functor.isRightAdjoint_of_iso (pushforwardId S).symm

中文:
实例 :
  签名: (pushforward.{v} (F := 𝟭 C) (𝟙 S)).是右伴随
  定义体: Functor.isRightAdjoint_of_iso (pushforwardId S).symm

Depends on / 依赖: IsRightAdjoint
-/
instance : (pushforward.{v} (F := 𝟭 C) (𝟙 S)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardId S).symm

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

variable (S) in
@[simp]
/--
lemma `conjugateEquiv_pullbackId_hom` / 引理 `conjugateEquiv_pullbackId_hom`

English:
lemma conjugateEquiv_pullbackId_hom
  proof: Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _

中文:
引理 conjugateEquiv_pullbackId_hom
  证明: Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _

Depends on / 依赖: Adjunction, Adjunction.conjugateEquiv_leftAdjointIdIso_hom, conjugateEquiv_leftAdjointIdIso_hom
-/
lemma conjugateEquiv_pullbackId_hom :
    conjugateEquiv .id (pullbackPushforwardAdjunction.{v} _) (pullbackId S).hom =
      (pushforwardId S).inv :=
  Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _

variable [(pushforward.{v} φ).IsRightAdjoint]

section

variable {K' : GrothendieckTopology D'} {K'' : GrothendieckTopology D''}
  {G : D ⥤ D'} {R' : Sheaf K' RingCat.{u}}
  [Functor.IsContinuous G K K']
  [Functor.IsContinuous (F ⋙ G) J K']
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')

variable [(pushforward.{v} ψ).IsRightAdjoint]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pushforward.{v} (F := F ⋙ G)
  body: Functor.isRightAdjoint_of_iso (pushforwardComp.{v} φ ψ)

中文:
实例 :
  签名: (pushforward.{v} (F := F ⋙ G)
  定义体: Functor.isRightAdjoint_of_iso (pushforwardComp.{v} φ ψ)
-/
instance : (pushforward.{v} (F := F ⋙ G)
    (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardComp.{v} φ ψ)

/--
Definition of `pullbackComp` / `pullbackComp` 的定义

English:
definition pullbackComp
  signature: :
  body: Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction.{v} φ) (pullbackPushforwardAdjunction.{v} ψ)
    (pullbackPushforwardAdjunction.{v} (F := F ⋙ G)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
    (pushforwardComp φ ψ)

@[simp]

中文:
定义 pullbackComp
  签名: :
  定义体: Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction.{v} φ) (pullbackPushforwardAdjunction.{v} ψ)
    (pullbackPushforwardAdjunction.{v} (F := F ⋙ G)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
    (pushforwardComp φ ψ)

@[simp]

Depends on / 依赖: F.sheafPushforwardContinuous, RingCat, sheafPushforwardContinuous
-/
noncomputable def pullbackComp :
    pullback.{v} φ ⋙ pullback.{v} ψ ≅
      pullback.{v} (F := F ⋙ G) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) :=
  Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction.{v} φ) (pullbackPushforwardAdjunction.{v} ψ)
    (pullbackPushforwardAdjunction.{v} (F := F ⋙ G)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
    (pushforwardComp φ ψ)

@[simp]
/--
lemma `conjugateEquiv_pullbackComp_inv` / 引理 `conjugateEquiv_pullbackComp_inv`

English:
lemma conjugateEquiv_pullbackComp_inv
  proof: Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

中文:
引理 conjugateEquiv_pullbackComp_inv
  证明: Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

Depends on / 依赖: Adjunction, Adjunction.conjugateEquiv_leftAdjointCompIso_inv, conjugateEquiv_leftAdjointCompIso_inv
-/
lemma conjugateEquiv_pullbackComp_inv :
    conjugateEquiv ((pullbackPushforwardAdjunction.{v} φ).comp
      (pullbackPushforwardAdjunction.{v} ψ))
    (pullbackPushforwardAdjunction.{v} _) (pullbackComp.{v} φ ψ).inv =
    (pushforwardComp.{v} φ ψ).hom :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

variable {G' : D' ⥤ D''} {R'' : Sheaf K'' RingCat.{u}}
  [Functor.IsContinuous G' K' K'']
  [Functor.IsContinuous (G ⋙ G') K K'']
  [Functor.IsContinuous ((F ⋙ G) ⋙ G') J K'']
  [Functor.IsContinuous (F ⋙ G ⋙ G') J K'']
  (ψ' : R' ⟶ (G'.sheafPushforwardContinuous RingCat.{u} K' K'').obj R'')

variable [(pushforward.{v} ψ').IsRightAdjoint]

/--
lemma `pullback_assoc` / 引理 `pullback_assoc`

English:
lemma pullback_assoc
  proof: Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (pushforward_assoc φ ψ ψ')

中文:
引理 pullback_assoc
  证明: Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (pushforward_assoc φ ψ ψ')
-/
lemma pullback_assoc :
    isoWhiskerLeft _ (pullbackComp.{v} ψ ψ') ≪≫
      pullbackComp.{v} (G := G ⋙ G') φ
        (ψ ≫ (G.sheafPushforwardContinuous RingCat.{u} K K').map ψ') =
    (associator _ _ _).symm ≪≫ isoWhiskerRight (pullbackComp.{v} φ ψ) _ ≪≫
      pullbackComp.{v} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) ψ' :=
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

end SheafOfModules
