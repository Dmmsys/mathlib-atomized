/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Pushforward of sheaves of modules

Assume that categories `C` and `D` are equipped with Grothendieck topologies, and
that `F : C ⥤ D` is a continuous functor.
Then, if `φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R` is
a morphism of sheaves of rings, we construct the pushforward functor
`pushforward φ : SheafOfModules.{v} R ⥤ SheafOfModules.{v} S`, and
we show that they interact with the composition of morphisms similarly as pseudofunctors.

-/

@[expose] public section

universe w v' u' v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Functor Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The pushforward of sheaves of modules that is induced by a continuous functor `F`
and a morphism of sheaves of rings `φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R`. -/
@[simps map_val, simps -isSimp obj_val]
/--
Definition of `pushforward` / `pushforward` 的定义

English:
definition pushforward
  signature: : SheafOfModules.{v} R ⥤ SheafOfModules.{v} S where
  body: { val := (PresheafOfModules.pushforward φ.hom).obj M.val
      isSheaf := ((F.sheafPushforwardContinuous _ J K).obj ⟨_, M.isSheaf⟩).property }
  map f :=
    { val := (PresheafOfModules.pushforward φ.hom).map f.val }

中文:
定义 pushforward
  签名: : 模层.{v} R ⥤ 模层.{v} S where
  定义体: { val := (PresheafOfModules.pushforward φ.hom).obj M.val
      isSheaf := ((F.sheafPushforwardContinuous _ J K).obj ⟨_, M.isSheaf⟩).property }
  map f :=
    { val := (PresheafOfModules.pushforward φ.hom).map f.val }

Depends on / 依赖: F.sheafPushforwardContinuous, M.isSheaf, M.val, PresheafOfModules, PresheafOfModules.pushforward, f.val, isSheaf, property, pushforward, sheafPushforwardContinuous
-/
noncomputable def pushforward : SheafOfModules.{v} R ⥤ SheafOfModules.{v} S where
  obj M :=
    { val := (PresheafOfModules.pushforward φ.hom).obj M.val
      isSheaf := ((F.sheafPushforwardContinuous _ J K).obj ⟨_, M.isSheaf⟩).property }
  map f :=
    { val := (PresheafOfModules.pushforward φ.hom).map f.val }

/--
lemma `forget₂_map_pushforward_obj_val_map` / 引理 `forget₂_map_pushforward_obj_val_map`

English:
lemma forget₂_map_pushforward_obj_val_map
  given: {U V : Cᵒᵖ} (f : U ⟶ V) (M)
  proof: rfl

中文:
引理 forget₂_map_pushforward_obj_val_map
  条件: {U V : Cᵒᵖ} (f : U ⟶ V) (M)
  证明: rfl
-/
lemma forget₂_map_pushforward_obj_val_map {U V : Cᵒᵖ} (f : U ⟶ V) (M) :
    (forget₂ _ Ab).map (((pushforward.{v} φ).obj M).val.map f) =
      M.val.presheaf.map (F.map f.unop).op :=
  rfl

variable (R) in
/--
Definition of `overFunctor` / `overFunctor` 的定义

English:
definition overFunctor
  signature: (X : D)
  body: pushforward (𝟙 _)

中文:
定义 overFunctor
  签名: (X : D)
  定义体: pushforward (𝟙 _)

Depends on / 依赖: pushforward
-/
noncomputable def overFunctor (X : D) :
    SheafOfModules.{v} R ⥤ SheafOfModules.{v} (R.over X) :=
  pushforward (𝟙 _)

/--
Definition of `over` / `over` 的定义

English:
abbreviation over
  signature: (M : SheafOfModules.{v} R) (X : D)
  body: (overFunctor R X).obj M

中文:
缩写 over
  签名: (M : 模层.{v} R) (X : D)
  定义体: (overFunctor R X).obj M

Depends on / 依赖: overFunctor
-/
noncomputable abbrev over (M : SheafOfModules.{v} R) (X : D) : SheafOfModules.{v} (R.over X) :=
  (overFunctor R X).obj M

/--
Definition of `Hom.over` / `Hom.over` 的定义

English:
abbreviation Hom.over
  signature: {M N : SheafOfModules.{v} R} (f : M ⟶ N) (X : D)
  body: (overFunctor R X).map f

中文:
缩写 态射.over
  签名: {M N : 模层.{v} R} (f : M ⟶ N) (X : D)
  定义体: (overFunctor R X).map f

Depends on / 依赖: overFunctor
-/
noncomputable abbrev Hom.over {M N : SheafOfModules.{v} R} (f : M ⟶ N) (X : D) :
    M.over X ⟶ N.over X :=
  (overFunctor R X).map f

variable (R) in
/--
Definition of `overMap` / `overMap` 的定义

English:
definition overMap
  signature: {X Y : D} (f : X ⟶ Y)
  body: pushforward (F := Over.map f) (Sheaf.pushforwardOverMapIso R f).inv

中文:
定义 overMap
  签名: {X Y : D} (f : X ⟶ Y)
  定义体: pushforward (F := Over.map f) (Sheaf.pushforwardOverMapIso R f).inv

Depends on / 依赖: Over.map, Sheaf.pushforwardOverMapIso, pushforward, pushforwardOverMapIso
-/
noncomputable def overMap {X Y : D} (f : X ⟶ Y) :
    SheafOfModules.{v} (R.over Y) ⥤ SheafOfModules.{v} (R.over X) :=
  pushforward (F := Over.map f) (Sheaf.pushforwardOverMapIso R f).inv

variable (R) in
/--
Definition of `overFunctorMap` / `overFunctorMap` 的定义

English:
definition overFunctorMap
  signature: {X Y : D} (f : X ⟶ Y)
  body: NatIso.ofComponents
fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
      PresheafOfModules.isoMk (fun U => Iso.refl _)

中文:
定义 overFunctorMap
  签名: {X Y : D} (f : X ⟶ Y)
  定义体: NatIso.ofComponents
fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
      PresheafOfModules.isoMk (fun U => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, PresheafOfModules, PresheafOfModules.isoMk, SheafOfModules, SheafOfModules.fullyFaithfulForget, fullyFaithfulForget, ofComponents, preimageIso
-/
noncomputable def overFunctorMap {X Y : D} (f : X ⟶ Y) :
    overFunctor.{v} R Y ⋙ overMap.{v} R f ≅ overFunctor.{v} R X :=
  NatIso.ofComponents
fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
      PresheafOfModules.isoMk (fun U => Iso.refl _)

/-- The pushforward of `R.over Y` along `Over.map f` is isomorphic to `R.over X`. -/
@[simps! +dsimpLhs]
/--
Definition of `overMapUnitIso` / `overMapUnitIso` 的定义

English:
definition overMapUnitIso
  signature: {X Y : D} (f : X ⟶ Y)
  body: Iso.refl _

中文:
定义 overMapUnitIso
  签名: {X Y : D} (f : X ⟶ Y)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def overMapUnitIso {X Y : D} (f : X ⟶ Y) :
    (overMap.{u} R f).obj (.unit (R.over Y)) ≅ .unit (R.over X) :=
  Iso.refl _

variable (R) in
/--
Definition of `overPullback` / `overPullback` 的定义

English:
definition overPullback
  signature: [Limits.HasPullbacks D] {X Y : D} (f : X ⟶ Y)
  body: pushforward (F := Over.pullback f) (Sheaf.toPushforwardOverPullback R f)

中文:
定义 overPullback
  签名: [Limits.有Pullbacks D] {X Y : D} (f : X ⟶ Y)
  定义体: pushforward (F := Over.pullback f) (Sheaf.toPushforwardOverPullback R f)

Depends on / 依赖: Over.pullback, Sheaf.toPushforwardOverPullback, pullback, pushforward, toPushforwardOverPullback
-/
noncomputable def overPullback [Limits.HasPullbacks D] {X Y : D} (f : X ⟶ Y) :
    SheafOfModules.{v} (R.over X) ⥤ SheafOfModules.{v} (R.over Y) :=
  pushforward (F := Over.pullback f) (Sheaf.toPushforwardOverPullback R f)

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

/-- Pushforwards along equal morphisms of sheaves of rings are isomorphic. -/
noncomputable
/--
Definition of `pushforwardCongr` / `pushforwardCongr` 的定义

English:
definition pushforwardCongr
  signature: {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ)
  body: NatIso.ofComponents (fun X => (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U => (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app _)
      fun _ _ _ => by subst e; rfl)) fun _ => by subst e; rfl

中文:
定义 pushforwardCongr
  签名: {φ ψ : S ⟶ (F.sheafPushforwardContinuous 环范畴.{u} J K).obj R} (e : φ = ψ)
  定义体: NatIso.ofComponents (fun X => (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U => (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app _)
      fun _ _ _ => by subst e; rfl)) fun _ => by subst e; rfl

Depends on / 依赖: ModuleCat, ModuleCat.restrictScalarsCongr, NatIso, NatIso.ofComponents, PresheafOfModules, PresheafOfModules.isoMk, SheafOfModules, SheafOfModules.fullyFaithfulForget, fullyFaithfulForget, ofComponents, preimageIso, restrictScalarsCongr
-/
def pushforwardCongr {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents (fun X => (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U => (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app _)
      fun _ _ _ => by subst e; rfl)) fun _ => by subst e; rfl

/--
lemma `pushforwardCongr_symm` / 引理 `pushforwardCongr_symm`

English:
lemma pushforwardCongr_symm
  proof: rfl

中文:
引理 pushforwardCongr_symm
  证明: rfl
-/
@[simp] lemma pushforwardCongr_symm
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ) :
  (pushforwardCongr e).symm = pushforwardCongr e.symm := rfl

/--
lemma `pushforwardCongr_hom_app_val_app` / 引理 `pushforwardCongr_hom_app_val_app`

English:
lemma pushforwardCongr_hom_app_val_app
  proof: rfl

中文:
引理 pushforwardCongr_hom_app_val_app
  证明: rfl
-/
@[simp] lemma pushforwardCongr_hom_app_val_app
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ) (M U x) :
  ((pushforwardCongr e).hom.app M).val.app U x = x := rfl

/--
lemma `pushforwardCongr_inv_app_val_app` / 引理 `pushforwardCongr_inv_app_val_app`

English:
lemma pushforwardCongr_inv_app_val_app
  proof: rfl

中文:
引理 pushforwardCongr_inv_app_val_app
  证明: rfl
-/
@[simp] lemma pushforwardCongr_inv_app_val_app
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ) (M U x) :
  ((pushforwardCongr e).inv.app M).val.app U x = x := rfl

section

variable {K' : GrothendieckTopology D'} {K'' : GrothendieckTopology D''}
  {G : D ⥤ D'} {R' : Sheaf K' RingCat.{u}}
  [Functor.IsContinuous G K K']
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')

/--
Definition of `pushforwardComp` / `pushforwardComp` 的定义

English:
definition pushforwardComp
  signature: :
  body: Functor.isContinuous_comp _ _ _ K _
    pushforward.{v} ψ ⋙ pushforward.{v} φ ≅
      pushforward.{v} (F := F ⋙ G) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) :=
  Iso.refl _

中文:
定义 pushforwardComp
  签名: :
  定义体: Functor.isContinuous_comp _ _ _ K _
    pushforward.{v} ψ ⋙ pushforward.{v} φ ≅
      pushforward.{v} (F := F ⋙ G) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) :=
  Iso.refl _

Depends on / 依赖: Functor, Functor.isContinuous_comp, isContinuous_comp
-/
noncomputable def pushforwardComp :
    haveI : Functor.IsContinuous (F ⋙ G) J K' := Functor.isContinuous_comp _ _ _ K _
    pushforward.{v} ψ ⋙ pushforward.{v} φ ≅
      pushforward.{v} (F := F ⋙ G) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) :=
  Iso.refl _

-- Not a simp because the type of the LHS is dsimp-able
/--
lemma `pushforwardComp_hom_app_val_app` / 引理 `pushforwardComp_hom_app_val_app`

English:
lemma pushforwardComp_hom_app_val_app
  given: (M U x)
  proof: rfl

中文:
引理 pushforwardComp_hom_app_val_app
  条件: (M U x)
  证明: rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, SemimoduleCat
-/
lemma pushforwardComp_hom_app_val_app (M U x) :
  ((pushforwardComp φ ψ).hom.app M).val.app U x = x := rfl

-- Not a simp because the type of the LHS is dsimp-able
/--
lemma `pushforwardComp_inv_app_val_app` / 引理 `pushforwardComp_inv_app_val_app`

English:
lemma pushforwardComp_inv_app_val_app
  given: (M U x)
  proof: rfl

中文:
引理 pushforwardComp_inv_app_val_app
  条件: (M U x)
  证明: rfl
-/
lemma pushforwardComp_inv_app_val_app (M U x) :
  ((pushforwardComp φ ψ).inv.app M).val.app U x = x := rfl

variable {G' : D' ⥤ D''} {R'' : Sheaf K'' RingCat.{u}}
  [Functor.IsContinuous G' K' K'']
  [Functor.IsContinuous (G ⋙ G') K K'']
  [(F ⋙ G).IsContinuous J K']
  (ψ' : R' ⟶ (G'.sheafPushforwardContinuous RingCat.{u} K' K'').obj R'')

/--
lemma `pushforward_assoc` / 引理 `pushforward_assoc`

English:
lemma pushforward_assoc
  proof: by ext; rfl

中文:
引理 pushforward_assoc
  证明: by ext; rfl

Depends on / 依赖: f.hom
-/
lemma pushforward_assoc :
    (pushforward ψ').isoWhiskerLeft (pushforwardComp φ ψ) ≪≫
      pushforwardComp (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) ψ' =
    ((pushforward ψ').associator (pushforward ψ) (pushforward φ)).symm ≪≫
      isoWhiskerRight (pushforwardComp ψ ψ') (pushforward φ) ≪≫
      pushforwardComp (G := G ⋙ G') φ (ψ ≫
        (G.sheafPushforwardContinuous RingCat.{u} K K').map ψ') := by ext; rfl

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

section NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F G H : C ⥤ D} {T : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  [Functor.IsContinuous G J K]
  [Functor.IsContinuous H J K]
  (φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S)

/-- A natural transformation gives a natural transformation between the pushforward functors. -/
noncomputable
/--
Definition of `pushforwardNatTrans` / `pushforwardNatTrans` 的定义

English:
definition pushforwardNatTrans
  signature: (α : F ⟶ G)
  body: { val.app U := (ModuleCat.restrictScalars (φ.hom.app U).hom).map (X.val.map (α.app U.unop).op)
    val.naturality {U V} i := by
      ext x
      dsimp
      change (X.val.presheaf.map (G.map i.unop).op ≫ X.val.presheaf.map (α.app V.unop).op) _ =
        (X.val.presheaf.map (α.app U.unop).op ≫ X.val.presheaf.map (F.map i.unop).op) _
      simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality {X Y} f := by
    ext U x
    exact congr($(f.val.naturality (α.app U.unop).op) x).symm

中文:
定义 pushforward自然数Trans
  签名: (α : F ⟶ G)
  定义体: { val.app U := (ModuleCat.restrictScalars (φ.hom.app U).hom).map (X.val.map (α.app U.unop).op)
    val.naturality {U V} i := by
      ext x
      dsimp
      change (X.val.presheaf.map (G.map i.unop).op ≫ X.val.presheaf.map (α.app V.unop).op) _ =
        (X.val.presheaf.map (α.app U.unop).op ≫ X.val.presheaf.map (F.map i.unop).op) _
      simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality {X Y} f := by
    ext U x
    exact congr($(f.val.naturality (α.app U.unop).op) x).symm

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_comp, F.map, Functor, G.map, ModuleCat, ModuleCat.restrictScalars, U.unop, V.unop, X.val.map, X.val.presheaf.map, f.val.naturality, hom.app, i.unop, map_comp, naturality, op_comp, presheaf, restrictScalars, val.app
-/
def pushforwardNatTrans (α : F ⟶ G) :
    pushforward.{v} φ ⟶
      pushforward.{v} (φ ≫ (Functor.sheafPushforwardContinuousNatTrans α _ _ _).app S) where
  app X :=
  { val.app U := (ModuleCat.restrictScalars (φ.hom.app U).hom).map (X.val.map (α.app U.unop).op)
    val.naturality {U V} i := by
      ext x
      dsimp
      change (X.val.presheaf.map (G.map i.unop).op ≫ X.val.presheaf.map (α.app V.unop).op) _ =
        (X.val.presheaf.map (α.app U.unop).op ≫ X.val.presheaf.map (F.map i.unop).op) _
      simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality {X Y} f := by
    ext U x
    exact congr($(f.val.naturality (α.app U.unop).op) x).symm

/--
lemma `pushforwardNatTrans_app_val_app` / 引理 `pushforwardNatTrans_app_val_app`

English:
lemma pushforwardNatTrans_app_val_app
  given: (α : F ⟶ G) (M U x)
  proof: rfl

@[simp]

中文:
引理 pushforward自然数Trans_app_val_app
  条件: (α : F ⟶ G) (M U x)
  证明: rfl

@[simp]
-/
@[simp] lemma pushforwardNatTrans_app_val_app (α : F ⟶ G) (M U x) :
    ((pushforwardNatTrans φ α).app M).val.app U x = M.val.map (α.app U.unop).op x := rfl

@[simp]
/--
lemma `pushforwardNatTrans_id` / 引理 `pushforwardNatTrans_id`

English:
lemma pushforwardNatTrans_id
  proof: by cat_disch

@[simp]

中文:
引理 pushforward自然数Trans_id
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma pushforwardNatTrans_id :
    pushforwardNatTrans φ (𝟙 G) = (pushforwardCongr (by cat_disch)).hom := by cat_disch

@[simp]
/--
lemma `pushforwardNatTrans_comp` / 引理 `pushforwardNatTrans_comp`

English:
lemma pushforwardNatTrans_comp
  statement: (α : F ⟶ G) (β : G ⟶ H)
  proof: by cat_disch

@[simp]

中文:
引理 pushforward自然数Trans_comp
  结论: (α : F ⟶ G) (β : G ⟶ H)
  证明: by cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma pushforwardNatTrans_comp (α : F ⟶ G) (β : G ⟶ H)
    (φ : T ⟶ (H.sheafPushforwardContinuous RingCat.{u} J K).obj S) :
    pushforwardNatTrans φ (α ≫ β) = pushforwardNatTrans φ β ≫ pushforwardNatTrans _ α ≫
      (pushforwardCongr (by cat_disch)).hom := by cat_disch

@[simp]
/--
lemma `pushforwardNatTrans_app_val_app_apply` / 引理 `pushforwardNatTrans_app_val_app_apply`

English:
lemma pushforwardNatTrans_app_val_app_apply
  given: (α : F ⟶ G) (X U x)
  proof: rfl

中文:
引理 pushforward自然数Trans_app_val_app_apply
  条件: (α : F ⟶ G) (X U x)
  证明: rfl
-/
lemma pushforwardNatTrans_app_val_app_apply (α : F ⟶ G) (X U x) :
    ((pushforwardNatTrans φ α).app X).val.app U x = X.val.map (α.app U.unop).op x := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural isomorphism gives a natural isomorphism between the pushforward functors. -/
@[simps]
/--
Definition of `pushforwardNatIso` / `pushforwardNatIso` 的定义

English:
definition pushforwardNatIso
  signature: (α : F ≅ G)
  body: pushforwardNatTrans _ α.hom
  inv := pushforwardNatTrans _ α.inv ≫
    (pushforwardCongr (by ext : 3; simp [← Functor.map_comp, ← op_comp])).hom
  hom_inv_id := by
    ext X U x
    suffices X.val.presheaf.map (α.hom.app U.unop).op ≫
      X.val.presheaf.map (α.inv.app U.unop).op = 𝟙 _ from congr($this x)
    simp only [← Functor.map_comp, ← op_comp,
      Iso.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    ext X U x
    suffices X.val.presheaf.map (α.inv.app U.unop).op ≫
      X.val.presheaf.map (α.hom.app U.unop).op = 𝟙 _ from congr($this x)
    simp only [← Functor.map_comp, ← op_comp,
      Iso.hom_inv_id_app, op_id, CategoryTheory.Functor.map_id]

中文:
定义 pushforward自然数Iso
  签名: (α : F ≅ G)
  定义体: pushforwardNatTrans _ α.hom
  inv := pushforwardNatTrans _ α.inv ≫
    (pushforwardCongr (by ext : 3; simp [← Functor.map_comp, ← op_comp])).hom
  hom_inv_id := by
    ext X U x
    suffices X.val.presheaf.map (α.hom.app U.unop).op ≫
      X.val.presheaf.map (α.inv.app U.unop).op = 𝟙 _ from congr($this x)
    simp only [← Functor.map_comp, ← op_comp,
      Iso.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    ext X U x
    suffices X.val.presheaf.map (α.inv.app U.unop).op ≫
      X.val.presheaf.map (α.hom.app U.unop).op = 𝟙 _ from congr($this x)
    simp only [← Functor.map_comp, ← op_comp,
      Iso.hom_inv_id_app, op_id, CategoryTheory.Functor.map_id]

Depends on / 依赖: pushforwardNatTrans
-/
noncomputable def pushforwardNatIso (α : F ≅ G) :
    pushforward.{v} φ ≅
      pushforward.{v} (φ ≫ (Functor.sheafPushforwardContinuousNatTrans α.hom _ _ _).app S) where
  hom := pushforwardNatTrans _ α.hom
  inv := pushforwardNatTrans _ α.inv ≫
    (pushforwardCongr (by ext : 3; simp [← Functor.map_comp, ← op_comp])).hom
  hom_inv_id := by
    ext X U x
    suffices X.val.presheaf.map (α.hom.app U.unop).op ≫
      X.val.presheaf.map (α.inv.app U.unop).op = 𝟙 _ from congr($this x)
    simp only [← Functor.map_comp, ← op_comp,
      Iso.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    ext X U x
    suffices X.val.presheaf.map (α.inv.app U.unop).op ≫
      X.val.presheaf.map (α.hom.app U.unop).op = 𝟙 _ from congr($this x)
    simp only [← Functor.map_comp, ← op_comp,
      Iso.hom_inv_id_app, op_id, CategoryTheory.Functor.map_id]

/-- More flexible variant of `SheafOfModules.pushforwardNatIso`. -/
@[simps!]
noncomputable
/--
Definition of `pushforwardCongr₂` / `pushforwardCongr₂` 的定义

English:
definition pushforwardCongr₂
  signature: {ψ : T ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S} (e : F ≅ G)
  body: pushforwardNatIso _ e ≪≫ pushforwardCongr he

中文:
定义 pushforwardCongr₂
  签名: {ψ : T ⟶ (F.sheafPushforwardContinuous 环范畴 J K).obj S} (e : F ≅ G)
  定义体: pushforwardNatIso _ e ≪≫ pushforwardCongr he

Depends on / 依赖: pushforwardCongr, pushforwardNatIso
-/
def pushforwardCongr₂ {ψ : T ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S} (e : F ≅ G)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom _ _ _).app S = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  pushforwardNatIso _ e ≪≫ pushforwardCongr he

end NatTrans

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} {G : D ⥤ C}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  [Functor.IsContinuous G K J]
  (adj : F ⊣ G)
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj S)
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.obj = ψ.hom ≫ G.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj)

set_option backward.isDefEq.respectTransparency false in
/-- If `F ⊣ G`, then the pushforwards along `F` and `G` are also adjoint. -/
noncomputable
/--
Definition of `pushforwardPushforwardAdj` / `pushforwardPushforwardAdj` 的定义

English:
definition pushforwardPushforwardAdj
  signature: : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  body: letI := CategoryTheory.Functor.isContinuous_comp G F K J K
    (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by ext1; simpa)).hom ≫ (pushforwardComp _ _).inv
  counit :=
    letI := CategoryTheory.Functor.isContinuous_comp F G J K J
    (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by ext1; simpa)).hom ≫ (pushforwardId _).hom
  left_triangle_components X := by
    ext U x
    change (X.val.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      X.val.presheaf.map (F.map (adj.unit.app U.unop)).op) _ = _
    dsimp only [id_obj]
    rw [← Functor.map_comp]; rw [← op_comp]; rw [adj.left_triangle_components]
    simp
  right_triangle_components X := by
    ext U x
    change (X.val.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      X.val.presheaf.map (adj.unit.app (G.obj U.unop)).op) _ = _
    rw [← Functor.map_comp]; rw [← op_comp]; rw [adj.right_triangle_components]
    simp

中文:
定义 pushforwardPushforwardAdj
  签名: : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  定义体: letI := CategoryTheory.Functor.isContinuous_comp G F K J K
    (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by ext1; simpa)).hom ≫ (pushforwardComp _ _).inv
  counit :=
    letI := CategoryTheory.Functor.isContinuous_comp F G J K J
    (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by ext1; simpa)).hom ≫ (pushforwardId _).hom
  left_triangle_components X := by
    ext U x
    change (X.val.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      X.val.presheaf.map (F.map (adj.unit.app U.unop)).op) _ = _
    dsimp only [id_obj]
    rw [← Functor.map_comp]; rw [← op_comp]; rw [adj.left_triangle_components]
    simp
  right_triangle_components X := by
    ext U x
    change (X.val.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      X.val.presheaf.map (adj.unit.app (G.obj U.unop)).op) _ = _
    rw [← Functor.map_comp]; rw [← op_comp]; rw [adj.right_triangle_components]
    simp

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.isContinuous_comp, F.obj, Functor, U.unop, X.val.presh, X.val.presheaf.map, adj.counit, adj.counit.app, adj.unit, counit, isContinuous_comp, left_triangle_components, presheaf, pushforwardComp, pushforwardCongr, pushforwardId, pushforwardNatTrans
-/
def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit :=
    letI := CategoryTheory.Functor.isContinuous_comp G F K J K
    (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by ext1; simpa)).hom ≫ (pushforwardComp _ _).inv
  counit :=
    letI := CategoryTheory.Functor.isContinuous_comp F G J K J
    (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by ext1; simpa)).hom ≫ (pushforwardId _).hom
  left_triangle_components X := by
    ext U x
    change (X.val.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      X.val.presheaf.map (F.map (adj.unit.app U.unop)).op) _ = _
    dsimp only [id_obj]
    rw [← Functor.map_comp]; rw [← op_comp]; rw [adj.left_triangle_components]
    simp
  right_triangle_components X := by
    ext U x
    change (X.val.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      X.val.presheaf.map (adj.unit.app (G.obj U.unop)).op) _ = _
    rw [← Functor.map_comp]; rw [← op_comp]; rw [adj.right_triangle_components]
    simp

-- Not a simp because the type of the LHS is dsimp-able
/--
lemma `pushforwardPushforwardAdj_unit_app_val_app` / 引理 `pushforwardPushforwardAdj_unit_app_val_app`

English:
lemma pushforwardPushforwardAdj_unit_app_val_app
  given: (M U x)
  proof: rfl

中文:
引理 pushforwardPushforwardAdj_unit_app_val_app
  条件: (M U x)
  证明: rfl
-/
lemma pushforwardPushforwardAdj_unit_app_val_app (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).val.app U x =
      M.val.map (adj.counit.app U.unop).op x := rfl

-- Not a simp because the type of the LHS is dsimp-able
/--
lemma `pushforwardPushforwardAdj_counit_app_val_app` / 引理 `pushforwardPushforwardAdj_counit_app_val_app`

English:
lemma pushforwardPushforwardAdj_counit_app_val_app
  given: (M U x)
  proof: rfl

中文:
引理 pushforwardPushforwardAdj_counit_app_val_app
  条件: (M U x)
  证明: rfl
-/
lemma pushforwardPushforwardAdj_counit_app_val_app (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app M).val.app U x =
      M.val.map (adj.unit.app U.unop).op x := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `isLeftAdjoint_pushforward_of_isIso` / 实例 `isLeftAdjoint_pushforward_of_isIso`

English:
instance isLeftAdjoint_pushforward_of_isIso
  signature: [F.IsCocontinuous J K] [IsIso φ] [F.IsLeftAdjoint]
  body: by
  let adj := Adjunction.ofIsLeftAdjoint F
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u}) J K
  let ψ : R ⟶ (F.rightAdjoint.sheafPushforwardContinuous RingCat.{u} K J).obj S :=
    shAdj.unit.app R ≫ (F.rightAdjoint.sheafPushforwardContinuous _ _ _).map (inv φ)
  refine (SheafOfModules.pushforwardPushforwardAdj adj φ ψ ?_ ?_).isLeftAdjoint
  · ext U : 2
    simp [ψ, shAdj]
  · ext U : 2
    have := (inv φ).hom.naturality
    dsimp at this
    simp only [ObjectProperty.hom_inv, NatIso.isIso_inv_app, sheafPushforwardContinuous_obj_obj_obj,
      IsIso.eq_inv_comp] at this
    simp [ψ, shAdj, ← this, ← Functor.map_comp_assoc, ← op_comp]

noncomputable section

中文:
实例 isLeftAdjoint_pushforward_of_isIso
  签名: [F.是余continuous J K] [是同构 φ] [F.是左伴随]
  定义体: by
  let adj := Adjunction.ofIsLeftAdjoint F
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u}) J K
  let ψ : R ⟶ (F.rightAdjoint.sheafPushforwardContinuous RingCat.{u} K J).obj S :=
    shAdj.unit.app R ≫ (F.rightAdjoint.sheafPushforwardContinuous _ _ _).map (inv φ)
  refine (SheafOfModules.pushforwardPushforwardAdj adj φ ψ ?_ ?_).isLeftAdjoint
  · ext U : 2
    simp [ψ, shAdj]
  · ext U : 2
    have := (inv φ).hom.naturality
    dsimp at this
    simp only [ObjectProperty.hom_inv, NatIso.isIso_inv_app, sheafPushforwardContinuous_obj_obj_obj,
      IsIso.eq_inv_comp] at this
    simp [ψ, shAdj, ← this, ← Functor.map_comp_assoc, ← op_comp]

noncomputable section

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, F.rightAdjoint.sheafPushforwardContinuous, NatIso, NatIso.isIso_inv_app, ObjectProperty, ObjectProperty.hom_inv, RingCat, SheafOfModules, SheafOfModules.pushforwardPushforwardAdj, adj.sheafPushforwardContinuous, hom.naturality, hom_inv, isIso_inv_app, isLeftAdjoint, naturality, ofIsLeftAdjoint, pushforwardPushforwardAdj, rightAdjoint, shAdj.unit.app
-/
instance isLeftAdjoint_pushforward_of_isIso [F.IsCocontinuous J K] [IsIso φ] [F.IsLeftAdjoint] :
    (pushforward.{u} φ).IsLeftAdjoint := by
  let adj := Adjunction.ofIsLeftAdjoint F
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u}) J K
  let ψ : R ⟶ (F.rightAdjoint.sheafPushforwardContinuous RingCat.{u} K J).obj S :=
    shAdj.unit.app R ≫ (F.rightAdjoint.sheafPushforwardContinuous _ _ _).map (inv φ)
  refine (SheafOfModules.pushforwardPushforwardAdj adj φ ψ ?_ ?_).isLeftAdjoint
  · ext U : 2
    simp [ψ, shAdj]
  · ext U : 2
    have := (inv φ).hom.naturality
    dsimp at this
    simp only [ObjectProperty.hom_inv, NatIso.isIso_inv_app, sheafPushforwardContinuous_obj_obj_obj,
      IsIso.eq_inv_comp] at this
    simp [ψ, shAdj, ← this, ← Functor.map_comp_assoc, ← op_comp]

noncomputable section

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `pushforwardOver` / `pushforwardOver` 的定义

English:
definition pushforwardOver
  signature: (x : C)
  body: ⟨{app U := R.obj.map Limits.prod.snd.op
    naturality U V f := by simp [← Functor.map_comp, ← op_comp]; rfl }⟩

中文:
定义 pushforwardOver
  签名: (x : C)
  定义体: ⟨{app U := R.obj.map Limits.prod.snd.op
    naturality U V f := by simp [← Functor.map_comp, ← op_comp]; rfl }⟩

Depends on / 依赖: Functor, Functor.map_comp, Limits, Limits.prod.snd.op, R.obj.map, map_comp, naturality, op_comp
-/
def pushforwardOver (x : C) :
    R ⟶ ((Over.star x).sheafPushforwardContinuous RingCat J (J.over x)).obj (R.over x) :=
  ⟨{app U := R.obj.map Limits.prod.snd.op
    naturality U V f := by simp [← Functor.map_comp, ← op_comp]; rfl }⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `overPushforwardOverAdj` / `overPushforwardOverAdj` 的定义

English:
definition overPushforwardOverAdj
  signature: (x : C)
  body: by
  refine pushforwardPushforwardAdj (Over.forgetAdjStar x) (𝟙 (R.over x)) _ ?_ ?_
  · ext y : 2
    simp [pushforwardOver]
  · ext y : 2
    simp [pushforwardOver, ← Functor.map_comp, ← op_comp]

中文:
定义 overPushforwardOverAdj
  签名: (x : C)
  定义体: by
  refine pushforwardPushforwardAdj (Over.forgetAdjStar x) (𝟙 (R.over x)) _ ?_ ?_
  · ext y : 2
    simp [pushforwardOver]
  · ext y : 2
    simp [pushforwardOver, ← Functor.map_comp, ← op_comp]

Depends on / 依赖: Functor, Functor.map_comp, Over.forgetAdjStar, R.over, forgetAdjStar, map_comp, op_comp, pushforwardOver, pushforwardPushforwardAdj
-/
def overPushforwardOverAdj (x : C) :
    pushforward.{w} (𝟙 (R.over x)) ⊣ pushforward.{w} (pushforwardOver x) := by
  refine pushforwardPushforwardAdj (Over.forgetAdjStar x) (𝟙 (R.over x)) _ ?_ ?_
  · ext y : 2
    simp [pushforwardOver]
  · ext y : 2
    simp [pushforwardOver, ← Functor.map_comp, ← op_comp]

instance (x : C) : IsLeftAdjoint (pushforward.{w} (𝟙 (R.over x))) where
  exists_rightAdjoint := ⟨_, Nonempty.intro (overPushforwardOverAdj x)⟩

variable (R) in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `overMapPushforwardAdj` / `overMapPushforwardAdj` 的定义

English:
definition overMapPushforwardAdj
  signature: [HasPullbacks C] {X Y : C} (f : X ⟶ Y)
  body: by
  refine pushforwardPushforwardAdj (Over.mapPullbackAdj f) _ _ ?_ ?_
  · ext
    simp [Sheaf.pushforwardOverMapIso]
  · ext
    simp [← Functor.map_comp, ← op_comp, Sheaf.pushforwardOverMapIso]

中文:
定义 overMapPushforwardAdj
  签名: [有Pullbacks C] {X Y : C} (f : X ⟶ Y)
  定义体: by
  refine pushforwardPushforwardAdj (Over.mapPullbackAdj f) _ _ ?_ ?_
  · ext
    simp [Sheaf.pushforwardOverMapIso]
  · ext
    simp [← Functor.map_comp, ← op_comp, Sheaf.pushforwardOverMapIso]

Depends on / 依赖: Functor, Functor.map_comp, Over.mapPullbackAdj, Sheaf.pushforwardOverMapIso, mapPullbackAdj, map_comp, op_comp, pushforwardOverMapIso, pushforwardPushforwardAdj
-/
def overMapPushforwardAdj [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    overMap R f ⊣ overPullback R f := by
  refine pushforwardPushforwardAdj (Over.mapPullbackAdj f) _ _ ?_ ?_
  · ext
    simp [Sheaf.pushforwardOverMapIso]
  · ext
    simp [← Functor.map_comp, ← op_comp, Sheaf.pushforwardOverMapIso]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPullbacks
  signature: C] {X Y
  body: (overMapPushforwardAdj R f).isLeftAdjoint

中文:
实例 [有Pullbacks
  签名: C] {X Y
  定义体: (overMapPushforwardAdj R f).isLeftAdjoint

Depends on / 依赖: isLeftAdjoint, overMapPushforwardAdj
-/
instance [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : (overMap R f).IsLeftAdjoint :=
  (overMapPushforwardAdj R f).isLeftAdjoint

end

end Adjunction

section Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (eqv : C ≌ D)
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous eqv.functor J K]
  [Functor.IsContinuous eqv.inverse K J]
  (φ : S ⟶ (eqv.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (eqv.inverse.sheafPushforwardContinuous RingCat.{u} K J).obj S)
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit) R.obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) S.obj = 𝟙 S.obj)

/-- If `e : C ≌ D`, then the pushforwards along `e.functor` and `e.inverse` forms an equivalence. -/
noncomputable
/--
Definition of `pushforwardPushforwardEquivalence` / `pushforwardPushforwardEquivalence` 的定义

English:
definition pushforwardPushforwardEquivalence
  signature: : SheafOfModules R ≌ SheafOfModules S where
  body: pushforward.{v} φ
  inverse := pushforward.{v} ψ
  unitIso :=
    letI := CategoryTheory.Functor.isContinuous_comp eqv.inverse eqv.functor K J K
    (pushforwardId _).symm ≪≫ pushforwardNatIso _ eqv.counitIso ≪≫
      pushforwardCongr (by ext1; simpa) ≪≫ (pushforwardComp _ _).symm
  counitIso :=
    letI := CategoryTheory.Functor.isContinuous_comp eqv.functor eqv.inverse J K J
    pushforwardComp _ _ ≪≫ pushforwardNatIso _ eqv.unitIso ≪≫
      pushforwardCongr (by ext1; simpa) ≪≫ pushforwardId _
  functor_unitIso_comp :=
    (pushforwardPushforwardAdj eqv.toAdjunction φ ψ H₁ H₂).left_triangle_components

中文:
定义 pushforwardPushforwardEquivalence
  签名: : 模层 R ≌ 模层 S where
  定义体: pushforward.{v} φ
  inverse := pushforward.{v} ψ
  unitIso :=
    letI := CategoryTheory.Functor.isContinuous_comp eqv.inverse eqv.functor K J K
    (pushforwardId _).symm ≪≫ pushforwardNatIso _ eqv.counitIso ≪≫
      pushforwardCongr (by ext1; simpa) ≪≫ (pushforwardComp _ _).symm
  counitIso :=
    letI := CategoryTheory.Functor.isContinuous_comp eqv.functor eqv.inverse J K J
    pushforwardComp _ _ ≪≫ pushforwardNatIso _ eqv.unitIso ≪≫
      pushforwardCongr (by ext1; simpa) ≪≫ pushforwardId _
  functor_unitIso_comp :=
    (pushforwardPushforwardAdj eqv.toAdjunction φ ψ H₁ H₂).left_triangle_components

Depends on / 依赖: pushforward
-/
def pushforwardPushforwardEquivalence : SheafOfModules R ≌ SheafOfModules S where
  functor := pushforward.{v} φ
  inverse := pushforward.{v} ψ
  unitIso :=
    letI := CategoryTheory.Functor.isContinuous_comp eqv.inverse eqv.functor K J K
    (pushforwardId _).symm ≪≫ pushforwardNatIso _ eqv.counitIso ≪≫
      pushforwardCongr (by ext1; simpa) ≪≫ (pushforwardComp _ _).symm
  counitIso :=
    letI := CategoryTheory.Functor.isContinuous_comp eqv.functor eqv.inverse J K J
    pushforwardComp _ _ ≪≫ pushforwardNatIso _ eqv.unitIso ≪≫
      pushforwardCongr (by ext1; simpa) ≪≫ pushforwardId _
  functor_unitIso_comp :=
    (pushforwardPushforwardAdj eqv.toAdjunction φ ψ H₁ H₂).left_triangle_components

-- Not a simp because the type of the LHS is dsimp-able
/--
lemma `pushforwardPushforwardEquivalence_unit_app_val_app` / 引理 `pushforwardPushforwardEquivalence_unit_app_val_app`

English:
lemma pushforwardPushforwardEquivalence_unit_app_val_app
  given: (M U x)
  proof: rfl

中文:
引理 pushforwardPushforwardEquivalence_unit_app_val_app
  条件: (M U x)
  证明: rfl
-/
lemma pushforwardPushforwardEquivalence_unit_app_val_app (M U x) :
    ((pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).unit.app M).val.app U x =
      M.val.map (eqv.counit.app U.unop).op x := rfl

-- Not a simp because the type of the LHS is dsimp-able
/--
lemma `pushforwardPushforwardEquivalence_counit_app_val_app` / 引理 `pushforwardPushforwardEquivalence_counit_app_val_app`

English:
lemma pushforwardPushforwardEquivalence_counit_app_val_app
  given: (M U x)
  proof: rfl

中文:
引理 pushforwardPushforwardEquivalence_counit_app_val_app
  条件: (M U x)
  证明: rfl
-/
lemma pushforwardPushforwardEquivalence_counit_app_val_app (M U x) :
    ((pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).counit.app M).val.app U x =
      M.val.map (eqv.unit.app U.unop).op x := rfl

end Equivalence

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pushforwardCompForgetToSheafModuleCat` / `pushforwardCompForgetToSheafModuleCat` 的定义

English:
definition pushforwardCompForgetToSheafModuleCat
  body: by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U => ?_) ?_
    · refine (ModuleCat.restrictScalarsComp'App _ _ _ ?_ _).symm ≪≫
        (ModuleCat.restrictScalarsComp _ _).app _
      rw [← RingCat.hom_comp]; rw [← RingCat.hom_comp]; rw [φ.hom.naturality]
      dsimp
      rw [hX'.hom_ext (hX'.to (Opposite.op (F.obj (Opposite.unop U)))) _]
    · cat_disch
  · cat_disch

中文:
定义 pushforwardCompForgetToSheafModuleCat
  定义体: by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U => ?_) ?_
    · refine (ModuleCat.restrictScalarsComp'App _ _ _ ?_ _).symm ≪≫
        (ModuleCat.restrictScalarsComp _ _).app _
      rw [← RingCat.hom_comp]; rw [← RingCat.hom_comp]; rw [φ.hom.naturality]
      dsimp
      rw [hX'.hom_ext (hX'.to (Opposite.op (F.obj (Opposite.unop U)))) _]
    · cat_disch
  · cat_disch

Depends on / 依赖: F.obj, ModuleCat, ModuleCat.restrictScalarsComp, NatIso, NatIso.ofComponents, ObjectProperty, ObjectProperty.isoMk, Opposite, Opposite.op, Opposite.unop, RingCat, RingCat.hom_comp, cat_disch, hom.naturality, hom_comp, hom_ext, naturality, ofComponents, restrictScalarsComp
-/
noncomputable def pushforwardCompForgetToSheafModuleCat
    (X : Cᵒᵖ) (hX : Limits.IsInitial X) (hX' : Limits.IsInitial (F.op.obj X)) :
    SheafOfModules.pushforward φ ⋙ SheafOfModules.forgetToSheafModuleCat _ X hX ≅
    SheafOfModules.forgetToSheafModuleCat _ _ hX' ⋙
      sheafCompose K (ModuleCat.restrictScalars <| (φ.hom.app _).hom) ⋙
        F.sheafPushforwardContinuous _ J K := by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U => ?_) ?_
    · refine (ModuleCat.restrictScalarsComp'App _ _ _ ?_ _).symm ≪≫
        (ModuleCat.restrictScalarsComp _ _).app _
      rw [← RingCat.hom_comp]; rw [← RingCat.hom_comp]; rw [φ.hom.naturality]
      dsimp
      rw [hX'.hom_ext (hX'.to (Opposite.op (F.obj (Opposite.unop U)))) _]
    · cat_disch
  · cat_disch

end SheafOfModules
