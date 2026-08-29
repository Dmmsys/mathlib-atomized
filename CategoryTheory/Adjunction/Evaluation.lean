/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!

# Adjunctions involving evaluation

We show that evaluation of functors has adjoints, given the existence of (co)products.

-/

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

noncomputable section

section

variable [forall a b : C, HasCoproductsOfShape (a ⟶ b) D]

set_option backward.isDefEq.respectTransparency false in
/-- The left adjoint of evaluation. -/
@[simps]
/--
Definition of `evaluationLeftAdjoint` / `evaluationLeftAdjoint` 的定义

English:
definition evaluationLeftAdjoint
  signature: (c : C)
  body: { obj := fun t => ∐ fun _ : c ⟶ t => d
map := fun f => Sigma.desc fun g => (Sigma.ι fun _ => d) g ≫ f }
  map {_ d₂} f :=
    { app := fun _ => Sigma.desc fun h => f ≫ Sigma.ι (fun _ => d₂) h
      naturality := by
        intros
        dsimp
        ext
        simp }

中文:
定义 evaluationLeftAdjoint
  签名: (c : C)
  定义体: { obj := fun t => ∐ fun _ : c ⟶ t => d
map := fun f => Sigma.desc fun g => (Sigma.ι fun _ => d) g ≫ f }
  map {_ d₂} f :=
    { app := fun _ => Sigma.desc fun h => f ≫ Sigma.ι (fun _ => d₂) h
      naturality := by
        intros
        dsimp
        ext
        simp }

Depends on / 依赖: Sigma.desc, intros, naturality
-/
def evaluationLeftAdjoint (c : C) : D ⥤ C ⥤ D where
  obj d :=
    { obj := fun t => ∐ fun _ : c ⟶ t => d
map := fun f => Sigma.desc fun g => (Sigma.ι fun _ => d) g ≫ f }
  map {_ d₂} f :=
    { app := fun _ => Sigma.desc fun h => f ≫ Sigma.ι (fun _ => d₂) h
      naturality := by
        intros
        dsimp
        ext
        simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction showing that evaluation is a right adjoint. -/
@[simps! unit_app counit_app_app]
/--
Definition of `evaluationAdjunctionRight` / `evaluationAdjunctionRight` 的定义

English:
definition evaluationAdjunctionRight
  signature: (c : C)
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun d F =>
        { toFun := fun f => Sigma.ι (fun _ => d) (𝟙 _) ≫ f.app c
          invFun := fun f => { app := fun _ => Sigma.desc fun h => f ≫ F.map h }
          left_inv := by
            intro f
            ext x
            dsimp
            ext g
  

中文:
定义 evaluationAdjunctionRight
  签名: (c : C)
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun d F =>
        { toFun := fun f => Sigma.ι (fun _ => d) (𝟙 _) ≫ f.app c
          invFun := fun f => { app := fun _ => Sigma.desc fun h => f ≫ F.map h }
          left_inv := by
            intro f
            ext x
            dsimp
            ext g
  

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Category, Category.assoc, Category.id_comp, Cofan.mk_, Cofan.mk_pt, Discrete, Discrete.functor_obj, F.map, Sigma.desc, colimit, evaluationLeftAdjoint_obj_map, f.app, f.naturality, functor_obj, homEquiv, id_comp, invFun, left_inv
-/
def evaluationAdjunctionRight (c : C) : evaluationLeftAdjoint D c ⊣ (evaluation _ _).obj c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun d F =>
        { toFun := fun f => Sigma.ι (fun _ => d) (𝟙 _) ≫ f.app c
          invFun := fun f => { app := fun _ => Sigma.desc fun h => f ≫ F.map h }
          left_inv := by
            intro f
            ext x
            dsimp
            ext g
            simp only [colimit.ι_desc, Cofan.mk_ι_app, Category.assoc, ← f.naturality,
              evaluationLeftAdjoint_obj_map, colimit.ι_desc_assoc,
              Discrete.functor_obj, Cofan.mk_pt, Category.id_comp]
          right_inv := fun f => by simp } }

/--
Instance `evaluationIsRightAdjoint` / 实例 `evaluationIsRightAdjoint`

English:
instance evaluationIsRightAdjoint
  signature: (c : C)
  body: ⟨_, ⟨evaluationAdjunctionRight _ _⟩⟩

中文:
实例 evaluationIsRightAdjoint
  签名: (c : C)
  定义体: ⟨_, ⟨evaluationAdjunctionRight _ _⟩⟩

Depends on / 依赖: evaluationAdjunctionRight
-/
instance evaluationIsRightAdjoint (c : C) : ((evaluation _ D).obj c).IsRightAdjoint :=
  ⟨_, ⟨evaluationAdjunctionRight _ _⟩⟩

/--
theorem `NatTrans.mono_iff_mono_app'` / 定理 `NatTrans.mono_iff_mono_app'`

English:
theorem NatTrans.mono_iff_mono_app'
  given: {F G : C ⥤ D} (η : F ⟶ G)
  statement: Mono η ↔ forall c, Mono (η.app c)
  proof: by
  constructor
  · intro h c
    exact (inferInstance : Mono (((evaluation _ _).obj c).map η))
  · intro _
    apply NatTrans.mono_of_mono_app

中文:
定理 NatTrans.mono_iff_mono_app'
  条件: {F G : C ⥤ D} (η : F ⟶ G)
  结论: Mono η ↔ 对任意 c, Mono (η.app c)
  证明: by
  constructor
  · intro h c
    exact (inferInstance : Mono (((evaluation _ _).obj c).map η))
  · intro _
    apply NatTrans.mono_of_mono_app

Depends on / 依赖: NatTrans, NatTrans.mono_of_mono_app, evaluation, mono_of_mono_app
-/
theorem NatTrans.mono_iff_mono_app' {F G : C ⥤ D} (η : F ⟶ G) : Mono η ↔ forall c, Mono (η.app c) := by
  constructor
  · intro h c
    exact (inferInstance : Mono (((evaluation _ _).obj c).map η))
  · intro _
    apply NatTrans.mono_of_mono_app

end

section

variable [forall a b : C, HasProductsOfShape (a ⟶ b) D]

set_option backward.isDefEq.respectTransparency false in
/-- The right adjoint of evaluation. -/
@[simps]
/--
Definition of `evaluationRightAdjoint` / `evaluationRightAdjoint` 的定义

English:
definition evaluationRightAdjoint
  signature: (c : C)
  body: { obj := fun t => ∏ᶜ fun _ : t ⟶ c => d
map := fun f => Pi.lift fun g => Pi.π _ f ≫ g }
  map f := { app := fun _ => Pi.lift fun g => Pi.π _ g ≫ f }

中文:
定义 evaluationRightAdjoint
  签名: (c : C)
  定义体: { obj := fun t => ∏ᶜ fun _ : t ⟶ c => d
map := fun f => Pi.lift fun g => Pi.π _ f ≫ g }
  map f := { app := fun _ => Pi.lift fun g => Pi.π _ g ≫ f }

Depends on / 依赖: Pi.lift
-/
def evaluationRightAdjoint (c : C) : D ⥤ C ⥤ D where
  obj d :=
    { obj := fun t => ∏ᶜ fun _ : t ⟶ c => d
map := fun f => Pi.lift fun g => Pi.π _ f ≫ g }
  map f := { app := fun _ => Pi.lift fun g => Pi.π _ g ≫ f }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction showing that evaluation is a left adjoint. -/
@[simps! unit_app_app counit_app]
/--
Definition of `evaluationAdjunctionLeft` / `evaluationAdjunctionLeft` 的定义

English:
definition evaluationAdjunctionLeft
  signature: (c : C)
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun F d =>
        { toFun := fun f => { app := fun _ => Pi.lift fun g => F.map g ≫ f }
          invFun := fun f => f.app _ ≫ Pi.π _ (𝟙 _)
          left_inv := fun f => by simp
          right_inv := by
            intro f
            ext x
            dsi

中文:
定义 evaluationAdjunctionLeft
  签名: (c : C)
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun F d =>
        { toFun := fun f => { app := fun _ => Pi.lift fun g => F.map g ≫ f }
          invFun := fun f => f.app _ ≫ Pi.π _ (𝟙 _)
          left_inv := fun f => by simp
          right_inv := by
            intro f
            ext x
            dsi

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Category, Category.comp_id, F.map, Fan.mk_, Fan.mk_pt, NatTrans, NatTrans.naturality_assoc, Pi.lift, comp_id, evaluationRightAdjoint_obj_map, evaluationRightAdjoint_obj_obj, f.app, homEquiv, invFun, left_inv, limit.lift_, mkOfHomEquiv, mk_pt
-/
def evaluationAdjunctionLeft (c : C) : (evaluation _ _).obj c ⊣ evaluationRightAdjoint D c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F d =>
        { toFun := fun f => { app := fun _ => Pi.lift fun g => F.map g ≫ f }
          invFun := fun f => f.app _ ≫ Pi.π _ (𝟙 _)
          left_inv := fun f => by simp
          right_inv := by
            intro f
            ext x
            dsimp
            ext g
            simp only [NatTrans.naturality_assoc,
              evaluationRightAdjoint_obj_obj, evaluationRightAdjoint_obj_map, limit.lift_π,
              Fan.mk_pt, Fan.mk_π_app, Category.comp_id] } }

/--
Instance `evaluationIsLeftAdjoint` / 实例 `evaluationIsLeftAdjoint`

English:
instance evaluationIsLeftAdjoint
  signature: (c : C)
  body: ⟨_, ⟨evaluationAdjunctionLeft _ _⟩⟩

中文:
实例 evaluationIsLeftAdjoint
  签名: (c : C)
  定义体: ⟨_, ⟨evaluationAdjunctionLeft _ _⟩⟩

Depends on / 依赖: evaluationAdjunctionLeft
-/
instance evaluationIsLeftAdjoint (c : C) : ((evaluation _ D).obj c).IsLeftAdjoint :=
  ⟨_, ⟨evaluationAdjunctionLeft _ _⟩⟩

/--
theorem `NatTrans.epi_iff_epi_app'` / 定理 `NatTrans.epi_iff_epi_app'`

English:
theorem NatTrans.epi_iff_epi_app'
  given: {F G : C ⥤ D} (η : F ⟶ G)
  statement: Epi η ↔ forall c, Epi (η.app c)
  proof: by
  constructor
  · intro h c
    exact (inferInstance : Epi (((evaluation _ _).obj c).map η))
  · intros
    apply NatTrans.epi_of_epi_app

中文:
定理 NatTrans.epi_iff_epi_app'
  条件: {F G : C ⥤ D} (η : F ⟶ G)
  结论: Epi η ↔ 对任意 c, Epi (η.app c)
  证明: by
  constructor
  · intro h c
    exact (inferInstance : Epi (((evaluation _ _).obj c).map η))
  · intros
    apply NatTrans.epi_of_epi_app

Depends on / 依赖: NatTrans, NatTrans.epi_of_epi_app, epi_of_epi_app, evaluation, intros
-/
theorem NatTrans.epi_iff_epi_app' {F G : C ⥤ D} (η : F ⟶ G) : Epi η ↔ forall c, Epi (η.app c) := by
  constructor
  · intro h c
    exact (inferInstance : Epi (((evaluation _ _).obj c).map η))
  · intros
    apply NatTrans.epi_of_epi_app

end

end

end CategoryTheory
