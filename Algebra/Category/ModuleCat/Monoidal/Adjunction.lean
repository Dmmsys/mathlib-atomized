/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# The monoidal adjunction between the extension and the restriction of scalars

Let `f : R →+* S` be a morphism of commutative rings. We show that the functor
`extendsScalars f : ModuleCat R ⥤ ModuleCat S` is monoidal, and deduce that
`restrictScalars f : ModuleCat S ⥤ ModuleCat R` is lax monoidal.

-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory ModuleCat MonoidalCategory Limits
  Functor.LaxMonoidal Functor.OplaxMonoidal TensorProduct

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S)

@[simp]
/--
lemma `extendsScalars_map_leftUnitor_inv_one_tmul` / 引理 `extendsScalars_map_leftUnitor_inv_one_tmul`

English:
lemma extendsScalars_map_leftUnitor_inv_one_tmul
  given: (M : ModuleCat R) (m : M)
  proof: f.toAlgebra
    (extendScalars f).map (fun_ M).inv ((1 : S) otimesₜ[R] m) = (1 : S) otimesₜ[R] (1 otimesₜ m) := rfl

@[simp]

中文:
引理 extendsScalars_map_leftUnitor_inv_one_tmul
  条件: (M : ModuleCat R) (m : M)
  证明: f.toAlgebra
    (extendScalars f).map (fun_ M).inv ((1 : S) otimesₜ[R] m) = (1 : S) otimesₜ[R] (1 otimesₜ m) := rfl

@[simp]

Depends on / 依赖: f.toAlgebra, toAlgebra
-/
lemma extendsScalars_map_leftUnitor_inv_one_tmul (M : ModuleCat R) (m : M) :
    letI := f.toAlgebra
    (extendScalars f).map (fun_ M).inv ((1 : S) otimesₜ[R] m) = (1 : S) otimesₜ[R] (1 otimesₜ m) := rfl

@[simp]
/--
lemma `extendsScalars_map_rightUnitor_inv_one_tmul` / 引理 `extendsScalars_map_rightUnitor_inv_one_tmul`

English:
lemma extendsScalars_map_rightUnitor_inv_one_tmul
  given: (M : ModuleCat R) (m : M)
  proof: f.toAlgebra
    (extendScalars f).map (ρ_ M).inv ((1 : S) otimesₜ[R] m) = (1 : S) otimesₜ[R] (m otimesₜ 1) := rfl

中文:
引理 extendsScalars_map_rightUnitor_inv_one_tmul
  条件: (M : ModuleCat R) (m : M)
  证明: f.toAlgebra
    (extendScalars f).map (ρ_ M).inv ((1 : S) otimesₜ[R] m) = (1 : S) otimesₜ[R] (m otimesₜ 1) := rfl

Depends on / 依赖: f.toAlgebra, toAlgebra
-/
lemma extendsScalars_map_rightUnitor_inv_one_tmul (M : ModuleCat R) (m : M) :
    letI := f.toAlgebra
    (extendScalars f).map (ρ_ M).inv ((1 : S) otimesₜ[R] m) = (1 : S) otimesₜ[R] (m otimesₜ 1) := rfl

set_option backward.isDefEq.respectTransparency.types false in
open ModuleCat.MonoidalCategory in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (extendScalars f).Monoidal
  body: letI : Algebra R S := f.toAlgebra
  Functor.CoreMonoidal.toMonoidal
    (.mk'
      (εIso := (AlgebraTensorModule.rid R S S).symm.toModuleIso)
      (μIso := fun M₁ M₂ => (AlgebraTensorModule.distribBaseChange R S M₁ M₂).symm.toModuleIso)
      (μIso_inv_natural_left := fun {M₁ M₁'} g M₂ =>
        

中文:
实例 :
  签名: (extendScalars f).Monoidal
  定义体: letI : Algebra R S := f.toAlgebra
  Functor.CoreMonoidal.toMonoidal
    (.mk'
      (εIso := (AlgebraTensorModule.rid R S S).symm.toModuleIso)
      (μIso := fun M₁ M₂ => (AlgebraTensorModule.distribBaseChange R S M₁ M₂).symm.toModuleIso)
      (μIso_inv_natural_left := fun {M₁ M₁'} g M₂ =>
        

Depends on / 依赖: Algebra, AlgebraTensorModule, AlgebraTensorModule.distribBaseChange, AlgebraTensorModule.rid, CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, distribBaseChange, extendRestrictScalarsAdj, f.toAlgebra, homEquiv, injective, oplax_associa, symm.toModuleIso, tensor_ext, toAlgebra, toModuleIso, toMonoidal
-/
noncomputable instance : (extendScalars f).Monoidal :=
  letI : Algebra R S := f.toAlgebra
  Functor.CoreMonoidal.toMonoidal
    (.mk'
      (εIso := (AlgebraTensorModule.rid R S S).symm.toModuleIso)
      (μIso := fun M₁ M₂ => (AlgebraTensorModule.distribBaseChange R S M₁ M₂).symm.toModuleIso)
      (μIso_inv_natural_left := fun {M₁ M₁'} g M₂ =>
        ((extendRestrictScalarsAdj f).homEquiv _ _).injective
          (tensor_ext (fun _ _ => rfl)))
      (μIso_inv_natural_right := fun {M₂ M₂'} M₁ g =>
        ((extendRestrictScalarsAdj f).homEquiv _ _).injective
          (tensor_ext (fun _ _ => rfl)))
      (oplax_associativity := fun M₁ M₂ M₃ =>
        ((extendRestrictScalarsAdj f).homEquiv _ _).injective
          (tensor_ext₃' (fun _ _ _ => rfl)))
      (oplax_left_unitality := fun M => by
        ext m
        dsimp
        rw [MonoidalCategory.leftUnitor_inv_apply]
        erw [AlgebraTensorModule.distribBaseChange_tmul,
          MonoidalCategory.whiskerRight_apply,
          AlgebraTensorModule.rid_tmul]
        rw [one_smul]
        rfl)
      (oplax_right_unitality := fun M => by
        ext m
        dsimp
        rw [MonoidalCategory.rightUnitor_inv_apply]
        erw [AlgebraTensorModule.distribBaseChange_tmul,
          MonoidalCategory.whiskerLeft_apply,
          AlgebraTensorModule.rid_tmul]
        rw [one_smul]
        rfl))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `extendScalars_ε` / 引理 `extendScalars_ε`

English:
lemma extendScalars_ε
  proof: f.toAlgebra
    dsimp% ε (extendScalars f) = (AlgebraTensorModule.rid R S S).toModuleIso.inv := rfl

中文:
引理 extendScalars_ε
  证明: f.toAlgebra
    dsimp% ε (extendScalars f) = (AlgebraTensorModule.rid R S S).toModuleIso.inv := rfl

Depends on / 依赖: f.toAlgebra, toAlgebra
-/
lemma extendScalars_ε :
    letI := f.toAlgebra
    dsimp% ε (extendScalars f) = (AlgebraTensorModule.rid R S S).toModuleIso.inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `extendScalars_η` / 引理 `extendScalars_η`

English:
lemma extendScalars_η
  proof: f.toAlgebra
    dsimp% η (extendScalars f) = (AlgebraTensorModule.rid R S S).toModuleIso.hom := rfl

中文:
引理 extendScalars_η
  证明: f.toAlgebra
    dsimp% η (extendScalars f) = (AlgebraTensorModule.rid R S S).toModuleIso.hom := rfl

Depends on / 依赖: f.toAlgebra, toAlgebra
-/
lemma extendScalars_η :
    letI := f.toAlgebra
    dsimp% η (extendScalars f) = (AlgebraTensorModule.rid R S S).toModuleIso.hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `extendScalars_μ` / 引理 `extendScalars_μ`

English:
lemma extendScalars_μ
  given: (M₁ M₂ : ModuleCat R)
  proof: f.toAlgebra
    dsimp% μ (extendScalars f) M₁ M₂ =
      (AlgebraTensorModule.distribBaseChange R S M₁ M₂).toModuleIso.inv :=
  rfl

中文:
引理 extendScalars_μ
  条件: (M₁ M₂ : ModuleCat R)
  证明: f.toAlgebra
    dsimp% μ (extendScalars f) M₁ M₂ =
      (AlgebraTensorModule.distribBaseChange R S M₁ M₂).toModuleIso.inv :=
  rfl

Depends on / 依赖: f.toAlgebra, toAlgebra
-/
lemma extendScalars_μ (M₁ M₂ : ModuleCat R) :
    letI := f.toAlgebra
    dsimp% μ (extendScalars f) M₁ M₂ =
      (AlgebraTensorModule.distribBaseChange R S M₁ M₂).toModuleIso.inv :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `extendScalars_δ` / 引理 `extendScalars_δ`

English:
lemma extendScalars_δ
  given: (M₁ M₂ : ModuleCat R)
  proof: f.toAlgebra
    dsimp% δ (extendScalars f) M₁ M₂ =
      (AlgebraTensorModule.distribBaseChange R S M₁ M₂).toModuleIso.hom :=
  rfl

中文:
引理 extendScalars_δ
  条件: (M₁ M₂ : ModuleCat R)
  证明: f.toAlgebra
    dsimp% δ (extendScalars f) M₁ M₂ =
      (AlgebraTensorModule.distribBaseChange R S M₁ M₂).toModuleIso.hom :=
  rfl

Depends on / 依赖: f.toAlgebra, toAlgebra
-/
lemma extendScalars_δ (M₁ M₂ : ModuleCat R) :
    letI := f.toAlgebra
    dsimp% δ (extendScalars f) M₁ M₂ =
      (AlgebraTensorModule.distribBaseChange R S M₁ M₂).toModuleIso.hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `extendScalars_δ_tmul` / 引理 `extendScalars_δ_tmul`

English:
lemma extendScalars_δ_tmul
  given: (M₁ M₂ : ModuleCat R) (m₁ : M₁) (m₂ : M₂)
  proof: f.toAlgebra
    dsimp% δ (extendScalars f) M₁ M₂ (((1 : S) otimesₜ[R] (m₁ otimesₜ[R] m₂) :)) =
      ((1 : S) otimesₜ[R] m₁) otimesₜ[S] ((1 : S) otimesₜ[R] m₂) := rfl

中文:
引理 extendScalars_δ_tmul
  条件: (M₁ M₂ : ModuleCat R) (m₁ : M₁) (m₂ : M₂)
  证明: f.toAlgebra
    dsimp% δ (extendScalars f) M₁ M₂ (((1 : S) otimesₜ[R] (m₁ otimesₜ[R] m₂) :)) =
      ((1 : S) otimesₜ[R] m₁) otimesₜ[S] ((1 : S) otimesₜ[R] m₂) := rfl

Depends on / 依赖: f.toAlgebra, toAlgebra
-/
lemma extendScalars_δ_tmul (M₁ M₂ : ModuleCat R) (m₁ : M₁) (m₂ : M₂) :
    letI := f.toAlgebra
    dsimp% δ (extendScalars f) M₁ M₂ (((1 : S) otimesₜ[R] (m₁ otimesₜ[R] m₂) :)) =
      ((1 : S) otimesₜ[R] m₁) otimesₜ[S] ((1 : S) otimesₜ[R] m₂) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (restrictScalars f).LaxMonoidal
  body: (extendRestrictScalarsAdj f).rightAdjointLaxMonoidal

中文:
实例 :
  签名: (restrictScalars f).LaxMonoidal
  定义体: (extendRestrictScalarsAdj f).rightAdjointLaxMonoidal

Depends on / 依赖: extendRestrictScalarsAdj, rightAdjointLaxMonoidal
-/
noncomputable instance : (restrictScalars f).LaxMonoidal :=
  (extendRestrictScalarsAdj f).rightAdjointLaxMonoidal

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `restrictScalars_η` / 引理 `restrictScalars_η`

English:
lemma restrictScalars_η
  given: (r : R)
  proof: by
  let := f.toAlgebra
  dsimp [Adjunction.rightAdjointLaxMonoidal_ε]
  rw [extendRestrictScalarsAdj_homEquiv_apply]; rw [extendScalars_η]
  erw [AlgebraTensorModule.rid_tmul]
  rw [RingHom.smul_toAlgebra]; rw [mul_one]

中文:
引理 restrictScalars_η
  条件: (r : R)
  证明: by
  let := f.toAlgebra
  dsimp [Adjunction.rightAdjointLaxMonoidal_ε]
  rw [extendRestrictScalarsAdj_homEquiv_apply]; rw [extendScalars_η]
  erw [AlgebraTensorModule.rid_tmul]
  rw [RingHom.smul_toAlgebra]; rw [mul_one]

Depends on / 依赖: Adjunction, Adjunction.rightAdjointLaxMonoidal_, AlgebraTensorModule, AlgebraTensorModule.rid_tmul, RingHom, RingHom.smul_toAlgebra, extendRestrictScalarsAdj_homEquiv_apply, f.toAlgebra, mul_one, rid_tmul, smul_toAlgebra, toAlgebra
-/
lemma restrictScalars_η (r : R) :
    ε (restrictScalars f) r = f r := by
  let := f.toAlgebra
  dsimp [Adjunction.rightAdjointLaxMonoidal_ε]
  rw [extendRestrictScalarsAdj_homEquiv_apply]; rw [extendScalars_η]
  erw [AlgebraTensorModule.rid_tmul]
  rw [RingHom.smul_toAlgebra]; rw [mul_one]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `restrictScalars_μ_tmul` / 引理 `restrictScalars_μ_tmul`

English:
lemma restrictScalars_μ_tmul
  given: (M₁ M₂ : ModuleCat S) (m₁ : M₁) (m₂ : M₂)
  proof: by
  dsimp [Adjunction.rightAdjointLaxMonoidal_μ]
  rw [extendRestrictScalarsAdj_homEquiv_apply]
  dsimp
  rw [extendScalars_δ_tmul]; rw [tensorHom_tmul]; rw [extendRestrictScalarsAdj_counit_app_apply_one_tmul]; rw [extendRestrictScalarsAdj_counit_app_apply_one_tmul]

中文:
引理 restrictScalars_μ_tmul
  条件: (M₁ M₂ : ModuleCat S) (m₁ : M₁) (m₂ : M₂)
  证明: by
  dsimp [Adjunction.rightAdjointLaxMonoidal_μ]
  rw [extendRestrictScalarsAdj_homEquiv_apply]
  dsimp
  rw [extendScalars_δ_tmul]; rw [tensorHom_tmul]; rw [extendRestrictScalarsAdj_counit_app_apply_one_tmul]; rw [extendRestrictScalarsAdj_counit_app_apply_one_tmul]

Depends on / 依赖: Adjunction, Adjunction.rightAdjointLaxMonoidal_, extendRestrictScalarsAdj_counit_app_apply_one_tmul, extendRestrictScalarsAdj_homEquiv_apply, tensorHom_tmul
-/
lemma restrictScalars_μ_tmul (M₁ M₂ : ModuleCat S) (m₁ : M₁) (m₂ : M₂) :
    dsimp% μ (restrictScalars f) M₁ M₂ (m₁ otimesₜ m₂) = m₁ otimesₜ m₂ := by
  dsimp [Adjunction.rightAdjointLaxMonoidal_μ]
  rw [extendRestrictScalarsAdj_homEquiv_apply]
  dsimp
  rw [extendScalars_δ_tmul]; rw [tensorHom_tmul]; rw [extendRestrictScalarsAdj_counit_app_apply_one_tmul]; rw [extendRestrictScalarsAdj_counit_app_apply_one_tmul]

end ModuleCat
