/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.SequentialProduct
public import Mathlib.CategoryTheory.Sites.Coherent.SequentialLimit
public import Mathlib.Condensed.Light.Functors
public import Mathlib.Condensed.Light.Limits
/-!

# Epimorphisms of light condensed objects

This file characterises epimorphisms in light condensed sets and modules as the locally surjective
morphisms. Here, the condition of locally surjective is phrased in terms of continuous surjections
of light profinite sets.

Further, we prove that the functor `lim : Discrete ℕ ⥤ LightCondMod R` preserves epimorphisms.
-/

public section

universe v u w u' v'

open CategoryTheory Sheaf Limits GrothendieckTopology

namespace LightCondensed

variable (A : Type u') [Category.{v'} A] {FA : A -> A -> Type*} {CA : A -> Type w}
variable [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [PreservesFiniteProducts (CategoryTheory.forget A)]

variable {X Y : LightCondensed.{u} A} (f : X ⟶ Y)

/--
lemma `isLocallySurjective_iff_locallySurjective_on_lightProfinite` / 引理 `isLocallySurjective_iff_locallySurjective_on_lightProfinite`

English:
lemma isLocallySurjective_iff_locallySurjective_on_lightProfinite
  statement: IsLocallySurjective f ↔
  proof: by
  rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff]
  simp_rw [LightProfinite.effectiveEpi_iff_surjective]

中文:
引理 isLocallySurjective_iff_locallySurjective_on_lightProfinite
  结论: 是LocallySurjective f ↔
  证明: by
  rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff]
  simp_rw [LightProfinite.effectiveEpi_iff_surjective]

Depends on / 依赖: LightProfinite, LightProfinite.effectiveEpi_iff_surjective, coherentTopology, coherentTopology.isLocallySurjective_iff, effectiveEpi_iff_surjective, isLocallySurjective_iff, regularTopology, regularTopology.isLocallySurjective_iff, simp_rw
-/
lemma isLocallySurjective_iff_locallySurjective_on_lightProfinite : IsLocallySurjective f ↔
    forall (S : LightProfinite) (y : ToType (Y.obj.obj ⟨S⟩)),
      (exists (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ)
        (x : ToType (X.obj.obj ⟨S'⟩)),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) := by
  rw [coherentTopology.isLocallySurjective_iff]; rw [regularTopology.isLocallySurjective_iff]
  simp_rw [LightProfinite.effectiveEpi_iff_surjective]

end LightCondensed

namespace LightCondSet

variable {X Y : LightCondSet.{u}} (f : X ⟶ Y)

/--
lemma `epi_iff_locallySurjective_on_lightProfinite` / 引理 `epi_iff_locallySurjective_on_lightProfinite`

English:
lemma epi_iff_locallySurjective_on_lightProfinite
  statement: Epi f ↔
  proof: by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

中文:
引理 epi_iff_locallySurjective_on_lightProfinite
  结论: 满态射 f ↔
  证明: by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

Depends on / 依赖: LightCondensed, LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite, isLocallySurjective_iff_epi, isLocallySurjective_iff_locallySurjective_on_lightProfinite
-/
lemma epi_iff_locallySurjective_on_lightProfinite : Epi f ↔
    forall (S : LightProfinite) (y : Y.obj.obj ⟨S⟩),
      (exists (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.obj.obj ⟨S'⟩),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R] {X Y : LightCondMod.{u} R} (f : X ⟶ Y)

/--
lemma `epi_iff_locallySurjective_on_lightProfinite` / 引理 `epi_iff_locallySurjective_on_lightProfinite`

English:
lemma epi_iff_locallySurjective_on_lightProfinite
  statement: Epi f ↔
  proof: by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

中文:
引理 epi_iff_locallySurjective_on_lightProfinite
  结论: 满态射 f ↔
  证明: by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

Depends on / 依赖: LightCondensed, LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite, isLocallySurjective_iff_epi, isLocallySurjective_iff_locallySurjective_on_lightProfinite
-/
lemma epi_iff_locallySurjective_on_lightProfinite : Epi f ↔
    forall (S : LightProfinite) (y : Y.obj.obj ⟨S⟩),
      (exists (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.obj.obj ⟨S'⟩),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (LightCondensed.forget R).ReflectsEpimorphisms
  body: by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.hom).mpr hf

中文:
实例 :
  签名: (LightCondensed.forget R).反映满态射
  定义体: by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.hom).mpr hf

Depends on / 依赖: Presheaf, Presheaf.isLocallySurjective_iff_whisker_forget, Sheaf.isLocallySurjective_iff_epi, f.hom, isLocallySurjective_iff_epi, isLocallySurjective_iff_whisker_forget
-/
instance : (LightCondensed.forget R).ReflectsEpimorphisms where
  reflects f hf := by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.hom).mpr hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (LightCondensed.forget R).PreservesEpimorphisms
  body: by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.hom).mp hf

中文:
实例 :
  签名: (LightCondensed.forget R).保持Epimorphisms
  定义体: by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.hom).mp hf

Depends on / 依赖: Presheaf, Presheaf.isLocallySurjective_iff_whisker_forget, Sheaf.isLocallySurjective_iff_epi, f.hom, isLocallySurjective_iff_epi, isLocallySurjective_iff_whisker_forget
-/
instance : (LightCondensed.forget R).PreservesEpimorphisms where
  preserves f hf := by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.hom).mp hf

set_option backward.isDefEq.respectTransparency false in
/--
lemma `factorsThru_lightProfinite_epi_of_epi` / 引理 `factorsThru_lightProfinite_epi_of_epi`

English:
lemma factorsThru_lightProfinite_epi_of_epi
  statement: [Epi f]
  proof: by
  have : Epi ((LightCondensed.forget _).map f) := inferInstance
  rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite] at this
obtain ⟨T, π, hπ, x, hx⟩ := this S (coherentTopology LightProfinite).yonedaEquiv
    (LightCondensed.freeForgetAdjunction R).homEquiv S.toCondensed Y p
  refine 

中文:
引理 factorsThru_lightProfinite_epi_of_epi
  结论: [满态射 f]
  证明: by
  have : Epi ((LightCondensed.forget _).map f) := inferInstance
  rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite] at this
obtain ⟨T, π, hπ, x, hx⟩ := this S (coherentTopology LightProfinite).yonedaEquiv
    (LightCondensed.freeForgetAdjunction R).homEquiv S.toCondensed Y p
  refine 

Depends on / 依赖: Functor, Functor.comp_map, LightCondSet, LightCondSet.epi_iff_locallySurjective_on_lightProfinite, LightCondensed, LightCondensed.forget, LightCondensed.freeForgetAdjunction, LightProfinite, LightProfinite.epi_iff_surjective, S.toCondensed, T.toCondensed, coherentTopology, comp_map, epi_iff_locallySurjective_on_lightProfinite, epi_iff_surjective, forget, freeForgetAdjunction, homEquiv, toCondensed, yonedaEquiv
-/
lemma factorsThru_lightProfinite_epi_of_epi [Epi f]
    {S : LightProfinite} (p : (LightCondensed.free R).obj S.toCondensed ⟶ Y) :
      exists (T : LightProfinite) (π : T ⟶ S) (g : ((LightCondensed.free R).obj T.toCondensed) ⟶ X),
        Epi π ∧ (lightProfiniteToLightCondSet ⋙ (LightCondensed.free R)).map π ≫ p = g ≫ f := by
  have : Epi ((LightCondensed.forget _).map f) := inferInstance
  rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite] at this
obtain ⟨T, π, hπ, x, hx⟩ := this S (coherentTopology LightProfinite).yonedaEquiv
    (LightCondensed.freeForgetAdjunction R).homEquiv S.toCondensed Y p
  refine ⟨T, π, ((LightCondensed.freeForgetAdjunction R).homEquiv T.toCondensed X).symm
    ((coherentTopology LightProfinite).yonedaEquiv.symm x),
    (LightProfinite.epi_iff_surjective π).mpr hπ, ?_⟩
  rw [Functor.comp_map]; rw [← Adjunction.homEquiv_naturality_left_square_iff
    (LightCondensed.freeForgetAdjunction R)]; rw [Sheaf.hom_ext_iff]; rw [Equiv.apply_symm_apply]; rw [GrothendieckTopology.yonedaEquiv_symm_naturality_right]; rw [hx]; rw [GrothendieckTopology.map_yonedaEquiv']; rw [← GrothendieckTopology.yonedaEquiv_symm_naturality_right]
  rfl

end LightCondMod

namespace LightCondensed

variable (R : Type*) [Ring R]
variable {F : Natᵒᵖ ⥤ LightCondMod R} {c : Cone F} (hc : IsLimit c)
  (hF : forall n, Epi (F.map (homOfLE (Nat.le_succ n)).op))

include hc hF in
/--
lemma `epi_π_app_zero_of_epi` / 引理 `epi_π_app_zero_of_epi`

English:
lemma epi_π_app_zero_of_epi
  statement: Epi (c.π.app ⟨0⟩)
  proof: by
  apply Functor.epi_of_epi_map (forget R)
  change Epi (((forget R).mapCone c).π.app ⟨0⟩)
  apply coherentTopology.epi_π_app_zero_of_epi
  · simp only [LightProfinite.effectiveEpi_iff_surjective]
    exact fun x h => Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit x) h
  · have :=

中文:
引理 epi_π_app_zero_of_epi
  结论: 满态射 (c.π.app ⟨0⟩)
  证明: by
  apply Functor.epi_of_epi_map (forget R)
  change Epi (((forget R).mapCone c).π.app ⟨0⟩)
  apply coherentTopology.epi_π_app_zero_of_epi
  · simp only [LightProfinite.effectiveEpi_iff_surjective]
    exact fun x h => Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit x) h
  · have :=

Depends on / 依赖: Concrete, Concrete.surjective_, Functor, Functor.epi_of_epi_map, LightProfinite, LightProfinite.effectiveEpi_iff_surjective, coherentTopology, coherentTopology.epi_, effectiveEpi_iff_surjective, epi_of_epi_map, forget, freeForgetAdjunction, isLimit, isLimitOfPreserves, isRightAdjoint, limit.isLimit, mapCone, map_epi
-/
lemma epi_π_app_zero_of_epi : Epi (c.π.app ⟨0⟩) := by
  apply Functor.epi_of_epi_map (forget R)
  change Epi (((forget R).mapCone c).π.app ⟨0⟩)
  apply coherentTopology.epi_π_app_zero_of_epi
  · simp only [LightProfinite.effectiveEpi_iff_surjective]
    exact fun x h => Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit x) h
  · have := (freeForgetAdjunction R).isRightAdjoint
    exact isLimitOfPreserves _ hc
  · exact fun _ => (forget R).map_epi _

end LightCondensed

open CategoryTheory.Limits.SequentialProduct

namespace LightCondensed

variable (n : Nat)

attribute [local instance] functorMap_epi Abelian.hasFiniteBiproducts

variable {R : Type u} [Ring R] {M N : Nat -> LightCondMod.{u} R} (f : forall n, M n ⟶ N n) [forall n, Epi (f n)]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (Limits.Pi.map f)
  body: epi_π_app_zero_of_epi R (isLimit f) (fun n => by
    simp only [Nat.succ_eq_add_one, Functor.ofOpSequence_obj, homOfLE_leOfHom,
      Functor.ofOpSequence_map_homOfLE_succ]
    infer_instance)

中文:
实例 :
  签名: 满态射 (Limits.依赖函数类型.map f)
  定义体: epi_π_app_zero_of_epi R (isLimit f) (fun n => by
    simp only [Nat.succ_eq_add_one, Functor.ofOpSequence_obj, homOfLE_leOfHom,
      Functor.ofOpSequence_map_homOfLE_succ]
    infer_instance)

Depends on / 依赖: Functor, Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_obj, Nat.succ_eq_add_one, homOfLE_leOfHom, infer_instance, isLimit, ofOpSequence_map_homOfLE_succ, ofOpSequence_obj, succ_eq_add_one
-/
instance : Epi (Limits.Pi.map f) :=
  epi_π_app_zero_of_epi R (isLimit f) (fun n => by
    simp only [Nat.succ_eq_add_one, Functor.ofOpSequence_obj, homOfLE_leOfHom,
      Functor.ofOpSequence_map_homOfLE_succ]
    infer_instance)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (lim (J := Discrete Nat) (C := LightCondMod R)).PreservesEpimorphisms
  body: by
    have : lim.map f = (Pi.isoLimit _).inv ≫ Limits.Pi.map (f.app ⟨·⟩) ≫ (Pi.isoLimit _).hom := by
      apply limit.hom_ext
      intro ⟨n⟩
      simp
    rw [this]
    dsimp
    infer_instance

中文:
实例 :
  签名: (lim (J := 离散 自然数) (C := LightCondMod R)).保持Epimorphisms
  定义体: by
    have : lim.map f = (Pi.isoLimit _).inv ≫ Limits.Pi.map (f.app ⟨·⟩) ≫ (Pi.isoLimit _).hom := by
      apply limit.hom_ext
      intro ⟨n⟩
      simp
    rw [this]
    dsimp
    infer_instance

Depends on / 依赖: Discrete, LightCondMod, PreservesEpimorphisms
-/
instance : (lim (J := Discrete Nat) (C := LightCondMod R)).PreservesEpimorphisms where
  preserves f _ := by
    have : lim.map f = (Pi.isoLimit _).inv ≫ Limits.Pi.map (f.app ⟨·⟩) ≫ (Pi.isoLimit _).hom := by
      apply limit.hom_ext
      intro ⟨n⟩
      simp
    rw [this]
    dsimp
    infer_instance

end LightCondensed
