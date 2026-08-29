/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Internal
public import Mathlib.Condensed.Light.Epi
public import Mathlib.Condensed.Light.Functors
public import Mathlib.Condensed.Light.Monoidal
/-!

# Characterization of internal projectivity in light condensed modules

This file gives an explicit condition on light condensed modules over a ring `R` to be internally
projective, namely the following:

`internallyProjective_iff_tensor_condition`: `P : LightCondMod R` is internally projective if and
only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : P ⊗ R[S] ⟶ B`, there exists a `S' : LightProfinite`
with a surjection `π : S' ⟶ S` and a morphism `g' : P ⊗ R[S'] ⟶ A`, making the diagram
```
P ⊗ R[S'] --> A
  | |
  v v
P ⊗ R[S] --> B
```
commute.

We also provide the analogous characterization with the tensor product commuted the other way around
(see `internallyProjective_iff_tensor_condition'`), and the special cases when `P` is the free
condensed module on a condensed set (`free_internallyProjective_iff_tensor_condition`,
`free_internallyProjective_iff_tensor_condition'`) and when `P` is the free condensed module on a
light profinite set (`free_lightProfinite_internallyProjective_iff_tensor_condition`/
`free_lightProfinite_internallyProjective_iff_tensor_condition'`).
-/

@[expose] public section

universe u

open CategoryTheory Category MonoidalCategory Functor Monoidal LaxMonoidal OplaxMonoidal

variable (R : Type u) [CommRing R]

namespace LightCondensed

/--
Definition of `ihomPoints` / `ihomPoints` 的定义

English:
definition ihomPoints
  signature: (A B : LightCondMod.{u} R) (S : LightProfinite)
  body: (((freeForgetAdjunction R).homEquiv _ _).trans
    (coherentTopology _).yonedaEquiv).symm.trans
      ((ihom.adjunction A).homEquiv _ _).symm

中文:
定义 ihomPoints
  签名: (A B : LightCondMod.{u} R) (S : LightProfinite)
  定义体: (((freeForgetAdjunction R).homEquiv _ _).trans
    (coherentTopology _).yonedaEquiv).symm.trans
      ((ihom.adjunction A).homEquiv _ _).symm

Depends on / 依赖: adjunction, coherentTopology, freeForgetAdjunction, homEquiv, ihom.adjunction, symm.trans, yonedaEquiv
-/
noncomputable def ihomPoints (A B : LightCondMod.{u} R) (S : LightProfinite) :
    (A ⟶[LightCondMod R] B).obj.obj ⟨S⟩ ≃ ((A otimes ((free R).obj S.toCondensed)) ⟶ B) :=
  (((freeForgetAdjunction R).homEquiv _ _).trans
    (coherentTopology _).yonedaEquiv).symm.trans
      ((ihom.adjunction A).homEquiv _ _).symm

/--
lemma `ihomPoints_apply` / 引理 `ihomPoints_apply`

English:
lemma ihomPoints_apply
  statement: (A B : LightCondMod.{u} R) (S : LightProfinite)
  proof: rfl

中文:
引理 ihomPoints_apply
  结论: (A B : LightCondMod.{u} R) (S : LightProfinite)
  证明: rfl
-/
lemma ihomPoints_apply (A B : LightCondMod.{u} R) (S : LightProfinite)
    (x : (A ⟶[LightCondMod R] B).obj.obj ⟨S⟩) :
    ihomPoints R A B S x = (MonoidalClosed.uncurry (((freeForgetAdjunction R).homEquiv _ _).symm
      ((coherentTopology LightProfinite.{u}).yonedaEquiv.symm x))) :=
  rfl

/--
lemma `ihomPoints_symm_apply` / 引理 `ihomPoints_symm_apply`

English:
lemma ihomPoints_symm_apply
  statement: (A B : LightCondMod.{u} R) (S : LightProfinite)
  proof: rfl

中文:
引理 ihomPoints_symm_apply
  结论: (A B : LightCondMod.{u} R) (S : LightProfinite)
  证明: rfl
-/
lemma ihomPoints_symm_apply (A B : LightCondMod.{u} R) (S : LightProfinite)
    (x : (A otimes ((free R).obj S.toCondensed)) ⟶ B) :
    (ihomPoints R A B S).symm x = (coherentTopology LightProfinite.{u}).yonedaEquiv
      ((freeForgetAdjunction R).homEquiv _ _ (MonoidalClosed.curry x)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ihom_map_val_app` / 引理 `ihom_map_val_app`

English:
lemma ihom_map_val_app
  statement: (A B P : LightCondMod.{u} R) (S : LightProfinite) (e : A ⟶ B)
  proof: by
  apply (ihomPoints R P B S).injective
  simp only [ihomPoints_apply, ← MonoidalClosed.uncurry_natural_right,
    ← Adjunction.homEquiv_naturality_right_symm, Equiv.apply_symm_apply]
  congr
  apply (coherentTopology LightProfinite.{u}).yonedaEquiv.injective
  simp [dsimp% GrothendieckTopology.yonedaEquiv_comp]

中文:
引理 ihom_map_val_app
  结论: (A B P : LightCondMod.{u} R) (S : LightProfinite) (e : A ⟶ B)
  证明: by
  apply (ihomPoints R P B S).injective
  simp only [ihomPoints_apply, ← MonoidalClosed.uncurry_natural_right,
    ← Adjunction.homEquiv_naturality_right_symm, Equiv.apply_symm_apply]
  congr
  apply (coherentTopology LightProfinite.{u}).yonedaEquiv.injective
  simp [dsimp% GrothendieckTopology.yonedaEquiv_comp]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_right_symm, Equiv.apply_symm_apply, GrothendieckTopology, GrothendieckTopology.yonedaEquiv_comp, LightProfinite, MonoidalClosed, MonoidalClosed.uncurry_natural_right, apply_symm_apply, coherentTopology, homEquiv_naturality_right_symm, ihomPoints, ihomPoints_apply, injective, uncurry_natural_right, yonedaEquiv, yonedaEquiv.injective, yonedaEquiv_comp
-/
lemma ihom_map_val_app (A B P : LightCondMod.{u} R) (S : LightProfinite) (e : A ⟶ B)
    (x : (P ⟶[LightCondMod R] A).obj.obj ⟨S⟩) :
    (((ihom P).map e).hom.app ⟨S⟩) x = (ihomPoints R P B S).symm (ihomPoints R P A S x ≫ e) := by
  apply (ihomPoints R P B S).injective
  simp only [ihomPoints_apply, ← MonoidalClosed.uncurry_natural_right,
    ← Adjunction.homEquiv_naturality_right_symm, Equiv.apply_symm_apply]
  congr
  apply (coherentTopology LightProfinite.{u}).yonedaEquiv.injective
  simp [dsimp% GrothendieckTopology.yonedaEquiv_comp]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ihomPoints_symm_comp` / 引理 `ihomPoints_symm_comp`

English:
lemma ihomPoints_symm_comp
  statement: (B P : LightCondMod.{u} R) (S S' : LightProfinite) (π : S ⟶ S')
  proof: by
  simpa [ihomPoints_symm_apply, MonoidalClosed.curry_natural_left, Adjunction.homEquiv_apply] using!
    (GrothendieckTopology.yonedaEquiv_naturality _ _ _).symm

中文:
引理 ihomPoints_symm_comp
  结论: (B P : LightCondMod.{u} R) (S S' : LightProfinite) (π : S ⟶ S')
  证明: by
  simpa [ihomPoints_symm_apply, MonoidalClosed.curry_natural_left, Adjunction.homEquiv_apply] using!
    (GrothendieckTopology.yonedaEquiv_naturality _ _ _).symm

Depends on / 依赖: Adjunction, Adjunction.homEquiv_apply, GrothendieckTopology, GrothendieckTopology.yonedaEquiv_naturality, MonoidalClosed, MonoidalClosed.curry_natural_left, curry_natural_left, homEquiv_apply, ihomPoints_symm_apply, yonedaEquiv_naturality
-/
lemma ihomPoints_symm_comp (B P : LightCondMod.{u} R) (S S' : LightProfinite) (π : S ⟶ S')
    (f : P otimes (free R).obj S'.toCondensed ⟶ B) :
    (ihomPoints R P B S).symm (P ◁ (free R).map (lightProfiniteToLightCondSet.map π) ≫ f) =
      ((P ⟶[LightCondMod R] B).obj.map π.op) ((ihomPoints R P B S').symm f) := by
  simpa [ihomPoints_symm_apply, MonoidalClosed.curry_natural_left, Adjunction.homEquiv_apply] using!
    (GrothendieckTopology.yonedaEquiv_naturality _ _ _).symm

set_option backward.defeqAttrib.useBackward true in
/--
lemma `internallyProjective_iff_tensor_condition` / 引理 `internallyProjective_iff_tensor_condition`

English:
lemma internallyProjective_iff_tensor_condition
  given: (P : LightCondMod R)
  statement: InternallyProjective P ↔
  proof: by
  refine ⟨fun ⟨h⟩ A B e he S g => ?_, fun h => ⟨⟨fun {A B} e he => ?_⟩⟩⟩
  · have hh := h.1 e
    rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite] at hh
    specialize hh S ((ihomPoints R P B S).symm g)
    obtain ⟨S', π, hπ, g', hh⟩ := hh
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _) g', ?_⟩
    rw [ihom_map_val_app] at hh
    apply (ihomPoints R P B S').symm.injective
    rw [hh]
    exact ihomPoints_symm_comp R B P S' S π g
  · rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    specialize h e S ((ihomPoints _ _ _ _) g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _).symm g', ?_⟩
    rw [ihom_map_val_app]
    have := ihomPoints_symm_comp R B P S' S π ((ihomPoints R P B S) g)
    dsimp at hh
    rw [hh] at this
    simp [this, Quiver.Hom.op]

中文:
引理 internallyProjective_iff_tensor_condition
  条件: (P : LightCondMod R)
  结论: 整数ernallyProjective P ↔
  证明: by
  refine ⟨fun ⟨h⟩ A B e he S g => ?_, fun h => ⟨⟨fun {A B} e he => ?_⟩⟩⟩
  · have hh := h.1 e
    rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite] at hh
    specialize hh S ((ihomPoints R P B S).symm g)
    obtain ⟨S', π, hπ, g', hh⟩ := hh
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _) g', ?_⟩
    rw [ihom_map_val_app] at hh
    apply (ihomPoints R P B S').symm.injective
    rw [hh]
    exact ihomPoints_symm_comp R B P S' S π g
  · rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    specialize h e S ((ihomPoints _ _ _ _) g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _).symm g', ?_⟩
    rw [ihom_map_val_app]
    have := ihomPoints_symm_comp R B P S' S π ((ihomPoints R P B S) g)
    dsimp at hh
    rw [hh] at this
    simp [this, Quiver.Hom.op]

Depends on / 依赖: LightCondMod, LightCondMod.epi_iff_locallySurjective_on_lightProfinite, epi_iff_locallySurjective_on_lightProfinite, ihomPoints, ihomPoints_symm_comp, ihom_map_val_app, injective, specialize, symm.injective
-/
lemma internallyProjective_iff_tensor_condition (P : LightCondMod R) : InternallyProjective P ↔
    forall {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (forall (S : LightProfinite) (g : P otimes (free R).obj S.toCondensed ⟶ B), exists (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : P otimes (free R).obj S'.toCondensed ⟶ A),
          (P ◁ ((lightProfiniteToLightCondSet ⋙ free R).map π)) ≫ g = g' ≫ e) := by
  refine ⟨fun ⟨h⟩ A B e he S g => ?_, fun h => ⟨⟨fun {A B} e he => ?_⟩⟩⟩
  · have hh := h.1 e
    rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite] at hh
    specialize hh S ((ihomPoints R P B S).symm g)
    obtain ⟨S', π, hπ, g', hh⟩ := hh
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _) g', ?_⟩
    rw [ihom_map_val_app] at hh
    apply (ihomPoints R P B S').symm.injective
    rw [hh]
    exact ihomPoints_symm_comp R B P S' S π g
  · rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    specialize h e S ((ihomPoints _ _ _ _) g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _).symm g', ?_⟩
    rw [ihom_map_val_app]
    have := ihomPoints_symm_comp R B P S' S π ((ihomPoints R P B S) g)
    dsimp at hh
    rw [hh] at this
    simp [this, Quiver.Hom.op]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `internallyProjective_iff_tensor_condition'` / 引理 `internallyProjective_iff_tensor_condition'`

English:
lemma internallyProjective_iff_tensor_condition'
  given: (P : LightCondMod R)
  statement: InternallyProjective P ↔
  proof: by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((β_ _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).inv ≫ g', ?_⟩
    simp [← hh]
  · specialize h e S ((β_ _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).hom ≫ g', ?_⟩
    simp [← hh]

中文:
引理 internallyProjective_iff_tensor_condition'
  条件: (P : LightCondMod R)
  结论: 整数ernallyProjective P ↔
  证明: by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((β_ _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).inv ≫ g', ?_⟩
    simp [← hh]
  · specialize h e S ((β_ _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).hom ≫ g', ?_⟩
    simp [← hh]

Depends on / 依赖: internallyProjective_iff_tensor_condition, specialize
-/
lemma internallyProjective_iff_tensor_condition' (P : LightCondMod R) : InternallyProjective P ↔
    forall {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (forall (S : LightProfinite) (g : (free R).obj S.toCondensed otimes P ⟶ B), exists (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj S'.toCondensed otimes P ⟶ A),
          (((lightProfiniteToLightCondSet ⋙ free R).map π) ▷ P) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((β_ _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).inv ≫ g', ?_⟩
    simp [← hh]
  · specialize h e S ((β_ _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).hom ≫ g', ?_⟩
    simp [← hh]

/--
lemma `free_internallyProjective_iff_tensor_condition` / 引理 `free_internallyProjective_iff_tensor_condition`

English:
lemma free_internallyProjective_iff_tensor_condition
  given: (P : LightCondSet.{u})
  proof: by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp only [← assoc]
    -- Generated by `simp?`. Leaving it unsqueezed is too slow
    simp only [μIso_hom, μIso_inv, Functor.comp_map, δ_natural_right, assoc, δ_μ, comp_id]
  · specialize h e S ((μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]; rw [← assoc]; rw [← assoc]
    -- Generated by `simp? [← μ_natural_right]`.
    -- Leaving it unsqueezed is too slow
    simp only [Functor.comp_map, μIso_hom, ← μ_natural_right, μIso_inv, assoc, μ_δ,
      comp_id]

中文:
引理 free_internallyProjective_iff_tensor_condition
  条件: (P : LightCondSet.{u})
  证明: by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp only [← assoc]
    -- Generated by `simp?`. Leaving it unsqueezed is too slow
    simp only [μIso_hom, μIso_inv, Functor.comp_map, δ_natural_right, assoc, δ_μ, comp_id]
  · specialize h e S ((μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]; rw [← assoc]; rw [← assoc]
    -- Generated by `simp? [← μ_natural_right]`.
    -- Leaving it unsqueezed is too slow
    simp only [Functor.comp_map, μIso_hom, ← μ_natural_right, μIso_inv, assoc, μ_δ,
      comp_id]

Depends on / 依赖: internallyProjective_iff_tensor_condition, specialize
-/
lemma free_internallyProjective_iff_tensor_condition (P : LightCondSet.{u}) :
    InternallyProjective ((free R).obj P) ↔
      forall {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (forall (S : LightProfinite)
        (g : (free R).obj (P otimes S.toCondensed) ⟶ B), exists (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (P otimes S'.toCondensed) ⟶ A),
            ((free R).map (P ◁ ((lightProfiniteToLightCondSet).map π))) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp only [← assoc]
    -- Generated by `simp?`. Leaving it unsqueezed is too slow
    simp only [μIso_hom, μIso_inv, Functor.comp_map, δ_natural_right, assoc, δ_μ, comp_id]
  · specialize h e S ((μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]; rw [← assoc]; rw [← assoc]
    -- Generated by `simp? [← μ_natural_right]`.
    -- Leaving it unsqueezed is too slow
    simp only [Functor.comp_map, μIso_hom, ← μ_natural_right, μIso_inv, assoc, μ_δ,
      comp_id]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `free_internallyProjective_iff_tensor_condition'` / 引理 `free_internallyProjective_iff_tensor_condition'`

English:
lemma free_internallyProjective_iff_tensor_condition'
  given: (P : LightCondSet.{u})
  proof: by
  rw [internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    -- Generated by `simp?`. Leaving it unsqueezed is too slow
    simp only [μIso_inv, comp_obj, Functor.comp_map, μIso_hom, μ_natural_left_assoc, δ_μ_assoc]
  · specialize h e S ((μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]; rw [← assoc]; rw [← assoc]
    -- Generated by `simp? [← μ_natural_left]`
    -- Leaving it unsqueezed is too slow.
    simp only [comp_obj, Functor.comp_map, μIso_hom, ← μ_natural_left, μIso_inv, assoc, μ_δ,
      comp_id]

中文:
引理 free_internallyProjective_iff_tensor_condition'
  条件: (P : LightCondSet.{u})
  证明: by
  rw [internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    -- Generated by `simp?`. Leaving it unsqueezed is too slow
    simp only [μIso_inv, comp_obj, Functor.comp_map, μIso_hom, μ_natural_left_assoc, δ_μ_assoc]
  · specialize h e S ((μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]; rw [← assoc]; rw [← assoc]
    -- Generated by `simp? [← μ_natural_left]`
    -- Leaving it unsqueezed is too slow.
    simp only [comp_obj, Functor.comp_map, μIso_hom, ← μ_natural_left, μIso_inv, assoc, μ_δ,
      comp_id]

Depends on / 依赖: internallyProjective_iff_tensor_condition, specialize
-/
lemma free_internallyProjective_iff_tensor_condition' (P : LightCondSet.{u}) :
    InternallyProjective ((free R).obj P) ↔
      forall {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (forall (S : LightProfinite)
        (g : (free R).obj (S.toCondensed otimes P) ⟶ B), exists (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (S'.toCondensed otimes P) ⟶ A),
            ((free R).map (((lightProfiniteToLightCondSet).map π) ▷ P)) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    -- Generated by `simp?`. Leaving it unsqueezed is too slow
    simp only [μIso_inv, comp_obj, Functor.comp_map, μIso_hom, μ_natural_left_assoc, δ_μ_assoc]
  · specialize h e S ((μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]; rw [← assoc]; rw [← assoc]
    -- Generated by `simp? [← μ_natural_left]`
    -- Leaving it unsqueezed is too slow.
    simp only [comp_obj, Functor.comp_map, μIso_hom, ← μ_natural_left, μIso_inv, assoc, μ_δ,
      comp_id]

attribute [-simp] ObjectProperty.whiskerLeft_def ObjectProperty.whiskerRight_def

/--
lemma `free_lightProfinite_internallyProjective_iff_tensor_condition` / 引理 `free_lightProfinite_internallyProjective_iff_tensor_condition`

English:
lemma free_lightProfinite_internallyProjective_iff_tensor_condition
  given: (P : LightProfinite.{u})
  proof: by
  rw [free_internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc]
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc, ← μ_natural_right_assoc]

中文:
引理 free_lightProfinite_internallyProjective_iff_tensor_condition
  条件: (P : LightProfinite.{u})
  证明: by
  rw [free_internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc]
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc, ← μ_natural_right_assoc]

Depends on / 依赖: free_internallyProjective_iff_tensor_condition, lightProfiniteToLightCondSet, map_comp, map_comp_assoc, specialize
-/
lemma free_lightProfinite_internallyProjective_iff_tensor_condition (P : LightProfinite.{u}) :
    InternallyProjective ((free R).obj P.toCondensed) ↔
      forall {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (forall (S : LightProfinite)
        (g : (free R).obj ((P otimes S).toCondensed) ⟶ B), exists (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (P otimes S').toCondensed ⟶ A),
            ((free R).map (lightProfiniteToLightCondSet.map (P ◁ π))) ≫ g = g' ≫ e) := by
  rw [free_internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc]
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc, ← μ_natural_right_assoc]

/--
lemma `free_lightProfinite_internallyProjective_iff_tensor_condition'` / 引理 `free_lightProfinite_internallyProjective_iff_tensor_condition'`

English:
lemma free_lightProfinite_internallyProjective_iff_tensor_condition'
  given: (P : LightProfinite.{u})
  proof: by
  rw [free_internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc]
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc, ← μ_natural_left_assoc]

中文:
引理 free_lightProfinite_internallyProjective_iff_tensor_condition'
  条件: (P : LightProfinite.{u})
  证明: by
  rw [free_internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc]
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc, ← μ_natural_left_assoc]

Depends on / 依赖: free_internallyProjective_iff_tensor_condition, lightProfiniteToLightCondSet, map_comp, map_comp_assoc, specialize
-/
lemma free_lightProfinite_internallyProjective_iff_tensor_condition' (P : LightProfinite.{u}) :
    InternallyProjective ((free R).obj P.toCondensed) ↔
      forall {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (forall (S : LightProfinite)
        (g : (free R).obj ((S otimes P).toCondensed) ⟶ B), exists (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (S' otimes P).toCondensed ⟶ A),
            ((free R).map (lightProfiniteToLightCondSet.map (π ▷ P))) ≫ g = g' ≫ e) := by
  rw [free_internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g => ?_, fun h A B e he S g => ?_⟩
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc]
  · specialize h e S ((free R).map (μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [assoc]; rw [← hh]
    simp [-map_comp, ← map_comp_assoc, ← μ_natural_left_assoc]

end LightCondensed
