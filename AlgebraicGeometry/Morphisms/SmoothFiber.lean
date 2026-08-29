/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth morphisms and their fibers

## Main results

- `Smooth.of_smooth_fiberToSpecResidueField`: A flat morphism, locally of
  finite presentation and smooth fibers is smooth.

-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Smooth.of_smooth_fiberToSpecResidueField` / 引理 `Smooth.of_smooth_fiberToSpecResidueField`

English:
lemma Smooth.of_smooth_fiberToSpecResidueField
  statement: [LocallyOfFinitePresentation f] [Flat f]
  proof: by
  wlog h : exists R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Smooth) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    refine this _ (fun y => ?_) ⟨_, rfl⟩
    apply MorphismProperty.of_isPullback
    · exact isPullback_fiberToSpecResidueField_of_isPull

中文:
引理 光滑.of_smooth_fiberToSpecResidueField
  结论: [局部有限呈现 f] [平坦 f]
  证明: by
  wlog h : exists R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Smooth) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    refine this _ (fun y => ?_) ⟨_, rfl⟩
    apply MorphismProperty.of_isPullback
    · exact isPullback_fiberToSpecResidueField_of_isPull

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff_of_openCover, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_openCover, MorphismProperty, MorphismProperty.of_isPullback, Scheme, Scheme.Cover.pullbackHom, Smooth, X.affineCover, Y.affineCover, affineCover, generalizing, iff_of_openCover, infer_instance, isPullback_fiberToSpecResidueField_of_isPullback, of_hasPullback, of_isPullback
-/
lemma Smooth.of_smooth_fiberToSpecResidueField [LocallyOfFinitePresentation f] [Flat f]
    (h : forall y, Smooth (f.fiberToSpecResidueField y)) :
    Smooth f := by
  wlog h : exists R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Smooth) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    refine this _ (fun y => ?_) ⟨_, rfl⟩
    apply MorphismProperty.of_isPullback
    · exact isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback _ _) _
    · infer_instance
  obtain ⟨R, rfl⟩ := h
  wlog h : exists S, X = Spec S generalizing f X
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) X.affineCover]
    intro i
    have _ (y) : Smooth (pullback.snd f ((Spec R).fromSpecResidueField y)) :=
inferInstanceAs Smooth (f.fiberToSpecResidueField y)
    refine this _ (fun y => ?_) ⟨_, rfl⟩
    rw [Scheme.Hom.fiberToSpecResidueField]; rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨S, rfl⟩ := h
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [HasRingHomProperty.Spec_iff] at *
  algebraize [φ.hom]
  refine Algebra.Smooth.of_formallySmooth_fiber fun p hp => ?_
  rw [← RingHom.formallySmooth_algebraMap]
  refine RingHom.Smooth.formallySmooth ?_
  rw [← CommRingCat.hom_ofHom (algebraMap p.ResidueField (p.Fiber ↑S))]; rw [← HasRingHomProperty.Spec_iff (P := @Smooth)]; rw [← MorphismProperty.arrow_mk_iso_iff (P := @Smooth)
    (Spec.fiberToSpecResidueFieldIso R S ⟨p]; rw [hp⟩)]
  exact h ⟨p, hp⟩

end AlgebraicGeometry
