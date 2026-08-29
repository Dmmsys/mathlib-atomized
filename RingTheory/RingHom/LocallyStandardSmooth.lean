/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Smooth is locally standard smooth

In this file we show that a ring homomorphism is smooth if and only if it is locally standard
smooth.
-/

universe u

public section

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S] {f : R ->+* S}

/--
lemma `IsStandardSmooth.smooth` / 引理 `IsStandardSmooth.smooth`

English:
lemma IsStandardSmooth.smooth
  statement: {R S : Type*} [CommRing R] [CommRing S] {f : R ->+* S}
  proof: by
  algebraize [f]
  rw [RingHom.Smooth]
  infer_instance

中文:
引理 IsStandardSmooth.smooth
  结论: {R S : 类型} [CommRing R] [CommRing S] {f : R ->+* S}
  证明: by
  algebraize [f]
  rw [RingHom.Smooth]
  infer_instance

Depends on / 依赖: RingHom, RingHom.Smooth, Smooth, algebraize, infer_instance
-/
lemma IsStandardSmooth.smooth {R S : Type*} [CommRing R] [CommRing S] {f : R ->+* S}
    (hf : IsStandardSmooth f) : Smooth f := by
  algebraize [f]
  rw [RingHom.Smooth]
  infer_instance

/--
theorem `Smooth.locally_isStandardSmooth` / 定理 `Smooth.locally_isStandardSmooth`

English:
theorem Smooth.locally_isStandardSmooth
  given: (hf : f.Smooth)
  statement: Locally IsStandardSmooth f
  proof: by
  algebraize [f]
  obtain ⟨s, hs, h⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R S
  refine ⟨s, hs, fun t ht => ?_⟩
  dsimp only
  rw [← f.algebraMap_toAlgebra]; rw [← IsScalarTower.algebraMap_eq]; rw [isStandardSmooth_algebraMap]
  exact h t ht

中文:
定理 Smooth.locally_isStandardSmooth
  条件: (hf : f.Smooth)
  结论: Locally IsStandardSmooth f
  证明: by
  algebraize [f]
  obtain ⟨s, hs, h⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R S
  refine ⟨s, hs, fun t ht => ?_⟩
  dsimp only
  rw [← f.algebraMap_toAlgebra]; rw [← IsScalarTower.algebraMap_eq]; rw [isStandardSmooth_algebraMap]
  exact h t ht

Depends on / 依赖: Algebra, Algebra.Smooth.exists_span_eq_top_isStandardSmooth, IsScalarTower, IsScalarTower.algebraMap_eq, Smooth, algebraMap_eq, algebraMap_toAlgebra, algebraize, exists_span_eq_top_isStandardSmooth, f.algebraMap_toAlgebra, isStandardSmooth_algebraMap
-/
theorem Smooth.locally_isStandardSmooth (hf : f.Smooth) : Locally IsStandardSmooth f := by
  algebraize [f]
  obtain ⟨s, hs, h⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R S
  refine ⟨s, hs, fun t ht => ?_⟩
  dsimp only
  rw [← f.algebraMap_toAlgebra]; rw [← IsScalarTower.algebraMap_eq]; rw [isStandardSmooth_algebraMap]
  exact h t ht

/--
theorem `smooth_iff_locally_isStandardSmooth` / 定理 `smooth_iff_locally_isStandardSmooth`

English:
theorem smooth_iff_locally_isStandardSmooth
  statement: Smooth f ↔ Locally IsStandardSmooth f
  proof: by
  refine ⟨fun hf => hf.locally_isStandardSmooth, fun hf => ?_⟩
  rw [← locally_iff_of_localizationSpanTarget Smooth.propertyIsLocal.respectsIso
    Smooth.ofLocalizationSpanTarget]
  exact locally_of_locally (fun hf => hf.smooth) hf

中文:
定理 smooth_iff_locally_isStandardSmooth
  结论: Smooth f ↔ Locally IsStandardSmooth f
  证明: by
  refine ⟨fun hf => hf.locally_isStandardSmooth, fun hf => ?_⟩
  rw [← locally_iff_of_localizationSpanTarget Smooth.propertyIsLocal.respectsIso
    Smooth.ofLocalizationSpanTarget]
  exact locally_of_locally (fun hf => hf.smooth) hf

Depends on / 依赖: Smooth, Smooth.ofLocalizationSpanTarget, Smooth.propertyIsLocal.respectsIso, hf.locally_isStandardSmooth, hf.smooth, locally_iff_of_localizationSpanTarget, locally_isStandardSmooth, locally_of_locally, ofLocalizationSpanTarget, propertyIsLocal, respectsIso, smooth
-/
theorem smooth_iff_locally_isStandardSmooth : Smooth f ↔ Locally IsStandardSmooth f := by
  refine ⟨fun hf => hf.locally_isStandardSmooth, fun hf => ?_⟩
  rw [← locally_iff_of_localizationSpanTarget Smooth.propertyIsLocal.respectsIso
    Smooth.ofLocalizationSpanTarget]
  exact locally_of_locally (fun hf => hf.smooth) hf

/--
lemma `etale_iff_isStandardSmoothOfRelativeDimension_zero` / 引理 `etale_iff_isStandardSmoothOfRelativeDimension_zero`

English:
lemma etale_iff_isStandardSmoothOfRelativeDimension_zero
  proof: by
  algebraize [f]
  exact Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero

中文:
引理 etale_iff_isStandardSmoothOfRelativeDimension_zero
  证明: by
  algebraize [f]
  exact Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero

Depends on / 依赖: Algebra, Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero, algebraize, iff_isStandardSmoothOfRelativeDimension_zero
-/
lemma etale_iff_isStandardSmoothOfRelativeDimension_zero :
    Etale f ↔ IsStandardSmoothOfRelativeDimension 0 f := by
  algebraize [f]
  exact Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero

end RingHom
