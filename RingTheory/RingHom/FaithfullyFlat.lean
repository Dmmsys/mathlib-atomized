/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.RingTheory.RingHom.Flat

/-!
# Faithfully flat ring maps

A ring map `f : R →+* S` is faithfully flat if `S` is faithfully flat as an `R`-algebra. This is
the same as being flat and a surjection on prime spectra.
-/

@[expose] public section

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S] {f : R ->+* S}

/-- A ring map `f : R →+* S` is faithfully flat if `S` is faithfully flat as an `R`-algebra. -/
@[stacks 00HB "Part (4)", algebraize Module.FaithfullyFlat]
/--
Definition of `FaithfullyFlat` / `FaithfullyFlat` 的定义

English:
definition FaithfullyFlat
  signature: {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S)
  body: letI : Algebra R S := f.toAlgebra
  Module.FaithfullyFlat R S

中文:
定义 FaithfullyFlat
  签名: {R S : 类型} [CommRing R] [CommRing S] (f : R ->+* S)
  定义体: letI : Algebra R S := f.toAlgebra
  Module.FaithfullyFlat R S

Depends on / 依赖: Algebra, FaithfullyFlat, Module, Module.FaithfullyFlat, f.toAlgebra, toAlgebra
-/
def FaithfullyFlat {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.FaithfullyFlat R S

/--
lemma `faithfullyFlat_algebraMap_iff` / 引理 `faithfullyFlat_algebraMap_iff`

English:
lemma faithfullyFlat_algebraMap_iff
  given: [Algebra R S]
  proof: by
  simp only [FaithfullyFlat]
  congr!
  exact Algebra.algebra_ext _ _ fun _ => rfl

中文:
引理 faithfullyFlat_algebraMap_iff
  条件: [Algebra R S]
  证明: by
  simp only [FaithfullyFlat]
  congr!
  exact Algebra.algebra_ext _ _ fun _ => rfl

Depends on / 依赖: Algebra, Algebra.algebra_ext, FaithfullyFlat, algebra_ext
-/
lemma faithfullyFlat_algebraMap_iff [Algebra R S] :
    (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S := by
  simp only [FaithfullyFlat]
  congr!
  exact Algebra.algebra_ext _ _ fun _ => rfl

namespace FaithfullyFlat

/--
lemma `flat` / 引理 `flat`

English:
lemma flat
  given: (hf : f.FaithfullyFlat)
  statement: f.Flat
  proof: by
  algebraize [f]
exact inferInstanceAs Module.Flat R S

中文:
引理 flat
  条件: (hf : f.FaithfullyFlat)
  结论: f.Flat
  证明: by
  algebraize [f]
exact inferInstanceAs Module.Flat R S

Depends on / 依赖: Module, Module.Flat, algebraize
-/
lemma flat (hf : f.FaithfullyFlat) : f.Flat := by
  algebraize [f]
exact inferInstanceAs Module.Flat R S

/--
lemma `iff_flat_and_comap_surjective` / 引理 `iff_flat_and_comap_surjective`

English:
lemma iff_flat_and_comap_surjective
  proof: by
  algebraize [f]
  rw [← algebraMap_toAlgebra f]; rw [faithfullyFlat_algebraMap_iff]; rw [flat_algebraMap_iff]
  exact ⟨fun h => ⟨inferInstance, PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩,
    fun ⟨h, hf⟩ => .of_comap_surjective hf⟩

中文:
引理 iff_flat_and_comap_surjective
  证明: by
  algebraize [f]
  rw [← algebraMap_toAlgebra f]; rw [faithfullyFlat_algebraMap_iff]; rw [flat_algebraMap_iff]
  exact ⟨fun h => ⟨inferInstance, PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩,
    fun ⟨h, hf⟩ => .of_comap_surjective hf⟩

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.comap_surjective_of_faithfullyFlat, algebraMap_toAlgebra, algebraize, comap_surjective_of_faithfullyFlat, faithfullyFlat_algebraMap_iff, flat_algebraMap_iff, of_comap_surjective
-/
lemma iff_flat_and_comap_surjective :
    f.FaithfullyFlat ↔ f.Flat ∧ Function.Surjective (PrimeSpectrum.comap f) := by
  algebraize [f]
  rw [← algebraMap_toAlgebra f]; rw [faithfullyFlat_algebraMap_iff]; rw [flat_algebraMap_iff]
  exact ⟨fun h => ⟨inferInstance, PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩,
    fun ⟨h, hf⟩ => .of_comap_surjective hf⟩

/--
lemma `eq_and` / 引理 `eq_and`

English:
lemma eq_and
  statement: FaithfullyFlat =
  proof: by
  ext
  rw [iff_flat_and_comap_surjective]

中文:
引理 eq_and
  结论: FaithfullyFlat =
  证明: by
  ext
  rw [iff_flat_and_comap_surjective]

Depends on / 依赖: iff_flat_and_comap_surjective
-/
lemma eq_and : FaithfullyFlat =
      fun (f : R ->+* S) => f.Flat ∧ Function.Surjective (PrimeSpectrum.comap f) := by
  ext
  rw [iff_flat_and_comap_surjective]

/--
lemma `stableUnderComposition` / 引理 `stableUnderComposition`

English:
lemma stableUnderComposition
  statement: StableUnderComposition FaithfullyFlat
  proof: by
  introv R hf hg
  algebraize [f, g, g.comp f]
  rw [← algebraMap_toAlgebra (g.comp f)]; rw [faithfullyFlat_algebraMap_iff]
  exact .trans R S T

中文:
引理 stableUnderComposition
  结论: StableUnderComposition FaithfullyFlat
  证明: by
  introv R hf hg
  algebraize [f, g, g.comp f]
  rw [← algebraMap_toAlgebra (g.comp f)]; rw [faithfullyFlat_algebraMap_iff]
  exact .trans R S T

Depends on / 依赖: algebraMap_toAlgebra, algebraize, faithfullyFlat_algebraMap_iff, g.comp, introv
-/
lemma stableUnderComposition : StableUnderComposition FaithfullyFlat := by
  introv R hf hg
  algebraize [f, g, g.comp f]
  rw [← algebraMap_toAlgebra (g.comp f)]; rw [faithfullyFlat_algebraMap_iff]
  exact .trans R S T

/--
lemma `of_bijective` / 引理 `of_bijective`

English:
lemma of_bijective
  given: (hf : Function.Bijective f)
  statement: f.FaithfullyFlat
  proof: by
  rw [iff_flat_and_comap_surjective]
  refine ⟨.of_bijective hf, fun p => ?_⟩
  use p.comap ((RingEquiv.ofBijective f hf).symm : _ ->+* _)
  have : ((RingEquiv.ofBijective f hf).symm : _ ->+* _).comp f = id R := by
    ext
    exact (RingEquiv.ofBijective f hf).injective (by simp)
  rw [← PrimeSp

中文:
引理 of_bijective
  条件: (hf : Function.Bijective f)
  结论: f.FaithfullyFlat
  证明: by
  rw [iff_flat_and_comap_surjective]
  refine ⟨.of_bijective hf, fun p => ?_⟩
  use p.comap ((RingEquiv.ofBijective f hf).symm : _ ->+* _)
  have : ((RingEquiv.ofBijective f hf).symm : _ ->+* _).comp f = id R := by
    ext
    exact (RingEquiv.ofBijective f hf).injective (by simp)
  rw [← PrimeSp

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.comap_comp_apply, PrimeSpectrum.comap_id, RingEquiv, RingEquiv.ofBijective, comap_comp_apply, comap_id, iff_flat_and_comap_surjective, injective, ofBijective, of_bijective, p.comap
-/
lemma of_bijective (hf : Function.Bijective f) : f.FaithfullyFlat := by
  rw [iff_flat_and_comap_surjective]
  refine ⟨.of_bijective hf, fun p => ?_⟩
  use p.comap ((RingEquiv.ofBijective f hf).symm : _ ->+* _)
  have : ((RingEquiv.ofBijective f hf).symm : _ ->+* _).comp f = id R := by
    ext
    exact (RingEquiv.ofBijective f hf).injective (by simp)
  rw [← PrimeSpectrum.comap_comp_apply]; rw [this]; rw [PrimeSpectrum.comap_id]

/--
lemma `injective` / 引理 `injective`

English:
lemma injective
  given: (hf : f.FaithfullyFlat)
  statement: Function.Injective ⇑f
  proof: by
  algebraize [f]
  exact FaithfulSMul.algebraMap_injective R S

中文:
引理 injective
  条件: (hf : f.FaithfullyFlat)
  结论: Function.Injective ⇑f
  证明: by
  algebraize [f]
  exact FaithfulSMul.algebraMap_injective R S

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, algebraize
-/
lemma injective (hf : f.FaithfullyFlat) : Function.Injective ⇑f := by
  algebraize [f]
  exact FaithfulSMul.algebraMap_injective R S

/--
lemma `respectsIso` / 引理 `respectsIso`

English:
lemma respectsIso
  statement: RespectsIso FaithfullyFlat
  proof: stableUnderComposition.respectsIso (fun e => .of_bijective e.bijective)

中文:
引理 respectsIso
  结论: RespectsIso FaithfullyFlat
  证明: stableUnderComposition.respectsIso (fun e => .of_bijective e.bijective)

Depends on / 依赖: bijective, e.bijective, of_bijective, respectsIso, stableUnderComposition, stableUnderComposition.respectsIso
-/
lemma respectsIso : RespectsIso FaithfullyFlat :=
  stableUnderComposition.respectsIso (fun e => .of_bijective e.bijective)

/--
lemma `isStableUnderBaseChange` / 引理 `isStableUnderBaseChange`

English:
lemma isStableUnderBaseChange
  statement: IsStableUnderBaseChange FaithfullyFlat
  proof: by
  refine .mk respectsIso (fun R S T _ _ _ _ _ _ => show (algebraMap _ _).FaithfullyFlat from ?_)
  rw [faithfullyFlat_algebraMap_iff] at *
  infer_instance

中文:
引理 isStableUnderBaseChange
  结论: IsStableUnderBaseChange FaithfullyFlat
  证明: by
  refine .mk respectsIso (fun R S T _ _ _ _ _ _ => show (algebraMap _ _).FaithfullyFlat from ?_)
  rw [faithfullyFlat_algebraMap_iff] at *
  infer_instance

Depends on / 依赖: FaithfullyFlat, algebraMap, faithfullyFlat_algebraMap_iff, infer_instance, respectsIso
-/
lemma isStableUnderBaseChange : IsStableUnderBaseChange FaithfullyFlat := by
  refine .mk respectsIso (fun R S T _ _ _ _ _ _ => show (algebraMap _ _).FaithfullyFlat from ?_)
  rw [faithfullyFlat_algebraMap_iff] at *
  infer_instance

end RingHom.FaithfullyFlat
