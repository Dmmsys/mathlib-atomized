/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Extension.Cotangent.BaseChange

/-!
# Etale descends along faithfully flat ring maps

In this file we show that smooth, unramified and étale algebras descend along faithfully flat
base change.

## Main results

- `Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`: Smooth descends.
- `Algebra.Unramified.of_smooth_tensorProduct_of_faithfullyFlat`: Unramified descends.
- `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat`: Etale descends.

We also provide the corresponding `RingHom.CodescendsAlong` lemmas.

## TODOs

- The lemma `Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat` has an
  additional `Algebra.FinitePresentation` assumption, because the proof uses that a flat module
  of finite presentation is projective and the former descends. This also holds without
  the finite presentation assumption, but requires showing that projectivity descends
  along faithfully flat base change, which is due to Raynaud and Gruson
  (see https://stacks.math.columbia.edu/tag/058B).
-/

public section

open TensorProduct

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]

/--
lemma `FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat` / 引理 `FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat`

English:
lemma FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat
  proof: by
  constructor
  let _ : Algebra S (T otimes[R] S) := TensorProduct.rightAlgebra
  have : Subsingleton (T otimes[R] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R T S (T otimes[R] S)).subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality R T _

中文:
引理 FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat
  证明: by
  constructor
  let _ : Algebra S (T otimes[R] S) := TensorProduct.rightAlgebra
  have : Subsingleton (T otimes[R] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R T S (T otimes[R] S)).subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality R T _

Depends on / 依赖: Algebra, FaithfullyFlat, KaehlerDifferential, KaehlerDifferential.tensorKaehlerEquivBase, Module, Module.FaithfullyFlat.lTensor_reflects_triviality, Subsingleton, TensorProduct, TensorProduct.rightAlgebra, lTensor_reflects_triviality, otimes, rightAlgebra, subsingleton, tensorKaehlerEquivBase
-/
lemma FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat
    [FormallyUnramified T (T otimes[R] S)] :
    FormallyUnramified R S := by
  constructor
  let _ : Algebra S (T otimes[R] S) := TensorProduct.rightAlgebra
  have : Subsingleton (T otimes[R] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R T S (T otimes[R] S)).subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality R T _

/-- Formally smooth algebras descend along faithfully flat base change. See the TODO
in the module docstring. -/
proof_wanted FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [FormallySmooth T (T otimes[R] S)] :
    FormallySmooth R S

/--
lemma `Smooth.of_smooth_tensorProduct_of_faithfullyFlat` / 引理 `Smooth.of_smooth_tensorProduct_of_faithfullyFlat`

English:
lemma Smooth.of_smooth_tensorProduct_of_faithfullyFlat
  given: [Smooth T (T otimes[R] S)]
  proof: by
  have : Algebra.FinitePresentation R S := .of_finitePresentation_tensorProduct_of_faithfullyFlat T
  refine ⟨?_, .of_finitePresentation_tensorProduct_of_faithfullyFlat T⟩
  rw [formallySmooth_iff]
  constructor
  · let _ : Algebra T (S otimes[R] T) := TensorProduct.rightAlgebra
    let e : S oti

中文:
引理 Smooth.of_smooth_tensorProduct_of_faithfullyFlat
  条件: [Smooth T (T otimes[R] S)]
  证明: by
  have : Algebra.FinitePresentation R S := .of_finitePresentation_tensorProduct_of_faithfullyFlat T
  refine ⟨?_, .of_finitePresentation_tensorProduct_of_faithfullyFlat T⟩
  rw [formallySmooth_iff]
  constructor
  · let _ : Algebra T (S otimes[R] T) := TensorProduct.rightAlgebra
    let e : S oti

Depends on / 依赖: Algebra, Algebra.FinitePresentation, FinitePresentation, FormallySmooth, RingHom, RingHom.algebraMap_toAlgebra, TensorProduct, TensorProduct.comm, TensorProduct.rightAlgebra, algebraMap_toAlgebra, e.symm, formallySmooth_iff, ofRingEquiv, of_equiv, of_finitePresentation_tensorProduct_of_faithfullyFlat, otimes, rightAlgebra
-/
lemma Smooth.of_smooth_tensorProduct_of_faithfullyFlat [Smooth T (T otimes[R] S)] :
    Smooth R S := by
  have : Algebra.FinitePresentation R S := .of_finitePresentation_tensorProduct_of_faithfullyFlat T
  refine ⟨?_, .of_finitePresentation_tensorProduct_of_faithfullyFlat T⟩
  rw [formallySmooth_iff]
  constructor
  · let _ : Algebra T (S otimes[R] T) := TensorProduct.rightAlgebra
    let e : S otimes[R] T ≃ₐ[T] T otimes[R] S :=
.ofRingEquiv (f := TensorProduct.comm R S T) by simp [RingHom.algebraMap_toAlgebra]
    have : FormallySmooth T (S otimes[R] T) := .of_equiv e.symm
    let e' : (S otimes[R] T) otimes[S] Ω[S⁄R] ≃ₗ[S otimes[R] T] Ω[S otimes[R] T⁄T] :=
      KaehlerDifferential.tensorKaehlerEquiv R T S (S otimes[R] T)
    have : Module.Flat (S otimes[R] T) ((S otimes[R] T) otimes[S] Ω[S⁄R]) := .of_linearEquiv e'
    have : Module.Flat S Ω[S⁄R] := Module.Flat.of_flat_tensorProduct _ _ (S otimes[R] T)
    exact Module.Flat.projective_of_finitePresentation
  · have : Subsingleton (T otimes[R] H1Cotangent R S) := (tensorH1CotangentOfFlat R S T).subsingleton
    exact Module.FaithfullyFlat.lTensor_reflects_triviality R T (H1Cotangent R S)

/--
lemma `Unramified.of_unramified_tensorProduct_of_faithfullyFlat` / 引理 `Unramified.of_unramified_tensorProduct_of_faithfullyFlat`

English:
lemma Unramified.of_unramified_tensorProduct_of_faithfullyFlat
  given: [Unramified T (T otimes[R] S)]
  proof: ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_finiteType_tensorProduct_of_faithfullyFlat T⟩

中文:
引理 Unramified.of_unramified_tensorProduct_of_faithfullyFlat
  条件: [Unramified T (T otimes[R] S)]
  证明: ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_finiteType_tensorProduct_of_faithfullyFlat T⟩

Depends on / 依赖: of_finiteType_tensorProduct_of_faithfullyFlat, of_formallyUnramified_tensorProduct_of_faithfullyFlat
-/
lemma Unramified.of_unramified_tensorProduct_of_faithfullyFlat [Unramified T (T otimes[R] S)] :
    Unramified R S :=
  ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_finiteType_tensorProduct_of_faithfullyFlat T⟩

/--
lemma `Etale.of_etale_tensorProduct_of_faithfullyFlat` / 引理 `Etale.of_etale_tensorProduct_of_faithfullyFlat`

English:
lemma Etale.of_etale_tensorProduct_of_faithfullyFlat
  given: [Etale T (T otimes[R] S)]
  proof: by
  rw [Etale.iff_formallyUnramified_and_smooth]
  exact ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_smooth_tensorProduct_of_faithfullyFlat T⟩

中文:
引理 Etale.of_etale_tensorProduct_of_faithfullyFlat
  条件: [Etale T (T otimes[R] S)]
  证明: by
  rw [Etale.iff_formallyUnramified_and_smooth]
  exact ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_smooth_tensorProduct_of_faithfullyFlat T⟩

Depends on / 依赖: Etale.iff_formallyUnramified_and_smooth, iff_formallyUnramified_and_smooth, of_formallyUnramified_tensorProduct_of_faithfullyFlat, of_smooth_tensorProduct_of_faithfullyFlat
-/
lemma Etale.of_etale_tensorProduct_of_faithfullyFlat [Etale T (T otimes[R] S)] :
    Etale R S := by
  rw [Etale.iff_formallyUnramified_and_smooth]
  exact ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_smooth_tensorProduct_of_faithfullyFlat T⟩

end Algebra

namespace RingHom

/--
lemma `Smooth.codescendsAlong_faithfullyFlat` / 引理 `Smooth.codescendsAlong_faithfullyFlat`

English:
lemma Smooth.codescendsAlong_faithfullyFlat
  statement: CodescendsAlong Smooth FaithfullyFlat
  proof: by
  refine .mk _ Smooth.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [smooth_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_smooth_tensorProduct_of_faithfullyFlat S

中文:
引理 Smooth.codescendsAlong_faithfullyFlat
  结论: CodescendsAlong Smooth FaithfullyFlat
  证明: by
  refine .mk _ Smooth.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [smooth_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_smooth_tensorProduct_of_faithfullyFlat S

Depends on / 依赖: Smooth, Smooth.respectsIso, faithfullyFlat_algebraMap_iff, of_smooth_tensorProduct_of_faithfullyFlat, respectsIso, smooth_algebraMap
-/
lemma Smooth.codescendsAlong_faithfullyFlat : CodescendsAlong Smooth FaithfullyFlat := by
  refine .mk _ Smooth.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [smooth_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_smooth_tensorProduct_of_faithfullyFlat S

/--
lemma `FormallyUnramified.codescendsAlong_faithfullyFlat` / 引理 `FormallyUnramified.codescendsAlong_faithfullyFlat`

English:
lemma FormallyUnramified.codescendsAlong_faithfullyFlat
  proof: by
  refine .mk _ FormallyUnramified.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [formallyUnramified_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_formallyUnramified_tensorProduct_of_faithfullyFlat S

中文:
引理 FormallyUnramified.codescendsAlong_faithfullyFlat
  证明: by
  refine .mk _ FormallyUnramified.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [formallyUnramified_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_formallyUnramified_tensorProduct_of_faithfullyFlat S

Depends on / 依赖: FormallyUnramified, FormallyUnramified.respectsIso, faithfullyFlat_algebraMap_iff, formallyUnramified_algebraMap, of_formallyUnramified_tensorProduct_of_faithfullyFlat, respectsIso
-/
lemma FormallyUnramified.codescendsAlong_faithfullyFlat :
    CodescendsAlong FormallyUnramified FaithfullyFlat := by
  refine .mk _ FormallyUnramified.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [formallyUnramified_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_formallyUnramified_tensorProduct_of_faithfullyFlat S

/--
lemma `Etale.codescendsAlong_faithfullyFlat` / 引理 `Etale.codescendsAlong_faithfullyFlat`

English:
lemma Etale.codescendsAlong_faithfullyFlat
  statement: CodescendsAlong Etale FaithfullyFlat
  proof: by
  refine .mk _ Etale.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [etale_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_etale_tensorProduct_of_faithfullyFlat S

中文:
引理 Etale.codescendsAlong_faithfullyFlat
  结论: CodescendsAlong Etale FaithfullyFlat
  证明: by
  refine .mk _ Etale.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [etale_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_etale_tensorProduct_of_faithfullyFlat S

Depends on / 依赖: Etale.respectsIso, etale_algebraMap, faithfullyFlat_algebraMap_iff, of_etale_tensorProduct_of_faithfullyFlat, respectsIso
-/
lemma Etale.codescendsAlong_faithfullyFlat : CodescendsAlong Etale FaithfullyFlat := by
  refine .mk _ Etale.respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [etale_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_etale_tensorProduct_of_faithfullyFlat S

end RingHom
