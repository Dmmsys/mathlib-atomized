/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Analysis.Complex.Basic

/-!
# Some lemmas on the spectrum and quasispectrum of elements and positivity on `ℂ`
-/

public section

namespace SpectrumRestricts
variable {A : Type*} [Ring A]

/--
lemma `real_iff` / 引理 `real_iff`

English:
lemma real_iff
  given: [Algebra Complex A] {a : A}
  proof: by
  simp [spectrumRestricts_iff, Set.LeftInvOn, Function.LeftInverse, eq_comm]

中文:
引理 real_iff
  条件: [代数 复形 A] {a : A}
  证明: by
  simp [spectrumRestricts_iff, Set.LeftInvOn, Function.LeftInverse, eq_comm]

Depends on / 依赖: Function, Function.LeftInverse, LeftInvOn, LeftInverse, Set.LeftInvOn, eq_comm, spectrumRestricts_iff
-/
lemma real_iff [Algebra Complex A] {a : A} :
    SpectrumRestricts a Complex.reCLM ↔ forall x in spectrum Complex a, x = x.re := by
  simp [spectrumRestricts_iff, Set.LeftInvOn, Function.LeftInverse, eq_comm]

end SpectrumRestricts

namespace QuasispectrumRestricts
local notation "σₙ" => quasispectrum
variable {A : Type*} [NonUnitalRing A]

/--
lemma `real_iff` / 引理 `real_iff`

English:
lemma real_iff
  given: [Module Complex A] [IsScalarTower Complex A A] [SMulCommClass Complex A A] {a : A}
  proof: by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr]; rw [Unitization.quasispectrum_eq_spectrum_inr' _ Complex]; rw [SpectrumRestricts.real_iff]

中文:
引理 real_iff
  条件: [模 复形 A] [标量塔 复形 A A] [标量交换类 复形 A A] {a : A}
  证明: by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr]; rw [Unitization.quasispectrum_eq_spectrum_inr' _ Complex]; rw [SpectrumRestricts.real_iff]

Depends on / 依赖: SpectrumRestricts, SpectrumRestricts.real_iff, Unitization, Unitization.quasispectrum_eq_spectrum_inr, quasispectrumRestricts_iff_spectrumRestricts_inr, quasispectrum_eq_spectrum_inr, real_iff
-/
lemma real_iff [Module Complex A] [IsScalarTower Complex A A] [SMulCommClass Complex A A] {a : A} :
    QuasispectrumRestricts a Complex.reCLM ↔ forall x in σₙ Complex a, x = x.re := by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr]; rw [Unitization.quasispectrum_eq_spectrum_inr' _ Complex]; rw [SpectrumRestricts.real_iff]

end QuasispectrumRestricts
