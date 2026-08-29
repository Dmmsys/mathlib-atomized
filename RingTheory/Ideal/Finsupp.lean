/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.RingTheory.Ideal.Operations

/-!

# Lemmas for action of ideals on submodules of `Finsupp`

-/

public section

variable (R : Type*) [CommRing R]

/--
lemma `Finsupp.submodule_smul` / 引理 `Finsupp.submodule_smul`

English:
lemma Finsupp.submodule_smul
  statement: {M : Type*} [AddCommGroup M] [Module R M]
  proof: by
  simp only [Finsupp.submodule_eq_iSup, Submodule.map_smul'', ← Submodule.smul_iSup]

中文:
引理 有限支撑.submodule_smul
  结论: {M : 类型} [加法交换群 M] [模 R M]
  证明: by
  simp only [Finsupp.submodule_eq_iSup, Submodule.map_smul'', ← Submodule.smul_iSup]

Depends on / 依赖: Finsupp, Finsupp.submodule_eq_iSup, Submodule, Submodule.map_smul, Submodule.smul_iSup, map_smul, smul_iSup, submodule_eq_iSup
-/
lemma Finsupp.submodule_smul {M : Type*} [AddCommGroup M] [Module R M]
    (ι : Type*) (p : ι -> Submodule R M) (I : Ideal R) :
    Finsupp.submodule (fun i => I • p i) = I • Finsupp.submodule p := by
  simp only [Finsupp.submodule_eq_iSup, Submodule.map_smul'', ← Submodule.smul_iSup]
