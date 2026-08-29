/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Semisimple

/-!
# Eigenspaces of semisimple linear endomorphisms

This file contains basic results relevant to the study of eigenspaces of semisimple linear
endomorphisms.

## Main definitions / results

* `Module.End.IsFinitelySemisimple.genEigenspace_eq_eigenspace`: for a semisimple endomorphism,
  a generalized eigenspace is an eigenspace.
* `Module.End.IsSemisimple.iSup_maxGenEigenspace_eq_top_iff`: a semisimple endomorphism is
  triangularizable if and only if it is diagonalizable.
* `Module.End.IsSemisimple.iSup_eigenspace_eq_top`: over an algebraically closed field,
  the eigenspaces of a semisimple endomorphism span the whole space.
* `Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue`: a semisimple endomorphism over
  an algebraically closed field is zero iff all eigenvalues are zero.

-/

public section

open Function Set

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {f g : End R M}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil` / 引理 `apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil`

English:
lemma apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
  proof: by
  rw [f.mem_genEigenspace] at hm
  obtain ⟨l, -, hm⟩ := hm
  rw [← f.mem_genEigenspace_nat] at hm
  set p := f.genEigenspace μ l
  have h₁ : MapsTo g p p := mapsTo_genEigenspace_of_comm hfg μ l
  have h₂ : MapsTo (g - algebraMap R (End R M) μ) p p :=
    mapsTo_genEigenspace_of_comm (hfg.sub_righ

中文:
引理 apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
  证明: by
  rw [f.mem_genEigenspace] at hm
  obtain ⟨l, -, hm⟩ := hm
  rw [← f.mem_genEigenspace_nat] at hm
  set p := f.genEigenspace μ l
  have h₁ : MapsTo g p p := mapsTo_genEigenspace_of_comm hfg μ l
  have h₂ : MapsTo (g - algebraMap R (End R M) μ) p p :=
    mapsTo_genEigenspace_of_comm (hfg.sub_righ

Depends on / 依赖: Algebra, Algebra.commute_algebraMap_right, Commute, Commute.sub_right, MapsTo, algebraMap, commute_algebraMap_right, f.genEigenspace, f.mem_genEigenspace, f.mem_genEigenspace_nat, genEigenspace, hfg.sub_right, mapsTo_genEigenspace_, mapsTo_genEigenspace_of_comm, mem_genEigenspace, mem_genEigenspace_nat, sub_right
-/
lemma apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
    {μ : R} {k : Nat∞} {m : M} (hm : m in f.genEigenspace μ k)
    (hfg : Commute f g) (hss : g.IsFinitelySemisimple) (hnil : IsNilpotent (f - g)) :
    g m = μ • m := by
  rw [f.mem_genEigenspace] at hm
  obtain ⟨l, -, hm⟩ := hm
  rw [← f.mem_genEigenspace_nat] at hm
  set p := f.genEigenspace μ l
  have h₁ : MapsTo g p p := mapsTo_genEigenspace_of_comm hfg μ l
  have h₂ : MapsTo (g - algebraMap R (End R M) μ) p p :=
    mapsTo_genEigenspace_of_comm (hfg.sub_right <| Algebra.commute_algebraMap_right μ f) μ l
  have h₃ : MapsTo (f - g) p p :=
    mapsTo_genEigenspace_of_comm (Commute.sub_right rfl hfg) μ l
  have h₄ : MapsTo (f - algebraMap R (End R M) μ) p p :=
    mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ l
  replace hfg : Commute (f - algebraMap R (End R M) μ) (f - g) :=
(Commute.sub_right rfl hfg).sub_left Algebra.commute_algebraMap_left μ (f - g)
  suffices IsNilpotent ((g - algebraMap R (End R M) μ).restrict h₂) by
    replace this : g.restrict h₁ - algebraMap R (End R p) μ = 0 :=
      eq_zero_of_isNilpotent_of_isFinitelySemisimple this (by simpa using hss.restrict _)
    simpa [LinearMap.restrict_apply, sub_eq_zero] using LinearMap.congr_fun this ⟨m, hm⟩
  simpa [LinearMap.restrict_sub h₄ h₃] using (LinearMap.restrict_commute hfg h₄ h₃).isNilpotent_sub
    (f.isNilpotent_restrict_sub_algebraMap μ l) (Module.End.isNilpotent.restrict h₃ hnil)

/--
lemma `IsFinitelySemisimple.genEigenspace_eq_eigenspace` / 引理 `IsFinitelySemisimple.genEigenspace_eq_eigenspace`

English:
lemma IsFinitelySemisimple.genEigenspace_eq_eigenspace
  proof: by
  refine le_antisymm (fun m hm => mem_eigenspace_iff.mpr ?_) (f.genEigenspace μ |>.mono ?_)
  · apply apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hm rfl hf
    simp
  · exact Order.one_le_iff_pos.mpr hk

中文:
引理 IsFinitelySemisimple.genEigenspace_eq_eigenspace
  证明: by
  refine le_antisymm (fun m hm => mem_eigenspace_iff.mpr ?_) (f.genEigenspace μ |>.mono ?_)
  · apply apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hm rfl hf
    simp
  · exact Order.one_le_iff_pos.mpr hk

Depends on / 依赖: Order.one_le_iff_pos.mpr, apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil, f.genEigenspace, genEigenspace, le_antisymm, mem_eigenspace_iff, mem_eigenspace_iff.mpr, one_le_iff_pos
-/
lemma IsFinitelySemisimple.genEigenspace_eq_eigenspace
    (hf : f.IsFinitelySemisimple) (μ : R) {k : Nat∞} (hk : 0 < k) :
    f.genEigenspace μ k = f.eigenspace μ := by
  refine le_antisymm (fun m hm => mem_eigenspace_iff.mpr ?_) (f.genEigenspace μ |>.mono ?_)
  · apply apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hm rfl hf
    simp
  · exact Order.one_le_iff_pos.mpr hk

/--
lemma `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace` / 引理 `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`

English:
lemma IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
  proof: hf.genEigenspace_eq_eigenspace μ ENat.top_pos

中文:
引理 IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
  证明: hf.genEigenspace_eq_eigenspace μ ENat.top_pos

Depends on / 依赖: ENat.top_pos, genEigenspace_eq_eigenspace, hf.genEigenspace_eq_eigenspace, top_pos
-/
lemma IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
    (hf : f.IsFinitelySemisimple) (μ : R) :
    f.maxGenEigenspace μ = f.eigenspace μ :=
  hf.genEigenspace_eq_eigenspace μ ENat.top_pos

/--
lemma `IsFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff` / 引理 `IsFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff`

English:
lemma IsFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff
  given: (hf : f.IsFinitelySemisimple)
  proof: by
  simp [hf.maxGenEigenspace_eq_eigenspace]

中文:
引理 IsFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff
  条件: (hf : f.IsFinitelySemisimple)
  证明: by
  simp [hf.maxGenEigenspace_eq_eigenspace]

Depends on / 依赖: hf.maxGenEigenspace_eq_eigenspace, maxGenEigenspace_eq_eigenspace
-/
lemma IsFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff (hf : f.IsFinitelySemisimple) :
    (⨆ μ : R, f.maxGenEigenspace μ) = ⊤ ↔ (⨆ μ : R, f.eigenspace μ) = ⊤ := by
  simp [hf.maxGenEigenspace_eq_eigenspace]

/--
lemma `IsSemisimple.iSup_maxGenEigenspace_eq_top_iff` / 引理 `IsSemisimple.iSup_maxGenEigenspace_eq_top_iff`

English:
lemma IsSemisimple.iSup_maxGenEigenspace_eq_top_iff
  given: (hf : f.IsSemisimple)
  proof: hf.isFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff

中文:
引理 IsSemisimple.iSup_maxGenEigenspace_eq_top_iff
  条件: (hf : f.IsSemisimple)
  证明: hf.isFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff

Depends on / 依赖: hf.isFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff, iSup_maxGenEigenspace_eq_top_iff, isFinitelySemisimple
-/
lemma IsSemisimple.iSup_maxGenEigenspace_eq_top_iff (hf : f.IsSemisimple) :
    (⨆ μ : R, f.maxGenEigenspace μ) = ⊤ ↔ (⨆ μ : R, f.eigenspace μ) = ⊤ :=
  hf.isFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff

section AlgClosed

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {f : End K V}

/--
lemma `IsSemisimple.iSup_eigenspace_eq_top` / 引理 `IsSemisimple.iSup_eigenspace_eq_top`

English:
lemma IsSemisimple.iSup_eigenspace_eq_top
  given: (hf : f.IsSemisimple)
  proof: by
  simpa only [(isFinitelySemisimple_iff_isSemisimple.mpr hf).maxGenEigenspace_eq_eigenspace] using
    iSup_maxGenEigenspace_eq_top f

中文:
引理 IsSemisimple.iSup_eigenspace_eq_top
  条件: (hf : f.IsSemisimple)
  证明: by
  simpa only [(isFinitelySemisimple_iff_isSemisimple.mpr hf).maxGenEigenspace_eq_eigenspace] using
    iSup_maxGenEigenspace_eq_top f

Depends on / 依赖: iSup_maxGenEigenspace_eq_top, isFinitelySemisimple_iff_isSemisimple, isFinitelySemisimple_iff_isSemisimple.mpr, maxGenEigenspace_eq_eigenspace
-/
lemma IsSemisimple.iSup_eigenspace_eq_top (hf : f.IsSemisimple) :
    ⨆ μ : K, f.eigenspace μ = ⊤ := by
  simpa only [(isFinitelySemisimple_iff_isSemisimple.mpr hf).maxGenEigenspace_eq_eigenspace] using
    iSup_maxGenEigenspace_eq_top f

/--
lemma `IsSemisimple.eq_zero_iff_forall_eigenvalue` / 引理 `IsSemisimple.eq_zero_iff_forall_eigenvalue`

English:
lemma IsSemisimple.eq_zero_iff_forall_eigenvalue
  given: (hf : f.IsSemisimple)
  proof: by
  constructor
  · rintro rfl μ hμ
    by_contra hμ0
    obtain ⟨x, hx, hx_ne⟩ := (Submodule.ne_bot_iff _).mp hμ
    rw [mem_eigenspace_iff] at hx
    exact hx_ne ((smul_eq_zero.mp hx.symm).resolve_left hμ0)
  · intro h
    suffices f.eigenspace 0 = ⊤ by rwa [eigenspace_zero, LinearMap.ker_eq_top]

中文:
引理 IsSemisimple.eq_zero_iff_forall_eigenvalue
  条件: (hf : f.IsSemisimple)
  证明: by
  constructor
  · rintro rfl μ hμ
    by_contra hμ0
    obtain ⟨x, hx, hx_ne⟩ := (Submodule.ne_bot_iff _).mp hμ
    rw [mem_eigenspace_iff] at hx
    exact hx_ne ((smul_eq_zero.mp hx.symm).resolve_left hμ0)
  · intro h
    suffices f.eigenspace 0 = ⊤ by rwa [eigenspace_zero, LinearMap.ker_eq_top]

Depends on / 依赖: LinearMap, LinearMap.ker_eq_top, Submodule, Submodule.ne_bot_iff, eigenspace, eigenspace_zero, eq_or_ne, f.eigenspace, hasEigenvalue_iff, hasEigenvalue_iff.not.mp, hf.iSup_eigenspace_eq_top, hx.symm, hx_ne, iSup_eigenspace_eq_top, iSup_le, ker_eq_top, le_antisymm, le_iSup, le_refl, mem_eigenspace_iff
-/
lemma IsSemisimple.eq_zero_iff_forall_eigenvalue (hf : f.IsSemisimple) :
    f = 0 ↔ forall μ : K, f.HasEigenvalue μ -> μ = 0 := by
  constructor
  · rintro rfl μ hμ
    by_contra hμ0
    obtain ⟨x, hx, hx_ne⟩ := (Submodule.ne_bot_iff _).mp hμ
    rw [mem_eigenspace_iff] at hx
    exact hx_ne ((smul_eq_zero.mp hx.symm).resolve_left hμ0)
  · intro h
    suffices f.eigenspace 0 = ⊤ by rwa [eigenspace_zero, LinearMap.ker_eq_top] at this
    rw [← hf.iSup_eigenspace_eq_top]
    refine le_antisymm (le_iSup _ 0) (iSup_le fun μ => ?_)
    rcases eq_or_ne μ 0 with rfl | hμ
    · exact le_refl _
    · have : f.eigenspace μ = ⊥ := not_not.mp (hasEigenvalue_iff.not.mp fun he => hμ (h μ he))
      simp [this]

end AlgClosed

end Module.End
