/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Basic Properties of Complete Local Ring

In this file we prove that for local ring `R` with finitely generated maximal ideal,
`AdicCompletion (IsLocalRing.maximalIdeal R) R` is local ring with maximal ideal equal to
`IsLocalRing.maximalIdeal R` mapped by algebra map. Furthermore, it is complete with respect to
its maximal ideal.

As a corollary, for Noetherian local ring `R`, `AdicCompletion (maximalIdeal R) R` is always
a complete Noetherian local ring.

Most results needing finitely generation of maximal ideal have a version for Noetherian ring without
this side condition for convenience.

# Main Results

* `AdicCompletion.isLocalRing_of_fg` : for a local ring `R` with finitely generated maximal ideal,
  its completion with respect to `IsLocalRing.maximalIdeal R` is local ring.

* `AdicCompletion.maximalIdeal_eq_map_of_fg` : for a local ring `R` with finitely generated
  maximal ideal, the maximal ideal of its completion with respect to `IsLocalRing.maximalIdeal R`
  is equal to `IsLocalRing.maximalIdeal R` mapped by algebra map.

* `AdicCompletion.isAdicComplete_of_fg` : for a local ring `R` with finitely generated
  maximal ideal, `AdicCompletion (IsLocalRing.maximalIdeal R) R` itself is complete with respect to
  its maximal ideal.

* `AdicCompletion.spanFinrank_maximalIdeal_eq` : for Noetherian local ring `R`, minimal number of
  generators of maximal ideal of `R` and `AdicCompletion (IsLocalRing.maximalIdeal R) R` are equal.

-/

public section

variable {R : Type*} [CommRing R]

open Ideal Quotient

/--
theorem `isLocalRing_of_isAdicComplete_maximal` / 定理 `isLocalRing_of_isAdicComplete_maximal`

English:
theorem isLocalRing_of_isAdicComplete_maximal
  given: (m : Ideal R) [m.IsMaximal] [IsAdicComplete m R]
  proof: IsLocalRing.of_unique_max_ideal ⟨m, ‹m.IsMaximal›, fun _ hJ =>
    (‹m.IsMaximal›.eq_of_le hJ.ne_top <|
(IsAdicComplete.le_jacobson_bot m).trans sInf_le ⟨bot_le, hJ⟩).symm⟩

中文:
定理 isLocalRing_of_isAdicComplete_maximal
  条件: (m : 理想 R) [m.是极大] [是AdicComplete m R]
  证明: IsLocalRing.of_unique_max_ideal ⟨m, ‹m.IsMaximal›, fun _ hJ =>
    (‹m.IsMaximal›.eq_of_le hJ.ne_top <|
(IsAdicComplete.le_jacobson_bot m).trans sInf_le ⟨bot_le, hJ⟩).symm⟩

Depends on / 依赖: IsAdicComplete, IsAdicComplete.le_jacobson_bot, IsLocalRing, IsLocalRing.of_unique_max_ideal, IsMaximal, bot_le, eq_of_le, hJ.ne_top, le_jacobson_bot, m.IsMaximal, ne_top, of_unique_max_ideal, sInf_le
-/
theorem isLocalRing_of_isAdicComplete_maximal (m : Ideal R) [m.IsMaximal] [IsAdicComplete m R] :
    IsLocalRing R :=
  IsLocalRing.of_unique_max_ideal ⟨m, ‹m.IsMaximal›, fun _ hJ =>
    (‹m.IsMaximal›.eq_of_le hJ.ne_top <|
(IsAdicComplete.le_jacobson_bot m).trans sInf_le ⟨bot_le, hJ⟩).symm⟩

open IsLocalRing

namespace AdicCompletion

variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/--
lemma `isAdicComplete_self` / 引理 `isAdicComplete_self`

English:
lemma isAdicComplete_self
  given: (fg : I.FG)
  proof: (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete fg)

中文:
引理 isAdicComplete_self
  条件: (fg : I.FG)
  证明: (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete fg)

Depends on / 依赖: AdicCompletion, AdicCompletion.isAdicComplete, IsAdicComplete, IsAdicComplete.map_algebraMap_iff, isAdicComplete, map_algebraMap_iff
-/
lemma isAdicComplete_self (fg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
  (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete fg)

/--
lemma `isMaximal_map_of_le` / 引理 `isMaximal_map_of_le`

English:
lemma isMaximal_map_of_le
  given: (m : Ideal R) [m.IsMaximal] (le : I <= m) (fg : I.FG)
  proof: by
  have mapeq : m.map (algebraMap R (AdicCompletion I R)) = (m.map (Ideal.Quotient.mk I)).comap
    (AdicCompletion.evalOneₐ I).toRingHom := by
    rw [← AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]; rw [← Ideal.map_map]; rw [Ideal.comap_map_of_surjective' (evalOneₐ I).toRingHom (evalOneₐ_surjective I)]; rw [eq_comm]; rw [sup_eq_left]; rw [AdicCompletion.ker_evalOneₐ_eq_map I fg]
    exact Ideal.map_mono le
  have : (Ideal.map (Ideal.Quotient.mk I) m).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using le)
  rw [mapeq]
  exact Ideal.comap_isMaximal_of_surjective _ (evalOneₐ_surjective I)

中文:
引理 isMaximal_map_of_le
  条件: (m : 理想 R) [m.是极大] (le : I <= m) (fg : I.FG)
  证明: by
  have mapeq : m.map (algebraMap R (AdicCompletion I R)) = (m.map (Ideal.Quotient.mk I)).comap
    (AdicCompletion.evalOneₐ I).toRingHom := by
    rw [← AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]; rw [← Ideal.map_map]; rw [Ideal.comap_map_of_surjective' (evalOneₐ I).toRingHom (evalOneₐ_surjective I)]; rw [eq_comm]; rw [sup_eq_left]; rw [AdicCompletion.ker_evalOneₐ_eq_map I fg]
    exact Ideal.map_mono le
  have : (Ideal.map (Ideal.Quotient.mk I) m).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using le)
  rw [mapeq]
  exact Ideal.comap_isMaximal_of_surjective _ (evalOneₐ_surjective I)

Depends on / 依赖: AdicCompletion, AdicCompletion.evalOne, AdicCompletion.ker_evalOne, Ideal.IsMaximal.map_of_surjective_of_ker_le, Ideal.Quotient.mk, Ideal.comap_map_of_surjective, Ideal.map, Ideal.map_map, Ideal.map_mono, IsMaximal, Quotient, algebraMap, comap_map_of_surjective, eq_comm, m.map, map_map, map_mono, map_of_surjective_of_ker_le, sup_eq_left, toRingHom
-/
lemma isMaximal_map_of_le (m : Ideal R) [m.IsMaximal] (le : I <= m) (fg : I.FG) :
    (m.map (algebraMap R (AdicCompletion I R))).IsMaximal := by
  have mapeq : m.map (algebraMap R (AdicCompletion I R)) = (m.map (Ideal.Quotient.mk I)).comap
    (AdicCompletion.evalOneₐ I).toRingHom := by
    rw [← AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]; rw [← Ideal.map_map]; rw [Ideal.comap_map_of_surjective' (evalOneₐ I).toRingHom (evalOneₐ_surjective I)]; rw [eq_comm]; rw [sup_eq_left]; rw [AdicCompletion.ker_evalOneₐ_eq_map I fg]
    exact Ideal.map_mono le
  have : (Ideal.map (Ideal.Quotient.mk I) m).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using le)
  rw [mapeq]
  exact Ideal.comap_isMaximal_of_surjective _ (evalOneₐ_surjective I)

/--
lemma `isLocalRing_of_fg` / 引理 `isLocalRing_of_fg`

English:
lemma isLocalRing_of_fg
  given: [IsLocalRing R] (fg : (maximalIdeal R).FG)
  proof: by
  have := AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg
  have := AdicCompletion.isAdicComplete_self _ fg
  exact isLocalRing_of_isAdicComplete_maximal
    ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)))

中文:
引理 isLocalRing_of_fg
  条件: [是局部环 R] (fg : (maximalIdeal R).FG)
  证明: by
  have := AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg
  have := AdicCompletion.isAdicComplete_self _ fg
  exact isLocalRing_of_isAdicComplete_maximal
    ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)))

Depends on / 依赖: AdicCompletion, AdicCompletion.isAdicComplete_self, AdicCompletion.isMaximal_map_of_le, algebraMap, isAdicComplete_self, isLocalRing_of_isAdicComplete_maximal, isMaximal_map_of_le, le_refl, maximalIdeal
-/
lemma isLocalRing_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    IsLocalRing (AdicCompletion (maximalIdeal R) R) := by
  have := AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg
  have := AdicCompletion.isAdicComplete_self _ fg
  exact isLocalRing_of_isAdicComplete_maximal
    ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNoetherianRing
  signature: R] [IsLocalRing R] : IsLocalRing (AdicCompletion (maximalIdeal R) R)
  body: AdicCompletion.isLocalRing_of_fg (fg_of_isNoetherianRing (maximalIdeal R))

中文:
实例 [是Noether环
  签名: R] [是局部环 R] : 是局部环 (AdicCompletion (maximalIdeal R) R)
  定义体: AdicCompletion.isLocalRing_of_fg (fg_of_isNoetherianRing (maximalIdeal R))

Depends on / 依赖: AdicCompletion, AdicCompletion.isLocalRing_of_fg, fg_of_isNoetherianRing, isLocalRing_of_fg, maximalIdeal
-/
instance [IsNoetherianRing R] [IsLocalRing R] : IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
  AdicCompletion.isLocalRing_of_fg (fg_of_isNoetherianRing (maximalIdeal R))

/--
lemma `maximalIdeal_eq_map_of_fg` / 引理 `maximalIdeal_eq_map_of_fg`

English:
lemma maximalIdeal_eq_map_of_fg
  given: [IsLocalRing R] (fg : (maximalIdeal R).FG)
  proof: AdicCompletion.isLocalRing_of_fg fg
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  haveI := AdicCompletion.isLocalRing_of_fg fg
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg)).symm

中文:
引理 maximalIdeal_eq_map_of_fg
  条件: [是局部环 R] (fg : (maximalIdeal R).FG)
  证明: AdicCompletion.isLocalRing_of_fg fg
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  haveI := AdicCompletion.isLocalRing_of_fg fg
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg)).symm

Depends on / 依赖: AdicCompletion, AdicCompletion.isLocalRing_of_fg, isLocalRing_of_fg
-/
lemma maximalIdeal_eq_map_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  haveI := AdicCompletion.isLocalRing_of_fg fg
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg)).symm

/--
lemma `maximalIdeal_eq_map` / 引理 `maximalIdeal_eq_map`

English:
lemma maximalIdeal_eq_map
  given: [IsNoetherianRing R] [IsLocalRing R]
  proof: (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _)
    (maximalIdeal R).fg_of_isNoetherianRing)).symm

中文:
引理 maximalIdeal_eq_map
  条件: [是Noether环 R] [是局部环 R]
  证明: (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _)
    (maximalIdeal R).fg_of_isNoetherianRing)).symm

Depends on / 依赖: AdicCompletion, AdicCompletion.isMaximal_map_of_le, IsLocalRing, IsLocalRing.eq_maximalIdeal, eq_maximalIdeal, fg_of_isNoetherianRing, isMaximal_map_of_le, le_refl, maximalIdeal
-/
lemma maximalIdeal_eq_map [IsNoetherianRing R] [IsLocalRing R] :
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _)
    (maximalIdeal R).fg_of_isNoetherianRing)).symm

/--
lemma `mem_maximalIdeal_iff_eval_one_eq_zero` / 引理 `mem_maximalIdeal_iff_eval_one_eq_zero`

English:
lemma mem_maximalIdeal_iff_eval_one_eq_zero
  statement: [IsNoetherianRing R] [IsLocalRing R]
  proof: by
  have : (AdicCompletion.eval (maximalIdeal R) R 1).ker =
    (maximalIdeal R) • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    simp [← pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing]
  rw [maximalIdeal_eq_map]; rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]
  simp [← this, eval]

中文:
引理 mem_maximalIdeal_iff_eval_one_eq_zero
  结论: [是Noether环 R] [是局部环 R]
  证明: by
  have : (AdicCompletion.eval (maximalIdeal R) R 1).ker =
    (maximalIdeal R) • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    simp [← pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing]
  rw [maximalIdeal_eq_map]; rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]
  simp [← this, eval]

Depends on / 依赖: AdicCompletion, AdicCompletion.eval, Ideal.smul_top_eq_map, Submodule, Submodule.restrictScalars_mem, fg_of_isNoetherianRing, maximalIdeal, maximalIdeal_eq_map, pow_smul_top_eq_ker_eval, restrictScalars_mem, smul_top_eq_map
-/
lemma mem_maximalIdeal_iff_eval_one_eq_zero [IsNoetherianRing R] [IsLocalRing R]
    (x : AdicCompletion (maximalIdeal R) R) :
    x in maximalIdeal (AdicCompletion (maximalIdeal R) R) ↔ x.1 1 = 0 := by
  have : (AdicCompletion.eval (maximalIdeal R) R 1).ker =
    (maximalIdeal R) • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    simp [← pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing]
  rw [maximalIdeal_eq_map]; rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]
  simp [← this, eval]

/--
lemma `algebraMap_isLocalHom_of_fg` / 引理 `algebraMap_isLocalHom_of_fg`

English:
lemma algebraMap_isLocalHom_of_fg
  given: [IsLocalRing R] (fg : (maximalIdeal R).FG)
  proof: by
  have := AdicCompletion.isLocalRing_of_fg fg
  apply ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
  simp [AdicCompletion.maximalIdeal_eq_map_of_fg fg]

中文:
引理 algebraMap_isLocalHom_of_fg
  条件: [是局部环 R] (fg : (maximalIdeal R).FG)
  证明: by
  have := AdicCompletion.isLocalRing_of_fg fg
  apply ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
  simp [AdicCompletion.maximalIdeal_eq_map_of_fg fg]

Depends on / 依赖: AdicCompletion, AdicCompletion.isLocalRing_of_fg, AdicCompletion.maximalIdeal_eq_map_of_fg, IsLocalRing, IsLocalRing.local_hom_TFAE, isLocalRing_of_fg, local_hom_TFAE, maximalIdeal_eq_map_of_fg
-/
lemma algebraMap_isLocalHom_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  have := AdicCompletion.isLocalRing_of_fg fg
  apply ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
  simp [AdicCompletion.maximalIdeal_eq_map_of_fg fg]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNoetherianRing
  signature: R] [IsLocalRing R] :
  body: AdicCompletion.algebraMap_isLocalHom_of_fg (maximalIdeal R).fg_of_isNoetherianRing

中文:
实例 [是Noether环
  签名: R] [是局部环 R] :
  定义体: AdicCompletion.algebraMap_isLocalHom_of_fg (maximalIdeal R).fg_of_isNoetherianRing

Depends on / 依赖: AdicCompletion, AdicCompletion.algebraMap_isLocalHom_of_fg, algebraMap_isLocalHom_of_fg, fg_of_isNoetherianRing, maximalIdeal
-/
instance [IsNoetherianRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  AdicCompletion.algebraMap_isLocalHom_of_fg (maximalIdeal R).fg_of_isNoetherianRing

/--
lemma `isAdicComplete_of_fg` / 引理 `isAdicComplete_of_fg`

English:
lemma isAdicComplete_of_fg
  given: [IsLocalRing R] (fg : (maximalIdeal R).FG)
  proof: AdicCompletion.isLocalRing_of_fg fg
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
  exact AdicCompletion.isAdicComplete_self _ fg

中文:
引理 isAdicComplete_of_fg
  条件: [是局部环 R] (fg : (maximalIdeal R).FG)
  证明: AdicCompletion.isLocalRing_of_fg fg
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
  exact AdicCompletion.isAdicComplete_self _ fg

Depends on / 依赖: AdicCompletion, AdicCompletion.isLocalRing_of_fg, isLocalRing_of_fg
-/
lemma isAdicComplete_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (AdicCompletion (maximalIdeal R) R) := by
  rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg]
  exact AdicCompletion.isAdicComplete_self _ fg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNoetherianRing
  signature: R] [IsLocalRing R] : IsAdicComplete
  body: AdicCompletion.isAdicComplete_of_fg (maximalIdeal R).fg_of_isNoetherianRing

中文:
实例 [是Noether环
  签名: R] [是局部环 R] : 是AdicComplete
  定义体: AdicCompletion.isAdicComplete_of_fg (maximalIdeal R).fg_of_isNoetherianRing

Depends on / 依赖: AdicCompletion, AdicCompletion.isAdicComplete_of_fg, fg_of_isNoetherianRing, isAdicComplete_of_fg, maximalIdeal
-/
instance [IsNoetherianRing R] [IsLocalRing R] : IsAdicComplete
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)) (AdicCompletion (maximalIdeal R) R) :=
  AdicCompletion.isAdicComplete_of_fg (maximalIdeal R).fg_of_isNoetherianRing

/--
lemma `residueField_map_bijective_of_fg` / 引理 `residueField_map_bijective_of_fg`

English:
lemma residueField_map_bijective_of_fg
  given: [IsLocalRing R] (fg : (maximalIdeal R).FG)
  proof: AdicCompletion.isLocalRing_of_fg fg
    haveI := AdicCompletion.algebraMap_isLocalHom_of_fg fg
    Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  have := AdicCompletion.isLocalRing_of_fg fg
  refine ⟨RingHom.injective _, fun x => ?_⟩
  rcases residue_surjective x with ⟨y, hy⟩
  rcases Ideal.Quotient.mk_surjective (y.1 1) with ⟨z, hz⟩
  use residue R z
  rw [IsLocalRing.ResidueField.map_residue]; rw [← hy]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [maximalIdeal_eq_map_of_fg fg]; rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]
  have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) z - y in
    (maximalIdeal R) ^ 1 • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    rw [AdicCompletion.algebraMap_apply]; rw [pow_smul_top_eq_ker_eval fg]
    simpa [eval, sub_eq_zero] using hz
  simpa

中文:
引理 residueField_map_bijective_of_fg
  条件: [是局部环 R] (fg : (maximalIdeal R).FG)
  证明: AdicCompletion.isLocalRing_of_fg fg
    haveI := AdicCompletion.algebraMap_isLocalHom_of_fg fg
    Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  have := AdicCompletion.isLocalRing_of_fg fg
  refine ⟨RingHom.injective _, fun x => ?_⟩
  rcases residue_surjective x with ⟨y, hy⟩
  rcases Ideal.Quotient.mk_surjective (y.1 1) with ⟨z, hz⟩
  use residue R z
  rw [IsLocalRing.ResidueField.map_residue]; rw [← hy]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [maximalIdeal_eq_map_of_fg fg]; rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]
  have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) z - y in
    (maximalIdeal R) ^ 1 • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    rw [AdicCompletion.algebraMap_apply]; rw [pow_smul_top_eq_ker_eval fg]
    simpa [eval, sub_eq_zero] using hz
  simpa

Depends on / 依赖: AdicCompletion, AdicCompletion.isLocalRing_of_fg, isLocalRing_of_fg
-/
lemma residueField_map_bijective_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    haveI := AdicCompletion.algebraMap_isLocalHom_of_fg fg
    Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  have := AdicCompletion.isLocalRing_of_fg fg
  refine ⟨RingHom.injective _, fun x => ?_⟩
  rcases residue_surjective x with ⟨y, hy⟩
  rcases Ideal.Quotient.mk_surjective (y.1 1) with ⟨z, hz⟩
  use residue R z
  rw [IsLocalRing.ResidueField.map_residue]; rw [← hy]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [maximalIdeal_eq_map_of_fg fg]; rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]
  have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) z - y in
    (maximalIdeal R) ^ 1 • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) := by
    rw [AdicCompletion.algebraMap_apply]; rw [pow_smul_top_eq_ker_eval fg]
    simpa [eval, sub_eq_zero] using hz
  simpa

variable (R) in
/--
lemma `residueField_map_bijective` / 引理 `residueField_map_bijective`

English:
lemma residueField_map_bijective
  given: [IsNoetherianRing R] [IsLocalRing R]
  proof: AdicCompletion.residueField_map_bijective_of_fg (maximalIdeal R).fg_of_isNoetherianRing

中文:
引理 residueField_map_bijective
  条件: [是Noether环 R] [是局部环 R]
  证明: AdicCompletion.residueField_map_bijective_of_fg (maximalIdeal R).fg_of_isNoetherianRing

Depends on / 依赖: AdicCompletion, AdicCompletion.residueField_map_bijective_of_fg, fg_of_isNoetherianRing, maximalIdeal, residueField_map_bijective_of_fg
-/
lemma residueField_map_bijective [IsNoetherianRing R] [IsLocalRing R] :
    Function.Bijective (IsLocalRing.ResidueField.map
      (algebraMap R (AdicCompletion (maximalIdeal R) R))) :=
    AdicCompletion.residueField_map_bijective_of_fg (maximalIdeal R).fg_of_isNoetherianRing

/--
lemma `spanFinrank_maximalIdeal_eq` / 引理 `spanFinrank_maximalIdeal_eq`

English:
lemma spanFinrank_maximalIdeal_eq
  given: [IsNoetherianRing R] [IsLocalRing R]
  proof: by
  have fg : (maximalIdeal R).FG := fg_of_isNoetherianRing (maximalIdeal R)
  have comapeq := IsLocalRing.maximalIdeal_comap (algebraMap R (AdicCompletion (maximalIdeal R) R))
  let f := Ideal.mapCotangent _ _ (Algebra.ofId R (AdicCompletion (maximalIdeal R) R))
    (le_of_eq comapeq.symm)
  have inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]; rw [LinearMap.ker_eq_bot']
    intro m hm
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    simp only [← hm', mapCotangent_toCotangent, Algebra.ofId_apply, toCotangent_eq_zero,
      maximalIdeal_eq_map, ← Ideal.map_pow, f] at hm
    rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]; rw [pow_smul_top_eq_ker_eval fg] at hm
    have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) m'.1 = of _ R m'.1 := rfl
    simp only [smul_eq_mul, eval, this, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk,
      of_apply, Submodule.mkQ_apply, mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hm
    simpa [← hm', toCotangent_eq_zero] using hm
  have surj : Function.Surjective f := by
    intro m
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    rcases Submodule.Quotient.mk_surjective _ (m'.1.1 2) with ⟨l, hl⟩
    have lmem : (transitionMap _ R (Nat.le_succ 1)) (m'.1.1 2) = m'.1.1 1 := m'.1.2 (Nat.le_succ 1)
    simp only [smul_eq_mul, Nat.succ_eq_add_one, Nat.reduceAdd, transitionMap, Submodule.factorPow,
      Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, ← hl, mk_eq_mk, factor_mk, pow_one,
      (mem_maximalIdeal_iff_eval_one_eq_zero m'.1).mp m'.2, eq_zero_iff_mem, mul_top] at lmem
    use (maximalIdeal R).toCotangent ⟨l, lmem⟩
    simp only [mapCotangent_toCotangent, Algebra.ofId_apply, ← hm', toCotangent_eq, f]
    change (of (maximalIdeal R) R l) - m' in _
    simp only [maximalIdeal_eq_map, ← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]
    simpa [pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing, eval, sub_eq_zero]
      using hl
  have rkeq := rank_eq_of_equiv_equiv _
    (LinearEquiv.ofBijective f ⟨inj, surj⟩).toAddEquiv
    (residueField_map_bijective R) (fun r m => by
      rcases IsLocalRing.residue_surjective r with ⟨s, rfl⟩
      exact map_smul f s m )
  have fg' : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).FG := by
    simpa [AdicCompletion.maximalIdeal_eq_map] using fg.map _
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg]; rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg']; rw [eq_comm]
  simp [Module.finrank, CotangentSpace, rkeq]

中文:
引理 spanFinrank_maximalIdeal_eq
  条件: [是Noether环 R] [是局部环 R]
  证明: by
  have fg : (maximalIdeal R).FG := fg_of_isNoetherianRing (maximalIdeal R)
  have comapeq := IsLocalRing.maximalIdeal_comap (algebraMap R (AdicCompletion (maximalIdeal R) R))
  let f := Ideal.mapCotangent _ _ (Algebra.ofId R (AdicCompletion (maximalIdeal R) R))
    (le_of_eq comapeq.symm)
  have inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]; rw [LinearMap.ker_eq_bot']
    intro m hm
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    simp only [← hm', mapCotangent_toCotangent, Algebra.ofId_apply, toCotangent_eq_zero,
      maximalIdeal_eq_map, ← Ideal.map_pow, f] at hm
    rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]; rw [pow_smul_top_eq_ker_eval fg] at hm
    have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) m'.1 = of _ R m'.1 := rfl
    simp only [smul_eq_mul, eval, this, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk,
      of_apply, Submodule.mkQ_apply, mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hm
    simpa [← hm', toCotangent_eq_zero] using hm
  have surj : Function.Surjective f := by
    intro m
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    rcases Submodule.Quotient.mk_surjective _ (m'.1.1 2) with ⟨l, hl⟩
    have lmem : (transitionMap _ R (Nat.le_succ 1)) (m'.1.1 2) = m'.1.1 1 := m'.1.2 (Nat.le_succ 1)
    simp only [smul_eq_mul, Nat.succ_eq_add_one, Nat.reduceAdd, transitionMap, Submodule.factorPow,
      Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, ← hl, mk_eq_mk, factor_mk, pow_one,
      (mem_maximalIdeal_iff_eval_one_eq_zero m'.1).mp m'.2, eq_zero_iff_mem, mul_top] at lmem
    use (maximalIdeal R).toCotangent ⟨l, lmem⟩
    simp only [mapCotangent_toCotangent, Algebra.ofId_apply, ← hm', toCotangent_eq, f]
    change (of (maximalIdeal R) R l) - m' in _
    simp only [maximalIdeal_eq_map, ← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]
    simpa [pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing, eval, sub_eq_zero]
      using hl
  have rkeq := rank_eq_of_equiv_equiv _
    (LinearEquiv.ofBijective f ⟨inj, surj⟩).toAddEquiv
    (residueField_map_bijective R) (fun r m => by
      rcases IsLocalRing.residue_surjective r with ⟨s, rfl⟩
      exact map_smul f s m )
  have fg' : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).FG := by
    simpa [AdicCompletion.maximalIdeal_eq_map] using fg.map _
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg]; rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg']; rw [eq_comm]
  simp [Module.finrank, CotangentSpace, rkeq]

Depends on / 依赖: AdicCompletion, Algebra, Algebra.ofId, Algebra.ofId_, Function, Function.Injective, Ideal.mapCotangent, Ideal.toCotangent_surjective, Injective, IsLocalRing, IsLocalRing.maximalIdeal_comap, LinearMap, LinearMap.ker_eq_bot, algebraMap, comapeq, comapeq.symm, fg_of_isNoetherianRing, ker_eq_bot, le_of_eq, mapCotangent
-/
lemma spanFinrank_maximalIdeal_eq [IsNoetherianRing R] [IsLocalRing R] :
    (maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank =
    (maximalIdeal R).spanFinrank := by
  have fg : (maximalIdeal R).FG := fg_of_isNoetherianRing (maximalIdeal R)
  have comapeq := IsLocalRing.maximalIdeal_comap (algebraMap R (AdicCompletion (maximalIdeal R) R))
  let f := Ideal.mapCotangent _ _ (Algebra.ofId R (AdicCompletion (maximalIdeal R) R))
    (le_of_eq comapeq.symm)
  have inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]; rw [LinearMap.ker_eq_bot']
    intro m hm
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    simp only [← hm', mapCotangent_toCotangent, Algebra.ofId_apply, toCotangent_eq_zero,
      maximalIdeal_eq_map, ← Ideal.map_pow, f] at hm
    rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]; rw [pow_smul_top_eq_ker_eval fg] at hm
    have : (algebraMap R (AdicCompletion (maximalIdeal R) R)) m'.1 = of _ R m'.1 := rfl
    simp only [smul_eq_mul, eval, this, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk,
      of_apply, Submodule.mkQ_apply, mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hm
    simpa [← hm', toCotangent_eq_zero] using hm
  have surj : Function.Surjective f := by
    intro m
    rcases Ideal.toCotangent_surjective _ m with ⟨m', hm'⟩
    rcases Submodule.Quotient.mk_surjective _ (m'.1.1 2) with ⟨l, hl⟩
    have lmem : (transitionMap _ R (Nat.le_succ 1)) (m'.1.1 2) = m'.1.1 1 := m'.1.2 (Nat.le_succ 1)
    simp only [smul_eq_mul, Nat.succ_eq_add_one, Nat.reduceAdd, transitionMap, Submodule.factorPow,
      Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, ← hl, mk_eq_mk, factor_mk, pow_one,
      (mem_maximalIdeal_iff_eval_one_eq_zero m'.1).mp m'.2, eq_zero_iff_mem, mul_top] at lmem
    use (maximalIdeal R).toCotangent ⟨l, lmem⟩
    simp only [mapCotangent_toCotangent, Algebra.ofId_apply, ← hm', toCotangent_eq, f]
    change (of (maximalIdeal R) R l) - m' in _
    simp only [maximalIdeal_eq_map, ← Ideal.map_pow]
    rw [← Submodule.restrictScalars_mem R]; rw [← Ideal.smul_top_eq_map]
    simpa [pow_smul_top_eq_ker_eval (maximalIdeal R).fg_of_isNoetherianRing, eval, sub_eq_zero]
      using hl
  have rkeq := rank_eq_of_equiv_equiv _
    (LinearEquiv.ofBijective f ⟨inj, surj⟩).toAddEquiv
    (residueField_map_bijective R) (fun r m => by
      rcases IsLocalRing.residue_surjective r with ⟨s, rfl⟩
      exact map_smul f s m )
  have fg' : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).FG := by
    simpa [AdicCompletion.maximalIdeal_eq_map] using fg.map _
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg]; rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg fg']; rw [eq_comm]
  simp [Module.finrank, CotangentSpace, rkeq]

end AdicCompletion
