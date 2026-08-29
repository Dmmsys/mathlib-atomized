/-
Copyright (c) 2024 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Divisibility.Prod
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Localizing a product of commutative rings

## Main Result

* `bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom`: the canonical map from a
    localization of a finite product of rings `R i` at a monoid `M` to the direct product of
    localizations `R i` at the projection of `M` onto each corresponding factor is bijective.

## Implementation notes

See `Mathlib/RingTheory/Localization/Defs.lean` for a design overview.

## Tags
localization, commutative ring
-/

public section

namespace IsLocalization

variable {ι : Type*} (R S : ι -> Type*)
  [Π i, CommSemiring (R i)] [Π i, CommSemiring (S i)] [Π i, Algebra (R i) (S i)]

/-- If `S i` is a localization of `R i` at the submonoid `M i` for each `i`,
then `Π i, S i` is a localization of `Π i, R i` at the product submonoid. -/
instance (M : Π i, Submonoid (R i)) [forall i, IsLocalization (M i) (S i)] :
    IsLocalization (.pi .univ M) (Π i, S i) where
  map_units m := Pi.isUnit_iff.mpr fun i => map_units _ ⟨m.1 i, m.2 i ⟨⟩⟩
  surj z := by
    choose rm h using fun i => surj (M := M i) (z i)
    exact ⟨(fun i => (rm i).1, ⟨_, fun i _ => (rm i).2.2⟩), funext h⟩
  exists_of_eq {x y} eq := by
    choose c hc using fun i => exists_of_eq (M := M i) (congr_fun eq i)
    exact ⟨⟨_, fun i _ => (c i).2⟩, funext hc⟩

variable (S' : Type*) [CommSemiring S'] [Algebra (Π i, R i) S'] (M : Submonoid (Π i, R i))

/--
theorem `iff_map_piEvalRingHom` / 定理 `iff_map_piEvalRingHom`

English:
theorem iff_map_piEvalRingHom
  given: [Finite ι]
  proof: iff_of_le_of_exists_dvd M _ (fun m hm i _ => ⟨m, hm, rfl⟩) fun n hn => by
    choose m mem eq using hn
    have := Fintype.ofFinite ι
    refine ⟨∏ i, m i ⟨⟩, prod_mem fun i _ => mem i _, pi_dvd_iff.mpr fun i => ?_⟩
    rw [Fintype.prod_apply]
    exact (eq i ⟨⟩).symm.dvd.trans (Finset.dvd_prod_of_mem _ <| Finset.mem_univ _)

中文:
定理 iff_map_piEvalRingHom
  条件: [有限 ι]
  证明: iff_of_le_of_exists_dvd M _ (fun m hm i _ => ⟨m, hm, rfl⟩) fun n hn => by
    choose m mem eq using hn
    have := Fintype.ofFinite ι
    refine ⟨∏ i, m i ⟨⟩, prod_mem fun i _ => mem i _, pi_dvd_iff.mpr fun i => ?_⟩
    rw [Fintype.prod_apply]
    exact (eq i ⟨⟩).symm.dvd.trans (Finset.dvd_prod_of_mem _ <| Finset.mem_univ _)

Depends on / 依赖: Finset, Finset.dvd_prod_of_mem, Finset.mem_univ, Fintype, Fintype.ofFinite, Fintype.prod_apply, dvd_prod_of_mem, iff_of_le_of_exists_dvd, mem_univ, ofFinite, pi_dvd_iff, pi_dvd_iff.mpr, prod_apply, prod_mem, symm.dvd.trans
-/
theorem iff_map_piEvalRingHom [Finite ι] :
    IsLocalization M S' ↔ IsLocalization (.pi .univ fun i => M.map (Pi.evalRingHom R i)) S' :=
  iff_of_le_of_exists_dvd M _ (fun m hm i _ => ⟨m, hm, rfl⟩) fun n hn => by
    choose m mem eq using hn
    have := Fintype.ofFinite ι
    refine ⟨∏ i, m i ⟨⟩, prod_mem fun i _ => mem i _, pi_dvd_iff.mpr fun i => ?_⟩
    rw [Fintype.prod_apply]
    exact (eq i ⟨⟩).symm.dvd.trans (Finset.dvd_prod_of_mem _ <| Finset.mem_univ _)

variable [forall i, IsLocalization (M.map (Pi.evalRingHom R i)) (S i)]

/--
lemma `isUnit_piRingHom_algebraMap_comp_piEvalRingHom` / 引理 `isUnit_piRingHom_algebraMap_comp_piEvalRingHom`

English:
lemma isUnit_piRingHom_algebraMap_comp_piEvalRingHom
  given: (y : M)
  proof: Pi.isUnit_iff.mpr fun i => map_units _ (⟨y.1 i, y, y.2, rfl⟩ : M.map (Pi.evalRingHom R i))

中文:
引理 isUnit_piRingHom_algebraMap_comp_piEvalRingHom
  条件: (y : M)
  证明: Pi.isUnit_iff.mpr fun i => map_units _ (⟨y.1 i, y, y.2, rfl⟩ : M.map (Pi.evalRingHom R i))

Depends on / 依赖: M.map, Pi.evalRingHom, Pi.isUnit_iff.mpr, evalRingHom, isUnit_iff, map_units
-/
lemma isUnit_piRingHom_algebraMap_comp_piEvalRingHom (y : M) :
    IsUnit ((RingHom.pi fun i => (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i)) y) :=
  Pi.isUnit_iff.mpr fun i => map_units _ (⟨y.1 i, y, y.2, rfl⟩ : M.map (Pi.evalRingHom R i))

/--
theorem `bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom` / 定理 `bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom`

English:
theorem bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom
  given: [IsLocalization M S'] [Finite ι]
  proof: have := (iff_map_piEvalRingHom R (Π i, S i) M).mpr inferInstance
  (ringEquivOfRingEquiv (M := M) (T := M) _ _ (.refl _) <|
    Submonoid.map_equiv_eq_comap_symm _ _).bijective

中文:
定理 bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom
  条件: [是Localization M S'] [有限 ι]
  证明: have := (iff_map_piEvalRingHom R (Π i, S i) M).mpr inferInstance
  (ringEquivOfRingEquiv (M := M) (T := M) _ _ (.refl _) <|
    Submonoid.map_equiv_eq_comap_symm _ _).bijective

Depends on / 依赖: isUnit_piRingHom_algebraMap_comp_piEvalRingHom
-/
theorem bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom [IsLocalization M S'] [Finite ι] :
    Function.Bijective (lift (S := S') (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M)) :=
  have := (iff_map_piEvalRingHom R (Π i, S i) M).mpr inferInstance
  (ringEquivOfRingEquiv (M := M) (T := M) _ _ (.refl _) <|
    Submonoid.map_equiv_eq_comap_symm _ _).bijective

open Function Ideal

include M in
variable {R} in
/--
lemma `surjective_piRingHom_algebraMap_comp_piEvalRingHom` / 引理 `surjective_piRingHom_algebraMap_comp_piEvalRingHom`

English:
lemma surjective_piRingHom_algebraMap_comp_piEvalRingHom
  proof: by
  apply Surjective.piMap (fun i => ?_)
  by_cases h₀ : (0 : R i) in (M.map (Pi.evalRingHom R i))
  · have := uniqueOfZeroMem h₀ (S := (S i))
    exact surjective_to_subsingleton (algebraMap (R i) (S i))
  · exact (IsLocalization.atUnits _ _ (by simpa)).surjective

中文:
引理 surjective_piRingHom_algebraMap_comp_piEvalRingHom
  证明: by
  apply Surjective.piMap (fun i => ?_)
  by_cases h₀ : (0 : R i) in (M.map (Pi.evalRingHom R i))
  · have := uniqueOfZeroMem h₀ (S := (S i))
    exact surjective_to_subsingleton (algebraMap (R i) (S i))
  · exact (IsLocalization.atUnits _ _ (by simpa)).surjective

Depends on / 依赖: IsLocalization, IsLocalization.atUnits, M.map, Pi.evalRingHom, Surjective, Surjective.piMap, algebraMap, atUnits, evalRingHom, surjective, surjective_to_subsingleton, uniqueOfZeroMem
-/
lemma surjective_piRingHom_algebraMap_comp_piEvalRingHom
    [forall i, Ring.KrullDimLE 0 (R i)] [forall i, IsLocalRing (R i)] :
    Surjective (RingHom.pi (fun i => (algebraMap (R i) (S i)).comp (Pi.evalRingHom R i))) := by
  apply Surjective.piMap (fun i => ?_)
  by_cases h₀ : (0 : R i) in (M.map (Pi.evalRingHom R i))
  · have := uniqueOfZeroMem h₀ (S := (S i))
    exact surjective_to_subsingleton (algebraMap (R i) (S i))
  · exact (IsLocalization.atUnits _ _ (by simpa)).surjective

variable {R} in
/--
lemma `algebraMap_pi_surjective_of_isLocalization` / 引理 `algebraMap_pi_surjective_of_isLocalization`

English:
lemma algebraMap_pi_surjective_of_isLocalization
  statement: [forall i, Ring.KrullDimLE 0 (R i)]
  proof: by
  intro s
  set S := fun (i : ι) => Localization (M.map (Pi.evalRingHom R i))
  obtain ⟨r, hr⟩ :=
    surjective_piRingHom_algebraMap_comp_piEvalRingHom
    S M ((lift (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M)) s)
  refine ⟨r, (bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom R S _ M).injective ?_⟩
  rwa [lift_eq (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M) r]

中文:
引理 algebraMap_pi_surjective_of_isLocalization
  结论: [对任意 i, 环.Krull维数不超过 0 (R i)]
  证明: by
  intro s
  set S := fun (i : ι) => Localization (M.map (Pi.evalRingHom R i))
  obtain ⟨r, hr⟩ :=
    surjective_piRingHom_algebraMap_comp_piEvalRingHom
    S M ((lift (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M)) s)
  refine ⟨r, (bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom R S _ M).injective ?_⟩
  rwa [lift_eq (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M) r]

Depends on / 依赖: Localization, M.map, Pi.evalRingHom, bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom, evalRingHom, injective, isUnit_piRingHom_algebraMap_comp_piEvalRingHom, lift_eq, surjective_piRingHom_algebraMap_comp_piEvalRingHom
-/
lemma algebraMap_pi_surjective_of_isLocalization [forall i, Ring.KrullDimLE 0 (R i)]
    [forall i, IsLocalRing (R i)] [IsLocalization M S']
    [Finite ι] : Surjective (algebraMap (Π i, R i) S') := by
  intro s
  set S := fun (i : ι) => Localization (M.map (Pi.evalRingHom R i))
  obtain ⟨r, hr⟩ :=
    surjective_piRingHom_algebraMap_comp_piEvalRingHom
    S M ((lift (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M)) s)
  refine ⟨r, (bijective_lift_piRingHom_algebraMap_comp_piEvalRingHom R S _ M).injective ?_⟩
  rwa [lift_eq (isUnit_piRingHom_algebraMap_comp_piEvalRingHom R S M) r]

end IsLocalization
