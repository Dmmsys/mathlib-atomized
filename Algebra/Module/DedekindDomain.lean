/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Modules over a Dedekind domain

Over a Dedekind domain, an `I`-torsion module is the internal direct sum of its `p i ^ e i`-torsion
submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in prime ideals.
Therefore, as any finitely generated torsion module is `I`-torsion for some `I`, it is an internal
direct sum of its `p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`.
-/

public section


universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R] {M : Type v} [AddCommGroup M] [Module R M]

open scoped DirectSum

namespace Submodule

open UniqueFactorizationMonoid

/--
theorem `isInternal_prime_power_torsion_of_is_torsion_by_ideal` / 定理 `isInternal_prime_power_torsion_of_is_torsion_by_ideal`

English:
theorem isInternal_prime_power_torsion_of_is_torsion_by_ideal
  proof: by
  let P := factors I
  have prime_of_mem := fun p (hp : p in P.toFinset) =>
    prime_of_factor p (Multiset.mem_toFinset.mp hp)
  apply torsionBySet_isInternal (p := fun p => p ^ P.count p) _
  · convert! hM
    rw [← Finset.inf_eq_iInf]; rw [IsDedekindDomain.inf_pow_eq_prod_of_prime]; rw [← Fins

中文:
定理 isInternal_prime_power_torsion_of_is_torsion_by_ideal
  证明: by
  let P := factors I
  have prime_of_mem := fun p (hp : p in P.toFinset) =>
    prime_of_factor p (Multiset.mem_toFinset.mp hp)
  apply torsionBySet_isInternal (p := fun p => p ^ P.count p) _
  · convert! hM
    rw [← Finset.inf_eq_iInf]; rw [IsDedekindDomain.inf_pow_eq_prod_of_prime]; rw [← Fins

Depends on / 依赖: Finset, Finset.inf_eq_iInf, Finset.prod_multiset_count, Ideal.irreducible_pow_sup, IsDedekindDomain, IsDedekindDomain.inf_pow_eq_prod_of_prime, Multiset, Multiset.mem_toFinset.mp, P.count, P.toFinset, associated_iff_eq, convert, factors, factors_prod, inf_eq_iInf, inf_pow_eq_prod_of_prime, irreducible_pow_sup, mem_toFinset, normalizedFactors, prime_of_factor
-/
theorem isInternal_prime_power_torsion_of_is_torsion_by_ideal
    {I : Ideal R} (hI : I != ⊥) (hM : Module.IsTorsionBySet R M I) :
    DirectSum.IsInternal fun p : (factors I).toFinset =>
      torsionBySet R M (p ^ (factors I).count ↑p : Ideal R) := by
  let P := factors I
  have prime_of_mem := fun p (hp : p in P.toFinset) =>
    prime_of_factor p (Multiset.mem_toFinset.mp hp)
  apply torsionBySet_isInternal (p := fun p => p ^ P.count p) _
  · convert! hM
    rw [← Finset.inf_eq_iInf]; rw [IsDedekindDomain.inf_pow_eq_prod_of_prime]; rw [← Finset.prod_multiset_count]; rw [← associated_iff_eq]
    · exact factors_prod hI
    · exact prime_of_mem
    · exact fun _ _ _ _ ij => ij
  · intro p hp q hq pq
    rw [Ideal.irreducible_pow_sup]
    · suffices (normalizedFactors _).count p = 0 by rw [this, zero_min, pow_zero, Ideal.one_eq_top]
      rw [Multiset.count_eq_zero]; rw [normalizedFactors_of_irreducible_pow (prime_of_mem q hq).irreducible]; rw [Multiset.mem_replicate]
exact fun H => pq H.2.trans normalize_eq q
    · rw [← Ideal.zero_eq_bot]; apply pow_ne_zero; exact (prime_of_mem q hq).ne_zero
    · exact (prime_of_mem p hp).irreducible

/--
theorem `isInternal_prime_power_torsion` / 定理 `isInternal_prime_power_torsion`

English:
theorem isInternal_prime_power_torsion
  statement: [Module.Finite R M]
  proof: by
  have hM' := Module.isTorsionBySet_annihilator_top R M
  have hI := Submodule.annihilator_top_inter_nonZeroDivisors hM
  refine isInternal_prime_power_torsion_of_is_torsion_by_ideal ?_ hM'
  rw [Submodule.ne_bot_iff]
  obtain ⟨x, H, hx⟩ := hI; exact ⟨x, H, nonZeroDivisors.ne_zero hx⟩

中文:
定理 isInternal_prime_power_torsion
  结论: [Module.Finite R M]
  证明: by
  have hM' := Module.isTorsionBySet_annihilator_top R M
  have hI := Submodule.annihilator_top_inter_nonZeroDivisors hM
  refine isInternal_prime_power_torsion_of_is_torsion_by_ideal ?_ hM'
  rw [Submodule.ne_bot_iff]
  obtain ⟨x, H, hx⟩ := hI; exact ⟨x, H, nonZeroDivisors.ne_zero hx⟩

Depends on / 依赖: Module, Module.isTorsionBySet_annihilator_top, Submodule, Submodule.annihilator_top_inter_nonZeroDivisors, Submodule.ne_bot_iff, annihilator_top_inter_nonZeroDivisors, isInternal_prime_power_torsion_of_is_torsion_by_ideal, isTorsionBySet_annihilator_top, ne_bot_iff, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero
-/
theorem isInternal_prime_power_torsion [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).toFinset =>
      torsionBySet R M (p ^ (factors (⊤ : Submodule R M).annihilator).count ↑p : Ideal R) := by
  have hM' := Module.isTorsionBySet_annihilator_top R M
  have hI := Submodule.annihilator_top_inter_nonZeroDivisors hM
  refine isInternal_prime_power_torsion_of_is_torsion_by_ideal ?_ hM'
  rw [Submodule.ne_bot_iff]
  obtain ⟨x, H, hx⟩ := hI; exact ⟨x, H, nonZeroDivisors.ne_zero hx⟩

/--
theorem `exists_isInternal_prime_power_torsion` / 定理 `exists_isInternal_prime_power_torsion`

English:
theorem exists_isInternal_prime_power_torsion
  given: [Module.Finite R M] (hM : Module.IsTorsion R M)
  proof: by
  exact ⟨_, _, fun p hp => prime_of_factor p (Multiset.mem_toFinset.mp hp), _,
    isInternal_prime_power_torsion hM⟩

中文:
定理 exists_isInternal_prime_power_torsion
  条件: [Module.Finite R M] (hM : Module.IsTorsion R M)
  证明: by
  exact ⟨_, _, fun p hp => prime_of_factor p (Multiset.mem_toFinset.mp hp), _,
    isInternal_prime_power_torsion hM⟩

Depends on / 依赖: Multiset, Multiset.mem_toFinset.mp, isInternal_prime_power_torsion, mem_toFinset, prime_of_factor
-/
theorem exists_isInternal_prime_power_torsion [Module.Finite R M] (hM : Module.IsTorsion R M) :
    exists (P : Finset <| Ideal R) (_ : DecidableEq P) (_ : forall p in P, Prime p) (e : P -> Nat),
      DirectSum.IsInternal fun p : P => torsionBySet R M (p ^ e p : Ideal R) := by
  exact ⟨_, _, fun p hp => prime_of_factor p (Multiset.mem_toFinset.mp hp), _,
    isInternal_prime_power_torsion hM⟩

end Submodule
