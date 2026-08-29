/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Order.Lattice.Nat

/-!
# Extra lemmas about periodic points
-/

public section

open Nat Set

namespace Function
variable {α : Type*} {f : α -> α} {x y : α}

open Function (Commute)

/--
theorem `directed_ptsOfPeriod_pnat` / 定理 `directed_ptsOfPeriod_pnat`

English:
theorem directed_ptsOfPeriod_pnat
  given: (f : α -> α)
  statement: Directed (· subseteq ·) fun n : Nat+ => ptsOfPeriod f n
  proof: fun m n => ⟨m * n, fun _ hx => hx.mul_const n, fun _ hx => hx.const_mul m⟩

中文:
定理 directed_ptsOfPeriod_pnat
  条件: (f : α -> α)
  结论: Directed (· subseteq ·) fun n : 自然数+ => ptsOfPeriod f n
  证明: fun m n => ⟨m * n, fun _ hx => hx.mul_const n, fun _ hx => hx.const_mul m⟩

Depends on / 依赖: const_mul, hx.const_mul, hx.mul_const, mul_const
-/
theorem directed_ptsOfPeriod_pnat (f : α -> α) : Directed (· subseteq ·) fun n : Nat+ => ptsOfPeriod f n :=
  fun m n => ⟨m * n, fun _ hx => hx.mul_const n, fun _ hx => hx.const_mul m⟩

variable (f) in
/--
theorem `bijOn_periodicPts` / 定理 `bijOn_periodicPts`

English:
theorem bijOn_periodicPts
  statement: BijOn f (periodicPts f) (periodicPts f)
  proof: iUnion_pnat_ptsOfPeriod f ▸
    bijOn_iUnion_of_directed (directed_ptsOfPeriod_pnat f) fun i => bijOn_ptsOfPeriod f i.pos

中文:
定理 bijOn_periodicPts
  结论: 双射限制 f (periodicPts f) (periodicPts f)
  证明: iUnion_pnat_ptsOfPeriod f ▸
    bijOn_iUnion_of_directed (directed_ptsOfPeriod_pnat f) fun i => bijOn_ptsOfPeriod f i.pos

Depends on / 依赖: bijOn_iUnion_of_directed, bijOn_ptsOfPeriod, directed_ptsOfPeriod_pnat, i.pos, iUnion_pnat_ptsOfPeriod
-/
theorem bijOn_periodicPts : BijOn f (periodicPts f) (periodicPts f) :=
  iUnion_pnat_ptsOfPeriod f ▸
    bijOn_iUnion_of_directed (directed_ptsOfPeriod_pnat f) fun i => bijOn_ptsOfPeriod f i.pos

/--
theorem `minimalPeriod_eq_prime_iff` / 定理 `minimalPeriod_eq_prime_iff`

English:
theorem minimalPeriod_eq_prime_iff
  given: {p : Nat} [hp : Fact p.Prime]
  proof: by
  rw [Function.isPeriodicPt_iff_minimalPeriod_dvd]; rw [Nat.dvd_prime hp.out]; rw [← minimalPeriod_eq_one_iff_isFixedPt.not]; rw [or_and_right]; rw [and_not_self_iff]; rw [false_or]; rw [iff_self_and]
  exact fun h => ne_of_eq_of_ne h hp.out.ne_one

中文:
定理 minimalPeriod_eq_prime_iff
  条件: {p : 自然数} [hp : Fact p.素]
  证明: by
  rw [Function.isPeriodicPt_iff_minimalPeriod_dvd]; rw [Nat.dvd_prime hp.out]; rw [← minimalPeriod_eq_one_iff_isFixedPt.not]; rw [or_and_right]; rw [and_not_self_iff]; rw [false_or]; rw [iff_self_and]
  exact fun h => ne_of_eq_of_ne h hp.out.ne_one

Depends on / 依赖: Function, Function.isPeriodicPt_iff_minimalPeriod_dvd, Nat.dvd_prime, and_not_self_iff, dvd_prime, false_or, hp.out, hp.out.ne_one, iff_self_and, isPeriodicPt_iff_minimalPeriod_dvd, minimalPeriod_eq_one_iff_isFixedPt, minimalPeriod_eq_one_iff_isFixedPt.not, ne_of_eq_of_ne, ne_one, or_and_right
-/
theorem minimalPeriod_eq_prime_iff {p : Nat} [hp : Fact p.Prime] :
    minimalPeriod f x = p ↔ IsPeriodicPt f p x ∧ ¬IsFixedPt f x := by
  rw [Function.isPeriodicPt_iff_minimalPeriod_dvd]; rw [Nat.dvd_prime hp.out]; rw [← minimalPeriod_eq_one_iff_isFixedPt.not]; rw [or_and_right]; rw [and_not_self_iff]; rw [false_or]; rw [iff_self_and]
  exact fun h => ne_of_eq_of_ne h hp.out.ne_one

/--
theorem `minimalPeriod_eq_sInf_n_pos_IsPeriodicPt` / 定理 `minimalPeriod_eq_sInf_n_pos_IsPeriodicPt`

English:
theorem minimalPeriod_eq_sInf_n_pos_IsPeriodicPt
  proof: by
  dsimp +instances [minimalPeriod, periodicPts, sInf]
  grind

中文:
定理 minimalPeriod_eq_sInf_n_pos_IsPeriodicPt
  证明: by
  dsimp +instances [minimalPeriod, periodicPts, sInf]
  grind

Depends on / 依赖: instances, minimalPeriod, periodicPts
-/
theorem minimalPeriod_eq_sInf_n_pos_IsPeriodicPt :
    minimalPeriod f x = sInf { n > 0 | IsPeriodicPt f n x } := by
  dsimp +instances [minimalPeriod, periodicPts, sInf]
  grind

/--
theorem `minimalPeriod_eq_prime` / 定理 `minimalPeriod_eq_prime`

English:
theorem minimalPeriod_eq_prime
  statement: {p : Nat} [hp : Fact p.Prime] (hper : IsPeriodicPt f p x)
  proof: minimalPeriod_eq_prime_iff.mpr ⟨hper, hfix⟩

中文:
定理 minimalPeriod_eq_prime
  结论: {p : 自然数} [hp : Fact p.素] (hper : IsPeriodicPt f p x)
  证明: minimalPeriod_eq_prime_iff.mpr ⟨hper, hfix⟩

Depends on / 依赖: minimalPeriod_eq_prime_iff, minimalPeriod_eq_prime_iff.mpr
-/
theorem minimalPeriod_eq_prime {p : Nat} [hp : Fact p.Prime] (hper : IsPeriodicPt f p x)
    (hfix : ¬IsFixedPt f x) : minimalPeriod f x = p :=
  minimalPeriod_eq_prime_iff.mpr ⟨hper, hfix⟩

/--
theorem `minimalPeriod_eq_prime_pow` / 定理 `minimalPeriod_eq_prime_pow`

English:
theorem minimalPeriod_eq_prime_pow
  statement: {p k : Nat} [hp : Fact p.Prime] (hk : ¬IsPeriodicPt f (p ^ k) x)
  proof: by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow hp.out <;>
    rwa [← isPeriodicPt_iff_minimalPeriod_dvd]

中文:
定理 minimalPeriod_eq_prime_pow
  结论: {p k : 自然数} [hp : Fact p.素] (hk : ¬IsPeriodicPt f (p ^ k) x)
  证明: by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow hp.out <;>
    rwa [← isPeriodicPt_iff_minimalPeriod_dvd]

Depends on / 依赖: Nat.eq_prime_pow_of_dvd_least_prime_pow, eq_prime_pow_of_dvd_least_prime_pow, hp.out, isPeriodicPt_iff_minimalPeriod_dvd
-/
theorem minimalPeriod_eq_prime_pow {p k : Nat} [hp : Fact p.Prime] (hk : ¬IsPeriodicPt f (p ^ k) x)
    (hk1 : IsPeriodicPt f (p ^ (k + 1)) x) : minimalPeriod f x = p ^ (k + 1) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow hp.out <;>
    rwa [← isPeriodicPt_iff_minimalPeriod_dvd]

/--
theorem `Commute.minimalPeriod_of_comp_dvd_mul` / 定理 `Commute.minimalPeriod_of_comp_dvd_mul`

English:
theorem Commute.minimalPeriod_of_comp_dvd_mul
  given: {g : α -> α} (h : Commute f g)
  proof: dvd_trans h.minimalPeriod_of_comp_dvd_lcm (Nat.lcm_dvd_mul _ _)

中文:
定理 Commute.minimalPeriod_of_comp_dvd_mul
  条件: {g : α -> α} (h : Commute f g)
  证明: dvd_trans h.minimalPeriod_of_comp_dvd_lcm (Nat.lcm_dvd_mul _ _)

Depends on / 依赖: Nat.lcm_dvd_mul, dvd_trans, h.minimalPeriod_of_comp_dvd_lcm, lcm_dvd_mul, minimalPeriod_of_comp_dvd_lcm
-/
theorem Commute.minimalPeriod_of_comp_dvd_mul {g : α -> α} (h : Commute f g) :
    minimalPeriod (f ∘ g) x ∣ minimalPeriod f x * minimalPeriod g x :=
  dvd_trans h.minimalPeriod_of_comp_dvd_lcm (Nat.lcm_dvd_mul _ _)

/--
theorem `Commute.minimalPeriod_of_comp_eq_mul_of_coprime` / 定理 `Commute.minimalPeriod_of_comp_eq_mul_of_coprime`

English:
theorem Commute.minimalPeriod_of_comp_eq_mul_of_coprime
  statement: {g : α -> α} (h : Commute f g)
  proof: by
  apply h.minimalPeriod_of_comp_dvd_mul.antisymm
  suffices forall {f g : α -> α},
      Commute f g ->
        Coprime (minimalPeriod f x) (minimalPeriod g x) ->
          minimalPeriod f x ∣ minimalPeriod (f ∘ g) x from
    hco.mul_dvd_of_dvd_of_dvd (this h hco) (h.comp_eq.symm ▸ this h.symm hco.symm)
  intro f g h hco
  refine hco.dvd_of_dvd_mul_left (IsPeriodicPt.left_of_comp h ?_ ?_).minimalPeriod_dvd
  · exact (isPeriodicPt_minimalPeriod _ _).const_mul _
  · exact (isPeriodicPt_minimalPeriod _ _).mul_const _

中文:
定理 Commute.minimalPeriod_of_comp_eq_mul_of_coprime
  结论: {g : α -> α} (h : Commute f g)
  证明: by
  apply h.minimalPeriod_of_comp_dvd_mul.antisymm
  suffices forall {f g : α -> α},
      Commute f g ->
        Coprime (minimalPeriod f x) (minimalPeriod g x) ->
          minimalPeriod f x ∣ minimalPeriod (f ∘ g) x from
    hco.mul_dvd_of_dvd_of_dvd (this h hco) (h.comp_eq.symm ▸ this h.symm hco.symm)
  intro f g h hco
  refine hco.dvd_of_dvd_mul_left (IsPeriodicPt.left_of_comp h ?_ ?_).minimalPeriod_dvd
  · exact (isPeriodicPt_minimalPeriod _ _).const_mul _
  · exact (isPeriodicPt_minimalPeriod _ _).mul_const _

Depends on / 依赖: Commute, Coprime, IsPeriodicPt, IsPeriodicPt.left_of_comp, antisymm, comp_eq, const_mul, dvd_of_dvd_mul_left, h.comp_eq.symm, h.minimalPeriod_of_comp_dvd_mul.antisymm, h.symm, hco.dvd_of_dvd_mul_left, hco.mul_dvd_of_dvd_of_dvd, hco.symm, isPeriodicPt_minimalPeriod, left_of_comp, minimalPeriod, minimalPeriod_dvd, minimalPeriod_of_comp_dvd_mul, mul_const
-/
theorem Commute.minimalPeriod_of_comp_eq_mul_of_coprime {g : α -> α} (h : Commute f g)
    (hco : Coprime (minimalPeriod f x) (minimalPeriod g x)) :
    minimalPeriod (f ∘ g) x = minimalPeriod f x * minimalPeriod g x := by
  apply h.minimalPeriod_of_comp_dvd_mul.antisymm
  suffices forall {f g : α -> α},
      Commute f g ->
        Coprime (minimalPeriod f x) (minimalPeriod g x) ->
          minimalPeriod f x ∣ minimalPeriod (f ∘ g) x from
    hco.mul_dvd_of_dvd_of_dvd (this h hco) (h.comp_eq.symm ▸ this h.symm hco.symm)
  intro f g h hco
  refine hco.dvd_of_dvd_mul_left (IsPeriodicPt.left_of_comp h ?_ ?_).minimalPeriod_dvd
  · exact (isPeriodicPt_minimalPeriod _ _).const_mul _
  · exact (isPeriodicPt_minimalPeriod _ _).mul_const _

section Fintype

open Fintype

/--
theorem `minimalPeriod_le_card` / 定理 `minimalPeriod_le_card`

English:
theorem minimalPeriod_le_card
  given: [Fintype α]
  statement: minimalPeriod f x <= card α
  proof: by
  rw [← periodicOrbit_length]
  exact List.Nodup.length_le_card nodup_periodicOrbit

中文:
定理 minimalPeriod_le_card
  条件: [有限类型 α]
  结论: minimalPeriod f x <= card α
  证明: by
  rw [← periodicOrbit_length]
  exact List.Nodup.length_le_card nodup_periodicOrbit

Depends on / 依赖: List.Nodup.length_le_card, length_le_card, nodup_periodicOrbit, periodicOrbit_length
-/
theorem minimalPeriod_le_card [Fintype α] : minimalPeriod f x <= card α := by
  rw [← periodicOrbit_length]
  exact List.Nodup.length_le_card nodup_periodicOrbit

/--
theorem `isPeriodicPt_factorial_card_of_mem_periodicPts` / 定理 `isPeriodicPt_factorial_card_of_mem_periodicPts`

English:
theorem isPeriodicPt_factorial_card_of_mem_periodicPts
  given: [Fintype α] (h : x in periodicPts f)
  proof: isPeriodicPt_iff_minimalPeriod_dvd.mpr
    (Nat.dvd_factorial (minimalPeriod_pos_of_mem_periodicPts h) minimalPeriod_le_card)

中文:
定理 isPeriodicPt_factorial_card_of_mem_periodicPts
  条件: [有限类型 α] (h : x in periodicPts f)
  证明: isPeriodicPt_iff_minimalPeriod_dvd.mpr
    (Nat.dvd_factorial (minimalPeriod_pos_of_mem_periodicPts h) minimalPeriod_le_card)

Depends on / 依赖: Nat.dvd_factorial, dvd_factorial, isPeriodicPt_iff_minimalPeriod_dvd, isPeriodicPt_iff_minimalPeriod_dvd.mpr, minimalPeriod_le_card, minimalPeriod_pos_of_mem_periodicPts
-/
theorem isPeriodicPt_factorial_card_of_mem_periodicPts [Fintype α] (h : x in periodicPts f) :
    IsPeriodicPt f (card α)! x :=
  isPeriodicPt_iff_minimalPeriod_dvd.mpr
    (Nat.dvd_factorial (minimalPeriod_pos_of_mem_periodicPts h) minimalPeriod_le_card)

/--
theorem `mem_periodicPts_iff_isPeriodicPt_factorial_card` / 定理 `mem_periodicPts_iff_isPeriodicPt_factorial_card`

English:
theorem mem_periodicPts_iff_isPeriodicPt_factorial_card
  given: [Fintype α]
  proof: isPeriodicPt_factorial_card_of_mem_periodicPts
  mpr h := minimalPeriod_pos_iff_mem_periodicPts.mp
    (IsPeriodicPt.minimalPeriod_pos (Nat.factorial_pos _) h)

中文:
定理 mem_periodicPts_iff_isPeriodicPt_factorial_card
  条件: [有限类型 α]
  证明: isPeriodicPt_factorial_card_of_mem_periodicPts
  mpr h := minimalPeriod_pos_iff_mem_periodicPts.mp
    (IsPeriodicPt.minimalPeriod_pos (Nat.factorial_pos _) h)

Depends on / 依赖: isPeriodicPt_factorial_card_of_mem_periodicPts
-/
theorem mem_periodicPts_iff_isPeriodicPt_factorial_card [Fintype α] :
    x in periodicPts f ↔ IsPeriodicPt f (card α)! x where
  mp := isPeriodicPt_factorial_card_of_mem_periodicPts
  mpr h := minimalPeriod_pos_iff_mem_periodicPts.mp
    (IsPeriodicPt.minimalPeriod_pos (Nat.factorial_pos _) h)

/--
theorem `Injective.mem_periodicPts` / 定理 `Injective.mem_periodicPts`

English:
theorem Injective.mem_periodicPts
  given: [Finite α] (h : Injective f) (x : α)
  statement: x in periodicPts f
  proof: by
  obtain ⟨m, n, heq, hne⟩ : exists m n, f^[m] x = f^[n] x ∧ m != n := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact mk_mem_periodicPts (by lia) (iterate_cancel h heq.symm)
  · exact mk_mem_periodicPts (by lia) (iterate_cancel h heq)

中文:
定理 单射.mem_periodicPts
  条件: [有限 α] (h : 单射 f) (x : α)
  结论: x in periodicPts f
  证明: by
  obtain ⟨m, n, heq, hne⟩ : exists m n, f^[m] x = f^[n] x ∧ m != n := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact mk_mem_periodicPts (by lia) (iterate_cancel h heq.symm)
  · exact mk_mem_periodicPts (by lia) (iterate_cancel h heq)

Depends on / 依赖: Injective, heq.symm, iterate_cancel, lt_or_gt_of_ne, mk_mem_periodicPts, not_injective_infinite_finite
-/
theorem Injective.mem_periodicPts [Finite α] (h : Injective f) (x : α) : x in periodicPts f := by
  obtain ⟨m, n, heq, hne⟩ : exists m n, f^[m] x = f^[n] x ∧ m != n := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact mk_mem_periodicPts (by lia) (iterate_cancel h heq.symm)
  · exact mk_mem_periodicPts (by lia) (iterate_cancel h heq)

/--
theorem `injective_iff_periodicPts_eq_univ` / 定理 `injective_iff_periodicPts_eq_univ`

English:
theorem injective_iff_periodicPts_eq_univ
  given: [Finite α]
  statement: Injective f ↔ periodicPts f = univ
  proof: by
  refine ⟨fun h => eq_univ_iff_forall.mpr h.mem_periodicPts, fun h => ?_⟩
  rw [Finite.injective_iff_surjective]; rw [← range_eq_univ]; rw [← univ_subset_iff]; rw [← h]
  apply periodicPts_subset_range

中文:
定理 injective_iff_periodicPts_eq_univ
  条件: [有限 α]
  结论: 单射 f ↔ periodicPts f = univ
  证明: by
  refine ⟨fun h => eq_univ_iff_forall.mpr h.mem_periodicPts, fun h => ?_⟩
  rw [Finite.injective_iff_surjective]; rw [← range_eq_univ]; rw [← univ_subset_iff]; rw [← h]
  apply periodicPts_subset_range

Depends on / 依赖: Finite, Finite.injective_iff_surjective, eq_univ_iff_forall, eq_univ_iff_forall.mpr, h.mem_periodicPts, injective_iff_surjective, mem_periodicPts, periodicPts_subset_range, range_eq_univ, univ_subset_iff
-/
theorem injective_iff_periodicPts_eq_univ [Finite α] : Injective f ↔ periodicPts f = univ := by
  refine ⟨fun h => eq_univ_iff_forall.mpr h.mem_periodicPts, fun h => ?_⟩
  rw [Finite.injective_iff_surjective]; rw [← range_eq_univ]; rw [← univ_subset_iff]; rw [← h]
  apply periodicPts_subset_range

/--
theorem `injective_iff_iterate_factorial_card_eq_id` / 定理 `injective_iff_iterate_factorial_card_eq_id`

English:
theorem injective_iff_iterate_factorial_card_eq_id
  given: [Fintype α]
  proof: by
  simp only [injective_iff_periodicPts_eq_univ, mem_periodicPts_iff_isPeriodicPt_factorial_card,
    funext_iff, eq_univ_iff_forall, IsPeriodicPt, id, IsFixedPt]

中文:
定理 injective_iff_iterate_factorial_card_eq_id
  条件: [有限类型 α]
  证明: by
  simp only [injective_iff_periodicPts_eq_univ, mem_periodicPts_iff_isPeriodicPt_factorial_card,
    funext_iff, eq_univ_iff_forall, IsPeriodicPt, id, IsFixedPt]

Depends on / 依赖: IsFixedPt, IsPeriodicPt, eq_univ_iff_forall, funext_iff, injective_iff_periodicPts_eq_univ, mem_periodicPts_iff_isPeriodicPt_factorial_card
-/
theorem injective_iff_iterate_factorial_card_eq_id [Fintype α] :
    Injective f ↔ f^[(card α)!] = id := by
  simp only [injective_iff_periodicPts_eq_univ, mem_periodicPts_iff_isPeriodicPt_factorial_card,
    funext_iff, eq_univ_iff_forall, IsPeriodicPt, id, IsFixedPt]

end Fintype

end Function

namespace Function

section Prod

variable {α β : Type*} {f : α -> α} {g : β -> β} {x : α × β} {a : α} {b : β} {m n : Nat}

/--
theorem `minimalPeriod_prodMap` / 定理 `minimalPeriod_prodMap`

English:
theorem minimalPeriod_prodMap
  given: (f : α -> α) (g : β -> β) (x : α × β)
  proof: eq_of_forall_dvd by simp [← isPeriodicPt_iff_minimalPeriod_dvd, Nat.lcm_dvd_iff]

中文:
定理 minimalPeriod_prodMap
  条件: (f : α -> α) (g : β -> β) (x : α × β)
  证明: eq_of_forall_dvd by simp [← isPeriodicPt_iff_minimalPeriod_dvd, Nat.lcm_dvd_iff]

Depends on / 依赖: Nat.lcm_dvd_iff, eq_of_forall_dvd, isPeriodicPt_iff_minimalPeriod_dvd, lcm_dvd_iff
-/
theorem minimalPeriod_prodMap (f : α -> α) (g : β -> β) (x : α × β) :
    minimalPeriod (Prod.map f g) x = (minimalPeriod f x.1).lcm (minimalPeriod g x.2) :=
eq_of_forall_dvd by simp [← isPeriodicPt_iff_minimalPeriod_dvd, Nat.lcm_dvd_iff]

/--
theorem `minimalPeriod_fst_dvd` / 定理 `minimalPeriod_fst_dvd`

English:
theorem minimalPeriod_fst_dvd
  statement: minimalPeriod f x.1 ∣ minimalPeriod (Prod.map f g) x
  proof: by
  rw [minimalPeriod_prodMap]; exact Nat.dvd_lcm_left _ _

中文:
定理 minimalPeriod_fst_dvd
  结论: minimalPeriod f x.1 ∣ minimalPeriod (积类型.map f g) x
  证明: by
  rw [minimalPeriod_prodMap]; exact Nat.dvd_lcm_left _ _

Depends on / 依赖: AddSubmonoid, AddSubmonoid.LocalizationMap.lift, IsAddUnit, IsAddUnit.map, LocalizationMap, Nat.dvd_lcm_left, dvd_lcm_left, g.map_nsmul, map_nsmul, minimalPeriod_prodMap, nsmulAddMonoidHom
-/
theorem minimalPeriod_fst_dvd : minimalPeriod f x.1 ∣ minimalPeriod (Prod.map f g) x := by
  rw [minimalPeriod_prodMap]; exact Nat.dvd_lcm_left _ _

/--
theorem `minimalPeriod_snd_dvd` / 定理 `minimalPeriod_snd_dvd`

English:
theorem minimalPeriod_snd_dvd
  statement: minimalPeriod g x.2 ∣ minimalPeriod (Prod.map f g) x
  proof: by
  rw [minimalPeriod_prodMap]; exact Nat.dvd_lcm_right _ _

中文:
定理 minimalPeriod_snd_dvd
  结论: minimalPeriod g x.2 ∣ minimalPeriod (积类型.map f g) x
  证明: by
  rw [minimalPeriod_prodMap]; exact Nat.dvd_lcm_right _ _

Depends on / 依赖: AddSubmonoid, AddSubmonoid.LocalizationMap.lift_eq, LocalizationMap, Nat.dvd_lcm_right, dvd_lcm_right, lift_eq, minimalPeriod_prodMap
-/
theorem minimalPeriod_snd_dvd : minimalPeriod g x.2 ∣ minimalPeriod (Prod.map f g) x := by
  rw [minimalPeriod_prodMap]; exact Nat.dvd_lcm_right _ _

end Prod

section Pi

variable {ι : Type*} {α : ι -> Type*} {f : forall i, α i -> α i} {x : forall i, α i}

/--
theorem `minimalPeriod_piMap` / 定理 `minimalPeriod_piMap`

English:
theorem minimalPeriod_piMap
  proof: by
  conv_lhs => simp [minimalPeriod_eq_sInf_n_pos_IsPeriodicPt]
  simp [← isPeriodicPt_iff_minimalPeriod_dvd]

中文:
定理 minimalPeriod_piMap
  证明: by
  conv_lhs => simp [minimalPeriod_eq_sInf_n_pos_IsPeriodicPt]
  simp [← isPeriodicPt_iff_minimalPeriod_dvd]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.LocalizationMap.lift_comp, LocalizationMap, conv_lhs, isPeriodicPt_iff_minimalPeriod_dvd, lift_comp, minimalPeriod_eq_sInf_n_pos_IsPeriodicPt
-/
theorem minimalPeriod_piMap :
    minimalPeriod (Pi.map f) x = sInf { n > 0 | forall i, minimalPeriod (f i) (x i) ∣ n } := by
  conv_lhs => simp [minimalPeriod_eq_sInf_n_pos_IsPeriodicPt]
  simp [← isPeriodicPt_iff_minimalPeriod_dvd]

/--
theorem `minimalPeriod_piMap_fintype` / 定理 `minimalPeriod_piMap_fintype`

English:
theorem minimalPeriod_piMap_fintype
  given: [Fintype ι]
  proof: eq_of_forall_dvd by simp [← isPeriodicPt_iff_minimalPeriod_dvd]

中文:
定理 minimalPeriod_piMap_fintype
  条件: [有限类型 ι]
  证明: eq_of_forall_dvd by simp [← isPeriodicPt_iff_minimalPeriod_dvd]

Depends on / 依赖: eq_of_forall_dvd, isPeriodicPt_iff_minimalPeriod_dvd
-/
theorem minimalPeriod_piMap_fintype [Fintype ι] :
    minimalPeriod (Pi.map f) x = Finset.univ.lcm (fun i => minimalPeriod (f i) (x i)) :=
eq_of_forall_dvd by simp [← isPeriodicPt_iff_minimalPeriod_dvd]

/--
theorem `minimalPeriod_single_dvd_minimalPeriod_piMap` / 定理 `minimalPeriod_single_dvd_minimalPeriod_piMap`

English:
theorem minimalPeriod_single_dvd_minimalPeriod_piMap
  given: (i : ι)
  proof: by
  simp only [minimalPeriod_piMap]
  by_cases h : {n | 0 < n ∧ forall (i : ι), minimalPeriod (f i) (x i) ∣ n}.Nonempty
  · exact (Nat.sInf_mem h).2 i
  · simp [not_nonempty_iff_eq_empty.mp h]

中文:
定理 minimalPeriod_single_dvd_minimalPeriod_piMap
  条件: (i : ι)
  证明: by
  simp only [minimalPeriod_piMap]
  by_cases h : {n | 0 < n ∧ forall (i : ι), minimalPeriod (f i) (x i) ∣ n}.Nonempty
  · exact (Nat.sInf_mem h).2 i
  · simp [not_nonempty_iff_eq_empty.mp h]

Depends on / 依赖: Nat.sInf_mem, Nonempty, minimalPeriod, minimalPeriod_piMap, not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty.mp, sInf_mem
-/
theorem minimalPeriod_single_dvd_minimalPeriod_piMap (i : ι) :
    minimalPeriod (f i) (x i) ∣ minimalPeriod (Pi.map f) x := by
  simp only [minimalPeriod_piMap]
  by_cases h : {n | 0 < n ∧ forall (i : ι), minimalPeriod (f i) (x i) ∣ n}.Nonempty
  · exact (Nat.sInf_mem h).2 i
  · simp [not_nonempty_iff_eq_empty.mp h]

end Pi

end Function
