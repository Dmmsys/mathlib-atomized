/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Localizations of commutative rings at the complement of a prime ideal

## Main definitions

* `IsLocalization.AtPrime (P : Ideal R) [IsPrime P] (S : Type*)` expresses that `S` is a
  localization at (the complement of) a prime ideal `P`, as an abbreviation of
  `IsLocalization P.prime_compl S`

## Main results

* `IsLocalization.AtPrime.isLocalRing`: a theorem (not an instance) stating a localization at the
  complement of a prime ideal is a local ring

## Implementation notes

See `RingTheory.Localization.Basic` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section

open Module

variable {R : Type*} [CommSemiring R] (S : Type*) [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

section AtPrime

variable (P : Ideal R) [hp : P.IsPrime]

/--
Definition of `IsLocalization.AtPrime` / `IsLocalization.AtPrime` 的定义

English:
abbreviation IsLocalization.AtPrime
  body: IsLocalization P.primeCompl S

中文:
缩写 IsLocalization.AtPrime
  定义体: IsLocalization P.primeCompl S
-/
protected abbrev IsLocalization.AtPrime :=
  IsLocalization P.primeCompl S

/--
Definition of `Localization.AtPrime` / `Localization.AtPrime` 的定义

English:
abbreviation Localization.AtPrime
  body: Localization P.primeCompl

中文:
缩写 Localization.AtPrime
  定义体: Localization P.primeCompl
-/
protected abbrev Localization.AtPrime :=
  Localization P.primeCompl

namespace IsLocalization

/--
theorem `AtPrime.nontrivial` / 定理 `AtPrime.nontrivial`

English:
theorem AtPrime.nontrivial
  given: [IsLocalization.AtPrime S P]
  statement: Nontrivial S
  proof: nontrivial_of_ne (0 : S) 1 fun hze => by
    rw [← (algebraMap R S).map_one]; rw [← (algebraMap R S).map_zero] at hze
    obtain ⟨t, ht⟩ := (eq_iff_exists P.primeCompl S).1 hze
    have htz : (t : R) = 0 := by simpa using ht.symm
    exact t.2 (htz.symm ▸ P.zero_mem : ↑t in P)

中文:
定理 AtPrime.nontrivial
  条件: [IsLocalization.AtPrime S P]
  结论: Nontrivial S
  证明: nontrivial_of_ne (0 : S) 1 fun hze => by
    rw [← (algebraMap R S).map_one]; rw [← (algebraMap R S).map_zero] at hze
    obtain ⟨t, ht⟩ := (eq_iff_exists P.primeCompl S).1 hze
    have htz : (t : R) = 0 := by simpa using ht.symm
    exact t.2 (htz.symm ▸ P.zero_mem : ↑t in P)

Depends on / 依赖: P.primeCompl, P.zero_mem, algebraMap, eq_iff_exists, ht.symm, htz.symm, map_one, map_zero, nontrivial_of_ne, primeCompl, zero_mem
-/
theorem AtPrime.nontrivial [IsLocalization.AtPrime S P] : Nontrivial S :=
  nontrivial_of_ne (0 : S) 1 fun hze => by
    rw [← (algebraMap R S).map_one]; rw [← (algebraMap R S).map_zero] at hze
    obtain ⟨t, ht⟩ := (eq_iff_exists P.primeCompl S).1 hze
    have htz : (t : R) = 0 := by simpa using ht.symm
    exact t.2 (htz.symm ▸ P.zero_mem : ↑t in P)

/--
theorem `AtPrime.isLocalRing` / 定理 `AtPrime.isLocalRing`

English:
theorem AtPrime.isLocalRing
  given: [IsLocalization.AtPrime S P]
  statement: IsLocalRing S
  proof: letI := AtPrime.nontrivial S P -- Can't be a local instance because we can't figure out `P`.
  IsLocalRing.of_nonunits_add
    (by
      intro x y hx hy hu
      obtain ⟨z, hxyz⟩ := isUnit_iff_exists_inv.1 hu
      have : forall {r : R} {s : P.primeCompl}, mk' S r s in nonunits S -> r in P := fun {r

中文:
定理 AtPrime.isLocalRing
  条件: [IsLocalization.AtPrime S P]
  结论: IsLocalRing S
  证明: letI := AtPrime.nontrivial S P -- Can't be a local instance because we can't figure out `P`.
  IsLocalRing.of_nonunits_add
    (by
      intro x y hx hy hu
      obtain ⟨z, hxyz⟩ := isUnit_iff_exists_inv.1 hu
      have : forall {r : R} {s : P.primeCompl}, mk' S r s in nonunits S -> r in P := fun {r

Depends on / 依赖: AtPrime, AtPrime.nontrivial, IsLocalRing, IsLocalRing.of_nonunits_add, P.primeCompl, _eq_one, _mul_mk, because, exists_mk, figure, instance, isUnit_iff_exists_inv, nontrivial, nonunits, not_imp_comm, of_nonunits_add, primeCompl
-/
theorem AtPrime.isLocalRing [IsLocalization.AtPrime S P] : IsLocalRing S :=
  letI := AtPrime.nontrivial S P -- Can't be a local instance because we can't figure out `P`.
  IsLocalRing.of_nonunits_add
    (by
      intro x y hx hy hu
      obtain ⟨z, hxyz⟩ := isUnit_iff_exists_inv.1 hu
      have : forall {r : R} {s : P.primeCompl}, mk' S r s in nonunits S -> r in P := fun {r s} =>
        not_imp_comm.1 fun nr => isUnit_iff_exists_inv.2 ⟨mk' S ↑s (⟨r, nr⟩ : P.primeCompl),
mk'_mul_mk'_eq_one' _ _ show r in P.primeCompl from nr⟩
      rcases exists_mk'_eq P.primeCompl x with ⟨rx, sx, hrx⟩
      rcases exists_mk'_eq P.primeCompl y with ⟨ry, sy, hry⟩
      rcases exists_mk'_eq P.primeCompl z with ⟨rz, sz, hrz⟩
      rw [← hrx]; rw [← hry]; rw [← hrz]; rw [← mk'_add]; rw [← mk'_mul]; rw [← mk'_self S P.primeCompl.one_mem] at hxyz
      rw [← hrx] at hx
      rw [← hry] at hy
      obtain ⟨t, ht⟩ := IsLocalization.eq.1 hxyz
      simp only [mul_one, one_mul, Submonoid.coe_mul] at ht
      suffices (t : R) * (sx * sy * sz) in P from
        not_or_intro (mt hp.mem_or_mem <| not_or_intro sx.2 sy.2) sz.2
          (hp.mem_or_mem <| (hp.mem_or_mem this).resolve_left t.2)
      rw [← ht]
      exact
P.mul_mem_left _ P.mul_mem_right _
P.add_mem (P.mul_mem_right _ <| this hx) P.mul_mem_right _ this hy)

variable {A : Type*} [CommRing A] [IsDomain A]

/--
Instance `isDomain_of_local_atPrime` / 实例 `isDomain_of_local_atPrime`

English:
instance isDomain_of_local_atPrime
  signature: {P : Ideal A} (_ : P.IsPrime)
  body: isDomain_localization P.primeCompl_le_nonZeroDivisors

中文:
实例 isDomain_of_local_atPrime
  签名: {P : Ideal A} (_ : P.IsPrime)
  定义体: isDomain_localization P.primeCompl_le_nonZeroDivisors

Depends on / 依赖: P.primeCompl_le_nonZeroDivisors, isDomain_localization, primeCompl_le_nonZeroDivisors
-/
instance isDomain_of_local_atPrime {P : Ideal A} (_ : P.IsPrime) :
    IsDomain (Localization.AtPrime P) :=
  isDomain_localization P.primeCompl_le_nonZeroDivisors

end IsLocalization

namespace Localization

/--
Instance `AtPrime.isLocalRing` / 实例 `AtPrime.isLocalRing`

English:
instance AtPrime.isLocalRing
  signature: : IsLocalRing (Localization P.primeCompl)
  body: IsLocalization.AtPrime.isLocalRing (Localization P.primeCompl) P

中文:
实例 AtPrime.isLocalRing
  签名: : IsLocalRing (Localization P.primeCompl)
  定义体: IsLocalization.AtPrime.isLocalRing (Localization P.primeCompl) P
-/
instance AtPrime.isLocalRing : IsLocalRing (Localization P.primeCompl) :=
  IsLocalization.AtPrime.isLocalRing (Localization P.primeCompl) P

instance {R S : Type*} [CommRing R] [IsDomain R] {P : Ideal R} [CommRing S] [Algebra R S]
    [IsTorsionFree R S] [IsDomain S] [P.IsPrime] :
IsTorsionFree (Localization.AtPrime P)
Localization Algebra.algebraMapSubmonoid S P.primeCompl :=
  .of_isLocalization R S P.primeCompl_le_nonZeroDivisors

/--
theorem `_root_.IsLocalization.AtPrime.faithfulSMul` / 定理 `_root_.IsLocalization.AtPrime.faithfulSMul`

English:
theorem _root_.IsLocalization.AtPrime.faithfulSMul
  statement: (R : Type*) [CommRing R] [NoZeroDivisors R]
  proof: by
  rw [faithfulSMul_iff_algebraMap_injective]; rw [IsLocalization.injective_iff_isRegular P.primeCompl]
exact fun ⟨_, h⟩ => .of_ne_zero by aesop

中文:
定理 _root_.IsLocalization.AtPrime.faithfulSMul
  结论: (R : 类型) [CommRing R] [NoZeroDivisors R]
  证明: by
  rw [faithfulSMul_iff_algebraMap_injective]; rw [IsLocalization.injective_iff_isRegular P.primeCompl]
exact fun ⟨_, h⟩ => .of_ne_zero by aesop

Depends on / 依赖: IsLocalization, IsLocalization.injective_iff_isRegular, P.primeCompl, faithfulSMul_iff_algebraMap_injective, injective_iff_isRegular, of_ne_zero, primeCompl
-/
theorem _root_.IsLocalization.AtPrime.faithfulSMul (R : Type*) [CommRing R] [NoZeroDivisors R]
    [Algebra R S] (P : Ideal R) [hp : P.IsPrime] [IsLocalization.AtPrime S P] :
    FaithfulSMul R S := by
  rw [faithfulSMul_iff_algebraMap_injective]; rw [IsLocalization.injective_iff_isRegular P.primeCompl]
exact fun ⟨_, h⟩ => .of_ne_zero by aesop

instance {R : Type*} [CommRing R] [NoZeroDivisors R] (P : Ideal R) [hp : P.IsPrime] :
    FaithfulSMul R (Localization.AtPrime P) := IsLocalization.AtPrime.faithfulSMul _ _ P

end Localization

end AtPrime

namespace IsLocalization

variable {A : Type*} [CommRing A] [IsDomain A]

/--
theorem `isDomain_of_atPrime` / 定理 `isDomain_of_atPrime`

English:
theorem isDomain_of_atPrime
  statement: (S : Type*) [CommSemiring S] [Algebra A S]
  proof: isDomain_of_le_nonZeroDivisors S P.primeCompl_le_nonZeroDivisors

中文:
定理 isDomain_of_atPrime
  结论: (S : 类型) [CommSemiring S] [Algebra A S]
  证明: isDomain_of_le_nonZeroDivisors S P.primeCompl_le_nonZeroDivisors

Depends on / 依赖: P.primeCompl_le_nonZeroDivisors, isDomain_of_le_nonZeroDivisors, primeCompl_le_nonZeroDivisors
-/
theorem isDomain_of_atPrime (S : Type*) [CommSemiring S] [Algebra A S]
    (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime S P] : IsDomain S :=
  isDomain_of_le_nonZeroDivisors S P.primeCompl_le_nonZeroDivisors

namespace AtPrime

variable (I : Ideal R) [hI : I.IsPrime] [IsLocalization.AtPrime S I]

set_option backward.isDefEq.respectTransparency false in
/-- The prime ideals in the localization of a commutative ring at a prime ideal I are in
order-preserving bijection with the prime ideals contained in I. -/
@[simps!]
/--
Definition of `orderIsoOfPrime` / `orderIsoOfPrime` 的定义

English:
definition orderIsoOfPrime
  signature: : { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ p <= I }
  body: (IsLocalization.orderIsoOfPrime I.primeCompl S).trans .setCongr _ _
    show Set.ofPred _ = Set.ofPred _
    by ext; simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left]

中文:
定义 orderIsoOfPrime
  签名: : { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ p <= I }
  定义体: (IsLocalization.orderIsoOfPrime I.primeCompl S).trans .setCongr _ _
    show Set.ofPred _ = Set.ofPred _
    by ext; simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left]

Depends on / 依赖: I.primeCompl, Ideal.primeCompl, IsLocalization, IsLocalization.orderIsoOfPrime, Set.ofPred, le_compl_iff_disjoint_left, ofPred, orderIsoOfPrime, primeCompl, setCongr
-/
def orderIsoOfPrime : { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ p <= I } :=
(IsLocalization.orderIsoOfPrime I.primeCompl S).trans .setCongr _ _
    show Set.ofPred _ = Set.ofPred _
    by ext; simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left]

/--
Definition of `primeSpectrumOrderIso` / `primeSpectrumOrderIso` 的定义

English:
definition primeSpectrumOrderIso
  signature: : PrimeSpectrum S ≃o Set.Iic (⟨I, hI⟩ : PrimeSpectrum R)
  body: (PrimeSpectrum.equivSubtype S).trans (orderIsoOfPrime S I).trans
    ⟨⟨fun p => ⟨⟨p, p.2.1⟩, p.2.2⟩, fun p => ⟨p.1.1, p.1.2, p.2⟩, fun _ => rfl, fun _ => rfl⟩, .rfl⟩

中文:
定义 primeSpectrumOrderIso
  签名: : PrimeSpectrum S ≃o Set.Iic (⟨I, hI⟩ : PrimeSpectrum R)
  定义体: (PrimeSpectrum.equivSubtype S).trans (orderIsoOfPrime S I).trans
    ⟨⟨fun p => ⟨⟨p, p.2.1⟩, p.2.2⟩, fun p => ⟨p.1.1, p.1.2, p.2⟩, fun _ => rfl, fun _ => rfl⟩, .rfl⟩
-/
@[simps!] def primeSpectrumOrderIso : PrimeSpectrum S ≃o Set.Iic (⟨I, hI⟩ : PrimeSpectrum R) :=
(PrimeSpectrum.equivSubtype S).trans (orderIsoOfPrime S I).trans
    ⟨⟨fun p => ⟨⟨p, p.2.1⟩, p.2.2⟩, fun p => ⟨p.1.1, p.1.2, p.2⟩, fun _ => rfl, fun _ => rfl⟩, .rfl⟩

/--
theorem `isUnit_to_map_iff` / 定理 `isUnit_to_map_iff`

English:
theorem isUnit_to_map_iff
  given: (x : R)
  statement: IsUnit ((algebraMap R S) x) ↔ x in I.primeCompl
  proof: ⟨fun h hx =>
(isPrime_of_isPrime_disjoint I.primeCompl S I hI disjoint_compl_left).ne_top
      (Ideal.map (algebraMap R S) I).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem _ hx) h,
    fun h => map_units S ⟨x, h⟩⟩

中文:
定理 isUnit_to_map_iff
  条件: (x : R)
  结论: IsUnit ((algebraMap R S) x) ↔ x in I.primeCompl
  证明: ⟨fun h hx =>
(isPrime_of_isPrime_disjoint I.primeCompl S I hI disjoint_compl_left).ne_top
      (Ideal.map (algebraMap R S) I).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem _ hx) h,
    fun h => map_units S ⟨x, h⟩⟩

Depends on / 依赖: I.primeCompl, Ideal.map, Ideal.mem_map_of_mem, algebraMap, disjoint_compl_left, eq_top_of_isUnit_mem, isPrime_of_isPrime_disjoint, map_units, mem_map_of_mem, ne_top, primeCompl
-/
theorem isUnit_to_map_iff (x : R) : IsUnit ((algebraMap R S) x) ↔ x in I.primeCompl :=
  ⟨fun h hx =>
(isPrime_of_isPrime_disjoint I.primeCompl S I hI disjoint_compl_left).ne_top
      (Ideal.map (algebraMap R S) I).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem _ hx) h,
    fun h => map_units S ⟨x, h⟩⟩

-- Can't use typeclasses to infer the `IsLocalRing` instance, so use an `optParam` instead
-- (since `IsLocalRing` is a `Prop`, there should be no unification issues.)
/--
theorem `to_map_mem_maximal_iff` / 定理 `to_map_mem_maximal_iff`

English:
theorem to_map_mem_maximal_iff
  given: (x : R) (h : IsLocalRing S := isLocalRing S I)
  proof: not_iff_not.mp by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using!
      isUnit_to_map_iff S I x

中文:
定理 to_map_mem_maximal_iff
  条件: (x : R) (h : IsLocalRing S := isLocalRing S I)
  证明: not_iff_not.mp by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using!
      isUnit_to_map_iff S I x

Depends on / 依赖: isLocalRing
-/
theorem to_map_mem_maximal_iff (x : R) (h : IsLocalRing S := isLocalRing S I) :
    algebraMap R S x in IsLocalRing.maximalIdeal S ↔ x in I :=
not_iff_not.mp by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using!
      isUnit_to_map_iff S I x

/--
theorem `under_maximalIdeal` / 定理 `under_maximalIdeal`

English:
theorem under_maximalIdeal
  given: (h : IsLocalRing S := isLocalRing S I)
  proof: Ideal.ext fun x => by simpa only [Ideal.mem_comap] using to_map_mem_maximal_iff _ I x

@[deprecated (since := "2026-04-09")] alias comap_maximalIdeal := under_maximalIdeal

中文:
定理 under_maximalIdeal
  条件: (h : IsLocalRing S := isLocalRing S I)
  证明: Ideal.ext fun x => by simpa only [Ideal.mem_comap] using to_map_mem_maximal_iff _ I x

@[deprecated (since := "2026-04-09")] alias comap_maximalIdeal := under_maximalIdeal

Depends on / 依赖: isLocalRing
-/
theorem under_maximalIdeal (h : IsLocalRing S := isLocalRing S I) :
    (IsLocalRing.maximalIdeal S).under R = I :=
  Ideal.ext fun x => by simpa only [Ideal.mem_comap] using to_map_mem_maximal_iff _ I x

@[deprecated (since := "2026-04-09")] alias comap_maximalIdeal := under_maximalIdeal

/--
Instance `liesOver_maximalIdeal` / 实例 `liesOver_maximalIdeal`

English:
instance liesOver_maximalIdeal
  signature: (h : IsLocalRing S := isLocalRing S I)
  body: (Ideal.liesOver_iff _ _).mpr (under_maximalIdeal _ _).symm

中文:
实例 liesOver_maximalIdeal
  签名: (h : IsLocalRing S := isLocalRing S I)
  定义体: (Ideal.liesOver_iff _ _).mpr (under_maximalIdeal _ _).symm

Depends on / 依赖: isLocalRing
-/
instance liesOver_maximalIdeal (h : IsLocalRing S := isLocalRing S I) :
    (IsLocalRing.maximalIdeal S).LiesOver I :=
  (Ideal.liesOver_iff _ _).mpr (under_maximalIdeal _ _).symm

/--
theorem `isUnit_mk'_iff` / 定理 `isUnit_mk'_iff`

English:
theorem isUnit_mk'_iff
  given: (x : R) (y : I.primeCompl)
  statement: IsUnit (mk' S x y) ↔ x in I.primeCompl
  proof: ⟨fun h hx => mk'_mem_iff.mpr ((to_map_mem_maximal_iff S I x).mpr hx) h, fun h =>
    isUnit_iff_exists_inv.mpr ⟨mk' S ↑y ⟨x, h⟩, mk'_mul_mk'_eq_one ⟨x, h⟩ y⟩⟩

中文:
定理 isUnit_mk'_iff
  条件: (x : R) (y : I.primeCompl)
  结论: IsUnit (mk' S x y) ↔ x in I.primeCompl
  证明: ⟨fun h hx => mk'_mem_iff.mpr ((to_map_mem_maximal_iff S I x).mpr hx) h, fun h =>
    isUnit_iff_exists_inv.mpr ⟨mk' S ↑y ⟨x, h⟩, mk'_mul_mk'_eq_one ⟨x, h⟩ y⟩⟩

Depends on / 依赖: _eq_one, _mem_iff, _mem_iff.mpr, _mul_mk, isUnit_iff_exists_inv, isUnit_iff_exists_inv.mpr, to_map_mem_maximal_iff
-/
theorem isUnit_mk'_iff (x : R) (y : I.primeCompl) : IsUnit (mk' S x y) ↔ x in I.primeCompl :=
  ⟨fun h hx => mk'_mem_iff.mpr ((to_map_mem_maximal_iff S I x).mpr hx) h, fun h =>
    isUnit_iff_exists_inv.mpr ⟨mk' S ↑y ⟨x, h⟩, mk'_mul_mk'_eq_one ⟨x, h⟩ y⟩⟩

/--
theorem `mk'_mem_maximal_iff` / 定理 `mk'_mem_maximal_iff`

English:
theorem mk'_mem_maximal_iff
  given: (x : R) (y : I.primeCompl) (h : IsLocalRing S := isLocalRing S I)
  proof: not_iff_not.mp by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using!
      isUnit_mk'_iff S I x y

中文:
定理 mk'_mem_maximal_iff
  条件: (x : R) (y : I.primeCompl) (h : IsLocalRing S := isLocalRing S I)
  证明: not_iff_not.mp by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using!
      isUnit_mk'_iff S I x y

Depends on / 依赖: isLocalRing
-/
theorem mk'_mem_maximal_iff (x : R) (y : I.primeCompl) (h : IsLocalRing S := isLocalRing S I) :
    mk' S x y in IsLocalRing.maximalIdeal S ↔ x in I :=
not_iff_not.mp by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using!
      isUnit_mk'_iff S I x y

end AtPrime

end IsLocalization

namespace Localization

open IsLocalization

variable (I : Ideal R) [hI : I.IsPrime]
variable {I}

/--
theorem `AtPrime.under_maximalIdeal` / 定理 `AtPrime.under_maximalIdeal`

English:
theorem AtPrime.under_maximalIdeal
  proof: IsLocalization.AtPrime.under_maximalIdeal _ _

@[deprecated (since := "2026-04-09")] alias AtPrime.comap_maximalIdeal := AtPrime.under_maximalIdeal

中文:
定理 AtPrime.under_maximalIdeal
  证明: IsLocalization.AtPrime.under_maximalIdeal _ _

@[deprecated (since := "2026-04-09")] alias AtPrime.comap_maximalIdeal := AtPrime.under_maximalIdeal

Depends on / 依赖: AtPrime, IsLocalization, IsLocalization.AtPrime.under_maximalIdeal, under_maximalIdeal
-/
theorem AtPrime.under_maximalIdeal :
    (IsLocalRing.maximalIdeal (Localization I.primeCompl)).under R = I :=
  IsLocalization.AtPrime.under_maximalIdeal _ _

@[deprecated (since := "2026-04-09")] alias AtPrime.comap_maximalIdeal := AtPrime.under_maximalIdeal

/--
theorem `AtPrime.map_eq_maximalIdeal` / 定理 `AtPrime.map_eq_maximalIdeal`

English:
theorem AtPrime.map_eq_maximalIdeal
  proof: by
  convert! congr_arg (Ideal.map _) AtPrime.under_maximalIdeal.symm
  rw [map_under I.primeCompl]

中文:
定理 AtPrime.map_eq_maximalIdeal
  证明: by
  convert! congr_arg (Ideal.map _) AtPrime.under_maximalIdeal.symm
  rw [map_under I.primeCompl]

Depends on / 依赖: AtPrime, AtPrime.under_maximalIdeal.symm, I.primeCompl, Ideal.map, congr_arg, convert, map_under, primeCompl, under_maximalIdeal
-/
theorem AtPrime.map_eq_maximalIdeal :
    Ideal.map (algebraMap R (Localization.AtPrime I)) I =
      IsLocalRing.maximalIdeal (Localization I.primeCompl) := by
  convert! congr_arg (Ideal.map _) AtPrime.under_maximalIdeal.symm
  rw [map_under I.primeCompl]

/--
lemma `AtPrime.eq_maximalIdeal_iff_under_eq` / 引理 `AtPrime.eq_maximalIdeal_iff_under_eq`

English:
lemma AtPrime.eq_maximalIdeal_iff_under_eq
  given: {J : Ideal (Localization.AtPrime I)}
  proof: le_antisymm (IsLocalRing.le_maximalIdeal (fun hJ => (hI.ne_top (h.symm ▸ hJ ▸ rfl)))) by
    simpa [← AtPrime.map_eq_maximalIdeal, ← h] using Ideal.map_comap_le
  mpr h := h.symm ▸ AtPrime.under_maximalIdeal

@[deprecated (since := "2026-04-09")] alias AtPrime.eq_maximalIdeal_iff_comap_eq :=
  AtPri

中文:
引理 AtPrime.eq_maximalIdeal_iff_under_eq
  条件: {J : Ideal (Localization.AtPrime I)}
  证明: le_antisymm (IsLocalRing.le_maximalIdeal (fun hJ => (hI.ne_top (h.symm ▸ hJ ▸ rfl)))) by
    simpa [← AtPrime.map_eq_maximalIdeal, ← h] using Ideal.map_comap_le
  mpr h := h.symm ▸ AtPrime.under_maximalIdeal

@[deprecated (since := "2026-04-09")] alias AtPrime.eq_maximalIdeal_iff_comap_eq :=
  AtPri

Depends on / 依赖: AtPrime, AtPrime.map_eq_maximalIdeal, AtPrime.under_maximalIdeal, Ideal.map_comap_le, IsLocalRing, IsLocalRing.le_maximalIdeal, h.symm, hI.ne_top, le_antisymm, le_maximalIdeal, map_comap_le, map_eq_maximalIdeal, ne_top, under_maximalIdeal
-/
lemma AtPrime.eq_maximalIdeal_iff_under_eq {J : Ideal (Localization.AtPrime I)} :
    J.under R = I ↔ J = IsLocalRing.maximalIdeal (Localization.AtPrime I) where
mp h := le_antisymm (IsLocalRing.le_maximalIdeal (fun hJ => (hI.ne_top (h.symm ▸ hJ ▸ rfl)))) by
    simpa [← AtPrime.map_eq_maximalIdeal, ← h] using Ideal.map_comap_le
  mpr h := h.symm ▸ AtPrime.under_maximalIdeal

@[deprecated (since := "2026-04-09")] alias AtPrime.eq_maximalIdeal_iff_comap_eq :=
  AtPrime.eq_maximalIdeal_iff_under_eq

/--
theorem `le_comap_primeCompl_iff` / 定理 `le_comap_primeCompl_iff`

English:
theorem le_comap_primeCompl_iff
  given: {J : Ideal P} [J.IsPrime] {f : R ->+* P}
  proof: ⟨fun h x hx => by
    contrapose hx
    exact h hx,
   fun h _ hx hfxJ => hx (h hfxJ)⟩

中文:
定理 le_comap_primeCompl_iff
  条件: {J : Ideal P} [J.IsPrime] {f : R ->+* P}
  证明: ⟨fun h x hx => by
    contrapose hx
    exact h hx,
   fun h _ hx hfxJ => hx (h hfxJ)⟩

Depends on / 依赖: contrapose
-/
theorem le_comap_primeCompl_iff {J : Ideal P} [J.IsPrime] {f : R ->+* P} :
    I.primeCompl <= J.primeCompl.comap f ↔ J.comap f <= I :=
  ⟨fun h x hx => by
    contrapose hx
    exact h hx,
   fun h _ hx hfxJ => hx (h hfxJ)⟩

variable (I)

/--
Definition of `localRingHom` / `localRingHom` 的定义

English:
definition localRingHom
  signature: (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f)
  body: IsLocalization.map (Localization.AtPrime J) f (le_comap_primeCompl_iff.mpr (ge_of_eq hIJ))

@[simp]

中文:
定义 localRingHom
  签名: (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f)
  定义体: IsLocalization.map (Localization.AtPrime J) f (le_comap_primeCompl_iff.mpr (ge_of_eq hIJ))

@[simp]

Depends on / 依赖: AtPrime, IsLocalization, IsLocalization.map, Localization, Localization.AtPrime, ge_of_eq, le_comap_primeCompl_iff, le_comap_primeCompl_iff.mpr
-/
noncomputable def localRingHom (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f) :
    Localization.AtPrime I ->+* Localization.AtPrime J :=
  IsLocalization.map (Localization.AtPrime J) f (le_comap_primeCompl_iff.mpr (ge_of_eq hIJ))

@[simp]
/--
theorem `localRingHom_to_map` / 定理 `localRingHom_to_map`

English:
theorem localRingHom_to_map
  statement: (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f)
  proof: map_eq _ _

@[simp]

中文:
定理 localRingHom_to_map
  结论: (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f)
  证明: map_eq _ _

@[simp]

Depends on / 依赖: map_eq
-/
theorem localRingHom_to_map (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f)
    (x : R) : localRingHom I J f hIJ (algebraMap _ _ x) = algebraMap _ _ (f x) :=
  map_eq _ _

@[simp]
/--
theorem `localRingHom_mk'` / 定理 `localRingHom_mk'`

English:
theorem localRingHom_mk'
  statement: (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R)
  proof: map_mk' _ _ _

@[simp]

中文:
定理 localRingHom_mk'
  结论: (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R)
  证明: map_mk' _ _ _

@[simp]

Depends on / 依赖: map_mk
-/
theorem localRingHom_mk' (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R)
    (y : I.primeCompl) :
    localRingHom I J f hIJ (IsLocalization.mk' _ x y) =
      IsLocalization.mk' (Localization.AtPrime J) (f x)
        (⟨f y, le_comap_primeCompl_iff.mpr (ge_of_eq hIJ) y.2⟩ : J.primeCompl) :=
  map_mk' _ _ _

@[simp]
/--
theorem `localRingHom_mk` / 定理 `localRingHom_mk`

English:
theorem localRingHom_mk
  statement: (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R)
  proof: by
  simp_rw [mk_eq_mk', localRingHom_mk']

@[instance]

中文:
定理 localRingHom_mk
  结论: (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R)
  证明: by
  simp_rw [mk_eq_mk', localRingHom_mk']

@[instance]

Depends on / 依赖: localRingHom_mk, mk_eq_mk, simp_rw
-/
theorem localRingHom_mk (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R)
    (y : I.primeCompl) :
    localRingHom I J f hIJ (mk x y) = mk (f x) ⟨f y, by aesop⟩ := by
  simp_rw [mk_eq_mk', localRingHom_mk']

@[instance]
/--
theorem `isLocalHom_localRingHom` / 定理 `isLocalHom_localRingHom`

English:
theorem isLocalHom_localRingHom
  statement: (J : Ideal P) [hJ : J.IsPrime] (f : R ->+* P)
  proof: IsLocalHom.mk fun x hx => by
    rcases IsLocalization.exists_mk'_eq I.primeCompl x with ⟨r, s, rfl⟩
    rw [localRingHom_mk'] at hx
    rw [AtPrime.isUnit_mk'_iff] at hx ⊢
    exact fun hr => hx ((SetLike.ext_iff.mp hIJ r).mp hr)

中文:
定理 isLocalHom_localRingHom
  结论: (J : Ideal P) [hJ : J.IsPrime] (f : R ->+* P)
  证明: IsLocalHom.mk fun x hx => by
    rcases IsLocalization.exists_mk'_eq I.primeCompl x with ⟨r, s, rfl⟩
    rw [localRingHom_mk'] at hx
    rw [AtPrime.isUnit_mk'_iff] at hx ⊢
    exact fun hr => hx ((SetLike.ext_iff.mp hIJ r).mp hr)

Depends on / 依赖: AtPrime, AtPrime.isUnit_mk, I.primeCompl, IsLocalHom, IsLocalHom.mk, IsLocalization, IsLocalization.exists_mk, SetLike, SetLike.ext_iff.mp, _iff, exists_mk, ext_iff, isUnit_mk, localRingHom_mk, primeCompl
-/
theorem isLocalHom_localRingHom (J : Ideal P) [hJ : J.IsPrime] (f : R ->+* P)
    (hIJ : I = J.comap f) : IsLocalHom (localRingHom I J f hIJ) :=
  IsLocalHom.mk fun x hx => by
    rcases IsLocalization.exists_mk'_eq I.primeCompl x with ⟨r, s, rfl⟩
    rw [localRingHom_mk'] at hx
    rw [AtPrime.isUnit_mk'_iff] at hx ⊢
    exact fun hr => hx ((SetLike.ext_iff.mp hIJ r).mp hr)

/--
theorem `localRingHom_unique` / 定理 `localRingHom_unique`

English:
theorem localRingHom_unique
  statement: (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f)
  proof: map_unique _ _ hj

@[simp]

中文:
定理 localRingHom_unique
  结论: (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f)
  证明: map_unique _ _ hj

@[simp]

Depends on / 依赖: map_unique
-/
theorem localRingHom_unique (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f)
    {j : Localization.AtPrime I ->+* Localization.AtPrime J}
    (hj : forall x : R, j (algebraMap _ _ x) = algebraMap _ _ (f x)) : localRingHom I J f hIJ = j :=
  map_unique _ _ hj

@[simp]
/--
theorem `localRingHom_id` / 定理 `localRingHom_id`

English:
theorem localRingHom_id
  statement: localRingHom I I (RingHom.id R) (Ideal.comap_id I).symm = RingHom.id _
  proof: localRingHom_unique _ _ _ _ fun _ => rfl

中文:
定理 localRingHom_id
  结论: localRingHom I I (RingHom.id R) (Ideal.comap_id I).symm = RingHom.id _
  证明: localRingHom_unique _ _ _ _ fun _ => rfl

Depends on / 依赖: localRingHom_unique
-/
theorem localRingHom_id : localRingHom I I (RingHom.id R) (Ideal.comap_id I).symm = RingHom.id _ :=
  localRingHom_unique _ _ _ _ fun _ => rfl

-- `simp` can't figure out `J` so this can't be a `@[simp]` lemma.
/--
theorem `localRingHom_comp` / 定理 `localRingHom_comp`

English:
theorem localRingHom_comp
  statement: {S : Type*} [CommSemiring S] (J : Ideal S) [hJ : J.IsPrime] (K : Ideal P)
  proof: localRingHom_unique _ _ _ _ fun r => by
    simp only [Function.comp_apply, RingHom.coe_comp, localRingHom_to_map]

中文:
定理 localRingHom_comp
  结论: {S : 类型} [CommSemiring S] (J : Ideal S) [hJ : J.IsPrime] (K : Ideal P)
  证明: localRingHom_unique _ _ _ _ fun r => by
    simp only [Function.comp_apply, RingHom.coe_comp, localRingHom_to_map]

Depends on / 依赖: Function, Function.comp_apply, RingHom, RingHom.coe_comp, coe_comp, comp_apply, localRingHom_to_map, localRingHom_unique
-/
theorem localRingHom_comp {S : Type*} [CommSemiring S] (J : Ideal S) [hJ : J.IsPrime] (K : Ideal P)
    [hK : K.IsPrime] (f : R ->+* S) (hIJ : I = J.comap f) (g : S ->+* P) (hJK : J = K.comap g) :
    localRingHom I K (g.comp f) (by rw [hIJ, hJK, Ideal.comap_comap f g]) =
      (localRingHom J K g hJK).comp (localRingHom I J f hIJ) :=
  localRingHom_unique _ _ _ _ fun r => by
    simp only [Function.comp_apply, RingHom.coe_comp, localRingHom_to_map]

/-- Isomorphic rings have isomorphic localizations. -/
@[simps]
/--
Definition of `localRingEquiv` / `localRingEquiv` 的定义

English:
definition localRingEquiv
  signature: (J : Ideal P) [J.IsPrime] (f : R ≃+* P) (hIJ : I = J.comap f)
  body: localRingHom I J f hIJ
  invFun := localRingHom J I f.symm
    (by rw [hIJ, ← Ideal.comap_coe f, Ideal.comap_comap, RingEquiv.comp_symm, Ideal.comap_id])
  left_inv x := by simp [localRingHom, map_map]
  right_inv x := by simp [localRingHom, map_map]

中文:
定义 localRingEquiv
  签名: (J : Ideal P) [J.IsPrime] (f : R ≃+* P) (hIJ : I = J.comap f)
  定义体: localRingHom I J f hIJ
  invFun := localRingHom J I f.symm
    (by rw [hIJ, ← Ideal.comap_coe f, Ideal.comap_comap, RingEquiv.comp_symm, Ideal.comap_id])
  left_inv x := by simp [localRingHom, map_map]
  right_inv x := by simp [localRingHom, map_map]

Depends on / 依赖: localRingHom
-/
noncomputable def localRingEquiv (J : Ideal P) [J.IsPrime] (f : R ≃+* P) (hIJ : I = J.comap f) :
    Localization.AtPrime I ≃+* Localization.AtPrime J where
  __ := localRingHom I J f hIJ
  invFun := localRingHom J I f.symm
    (by rw [hIJ, ← Ideal.comap_coe f, Ideal.comap_comap, RingEquiv.comp_symm, Ideal.comap_id])
  left_inv x := by simp [localRingHom, map_map]
  right_inv x := by simp [localRingHom, map_map]

variable {S} in
/--
Definition of `localAlgHom` / `localAlgHom` 的定义

English:
definition localAlgHom
  signature: [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
  body: localRingHom I J f.toRingHom hIJ
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime I),
      localRingHom_to_map, IsScalarTower.algebraMap_apply R P (Localization.AtPrime J)]

中文:
定义 localAlgHom
  签名: [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
  定义体: localRingHom I J f.toRingHom hIJ
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime I),
      localRingHom_to_map, IsScalarTower.algebraMap_apply R P (Localization.AtPrime J)]

Depends on / 依赖: f.toRingHom, localRingHom, toRingHom
-/
noncomputable def localAlgHom [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
    (f : S ->ₐ[R] P) (hIJ : I = J.comap f) :
    Localization.AtPrime I ->ₐ[R] Localization.AtPrime J where
  __ := localRingHom I J f.toRingHom hIJ
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime I),
      localRingHom_to_map, IsScalarTower.algebraMap_apply R P (Localization.AtPrime J)]

variable {S} in
/--
lemma `localAlgHom_apply` / 引理 `localAlgHom_apply`

English:
lemma localAlgHom_apply
  statement: [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
  proof: rfl

中文:
引理 localAlgHom_apply
  结论: [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
  证明: rfl
-/
@[simp] lemma localAlgHom_apply [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
    (f : S ->ₐ[R] P) (hIJ : I = J.comap f) (x) :
    localAlgHom I J f hIJ x = localRingHom I J f.toRingHom hIJ x := rfl

variable {S} in
/-- Isomorphic algebras have isomorphic localizations.

See `localAlgEquiv'` for a variant where the base ring is also localized. -/
@[simps]
/--
Definition of `localAlgEquiv` / `localAlgEquiv` 的定义

English:
definition localAlgEquiv
  signature: [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
  body: localAlgHom I J f.toAlgHom hIJ
  __ := localRingEquiv I J f.toRingEquiv hIJ

中文:
定义 localAlgEquiv
  签名: [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
  定义体: localAlgHom I J f.toAlgHom hIJ
  __ := localRingEquiv I J f.toRingEquiv hIJ

Depends on / 依赖: f.toAlgHom, localAlgHom, toAlgHom
-/
noncomputable def localAlgEquiv [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
    (f : S ≃ₐ[R] P) (hIJ : I = J.comap f) :
    Localization.AtPrime I ≃ₐ[R] Localization.AtPrime J where
  __ := localAlgHom I J f.toAlgHom hIJ
  __ := localRingEquiv I J f.toRingEquiv hIJ

/--
lemma `localRingHom_bijective_of_saturated_inf_eq_top` / 引理 `localRingHom_bijective_of_saturated_inf_eq_top`

English:
lemma localRingHom_bijective_of_saturated_inf_eq_top
  proof: by
  constructor
  · suffices forall a in s, forall b in s, b ∉ P -> forall c in s, forall d in s, d ∉ P -> forall x ∉ P,
        x * (a * d) = x * (c * b) -> exists a_6 ∉ P, a_6 in s ∧ a_6 * (a * d) = a_6 * (c * b) by
      simpa [Function.Injective, (IsLocalization.mk'_surjective p.primeCompl).for

中文:
引理 localRingHom_bijective_of_saturated_inf_eq_top
  证明: by
  constructor
  · suffices forall a in s, forall b in s, b ∉ P -> forall c in s, forall d in s, d ∉ P -> forall x ∉ P,
        x * (a * d) = x * (c * b) -> exists a_6 ∉ P, a_6 in s ∧ a_6 * (a * d) = a_6 * (c * b) by
      simpa [Function.Injective, (IsLocalization.mk'_surjective p.primeCompl).for

Depends on / 依赖: Function, Function.Injective, Injective, IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.mk, Localization, Localization.localRingHom_mk, P.over_def, P.primeCompl, Subtype, Subtype.ext_iff, _eq_iff_eq, _surjective, eq_iff_exists, ext_iff, localRingHom_mk, map_mul, over_def, p.primeCompl
-/
lemma localRingHom_bijective_of_saturated_inf_eq_top
    {P : Ideal S} [P.IsPrime] {s : Subalgebra R S}
    (H : s.saturation (P.primeCompl ⊓ s.toSubmonoid) (by simp) = ⊤) (p : Ideal s)
    [p.IsPrime] [P.LiesOver p] :
    Function.Bijective (Localization.localRingHom _ _ _ (P.over_def p)) := by
  constructor
  · suffices forall a in s, forall b in s, b ∉ P -> forall c in s, forall d in s, d ∉ P -> forall x ∉ P,
        x * (a * d) = x * (c * b) -> exists a_6 ∉ P, a_6 in s ∧ a_6 * (a * d) = a_6 * (c * b) by
      simpa [Function.Injective, (IsLocalization.mk'_surjective p.primeCompl).forall, P.over_def p,
        Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq', Subtype.ext_iff, -map_mul,
        IsLocalization.eq_iff_exists P.primeCompl, IsLocalization.eq_iff_exists p.primeCompl]
    intro a _ b _ _ c _ d _ _ x hxP e
    obtain ⟨t, ⟨htP, -⟩, ht⟩ := H.ge (Set.mem_univ x)
    exact ⟨_, ‹P.IsPrime›.mul_notMem htP hxP, ht, by simp [mul_assoc, e]⟩
  · suffices forall y, forall z ∉ P, exists y' in s, exists z' ∉ P, z' in s ∧ exists t ∉ P, t * (z * y') = t * (z' * y) by
      simpa [(IsLocalization.mk'_surjective p.primeCompl).exists,
        (IsLocalization.mk'_surjective P.primeCompl).forall, P.over_def p,
        Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq, -map_mul,
        IsLocalization.eq_iff_exists P.primeCompl, Function.Surjective] using this
    intro y z hzP
    obtain ⟨a, ⟨haP, has⟩, ha⟩ := H.ge (Set.mem_univ y)
    obtain ⟨b, ⟨hbP, hbs⟩, hb⟩ := H.ge (Set.mem_univ z)
    exact ⟨_, mul_mem ha hbs, _, P.primeCompl.mul_mem (mul_mem hbP hzP) haP, mul_mem hb has, 1,
      P.primeCompl.one_mem, by ring⟩

namespace AtPrime

section

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra A B]
  [IsScalarTower R A B] [CommSemiring C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- If `P` lies over `p`, then `Localization.AtPrime P` is an algebra over `Localization.AtPrime p`.
This is not an instance for performance reasons and to avoid diamonds in the situation where the top
ring is already an algebra over `Localization.AtPrime p` (e.g., this happens for `Ideal.Fiber`). -/
@[instance_reducible]
/--
Definition of `algebraOfLiesOver` / `algebraOfLiesOver` 的定义

English:
definition algebraOfLiesOver
  body: (Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over).toAlgebra

@[deprecated (since := "2026-04-24")] alias instAlgebraOfLiesOver := algebraOfLiesOver

中文:
定义 algebraOfLiesOver
  定义体: (Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over).toAlgebra

@[deprecated (since := "2026-04-24")] alias instAlgebraOfLiesOver := algebraOfLiesOver

Depends on / 依赖: Ideal.LiesOver.over, LiesOver, Localization, Localization.localRingHom, algebraMap, localRingHom, toAlgebra
-/
noncomputable def algebraOfLiesOver
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
  (Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over).toAlgebra

@[deprecated (since := "2026-04-24")] alias instAlgebraOfLiesOver := algebraOfLiesOver

/--
Definition of `IsLiesOverAlgebra` / `IsLiesOverAlgebra` 的定义

English:
class IsLiesOverAlgebra
  parameters: (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
  axioms and operations (1):
    - algebraMap_eq : algebraMap (Localization.AtPrime p) (Localization.AtPrime P) = Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over

中文:
类 IsLiesOverAlgebra
  参数: (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
  公理与运算 (1 个):
    - algebraMap_eq : algebraMap (Localization.AtPrime p) (Localization.AtPrime P) = Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over
-/
class IsLiesOverAlgebra (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)] : Prop where
  algebraMap_eq : algebraMap (Localization.AtPrime p) (Localization.AtPrime P) =
    Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over

instance (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    letI := algebraOfLiesOver p P; IsLiesOverAlgebra p P :=
  letI := algebraOfLiesOver p P; ⟨rfl⟩

instance (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)] [IsLiesOverAlgebra p P] :
    IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P) :=
.of_algebraMap_eq by
    simp [IsScalarTower.algebraMap_apply R A (Localization.AtPrime p),
      Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R B (Localization.AtPrime P),
      IsScalarTower.algebraMap_apply R A B, IsLiesOverAlgebra.algebraMap_eq]

instance (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] (Q : Ideal C)
    [Q.IsPrime] [Q.LiesOver P] [Q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)] [IsLiesOverAlgebra p P]
    [Algebra (Localization.AtPrime P) (Localization.AtPrime Q)] [IsLiesOverAlgebra P Q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime Q)] [IsLiesOverAlgebra p Q] :
    IsScalarTower (Localization.AtPrime p) (Localization.AtPrime P) (Localization.AtPrime Q) :=
.of_algebraMap_eq' by
    simp [IsLiesOverAlgebra.algebraMap_eq, ← localRingHom_comp, ← IsScalarTower.algebraMap_eq]

end

variable {ι : Type*} {R : ι -> Type*} [forall i, CommSemiring (R i)]
variable {i : ι} (I : Ideal (R i)) [I.IsPrime]

/--
Definition of `mapPiEvalRingHom` / `mapPiEvalRingHom` 的定义

English:
abbreviation mapPiEvalRingHom
  signature: :
  body: localRingHom _ _ _ rfl

中文:
缩写 mapPiEvalRingHom
  签名: :
  定义体: localRingHom _ _ _ rfl

Depends on / 依赖: localRingHom
-/
noncomputable abbrev mapPiEvalRingHom :
    Localization.AtPrime (I.comap <| Pi.evalRingHom R i) ->+* Localization.AtPrime I :=
  localRingHom _ _ _ rfl

/--
theorem `mapPiEvalRingHom_bijective` / 定理 `mapPiEvalRingHom_bijective`

English:
theorem mapPiEvalRingHom_bijective
  statement: Function.Bijective (mapPiEvalRingHom I)
  proof: Localization.mapPiEvalRingHom_bijective _

中文:
定理 mapPiEvalRingHom_bijective
  结论: Function.Bijective (mapPiEvalRingHom I)
  证明: Localization.mapPiEvalRingHom_bijective _

Depends on / 依赖: Localization, Localization.mapPiEvalRingHom_bijective, mapPiEvalRingHom_bijective
-/
theorem mapPiEvalRingHom_bijective : Function.Bijective (mapPiEvalRingHom I) :=
  Localization.mapPiEvalRingHom_bijective _

/--
theorem `mapPiEvalRingHom_comp_algebraMap` / 定理 `mapPiEvalRingHom_comp_algebraMap`

English:
theorem mapPiEvalRingHom_comp_algebraMap
  proof: IsLocalization.map_comp _

中文:
定理 mapPiEvalRingHom_comp_algebraMap
  证明: IsLocalization.map_comp _

Depends on / 依赖: IsLocalization, IsLocalization.map_comp, map_comp
-/
theorem mapPiEvalRingHom_comp_algebraMap :
    (mapPiEvalRingHom I).comp (algebraMap _ _) = (algebraMap _ _).comp (Pi.evalRingHom R i) :=
  IsLocalization.map_comp _

/--
theorem `mapPiEvalRingHom_algebraMap_apply` / 定理 `mapPiEvalRingHom_algebraMap_apply`

English:
theorem mapPiEvalRingHom_algebraMap_apply
  given: {r : Π i, R i}
  proof: localRingHom_to_map ..

中文:
定理 mapPiEvalRingHom_algebraMap_apply
  条件: {r : Π i, R i}
  证明: localRingHom_to_map ..

Depends on / 依赖: localRingHom_to_map
-/
theorem mapPiEvalRingHom_algebraMap_apply {r : Π i, R i} :
    mapPiEvalRingHom I (algebraMap _ _ r) = algebraMap _ _ (r i) :=
  localRingHom_to_map ..

end AtPrime

section localAlg

open AtPrime

variable {S} [Algebra R P] (J : Ideal S) (K : Ideal P) [J.IsPrime] [K.IsPrime]
  [J.LiesOver I] [Algebra (Localization.AtPrime I) (Localization.AtPrime J)] [IsLiesOverAlgebra I J]
  [K.LiesOver I] [Algebra (Localization.AtPrime I) (Localization.AtPrime K)] [IsLiesOverAlgebra I K]

/-- For an `R`-algebra homomorphism `f : S →ₐ[R] P` and prime ideals `J = f⁻¹(K)` lying over `I`,
the induced algebra homomorphism from the localization of `S` at `J` to the localization of `P` at
`K` over the localization of `R` at `I`.

See `localAlgHom` for a variant where the base ring `R` is not localized. -/
@[simps!]
/--
Definition of `localAlgHom'` / `localAlgHom'` 的定义

English:
definition localAlgHom'
  signature: (f : S ->ₐ[R] P) (h : J = K.comap f)
  body: (localAlgHom J K f h).extendScalarsOfIsLocalization (Localization.AtPrime I) I.primeCompl

#adaptation_note

中文:
定义 localAlgHom'
  签名: (f : S ->ₐ[R] P) (h : J = K.comap f)
  定义体: (localAlgHom J K f h).extendScalarsOfIsLocalization (Localization.AtPrime I) I.primeCompl

#adaptation_note

Depends on / 依赖: AtPrime, I.primeCompl, Localization, Localization.AtPrime, extendScalarsOfIsLocalization, localAlgHom, primeCompl
-/
noncomputable def localAlgHom' (f : S ->ₐ[R] P) (h : J = K.comap f) :
    Localization.AtPrime J ->ₐ[Localization.AtPrime I] Localization.AtPrime K :=
  (localAlgHom J K f h).extendScalarsOfIsLocalization (Localization.AtPrime I) I.primeCompl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Isomorphic algebras have isomorphic localizations.

See `localAlgEquiv` for a variant where the base ring is not localized. -/
@[simps!]
/--
Definition of `localAlgEquiv'` / `localAlgEquiv'` 的定义

English:
definition localAlgEquiv'
  signature: (f : S ≃ₐ[R] P) (h : J = K.comap f)
  body: (localAlgEquiv J K f h).extendScalarsOfIsLocalization (Localization.AtPrime I) I.primeCompl

中文:
定义 localAlgEquiv'
  签名: (f : S ≃ₐ[R] P) (h : J = K.comap f)
  定义体: (localAlgEquiv J K f h).extendScalarsOfIsLocalization (Localization.AtPrime I) I.primeCompl

Depends on / 依赖: AtPrime, I.primeCompl, Localization, Localization.AtPrime, extendScalarsOfIsLocalization, localAlgEquiv, primeCompl
-/
noncomputable def localAlgEquiv' (f : S ≃ₐ[R] P) (h : J = K.comap f) :
    Localization.AtPrime J ≃ₐ[Localization.AtPrime I] Localization.AtPrime K :=
  (localAlgEquiv J K f h).extendScalarsOfIsLocalization (Localization.AtPrime I) I.primeCompl

end localAlg

end Localization

section

variable (q : Ideal R) [q.IsPrime] (M : Submonoid R) {S : Type*} [CommSemiring S] [Algebra R S]
  [IsLocalization.AtPrime S q]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Ideal.isPrime_map_of_isLocalizationAtPrime` / 引理 `Ideal.isPrime_map_of_isLocalizationAtPrime`

English:
lemma Ideal.isPrime_map_of_isLocalizationAtPrime
  given: {p : Ideal R} [p.IsPrime] (hpq : p <= q)
  proof: by
  have disj : Disjoint (q.primeCompl : Set R) p := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  apply IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p (by simpa) disj

中文:
引理 Ideal.isPrime_map_of_isLocalizationAtPrime
  条件: {p : Ideal R} [p.IsPrime] (hpq : p <= q)
  证明: by
  have disj : Disjoint (q.primeCompl : Set R) p := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  apply IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p (by simpa) disj

Depends on / 依赖: Disjoint, Ideal.primeCompl, IsLocalization, IsLocalization.isPrime_of_isPrime_disjoint, isPrime_of_isPrime_disjoint, le_compl_iff_disjoint_left, primeCompl, q.primeCompl
-/
lemma Ideal.isPrime_map_of_isLocalizationAtPrime {p : Ideal R} [p.IsPrime] (hpq : p <= q) :
    (p.map (algebraMap R S)).IsPrime := by
  have disj : Disjoint (q.primeCompl : Set R) p := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  apply IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p (by simpa) disj

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Ideal.under_map_of_isLocalizationAtPrime` / 引理 `Ideal.under_map_of_isLocalizationAtPrime`

English:
lemma Ideal.under_map_of_isLocalizationAtPrime
  given: {p : Ideal R} [p.IsPrime] (hpq : p <= q)
  proof: by
  have disj : Disjoint (q.primeCompl : Set R) p := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  exact IsLocalization.under_map_of_isPrime_disjoint _ _ (by simpa) disj

中文:
引理 Ideal.under_map_of_isLocalizationAtPrime
  条件: {p : Ideal R} [p.IsPrime] (hpq : p <= q)
  证明: by
  have disj : Disjoint (q.primeCompl : Set R) p := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  exact IsLocalization.under_map_of_isPrime_disjoint _ _ (by simpa) disj

Depends on / 依赖: Disjoint, Ideal.primeCompl, IsLocalization, IsLocalization.under_map_of_isPrime_disjoint, le_compl_iff_disjoint_left, primeCompl, q.primeCompl, under_map_of_isPrime_disjoint
-/
lemma Ideal.under_map_of_isLocalizationAtPrime {p : Ideal R} [p.IsPrime] (hpq : p <= q) :
    (p.map (algebraMap R S)).under R = p := by
  have disj : Disjoint (q.primeCompl : Set R) p := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  exact IsLocalization.under_map_of_isPrime_disjoint _ _ (by simpa) disj

/--
lemma `IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes` / 引理 `IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes`

English:
lemma IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes
  proof: have := hp.1.1
  have : Unique (Set.Iic (⟨p, hp.1.1⟩ : PrimeSpectrum R)) := ⟨⟨⟨p, hp.1.1⟩, by exact
fun ⦃x⦄ a => a⟩, fun i => Subtype.ext PrimeSpectrum.ext
    (minimalPrimes_eq_minimals (R := R) ▸ hp).eq_of_le i.1.2 i.2⟩
  (IsLocalization.AtPrime.primeSpectrumOrderIso S p).subsingleton

中文:
引理 IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes
  证明: have := hp.1.1
  have : Unique (Set.Iic (⟨p, hp.1.1⟩ : PrimeSpectrum R)) := ⟨⟨⟨p, hp.1.1⟩, by exact
fun ⦃x⦄ a => a⟩, fun i => Subtype.ext PrimeSpectrum.ext
    (minimalPrimes_eq_minimals (R := R) ▸ hp).eq_of_le i.1.2 i.2⟩
  (IsLocalization.AtPrime.primeSpectrumOrderIso S p).subsingleton
-/
lemma IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes
    {R : Type*} [CommSemiring R] (p : Ideal R) (hp : p in minimalPrimes R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S p (hp := hp.1.1)] :
    Subsingleton (PrimeSpectrum S) :=
  have := hp.1.1
  have : Unique (Set.Iic (⟨p, hp.1.1⟩ : PrimeSpectrum R)) := ⟨⟨⟨p, hp.1.1⟩, by exact
fun ⦃x⦄ a => a⟩, fun i => Subtype.ext PrimeSpectrum.ext
    (minimalPrimes_eq_minimals (R := R) ▸ hp).eq_of_le i.1.2 i.2⟩
  (IsLocalization.AtPrime.primeSpectrumOrderIso S p).subsingleton

open Ideal in
/--
lemma `IsLocalization.liesOver_of_isPrime_of_disjoint` / 引理 `IsLocalization.liesOver_of_isPrime_of_disjoint`

English:
lemma IsLocalization.liesOver_of_isPrime_of_disjoint
  statement: {R' S' : Type*}
  proof: by
  suffices h : Ideal.map (algebraMap R R') (under R (under R' (P.map (algebraMap S S')))) =
      Ideal.map (algebraMap R R') p from ⟨by rw [← h, IsLocalization.map_under (M := M)]⟩
  rw [under_under]; rw [← under_under (B := S)]; rw [under_map_of_isPrime_disjoint _ _ ‹_› disj]; rw [LiesOver.over

中文:
引理 IsLocalization.liesOver_of_isPrime_of_disjoint
  结论: {R' S' : 类型}
  证明: by
  suffices h : Ideal.map (algebraMap R R') (under R (under R' (P.map (algebraMap S S')))) =
      Ideal.map (algebraMap R R') p from ⟨by rw [← h, IsLocalization.map_under (M := M)]⟩
  rw [under_under]; rw [← under_under (B := S)]; rw [under_map_of_isPrime_disjoint _ _ ‹_› disj]; rw [LiesOver.over

Depends on / 依赖: Ideal.map, IsLocalization, IsLocalization.map_under, LiesOver, LiesOver.over, P.map, algebraMap, map_under, under_map_of_isPrime_disjoint, under_under
-/
lemma IsLocalization.liesOver_of_isPrime_of_disjoint {R' S' : Type*}
    (M : Submonoid R) (T : Submonoid S)
    [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
    [IsLocalization M R'] [IsLocalization T S']
    (p : Ideal R) {P : Ideal S} [P.IsPrime] [P.LiesOver p]
    (disj : Disjoint (T : Set S) (P : Set S)) :
    (P.map (algebraMap S S')).LiesOver (p.map (algebraMap R R')) := by
  suffices h : Ideal.map (algebraMap R R') (under R (under R' (P.map (algebraMap S S')))) =
      Ideal.map (algebraMap R R') p from ⟨by rw [← h, IsLocalization.map_under (M := M)]⟩
  rw [under_under]; rw [← under_under (B := S)]; rw [under_map_of_isPrime_disjoint _ _ ‹_› disj]; rw [LiesOver.over (P := P) (p := p)]

/--
lemma `Ideal.IsMaximal.of_isLocalization_of_disjoint` / 引理 `Ideal.IsMaximal.of_isLocalization_of_disjoint`

English:
lemma Ideal.IsMaximal.of_isLocalization_of_disjoint
  statement: [IsLocalization M S] {J : Ideal S}
  proof: by
obtain ⟨m, maxm, hm⟩ := exists_le_maximal J by
    rintro rfl
    exact Ideal.IsMaximal.ne_top ‹_› (by simp)
  replace hm : under R J <= under R m := comap_mono hm
  rwa [← IsLocalization.map_under M S J, IsMaximal.eq_of_le ‹_› (IsPrime.under R m).ne_top hm,
    IsLocalization.map_under M S m]

中文:
引理 Ideal.IsMaximal.of_isLocalization_of_disjoint
  结论: [IsLocalization M S] {J : Ideal S}
  证明: by
obtain ⟨m, maxm, hm⟩ := exists_le_maximal J by
    rintro rfl
    exact Ideal.IsMaximal.ne_top ‹_› (by simp)
  replace hm : under R J <= under R m := comap_mono hm
  rwa [← IsLocalization.map_under M S J, IsMaximal.eq_of_le ‹_› (IsPrime.under R m).ne_top hm,
    IsLocalization.map_under M S m]

Depends on / 依赖: Ideal.IsMaximal.ne_top, IsLocalization, IsLocalization.map_under, IsMaximal, IsMaximal.eq_of_le, IsPrime, IsPrime.under, comap_mono, eq_of_le, exists_le_maximal, map_under, ne_top, replace
-/
lemma Ideal.IsMaximal.of_isLocalization_of_disjoint [IsLocalization M S] {J : Ideal S}
    [(J.under R).IsMaximal] : J.IsMaximal := by
obtain ⟨m, maxm, hm⟩ := exists_le_maximal J by
    rintro rfl
    exact Ideal.IsMaximal.ne_top ‹_› (by simp)
  replace hm : under R J <= under R m := comap_mono hm
  rwa [← IsLocalization.map_under M S J, IsMaximal.eq_of_le ‹_› (IsPrime.under R m).ne_top hm,
    IsLocalization.map_under M S m]

end

namespace IsLocalization.AtPrime

open Algebra IsLocalRing Ideal IsLocalization IsLocalization.AtPrime

variable (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommSemiring Rₚ] [Algebra R Rₚ]
  [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] (Sₚ : Type*) [CommSemiring Sₚ] [Algebra S Sₚ]
  [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ] [Algebra Rₚ Sₚ]
  (P : Ideal S)

/--
theorem `isPrime_map_of_liesOver` / 定理 `isPrime_map_of_liesOver`

English:
theorem isPrime_map_of_liesOver
  given: [P.IsPrime] [P.LiesOver p]
  statement: (P.map (algebraMap S Sₚ)).IsPrime
  proof: isPrime_of_isPrime_disjoint _ _ _ inferInstance (Ideal.disjoint_primeCompl_of_liesOver P p)

中文:
定理 isPrime_map_of_liesOver
  条件: [P.IsPrime] [P.LiesOver p]
  结论: (P.map (algebraMap S Sₚ)).IsPrime
  证明: isPrime_of_isPrime_disjoint _ _ _ inferInstance (Ideal.disjoint_primeCompl_of_liesOver P p)

Depends on / 依赖: Ideal.disjoint_primeCompl_of_liesOver, disjoint_primeCompl_of_liesOver, isPrime_of_isPrime_disjoint
-/
theorem isPrime_map_of_liesOver [P.IsPrime] [P.LiesOver p] : (P.map (algebraMap S Sₚ)).IsPrime :=
  isPrime_of_isPrime_disjoint _ _ _ inferInstance (Ideal.disjoint_primeCompl_of_liesOver P p)

/--
theorem `map_eq_maximalIdeal` / 定理 `map_eq_maximalIdeal`

English:
theorem map_eq_maximalIdeal
  statement: p.map (algebraMap R Rₚ) = maximalIdeal Rₚ
  proof: by
  convert! congr_arg (Ideal.map (algebraMap R Rₚ)) (under_maximalIdeal Rₚ p).symm
  rw [map_under p.primeCompl]

中文:
定理 map_eq_maximalIdeal
  结论: p.map (algebraMap R Rₚ) = maximalIdeal Rₚ
  证明: by
  convert! congr_arg (Ideal.map (algebraMap R Rₚ)) (under_maximalIdeal Rₚ p).symm
  rw [map_under p.primeCompl]

Depends on / 依赖: Ideal.map, algebraMap, congr_arg, convert, map_under, p.primeCompl, primeCompl, under_maximalIdeal
-/
theorem map_eq_maximalIdeal : p.map (algebraMap R Rₚ) = maximalIdeal Rₚ := by
  convert! congr_arg (Ideal.map (algebraMap R Rₚ)) (under_maximalIdeal Rₚ p).symm
  rw [map_under p.primeCompl]

/--
Instance `isMaximal_map` / 实例 `isMaximal_map`

English:
instance isMaximal_map
  signature: : (p.map (algebraMap R Rₚ)).IsMaximal
  body: by
  rw [map_eq_maximalIdeal]
  exact maximalIdeal.isMaximal Rₚ

中文:
实例 isMaximal_map
  签名: : (p.map (algebraMap R Rₚ)).IsMaximal
  定义体: by
  rw [map_eq_maximalIdeal]
  exact maximalIdeal.isMaximal Rₚ

Depends on / 依赖: isMaximal, map_eq_maximalIdeal, maximalIdeal, maximalIdeal.isMaximal
-/
instance isMaximal_map : (p.map (algebraMap R Rₚ)).IsMaximal := by
  rw [map_eq_maximalIdeal]
  exact maximalIdeal.isMaximal Rₚ

/--
theorem `under_map_of_isMaximal` / 定理 `under_map_of_isMaximal`

English:
theorem under_map_of_isMaximal
  given: [P.IsMaximal] [P.LiesOver p]
  proof: comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver S p Sₚ P).ne_top

@[deprecated (since := "2026-04-09")] alias comap_map_of_isMaximal := under_map_of_isMaximal

中文:
定理 under_map_of_isMaximal
  条件: [P.IsMaximal] [P.LiesOver p]
  证明: comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver S p Sₚ P).ne_top

@[deprecated (since := "2026-04-09")] alias comap_map_of_isMaximal := under_map_of_isMaximal

Depends on / 依赖: comap_map_eq_self_of_isMaximal, isPrime_map_of_liesOver, ne_top
-/
theorem under_map_of_isMaximal [P.IsMaximal] [P.LiesOver p] :
    (Ideal.map (algebraMap S Sₚ) P).under S = P :=
  comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver S p Sₚ P).ne_top

@[deprecated (since := "2026-04-09")] alias comap_map_of_isMaximal := under_map_of_isMaximal

/--
lemma `under_maximalIdeal_pow` / 引理 `under_maximalIdeal_pow`

English:
lemma under_maximalIdeal_pow
  given: [p.IsMaximal] (n : Nat)
  proof: by
  ext
  rw [mem_comap]; rw [← map_eq_maximalIdeal p Rₚ]; rw [← Ideal.map_pow]; rw [algebraMap_mem_map_algebraMap_iff p.primeCompl Rₚ]
  refine ⟨fun ⟨m, hm, h⟩ => ?_, fun h => ⟨1, by simp, by simp [h]⟩⟩
  exact (IsMaximal.mul_mem_pow _ h).resolve_left (mem_primeCompl_iff.mp hm)

@[deprecated (sinc

中文:
引理 under_maximalIdeal_pow
  条件: [p.IsMaximal] (n : 自然数)
  证明: by
  ext
  rw [mem_comap]; rw [← map_eq_maximalIdeal p Rₚ]; rw [← Ideal.map_pow]; rw [algebraMap_mem_map_algebraMap_iff p.primeCompl Rₚ]
  refine ⟨fun ⟨m, hm, h⟩ => ?_, fun h => ⟨1, by simp, by simp [h]⟩⟩
  exact (IsMaximal.mul_mem_pow _ h).resolve_left (mem_primeCompl_iff.mp hm)

@[deprecated (sinc

Depends on / 依赖: Ideal.map_pow, IsEmbedding, IsMaximal, IsMaximal.mul_mem_pow, Topology, Topology.IsEmbedding.subtypeVal.continuous_iff, algebraMap_mem_map_algebraMap_iff, continuous_iff, continuous_vsub, fun_prop, map_eq_maximalIdeal, map_pow, mem_comap, mem_primeCompl_iff, mem_primeCompl_iff.mp, mul_mem_pow, p.primeCompl, primeCompl, resolve_left, subtypeVal
-/
lemma under_maximalIdeal_pow [p.IsMaximal] (n : Nat) :
    (IsLocalRing.maximalIdeal Rₚ ^ n).under R = p ^ n := by
  ext
  rw [mem_comap]; rw [← map_eq_maximalIdeal p Rₚ]; rw [← Ideal.map_pow]; rw [algebraMap_mem_map_algebraMap_iff p.primeCompl Rₚ]
  refine ⟨fun ⟨m, hm, h⟩ => ?_, fun h => ⟨1, by simp, by simp [h]⟩⟩
  exact (IsMaximal.mul_mem_pow _ h).resolve_left (mem_primeCompl_iff.mp hm)

@[deprecated (since := "2026-04-09")] alias comap_maximalIdeal_pow := under_maximalIdeal_pow

section isomorphisms

attribute [local instance] Ideal.Quotient.field

variable {S R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]
variable (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]

open IsLocalRing

/-- The isomorphism `R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ`, where `Rₚ` satisfies
`IsLocalization.AtPrime Rₚ p`. In particular, localization preserves the residue field. -/
noncomputable
/--
Definition of `equivQuotMaximalIdeal` / `equivQuotMaximalIdeal` 的定义

English:
definition equivQuotMaximalIdeal
  signature: : R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ
  body: by
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap R (Rₚ ⧸ maximalIdeal Rₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq R Rₚ, ← RingHom.comap_ker, ← under_def,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, IsLocalization.AtPrime.under_maximalIdeal 

中文:
定义 equivQuotMaximalIdeal
  签名: : R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ
  定义体: by
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap R (Rₚ ⧸ maximalIdeal Rₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq R Rₚ, ← RingHom.comap_ker, ← under_def,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, IsLocalization.AtPrime.under_maximalIdeal 

Depends on / 依赖: AtPrime, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.mk_ker, Ideal.quotEquivOfEq, IsLocalization, IsLocalization.AtPrime.under_maximalIdeal, IsLocalization.exists_mk, IsScalarTower, IsScalarTower.algebraMap_eq, Quotient, RingHom, RingHom.comap_ker, RingHom.quotientKerEquivOfSurjective, algebraMap, algebraMap_eq, comap_ker, exists_mk, maximalIdeal
-/
def equivQuotMaximalIdeal : R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ := by
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap R (Rₚ ⧸ maximalIdeal Rₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq R Rₚ, ← RingHom.comap_ker, ← under_def,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, IsLocalization.AtPrime.under_maximalIdeal Rₚ p]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p s)⁻¹
    simp only [IsScalarTower.algebraMap_eq R Rₚ (Rₚ ⧸ _),
      Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
    use x * s'
    rw [← sub_eq_zero]; rw [← map_sub]; rw [Ideal.Quotient.eq_zero_iff_mem]
    have : algebraMap R Rₚ s ∉ maximalIdeal Rₚ := by
      rw [← Ideal.mem_under]; rw [IsLocalization.AtPrime.under_maximalIdeal Rₚ p]
      exact s.prop
    refine ((inferInstance : (maximalIdeal Rₚ).IsPrime).mem_or_mem ?_).resolve_left this
    rw [mul_sub]; rw [IsLocalization.mul_mk'_eq_mk'_of_mul]; rw [IsLocalization.mk'_mul_cancel_left]; rw [← map_mul]; rw [← map_sub]; rw [← Ideal.mem_under]; rw [under_maximalIdeal Rₚ p]; rw [mul_left_comm]; rw [← Ideal.Quotient.eq_zero_iff_mem]; rw [map_sub]; rw [map_mul]; rw [map_mul]; rw [hs]; rw [mul_inv_cancel₀]; rw [mul_one]; rw [sub_self]
    rw [Ne]; rw [Ideal.Quotient.eq_zero_iff_mem]
    exact s.prop

@[simp]
/--
theorem `equivQuotMaximalIdeal_apply_mk` / 定理 `equivQuotMaximalIdeal_apply_mk`

English:
theorem equivQuotMaximalIdeal_apply_mk
  given: (x : R)
  proof: rfl

@[simp]

中文:
定理 equivQuotMaximalIdeal_apply_mk
  条件: (x : R)
  证明: rfl

@[simp]
-/
theorem equivQuotMaximalIdeal_apply_mk (x : R) :
    equivQuotMaximalIdeal p Rₚ (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap R Rₚ x)) := rfl

@[simp]
/--
theorem `equivQuotMaximalIdeal_symm_apply_mk` / 定理 `equivQuotMaximalIdeal_symm_apply_mk`

English:
theorem equivQuotMaximalIdeal_symm_apply_mk
  given: (x : R) (s : p.primeCompl)
  proof: by
  have h₁ : Ideal.Quotient.mk p ↑s != 0 := by
    simpa [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using Ideal.mem_primeCompl_iff.mp s.prop
  have h₂ : equivQuotMaximalIdeal p Rₚ (Ideal.Quotient.mk p ↑s) != 0 := by
    rwa [RingEquiv.map_ne_zero_iff]
  rw [RingEquiv.symm_apply_eq]; rw [← mul_left_in

中文:
定理 equivQuotMaximalIdeal_symm_apply_mk
  条件: (x : R) (s : p.primeCompl)
  证明: by
  have h₁ : Ideal.Quotient.mk p ↑s != 0 := by
    simpa [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using Ideal.mem_primeCompl_iff.mp s.prop
  have h₂ : equivQuotMaximalIdeal p Rₚ (Ideal.Quotient.mk p ↑s) != 0 := by
    rwa [RingEquiv.map_ne_zero_iff]
  rw [RingEquiv.symm_apply_eq]; rw [← mul_left_in

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk, Ideal.Quotient.mk_algebraMap, Ideal.mem_primeCompl_iff.mp, Quotient, RingEquiv, RingEquiv.map_ne_zero_iff, RingEquiv.symm_apply_eq, _spec, eq_zero_iff_mem, equivQuotMaximalIdeal, equivQuotMaximalIdeal_apply_mk, map_mul, map_ne_zero_iff, map_one, mem_primeCompl_iff, mk_algebraMap, mul_assoc, mul_left_inj, mul_one
-/
theorem equivQuotMaximalIdeal_symm_apply_mk (x : R) (s : p.primeCompl) :
    (equivQuotMaximalIdeal p Rₚ).symm (Ideal.Quotient.mk _ (IsLocalization.mk' Rₚ x s)) =
        (Ideal.Quotient.mk p x) * (Ideal.Quotient.mk p s)⁻¹ := by
  have h₁ : Ideal.Quotient.mk p ↑s != 0 := by
    simpa [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using Ideal.mem_primeCompl_iff.mp s.prop
  have h₂ : equivQuotMaximalIdeal p Rₚ (Ideal.Quotient.mk p ↑s) != 0 := by
    rwa [RingEquiv.map_ne_zero_iff]
  rw [RingEquiv.symm_apply_eq]; rw [← mul_left_inj' h₂]; rw [map_mul]; rw [mul_assoc]; rw [← map_mul]; rw [inv_mul_cancel₀ h₁]; rw [map_one]; rw [mul_one]; rw [equivQuotMaximalIdeal_apply_mk]; rw [← map_mul]; rw [mk'_spec]; rw [Ideal.Quotient.mk_algebraMap]; rw [equivQuotMaximalIdeal_apply_mk]; rw [Ideal.Quotient.mk_algebraMap]

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism `R ⧸ p ^ n ≃ₐ[R] Rₚ ⧸ maximalIdeal Rₚ ^ n`, where `Rₚ` satisfies
`IsLocalization.AtPrime Rₚ p`. -/
noncomputable
/--
Definition of `equivQuotMaximalIdealPow` / `equivQuotMaximalIdealPow` 的定义

English:
definition equivQuotMaximalIdealPow
  signature: (n : Nat)
  body: by
  refine AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) ?_) ?_ ?_ ?_
  · simp_rw [ofId_apply, ← RingHom.mem_ker, ← SetLike.le_def]
    rw [← Quotient.mk_comp_algebraMap]; rw [← RingHom.comap_ker]; rw [mk_ker]; rw [← under_def]; rw [under_maximalIdeal_pow p]
  · refine Ideal.Quotient

中文:
定义 equivQuotMaximalIdealPow
  签名: (n : 自然数)
  定义体: by
  refine AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) ?_) ?_ ?_ ?_
  · simp_rw [ofId_apply, ← RingHom.mem_ker, ← SetLike.le_def]
    rw [← Quotient.mk_comp_algebraMap]; rw [← RingHom.comap_ker]; rw [mk_ker]; rw [← under_def]; rw [under_maximalIdeal_pow p]
  · refine Ideal.Quotient

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, Algebra, Algebra.ofId, Ideal.Quotient.isUnit_mk_pow_of_notMem, Ideal.Quotient.lift, Ideal.Quotient.mk, IsLocalization, IsLocalization.liftAlgHom, Quotient, Quotient.mk_comp_algebraMap, RingHom, RingHom.comap_ker, RingHom.mem_ker, SetLike, SetLike.le_def, comap_ker, isUnit_mk_pow_of_notMem, le_def, liftAlgHom
-/
def equivQuotMaximalIdealPow (n : Nat) : (R ⧸ p ^ n) ≃ₐ[R] Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ n := by
  refine AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) ?_) ?_ ?_ ?_
  · simp_rw [ofId_apply, ← RingHom.mem_ker, ← SetLike.le_def]
    rw [← Quotient.mk_comp_algebraMap]; rw [← RingHom.comap_ker]; rw [mk_ker]; rw [← under_def]; rw [under_maximalIdeal_pow p]
  · refine Ideal.Quotient.liftₐ _
      (IsLocalization.liftAlgHom (f := Ideal.Quotient.mkₐ R (p ^ n)) fun (u : p.primeCompl) =>
Ideal.Quotient.isUnit_mk_pow_of_notMem _ mem_primeCompl_iff.mp u.prop) fun x hx => ?_
    obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    rw [IsLocalization.mk'_mem_iff]; rw [← Ideal.mem_under]; rw [under_maximalIdeal_pow p] at hx
    simpa [lift_mk', Quotient.eq_zero_iff_mem] using hx
  · rw [← AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective _ _)]
    exact IsLocalization.algHom_ext (W := p.primeCompl) (A := R) (by ext)
  · rw [← AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective _ _)]
    ext

@[simp]
/--
theorem `equivQuotMaximalIdealPow_apply_mk` / 定理 `equivQuotMaximalIdealPow_apply_mk`

English:
theorem equivQuotMaximalIdealPow_apply_mk
  given: (n : Nat) (x : R)
  proof: rfl

中文:
定理 equivQuotMaximalIdealPow_apply_mk
  条件: (n : 自然数) (x : R)
  证明: rfl
-/
theorem equivQuotMaximalIdealPow_apply_mk (n : Nat) (x : R) :
    equivQuotMaximalIdealPow p Rₚ n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap R Rₚ x) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `equivQuotMaximalIdealPow_symm_apply_mk_mul` / 定理 `equivQuotMaximalIdealPow_symm_apply_mk_mul`

English:
theorem equivQuotMaximalIdealPow_symm_apply_mk_mul
  given: (n : Nat) (x : R) (s : p.primeCompl)
  proof: by
  simp [equivQuotMaximalIdealPow, lift_mk', IsUnit.liftRight_apply, mul_assoc]

中文:
定理 equivQuotMaximalIdealPow_symm_apply_mk_mul
  条件: (n : 自然数) (x : R) (s : p.primeCompl)
  证明: by
  simp [equivQuotMaximalIdealPow, lift_mk', IsUnit.liftRight_apply, mul_assoc]

Depends on / 依赖: IsUnit, IsUnit.liftRight_apply, equivQuotMaximalIdealPow, liftRight_apply, lift_mk, mul_assoc
-/
theorem equivQuotMaximalIdealPow_symm_apply_mk_mul (n : Nat) (x : R) (s : p.primeCompl) :
    (equivQuotMaximalIdealPow p Rₚ n).symm (Ideal.Quotient.mk _ (IsLocalization.mk' Rₚ x s)) *
      Ideal.Quotient.mk (p ^ n) s = Ideal.Quotient.mk (p ^ n) x := by
  simp [equivQuotMaximalIdealPow, lift_mk', IsUnit.liftRight_apply, mul_assoc]

variable {Sₚ : Type*} [CommRing S] [Algebra R S] [CommRing Sₚ] [Algebra S Sₚ] [Algebra R Sₚ]
variable [Algebra Rₚ Sₚ] [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
variable [IsScalarTower R S Sₚ]

local notation "pS" => Ideal.map (algebraMap R S) p
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ)

/--
lemma `under_map_eq_map` / 引理 `under_map_eq_map`

English:
lemma under_map_eq_map
  statement: (Ideal.map (algebraMap R Sₚ) p).under S = pS
  proof: by
  rw [IsScalarTower.algebraMap_eq R S Sₚ]; rw [← Ideal.map_map]; rw [eq_comm]
  apply Ideal.le_comap_map.antisymm
  intro x hx
  obtain ⟨α, hα, hαx⟩ : exists α ∉ p, α • x in pS := by
    have ⟨⟨y, s⟩, hy⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl)

中文:
引理 under_map_eq_map
  结论: (Ideal.map (algebraMap R Sₚ) p).under S = pS
  证明: by
  rw [IsScalarTower.algebraMap_eq R S Sₚ]; rw [← Ideal.map_map]; rw [eq_comm]
  apply Ideal.le_comap_map.antisymm
  intro x hx
  obtain ⟨α, hα, hαx⟩ : exists α ∉ p, α • x in pS := by
    have ⟨⟨y, s⟩, hy⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl)

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Algebra.smul_def, Ideal.le_comap_map.antisymm, Ideal.map_map, IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.mem_map_algebraMap_iff, IsScalarTower, IsScalarTower.algebraMap_eq, algebraMapSubmonoid, algebraMap_eq, antisymm, eq_comm, eq_iff_exists, le_comap_map, map_map, map_mul, mem_map_algebraMap_iff, p.primeCompl
-/
lemma under_map_eq_map : (Ideal.map (algebraMap R Sₚ) p).under S = pS := by
  rw [IsScalarTower.algebraMap_eq R S Sₚ]; rw [← Ideal.map_map]; rw [eq_comm]
  apply Ideal.le_comap_map.antisymm
  intro x hx
  obtain ⟨α, hα, hαx⟩ : exists α ∉ p, α • x in pS := by
    have ⟨⟨y, s⟩, hy⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ).mp hx
    rw [← map_mul]; rw [IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S p.primeCompl)] at hy
    obtain ⟨c, hc⟩ := hy
    obtain ⟨α, hα, e⟩ := (c * s).prop
    refine ⟨α, hα, ?_⟩
    rw [Algebra.smul_def]; rw [e]; rw [Submonoid.coe_mul]; rw [mul_assoc]; rw [mul_comm _ x]; rw [hc]
    exact Ideal.mul_mem_left _ _ y.prop
  obtain ⟨β, γ, hγ, hβ⟩ : exists β γ, γ in p ∧ β * α = 1 + γ := by
    obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
    refine ⟨β, β * α - 1, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
        map_mul, hβ, inv_mul_cancel₀, sub_self]
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [add_sub_cancel]
  have := Ideal.mul_mem_left _ (algebraMap _ _ β) hαx
  rw [← Algebra.smul_def]; rw [smul_smul]; rw [hβ]; rw [add_smul]; rw [one_smul] at this
  refine (Submodule.add_mem_iff_left pS ?_).mp this
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_right
  exact Ideal.mem_map_of_mem _ hγ

@[deprecated (since := "2026-04-09")] alias comap_map_eq_map := under_map_eq_map

variable [IsScalarTower R Rₚ Sₚ]

variable (S Sₚ) in
/--
Definition of `equivQuotientMapMaximalIdeal` / `equivQuotientMapMaximalIdeal` 的定义

English:
definition equivQuotientMapMaximalIdeal
  signature: : S ⧸ pS ≃+* Sₚ ⧸ pSₚ
  body: by
  haveI h : pSₚ = Ideal.map (algebraMap S Sₚ) pS := by
    rw [← map_eq_maximalIdeal p]; rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMa

中文:
定义 equivQuotientMapMaximalIdeal
  签名: : S ⧸ pS ≃+* Sₚ ⧸ pSₚ
  定义体: by
  haveI h : pSₚ = Ideal.map (algebraMap S Sₚ) pS := by
    rw [← map_eq_maximalIdeal p]; rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMa

Depends on / 依赖: Ideal.Quotient.algebraMap_eq, Ideal.map, Ideal.map_map, Ideal.mk_ker, Ideal.quotEquivOfEq, IsScalarTower, IsScalarTower.algebraMap_eq, Quotient, RingHom, RingHom.comap_ker, RingHom.quotientKerEquivOfSurjective, algebraMap, algebraMap_eq, comap_ker, map_eq_maximalIdeal, map_map, mk_ker, quotEquivOfEq, quotientKerEquivOfSurjective, under_def
-/
noncomputable def equivQuotientMapMaximalIdeal : S ⧸ pS ≃+* Sₚ ⧸ pSₚ := by
  haveI h : pSₚ = Ideal.map (algebraMap S Sₚ) pS := by
    rw [← map_eq_maximalIdeal p]; rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ pSₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq S Sₚ, Ideal.Quotient.algebraMap_eq, ← RingHom.comap_ker,
      Ideal.mk_ker, h, Ideal.map_map, ← IsScalarTower.algebraMap_eq, ← under_def, under_map_eq_map]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (Algebra.algebraMapSubmonoid S p.primeCompl) x
    obtain ⟨α, hα : α ∉ p, e⟩ := s.prop
    obtain ⟨β, γ, hγ, hβ⟩ : exists β γ, γ in p ∧ α * β = 1 + γ := by
      obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
      refine ⟨β, α * β - 1, ?_, ?_⟩
      · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
          map_mul, hβ, mul_inv_cancel₀, sub_self]
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      · rw [add_sub_cancel]
    use β • x
    rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ pSₚ)]; rw [Ideal.Quotient.algebraMap_eq]; rw [RingHom.comp_apply]; rw [← sub_eq_zero]; rw [← map_sub]; rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [h]; rw [IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    refine ⟨⟨⟨γ • x, ?_⟩, s⟩, ?_⟩
    · rw [Algebra.smul_def]
      apply Ideal.mul_mem_right
      exact Ideal.mem_map_of_mem _ hγ
    simp only
    rw [mul_comm]; rw [mul_sub]; rw [IsLocalization.mul_mk'_eq_mk'_of_mul]; rw [IsLocalization.mk'_mul_cancel_left]; rw [← map_mul]; rw [← e]; rw [← Algebra.smul_def]; rw [smul_smul]; rw [hβ]; rw [← map_sub]; rw [add_smul]; rw [one_smul]; rw [add_comm x]; rw [add_sub_cancel_right]

end isomorphisms

/--
lemma `map_eq_top_of_not_le` / 引理 `map_eq_top_of_not_le`

English:
lemma map_eq_top_of_not_le
  statement: {I : Ideal R} {p : Ideal R} [p.IsPrime] [IsLocalization.AtPrime S p]
  proof: by
  apply IsLocalization.map_eq_top_of_not_subset p.primeCompl
  simpa [SetLike.le_def, Set.not_subset_iff_exists_mem_notMem] using hle

中文:
引理 map_eq_top_of_not_le
  结论: {I : Ideal R} {p : Ideal R} [p.IsPrime] [IsLocalization.AtPrime S p]
  证明: by
  apply IsLocalization.map_eq_top_of_not_subset p.primeCompl
  simpa [SetLike.le_def, Set.not_subset_iff_exists_mem_notMem] using hle

Depends on / 依赖: IsLocalization, IsLocalization.map_eq_top_of_not_subset, Set.not_subset_iff_exists_mem_notMem, SetLike, SetLike.le_def, le_def, map_eq_top_of_not_subset, not_subset_iff_exists_mem_notMem, p.primeCompl, primeCompl
-/
lemma map_eq_top_of_not_le {I : Ideal R} {p : Ideal R} [p.IsPrime] [IsLocalization.AtPrime S p]
    (hle : ¬ I <= p) : Ideal.map (algebraMap R S) I = ⊤ := by
  apply IsLocalization.map_eq_top_of_not_subset p.primeCompl
  simpa [SetLike.le_def, Set.not_subset_iff_exists_mem_notMem] using hle

end IsLocalization.AtPrime
