/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Fintype.Inv
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.FieldSimp

/-!
# Integral domains

Assorted theorems about integral domains.

## Main theorems

* `isCyclic_of_subgroup_isDomain`: A finite subgroup of the units of an integral domain is cyclic.
* `Fintype.fieldOfDomain`: A finite integral domain is a field.

## Notes

Wedderburn's little theorem, which shows that all finite division rings are actually fields,
is in `Mathlib/RingTheory/LittleWedderburn.lean`.

## Tags

integral domain, finite integral domain, finite field
-/

@[expose] public section

section

open Finset Polynomial Function

section CancelMonoidWithZero

-- There doesn't seem to be a better home for these right now
variable {M : Type*} [MonoidWithZero M] [Finite M]

/--
theorem `mul_right_bijective_of_finite₀` / 定理 `mul_right_bijective_of_finite₀`

English:
theorem mul_right_bijective_of_finite₀
  given: [IsLeftCancelMulZero M] {a : M} (ha : a != 0)
  proof: Finite.injective_iff_bijective.1 mul_right_injective₀ ha

中文:
定理 mul_right_bijective_of_finite₀
  条件: [IsLeftCancelMulZero M] {a : M} (ha : a != 0)
  证明: Finite.injective_iff_bijective.1 mul_right_injective₀ ha

Depends on / 依赖: Finite, Finite.injective_iff_bijective, injective_iff_bijective
-/
theorem mul_right_bijective_of_finite₀ [IsLeftCancelMulZero M] {a : M} (ha : a != 0) :
    Bijective fun b => a * b :=
Finite.injective_iff_bijective.1 mul_right_injective₀ ha

/--
theorem `mul_left_bijective_of_finite₀` / 定理 `mul_left_bijective_of_finite₀`

English:
theorem mul_left_bijective_of_finite₀
  given: [IsRightCancelMulZero M] {a : M} (ha : a != 0)
  proof: Finite.injective_iff_bijective.1 mul_left_injective₀ ha

中文:
定理 mul_left_bijective_of_finite₀
  条件: [IsRightCancelMulZero M] {a : M} (ha : a != 0)
  证明: Finite.injective_iff_bijective.1 mul_left_injective₀ ha

Depends on / 依赖: Finite, Finite.injective_iff_bijective, injective_iff_bijective
-/
theorem mul_left_bijective_of_finite₀ [IsRightCancelMulZero M] {a : M} (ha : a != 0) :
    Bijective fun b => b * a :=
Finite.injective_iff_bijective.1 mul_left_injective₀ ha

/-- Every finite nontrivial cancellative monoid with zero is a group with zero. -/
@[instance_reducible]
/--
Definition of `Fintype.groupWithZeroOfCancel` / `Fintype.groupWithZeroOfCancel` 的定义

English:
definition Fintype.groupWithZeroOfCancel
  signature: (M : Type*) [MonoidWithZero M] [IsLeftCancelMulZero M]
  body: { ‹Nontrivial M›,
    ‹MonoidWithZero M› with
    inv := fun a => if h : a = 0 then 0 else Fintype.bijInv (mul_right_bijective_of_finite₀ h) 1
    mul_inv_cancel := fun a ha => by
      simp only [dif_neg ha]
      exact Fintype.rightInverse_bijInv _ _
    inv_zero := by simp }

中文:
定义 Fintype.groupWithZeroOfCancel
  签名: (M : 类型) [MonoidWithZero M] [IsLeftCancelMulZero M]
  定义体: { ‹Nontrivial M›,
    ‹MonoidWithZero M› with
    inv := fun a => if h : a = 0 then 0 else Fintype.bijInv (mul_right_bijective_of_finite₀ h) 1
    mul_inv_cancel := fun a ha => by
      simp only [dif_neg ha]
      exact Fintype.rightInverse_bijInv _ _
    inv_zero := by simp }

Depends on / 依赖: Fintype, Fintype.bijInv, Fintype.rightInverse_bijInv, MonoidWithZero, Nontrivial, bijInv, dif_neg, inv_zero, mul_inv_cancel, rightInverse_bijInv
-/
def Fintype.groupWithZeroOfCancel (M : Type*) [MonoidWithZero M] [IsLeftCancelMulZero M]
    [DecidableEq M] [Fintype M] [Nontrivial M] : GroupWithZero M :=
  { ‹Nontrivial M›,
    ‹MonoidWithZero M› with
    inv := fun a => if h : a = 0 then 0 else Fintype.bijInv (mul_right_bijective_of_finite₀ h) 1
    mul_inv_cancel := fun a ha => by
      simp only [dif_neg ha]
      exact Fintype.rightInverse_bijInv _ _
    inv_zero := by simp }

/--
theorem `exists_eq_pow_of_mul_eq_pow_of_coprime` / 定理 `exists_eq_pow_of_mul_eq_pow_of_coprime`

English:
theorem exists_eq_pow_of_mul_eq_pow_of_coprime
  statement: {R : Type*} [CommSemiring R]
  proof: by
  refine exists_eq_pow_of_mul_eq_pow (isUnit_of_dvd_one ?_) h
  obtain ⟨x, y, hxy⟩ := cp
  rw [← hxy]
  exact dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
    (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _)

nonrec

中文:
定理 exists_eq_pow_of_mul_eq_pow_of_coprime
  结论: {R : 类型} [CommSemiring R]
  证明: by
  refine exists_eq_pow_of_mul_eq_pow (isUnit_of_dvd_one ?_) h
  obtain ⟨x, y, hxy⟩ := cp
  rw [← hxy]
  exact dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
    (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _)

nonrec

Depends on / 依赖: dvd_add, dvd_mul_of_dvd_right, exists_eq_pow_of_mul_eq_pow, gcd_dvd_left, gcd_dvd_right, isUnit_of_dvd_one
-/
theorem exists_eq_pow_of_mul_eq_pow_of_coprime {R : Type*} [CommSemiring R]
    [GCDMonoid R] [Subsingleton Rˣ] {a b c : R} {n : Nat} (cp : IsCoprime a b) (h : a * b = c ^ n) :
    exists d : R, a = d ^ n := by
  refine exists_eq_pow_of_mul_eq_pow (isUnit_of_dvd_one ?_) h
  obtain ⟨x, y, hxy⟩ := cp
  rw [← hxy]
  exact dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
    (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _)

nonrec
/--
theorem `Finset.exists_eq_pow_of_mul_eq_pow_of_coprime` / 定理 `Finset.exists_eq_pow_of_mul_eq_pow_of_coprime`

English:
theorem Finset.exists_eq_pow_of_mul_eq_pow_of_coprime
  statement: {ι R : Type*} [CommSemiring R]
  proof: by
  classical
    intro i hi
    rw [← insert_erase hi]; rw [prod_insert (notMem_erase i s)] at hprod
    refine
      exists_eq_pow_of_mul_eq_pow_of_coprime
        (IsCoprime.prod_right fun j hj => h i hi j (erase_subset i s hj) fun hij => ?_) hprod
    rw [hij] at hj
    exact (s.notMem_erase _)

中文:
定理 Finset.exists_eq_pow_of_mul_eq_pow_of_coprime
  结论: {ι R : 类型} [CommSemiring R]
  证明: by
  classical
    intro i hi
    rw [← insert_erase hi]; rw [prod_insert (notMem_erase i s)] at hprod
    refine
      exists_eq_pow_of_mul_eq_pow_of_coprime
        (IsCoprime.prod_right fun j hj => h i hi j (erase_subset i s hj) fun hij => ?_) hprod
    rw [hij] at hj
    exact (s.notMem_erase _)

Depends on / 依赖: IsCoprime, IsCoprime.prod_right, classical, erase_subset, exists_eq_pow_of_mul_eq_pow_of_coprime, insert_erase, notMem_erase, prod_insert, prod_right, s.notMem_erase
-/
theorem Finset.exists_eq_pow_of_mul_eq_pow_of_coprime {ι R : Type*} [CommSemiring R]
    [GCDMonoid R] [Subsingleton Rˣ] {n : Nat} {c : R} {s : Finset ι} {f : ι -> R}
    (h : forall i in s, forall j in s, i != j -> IsCoprime (f i) (f j))
    (hprod : ∏ i in s, f i = c ^ n) : forall i in s, exists d : R, f i = d ^ n := by
  classical
    intro i hi
    rw [← insert_erase hi]; rw [prod_insert (notMem_erase i s)] at hprod
    refine
      exists_eq_pow_of_mul_eq_pow_of_coprime
        (IsCoprime.prod_right fun j hj => h i hi j (erase_subset i s hj) fun hij => ?_) hprod
    rw [hij] at hj
    exact (s.notMem_erase _) hj

end CancelMonoidWithZero

variable {R : Type*} {G : Type*}

section Ring

/-- Every finite domain is a division ring. More generally, they are fields; this can be found in
`Mathlib/RingTheory/LittleWedderburn.lean`. -/
@[instance_reducible]
/--
Definition of `Fintype.divisionRingOfIsDomain` / `Fintype.divisionRingOfIsDomain` 的定义

English:
definition Fintype.divisionRingOfIsDomain
  signature: (R : Type*) [Ring R] [IsDomain R] [DecidableEq R] [Fintype R]
  body: (‹Ring R› :) -- this also works without the `( :)`, but it's slightly slow
  __ := Fintype.groupWithZeroOfCancel R
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

中文:
定义 Fintype.divisionRingOfIsDomain
  签名: (R : 类型) [Ring R] [IsDomain R] [DecidableEq R] [Fintype R]
  定义体: (‹Ring R› :) -- this also works without the `( :)`, but it's slightly slow
  __ := Fintype.groupWithZeroOfCancel R
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

Depends on / 依赖: slightly, without
-/
def Fintype.divisionRingOfIsDomain (R : Type*) [Ring R] [IsDomain R] [DecidableEq R] [Fintype R] :
    DivisionRing R where
  __ := (‹Ring R› :) -- this also works without the `( :)`, but it's slightly slow
  __ := Fintype.groupWithZeroOfCancel R
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- Every finite commutative domain is a field. More generally, commutativity is not required: this
can be found in `Mathlib/RingTheory/LittleWedderburn.lean`. -/
@[instance_reducible]
/--
Definition of `Fintype.fieldOfDomain` / `Fintype.fieldOfDomain` 的定义

English:
definition Fintype.fieldOfDomain
  signature: (R) [CommRing R] [IsDomain R] [DecidableEq R] [Fintype R]
  body: { Fintype.divisionRingOfIsDomain R, ‹CommRing R› with }

中文:
定义 Fintype.fieldOfDomain
  签名: (R) [CommRing R] [IsDomain R] [DecidableEq R] [Fintype R]
  定义体: { Fintype.divisionRingOfIsDomain R, ‹CommRing R› with }

Depends on / 依赖: CommRing, Fintype, Fintype.divisionRingOfIsDomain, divisionRingOfIsDomain
-/
def Fintype.fieldOfDomain (R) [CommRing R] [IsDomain R] [DecidableEq R] [Fintype R] : Field R :=
  { Fintype.divisionRingOfIsDomain R, ‹CommRing R› with }

/--
theorem `Finite.isField_of_domain` / 定理 `Finite.isField_of_domain`

English:
theorem Finite.isField_of_domain
  given: (R) [CommRing R] [IsDomain R] [Finite R]
  statement: IsField R
  proof: by
  cases nonempty_fintype R
  exact @Field.toIsField R (@Fintype.fieldOfDomain R _ _ (Classical.decEq R) _)

中文:
定理 Finite.isField_of_domain
  条件: (R) [CommRing R] [IsDomain R] [Finite R]
  结论: IsField R
  证明: by
  cases nonempty_fintype R
  exact @Field.toIsField R (@Fintype.fieldOfDomain R _ _ (Classical.decEq R) _)

Depends on / 依赖: Classical, Classical.decEq, Field.toIsField, Fintype, Fintype.fieldOfDomain, fieldOfDomain, nonempty_fintype, toIsField
-/
theorem Finite.isField_of_domain (R) [CommRing R] [IsDomain R] [Finite R] : IsField R := by
  cases nonempty_fintype R
  exact @Field.toIsField R (@Fintype.fieldOfDomain R _ _ (Classical.decEq R) _)

end Ring

variable [CommRing R] [IsDomain R] [Group G]

/--
theorem `card_nthRoots_subgroup_units` / 定理 `card_nthRoots_subgroup_units`

English:
theorem card_nthRoots_subgroup_units
  statement: [Fintype G] [DecidableEq G] (f : G ->* R) (hf : Injective f)
  proof: by
  have : DecidableEq R := Classical.decEq _
  calc
    _ <= #(nthRoots n (f g₀)).toFinset :=
      card_le_card_of_injOn f (by aesop (add safe unfold Set.MapsTo)) hf.injOn
    _ <= _ := (nthRoots n (f g₀)).toFinset_card_le

中文:
定理 card_nthRoots_subgroup_units
  结论: [Fintype G] [DecidableEq G] (f : G ->* R) (hf : Injective f)
  证明: by
  have : DecidableEq R := Classical.decEq _
  calc
    _ <= #(nthRoots n (f g₀)).toFinset :=
      card_le_card_of_injOn f (by aesop (add safe unfold Set.MapsTo)) hf.injOn
    _ <= _ := (nthRoots n (f g₀)).toFinset_card_le

Depends on / 依赖: Classical, Classical.decEq, DecidableEq, MapsTo, Set.MapsTo, card_le_card_of_injOn, hf.injOn, nthRoots, toFinset, toFinset_card_le
-/
theorem card_nthRoots_subgroup_units [Fintype G] [DecidableEq G] (f : G ->* R) (hf : Injective f)
    {n : Nat} (hn : 0 < n) (g₀ : G) :
    #{g | g ^ n = g₀} <= Multiset.card (nthRoots n (f g₀)) := by
  have : DecidableEq R := Classical.decEq _
  calc
    _ <= #(nthRoots n (f g₀)).toFinset :=
      card_le_card_of_injOn f (by aesop (add safe unfold Set.MapsTo)) hf.injOn
    _ <= _ := (nthRoots n (f g₀)).toFinset_card_le

/--
theorem `isCyclic_of_injective_ringHom` / 定理 `isCyclic_of_injective_ringHom`

English:
theorem isCyclic_of_injective_ringHom
  given: [Finite G] (f : G ->* R) (hf : Injective f)
  statement: IsCyclic G
  proof: by
  classical
    cases nonempty_fintype G
    apply isCyclic_of_card_pow_eq_one_le
    intro n hn
    exact le_trans (card_nthRoots_subgroup_units f hf hn 1) (card_nthRoots n (f 1))

@[deprecated (since := "2026-03-04")]
alias isCyclic_of_subgroup_isDomain := isCyclic_of_injective_ringHom

中文:
定理 isCyclic_of_injective_ringHom
  条件: [Finite G] (f : G ->* R) (hf : Injective f)
  结论: IsCyclic G
  证明: by
  classical
    cases nonempty_fintype G
    apply isCyclic_of_card_pow_eq_one_le
    intro n hn
    exact le_trans (card_nthRoots_subgroup_units f hf hn 1) (card_nthRoots n (f 1))

@[deprecated (since := "2026-03-04")]
alias isCyclic_of_subgroup_isDomain := isCyclic_of_injective_ringHom

Depends on / 依赖: card_nthRoots, card_nthRoots_subgroup_units, classical, isCyclic_of_card_pow_eq_one_le, le_trans, nonempty_fintype
-/
theorem isCyclic_of_injective_ringHom [Finite G] (f : G ->* R) (hf : Injective f) : IsCyclic G := by
  classical
    cases nonempty_fintype G
    apply isCyclic_of_card_pow_eq_one_le
    intro n hn
    exact le_trans (card_nthRoots_subgroup_units f hf hn 1) (card_nthRoots n (f 1))

@[deprecated (since := "2026-03-04")]
alias isCyclic_of_subgroup_isDomain := isCyclic_of_injective_ringHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: Rˣ] : IsCyclic Rˣ
  body: isCyclic_of_injective_ringHom (Units.coeHom R) Units.val_injective

中文:
实例 [Finite
  签名: Rˣ] : IsCyclic Rˣ
  定义体: isCyclic_of_injective_ringHom (Units.coeHom R) Units.val_injective

Depends on / 依赖: Units.coeHom, Units.val_injective, coeHom, isCyclic_of_injective_ringHom, val_injective
-/
instance [Finite Rˣ] : IsCyclic Rˣ :=
  isCyclic_of_injective_ringHom (Units.coeHom R) Units.val_injective

section

variable (S : Subgroup Rˣ) [Finite S]

/--
Instance `isCyclic_subgroup_units` / 实例 `isCyclic_subgroup_units`

English:
instance isCyclic_subgroup_units
  signature: : IsCyclic S
  body: isCyclic_of_injective_ringHom { toFun s := (s.val : R), map_one' := rfl, map_mul' := by simp }
    (Units.val_injective.comp Subtype.val_injective)

@[deprecated (since := "2026-03-03")] alias subgroup_units_cyclic := isCyclic_subgroup_units

中文:
实例 isCyclic_subgroup_units
  签名: : IsCyclic S
  定义体: isCyclic_of_injective_ringHom { toFun s := (s.val : R), map_one' := rfl, map_mul' := by simp }
    (Units.val_injective.comp Subtype.val_injective)

@[deprecated (since := "2026-03-03")] alias subgroup_units_cyclic := isCyclic_subgroup_units

Depends on / 依赖: Subtype, Subtype.val_injective, Units.val_injective.comp, isCyclic_of_injective_ringHom, map_mul, map_one, s.val, val_injective
-/
instance isCyclic_subgroup_units : IsCyclic S :=
  isCyclic_of_injective_ringHom { toFun s := (s.val : R), map_one' := rfl, map_mul' := by simp }
    (Units.val_injective.comp Subtype.val_injective)

@[deprecated (since := "2026-03-03")] alias subgroup_units_cyclic := isCyclic_subgroup_units

end

-- TODO: find a better home (Mathlib.Algebra.Polynomial.PartialFractions)?
section EuclideanDivision

namespace Polynomial

variable (K : Type*) [Field K] [Algebra R[X] K] [IsFractionRing R[X] K]

/--
theorem `div_eq_quo_add_rem_div` / 定理 `div_eq_quo_add_rem_div`

English:
theorem div_eq_quo_add_rem_div
  given: (f : R[X]) {g : R[X]} (hg : g.Monic)
  proof: by
  refine ⟨f /ₘ g, f %ₘ g, ?_, ?_⟩
  · exact degree_modByMonic_lt _ hg
  · have hg' : algebraMap R[X] K g != 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R[X] K)).mpr (Monic.ne_zero hg)
    field_simp
    rw [add_comm]; rw [← map_mul]; rw [← map_add]; rw [modByMonic_add_div]

中文:
定理 div_eq_quo_add_rem_div
  条件: (f : R[X]) {g : R[X]} (hg : g.Monic)
  证明: by
  refine ⟨f /ₘ g, f %ₘ g, ?_, ?_⟩
  · exact degree_modByMonic_lt _ hg
  · have hg' : algebraMap R[X] K g != 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R[X] K)).mpr (Monic.ne_zero hg)
    field_simp
    rw [add_comm]; rw [← map_mul]; rw [← map_add]; rw [modByMonic_add_div]

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, Monic.ne_zero, add_comm, algebraMap, degree_modByMonic_lt, injective, map_add, map_mul, map_ne_zero_iff, modByMonic_add_div, ne_zero
-/
theorem div_eq_quo_add_rem_div (f : R[X]) {g : R[X]} (hg : g.Monic) :
    exists q r : R[X], r.degree < g.degree ∧
      (algebraMap R[X] K f) / (algebraMap R[X] K g) =
        algebraMap R[X] K q + (algebraMap R[X] K r) / (algebraMap R[X] K g) := by
  refine ⟨f /ₘ g, f %ₘ g, ?_, ?_⟩
  · exact degree_modByMonic_lt _ hg
  · have hg' : algebraMap R[X] K g != 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R[X] K)).mpr (Monic.ne_zero hg)
    field_simp
    rw [add_comm]; rw [← map_mul]; rw [← map_add]; rw [modByMonic_add_div]

end Polynomial

end EuclideanDivision

variable [Fintype G]

/--
theorem `sum_hom_units_eq_zero` / 定理 `sum_hom_units_eq_zero`

English:
theorem sum_hom_units_eq_zero
  given: (f : G ->* R) (hf : f != 1)
  statement: ∑ g : G, f g = 0
  proof: by
  classical
    obtain ⟨x, hx⟩ := IsCyclic.exists_monoid_generator (α := MonoidHom.range f.toHomUnits)
    have hx1 : (x.1 : R) - 1 != 0 := by
      rw [sub_ne_zero]
      contrapose hf
      ext g
      obtain ⟨n, hn⟩ := hx ⟨f.toHomUnits g, g, rfl⟩
      simpa [hf, Subtype.ext_iff, Units.ext_iff

中文:
定理 sum_hom_units_eq_zero
  条件: (f : G ->* R) (hf : f != 1)
  结论: ∑ g : G, f g = 0
  证明: by
  classical
    obtain ⟨x, hx⟩ := IsCyclic.exists_monoid_generator (α := MonoidHom.range f.toHomUnits)
    have hx1 : (x.1 : R) - 1 != 0 := by
      rw [sub_ne_zero]
      contrapose hf
      ext g
      obtain ⟨n, hn⟩ := hx ⟨f.toHomUnits g, g, rfl⟩
      simpa [hf, Subtype.ext_iff, Units.ext_iff

Depends on / 依赖: IsCyclic, IsCyclic.exists_monoid_generator, MonoidHom, MonoidHom.range, Subtype, Subtype.ext_iff, Units.ext_iff, classical, contrapose, exists_monoid_generator, ext_iff, f.toHomUnits, hn.symm, sub_ne_zero, sum_comp, sum_cong, toHomUnits, univ.image
-/
theorem sum_hom_units_eq_zero (f : G ->* R) (hf : f != 1) : ∑ g : G, f g = 0 := by
  classical
    obtain ⟨x, hx⟩ := IsCyclic.exists_monoid_generator (α := MonoidHom.range f.toHomUnits)
    have hx1 : (x.1 : R) - 1 != 0 := by
      rw [sub_ne_zero]
      contrapose hf
      ext g
      obtain ⟨n, hn⟩ := hx ⟨f.toHomUnits g, g, rfl⟩
      simpa [hf, Subtype.ext_iff, Units.ext_iff] using hn.symm
    let c := #{g | f.toHomUnits g = 1}
    calc
      ∑ g : G, f g = ∑ u in univ.image f.toHomUnits, #{g | f.toHomUnits g = u} • (u : R) :=
        sum_comp ((↑) : Rˣ -> R) f.toHomUnits
      _ = ∑ u in univ.image f.toHomUnits, c • (u : R) :=
        (sum_congr rfl fun u hu => congr_arg₂ _ ?_ rfl)
      -- remaining goal 1, proven below
      _ = ∑ b : MonoidHom.range f.toHomUnits, c • (b.1 : R) :=
        (Finset.sum_subtype _ (by simp) _)
      _ = c • ∑ b : MonoidHom.range f.toHomUnits, (b.1 : R) := smul_sum.symm
      _ = c • 0 := congr_arg₂ _ rfl ?_
      -- remaining goal 2, proven below
      _ = 0 := smul_zero _
    · -- remaining goal 1
      apply MonoidHom.card_fiber_eq_of_mem_range f.toHomUnits
      · simpa only [mem_image, mem_univ, true_and, Set.mem_range] using hu
      · exact ⟨1, f.toHomUnits.map_one⟩
    -- remaining goal 2
    calc
      (∑ b : MonoidHom.range f.toHomUnits, (b.1 : R))
        = ∑ n in range (orderOf x), (x.1 : R) ^ n :=
Eq.symm
          sum_nbij (x ^ ·) (by simp)
            (by simpa using pow_injOn_Iio_orderOf)
            (fun b _ => let ⟨n, hn⟩ := hx b
              ⟨n % orderOf x, mem_range.2 (Nat.mod_lt _ (orderOf_pos _)), by simp [hn]⟩)
            (by simp)
      _ = 0 := ?_
    rw [← mul_left_inj' hx1]; rw [zero_mul]; rw [geom_sum_mul]
    norm_cast
    simp [pow_orderOf_eq_one]

/--
theorem `sum_hom_units` / 定理 `sum_hom_units`

English:
theorem sum_hom_units
  given: (f : G ->* R) [Decidable (f = 1)]
  proof: by
  split_ifs with h
  · simp [h]
  · rw [Nat.cast_zero]
    exact sum_hom_units_eq_zero f h

中文:
定理 sum_hom_units
  条件: (f : G ->* R) [Decidable (f = 1)]
  证明: by
  split_ifs with h
  · simp [h]
  · rw [Nat.cast_zero]
    exact sum_hom_units_eq_zero f h

Depends on / 依赖: Nat.cast_zero, cast_zero, split_ifs, sum_hom_units_eq_zero
-/
theorem sum_hom_units (f : G ->* R) [Decidable (f = 1)] :
    ∑ g : G, f g = if f = 1 then Fintype.card G else 0 := by
  split_ifs with h
  · simp [h]
  · rw [Nat.cast_zero]
    exact sum_hom_units_eq_zero f h

end
