/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Squarefree elements of monoids

An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

Results about squarefree natural numbers are proved in `Data.Nat.Squarefree`.

## Main Definitions
- `Squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
- `multiplicity.squarefree_iff_emultiplicity_le_one`: `x` is `Squarefree` iff for every `y`, either
  `emultiplicity y x ≤ 1` or `IsUnit y`.
- `UniqueFactorizationMonoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
  factorization monoid is squarefree iff `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/

@[expose] public section


variable {R : Type*}

/--
Definition of `Squarefree` / `Squarefree` 的定义

English:
definition Squarefree
  signature: [Monoid R] (r : R)
  body: forall x : R, x * x ∣ r -> IsUnit x

中文:
定义 Squarefree
  签名: [Monoid R] (r : R)
  定义体: forall x : R, x * x ∣ r -> IsUnit x

Depends on / 依赖: IsUnit
-/
def Squarefree [Monoid R] (r : R) : Prop :=
  forall x : R, x * x ∣ r -> IsUnit x

/--
theorem `IsRelPrime.of_squarefree_mul` / 定理 `IsRelPrime.of_squarefree_mul`

English:
theorem IsRelPrime.of_squarefree_mul
  given: [CommMonoid R] {m n : R} (h : Squarefree (m * n))
  proof: fun c hca hcb => h c (mul_dvd_mul hca hcb)

@[simp]

中文:
定理 IsRelPrime.of_squarefree_mul
  条件: [CommMonoid R] {m n : R} (h : Squarefree (m * n))
  证明: fun c hca hcb => h c (mul_dvd_mul hca hcb)

@[simp]

Depends on / 依赖: mul_dvd_mul
-/
theorem IsRelPrime.of_squarefree_mul [CommMonoid R] {m n : R} (h : Squarefree (m * n)) :
    IsRelPrime m n := fun c hca hcb => h c (mul_dvd_mul hca hcb)

@[simp]
/--
theorem `IsUnit.squarefree` / 定理 `IsUnit.squarefree`

English:
theorem IsUnit.squarefree
  given: [CommMonoid R] {x : R} (h : IsUnit x)
  statement: Squarefree x
  proof: fun _ hdvd =>
  isUnit_of_mul_isUnit_left (isUnit_of_dvd_unit hdvd h)

中文:
定理 IsUnit.squarefree
  条件: [CommMonoid R] {x : R} (h : IsUnit x)
  结论: Squarefree x
  证明: fun _ hdvd =>
  isUnit_of_mul_isUnit_left (isUnit_of_dvd_unit hdvd h)
-/
theorem IsUnit.squarefree [CommMonoid R] {x : R} (h : IsUnit x) : Squarefree x := fun _ hdvd =>
  isUnit_of_mul_isUnit_left (isUnit_of_dvd_unit hdvd h)

/--
theorem `squarefree_one` / 定理 `squarefree_one`

English:
theorem squarefree_one
  given: [CommMonoid R]
  statement: Squarefree (1 : R)
  proof: isUnit_one.squarefree

@[simp]

中文:
定理 squarefree_one
  条件: [CommMonoid R]
  结论: Squarefree (1 : R)
  证明: isUnit_one.squarefree

@[simp]

Depends on / 依赖: isUnit_one, isUnit_one.squarefree, squarefree
-/
theorem squarefree_one [CommMonoid R] : Squarefree (1 : R) :=
  isUnit_one.squarefree

@[simp]
/--
theorem `not_squarefree_zero` / 定理 `not_squarefree_zero`

English:
theorem not_squarefree_zero
  given: [MonoidWithZero R] [Nontrivial R]
  statement: ¬Squarefree (0 : R)
  proof: by
  rw [Squarefree]; rw [not_forall]
  exact ⟨0, by simp⟩

中文:
定理 not_squarefree_zero
  条件: [MonoidWithZero R] [Nontrivial R]
  结论: ¬Squarefree (0 : R)
  证明: by
  rw [Squarefree]; rw [not_forall]
  exact ⟨0, by simp⟩

Depends on / 依赖: Squarefree, not_forall
-/
theorem not_squarefree_zero [MonoidWithZero R] [Nontrivial R] : ¬Squarefree (0 : R) := by
  rw [Squarefree]; rw [not_forall]
  exact ⟨0, by simp⟩

/--
theorem `Squarefree.ne_zero` / 定理 `Squarefree.ne_zero`

English:
theorem Squarefree.ne_zero
  given: [MonoidWithZero R] [Nontrivial R] {m : R} (hm : Squarefree (m : R))
  proof: by
  rintro rfl
  exact not_squarefree_zero hm

@[simp]

中文:
定理 Squarefree.ne_zero
  条件: [MonoidWithZero R] [Nontrivial R] {m : R} (hm : Squarefree (m : R))
  证明: by
  rintro rfl
  exact not_squarefree_zero hm

@[simp]

Depends on / 依赖: not_squarefree_zero
-/
theorem Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R] {m : R} (hm : Squarefree (m : R)) :
    m != 0 := by
  rintro rfl
  exact not_squarefree_zero hm

@[simp]
/--
theorem `Irreducible.squarefree` / 定理 `Irreducible.squarefree`

English:
theorem Irreducible.squarefree
  given: [CommMonoid R] {x : R} (h : Irreducible x)
  statement: Squarefree x
  proof: by
  rintro y ⟨z, hz⟩
  rw [mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact hu
  · apply isUnit_of_mul_isUnit_left hu

@[simp]

中文:
定理 Irreducible.squarefree
  条件: [CommMonoid R] {x : R} (h : Irreducible x)
  结论: Squarefree x
  证明: by
  rintro y ⟨z, hz⟩
  rw [mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact hu
  · apply isUnit_of_mul_isUnit_left hu

@[simp]

Depends on / 依赖: h.isUnit_or_isUnit, isUnit_of_mul_isUnit_left, isUnit_or_isUnit, mul_assoc
-/
theorem Irreducible.squarefree [CommMonoid R] {x : R} (h : Irreducible x) : Squarefree x := by
  rintro y ⟨z, hz⟩
  rw [mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact hu
  · apply isUnit_of_mul_isUnit_left hu

@[simp]
/--
theorem `Prime.squarefree` / 定理 `Prime.squarefree`

English:
theorem Prime.squarefree
  given: [CommMonoidWithZero R] [IsCancelMulZero R] {x : R} (h : Prime x)
  proof: h.irreducible.squarefree

中文:
定理 Prime.squarefree
  条件: [CommMonoidWithZero R] [IsCancelMulZero R] {x : R} (h : Prime x)
  证明: h.irreducible.squarefree

Depends on / 依赖: h.irreducible.squarefree, irreducible, squarefree
-/
theorem Prime.squarefree [CommMonoidWithZero R] [IsCancelMulZero R] {x : R} (h : Prime x) :
    Squarefree x :=
  h.irreducible.squarefree

/--
theorem `Squarefree.of_mul_left` / 定理 `Squarefree.of_mul_left`

English:
theorem Squarefree.of_mul_left
  given: [Monoid R] {m n : R} (hmn : Squarefree (m * n))
  statement: Squarefree m
  proof: fun p hp => hmn p (dvd_mul_of_dvd_left hp n)

中文:
定理 Squarefree.of_mul_left
  条件: [Monoid R] {m n : R} (hmn : Squarefree (m * n))
  结论: Squarefree m
  证明: fun p hp => hmn p (dvd_mul_of_dvd_left hp n)

Depends on / 依赖: dvd_mul_of_dvd_left
-/
theorem Squarefree.of_mul_left [Monoid R] {m n : R} (hmn : Squarefree (m * n)) : Squarefree m :=
  fun p hp => hmn p (dvd_mul_of_dvd_left hp n)

/--
theorem `Squarefree.of_mul_right` / 定理 `Squarefree.of_mul_right`

English:
theorem Squarefree.of_mul_right
  given: [CommMonoid R] {m n : R} (hmn : Squarefree (m * n))
  proof: fun p hp => hmn p (dvd_mul_of_dvd_right hp m)

中文:
定理 Squarefree.of_mul_right
  条件: [CommMonoid R] {m n : R} (hmn : Squarefree (m * n))
  证明: fun p hp => hmn p (dvd_mul_of_dvd_right hp m)

Depends on / 依赖: dvd_mul_of_dvd_right
-/
theorem Squarefree.of_mul_right [CommMonoid R] {m n : R} (hmn : Squarefree (m * n)) :
    Squarefree n := fun p hp => hmn p (dvd_mul_of_dvd_right hp m)

/--
theorem `Squarefree.squarefree_of_dvd` / 定理 `Squarefree.squarefree_of_dvd`

English:
theorem Squarefree.squarefree_of_dvd
  given: [Monoid R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y)
  proof: fun _ h => hsq _ (h.trans hdvd)

中文:
定理 Squarefree.squarefree_of_dvd
  条件: [Monoid R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y)
  证明: fun _ h => hsq _ (h.trans hdvd)

Depends on / 依赖: h.trans
-/
theorem Squarefree.squarefree_of_dvd [Monoid R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y) :
    Squarefree x := fun _ h => hsq _ (h.trans hdvd)

/--
theorem `Associated.squarefree_iff` / 定理 `Associated.squarefree_iff`

English:
theorem Associated.squarefree_iff
  given: [Monoid R] {x y : R} (h : Associated x y)
  proof: ⟨fun hx => hx.squarefree_of_dvd h.dvd', fun hy => hy.squarefree_of_dvd h.dvd⟩

中文:
定理 Associated.squarefree_iff
  条件: [Monoid R] {x y : R} (h : Associated x y)
  证明: ⟨fun hx => hx.squarefree_of_dvd h.dvd', fun hy => hy.squarefree_of_dvd h.dvd⟩

Depends on / 依赖: h.dvd, hx.squarefree_of_dvd, hy.squarefree_of_dvd, squarefree_of_dvd
-/
theorem Associated.squarefree_iff [Monoid R] {x y : R} (h : Associated x y) :
    Squarefree x ↔ Squarefree y :=
  ⟨fun hx => hx.squarefree_of_dvd h.dvd', fun hy => hy.squarefree_of_dvd h.dvd⟩

/--
theorem `Squarefree.eq_zero_or_one_of_pow_of_not_isUnit` / 定理 `Squarefree.eq_zero_or_one_of_pow_of_not_isUnit`

English:
theorem Squarefree.eq_zero_or_one_of_pow_of_not_isUnit
  statement: [Monoid R] {x : R} {n : Nat}
  proof: by
  contrapose! h'
  replace h' : 2 <= n := by lia
  have : x * x ∣ x ^ n := by rw [← sq]; exact pow_dvd_pow x h'
  exact h.squarefree_of_dvd this x (refl _)

中文:
定理 Squarefree.eq_zero_or_one_of_pow_of_not_isUnit
  结论: [Monoid R] {x : R} {n : 自然数}
  证明: by
  contrapose! h'
  replace h' : 2 <= n := by lia
  have : x * x ∣ x ^ n := by rw [← sq]; exact pow_dvd_pow x h'
  exact h.squarefree_of_dvd this x (refl _)

Depends on / 依赖: contrapose, h.squarefree_of_dvd, pow_dvd_pow, replace, squarefree_of_dvd
-/
theorem Squarefree.eq_zero_or_one_of_pow_of_not_isUnit [Monoid R] {x : R} {n : Nat}
    (h : Squarefree (x ^ n)) (h' : ¬ IsUnit x) :
    n = 0 ∨ n = 1 := by
  contrapose! h'
  replace h' : 2 <= n := by lia
  have : x * x ∣ x ^ n := by rw [← sq]; exact pow_dvd_pow x h'
  exact h.squarefree_of_dvd this x (refl _)

/--
theorem `Squarefree.pow_dvd_of_pow_dvd` / 定理 `Squarefree.pow_dvd_of_pow_dvd`

English:
theorem Squarefree.pow_dvd_of_pow_dvd
  statement: [Monoid R] {x y : R} {n : Nat}
  proof: by
  by_cases hu : IsUnit x
  · exact (hu.pow n).dvd
  · rcases (hx.squarefree_of_dvd h).eq_zero_or_one_of_pow_of_not_isUnit hu with rfl | rfl <;> simp

中文:
定理 Squarefree.pow_dvd_of_pow_dvd
  结论: [Monoid R] {x y : R} {n : 自然数}
  证明: by
  by_cases hu : IsUnit x
  · exact (hu.pow n).dvd
  · rcases (hx.squarefree_of_dvd h).eq_zero_or_one_of_pow_of_not_isUnit hu with rfl | rfl <;> simp

Depends on / 依赖: IsUnit, eq_zero_or_one_of_pow_of_not_isUnit, hu.pow, hx.squarefree_of_dvd, squarefree_of_dvd
-/
theorem Squarefree.pow_dvd_of_pow_dvd [Monoid R] {x y : R} {n : Nat}
    (hx : Squarefree y) (h : x ^ n ∣ y) : x ^ n ∣ x := by
  by_cases hu : IsUnit x
  · exact (hu.pow n).dvd
  · rcases (hx.squarefree_of_dvd h).eq_zero_or_one_of_pow_of_not_isUnit hu with rfl | rfl <;> simp

section SquarefreeGcdOfSquarefree

variable {α : Type*} [CommMonoidWithZero α] [GCDMonoid α]

/--
theorem `Squarefree.gcd_right` / 定理 `Squarefree.gcd_right`

English:
theorem Squarefree.gcd_right
  given: (a : α) {b : α} (hb : Squarefree b)
  statement: Squarefree (gcd a b)
  proof: hb.squarefree_of_dvd (gcd_dvd_right _ _)

中文:
定理 Squarefree.gcd_right
  条件: (a : α) {b : α} (hb : Squarefree b)
  结论: Squarefree (gcd a b)
  证明: hb.squarefree_of_dvd (gcd_dvd_right _ _)

Depends on / 依赖: gcd_dvd_right, hb.squarefree_of_dvd, squarefree_of_dvd
-/
theorem Squarefree.gcd_right (a : α) {b : α} (hb : Squarefree b) : Squarefree (gcd a b) :=
  hb.squarefree_of_dvd (gcd_dvd_right _ _)

/--
theorem `Squarefree.gcd_left` / 定理 `Squarefree.gcd_left`

English:
theorem Squarefree.gcd_left
  given: {a : α} (b : α) (ha : Squarefree a)
  statement: Squarefree (gcd a b)
  proof: ha.squarefree_of_dvd (gcd_dvd_left _ _)

中文:
定理 Squarefree.gcd_left
  条件: {a : α} (b : α) (ha : Squarefree a)
  结论: Squarefree (gcd a b)
  证明: ha.squarefree_of_dvd (gcd_dvd_left _ _)

Depends on / 依赖: gcd_dvd_left, ha.squarefree_of_dvd, squarefree_of_dvd
-/
theorem Squarefree.gcd_left {a : α} (b : α) (ha : Squarefree a) : Squarefree (gcd a b) :=
  ha.squarefree_of_dvd (gcd_dvd_left _ _)

end SquarefreeGcdOfSquarefree

/--
theorem `squarefree_iff_emultiplicity_le_one` / 定理 `squarefree_iff_emultiplicity_le_one`

English:
theorem squarefree_iff_emultiplicity_le_one
  given: [CommMonoid R] (r : R)
  proof: by
  refine forall_congr' fun a => ?_
  rw [← sq]; rw [pow_dvd_iff_le_emultiplicity]; rw [or_iff_not_imp_left]; rw [not_le]; rw [imp_congr _ Iff.rfl]
  norm_cast
  rw [← one_add_one_eq_two]
  exact Order.add_one_le_iff_of_not_isMax (by simp)

中文:
定理 squarefree_iff_emultiplicity_le_one
  条件: [CommMonoid R] (r : R)
  证明: by
  refine forall_congr' fun a => ?_
  rw [← sq]; rw [pow_dvd_iff_le_emultiplicity]; rw [or_iff_not_imp_left]; rw [not_le]; rw [imp_congr _ Iff.rfl]
  norm_cast
  rw [← one_add_one_eq_two]
  exact Order.add_one_le_iff_of_not_isMax (by simp)

Depends on / 依赖: Iff.rfl, Order.add_one_le_iff_of_not_isMax, add_one_le_iff_of_not_isMax, forall_congr, imp_congr, not_le, one_add_one_eq_two, or_iff_not_imp_left, pow_dvd_iff_le_emultiplicity
-/
theorem squarefree_iff_emultiplicity_le_one [CommMonoid R] (r : R) :
    Squarefree r ↔ forall x : R, emultiplicity x r <= 1 ∨ IsUnit x := by
  refine forall_congr' fun a => ?_
  rw [← sq]; rw [pow_dvd_iff_le_emultiplicity]; rw [or_iff_not_imp_left]; rw [not_le]; rw [imp_congr _ Iff.rfl]
  norm_cast
  rw [← one_add_one_eq_two]
  exact Order.add_one_le_iff_of_not_isMax (by simp)

section Irreducible

variable [CommMonoidWithZero R] [WfDvdMonoid R]

/--
theorem `squarefree_iff_no_irreducibles` / 定理 `squarefree_iff_no_irreducibles`

English:
theorem squarefree_iff_no_irreducibles
  given: {x : R} (hx₀ : x != 0)
  proof: by
  refine ⟨fun h p hp hp' => hp.not_isUnit (h p hp'), fun h d hd => by_contra fun hdu => ?_⟩
  have hd₀ : d != 0 := ne_zero_of_dvd_ne_zero (ne_zero_of_dvd_ne_zero hx₀ hd) (dvd_mul_left d d)
  obtain ⟨p, irr, dvd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd₀
  exact h p irr ((mul_dvd_mul dvd dv

中文:
定理 squarefree_iff_no_irreducibles
  条件: {x : R} (hx₀ : x != 0)
  证明: by
  refine ⟨fun h p hp hp' => hp.not_isUnit (h p hp'), fun h d hd => by_contra fun hdu => ?_⟩
  have hd₀ : d != 0 := ne_zero_of_dvd_ne_zero (ne_zero_of_dvd_ne_zero hx₀ hd) (dvd_mul_left d d)
  obtain ⟨p, irr, dvd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd₀
  exact h p irr ((mul_dvd_mul dvd dv

Depends on / 依赖: WfDvdMonoid, WfDvdMonoid.exists_irreducible_factor, dvd_mul_left, exists_irreducible_factor, hp.not_isUnit, mul_dvd_mul, ne_zero_of_dvd_ne_zero, not_isUnit
-/
theorem squarefree_iff_no_irreducibles {x : R} (hx₀ : x != 0) :
    Squarefree x ↔ forall p, Irreducible p -> ¬ (p * p ∣ x) := by
  refine ⟨fun h p hp hp' => hp.not_isUnit (h p hp'), fun h d hd => by_contra fun hdu => ?_⟩
  have hd₀ : d != 0 := ne_zero_of_dvd_ne_zero (ne_zero_of_dvd_ne_zero hx₀ hd) (dvd_mul_left d d)
  obtain ⟨p, irr, dvd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd₀
  exact h p irr ((mul_dvd_mul dvd dvd).trans hd)

/--
theorem `irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree` / 定理 `irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree`

English:
theorem irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree
  given: (r : R)
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases eq_or_ne r 0 with (rfl | hr)
    · exact .inl (by simpa using h)
    · exact .inr ((squarefree_iff_no_irreducibles hr).mpr h)
  · rintro (⟨rfl, h⟩ | h)
    · simpa using h
    intro x hx t
    exact hx.not_isUnit (h x t)

中文:
定理 irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree
  条件: (r : R)
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rcases eq_or_ne r 0 with (rfl | hr)
    · exact .inl (by simpa using h)
    · exact .inr ((squarefree_iff_no_irreducibles hr).mpr h)
  · rintro (⟨rfl, h⟩ | h)
    · simpa using h
    intro x hx t
    exact hx.not_isUnit (h x t)

Depends on / 依赖: eq_or_ne, hx.not_isUnit, not_isUnit, squarefree_iff_no_irreducibles
-/
theorem irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) :
    (forall x : R, Irreducible x -> ¬x * x ∣ r) ↔ (r = 0 ∧ forall x : R, ¬Irreducible x) ∨ Squarefree r := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases eq_or_ne r 0 with (rfl | hr)
    · exact .inl (by simpa using h)
    · exact .inr ((squarefree_iff_no_irreducibles hr).mpr h)
  · rintro (⟨rfl, h⟩ | h)
    · simpa using h
    intro x hx t
    exact hx.not_isUnit (h x t)

/--
theorem `squarefree_iff_irreducible_sq_not_dvd_of_ne_zero` / 定理 `squarefree_iff_irreducible_sq_not_dvd_of_ne_zero`

English:
theorem squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
  given: {r : R} (hr : r != 0)
  proof: by
  simpa [hr] using (irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree r).symm

中文:
定理 squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
  条件: {r : R} (hr : r != 0)
  证明: by
  simpa [hr] using (irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree r).symm

Depends on / 依赖: irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree
-/
theorem squarefree_iff_irreducible_sq_not_dvd_of_ne_zero {r : R} (hr : r != 0) :
    Squarefree r ↔ forall x : R, Irreducible x -> ¬x * x ∣ r := by
  simpa [hr] using (irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree r).symm

/--
theorem `squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible` / 定理 `squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible`

English:
theorem squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible
  statement: {r : R}
  proof: by
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree]; rw [← not_exists]
  simp only [hr, not_true, false_or, and_false]

中文:
定理 squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible
  结论: {r : R}
  证明: by
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree]; rw [← not_exists]
  simp only [hr, not_true, false_or, and_false]

Depends on / 依赖: and_false, false_or, irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree, not_exists, not_true
-/
theorem squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible {r : R}
    (hr : exists x : R, Irreducible x) : Squarefree r ↔ forall x : R, Irreducible x -> ¬x * x ∣ r := by
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree]; rw [← not_exists]
  simp only [hr, not_true, false_or, and_false]

end Irreducible

section IsRadical

section
variable [CommMonoidWithZero R] [DecompositionMonoid R]

/--
theorem `Squarefree.isRadical` / 定理 `Squarefree.isRadical`

English:
theorem Squarefree.isRadical
  given: {x : R} (hx : Squarefree x)
  statement: IsRadical x
  proof: (isRadical_iff_pow_one_lt 2 one_lt_two).2 fun y hy => by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (sq y ▸ hy)
    exact (IsRelPrime.of_squarefree_mul hx).mul_dvd ha hb

中文:
定理 Squarefree.isRadical
  条件: {x : R} (hx : Squarefree x)
  结论: IsRadical x
  证明: (isRadical_iff_pow_one_lt 2 one_lt_two).2 fun y hy => by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (sq y ▸ hy)
    exact (IsRelPrime.of_squarefree_mul hx).mul_dvd ha hb

Depends on / 依赖: IsRelPrime, IsRelPrime.of_squarefree_mul, exists_dvd_and_dvd_of_dvd_mul, isRadical_iff_pow_one_lt, mul_dvd, of_squarefree_mul, one_lt_two
-/
theorem Squarefree.isRadical {x : R} (hx : Squarefree x) : IsRadical x :=
  (isRadical_iff_pow_one_lt 2 one_lt_two).2 fun y hy => by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (sq y ▸ hy)
    exact (IsRelPrime.of_squarefree_mul hx).mul_dvd ha hb

/--
theorem `Squarefree.dvd_pow_iff_dvd` / 定理 `Squarefree.dvd_pow_iff_dvd`

English:
theorem Squarefree.dvd_pow_iff_dvd
  given: {x y : R} {n : Nat} (hsq : Squarefree x) (h0 : n != 0)
  proof: ⟨hsq.isRadical n y, (·.pow h0)⟩

中文:
定理 Squarefree.dvd_pow_iff_dvd
  条件: {x y : R} {n : 自然数} (hsq : Squarefree x) (h0 : n != 0)
  证明: ⟨hsq.isRadical n y, (·.pow h0)⟩

Depends on / 依赖: hsq.isRadical, isRadical
-/
theorem Squarefree.dvd_pow_iff_dvd {x y : R} {n : Nat} (hsq : Squarefree x) (h0 : n != 0) :
    x ∣ y ^ n ↔ x ∣ y := ⟨hsq.isRadical n y, (·.pow h0)⟩

end

variable [CommMonoidWithZero R] [IsCancelMulZero R] {x y p d : R}

/--
theorem `IsRadical.squarefree` / 定理 `IsRadical.squarefree`

English:
theorem IsRadical.squarefree
  given: (h0 : x != 0) (h : IsRadical x)
  statement: Squarefree x
  proof: by
  rintro z ⟨w, rfl⟩
  specialize h 2 (z * w) ⟨w, by simp_rw [pow_two, mul_left_comm, ← mul_assoc]⟩
  rwa [← one_mul (z * w), mul_assoc, mul_dvd_mul_iff_right, ← isUnit_iff_dvd_one] at h
  rw [mul_assoc]; rw [mul_ne_zero_iff] at h0; exact h0.2

中文:
定理 IsRadical.squarefree
  条件: (h0 : x != 0) (h : IsRadical x)
  结论: Squarefree x
  证明: by
  rintro z ⟨w, rfl⟩
  specialize h 2 (z * w) ⟨w, by simp_rw [pow_two, mul_left_comm, ← mul_assoc]⟩
  rwa [← one_mul (z * w), mul_assoc, mul_dvd_mul_iff_right, ← isUnit_iff_dvd_one] at h
  rw [mul_assoc]; rw [mul_ne_zero_iff] at h0; exact h0.2

Depends on / 依赖: isUnit_iff_dvd_one, mul_assoc, mul_dvd_mul_iff_right, mul_left_comm, mul_ne_zero_iff, one_mul, pow_two, simp_rw, specialize
-/
theorem IsRadical.squarefree (h0 : x != 0) (h : IsRadical x) : Squarefree x := by
  rintro z ⟨w, rfl⟩
  specialize h 2 (z * w) ⟨w, by simp_rw [pow_two, mul_left_comm, ← mul_assoc]⟩
  rwa [← one_mul (z * w), mul_assoc, mul_dvd_mul_iff_right, ← isUnit_iff_dvd_one] at h
  rw [mul_assoc]; rw [mul_ne_zero_iff] at h0; exact h0.2

namespace Squarefree

/--
theorem `pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right` / 定理 `pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right`

English:
theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right
  statement: {k : Nat}
  proof: by
  by_cases hxp : p ∣ x
  · obtain ⟨x', rfl⟩ := hxp
have hx' : ¬ p ∣ x' := fun contra => hp.not_isUnit hx p (mul_dvd_mul_left p contra)
    replace h : p ^ k ∣ x' * y := by
      rw [pow_succ']; rw [mul_assoc] at h
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp h
    exact hp.pow_dvd_of_dvd_mul_

中文:
定理 pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right
  结论: {k : 自然数}
  证明: by
  by_cases hxp : p ∣ x
  · obtain ⟨x', rfl⟩ := hxp
have hx' : ¬ p ∣ x' := fun contra => hp.not_isUnit hx p (mul_dvd_mul_left p contra)
    replace h : p ^ k ∣ x' * y := by
      rw [pow_succ']; rw [mul_assoc] at h
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp h
    exact hp.pow_dvd_of_dvd_mul_

Depends on / 依赖: _zero, contra, hp.ne_zero, hp.not_isUnit, hp.pow_dvd_of_dvd_mul_left, k.le_succ, le_succ, mul_assoc, mul_dvd_mul_iff_left, mul_dvd_mul_left, ne_zero, not_isUnit, pow_dvd_of_dvd_mul_left, pow_dvd_pow, pow_succ, preNormEDS, replace
-/
theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right {k : Nat}
    (hx : Squarefree x) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ y := by
  by_cases hxp : p ∣ x
  · obtain ⟨x', rfl⟩ := hxp
have hx' : ¬ p ∣ x' := fun contra => hp.not_isUnit hx p (mul_dvd_mul_left p contra)
    replace h : p ^ k ∣ x' * y := by
      rw [pow_succ']; rw [mul_assoc] at h
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp h
    exact hp.pow_dvd_of_dvd_mul_left _ hx' h
  · exact (pow_dvd_pow _ k.le_succ).trans (hp.pow_dvd_of_dvd_mul_left _ hxp h)

/--
theorem `pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left` / 定理 `pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left`

English:
theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left
  statement: {k : Nat}
  proof: by
  rw [mul_comm] at h
  exact pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hy hp h

中文:
定理 pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left
  结论: {k : 自然数}
  证明: by
  rw [mul_comm] at h
  exact pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hy hp h

Depends on / 依赖: _one, mul_comm, pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right, preNormEDS
-/
theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left {k : Nat}
    (hy : Squarefree y) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ x := by
  rw [mul_comm] at h
  exact pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hy hp h

variable [DecompositionMonoid R]

/--
theorem `dvd_of_squarefree_of_mul_dvd_mul_right` / 定理 `dvd_of_squarefree_of_mul_dvd_mul_right`

English:
theorem dvd_of_squarefree_of_mul_dvd_mul_right
  given: (hx : Squarefree x) (h : d * d ∣ x * y)
  statement: d ∣ y
  proof: by
  nontriviality R
  obtain ⟨a, b, ha, hb, eq⟩ := exists_dvd_and_dvd_of_dvd_mul h
  replace ha : Squarefree a := hx.squarefree_of_dvd ha
  obtain ⟨c, hc⟩ : a ∣ d := ha.isRadical 2 d ⟨b, by rw [sq, eq]⟩
  rw [hc]; rw [mul_assoc]; rw [(mul_right_injective₀ ha.ne_zero).eq_iff] at eq
  exact dvd_trans

中文:
定理 dvd_of_squarefree_of_mul_dvd_mul_right
  条件: (hx : Squarefree x) (h : d * d ∣ x * y)
  结论: d ∣ y
  证明: by
  nontriviality R
  obtain ⟨a, b, ha, hb, eq⟩ := exists_dvd_and_dvd_of_dvd_mul h
  replace ha : Squarefree a := hx.squarefree_of_dvd ha
  obtain ⟨c, hc⟩ : a ∣ d := ha.isRadical 2 d ⟨b, by rw [sq, eq]⟩
  rw [hc]; rw [mul_assoc]; rw [(mul_right_injective₀ ha.ne_zero).eq_iff] at eq
  exact dvd_trans

Depends on / 依赖: Squarefree, _two, dvd_trans, eq_iff, exists_dvd_and_dvd_of_dvd_mul, ha.isRadical, ha.ne_zero, hx.squarefree_of_dvd, isRadical, mul_assoc, mul_comm, ne_zero, nontriviality, preNormEDS, replace, squarefree_of_dvd
-/
theorem dvd_of_squarefree_of_mul_dvd_mul_right (hx : Squarefree x) (h : d * d ∣ x * y) : d ∣ y := by
  nontriviality R
  obtain ⟨a, b, ha, hb, eq⟩ := exists_dvd_and_dvd_of_dvd_mul h
  replace ha : Squarefree a := hx.squarefree_of_dvd ha
  obtain ⟨c, hc⟩ : a ∣ d := ha.isRadical 2 d ⟨b, by rw [sq, eq]⟩
  rw [hc]; rw [mul_assoc]; rw [(mul_right_injective₀ ha.ne_zero).eq_iff] at eq
  exact dvd_trans ⟨c, by rw [hc, ← eq, mul_comm]⟩ hb

/--
theorem `dvd_of_squarefree_of_mul_dvd_mul_left` / 定理 `dvd_of_squarefree_of_mul_dvd_mul_left`

English:
theorem dvd_of_squarefree_of_mul_dvd_mul_left
  given: (hy : Squarefree y) (h : d * d ∣ x * y)
  statement: d ∣ x
  proof: dvd_of_squarefree_of_mul_dvd_mul_right hy (mul_comm x y ▸ h)

中文:
定理 dvd_of_squarefree_of_mul_dvd_mul_left
  条件: (hy : Squarefree y) (h : d * d ∣ x * y)
  结论: d ∣ x
  证明: dvd_of_squarefree_of_mul_dvd_mul_right hy (mul_comm x y ▸ h)

Depends on / 依赖: _three, dvd_of_squarefree_of_mul_dvd_mul_right, mul_comm, preNormEDS
-/
theorem dvd_of_squarefree_of_mul_dvd_mul_left (hy : Squarefree y) (h : d * d ∣ x * y) : d ∣ x :=
  dvd_of_squarefree_of_mul_dvd_mul_right hy (mul_comm x y ▸ h)

end Squarefree

variable [DecompositionMonoid R]

/--
theorem `squarefree_mul_iff` / 定理 `squarefree_mul_iff`

English:
theorem squarefree_mul_iff
  statement: Squarefree (x * y) ↔ IsRelPrime x y ∧ Squarefree x ∧ Squarefree y
  proof: ⟨fun h => ⟨IsRelPrime.of_squarefree_mul h, h.of_mul_left, h.of_mul_right⟩,
    fun ⟨hp, sqx, sqy⟩ _ dvd => hp (sqy.dvd_of_squarefree_of_mul_dvd_mul_left dvd)
      (sqx.dvd_of_squarefree_of_mul_dvd_mul_right dvd)⟩

中文:
定理 squarefree_mul_iff
  结论: Squarefree (x * y) ↔ IsRelPrime x y ∧ Squarefree x ∧ Squarefree y
  证明: ⟨fun h => ⟨IsRelPrime.of_squarefree_mul h, h.of_mul_left, h.of_mul_right⟩,
    fun ⟨hp, sqx, sqy⟩ _ dvd => hp (sqy.dvd_of_squarefree_of_mul_dvd_mul_left dvd)
      (sqx.dvd_of_squarefree_of_mul_dvd_mul_right dvd)⟩

Depends on / 依赖: IsRelPrime, IsRelPrime.of_squarefree_mul, _four, dvd_of_squarefree_of_mul_dvd_mul_left, dvd_of_squarefree_of_mul_dvd_mul_right, h.of_mul_left, h.of_mul_right, of_mul_left, of_mul_right, of_squarefree_mul, preNormEDS, sqx.dvd_of_squarefree_of_mul_dvd_mul_right, sqy.dvd_of_squarefree_of_mul_dvd_mul_left
-/
theorem squarefree_mul_iff : Squarefree (x * y) ↔ IsRelPrime x y ∧ Squarefree x ∧ Squarefree y :=
  ⟨fun h => ⟨IsRelPrime.of_squarefree_mul h, h.of_mul_left, h.of_mul_right⟩,
    fun ⟨hp, sqx, sqy⟩ _ dvd => hp (sqy.dvd_of_squarefree_of_mul_dvd_mul_left dvd)
      (sqx.dvd_of_squarefree_of_mul_dvd_mul_right dvd)⟩

open scoped Function in
/--
theorem `Finset.squarefree_prod_of_pairwise_isCoprime` / 定理 `Finset.squarefree_prod_of_pairwise_isCoprime`

English:
theorem Finset.squarefree_prod_of_pairwise_isCoprime
  statement: {ι : Type*} {s : Finset ι}
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons]; rw [squarefree_mul_iff]
    rw [Finset.coe_cons]; rw [Set.pairwise_insert] at hs
    refine ⟨.prod_right fun i hi => ?_, hs' a (by simp), ?_⟩
    · exact (hs.right i (by simp [hi]) fu

中文:
定理 Finset.squarefree_prod_of_pairwise_isCoprime
  结论: {ι : 类型} {s : Finset ι}
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons]; rw [squarefree_mul_iff]
    rw [Finset.coe_cons]; rw [Set.pairwise_insert] at hs
    refine ⟨.prod_right fun i hi => ?_, hs' a (by simp), ?_⟩
    · exact (hs.right i (by simp [hi]) fu

Depends on / 依赖: Finset, Finset.coe_cons, Finset.cons_induction, Finset.mem_cons_of_mem, Finset.prod_cons, Set.pairwise_insert, _even, coe_cons, cons_induction, hs.left, hs.right, mem_cons_of_mem, pairwise_insert, preNormEDS, prod_cons, prod_right, squarefree_mul_iff
-/
theorem Finset.squarefree_prod_of_pairwise_isCoprime {ι : Type*} {s : Finset ι}
    {f : ι -> R} (hs : Set.Pairwise s (IsRelPrime on f)) (hs' : forall i in s, Squarefree (f i)) :
    Squarefree (∏ i in s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons]; rw [squarefree_mul_iff]
    rw [Finset.coe_cons]; rw [Set.pairwise_insert] at hs
    refine ⟨.prod_right fun i hi => ?_, hs' a (by simp), ?_⟩
    · exact (hs.right i (by simp [hi]) fun h => ha (h ▸ hi)).left
· exact ih hs.left fun i hi => hs' i Finset.mem_cons_of_mem hi

/--
theorem `isRadical_iff_squarefree_or_zero` / 定理 `isRadical_iff_squarefree_or_zero`

English:
theorem isRadical_iff_squarefree_or_zero
  statement: IsRadical x ↔ Squarefree x ∨ x = 0
  proof: ⟨fun hx => (em <| x = 0).elim .inr fun h => .inl hx.squarefree h,
Or.rec Squarefree.isRadical by
      rintro rfl
      rw [zero_isRadical_iff]
      infer_instance⟩

中文:
定理 isRadical_iff_squarefree_or_zero
  结论: IsRadical x ↔ Squarefree x ∨ x = 0
  证明: ⟨fun hx => (em <| x = 0).elim .inr fun h => .inl hx.squarefree h,
Or.rec Squarefree.isRadical by
      rintro rfl
      rw [zero_isRadical_iff]
      infer_instance⟩

Depends on / 依赖: Or.rec, Squarefree, Squarefree.isRadical, _odd, hx.squarefree, infer_instance, isRadical, preNormEDS, squarefree, zero_isRadical_iff
-/
theorem isRadical_iff_squarefree_or_zero : IsRadical x ↔ Squarefree x ∨ x = 0 :=
⟨fun hx => (em <| x = 0).elim .inr fun h => .inl hx.squarefree h,
Or.rec Squarefree.isRadical by
      rintro rfl
      rw [zero_isRadical_iff]
      infer_instance⟩

/--
theorem `isRadical_iff_squarefree_of_ne_zero` / 定理 `isRadical_iff_squarefree_of_ne_zero`

English:
theorem isRadical_iff_squarefree_of_ne_zero
  given: (h : x != 0)
  statement: IsRadical x ↔ Squarefree x
  proof: ⟨IsRadical.squarefree h, Squarefree.isRadical⟩

中文:
定理 isRadical_iff_squarefree_of_ne_zero
  条件: (h : x != 0)
  结论: IsRadical x ↔ Squarefree x
  证明: ⟨IsRadical.squarefree h, Squarefree.isRadical⟩

Depends on / 依赖: IsRadical, IsRadical.squarefree, Squarefree, Squarefree.isRadical, isRadical, squarefree
-/
theorem isRadical_iff_squarefree_of_ne_zero (h : x != 0) : IsRadical x ↔ Squarefree x :=
  ⟨IsRadical.squarefree h, Squarefree.isRadical⟩

end IsRadical

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

/--
lemma `_root_.exists_squarefree_dvd_pow_of_ne_zero` / 引理 `_root_.exists_squarefree_dvd_pow_of_ne_zero`

English:
lemma _root_.exists_squarefree_dvd_pow_of_ne_zero
  given: {x : R} (hx : x != 0)
  proof: by
  induction x using WfDvdMonoid.induction_on_irreducible with
  | zero => contradiction
  | unit u hu => exact ⟨1, 0, squarefree_one, one_dvd u, hu.dvd⟩
  | mul z p hz hp ih =>
    obtain ⟨y, n, hy, hyx, hy'⟩ := ih hz
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨p, 1, hp.squarefree, dvd

中文:
引理 _root_.exists_squarefree_dvd_pow_of_ne_zero
  条件: {x : R} (hx : x != 0)
  证明: by
  induction x using WfDvdMonoid.induction_on_irreducible with
  | zero => contradiction
  | unit u hu => exact ⟨1, 0, squarefree_one, one_dvd u, hu.dvd⟩
  | mul z p hz hp ih =>
    obtain ⟨y, n, hy, hyx, hy'⟩ := ih hz
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨p, 1, hp.squarefree, dvd

Depends on / 依赖: Squarefree, WfDvdMonoid, WfDvdMonoid.induction_on_irreducible, dvd_mul_of_dvd_right, dvd_mul_right, eq_zero_or_pos, hp.squarefree, hu.dvd, induction_on_irreducible, isUnit_of_dvd_one, mul_comm, mul_dvd_mul, n.eq_zero_or_pos, one_dvd, pow_succ, pow_zero, squarefree, squarefree_one
-/
lemma _root_.exists_squarefree_dvd_pow_of_ne_zero {x : R} (hx : x != 0) :
    exists (y : R) (n : Nat), Squarefree y ∧ y ∣ x ∧ x ∣ y ^ n := by
  induction x using WfDvdMonoid.induction_on_irreducible with
  | zero => contradiction
  | unit u hu => exact ⟨1, 0, squarefree_one, one_dvd u, hu.dvd⟩
  | mul z p hz hp ih =>
    obtain ⟨y, n, hy, hyx, hy'⟩ := ih hz
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨p, 1, hp.squarefree, dvd_mul_right p z, by simp [isUnit_of_dvd_one (pow_zero y ▸ hy')]⟩
    by_cases hp' : p ∣ y
    · exact ⟨y, n + 1, hy, dvd_mul_of_dvd_right hyx _,
        mul_comm p z ▸ pow_succ y n ▸ mul_dvd_mul hy' hp'⟩
    · suffices Squarefree (p * y) from ⟨p * y, n, this,
        mul_dvd_mul_left p hyx, mul_pow p y n ▸ mul_dvd_mul (dvd_pow_self p hn.ne') hy'⟩
      exact squarefree_mul_iff.mpr ⟨hp.isRelPrime_iff_not_dvd.mpr hp', hp.squarefree, hy⟩

/--
theorem `squarefree_iff_nodup_normalizedFactors` / 定理 `squarefree_iff_nodup_normalizedFactors`

English:
theorem squarefree_iff_nodup_normalizedFactors
  statement: [NormalizationMonoid R] {x : R}
  proof: by
  classical
  rw [squarefree_iff_emultiplicity_le_one]; rw [Multiset.nodup_iff_count_le_one]
  have := nontrivial_of_ne x 0 x0
  constructor <;> intro h a
  · by_cases hmem : a in normalizedFactors x
    · have ha := irreducible_of_normalized_factor _ hmem
      rcases h a with (h | h)
      · rw

中文:
定理 squarefree_iff_nodup_normalizedFactors
  结论: [NormalizationMonoid R] {x : R}
  证明: by
  classical
  rw [squarefree_iff_emultiplicity_le_one]; rw [Multiset.nodup_iff_count_le_one]
  have := nontrivial_of_ne x 0 x0
  constructor <;> intro h a
  · by_cases hmem : a in normalizedFactors x
    · have ha := irreducible_of_normalized_factor _ hmem
      rcases h a with (h | h)
      · rw

Depends on / 依赖: Multiset, Multiset.count_eq_zero_of_notMem, Multiset.nodup_iff_count_le_one, assumption_mod_cast, classical, count_eq_zero_of_notMem, emultiplicity_eq_count_normalizedFactors, irreducible_of_normalized_factor, nodup_iff_count_le_one, nontrivial_of_ne, normalize_normalized_factor, normalizedFactors, or_iff_not_imp_right, squarefree_iff_emultiplicity_le_one
-/
theorem squarefree_iff_nodup_normalizedFactors [NormalizationMonoid R] {x : R}
    (x0 : x != 0) : Squarefree x ↔ Multiset.Nodup (normalizedFactors x) := by
  classical
  rw [squarefree_iff_emultiplicity_le_one]; rw [Multiset.nodup_iff_count_le_one]
  have := nontrivial_of_ne x 0 x0
  constructor <;> intro h a
  · by_cases hmem : a in normalizedFactors x
    · have ha := irreducible_of_normalized_factor _ hmem
      rcases h a with (h | h)
      · rw [← normalize_normalized_factor _ hmem]
        rw [emultiplicity_eq_count_normalizedFactors ha x0] at h
        assumption_mod_cast
      · have := ha.1
        contradiction
    · simp [Multiset.count_eq_zero_of_notMem hmem]
  · rw [or_iff_not_imp_right]
    intro hu
    rcases eq_or_ne a 0 with rfl | h0
    · simp [x0]
    rcases WfDvdMonoid.exists_irreducible_factor hu h0 with ⟨b, hib, hdvd⟩
    apply le_trans (emultiplicity_le_emultiplicity_of_dvd_left hdvd)
    rw [emultiplicity_eq_count_normalizedFactors hib x0]
    exact_mod_cast h (normalize b)

end UniqueFactorizationMonoid

namespace Int

@[simp]
/--
theorem `squarefree_natAbs` / 定理 `squarefree_natAbs`

English:
theorem squarefree_natAbs
  given: {n : Int}
  statement: Squarefree n.natAbs ↔ Squarefree n
  proof: by
  simp_rw [Squarefree, natAbs_surjective.forall, ← natAbs_mul, natAbs_dvd_natAbs,
    isUnit_iff_natAbs_eq, Nat.isUnit_iff]

@[simp]

中文:
定理 squarefree_natAbs
  条件: {n : 整数}
  结论: Squarefree n.natAbs ↔ Squarefree n
  证明: by
  simp_rw [Squarefree, natAbs_surjective.forall, ← natAbs_mul, natAbs_dvd_natAbs,
    isUnit_iff_natAbs_eq, Nat.isUnit_iff]

@[simp]

Depends on / 依赖: Nat.isUnit_iff, Squarefree, isUnit_iff, isUnit_iff_natAbs_eq, natAbs_dvd_natAbs, natAbs_mul, natAbs_surjective, natAbs_surjective.forall, simp_rw
-/
theorem squarefree_natAbs {n : Int} : Squarefree n.natAbs ↔ Squarefree n := by
  simp_rw [Squarefree, natAbs_surjective.forall, ← natAbs_mul, natAbs_dvd_natAbs,
    isUnit_iff_natAbs_eq, Nat.isUnit_iff]

@[simp]
/--
theorem `squarefree_natCast` / 定理 `squarefree_natCast`

English:
theorem squarefree_natCast
  given: {n : Nat}
  statement: Squarefree (n : Int) ↔ Squarefree n
  proof: by
  rw [← squarefree_natAbs]; rw [natAbs_natCast]

中文:
定理 squarefree_natCast
  条件: {n : 自然数}
  结论: Squarefree (n : 整数) ↔ Squarefree n
  证明: by
  rw [← squarefree_natAbs]; rw [natAbs_natCast]

Depends on / 依赖: natAbs_natCast, squarefree_natAbs
-/
theorem squarefree_natCast {n : Nat} : Squarefree (n : Int) ↔ Squarefree n := by
  rw [← squarefree_natAbs]; rw [natAbs_natCast]

end Int
