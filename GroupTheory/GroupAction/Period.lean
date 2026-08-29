/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Period of a group action

This module defines some helpful lemmas around [`MulAction.period`] and [`AddAction.period`].
The period of a point `a` by a group element `g` is the smallest `m` such that `g ^ m • a = a`
(resp. `(m • g) +ᵥ a = a`) for a given `g : G` and `a : α`.

If such an `m` does not exist,
then by convention `MulAction.period` and `AddAction.period` return 0.
-/

public section

namespace MulAction

universe u v
variable {α : Type v}
variable {G : Type u} [Group G] [MulAction G α]
variable {M : Type u} [Monoid M] [MulAction M α]

/-- If the action is periodic, then a lower bound for its period can be computed. -/
@[to_additive /-- If the action is periodic, then a lower bound for its period can be computed. -/]
/--
theorem `le_period` / 定理 `le_period`

English:
theorem le_period
  statement: {m : M} {a : α} {n : Nat} (period_pos : 0 < period m a)
  proof: le_of_not_gt fun period_lt_n =>
moved _ period_pos period_lt_n pow_period_smul m a

中文:
定理 le_period
  结论: {m : M} {a : α} {n : 自然数} (period_pos : 0 < period m a)
  证明: le_of_not_gt fun period_lt_n =>
moved _ period_pos period_lt_n pow_period_smul m a

Depends on / 依赖: le_of_not_gt, period_lt_n, period_pos, pow_period_smul
-/
theorem le_period {m : M} {a : α} {n : Nat} (period_pos : 0 < period m a)
    (moved : forall k, 0 < k -> k < n -> m ^ k • a != a) : n <= period m a :=
  le_of_not_gt fun period_lt_n =>
moved _ period_pos period_lt_n pow_period_smul m a

/-- If for some `n`, `m ^ n • a = a`, then `period m a ≤ n`. -/
@[to_additive /-- If for some `n`, `(n • m) +ᵥ a = a`, then `period m a ≤ n`. -/]
/--
theorem `period_le_of_fixed` / 定理 `period_le_of_fixed`

English:
theorem period_le_of_fixed
  given: {m : M} {a : α} {n : Nat} (n_pos : 0 < n) (fixed : m ^ n • a = a)
  proof: (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_le n_pos

中文:
定理 period_le_of_fixed
  条件: {m : M} {a : α} {n : 自然数} (n_pos : 0 < n) (fixed : m ^ n • a = a)
  证明: (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_le n_pos

Depends on / 依赖: isPeriodicPt_smul_iff, isPeriodicPt_smul_iff.mpr, minimalPeriod_le, n_pos
-/
theorem period_le_of_fixed {m : M} {a : α} {n : Nat} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    period m a <= n :=
  (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_le n_pos

/-- If for some `n`, `m ^ n • a = a`, then `0 < period m a`. -/
@[to_additive /-- If for some `n`, `(n • m) +ᵥ a = a`, then `0 < period m a`. -/]
/--
theorem `period_pos_of_fixed` / 定理 `period_pos_of_fixed`

English:
theorem period_pos_of_fixed
  given: {m : M} {a : α} {n : Nat} (n_pos : 0 < n) (fixed : m ^ n • a = a)
  proof: (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_pos n_pos

@[to_additive]

中文:
定理 period_pos_of_fixed
  条件: {m : M} {a : α} {n : 自然数} (n_pos : 0 < n) (fixed : m ^ n • a = a)
  证明: (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_pos n_pos

@[to_additive]

Depends on / 依赖: isPeriodicPt_smul_iff, isPeriodicPt_smul_iff.mpr, minimalPeriod_pos, n_pos
-/
theorem period_pos_of_fixed {m : M} {a : α} {n : Nat} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    0 < period m a :=
  (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_pos n_pos

@[to_additive]
/--
theorem `period_eq_one_iff` / 定理 `period_eq_one_iff`

English:
theorem period_eq_one_iff
  given: {m : M} {a : α}
  statement: period m a = 1 ↔ m • a = a
  proof: ⟨fun eq_one => pow_one m ▸ eq_one ▸ pow_period_smul m a,
   fun fixed => le_antisymm
    (period_le_of_fixed one_pos (by simpa))
    (period_pos_of_fixed one_pos (by simpa))⟩

中文:
定理 period_eq_one_iff
  条件: {m : M} {a : α}
  结论: period m a = 1 ↔ m • a = a
  证明: ⟨fun eq_one => pow_one m ▸ eq_one ▸ pow_period_smul m a,
   fun fixed => le_antisymm
    (period_le_of_fixed one_pos (by simpa))
    (period_pos_of_fixed one_pos (by simpa))⟩

Depends on / 依赖: eq_one, le_antisymm, one_pos, period_le_of_fixed, period_pos_of_fixed, pow_one, pow_period_smul
-/
theorem period_eq_one_iff {m : M} {a : α} : period m a = 1 ↔ m • a = a :=
  ⟨fun eq_one => pow_one m ▸ eq_one ▸ pow_period_smul m a,
   fun fixed => le_antisymm
    (period_le_of_fixed one_pos (by simpa))
    (period_pos_of_fixed one_pos (by simpa))⟩

/-- For any non-zero `n` less than the period of `m` on `a`, `a` is moved by `m ^ n`. -/
@[to_additive
/-- For any non-zero `n` less than the period of `m` on `a`, `a` is moved by `n • m`. -/]
/--
theorem `pow_smul_ne_of_lt_period` / 定理 `pow_smul_ne_of_lt_period`

English:
theorem pow_smul_ne_of_lt_period
  statement: {m : M} {a : α} {n : Nat} (n_pos : 0 < n)
  proof: fun a_fixed =>
not_le_of_gt n_lt_period period_le_of_fixed n_pos a_fixed

中文:
定理 pow_smul_ne_of_lt_period
  结论: {m : M} {a : α} {n : 自然数} (n_pos : 0 < n)
  证明: fun a_fixed =>
not_le_of_gt n_lt_period period_le_of_fixed n_pos a_fixed

Depends on / 依赖: a_fixed
-/
theorem pow_smul_ne_of_lt_period {m : M} {a : α} {n : Nat} (n_pos : 0 < n)
    (n_lt_period : n < period m a) : m ^ n • a != a := fun a_fixed =>
not_le_of_gt n_lt_period period_le_of_fixed n_pos a_fixed

section Identities

/-! ### `MulAction.period` for common group elements
-/

variable (M) in
@[to_additive (attr := simp)]
/--
theorem `period_one` / 定理 `period_one`

English:
theorem period_one
  given: (a : α)
  statement: period (1 : M) a = 1
  proof: period_eq_one_iff.mpr (one_smul M a)

@[to_additive (attr := simp)]

中文:
定理 period_one
  条件: (a : α)
  结论: period (1 : M) a = 1
  证明: period_eq_one_iff.mpr (one_smul M a)

@[to_additive (attr := simp)]

Depends on / 依赖: one_smul, period_eq_one_iff, period_eq_one_iff.mpr
-/
theorem period_one (a : α) : period (1 : M) a = 1 := period_eq_one_iff.mpr (one_smul M a)

@[to_additive (attr := simp)]
/--
theorem `period_inv` / 定理 `period_inv`

English:
theorem period_inv
  given: (g : G) (a : α)
  statement: period g⁻¹ a = period g a
  proof: by
  simp only [period_eq_minimalPeriod, Function.minimalPeriod_eq_minimalPeriod_iff,
    isPeriodicPt_smul_iff]
  intro n
  rw [smul_eq_iff_eq_inv_smul]; rw [eq_comm]; rw [← zpow_natCast]; rw [inv_zpow]; rw [inv_inv]; rw [zpow_natCast]

中文:
定理 period_inv
  条件: (g : G) (a : α)
  结论: period g⁻¹ a = period g a
  证明: by
  simp only [period_eq_minimalPeriod, Function.minimalPeriod_eq_minimalPeriod_iff,
    isPeriodicPt_smul_iff]
  intro n
  rw [smul_eq_iff_eq_inv_smul]; rw [eq_comm]; rw [← zpow_natCast]; rw [inv_zpow]; rw [inv_inv]; rw [zpow_natCast]

Depends on / 依赖: Function, Function.minimalPeriod_eq_minimalPeriod_iff, eq_comm, inv_inv, inv_zpow, isPeriodicPt_smul_iff, minimalPeriod_eq_minimalPeriod_iff, period_eq_minimalPeriod, smul_eq_iff_eq_inv_smul, zpow_natCast
-/
theorem period_inv (g : G) (a : α) : period g⁻¹ a = period g a := by
  simp only [period_eq_minimalPeriod, Function.minimalPeriod_eq_minimalPeriod_iff,
    isPeriodicPt_smul_iff]
  intro n
  rw [smul_eq_iff_eq_inv_smul]; rw [eq_comm]; rw [← zpow_natCast]; rw [inv_zpow]; rw [inv_inv]; rw [zpow_natCast]

end Identities

section MonoidExponent

/-! ### `MulAction.period` and group exponents

The period of a given element `m : M` can be bounded by the `Monoid.exponent M` or `orderOf m`.
-/

@[to_additive]
/--
theorem `period_dvd_orderOf` / 定理 `period_dvd_orderOf`

English:
theorem period_dvd_orderOf
  given: (m : M) (a : α)
  statement: period m a ∣ orderOf m
  proof: by
  rw [← pow_smul_eq_iff_period_dvd]; rw [pow_orderOf_eq_one]; rw [one_smul]

@[to_additive]

中文:
定理 period_dvd_orderOf
  条件: (m : M) (a : α)
  结论: period m a ∣ orderOf m
  证明: by
  rw [← pow_smul_eq_iff_period_dvd]; rw [pow_orderOf_eq_one]; rw [one_smul]

@[to_additive]

Depends on / 依赖: one_smul, pow_orderOf_eq_one, pow_smul_eq_iff_period_dvd
-/
theorem period_dvd_orderOf (m : M) (a : α) : period m a ∣ orderOf m := by
  rw [← pow_smul_eq_iff_period_dvd]; rw [pow_orderOf_eq_one]; rw [one_smul]

@[to_additive]
/--
theorem `period_pos_of_orderOf_pos` / 定理 `period_pos_of_orderOf_pos`

English:
theorem period_pos_of_orderOf_pos
  given: {m : M} (order_pos : 0 < orderOf m) (a : α)
  proof: Nat.pos_of_dvd_of_pos (period_dvd_orderOf m a) order_pos

@[to_additive]

中文:
定理 period_pos_of_orderOf_pos
  条件: {m : M} (order_pos : 0 < orderOf m) (a : α)
  证明: Nat.pos_of_dvd_of_pos (period_dvd_orderOf m a) order_pos

@[to_additive]

Depends on / 依赖: Nat.pos_of_dvd_of_pos, order_pos, period_dvd_orderOf, pos_of_dvd_of_pos
-/
theorem period_pos_of_orderOf_pos {m : M} (order_pos : 0 < orderOf m) (a : α) :
    0 < period m a :=
  Nat.pos_of_dvd_of_pos (period_dvd_orderOf m a) order_pos

@[to_additive]
/--
theorem `period_le_orderOf` / 定理 `period_le_orderOf`

English:
theorem period_le_orderOf
  given: {m : M} (order_pos : 0 < orderOf m) (a : α)
  proof: Nat.le_of_dvd order_pos (period_dvd_orderOf m a)

@[to_additive]

中文:
定理 period_le_orderOf
  条件: {m : M} (order_pos : 0 < orderOf m) (a : α)
  证明: Nat.le_of_dvd order_pos (period_dvd_orderOf m a)

@[to_additive]

Depends on / 依赖: Nat.le_of_dvd, le_of_dvd, order_pos, period_dvd_orderOf
-/
theorem period_le_orderOf {m : M} (order_pos : 0 < orderOf m) (a : α) :
    period m a <= orderOf m :=
  Nat.le_of_dvd order_pos (period_dvd_orderOf m a)

@[to_additive]
/--
theorem `period_dvd_exponent` / 定理 `period_dvd_exponent`

English:
theorem period_dvd_exponent
  given: (m : M) (a : α)
  statement: period m a ∣ Monoid.exponent M
  proof: by
  rw [← pow_smul_eq_iff_period_dvd]; rw [Monoid.pow_exponent_eq_one]; rw [one_smul]

@[to_additive]

中文:
定理 period_dvd_exponent
  条件: (m : M) (a : α)
  结论: period m a ∣ Monoid.exponent M
  证明: by
  rw [← pow_smul_eq_iff_period_dvd]; rw [Monoid.pow_exponent_eq_one]; rw [one_smul]

@[to_additive]

Depends on / 依赖: Monoid, Monoid.pow_exponent_eq_one, one_smul, pow_exponent_eq_one, pow_smul_eq_iff_period_dvd
-/
theorem period_dvd_exponent (m : M) (a : α) : period m a ∣ Monoid.exponent M := by
  rw [← pow_smul_eq_iff_period_dvd]; rw [Monoid.pow_exponent_eq_one]; rw [one_smul]

@[to_additive]
/--
theorem `period_pos_of_exponent_pos` / 定理 `period_pos_of_exponent_pos`

English:
theorem period_pos_of_exponent_pos
  given: (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α)
  proof: Nat.pos_of_dvd_of_pos (period_dvd_exponent m a) exp_pos

@[to_additive]

中文:
定理 period_pos_of_exponent_pos
  条件: (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α)
  证明: Nat.pos_of_dvd_of_pos (period_dvd_exponent m a) exp_pos

@[to_additive]

Depends on / 依赖: Nat.pos_of_dvd_of_pos, exp_pos, period_dvd_exponent, pos_of_dvd_of_pos
-/
theorem period_pos_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    0 < period m a :=
  Nat.pos_of_dvd_of_pos (period_dvd_exponent m a) exp_pos

@[to_additive]
/--
theorem `period_le_exponent` / 定理 `period_le_exponent`

English:
theorem period_le_exponent
  given: (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α)
  proof: Nat.le_of_dvd exp_pos (period_dvd_exponent m a)

中文:
定理 period_le_exponent
  条件: (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α)
  证明: Nat.le_of_dvd exp_pos (period_dvd_exponent m a)

Depends on / 依赖: Nat.le_of_dvd, exp_pos, le_of_dvd, period_dvd_exponent
-/
theorem period_le_exponent (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    period m a <= Monoid.exponent M :=
  Nat.le_of_dvd exp_pos (period_dvd_exponent m a)

variable (α)

@[to_additive]
/--
theorem `period_bounded_of_exponent_pos` / 定理 `period_bounded_of_exponent_pos`

English:
theorem period_bounded_of_exponent_pos
  given: (exp_pos : 0 < Monoid.exponent M) (m : M)
  proof: by
  use Monoid.exponent M
  simpa [upperBounds] using period_le_exponent exp_pos _

中文:
定理 period_bounded_of_exponent_pos
  条件: (exp_pos : 0 < Monoid.exponent M) (m : M)
  证明: by
  use Monoid.exponent M
  simpa [upperBounds] using period_le_exponent exp_pos _

Depends on / 依赖: Monoid, Monoid.exponent, exp_pos, exponent, period_le_exponent, upperBounds
-/
theorem period_bounded_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) :
    BddAbove (Set.range (fun a : α => period m a)) := by
  use Monoid.exponent M
  simpa [upperBounds] using period_le_exponent exp_pos _

end MonoidExponent


end MulAction
