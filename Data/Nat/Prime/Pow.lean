/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime numbers

This file develops the theory of prime numbers: natural numbers `p ≥ 2` whose only divisors are
`p` and `1`.

-/

public section

namespace Nat

/--
theorem `pow_minFac` / 定理 `pow_minFac`

English:
theorem pow_minFac
  given: {n k : Nat} (hk : k != 0)
  statement: (n ^ k).minFac = n.minFac
  proof: by
  rcases eq_or_ne n 1 with (rfl | hn)
  · simp
  have hnk : n ^ k != 1 := fun hk' => hn ((pow_eq_one_iff_left hk).1 hk')
  apply (minFac_le_of_dvd (minFac_prime hn).two_le ((minFac_dvd n).pow hk)).antisymm
  apply
    minFac_le_of_dvd (minFac_prime hnk).two_le
      ((minFac_prime hnk).dvd_of_dvd

中文:
定理 pow_minFac
  条件: {n k : 自然数} (hk : k != 0)
  结论: (n ^ k).minFac = n.minFac
  证明: by
  rcases eq_or_ne n 1 with (rfl | hn)
  · simp
  have hnk : n ^ k != 1 := fun hk' => hn ((pow_eq_one_iff_left hk).1 hk')
  apply (minFac_le_of_dvd (minFac_prime hn).two_le ((minFac_dvd n).pow hk)).antisymm
  apply
    minFac_le_of_dvd (minFac_prime hnk).two_le
      ((minFac_prime hnk).dvd_of_dvd

Depends on / 依赖: antisymm, dvd_of_dvd_pow, eq_or_ne, minFac_dvd, minFac_le_of_dvd, minFac_prime, pow_eq_one_iff_left, two_le
-/
theorem pow_minFac {n k : Nat} (hk : k != 0) : (n ^ k).minFac = n.minFac := by
  rcases eq_or_ne n 1 with (rfl | hn)
  · simp
  have hnk : n ^ k != 1 := fun hk' => hn ((pow_eq_one_iff_left hk).1 hk')
  apply (minFac_le_of_dvd (minFac_prime hn).two_le ((minFac_dvd n).pow hk)).antisymm
  apply
    minFac_le_of_dvd (minFac_prime hnk).two_le
      ((minFac_prime hnk).dvd_of_dvd_pow (minFac_dvd _))

/--
theorem `Prime.pow_minFac` / 定理 `Prime.pow_minFac`

English:
theorem Prime.pow_minFac
  given: {p k : Nat} (hp : p.Prime) (hk : k != 0)
  statement: (p ^ k).minFac = p
  proof: by
  rw [Nat.pow_minFac hk]; rw [hp.minFac_eq]

中文:
定理 素.pow_minFac
  条件: {p k : 自然数} (hp : p.素) (hk : k != 0)
  结论: (p ^ k).minFac = p
  证明: by
  rw [Nat.pow_minFac hk]; rw [hp.minFac_eq]

Depends on / 依赖: Nat.pow_minFac, hp.minFac_eq, minFac_eq, pow_minFac
-/
theorem Prime.pow_minFac {p k : Nat} (hp : p.Prime) (hk : k != 0) : (p ^ k).minFac = p := by
  rw [Nat.pow_minFac hk]; rw [hp.minFac_eq]

end Nat
