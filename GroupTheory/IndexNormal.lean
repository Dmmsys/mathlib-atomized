/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.GroupTheory.Index

/-! # Subgroups of small index are normal

* `Subgroup.normal_of_index_eq_smallest_prime_factor`: in a finite group `G`,
  a subgroup of index equal to the smallest prime factor of `Nat.card G` is normal.

* `Subgroup.normal_of_index_two`: in a group `G`, a subgroup of index 2 is normal
  (This does not require `G` to be finite.)

-/

public section

assert_not_exists Field

open MulAction MonoidHom Nat

variable {G : Type*} [Group G] {H : Subgroup G} {p : Nat}

namespace Subgroup

/--
theorem `normal_of_index_eq_one` / 定理 `normal_of_index_eq_one`

English:
theorem normal_of_index_eq_one
  given: (hH : H.index = 1)
  statement: H.Normal
  proof: by
  rw [index_eq_one] at hH
  rw [hH]
  infer_instance

中文:
定理 normal_of_index_eq_one
  条件: (hH : H.index = 1)
  结论: H.正规
  证明: by
  rw [index_eq_one] at hH
  rw [hH]
  infer_instance

Depends on / 依赖: index_eq_one, infer_instance
-/
theorem normal_of_index_eq_one (hH : H.index = 1) : H.Normal := by
  rw [index_eq_one] at hH
  rw [hH]
  infer_instance

/--
theorem `normal_of_index_eq_two` / 定理 `normal_of_index_eq_two`

English:
theorem normal_of_index_eq_two
  given: (hH : H.index = 2)
  statement: H.Normal where
  proof: by simp_rw [mul_mem_iff_of_index_two hH, hxH, iff_true, inv_mem_iff]

中文:
定理 normal_of_index_eq_two
  条件: (hH : H.index = 2)
  结论: H.正规 where
  证明: by simp_rw [mul_mem_iff_of_index_two hH, hxH, iff_true, inv_mem_iff]

Depends on / 依赖: iff_true, inv_mem_iff, mul_mem_iff_of_index_two, simp_rw
-/
theorem normal_of_index_eq_two (hH : H.index = 2) : H.Normal where
  conj_mem x hxH g := by simp_rw [mul_mem_iff_of_index_two hH, hxH, iff_true, inv_mem_iff]

/--
theorem `normal_of_index_eq_minFac_card` / 定理 `normal_of_index_eq_minFac_card`

English:
theorem normal_of_index_eq_minFac_card
  given: (hHp : H.index = (Nat.card G).minFac)
  proof: by
  by_cases hG0 : Nat.card G = 0
  · rw [hG0, minFac_zero] at hHp
    exact normal_of_index_eq_two hHp
  by_cases hG1 : Nat.card G = 1
  · rw [hG1, minFac_one] at hHp
    exact normal_of_index_eq_one hHp
  suffices H.normalCore.relIndex H = 1 by
    convert! H.normalCore_normal
    exact le_antisy

中文:
定理 normal_of_index_eq_minFac_card
  条件: (hHp : H.index = (自然数.card G).minFac)
  证明: by
  by_cases hG0 : Nat.card G = 0
  · rw [hG0, minFac_zero] at hHp
    exact normal_of_index_eq_two hHp
  by_cases hG1 : Nat.card G = 1
  · rw [hG1, minFac_one] at hHp
    exact normal_of_index_eq_one hHp
  suffices H.normalCore.relIndex H = 1 by
    convert! H.normalCore_normal
    exact le_antisy

Depends on / 依赖: Finite, H.index, H.normalCore.relIndex, H.normalCore_normal, Nat.card, convert, finite_of_card_ne_zero, index_ne_zero, index_ne_zero_of_finite, le_antisymm, minFac_one, minFac_zero, mul_left_inj, normalCore, normalCore_le, normalCore_normal, normal_of_index_eq_one, normal_of_index_eq_two, one_mul, relIndex
-/
theorem normal_of_index_eq_minFac_card (hHp : H.index = (Nat.card G).minFac) :
    H.Normal := by
  by_cases hG0 : Nat.card G = 0
  · rw [hG0, minFac_zero] at hHp
    exact normal_of_index_eq_two hHp
  by_cases hG1 : Nat.card G = 1
  · rw [hG1, minFac_one] at hHp
    exact normal_of_index_eq_one hHp
  suffices H.normalCore.relIndex H = 1 by
    convert! H.normalCore_normal
    exact le_antisymm (relIndex_eq_one.mp this) (normalCore_le H)
  have : Finite G := finite_of_card_ne_zero hG0
  have index_ne_zero : H.index != 0 := index_ne_zero_of_finite
  rw [← mul_left_inj' index_ne_zero]; rw [one_mul]; rw [relIndex_mul_index H.normalCore_le]
  have hp : Nat.Prime H.index := hHp ▸ minFac_prime hG1
  have h : H.normalCore.index ∣ H.index ! := by
    rw [normalCore_eq_ker]; rw [index_ker]; rw [index_eq_card]; rw [← Nat.card_perm]
    exact card_subgroup_dvd_card (toPermHom G (G ⧸ H)).range
  apply dvd_antisymm _ (index_dvd_of_le H.normalCore_le)
  rwa [← Coprime.dvd_mul_right, mul_factorial_pred hp.ne_zero]
have hr1 : H.normalCore.index != 1 := fun hr1 => hp.ne_one
    Nat.eq_one_of_dvd_one (hr1 ▸ H.normalCore.index_dvd_of_le H.normalCore_le)
  rw [Nat.coprime_factorial_iff hr1]
exact lt_of_lt_of_le (Nat.sub_one_lt hp.ne_zero)
    hHp ▸ minFac_le_of_dvd (Nat.minFac_prime hr1).two_le
      (dvd_trans (minFac_dvd H.normalCore.index) (H.normalCore.index_dvd_card))

end Subgroup
