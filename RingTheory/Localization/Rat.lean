/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Localization.NumDen

/-!
# Ring-theoretic fractions in `ℚ`
-/

public section

namespace Rat

open IsFractionRing

/--
theorem `isLocalizationIsInteger_iff` / 定理 `isLocalizationIsInteger_iff`

English:
theorem isLocalizationIsInteger_iff
  given: (q : Rat)
  proof: by
  simp [IsLocalization.IsInteger]

中文:
定理 isLocalizationIs整数eger_iff
  条件: (q : 有理数)
  证明: by
  simp [IsLocalization.IsInteger]

Depends on / 依赖: IsInteger, IsLocalization, IsLocalization.IsInteger
-/
theorem isLocalizationIsInteger_iff (q : Rat) :
    IsLocalization.IsInteger Int q ↔ q in Set.range Int.cast := by
  simp [IsLocalization.IsInteger]

/--
theorem `associated_num_den` / 定理 `associated_num_den`

English:
theorem associated_num_den
  given: (q : Rat)
  proof: num_den_unique Int q q.num ⟨q.den, by simp⟩
    (by simpa [isRelPrime_iff_isCoprime, Int.isCoprime_iff_nat_coprime] using q.reduced)
    (by simp [Rat.num_div_den])

中文:
定理 associated_num_den
  条件: (q : 有理数)
  证明: num_den_unique Int q q.num ⟨q.den, by simp⟩
    (by simpa [isRelPrime_iff_isCoprime, Int.isCoprime_iff_nat_coprime] using q.reduced)
    (by simp [Rat.num_div_den])

Depends on / 依赖: Int.isCoprime_iff_nat_coprime, Rat.num_div_den, isCoprime_iff_nat_coprime, isRelPrime_iff_isCoprime, num_den_unique, num_div_den, q.den, q.num, q.reduced, reduced
-/
theorem associated_num_den (q : Rat) :
    Associated (IsFractionRing.num Int q) q.num ∧ Associated (IsFractionRing.den Int q : Int) q.den :=
  num_den_unique Int q q.num ⟨q.den, by simp⟩
    (by simpa [isRelPrime_iff_isCoprime, Int.isCoprime_iff_nat_coprime] using q.reduced)
    (by simp [Rat.num_div_den])

/--
theorem `isFractionRingDen` / 定理 `isFractionRingDen`

English:
theorem isFractionRingDen
  given: (q : Rat)
  statement: (IsFractionRing.den Int q : Int).natAbs = q.den
  proof: by
  simpa [Int.associated_iff_natAbs] using q.associated_num_den.2

中文:
定理 isFractionRingDen
  条件: (q : 有理数)
  结论: (IsFractionRing.den 整数 q : 整数).natAbs = q.den
  证明: by
  simpa [Int.associated_iff_natAbs] using q.associated_num_den.2

Depends on / 依赖: Int.associated_iff_natAbs, associated_iff_natAbs, associated_num_den, q.associated_num_den
-/
theorem isFractionRingDen (q : Rat) : (IsFractionRing.den Int q : Int).natAbs = q.den := by
  simpa [Int.associated_iff_natAbs] using q.associated_num_den.2

/--
theorem `isFractionRingNum` / 定理 `isFractionRingNum`

English:
theorem isFractionRingNum
  given: (q : Rat)
  statement: Associated (IsFractionRing.num Int q : Int) q.num
  proof: q.associated_num_den.1

中文:
定理 isFractionRingNum
  条件: (q : 有理数)
  结论: Associated (IsFractionRing.num 整数 q : 整数) q.num
  证明: q.associated_num_den.1

Depends on / 依赖: associated_num_den, q.associated_num_den
-/
theorem isFractionRingNum (q : Rat) : Associated (IsFractionRing.num Int q : Int) q.num :=
  q.associated_num_den.1

end Rat
