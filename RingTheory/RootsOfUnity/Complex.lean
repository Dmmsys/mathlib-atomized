/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Snir Broshi
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Qify

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `exp (2 * π * I * (i / n))` for `i ∈ Finset.range n`.

## Main declarations

* `Complex.mem_rootsOfUnity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `exp (2 * π * I * (i / n))` for some `i < n`.
* `Complex.card_rootsOfUnity`: the number of `n`-th roots of unity is exactly `n`.
* `Complex.norm_rootOfUnity_eq_one`: A complex root of unity has norm `1`.

-/

public section


namespace Complex

open Polynomial Real

open scoped Nat Real

/--
theorem `isPrimitiveRoot_I` / 定理 `isPrimitiveRoot_I`

English:
theorem isPrimitiveRoot_I
  statement: IsPrimitiveRoot I 4
  proof: .mk_of_lt I zero_lt_four I_pow_four fun l hl0 hl4 => by
    interval_cases l <;> norm_num [Complex.ext_iff]

中文:
定理 isPrimitiveRoot_I
  结论: 是PrimitiveRoot I 4
  证明: .mk_of_lt I zero_lt_four I_pow_four fun l hl0 hl4 => by
    interval_cases l <;> norm_num [Complex.ext_iff]

Depends on / 依赖: Complex.ext_iff, I_pow_four, ext_iff, interval_cases, mk_of_lt, zero_lt_four
-/
theorem isPrimitiveRoot_I : IsPrimitiveRoot I 4 :=
  .mk_of_lt I zero_lt_four I_pow_four fun l hl0 hl4 => by
    interval_cases l <;> norm_num [Complex.ext_iff]

/--
theorem `isPrimitiveRoot_neg_I` / 定理 `isPrimitiveRoot_neg_I`

English:
theorem isPrimitiveRoot_neg_I
  statement: IsPrimitiveRoot (-I) 4
  proof: by
  simpa only [inv_I] using isPrimitiveRoot_I.inv

中文:
定理 isPrimitiveRoot_neg_I
  结论: 是PrimitiveRoot (-I) 4
  证明: by
  simpa only [inv_I] using isPrimitiveRoot_I.inv

Depends on / 依赖: inv_I, isPrimitiveRoot_I, isPrimitiveRoot_I.inv
-/
theorem isPrimitiveRoot_neg_I : IsPrimitiveRoot (-I) 4 := by
  simpa only [inv_I] using isPrimitiveRoot_I.inv

/--
theorem `isPrimitiveRoot_exp_of_isCoprime` / 定理 `isPrimitiveRoot_exp_of_isCoprime`

English:
theorem isPrimitiveRoot_exp_of_isCoprime
  given: (i : Int) (n : Nat) (h0 : n != 0) (hi : IsCoprime i n)
  proof: by
  rw [IsPrimitiveRoot.iff_def]
  simp only [← exp_nat_mul, exp_eq_one_iff]
  constructor
  · use i
    simp (discharger := norm_cast) [field]
  · simp only [forall_exists_index]
    have hn0 : (n : Complex) != 0 := mod_cast h0
    rintro l k hk
    field_simp at hk
    norm_cast at hk
exact Int.natCast_dvd_natCast.mp hi.symm.dvd_of_dvd_mul_right hk ▸ dvd_mul_right ..

中文:
定理 isPrimitiveRoot_exp_of_isCoprime
  条件: (i : 整数) (n : 自然数) (h0 : n != 0) (hi : IsCoprime i n)
  证明: by
  rw [IsPrimitiveRoot.iff_def]
  simp only [← exp_nat_mul, exp_eq_one_iff]
  constructor
  · use i
    simp (discharger := norm_cast) [field]
  · simp only [forall_exists_index]
    have hn0 : (n : Complex) != 0 := mod_cast h0
    rintro l k hk
    field_simp at hk
    norm_cast at hk
exact Int.natCast_dvd_natCast.mp hi.symm.dvd_of_dvd_mul_right hk ▸ dvd_mul_right ..

Depends on / 依赖: Int.natCast_dvd_natCast.mp, IsPrimitiveRoot, IsPrimitiveRoot.iff_def, discharger, dvd_mul_right, dvd_of_dvd_mul_right, exp_eq_one_iff, exp_nat_mul, forall_exists_index, hi.symm.dvd_of_dvd_mul_right, iff_def, mod_cast, natCast_dvd_natCast
-/
theorem isPrimitiveRoot_exp_of_isCoprime (i : Int) (n : Nat) (h0 : n != 0) (hi : IsCoprime i n) :
    IsPrimitiveRoot (exp (2 * π * I * (i / n))) n := by
  rw [IsPrimitiveRoot.iff_def]
  simp only [← exp_nat_mul, exp_eq_one_iff]
  constructor
  · use i
    simp (discharger := norm_cast) [field]
  · simp only [forall_exists_index]
    have hn0 : (n : Complex) != 0 := mod_cast h0
    rintro l k hk
    field_simp at hk
    norm_cast at hk
exact Int.natCast_dvd_natCast.mp hi.symm.dvd_of_dvd_mul_right hk ▸ dvd_mul_right ..

/--
theorem `isPrimitiveRoot_exp_of_coprime` / 定理 `isPrimitiveRoot_exp_of_coprime`

English:
theorem isPrimitiveRoot_exp_of_coprime
  given: (i n : Nat) (h0 : n != 0) (hi : i.Coprime n)
  proof: isPrimitiveRoot_exp_of_isCoprime _ _ h0 hi.isCoprime

中文:
定理 isPrimitiveRoot_exp_of_coprime
  条件: (i n : 自然数) (h0 : n != 0) (hi : i.Coprime n)
  证明: isPrimitiveRoot_exp_of_isCoprime _ _ h0 hi.isCoprime

Depends on / 依赖: hi.isCoprime, isCoprime, isPrimitiveRoot_exp_of_isCoprime
-/
theorem isPrimitiveRoot_exp_of_coprime (i n : Nat) (h0 : n != 0) (hi : i.Coprime n) :
    IsPrimitiveRoot (exp (2 * π * I * (i / n))) n :=
  isPrimitiveRoot_exp_of_isCoprime _ _ h0 hi.isCoprime

/--
theorem `isPrimitiveRoot_exp_rat` / 定理 `isPrimitiveRoot_exp_rat`

English:
theorem isPrimitiveRoot_exp_rat
  given: (q : Rat)
  statement: IsPrimitiveRoot (exp (2 * π * I * q)) q.den
  proof: by
  convert!
isPrimitiveRoot_exp_of_isCoprime _ _ q.den_nz Int.isCoprime_iff_nat_coprime.mpr q.reduced
  nth_rw 1 [← Rat.num_div_den q]
  simp

中文:
定理 isPrimitiveRoot_exp_rat
  条件: (q : 有理数)
  结论: 是PrimitiveRoot (exp (2 * π * I * q)) q.den
  证明: by
  convert!
isPrimitiveRoot_exp_of_isCoprime _ _ q.den_nz Int.isCoprime_iff_nat_coprime.mpr q.reduced
  nth_rw 1 [← Rat.num_div_den q]
  simp

Depends on / 依赖: Int.isCoprime_iff_nat_coprime.mpr, Rat.num_div_den, convert, den_nz, isCoprime_iff_nat_coprime, isPrimitiveRoot_exp_of_isCoprime, nth_rw, num_div_den, q.den_nz, q.reduced, reduced
-/
theorem isPrimitiveRoot_exp_rat (q : Rat) : IsPrimitiveRoot (exp (2 * π * I * q)) q.den := by
  convert!
isPrimitiveRoot_exp_of_isCoprime _ _ q.den_nz Int.isCoprime_iff_nat_coprime.mpr q.reduced
  nth_rw 1 [← Rat.num_div_den q]
  simp

/--
theorem `isPrimitiveRoot_exp_rat_of_even_num` / 定理 `isPrimitiveRoot_exp_rat_of_even_num`

English:
theorem isPrimitiveRoot_exp_rat_of_even_num
  given: (q : Rat) (h : Even q.num)
  proof: by
.mp h have ⟨n, hn⟩ := even_iff_exists_two_nsmul _
  convert! isPrimitiveRoot_exp_rat (n / q.den) using 1
  · nth_rw 1 [← q.num_div_den, hn, Int.nsmul_eq_mul]
    push_cast
    ring_nf
  · rw [← Int.cast_natCast, ← Rat.divInt_eq_div, ← Rat.mk_eq_divInt (nz := by simp)]
    apply Nat.Coprime.coprime_mul_left (k := 2)
    convert! q.reduced
    grind

中文:
定理 isPrimitiveRoot_exp_rat_of_even_num
  条件: (q : 有理数) (h : Even q.num)
  证明: by
.mp h have ⟨n, hn⟩ := even_iff_exists_two_nsmul _
  convert! isPrimitiveRoot_exp_rat (n / q.den) using 1
  · nth_rw 1 [← q.num_div_den, hn, Int.nsmul_eq_mul]
    push_cast
    ring_nf
  · rw [← Int.cast_natCast, ← Rat.divInt_eq_div, ← Rat.mk_eq_divInt (nz := by simp)]
    apply Nat.Coprime.coprime_mul_left (k := 2)
    convert! q.reduced
    grind

Depends on / 依赖: Coprime, Int.cast_natCast, Int.nsmul_eq_mul, Nat.Coprime.coprime_mul_left, Rat.divInt_eq_div, Rat.mk_eq_divInt, cast_natCast, convert, coprime_mul_left, divInt_eq_div, even_iff_exists_two_nsmul, isPrimitiveRoot_exp_rat, mk_eq_divInt, nsmul_eq_mul, nth_rw, num_div_den, q.den, q.num_div_den, q.reduced, reduced
-/
theorem isPrimitiveRoot_exp_rat_of_even_num (q : Rat) (h : Even q.num) :
    IsPrimitiveRoot (exp (π * I * q)) q.den := by
.mp h have ⟨n, hn⟩ := even_iff_exists_two_nsmul _
  convert! isPrimitiveRoot_exp_rat (n / q.den) using 1
  · nth_rw 1 [← q.num_div_den, hn, Int.nsmul_eq_mul]
    push_cast
    ring_nf
  · rw [← Int.cast_natCast, ← Rat.divInt_eq_div, ← Rat.mk_eq_divInt (nz := by simp)]
    apply Nat.Coprime.coprime_mul_left (k := 2)
    convert! q.reduced
    grind

/--
theorem `isPrimitiveRoot_exp_rat_of_odd_num` / 定理 `isPrimitiveRoot_exp_rat_of_odd_num`

English:
theorem isPrimitiveRoot_exp_rat_of_odd_num
  given: (q : Rat) (h : Odd q.num)
  proof: by
  convert! isPrimitiveRoot_exp_rat (q / 2) using 1
  · push_cast
    ring_nf
  · nth_rw 2 [← q.num_div_den]
    rw [mul_comm]; rw [div_div]; rw [← Int.cast_ofNat]; rw [← Int.cast_natCast]; rw [← Int.cast_mul]; rw [← Rat.divInt_eq_div]; rw [← Nat.cast_ofNat (R := Int)]; rw [← Nat.cast_mul]; rw [← Rat.mk_eq_divInt (nz := by simp)
        (c := Nat.Coprime.mul_right q.reduced h.natAbs.coprime_two_right)]

中文:
定理 isPrimitiveRoot_exp_rat_of_odd_num
  条件: (q : 有理数) (h : Odd q.num)
  证明: by
  convert! isPrimitiveRoot_exp_rat (q / 2) using 1
  · push_cast
    ring_nf
  · nth_rw 2 [← q.num_div_den]
    rw [mul_comm]; rw [div_div]; rw [← Int.cast_ofNat]; rw [← Int.cast_natCast]; rw [← Int.cast_mul]; rw [← Rat.divInt_eq_div]; rw [← Nat.cast_ofNat (R := Int)]; rw [← Nat.cast_mul]; rw [← Rat.mk_eq_divInt (nz := by simp)
        (c := Nat.Coprime.mul_right q.reduced h.natAbs.coprime_two_right)]

Depends on / 依赖: Coprime, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.Coprime.mul_right, Nat.cast_mul, Nat.cast_ofNat, Rat.divInt_eq_div, Rat.mk_eq_divInt, cast_mul, cast_natCast, cast_ofNat, convert, coprime_two_right, divInt_eq_div, div_div, h.natAbs.coprime_two_right, isPrimitiveRoot_exp_rat, mk_eq_divInt, mul_comm
-/
theorem isPrimitiveRoot_exp_rat_of_odd_num (q : Rat) (h : Odd q.num) :
    IsPrimitiveRoot (exp (π * I * q)) (2 * q.den) := by
  convert! isPrimitiveRoot_exp_rat (q / 2) using 1
  · push_cast
    ring_nf
  · nth_rw 2 [← q.num_div_den]
    rw [mul_comm]; rw [div_div]; rw [← Int.cast_ofNat]; rw [← Int.cast_natCast]; rw [← Int.cast_mul]; rw [← Rat.divInt_eq_div]; rw [← Nat.cast_ofNat (R := Int)]; rw [← Nat.cast_mul]; rw [← Rat.mk_eq_divInt (nz := by simp)
        (c := Nat.Coprime.mul_right q.reduced h.natAbs.coprime_two_right)]

/--
theorem `isPrimitiveRoot_exp` / 定理 `isPrimitiveRoot_exp`

English:
theorem isPrimitiveRoot_exp
  given: (n : Nat) (h0 : n != 0)
  statement: IsPrimitiveRoot (exp (2 * π * I / n)) n
  proof: by
  simpa only [Nat.cast_one, one_div] using!
    isPrimitiveRoot_exp_of_coprime 1 n h0 n.coprime_one_left

中文:
定理 isPrimitiveRoot_exp
  条件: (n : 自然数) (h0 : n != 0)
  结论: 是PrimitiveRoot (exp (2 * π * I / n)) n
  证明: by
  simpa only [Nat.cast_one, one_div] using!
    isPrimitiveRoot_exp_of_coprime 1 n h0 n.coprime_one_left

Depends on / 依赖: Nat.cast_one, cast_one, coprime_one_left, isPrimitiveRoot_exp_of_coprime, n.coprime_one_left, one_div
-/
theorem isPrimitiveRoot_exp (n : Nat) (h0 : n != 0) : IsPrimitiveRoot (exp (2 * π * I / n)) n := by
  simpa only [Nat.cast_one, one_div] using!
    isPrimitiveRoot_exp_of_coprime 1 n h0 n.coprime_one_left

/--
theorem `isPrimitiveRoot_iff` / 定理 `isPrimitiveRoot_iff`

English:
theorem isPrimitiveRoot_iff
  given: (ζ : Complex) (n : Nat) (hn : n != 0)
  proof: by
  have hn0 : (n : Complex) != 0 := mod_cast hn
  constructor; swap
  · rintro ⟨i, -, hi, rfl⟩; exact isPrimitiveRoot_exp_of_coprime i n hn hi
  intro h
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, hi, rfl⟩ :=
    (isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨i, hi, ((isPrimitiveRoot_exp n hn).pow_iff_coprime (Nat.pos_of_ne_zero hn) i).mp h, ?_⟩
  rw [← exp_nat_mul]
  congr 1
  ring

中文:
定理 isPrimitiveRoot_iff
  条件: (ζ : 复形) (n : 自然数) (hn : n != 0)
  证明: by
  have hn0 : (n : Complex) != 0 := mod_cast hn
  constructor; swap
  · rintro ⟨i, -, hi, rfl⟩; exact isPrimitiveRoot_exp_of_coprime i n hn hi
  intro h
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, hi, rfl⟩ :=
    (isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨i, hi, ((isPrimitiveRoot_exp n hn).pow_iff_coprime (Nat.pos_of_ne_zero hn) i).mp h, ?_⟩
  rw [← exp_nat_mul]
  congr 1
  ring

Depends on / 依赖: Nat.pos_of_ne_zero, NeZero, eq_pow_of_pow_eq_one, exp_nat_mul, h.pow_eq_one, isPrimitiveRoot_exp, isPrimitiveRoot_exp_of_coprime, mod_cast, pos_of_ne_zero, pow_eq_one, pow_iff_coprime
-/
theorem isPrimitiveRoot_iff (ζ : Complex) (n : Nat) (hn : n != 0) :
    IsPrimitiveRoot ζ n ↔ exists i < n, exists _ : i.Coprime n, exp (2 * π * I * (i / n)) = ζ := by
  have hn0 : (n : Complex) != 0 := mod_cast hn
  constructor; swap
  · rintro ⟨i, -, hi, rfl⟩; exact isPrimitiveRoot_exp_of_coprime i n hn hi
  intro h
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, hi, rfl⟩ :=
    (isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨i, hi, ((isPrimitiveRoot_exp n hn).pow_iff_coprime (Nat.pos_of_ne_zero hn) i).mp h, ?_⟩
  rw [← exp_nat_mul]
  congr 1
  ring

/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `exp (2 * Real.pi * Complex.I * (i / n))` for some `i < n`. -/
nonrec theorem mem_rootsOfUnity (n : Nat) [NeZero n] (x : Units Complex) :
    x in rootsOfUnity n Complex ↔ exists i < n, exp (2 * π * I * (i / n)) = x := by
  rw [mem_rootsOfUnity]; rw [Units.ext_iff]; rw [Units.val_pow_eq_pow_val]; rw [Units.val_one]
  have hn0 : (n : Complex) != 0 := mod_cast NeZero.out
  constructor
  · intro h
    obtain ⟨i, hi, H⟩ : exists i < (n : Nat), exp (2 * π * I / n) ^ i = x :=
      (isPrimitiveRoot_exp n NeZero.out).eq_pow_of_pow_eq_one h
    refine ⟨i, hi, ?_⟩
    rw [← H]; rw [← exp_nat_mul]
    congr 1
    ring
  · rintro ⟨i, _, H⟩
    rw [← H]; rw [← exp_nat_mul]; rw [exp_eq_one_iff]
    use i
    simp [field]

/--
theorem `card_rootsOfUnity` / 定理 `card_rootsOfUnity`

English:
theorem card_rootsOfUnity
  given: (n : Nat) [NeZero n]
  statement: Nat.card (rootsOfUnity n Complex) = n
  proof: (isPrimitiveRoot_exp n NeZero.out).card_rootsOfUnity

中文:
定理 card_rootsOfUnity
  条件: (n : 自然数) [NeZero n]
  结论: 自然数.card (rootsOfUnity n 复形) = n
  证明: (isPrimitiveRoot_exp n NeZero.out).card_rootsOfUnity

Depends on / 依赖: NeZero, NeZero.out, card_rootsOfUnity, isPrimitiveRoot_exp
-/
theorem card_rootsOfUnity (n : Nat) [NeZero n] : Nat.card (rootsOfUnity n Complex) = n :=
  (isPrimitiveRoot_exp n NeZero.out).card_rootsOfUnity

/--
theorem `card_primitiveRoots` / 定理 `card_primitiveRoots`

English:
theorem card_primitiveRoots
  given: (k : Nat)
  statement: (primitiveRoots k Complex).card = φ k
  proof: by
  by_cases h : k = 0
  · simp [h]
  exact (isPrimitiveRoot_exp k h).card_primitiveRoots

中文:
定理 card_primitiveRoots
  条件: (k : 自然数)
  结论: (primitiveRoots k 复形).card = φ k
  证明: by
  by_cases h : k = 0
  · simp [h]
  exact (isPrimitiveRoot_exp k h).card_primitiveRoots

Depends on / 依赖: card_primitiveRoots, isPrimitiveRoot_exp
-/
theorem card_primitiveRoots (k : Nat) : (primitiveRoots k Complex).card = φ k := by
  by_cases h : k = 0
  · simp [h]
  exact (isPrimitiveRoot_exp k h).card_primitiveRoots

end Complex

/--
theorem `IsPrimitiveRoot.norm'_eq_one` / 定理 `IsPrimitiveRoot.norm'_eq_one`

English:
theorem IsPrimitiveRoot.norm'_eq_one
  given: {ζ : Complex} {n : Nat} (h : IsPrimitiveRoot ζ n) (hn : n != 0)
  proof: Complex.norm_eq_one_of_pow_eq_one h.pow_eq_one hn

中文:
定理 是PrimitiveRoot.norm'_eq_one
  条件: {ζ : 复形} {n : 自然数} (h : 是PrimitiveRoot ζ n) (hn : n != 0)
  证明: Complex.norm_eq_one_of_pow_eq_one h.pow_eq_one hn

Depends on / 依赖: Complex.norm_eq_one_of_pow_eq_one, h.pow_eq_one, norm_eq_one_of_pow_eq_one, pow_eq_one
-/
theorem IsPrimitiveRoot.norm'_eq_one {ζ : Complex} {n : Nat} (h : IsPrimitiveRoot ζ n) (hn : n != 0) :
    ‖ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one h.pow_eq_one hn

/--
theorem `IsPrimitiveRoot.nnnorm_eq_one` / 定理 `IsPrimitiveRoot.nnnorm_eq_one`

English:
theorem IsPrimitiveRoot.nnnorm_eq_one
  given: {ζ : Complex} {n : Nat} (h : IsPrimitiveRoot ζ n) (hn : n != 0)
  proof: Subtype.ext h.norm'_eq_one hn

中文:
定理 是PrimitiveRoot.nnnorm_eq_one
  条件: {ζ : 复形} {n : 自然数} (h : 是PrimitiveRoot ζ n) (hn : n != 0)
  证明: Subtype.ext h.norm'_eq_one hn

Depends on / 依赖: Subtype, Subtype.ext, _eq_one, h.norm
-/
theorem IsPrimitiveRoot.nnnorm_eq_one {ζ : Complex} {n : Nat} (h : IsPrimitiveRoot ζ n) (hn : n != 0) :
    ‖ζ‖₊ = 1 :=
Subtype.ext h.norm'_eq_one hn

/--
theorem `IsPrimitiveRoot.arg_ext` / 定理 `IsPrimitiveRoot.arg_ext`

English:
theorem IsPrimitiveRoot.arg_ext
  statement: {n m : Nat} {ζ μ : Complex} (hζ : IsPrimitiveRoot ζ n)
  proof: Complex.ext_norm_arg ((hζ.norm'_eq_one hn).trans (hμ.norm'_eq_one hm).symm) h

中文:
定理 是PrimitiveRoot.arg_ext
  结论: {n m : 自然数} {ζ μ : 复形} (hζ : 是PrimitiveRoot ζ n)
  证明: Complex.ext_norm_arg ((hζ.norm'_eq_one hn).trans (hμ.norm'_eq_one hm).symm) h

Depends on / 依赖: Complex.ext_norm_arg, _eq_one, ext_norm_arg
-/
theorem IsPrimitiveRoot.arg_ext {n m : Nat} {ζ μ : Complex} (hζ : IsPrimitiveRoot ζ n)
    (hμ : IsPrimitiveRoot μ m) (hn : n != 0) (hm : m != 0) (h : ζ.arg = μ.arg) : ζ = μ :=
  Complex.ext_norm_arg ((hζ.norm'_eq_one hn).trans (hμ.norm'_eq_one hm).symm) h

/--
theorem `IsPrimitiveRoot.arg_eq_zero_iff` / 定理 `IsPrimitiveRoot.arg_eq_zero_iff`

English:
theorem IsPrimitiveRoot.arg_eq_zero_iff
  given: {n : Nat} {ζ : Complex} (hζ : IsPrimitiveRoot ζ n) (hn : n != 0)
  proof: ⟨fun h => hζ.arg_ext IsPrimitiveRoot.one hn one_ne_zero (h.trans Complex.arg_one.symm), fun h =>
    h.symm ▸ Complex.arg_one⟩

中文:
定理 是PrimitiveRoot.arg_eq_zero_iff
  条件: {n : 自然数} {ζ : 复形} (hζ : 是PrimitiveRoot ζ n) (hn : n != 0)
  证明: ⟨fun h => hζ.arg_ext IsPrimitiveRoot.one hn one_ne_zero (h.trans Complex.arg_one.symm), fun h =>
    h.symm ▸ Complex.arg_one⟩

Depends on / 依赖: Complex.arg_one, Complex.arg_one.symm, IsPrimitiveRoot, IsPrimitiveRoot.one, arg_ext, arg_one, h.symm, h.trans, one_ne_zero
-/
theorem IsPrimitiveRoot.arg_eq_zero_iff {n : Nat} {ζ : Complex} (hζ : IsPrimitiveRoot ζ n) (hn : n != 0) :
    ζ.arg = 0 ↔ ζ = 1 :=
  ⟨fun h => hζ.arg_ext IsPrimitiveRoot.one hn one_ne_zero (h.trans Complex.arg_one.symm), fun h =>
    h.symm ▸ Complex.arg_one⟩

/--
theorem `IsPrimitiveRoot.arg_eq_pi_iff` / 定理 `IsPrimitiveRoot.arg_eq_pi_iff`

English:
theorem IsPrimitiveRoot.arg_eq_pi_iff
  given: {n : Nat} {ζ : Complex} (hζ : IsPrimitiveRoot ζ n) (hn : n != 0)
  proof: ⟨fun h =>
    hζ.arg_ext (IsPrimitiveRoot.neg_one 0 two_ne_zero.symm) hn two_ne_zero
      (h.trans Complex.arg_neg_one.symm),
    fun h => h.symm ▸ Complex.arg_neg_one⟩

中文:
定理 是PrimitiveRoot.arg_eq_pi_iff
  条件: {n : 自然数} {ζ : 复形} (hζ : 是PrimitiveRoot ζ n) (hn : n != 0)
  证明: ⟨fun h =>
    hζ.arg_ext (IsPrimitiveRoot.neg_one 0 two_ne_zero.symm) hn two_ne_zero
      (h.trans Complex.arg_neg_one.symm),
    fun h => h.symm ▸ Complex.arg_neg_one⟩

Depends on / 依赖: Complex.arg_neg_one, Complex.arg_neg_one.symm, IsPrimitiveRoot, IsPrimitiveRoot.neg_one, arg_ext, arg_neg_one, h.symm, h.trans, neg_one, two_ne_zero, two_ne_zero.symm
-/
theorem IsPrimitiveRoot.arg_eq_pi_iff {n : Nat} {ζ : Complex} (hζ : IsPrimitiveRoot ζ n) (hn : n != 0) :
    ζ.arg = Real.pi ↔ ζ = -1 :=
  ⟨fun h =>
    hζ.arg_ext (IsPrimitiveRoot.neg_one 0 two_ne_zero.symm) hn two_ne_zero
      (h.trans Complex.arg_neg_one.symm),
    fun h => h.symm ▸ Complex.arg_neg_one⟩

/--
theorem `IsPrimitiveRoot.arg` / 定理 `IsPrimitiveRoot.arg`

English:
theorem IsPrimitiveRoot.arg
  given: {n : Nat} {ζ : Complex} (h : IsPrimitiveRoot ζ n) (hn : n != 0)
  proof: by
  rw [Complex.isPrimitiveRoot_iff _ _ hn] at h
  obtain ⟨i, h, hin, rfl⟩ := h
  rw [mul_comm]; rw [← mul_assoc]; rw [Complex.exp_mul_I]
  refine ⟨if i * 2 <= n then i else i - n, ?_, ?isCoprime, by lia⟩
  case isCoprime =>
    replace hin := Nat.isCoprime_iff_coprime.mpr hin
    split_ifs
    · exact hin
    · convert! hin.add_mul_left_left (-1) using 1
      rw [mul_neg_one]; rw [sub_eq_add_neg]
  split_ifs with h₂
  · convert! Complex.arg_cos_add_sin_mul_I _
    · push_cast; rfl
    · push_cast; rfl
    simp only [Int.cast_natCast, Set.mem_Ioc]
    refine ⟨(neg_lt_neg Real.pi_pos).trans_le ?_, ?_⟩
    · rw [neg_zero]
      positivity
    refine Eq.trans_le (b := Real.pi * (i * 2 / n)) (by ring) ?_
    rw [← mul_one n] at h₂
    exact mul_le_of_le_one_right Real.pi_pos.le
      ((div_le_iff₀' <| mod_cast pos_of_gt h).mpr <| mod_cast h₂)
  rw [← Complex.cos_sub_two_pi]; rw [← Complex.sin_sub_two_pi]
  convert! Complex.arg_cos_add_sin_mul_I _
  · push_cast
    rw [← sub_one_mul]; rw [sub_div]; rw [div_self]
    exact mod_cast hn
  · push_cast
    rw [← sub_one_mul]; rw [sub_div]; rw [div_self]
    exact mod_cast hn
  simp only [Int.cast_sub, Int.cast_natCast, Set.mem_Ioc]
  field_simp
  constructor
  · push Not at h₂
    rify at h₂
    linear_combination h₂
  · rify at h
    linear_combination 2 * h + (n : Real) * one_pos (α := Real)

中文:
定理 是PrimitiveRoot.arg
  条件: {n : 自然数} {ζ : 复形} (h : 是PrimitiveRoot ζ n) (hn : n != 0)
  证明: by
  rw [Complex.isPrimitiveRoot_iff _ _ hn] at h
  obtain ⟨i, h, hin, rfl⟩ := h
  rw [mul_comm]; rw [← mul_assoc]; rw [Complex.exp_mul_I]
  refine ⟨if i * 2 <= n then i else i - n, ?_, ?isCoprime, by lia⟩
  case isCoprime =>
    replace hin := Nat.isCoprime_iff_coprime.mpr hin
    split_ifs
    · exact hin
    · convert! hin.add_mul_left_left (-1) using 1
      rw [mul_neg_one]; rw [sub_eq_add_neg]
  split_ifs with h₂
  · convert! Complex.arg_cos_add_sin_mul_I _
    · push_cast; rfl
    · push_cast; rfl
    simp only [Int.cast_natCast, Set.mem_Ioc]
    refine ⟨(neg_lt_neg Real.pi_pos).trans_le ?_, ?_⟩
    · rw [neg_zero]
      positivity
    refine Eq.trans_le (b := Real.pi * (i * 2 / n)) (by ring) ?_
    rw [← mul_one n] at h₂
    exact mul_le_of_le_one_right Real.pi_pos.le
      ((div_le_iff₀' <| mod_cast pos_of_gt h).mpr <| mod_cast h₂)
  rw [← Complex.cos_sub_two_pi]; rw [← Complex.sin_sub_two_pi]
  convert! Complex.arg_cos_add_sin_mul_I _
  · push_cast
    rw [← sub_one_mul]; rw [sub_div]; rw [div_self]
    exact mod_cast hn
  · push_cast
    rw [← sub_one_mul]; rw [sub_div]; rw [div_self]
    exact mod_cast hn
  simp only [Int.cast_sub, Int.cast_natCast, Set.mem_Ioc]
  field_simp
  constructor
  · push Not at h₂
    rify at h₂
    linear_combination h₂
  · rify at h
    linear_combination 2 * h + (n : Real) * one_pos (α := Real)

Depends on / 依赖: Complex.arg_cos_add_sin_mul_I, Complex.exp_mul_I, Complex.isPrimitiveRoot_iff, Int.cast_natCast, Nat.isCoprime_iff_coprime.mpr, Set.m, add_mul_left_left, arg_cos_add_sin_mul_I, cast_natCast, convert, exp_mul_I, hin.add_mul_left_left, isCoprime, isCoprime_iff_coprime, isPrimitiveRoot_iff, mul_assoc, mul_comm, mul_neg_one, replace, split_ifs
-/
theorem IsPrimitiveRoot.arg {n : Nat} {ζ : Complex} (h : IsPrimitiveRoot ζ n) (hn : n != 0) :
    exists i : Int, ζ.arg = i / n * (2 * Real.pi) ∧ IsCoprime i n ∧ i.natAbs < n := by
  rw [Complex.isPrimitiveRoot_iff _ _ hn] at h
  obtain ⟨i, h, hin, rfl⟩ := h
  rw [mul_comm]; rw [← mul_assoc]; rw [Complex.exp_mul_I]
  refine ⟨if i * 2 <= n then i else i - n, ?_, ?isCoprime, by lia⟩
  case isCoprime =>
    replace hin := Nat.isCoprime_iff_coprime.mpr hin
    split_ifs
    · exact hin
    · convert! hin.add_mul_left_left (-1) using 1
      rw [mul_neg_one]; rw [sub_eq_add_neg]
  split_ifs with h₂
  · convert! Complex.arg_cos_add_sin_mul_I _
    · push_cast; rfl
    · push_cast; rfl
    simp only [Int.cast_natCast, Set.mem_Ioc]
    refine ⟨(neg_lt_neg Real.pi_pos).trans_le ?_, ?_⟩
    · rw [neg_zero]
      positivity
    refine Eq.trans_le (b := Real.pi * (i * 2 / n)) (by ring) ?_
    rw [← mul_one n] at h₂
    exact mul_le_of_le_one_right Real.pi_pos.le
      ((div_le_iff₀' <| mod_cast pos_of_gt h).mpr <| mod_cast h₂)
  rw [← Complex.cos_sub_two_pi]; rw [← Complex.sin_sub_two_pi]
  convert! Complex.arg_cos_add_sin_mul_I _
  · push_cast
    rw [← sub_one_mul]; rw [sub_div]; rw [div_self]
    exact mod_cast hn
  · push_cast
    rw [← sub_one_mul]; rw [sub_div]; rw [div_self]
    exact mod_cast hn
  simp only [Int.cast_sub, Int.cast_natCast, Set.mem_Ioc]
  field_simp
  constructor
  · push Not at h₂
    rify at h₂
    linear_combination h₂
  · rify at h
    linear_combination 2 * h + (n : Real) * one_pos (α := Real)

/--
lemma `Complex.norm_eq_one_of_mem_rootsOfUnity` / 引理 `Complex.norm_eq_one_of_mem_rootsOfUnity`

English:
lemma Complex.norm_eq_one_of_mem_rootsOfUnity
  statement: {ζ : Complexˣ} {n : Nat} [NeZero n]
  proof: by
refine norm_eq_one_of_pow_eq_one ?_ NeZero.ne n
  norm_cast
  rw [_root_.mem_rootsOfUnity] at hζ
  rw [hζ]; rw [Units.val_one]

中文:
引理 复形.norm_eq_one_of_mem_rootsOfUnity
  结论: {ζ : Complexˣ} {n : 自然数} [NeZero n]
  证明: by
refine norm_eq_one_of_pow_eq_one ?_ NeZero.ne n
  norm_cast
  rw [_root_.mem_rootsOfUnity] at hζ
  rw [hζ]; rw [Units.val_one]

Depends on / 依赖: NeZero, NeZero.ne, Units.val_one, _root_, _root_.mem_rootsOfUnity, mem_rootsOfUnity, norm_eq_one_of_pow_eq_one, val_one
-/
lemma Complex.norm_eq_one_of_mem_rootsOfUnity {ζ : Complexˣ} {n : Nat} [NeZero n]
    (hζ : ζ in rootsOfUnity n Complex) :
    ‖(ζ : Complex)‖ = 1 := by
refine norm_eq_one_of_pow_eq_one ?_ NeZero.ne n
  norm_cast
  rw [_root_.mem_rootsOfUnity] at hζ
  rw [hζ]; rw [Units.val_one]

/--
theorem `Complex.conj_rootsOfUnity` / 定理 `Complex.conj_rootsOfUnity`

English:
theorem Complex.conj_rootsOfUnity
  given: {ζ : Complexˣ} {n : Nat} [NeZero n] (hζ : ζ in rootsOfUnity n Complex)
  proof: by
  rw [← Units.mul_eq_one_iff_eq_inv]; rw [conj_mul']; rw [norm_eq_one_of_mem_rootsOfUnity hζ]; rw [ofReal_one]; rw [one_pow]

中文:
定理 复形.conj_rootsOfUnity
  条件: {ζ : Complexˣ} {n : 自然数} [NeZero n] (hζ : ζ in rootsOfUnity n 复形)
  证明: by
  rw [← Units.mul_eq_one_iff_eq_inv]; rw [conj_mul']; rw [norm_eq_one_of_mem_rootsOfUnity hζ]; rw [ofReal_one]; rw [one_pow]

Depends on / 依赖: Units.mul_eq_one_iff_eq_inv, conj_mul, mul_eq_one_iff_eq_inv, norm_eq_one_of_mem_rootsOfUnity, ofReal_one, one_pow
-/
theorem Complex.conj_rootsOfUnity {ζ : Complexˣ} {n : Nat} [NeZero n] (hζ : ζ in rootsOfUnity n Complex) :
    (starRingEnd Complex) ζ = ζ⁻¹ := by
  rw [← Units.mul_eq_one_iff_eq_inv]; rw [conj_mul']; rw [norm_eq_one_of_mem_rootsOfUnity hζ]; rw [ofReal_one]; rw [one_pow]
