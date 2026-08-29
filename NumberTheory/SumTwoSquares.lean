/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Sums of two squares

Fermat's theorem on the sum of two squares. Every prime `p` congruent to 1 mod 4 is the
sum of two squares; see `Nat.Prime.sq_add_sq` (which has the weaker assumption `p % 4 ≠ 3`).

We also give the result that characterizes the (positive) natural numbers that are sums
of two squares as those numbers `n` such that for every prime `q` congruent to 3 mod 4, the
exponent of the largest power of `q` dividing `n` is even; see `Nat.eq_sq_add_sq_iff`.

There is an alternative characterization as the numbers of the form `a^2 * b`, where `b` is a
natural number such that `-1` is a square modulo `b`; see `Nat.eq_sq_add_sq_iff_eq_sq_mul`.
-/

public section


section Fermat

open GaussianInt

/--
theorem `Nat.Prime.sq_add_sq` / 定理 `Nat.Prime.sq_add_sq`

English:
theorem Nat.Prime.sq_add_sq
  given: {p : Nat} [Fact p.Prime] (hp : p % 4 != 3)
  proof: by
  apply sq_add_sq_of_nat_prime_of_not_irreducible p
  rwa [_root_.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p]

中文:
定理 Nat.Prime.sq_add_sq
  条件: {p : 自然数} [Fact p.Prime] (hp : p % 4 != 3)
  证明: by
  apply sq_add_sq_of_nat_prime_of_not_irreducible p
  rwa [_root_.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p]

Depends on / 依赖: _root_, _root_.irreducible_iff_prime, irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime, sq_add_sq_of_nat_prime_of_not_irreducible
-/
theorem Nat.Prime.sq_add_sq {p : Nat} [Fact p.Prime] (hp : p % 4 != 3) :
    exists a b : Nat, a ^ 2 + b ^ 2 = p := by
  apply sq_add_sq_of_nat_prime_of_not_irreducible p
  rwa [_root_.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p]

end Fermat

/-!
### Generalities on sums of two squares
-/


section General

/--
theorem `sq_add_sq_mul` / 定理 `sq_add_sq_mul`

English:
theorem sq_add_sq_mul
  statement: {R} [CommRing R] {a b x y u v : R} (ha : a = x ^ 2 + y ^ 2)
  proof: ⟨x * u - y * v, x * v + y * u, by rw [ha, hb]; ring⟩

中文:
定理 sq_add_sq_mul
  结论: {R} [CommRing R] {a b x y u v : R} (ha : a = x ^ 2 + y ^ 2)
  证明: ⟨x * u - y * v, x * v + y * u, by rw [ha, hb]; ring⟩
-/
theorem sq_add_sq_mul {R} [CommRing R] {a b x y u v : R} (ha : a = x ^ 2 + y ^ 2)
    (hb : b = u ^ 2 + v ^ 2) : exists r s : R, a * b = r ^ 2 + s ^ 2 :=
  ⟨x * u - y * v, x * v + y * u, by rw [ha, hb]; ring⟩

/--
theorem `Nat.sq_add_sq_mul` / 定理 `Nat.sq_add_sq_mul`

English:
theorem Nat.sq_add_sq_mul
  given: {a b x y u v : Nat} (ha : a = x ^ 2 + y ^ 2) (hb : b = u ^ 2 + v ^ 2)
  proof: by
  zify at ha hb ⊢
  obtain ⟨r, s, h⟩ := _root_.sq_add_sq_mul ha hb
  refine ⟨r.natAbs, s.natAbs, ?_⟩
  simpa only [Int.natCast_natAbs, sq_abs]

中文:
定理 Nat.sq_add_sq_mul
  条件: {a b x y u v : 自然数} (ha : a = x ^ 2 + y ^ 2) (hb : b = u ^ 2 + v ^ 2)
  证明: by
  zify at ha hb ⊢
  obtain ⟨r, s, h⟩ := _root_.sq_add_sq_mul ha hb
  refine ⟨r.natAbs, s.natAbs, ?_⟩
  simpa only [Int.natCast_natAbs, sq_abs]

Depends on / 依赖: Int.natCast_natAbs, _root_, _root_.sq_add_sq_mul, natAbs, natCast_natAbs, r.natAbs, s.natAbs, sq_abs, sq_add_sq_mul
-/
theorem Nat.sq_add_sq_mul {a b x y u v : Nat} (ha : a = x ^ 2 + y ^ 2) (hb : b = u ^ 2 + v ^ 2) :
    exists r s : Nat, a * b = r ^ 2 + s ^ 2 := by
  zify at ha hb ⊢
  obtain ⟨r, s, h⟩ := _root_.sq_add_sq_mul ha hb
  refine ⟨r.natAbs, s.natAbs, ?_⟩
  simpa only [Int.natCast_natAbs, sq_abs]

end General

/-!
### Results on when -1 is a square modulo a natural number
-/


section NegOneSquare

-- This could be formulated for a general integer `a` in place of `-1`,
-- but it would not directly specialize to `-1`,
-- because `((-1 : ℤ) : ZMod n)` is not the same as `(-1 : ZMod n)`.
/--
theorem `ZMod.isSquare_neg_one_of_dvd` / 定理 `ZMod.isSquare_neg_one_of_dvd`

English:
theorem ZMod.isSquare_neg_one_of_dvd
  given: {m n : Nat} (hd : m ∣ n) (hs : IsSquare (-1 : ZMod n))
  proof: by
  let f : ZMod n ->+* ZMod m := ZMod.castHom hd _
  rw [← map_one f]; rw [← map_neg]
  exact hs.map f

中文:
定理 ZMod.isSquare_neg_one_of_dvd
  条件: {m n : 自然数} (hd : m ∣ n) (hs : IsSquare (-1 : ZMod n))
  证明: by
  let f : ZMod n ->+* ZMod m := ZMod.castHom hd _
  rw [← map_one f]; rw [← map_neg]
  exact hs.map f

Depends on / 依赖: ZMod.castHom, castHom, hs.map, map_neg, map_one
-/
theorem ZMod.isSquare_neg_one_of_dvd {m n : Nat} (hd : m ∣ n) (hs : IsSquare (-1 : ZMod n)) :
    IsSquare (-1 : ZMod m) := by
  let f : ZMod n ->+* ZMod m := ZMod.castHom hd _
  rw [← map_one f]; rw [← map_neg]
  exact hs.map f

/--
theorem `ZMod.isSquare_neg_one_mul` / 定理 `ZMod.isSquare_neg_one_mul`

English:
theorem ZMod.isSquare_neg_one_mul
  statement: {m n : Nat} (hc : m.Coprime n) (hm : IsSquare (-1 : ZMod m))
  proof: by
  have : IsSquare (-1 : ZMod m × ZMod n) := by
    rw [show (-1 : ZMod m × ZMod n) = ((-1 : ZMod m)]; rw [(-1 : ZMod n)) from rfl]
    obtain ⟨x, hx⟩ := hm
    obtain ⟨y, hy⟩ := hn
    rw [hx]; rw [hy]
    exact ⟨(x, y), rfl⟩
  simpa only [RingEquiv.map_neg_one] using this.map (ZMod.chineseRemain

中文:
定理 ZMod.isSquare_neg_one_mul
  结论: {m n : 自然数} (hc : m.Coprime n) (hm : IsSquare (-1 : ZMod m))
  证明: by
  have : IsSquare (-1 : ZMod m × ZMod n) := by
    rw [show (-1 : ZMod m × ZMod n) = ((-1 : ZMod m)]; rw [(-1 : ZMod n)) from rfl]
    obtain ⟨x, hx⟩ := hm
    obtain ⟨y, hy⟩ := hn
    rw [hx]; rw [hy]
    exact ⟨(x, y), rfl⟩
  simpa only [RingEquiv.map_neg_one] using this.map (ZMod.chineseRemain

Depends on / 依赖: IsSquare, RingEquiv, RingEquiv.map_neg_one, ZMod.chineseRemainder, chineseRemainder, map_neg_one, this.map
-/
theorem ZMod.isSquare_neg_one_mul {m n : Nat} (hc : m.Coprime n) (hm : IsSquare (-1 : ZMod m))
    (hn : IsSquare (-1 : ZMod n)) : IsSquare (-1 : ZMod (m * n)) := by
  have : IsSquare (-1 : ZMod m × ZMod n) := by
    rw [show (-1 : ZMod m × ZMod n) = ((-1 : ZMod m)]; rw [(-1 : ZMod n)) from rfl]
    obtain ⟨x, hx⟩ := hm
    obtain ⟨y, hy⟩ := hn
    rw [hx]; rw [hy]
    exact ⟨(x, y), rfl⟩
  simpa only [RingEquiv.map_neg_one] using this.map (ZMod.chineseRemainder hc).symm

/--
theorem `Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one` / 定理 `Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one`

English:
theorem Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one
  statement: {p n : Nat}
  proof: by
  obtain ⟨y, h⟩ := ZMod.isSquare_neg_one_of_dvd (Nat.dvd_of_mem_primeFactors hp) hs
  rw [← sq]; rw [eq_comm]; rw [show (-1 : ZMod p) = -1 ^ 2 by ring] at h
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' one_ne_zero h

中文:
定理 Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one
  结论: {p n : 自然数}
  证明: by
  obtain ⟨y, h⟩ := ZMod.isSquare_neg_one_of_dvd (Nat.dvd_of_mem_primeFactors hp) hs
  rw [← sq]; rw [eq_comm]; rw [show (-1 : ZMod p) = -1 ^ 2 by ring] at h
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' one_ne_zero h

Depends on / 依赖: Nat.dvd_of_mem_primeFactors, Nat.prime_of_mem_primeFactors, ZMod.isSquare_neg_one_of_dvd, ZMod.mod_four_ne_three_of_sq_eq_neg_sq, dvd_of_mem_primeFactors, eq_comm, isSquare_neg_one_of_dvd, mod_four_ne_three_of_sq_eq_neg_sq, one_ne_zero, p.Prime, prime_of_mem_primeFactors
-/
theorem Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one {p n : Nat}
    (hp : p in n.primeFactors) (hs : IsSquare (-1 : ZMod n)) : p % 4 != 3 := by
  obtain ⟨y, h⟩ := ZMod.isSquare_neg_one_of_dvd (Nat.dvd_of_mem_primeFactors hp) hs
  rw [← sq]; rw [eq_comm]; rw [show (-1 : ZMod p) = -1 ^ 2 by ring] at h
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' one_ne_zero h

/--
theorem `ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three` / 定理 `ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three`

English:
theorem ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three
  statement: {n : Nat}
  proof: by
  refine ⟨fun H q hq => Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hq H,
    fun H => ?_⟩
  induction n using induction_on_primes with
  | zero => exact False.elim (hn.ne_zero rfl)
  | one => exact ⟨0, by simp only [mul_zero, eq_iff_true_of_subsingleton]⟩
  | prime_mul p n hpp 

中文:
定理 ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three
  结论: {n : 自然数}
  证明: by
  refine ⟨fun H q hq => Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hq H,
    fun H => ?_⟩
  induction n using induction_on_primes with
  | zero => exact False.elim (hn.ne_zero rfl)
  | one => exact ⟨0, by simp only [mul_zero, eq_iff_true_of_subsingleton]⟩
  | prime_mul p n hpp 

Depends on / 依赖: Coprime, False.elim, Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one, ZMod.exists_sq_eq_neg_one_iff.mpr, dvd_iff_not_coprime, eq_iff_true_of_subsingleton, exists_sq_eq_neg_one_iff, hn.ne_zero, hpp.dvd_iff_not_coprime.mpr, hpp.not_isUnit, induction_on_primes, mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one, mul_dvd_mul_left, mul_zero, ne_zero, not_isUnit, p.Coprime, p.Prime, prime_mul
-/
theorem ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three {n : Nat}
    (hn : Squarefree n) : IsSquare (-1 : ZMod n) ↔ forall q in n.primeFactors, q % 4 != 3 := by
  refine ⟨fun H q hq => Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hq H,
    fun H => ?_⟩
  induction n using induction_on_primes with
  | zero => exact False.elim (hn.ne_zero rfl)
  | one => exact ⟨0, by simp only [mul_zero, eq_iff_true_of_subsingleton]⟩
  | prime_mul p n hpp ih =>
    have : Fact p.Prime := ⟨hpp⟩
    have hcp : p.Coprime n := by
      by_contra hc
      exact hpp.not_isUnit (hn p <| mul_dvd_mul_left p <| hpp.dvd_iff_not_coprime.mpr hc)
have hp₁ := ZMod.exists_sq_eq_neg_one_iff.mpr H _
      Nat.mem_primeFactors.mpr ⟨hpp, Nat.dvd_mul_right .., Squarefree.ne_zero hn⟩
exact ZMod.isSquare_neg_one_mul hcp hp₁ ih hn.of_mul_right fun q hqp => H q
        Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hqp,
          dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hqp) _, Squarefree.ne_zero hn⟩

/--
theorem `ZMod.isSquare_neg_one_iff'` / 定理 `ZMod.isSquare_neg_one_iff'`

English:
theorem ZMod.isSquare_neg_one_iff'
  given: {n : Nat} (hn : Squarefree n)
  proof: by
  have help : forall a b : ZMod 4, a != 3 -> b != 3 -> a * b != 3 := by decide
  rw [ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three hn]
refine ⟨?_, fun H q hq => H Nat.dvd_of_mem_primeFactors hq⟩
  intro H
  refine @induction_on_primes _ ?_ ?_ (fun p q hp hq hpq => ?_)
  · ex

中文:
定理 ZMod.isSquare_neg_one_iff'
  条件: {n : 自然数} (hn : Squarefree n)
  证明: by
  have help : forall a b : ZMod 4, a != 3 -> b != 3 -> a * b != 3 := by decide
  rw [ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three hn]
refine ⟨?_, fun H q hq => H Nat.dvd_of_mem_primeFactors hq⟩
  intro H
  refine @induction_on_primes _ ?_ ?_ (fun p q hp hq hpq => ?_)
  · ex

Depends on / 依赖: Nat.dvd_of_mem_primeFactors, Nat.mem_primeFactors.mpr, Squarefree, Squarefree.ne_zero, ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three, dvd_of_mem_primeFactors, dvd_of_mul_left_dvd, dvd_of_mul_right_dvd, induction_on_primes, isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three, mem_primeFactors, ne_zero, replace
-/
theorem ZMod.isSquare_neg_one_iff' {n : Nat} (hn : Squarefree n) :
    IsSquare (-1 : ZMod n) ↔ forall {q : Nat}, q ∣ n -> q % 4 != 3 := by
  have help : forall a b : ZMod 4, a != 3 -> b != 3 -> a * b != 3 := by decide
  rw [ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three hn]
refine ⟨?_, fun H q hq => H Nat.dvd_of_mem_primeFactors hq⟩
  intro H
  refine @induction_on_primes _ ?_ ?_ (fun p q hp hq hpq => ?_)
  · exact fun _ => by simp
  · exact fun _ => by simp
· replace hp := H _
      Nat.mem_primeFactors.mpr ⟨hp, dvd_of_mul_right_dvd hpq, Squarefree.ne_zero hn⟩
    replace hq := hq (dvd_of_mul_left_dvd hpq)
    rw [show 3 = 3 % 4 by simp]; rw [Ne]; rw [← ZMod.natCast_eq_natCast_iff'] at hp hq ⊢
    rw [Nat.cast_mul]
    exact help p q hp hq

/-!
### Relation to sums of two squares
-/


/--
theorem `Nat.eq_sq_add_sq_of_isSquare_mod_neg_one` / 定理 `Nat.eq_sq_add_sq_of_isSquare_mod_neg_one`

English:
theorem Nat.eq_sq_add_sq_of_isSquare_mod_neg_one
  given: {n : Nat} (h : IsSquare (-1 : ZMod n))
  proof: by
  induction n using induction_on_primes with
  | zero => exact ⟨0, 0, rfl⟩
  | one => exact ⟨0, 1, rfl⟩
  | prime_mul p n hpp ih =>
    have : Fact p.Prime := ⟨hpp⟩
    have hp : IsSquare (-1 : ZMod p) := ZMod.isSquare_neg_one_of_dvd ⟨n, rfl⟩ h
    obtain ⟨u, v, huv⟩ := Nat.Prime.sq_add_sq (ZMod.

中文:
定理 Nat.eq_sq_add_sq_of_isSquare_mod_neg_one
  条件: {n : 自然数} (h : IsSquare (-1 : ZMod n))
  证明: by
  induction n using induction_on_primes with
  | zero => exact ⟨0, 0, rfl⟩
  | one => exact ⟨0, 1, rfl⟩
  | prime_mul p n hpp ih =>
    have : Fact p.Prime := ⟨hpp⟩
    have hp : IsSquare (-1 : ZMod p) := ZMod.isSquare_neg_one_of_dvd ⟨n, rfl⟩ h
    obtain ⟨u, v, huv⟩ := Nat.Prime.sq_add_sq (ZMod.

Depends on / 依赖: IsSquare, Nat.Prime.sq_add_sq, Nat.sq_add_sq_mul, ZMod.exists_sq_eq_neg_one_iff.mp, ZMod.isSquare_neg_one_of_dvd, exists_sq_eq_neg_one_iff, huv.symm, induction_on_primes, isSquare_neg_one_of_dvd, mul_comm, p.Prime, prime_mul, sq_add_sq, sq_add_sq_mul
-/
theorem Nat.eq_sq_add_sq_of_isSquare_mod_neg_one {n : Nat} (h : IsSquare (-1 : ZMod n)) :
    exists x y : Nat, n = x ^ 2 + y ^ 2 := by
  induction n using induction_on_primes with
  | zero => exact ⟨0, 0, rfl⟩
  | one => exact ⟨0, 1, rfl⟩
  | prime_mul p n hpp ih =>
    have : Fact p.Prime := ⟨hpp⟩
    have hp : IsSquare (-1 : ZMod p) := ZMod.isSquare_neg_one_of_dvd ⟨n, rfl⟩ h
    obtain ⟨u, v, huv⟩ := Nat.Prime.sq_add_sq (ZMod.exists_sq_eq_neg_one_iff.mp hp)
    obtain ⟨x, y, hxy⟩ := ih (ZMod.isSquare_neg_one_of_dvd ⟨p, mul_comm _ _⟩ h)
    exact Nat.sq_add_sq_mul huv.symm hxy

/--
theorem `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime` / 定理 `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime`

English:
theorem ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime
  statement: {n x y : Int} (h : n = x ^ 2 + y ^ 2)
  proof: by
  obtain ⟨u, v, huv⟩ : IsCoprime x n := by
    have hc2 : IsCoprime (x ^ 2) (y ^ 2) := hc.pow
    rw [show y ^ 2 = n + -1 * x ^ 2 by lia] at hc2
    exact (IsCoprime.pow_left_iff zero_lt_two).mp hc2.of_add_mul_right_right
  have H : u * y * (u * y) - -1 = n * (-v ^ 2 * n + u ^ 2 + 2 * v) := by
  

中文:
定理 ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime
  结论: {n x y : 整数} (h : n = x ^ 2 + y ^ 2)
  证明: by
  obtain ⟨u, v, huv⟩ : IsCoprime x n := by
    have hc2 : IsCoprime (x ^ 2) (y ^ 2) := hc.pow
    rw [show y ^ 2 = n + -1 * x ^ 2 by lia] at hc2
    exact (IsCoprime.pow_left_iff zero_lt_two).mp hc2.of_add_mul_right_right
  have H : u * y * (u * y) - -1 = n * (-v ^ 2 * n + u ^ 2 + 2 * v) := by
  

Depends on / 依赖: IsCoprime, IsCoprime.pow_left_iff, ZMod.intCast_eq_intCast_iff_dvd_sub, conv_rhs, hc.pow, hc2.of_add_mul_right_right, intCast_eq_intCast_iff_dvd_sub, linear_combination, n.natAbs, natAbs, of_add_mul_right_right, pow_left_iff, tactic, zero_lt_two
-/
theorem ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime {n x y : Int} (h : n = x ^ 2 + y ^ 2)
    (hc : IsCoprime x y) : IsSquare (-1 : ZMod n.natAbs) := by
  obtain ⟨u, v, huv⟩ : IsCoprime x n := by
    have hc2 : IsCoprime (x ^ 2) (y ^ 2) := hc.pow
    rw [show y ^ 2 = n + -1 * x ^ 2 by lia] at hc2
    exact (IsCoprime.pow_left_iff zero_lt_two).mp hc2.of_add_mul_right_right
  have H : u * y * (u * y) - -1 = n * (-v ^ 2 * n + u ^ 2 + 2 * v) := by
    linear_combination -u ^ 2 * h + (n * v - u * x - 1) * huv
  refine ⟨u * y, ?_⟩
  conv_rhs => tactic => norm_cast
  rw [(by norm_cast : (-1 : ZMod n.natAbs) = (-1 : Int))]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (Int.natAbs_dvd.mpr ⟨_, H⟩)

/--
theorem `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime` / 定理 `ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime`

English:
theorem ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime
  statement: {n x y : Nat} (h : n = x ^ 2 + y ^ 2)
  proof: by
  zify at h
  exact ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime h hc.isCoprime

中文:
定理 ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime
  结论: {n x y : 自然数} (h : n = x ^ 2 + y ^ 2)
  证明: by
  zify at h
  exact ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime h hc.isCoprime

Depends on / 依赖: ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime, hc.isCoprime, isCoprime, isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime
-/
theorem ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime {n x y : Nat} (h : n = x ^ 2 + y ^ 2)
    (hc : x.Coprime y) : IsSquare (-1 : ZMod n) := by
  zify at h
  exact ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime h hc.isCoprime

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Nat.eq_sq_add_sq_iff_eq_sq_mul` / 定理 `Nat.eq_sq_add_sq_iff_eq_sq_mul`

English:
theorem Nat.eq_sq_add_sq_iff_eq_sq_mul
  given: {n : Nat}
  proof: by
  constructor
  · rintro ⟨x, y, h⟩
    by_cases hxy : x = 0 ∧ y = 0
    · exact ⟨0, 1, by rw [h, hxy.1, hxy.2, zero_pow two_ne_zero, add_zero, zero_mul],
        ⟨0, by rw [zero_mul, neg_eq_zero, Fin.one_eq_zero_iff]⟩⟩
    · have hg := Nat.pos_of_ne_zero (mt Nat.gcd_eq_zero_iff.mp hxy)
      obta

中文:
定理 Nat.eq_sq_add_sq_iff_eq_sq_mul
  条件: {n : 自然数}
  证明: by
  constructor
  · rintro ⟨x, y, h⟩
    by_cases hxy : x = 0 ∧ y = 0
    · exact ⟨0, 1, by rw [h, hxy.1, hxy.2, zero_pow two_ne_zero, add_zero, zero_mul],
        ⟨0, by rw [zero_mul, neg_eq_zero, Fin.one_eq_zero_iff]⟩⟩
    · have hg := Nat.pos_of_ne_zero (mt Nat.gcd_eq_zero_iff.mp hxy)
      obta

Depends on / 依赖: Fin.one_eq_zero_iff, Nat.eq_sq_add_sq_of, Nat.exists_coprime, Nat.gcd_eq_zero_iff.mp, Nat.pos_of_ne_zero, ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime, add_zero, eq_sq_add_sq_of, exists_coprime, gcd_eq_zero_iff, isSquare_neg_one_of_eq_sq_add_sq_of_coprime, neg_eq_zero, one_eq_zero_iff, pos_of_ne_zero, two_ne_zero, zero_mul, zero_pow
-/
theorem Nat.eq_sq_add_sq_iff_eq_sq_mul {n : Nat} :
    (exists x y : Nat, n = x ^ 2 + y ^ 2) ↔ exists a b : Nat, n = a ^ 2 * b ∧ IsSquare (-1 : ZMod b) := by
  constructor
  · rintro ⟨x, y, h⟩
    by_cases hxy : x = 0 ∧ y = 0
    · exact ⟨0, 1, by rw [h, hxy.1, hxy.2, zero_pow two_ne_zero, add_zero, zero_mul],
        ⟨0, by rw [zero_mul, neg_eq_zero, Fin.one_eq_zero_iff]⟩⟩
    · have hg := Nat.pos_of_ne_zero (mt Nat.gcd_eq_zero_iff.mp hxy)
      obtain ⟨g, x₁, y₁, _, h₂, h₃, h₄⟩ := Nat.exists_coprime' hg
      exact ⟨g, x₁ ^ 2 + y₁ ^ 2, by rw [h, h₃, h₄]; ring,
        ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime rfl h₂⟩
  · rintro ⟨a, b, h₁, h₂⟩
    obtain ⟨x', y', h⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one h₂
    exact ⟨a * x', a * y', by rw [h₁, h]; ring⟩

end NegOneSquare

/-!
### Characterization in terms of the prime factorization
-/


section Main

/--
theorem `Nat.eq_sq_add_sq_iff` / 定理 `Nat.eq_sq_add_sq_iff`

English:
theorem Nat.eq_sq_add_sq_iff
  given: {n : Nat}
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hn₀)
  · exact ⟨fun _ q _ _ => (padicValNat_zero_right _).symm ▸ Even.zero, fun _ => ⟨0, 0, rfl⟩⟩
  -- now `0 < n`
  refine eq_sq_add_sq_iff_eq_sq_mul.trans ⟨fun ⟨a, b, h₁, h₂⟩ q hq h => ?_, fun H => ?_⟩
  · have : Fact q.Prime := ⟨prime_of_mem_primeFactors h

中文:
定理 Nat.eq_sq_add_sq_iff
  条件: {n : 自然数}
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hn₀)
  · exact ⟨fun _ q _ _ => (padicValNat_zero_right _).symm ▸ Even.zero, fun _ => ⟨0, 0, rfl⟩⟩
  -- now `0 < n`
  refine eq_sq_add_sq_iff_eq_sq_mul.trans ⟨fun ⟨a, b, h₁, h₂⟩ q hq h => ?_, fun H => ?_⟩
  · have : Fact q.Prime := ⟨prime_of_mem_primeFactors h

Depends on / 依赖: Even.zero, eq_zero_or_pos, n.eq_zero_or_pos, padicValNat_zero_right
-/
theorem Nat.eq_sq_add_sq_iff {n : Nat} :
    (exists x y, n = x ^ 2 + y ^ 2) ↔ forall q in n.primeFactors, q % 4 = 3 -> Even (padicValNat q n) := by
  rcases n.eq_zero_or_pos with (rfl | hn₀)
  · exact ⟨fun _ q _ _ => (padicValNat_zero_right _).symm ▸ Even.zero, fun _ => ⟨0, 0, rfl⟩⟩
  -- now `0 < n`
  refine eq_sq_add_sq_iff_eq_sq_mul.trans ⟨fun ⟨a, b, h₁, h₂⟩ q hq h => ?_, fun H => ?_⟩
  · have : Fact q.Prime := ⟨prime_of_mem_primeFactors hq⟩
    have : q ∣ b -> q in b.primeFactors := by grind
    grind (splits := 10) [padicValNat.mul, padicValNat.pow,
      padicValNat.eq_zero_of_not_dvd, mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one]
  · obtain ⟨b, a, hb₀, ha₀, hab, hb⟩ := sq_mul_squarefree_of_pos hn₀
    refine ⟨a, b, hab.symm, ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three hb
.mpr fun q hq hq4 => ?_⟩
    have : Fact q.Prime := ⟨prime_of_mem_primeFactors hq⟩
have := Nat.primeFactors_mono Dvd.intro_left _ hab
    have : b.factorization q = 1 := by grind [Squarefree.natFactorization_le_one,
      Prime.dvd_iff_one_le_factorization, prime_of_mem_primeFactors, dvd_of_mem_primeFactors]
    grind [factorization_def, prime_of_mem_primeFactors, padicValNat.mul, padicValNat.pow]

end Main

instance {n : Nat} : Decidable (exists x y, n = x ^ 2 + y ^ 2) :=
  decidable_of_iff' _ Nat.eq_sq_add_sq_iff
