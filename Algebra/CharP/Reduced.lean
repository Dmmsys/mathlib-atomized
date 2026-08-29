/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Algebra.CharP.Frobenius

/-!
# Results about characteristic p reduced rings
-/

public section


open Finset

section

variable (R : Type*) [CommRing R] [IsReduced R] (p n : Nat) [ExpChar R p]

/--
theorem `iterateFrobenius_inj` / 定理 `iterateFrobenius_inj`

English:
theorem iterateFrobenius_inj
  statement: Function.Injective (iterateFrobenius R p n)
  proof: fun x y H => by
  rw [← sub_eq_zero] at H ⊢
  simp_rw [iterateFrobenius_def, ← sub_pow_expChar_pow] at H
  exact IsReduced.eq_zero _ ⟨_, H⟩

中文:
定理 iterateFrobenius_inj
  结论: 函数.单射 (iterateFrobenius R p n)
  证明: fun x y H => by
  rw [← sub_eq_zero] at H ⊢
  simp_rw [iterateFrobenius_def, ← sub_pow_expChar_pow] at H
  exact IsReduced.eq_zero _ ⟨_, H⟩

Depends on / 依赖: IsReduced, IsReduced.eq_zero, eq_zero, iterateFrobenius_def, simp_rw, sub_eq_zero, sub_pow_expChar_pow
-/
theorem iterateFrobenius_inj : Function.Injective (iterateFrobenius R p n) := fun x y H => by
  rw [← sub_eq_zero] at H ⊢
  simp_rw [iterateFrobenius_def, ← sub_pow_expChar_pow] at H
  exact IsReduced.eq_zero _ ⟨_, H⟩

/--
theorem `frobenius_inj` / 定理 `frobenius_inj`

English:
theorem frobenius_inj
  statement: Function.Injective (frobenius R p)
  proof: iterateFrobenius_one (R := R) p ▸ iterateFrobenius_inj R p 1

中文:
定理 frobenius_inj
  结论: 函数.单射 (frobenius R p)
  证明: iterateFrobenius_one (R := R) p ▸ iterateFrobenius_inj R p 1

Depends on / 依赖: iterateFrobenius_inj, iterateFrobenius_one
-/
theorem frobenius_inj : Function.Injective (frobenius R p) :=
  iterateFrobenius_one (R := R) p ▸ iterateFrobenius_inj R p 1

end

/--
theorem `isSquare_of_charTwo'` / 定理 `isSquare_of_charTwo'`

English:
theorem isSquare_of_charTwo'
  statement: {R : Type*} [Finite R] [CommRing R] [IsReduced R] [CharP R 2]
  proof: by
  cases nonempty_fintype R
  exact
    Exists.imp (fun b h => pow_two b ▸ Eq.symm h)
      (((Fintype.bijective_iff_injective_and_card _).mpr ⟨frobenius_inj R 2, rfl⟩).surjective a)

中文:
定理 isSquare_of_charTwo'
  结论: {R : 类型} [有限 R] [交换环 R] [是既约 R] [特征p R 2]
  证明: by
  cases nonempty_fintype R
  exact
    Exists.imp (fun b h => pow_two b ▸ Eq.symm h)
      (((Fintype.bijective_iff_injective_and_card _).mpr ⟨frobenius_inj R 2, rfl⟩).surjective a)

Depends on / 依赖: Eq.symm, Exists, Exists.imp, Fintype, Fintype.bijective_iff_injective_and_card, bijective_iff_injective_and_card, frobenius_inj, nonempty_fintype, pow_two, surjective
-/
theorem isSquare_of_charTwo' {R : Type*} [Finite R] [CommRing R] [IsReduced R] [CharP R 2]
    (a : R) : IsSquare a := by
  cases nonempty_fintype R
  exact
    Exists.imp (fun b h => pow_two b ▸ Eq.symm h)
      (((Fintype.bijective_iff_injective_and_card _).mpr ⟨frobenius_inj R 2, rfl⟩).surjective a)

variable {R : Type*} [CommRing R] [IsReduced R]

@[simp]
/--
theorem `ExpChar.pow_prime_pow_mul_eq_one_iff` / 定理 `ExpChar.pow_prime_pow_mul_eq_one_iff`

English:
theorem ExpChar.pow_prime_pow_mul_eq_one_iff
  given: (p k m : Nat) [ExpChar R p] (x : R)
  proof: by
  rw [pow_mul']
  convert! ← (iterateFrobenius_inj R p k).eq_iff
  apply map_one

中文:
定理 ExpChar.pow_prime_pow_mul_eq_one_iff
  条件: (p k m : 自然数) [ExpChar R p] (x : R)
  证明: by
  rw [pow_mul']
  convert! ← (iterateFrobenius_inj R p k).eq_iff
  apply map_one

Depends on / 依赖: convert, eq_iff, iterateFrobenius_inj, map_one, pow_mul
-/
theorem ExpChar.pow_prime_pow_mul_eq_one_iff (p k m : Nat) [ExpChar R p] (x : R) :
    x ^ (p ^ k * m) = 1 ↔ x ^ m = 1 := by
  rw [pow_mul']
  convert! ← (iterateFrobenius_inj R p k).eq_iff
  apply map_one
