/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Dickson polynomials

The (generalised) Dickson polynomials are a family of polynomials indexed by `ℕ × ℕ`,
with coefficients in a commutative ring `R` depending on an element `a∈R`. More precisely, the
they satisfy the recursion `dickson k a (n + 2) = X * (dickson k a n + 1) - a * (dickson k a n)`
with starting values `dickson k a 0 = 3 - k` and `dickson k a 1 = X`. In the literature,
`dickson k a n` is called the `n`-th Dickson polynomial of the `k`-th kind associated to the
parameter `a : R`. They are closely related to the Chebyshev polynomials in the case that `a=1`.
When `a=0` they are just the family of monomials `X ^ n`.

## Main definition

* `Polynomial.dickson`: the generalised Dickson polynomials.

## Main statements

* `Polynomial.dickson_one_one_mul`, the `(m * n)`-th Dickson polynomial of the first kind for
  parameter `1 : R` is the composition of the `m`-th and `n`-th Dickson polynomials of the first
  kind for `1 : R`.
* `Polynomial.dickson_one_one_charP`, for a prime number `p`, the `p`-th Dickson polynomial of the
  first kind associated to parameter `1 : R` is congruent to `X ^ p` modulo `p`.

## References

* [R. Lidl, G. L. Mullen and G. Turnwald, _Dickson polynomials_][MR1237403]

## TODO

* Redefine `dickson` in terms of `LinearRecurrence`.
* Show that `dickson 2 1` is equal to the characteristic polynomial of the adjacency matrix of a
  type A Dynkin diagram.
* Prove that the adjacency matrices of simply laced Dynkin diagrams are precisely the adjacency
  matrices of simple connected graphs which annihilate `dickson 2 1`.
-/

@[expose] public section


noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (k : Nat) (a : R)

/--
Definition of `dickson` / `dickson` 的定义

English:
definition dickson
  signature: : Nat -> R[X]

中文:
定义 dickson
  签名: : 自然数 -> R[X]
-/
noncomputable def dickson : Nat -> R[X]
  | 0 => 3 - k
  | 1 => X
  | n + 2 => X * dickson (n + 1) - C a * dickson n

@[simp]
/--
theorem `dickson_zero` / 定理 `dickson_zero`

English:
theorem dickson_zero
  statement: dickson k a 0 = 3 - k
  proof: rfl

@[simp]

中文:
定理 dickson_zero
  结论: dickson k a 0 = 3 - k
  证明: rfl

@[simp]
-/
theorem dickson_zero : dickson k a 0 = 3 - k :=
  rfl

@[simp]
/--
theorem `dickson_one` / 定理 `dickson_one`

English:
theorem dickson_one
  statement: dickson k a 1 = X
  proof: rfl

中文:
定理 dickson_one
  结论: dickson k a 1 = X
  证明: rfl
-/
theorem dickson_one : dickson k a 1 = X :=
  rfl

/--
theorem `dickson_two` / 定理 `dickson_two`

English:
theorem dickson_two
  statement: dickson k a 2 = X ^ 2 - C a * (3 - k : R[X])
  proof: by
  simp only [dickson, sq]

@[simp]

中文:
定理 dickson_two
  结论: dickson k a 2 = X ^ 2 - C a * (3 - k : R[X])
  证明: by
  simp only [dickson, sq]

@[simp]

Depends on / 依赖: dickson
-/
theorem dickson_two : dickson k a 2 = X ^ 2 - C a * (3 - k : R[X]) := by
  simp only [dickson, sq]

@[simp]
/--
theorem `dickson_add_two` / 定理 `dickson_add_two`

English:
theorem dickson_add_two
  given: (n : Nat)
  proof: by rw [dickson]

中文:
定理 dickson_add_two
  条件: (n : 自然数)
  证明: by rw [dickson]

Depends on / 依赖: dickson
-/
theorem dickson_add_two (n : Nat) :
    dickson k a (n + 2) = X * dickson k a (n + 1) - C a * dickson k a n := by rw [dickson]

/--
theorem `dickson_of_two_le` / 定理 `dickson_of_two_le`

English:
theorem dickson_of_two_le
  given: {n : Nat} (h : 2 <= n)
  proof: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]
  exact dickson_add_two k a n

中文:
定理 dickson_of_two_le
  条件: {n : 自然数} (h : 2 <= n)
  证明: by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]
  exact dickson_add_two k a n

Depends on / 依赖: Nat.exists_eq_add_of_le, add_comm, dickson_add_two, exists_eq_add_of_le
-/
theorem dickson_of_two_le {n : Nat} (h : 2 <= n) :
    dickson k a n = X * dickson k a (n - 1) - C a * dickson k a (n - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]
  exact dickson_add_two k a n

variable {k a}

/--
theorem `map_dickson` / 定理 `map_dickson`

English:
theorem map_dickson
  given: (f : R ->+* S)
  statement: forall n : Nat, map f (dickson k a n) = dickson k (f a) n

中文:
定理 map_dickson
  条件: (f : R ->+* S)
  结论: 对任意 n : 自然数, map f (dickson k a n) = dickson k (f a) n
-/
theorem map_dickson (f : R ->+* S) : forall n : Nat, map f (dickson k a n) = dickson k (f a) n
  | 0 => by
    simp_rw [dickson_zero, Polynomial.map_sub, Polynomial.map_natCast, Polynomial.map_ofNat]
  | 1 => by simp only [dickson_one, map_X]
  | n + 2 => by
    simp only [dickson_add_two, Polynomial.map_sub, Polynomial.map_mul, map_X, map_C]
    rw [map_dickson f n]; rw [map_dickson f (n + 1)]

@[simp]
/--
theorem `dickson_two_zero` / 定理 `dickson_two_zero`

English:
theorem dickson_two_zero
  statement: forall n : Nat, dickson 2 (0 : R) n = X ^ n

中文:
定理 dickson_two_zero
  结论: 对任意 n : 自然数, dickson 2 (0 : R) n = X ^ n
-/
theorem dickson_two_zero : forall n : Nat, dickson 2 (0 : R) n = X ^ n
  | 0 => by
    simp only [dickson_zero, pow_zero]
    norm_num
  | 1 => by simp only [dickson_one, pow_one]
  | n + 2 => by
    simp only [dickson_add_two, C_0, zero_mul, sub_zero]
    rw [dickson_two_zero (n + 1)]; rw [pow_add X (n + 1) 1]; rw [mul_comm]; rw [pow_one]

section Dickson


/--
theorem `dickson_one_one_eval_add_inv` / 定理 `dickson_one_one_eval_add_inv`

English:
theorem dickson_one_one_eval_add_inv
  given: (x y : R) (h : x * y = 1)

中文:
定理 dickson_one_one_eval_add_inv
  条件: (x y : R) (h : x * y = 1)

Depends on / 依赖: C_add, invOf_two_add_invOf_two, two_mul
-/
theorem dickson_one_one_eval_add_inv (x y : R) (h : x * y = 1) :
    forall n, (dickson 1 (1 : R) n).eval (x + y) = x ^ n + y ^ n
  | 0 => by
    simp only [pow_zero, dickson_zero]; norm_num
  | 1 => by simp only [eval_X, dickson_one, pow_one]
  | n + 2 => by
    simp only [eval_sub, eval_mul, dickson_one_one_eval_add_inv x y h _, eval_X, dickson_add_two,
      C_1, eval_one]
    conv_lhs => simp only [pow_succ', add_mul, mul_add, h, ← mul_assoc, mul_comm y x, one_mul]
    ring

variable (R)

/--
theorem `two_mul_C_half_eq_one` / 定理 `two_mul_C_half_eq_one`

English:
theorem two_mul_C_half_eq_one
  given: [Invertible (2 : R)]
  statement: 2 * C (⅟2 : R) = 1
  proof: by
  rw [two_mul]; rw [← C_add]; rw [invOf_two_add_invOf_two]; rw [C_1]

中文:
定理 two_mul_C_half_eq_one
  条件: [可逆 (2 : R)]
  结论: 2 * C (⅟2 : R) = 1
  证明: by
  rw [two_mul]; rw [← C_add]; rw [invOf_two_add_invOf_two]; rw [C_1]
-/
private theorem two_mul_C_half_eq_one [Invertible (2 : R)] : 2 * C (⅟2 : R) = 1 := by
  rw [two_mul]; rw [← C_add]; rw [invOf_two_add_invOf_two]; rw [C_1]

/--
theorem `C_half_mul_two_eq_one` / 定理 `C_half_mul_two_eq_one`

English:
theorem C_half_mul_two_eq_one
  given: [Invertible (2 : R)]
  statement: C (⅟2 : R) * 2 = 1
  proof: by
  rw [mul_comm]; rw [two_mul_C_half_eq_one]

中文:
定理 C_half_mul_two_eq_one
  条件: [可逆 (2 : R)]
  结论: C (⅟2 : R) * 2 = 1
  证明: by
  rw [mul_comm]; rw [two_mul_C_half_eq_one]
-/
private theorem C_half_mul_two_eq_one [Invertible (2 : R)] : C (⅟2 : R) * 2 = 1 := by
  rw [mul_comm]; rw [two_mul_C_half_eq_one]

/--
theorem `dickson_one_one_eq_chebyshev_C` / 定理 `dickson_one_one_eq_chebyshev_C`

English:
theorem dickson_one_one_eq_chebyshev_C
  statement: forall n, dickson 1 (1 : R) n = Chebyshev.C R n

中文:
定理 dickson_one_one_eq_chebyshev_C
  结论: 对任意 n, dickson 1 (1 : R) n = Chebyshev.C R n
-/
theorem dickson_one_one_eq_chebyshev_C : forall n, dickson 1 (1 : R) n = Chebyshev.C R n
  | 0 => by
    simp only [dickson_zero]
    norm_num
  | 1 => by
    rw [dickson_one]; rw [Nat.cast_one]; rw [Chebyshev.C_one]
  | n + 2 => by
    rw [dickson_add_two]; rw [C_1]; rw [Nat.cast_add]; rw [Nat.cast_two]; rw [Chebyshev.C_add_two]; rw [dickson_one_one_eq_chebyshev_C (n + 1)]; rw [dickson_one_one_eq_chebyshev_C n]
    push_cast
    ring

/--
theorem `dickson_one_one_eq_chebyshev_T` / 定理 `dickson_one_one_eq_chebyshev_T`

English:
theorem dickson_one_one_eq_chebyshev_T
  given: [Invertible (2 : R)] (n : Nat)
  proof: (dickson_one_one_eq_chebyshev_C R n).trans (Chebyshev.C_eq_two_mul_T_comp_half_mul_X R n)

中文:
定理 dickson_one_one_eq_chebyshev_T
  条件: [可逆 (2 : R)] (n : 自然数)
  证明: (dickson_one_one_eq_chebyshev_C R n).trans (Chebyshev.C_eq_two_mul_T_comp_half_mul_X R n)

Depends on / 依赖: C_eq_two_mul_T_comp_half_mul_X, Chebyshev, Chebyshev.C_eq_two_mul_T_comp_half_mul_X, dickson_one_one_eq_chebyshev_C
-/
theorem dickson_one_one_eq_chebyshev_T [Invertible (2 : R)] (n : Nat) :
    dickson 1 (1 : R) n = 2 * (Chebyshev.T R n).comp (C (⅟2) * X) :=
  (dickson_one_one_eq_chebyshev_C R n).trans (Chebyshev.C_eq_two_mul_T_comp_half_mul_X R n)

/--
theorem `chebyshev_T_eq_dickson_one_one` / 定理 `chebyshev_T_eq_dickson_one_one`

English:
theorem chebyshev_T_eq_dickson_one_one
  given: [Invertible (2 : R)] (n : Nat)
  proof: dickson_one_one_eq_chebyshev_C R n ▸ Chebyshev.T_eq_half_mul_C_comp_two_mul_X R n

中文:
定理 chebyshev_T_eq_dickson_one_one
  条件: [可逆 (2 : R)] (n : 自然数)
  证明: dickson_one_one_eq_chebyshev_C R n ▸ Chebyshev.T_eq_half_mul_C_comp_two_mul_X R n

Depends on / 依赖: Chebyshev, Chebyshev.T_eq_half_mul_C_comp_two_mul_X, T_eq_half_mul_C_comp_two_mul_X, dickson_one_one_eq_chebyshev_C
-/
theorem chebyshev_T_eq_dickson_one_one [Invertible (2 : R)] (n : Nat) :
    Chebyshev.T R n = C (⅟2) * (dickson 1 1 n).comp (2 * X) :=
  dickson_one_one_eq_chebyshev_C R n ▸ Chebyshev.T_eq_half_mul_C_comp_two_mul_X R n

/--
theorem `dickson_two_one_eq_chebyshev_S` / 定理 `dickson_two_one_eq_chebyshev_S`

English:
theorem dickson_two_one_eq_chebyshev_S
  statement: forall n, dickson 2 (1 : R) n = Chebyshev.S R n

中文:
定理 dickson_two_one_eq_chebyshev_S
  结论: 对任意 n, dickson 2 (1 : R) n = Chebyshev.S R n
-/
theorem dickson_two_one_eq_chebyshev_S : forall n, dickson 2 (1 : R) n = Chebyshev.S R n
  | 0 => by
    simp only [dickson_zero]
    norm_num
  | 1 => by
    rw [dickson_one]; rw [Nat.cast_one]; rw [Chebyshev.S_one]
  | n + 2 => by
    rw [dickson_add_two]; rw [C_1]; rw [Nat.cast_add]; rw [Nat.cast_two]; rw [Chebyshev.S_add_two]; rw [dickson_two_one_eq_chebyshev_S (n + 1)]; rw [dickson_two_one_eq_chebyshev_S n]
    push_cast
    ring

/--
theorem `dickson_two_one_eq_chebyshev_U` / 定理 `dickson_two_one_eq_chebyshev_U`

English:
theorem dickson_two_one_eq_chebyshev_U
  given: [Invertible (2 : R)] (n : Nat)
  proof: (dickson_two_one_eq_chebyshev_S R n).trans (Chebyshev.S_eq_U_comp_half_mul_X R n)

中文:
定理 dickson_two_one_eq_chebyshev_U
  条件: [可逆 (2 : R)] (n : 自然数)
  证明: (dickson_two_one_eq_chebyshev_S R n).trans (Chebyshev.S_eq_U_comp_half_mul_X R n)

Depends on / 依赖: Chebyshev, Chebyshev.S_eq_U_comp_half_mul_X, S_eq_U_comp_half_mul_X, dickson_two_one_eq_chebyshev_S
-/
theorem dickson_two_one_eq_chebyshev_U [Invertible (2 : R)] (n : Nat) :
    dickson 2 (1 : R) n = (Chebyshev.U R n).comp (C (⅟2) * X) :=
  (dickson_two_one_eq_chebyshev_S R n).trans (Chebyshev.S_eq_U_comp_half_mul_X R n)

/--
theorem `chebyshev_U_eq_dickson_two_one` / 定理 `chebyshev_U_eq_dickson_two_one`

English:
theorem chebyshev_U_eq_dickson_two_one
  given: (n : Nat)
  proof: dickson_two_one_eq_chebyshev_S R n ▸ (Chebyshev.S_comp_two_mul_X R n).symm

中文:
定理 chebyshev_U_eq_dickson_two_one
  条件: (n : 自然数)
  证明: dickson_two_one_eq_chebyshev_S R n ▸ (Chebyshev.S_comp_two_mul_X R n).symm

Depends on / 依赖: Chebyshev, Chebyshev.S_comp_two_mul_X, S_comp_two_mul_X, dickson_two_one_eq_chebyshev_S
-/
theorem chebyshev_U_eq_dickson_two_one (n : Nat) :
    Chebyshev.U R n = (dickson 2 (1 : R) n).comp (2 * X) :=
  dickson_two_one_eq_chebyshev_S R n ▸ (Chebyshev.S_comp_two_mul_X R n).symm

/--
theorem `dickson_one_one_mul` / 定理 `dickson_one_one_mul`

English:
theorem dickson_one_one_mul
  given: (m n : Nat)
  proof: by
  have h : (1 : R) = Int.castRingHom R 1 := by simp only [eq_intCast, Int.cast_one]
  rw [h]
  simp only [← map_dickson (Int.castRingHom R), ← map_comp]
  congr 1
  apply map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_dickson, map_comp, eq_intCast, Int.cast_one, dickson_o

中文:
定理 dickson_one_one_mul
  条件: (m n : 自然数)
  证明: by
  have h : (1 : R) = Int.castRingHom R 1 := by simp only [eq_intCast, Int.cast_one]
  rw [h]
  simp only [← map_dickson (Int.castRingHom R), ← map_comp]
  congr 1
  apply map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_dickson, map_comp, eq_intCast, Int.cast_one, dickson_o

Depends on / 依赖: C_comp, Chebyshev, Chebyshev.T_mul, Int.castRingHom, Int.cast_injective, Int.cast_one, Nat.cast_mul, T_mul, add_comp, castRingHom, cast_injective, cast_mul, cast_one, comp_assoc, dickson_one_one_eq_chebyshev_T, eq_intCast, map_comp, map_dickson, map_injective, mul_comp
-/
theorem dickson_one_one_mul (m n : Nat) :
    dickson 1 (1 : R) (m * n) = (dickson 1 1 m).comp (dickson 1 1 n) := by
  have h : (1 : R) = Int.castRingHom R 1 := by simp only [eq_intCast, Int.cast_one]
  rw [h]
  simp only [← map_dickson (Int.castRingHom R), ← map_comp]
  congr 1
  apply map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_dickson, map_comp, eq_intCast, Int.cast_one, dickson_one_one_eq_chebyshev_T,
    Nat.cast_mul, Chebyshev.T_mul, two_mul, ← add_comp]
  simp only [← two_mul, ← comp_assoc]
  apply eval₂_congr rfl rfl
  rw [comp_assoc]
  apply eval₂_congr rfl _ rfl
  rw [mul_comp]; rw [C_comp]; rw [X_comp]; rw [← mul_assoc]; rw [C_half_mul_two_eq_one]; rw [one_mul]

/--
theorem `dickson_one_one_comp_comm` / 定理 `dickson_one_one_comp_comm`

English:
theorem dickson_one_one_comp_comm
  given: (m n : Nat)
  proof: by
  rw [← dickson_one_one_mul]; rw [mul_comm]; rw [dickson_one_one_mul]

中文:
定理 dickson_one_one_comp_comm
  条件: (m n : 自然数)
  证明: by
  rw [← dickson_one_one_mul]; rw [mul_comm]; rw [dickson_one_one_mul]

Depends on / 依赖: dickson_one_one_mul, mul_comm
-/
theorem dickson_one_one_comp_comm (m n : Nat) :
    (dickson 1 (1 : R) m).comp (dickson 1 1 n) = (dickson 1 1 n).comp (dickson 1 1 m) := by
  rw [← dickson_one_one_mul]; rw [mul_comm]; rw [dickson_one_one_mul]

/--
theorem `dickson_one_one_zmod_p` / 定理 `dickson_one_one_zmod_p`

English:
theorem dickson_one_one_zmod_p
  given: (p : Nat) [Fact p.Prime]
  statement: dickson 1 (1 : ZMod p) p = X ^ p
  proof: by
  -- Recall that `dickson_one_one_eval_add_inv` characterises `dickson 1 1 p`
  -- as a polynomial that maps `x + x⁻¹` to `x ^ p + (x⁻¹) ^ p`.
  -- Since `X ^ p` also satisfies this property in characteristic `p`,
  -- we can use a variant on `Polynomial.funext` to conclude that these polynomials

中文:
定理 dickson_one_one_zmod_p
  条件: (p : 自然数) [Fact p.素]
  结论: dickson 1 (1 : ZMod p) p = X ^ p
  证明: by
  -- Recall that `dickson_one_one_eval_add_inv` characterises `dickson 1 1 p`
  -- as a polynomial that maps `x + x⁻¹` to `x ^ p + (x⁻¹) ^ p`.
  -- Since `X ^ p` also satisfies this property in characteristic `p`,
  -- we can use a variant on `Polynomial.funext` to conclude that these polynomials
-/
theorem dickson_one_one_zmod_p (p : Nat) [Fact p.Prime] : dickson 1 (1 : ZMod p) p = X ^ p := by
  -- Recall that `dickson_one_one_eval_add_inv` characterises `dickson 1 1 p`
  -- as a polynomial that maps `x + x⁻¹` to `x ^ p + (x⁻¹) ^ p`.
  -- Since `X ^ p` also satisfies this property in characteristic `p`,
  -- we can use a variant on `Polynomial.funext` to conclude that these polynomials are equal.
  -- For this argument, we need an arbitrary infinite field of characteristic `p`.
  obtain ⟨K, _, _, H⟩ : exists (K : Type) (_ : Field K), exists _ : CharP K p, Infinite K := by
    let K := FractionRing (Polynomial (ZMod p))
    let f : ZMod p ->+* K := (algebraMap _ (FractionRing _)).comp C
    have : CharP K p := by
      rw [← f.charP_iff_charP]
      infer_instance
    have : Infinite K :=
      Infinite.of_injective (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))))
        (IsFractionRing.injective _ _)
    refine ⟨K, ?_, ?_, ?_⟩ <;> infer_instance
  apply map_injective (ZMod.castHom (dvd_refl p) K) (RingHom.injective _)
  rw [map_dickson]; rw [Polynomial.map_pow]; rw [map_X]
  apply eq_of_infinite_eval_eq
  -- The two polynomials agree on all `x` of the form `x = y + y⁻¹`.
  apply @Set.Infinite.mono _ { x : K | exists y, x = y + y⁻¹ ∧ y != 0 }
  · rintro _ ⟨x, rfl, hx⟩
    simp only [eval_X, eval_pow, Set.mem_ofPred_eq, ZMod.cast_one', add_pow_char,
      dickson_one_one_eval_add_inv _ _ (mul_inv_cancel₀ hx), ZMod.castHom_apply]
  -- Now we need to show that the set of such `x` is infinite.
  -- If the set is finite, then we will show that `K` is also finite.
  · intro h
    rw [← Set.infinite_univ_iff] at H
    apply H
    -- To each `x` of the form `x = y + y⁻¹`
    -- we `bind` the set of `y` that solve the equation `x = y + y⁻¹`.
    -- For every `x`, that set is finite (since it is governed by a quadratic equation).
    -- For the moment, we claim that all these sets together cover `K`.
    suffices (Set.univ : Set K) =
        ⋃ x in { x : K | exists y : K, x = y + y⁻¹ ∧ y != 0 }, { y | x = y + y⁻¹ ∨ y = 0 } by
      rw [this]
      clear this
      refine h.biUnion fun x _ => ?_
      -- The following quadratic polynomial has as solutions the `y` for which `x = y + y⁻¹`.
      let φ : K[X] := X ^ 2 - C x * X + 1
      have hφ : φ != 0 := by
        intro H
        have : φ.eval 0 = 0 := by rw [H, eval_zero]
        simpa [φ, eval_X, eval_one, eval_pow, eval_sub, sub_zero, eval_add, eval_mul,
          mul_zero, sq, zero_add, one_ne_zero]
      classical
        convert! (φ.roots union {0}).toFinset.finite_toSet using 1
        ext1 y
        simp only [φ, Multiset.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_union,
          mem_roots hφ, IsRoot, eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C, eval_one,
          Multiset.mem_singleton]
        by_cases hy : y = 0
        · simp only [hy, or_true]
        apply or_congr _ Iff.rfl
        rw [← mul_left_inj' hy]; rw [eq_comm]; rw [← sub_eq_zero]; rw [add_mul]; rw [inv_mul_cancel₀ hy]
        apply eq_iff_eq_cancel_right.mpr
        ring
    -- Finally, we prove the claim that our finite union of finite sets covers all of `K`.
    apply (Set.eq_univ_of_forall _).symm
    intro x
    simp only [exists_prop, Set.mem_iUnion, Ne, Set.mem_ofPred_eq]
    by_cases hx : x = 0
    · simp only [hx, and_true, inv_zero, or_true]
      exact ⟨_, 1, rfl, one_ne_zero⟩
    · simp only [hx, or_false, exists_eq_right]
      exact ⟨_, rfl, hx⟩

/--
theorem `dickson_one_one_charP` / 定理 `dickson_one_one_charP`

English:
theorem dickson_one_one_charP
  given: (p : Nat) [Fact p.Prime] [CharP R p]
  statement: dickson 1 (1 : R) p = X ^ p
  proof: by
  have h : (1 : R) = ZMod.castHom (dvd_refl p) R 1 := by
    simp only [ZMod.castHom_apply, ZMod.cast_one']
  rw [h]; rw [← map_dickson (ZMod.castHom (dvd_refl p) R)]; rw [dickson_one_one_zmod_p]; rw [Polynomial.map_pow]; rw [map_X]

中文:
定理 dickson_one_one_charP
  条件: (p : 自然数) [Fact p.素] [特征p R p]
  结论: dickson 1 (1 : R) p = X ^ p
  证明: by
  have h : (1 : R) = ZMod.castHom (dvd_refl p) R 1 := by
    simp only [ZMod.castHom_apply, ZMod.cast_one']
  rw [h]; rw [← map_dickson (ZMod.castHom (dvd_refl p) R)]; rw [dickson_one_one_zmod_p]; rw [Polynomial.map_pow]; rw [map_X]

Depends on / 依赖: Polynomial, Polynomial.map_pow, ZMod.castHom, ZMod.castHom_apply, ZMod.cast_one, castHom, castHom_apply, cast_one, dickson_one_one_zmod_p, dvd_refl, map_X, map_dickson, map_pow
-/
theorem dickson_one_one_charP (p : Nat) [Fact p.Prime] [CharP R p] : dickson 1 (1 : R) p = X ^ p := by
  have h : (1 : R) = ZMod.castHom (dvd_refl p) R 1 := by
    simp only [ZMod.castHom_apply, ZMod.cast_one']
  rw [h]; rw [← map_dickson (ZMod.castHom (dvd_refl p) R)]; rw [dickson_one_one_zmod_p]; rw [Polynomial.map_pow]; rw [map_X]

end Dickson

end Polynomial
