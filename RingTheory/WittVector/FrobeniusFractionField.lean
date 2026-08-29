/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/
module

public import Mathlib.Data.Nat.Cast.WithTop
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-!
# Solving equations about the Frobenius map on the field of fractions of `𝕎 k`

The goal of this file is to prove `WittVector.exists_frobenius_solution_fractionRing`,
which says that for an algebraically closed field `k` of characteristic `p` and `a, b` in the
field of fractions of Witt vectors over `k`,
there is a solution `b` to the equation `φ b * a = p ^ m * b`, where `φ` is the Frobenius map.

Most of this file builds up the equivalent theorem over `𝕎 k` directly,
moving to the field of fractions at the end.
See `WittVector.frobeniusRotation` and its specification.

The construction proceeds by recursively defining a sequence of coefficients as solutions to a
polynomial equation in `k`. We must define these as generic polynomials using Witt vector API
(`WittVector.wittMul`, `wittPolynomial`) to show that they satisfy the desired equation.

Preliminary work is done in the dependency `RingTheory.WittVector.MulCoeff`
to isolate the `n+1`st coefficients of `x` and `y` in the `n+1`st coefficient of `x*y`.

This construction is described in Dupuis, Lewis, and Macbeth,
[Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022].
We approximately follow an approach sketched on MathOverflow:
<https://mathoverflow.net/questions/62468/about-frobenius-of-witt-vectors>

The result is a dependency for the proof of `WittVector.isocrystal_classification`,
the classification of one-dimensional isocrystals over an algebraically closed field.
-/

@[expose] public section


noncomputable section

namespace WittVector

variable (p : Nat) [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

namespace RecursionMain

/-!

## The recursive case of the vector coefficients

The first coefficient of our solution vector is easy to define below.
In this section we focus on the recursive case.
The goal is to turn `WittVector.wittPolyProd n` into a univariate polynomial
whose variable represents the `n`th coefficient of `x` in `x * a`.

-/


section CommRing

variable {k : Type*} [CommRing k] [CharP k p]

open Polynomial

/--
Definition of `succNthDefiningPoly` / `succNthDefiningPoly` 的定义

English:
definition succNthDefiningPoly
  signature: (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k)
  body: X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1)) - X * C (a₂.coeff 0 ^ p ^ (n + 1)) +
    C
      (a₁.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) +
            nthRemainder p n (fun v => bs v ^ p) (truncateFun (n + 1) a₁) -
          a₂.coeff (n + 1) * bs 0 ^ p ^ (n + 1) -
        nthRemainder p n bs (truncateFun 

中文:
定义 succNthDefiningPoly
  签名: (n : 自然数) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k)
  定义体: X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1)) - X * C (a₂.coeff 0 ^ p ^ (n + 1)) +
    C
      (a₁.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) +
            nthRemainder p n (fun v => bs v ^ p) (truncateFun (n + 1) a₁) -
          a₂.coeff (n + 1) * bs 0 ^ p ^ (n + 1) -
        nthRemainder p n bs (truncateFun 

Depends on / 依赖: nthRemainder, truncateFun
-/
def succNthDefiningPoly (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) : Polynomial k :=
  X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1)) - X * C (a₂.coeff 0 ^ p ^ (n + 1)) +
    C
      (a₁.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) +
            nthRemainder p n (fun v => bs v ^ p) (truncateFun (n + 1) a₁) -
          a₂.coeff (n + 1) * bs 0 ^ p ^ (n + 1) -
        nthRemainder p n bs (truncateFun (n + 1) a₂))

/--
theorem `succNthDefiningPoly_degree` / 定理 `succNthDefiningPoly_degree`

English:
theorem succNthDefiningPoly_degree
  statement: [IsDomain k] (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k)
  proof: by
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1))).degree = (p : WithBot Nat) := by
    rw [degree_mul]; rw [degree_C]
    · simp
    · exact pow_ne_zero _ ha₁
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1)) - X * C (a₂.coeff 0 ^ p ^ (n + 1))).degree =
      (p : WithBot Nat) := by
    rw [degree_sub

中文:
定理 succNthDefiningPoly_degree
  结论: [IsDomain k] (n : 自然数) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k)
  证明: by
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1))).degree = (p : WithBot Nat) := by
    rw [degree_mul]; rw [degree_C]
    · simp
    · exact pow_ne_zero _ ha₁
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1)) - X * C (a₂.coeff 0 ^ p ^ (n + 1))).degree =
      (p : WithBot Nat) := by
    rw [degree_sub

Depends on / 依赖: WithBot, add_zero, degree, degree_C, degree_X, degree_add_eq_left_of_degree_lt, degree_mul, degree_sub_eq_left_of_degree_lt, hp.out.one_lt, mod_cast, one_lt, pow_ne_zero, succNthDefiningPoly
-/
theorem succNthDefiningPoly_degree [IsDomain k] (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k)
    (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) :
    (succNthDefiningPoly p n a₁ a₂ bs).degree = p := by
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1))).degree = (p : WithBot Nat) := by
    rw [degree_mul]; rw [degree_C]
    · simp
    · exact pow_ne_zero _ ha₁
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n + 1)) - X * C (a₂.coeff 0 ^ p ^ (n + 1))).degree =
      (p : WithBot Nat) := by
    rw [degree_sub_eq_left_of_degree_lt]; rw [this]
    rw [this]; rw [degree_mul]; rw [degree_C]; rw [degree_X]; rw [add_zero]
    · exact mod_cast hp.out.one_lt
    · exact pow_ne_zero _ ha₂
  rw [succNthDefiningPoly]; rw [degree_add_eq_left_of_degree_lt]; rw [this]
  apply lt_of_le_of_lt degree_C_le
  rw [this]
  exact mod_cast hp.out.pos

end CommRing

section IsAlgClosed

variable {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]

/--
theorem `root_exists` / 定理 `root_exists`

English:
theorem root_exists
  statement: (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
  proof: IsAlgClosed.exists_root _ by
    simp only [succNthDefiningPoly_degree p n a₁ a₂ bs ha₁ ha₂, ne_eq, Nat.cast_eq_zero,
      hp.out.ne_zero, not_false_eq_true]

中文:
定理 root_exists
  结论: (n : 自然数) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
  证明: IsAlgClosed.exists_root _ by
    simp only [succNthDefiningPoly_degree p n a₁ a₂ bs ha₁ ha₂, ne_eq, Nat.cast_eq_zero,
      hp.out.ne_zero, not_false_eq_true]

Depends on / 依赖: IsAlgClosed, IsAlgClosed.exists_root, Nat.cast_eq_zero, cast_eq_zero, exists_root, hp.out.ne_zero, ne_eq, ne_zero, not_false_eq_true, succNthDefiningPoly_degree
-/
theorem root_exists (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
    (ha₂ : a₂.coeff 0 != 0) : exists b : k, (succNthDefiningPoly p n a₁ a₂ bs).IsRoot b :=
IsAlgClosed.exists_root _ by
    simp only [succNthDefiningPoly_degree p n a₁ a₂ bs ha₁ ha₂, ne_eq, Nat.cast_eq_zero,
      hp.out.ne_zero, not_false_eq_true]

/--
Definition of `succNthVal` / `succNthVal` 的定义

English:
definition succNthVal
  signature: (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
  body: Classical.choose (root_exists p n a₁ a₂ bs ha₁ ha₂)

中文:
定义 succNthVal
  签名: (n : 自然数) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
  定义体: Classical.choose (root_exists p n a₁ a₂ bs ha₁ ha₂)

Depends on / 依赖: Classical, Classical.choose, root_exists
-/
def succNthVal (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
    (ha₂ : a₂.coeff 0 != 0) : k :=
  Classical.choose (root_exists p n a₁ a₂ bs ha₁ ha₂)

/--
theorem `succNthVal_spec` / 定理 `succNthVal_spec`

English:
theorem succNthVal_spec
  statement: (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
  proof: Classical.choose_spec (root_exists p n a₁ a₂ bs ha₁ ha₂)

中文:
定理 succNthVal_spec
  结论: (n : 自然数) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
  证明: Classical.choose_spec (root_exists p n a₁ a₂ bs ha₁ ha₂)

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, root_exists
-/
theorem succNthVal_spec (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
    (ha₂ : a₂.coeff 0 != 0) :
    (succNthDefiningPoly p n a₁ a₂ bs).IsRoot (succNthVal p n a₁ a₂ bs ha₁ ha₂) :=
  Classical.choose_spec (root_exists p n a₁ a₂ bs ha₁ ha₂)

/--
theorem `succNthVal_spec'` / 定理 `succNthVal_spec'`

English:
theorem succNthVal_spec'
  statement: (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
  proof: by
  rw [← sub_eq_zero]
  have := succNthVal_spec p n a₁ a₂ bs ha₁ ha₂
  simp only [Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_pow, succNthDefiningPoly, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.IsRoot.def]
    at this
  convert! this using 1
  ring

中文:
定理 succNthVal_spec'
  结论: (n : 自然数) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
  证明: by
  rw [← sub_eq_zero]
  have := succNthVal_spec p n a₁ a₂ bs ha₁ ha₂
  simp only [Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_pow, succNthDefiningPoly, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.IsRoot.def]
    at this
  convert! this using 1
  ring

Depends on / 依赖: IsRoot, Polynomial, Polynomial.IsRoot.def, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, convert, eval_C, eval_X, eval_add, eval_mul, eval_pow, eval_sub, sub_eq_zero, succNthDefiningPoly, succNthVal_spec
-/
theorem succNthVal_spec' (n : Nat) (a₁ a₂ : 𝕎 k) (bs : Fin (n + 1) -> k) (ha₁ : a₁.coeff 0 != 0)
    (ha₂ : a₂.coeff 0 != 0) :
    succNthVal p n a₁ a₂ bs ha₁ ha₂ ^ p * a₁.coeff 0 ^ p ^ (n + 1) +
          a₁.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) +
        nthRemainder p n (fun v => bs v ^ p) (truncateFun (n + 1) a₁) =
      succNthVal p n a₁ a₂ bs ha₁ ha₂ * a₂.coeff 0 ^ p ^ (n + 1) +
          a₂.coeff (n + 1) * bs 0 ^ p ^ (n + 1) +
        nthRemainder p n bs (truncateFun (n + 1) a₂) := by
  rw [← sub_eq_zero]
  have := succNthVal_spec p n a₁ a₂ bs ha₁ ha₂
  simp only [Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_pow, succNthDefiningPoly, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.IsRoot.def]
    at this
  convert! this using 1
  ring

end IsAlgClosed

end RecursionMain

namespace RecursionBase

variable {k : Type*} [Field k] [IsAlgClosed k]

/--
theorem `solution_pow` / 定理 `solution_pow`

English:
theorem solution_pow
  given: (a₁ a₂ : 𝕎 k)
  statement: exists x : k, x ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0
  proof: IsAlgClosed.exists_pow_nat_eq _ tsub_pos_of_lt hp.out.one_lt

中文:
定理 solution_pow
  条件: (a₁ a₂ : 𝕎 k)
  结论: 存在 x : k, x ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0
  证明: IsAlgClosed.exists_pow_nat_eq _ tsub_pos_of_lt hp.out.one_lt

Depends on / 依赖: IsAlgClosed, IsAlgClosed.exists_pow_nat_eq, exists_pow_nat_eq, hp.out.one_lt, one_lt, tsub_pos_of_lt
-/
theorem solution_pow (a₁ a₂ : 𝕎 k) : exists x : k, x ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0 :=
IsAlgClosed.exists_pow_nat_eq _ tsub_pos_of_lt hp.out.one_lt

/--
Definition of `solution` / `solution` 的定义

English:
definition solution
  signature: (a₁ a₂ : 𝕎 k)
  body: Classical.choose solution_pow p a₁ a₂

中文:
定义 solution
  签名: (a₁ a₂ : 𝕎 k)
  定义体: Classical.choose solution_pow p a₁ a₂

Depends on / 依赖: Classical, Classical.choose, solution_pow
-/
def solution (a₁ a₂ : 𝕎 k) : k :=
Classical.choose solution_pow p a₁ a₂

/--
theorem `solution_spec` / 定理 `solution_spec`

English:
theorem solution_spec
  given: (a₁ a₂ : 𝕎 k)
  statement: solution p a₁ a₂ ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0
  proof: Classical.choose_spec solution_pow p a₁ a₂

中文:
定理 solution_spec
  条件: (a₁ a₂ : 𝕎 k)
  结论: solution p a₁ a₂ ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0
  证明: Classical.choose_spec solution_pow p a₁ a₂

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, solution_pow
-/
theorem solution_spec (a₁ a₂ : 𝕎 k) : solution p a₁ a₂ ^ (p - 1) = a₂.coeff 0 / a₁.coeff 0 :=
Classical.choose_spec solution_pow p a₁ a₂

/--
theorem `solution_nonzero` / 定理 `solution_nonzero`

English:
theorem solution_nonzero
  given: {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0)
  proof: by
  intro h
  have := solution_spec p a₁ a₂
  rw [h]; rw [zero_pow] at this
  · simpa [ha₁, ha₂] using _root_.div_eq_zero_iff.mp this.symm
  · exact Nat.sub_ne_zero_of_lt hp.out.one_lt

中文:
定理 solution_nonzero
  条件: {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0)
  证明: by
  intro h
  have := solution_spec p a₁ a₂
  rw [h]; rw [zero_pow] at this
  · simpa [ha₁, ha₂] using _root_.div_eq_zero_iff.mp this.symm
  · exact Nat.sub_ne_zero_of_lt hp.out.one_lt

Depends on / 依赖: Nat.sub_ne_zero_of_lt, _root_, _root_.div_eq_zero_iff.mp, div_eq_zero_iff, hp.out.one_lt, one_lt, solution_spec, sub_ne_zero_of_lt, this.symm, zero_pow
-/
theorem solution_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) :
    solution p a₁ a₂ != 0 := by
  intro h
  have := solution_spec p a₁ a₂
  rw [h]; rw [zero_pow] at this
  · simpa [ha₁, ha₂] using _root_.div_eq_zero_iff.mp this.symm
  · exact Nat.sub_ne_zero_of_lt hp.out.one_lt

/--
theorem `solution_spec'` / 定理 `solution_spec'`

English:
theorem solution_spec'
  given: {a₁ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (a₂ : 𝕎 k)
  proof: by
  have := solution_spec p a₁ a₂
  have := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
  grind

中文:
定理 solution_spec'
  条件: {a₁ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (a₂ : 𝕎 k)
  证明: by
  have := solution_spec p a₁ a₂
  have := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
  grind

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, exists_eq_succ_of_ne_zero, hp.out.ne_zero, ne_zero, solution_spec
-/
theorem solution_spec' {a₁ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (a₂ : 𝕎 k) :
    solution p a₁ a₂ ^ p * a₁.coeff 0 = solution p a₁ a₂ * a₂.coeff 0 := by
  have := solution_spec p a₁ a₂
  have := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
  grind

end RecursionBase

open RecursionMain RecursionBase

section FrobeniusRotation

section IsAlgClosed

variable {k : Type*} [Field k] [CharP k p] [IsAlgClosed k]

/--
Definition of `frobeniusRotationCoeff` / `frobeniusRotationCoeff` 的定义

English:
definition frobeniusRotationCoeff
  signature: {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0)

中文:
定义 frobeniusRotationCoeff
  签名: {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0)
-/
noncomputable def frobeniusRotationCoeff {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0)
    (ha₂ : a₂.coeff 0 != 0) : Nat -> k
  | 0 => solution p a₁ a₂
  | n + 1 => succNthVal p n a₁ a₂ (fun i => frobeniusRotationCoeff ha₁ ha₂ i.val) ha₁ ha₂

/--
Definition of `frobeniusRotation` / `frobeniusRotation` 的定义

English:
definition frobeniusRotation
  signature: {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0)
  body: WittVector.mk p (frobeniusRotationCoeff p ha₁ ha₂)

中文:
定义 frobeniusRotation
  签名: {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0)
  定义体: WittVector.mk p (frobeniusRotationCoeff p ha₁ ha₂)

Depends on / 依赖: WittVector, WittVector.mk, frobeniusRotationCoeff
-/
def frobeniusRotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) : 𝕎 k :=
  WittVector.mk p (frobeniusRotationCoeff p ha₁ ha₂)

/--
theorem `frobeniusRotation_nonzero` / 定理 `frobeniusRotation_nonzero`

English:
theorem frobeniusRotation_nonzero
  given: {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0)
  proof: by
  intro h
  apply solution_nonzero p ha₁ ha₂
  simpa [← h, frobeniusRotation, frobeniusRotationCoeff] using WittVector.zero_coeff p k 0

中文:
定理 frobeniusRotation_nonzero
  条件: {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0)
  证明: by
  intro h
  apply solution_nonzero p ha₁ ha₂
  simpa [← h, frobeniusRotation, frobeniusRotationCoeff] using WittVector.zero_coeff p k 0

Depends on / 依赖: WittVector, WittVector.zero_coeff, frobeniusRotation, frobeniusRotationCoeff, solution_nonzero, zero_coeff
-/
theorem frobeniusRotation_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) :
    frobeniusRotation p ha₁ ha₂ != 0 := by
  intro h
  apply solution_nonzero p ha₁ ha₂
  simpa [← h, frobeniusRotation, frobeniusRotationCoeff] using WittVector.zero_coeff p k 0

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `frobenius_frobeniusRotation` / 定理 `frobenius_frobeniusRotation`

English:
theorem frobenius_frobeniusRotation
  given: {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0)
  proof: by
  ext n
  rcases n with - | n
  · simp only [WittVector.mul_coeff_zero, WittVector.coeff_frobenius_charP, frobeniusRotation,
      coeff_mk, frobeniusRotationCoeff]
    exact solution_spec' _ ha₁ _
  · simp only [nthRemainder_spec, WittVector.coeff_frobenius_charP,
      frobeniusRotation, coeff_

中文:
定理 frobenius_frobeniusRotation
  条件: {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0)
  证明: by
  ext n
  rcases n with - | n
  · simp only [WittVector.mul_coeff_zero, WittVector.coeff_frobenius_charP, frobeniusRotation,
      coeff_mk, frobeniusRotationCoeff]
    exact solution_spec' _ ha₁ _
  · simp only [nthRemainder_spec, WittVector.coeff_frobenius_charP,
      frobeniusRotation, coeff_

Depends on / 依赖: Fin.val_zero, WittVector, WittVector.coeff_frobenius_charP, WittVector.mul_coeff_zero, coeff_frobenius_charP, coeff_mk, convert, frobeniusRotation, frobeniusRotationCoeff, i.val, mul_coeff_zero, nthRemainder_spec, solution_spec, succNthVal_spec, val_zero
-/
theorem frobenius_frobeniusRotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 != 0) (ha₂ : a₂.coeff 0 != 0) :
    frobenius (frobeniusRotation p ha₁ ha₂) * a₁ = frobeniusRotation p ha₁ ha₂ * a₂ := by
  ext n
  rcases n with - | n
  · simp only [WittVector.mul_coeff_zero, WittVector.coeff_frobenius_charP, frobeniusRotation,
      coeff_mk, frobeniusRotationCoeff]
    exact solution_spec' _ ha₁ _
  · simp only [nthRemainder_spec, WittVector.coeff_frobenius_charP,
      frobeniusRotation, coeff_mk, frobeniusRotationCoeff]
    have :=
      succNthVal_spec' p n a₁ a₂ (fun i : Fin (n + 1) => frobeniusRotationCoeff p ha₁ ha₂ i.val)
        ha₁ ha₂
    simp only [frobeniusRotationCoeff, Fin.val_zero] at this
    convert! this using 3; clear this
    apply TruncatedWittVector.ext
    intro i
    simp only [WittVector.coeff_truncateFun, WittVector.coeff_frobenius_charP]
    rfl

local notation "φ" => IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)

-- Non-terminal simp, used to be field_simp
set_option linter.flexible false in
-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/--
theorem `exists_frobenius_solution_fractionRing_aux` / 定理 `exists_frobenius_solution_fractionRing_aux`

English:
theorem exists_frobenius_solution_fractionRing_aux
  statement: (m n : Nat) (r' q' : 𝕎 k) (hr' : r'.coeff 0 != 0)
  proof: frobeniusRotation p hr' hq'
    IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)
          (algebraMap (𝕎 k) (FractionRing (𝕎 k)) b) *
        Localization.mk ((p : 𝕎 k) ^ m * r') ⟨(p : 𝕎 k) ^ n * q', hq⟩ =
      (p : Localization (nonZeroDivisors (𝕎 k))) ^ (m - n : Int) *
        algebraMap

中文:
定理 exists_frobenius_solution_fractionRing_aux
  结论: (m n : 自然数) (r' q' : 𝕎 k) (hr' : r'.coeff 0 != 0)
  证明: frobeniusRotation p hr' hq'
    IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)
          (algebraMap (𝕎 k) (FractionRing (𝕎 k)) b) *
        Localization.mk ((p : 𝕎 k) ^ m * r') ⟨(p : 𝕎 k) ^ n * q', hq⟩ =
      (p : Localization (nonZeroDivisors (𝕎 k))) ^ (m - n : Int) *
        algebraMap

Depends on / 依赖: frobeniusRotation
-/
theorem exists_frobenius_solution_fractionRing_aux (m n : Nat) (r' q' : 𝕎 k) (hr' : r'.coeff 0 != 0)
    (hq' : q'.coeff 0 != 0) (hq : (p : 𝕎 k) ^ n * q' in nonZeroDivisors (𝕎 k)) :
    let b : 𝕎 k := frobeniusRotation p hr' hq'
    IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)
          (algebraMap (𝕎 k) (FractionRing (𝕎 k)) b) *
        Localization.mk ((p : 𝕎 k) ^ m * r') ⟨(p : 𝕎 k) ^ n * q', hq⟩ =
      (p : Localization (nonZeroDivisors (𝕎 k))) ^ (m - n : Int) *
        algebraMap (𝕎 k) (FractionRing (𝕎 k)) b := by
  intro b
  have key : WittVector.frobenius b * r' = q' * b := by
    linear_combination frobenius_frobeniusRotation p hr' hq'
  have hq'' : algebraMap (𝕎 k) (FractionRing (𝕎 k)) q' != 0 := by
    have hq''' : q' != 0 := fun h => hq' (by simp [h])
    simpa only [Ne, map_zero] using
      (IsFractionRing.injective (𝕎 k) (FractionRing (𝕎 k))).ne hq'''
  rw [zpow_sub₀ (FractionRing.p_nonzero p k)]
  simp [field, FractionRing.p_nonzero p k]
  convert! congr_arg (fun x => algebraMap (𝕎 k) (FractionRing (𝕎 k)) x) key using 1
  · simp only [map_mul]
  · simp only [map_mul]

/--
theorem `exists_frobenius_solution_fractionRing` / 定理 `exists_frobenius_solution_fractionRing`

English:
theorem exists_frobenius_solution_fractionRing
  given: {a : FractionRing (𝕎 k)} (ha : a != 0)
  proof: by
  revert ha
  refine Localization.induction_on a ?_
  rintro ⟨r, q, hq⟩ hrq
  have hq0 : q != 0 := mem_nonZeroDivisors_iff_ne_zero.1 hq
  have hr0 : r != 0 := fun h => hrq (by simp [h])
  obtain ⟨m, r', hr', rfl⟩ := exists_eq_pow_p_mul r hr0
  obtain ⟨n, q', hq', rfl⟩ := exists_eq_pow_p_mul q hq0

中文:
定理 exists_frobenius_solution_fractionRing
  条件: {a : FractionRing (𝕎 k)} (ha : a != 0)
  证明: by
  revert ha
  refine Localization.induction_on a ?_
  rintro ⟨r, q, hq⟩ hrq
  have hq0 : q != 0 := mem_nonZeroDivisors_iff_ne_zero.1 hq
  have hr0 : r != 0 := fun h => hrq (by simp [h])
  obtain ⟨m, r', hr', rfl⟩ := exists_eq_pow_p_mul r hr0
  obtain ⟨n, q', hq', rfl⟩ := exists_eq_pow_p_mul q hq0

Depends on / 依赖: FractionRing, IsFractionRing, IsFractionRing.injective, Localization, Localization.induction_on, WittVector, algebraMap, exists_eq_pow_p_mul, frobeniusRotation, induction_on, injective, map_zero, mem_nonZeroDivisors_iff_ne_zero, revert
-/
theorem exists_frobenius_solution_fractionRing {a : FractionRing (𝕎 k)} (ha : a != 0) :
    existsᵉ (b != 0) (m : Int), φ b * a = (p : FractionRing (𝕎 k)) ^ m * b := by
  revert ha
  refine Localization.induction_on a ?_
  rintro ⟨r, q, hq⟩ hrq
  have hq0 : q != 0 := mem_nonZeroDivisors_iff_ne_zero.1 hq
  have hr0 : r != 0 := fun h => hrq (by simp [h])
  obtain ⟨m, r', hr', rfl⟩ := exists_eq_pow_p_mul r hr0
  obtain ⟨n, q', hq', rfl⟩ := exists_eq_pow_p_mul q hq0
  let b := frobeniusRotation p hr' hq'
  refine ⟨algebraMap (𝕎 k) (FractionRing (𝕎 k)) b, ?_, m - n, ?_⟩
  · simpa only [map_zero] using
      (IsFractionRing.injective (WittVector p k) (FractionRing (WittVector p k))).ne
        (frobeniusRotation_nonzero p hr' hq')
  exact exists_frobenius_solution_fractionRing_aux p m n r' q' hr' hq' hq

end IsAlgClosed

end FrobeniusRotation

end WittVector
