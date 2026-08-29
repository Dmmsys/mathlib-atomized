/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Algebra

/-!
# The Pochhammer polynomials

We define and prove some basic relations about
`ascPochhammer S n : S[X] := X * (X + 1) * ... * (X + n - 1)`
which is also known as the rising factorial and about
`descPochhammer R n : R[X] := X * (X - 1) * ... * (X - n + 1)`
which is also known as the falling factorial. Versions of this definition
that are focused on `Nat` can be found in `Data.Nat.Factorial` as `Nat.ascFactorial` and
`Nat.descFactorial`.

## Implementation

As with many other families of polynomials, even though the coefficients are always in `ℕ` or `ℤ`,
we define the polynomial with coefficients in any `[Semiring S]` or `[Ring R]`.
In an integral domain `S`, we show that `ascPochhammer S n` is zero iff
`n` is a sufficiently large non-positive integer.

## TODO

There is lots more in this direction:
* q-factorials, q-binomials, q-Pochhammer.
-/

@[expose] public section


universe u v

open Polynomial

section Semiring

variable (S : Type u) [Semiring S]

/--
Definition of `ascPochhammer` / `ascPochhammer` 的定义

English:
definition ascPochhammer
  signature: : Nat -> S[X]

中文:
定义 ascPochhammer
  签名: : 自然数 -> S[X]
-/
noncomputable def ascPochhammer : Nat -> S[X]
  | 0 => 1
  | n + 1 => X * (ascPochhammer n).comp (X + 1)

@[simp]
/--
theorem `ascPochhammer_zero` / 定理 `ascPochhammer_zero`

English:
theorem ascPochhammer_zero
  statement: ascPochhammer S 0 = 1
  proof: rfl

@[simp]

中文:
定理 ascPochhammer_zero
  结论: ascPochhammer S 0 = 1
  证明: rfl

@[simp]
-/
theorem ascPochhammer_zero : ascPochhammer S 0 = 1 :=
  rfl

@[simp]
/--
theorem `ascPochhammer_one` / 定理 `ascPochhammer_one`

English:
theorem ascPochhammer_one
  statement: ascPochhammer S 1 = X
  proof: by simp [ascPochhammer]

中文:
定理 ascPochhammer_one
  结论: ascPochhammer S 1 = X
  证明: by simp [ascPochhammer]

Depends on / 依赖: ascPochhammer
-/
theorem ascPochhammer_one : ascPochhammer S 1 = X := by simp [ascPochhammer]

/--
theorem `ascPochhammer_succ_left` / 定理 `ascPochhammer_succ_left`

English:
theorem ascPochhammer_succ_left
  given: (n : Nat)
  proof: by
  rw [ascPochhammer]

中文:
定理 ascPochhammer_succ_left
  条件: (n : 自然数)
  证明: by
  rw [ascPochhammer]

Depends on / 依赖: ascPochhammer
-/
theorem ascPochhammer_succ_left (n : Nat) :
    ascPochhammer S (n + 1) = X * (ascPochhammer S n).comp (X + 1) := by
  rw [ascPochhammer]

/--
theorem `monic_ascPochhammer` / 定理 `monic_ascPochhammer`

English:
theorem monic_ascPochhammer
  given: (n : Nat) [Nontrivial S] [NoZeroDivisors S]
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    have : leadingCoeff (X + 1 : S[X]) = 1 := leadingCoeff_X_add_C 1
    rw [ascPochhammer_succ_left]; rw [Monic.def]; rw [leadingCoeff_mul]; rw [leadingCoeff_comp (ne_zero_of_eq_one <| natDegree_X_add_C 1 : natDegree (X + 1) != 0)]; rw [hn]; r

中文:
定理 monic_ascPochhammer
  条件: (n : 自然数) [非平凡 S] [无零因子 S]
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    have : leadingCoeff (X + 1 : S[X]) = 1 := leadingCoeff_X_add_C 1
    rw [ascPochhammer_succ_left]; rw [Monic.def]; rw [leadingCoeff_mul]; rw [leadingCoeff_comp (ne_zero_of_eq_one <| natDegree_X_add_C 1 : natDegree (X + 1) != 0)]; rw [hn]; r

Depends on / 依赖: Monic.def, ascPochhammer_succ_left, continuousMul_induced, leadingCoeff, leadingCoeff_X_add_C, leadingCoeff_comp, leadingCoeff_mul, monic_X, natDegree, natDegree_X_add_C, ne_zero_of_eq_one, one_mul, one_pow, opMulEquiv, opMulEquiv.symm
-/
theorem monic_ascPochhammer (n : Nat) [Nontrivial S] [NoZeroDivisors S] :
Monic ascPochhammer S n := by
  induction n with
  | zero => simp
  | succ n hn =>
    have : leadingCoeff (X + 1 : S[X]) = 1 := leadingCoeff_X_add_C 1
    rw [ascPochhammer_succ_left]; rw [Monic.def]; rw [leadingCoeff_mul]; rw [leadingCoeff_comp (ne_zero_of_eq_one <| natDegree_X_add_C 1 : natDegree (X + 1) != 0)]; rw [hn]; rw [monic_X]; rw [one_mul]; rw [one_mul]; rw [this]; rw [one_pow]

section

variable {S} {T : Type v} [Semiring T]

@[simp]
/--
theorem `ascPochhammer_map` / 定理 `ascPochhammer_map`

English:
theorem ascPochhammer_map
  given: (f : S ->+* T) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, ascPochhammer_succ_left, map_comp]

中文:
定理 ascPochhammer_map
  条件: (f : S ->+* T) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, ascPochhammer_succ_left, map_comp]

Depends on / 依赖: ascPochhammer_succ_left, map_comp
-/
theorem ascPochhammer_map (f : S ->+* T) (n : Nat) :
    (ascPochhammer S n).map f = ascPochhammer T n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, ascPochhammer_succ_left, map_comp]

/--
theorem `ascPochhammer_eval₂` / 定理 `ascPochhammer_eval₂`

English:
theorem ascPochhammer_eval₂
  given: (f : S ->+* T) (n : Nat) (t : T)
  proof: by
  rw [← ascPochhammer_map f]
  exact eval_map f t

中文:
定理 ascPochhammer_eval₂
  条件: (f : S ->+* T) (n : 自然数) (t : T)
  证明: by
  rw [← ascPochhammer_map f]
  exact eval_map f t

Depends on / 依赖: ascPochhammer_map, eval_map
-/
theorem ascPochhammer_eval₂ (f : S ->+* T) (n : Nat) (t : T) :
    (ascPochhammer T n).eval t = (ascPochhammer S n).eval₂ f t := by
  rw [← ascPochhammer_map f]
  exact eval_map f t

/--
theorem `ascPochhammer_eval_comp` / 定理 `ascPochhammer_eval_comp`

English:
theorem ascPochhammer_eval_comp
  statement: {R : Type*} [CommSemiring R] (n : Nat) (p : R[X]) [Algebra R S]
  proof: by
  rw [ascPochhammer_eval₂ (algebraMap R S)]; rw [← eval₂_comp']; rw [← ascPochhammer_map (algebraMap R S)]; rw [← map_comp]; rw [eval_map]

中文:
定理 ascPochhammer_eval_comp
  结论: {R : 类型} [交换半环 R] (n : 自然数) (p : R[X]) [代数 R S]
  证明: by
  rw [ascPochhammer_eval₂ (algebraMap R S)]; rw [← eval₂_comp']; rw [← ascPochhammer_map (algebraMap R S)]; rw [← map_comp]; rw [eval_map]

Depends on / 依赖: algebraMap, ascPochhammer_map, eval_map, map_comp
-/
theorem ascPochhammer_eval_comp {R : Type*} [CommSemiring R] (n : Nat) (p : R[X]) [Algebra R S]
    (x : S) : ((ascPochhammer S n).comp (p.map (algebraMap R S))).eval x =
    (ascPochhammer S n).eval (p.eval₂ (algebraMap R S) x) := by
  rw [ascPochhammer_eval₂ (algebraMap R S)]; rw [← eval₂_comp']; rw [← ascPochhammer_map (algebraMap R S)]; rw [← map_comp]; rw [eval_map]

end

@[simp, norm_cast]
/--
theorem `ascPochhammer_eval_cast` / 定理 `ascPochhammer_eval_cast`

English:
theorem ascPochhammer_eval_cast
  given: (n k : Nat)
  proof: by
  rw [← ascPochhammer_map (algebraMap Nat S)]; rw [eval_map]; rw [← eq_natCast (algebraMap Nat S)]; rw [eval₂_at_natCast]; rw [Nat.cast_id]

中文:
定理 ascPochhammer_eval_cast
  条件: (n k : 自然数)
  证明: by
  rw [← ascPochhammer_map (algebraMap Nat S)]; rw [eval_map]; rw [← eq_natCast (algebraMap Nat S)]; rw [eval₂_at_natCast]; rw [Nat.cast_id]

Depends on / 依赖: Nat.cast_id, algebraMap, ascPochhammer_map, cast_id, eq_natCast, eval_map
-/
theorem ascPochhammer_eval_cast (n k : Nat) :
    (((ascPochhammer Nat n).eval k : Nat) : S) = ((ascPochhammer S n).eval k : S) := by
  rw [← ascPochhammer_map (algebraMap Nat S)]; rw [eval_map]; rw [← eq_natCast (algebraMap Nat S)]; rw [eval₂_at_natCast]; rw [Nat.cast_id]

/--
theorem `ascPochhammer_eval_zero` / 定理 `ascPochhammer_eval_zero`

English:
theorem ascPochhammer_eval_zero
  given: {n : Nat}
  statement: (ascPochhammer S n).eval 0 = if n = 0 then 1 else 0
  proof: by
  cases n
  · simp
  · simp [X_mul, ascPochhammer_succ_left]

中文:
定理 ascPochhammer_eval_zero
  条件: {n : 自然数}
  结论: (ascPochhammer S n).eval 0 = if n = 0 then 1 else 0
  证明: by
  cases n
  · simp
  · simp [X_mul, ascPochhammer_succ_left]

Depends on / 依赖: X_mul, ascPochhammer_succ_left
-/
theorem ascPochhammer_eval_zero {n : Nat} : (ascPochhammer S n).eval 0 = if n = 0 then 1 else 0 := by
  cases n
  · simp
  · simp [X_mul, ascPochhammer_succ_left]

/--
theorem `ascPochhammer_zero_eval_zero` / 定理 `ascPochhammer_zero_eval_zero`

English:
theorem ascPochhammer_zero_eval_zero
  statement: (ascPochhammer S 0).eval 0 = 1
  proof: by simp

@[simp]

中文:
定理 ascPochhammer_zero_eval_zero
  结论: (ascPochhammer S 0).eval 0 = 1
  证明: by simp

@[simp]
-/
theorem ascPochhammer_zero_eval_zero : (ascPochhammer S 0).eval 0 = 1 := by simp

@[simp]
/--
theorem `ascPochhammer_ne_zero_eval_zero` / 定理 `ascPochhammer_ne_zero_eval_zero`

English:
theorem ascPochhammer_ne_zero_eval_zero
  given: {n : Nat} (h : n != 0)
  statement: (ascPochhammer S n).eval 0 = 0
  proof: by
  simp [ascPochhammer_eval_zero, h]

中文:
定理 ascPochhammer_ne_zero_eval_zero
  条件: {n : 自然数} (h : n != 0)
  结论: (ascPochhammer S n).eval 0 = 0
  证明: by
  simp [ascPochhammer_eval_zero, h]

Depends on / 依赖: ascPochhammer_eval_zero
-/
theorem ascPochhammer_ne_zero_eval_zero {n : Nat} (h : n != 0) : (ascPochhammer S n).eval 0 = 0 := by
  simp [ascPochhammer_eval_zero, h]

/--
theorem `ascPochhammer_succ_right` / 定理 `ascPochhammer_succ_right`

English:
theorem ascPochhammer_succ_right
  given: (n : Nat)
  proof: by
  suffices h : ascPochhammer Nat (n + 1) = ascPochhammer Nat n * (X + (n : Nat[X])) by
    apply_fun Polynomial.map (algebraMap Nat S) at h
    simpa only [ascPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_natCast] using h
  induction n with
  | zero => simp
 

中文:
定理 ascPochhammer_succ_right
  条件: (n : 自然数)
  证明: by
  suffices h : ascPochhammer Nat (n + 1) = ascPochhammer Nat n * (X + (n : Nat[X])) by
    apply_fun Polynomial.map (algebraMap Nat S) at h
    simpa only [ascPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_natCast] using h
  induction n with
  | zero => simp
 

Depends on / 依赖: Polynomial, Polynomial.map, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_natCast, X_comp, add_assoc, add_comm, add_comp, algebraMap, apply_fun, ascPochhammer, ascPochhammer_map, ascPochhammer_succ_left, conv_lhs, map_X, map_add, map_mul, map_natCast, mul_assoc
-/
theorem ascPochhammer_succ_right (n : Nat) :
    ascPochhammer S (n + 1) = ascPochhammer S n * (X + (n : S[X])) := by
  suffices h : ascPochhammer Nat (n + 1) = ascPochhammer Nat n * (X + (n : Nat[X])) by
    apply_fun Polynomial.map (algebraMap Nat S) at h
    simpa only [ascPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_natCast] using h
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs =>
      rw [ascPochhammer_succ_left]; rw [ih]; rw [mul_comp]; rw [← mul_assoc]; rw [← ascPochhammer_succ_left]; rw [add_comp]; rw [X_comp]; rw [natCast_comp]; rw [add_assoc]; rw [add_comm (1 : Nat[X]), ← Nat.cast_succ]

/--
theorem `ascPochhammer_succ_eval` / 定理 `ascPochhammer_succ_eval`

English:
theorem ascPochhammer_succ_eval
  given: {S : Type*} [Semiring S] (n : Nat) (k : S)
  proof: by
  rw [ascPochhammer_succ_right]; rw [mul_add]; rw [eval_add]; rw [eval_mul_X]; rw [← Nat.cast_comm]; rw [← C_eq_natCast]; rw [eval_C_mul]; rw [Nat.cast_comm]; rw [← mul_add]

中文:
定理 ascPochhammer_succ_eval
  条件: {S : 类型} [半环 S] (n : 自然数) (k : S)
  证明: by
  rw [ascPochhammer_succ_right]; rw [mul_add]; rw [eval_add]; rw [eval_mul_X]; rw [← Nat.cast_comm]; rw [← C_eq_natCast]; rw [eval_C_mul]; rw [Nat.cast_comm]; rw [← mul_add]

Depends on / 依赖: C_eq_natCast, Nat.cast_comm, ascPochhammer_succ_right, cast_comm, eval_C_mul, eval_add, eval_mul_X, mul_add
-/
theorem ascPochhammer_succ_eval {S : Type*} [Semiring S] (n : Nat) (k : S) :
    (ascPochhammer S (n + 1)).eval k = (ascPochhammer S n).eval k * (k + n) := by
  rw [ascPochhammer_succ_right]; rw [mul_add]; rw [eval_add]; rw [eval_mul_X]; rw [← Nat.cast_comm]; rw [← C_eq_natCast]; rw [eval_C_mul]; rw [Nat.cast_comm]; rw [← mul_add]

/--
theorem `ascPochhammer_succ_comp_X_add_one` / 定理 `ascPochhammer_succ_comp_X_add_one`

English:
theorem ascPochhammer_succ_comp_X_add_one
  given: (n : Nat)
  proof: by
  suffices (ascPochhammer Nat (n + 1)).comp (X + 1) =
      ascPochhammer Nat (n + 1) + (n + 1) * (ascPochhammer Nat n).comp (X + 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Nat.castRingHom S)) this
  nth_rw 2 [ascPochhammer_succ_left]
  rw [← add_mul]; rw [ascPochhammer_succ_righ

中文:
定理 ascPochhammer_succ_comp_X_add_one
  条件: (n : 自然数)
  证明: by
  suffices (ascPochhammer Nat (n + 1)).comp (X + 1) =
      ascPochhammer Nat (n + 1) + (n + 1) * (ascPochhammer Nat n).comp (X + 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Nat.castRingHom S)) this
  nth_rw 2 [ascPochhammer_succ_left]
  rw [← add_mul]; rw [ascPochhammer_succ_righ

Depends on / 依赖: Nat.castRingHom, Polynomial, Polynomial.map, X_comp, add_assoc, add_comm, add_comp, add_mul, ascPochhammer, ascPochhammer_succ_left, ascPochhammer_succ_right, castRingHom, congr_arg, map_comp, mul_comm, mul_comp, natCast_comp, nth_rw
-/
theorem ascPochhammer_succ_comp_X_add_one (n : Nat) :
    (ascPochhammer S (n + 1)).comp (X + 1) =
      ascPochhammer S (n + 1) + (n + 1) • (ascPochhammer S n).comp (X + 1) := by
  suffices (ascPochhammer Nat (n + 1)).comp (X + 1) =
      ascPochhammer Nat (n + 1) + (n + 1) * (ascPochhammer Nat n).comp (X + 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Nat.castRingHom S)) this
  nth_rw 2 [ascPochhammer_succ_left]
  rw [← add_mul]; rw [ascPochhammer_succ_right Nat n]; rw [mul_comp]; rw [mul_comm]; rw [add_comp]; rw [X_comp]; rw [natCast_comp]; rw [add_comm]; rw [← add_assoc]
  ring

/--
theorem `ascPochhammer_mul` / 定理 `ascPochhammer_mul`

English:
theorem ascPochhammer_mul
  given: (n m : Nat)
  proof: by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_right]; rw [Polynomial.mul_X_add_natCast_comp]; rw [← mul_assoc]; rw [ih]; rw [← add_assoc]; rw [ascPochhammer_succ_right]; rw [Nat.cast_add]; rw [add_assoc]

中文:
定理 ascPochhammer_mul
  条件: (n m : 自然数)
  证明: by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_right]; rw [Polynomial.mul_X_add_natCast_comp]; rw [← mul_assoc]; rw [ih]; rw [← add_assoc]; rw [ascPochhammer_succ_right]; rw [Nat.cast_add]; rw [add_assoc]

Depends on / 依赖: Nat.cast_add, Polynomial, Polynomial.mul_X_add_natCast_comp, add_assoc, ascPochhammer_succ_right, cast_add, mul_X_add_natCast_comp, mul_assoc
-/
theorem ascPochhammer_mul (n m : Nat) :
    ascPochhammer S n * (ascPochhammer S m).comp (X + (n : S[X])) = ascPochhammer S (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_right]; rw [Polynomial.mul_X_add_natCast_comp]; rw [← mul_assoc]; rw [ih]; rw [← add_assoc]; rw [ascPochhammer_succ_right]; rw [Nat.cast_add]; rw [add_assoc]

/--
theorem `ascPochhammer_nat_eq_ascFactorial` / 定理 `ascPochhammer_nat_eq_ascFactorial`

English:
theorem ascPochhammer_nat_eq_ascFactorial
  given: (n : Nat)

中文:
定理 ascPochhammer_nat_eq_ascFactorial
  条件: (n : 自然数)
-/
theorem ascPochhammer_nat_eq_ascFactorial (n : Nat) :
    forall k, (ascPochhammer Nat k).eval n = n.ascFactorial k
  | 0 => by rw [ascPochhammer_zero, eval_one, Nat.ascFactorial_zero]
  | t + 1 => by
    rw [ascPochhammer_succ_right]; rw [eval_mul]; rw [ascPochhammer_nat_eq_ascFactorial n t]; rw [eval_add]; rw [eval_X]; rw [eval_natCast]; rw [Nat.cast_id]; rw [Nat.ascFactorial_succ]; rw [mul_comm]

/--
theorem `ascPochhammer_nat_eq_natCast_ascFactorial` / 定理 `ascPochhammer_nat_eq_natCast_ascFactorial`

English:
theorem ascPochhammer_nat_eq_natCast_ascFactorial
  given: (S : Type*) [Semiring S] (n k : Nat)
  proof: by
  norm_cast
  rw [ascPochhammer_nat_eq_ascFactorial]

中文:
定理 ascPochhammer_nat_eq_natCast_ascFactorial
  条件: (S : 类型) [半环 S] (n k : 自然数)
  证明: by
  norm_cast
  rw [ascPochhammer_nat_eq_ascFactorial]

Depends on / 依赖: ascPochhammer_nat_eq_ascFactorial
-/
theorem ascPochhammer_nat_eq_natCast_ascFactorial (S : Type*) [Semiring S] (n k : Nat) :
    (ascPochhammer S k).eval (n : S) = n.ascFactorial k := by
  norm_cast
  rw [ascPochhammer_nat_eq_ascFactorial]

/--
theorem `ascPochhammer_nat_eq_descFactorial` / 定理 `ascPochhammer_nat_eq_descFactorial`

English:
theorem ascPochhammer_nat_eq_descFactorial
  given: (a b : Nat)
  proof: by
  rw [ascPochhammer_nat_eq_ascFactorial]; rw [Nat.add_descFactorial_eq_ascFactorial']

中文:
定理 ascPochhammer_nat_eq_descFactorial
  条件: (a b : 自然数)
  证明: by
  rw [ascPochhammer_nat_eq_ascFactorial]; rw [Nat.add_descFactorial_eq_ascFactorial']

Depends on / 依赖: Nat.add_descFactorial_eq_ascFactorial, add_descFactorial_eq_ascFactorial, ascPochhammer_nat_eq_ascFactorial
-/
theorem ascPochhammer_nat_eq_descFactorial (a b : Nat) :
    (ascPochhammer Nat b).eval a = (a + b - 1).descFactorial b := by
  rw [ascPochhammer_nat_eq_ascFactorial]; rw [Nat.add_descFactorial_eq_ascFactorial']

/--
theorem `ascPochhammer_nat_eq_natCast_descFactorial` / 定理 `ascPochhammer_nat_eq_natCast_descFactorial`

English:
theorem ascPochhammer_nat_eq_natCast_descFactorial
  given: (S : Type*) [Semiring S] (a b : Nat)
  proof: by
  norm_cast
  rw [ascPochhammer_nat_eq_descFactorial]

@[simp]

中文:
定理 ascPochhammer_nat_eq_natCast_descFactorial
  条件: (S : 类型) [半环 S] (a b : 自然数)
  证明: by
  norm_cast
  rw [ascPochhammer_nat_eq_descFactorial]

@[simp]

Depends on / 依赖: ascPochhammer_nat_eq_descFactorial
-/
theorem ascPochhammer_nat_eq_natCast_descFactorial (S : Type*) [Semiring S] (a b : Nat) :
    (ascPochhammer S b).eval (a : S) = (a + b - 1).descFactorial b := by
  norm_cast
  rw [ascPochhammer_nat_eq_descFactorial]

@[simp]
/--
theorem `ascPochhammer_natDegree` / 定理 `ascPochhammer_natDegree`

English:
theorem ascPochhammer_natDegree
  given: (n : Nat) [NoZeroDivisors S] [Nontrivial S]
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    have : natDegree (X + (n : S[X])) = 1 := natDegree_X_add_C (n : S)
    rw [ascPochhammer_succ_right]; rw [natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one)]; rw [hn]; rw [this]
    cases n
    · simp
· refine ne_zero_

中文:
定理 ascPochhammer_natDegree
  条件: (n : 自然数) [无零因子 S] [非平凡 S]
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    have : natDegree (X + (n : S[X])) = 1 := natDegree_X_add_C (n : S)
    rw [ascPochhammer_succ_right]; rw [natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one)]; rw [hn]; rw [this]
    cases n
    · simp
· refine ne_zero_

Depends on / 依赖: Nat.add_one_pos, Nat.zero_lt_one, add_one_pos, ascPochhammer_succ_right, hn.symm, natDegree, natDegree_X_add_C, natDegree_mul, ne_zero_of_natDegree_gt, this.symm, zero_lt_one
-/
theorem ascPochhammer_natDegree (n : Nat) [NoZeroDivisors S] [Nontrivial S] :
    (ascPochhammer S n).natDegree = n := by
  induction n with
  | zero => simp
  | succ n hn =>
    have : natDegree (X + (n : S[X])) = 1 := natDegree_X_add_C (n : S)
    rw [ascPochhammer_succ_right]; rw [natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one)]; rw [hn]; rw [this]
    cases n
    · simp
· refine ne_zero_of_natDegree_gt hn.symm ▸ Nat.add_one_pos _

end Semiring

section StrictOrderedSemiring

variable {S : Type*} [Semiring S] [PartialOrder S] [IsStrictOrderedRing S]

/--
theorem `ascPochhammer_pos` / 定理 `ascPochhammer_pos`

English:
theorem ascPochhammer_pos
  given: (n : Nat) (s : S) (h : 0 < s)
  statement: 0 < (ascPochhammer S n).eval s
  proof: by
  induction n with
  | zero =>
    simp only [ascPochhammer_zero, eval_one]
    exact zero_lt_one
  | succ n ih =>
    rw [ascPochhammer_succ_right]; rw [mul_add]; rw [eval_add]; rw [← Nat.cast_comm]; rw [eval_natCast_mul]; rw [eval_mul_X]; rw [Nat.cast_comm]; rw [← mul_add]
    exact mul_pos ih 

中文:
定理 ascPochhammer_pos
  条件: (n : 自然数) (s : S) (h : 0 < s)
  结论: 0 < (ascPochhammer S n).eval s
  证明: by
  induction n with
  | zero =>
    simp only [ascPochhammer_zero, eval_one]
    exact zero_lt_one
  | succ n ih =>
    rw [ascPochhammer_succ_right]; rw [mul_add]; rw [eval_add]; rw [← Nat.cast_comm]; rw [eval_natCast_mul]; rw [eval_mul_X]; rw [Nat.cast_comm]; rw [← mul_add]
    exact mul_pos ih 

Depends on / 依赖: Nat.cast_comm, Nat.cast_nonneg, ascPochhammer_succ_right, ascPochhammer_zero, cast_comm, cast_nonneg, eval_add, eval_mul_X, eval_natCast_mul, eval_one, le_add_of_nonneg_right, lt_of_lt_of_le, mul_add, mul_pos, zero_lt_one
-/
theorem ascPochhammer_pos (n : Nat) (s : S) (h : 0 < s) : 0 < (ascPochhammer S n).eval s := by
  induction n with
  | zero =>
    simp only [ascPochhammer_zero, eval_one]
    exact zero_lt_one
  | succ n ih =>
    rw [ascPochhammer_succ_right]; rw [mul_add]; rw [eval_add]; rw [← Nat.cast_comm]; rw [eval_natCast_mul]; rw [eval_mul_X]; rw [Nat.cast_comm]; rw [← mul_add]
    exact mul_pos ih (lt_of_lt_of_le h (le_add_of_nonneg_right (Nat.cast_nonneg n)))

end StrictOrderedSemiring

section Factorial

open Nat

variable (S : Type*) [Semiring S] (r n : Nat)

@[simp]
/--
theorem `ascPochhammer_eval_one` / 定理 `ascPochhammer_eval_one`

English:
theorem ascPochhammer_eval_one
  given: (S : Type*) [Semiring S] (n : Nat)
  proof: by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.one_ascFactorial]

中文:
定理 ascPochhammer_eval_one
  条件: (S : 类型) [半环 S] (n : 自然数)
  证明: by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.one_ascFactorial]

Depends on / 依赖: Nat.one_ascFactorial, ascPochhammer_nat_eq_ascFactorial, one_ascFactorial, rw_mod_cast
-/
theorem ascPochhammer_eval_one (S : Type*) [Semiring S] (n : Nat) :
    (ascPochhammer S n).eval (1 : S) = (n ! : S) := by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.one_ascFactorial]

/--
theorem `factorial_mul_ascPochhammer` / 定理 `factorial_mul_ascPochhammer`

English:
theorem factorial_mul_ascPochhammer
  given: (S : Type*) [Semiring S] (r n : Nat)
  proof: by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.factorial_mul_ascFactorial]

中文:
定理 factorial_mul_ascPochhammer
  条件: (S : 类型) [半环 S] (r n : 自然数)
  证明: by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.factorial_mul_ascFactorial]

Depends on / 依赖: Nat.factorial_mul_ascFactorial, ascPochhammer_nat_eq_ascFactorial, factorial_mul_ascFactorial, rw_mod_cast
-/
theorem factorial_mul_ascPochhammer (S : Type*) [Semiring S] (r n : Nat) :
    (r ! : S) * (ascPochhammer S n).eval (r + 1 : S) = (r + n)! := by
  rw_mod_cast [ascPochhammer_nat_eq_ascFactorial, Nat.factorial_mul_ascFactorial]

/--
theorem `ascPochhammer_nat_eval_succ` / 定理 `ascPochhammer_nat_eval_succ`

English:
theorem ascPochhammer_nat_eval_succ
  given: (r : Nat)

中文:
定理 ascPochhammer_nat_eval_succ
  条件: (r : 自然数)
-/
theorem ascPochhammer_nat_eval_succ (r : Nat) :
    forall n : Nat, n * (ascPochhammer Nat r).eval (n + 1) = (n + r) * (ascPochhammer Nat r).eval n
  | 0 => by
    by_cases h : r = 0
    · simp only [h, zero_mul, zero_add]
    · simp only [ascPochhammer_eval_zero, zero_mul, if_neg h, mul_zero]
  | k + 1 => by simp only [ascPochhammer_nat_eq_ascFactorial, Nat.succ_ascFactorial, add_right_comm]

/--
theorem `ascPochhammer_eval_succ` / 定理 `ascPochhammer_eval_succ`

English:
theorem ascPochhammer_eval_succ
  given: (r n : Nat)
  proof: mod_cast congr_arg Nat.cast (ascPochhammer_nat_eval_succ r n)

中文:
定理 ascPochhammer_eval_succ
  条件: (r n : 自然数)
  证明: mod_cast congr_arg Nat.cast (ascPochhammer_nat_eval_succ r n)

Depends on / 依赖: Nat.cast, ascPochhammer_nat_eval_succ, congr_arg, mod_cast
-/
theorem ascPochhammer_eval_succ (r n : Nat) :
    (n : S) * (ascPochhammer S r).eval (n + 1 : S) =
    (n + r) * (ascPochhammer S r).eval (n : S) :=
  mod_cast congr_arg Nat.cast (ascPochhammer_nat_eval_succ r n)

namespace Nat
variable (a b : Nat)

/--
theorem `cast_ascFactorial` / 定理 `cast_ascFactorial`

English:
theorem cast_ascFactorial
  statement: a.ascFactorial b = (ascPochhammer S b).eval (a : S)
  proof: by
  rw [← ascPochhammer_nat_eq_ascFactorial]; rw [ascPochhammer_eval_cast]

中文:
定理 cast_ascFactorial
  结论: a.ascFactorial b = (ascPochhammer S b).eval (a : S)
  证明: by
  rw [← ascPochhammer_nat_eq_ascFactorial]; rw [ascPochhammer_eval_cast]

Depends on / 依赖: ascPochhammer_eval_cast, ascPochhammer_nat_eq_ascFactorial
-/
theorem cast_ascFactorial : a.ascFactorial b = (ascPochhammer S b).eval (a : S) := by
  rw [← ascPochhammer_nat_eq_ascFactorial]; rw [ascPochhammer_eval_cast]

/--
theorem `cast_descFactorial` / 定理 `cast_descFactorial`

English:
theorem cast_descFactorial
  proof: by
  rw [← ascPochhammer_eval_cast]; rw [ascPochhammer_nat_eq_descFactorial]
  induction b with
  | zero => simp
  | succ b =>
    simp_rw [add_succ, Nat.add_one_sub_one]
    obtain h | h := le_total a b
    · rw [descFactorial_of_lt (lt_succ_of_le h), descFactorial_of_lt (lt_succ_of_le _)]
      rw

中文:
定理 cast_descFactorial
  证明: by
  rw [← ascPochhammer_eval_cast]; rw [ascPochhammer_nat_eq_descFactorial]
  induction b with
  | zero => simp
  | succ b =>
    simp_rw [add_succ, Nat.add_one_sub_one]
    obtain h | h := le_total a b
    · rw [descFactorial_of_lt (lt_succ_of_le h), descFactorial_of_lt (lt_succ_of_le _)]
      rw

Depends on / 依赖: Nat.add_one_sub_one, add_one_sub_one, add_succ, ascPochhammer_eval_cast, ascPochhammer_nat_eq_descFactorial, descFactorial_of_lt, le_total, lt_succ_of_le, simp_rw, tsub_add_cancel_of_le, tsub_eq_zero_iff_le, tsub_eq_zero_iff_le.mpr, zero_add
-/
theorem cast_descFactorial :
    a.descFactorial b = (ascPochhammer S b).eval (a - (b - 1) : S) := by
  rw [← ascPochhammer_eval_cast]; rw [ascPochhammer_nat_eq_descFactorial]
  induction b with
  | zero => simp
  | succ b =>
    simp_rw [add_succ, Nat.add_one_sub_one]
    obtain h | h := le_total a b
    · rw [descFactorial_of_lt (lt_succ_of_le h), descFactorial_of_lt (lt_succ_of_le _)]
      rw [tsub_eq_zero_iff_le.mpr h]; rw [zero_add]
    · rw [tsub_add_cancel_of_le h]

/--
theorem `cast_factorial` / 定理 `cast_factorial`

English:
theorem cast_factorial
  statement: (a ! : S) = (ascPochhammer S a).eval 1
  proof: by
  rw [← one_ascFactorial]; rw [cast_ascFactorial]; rw [cast_one]

中文:
定理 cast_factorial
  结论: (a ! : S) = (ascPochhammer S a).eval 1
  证明: by
  rw [← one_ascFactorial]; rw [cast_ascFactorial]; rw [cast_one]

Depends on / 依赖: cast_ascFactorial, cast_one, one_ascFactorial
-/
theorem cast_factorial : (a ! : S) = (ascPochhammer S a).eval 1 := by
  rw [← one_ascFactorial]; rw [cast_ascFactorial]; rw [cast_one]

end Nat

end Factorial

section Ring

variable (R : Type u) [Ring R]

/--
Definition of `descPochhammer` / `descPochhammer` 的定义

English:
definition descPochhammer
  signature: : Nat -> R[X]

中文:
定义 descPochhammer
  签名: : 自然数 -> R[X]
-/
noncomputable def descPochhammer : Nat -> R[X]
  | 0 => 1
  | n + 1 => X * (descPochhammer n).comp (X - 1)

@[simp]
/--
theorem `descPochhammer_zero` / 定理 `descPochhammer_zero`

English:
theorem descPochhammer_zero
  statement: descPochhammer R 0 = 1
  proof: rfl

@[simp]

中文:
定理 descPochhammer_zero
  结论: descPochhammer R 0 = 1
  证明: rfl

@[simp]
-/
theorem descPochhammer_zero : descPochhammer R 0 = 1 :=
  rfl

@[simp]
/--
theorem `descPochhammer_one` / 定理 `descPochhammer_one`

English:
theorem descPochhammer_one
  statement: descPochhammer R 1 = X
  proof: by simp [descPochhammer]

中文:
定理 descPochhammer_one
  结论: descPochhammer R 1 = X
  证明: by simp [descPochhammer]

Depends on / 依赖: descPochhammer
-/
theorem descPochhammer_one : descPochhammer R 1 = X := by simp [descPochhammer]

/--
theorem `descPochhammer_succ_left` / 定理 `descPochhammer_succ_left`

English:
theorem descPochhammer_succ_left
  given: (n : Nat)
  proof: by
  rw [descPochhammer]

中文:
定理 descPochhammer_succ_left
  条件: (n : 自然数)
  证明: by
  rw [descPochhammer]

Depends on / 依赖: descPochhammer
-/
theorem descPochhammer_succ_left (n : Nat) :
    descPochhammer R (n + 1) = X * (descPochhammer R n).comp (X - 1) := by
  rw [descPochhammer]

/--
theorem `monic_descPochhammer` / 定理 `monic_descPochhammer`

English:
theorem monic_descPochhammer
  given: (n : Nat) [Nontrivial R] [NoZeroDivisors R]
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    have h : leadingCoeff (X - 1 : R[X]) = 1 := leadingCoeff_X_sub_C 1
have : natDegree (X - (1 : R[X])) != 0 := ne_zero_of_eq_one natDegree_X_sub_C (1 : R)
    rw [descPochhammer_succ_left]; rw [Monic.def]; rw [leadingCoeff_mul]; rw [leadingCo

中文:
定理 monic_descPochhammer
  条件: (n : 自然数) [非平凡 R] [无零因子 R]
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    have h : leadingCoeff (X - 1 : R[X]) = 1 := leadingCoeff_X_sub_C 1
have : natDegree (X - (1 : R[X])) != 0 := ne_zero_of_eq_one natDegree_X_sub_C (1 : R)
    rw [descPochhammer_succ_left]; rw [Monic.def]; rw [leadingCoeff_mul]; rw [leadingCo

Depends on / 依赖: Monic.def, descPochhammer_succ_left, leadingCoeff, leadingCoeff_X_sub_C, leadingCoeff_comp, leadingCoeff_mul, monic_X, natDegree, natDegree_X_sub_C, ne_zero_of_eq_one, one_mul, one_pow
-/
theorem monic_descPochhammer (n : Nat) [Nontrivial R] [NoZeroDivisors R] :
Monic descPochhammer R n := by
  induction n with
  | zero => simp
  | succ n hn =>
    have h : leadingCoeff (X - 1 : R[X]) = 1 := leadingCoeff_X_sub_C 1
have : natDegree (X - (1 : R[X])) != 0 := ne_zero_of_eq_one natDegree_X_sub_C (1 : R)
    rw [descPochhammer_succ_left]; rw [Monic.def]; rw [leadingCoeff_mul]; rw [leadingCoeff_comp this]; rw [hn]; rw [monic_X]; rw [one_mul]; rw [one_mul]; rw [h]; rw [one_pow]

section

variable {R} {T : Type v} [Ring T]

@[simp]
/--
theorem `descPochhammer_map` / 定理 `descPochhammer_map`

English:
theorem descPochhammer_map
  given: (f : R ->+* T) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, descPochhammer_succ_left, map_comp]

中文:
定理 descPochhammer_map
  条件: (f : R ->+* T) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, descPochhammer_succ_left, map_comp]

Depends on / 依赖: descPochhammer_succ_left, map_comp
-/
theorem descPochhammer_map (f : R ->+* T) (n : Nat) :
    (descPochhammer R n).map f = descPochhammer T n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, descPochhammer_succ_left, map_comp]
end

@[simp, norm_cast]
/--
theorem `descPochhammer_eval_cast` / 定理 `descPochhammer_eval_cast`

English:
theorem descPochhammer_eval_cast
  given: (n : Nat) (k : Int)
  proof: by
  rw [← descPochhammer_map (algebraMap Int R)]; rw [eval_map]; rw [← eq_intCast (algebraMap Int R)]
  simp only [algebraMap_int_eq, eq_intCast, eval₂_at_intCast, Int.cast_id]

中文:
定理 descPochhammer_eval_cast
  条件: (n : 自然数) (k : 整数)
  证明: by
  rw [← descPochhammer_map (algebraMap Int R)]; rw [eval_map]; rw [← eq_intCast (algebraMap Int R)]
  simp only [algebraMap_int_eq, eq_intCast, eval₂_at_intCast, Int.cast_id]

Depends on / 依赖: Int.cast_id, algebraMap, algebraMap_int_eq, cast_id, descPochhammer_map, eq_intCast, eval_map
-/
theorem descPochhammer_eval_cast (n : Nat) (k : Int) :
    (((descPochhammer Int n).eval k : Int) : R) = ((descPochhammer R n).eval k : R) := by
  rw [← descPochhammer_map (algebraMap Int R)]; rw [eval_map]; rw [← eq_intCast (algebraMap Int R)]
  simp only [algebraMap_int_eq, eq_intCast, eval₂_at_intCast, Int.cast_id]

/--
theorem `descPochhammer_eval_zero` / 定理 `descPochhammer_eval_zero`

English:
theorem descPochhammer_eval_zero
  given: {n : Nat}
  proof: by
  cases n
  · simp
  · simp [X_mul, descPochhammer_succ_left]

中文:
定理 descPochhammer_eval_zero
  条件: {n : 自然数}
  证明: by
  cases n
  · simp
  · simp [X_mul, descPochhammer_succ_left]

Depends on / 依赖: X_mul, descPochhammer_succ_left
-/
theorem descPochhammer_eval_zero {n : Nat} :
    (descPochhammer R n).eval 0 = if n = 0 then 1 else 0 := by
  cases n
  · simp
  · simp [X_mul, descPochhammer_succ_left]

/--
theorem `descPochhammer_zero_eval_zero` / 定理 `descPochhammer_zero_eval_zero`

English:
theorem descPochhammer_zero_eval_zero
  statement: (descPochhammer R 0).eval 0 = 1
  proof: by simp

@[simp]

中文:
定理 descPochhammer_zero_eval_zero
  结论: (descPochhammer R 0).eval 0 = 1
  证明: by simp

@[simp]
-/
theorem descPochhammer_zero_eval_zero : (descPochhammer R 0).eval 0 = 1 := by simp

@[simp]
/--
theorem `descPochhammer_ne_zero_eval_zero` / 定理 `descPochhammer_ne_zero_eval_zero`

English:
theorem descPochhammer_ne_zero_eval_zero
  given: {n : Nat} (h : n != 0)
  statement: (descPochhammer R n).eval 0 = 0
  proof: by
  simp [descPochhammer_eval_zero, h]

中文:
定理 descPochhammer_ne_zero_eval_zero
  条件: {n : 自然数} (h : n != 0)
  结论: (descPochhammer R n).eval 0 = 0
  证明: by
  simp [descPochhammer_eval_zero, h]

Depends on / 依赖: descPochhammer_eval_zero
-/
theorem descPochhammer_ne_zero_eval_zero {n : Nat} (h : n != 0) : (descPochhammer R n).eval 0 = 0 := by
  simp [descPochhammer_eval_zero, h]

/--
theorem `descPochhammer_succ_right` / 定理 `descPochhammer_succ_right`

English:
theorem descPochhammer_succ_right
  given: (n : Nat)
  proof: by
  suffices h : descPochhammer Int (n + 1) = descPochhammer Int n * (X - (n : Int[X])) by
    apply_fun Polynomial.map (algebraMap Int R) at h
    simpa [descPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_intCast] using h
  induction n with
  | zero => simp [de

中文:
定理 descPochhammer_succ_right
  条件: (n : 自然数)
  证明: by
  suffices h : descPochhammer Int (n + 1) = descPochhammer Int n * (X - (n : Int[X])) by
    apply_fun Polynomial.map (algebraMap Int R) at h
    simpa [descPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_intCast] using h
  induction n with
  | zero => simp [de

Depends on / 依赖: Nat.cast_add, Polynomial, Polynomial.map, Polynomial.map_add, Polynomial.map_intCast, Polynomial.map_mul, X_comp, algebraMap, apply_fun, cast_add, conv_lhs, descPochhammer, descPochhammer_map, descPochhammer_succ_left, map_X, map_add, map_intCast, map_mul, mul_assoc, mul_comp
-/
theorem descPochhammer_succ_right (n : Nat) :
    descPochhammer R (n + 1) = descPochhammer R n * (X - (n : R[X])) := by
  suffices h : descPochhammer Int (n + 1) = descPochhammer Int n * (X - (n : Int[X])) by
    apply_fun Polynomial.map (algebraMap Int R) at h
    simpa [descPochhammer_map, Polynomial.map_mul, Polynomial.map_add, map_X,
      Polynomial.map_intCast] using h
  induction n with
  | zero => simp [descPochhammer]
  | succ n ih =>
    conv_lhs =>
      rw [descPochhammer_succ_left]; rw [ih]; rw [mul_comp]; rw [← mul_assoc]; rw [← descPochhammer_succ_left]; rw [sub_comp]; rw [X_comp]; rw [natCast_comp]
    rw [Nat.cast_add]; rw [Nat.cast_one]; rw [sub_add_eq_sub_sub_swap]

@[simp]
/--
theorem `descPochhammer_natDegree` / 定理 `descPochhammer_natDegree`

English:
theorem descPochhammer_natDegree
  given: (n : Nat) [NoZeroDivisors R] [Nontrivial R]
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    have : natDegree (X - (n : R[X])) = 1 := natDegree_X_sub_C (n : R)
    rw [descPochhammer_succ_right]; rw [natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one)]; rw [hn]; rw [this]
    cases n
    · simp
· refine ne_zero

中文:
定理 descPochhammer_natDegree
  条件: (n : 自然数) [无零因子 R] [非平凡 R]
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    have : natDegree (X - (n : R[X])) = 1 := natDegree_X_sub_C (n : R)
    rw [descPochhammer_succ_right]; rw [natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one)]; rw [hn]; rw [this]
    cases n
    · simp
· refine ne_zero

Depends on / 依赖: Nat.add_one_pos, Nat.zero_lt_one, add_one_pos, descPochhammer_succ_right, hn.symm, natDegree, natDegree_X_sub_C, natDegree_mul, ne_zero_of_natDegree_gt, this.symm, zero_lt_one
-/
theorem descPochhammer_natDegree (n : Nat) [NoZeroDivisors R] [Nontrivial R] :
    (descPochhammer R n).natDegree = n := by
  induction n with
  | zero => simp
  | succ n hn =>
    have : natDegree (X - (n : R[X])) = 1 := natDegree_X_sub_C (n : R)
    rw [descPochhammer_succ_right]; rw [natDegree_mul _ (ne_zero_of_natDegree_gt <| this.symm ▸ Nat.zero_lt_one)]; rw [hn]; rw [this]
    cases n
    · simp
· refine ne_zero_of_natDegree_gt hn.symm ▸ Nat.add_one_pos _

/--
theorem `descPochhammer_succ_eval` / 定理 `descPochhammer_succ_eval`

English:
theorem descPochhammer_succ_eval
  given: {S : Type*} [Ring S] (n : Nat) (k : S)
  proof: by
  rw [descPochhammer_succ_right]; rw [mul_sub]; rw [eval_sub]; rw [eval_mul_X]; rw [← Nat.cast_comm]; rw [← C_eq_natCast]; rw [eval_C_mul]; rw [Nat.cast_comm]; rw [← mul_sub]

中文:
定理 descPochhammer_succ_eval
  条件: {S : 类型} [环 S] (n : 自然数) (k : S)
  证明: by
  rw [descPochhammer_succ_right]; rw [mul_sub]; rw [eval_sub]; rw [eval_mul_X]; rw [← Nat.cast_comm]; rw [← C_eq_natCast]; rw [eval_C_mul]; rw [Nat.cast_comm]; rw [← mul_sub]

Depends on / 依赖: C_eq_natCast, Nat.cast_comm, cast_comm, descPochhammer_succ_right, eval_C_mul, eval_mul_X, eval_sub, mul_sub
-/
theorem descPochhammer_succ_eval {S : Type*} [Ring S] (n : Nat) (k : S) :
    (descPochhammer S (n + 1)).eval k = (descPochhammer S n).eval k * (k - n) := by
  rw [descPochhammer_succ_right]; rw [mul_sub]; rw [eval_sub]; rw [eval_mul_X]; rw [← Nat.cast_comm]; rw [← C_eq_natCast]; rw [eval_C_mul]; rw [Nat.cast_comm]; rw [← mul_sub]

/--
theorem `descPochhammer_succ_comp_X_sub_one` / 定理 `descPochhammer_succ_comp_X_sub_one`

English:
theorem descPochhammer_succ_comp_X_sub_one
  given: (n : Nat)
  proof: by
  suffices (descPochhammer Int (n + 1)).comp (X - 1) =
      descPochhammer Int (n + 1) - (n + 1) * (descPochhammer Int n).comp (X - 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Int.castRingHom R)) this
  nth_rw 2 [descPochhammer_succ_left]
  rw [← sub_mul]; rw [descPochhammer_succ

中文:
定理 descPochhammer_succ_comp_X_sub_one
  条件: (n : 自然数)
  证明: by
  suffices (descPochhammer Int (n + 1)).comp (X - 1) =
      descPochhammer Int (n + 1) - (n + 1) * (descPochhammer Int n).comp (X - 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Int.castRingHom R)) this
  nth_rw 2 [descPochhammer_succ_left]
  rw [← sub_mul]; rw [descPochhammer_succ

Depends on / 依赖: Int.castRingHom, Polynomial, Polynomial.map, X_comp, castRingHom, congr_arg, descPochhammer, descPochhammer_succ_left, descPochhammer_succ_right, map_comp, mul_comm, mul_comp, natCast_comp, nth_rw, sub_comp, sub_mul
-/
theorem descPochhammer_succ_comp_X_sub_one (n : Nat) :
    (descPochhammer R (n + 1)).comp (X - 1) =
      descPochhammer R (n + 1) - (n + (1 : R[X])) • (descPochhammer R n).comp (X - 1) := by
  suffices (descPochhammer Int (n + 1)).comp (X - 1) =
      descPochhammer Int (n + 1) - (n + 1) * (descPochhammer Int n).comp (X - 1)
    by simpa [map_comp] using congr_arg (Polynomial.map (Int.castRingHom R)) this
  nth_rw 2 [descPochhammer_succ_left]
  rw [← sub_mul]; rw [descPochhammer_succ_right Int n]; rw [mul_comp]; rw [mul_comm]; rw [sub_comp]; rw [X_comp]; rw [natCast_comp]
  ring

/--
theorem `descPochhammer_eq_ascPochhammer` / 定理 `descPochhammer_eq_ascPochhammer`

English:
theorem descPochhammer_eq_ascPochhammer
  given: (n : Nat)
  proof: by
  induction n with
  | zero => rw [descPochhammer_zero, ascPochhammer_zero, one_comp]
  | succ n ih =>
    rw [Nat.cast_succ]; rw [sub_add]; rw [add_sub_cancel_right]; rw [descPochhammer_succ_right]; rw [ascPochhammer_succ_left]; rw [ih]; rw [X_mul]; rw [mul_X_comp]; rw [comp_assoc]; rw [add_comp

中文:
定理 descPochhammer_eq_ascPochhammer
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => rw [descPochhammer_zero, ascPochhammer_zero, one_comp]
  | succ n ih =>
    rw [Nat.cast_succ]; rw [sub_add]; rw [add_sub_cancel_right]; rw [descPochhammer_succ_right]; rw [ascPochhammer_succ_left]; rw [ih]; rw [X_mul]; rw [mul_X_comp]; rw [comp_assoc]; rw [add_comp

Depends on / 依赖: Nat.cast_succ, X_comp, X_mul, add_comp, add_sub_cancel_right, ascPochhammer_succ_left, ascPochhammer_zero, cast_succ, comp_assoc, descPochhammer_succ_right, descPochhammer_zero, mul_X_comp, one_comp, sub_add
-/
theorem descPochhammer_eq_ascPochhammer (n : Nat) :
    descPochhammer Int n = (ascPochhammer Int n).comp ((X : Int[X]) - n + 1) := by
  induction n with
  | zero => rw [descPochhammer_zero, ascPochhammer_zero, one_comp]
  | succ n ih =>
    rw [Nat.cast_succ]; rw [sub_add]; rw [add_sub_cancel_right]; rw [descPochhammer_succ_right]; rw [ascPochhammer_succ_left]; rw [ih]; rw [X_mul]; rw [mul_X_comp]; rw [comp_assoc]; rw [add_comp]; rw [X_comp]; rw [one_comp]

/--
theorem `descPochhammer_eval_eq_ascPochhammer` / 定理 `descPochhammer_eval_eq_ascPochhammer`

English:
theorem descPochhammer_eval_eq_ascPochhammer
  given: (r : R) (n : Nat)
  proof: by
  induction n with
  | zero => rw [descPochhammer_zero, eval_one, ascPochhammer_zero, eval_one]
  | succ n ih =>
    rw [Nat.cast_succ]; rw [sub_add]; rw [add_sub_cancel_right]; rw [descPochhammer_succ_eval]; rw [ih]; rw [ascPochhammer_succ_left]; rw [X_mul]; rw [eval_mul_X]; rw [show (X + 1 : R[

中文:
定理 descPochhammer_eval_eq_ascPochhammer
  条件: (r : R) (n : 自然数)
  证明: by
  induction n with
  | zero => rw [descPochhammer_zero, eval_one, ascPochhammer_zero, eval_one]
  | succ n ih =>
    rw [Nat.cast_succ]; rw [sub_add]; rw [add_sub_cancel_right]; rw [descPochhammer_succ_eval]; rw [ih]; rw [ascPochhammer_succ_left]; rw [X_mul]; rw [eval_mul_X]; rw [show (X + 1 : R[

Depends on / 依赖: Finite, I.IsMaximal, IsMaximal, Nat.cast_succ, Polynomial, Polynomial.map_add, Polynomial.map_one, X_mul, add_sub_cancel_right, algebraMap, ascPochhammer_eval_comp, ascPochhammer_succ_left, ascPochhammer_zero, cast_succ, descPochhammer_succ_eval, descPochhammer_zero, eval_mul_X, eval_one, map_X, map_add
-/
theorem descPochhammer_eval_eq_ascPochhammer (r : R) (n : Nat) :
    (descPochhammer R n).eval r = (ascPochhammer R n).eval (r - n + 1) := by
  induction n with
  | zero => rw [descPochhammer_zero, eval_one, ascPochhammer_zero, eval_one]
  | succ n ih =>
    rw [Nat.cast_succ]; rw [sub_add]; rw [add_sub_cancel_right]; rw [descPochhammer_succ_eval]; rw [ih]; rw [ascPochhammer_succ_left]; rw [X_mul]; rw [eval_mul_X]; rw [show (X + 1 : R[X]) =
      (X + 1 : Nat[X]).map (algebraMap Nat R) by simp only [Polynomial.map_add, map_X,
      Polynomial.map_one], ascPochhammer_eval_comp, eval₂_add, eval₂_X, eval₂_one]

/--
theorem `descPochhammer_mul` / 定理 `descPochhammer_mul`

English:
theorem descPochhammer_mul
  given: (n m : Nat)
  proof: by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [descPochhammer_succ_right]; rw [Polynomial.mul_X_sub_intCast_comp]; rw [← mul_assoc]; rw [ih]; rw [← add_assoc]; rw [descPochhammer_succ_right]; rw [Nat.cast_add]; rw [sub_add_eq_sub_sub]

中文:
定理 descPochhammer_mul
  条件: (n m : 自然数)
  证明: by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [descPochhammer_succ_right]; rw [Polynomial.mul_X_sub_intCast_comp]; rw [← mul_assoc]; rw [ih]; rw [← add_assoc]; rw [descPochhammer_succ_right]; rw [Nat.cast_add]; rw [sub_add_eq_sub_sub]

Depends on / 依赖: Nat.cast_add, Polynomial, Polynomial.mul_X_sub_intCast_comp, add_assoc, cast_add, descPochhammer_succ_right, mul_X_sub_intCast_comp, mul_assoc, sub_add_eq_sub_sub
-/
theorem descPochhammer_mul (n m : Nat) :
    descPochhammer R n * (descPochhammer R m).comp (X - (n : R[X])) = descPochhammer R (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [descPochhammer_succ_right]; rw [Polynomial.mul_X_sub_intCast_comp]; rw [← mul_assoc]; rw [ih]; rw [← add_assoc]; rw [descPochhammer_succ_right]; rw [Nat.cast_add]; rw [sub_add_eq_sub_sub]

/--
theorem `ascPochhammer_eval_neg_eq_descPochhammer` / 定理 `ascPochhammer_eval_neg_eq_descPochhammer`

English:
theorem ascPochhammer_eval_neg_eq_descPochhammer
  given: (r : R)
  statement: forall (k : Nat),

中文:
定理 ascPochhammer_eval_neg_eq_descPochhammer
  条件: (r : R)
  结论: 对任意 (k : 自然数),
-/
theorem ascPochhammer_eval_neg_eq_descPochhammer (r : R) : forall (k : Nat),
    (ascPochhammer R k).eval (-r) = (-1) ^ k * (descPochhammer R k).eval r
  | 0 => by
    rw [ascPochhammer_zero]; rw [descPochhammer_zero]
    simp only [eval_one, pow_zero, mul_one]
  | (k + 1) => by
    rw [ascPochhammer_succ_right]; rw [mul_add]; rw [eval_add]; rw [eval_mul_X]; rw [← Nat.cast_comm]; rw [eval_natCast_mul]; rw [Nat.cast_comm]; rw [← mul_add]; rw [ascPochhammer_eval_neg_eq_descPochhammer r k]; rw [mul_assoc]; rw [descPochhammer_succ_right]; rw [mul_sub]; rw [eval_sub]; rw [eval_mul_X]; rw [← Nat.cast_comm]; rw [eval_natCast_mul]; rw [pow_add]; rw [pow_one]; rw [mul_assoc ((-1) ^ k) (-1)]; rw [mul_sub]; rw [neg_one_mul]; rw [neg_mul_eq_mul_neg]; rw [Nat.cast_comm]; rw [sub_eq_add_neg]; rw [neg_one_mul]; rw [neg_neg]; rw [← mul_add]

/--
theorem `descPochhammer_eval_eq_descFactorial` / 定理 `descPochhammer_eval_eq_descFactorial`

English:
theorem descPochhammer_eval_eq_descFactorial
  given: (n k : Nat)
  proof: by
  induction k with
  | zero => rw [descPochhammer_zero, eval_one, Nat.descFactorial_zero, Nat.cast_one]
  | succ k ih =>
    rw [descPochhammer_succ_right]; rw [Nat.descFactorial_succ]; rw [mul_sub]; rw [eval_sub]; rw [eval_mul_X]; rw [← Nat.cast_comm k]; rw [eval_natCast_mul]; rw [← Nat.cast_com

中文:
定理 descPochhammer_eval_eq_descFactorial
  条件: (n k : 自然数)
  证明: by
  induction k with
  | zero => rw [descPochhammer_zero, eval_one, Nat.descFactorial_zero, Nat.cast_one]
  | succ k ih =>
    rw [descPochhammer_succ_right]; rw [Nat.descFactorial_succ]; rw [mul_sub]; rw [eval_sub]; rw [eval_mul_X]; rw [← Nat.cast_comm k]; rw [eval_natCast_mul]; rw [← Nat.cast_com

Depends on / 依赖: Nat.cast_comm, Nat.cast_mul, Nat.cast_one, Nat.cast_sub, Nat.cast_zero, Nat.descFactorial_eq_zero_iff_lt.mpr, Nat.descFactorial_succ, Nat.descFactorial_zero, cast_comm, cast_mul, cast_one, cast_sub, cast_zero, descFactorial_eq_zero_iff_lt, descFactorial_succ, descFactorial_zero, descPochhammer_succ_right, descPochhammer_zero, eval_mul_X, eval_natCast_mul
-/
theorem descPochhammer_eval_eq_descFactorial (n k : Nat) :
    (descPochhammer R k).eval (n : R) = n.descFactorial k := by
  induction k with
  | zero => rw [descPochhammer_zero, eval_one, Nat.descFactorial_zero, Nat.cast_one]
  | succ k ih =>
    rw [descPochhammer_succ_right]; rw [Nat.descFactorial_succ]; rw [mul_sub]; rw [eval_sub]; rw [eval_mul_X]; rw [← Nat.cast_comm k]; rw [eval_natCast_mul]; rw [← Nat.cast_comm n]; rw [← sub_mul]; rw [ih]
    by_cases! h : n < k
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, mul_zero, mul_zero, Nat.cast_zero]
    · rw [Nat.cast_mul, Nat.cast_sub h]

/--
theorem `descPochhammer_int_eq_ascFactorial` / 定理 `descPochhammer_int_eq_ascFactorial`

English:
theorem descPochhammer_int_eq_ascFactorial
  given: (a b : Nat)
  proof: by
  rw [← Nat.cast_add]; rw [descPochhammer_eval_eq_descFactorial Int (a + b) b]; rw [Nat.add_descFactorial_eq_ascFactorial]

中文:
定理 descPochhammer_int_eq_ascFactorial
  条件: (a b : 自然数)
  证明: by
  rw [← Nat.cast_add]; rw [descPochhammer_eval_eq_descFactorial Int (a + b) b]; rw [Nat.add_descFactorial_eq_ascFactorial]

Depends on / 依赖: Nat.add_descFactorial_eq_ascFactorial, Nat.cast_add, add_descFactorial_eq_ascFactorial, cast_add, descPochhammer_eval_eq_descFactorial
-/
theorem descPochhammer_int_eq_ascFactorial (a b : Nat) :
    (descPochhammer Int b).eval (a + b : Int) = (a + 1).ascFactorial b := by
  rw [← Nat.cast_add]; rw [descPochhammer_eval_eq_descFactorial Int (a + b) b]; rw [Nat.add_descFactorial_eq_ascFactorial]

variable {R}

/--
theorem `ascPochhammer_eval_neg_coe_nat_of_lt` / 定理 `ascPochhammer_eval_neg_coe_nat_of_lt`

English:
theorem ascPochhammer_eval_neg_coe_nat_of_lt
  given: {n k : Nat} (h : k < n)
  proof: by
  induction n with
  | zero => contradiction
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    rcases lt_trichotomy k n with hkn | rfl | hkn
    · simp [ih hkn]
    · simp
    · lia

中文:
定理 ascPochhammer_eval_neg_coe_nat_of_lt
  条件: {n k : 自然数} (h : k < n)
  证明: by
  induction n with
  | zero => contradiction
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    rcases lt_trichotomy k n with hkn | rfl | hkn
    · simp [ih hkn]
    · simp
    · lia

Depends on / 依赖: ascPochhammer_succ_eval, lt_trichotomy
-/
theorem ascPochhammer_eval_neg_coe_nat_of_lt {n k : Nat} (h : k < n) :
    (ascPochhammer R n).eval (-(k : R)) = 0 := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    rcases lt_trichotomy k n with hkn | rfl | hkn
    · simp [ih hkn]
    · simp
    · lia

/-- Over an integral domain, the Pochhammer polynomial of degree `n` has roots *only* at
`0`, `-1`, ..., `-(n - 1)`. -/
@[simp]
/--
theorem `ascPochhammer_eval_eq_zero_iff` / 定理 `ascPochhammer_eval_eq_zero_iff`

English:
theorem ascPochhammer_eval_eq_zero_iff
  statement: [IsDomain R]
  proof: by
  refine ⟨fun zero' => ?_, fun hrn => ?_⟩
  · induction n with
    | zero => simp only [ascPochhammer_zero, Polynomial.eval_one, one_ne_zero] at zero'
    | succ n ih =>
      rw [ascPochhammer_succ_eval]; rw [mul_eq_zero] at zero'
      cases zero' with
      | inl h =>
        obtain ⟨rn, hrn, 

中文:
定理 ascPochhammer_eval_eq_zero_iff
  结论: [是整环 R]
  证明: by
  refine ⟨fun zero' => ?_, fun hrn => ?_⟩
  · induction n with
    | zero => simp only [ascPochhammer_zero, Polynomial.eval_one, one_ne_zero] at zero'
    | succ n ih =>
      rw [ascPochhammer_succ_eval]; rw [mul_eq_zero] at zero'
      cases zero' with
      | inl h =>
        obtain ⟨rn, hrn, 

Depends on / 依赖: Polynomial, Polynomial.eval_one, ascPochhammer_eval_neg_coe_nat_of_lt, ascPochhammer_succ_eval, ascPochhammer_zero, convert, eq_neg_of_add_eq_zero_right, eval_one, lt_add_one, mul_eq_zero, one_ne_zero
-/
theorem ascPochhammer_eval_eq_zero_iff [IsDomain R]
    (n : Nat) (r : R) : (ascPochhammer R n).eval r = 0 ↔ exists k < n, k = -r := by
  refine ⟨fun zero' => ?_, fun hrn => ?_⟩
  · induction n with
    | zero => simp only [ascPochhammer_zero, Polynomial.eval_one, one_ne_zero] at zero'
    | succ n ih =>
      rw [ascPochhammer_succ_eval]; rw [mul_eq_zero] at zero'
      cases zero' with
      | inl h =>
        obtain ⟨rn, hrn, rrn⟩ := ih h
        exact ⟨rn, by lia, rrn⟩
      | inr h =>
        exact ⟨n, lt_add_one n, eq_neg_of_add_eq_zero_right h⟩
  · obtain ⟨rn, hrn, rnn⟩ := hrn
    convert! ascPochhammer_eval_neg_coe_nat_of_lt hrn
    simp [rnn]

/--
theorem `descPochhammer_eval_coe_nat_of_lt` / 定理 `descPochhammer_eval_coe_nat_of_lt`

English:
theorem descPochhammer_eval_coe_nat_of_lt
  given: {k n : Nat} (h : k < n)
  proof: by
  rw [descPochhammer_eval_eq_ascPochhammer]; rw [sub_add_eq_add_sub]; rw [← Nat.cast_add_one]; rw [← neg_sub]; rw [← Nat.cast_sub h]
  exact ascPochhammer_eval_neg_coe_nat_of_lt (Nat.sub_lt_of_pos_le k.succ_pos h)

中文:
定理 descPochhammer_eval_coe_nat_of_lt
  条件: {k n : 自然数} (h : k < n)
  证明: by
  rw [descPochhammer_eval_eq_ascPochhammer]; rw [sub_add_eq_add_sub]; rw [← Nat.cast_add_one]; rw [← neg_sub]; rw [← Nat.cast_sub h]
  exact ascPochhammer_eval_neg_coe_nat_of_lt (Nat.sub_lt_of_pos_le k.succ_pos h)

Depends on / 依赖: Nat.cast_add_one, Nat.cast_sub, Nat.sub_lt_of_pos_le, ascPochhammer_eval_neg_coe_nat_of_lt, cast_add_one, cast_sub, descPochhammer_eval_eq_ascPochhammer, k.succ_pos, neg_sub, sub_add_eq_add_sub, sub_lt_of_pos_le, succ_pos
-/
theorem descPochhammer_eval_coe_nat_of_lt {k n : Nat} (h : k < n) :
    (descPochhammer R n).eval (k : R) = 0 := by
  rw [descPochhammer_eval_eq_ascPochhammer]; rw [sub_add_eq_add_sub]; rw [← Nat.cast_add_one]; rw [← neg_sub]; rw [← Nat.cast_sub h]
  exact ascPochhammer_eval_neg_coe_nat_of_lt (Nat.sub_lt_of_pos_le k.succ_pos h)

/--
lemma `descPochhammer_eval_eq_prod_range` / 引理 `descPochhammer_eval_eq_prod_range`

English:
lemma descPochhammer_eval_eq_prod_range
  given: {R : Type*} [CommRing R] (n : Nat) (r : R)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp [descPochhammer_succ_right, ih, ← Finset.prod_range_succ]

中文:
引理 descPochhammer_eval_eq_prod_range
  条件: {R : 类型} [交换环 R] (n : 自然数) (r : R)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp [descPochhammer_succ_right, ih, ← Finset.prod_range_succ]

Depends on / 依赖: Finset, Finset.prod_range_succ, descPochhammer_succ_right, prod_range_succ
-/
lemma descPochhammer_eval_eq_prod_range {R : Type*} [CommRing R] (n : Nat) (r : R) :
    (descPochhammer R n).eval r = ∏ j in Finset.range n, (r - j) := by
  induction n with
  | zero => simp
  | succ n ih => simp [descPochhammer_succ_right, ih, ← Finset.prod_range_succ]

end Ring

section StrictOrderedRing

variable {S : Type*} [Ring S] [PartialOrder S] [IsStrictOrderedRing S]

/--
theorem `descPochhammer_pos` / 定理 `descPochhammer_pos`

English:
theorem descPochhammer_pos
  given: {n : Nat} {s : S} (h : n - 1 < s)
  proof: by
  rw [← sub_pos]; rw [← sub_add] at h
  rw [descPochhammer_eval_eq_ascPochhammer]
  exact ascPochhammer_pos n (s - n + 1) h

中文:
定理 descPochhammer_pos
  条件: {n : 自然数} {s : S} (h : n - 1 < s)
  证明: by
  rw [← sub_pos]; rw [← sub_add] at h
  rw [descPochhammer_eval_eq_ascPochhammer]
  exact ascPochhammer_pos n (s - n + 1) h

Depends on / 依赖: ascPochhammer_pos, descPochhammer_eval_eq_ascPochhammer, sub_add, sub_pos
-/
theorem descPochhammer_pos {n : Nat} {s : S} (h : n - 1 < s) :
    0 < (descPochhammer S n).eval s := by
  rw [← sub_pos]; rw [← sub_add] at h
  rw [descPochhammer_eval_eq_ascPochhammer]
  exact ascPochhammer_pos n (s - n + 1) h

/--
theorem `descPochhammer_nonneg` / 定理 `descPochhammer_nonneg`

English:
theorem descPochhammer_nonneg
  given: {n : Nat} {s : S} (h : n - 1 <= s)
  proof: by
  rcases eq_or_lt_of_le h with heq | h
  · rw [← heq, descPochhammer_eval_eq_ascPochhammer,
      sub_sub_cancel_left, neg_add_cancel, ascPochhammer_eval_zero]
    positivity
  · exact (descPochhammer_pos h).le

中文:
定理 descPochhammer_nonneg
  条件: {n : 自然数} {s : S} (h : n - 1 <= s)
  证明: by
  rcases eq_or_lt_of_le h with heq | h
  · rw [← heq, descPochhammer_eval_eq_ascPochhammer,
      sub_sub_cancel_left, neg_add_cancel, ascPochhammer_eval_zero]
    positivity
  · exact (descPochhammer_pos h).le

Depends on / 依赖: ascPochhammer_eval_zero, descPochhammer_eval_eq_ascPochhammer, descPochhammer_pos, eq_or_lt_of_le, neg_add_cancel, sub_sub_cancel_left
-/
theorem descPochhammer_nonneg {n : Nat} {s : S} (h : n - 1 <= s) :
    0 <= (descPochhammer S n).eval s := by
  rcases eq_or_lt_of_le h with heq | h
  · rw [← heq, descPochhammer_eval_eq_ascPochhammer,
      sub_sub_cancel_left, neg_add_cancel, ascPochhammer_eval_zero]
    positivity
  · exact (descPochhammer_pos h).le

/--
theorem `pow_le_descPochhammer_eval` / 定理 `pow_le_descPochhammer_eval`

English:
theorem pow_le_descPochhammer_eval
  given: {n : Nat} {s : S} (h : n - 1 <= s)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one]; rw [add_sub_cancel_right]; rw [← sub_nonneg] at h
    have hsub1 : n - 1 <= s := (sub_le_self (n : S) zero_le_one).trans (le_of_sub_nonneg h)
    rw [pow_succ]; rw [descPochhammer_succ_eval]; rw [Nat.cast_add_one]; rw

中文:
定理 pow_le_descPochhammer_eval
  条件: {n : 自然数} {s : S} (h : n - 1 <= s)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one]; rw [add_sub_cancel_right]; rw [← sub_nonneg] at h
    have hsub1 : n - 1 <= s := (sub_le_self (n : S) zero_le_one).trans (le_of_sub_nonneg h)
    rw [pow_succ]; rw [descPochhammer_succ_eval]; rw [Nat.cast_add_one]; rw

Depends on / 依赖: Nat.cast_add_one, add_sub_cancel_right, cast_add_one, descPochhammer_nonneg, descPochhammer_succ_eval, le_add_of_nonneg_right, le_of_sub_nonneg, le_rfl, mul_le_mul, pow_succ, sub_add, sub_le_self, sub_nonneg, zero_le_one
-/
theorem pow_le_descPochhammer_eval {n : Nat} {s : S} (h : n - 1 <= s) :
    (s - n + 1) ^ n <= (descPochhammer S n).eval s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one]; rw [add_sub_cancel_right]; rw [← sub_nonneg] at h
    have hsub1 : n - 1 <= s := (sub_le_self (n : S) zero_le_one).trans (le_of_sub_nonneg h)
    rw [pow_succ]; rw [descPochhammer_succ_eval]; rw [Nat.cast_add_one]; rw [sub_add]; rw [add_sub_cancel_right]
    apply mul_le_mul _ le_rfl h (descPochhammer_nonneg hsub1)
exact (ih hsub1).trans' pow_le_pow_left₀ h (le_add_of_nonneg_right zero_le_one) n

/--
theorem `monotoneOn_descPochhammer_eval` / 定理 `monotoneOn_descPochhammer_eval`

English:
theorem monotoneOn_descPochhammer_eval
  given: (n : Nat)
  proof: by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    rw [Set.mem_Ici]; rw [Nat.cast_add_one]; rw [add_sub_cancel_right] at ha hb
    have ha_sub1 : n - 1 <= a := (sub_le_self (n : S) zero_le_one).trans ha
    have hb_sub1 : n - 1 <= b := (sub_le_self

中文:
定理 monotoneOn_descPochhammer_eval
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    rw [Set.mem_Ici]; rw [Nat.cast_add_one]; rw [add_sub_cancel_right] at ha hb
    have ha_sub1 : n - 1 <= a := (sub_le_self (n : S) zero_le_one).trans ha
    have hb_sub1 : n - 1 <= b := (sub_le_self

Depends on / 依赖: Nat.cast_add_one, Set.mem_Ici, add_sub_cancel_right, cast_add_one, descPochhammer_nonneg, descPochhammer_succ_eval, ha_sub1, hb_sub1, mem_Ici, monotoneOn_const, mul_le_mul, simp_rw, sub_le_self, sub_le_sub_right, sub_nonneg_of_le, zero_le_one
-/
theorem monotoneOn_descPochhammer_eval (n : Nat) :
    MonotoneOn (descPochhammer S n).eval (Set.Ici (n - 1 : S)) := by
  induction n with
  | zero => simp [monotoneOn_const]
  | succ n ih =>
    intro a ha b hb hab
    rw [Set.mem_Ici]; rw [Nat.cast_add_one]; rw [add_sub_cancel_right] at ha hb
    have ha_sub1 : n - 1 <= a := (sub_le_self (n : S) zero_le_one).trans ha
    have hb_sub1 : n - 1 <= b := (sub_le_self (n : S) zero_le_one).trans hb
    simp_rw [descPochhammer_succ_eval]
    exact mul_le_mul (ih ha_sub1 hb_sub1 hab) (sub_le_sub_right hab (n : S))
      (sub_nonneg_of_le ha) (descPochhammer_nonneg hb_sub1)

end StrictOrderedRing

variable (K : Type*)

namespace Nat
section DivisionSemiring
variable [DivisionSemiring K] [CharZero K]

/--
theorem `cast_choose_eq_ascPochhammer_div` / 定理 `cast_choose_eq_ascPochhammer_div`

English:
theorem cast_choose_eq_ascPochhammer_div
  given: (a b : Nat)
  proof: by
  rw [eq_div_iff_mul_eq (cast_ne_zero.2 b.factorial_ne_zero : (b ! : K) != 0)]; rw [← cast_mul]; rw [mul_comm]; rw [← descFactorial_eq_factorial_mul_choose]; rw [← cast_descFactorial]

中文:
定理 cast_choose_eq_ascPochhammer_div
  条件: (a b : 自然数)
  证明: by
  rw [eq_div_iff_mul_eq (cast_ne_zero.2 b.factorial_ne_zero : (b ! : K) != 0)]; rw [← cast_mul]; rw [mul_comm]; rw [← descFactorial_eq_factorial_mul_choose]; rw [← cast_descFactorial]

Depends on / 依赖: b.factorial_ne_zero, cast_descFactorial, cast_mul, cast_ne_zero, descFactorial_eq_factorial_mul_choose, eq_div_iff_mul_eq, factorial_ne_zero, mul_comm
-/
theorem cast_choose_eq_ascPochhammer_div (a b : Nat) :
    (a.choose b : K) = (ascPochhammer K b).eval ↑(a - (b - 1)) / b ! := by
  rw [eq_div_iff_mul_eq (cast_ne_zero.2 b.factorial_ne_zero : (b ! : K) != 0)]; rw [← cast_mul]; rw [mul_comm]; rw [← descFactorial_eq_factorial_mul_choose]; rw [← cast_descFactorial]

end DivisionSemiring

section DivisionRing
variable [DivisionRing K] [CharZero K]

/--
theorem `cast_choose_eq_descPochhammer_div` / 定理 `cast_choose_eq_descPochhammer_div`

English:
theorem cast_choose_eq_descPochhammer_div
  given: (a b : Nat)
  proof: by
  rw [eq_div_iff_mul_eq (cast_ne_zero.2 b.factorial_ne_zero : (b ! : K) != 0)]; rw [← cast_mul]; rw [mul_comm]; rw [← descFactorial_eq_factorial_mul_choose]; rw [descPochhammer_eval_eq_descFactorial]

中文:
定理 cast_choose_eq_descPochhammer_div
  条件: (a b : 自然数)
  证明: by
  rw [eq_div_iff_mul_eq (cast_ne_zero.2 b.factorial_ne_zero : (b ! : K) != 0)]; rw [← cast_mul]; rw [mul_comm]; rw [← descFactorial_eq_factorial_mul_choose]; rw [descPochhammer_eval_eq_descFactorial]

Depends on / 依赖: b.factorial_ne_zero, cast_mul, cast_ne_zero, descFactorial_eq_factorial_mul_choose, descPochhammer_eval_eq_descFactorial, eq_div_iff_mul_eq, factorial_ne_zero, mul_comm
-/
theorem cast_choose_eq_descPochhammer_div (a b : Nat) :
    (a.choose b : K) = (descPochhammer K b).eval ↑a / b ! := by
  rw [eq_div_iff_mul_eq (cast_ne_zero.2 b.factorial_ne_zero : (b ! : K) != 0)]; rw [← cast_mul]; rw [mul_comm]; rw [← descFactorial_eq_factorial_mul_choose]; rw [descPochhammer_eval_eq_descFactorial]

end DivisionRing
end Nat
