/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Evaluating a polynomial

## Main definitions
* `Polynomial.eval₂`: evaluate `p : R[X]` in `S` given a ring hom `f : R →+* S` and `x : S`.
* `Polynomial.eval`: evaluate `p : R[X]` given `x : R`.
* `Polynomial.IsRoot`: `x : R` is a root of `p : R[X]`.
* `Polynomial.comp`: compose two polynomials `p q : R[X]` by evaluating `p` at `q`.
* `Polynomial.map`: apply `f : R →+* S` to the coefficients of `p : R[X]`.

We also provide the following bundled versions:
* `Polynomial.eval₂AddMonoidHom`, `Polynomial.eval₂RingHom`
* `Polynomial.evalRingHom`
* `Polynomial.compRingHom`
* `Polynomial.mapRingHom`

We include results on applying the definitions to `C`, `X` and ring operations.

-/

@[expose] public section

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : Nat}

section Semiring

variable [Semiring R] {p q r : R[X]}

section

variable [Semiring S]
variable (f : R ->+* S) (x : S)

/-- Evaluate a polynomial `p` given a ring hom `f` from the scalar ring
  to the target and a value `x` for the variable in the target -/
irreducible_def eval₂ (p : R[X]) : S :=
  p.sum fun e a => f a * x ^ e

/--
theorem `eval₂_eq_sum` / 定理 `eval₂_eq_sum`

English:
theorem eval₂_eq_sum
  given: {f : R ->+* S} {x : S}
  statement: p.eval₂ f x = p.sum fun e a => f a * x ^ e
  proof: by
  rw [eval₂_def]

中文:
定理 eval₂_eq_sum
  条件: {f : R ->+* S} {x : S}
  结论: p.eval₂ f x = p.sum fun e a => f a * x ^ e
  证明: by
  rw [eval₂_def]
-/
theorem eval₂_eq_sum {f : R ->+* S} {x : S} : p.eval₂ f x = p.sum fun e a => f a * x ^ e := by
  rw [eval₂_def]

/--
theorem `eval₂_congr` / 定理 `eval₂_congr`

English:
theorem eval₂_congr
  statement: {R S : Type*} [Semiring R] [Semiring S] {f g : R ->+* S} {s t : S}
  proof: by
  rintro rfl rfl rfl; rfl

@[simp]

中文:
定理 eval₂_congr
  结论: {R S : 类型} [Semiring R] [Semiring S] {f g : R ->+* S} {s t : S}
  证明: by
  rintro rfl rfl rfl; rfl

@[simp]
-/
theorem eval₂_congr {R S : Type*} [Semiring R] [Semiring S] {f g : R ->+* S} {s t : S}
    {φ ψ : R[X]} : f = g -> s = t -> φ = ψ -> eval₂ f s φ = eval₂ g t ψ := by
  rintro rfl rfl rfl; rfl

@[simp]
/--
theorem `eval₂_zero` / 定理 `eval₂_zero`

English:
theorem eval₂_zero
  statement: (0 : R[X]).eval₂ f x = 0
  proof: by simp [eval₂_eq_sum]

@[simp]

中文:
定理 eval₂_zero
  结论: (0 : R[X]).eval₂ f x = 0
  证明: by simp [eval₂_eq_sum]

@[simp]
-/
theorem eval₂_zero : (0 : R[X]).eval₂ f x = 0 := by simp [eval₂_eq_sum]

@[simp]
/--
theorem `eval₂_C` / 定理 `eval₂_C`

English:
theorem eval₂_C
  statement: (C a).eval₂ f x = f a
  proof: by simp [eval₂_eq_sum]

@[simp]

中文:
定理 eval₂_C
  结论: (C a).eval₂ f x = f a
  证明: by simp [eval₂_eq_sum]

@[simp]
-/
theorem eval₂_C : (C a).eval₂ f x = f a := by simp [eval₂_eq_sum]

@[simp]
/--
theorem `eval₂_X` / 定理 `eval₂_X`

English:
theorem eval₂_X
  statement: X.eval₂ f x = x
  proof: by simp [eval₂_eq_sum]

@[simp]

中文:
定理 eval₂_X
  结论: X.eval₂ f x = x
  证明: by simp [eval₂_eq_sum]

@[simp]
-/
theorem eval₂_X : X.eval₂ f x = x := by simp [eval₂_eq_sum]

@[simp]
/--
theorem `eval₂_monomial` / 定理 `eval₂_monomial`

English:
theorem eval₂_monomial
  given: {n : Nat} {r : R}
  statement: (monomial n r).eval₂ f x = f r * x ^ n
  proof: by
  simp [eval₂_eq_sum]

@[simp]

中文:
定理 eval₂_monomial
  条件: {n : 自然数} {r : R}
  结论: (monomial n r).eval₂ f x = f r * x ^ n
  证明: by
  simp [eval₂_eq_sum]

@[simp]
-/
theorem eval₂_monomial {n : Nat} {r : R} : (monomial n r).eval₂ f x = f r * x ^ n := by
  simp [eval₂_eq_sum]

@[simp]
/--
theorem `eval₂_X_pow` / 定理 `eval₂_X_pow`

English:
theorem eval₂_X_pow
  given: {n : Nat}
  statement: (X ^ n).eval₂ f x = x ^ n
  proof: by
  rw [X_pow_eq_monomial]
  convert! eval₂_monomial f x (n := n) (r := 1)
  simp

@[simp]

中文:
定理 eval₂_X_pow
  条件: {n : 自然数}
  结论: (X ^ n).eval₂ f x = x ^ n
  证明: by
  rw [X_pow_eq_monomial]
  convert! eval₂_monomial f x (n := n) (r := 1)
  simp

@[simp]

Depends on / 依赖: X_pow_eq_monomial, convert
-/
theorem eval₂_X_pow {n : Nat} : (X ^ n).eval₂ f x = x ^ n := by
  rw [X_pow_eq_monomial]
  convert! eval₂_monomial f x (n := n) (r := 1)
  simp

@[simp]
/--
theorem `eval₂_add` / 定理 `eval₂_add`

English:
theorem eval₂_add
  statement: (p + q).eval₂ f x = p.eval₂ f x + q.eval₂ f x
  proof: by
  simp only [eval₂_eq_sum]
  apply sum_add_index <;> simp [add_mul]

@[simp]

中文:
定理 eval₂_add
  结论: (p + q).eval₂ f x = p.eval₂ f x + q.eval₂ f x
  证明: by
  simp only [eval₂_eq_sum]
  apply sum_add_index <;> simp [add_mul]

@[simp]

Depends on / 依赖: add_mul, sum_add_index
-/
theorem eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.eval₂ f x := by
  simp only [eval₂_eq_sum]
  apply sum_add_index <;> simp [add_mul]

@[simp]
/--
theorem `eval₂_one` / 定理 `eval₂_one`

English:
theorem eval₂_one
  statement: (1 : R[X]).eval₂ f x = 1
  proof: by rw [← C_1, eval₂_C, f.map_one]

中文:
定理 eval₂_one
  结论: (1 : R[X]).eval₂ f x = 1
  证明: by rw [← C_1, eval₂_C, f.map_one]

Depends on / 依赖: f.map_one, map_one
-/
theorem eval₂_one : (1 : R[X]).eval₂ f x = 1 := by rw [← C_1, eval₂_C, f.map_one]

/-- `eval₂AddMonoidHom (f : R →+* S) (x : S)` is the `AddMonoidHom` from
`R[X]` to `S` obtained by evaluating the pushforward of `p` along `f` at `x`. -/
@[simps]
/--
Definition of `eval₂AddMonoidHom` / `eval₂AddMonoidHom` 的定义

English:
definition eval₂AddMonoidHom
  signature: : R[X] ->+ S where
  body: eval₂ f x
  map_zero' := eval₂_zero _ _
  map_add' _ _ := eval₂_add _ _

@[simp]

中文:
定义 eval₂AddMonoidHom
  签名: : R[X] ->+ S where
  定义体: eval₂ f x
  map_zero' := eval₂_zero _ _
  map_add' _ _ := eval₂_add _ _

@[simp]
-/
def eval₂AddMonoidHom : R[X] ->+ S where
  toFun := eval₂ f x
  map_zero' := eval₂_zero _ _
  map_add' _ _ := eval₂_add _ _

@[simp]
/--
theorem `eval₂_natCast` / 定理 `eval₂_natCast`

English:
theorem eval₂_natCast
  given: (n : Nat)
  statement: (n : R[X]).eval₂ f x = n
  proof: by
  induction n with
  | zero => simp only [eval₂_zero, Nat.cast_zero]
  | succ n ih => rw [n.cast_succ, eval₂_add, ih, eval₂_one, n.cast_succ]

@[simp]

中文:
定理 eval₂_natCast
  条件: (n : 自然数)
  结论: (n : R[X]).eval₂ f x = n
  证明: by
  induction n with
  | zero => simp only [eval₂_zero, Nat.cast_zero]
  | succ n ih => rw [n.cast_succ, eval₂_add, ih, eval₂_one, n.cast_succ]

@[simp]

Depends on / 依赖: Nat.cast_zero, cast_succ, cast_zero, n.cast_succ
-/
theorem eval₂_natCast (n : Nat) : (n : R[X]).eval₂ f x = n := by
  induction n with
  | zero => simp only [eval₂_zero, Nat.cast_zero]
  | succ n ih => rw [n.cast_succ, eval₂_add, ih, eval₂_one, n.cast_succ]

@[simp]
/--
lemma `eval₂_ofNat` / 引理 `eval₂_ofNat`

English:
lemma eval₂_ofNat
  given: {S : Type*} [Semiring S] (n : Nat) [n.AtLeastTwo] (f : R ->+* S) (a : S)
  proof: by
  simp [OfNat.ofNat]

中文:
引理 eval₂_ofNat
  条件: {S : 类型} [Semiring S] (n : 自然数) [n.AtLeastTwo] (f : R ->+* S) (a : S)
  证明: by
  simp [OfNat.ofNat]

Depends on / 依赖: OfNat.ofNat
-/
lemma eval₂_ofNat {S : Type*} [Semiring S] (n : Nat) [n.AtLeastTwo] (f : R ->+* S) (a : S) :
    (ofNat(n) : R[X]).eval₂ f a = ofNat(n) := by
  simp [OfNat.ofNat]

variable [Semiring T]

/--
theorem `eval₂_sum` / 定理 `eval₂_sum`

English:
theorem eval₂_sum
  given: (p : T[X]) (g : Nat -> T -> R[X]) (x : S)
  proof: by
  let T : R[X] ->+ S :=
    { toFun := eval₂ f x
      map_zero' := eval₂_zero _ _
      map_add' := fun p q => eval₂_add _ _ }
  have A : forall y, eval₂ f x y = T y := fun y => rfl
  simp only [A]
  rw [sum]; rw [map_sum]; rw [sum]

中文:
定理 eval₂_sum
  条件: (p : T[X]) (g : 自然数 -> T -> R[X]) (x : S)
  证明: by
  let T : R[X] ->+ S :=
    { toFun := eval₂ f x
      map_zero' := eval₂_zero _ _
      map_add' := fun p q => eval₂_add _ _ }
  have A : forall y, eval₂ f x y = T y := fun y => rfl
  simp only [A]
  rw [sum]; rw [map_sum]; rw [sum]

Depends on / 依赖: map_add, map_sum, map_zero
-/
theorem eval₂_sum (p : T[X]) (g : Nat -> T -> R[X]) (x : S) :
    (p.sum g).eval₂ f x = p.sum fun n a => (g n a).eval₂ f x := by
  let T : R[X] ->+ S :=
    { toFun := eval₂ f x
      map_zero' := eval₂_zero _ _
      map_add' := fun p q => eval₂_add _ _ }
  have A : forall y, eval₂ f x y = T y := fun y => rfl
  simp only [A]
  rw [sum]; rw [map_sum]; rw [sum]

/--
theorem `eval₂_list_sum` / 定理 `eval₂_list_sum`

English:
theorem eval₂_list_sum
  given: (l : List R[X]) (x : S)
  statement: eval₂ f x l.sum = (l.map (eval₂ f x)).sum
  proof: map_list_sum (eval₂AddMonoidHom f x) l

中文:
定理 eval₂_list_sum
  条件: (l : List R[X]) (x : S)
  结论: eval₂ f x l.sum = (l.map (eval₂ f x)).sum
  证明: map_list_sum (eval₂AddMonoidHom f x) l

Depends on / 依赖: map_list_sum
-/
theorem eval₂_list_sum (l : List R[X]) (x : S) : eval₂ f x l.sum = (l.map (eval₂ f x)).sum :=
  map_list_sum (eval₂AddMonoidHom f x) l

/--
theorem `eval₂_multiset_sum` / 定理 `eval₂_multiset_sum`

English:
theorem eval₂_multiset_sum
  given: (s : Multiset R[X]) (x : S)
  proof: map_multiset_sum (eval₂AddMonoidHom f x) s

中文:
定理 eval₂_multiset_sum
  条件: (s : Multiset R[X]) (x : S)
  证明: map_multiset_sum (eval₂AddMonoidHom f x) s

Depends on / 依赖: map_multiset_sum
-/
theorem eval₂_multiset_sum (s : Multiset R[X]) (x : S) :
    eval₂ f x s.sum = (s.map (eval₂ f x)).sum :=
  map_multiset_sum (eval₂AddMonoidHom f x) s

/--
theorem `eval₂_finsetSum` / 定理 `eval₂_finsetSum`

English:
theorem eval₂_finsetSum
  given: (s : Finset ι) (g : ι -> R[X]) (x : S)
  proof: map_sum (eval₂AddMonoidHom f x) _ _

@[deprecated (since := "2026-04-08")] alias eval₂_finset_sum := eval₂_finsetSum

中文:
定理 eval₂_finsetSum
  条件: (s : Finset ι) (g : ι -> R[X]) (x : S)
  证明: map_sum (eval₂AddMonoidHom f x) _ _

@[deprecated (since := "2026-04-08")] alias eval₂_finset_sum := eval₂_finsetSum

Depends on / 依赖: map_sum
-/
theorem eval₂_finsetSum (s : Finset ι) (g : ι -> R[X]) (x : S) :
    (∑ i in s, g i).eval₂ f x = ∑ i in s, (g i).eval₂ f x :=
  map_sum (eval₂AddMonoidHom f x) _ _

@[deprecated (since := "2026-04-08")] alias eval₂_finset_sum := eval₂_finsetSum

/--
theorem `eval₂_ofFinsupp` / 定理 `eval₂_ofFinsupp`

English:
theorem eval₂_ofFinsupp
  given: {f : R ->+* S} {x : S} {p : R[Nat]}
  proof: by
  simp only [eval₂_eq_sum, sum, support, coeff]
  rfl

中文:
定理 eval₂_ofFinsupp
  条件: {f : R ->+* S} {x : S} {p : R[自然数]}
  证明: by
  simp only [eval₂_eq_sum, sum, support, coeff]
  rfl

Depends on / 依赖: support
-/
theorem eval₂_ofFinsupp {f : R ->+* S} {x : S} {p : R[Nat]} :
    eval₂ f x (⟨p⟩ : R[X]) = liftNC (↑f) (powersHom S x) p := by
  simp only [eval₂_eq_sum, sum, support, coeff]
  rfl

/--
theorem `eval₂_mul_noncomm` / 定理 `eval₂_mul_noncomm`

English:
theorem eval₂_mul_noncomm
  given: (hf : forall k, Commute (f <| q.coeff k) x)
  proof: by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  simp only [coeff] at hf
  simp only [← ofFinsupp_mul, eval₂_ofFinsupp]
  exact liftNC_mul _ _ p q fun {k n} _hn => (hf k).pow_right n

@[simp]

中文:
定理 eval₂_mul_noncomm
  条件: (hf : 对任意 k, Commute (f <| q.coeff k) x)
  证明: by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  simp only [coeff] at hf
  simp only [← ofFinsupp_mul, eval₂_ofFinsupp]
  exact liftNC_mul _ _ p q fun {k n} _hn => (hf k).pow_right n

@[simp]

Depends on / 依赖: liftNC_mul, ofFinsupp_mul, pow_right
-/
theorem eval₂_mul_noncomm (hf : forall k, Commute (f <| q.coeff k) x) :
    eval₂ f x (p * q) = eval₂ f x p * eval₂ f x q := by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  simp only [coeff] at hf
  simp only [← ofFinsupp_mul, eval₂_ofFinsupp]
  exact liftNC_mul _ _ p q fun {k n} _hn => (hf k).pow_right n

@[simp]
/--
theorem `eval₂_mul_X` / 定理 `eval₂_mul_X`

English:
theorem eval₂_mul_X
  statement: eval₂ f x (p * X) = eval₂ f x p * x
  proof: by
  refine _root_.trans (eval₂_mul_noncomm _ _ fun k => ?_) (by rw [eval₂_X])
  rcases em (k = 1) with (rfl | hk)
  · simp
  · simp [coeff_X_of_ne_one hk]

@[simp]

中文:
定理 eval₂_mul_X
  结论: eval₂ f x (p * X) = eval₂ f x p * x
  证明: by
  refine _root_.trans (eval₂_mul_noncomm _ _ fun k => ?_) (by rw [eval₂_X])
  rcases em (k = 1) with (rfl | hk)
  · simp
  · simp [coeff_X_of_ne_one hk]

@[simp]

Depends on / 依赖: _root_, _root_.trans, coeff_X_of_ne_one
-/
theorem eval₂_mul_X : eval₂ f x (p * X) = eval₂ f x p * x := by
  refine _root_.trans (eval₂_mul_noncomm _ _ fun k => ?_) (by rw [eval₂_X])
  rcases em (k = 1) with (rfl | hk)
  · simp
  · simp [coeff_X_of_ne_one hk]

@[simp]
/--
theorem `eval₂_X_mul` / 定理 `eval₂_X_mul`

English:
theorem eval₂_X_mul
  statement: eval₂ f x (X * p) = eval₂ f x p * x
  proof: by rw [X_mul, eval₂_mul_X]

中文:
定理 eval₂_X_mul
  结论: eval₂ f x (X * p) = eval₂ f x p * x
  证明: by rw [X_mul, eval₂_mul_X]

Depends on / 依赖: X_mul
-/
theorem eval₂_X_mul : eval₂ f x (X * p) = eval₂ f x p * x := by rw [X_mul, eval₂_mul_X]

/--
theorem `eval₂_mul_C'` / 定理 `eval₂_mul_C'`

English:
theorem eval₂_mul_C'
  given: (h : Commute (f a) x)
  statement: eval₂ f x (p * C a) = eval₂ f x p * f a
  proof: by
  rw [eval₂_mul_noncomm]; rw [eval₂_C]
  intro k
  by_cases hk : k = 0
  · simp only [hk, h, coeff_C_zero]
  · simp only [coeff_C_of_ne_zero hk, map_zero, Commute.zero_left]

中文:
定理 eval₂_mul_C'
  条件: (h : Commute (f a) x)
  结论: eval₂ f x (p * C a) = eval₂ f x p * f a
  证明: by
  rw [eval₂_mul_noncomm]; rw [eval₂_C]
  intro k
  by_cases hk : k = 0
  · simp only [hk, h, coeff_C_zero]
  · simp only [coeff_C_of_ne_zero hk, map_zero, Commute.zero_left]

Depends on / 依赖: Commute, Commute.zero_left, coeff_C_of_ne_zero, coeff_C_zero, map_zero, zero_left
-/
theorem eval₂_mul_C' (h : Commute (f a) x) : eval₂ f x (p * C a) = eval₂ f x p * f a := by
  rw [eval₂_mul_noncomm]; rw [eval₂_C]
  intro k
  by_cases hk : k = 0
  · simp only [hk, h, coeff_C_zero]
  · simp only [coeff_C_of_ne_zero hk, map_zero, Commute.zero_left]

/--
theorem `eval₂_list_prod_noncomm` / 定理 `eval₂_list_prod_noncomm`

English:
theorem eval₂_list_prod_noncomm
  statement: (ps : List R[X])
  proof: by
  induction ps using List.reverseRecOn with
  | nil => simp
  | append_singleton ps p ihp =>
    simp only [List.forall_mem_append, List.forall_mem_singleton] at hf
    simp [eval₂_mul_noncomm _ _ hf.2, ihp hf.1]

中文:
定理 eval₂_list_prod_noncomm
  结论: (ps : List R[X])
  证明: by
  induction ps using List.reverseRecOn with
  | nil => simp
  | append_singleton ps p ihp =>
    simp only [List.forall_mem_append, List.forall_mem_singleton] at hf
    simp [eval₂_mul_noncomm _ _ hf.2, ihp hf.1]

Depends on / 依赖: List.forall_mem_append, List.forall_mem_singleton, List.reverseRecOn, append_singleton, forall_mem_append, forall_mem_singleton, reverseRecOn
-/
theorem eval₂_list_prod_noncomm (ps : List R[X])
    (hf : forall p in ps, forall (k), Commute (f <| coeff p k) x) :
    eval₂ f x ps.prod = (ps.map (Polynomial.eval₂ f x)).prod := by
  induction ps using List.reverseRecOn with
  | nil => simp
  | append_singleton ps p ihp =>
    simp only [List.forall_mem_append, List.forall_mem_singleton] at hf
    simp [eval₂_mul_noncomm _ _ hf.2, ihp hf.1]

/-- `eval₂` as a `RingHom` for noncommutative rings -/
@[simps]
/--
Definition of `eval₂RingHom'` / `eval₂RingHom'` 的定义

English:
definition eval₂RingHom'
  signature: (f : R ->+* S) (x : S) (hf : forall a, Commute (f a) x)
  body: eval₂ f x
  map_add' _ _ := eval₂_add _ _
  map_zero' := eval₂_zero _ _
map_mul' _p q := eval₂_mul_noncomm f x fun k => hf coeff q k
  map_one' := eval₂_one _ _

中文:
定义 eval₂RingHom'
  签名: (f : R ->+* S) (x : S) (hf : 对任意 a, Commute (f a) x)
  定义体: eval₂ f x
  map_add' _ _ := eval₂_add _ _
  map_zero' := eval₂_zero _ _
map_mul' _p q := eval₂_mul_noncomm f x fun k => hf coeff q k
  map_one' := eval₂_one _ _
-/
def eval₂RingHom' (f : R ->+* S) (x : S) (hf : forall a, Commute (f a) x) : R[X] ->+* S where
  toFun := eval₂ f x
  map_add' _ _ := eval₂_add _ _
  map_zero' := eval₂_zero _ _
map_mul' _p q := eval₂_mul_noncomm f x fun k => hf coeff q k
  map_one' := eval₂_one _ _

end

/-!
We next prove that eval₂ is multiplicative
as long as target ring is commutative
(even if the source ring is not).
-/


section Eval₂

section

variable [CommSemiring S] (f : R ->+* S) (x : S)

@[simp]
/--
theorem `eval₂_mul` / 定理 `eval₂_mul`

English:
theorem eval₂_mul
  statement: (p * q).eval₂ f x = p.eval₂ f x * q.eval₂ f x
  proof: eval₂_mul_noncomm _ _ fun _k => Commute.all _ _

中文:
定理 eval₂_mul
  结论: (p * q).eval₂ f x = p.eval₂ f x * q.eval₂ f x
  证明: eval₂_mul_noncomm _ _ fun _k => Commute.all _ _

Depends on / 依赖: Commute, Commute.all
-/
theorem eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.eval₂ f x :=
  eval₂_mul_noncomm _ _ fun _k => Commute.all _ _

/--
theorem `eval₂_mul_eq_zero_of_left` / 定理 `eval₂_mul_eq_zero_of_left`

English:
theorem eval₂_mul_eq_zero_of_left
  given: (q : R[X]) (hp : p.eval₂ f x = 0)
  statement: (p * q).eval₂ f x = 0
  proof: by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_left hp (q.eval₂ f x)

中文:
定理 eval₂_mul_eq_zero_of_left
  条件: (q : R[X]) (hp : p.eval₂ f x = 0)
  结论: (p * q).eval₂ f x = 0
  证明: by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_left hp (q.eval₂ f x)

Depends on / 依赖: mul_eq_zero_of_left, q.eval
-/
theorem eval₂_mul_eq_zero_of_left (q : R[X]) (hp : p.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_left hp (q.eval₂ f x)

/--
theorem `eval₂_mul_eq_zero_of_right` / 定理 `eval₂_mul_eq_zero_of_right`

English:
theorem eval₂_mul_eq_zero_of_right
  given: (p : R[X]) (hq : q.eval₂ f x = 0)
  statement: (p * q).eval₂ f x = 0
  proof: by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_right (p.eval₂ f x) hq

中文:
定理 eval₂_mul_eq_zero_of_right
  条件: (p : R[X]) (hq : q.eval₂ f x = 0)
  结论: (p * q).eval₂ f x = 0
  证明: by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_right (p.eval₂ f x) hq

Depends on / 依赖: mul_eq_zero_of_right, p.eval
-/
theorem eval₂_mul_eq_zero_of_right (p : R[X]) (hq : q.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_right (p.eval₂ f x) hq

/--
Definition of `eval₂RingHom` / `eval₂RingHom` 的定义

English:
definition eval₂RingHom
  signature: (f : R ->+* S) (x : S)
  body: { eval₂AddMonoidHom f x with
    map_one' := eval₂_one _ _
    map_mul' := fun _ _ => eval₂_mul _ _ }

@[simp]

中文:
定义 eval₂RingHom
  签名: (f : R ->+* S) (x : S)
  定义体: { eval₂AddMonoidHom f x with
    map_one' := eval₂_one _ _
    map_mul' := fun _ _ => eval₂_mul _ _ }

@[simp]

Depends on / 依赖: map_mul, map_one
-/
def eval₂RingHom (f : R ->+* S) (x : S) : R[X] ->+* S :=
  { eval₂AddMonoidHom f x with
    map_one' := eval₂_one _ _
    map_mul' := fun _ _ => eval₂_mul _ _ }

@[simp]
/--
theorem `coe_eval₂RingHom` / 定理 `coe_eval₂RingHom`

English:
theorem coe_eval₂RingHom
  given: (f : R ->+* S) (x)
  statement: ⇑(eval₂RingHom f x) = eval₂ f x
  proof: rfl

@[simp]

中文:
定理 coe_eval₂RingHom
  条件: (f : R ->+* S) (x)
  结论: ⇑(eval₂RingHom f x) = eval₂ f x
  证明: rfl

@[simp]
-/
theorem coe_eval₂RingHom (f : R ->+* S) (x) : ⇑(eval₂RingHom f x) = eval₂ f x :=
  rfl

@[simp]
/--
theorem `eval₂RingHom_comp_C` / 定理 `eval₂RingHom_comp_C`

English:
theorem eval₂RingHom_comp_C
  given: (f : R ->+* S) (x : S)
  statement: (eval₂RingHom f x).comp C = f
  proof: by
  ext
  simp

中文:
定理 eval₂RingHom_comp_C
  条件: (f : R ->+* S) (x : S)
  结论: (eval₂RingHom f x).comp C = f
  证明: by
  ext
  simp
-/
theorem eval₂RingHom_comp_C (f : R ->+* S) (x : S) : (eval₂RingHom f x).comp C = f := by
  ext
  simp

/--
theorem `eval₂_pow` / 定理 `eval₂_pow`

English:
theorem eval₂_pow
  given: (n : Nat)
  statement: (p ^ n).eval₂ f x = p.eval₂ f x ^ n
  proof: (eval₂RingHom _ _).map_pow _ _

@[gcongr]

中文:
定理 eval₂_pow
  条件: (n : 自然数)
  结论: (p ^ n).eval₂ f x = p.eval₂ f x ^ n
  证明: (eval₂RingHom _ _).map_pow _ _

@[gcongr]

Depends on / 依赖: map_pow
-/
theorem eval₂_pow (n : Nat) : (p ^ n).eval₂ f x = p.eval₂ f x ^ n :=
  (eval₂RingHom _ _).map_pow _ _

@[gcongr]
/--
theorem `eval₂_dvd` / 定理 `eval₂_dvd`

English:
theorem eval₂_dvd
  statement: p ∣ q -> eval₂ f x p ∣ eval₂ f x q
  proof: map_dvd (eval₂RingHom f x)

中文:
定理 eval₂_dvd
  结论: p ∣ q -> eval₂ f x p ∣ eval₂ f x q
  证明: map_dvd (eval₂RingHom f x)

Depends on / 依赖: map_dvd
-/
theorem eval₂_dvd : p ∣ q -> eval₂ f x p ∣ eval₂ f x q :=
  map_dvd (eval₂RingHom f x)

/--
theorem `eval₂_eq_zero_of_dvd_of_eval₂_eq_zero` / 定理 `eval₂_eq_zero_of_dvd_of_eval₂_eq_zero`

English:
theorem eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
  given: (h : p ∣ q) (h0 : eval₂ f x p = 0)
  proof: zero_dvd_iff.mp (h0 ▸ eval₂_dvd f x h)

中文:
定理 eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
  条件: (h : p ∣ q) (h0 : eval₂ f x p = 0)
  证明: zero_dvd_iff.mp (h0 ▸ eval₂_dvd f x h)

Depends on / 依赖: zero_dvd_iff, zero_dvd_iff.mp
-/
theorem eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (h : p ∣ q) (h0 : eval₂ f x p = 0) :
    eval₂ f x q = 0 :=
  zero_dvd_iff.mp (h0 ▸ eval₂_dvd f x h)

/--
theorem `eval₂_list_prod` / 定理 `eval₂_list_prod`

English:
theorem eval₂_list_prod
  given: (l : List R[X]) (x : S)
  statement: eval₂ f x l.prod = (l.map (eval₂ f x)).prod
  proof: map_list_prod (eval₂RingHom f x) l

中文:
定理 eval₂_list_prod
  条件: (l : List R[X]) (x : S)
  结论: eval₂ f x l.prod = (l.map (eval₂ f x)).prod
  证明: map_list_prod (eval₂RingHom f x) l

Depends on / 依赖: map_list_prod
-/
theorem eval₂_list_prod (l : List R[X]) (x : S) : eval₂ f x l.prod = (l.map (eval₂ f x)).prod :=
  map_list_prod (eval₂RingHom f x) l

end

end Eval₂

section Eval

variable {x : R}

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (x : R) (p : R[X])
  body: eval₂ (RingHom.id _) x p

@[simp]

中文:
定义 eval
  签名: (x : R) (p : R[X])
  定义体: eval₂ (RingHom.id _) x p

@[simp]

Depends on / 依赖: RingHom, RingHom.id
-/
def eval (x : R) (p : R[X]) : R :=
  eval₂ (RingHom.id _) x p

@[simp]
/--
theorem `eval₂_id` / 定理 `eval₂_id`

English:
theorem eval₂_id
  statement: eval₂ (RingHom.id _) x p = p.eval x
  proof: rfl

中文:
定理 eval₂_id
  结论: eval₂ (RingHom.id _) x p = p.eval x
  证明: rfl
-/
theorem eval₂_id : eval₂ (RingHom.id _) x p = p.eval x := rfl

/--
theorem `eval_eq_sum` / 定理 `eval_eq_sum`

English:
theorem eval_eq_sum
  statement: p.eval x = p.sum fun e a => a * x ^ e
  proof: by
  rw [eval]; rw [eval₂_eq_sum]
  rfl

@[simp]

中文:
定理 eval_eq_sum
  结论: p.eval x = p.sum fun e a => a * x ^ e
  证明: by
  rw [eval]; rw [eval₂_eq_sum]
  rfl

@[simp]
-/
theorem eval_eq_sum : p.eval x = p.sum fun e a => a * x ^ e := by
  rw [eval]; rw [eval₂_eq_sum]
  rfl

@[simp]
/--
theorem `eval₂_at_apply` / 定理 `eval₂_at_apply`

English:
theorem eval₂_at_apply
  given: {S : Type*} [Semiring S] (f : R ->+* S) (r : R)
  proof: by
  rw [eval₂_eq_sum]; rw [eval_eq_sum]; rw [sum]; rw [sum]; rw [map_sum f]
  simp only [f.map_mul, f.map_pow]

@[simp]

中文:
定理 eval₂_at_apply
  条件: {S : 类型} [Semiring S] (f : R ->+* S) (r : R)
  证明: by
  rw [eval₂_eq_sum]; rw [eval_eq_sum]; rw [sum]; rw [sum]; rw [map_sum f]
  simp only [f.map_mul, f.map_pow]

@[simp]

Depends on / 依赖: eval_eq_sum, f.map_mul, f.map_pow, map_mul, map_pow, map_sum
-/
theorem eval₂_at_apply {S : Type*} [Semiring S] (f : R ->+* S) (r : R) :
    p.eval₂ f (f r) = f (p.eval r) := by
  rw [eval₂_eq_sum]; rw [eval_eq_sum]; rw [sum]; rw [sum]; rw [map_sum f]
  simp only [f.map_mul, f.map_pow]

@[simp]
/--
theorem `eval₂_at_one` / 定理 `eval₂_at_one`

English:
theorem eval₂_at_one
  given: {S : Type*} [Semiring S] (f : R ->+* S)
  statement: p.eval₂ f 1 = f (p.eval 1)
  proof: by
  convert! eval₂_at_apply (p := p) f 1
  simp

@[simp]

中文:
定理 eval₂_at_one
  条件: {S : 类型} [Semiring S] (f : R ->+* S)
  结论: p.eval₂ f 1 = f (p.eval 1)
  证明: by
  convert! eval₂_at_apply (p := p) f 1
  simp

@[simp]

Depends on / 依赖: convert
-/
theorem eval₂_at_one {S : Type*} [Semiring S] (f : R ->+* S) : p.eval₂ f 1 = f (p.eval 1) := by
  convert! eval₂_at_apply (p := p) f 1
  simp

@[simp]
/--
theorem `eval₂_at_natCast` / 定理 `eval₂_at_natCast`

English:
theorem eval₂_at_natCast
  given: {S : Type*} [Semiring S] (f : R ->+* S) (n : Nat)
  proof: by
  convert! eval₂_at_apply (p := p) f n
  simp

@[simp]

中文:
定理 eval₂_at_natCast
  条件: {S : 类型} [Semiring S] (f : R ->+* S) (n : 自然数)
  证明: by
  convert! eval₂_at_apply (p := p) f n
  simp

@[simp]

Depends on / 依赖: convert
-/
theorem eval₂_at_natCast {S : Type*} [Semiring S] (f : R ->+* S) (n : Nat) :
    p.eval₂ f n = f (p.eval n) := by
  convert! eval₂_at_apply (p := p) f n
  simp

@[simp]
/--
theorem `eval₂_at_ofNat` / 定理 `eval₂_at_ofNat`

English:
theorem eval₂_at_ofNat
  given: {S : Type*} [Semiring S] (f : R ->+* S) (n : Nat) [n.AtLeastTwo]
  proof: by
  simp [OfNat.ofNat]

@[simp]

中文:
定理 eval₂_at_ofNat
  条件: {S : 类型} [Semiring S] (f : R ->+* S) (n : 自然数) [n.AtLeastTwo]
  证明: by
  simp [OfNat.ofNat]

@[simp]

Depends on / 依赖: OfNat.ofNat
-/
theorem eval₂_at_ofNat {S : Type*} [Semiring S] (f : R ->+* S) (n : Nat) [n.AtLeastTwo] :
    p.eval₂ f ofNat(n) = f (p.eval (ofNat(n))) := by
  simp [OfNat.ofNat]

@[simp]
/--
theorem `eval_C` / 定理 `eval_C`

English:
theorem eval_C
  statement: (C a).eval x = a
  proof: eval₂_C _ _

@[simp]

中文:
定理 eval_C
  结论: (C a).eval x = a
  证明: eval₂_C _ _

@[simp]
-/
theorem eval_C : (C a).eval x = a :=
  eval₂_C _ _

@[simp]
/--
theorem `eval_natCast` / 定理 `eval_natCast`

English:
theorem eval_natCast
  given: {n : Nat}
  statement: (n : R[X]).eval x = n
  proof: by simp only [← C_eq_natCast, eval_C]

@[simp]

中文:
定理 eval_natCast
  条件: {n : 自然数}
  结论: (n : R[X]).eval x = n
  证明: by simp only [← C_eq_natCast, eval_C]

@[simp]

Depends on / 依赖: C_eq_natCast, eval_C
-/
theorem eval_natCast {n : Nat} : (n : R[X]).eval x = n := by simp only [← C_eq_natCast, eval_C]

@[simp]
/--
lemma `eval_ofNat` / 引理 `eval_ofNat`

English:
lemma eval_ofNat
  given: (n : Nat) [n.AtLeastTwo] (a : R)
  proof: by
  simp only [OfNat.ofNat, eval_natCast]

@[simp]

中文:
引理 eval_ofNat
  条件: (n : 自然数) [n.AtLeastTwo] (a : R)
  证明: by
  simp only [OfNat.ofNat, eval_natCast]

@[simp]

Depends on / 依赖: OfNat.ofNat, eval_natCast
-/
lemma eval_ofNat (n : Nat) [n.AtLeastTwo] (a : R) :
    (ofNat(n) : R[X]).eval a = ofNat(n) := by
  simp only [OfNat.ofNat, eval_natCast]

@[simp]
/--
theorem `eval_X` / 定理 `eval_X`

English:
theorem eval_X
  statement: X.eval x = x
  proof: eval₂_X _ _

@[simp]

中文:
定理 eval_X
  结论: X.eval x = x
  证明: eval₂_X _ _

@[simp]
-/
theorem eval_X : X.eval x = x :=
  eval₂_X _ _

@[simp]
/--
theorem `eval_monomial` / 定理 `eval_monomial`

English:
theorem eval_monomial
  given: {n a}
  statement: (monomial n a).eval x = a * x ^ n
  proof: eval₂_monomial _ _

@[simp]

中文:
定理 eval_monomial
  条件: {n a}
  结论: (monomial n a).eval x = a * x ^ n
  证明: eval₂_monomial _ _

@[simp]
-/
theorem eval_monomial {n a} : (monomial n a).eval x = a * x ^ n :=
  eval₂_monomial _ _

@[simp]
/--
theorem `eval_zero` / 定理 `eval_zero`

English:
theorem eval_zero
  statement: (0 : R[X]).eval x = 0
  proof: eval₂_zero _ _

@[simp]

中文:
定理 eval_zero
  结论: (0 : R[X]).eval x = 0
  证明: eval₂_zero _ _

@[simp]
-/
theorem eval_zero : (0 : R[X]).eval x = 0 :=
  eval₂_zero _ _

@[simp]
/--
theorem `eval_add` / 定理 `eval_add`

English:
theorem eval_add
  statement: (p + q).eval x = p.eval x + q.eval x
  proof: eval₂_add _ _

@[simp]

中文:
定理 eval_add
  结论: (p + q).eval x = p.eval x + q.eval x
  证明: eval₂_add _ _

@[simp]
-/
theorem eval_add : (p + q).eval x = p.eval x + q.eval x :=
  eval₂_add _ _

@[simp]
/--
theorem `eval_one` / 定理 `eval_one`

English:
theorem eval_one
  statement: (1 : R[X]).eval x = 1
  proof: eval₂_one _ _

@[simp]

中文:
定理 eval_one
  结论: (1 : R[X]).eval x = 1
  证明: eval₂_one _ _

@[simp]
-/
theorem eval_one : (1 : R[X]).eval x = 1 :=
  eval₂_one _ _

@[simp]
/--
theorem `eval_C_mul` / 定理 `eval_C_mul`

English:
theorem eval_C_mul
  statement: (C a * p).eval x = a * p.eval x
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [mul_add, eval_add, ph, qh]
  | monomial n b => simp only [mul_assoc, C_mul_monomial, eval_monomial]

@[simp]

中文:
定理 eval_C_mul
  结论: (C a * p).eval x = a * p.eval x
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [mul_add, eval_add, ph, qh]
  | monomial n b => simp only [mul_assoc, C_mul_monomial, eval_monomial]

@[simp]

Depends on / 依赖: C_mul_monomial, Polynomial, Polynomial.induction_on, eval_add, eval_monomial, induction_on, monomial, mul_add, mul_assoc
-/
theorem eval_C_mul : (C a * p).eval x = a * p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [mul_add, eval_add, ph, qh]
  | monomial n b => simp only [mul_assoc, C_mul_monomial, eval_monomial]

@[simp]
/--
theorem `eval_natCast_mul` / 定理 `eval_natCast_mul`

English:
theorem eval_natCast_mul
  given: {n : Nat}
  statement: ((n : R[X]) * p).eval x = n * p.eval x
  proof: by
  rw [← C_eq_natCast]; rw [eval_C_mul]

@[simp]

中文:
定理 eval_natCast_mul
  条件: {n : 自然数}
  结论: ((n : R[X]) * p).eval x = n * p.eval x
  证明: by
  rw [← C_eq_natCast]; rw [eval_C_mul]

@[simp]

Depends on / 依赖: C_eq_natCast, eval_C_mul
-/
theorem eval_natCast_mul {n : Nat} : ((n : R[X]) * p).eval x = n * p.eval x := by
  rw [← C_eq_natCast]; rw [eval_C_mul]

@[simp]
/--
theorem `eval_mul_X` / 定理 `eval_mul_X`

English:
theorem eval_mul_X
  statement: (p * X).eval x = p.eval x * x
  proof: eval₂_mul_X ..

@[simp]

中文:
定理 eval_mul_X
  结论: (p * X).eval x = p.eval x * x
  证明: eval₂_mul_X ..

@[simp]
-/
theorem eval_mul_X : (p * X).eval x = p.eval x * x := eval₂_mul_X ..

@[simp]
/--
theorem `eval_mul_X_pow` / 定理 `eval_mul_X_pow`

English:
theorem eval_mul_X_pow
  given: {k : Nat}
  statement: (p * X ^ k).eval x = p.eval x * x ^ k
  proof: by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, ← mul_assoc, ih]

中文:
定理 eval_mul_X_pow
  条件: {k : 自然数}
  结论: (p * X ^ k).eval x = p.eval x * x ^ k
  证明: by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, ← mul_assoc, ih]

Depends on / 依赖: mul_assoc, pow_succ
-/
theorem eval_mul_X_pow {k : Nat} : (p * X ^ k).eval x = p.eval x * x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, ← mul_assoc, ih]

/--
theorem `eval_mul_C_of_commute` / 定理 `eval_mul_C_of_commute`

English:
theorem eval_mul_C_of_commute
  given: (h : Commute a x)
  statement: (p * C a).eval x = p.eval x * a
  proof: by
  rw [eval]; rw [eval₂_mul_C'] <;> simp [h]

中文:
定理 eval_mul_C_of_commute
  条件: (h : Commute a x)
  结论: (p * C a).eval x = p.eval x * a
  证明: by
  rw [eval]; rw [eval₂_mul_C'] <;> simp [h]
-/
theorem eval_mul_C_of_commute (h : Commute a x) : (p * C a).eval x = p.eval x * a := by
  rw [eval]; rw [eval₂_mul_C'] <;> simp [h]

/--
theorem `eval_listSum` / 定理 `eval_listSum`

English:
theorem eval_listSum
  given: (l : List R[X]) (x : R)
  statement: eval x l.sum = (l.map (eval x)).sum
  proof: eval₂_list_sum ..

中文:
定理 eval_listSum
  条件: (l : List R[X]) (x : R)
  结论: eval x l.sum = (l.map (eval x)).sum
  证明: eval₂_list_sum ..
-/
theorem eval_listSum (l : List R[X]) (x : R) : eval x l.sum = (l.map (eval x)).sum :=
  eval₂_list_sum ..

/--
theorem `eval_multisetSum` / 定理 `eval_multisetSum`

English:
theorem eval_multisetSum
  given: (s : Multiset R[X]) (x : R)
  statement: eval x s.sum = (s.map (eval x)).sum
  proof: eval₂_multiset_sum ..

中文:
定理 eval_multisetSum
  条件: (s : Multiset R[X]) (x : R)
  结论: eval x s.sum = (s.map (eval x)).sum
  证明: eval₂_multiset_sum ..
-/
theorem eval_multisetSum (s : Multiset R[X]) (x : R) : eval x s.sum = (s.map (eval x)).sum :=
  eval₂_multiset_sum ..

/--
theorem `eval_sum` / 定理 `eval_sum`

English:
theorem eval_sum
  given: (p : R[X]) (f : Nat -> R -> R[X]) (x : R)
  proof: eval₂_sum _ _ _ _

中文:
定理 eval_sum
  条件: (p : R[X]) (f : 自然数 -> R -> R[X]) (x : R)
  证明: eval₂_sum _ _ _ _
-/
theorem eval_sum (p : R[X]) (f : Nat -> R -> R[X]) (x : R) :
    (p.sum f).eval x = p.sum fun n a => (f n a).eval x :=
  eval₂_sum _ _ _ _

/--
theorem `eval_finsetSum` / 定理 `eval_finsetSum`

English:
theorem eval_finsetSum
  given: (s : Finset ι) (g : ι -> R[X]) (x : R)
  proof: eval₂_finsetSum _ _ _ _

@[deprecated (since := "2026-04-08")] alias eval_finset_sum := eval_finsetSum

中文:
定理 eval_finsetSum
  条件: (s : Finset ι) (g : ι -> R[X]) (x : R)
  证明: eval₂_finsetSum _ _ _ _

@[deprecated (since := "2026-04-08")] alias eval_finset_sum := eval_finsetSum
-/
theorem eval_finsetSum (s : Finset ι) (g : ι -> R[X]) (x : R) :
    (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x :=
  eval₂_finsetSum _ _ _ _

@[deprecated (since := "2026-04-08")] alias eval_finset_sum := eval_finsetSum

/--
Definition of `IsRoot` / `IsRoot` 的定义

English:
definition IsRoot
  signature: (p : R[X]) (a : R)
  body: p.eval a = 0

中文:
定义 IsRoot
  签名: (p : R[X]) (a : R)
  定义体: p.eval a = 0

Depends on / 依赖: p.eval
-/
def IsRoot (p : R[X]) (a : R) : Prop :=
  p.eval a = 0

/--
Instance `IsRoot.decidable` / 实例 `IsRoot.decidable`

English:
instance IsRoot.decidable
  signature: [DecidableEq R]
  body: inferInstanceAs Decidable (eval a p = 0)

@[simp]

中文:
实例 IsRoot.decidable
  签名: [DecidableEq R]
  定义体: inferInstanceAs Decidable (eval a p = 0)

@[simp]

Depends on / 依赖: Decidable
-/
instance IsRoot.decidable [DecidableEq R] : Decidable (IsRoot p a) :=
inferInstanceAs Decidable (eval a p = 0)

@[simp]
/--
theorem `IsRoot.def` / 定理 `IsRoot.def`

English:
theorem IsRoot.def
  statement: IsRoot p a ↔ p.eval a = 0
  proof: Iff.rfl

中文:
定理 IsRoot.def
  结论: IsRoot p a ↔ p.eval a = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem IsRoot.def : IsRoot p a ↔ p.eval a = 0 :=
  Iff.rfl

/--
theorem `IsRoot.eq_zero` / 定理 `IsRoot.eq_zero`

English:
theorem IsRoot.eq_zero
  given: (h : IsRoot p x)
  statement: eval x p = 0
  proof: h

中文:
定理 IsRoot.eq_zero
  条件: (h : IsRoot p x)
  结论: eval x p = 0
  证明: h
-/
theorem IsRoot.eq_zero (h : IsRoot p x) : eval x p = 0 :=
  h

/--
theorem `IsRoot.dvd` / 定理 `IsRoot.dvd`

English:
theorem IsRoot.dvd
  statement: {R : Type*} [CommSemiring R] {p q : R[X]} {x : R} (h : p.IsRoot x)
  proof: by
  rwa [IsRoot, eval, eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hpq]

中文:
定理 IsRoot.dvd
  结论: {R : 类型} [CommSemiring R] {p q : R[X]} {x : R} (h : p.IsRoot x)
  证明: by
  rwa [IsRoot, eval, eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hpq]

Depends on / 依赖: IsRoot
-/
theorem IsRoot.dvd {R : Type*} [CommSemiring R] {p q : R[X]} {x : R} (h : p.IsRoot x)
    (hpq : p ∣ q) : q.IsRoot x := by
  rwa [IsRoot, eval, eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hpq]

/--
theorem `not_isRoot_C` / 定理 `not_isRoot_C`

English:
theorem not_isRoot_C
  given: (r a : R) (hr : r != 0)
  statement: ¬IsRoot (C r) a
  proof: by simpa using hr

中文:
定理 not_isRoot_C
  条件: (r a : R) (hr : r != 0)
  结论: ¬IsRoot (C r) a
  证明: by simpa using hr
-/
theorem not_isRoot_C (r a : R) (hr : r != 0) : ¬IsRoot (C r) a := by simpa using hr

/--
theorem `eval_surjective` / 定理 `eval_surjective`

English:
theorem eval_surjective
  given: (x : R)
  statement: Function.Surjective eval x
  proof: fun y => ⟨C y, eval_C⟩

中文:
定理 eval_surjective
  条件: (x : R)
  结论: Function.Surjective eval x
  证明: fun y => ⟨C y, eval_C⟩

Depends on / 依赖: eval_C
-/
theorem eval_surjective (x : R) : Function.Surjective eval x := fun y => ⟨C y, eval_C⟩

end Eval

section Comp

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (p q : R[X])
  body: p.eval₂ C q

中文:
定义 comp
  签名: (p q : R[X])
  定义体: p.eval₂ C q

Depends on / 依赖: p.eval
-/
def comp (p q : R[X]) : R[X] :=
  p.eval₂ C q

/--
theorem `comp_eq_sum_left` / 定理 `comp_eq_sum_left`

English:
theorem comp_eq_sum_left
  statement: p.comp q = p.sum fun e a => C a * q ^ e
  proof: by rw [comp, eval₂_eq_sum]

@[simp]

中文:
定理 comp_eq_sum_left
  结论: p.comp q = p.sum fun e a => C a * q ^ e
  证明: by rw [comp, eval₂_eq_sum]

@[simp]
-/
theorem comp_eq_sum_left : p.comp q = p.sum fun e a => C a * q ^ e := by rw [comp, eval₂_eq_sum]

@[simp]
/--
theorem `comp_X` / 定理 `comp_X`

English:
theorem comp_X
  statement: p.comp X = p
  proof: by
  simp only [comp, eval₂_def, C_mul_X_pow_eq_monomial]
  exact sum_monomial_eq _

@[simp]

中文:
定理 comp_X
  结论: p.comp X = p
  证明: by
  simp only [comp, eval₂_def, C_mul_X_pow_eq_monomial]
  exact sum_monomial_eq _

@[simp]

Depends on / 依赖: C_mul_X_pow_eq_monomial, sum_monomial_eq
-/
theorem comp_X : p.comp X = p := by
  simp only [comp, eval₂_def, C_mul_X_pow_eq_monomial]
  exact sum_monomial_eq _

@[simp]
/--
theorem `X_comp` / 定理 `X_comp`

English:
theorem X_comp
  statement: X.comp p = p
  proof: eval₂_X _ _

@[simp]

中文:
定理 X_comp
  结论: X.comp p = p
  证明: eval₂_X _ _

@[simp]
-/
theorem X_comp : X.comp p = p :=
  eval₂_X _ _

@[simp]
/--
theorem `comp_C` / 定理 `comp_C`

English:
theorem comp_C
  statement: p.comp (C a) = C (p.eval a)
  proof: by simp [comp]

@[simp]

中文:
定理 comp_C
  结论: p.comp (C a) = C (p.eval a)
  证明: by simp [comp]

@[simp]
-/
theorem comp_C : p.comp (C a) = C (p.eval a) := by simp [comp]

@[simp]
/--
theorem `C_comp` / 定理 `C_comp`

English:
theorem C_comp
  statement: (C a).comp p = C a
  proof: eval₂_C _ _

@[simp]

中文:
定理 C_comp
  结论: (C a).comp p = C a
  证明: eval₂_C _ _

@[simp]
-/
theorem C_comp : (C a).comp p = C a :=
  eval₂_C _ _

@[simp]
/--
theorem `natCast_comp` / 定理 `natCast_comp`

English:
theorem natCast_comp
  given: {n : Nat}
  statement: (n : R[X]).comp p = n
  proof: by rw [← C_eq_natCast, C_comp]

@[simp]

中文:
定理 natCast_comp
  条件: {n : 自然数}
  结论: (n : R[X]).comp p = n
  证明: by rw [← C_eq_natCast, C_comp]

@[simp]

Depends on / 依赖: C_comp, C_eq_natCast
-/
theorem natCast_comp {n : Nat} : (n : R[X]).comp p = n := by rw [← C_eq_natCast, C_comp]

@[simp]
/--
theorem `ofNat_comp` / 定理 `ofNat_comp`

English:
theorem ofNat_comp
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : R[X]).comp p = n
  proof: natCast_comp

@[simp]

中文:
定理 ofNat_comp
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : R[X]).comp p = n
  证明: natCast_comp

@[simp]

Depends on / 依赖: natCast_comp
-/
theorem ofNat_comp (n : Nat) [n.AtLeastTwo] : (ofNat(n) : R[X]).comp p = n :=
  natCast_comp

@[simp]
/--
theorem `comp_zero` / 定理 `comp_zero`

English:
theorem comp_zero
  statement: p.comp (0 : R[X]) = C (p.eval 0)
  proof: by rw [← C_0, comp_C]

@[simp]

中文:
定理 comp_zero
  结论: p.comp (0 : R[X]) = C (p.eval 0)
  证明: by rw [← C_0, comp_C]

@[simp]

Depends on / 依赖: comp_C
-/
theorem comp_zero : p.comp (0 : R[X]) = C (p.eval 0) := by rw [← C_0, comp_C]

@[simp]
/--
theorem `zero_comp` / 定理 `zero_comp`

English:
theorem zero_comp
  statement: comp (0 : R[X]) p = 0
  proof: by rw [← C_0, C_comp]

@[simp]

中文:
定理 zero_comp
  结论: comp (0 : R[X]) p = 0
  证明: by rw [← C_0, C_comp]

@[simp]

Depends on / 依赖: C_comp
-/
theorem zero_comp : comp (0 : R[X]) p = 0 := by rw [← C_0, C_comp]

@[simp]
/--
theorem `comp_one` / 定理 `comp_one`

English:
theorem comp_one
  statement: p.comp 1 = C (p.eval 1)
  proof: by rw [← C_1, comp_C]

@[simp]

中文:
定理 comp_one
  结论: p.comp 1 = C (p.eval 1)
  证明: by rw [← C_1, comp_C]

@[simp]

Depends on / 依赖: comp_C
-/
theorem comp_one : p.comp 1 = C (p.eval 1) := by rw [← C_1, comp_C]

@[simp]
/--
theorem `one_comp` / 定理 `one_comp`

English:
theorem one_comp
  statement: comp (1 : R[X]) p = 1
  proof: by rw [← C_1, C_comp]

@[simp]

中文:
定理 one_comp
  结论: comp (1 : R[X]) p = 1
  证明: by rw [← C_1, C_comp]

@[simp]

Depends on / 依赖: C_comp
-/
theorem one_comp : comp (1 : R[X]) p = 1 := by rw [← C_1, C_comp]

@[simp]
/--
theorem `add_comp` / 定理 `add_comp`

English:
theorem add_comp
  statement: (p + q).comp r = p.comp r + q.comp r
  proof: eval₂_add _ _

@[simp]

中文:
定理 add_comp
  结论: (p + q).comp r = p.comp r + q.comp r
  证明: eval₂_add _ _

@[simp]
-/
theorem add_comp : (p + q).comp r = p.comp r + q.comp r :=
  eval₂_add _ _

@[simp]
/--
theorem `monomial_comp` / 定理 `monomial_comp`

English:
theorem monomial_comp
  given: (n : Nat)
  statement: (monomial n a).comp p = C a * p ^ n
  proof: eval₂_monomial _ _

@[simp]

中文:
定理 monomial_comp
  条件: (n : 自然数)
  结论: (monomial n a).comp p = C a * p ^ n
  证明: eval₂_monomial _ _

@[simp]

Depends on / 依赖: Subsemiring, Subsemiring.center.smulCommClass_left, center, smulCommClass_left
-/
theorem monomial_comp (n : Nat) : (monomial n a).comp p = C a * p ^ n :=
  eval₂_monomial _ _

@[simp]
/--
theorem `mul_X_comp` / 定理 `mul_X_comp`

English:
theorem mul_X_comp
  statement: (p * X).comp r = p.comp r * r
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, add_mul, add_comp]
  | monomial n b => simp only [pow_succ, mul_assoc, monomial_mul_X, monomial_comp]

@[simp]

中文:
定理 mul_X_comp
  结论: (p * X).comp r = p.comp r * r
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, add_mul, add_comp]
  | monomial n b => simp only [pow_succ, mul_assoc, monomial_mul_X, monomial_comp]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.induction_on, Subsemiring, Subsemiring.center.smulCommClass_right, add_comp, add_mul, center, induction_on, monomial, monomial_comp, monomial_mul_X, mul_assoc, pow_succ, smulCommClass_right
-/
theorem mul_X_comp : (p * X).comp r = p.comp r * r := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [hp, hq, add_mul, add_comp]
  | monomial n b => simp only [pow_succ, mul_assoc, monomial_mul_X, monomial_comp]

@[simp]
/--
theorem `X_pow_comp` / 定理 `X_pow_comp`

English:
theorem X_pow_comp
  given: {k : Nat}
  statement: (X ^ k).comp p = p ^ k
  proof: by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, mul_X_comp, ih]

@[simp]

中文:
定理 X_pow_comp
  条件: {k : 自然数}
  结论: (X ^ k).comp p = p ^ k
  证明: by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, mul_X_comp, ih]

@[simp]

Depends on / 依赖: SMulCommClass, Submonoid, Submonoid.center, center, mul_X_comp, pow_succ
-/
theorem X_pow_comp {k : Nat} : (X ^ k).comp p = p ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, mul_X_comp, ih]

@[simp]
/--
theorem `mul_X_pow_comp` / 定理 `mul_X_pow_comp`

English:
theorem mul_X_pow_comp
  given: {k : Nat}
  statement: (p * X ^ k).comp r = p.comp r * r ^ k
  proof: by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, mul_X_comp]

@[simp]

中文:
定理 mul_X_pow_comp
  条件: {k : 自然数}
  结论: (p * X ^ k).comp r = p.comp r * r ^ k
  证明: by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, mul_X_comp]

@[simp]

Depends on / 依赖: SMulCommClass, Submonoid, Submonoid.center, center, mul_X_comp, mul_assoc, pow_succ
-/
theorem mul_X_pow_comp {k : Nat} : (p * X ^ k).comp r = p.comp r * r ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, mul_X_comp]

@[simp]
/--
theorem `C_mul_comp` / 定理 `C_mul_comp`

English:
theorem C_mul_comp
  statement: (C a * p).comp r = C a * p.comp r
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial n b => simp [mul_assoc]

@[simp]

中文:
定理 C_mul_comp
  结论: (C a * p).comp r = C a * p.comp r
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial n b => simp [mul_assoc]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.induction_on, induction_on, monomial, mul_add, mul_assoc
-/
theorem C_mul_comp : (C a * p).comp r = C a * p.comp r := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial n b => simp [mul_assoc]

@[simp]
/--
theorem `natCast_mul_comp` / 定理 `natCast_mul_comp`

English:
theorem natCast_mul_comp
  given: {n : Nat}
  statement: ((n : R[X]) * p).comp r = n * p.comp r
  proof: by
  rw [← C_eq_natCast]; rw [C_mul_comp]

中文:
定理 natCast_mul_comp
  条件: {n : 自然数}
  结论: ((n : R[X]) * p).comp r = n * p.comp r
  证明: by
  rw [← C_eq_natCast]; rw [C_mul_comp]

Depends on / 依赖: C_eq_natCast, C_mul_comp
-/
theorem natCast_mul_comp {n : Nat} : ((n : R[X]) * p).comp r = n * p.comp r := by
  rw [← C_eq_natCast]; rw [C_mul_comp]

/--
theorem `mul_X_add_natCast_comp` / 定理 `mul_X_add_natCast_comp`

English:
theorem mul_X_add_natCast_comp
  given: {n : Nat}
  proof: by
  rw [mul_add]; rw [add_comp]; rw [mul_X_comp]; rw [← Nat.cast_comm]; rw [natCast_mul_comp]; rw [Nat.cast_comm]; rw [mul_add]

@[simp]

中文:
定理 mul_X_add_natCast_comp
  条件: {n : 自然数}
  证明: by
  rw [mul_add]; rw [add_comp]; rw [mul_X_comp]; rw [← Nat.cast_comm]; rw [natCast_mul_comp]; rw [Nat.cast_comm]; rw [mul_add]

@[simp]

Depends on / 依赖: Nat.cast_comm, add_comp, cast_comm, mul_X_comp, mul_add, natCast_mul_comp
-/
theorem mul_X_add_natCast_comp {n : Nat} :
    (p * (X + (n : R[X]))).comp q = p.comp q * (q + n) := by
  rw [mul_add]; rw [add_comp]; rw [mul_X_comp]; rw [← Nat.cast_comm]; rw [natCast_mul_comp]; rw [Nat.cast_comm]; rw [mul_add]

@[simp]
/--
theorem `mul_comp` / 定理 `mul_comp`

English:
theorem mul_comp
  given: {R : Type*} [CommSemiring R] (p q r : R[X])
  proof: eval₂_mul _ _

@[simp]

中文:
定理 mul_comp
  条件: {R : 类型} [CommSemiring R] (p q r : R[X])
  证明: eval₂_mul _ _

@[simp]
-/
theorem mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]) :
    (p * q).comp r = p.comp r * q.comp r :=
  eval₂_mul _ _

@[simp]
/--
theorem `mul_comp_neg_X` / 定理 `mul_comp_neg_X`

English:
theorem mul_comp_neg_X
  given: {R : Type*} [Ring R] (p q : R[X])
  proof: eval₂_mul_noncomm C (-X) fun _ => Commute.symm (commute_X _).neg_left

@[simp]

中文:
定理 mul_comp_neg_X
  条件: {R : 类型} [Ring R] (p q : R[X])
  证明: eval₂_mul_noncomm C (-X) fun _ => Commute.symm (commute_X _).neg_left

@[simp]

Depends on / 依赖: Commute, Commute.symm, commute_X, neg_left
-/
theorem mul_comp_neg_X {R : Type*} [Ring R] (p q : R[X]) :
    (p * q).comp (-X) = p.comp (-X) * q.comp (-X) :=
  eval₂_mul_noncomm C (-X) fun _ => Commute.symm (commute_X _).neg_left

@[simp]
/--
theorem `pow_comp` / 定理 `pow_comp`

English:
theorem pow_comp
  given: {R : Type*} [CommSemiring R] (p q : R[X]) (n : Nat)
  proof: (MonoidHom.mk (OneHom.mk (fun r : R[X] => r.comp q) one_comp) fun r s => mul_comp r s q).map_pow
    p n

中文:
定理 pow_comp
  条件: {R : 类型} [CommSemiring R] (p q : R[X]) (n : 自然数)
  证明: (MonoidHom.mk (OneHom.mk (fun r : R[X] => r.comp q) one_comp) fun r s => mul_comp r s q).map_pow
    p n

Depends on / 依赖: MonoidHom, MonoidHom.mk, OneHom, OneHom.mk, map_pow, mul_comp, one_comp, r.comp
-/
theorem pow_comp {R : Type*} [CommSemiring R] (p q : R[X]) (n : Nat) :
    (p ^ n).comp q = p.comp q ^ n :=
  (MonoidHom.mk (OneHom.mk (fun r : R[X] => r.comp q) one_comp) fun r s => mul_comp r s q).map_pow
    p n

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: {R : Type*} [CommSemiring R] (φ ψ χ : R[X])
  proof: by
  refine Polynomial.induction_on φ ?_ ?_ ?_ <;>
    · intros
      simp_all only [add_comp, mul_comp, C_comp, X_comp, pow_succ, ← mul_assoc]

中文:
定理 comp_assoc
  条件: {R : 类型} [CommSemiring R] (φ ψ χ : R[X])
  证明: by
  refine Polynomial.induction_on φ ?_ ?_ ?_ <;>
    · intros
      simp_all only [add_comp, mul_comp, C_comp, X_comp, pow_succ, ← mul_assoc]

Depends on / 依赖: C_comp, Polynomial, Polynomial.induction_on, X_comp, add_comp, induction_on, intros, mul_assoc, mul_comp, pow_succ
-/
theorem comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : R[X]) :
    (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := by
  refine Polynomial.induction_on φ ?_ ?_ ?_ <;>
    · intros
      simp_all only [add_comp, mul_comp, C_comp, X_comp, pow_succ, ← mul_assoc]

/--
lemma `sum_comp` / 引理 `sum_comp`

English:
lemma sum_comp
  given: (s : Finset ι) (p : ι -> R[X]) (q : R[X])
  proof: Polynomial.eval₂_finsetSum _ _ _ _

中文:
引理 sum_comp
  条件: (s : Finset ι) (p : ι -> R[X]) (q : R[X])
  证明: Polynomial.eval₂_finsetSum _ _ _ _

Depends on / 依赖: SubringClass, SubringClass.addSubgroupClass, addSubgroupClass
-/
@[simp] lemma sum_comp (s : Finset ι) (p : ι -> R[X]) (q : R[X]) :
    (∑ i in s, p i).comp q = ∑ i in s, (p i).comp q := Polynomial.eval₂_finsetSum _ _ _ _

end Comp

section Map

variable [Semiring S]
variable (f : R ->+* S)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : R[X] -> S[X]
  body: eval₂ (C.comp f) X

@[simp]

中文:
定义 map
  签名: : R[X] -> S[X]
  定义体: eval₂ (C.comp f) X

@[simp]

Depends on / 依赖: C.comp, SubringClass, SubringClass.nonUnitalSubringClass, nonUnitalSubringClass
-/
def map : R[X] -> S[X] :=
  eval₂ (C.comp f) X

@[simp]
/--
theorem `map_C` / 定理 `map_C`

English:
theorem map_C
  statement: (C a).map f = C (f a)
  proof: eval₂_C _ _

@[simp]

中文:
定理 map_C
  结论: (C a).map f = C (f a)
  证明: eval₂_C _ _

@[simp]
-/
theorem map_C : (C a).map f = C (f a) :=
  eval₂_C _ _

@[simp]
/--
theorem `map_X` / 定理 `map_X`

English:
theorem map_X
  statement: X.map f = X
  proof: eval₂_X _ _

@[simp]

中文:
定理 map_X
  结论: X.map f = X
  证明: eval₂_X _ _

@[simp]

Depends on / 依赖: IntCast, toHasIntCast
-/
theorem map_X : X.map f = X :=
  eval₂_X _ _

@[simp]
/--
theorem `map_monomial` / 定理 `map_monomial`

English:
theorem map_monomial
  given: {n a}
  statement: (monomial n a).map f = monomial n (f a)
  proof: by
  dsimp only [map]
  rw [eval₂_monomial]; rw [← C_mul_X_pow_eq_monomial]; rfl

@[simp]

中文:
定理 map_monomial
  条件: {n a}
  结论: (monomial n a).map f = monomial n (f a)
  证明: by
  dsimp only [map]
  rw [eval₂_monomial]; rw [← C_mul_X_pow_eq_monomial]; rfl

@[simp]

Depends on / 依赖: C_mul_X_pow_eq_monomial, NonAssocRing, fast_instance, toNonAssocRing
-/
theorem map_monomial {n a} : (monomial n a).map f = monomial n (f a) := by
  dsimp only [map]
  rw [eval₂_monomial]; rw [← C_mul_X_pow_eq_monomial]; rfl

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: (0 : R[X]).map f = 0
  proof: eval₂_zero _ _

@[simp]

中文:
定理 map_zero
  结论: (0 : R[X]).map f = 0
  证明: eval₂_zero _ _

@[simp]

Depends on / 依赖: SetLike, SubringClass, toRing
-/
protected theorem map_zero : (0 : R[X]).map f = 0 :=
  eval₂_zero _ _

@[simp]
/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  statement: (p + q).map f = p.map f + q.map f
  proof: eval₂_add _ _

@[simp]

中文:
定理 map_add
  结论: (p + q).map f = p.map f + q.map f
  证明: eval₂_add _ _

@[simp]

Depends on / 依赖: NonAssocCommRing, SetLike, toNonAssocCommRing
-/
protected theorem map_add : (p + q).map f = p.map f + q.map f :=
  eval₂_add _ _

@[simp]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  statement: (1 : R[X]).map f = 1
  proof: eval₂_one _ _

@[simp]

中文:
定理 map_one
  结论: (1 : R[X]).map f = 1
  证明: eval₂_one _ _

@[simp]

Depends on / 依赖: CommRing, SetLike, SubringClass, toCommRing
-/
protected theorem map_one : (1 : R[X]).map f = 1 :=
  eval₂_one _ _

@[simp]
/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  statement: (p * q).map f = p.map f * q.map f
  proof: by
  rw [map]; rw [eval₂_mul_noncomm]
  exact fun k => (commute_X _).symm

中文:
定理 map_mul
  结论: (p * q).map f = p.map f * q.map f
  证明: by
  rw [map]; rw [eval₂_mul_noncomm]
  exact fun k => (commute_X _).symm

Depends on / 依赖: IsDomain, SetLike, SubringClass
-/
protected theorem map_mul : (p * q).map f = p.map f * q.map f := by
  rw [map]; rw [eval₂_mul_noncomm]
  exact fun k => (commute_X _).symm

-- `map` is a ring-hom unconditionally, and theoretically the definition could be replaced,
-- but this turns out not to be easy because `p.map f` does not resolve to `Polynomial.map`
-- if `map` is a `RingHom` instead of a plain function; the elaborator does not try to coerce
-- to a function before trying field (dot) notation (this may be technically infeasible);
-- the relevant code is (both lines): https://github.com/leanprover-community/
-- lean/blob/487ac5d7e9b34800502e1ddf3c7c806c01cf9d51/src/frontends/lean/elaborator.cpp#L1876-L1913
/--
Definition of `mapRingHom` / `mapRingHom` 的定义

English:
definition mapRingHom
  signature: (f : R ->+* S)
  body: Polynomial.map f
  map_add' _ _ := Polynomial.map_add f
  map_zero' := Polynomial.map_zero f
  map_mul' _ _ := Polynomial.map_mul f
  map_one' := Polynomial.map_one f

@[simp]

中文:
定义 mapRingHom
  签名: (f : R ->+* S)
  定义体: Polynomial.map f
  map_add' _ _ := Polynomial.map_add f
  map_zero' := Polynomial.map_zero f
  map_mul' _ _ := Polynomial.map_mul f
  map_one' := Polynomial.map_one f

@[simp]

Depends on / 依赖: Polynomial, Polynomial.map
-/
def mapRingHom (f : R ->+* S) : R[X] ->+* S[X] where
  toFun := Polynomial.map f
  map_add' _ _ := Polynomial.map_add f
  map_zero' := Polynomial.map_zero f
  map_mul' _ _ := Polynomial.map_mul f
  map_one' := Polynomial.map_one f

@[simp]
/--
theorem `coe_mapRingHom` / 定理 `coe_mapRingHom`

English:
theorem coe_mapRingHom
  given: (f : R ->+* S)
  statement: ⇑(mapRingHom f) = map f
  proof: rfl

中文:
定理 coe_mapRingHom
  条件: (f : R ->+* S)
  结论: ⇑(mapRingHom f) = map f
  证明: rfl
-/
theorem coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom f) = map f :=
  rfl

-- This is protected to not clash with the global `map_natCast`.
@[simp]
/--
theorem `map_natCast` / 定理 `map_natCast`

English:
theorem map_natCast
  given: (n : Nat)
  statement: (n : R[X]).map f = n
  proof: map_natCast (mapRingHom f) n

@[simp]

中文:
定理 map_natCast
  条件: (n : 自然数)
  结论: (n : R[X]).map f = n
  证明: map_natCast (mapRingHom f) n

@[simp]
-/
protected theorem map_natCast (n : Nat) : (n : R[X]).map f = n :=
  map_natCast (mapRingHom f) n

@[simp]
/--
theorem `map_ofNat` / 定理 `map_ofNat`

English:
theorem map_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: show (n : R[X]).map f = n by rw [Polynomial.map_natCast]

中文:
定理 map_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: show (n : R[X]).map f = n by rw [Polynomial.map_natCast]
-/
protected theorem map_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : R[X]).map f = ofNat(n) :=
  show (n : R[X]).map f = n by rw [Polynomial.map_natCast]

--TODO rename to `map_dvd_map`
/--
theorem `map_dvd` / 定理 `map_dvd`

English:
theorem map_dvd
  given: (f : R ->+* S) {x y : R[X]}
  statement: x ∣ y -> x.map f ∣ y.map f
  proof: _root_.map_dvd (mapRingHom f)

中文:
定理 map_dvd
  条件: (f : R ->+* S) {x y : R[X]}
  结论: x ∣ y -> x.map f ∣ y.map f
  证明: _root_.map_dvd (mapRingHom f)

Depends on / 依赖: _root_, _root_.map_dvd, mapRingHom, map_dvd
-/
theorem map_dvd (f : R ->+* S) {x y : R[X]} : x ∣ y -> x.map f ∣ y.map f :=
  _root_.map_dvd (mapRingHom f)

/--
lemma `associated_map_map` / 引理 `associated_map_map`

English:
lemma associated_map_map
  given: (f : R ->+* S) {x y : R[X]}
  proof: .map (mapRingHom f)

中文:
引理 associated_map_map
  条件: (f : R ->+* S) {x y : R[X]}
  证明: .map (mapRingHom f)

Depends on / 依赖: mapRingHom
-/
lemma associated_map_map (f : R ->+* S) {x y : R[X]} :
    Associated x y -> Associated (x.map f) (y.map f) := .map (mapRingHom f)

/--
lemma `mapRingHom_comp_C` / 引理 `mapRingHom_comp_C`

English:
lemma mapRingHom_comp_C
  given: {R S : Type*} [Semiring R] [Semiring S] (f : R ->+* S)
  proof: by ext; simp

中文:
引理 mapRingHom_comp_C
  条件: {R S : 类型} [Semiring R] [Semiring S] (f : R ->+* S)
  证明: by ext; simp
-/
lemma mapRingHom_comp_C {R S : Type*} [Semiring R] [Semiring S] (f : R ->+* S) :
    (mapRingHom f).comp C = C.comp f := by ext; simp

/--
theorem `eval₂_eq_eval_map` / 定理 `eval₂_eq_eval_map`

English:
theorem eval₂_eq_eval_map
  given: {x : S}
  statement: p.eval₂ f x = (p.map f).eval x
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n r => simp

中文:
定理 eval₂_eq_eval_map
  条件: {x : S}
  结论: p.eval₂ f x = (p.map f).eval x
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n r => simp

Depends on / 依赖: Polynomial, Polynomial.induction_on, induction_on, monomial
-/
theorem eval₂_eq_eval_map {x : S} : p.eval₂ f x = (p.map f).eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n r => simp

/--
theorem `map_list_prod` / 定理 `map_list_prod`

English:
theorem map_list_prod
  given: (L : List R[X])
  statement: L.prod.map f = (L.map <| map f).prod
  proof: Eq.symm List.prod_hom _ (mapRingHom f).toMonoidHom

@[simp]

中文:
定理 map_list_prod
  条件: (L : List R[X])
  结论: L.prod.map f = (L.map <| map f).prod
  证明: Eq.symm List.prod_hom _ (mapRingHom f).toMonoidHom

@[simp]
-/
protected theorem map_list_prod (L : List R[X]) : L.prod.map f = (L.map <| map f).prod :=
Eq.symm List.prod_hom _ (mapRingHom f).toMonoidHom

@[simp]
/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  given: (n : Nat)
  statement: (p ^ n).map f = p.map f ^ n
  proof: (mapRingHom f).map_pow _ _

中文:
定理 map_pow
  条件: (n : 自然数)
  结论: (p ^ n).map f = p.map f ^ n
  证明: (mapRingHom f).map_pow _ _
-/
protected theorem map_pow (n : Nat) : (p ^ n).map f = p.map f ^ n :=
  (mapRingHom f).map_pow _ _

/--
theorem `eval_map` / 定理 `eval_map`

English:
theorem eval_map
  given: (x : S)
  statement: (p.map f).eval x = p.eval₂ f x
  proof: (eval₂_eq_eval_map f).symm

中文:
定理 eval_map
  条件: (x : S)
  结论: (p.map f).eval x = p.eval₂ f x
  证明: (eval₂_eq_eval_map f).symm
-/
theorem eval_map (x : S) : (p.map f).eval x = p.eval₂ f x :=
  (eval₂_eq_eval_map f).symm

/--
lemma `eval_map_apply` / 引理 `eval_map_apply`

English:
lemma eval_map_apply
  given: (x : R)
  statement: (p.map f).eval (f x) = f (p.eval x)
  proof: eval_map f _ ▸ eval₂_at_apply ..

中文:
引理 eval_map_apply
  条件: (x : R)
  结论: (p.map f).eval (f x) = f (p.eval x)
  证明: eval_map f _ ▸ eval₂_at_apply ..
-/
@[simp] lemma eval_map_apply (x : R) : (p.map f).eval (f x) = f (p.eval x) :=
  eval_map f _ ▸ eval₂_at_apply ..

/--
theorem `map_sum` / 定理 `map_sum`

English:
theorem map_sum
  given: {ι : Type*} (g : ι -> R[X]) (s : Finset ι)
  proof: map_sum (mapRingHom f) _ _

中文:
定理 map_sum
  条件: {ι : 类型} (g : ι -> R[X]) (s : Finset ι)
  证明: map_sum (mapRingHom f) _ _

Depends on / 依赖: CanLift, Subring
-/
protected theorem map_sum {ι : Type*} (g : ι -> R[X]) (s : Finset ι) :
    (∑ i in s, g i).map f = ∑ i in s, (g i).map f :=
  map_sum (mapRingHom f) _ _

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (p q : R[X])
  statement: map f (p.comp q) = (map f p).comp (map f q)
  proof: Polynomial.induction_on p (by simp)
    (by
      simp +contextual only [Polynomial.map_add, add_comp, forall_const,
        imp_true_iff])
    (by
      simp +contextual only [pow_succ, ← mul_assoc, comp, forall_const,
        eval₂_mul_X, imp_true_iff, map_X, Polynomial.map_mul])

中文:
定理 map_comp
  条件: (p q : R[X])
  结论: map f (p.comp q) = (map f p).comp (map f q)
  证明: Polynomial.induction_on p (by simp)
    (by
      simp +contextual only [Polynomial.map_add, add_comp, forall_const,
        imp_true_iff])
    (by
      simp +contextual only [pow_succ, ← mul_assoc, comp, forall_const,
        eval₂_mul_X, imp_true_iff, map_X, Polynomial.map_mul])

Depends on / 依赖: Polynomial, Polynomial.induction_on, Polynomial.map_add, Polynomial.map_mul, add_comp, contextual, forall_const, imp_true_iff, induction_on, map_X, map_add, map_mul, mul_assoc, pow_succ
-/
theorem map_comp (p q : R[X]) : map f (p.comp q) = (map f p).comp (map f q) :=
  Polynomial.induction_on p (by simp)
    (by
      simp +contextual only [Polynomial.map_add, add_comp, forall_const,
        imp_true_iff])
    (by
      simp +contextual only [pow_succ, ← mul_assoc, comp, forall_const,
        eval₂_mul_X, imp_true_iff, map_X, Polynomial.map_mul])

/--
theorem `eval_X_pow` / 定理 `eval_X_pow`

English:
theorem eval_X_pow
  given: {x : R} (n : Nat)
  statement: (X ^ n : R[X]).eval x = x ^ n
  proof: by
  simp [eval]

中文:
定理 eval_X_pow
  条件: {x : R} (n : 自然数)
  结论: (X ^ n : R[X]).eval x = x ^ n
  证明: by
  simp [eval]
-/
theorem eval_X_pow {x : R} (n : Nat) : (X ^ n : R[X]).eval x = x ^ n := by
  simp [eval]

end Map

end Semiring

section CommSemiring

section Eval

section

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R ->+* S)

@[simp]
/--
theorem `eval_mul` / 定理 `eval_mul`

English:
theorem eval_mul
  statement: (p * q).eval x = p.eval x * q.eval x
  proof: eval₂_mul _ _

中文:
定理 eval_mul
  结论: (p * q).eval x = p.eval x * q.eval x
  证明: eval₂_mul _ _
-/
theorem eval_mul : (p * q).eval x = p.eval x * q.eval x :=
  eval₂_mul _ _

/--
Definition of `evalRingHom` / `evalRingHom` 的定义

English:
definition evalRingHom
  signature: : R -> R[X] ->+* R
  body: eval₂RingHom (RingHom.id _)

@[simp]

中文:
定义 evalRingHom
  签名: : R -> R[X] ->+* R
  定义体: eval₂RingHom (RingHom.id _)

@[simp]

Depends on / 依赖: RingHom, RingHom.id
-/
def evalRingHom : R -> R[X] ->+* R :=
  eval₂RingHom (RingHom.id _)

@[simp]
/--
theorem `coe_evalRingHom` / 定理 `coe_evalRingHom`

English:
theorem coe_evalRingHom
  given: (r : R)
  statement: (evalRingHom r : R[X] -> R) = eval r
  proof: rfl

@[simp]

中文:
定理 coe_evalRingHom
  条件: (r : R)
  结论: (evalRingHom r : R[X] -> R) = eval r
  证明: rfl

@[simp]
-/
theorem coe_evalRingHom (r : R) : (evalRingHom r : R[X] -> R) = eval r :=
  rfl

@[simp]
/--
theorem `eval_pow` / 定理 `eval_pow`

English:
theorem eval_pow
  given: (n : Nat)
  statement: (p ^ n).eval x = p.eval x ^ n
  proof: eval₂_pow _ _ _

@[simp]

中文:
定理 eval_pow
  条件: (n : 自然数)
  结论: (p ^ n).eval x = p.eval x ^ n
  证明: eval₂_pow _ _ _

@[simp]
-/
theorem eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n :=
  eval₂_pow _ _ _

@[simp]
/--
theorem `eval_comp` / 定理 `eval_comp`

English:
theorem eval_comp
  statement: (p.comp q).eval x = p.eval (q.eval x)
  proof: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp [add_comp, hr, hs]
  | monomial n a => simp

中文:
定理 eval_comp
  结论: (p.comp q).eval x = p.eval (q.eval x)
  证明: by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp [add_comp, hr, hs]
  | monomial n a => simp

Depends on / 依赖: Polynomial, Polynomial.induction_on, add_comp, induction_on, monomial
-/
theorem eval_comp : (p.comp q).eval x = p.eval (q.eval x) := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp [add_comp, hr, hs]
  | monomial n a => simp

/--
lemma `isRoot_comp` / 引理 `isRoot_comp`

English:
lemma isRoot_comp
  given: {R} [CommSemiring R] {p q : R[X]} {r : R}
  proof: by simp_rw [IsRoot, eval_comp]

中文:
引理 isRoot_comp
  条件: {R} [CommSemiring R] {p q : R[X]} {r : R}
  证明: by simp_rw [IsRoot, eval_comp]

Depends on / 依赖: IsRoot, eval_comp, simp_rw
-/
lemma isRoot_comp {R} [CommSemiring R] {p q : R[X]} {r : R} :
    (p.comp q).IsRoot r ↔ p.IsRoot (q.eval r) := by simp_rw [IsRoot, eval_comp]

/--
Definition of `compRingHom` / `compRingHom` 的定义

English:
definition compRingHom
  signature: : R[X] -> R[X] ->+* R[X]
  body: eval₂RingHom C

@[simp]

中文:
定义 compRingHom
  签名: : R[X] -> R[X] ->+* R[X]
  定义体: eval₂RingHom C

@[simp]
-/
def compRingHom : R[X] -> R[X] ->+* R[X] :=
  eval₂RingHom C

@[simp]
/--
theorem `coe_compRingHom` / 定理 `coe_compRingHom`

English:
theorem coe_compRingHom
  given: (q : R[X])
  statement: (compRingHom q : R[X] -> R[X]) = fun p => comp p q
  proof: rfl

中文:
定理 coe_compRingHom
  条件: (q : R[X])
  结论: (compRingHom q : R[X] -> R[X]) = fun p => comp p q
  证明: rfl
-/
theorem coe_compRingHom (q : R[X]) : (compRingHom q : R[X] -> R[X]) = fun p => comp p q :=
  rfl

/--
theorem `coe_compRingHom_apply` / 定理 `coe_compRingHom_apply`

English:
theorem coe_compRingHom_apply
  given: (p q : R[X])
  statement: (compRingHom q : R[X] -> R[X]) p = comp p q
  proof: rfl

中文:
定理 coe_compRingHom_apply
  条件: (p q : R[X])
  结论: (compRingHom q : R[X] -> R[X]) p = comp p q
  证明: rfl
-/
theorem coe_compRingHom_apply (p q : R[X]) : (compRingHom q : R[X] -> R[X]) p = comp p q :=
  rfl

/--
theorem `root_mul_left_of_isRoot` / 定理 `root_mul_left_of_isRoot`

English:
theorem root_mul_left_of_isRoot
  given: (p : R[X]) {q : R[X]}
  statement: IsRoot q a -> IsRoot (p * q) a
  proof: fun H => by
  rw [IsRoot]; rw [eval_mul]; rw [IsRoot.def.1 H]; rw [mul_zero]

中文:
定理 root_mul_left_of_isRoot
  条件: (p : R[X]) {q : R[X]}
  结论: IsRoot q a -> IsRoot (p * q) a
  证明: fun H => by
  rw [IsRoot]; rw [eval_mul]; rw [IsRoot.def.1 H]; rw [mul_zero]

Depends on / 依赖: IsRoot, IsRoot.def, SetLike, SetLike.coe_injective, coe_injective, eval_mul, ha.symm, mul_zero
-/
theorem root_mul_left_of_isRoot (p : R[X]) {q : R[X]} : IsRoot q a -> IsRoot (p * q) a := fun H => by
  rw [IsRoot]; rw [eval_mul]; rw [IsRoot.def.1 H]; rw [mul_zero]

/--
theorem `root_mul_right_of_isRoot` / 定理 `root_mul_right_of_isRoot`

English:
theorem root_mul_right_of_isRoot
  given: {p : R[X]} (q : R[X])
  statement: IsRoot p a -> IsRoot (p * q) a
  proof: fun H =>
  by rw [IsRoot, eval_mul, IsRoot.def.1 H, zero_mul]

中文:
定理 root_mul_right_of_isRoot
  条件: {p : R[X]} (q : R[X])
  结论: IsRoot p a -> IsRoot (p * q) a
  证明: fun H =>
  by rw [IsRoot, eval_mul, IsRoot.def.1 H, zero_mul]
-/
theorem root_mul_right_of_isRoot {p : R[X]} (q : R[X]) : IsRoot p a -> IsRoot (p * q) a := fun H =>
  by rw [IsRoot, eval_mul, IsRoot.def.1 H, zero_mul]

/--
theorem `eval₂_multiset_prod` / 定理 `eval₂_multiset_prod`

English:
theorem eval₂_multiset_prod
  given: (s : Multiset R[X]) (x : S)
  proof: map_multiset_prod (eval₂RingHom f x) s

中文:
定理 eval₂_multiset_prod
  条件: (s : Multiset R[X]) (x : S)
  证明: map_multiset_prod (eval₂RingHom f x) s

Depends on / 依赖: map_multiset_prod
-/
theorem eval₂_multiset_prod (s : Multiset R[X]) (x : S) :
    eval₂ f x s.prod = (s.map (eval₂ f x)).prod :=
  map_multiset_prod (eval₂RingHom f x) s

/--
theorem `eval₂_finsetProd` / 定理 `eval₂_finsetProd`

English:
theorem eval₂_finsetProd
  given: (s : Finset ι) (g : ι -> R[X]) (x : S)
  proof: map_prod (eval₂RingHom f x) _ _

@[deprecated (since := "2026-04-08")] alias eval₂_finset_prod := eval₂_finsetProd

中文:
定理 eval₂_finsetProd
  条件: (s : Finset ι) (g : ι -> R[X]) (x : S)
  证明: map_prod (eval₂RingHom f x) _ _

@[deprecated (since := "2026-04-08")] alias eval₂_finset_prod := eval₂_finsetProd

Depends on / 依赖: map_prod
-/
theorem eval₂_finsetProd (s : Finset ι) (g : ι -> R[X]) (x : S) :
    (∏ i in s, g i).eval₂ f x = ∏ i in s, (g i).eval₂ f x :=
  map_prod (eval₂RingHom f x) _ _

@[deprecated (since := "2026-04-08")] alias eval₂_finset_prod := eval₂_finsetProd

/--
theorem `eval_list_prod` / 定理 `eval_list_prod`

English:
theorem eval_list_prod
  given: (l : List R[X]) (x : R)
  statement: eval x l.prod = (l.map (eval x)).prod
  proof: map_list_prod (evalRingHom x) l

中文:
定理 eval_list_prod
  条件: (l : List R[X]) (x : R)
  结论: eval x l.prod = (l.map (eval x)).prod
  证明: map_list_prod (evalRingHom x) l

Depends on / 依赖: evalRingHom, map_list_prod
-/
theorem eval_list_prod (l : List R[X]) (x : R) : eval x l.prod = (l.map (eval x)).prod :=
  map_list_prod (evalRingHom x) l

/--
theorem `eval_multiset_prod` / 定理 `eval_multiset_prod`

English:
theorem eval_multiset_prod
  given: (s : Multiset R[X]) (x : R)
  statement: eval x s.prod = (s.map (eval x)).prod
  proof: (evalRingHom x).map_multiset_prod s

中文:
定理 eval_multiset_prod
  条件: (s : Multiset R[X]) (x : R)
  结论: eval x s.prod = (s.map (eval x)).prod
  证明: (evalRingHom x).map_multiset_prod s

Depends on / 依赖: evalRingHom, map_multiset_prod
-/
theorem eval_multiset_prod (s : Multiset R[X]) (x : R) : eval x s.prod = (s.map (eval x)).prod :=
  (evalRingHom x).map_multiset_prod s

/--
theorem `eval_prod` / 定理 `eval_prod`

English:
theorem eval_prod
  given: {ι : Type*} (s : Finset ι) (p : ι -> R[X]) (x : R)
  proof: map_prod (evalRingHom x) _ _

中文:
定理 eval_prod
  条件: {ι : 类型} (s : Finset ι) (p : ι -> R[X]) (x : R)
  证明: map_prod (evalRingHom x) _ _

Depends on / 依赖: evalRingHom, map_prod
-/
theorem eval_prod {ι : Type*} (s : Finset ι) (p : ι -> R[X]) (x : R) :
    eval x (∏ j in s, p j) = ∏ j in s, eval x (p j) :=
  map_prod (evalRingHom x) _ _

/--
theorem `list_prod_comp` / 定理 `list_prod_comp`

English:
theorem list_prod_comp
  given: (l : List R[X]) (q : R[X])
  proof: map_list_prod (compRingHom q) _

中文:
定理 list_prod_comp
  条件: (l : List R[X]) (q : R[X])
  证明: map_list_prod (compRingHom q) _

Depends on / 依赖: compRingHom, map_list_prod
-/
theorem list_prod_comp (l : List R[X]) (q : R[X]) :
    l.prod.comp q = (l.map fun p : R[X] => p.comp q).prod :=
  map_list_prod (compRingHom q) _

/--
theorem `multiset_prod_comp` / 定理 `multiset_prod_comp`

English:
theorem multiset_prod_comp
  given: (s : Multiset R[X]) (q : R[X])
  proof: map_multiset_prod (compRingHom q) _

中文:
定理 multiset_prod_comp
  条件: (s : Multiset R[X]) (q : R[X])
  证明: map_multiset_prod (compRingHom q) _

Depends on / 依赖: compRingHom, map_multiset_prod
-/
theorem multiset_prod_comp (s : Multiset R[X]) (q : R[X]) :
    s.prod.comp q = (s.map fun p : R[X] => p.comp q).prod :=
  map_multiset_prod (compRingHom q) _

/--
theorem `prod_comp` / 定理 `prod_comp`

English:
theorem prod_comp
  given: {ι : Type*} (s : Finset ι) (p : ι -> R[X]) (q : R[X])
  proof: map_prod (compRingHom q) _ _

中文:
定理 prod_comp
  条件: {ι : 类型} (s : Finset ι) (p : ι -> R[X]) (q : R[X])
  证明: map_prod (compRingHom q) _ _

Depends on / 依赖: compRingHom, map_prod
-/
theorem prod_comp {ι : Type*} (s : Finset ι) (p : ι -> R[X]) (q : R[X]) :
    (∏ j in s, p j).comp q = ∏ j in s, (p j).comp q :=
  map_prod (compRingHom q) _ _

/--
theorem `isRoot_prod` / 定理 `isRoot_prod`

English:
theorem isRoot_prod
  statement: {R} [CommSemiring R] [IsDomain R] {ι : Type*} (s : Finset ι) (p : ι -> R[X])
  proof: by
  simp only [IsRoot, eval_prod, Finset.prod_eq_zero_iff]

@[gcongr]

中文:
定理 isRoot_prod
  结论: {R} [CommSemiring R] [IsDomain R] {ι : 类型} (s : Finset ι) (p : ι -> R[X])
  证明: by
  simp only [IsRoot, eval_prod, Finset.prod_eq_zero_iff]

@[gcongr]

Depends on / 依赖: Finset, Finset.prod_eq_zero_iff, IsRoot, eval_prod, prod_eq_zero_iff
-/
theorem isRoot_prod {R} [CommSemiring R] [IsDomain R] {ι : Type*} (s : Finset ι) (p : ι -> R[X])
    (x : R) : IsRoot (∏ j in s, p j) x ↔ exists i in s, IsRoot (p i) x := by
  simp only [IsRoot, eval_prod, Finset.prod_eq_zero_iff]

@[gcongr]
/--
theorem `eval_dvd` / 定理 `eval_dvd`

English:
theorem eval_dvd
  statement: p ∣ q -> eval x p ∣ eval x q
  proof: eval₂_dvd _ _

中文:
定理 eval_dvd
  结论: p ∣ q -> eval x p ∣ eval x q
  证明: eval₂_dvd _ _

Depends on / 依赖: nontrivial, s.toSubsemiring.nontrivial, toSubsemiring
-/
theorem eval_dvd : p ∣ q -> eval x p ∣ eval x q :=
  eval₂_dvd _ _

/--
theorem `eval_eq_zero_of_dvd_of_eval_eq_zero` / 定理 `eval_eq_zero_of_dvd_of_eval_eq_zero`

English:
theorem eval_eq_zero_of_dvd_of_eval_eq_zero
  statement: p ∣ q -> eval x p = 0 -> eval x q = 0
  proof: eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _

@[simp]

中文:
定理 eval_eq_zero_of_dvd_of_eval_eq_zero
  结论: p ∣ q -> eval x p = 0 -> eval x q = 0
  证明: eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _

@[simp]

Depends on / 依赖: noZeroDivisors, s.toSubsemiring.noZeroDivisors, toSubsemiring
-/
theorem eval_eq_zero_of_dvd_of_eval_eq_zero : p ∣ q -> eval x p = 0 -> eval x q = 0 :=
  eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _

@[simp]
/--
theorem `eval_geom_sum` / 定理 `eval_geom_sum`

English:
theorem eval_geom_sum
  given: {R} [CommSemiring R] {n : Nat} {x : R}
  proof: by simp [eval_finsetSum]

中文:
定理 eval_geom_sum
  条件: {R} [CommSemiring R] {n : 自然数} {x : R}
  证明: by simp [eval_finsetSum]

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, eval_finsetSum, to_isDomain
-/
theorem eval_geom_sum {R} [CommSemiring R] {n : Nat} {x : R} :
    eval x (∑ i in range n, X ^ i) = ∑ i in range n, x ^ i := by simp [eval_finsetSum]

variable [NoZeroDivisors R]

/--
lemma `root_mul` / 引理 `root_mul`

English:
lemma root_mul
  statement: IsRoot (p * q) a ↔ IsRoot p a ∨ IsRoot q a
  proof: by
  simp_rw [IsRoot, eval_mul, mul_eq_zero]

中文:
引理 root_mul
  结论: IsRoot (p * q) a ↔ IsRoot p a ∨ IsRoot q a
  证明: by
  simp_rw [IsRoot, eval_mul, mul_eq_zero]

Depends on / 依赖: IsRoot, eval_mul, mul_eq_zero, simp_rw
-/
lemma root_mul : IsRoot (p * q) a ↔ IsRoot p a ∨ IsRoot q a := by
  simp_rw [IsRoot, eval_mul, mul_eq_zero]

/--
lemma `root_or_root_of_root_mul` / 引理 `root_or_root_of_root_mul`

English:
lemma root_or_root_of_root_mul
  given: (h : IsRoot (p * q) a)
  statement: IsRoot p a ∨ IsRoot q a
  proof: root_mul.1 h

中文:
引理 root_or_root_of_root_mul
  条件: (h : IsRoot (p * q) a)
  结论: IsRoot p a ∨ IsRoot q a
  证明: root_mul.1 h

Depends on / 依赖: root_mul
-/
lemma root_or_root_of_root_mul (h : IsRoot (p * q) a) : IsRoot p a ∨ IsRoot q a :=
  root_mul.1 h

end

end Eval

section Map

variable [CommSemiring R] [CommSemiring S] (f : R ->+* S)

/--
theorem `map_multiset_prod` / 定理 `map_multiset_prod`

English:
theorem map_multiset_prod
  given: (m : Multiset R[X])
  statement: m.prod.map f = (m.map <| map f).prod
  proof: Eq.symm Multiset.prod_hom _ (mapRingHom f).toMonoidHom

中文:
定理 map_multiset_prod
  条件: (m : Multiset R[X])
  结论: m.prod.map f = (m.map <| map f).prod
  证明: Eq.symm Multiset.prod_hom _ (mapRingHom f).toMonoidHom
-/
protected theorem map_multiset_prod (m : Multiset R[X]) : m.prod.map f = (m.map <| map f).prod :=
Eq.symm Multiset.prod_hom _ (mapRingHom f).toMonoidHom

/--
theorem `map_prod` / 定理 `map_prod`

English:
theorem map_prod
  given: {ι : Type*} (g : ι -> R[X]) (s : Finset ι)
  proof: map_prod (mapRingHom f) _ _

中文:
定理 map_prod
  条件: {ι : 类型} (g : ι -> R[X]) (s : Finset ι)
  证明: map_prod (mapRingHom f) _ _
-/
protected theorem map_prod {ι : Type*} (g : ι -> R[X]) (s : Finset ι) :
    (∏ i in s, g i).map f = ∏ i in s, (g i).map f :=
  map_prod (mapRingHom f) _ _

end Map

end CommSemiring

section Ring

variable [Ring R] {p q r : R[X]}

@[simp]
/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: {S} [Ring S] (f : R ->+* S)
  statement: (p - q).map f = p.map f - q.map f
  proof: (mapRingHom f).map_sub p q

@[simp]

中文:
定理 map_sub
  条件: {S} [Ring S] (f : R ->+* S)
  结论: (p - q).map f = p.map f - q.map f
  证明: (mapRingHom f).map_sub p q

@[simp]
-/
protected theorem map_sub {S} [Ring S] (f : R ->+* S) : (p - q).map f = p.map f - q.map f :=
  (mapRingHom f).map_sub p q

@[simp]
/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: {S} [Ring S] (f : R ->+* S)
  statement: (-p).map f = -p.map f
  proof: (mapRingHom f).map_neg p

中文:
定理 map_neg
  条件: {S} [Ring S] (f : R ->+* S)
  结论: (-p).map f = -p.map f
  证明: (mapRingHom f).map_neg p
-/
protected theorem map_neg {S} [Ring S] (f : R ->+* S) : (-p).map f = -p.map f :=
  (mapRingHom f).map_neg p

/--
lemma `map_intCast` / 引理 `map_intCast`

English:
lemma map_intCast
  given: {S} [Ring S] (f : R ->+* S) (n : Int)
  statement: map f ↑n = ↑n
  proof: map_intCast (mapRingHom f) n

@[simp]

中文:
引理 map_intCast
  条件: {S} [Ring S] (f : R ->+* S) (n : 整数)
  结论: map f ↑n = ↑n
  证明: map_intCast (mapRingHom f) n

@[simp]
-/
@[simp] protected lemma map_intCast {S} [Ring S] (f : R ->+* S) (n : Int) : map f ↑n = ↑n :=
  map_intCast (mapRingHom f) n

@[simp]
/--
theorem `eval_intCast` / 定理 `eval_intCast`

English:
theorem eval_intCast
  given: {n : Int} {x : R}
  statement: (n : R[X]).eval x = n
  proof: by
  simp only [← C_eq_intCast, eval_C]

@[simp]

中文:
定理 eval_intCast
  条件: {n : 整数} {x : R}
  结论: (n : R[X]).eval x = n
  证明: by
  simp only [← C_eq_intCast, eval_C]

@[simp]

Depends on / 依赖: C_eq_intCast, eval_C
-/
theorem eval_intCast {n : Int} {x : R} : (n : R[X]).eval x = n := by
  simp only [← C_eq_intCast, eval_C]

@[simp]
/--
theorem `eval₂_neg` / 定理 `eval₂_neg`

English:
theorem eval₂_neg
  given: {S} [Ring S] (f : R ->+* S) {x : S}
  statement: (-p).eval₂ f x = -p.eval₂ f x
  proof: by
  rw [eq_neg_iff_add_eq_zero]; rw [← eval₂_add]; rw [neg_add_cancel]; rw [eval₂_zero]

@[simp]

中文:
定理 eval₂_neg
  条件: {S} [Ring S] (f : R ->+* S) {x : S}
  结论: (-p).eval₂ f x = -p.eval₂ f x
  证明: by
  rw [eq_neg_iff_add_eq_zero]; rw [← eval₂_add]; rw [neg_add_cancel]; rw [eval₂_zero]

@[simp]

Depends on / 依赖: eq_neg_iff_add_eq_zero, neg_add_cancel
-/
theorem eval₂_neg {S} [Ring S] (f : R ->+* S) {x : S} : (-p).eval₂ f x = -p.eval₂ f x := by
  rw [eq_neg_iff_add_eq_zero]; rw [← eval₂_add]; rw [neg_add_cancel]; rw [eval₂_zero]

@[simp]
/--
theorem `eval₂_sub` / 定理 `eval₂_sub`

English:
theorem eval₂_sub
  given: {S} [Ring S] (f : R ->+* S) {x : S}
  proof: by
  rw [sub_eq_add_neg]; rw [eval₂_add]; rw [eval₂_neg]; rw [sub_eq_add_neg]

@[simp]

中文:
定理 eval₂_sub
  条件: {S} [Ring S] (f : R ->+* S) {x : S}
  证明: by
  rw [sub_eq_add_neg]; rw [eval₂_add]; rw [eval₂_neg]; rw [sub_eq_add_neg]

@[simp]

Depends on / 依赖: sub_eq_add_neg
-/
theorem eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} :
    (p - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x := by
  rw [sub_eq_add_neg]; rw [eval₂_add]; rw [eval₂_neg]; rw [sub_eq_add_neg]

@[simp]
/--
theorem `eval_neg` / 定理 `eval_neg`

English:
theorem eval_neg
  given: (p : R[X]) (x : R)
  statement: (-p).eval x = -p.eval x
  proof: eval₂_neg _

@[simp]

中文:
定理 eval_neg
  条件: (p : R[X]) (x : R)
  结论: (-p).eval x = -p.eval x
  证明: eval₂_neg _

@[simp]
-/
theorem eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval x :=
  eval₂_neg _

@[simp]
/--
theorem `eval_sub` / 定理 `eval_sub`

English:
theorem eval_sub
  given: (p q : R[X]) (x : R)
  statement: (p - q).eval x = p.eval x - q.eval x
  proof: eval₂_sub _

中文:
定理 eval_sub
  条件: (p q : R[X]) (x : R)
  结论: (p - q).eval x = p.eval x - q.eval x
  证明: eval₂_sub _
-/
theorem eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.eval x - q.eval x :=
  eval₂_sub _

/--
theorem `root_X_sub_C` / 定理 `root_X_sub_C`

English:
theorem root_X_sub_C
  statement: IsRoot (X - C a) b ↔ a = b
  proof: by
  rw [IsRoot.def]; rw [eval_sub]; rw [eval_X]; rw [eval_C]; rw [sub_eq_zero]; rw [eq_comm]

@[simp]

中文:
定理 root_X_sub_C
  结论: IsRoot (X - C a) b ↔ a = b
  证明: by
  rw [IsRoot.def]; rw [eval_sub]; rw [eval_X]; rw [eval_C]; rw [sub_eq_zero]; rw [eq_comm]

@[simp]

Depends on / 依赖: IsRoot, IsRoot.def, eq_comm, eval_C, eval_X, eval_sub, sub_eq_zero
-/
theorem root_X_sub_C : IsRoot (X - C a) b ↔ a = b := by
  rw [IsRoot.def]; rw [eval_sub]; rw [eval_X]; rw [eval_C]; rw [sub_eq_zero]; rw [eq_comm]

@[simp]
/--
theorem `neg_comp` / 定理 `neg_comp`

English:
theorem neg_comp
  statement: (-p).comp q = -p.comp q
  proof: eval₂_neg _

@[simp]

中文:
定理 neg_comp
  结论: (-p).comp q = -p.comp q
  证明: eval₂_neg _

@[simp]
-/
theorem neg_comp : (-p).comp q = -p.comp q :=
  eval₂_neg _

@[simp]
/--
theorem `sub_comp` / 定理 `sub_comp`

English:
theorem sub_comp
  statement: (p - q).comp r = p.comp r - q.comp r
  proof: eval₂_sub _

@[simp]

中文:
定理 sub_comp
  结论: (p - q).comp r = p.comp r - q.comp r
  证明: eval₂_sub _

@[simp]
-/
theorem sub_comp : (p - q).comp r = p.comp r - q.comp r :=
  eval₂_sub _

@[simp]
/--
theorem `intCast_comp` / 定理 `intCast_comp`

English:
theorem intCast_comp
  given: (i : Int)
  statement: comp (i : R[X]) p = i
  proof: by cases i <;> simp

@[simp]

中文:
定理 intCast_comp
  条件: (i : 整数)
  结论: comp (i : R[X]) p = i
  证明: by cases i <;> simp

@[simp]
-/
theorem intCast_comp (i : Int) : comp (i : R[X]) p = i := by cases i <;> simp

@[simp]
/--
theorem `eval₂_at_intCast` / 定理 `eval₂_at_intCast`

English:
theorem eval₂_at_intCast
  given: {S : Type*} [Ring S] (f : R ->+* S) (n : Int)
  proof: by
  convert! eval₂_at_apply (p := p) f n
  simp

中文:
定理 eval₂_at_intCast
  条件: {S : 类型} [Ring S] (f : R ->+* S) (n : 整数)
  证明: by
  convert! eval₂_at_apply (p := p) f n
  simp

Depends on / 依赖: convert
-/
theorem eval₂_at_intCast {S : Type*} [Ring S] (f : R ->+* S) (n : Int) :
    p.eval₂ f n = f (p.eval n) := by
  convert! eval₂_at_apply (p := p) f n
  simp

/--
theorem `mul_X_sub_intCast_comp` / 定理 `mul_X_sub_intCast_comp`

English:
theorem mul_X_sub_intCast_comp
  given: {n : Nat}
  proof: by
  rw [mul_sub]; rw [sub_comp]; rw [mul_X_comp]; rw [← Nat.cast_comm]; rw [natCast_mul_comp]; rw [Nat.cast_comm]; rw [mul_sub]

中文:
定理 mul_X_sub_intCast_comp
  条件: {n : 自然数}
  证明: by
  rw [mul_sub]; rw [sub_comp]; rw [mul_X_comp]; rw [← Nat.cast_comm]; rw [natCast_mul_comp]; rw [Nat.cast_comm]; rw [mul_sub]

Depends on / 依赖: Nat.cast_comm, cast_comm, mul_X_comp, mul_sub, natCast_mul_comp, sub_comp
-/
theorem mul_X_sub_intCast_comp {n : Nat} :
    (p * (X - (n : R[X]))).comp q = p.comp q * (q - n) := by
  rw [mul_sub]; rw [sub_comp]; rw [mul_X_comp]; rw [← Nat.cast_comm]; rw [natCast_mul_comp]; rw [Nat.cast_comm]; rw [mul_sub]

end Ring

end Polynomial
