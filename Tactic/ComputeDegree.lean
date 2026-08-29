/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!

# `compute_degree` and `monicity`: tactics for explicit polynomials

This file defines two related tactics: `compute_degree` and `monicity`.

Using `compute_degree` when the goal is of one of the seven forms
* `natDegree f ≤ d` (or `<`),
* `degree f ≤ d` (or `<`),
* `natDegree f = d`,
* `degree f = d`,
* `coeff f d = r`, if `d` is the degree of `f`,

tries to solve the goal.
It may leave side-goals, in case it is not entirely successful.

Using `monicity` when the goal is of the form `Monic f` tries to solve the goal.
It may leave side-goals, in case it is not entirely successful.

Both tactics admit a `!` modifier (`compute_degree!` and `monicity!`) instructing
Lean to try harder to close the goal.

See the doc-strings for more details.

## Future work

* Currently, `compute_degree` does not deal correctly with some edge cases. For instance,
  ```lean
  example [Semiring R] : natDegree (C 0 : R[X]) = 0 := by
    compute_degree
  -- ⊢ 0 ≠ 0
  ```
  Still, it may not be worth to provide special support for `natDegree f = 0`.
* Make sure that numerals in coefficients are treated correctly.
* Make sure that `compute_degree` works with goals of the form `degree f ≤ ↑d`, with an
  explicit coercion from `ℕ` on the RHS.
* Add support for proving goals of the from `natDegree f ≠ 0` and `degree f ≠ 0`.
* Make sure that `degree`, `natDegree` and `coeff` are equally supported.

## Implementation details

Assume that `f : R[X]` is a polynomial with coefficients in a semiring `R` and
`d` is either in `ℕ` or in `WithBot ℕ`.

If the goal has the form `natDegree f < d`, then we convert it to two separate goals:
* `natDegree f ≤ ?_`, on which we apply the following steps;
* `?_ < d`;

where `?_` is a metavariable that `compute_degree` computes in its process.
We proceed similarly for `degree f < d`.

If the goal has the form `natDegree f = d`, then we convert it to three separate goals:
* `natDegree f ≤ d`;
* `coeff f d = r`;
* `r ≠ 0`.

Similarly, an initial goal of the form `degree f = d` gives rise to goals of the form
* `degree f ≤ d`;
* `coeff f d = r`;
* `r ≠ 0`.

Next, we apply successively lemmas whose side-goals all have the shape
* `natDegree f ≤ d`;
* `degree f ≤ d`;
* `coeff f d = r`;

plus possibly "numerical" identities and choices of elements in `ℕ`, `WithBot ℕ`, and `R`.

Recursing into `f`, we break apart additions, multiplications, powers, subtractions,...
The leaves of the process are
* numerals, `C a`, `X` and `monomial a n`, to which we assign degree `0`, `1` and `a` respectively;
* `fvar`s `f`, to which we tautologically assign degree `natDegree f`.
-/

public meta section

open Polynomial

namespace Mathlib.Tactic.ComputeDegree

section recursion_lemmas
/-!
### Simple lemmas about `natDegree`

The lemmas in this section all have the form `natDegree <some form of cast> ≤ 0`.
Their proofs are weakenings of the stronger lemmas `natDegree <same> = 0`.
These are the lemmas called by `compute_degree` on (almost) all the leaves of its recursion.
-/

variable {R : Type*}

section semiring
variable [Semiring R]

/--
theorem `natDegree_C_le` / 定理 `natDegree_C_le`

English:
theorem natDegree_C_le
  given: (a : R)
  statement: natDegree (C a) <= 0
  proof: (natDegree_C a).le

中文:
定理 natDegree_C_le
  条件: (a : R)
  结论: natDegree (C a) <= 0
  证明: (natDegree_C a).le

Depends on / 依赖: natDegree_C
-/
theorem natDegree_C_le (a : R) : natDegree (C a) <= 0 := (natDegree_C a).le

/--
theorem `natDegree_natCast_le` / 定理 `natDegree_natCast_le`

English:
theorem natDegree_natCast_le
  given: (n : Nat)
  statement: natDegree (n : R[X]) <= 0
  proof: (natDegree_natCast _).le

中文:
定理 natDegree_natCast_le
  条件: (n : 自然数)
  结论: natDegree (n : R[X]) <= 0
  证明: (natDegree_natCast _).le

Depends on / 依赖: natDegree_natCast
-/
theorem natDegree_natCast_le (n : Nat) : natDegree (n : R[X]) <= 0 := (natDegree_natCast _).le
/--
theorem `natDegree_zero_le` / 定理 `natDegree_zero_le`

English:
theorem natDegree_zero_le
  statement: natDegree (0 : R[X]) <= 0
  proof: natDegree_zero.le

中文:
定理 natDegree_zero_le
  结论: natDegree (0 : R[X]) <= 0
  证明: natDegree_zero.le

Depends on / 依赖: natDegree_zero, natDegree_zero.le
-/
theorem natDegree_zero_le : natDegree (0 : R[X]) <= 0 := natDegree_zero.le
/--
theorem `natDegree_one_le` / 定理 `natDegree_one_le`

English:
theorem natDegree_one_le
  statement: natDegree (1 : R[X]) <= 0
  proof: natDegree_one.le

中文:
定理 natDegree_one_le
  结论: natDegree (1 : R[X]) <= 0
  证明: natDegree_one.le

Depends on / 依赖: natDegree_one, natDegree_one.le
-/
theorem natDegree_one_le : natDegree (1 : R[X]) <= 0 := natDegree_one.le

/--
theorem `coeff_add_of_eq` / 定理 `coeff_add_of_eq`

English:
theorem coeff_add_of_eq
  statement: {n : Nat} {a b : R} {f g : R[X]}
  proof: by subst ‹_› ‹_›; apply coeff_add

中文:
定理 coeff_add_of_eq
  结论: {n : 自然数} {a b : R} {f g : R[X]}
  证明: by subst ‹_› ‹_›; apply coeff_add

Depends on / 依赖: coeff_add
-/
theorem coeff_add_of_eq {n : Nat} {a b : R} {f g : R[X]}
    (h_add_left : f.coeff n = a) (h_add_right : g.coeff n = b) :
    (f + g).coeff n = a + b := by subst ‹_› ‹_›; apply coeff_add

/--
theorem `coeff_mul_add_of_le_natDegree_of_eq_ite` / 定理 `coeff_mul_add_of_le_natDegree_of_eq_ite`

English:
theorem coeff_mul_add_of_le_natDegree_of_eq_ite
  statement: {d df dg : Nat} {a b : R} {f g : R[X]}
  proof: by
  split_ifs with h
  · subst h_mul_left h_mul_right h
    exact coeff_mul_add_eq_of_natDegree_le ‹_› ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ddf ?_)
    · exact natDegree_mul_le_of_le ‹_› ‹_›
    · exact ne_comm.mp h

中文:
定理 coeff_mul_add_of_le_natDegree_of_eq_ite
  结论: {d df dg : 自然数} {a b : R} {f g : R[X]}
  证明: by
  split_ifs with h
  · subst h_mul_left h_mul_right h
    exact coeff_mul_add_eq_of_natDegree_le ‹_› ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ddf ?_)
    · exact natDegree_mul_le_of_le ‹_› ‹_›
    · exact ne_comm.mp h

Depends on / 依赖: coeff_eq_zero_of_natDegree_lt, coeff_mul_add_eq_of_natDegree_le, h_mul_left, h_mul_right, lt_of_le_of_lt, lt_of_le_of_ne, natDegree_mul_le_of_le, ne_comm, ne_comm.mp, split_ifs
-/
theorem coeff_mul_add_of_le_natDegree_of_eq_ite {d df dg : Nat} {a b : R} {f g : R[X]}
    (h_mul_left : natDegree f <= df) (h_mul_right : natDegree g <= dg)
    (h_mul_left : f.coeff df = a) (h_mul_right : g.coeff dg = b) (ddf : df + dg <= d) :
    (f * g).coeff d = if d = df + dg then a * b else 0 := by
  split_ifs with h
  · subst h_mul_left h_mul_right h
    exact coeff_mul_add_eq_of_natDegree_le ‹_› ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ddf ?_)
    · exact natDegree_mul_le_of_le ‹_› ‹_›
    · exact ne_comm.mp h

/--
theorem `coeff_pow_of_natDegree_le_of_eq_ite'` / 定理 `coeff_pow_of_natDegree_le_of_eq_ite'`

English:
theorem coeff_pow_of_natDegree_le_of_eq_ite'
  statement: {m n o : Nat} {a : R} {p : R[X]}
  proof: by
  split_ifs with h
  · subst h h_pow_bas
    exact coeff_pow_of_natDegree_le ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ‹_› ?_)
    · exact natDegree_pow_le_of_le m ‹_›
    · exact Iff.mp ne_comm h

中文:
定理 coeff_pow_of_natDegree_le_of_eq_ite'
  结论: {m n o : 自然数} {a : R} {p : R[X]}
  证明: by
  split_ifs with h
  · subst h h_pow_bas
    exact coeff_pow_of_natDegree_le ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ‹_› ?_)
    · exact natDegree_pow_le_of_le m ‹_›
    · exact Iff.mp ne_comm h

Depends on / 依赖: Iff.mp, coeff_eq_zero_of_natDegree_lt, coeff_pow_of_natDegree_le, h_pow_bas, lt_of_le_of_lt, lt_of_le_of_ne, natDegree_pow_le_of_le, ne_comm, split_ifs
-/
theorem coeff_pow_of_natDegree_le_of_eq_ite' {m n o : Nat} {a : R} {p : R[X]}
    (h_pow : natDegree p <= n) (h_exp : m * n <= o) (h_pow_bas : coeff p n = a) :
    coeff (p ^ m) o = if o = m * n then a ^ m else 0 := by
  split_ifs with h
  · subst h h_pow_bas
    exact coeff_pow_of_natDegree_le ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ‹_› ?_)
    · exact natDegree_pow_le_of_le m ‹_›
    · exact Iff.mp ne_comm h

section SMul

variable {S : Type*} [SMulZeroClass S R] {n : Nat} {a : S} {f : R[X]}

/--
theorem `natDegree_smul_le_of_le` / 定理 `natDegree_smul_le_of_le`

English:
theorem natDegree_smul_le_of_le
  given: (hf : natDegree f <= n)
  proof: (natDegree_smul_le a f).trans hf

中文:
定理 natDegree_smul_le_of_le
  条件: (hf : natDegree f <= n)
  证明: (natDegree_smul_le a f).trans hf

Depends on / 依赖: natDegree_smul_le
-/
theorem natDegree_smul_le_of_le (hf : natDegree f <= n) :
    natDegree (a • f) <= n :=
  (natDegree_smul_le a f).trans hf

/--
theorem `degree_smul_le_of_le` / 定理 `degree_smul_le_of_le`

English:
theorem degree_smul_le_of_le
  given: (hf : degree f <= n)
  proof: (degree_smul_le a f).trans hf

中文:
定理 degree_smul_le_of_le
  条件: (hf : degree f <= n)
  证明: (degree_smul_le a f).trans hf

Depends on / 依赖: degree_smul_le
-/
theorem degree_smul_le_of_le (hf : degree f <= n) :
    degree (a • f) <= n :=
  (degree_smul_le a f).trans hf

/--
theorem `coeff_smul` / 定理 `coeff_smul`

English:
theorem coeff_smul
  statement: (a • f).coeff n = a • f.coeff n
  proof: rfl

中文:
定理 coeff_smul
  结论: (a • f).coeff n = a • f.coeff n
  证明: rfl
-/
theorem coeff_smul : (a • f).coeff n = a • f.coeff n := rfl

end SMul

section congr_lemmas

/--
theorem `natDegree_eq_of_le_of_coeff_ne_zero'` / 定理 `natDegree_eq_of_le_of_coeff_ne_zero'`

English:
theorem natDegree_eq_of_le_of_coeff_ne_zero'
  statement: {deg m o : Nat} {c : R} {p : R[X]}
  proof: by
  subst coeff_eq deg_eq_deg coeff_eq_deg
  exact natDegree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

中文:
定理 natDegree_eq_of_le_of_coeff_ne_zero'
  结论: {deg m o : 自然数} {c : R} {p : R[X]}
  证明: by
  subst coeff_eq deg_eq_deg coeff_eq_deg
  exact natDegree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

Depends on / 依赖: coeff_eq, coeff_eq_deg, deg_eq_deg, natDegree_eq_of_le_of_coeff_ne_zero
-/
theorem natDegree_eq_of_le_of_coeff_ne_zero' {deg m o : Nat} {c : R} {p : R[X]}
    (h_natDeg_le : natDegree p <= m) (coeff_eq : coeff p o = c)
    (coeff_ne_zero : c != 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) :
    natDegree p = deg := by
  subst coeff_eq deg_eq_deg coeff_eq_deg
  exact natDegree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

/--
theorem `degree_eq_of_le_of_coeff_ne_zero'` / 定理 `degree_eq_of_le_of_coeff_ne_zero'`

English:
theorem degree_eq_of_le_of_coeff_ne_zero'
  statement: {deg m o : WithBot Nat} {c : R} {p : R[X]}
  proof: by
  subst coeff_eq coeff_eq_deg deg_eq_deg
  rcases eq_or_ne m ⊥ with rfl | hh
  · exact bot_unique h_deg_le
  · obtain ⟨m, rfl⟩ := WithBot.ne_bot_iff_exists.mp hh
    exact degree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

中文:
定理 degree_eq_of_le_of_coeff_ne_zero'
  结论: {deg m o : WithBot 自然数} {c : R} {p : R[X]}
  证明: by
  subst coeff_eq coeff_eq_deg deg_eq_deg
  rcases eq_or_ne m ⊥ with rfl | hh
  · exact bot_unique h_deg_le
  · obtain ⟨m, rfl⟩ := WithBot.ne_bot_iff_exists.mp hh
    exact degree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

Depends on / 依赖: WithBot, WithBot.ne_bot_iff_exists.mp, bot_unique, coeff_eq, coeff_eq_deg, deg_eq_deg, degree_eq_of_le_of_coeff_ne_zero, eq_or_ne, h_deg_le, ne_bot_iff_exists
-/
theorem degree_eq_of_le_of_coeff_ne_zero' {deg m o : WithBot Nat} {c : R} {p : R[X]}
    (h_deg_le : degree p <= m) (coeff_eq : coeff p (WithBot.unbotD 0 deg) = c)
    (coeff_ne_zero : c != 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) :
    degree p = deg := by
  subst coeff_eq coeff_eq_deg deg_eq_deg
  rcases eq_or_ne m ⊥ with rfl | hh
  · exact bot_unique h_deg_le
  · obtain ⟨m, rfl⟩ := WithBot.ne_bot_iff_exists.mp hh
    exact degree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

variable {m n : Nat} {f : R[X]} {r : R}

/--
theorem `coeff_congr_lhs` / 定理 `coeff_congr_lhs`

English:
theorem coeff_congr_lhs
  given: (h : coeff f m = r) (natDeg_eq_coeff : m = n)
  statement: coeff f n = r
  proof: natDeg_eq_coeff ▸ h

中文:
定理 coeff_congr_lhs
  条件: (h : coeff f m = r) (natDeg_eq_coeff : m = n)
  结论: coeff f n = r
  证明: natDeg_eq_coeff ▸ h

Depends on / 依赖: natDeg_eq_coeff
-/
theorem coeff_congr_lhs (h : coeff f m = r) (natDeg_eq_coeff : m = n) : coeff f n = r :=
  natDeg_eq_coeff ▸ h
/--
theorem `coeff_congr` / 定理 `coeff_congr`

English:
theorem coeff_congr
  given: (h : coeff f m = r) (natDeg_eq_coeff : m = n) {s : R} (rs : r = s)
  proof: natDeg_eq_coeff ▸ rs ▸ h

中文:
定理 coeff_congr
  条件: (h : coeff f m = r) (natDeg_eq_coeff : m = n) {s : R} (rs : r = s)
  证明: natDeg_eq_coeff ▸ rs ▸ h

Depends on / 依赖: natDeg_eq_coeff
-/
theorem coeff_congr (h : coeff f m = r) (natDeg_eq_coeff : m = n) {s : R} (rs : r = s) :
    coeff f n = s :=
  natDeg_eq_coeff ▸ rs ▸ h

end congr_lemmas

end semiring

section ring
variable [Ring R]

/--
theorem `natDegree_intCast_le` / 定理 `natDegree_intCast_le`

English:
theorem natDegree_intCast_le
  given: (n : Int)
  statement: natDegree (n : R[X]) <= 0
  proof: (natDegree_intCast _).le

中文:
定理 natDegree_intCast_le
  条件: (n : 整数)
  结论: natDegree (n : R[X]) <= 0
  证明: (natDegree_intCast _).le

Depends on / 依赖: natDegree_intCast
-/
theorem natDegree_intCast_le (n : Int) : natDegree (n : R[X]) <= 0 := (natDegree_intCast _).le

/--
theorem `coeff_sub_of_eq` / 定理 `coeff_sub_of_eq`

English:
theorem coeff_sub_of_eq
  given: {n : Nat} {a b : R} {f g : R[X]} (hf : f.coeff n = a) (hg : g.coeff n = b)
  proof: by subst hf hg; apply coeff_sub

中文:
定理 coeff_sub_of_eq
  条件: {n : 自然数} {a b : R} {f g : R[X]} (hf : f.coeff n = a) (hg : g.coeff n = b)
  证明: by subst hf hg; apply coeff_sub

Depends on / 依赖: coeff_sub
-/
theorem coeff_sub_of_eq {n : Nat} {a b : R} {f g : R[X]} (hf : f.coeff n = a) (hg : g.coeff n = b) :
    (f - g).coeff n = a - b := by subst hf hg; apply coeff_sub

/--
theorem `coeff_intCast_ite` / 定理 `coeff_intCast_ite`

English:
theorem coeff_intCast_ite
  given: {n : Nat} {a : Int}
  statement: (Int.cast a : R[X]).coeff n = ite (n = 0) a 0
  proof: by
  simp only [← C_eq_intCast, coeff_C, Int.cast_ite, Int.cast_zero]

中文:
定理 coeff_intCast_ite
  条件: {n : 自然数} {a : 整数}
  结论: (整数.cast a : R[X]).coeff n = ite (n = 0) a 0
  证明: by
  simp only [← C_eq_intCast, coeff_C, Int.cast_ite, Int.cast_zero]

Depends on / 依赖: C_eq_intCast, Int.cast_ite, Int.cast_zero, cast_ite, cast_zero, coeff_C
-/
theorem coeff_intCast_ite {n : Nat} {a : Int} : (Int.cast a : R[X]).coeff n = ite (n = 0) a 0 := by
  simp only [← C_eq_intCast, coeff_C, Int.cast_ite, Int.cast_zero]

end ring

end recursion_lemmas

section Tactic

open Lean Elab Tactic Meta Expr

/--
Definition of `twoHeadsArgs` / `twoHeadsArgs` 的定义

English:
definition twoHeadsArgs
  signature: (e : Expr)
  body: Id.run do
  let (eq_or_le, lhs, rhs) ← match e.getAppFnArgs with
    | (na@``Eq, #[_, lhs, rhs]) => pure (na, lhs, rhs)
    | (na@``LE.le, #[_, _, lhs, rhs]) => pure (na, lhs, rhs)
    | (na@``LT.lt, #[_, _, lhs, rhs]) => pure (na, lhs, rhs)
    | _ => return (.anonymous, .anonymous, .inl .anonymous

中文:
定义 twoHeadsArgs
  签名: (e : Expr)
  定义体: Id.run do
  let (eq_or_le, lhs, rhs) ← match e.getAppFnArgs with
    | (na@``Eq, #[_, lhs, rhs]) => pure (na, lhs, rhs)
    | (na@``LE.le, #[_, _, lhs, rhs]) => pure (na, lhs, rhs)
    | (na@``LT.lt, #[_, _, lhs, rhs]) => pure (na, lhs, rhs)
    | _ => return (.anonymous, .anonymous, .inl .anonymous

Depends on / 依赖: Id.run
-/
def twoHeadsArgs (e : Expr) : Name × Name × (Name oplus Name) × List Bool := Id.run do
  let (eq_or_le, lhs, rhs) ← match e.getAppFnArgs with
    | (na@``Eq, #[_, lhs, rhs]) => pure (na, lhs, rhs)
    | (na@``LE.le, #[_, _, lhs, rhs]) => pure (na, lhs, rhs)
    | (na@``LT.lt, #[_, _, lhs, rhs]) => pure (na, lhs, rhs)
    | _ => return (.anonymous, .anonymous, .inl .anonymous, [])
  let (ndeg_or_deg_or_coeff, pol, and?) ← match lhs.getAppFnArgs with
    | (na@``Polynomial.natDegree, #[_, _, pol]) => (na, pol, [rhs.isMVar])
    | (na@``Polynomial.degree, #[_, _, pol]) => (na, pol, [rhs.isMVar])
    | (na@``Polynomial.coeff, #[_, _, pol, c]) => (na, pol, [rhs.isMVar, c.isMVar])
    | _ => return (.anonymous, eq_or_le, .inl .anonymous, [])
  let head := match pol.numeral? with
    -- can I avoid the tri-splitting `n = 0`, `n = 1`, and generic `n`?
    | some 0 => .inl `zero
    | some 1 => .inl `one
    | some _ => .inl `many
    | none => match pol.getAppFnArgs with
      | (``DFunLike.coe, #[_, _, _, _, polFun, _]) =>
        let na := polFun.getAppFn.constName
        if na in [``Polynomial.monomial, ``Polynomial.C] then
          .inr na
        else
          .inl .anonymous
      | (na, _) => .inr na
  (ndeg_or_deg_or_coeff, eq_or_le, head, and?)

/--
Definition of `getCongrLemma` / `getCongrLemma` 的定义

English:
definition getCongrLemma
  signature: (twoH : Name × Name × List Bool) (debug : Bool := false)
  body: let nam := match twoH with
    | (_, ``LE.le, [rhs]) => if rhs then ``id else ``le_trans
    | (_, ``LT.lt, [rhs]) => if rhs then ``id else ``lt_of_le_of_lt
    | (``natDegree, ``Eq, [rhs]) => if rhs then ``id else ``natDegree_eq_of_le_of_coeff_ne_zero'
    | (``degree, ``Eq, [rhs]) => if rhs then `

中文:
定义 getCongrLemma
  签名: (twoH : Name × Name × 列表 布尔值) (debug : 布尔值 := false)
  定义体: let nam := match twoH with
    | (_, ``LE.le, [rhs]) => if rhs then ``id else ``le_trans
    | (_, ``LT.lt, [rhs]) => if rhs then ``id else ``lt_of_le_of_lt
    | (``natDegree, ``Eq, [rhs]) => if rhs then ``id else ``natDegree_eq_of_le_of_coeff_ne_zero'
    | (``degree, ``Eq, [rhs]) => if rhs then `
-/
def getCongrLemma (twoH : Name × Name × List Bool) (debug : Bool := false) : Name :=
  let nam := match twoH with
    | (_, ``LE.le, [rhs]) => if rhs then ``id else ``le_trans
    | (_, ``LT.lt, [rhs]) => if rhs then ``id else ``lt_of_le_of_lt
    | (``natDegree, ``Eq, [rhs]) => if rhs then ``id else ``natDegree_eq_of_le_of_coeff_ne_zero'
    | (``degree, ``Eq, [rhs]) => if rhs then ``id else ``degree_eq_of_le_of_coeff_ne_zero'
    | (``coeff, ``Eq, [rhs, c]) =>
      match rhs, c with
      | false, false => ``coeff_congr
      | false, true => ``Eq.trans
      | true, false => ``coeff_congr_lhs
      | true, true => ``id
    | _ => ``id
  if debug then
    let last := nam.lastComponentAsString
    let natr := if last == "trans" then nam.toString else last
    dbg_trace f!"congr lemma: '{natr}'"
    nam
  else
    nam

-- Internally, `dispatchLemma` produces 3 names: these are the lemmas that are appropriate
-- for goals of the form `natDegree f ≤ d`, `degree f ≤ d`, `coeff f d = a`, in this order.
/--
Definition of `dispatchLemma` / `dispatchLemma` 的定义

English:
definition dispatchLemma
  body: match twoH with
    | (.anonymous, _, _) => ``id -- `twoH` gave default value, so we do nothing
    | (_, .anonymous, _) => ``id -- `twoH` gave default value, so we do nothing
    | (na1, na2, head, bools) =>
      let msg := f!"\ndispatchLemma:\n {head}"
      -- if there is some non-metavariable o

中文:
定义 dispatchLemma
  定义体: match twoH with
    | (.anonymous, _, _) => ``id -- `twoH` gave default value, so we do nothing
    | (_, .anonymous, _) => ``id -- `twoH` gave default value, so we do nothing
    | (na1, na2, head, bools) =>
      let msg := f!"\ndispatchLemma:\n {head}"
      -- if there is some non-metavariable o
-/
def dispatchLemma
    (twoH : Name × Name × (Name oplus Name) × List Bool) (debug : Bool := false) : Name :=
  match twoH with
    | (.anonymous, _, _) => ``id -- `twoH` gave default value, so we do nothing
    | (_, .anonymous, _) => ``id -- `twoH` gave default value, so we do nothing
    | (na1, na2, head, bools) =>
      let msg := f!"\ndispatchLemma:\n {head}"
      -- if there is some non-metavariable on the way, we "congr" it away
      if false in bools then getCongrLemma (na1, na2, bools) debug
      else
      -- otherwise, we select either the first, second or third element of the triple in `nas` below
      let π (natDegLE : Name) (degLE : Name) (coeff : Name) : Name := Id.run do
        let lem := match na1, na2 with
          | ``natDegree, ``LE.le => natDegLE
          | ``degree, ``LE.le => degLE
          | ``coeff, ``Eq => coeff
          | _, ``LE.le => ``le_rfl
          | _, _ => ``rfl
        if debug then
          dbg_trace f!"{lem.lastComponentAsString}\n{msg}"
        lem
      match head with
        | .inl `zero => π ``natDegree_zero_le ``degree_zero_le ``coeff_zero
        | .inl `one => π ``natDegree_one_le ``degree_one_le ``coeff_one
        | .inl `many => π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inl .anonymous => π ``le_rfl ``le_rfl ``rfl
        | .inr ``HAdd.hAdd =>
          π ``natDegree_add_le_of_le ``degree_add_le_of_le ``coeff_add_of_eq
        | .inr ``HSub.hSub =>
          π ``natDegree_sub_le_of_le ``degree_sub_le_of_le ``coeff_sub_of_eq
        | .inr ``HMul.hMul =>
          π ``natDegree_mul_le_of_le ``degree_mul_le_of_le ``coeff_mul_add_of_le_natDegree_of_eq_ite
        | .inr ``HPow.hPow =>
          π ``natDegree_pow_le_of_le ``degree_pow_le_of_le ``coeff_pow_of_natDegree_le_of_eq_ite'
        | .inr ``Neg.neg =>
          π ``natDegree_neg_le_of_le ``degree_neg_le_of_le ``coeff_neg
        | .inr ``Polynomial.X =>
          π ``natDegree_X_le ``degree_X_le ``coeff_X
        | .inr ``Nat.cast =>
          π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inr ``NatCast.natCast =>
          π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inr ``Int.cast =>
          π ``natDegree_intCast_le ``degree_intCast_le ``coeff_intCast_ite
        | .inr ``IntCast.intCast =>
          π ``natDegree_intCast_le ``degree_intCast_le ``coeff_intCast_ite
        | .inr ``Polynomial.monomial =>
          π ``natDegree_monomial_le ``degree_monomial_le ``coeff_monomial
        | .inr ``Polynomial.C =>
          π ``natDegree_C_le ``degree_C_le ``coeff_C
        | .inr ``HSMul.hSMul =>
          π ``natDegree_smul_le_of_le ``degree_smul_le_of_le ``coeff_smul
        | _ => π ``le_rfl ``le_rfl ``rfl

/--
Definition of `tryRfl` / `tryRfl` 的定义

English:
definition tryRfl
  signature: (mvs : List MVarId)
  body: do
  let (yesMV, noMV) ← mvs.partitionM fun mv =>
                          return hasExprMVar (← instantiateMVars (← mv.getDecl).type)
let tried_rfl ← noMV.mapM fun g => g.applyConst ``rfl > return [g]
  let assignable ← yesMV.mapM fun g => do
    let tgt ← instantiateMVars (← g.getDecl).type
    m

中文:
定义 tryRfl
  签名: (mvs : 列表 MVarId)
  定义体: do
  let (yesMV, noMV) ← mvs.partitionM fun mv =>
                          return hasExprMVar (← instantiateMVars (← mv.getDecl).type)
let tried_rfl ← noMV.mapM fun g => g.applyConst ``rfl > return [g]
  let assignable ← yesMV.mapM fun g => do
    let tgt ← instantiateMVars (← g.getDecl).type
    m
-/
def tryRfl (mvs : List MVarId) : MetaM (List MVarId) := do
  let (yesMV, noMV) ← mvs.partitionM fun mv =>
                          return hasExprMVar (← instantiateMVars (← mv.getDecl).type)
let tried_rfl ← noMV.mapM fun g => g.applyConst ``rfl > return [g]
  let assignable ← yesMV.mapM fun g => do
    let tgt ← instantiateMVars (← g.getDecl).type
    match tgt.eq? with
      | some (_, lhs, rhs) =>
        if (isMVar rhs && (! hasExprMVar lhs)) ||
           (isMVar lhs && (! hasExprMVar rhs)) then
           g.applyConst ``rfl
        else pure [g]
      | none =>
        return [g]
  return (assignable.flatten ++ tried_rfl.flatten)

@[deprecated (since := "2026-05-27")] alias try_rfl := tryRfl

/--
Definition of `splitApply` / `splitApply` 的定义

English:
definition splitApply
  signature: (mvs static : List MVarId)
  body: do
  let (can_progress, curr_static) ← mvs.partitionM fun mv => do
    return dispatchLemma (twoHeadsArgs (← mv.getType'')) != ``id
  let progress ← can_progress.mapM fun mv => do
let lem := dispatchLemma twoHeadsArgs (← mv.getType'')
mv.applyConst lem
  return (progress.flatten, static ++ curr_stat

中文:
定义 splitApply
  签名: (mvs static : 列表 MVarId)
  定义体: do
  let (can_progress, curr_static) ← mvs.partitionM fun mv => do
    return dispatchLemma (twoHeadsArgs (← mv.getType'')) != ``id
  let progress ← can_progress.mapM fun mv => do
let lem := dispatchLemma twoHeadsArgs (← mv.getType'')
mv.applyConst lem
  return (progress.flatten, static ++ curr_stat
-/
def splitApply (mvs static : List MVarId) : MetaM ((List MVarId) × (List MVarId)) := do
  let (can_progress, curr_static) ← mvs.partitionM fun mv => do
    return dispatchLemma (twoHeadsArgs (← mv.getType'')) != ``id
  let progress ← can_progress.mapM fun mv => do
let lem := dispatchLemma twoHeadsArgs (← mv.getType'')
mv.applyConst lem
  return (progress.flatten, static ++ curr_static)

/--
Definition of `miscomputedDegree?` / `miscomputedDegree?` 的定义

English:
definition miscomputedDegree?
  signature: (deg : Expr)
  body: miscomputedDegree? deg tgts
    if tgt.ne?.isSome then
      m!"* the coefficient of degree {deg} may be zero" :: rest
    else if let some ((Expr.const ``Nat []), lhs, _) := tgt.le? then
      m!"* there is at least one term of naïve degree {lhs}" :: rest
    else if let some (_, lhs, _) := tgt.eq?

中文:
定义 miscomputedDegree?
  签名: (deg : Expr)
  定义体: miscomputedDegree? deg tgts
    if tgt.ne?.isSome then
      m!"* the coefficient of degree {deg} may be zero" :: rest
    else if let some ((Expr.const ``Nat []), lhs, _) := tgt.le? then
      m!"* there is at least one term of naïve degree {lhs}" :: rest
    else if let some (_, lhs, _) := tgt.eq?

Depends on / 依赖: miscomputedDegree
-/
def miscomputedDegree? (deg : Expr) : List Expr -> List MessageData
  | tgt::tgts =>
    let rest := miscomputedDegree? deg tgts
    if tgt.ne?.isSome then
      m!"* the coefficient of degree {deg} may be zero" :: rest
    else if let some ((Expr.const ``Nat []), lhs, _) := tgt.le? then
      m!"* there is at least one term of naïve degree {lhs}" :: rest
    else if let some (_, lhs, _) := tgt.eq? then
      m!"* there may be a term of naïve degree {lhs}" :: rest
    else rest
  | [] => []

/--
`compute_degree` is a tactic to solve goals of the form
* `natDegree f = d`,
* `degree f = d`,
* `natDegree f ≤ d` (or `<`),
* `degree f ≤ d` (or `<`),
* `coeff f d = r`, if `d` is the degree of `f`.

The tactic may leave goals of the form `d' = d`, `d' ≤ d`, `d' < d`, or `r ≠ 0`, where `d'` in `ℕ`
or `WithBot ℕ` is the tactic's guess of the degree, and `r` is the coefficient's guess of the
leading coefficient of `f`.

`compute_degree` applies `norm_num` to the left-hand side of all side goals, trying to close them.

The variant `compute_degree!` first applies `compute_degree`.
Then it uses `norm_num` on all the remaining goals and tries `assumption`.
-/
syntax (name := computeDegree) "compute_degree" "!"? : tactic

initialize registerTraceClass `Tactic.compute_degree

@[tactic_alt computeDegree]
macro "compute_degree!" : tactic => `(tactic| compute_degree !)

elab_rules : tactic | `(tactic| compute_degree $[!%$bang]?) => focus withMainContext do
  let goal ← getMainGoal
  let gt ← goal.getType''
  let deg? := match gt.eq? with
    | some (_, _, rhs) => some rhs
    | _ => none
  let twoH := twoHeadsArgs gt
  match twoH with
    | (_, .anonymous, _) => throwError m!"'compute_degree' inapplicable. \
        The goal{indentD gt}\nis expected to be '<=', '<' or '='."
    | (.anonymous, _, _) => throwError m!"'compute_degree' inapplicable. \
        The LHS must be an application of 'natDegree', 'degree', or 'coeff'."
    | _ =>
      let lem := dispatchLemma twoH
      trace[Tactic.compute_degree]
        f!"'compute_degree' first applies lemma '{lem.lastComponentAsString}'"
      let mut (gls, static) := (← goal.applyConst lem, [])
      while gls != [] do (gls, static) ← splitApply gls static
      let rfled ← tryRfl static
      setGoals rfled
      -- simplify the left-hand sides, since this is where the degree computations leave
      -- expressions such as `max (0 * 1) (max (1 + 0 + 3 * 4) (7 * 0))`
      evalTactic
        (← `(tactic| try any_goals conv_lhs =>
                       (simp +decide only [Nat.cast_withBot]; norm_num)))
      if bang.isSome then
        let mut false_goals : Array MVarId := #[]
        let mut new_goals : Array MVarId := #[]
        for g in ← getGoals do
          let gs' ← run g do evalTactic (←
            `(tactic| try (any_goals norm_num <;> norm_cast <;> try assumption)))
          new_goals := new_goals ++ gs'.toArray
          if ← gs'.anyM fun g' => g'.withContext do return (← g'.getType'').isConstOf ``False then
            false_goals := false_goals.push g
        setGoals new_goals.toList
        if let some deg := deg? then
          let errors := miscomputedDegree? deg (← false_goals.mapM (MVarId.getType'' ·)).toList
          unless errors.isEmpty do
            throwError Lean.MessageData.joinSep
              (m!"The given degree is '{deg}'. However,\n" :: errors) "\n"

/-- `monicity` tries to solve a goal of the form `Monic f`.
It converts the goal into a goal of the form `natDegree f ≤ n` and one of the form `f.coeff n = 1`
and calls `compute_degree` on those two goals.

The variant `monicity!` starts like `monicity`, but calls `compute_degree!` on the two side-goals.
-/
macro (name := monicityMacro) "monicity" : tactic =>
  `(tactic| (apply monic_of_natDegree_le_of_coeff_eq_one <;> compute_degree))

@[tactic_alt monicityMacro]
macro "monicity!" : tactic =>
  `(tactic| (apply monic_of_natDegree_le_of_coeff_eq_one <;> compute_degree!))

end Tactic

end Mathlib.Tactic.ComputeDegree

/-!
We register `compute_degree` with the `hint` tactic.
-/
register_hint 1000 compute_degree
register_try?_tactic (priority := 1000) compute_degree
