/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Mario Carneiro, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Int.Cast.Lemmas
public meta import Mathlib.Tactic.ToAdditive

/-!
# `qify` tactic

The `qify` tactic is used to shift propositions from `ℕ` or `ℤ` to `ℚ`.
This is often useful since `ℚ` has well-behaved division.
```
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  qify
  qify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/

  sorry
```
-/

public meta section

namespace Mathlib.Tactic.Qify

open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic

/--
`qify` rewrites the main goal by shifting propositions from `ℕ` or `ℤ` to `ℚ`.
This is often useful since `ℚ` has well-behaved subtraction and division.

`qify` makes use of the `@[zify_simps]` and `@[qify_simps]` attributes to insert casts into
propositions, and the `push_cast` tactic to simplify the `ℚ`-valued expressions.

`qify` is in some sense dual to the `lift` tactic. `lift (q : ℚ) to ℤ` will change the type of a
rational number `q` (in the supertype) to `ℤ` (the subtype), given a proof that `q.den = 1`;
propositions concerning `q` will still be over `ℚ`. `qify` changes propositions about `ℕ` or `ℤ`
(the subtype) to propositions about `ℚ` (the supertype), without changing the type of any variable.

* `qify at l1 l2 ...` rewrites at the given locations.
* `qify [h₁, ..., hₙ]` uses the expressions `h₁`, ..., `hₙ` as extra lemmas for simplification.
  This is especially useful in the presence of nat subtraction or of division: passing arguments of
  type `· ≤ ·` or `· ∣ ·` will allow `push_cast` to do more work.

Examples:
```
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  qify
  qify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
  sorry

example (a b c : Int) (h : a / b = c) (hab : b ∣ a) (hb : b != 0) : a = c * b := by
  -- Divisibility hypothesis allows pushing `· / ·`.
  qify [hab] at h hb ⊢
  exact (div_eq_iff hb).1 h
```
-/
syntax (name := qify) "qify" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| qify $[[$simpArgs,*]]? $[at $location]?) =>
.getD #[] let args := simpArgs.map (·.getElems)
  `(tactic|
    simp -decide only [zify_simps, qify_simps, push_cast, $args,*]
 [at $location]?)

/--
lemma `intCast_eq` / 引理 `intCast_eq`

English:
lemma intCast_eq
  given: (a b : Int)
  statement: a = b ↔ (a : Rat) = (b : Rat)
  proof: by simp only [Int.cast_inj]

中文:
引理 intCast_eq
  条件: (a b : 整数)
  结论: a = b ↔ (a : Rat) = (b : Rat)
  证明: by simp only [Int.cast_inj]
-/
@[qify_simps] lemma intCast_eq (a b : Int) : a = b ↔ (a : Rat) = (b : Rat) := by simp only [Int.cast_inj]
/--
lemma `intCast_le` / 引理 `intCast_le`

English:
lemma intCast_le
  given: (a b : Int)
  statement: a <= b ↔ (a : Rat) <= (b : Rat)
  proof: Int.cast_le.symm

中文:
引理 intCast_le
  条件: (a b : 整数)
  结论: a <= b ↔ (a : Rat) <= (b : Rat)
  证明: Int.cast_le.symm
-/
@[qify_simps] lemma intCast_le (a b : Int) : a <= b ↔ (a : Rat) <= (b : Rat) := Int.cast_le.symm
/--
lemma `intCast_lt` / 引理 `intCast_lt`

English:
lemma intCast_lt
  given: (a b : Int)
  statement: a < b ↔ (a : Rat) < (b : Rat)
  proof: Int.cast_lt.symm

中文:
引理 intCast_lt
  条件: (a b : 整数)
  结论: a < b ↔ (a : Rat) < (b : Rat)
  证明: Int.cast_lt.symm
-/
@[qify_simps] lemma intCast_lt (a b : Int) : a < b ↔ (a : Rat) < (b : Rat) := Int.cast_lt.symm
/--
lemma `intCast_ne` / 引理 `intCast_ne`

English:
lemma intCast_ne
  given: (a b : Int)
  statement: a != b ↔ (a : Rat) != (b : Rat)
  proof: by
  simp only [ne_eq, Int.cast_inj]

中文:
引理 intCast_ne
  条件: (a b : 整数)
  结论: a != b ↔ (a : Rat) != (b : Rat)
  证明: by
  simp only [ne_eq, Int.cast_inj]
-/
@[qify_simps] lemma intCast_ne (a b : Int) : a != b ↔ (a : Rat) != (b : Rat) := by
  simp only [ne_eq, Int.cast_inj]

end Qify

end Mathlib.Tactic
