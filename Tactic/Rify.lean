/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Mario Carneiro, Robert Y. Lewis, Patrick Massot
-/
module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Qify -- shake: keep (for `@[qify_simps]`)

/-!
# `rify` tactic

The `rify` tactic is used to shift propositions from `ℕ`, `ℤ`, `ℚ` or `ℝ≥0` to `ℝ`.

Although less useful than its cousins `zify` and `qify`, it can be useful when your
goal or context already involves real numbers.

In the example below, assumption `hn` is about natural numbers, `hk` is about integers
and involves casting a natural number to `ℤ`, and the conclusion is about real numbers.
The proof uses `rify` to lift both assumptions to `ℝ` before calling `linarith`.
```
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Rify

example {n : ℕ} {k : ℤ} (hn : 8 ≤ n) (hk : 2 * k ≤ n + 2) :
    (0 : ℝ) < n - k - 1 := by
  rify at hn hk
  linarith
```

TODO: Investigate whether we should generalize this to other fields.
-/

public meta section

namespace Mathlib.Tactic.Rify

open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic

/--
`rify` rewrites the main goal by shifting propositions from `ℕ`, `ℤ`, `ℚ` or `ℝ≥0` to `ℝ`.
Although less useful than its cousins `zify` and `qify`, it can be useful when your
goal or context already involves real numbers.

`rify` makes use of the `@[zify_simps]`, `@[qify_simps]` and `@[rify_simps]` attributes to insert
casts into propositions, and the `push_cast` tactic to simplify the `ℝ`-valued expressions.

`rify` is in some sense dual to the `lift` tactic. `lift (r : ℝ) to ℚ` will change the type of a
real number `r` (in the supertype) to `ℚ` (the subtype), given a proof that `r` is rational;
propositions concerning `r` will still be over `ℝ`. `rify` changes propositions about `ℕ`, `ℤ`, `ℚ`
or `ℝ≥0` (the subtype) to propositions about `ℝ` (the supertype), without changing the type of any
variable.

* `rify at l1 l2 ...` rewrites at the given locations.
* `rify [h₁, ..., hₙ]` uses the expressions `h₁`, ..., `hₙ` as extra lemmas for simplification.
  This is especially useful in the presence of nat subtraction or of division: passing arguments of
  type `· ≤ ·` or `· ∣ ·` will allow `push_cast` to do more work.

Examples:
```
/--
import Mathlib

open Real
Here, the assumption `hn` is about natural numbers, `hk` is about integers
and involves casting a natural number to `ℤ`, and the conclusion is about real numbers.
-/
example {n : Nat} {k : Int} (hn : 8 <= n) (hk : 2 * k <= n + 2) :
    (0 : Real) < n - k - 1 := by
  rify at hn hk /- Now have hn : 8 ≤ (n : ℝ) hk : 2 * (k : ℝ) ≤ (n : ℝ) + 2 -/
  linarith

-- Extra hypotheses allow `push_cast` to do more work.
example (a b c : Nat) (h : a - b < c) (hab : b <= a) : a < b + c := by
  rify [hab] at h ⊢ -- Here `zify` or `qify` would have also worked.
  linarith

example (a b : Nat) (ha : π <= a) : 3 <= a + b := by
  rify
  linarith [pi_gt_three]
```
-/
syntax (name := rify) "rify" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| rify $[[$simpArgs,*]]? $[at $location]?) =>
.getD #[] let args := simpArgs.map (·.getElems)
  `(tactic|
    simp -decide only [zify_simps, qify_simps, rify_simps, push_cast, $args,*]
 [at $location]?)

/--
Definition of `mkRifyContext` / `mkRifyContext` 的定义

English:
definition mkRifyContext
  signature: : MetaM Simp.Context
  body: do
  let result ← #[`zify_simps, `qify_simps, `rify_simps, `push_cast].mapM fun ext => do
    let some ext ← getSimpExtension? ext | failure
    ext.getTheorems
  Simp.mkContext {failIfUnchanged := false} (simpTheorems := result)

中文:
定义 mkRifyContext
  签名: : MetaM Simp.Context
  定义体: do
  let result ← #[`zify_simps, `qify_simps, `rify_simps, `push_cast].mapM fun ext => do
    let some ext ← getSimpExtension? ext | failure
    ext.getTheorems
  Simp.mkContext {failIfUnchanged := false} (simpTheorems := result)
-/
def mkRifyContext : MetaM Simp.Context := do
  let result ← #[`zify_simps, `qify_simps, `rify_simps, `push_cast].mapM fun ext => do
    let some ext ← getSimpExtension? ext | failure
    ext.getTheorems
  Simp.mkContext {failIfUnchanged := false} (simpTheorems := result)

/--
Definition of `rifyProof` / `rifyProof` 的定义

English:
definition rifyProof
  signature: (proof : Expr) (prop : Expr)
  body: do
  let (r, _) ← simp prop (← mkRifyContext)
  Zify.applySimpResultToProp' proof prop r

中文:
定义 rifyProof
  签名: (proof : Expr) (prop : Expr)
  定义体: do
  let (r, _) ← simp prop (← mkRifyContext)
  Zify.applySimpResultToProp' proof prop r
-/
def rifyProof (proof : Expr) (prop : Expr) : MetaM (Expr × Expr) := do
  let (r, _) ← simp prop (← mkRifyContext)
  Zify.applySimpResultToProp' proof prop r

/--
lemma `ratCast_eq` / 引理 `ratCast_eq`

English:
lemma ratCast_eq
  given: (a b : Rat)
  statement: a = b ↔ (a : Real) = (b : Real)
  proof: by simp

中文:
引理 ratCast_eq
  条件: (a b : Rat)
  结论: a = b ↔ (a : 实数) = (b : 实数)
  证明: by simp
-/
@[rify_simps] lemma ratCast_eq (a b : Rat) : a = b ↔ (a : Real) = (b : Real) := by simp
/--
lemma `ratCast_le` / 引理 `ratCast_le`

English:
lemma ratCast_le
  given: (a b : Rat)
  statement: a <= b ↔ (a : Real) <= (b : Real)
  proof: by simp

中文:
引理 ratCast_le
  条件: (a b : Rat)
  结论: a <= b ↔ (a : 实数) <= (b : 实数)
  证明: by simp
-/
@[rify_simps] lemma ratCast_le (a b : Rat) : a <= b ↔ (a : Real) <= (b : Real) := by simp
/--
lemma `ratCast_lt` / 引理 `ratCast_lt`

English:
lemma ratCast_lt
  given: (a b : Rat)
  statement: a < b ↔ (a : Real) < (b : Real)
  proof: by simp

中文:
引理 ratCast_lt
  条件: (a b : Rat)
  结论: a < b ↔ (a : 实数) < (b : 实数)
  证明: by simp
-/
@[rify_simps] lemma ratCast_lt (a b : Rat) : a < b ↔ (a : Real) < (b : Real) := by simp
/--
lemma `ratCast_ne` / 引理 `ratCast_ne`

English:
lemma ratCast_ne
  given: (a b : Rat)
  statement: a != b ↔ (a : Real) != (b : Real)
  proof: by simp

中文:
引理 ratCast_ne
  条件: (a b : Rat)
  结论: a != b ↔ (a : 实数) != (b : 实数)
  证明: by simp
-/
@[rify_simps] lemma ratCast_ne (a b : Rat) : a != b ↔ (a : Real) != (b : Real) := by simp


/--
lemma `ofNat_rat_real` / 引理 `ofNat_rat_real`

English:
lemma ofNat_rat_real
  given: (a : Nat) [a.AtLeastTwo]
  proof: rfl

中文:
引理 ofNat_rat_real
  条件: (a : 自然数) [a.AtLeastTwo]
  证明: rfl
-/
@[rify_simps] lemma ofNat_rat_real (a : Nat) [a.AtLeastTwo] :
    ((ofNat(a) : Rat) : Real) = (ofNat(a) : Real) := rfl

end Mathlib.Tactic.Rify
