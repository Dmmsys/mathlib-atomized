/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.ENat.Basic
public meta import Mathlib.Tactic.ToAdditive

/-!
# `enat_to_nat`

This file implements the `enat_to_nat` tactic that shifts `ENat`s in the context to `Nat`.

## Implementation details
The implementation follows these steps:
1. Apply the `cases` tactic to each `ENat` variable, producing two goals: one where the variable
   is `⊤`, and one where it is a finite natural number.
2. Simplify arithmetic expressions involving infinities, making (in)equalities either trivial
   or free of infinities. This step uses the `enat_to_nat_top` simp set.
3. Translate the remaining goals from `ENat` to `Nat` using the `enat_to_nat_coe` simp set.

-/

public meta section

namespace Mathlib.Tactic.ENatToNat

attribute [enat_to_nat_top] OfNat.ofNat_ne_zero ne_eq not_false_eq_true ENat.natCast_ne_top
  ENat.top_ne_natCast ENat.natCast_lt_top top_le_iff le_top
attribute [enat_to_nat_top] top_add ENat.sub_top ENat.top_sub_natCast ENat.mul_top ENat.top_mul

/--
lemma `not_lt_top` / 引理 `not_lt_top`

English:
lemma not_lt_top
  given: (x : ENat)
  proof: by cases x <;> simp

中文:
引理 not_lt_top
  条件: (x : E自然数)
  证明: by cases x <;> simp
-/
@[enat_to_nat_top] lemma not_lt_top (x : ENat) :
    ¬(⊤ < x) := by cases x <;> simp

/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (m n : Nat)
  proof: rfl

中文:
引理 coe_add
  条件: (m n : 自然数)
  证明: rfl
-/
@[enat_to_nat_coe] lemma coe_add (m n : Nat) :
    (m : ENat) + (n : ENat) = ((m + n : Nat) : ENat) := rfl

/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: (m n : Nat)
  proof: rfl

中文:
引理 coe_sub
  条件: (m n : 自然数)
  证明: rfl
-/
@[enat_to_nat_coe] lemma coe_sub (m n : Nat) :
    (m : ENat) - (n : ENat) = ((m - n : Nat) : ENat) := rfl

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (m n : Nat)
  proof: rfl

中文:
引理 coe_mul
  条件: (m n : 自然数)
  证明: rfl
-/
@[enat_to_nat_coe] lemma coe_mul (m n : Nat) :
    (m : ENat) * (n : ENat) = ((m * n : Nat) : ENat) := rfl

/--
lemma `coe_ofNat` / 引理 `coe_ofNat`

English:
lemma coe_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
引理 coe_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
@[enat_to_nat_coe] lemma coe_ofNat (n : Nat) [n.AtLeastTwo] :
    (OfNat.ofNat n : ENat) = (OfNat.ofNat n : Nat) := rfl

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: (0 : ENat) = ((0 : Nat) : ENat)
  proof: rfl

中文:
引理 coe_zero
  结论: (0 : E自然数) = ((0 : 自然数) : E自然数)
  证明: rfl
-/
@[enat_to_nat_coe] lemma coe_zero : (0 : ENat) = ((0 : Nat) : ENat) := rfl

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: (1 : ENat) = ((1 : Nat) : ENat)
  proof: rfl

中文:
引理 coe_one
  结论: (1 : E自然数) = ((1 : 自然数) : E自然数)
  证明: rfl
-/
@[enat_to_nat_coe] lemma coe_one : (1 : ENat) = ((1 : Nat) : ENat) := rfl

attribute [enat_to_nat_coe] ENat.natCast_inj ENat.natCast_le_natCast ENat.natCast_lt_natCast

open Qq Lean Elab Tactic Term Meta in
/-- Finds the first `ENat` in the context and applies the `cases` tactic to it.
Then simplifies expressions involving `⊤` using the `enat_to_nat_top` simp set. -/
elab "cases_first_enat" : tactic => focus do
  let g ← getMainGoal
  g.withContext do
    let ctx ← getLCtx
    let decl? ← ctx.findDeclM? fun decl => do
      if ← (isExprDefEq (← inferType decl.toExpr) q(ENat)) then
        return Option.some decl
      else
        return Option.none
    let some decl := decl? | throwError "No ENats"
.isSome let isInaccessible := ctx.inaccessibleFVars.find? (·.fvarId == decl.fvarId)
    if isInaccessible then
      let name : Name := `enat_to_nat_aux
      setGoals [← g.rename decl.fvarId name]
      let x := mkIdent name
      evalTactic (← `(tactic| cases $x:ident using ENat.recTopCoe))
    else
      let x := mkIdent decl.userName
      evalTactic
        (← `(tactic| cases $x:ident using ENat.recTopCoe with | top => _ | coe $x:ident => _))
    evalTactic (← `(tactic| all_goals try simp only [enat_to_nat_top] at *))

/-- `enat_to_nat` shifts all `ENat`s in the context to `Nat`, rewriting propositions about them.
A typical use case is `enat_to_nat; lia`. -/
macro "enat_to_nat" : tactic => `(tactic| focus (
    (repeat' cases_first_enat) <;>
    (try simp only [enat_to_nat_top, enat_to_nat_coe] at *)
  )
)

end Mathlib.Tactic.ENatToNat
