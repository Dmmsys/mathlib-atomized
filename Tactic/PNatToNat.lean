/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.PNat.Basic
public meta import Mathlib.Tactic.ToAdditive


/-!
# `pnat_to_nat`

This file implements the `pnat_to_nat` tactic that shifts `PNat`s in the context to `Nat`.

## Implementation details
The implementation follows these steps:
1. For each `x : PNat` in the context, add the hypothesis `0 < (↑x : ℕ)`.
2. Translate arithmetic on `PNat` to `Nat` using the `pnat_to_nat_coe` simp set.

-/

public meta section

namespace Mathlib.Tactic.PNatToNat

open Lean Meta Elab Tactic Qq

/-- For each `x : PNat` in the context, add the hypothesis `0 < (↑x : ℕ)`. -/
elab "pnat_positivity" : tactic => withMainContext do
  let result ← (← getLCtx).foldlM (init := ← getMainGoal) fun g decl => do
    let ⟨1, declType, declExpr⟩ ← inferTypeQ decl.toExpr | return g
    let ~q(PNat) := declType | return g
    let pf := q(PNat.pos $declExpr)
    let ctx ← getLCtx
let alreadyDeclared := Option.isSome ← ctx.findDeclM? fun ldecl => do
      if ← isDefEq ldecl.type q(0 < PNat.val $declExpr) then
pure some ()
      else
        pure none
    if alreadyDeclared then
      return g
    let (_, mvarIdNew) ← (← g.assert .anonymous q(0 < PNat.val $declExpr) pf).intro1P
    return mvarIdNew
  setGoals [result]

@[pnat_to_nat_coe]
/--
lemma `coe_inj` / 引理 `coe_inj`

English:
lemma coe_inj
  given: (m n : PNat)
  statement: m = n ↔ (m : Nat) = (n : Nat)
  proof: by simp

@[pnat_to_nat_coe]

中文:
引理 coe_inj
  条件: (m n : P自然数)
  结论: m = n ↔ (m : 自然数) = (n : 自然数)
  证明: by simp

@[pnat_to_nat_coe]
-/
lemma coe_inj (m n : PNat) : m = n ↔ (m : Nat) = (n : Nat) := by simp

@[pnat_to_nat_coe]
/--
lemma `coe_le_coe` / 引理 `coe_le_coe`

English:
lemma coe_le_coe
  given: (m n : PNat)
  statement: m <= n ↔ (m : Nat) <= (n : Nat)
  proof: by simp

@[pnat_to_nat_coe]

中文:
引理 coe_le_coe
  条件: (m n : P自然数)
  结论: m <= n ↔ (m : 自然数) <= (n : 自然数)
  证明: by simp

@[pnat_to_nat_coe]
-/
lemma coe_le_coe (m n : PNat) : m <= n ↔ (m : Nat) <= (n : Nat) := by simp

@[pnat_to_nat_coe]
/--
lemma `coe_lt_coe` / 引理 `coe_lt_coe`

English:
lemma coe_lt_coe
  given: (m n : PNat)
  statement: m < n ↔ (m : Nat) < (n : Nat)
  proof: by simp

中文:
引理 coe_lt_coe
  条件: (m n : P自然数)
  结论: m < n ↔ (m : 自然数) < (n : 自然数)
  证明: by simp
-/
lemma coe_lt_coe (m n : PNat) : m < n ↔ (m : Nat) < (n : Nat) := by simp

attribute [pnat_to_nat_coe] PNat.add_coe PNat.mul_coe PNat.val_ofNat

set_option backward.isDefEq.respectTransparency false in
@[pnat_to_nat_coe]
/--
lemma `sub_coe` / 引理 `sub_coe`

English:
lemma sub_coe
  given: (a b : PNat)
  statement: ((a - b : PNat) : Nat) = a.val - 1 - b.val + 1
  proof: by
  cases a
  cases b
  simp only [PNat.mk_coe, _root_.PNat.sub_coe, ← _root_.PNat.coe_lt_coe]
  split_ifs <;> lia

中文:
引理 sub_coe
  条件: (a b : P自然数)
  结论: ((a - b : P自然数) : 自然数) = a.val - 1 - b.val + 1
  证明: by
  cases a
  cases b
  simp only [PNat.mk_coe, _root_.PNat.sub_coe, ← _root_.PNat.coe_lt_coe]
  split_ifs <;> lia

Depends on / 依赖: PNat.mk_coe, _root_, _root_.PNat.coe_lt_coe, _root_.PNat.sub_coe, coe_lt_coe, mk_coe, split_ifs, sub_coe
-/
lemma sub_coe (a b : PNat) : ((a - b : PNat) : Nat) = a.val - 1 - b.val + 1 := by
  cases a
  cases b
  simp only [PNat.mk_coe, _root_.PNat.sub_coe, ← _root_.PNat.coe_lt_coe]
  split_ifs <;> lia

/-- `pnat_to_nat` shifts all `PNat`s in the context to `Nat`, rewriting propositions about them.
A typical use case is `pnat_to_nat; lia`. -/
macro "pnat_to_nat" : tactic => `(tactic| focus (
  pnat_positivity;
  simp only [pnat_to_nat_coe] at *)
)

end Mathlib.Tactic.PNatToNat
