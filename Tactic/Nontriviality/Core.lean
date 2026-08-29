/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro
-/
module

public meta import Qq.MetaM
public import Mathlib.Logic.Nontrivial.Basic -- shake: keep (tactic dependency)
public import Mathlib.Tactic.Attr.Register -- shake: keep (tactic dependency)
public meta import Lean.Elab.Tactic.Meta
public meta import Lean.Elab.Tactic.SolveByElim

/-! # The `nontriviality` tactic. -/

public meta section

universe u

namespace Mathlib.Tactic.Nontriviality
open Lean Elab Meta Tactic Qq

/--
theorem `subsingleton_or_nontrivial_elim` / 定理 `subsingleton_or_nontrivial_elim`

English:
theorem subsingleton_or_nontrivial_elim
  statement: {p : Prop} {α : Type u}
  proof: (subsingleton_or_nontrivial α).elim @h₁ @h₂

中文:
定理 subsingleton_or_nontrivial_elim
  结论: {p : 命题} {α : 类型u}
  证明: (subsingleton_or_nontrivial α).elim @h₁ @h₂

Depends on / 依赖: subsingleton_or_nontrivial
-/
theorem subsingleton_or_nontrivial_elim {p : Prop} {α : Type u}
    (h₁ : Subsingleton α -> p) (h₂ : Nontrivial α -> p) : p :=
  (subsingleton_or_nontrivial α).elim @h₁ @h₂

/--
Definition of `nontrivialityByElim` / `nontrivialityByElim` 的定义

English:
definition nontrivialityByElim
  signature: {u : Level} (α : Q(Type u)) (g : MVarId) (simpArgs : Array Syntax)
  body: do
  let p : Q(Prop) ← g.getType
  guard (← instantiateMVars (← inferType p)).isProp
  g.withContext do
    let g₁ ← mkFreshExprMVarQ q(Subsingleton $α -> $p)
    let (_, g₁') ← g₁.mvarId!.intro1
    g₁'.withContext try
      -- FIXME: restore after https://github.com/leanprover/lean4/issues/2054 is

中文:
定义 nontrivialityByElim
  签名: {u : Level} (α : Q(类型u)) (g : MVarId) (simpArgs : Array Syntax)
  定义体: do
  let p : Q(Prop) ← g.getType
  guard (← instantiateMVars (← inferType p)).isProp
  g.withContext do
    let g₁ ← mkFreshExprMVarQ q(Subsingleton $α -> $p)
    let (_, g₁') ← g₁.mvarId!.intro1
    g₁'.withContext try
      -- FIXME: restore after https://github.com/leanprover/lean4/issues/2054 is
-/
def nontrivialityByElim {u : Level} (α : Q(Type u)) (g : MVarId) (simpArgs : Array Syntax) :
    MetaM MVarId := do
  let p : Q(Prop) ← g.getType
  guard (← instantiateMVars (← inferType p)).isProp
  g.withContext do
    let g₁ ← mkFreshExprMVarQ q(Subsingleton $α -> $p)
    let (_, g₁') ← g₁.mvarId!.intro1
    g₁'.withContext try
      -- FIXME: restore after https://github.com/leanprover/lean4/issues/2054 is fixed
      -- g₁'.inferInstance <|> do
(do g₁'.assign (← synthInstance (← g₁'.getType))) > do
        let simpArgs := simpArgs.push (Unhygienic.run `(Parser.Tactic.simpLemma| nontriviality))
        let stx := open TSyntax.Compat in Unhygienic.run `(tactic| simp [$simpArgs,*])
        let ([], _) ← runTactic g₁' stx | failure
    catch _ => throwError
      "Could not prove goal assuming `{q(Subsingleton $α)}`\n{MessageData.ofGoal g₁'}"
    let g₂ : Q(Nontrivial $α -> $p) ← mkFreshExprMVarQ q(Nontrivial $α -> $p)
    g.assign q(subsingleton_or_nontrivial_elim $g₁ $g₂)
    pure g₂.mvarId!

open Lean.Elab.Tactic.SolveByElim in
/--
Definition of `nontrivialityByAssumption` / `nontrivialityByAssumption` 的定义

English:
definition nontrivialityByAssumption
  signature: (g : MVarId)
  body: do
g.inferInstance > do
    _ ← processSyntax {maxDepth := 6}
      false false [← `(nontrivial_of_ne), ← `(nontrivial_of_lt)] [] #[] [g]

中文:
定义 nontrivialityByAssumption
  签名: (g : MVarId)
  定义体: do
g.inferInstance > do
    _ ← processSyntax {maxDepth := 6}
      false false [← `(nontrivial_of_ne), ← `(nontrivial_of_lt)] [] #[] [g]
-/
def nontrivialityByAssumption (g : MVarId) : MetaM Unit := do
g.inferInstance > do
    _ ← processSyntax {maxDepth := 6}
      false false [← `(nontrivial_of_ne), ← `(nontrivial_of_lt)] [] #[] [g]

/-- `nontriviality α` generates a proof of `Nontrivial α` and adds this as a hypothesis.

The tactic first tries to find a proof of `Nontrivial α` using instance synthesis.
If this fails, it will derive this proof using `a < b`, `a ≠ b` or `a > b` hypotheses in the
local context. Otherwise it will perform a case split on `Subsingleton α ∨ Nontrivial α`, and
attempt to prove `Subsingleton α` implies the main goal using `simp [nontriviality]`.
If the `Subsingleton` goal cannot be closed automatically, `nontriviality` fails.

This tactic is extensible: tag a lemma with `@[nontriviality]` to use it in the `simp` set for the
`Subsingleton` case. All `@[simp]` lemmas are automatically used too.

* `nontriviality` (without the argument `α`) infers the type from the main goal,
  if the goal is an (in)equality.
* `nontriviality using h₁, h₂, ..., hₙ` uses `h₁`, ..., `hₙ` as extra arguments to `simp`
  in the `Subsingleton` case. This supports the typical `simp` argument syntax:
  `nontriviality using ← h` rewrites right-to-left with this argument;
  `nontriviality using -h` removes a lemma from the default `simp` set for this tactic invocation.
  `nontriviality using *` adds all local hypotheses to the `simp` set.

Examples:
```
example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : 0 < a := by
  nontriviality -- There is now a `Nontrivial R` hypothesis available.
  assumption

example {R : Type} [CommRing R] {r s : R} : r * s = s * r := by
  nontriviality -- There is now a `Nontrivial R` hypothesis available.
  apply mul_comm

example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : (2 : ℕ) ∣ 4 := by
  nontriviality R -- there is now a `Nontrivial R` hypothesis available.
  dec_trivial

def myeq {α : Type} (a b : α) : Prop := a = b

example {α : Type} (a b : α) (h : a = b) : myeq a b := by
  success_if_fail nontriviality α -- Fails
  nontriviality α using myeq -- There is now a `Nontrivial α` hypothesis available
  assumption
```
-/
syntax (name := nontriviality) "nontriviality" (ppSpace colGt term)?
  (" using " Parser.Tactic.simpArg,+)? : tactic

/--
Definition of `elabNontriviality` / `elabNontriviality` 的定义

English:
definition elabNontriviality
  signature: : Tactic
  body: fun stx => do
    let g ← getMainGoal
    let α ← match stx[1].getOptional? with
    | some e => Term.elabType e
    | none => (do
      let mut tgt ← withReducible g.getType'
      if let some tgt' := tgt.not? then tgt ← withReducible (whnf tgt')
      if let some (α, _) := tgt.eq? then return α
  

中文:
定义 elabNontriviality
  签名: : Tactic
  定义体: fun stx => do
    let g ← getMainGoal
    let α ← match stx[1].getOptional? with
    | some e => Term.elabType e
    | none => (do
      let mut tgt ← withReducible g.getType'
      if let some tgt' := tgt.not? then tgt ← withReducible (whnf tgt')
      if let some (α, _) := tgt.eq? then return α
  
-/
@[tactic nontriviality] def elabNontriviality : Tactic := fun stx => do
    let g ← getMainGoal
    let α ← match stx[1].getOptional? with
    | some e => Term.elabType e
    | none => (do
      let mut tgt ← withReducible g.getType'
      if let some tgt' := tgt.not? then tgt ← withReducible (whnf tgt')
      if let some (α, _) := tgt.eq? then return α
      if let some (α, _) := tgt.app4? ``LE.le then return α
      if let some (α, _) := tgt.app4? ``LT.lt then return α
      throwError "The goal is not an (in)equality, so you'll need to specify the desired \
        `Nontrivial α` instance by invoking `nontriviality α`.")
    let .sort u ← whnf (← inferType α) | unreachable!
    let some v := u.dec | throwError "not a type{indentExpr α}"
    let α : Q(Type v) := α
    let tac := do
      let ty := q(Nontrivial $α)
      let m ← mkFreshExprMVar (some ty)
      nontrivialityByAssumption m.mvarId!
      g.assert `inst ty m
let g ← liftM tac > nontrivialityByElim α g stx[2][1].getSepArgs
    replaceMainGoal [(← g.intro1).2]

end Nontriviality

end Mathlib.Tactic
