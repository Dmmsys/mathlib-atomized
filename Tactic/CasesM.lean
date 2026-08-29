/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.Conv.Pattern

/-!
# `casesm`, `cases_type`, `constructorm` tactics

These tactics implement repeated `cases` / `constructor` on anything satisfying a predicate.
-/

public meta section

namespace Lean.MVarId

/--
Definition of `casesMatching` / `casesMatching` 的定义

English:
definition casesMatching
  signature: (matcher : Expr -> MetaM Bool) (recursive := false) (allowSplit := true)
  body: do
  let result := (← go g).toList
  if throwOnNoMatch && result == [g] then
    throwError "no match"
  else
    return result

中文:
定义 casesMatching
  签名: (matcher : Expr -> MetaM 布尔值) (recursive := false) (allowSplit := true)
  定义体: do
  let result := (← go g).toList
  if throwOnNoMatch && result == [g] then
    throwError "no match"
  else
    return result
-/
partial def casesMatching (matcher : Expr -> MetaM Bool) (recursive := false) (allowSplit := true)
    (throwOnNoMatch := true) (g : MVarId) : MetaM (List MVarId) := do
  let result := (← go g).toList
  if throwOnNoMatch && result == [g] then
    throwError "no match"
  else
    return result
where
  /-- Auxiliary for `casesMatching`. Accumulates generated subgoals in `acc`. -/
  go (g : MVarId) (acc : Array MVarId := #[]) : MetaM (Array MVarId) :=
    g.withContext do
      for ldecl in ← getLCtx do
        if ldecl.isImplementationDetail then continue
        if ← matcher ldecl.type then
          let mut acc := acc
          let subgoals ← if allowSplit then
            g.cases ldecl.fvarId
          else
            let s ← saveState
            let subgoals ← g.cases ldecl.fvarId (givenNames := #[⟨true, [ldecl.userName]⟩])
            if subgoals.size > 1 then
              s.restore
              continue
            else
              pure subgoals
          for subgoal in subgoals do
            -- If only one new hypothesis is generated, rename it to the original name.
            let g ← match subgoal.fields with
            | #[.fvar fvarId] => subgoal.mvarId.rename fvarId ldecl.userName
            | _ => pure subgoal.mvarId
            if recursive then
              acc ← go g acc
            else
              acc := acc.push g
          return acc
      return (acc.push g)

/--
Definition of `casesType` / `casesType` 的定义

English:
definition casesType
  signature: (heads : Array Name) (recursive := false) (allowSplit := true)
  body: let matcher ty := pure
    if let .const n .. := ty.headBeta.getAppFn then heads.contains n else false
  casesMatching matcher recursive allowSplit

中文:
定义 casesType
  签名: (heads : 数组 Name) (recursive := false) (allowSplit := true)
  定义体: let matcher ty := pure
    if let .const n .. := ty.headBeta.getAppFn then heads.contains n else false
  casesMatching matcher recursive allowSplit

Depends on / 依赖: allowSplit
-/
def casesType (heads : Array Name) (recursive := false) (allowSplit := true) :
    MVarId -> MetaM (List MVarId) :=
let matcher ty := pure
    if let .const n .. := ty.headBeta.getAppFn then heads.contains n else false
  casesMatching matcher recursive allowSplit

end Lean.MVarId

namespace Mathlib.Tactic
open Lean Meta Elab Tactic MVarId

/--
Definition of `elabPatterns` / `elabPatterns` 的定义

English:
definition elabPatterns
  signature: (pats : Array Term)
  body: withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true })
Term.withoutErrToSorry
  pats.mapM fun p => Term.withoutModifyingElabMetaStateWithInfo do
withRef p abstractMVars (← Term.elabTerm p none)

中文:
定义 elabPatterns
  签名: (pats : 数组 项)
  定义体: withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true })
Term.withoutErrToSorry
  pats.mapM fun p => Term.withoutModifyingElabMetaStateWithInfo do
withRef p abstractMVars (← Term.elabTerm p none)

Depends on / 依赖: Context, Term.Context, Term.elabTerm, Term.withoutErrToSorry, Term.withoutModifyingElabMetaStateWithInfo, abstractMVars, elabTerm, ignoreTCFailures, pats.mapM, withRef, withTheReader, withoutErrToSorry, withoutModifyingElabMetaStateWithInfo
-/
def elabPatterns (pats : Array Term) : TermElabM (Array AbstractMVarsResult) :=
withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true })
Term.withoutErrToSorry
  pats.mapM fun p => Term.withoutModifyingElabMetaStateWithInfo do
withRef p abstractMVars (← Term.elabTerm p none)

/--
Definition of `matchPatterns` / `matchPatterns` 的定义

English:
definition matchPatterns
  signature: (pats : Array AbstractMVarsResult) (e : Expr)
  body: do
  let e ← instantiateMVars e
  pats.anyM fun p => return (← Conv.matchPattern? p e) matches some (_, #[])

中文:
定义 matchPatterns
  签名: (pats : 数组 AbstractMVarsResult) (e : Expr)
  定义体: do
  let e ← instantiateMVars e
  pats.anyM fun p => return (← Conv.matchPattern? p e) matches some (_, #[])
-/
def matchPatterns (pats : Array AbstractMVarsResult) (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  pats.anyM fun p => return (← Conv.matchPattern? p e) matches some (_, #[])

/--
Definition of `elabCasesM` / `elabCasesM` 的定义

English:
definition elabCasesM
  signature: (pats : Array Term) (recursive allowSplit : Bool)
  body: do
  let pats ← elabPatterns pats
  liftMetaTactic (casesMatching (matchPatterns pats) recursive allowSplit)

中文:
定义 elabCasesM
  签名: (pats : 数组 项) (recursive allowSplit : 布尔值)
  定义体: do
  let pats ← elabPatterns pats
  liftMetaTactic (casesMatching (matchPatterns pats) recursive allowSplit)
-/
def elabCasesM (pats : Array Term) (recursive allowSplit : Bool) : TacticM Unit := do
  let pats ← elabPatterns pats
  liftMetaTactic (casesMatching (matchPatterns pats) recursive allowSplit)

/--
`casesm p` searches for the first hypothesis `h : type` where `type` matches the term `p`,
and splits the main goal by cases on `h`. Use holes in `p` to indicate arbitrary subexpressions,
for example `casesm _ ∧ _` will match any conjunction. `casesm p` fails if no hypothesis type
matches `p`.

* `casesm p_1, ..., p_n` searches for a hypothesis `h : type` where `type` matches one or more of
  the given patterns `p_1`, ... `p_n`, and splits the main goal by cases on `h`.
* `casesm* p` repeatedly performs case splits until no more hypothesis type matches `p`.
  This is a more efficient and compact version of `· repeat casesm p`.
  It is more efficient because the pattern is compiled once.
* `casesm! p` and `casesm!* p` skip a hypothesis if the main goal would be replaced with two or more
  subgoals.

Example:
```
example (h : a ∧ b ∨ c ∧ d) (h2 : e ∧ f) : True := by
  -- The following tactic destructs all conjunctions and disjunctions in the current context.
  casesm* _∨_, _∧_
  · clear ‹a› ‹b› ‹e› ‹f›; (fail_if_success clear ‹c›); trivial
  · clear ‹c› ‹d› ‹e› ‹f›; trivial
```
-/
elab (name := casesM) "casesm" recursive:"*"? ppSpace pats:term,+ : tactic => do
  elabCasesM pats recursive.isSome true

@[tactic_alt casesM]
elab (name := casesm!) "casesm!" recursive:"*"? ppSpace pats:term,+ : tactic => do
  elabCasesM pats recursive.isSome false

/--
Definition of `elabCasesType` / `elabCasesType` 的定义

English:
definition elabCasesType
  signature: (heads : Array Ident)
  body: do
  let heads ← heads.mapM (fun stx => realizeGlobalConstNoOverloadWithInfo stx)
  liftMetaTactic (casesType heads recursive allowSplit)

中文:
定义 elabCasesType
  签名: (heads : 数组 Ident)
  定义体: do
  let heads ← heads.mapM (fun stx => realizeGlobalConstNoOverloadWithInfo stx)
  liftMetaTactic (casesType heads recursive allowSplit)

Depends on / 依赖: TacticM, allowSplit
-/
def elabCasesType (heads : Array Ident)
    (recursive := false) (allowSplit := true) : TacticM Unit := do
  let heads ← heads.mapM (fun stx => realizeGlobalConstNoOverloadWithInfo stx)
  liftMetaTactic (casesType heads recursive allowSplit)

/--
`cases_type I` searches for a hypothesis `h : type` where `I` has the form `(I ...)`, and splits the
main goal by cases on `h`. `cases_type p` fails if no hypothesis type has the identifier `I` as its
head symbol.

* `cases_type I_1 ... I_n` searches for a hypothesis `h : type` where `type` has one or more of
  `I_1`, ..., `I_n` as its head symbol, and splits the main goal by cases on `h`.
* `cases_type* I` repeatedly performs case splits until no more hypothesis type has `I` as its head
  symbol. This shorthand for `· repeat cases_type I`.
* `cases_type! p` and `cases_type!* p` skip a hypothesis if the main goal would be replaced with two
  or more subgoals.

Example:
```
example (h : a ∧ b ∨ c ∧ d) (h2 : e ∧ f) : True := by
  -- The following tactic destructs all conjunctions and disjunctions in the current context.
  cases_type* Or And
  · clear ‹a› ‹b› ‹e› ‹f›; (fail_if_success clear ‹c›); trivial
  · clear ‹c› ‹d› ‹e› ‹f›; trivial
```
-/
elab (name := casesType) "cases_type" recursive:"*"? heads:(ppSpace colGt ident)+ : tactic =>
  elabCasesType heads recursive.isSome true

@[tactic_alt casesType]
elab (name := casesType!) "cases_type!" recursive:"*"? heads:(ppSpace colGt ident)+ : tactic =>
  elabCasesType heads recursive.isSome false

/--
Definition of `constructorMatching` / `constructorMatching` 的定义

English:
definition constructorMatching
  signature: (g : MVarId) (matcher : Expr -> MetaM Bool)
  body: do
  let result ←
    (if recursive then (do
      let result ← go g
      pure result.toList)
     else
      (g.withContext do
          if ← matcher (← g.getType) then g.constructor else pure [g]))
  if throwOnNoMatch && [g] == result then
    throwError "no match"
  else
    return result

中文:
定义 constructorMatching
  签名: (g : MVarId) (matcher : Expr -> MetaM 布尔值)
  定义体: do
  let result ←
    (if recursive then (do
      let result ← go g
      pure result.toList)
     else
      (g.withContext do
          if ← matcher (← g.getType) then g.constructor else pure [g]))
  if throwOnNoMatch && [g] == result then
    throwError "no match"
  else
    return result
-/
partial def constructorMatching (g : MVarId) (matcher : Expr -> MetaM Bool)
    (recursive := false) (throwOnNoMatch := true) : MetaM (List MVarId) := do
  let result ←
    (if recursive then (do
      let result ← go g
      pure result.toList)
     else
      (g.withContext do
          if ← matcher (← g.getType) then g.constructor else pure [g]))
  if throwOnNoMatch && [g] == result then
    throwError "no match"
  else
    return result
where
  /-- Auxiliary for `constructorMatching`. Accumulates generated subgoals in `acc`. -/
  go (g : MVarId) (acc : Array MVarId := #[]) : MetaM (Array MVarId) :=
    g.withContext do
      if ← matcher (← g.getType) then
        let mut acc := acc
        for g' in ← g.constructor do
          acc ← go g' acc
        return acc
      return (acc.push g)

/--
`constructorm p_1, ..., p_n`, where the main goal has type `type`, applies the first matching
constructor for `type`, if `type` matches one of the given patterns. If `type` does not match any
of the patterns, `constructorm` fails.

* `constructorm* p_1, ..., p_n` repeatedly applies a constructor until the goal no longer matches
  `p_1`, ..., `p_n`. This is a more efficient and compact version of
  `· repeat constructorm p_1, ..., p_n`. It is more efficient because the pattern is compiled once.

Examples:
```
example : True ∧ (True ∨ True) := by
  constructorm* _ ∨ _, _ ∧ _, True
```
-/
elab (name := constructorM) "constructorm" recursive:"*"? ppSpace pats:term,+ : tactic => do
  let pats ← elabPatterns pats.getElems
  liftMetaTactic (constructorMatching · (matchPatterns pats) recursive.isSome)

end Mathlib.Tactic
