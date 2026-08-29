/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Simon Hudon, Thomas Murrills, Mario Carneiro
-/
module

public meta import Qq
public meta import Mathlib.Util.AtomM
public import Mathlib.Data.List.TFAE -- shake: keep (dependency of Qq output)
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ExtendDoc
public import Mathlib.Util.AtomM

/-!
# The Following Are Equivalent (TFAE)

This file provides the tactics `tfae_have` and `tfae_finish` for proving goals of the form
`TFAE [P₁, P₂, ...]`.
-/

public meta section

namespace Mathlib.Tactic.TFAE

/-! ### Parsing and syntax

We implement `tfae_have` in terms of a syntactic `have`. To support as much of the same syntax as
possible, we recreate the parsers for `have`, except with the changes necessary for `tfae_have`.
-/

open Lean.Parser Term

namespace Parser

-- An arrow of the form `←`, `→`, or `↔`.
/--
Definition of `impTo` / `impTo` 的定义

English:
definition impTo
  signature: : Parser
  body: leading_parser unicodeSymbol " -> " " -> "

中文:
定义 impTo
  签名: : Parser
  定义体: leading_parser unicodeSymbol " -> " " -> "

Depends on / 依赖: leading_parser, unicodeSymbol
-/
def impTo : Parser := leading_parser unicodeSymbol " -> " " -> "
/--
Definition of `impFrom` / `impFrom` 的定义

English:
definition impFrom
  signature: : Parser
  body: leading_parser unicodeSymbol " ← " " <- "

中文:
定义 impFrom
  签名: : Parser
  定义体: leading_parser unicodeSymbol " ← " " <- "

Depends on / 依赖: leading_parser, unicodeSymbol
-/
def impFrom : Parser := leading_parser unicodeSymbol " ← " " <- "
/--
Definition of `impIff` / `impIff` 的定义

English:
definition impIff
  signature: : Parser
  body: leading_parser unicodeSymbol " ↔ " " <-> "

中文:
定义 impIff
  签名: : Parser
  定义体: leading_parser unicodeSymbol " ↔ " " <-> "

Depends on / 依赖: leading_parser, unicodeSymbol
-/
def impIff : Parser := leading_parser unicodeSymbol " ↔ " " <-> "
/--
Definition of `impArrow` / `impArrow` 的定义

English:
definition impArrow
  signature: : Parser
  body: leading_parser impTo > impFrom > impIff

中文:
定义 impArrow
  签名: : Parser
  定义体: leading_parser impTo > impFrom > impIff

Depends on / 依赖: impFrom, impIff, leading_parser
-/
def impArrow : Parser := leading_parser impTo > impFrom > impIff

attribute [nolint docBlame] impTo impFrom impIff impArrow

/--
Definition of `tfaeType` / `tfaeType` 的定义

English:
definition tfaeType
  body: leading_parser num >> impArrow >> num

中文:
定义 tfaeType
  定义体: leading_parser num >> impArrow >> num

Depends on / 依赖: impArrow, leading_parser
-/
def tfaeType := leading_parser num >> impArrow >> num

/-!
The following parsers are similar to those for `have` in `Lean.Parser.Term`, but
instead of `optType`, we use `tfaeType := num >> impArrow >> num` (as a `tfae_have` invocation must
always include this specification). Also, we disallow including extra binders, as that makes no
sense in this context; we also include `" : "` after the binder to avoid breaking `tfae_have 1 → 2`
syntax (which, unlike `have`, omits `" : "`).
-/

/--
Definition of `binder` / `binder` 的定义

English:
definition binder
  body: leading_parser ppSpace >> binderIdent >> " : "

中文:
定义 binder
  定义体: leading_parser ppSpace >> binderIdent >> " : "

Depends on / 依赖: binderIdent, leading_parser, ppSpace
-/
def binder := leading_parser ppSpace >> binderIdent >> " : "
/--
Definition of `tfaeHaveIdLhs` / `tfaeHaveIdLhs` 的定义

English:
definition tfaeHaveIdLhs
  body: leading_parser
  (binder <|> hygieneInfo) >> tfaeType

中文:
定义 tfaeHaveIdLhs
  定义体: leading_parser
  (binder <|> hygieneInfo) >> tfaeType

Depends on / 依赖: leading_parser
-/
def tfaeHaveIdLhs := leading_parser
  (binder <|> hygieneInfo) >> tfaeType
/--
Definition of `tfaeHaveIdDecl` / `tfaeHaveIdDecl` 的定义

English:
definition tfaeHaveIdDecl
  body: leading_parser (withAnonymousAntiquot := false)
  atomic (tfaeHaveIdLhs >> " := ") >> termParser

中文:
定义 tfaeHaveIdDecl
  定义体: leading_parser (withAnonymousAntiquot := false)
  atomic (tfaeHaveIdLhs >> " := ") >> termParser

Depends on / 依赖: leading_parser, withAnonymousAntiquot
-/
def tfaeHaveIdDecl := leading_parser (withAnonymousAntiquot := false)
  atomic (tfaeHaveIdLhs >> " := ") >> termParser
/--
Definition of `tfaeHaveEqnsDecl` / `tfaeHaveEqnsDecl` 的定义

English:
definition tfaeHaveEqnsDecl
  body: leading_parser (withAnonymousAntiquot := false)
  tfaeHaveIdLhs >> matchAlts

中文:
定义 tfaeHaveEqnsDecl
  定义体: leading_parser (withAnonymousAntiquot := false)
  tfaeHaveIdLhs >> matchAlts

Depends on / 依赖: leading_parser, withAnonymousAntiquot
-/
def tfaeHaveEqnsDecl := leading_parser (withAnonymousAntiquot := false)
  tfaeHaveIdLhs >> matchAlts
/--
Definition of `tfaeHavePatDecl` / `tfaeHavePatDecl` 的定义

English:
definition tfaeHavePatDecl
  body: leading_parser (withAnonymousAntiquot := false)
  atomic (termParser >> pushNone >> " : " >> tfaeType >> " := ") >> termParser

中文:
定义 tfaeHavePatDecl
  定义体: leading_parser (withAnonymousAntiquot := false)
  atomic (termParser >> pushNone >> " : " >> tfaeType >> " := ") >> termParser

Depends on / 依赖: leading_parser, withAnonymousAntiquot
-/
def tfaeHavePatDecl := leading_parser (withAnonymousAntiquot := false)
  atomic (termParser >> pushNone >> " : " >> tfaeType >> " := ") >> termParser
/--
Definition of `tfaeHaveDecl` / `tfaeHaveDecl` 的定义

English:
definition tfaeHaveDecl
  body: leading_parser (withAnonymousAntiquot := false)
tfaeHaveIdDecl > (ppSpace >> tfaeHavePatDecl) > tfaeHaveEqnsDecl

中文:
定义 tfaeHaveDecl
  定义体: leading_parser (withAnonymousAntiquot := false)
tfaeHaveIdDecl > (ppSpace >> tfaeHavePatDecl) > tfaeHaveEqnsDecl

Depends on / 依赖: leading_parser, withAnonymousAntiquot
-/
def tfaeHaveDecl := leading_parser (withAnonymousAntiquot := false)
tfaeHaveIdDecl > (ppSpace >> tfaeHavePatDecl) > tfaeHaveEqnsDecl

-- Don't put doc-strings on these parsers in order to not override hover doc-strings.
attribute [nolint docBlame] binder
  tfaeHaveIdLhs tfaeHaveIdDecl tfaeHaveEqnsDecl tfaeHavePatDecl tfaeHaveDecl

end Parser

open Parser

/--
`tfae_have i → j := t`, where the goal is `TFAE [P₁, P₂, ...]` introduces a hypothesis
`tfae_i_to_j : Pᵢ → Pⱼ` and proof `t` to the local context. Note that `i` and `j` are
natural number literals (beginning at 1) used as indices to specify the propositions
`P₁, P₂, ...` that appear in the goal.

Once sufficient hypotheses have been introduced by `tfae_have`, `tfae_finish` can be used to close
the goal.

All features of `have` are supported by `tfae_have`, including naming, matching,
destructuring, and goal creation.

* `tfae_have i ← j := t` adds a hypothesis in the reverse direction, of type `Pⱼ → Pᵢ`.
* `tfae_have i ↔ j := t` adds a hypothesis in the both directions, of type `Pᵢ ↔ Pⱼ`.
* `tfae_have hij : i → j := t` names the introduced hypothesis `hij` instead of `tfae_i_to_j`.
* `tfae_have i j | p₁ => t₁ | ...` matches on the assumption `p : Pᵢ`.
* `tfae_have ⟨hij, hji⟩ : i ↔ j := t` destructures the bi-implication into `hij : Pᵢ → Pⱼ`
  and `hji : Pⱼ → Pⱼ`.
* `tfae_have i → j := t ?a` creates a new goal for `?a`.

Examples:
```lean4
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have 1 → 3 := h
  -- The resulting context now includes `tfae_1_to_3 : P → R`.
  sorry
```

```lean4
-- An example of `tfae_have` and `tfae_finish`:
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- proof of P → Q -/
  tfae_have 2 -> 1 := sorry /- proof of Q → P -/
  tfae_have 2 ↔ 3 := sorry /- proof of Q ↔ R -/
  tfae_finish
```

```lean4
-- All features of `have` are supported by `tfae_have`:
example : TFAE [P, Q] := by
  -- assert `tfae_1_to_2 : P → Q`:
  tfae_have 1 -> 2 := sorry

  -- assert `hpq : P → Q`:
  tfae_have hpq : 1 -> 2 := sorry

  -- match on `p : P` and prove `Q` via `f p`:
  tfae_have 1 -> 2
  | p => f p

  -- assert `pq : P → Q`, `qp : Q → P`:
  tfae_have ⟨pq, qp⟩ : 1 ↔ 2 := sorry

  -- assert `h : P → Q`; `?a` is a new goal:
  tfae_have h : 1 -> 2 := f ?a

  sorry
```
-/
syntax (name := tfaeHave) "tfae_have " tfaeHaveDecl : tactic

/--
`tfae_finish` closes goals of the form `TFAE [P₁, P₂, ...]` once a sufficient collection
of hypotheses of the form `Pᵢ → Pⱼ` or `Pᵢ ↔ Pⱼ` have been introduced to the local context.

`tfae_have` can be used to conveniently introduce these hypotheses; see `tfae_have`.

Example:
```lean4
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- proof of P → Q -/
  tfae_have 2 -> 1 := sorry /- proof of Q → P -/
  tfae_have 2 ↔ 3 := sorry /- proof of Q ↔ R -/
  tfae_finish
```
-/
syntax (name := tfaeFinish) "tfae_finish" : tactic


/-! ### Setup -/

open List Lean Meta Expr Elab Tactic Mathlib.Tactic Qq

/--
Definition of `getTFAEList` / `getTFAEList` 的定义

English:
definition getTFAEList
  signature: (t : Expr)
  body: do
let .app tfae (l : Q(List Prop)) ← whnfR ← instantiateMVars t
    | throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  unless (← withNewMCtxDepth <| isDefEq tfae q(TFAE)) do
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  return (l, ← getExplicitList l)

中文:
定义 getTFAEList
  签名: (t : Expr)
  定义体: do
let .app tfae (l : Q(List Prop)) ← whnfR ← instantiateMVars t
    | throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  unless (← withNewMCtxDepth <| isDefEq tfae q(TFAE)) do
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  return (l, ← getExplicitList l)
-/
partial def getTFAEList (t : Expr) : MetaM (Q(List Prop) × List Q(Prop)) := do
let .app tfae (l : Q(List Prop)) ← whnfR ← instantiateMVars t
    | throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  unless (← withNewMCtxDepth <| isDefEq tfae q(TFAE)) do
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  return (l, ← getExplicitList l)
where
  /-- Convert an expression representing an explicit list into a list of expressions. -/
  getExplicitList (l : Q(List Prop)) : MetaM (List Q(Prop)) := do
    match l with
    | ~q([]) => return ([] : List Expr)
    | ~q($a :: $l') => return (a :: (← getExplicitList l'))
    | e => throwError "{e} must be an explicit list of propositions"

/-! ### Proof construction -/

variable (hyps : Array (Nat × Nat × Expr)) (atoms : Array Q(Prop))

/--
Definition of `dfs` / `dfs` 的定义

English:
definition dfs
  signature: (i j : Nat) (P P' : Q(Prop)) (hP : Q($P))
  body: do
  if i == j then
    return hP
  modify (·.insert i)
  for (a, b, h) in hyps do
    if i == a then
      if !(← get).contains b then
        have Q := atoms[b]!
        have h : Q($P -> $Q) := h
        try return ← dfs b j Q P' q($h $hP) catch _ => pure ()
  failure

中文:
定义 dfs
  签名: (i j : 自然数) (P P' : Q(命题)) (hP : Q($P))
  定义体: do
  if i == j then
    return hP
  modify (·.insert i)
  for (a, b, h) in hyps do
    if i == a then
      if !(← get).contains b then
        have Q := atoms[b]!
        have h : Q($P -> $Q) := h
        try return ← dfs b j Q P' q($h $hP) catch _ => pure ()
  failure
-/
partial def dfs (i j : Nat) (P P' : Q(Prop)) (hP : Q($P)) : StateT (Std.HashSet Nat) MetaM Q($P') := do
  if i == j then
    return hP
  modify (·.insert i)
  for (a, b, h) in hyps do
    if i == a then
      if !(← get).contains b then
        have Q := atoms[b]!
        have h : Q($P -> $Q) := h
        try return ← dfs b j Q P' q($h $hP) catch _ => pure ()
  failure

/--
Definition of `proveImpl` / `proveImpl` 的定义

English:
definition proveImpl
  signature: (i j : Nat) (P P' : Q(Prop))
  body: do
  try
    withLocalDeclD (← mkFreshUserName `h) P fun (h : Q($P)) => do
mkLambdaFVars #[h] .run' {} ← dfs hyps atoms i j P P' h
  catch _ =>
    throwError "couldn't prove {P} -> {P'}"

中文:
定义 proveImpl
  签名: (i j : 自然数) (P P' : Q(命题))
  定义体: do
  try
    withLocalDeclD (← mkFreshUserName `h) P fun (h : Q($P)) => do
mkLambdaFVars #[h] .run' {} ← dfs hyps atoms i j P P' h
  catch _ =>
    throwError "couldn't prove {P} -> {P'}"
-/
def proveImpl (i j : Nat) (P P' : Q(Prop)) : MetaM Q($P -> $P') := do
  try
    withLocalDeclD (← mkFreshUserName `h) P fun (h : Q($P)) => do
mkLambdaFVars #[h] .run' {} ← dfs hyps atoms i j P P' h
  catch _ =>
    throwError "couldn't prove {P} -> {P'}"

/--
Definition of `proveChain` / `proveChain` 的定义

English:
definition proveChain
  signature: (i : Nat) (is : List Nat) (P : Q(Prop)) (l : Q(List Prop))
  body: do
  match l with
  | ~q([]) => return q(.singleton _)
  | ~q($P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i' :: is' := id is | unreachable!
    have cl' : Q(IsChain (· -> ·) ($P' :: $l')) := ← proveChain i' is' q($P') q($l')
    let p ← proveImpl hyps atoms i i' P P'
    return q(.cons_cons $p $cl')

中文:
定义 proveChain
  签名: (i : 自然数) (is : 列表 自然数) (P : Q(命题)) (l : Q(列表 命题))
  定义体: do
  match l with
  | ~q([]) => return q(.singleton _)
  | ~q($P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i' :: is' := id is | unreachable!
    have cl' : Q(IsChain (· -> ·) ($P' :: $l')) := ← proveChain i' is' q($P') q($l')
    let p ← proveImpl hyps atoms i i' P P'
    return q(.cons_cons $p $cl')
-/
partial def proveChain (i : Nat) (is : List Nat) (P : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(IsChain (· -> ·) ($P :: $l)) := do
  match l with
  | ~q([]) => return q(.singleton _)
  | ~q($P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i' :: is' := id is | unreachable!
    have cl' : Q(IsChain (· -> ·) ($P' :: $l')) := ← proveChain i' is' q($P') q($l')
    let p ← proveImpl hyps atoms i i' P P'
    return q(.cons_cons $p $cl')

/--
Definition of `proveGetLastDImpl` / `proveGetLastDImpl` 的定义

English:
definition proveGetLastDImpl
  signature: (i i' : Nat) (is : List Nat) (P P' : Q(Prop)) (l : Q(List Prop))
  body: do
  match l with
  | ~q([]) => proveImpl hyps atoms i' i P' P
  | ~q($P'' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i'' :: is' := id is | unreachable!
    proveGetLastDImpl i i'' is' P P'' l'

中文:
定义 proveGetLastDImpl
  签名: (i i' : 自然数) (is : 列表 自然数) (P P' : Q(命题)) (l : Q(列表 命题))
  定义体: do
  match l with
  | ~q([]) => proveImpl hyps atoms i' i P' P
  | ~q($P'' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i'' :: is' := id is | unreachable!
    proveGetLastDImpl i i'' is' P P'' l'
-/
partial def proveGetLastDImpl (i i' : Nat) (is : List Nat) (P P' : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(getLastD $l $P' -> $P) := do
  match l with
  | ~q([]) => proveImpl hyps atoms i' i P' P
  | ~q($P'' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i'' :: is' := id is | unreachable!
    proveGetLastDImpl i i'' is' P P'' l'

/--
Definition of `proveTFAE` / `proveTFAE` 的定义

English:
definition proveTFAE
  signature: (is : List Nat) (l : Q(List Prop))
  body: do
  match l with
  | ~q([]) => return q(tfae_nil)
  | ~q([$P]) => return q(tfae_singleton $P)
  | ~q($P :: $P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i :: i' :: is' := id is | unreachable!
    let c ← proveChain hyps atoms i (i'::is') P q($P' :: $l')
    let il ← proveGetLastDImpl hyps atoms i i' is' P P' l'
    return q(tfae_of_cycle $c $il)

中文:
定义 proveTFAE
  签名: (is : 列表 自然数) (l : Q(列表 命题))
  定义体: do
  match l with
  | ~q([]) => return q(tfae_nil)
  | ~q([$P]) => return q(tfae_singleton $P)
  | ~q($P :: $P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i :: i' :: is' := id is | unreachable!
    let c ← proveChain hyps atoms i (i'::is') P q($P' :: $l')
    let il ← proveGetLastDImpl hyps atoms i i' is' P P' l'
    return q(tfae_of_cycle $c $il)
-/
def proveTFAE (is : List Nat) (l : Q(List Prop)) : MetaM Q(TFAE $l) := do
  match l with
  | ~q([]) => return q(tfae_nil)
  | ~q([$P]) => return q(tfae_singleton $P)
  | ~q($P :: $P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i :: i' :: is' := id is | unreachable!
    let c ← proveChain hyps atoms i (i'::is') P q($P' :: $l')
    let il ← proveGetLastDImpl hyps atoms i i' is' P P' l'
    return q(tfae_of_cycle $c $il)

/-! ### `tfae_have` components -/

/--
Definition of `mkTFAEId` / `mkTFAEId` 的定义

English:
definition mkTFAEId
  signature: : TSyntax ``tfaeType -> MacroM Name

中文:
定义 mkTFAEId
  签名: : TSyntax ``tfaeType -> MacroM Name
-/
def mkTFAEId : TSyntax ``tfaeType -> MacroM Name
  | `(tfaeType|$i:num $arr:impArrow $j:num) => do
    let arr ← match arr with
    | `(impArrow| ← ) => pure "from"
    | `(impArrow| -> ) => pure "to"
    | `(impArrow| ↔ ) => pure "iff"
    | _ => Macro.throwUnsupported
return .mkSimple String.intercalate "_" ["tfae", s!"{i.getNat}", arr, s!"{j.getNat}"]
  | _ => Macro.throwUnsupported

/--
Definition of `elabIndex` / `elabIndex` 的定义

English:
definition elabIndex
  signature: (i : TSyntax `num) (maxIndex : Nat)
  body: do
  let i' := i.getNat
  unless 1 <= i' && i' <= maxIndex do
    throwErrorAt i "{i} must be between 1 and {maxIndex}"
  return i'

中文:
定义 elabIndex
  签名: (i : TSyntax `num) (maxIndex : 自然数)
  定义体: do
  let i' := i.getNat
  unless 1 <= i' && i' <= maxIndex do
    throwErrorAt i "{i} must be between 1 and {maxIndex}"
  return i'
-/
def elabIndex (i : TSyntax `num) (maxIndex : Nat) : MetaM Nat := do
  let i' := i.getNat
  unless 1 <= i' && i' <= maxIndex do
    throwErrorAt i "{i} must be between 1 and {maxIndex}"
  return i'

/-! ### Tactic implementation -/

/--
Definition of `elabTFAEType` / `elabTFAEType` 的定义

English:
definition elabTFAEType
  signature: (tfaeList : List Q(Prop))
  body: tfaeList.length
    let i' ← elabIndex i l
    let j' ← elabIndex j l
    let Pi := tfaeList[i'-1]!
    let Pj := tfaeList[j'-1]!
    /- TODO: this is a hack to show the types `Pi`, `Pj` on hover. See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Pre-RFC.3A.20Forcing.20terms.20to.20be.20shown.20in.20hover.3F). -/
    Term.addTermInfo' i q(sorry : $Pi) Pi
    Term.addTermInfo' j q(sorry : $Pj) Pj
    let (ty : Q(Prop)) ← match arr with
      | `(impArrow| ← ) => pure q($Pj -> $Pi)
      | `(impArrow| -> ) => pure q($Pi -> $Pj)
      | `(impArrow| ↔ ) => pure q($Pi ↔ $Pj)
      | _ => throwUnsupportedSyntax
    Term.addTermInfo' stx q(sorry : $ty) ty
    return ty
  | _ => throwUnsupportedSyntax

中文:
定义 elabTFAEType
  签名: (tfaeList : 列表 Q(命题))
  定义体: tfaeList.length
    let i' ← elabIndex i l
    let j' ← elabIndex j l
    let Pi := tfaeList[i'-1]!
    let Pj := tfaeList[j'-1]!
    /- TODO: this is a hack to show the types `Pi`, `Pj` on hover. See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Pre-RFC.3A.20Forcing.20terms.20to.20be.20shown.20in.20hover.3F). -/
    Term.addTermInfo' i q(sorry : $Pi) Pi
    Term.addTermInfo' j q(sorry : $Pj) Pj
    let (ty : Q(Prop)) ← match arr with
      | `(impArrow| ← ) => pure q($Pj -> $Pi)
      | `(impArrow| -> ) => pure q($Pi -> $Pj)
      | `(impArrow| ↔ ) => pure q($Pi ↔ $Pj)
      | _ => throwUnsupportedSyntax
    Term.addTermInfo' stx q(sorry : $ty) ty
    return ty
  | _ => throwUnsupportedSyntax

Depends on / 依赖: length, tfaeList, tfaeList.length
-/
def elabTFAEType (tfaeList : List Q(Prop)) : TSyntax ``tfaeType -> TermElabM Expr
  | stx@`(tfaeType|$i:num $arr:impArrow $j:num) => do
    let l := tfaeList.length
    let i' ← elabIndex i l
    let j' ← elabIndex j l
    let Pi := tfaeList[i'-1]!
    let Pj := tfaeList[j'-1]!
    /- TODO: this is a hack to show the types `Pi`, `Pj` on hover. See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Pre-RFC.3A.20Forcing.20terms.20to.20be.20shown.20in.20hover.3F). -/
    Term.addTermInfo' i q(sorry : $Pi) Pi
    Term.addTermInfo' j q(sorry : $Pj) Pj
    let (ty : Q(Prop)) ← match arr with
      | `(impArrow| ← ) => pure q($Pj -> $Pi)
      | `(impArrow| -> ) => pure q($Pi -> $Pj)
      | `(impArrow| ↔ ) => pure q($Pi ↔ $Pj)
      | _ => throwUnsupportedSyntax
    Term.addTermInfo' stx q(sorry : $ty) ty
    return ty
  | _ => throwUnsupportedSyntax

/- Convert `tfae_have i <arr> j ...` to `tfae_have tfae_i_arr_j : i <arr> j ...`. See
`expandHave`, which is responsible for inserting `this` in `have : A := ...`. -/
macro_rules
| `(tfaeHave|tfae_have $hy:hygieneInfo $t:tfaeType := $val) => do
  let id := HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true)
  `(tfaeHave|tfae_have $id : $t := $val)
| `(tfaeHave|tfae_have $hy:hygieneInfo $t:tfaeType $alts:matchAlts) => do
  let id := HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true)
  `(tfaeHave|tfae_have $id : $t $alts)

open Term

elab_rules : tactic
| `(tfaeHave|tfae_have $d:tfaeHaveDecl) => withMainContext do
  let goal ← getMainGoal
  let (_, tfaeList) ← getTFAEList (← goal.getType)
  withRef d do
    match d with
    | `(tfaeHaveDecl| $b : $t:tfaeType := $pf:term) =>
      let type ← elabTFAEType tfaeList t
evalTactic ← `(tactic|have $b : $(← exprToSyntax type) := $pf)
    | `(tfaeHaveDecl| $b : $t:tfaeType $alts:matchAlts) =>
      let type ← elabTFAEType tfaeList t
evalTactic ← `(tactic|have $b : $(← exprToSyntax type) $alts:matchAlts)
    | `(tfaeHaveDecl| $pat:term : $t:tfaeType := $pf:term) =>
      let type ← elabTFAEType tfaeList t
evalTactic ← `(tactic|have $pat:term : $(← exprToSyntax type) := $pf)
    | _ => throwUnsupportedSyntax

elab_rules : tactic
| `(tactic| tfae_finish) => do
  let goal ← getMainGoal
  goal.withContext do
    let (tfaeListQ, tfaeList) ← getTFAEList (← goal.getType)
closeMainGoal `tfae_finish ← AtomM.run .reducible do
      let is ← tfaeList.mapM (fun e => Prod.fst <$> AtomM.addAtom e)
      let mut hyps := #[]
      for hyp in ← getLocalHyps do
let ty ← whnfR ← instantiateMVars ← inferType hyp
        if let (``Iff, #[p1, p2]) := ty.getAppFnArgs then
          let (q1, _) ← AtomM.addAtom p1
          let (q2, _) ← AtomM.addAtom p2
          hyps := hyps.push (q1, q2, ← mkAppM ``Iff.mp #[hyp])
          hyps := hyps.push (q2, q1, ← mkAppM ``Iff.mpr #[hyp])
        else if ty.isArrow then
          let (q1, _) ← AtomM.addAtom ty.bindingDomain!
          let (q2, _) ← AtomM.addAtom ty.bindingBody!
          hyps := hyps.push (q1, q2, hyp)
      proveTFAE hyps (← get).atoms is tfaeListQ

end Mathlib.Tactic.TFAE

/-!

### Deprecated "Goal-style" `tfae_have`

This syntax and its implementation, which behaves like "Mathlib `have`" is deprecated; we preserve
it here to provide graceful deprecation behavior.

-/

/-- Re-enables "goal-style" syntax for `tfae_have` when `true`. -/
register_option Mathlib.Tactic.TFAE.useDeprecated : Bool := {
  descr := "Re-enable \"goal-style\" 'tfae_have' syntax"
  defValue := false
}

namespace Mathlib.Tactic.TFAE

open Lean Parser Meta Elab Tactic

@[tactic_alt tfaeHave]
syntax (name := tfaeHave') "tfae_have " tfaeHaveIdLhs : tactic

extend_docs tfaeHave'
  before "\"Goal-style\" `tfae_have` syntax is deprecated. Now, `tfae_have ...` should be followed\
    by `:= ...`; see below for the new behavior. This warning can be turned off with \
    `set_option Mathlib.Tactic.TFAE.useDeprecated true`.\n\n***"

elab_rules : tactic
| `(tfaeHave'|tfae_have $d:tfaeHaveIdLhs) => withMainContext do
  -- Deprecate syntax:
  let ref ← getRef
  unless useDeprecated.get (← getOptions) do
logWarning .tagged ``Linter.deprecatedAttr m!"\
      \"Goal-style\" syntax '{ref}' is deprecated in favor of '{ref} := ...'.\n\n\
      To turn this warning off, use set_option Mathlib.Tactic.TFAE.useDeprecated true"

  let goal ← getMainGoal
  let (_, tfaeList) ← getTFAEList (← goal.getType)
let (b, t) ← liftMacroM match d with
    | `(tfaeHaveIdLhs| $hy:hygieneInfo $t:tfaeType) => do
      pure (HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true), t)
    | `(tfaeHaveIdLhs| $b:ident : $t:tfaeType) =>
      pure (b, t)
    | _ => Macro.throwUnsupported
  let n := b.getId
  let type ← elabTFAEType tfaeList t
  let p ← mkFreshExprMVar type MetavarKind.syntheticOpaque n
  let (fv, mainGoal) ← (← MVarId.assert goal n type p).intro1P
  mainGoal.withContext do
    Term.addTermInfo' (isBinder := true) b (mkFVar fv)
  replaceMainGoal [p.mvarId!, mainGoal]

end TFAE

end Mathlib.Tactic
