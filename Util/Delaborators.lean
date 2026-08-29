/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Init
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public import Mathlib.Util.PPOptions

/-! # Pi type notation

Provides the `Π x : α, β x` notation as an alternative to Lean 4's built-in
`(x : α) → β x` notation. To get all non-`∀` pi types to pretty print this way
then do `open scoped PiNotation`.

The notation also accepts extended binders, like `Π x ∈ s, β x` for `Π x, x ∈ s → β x`.
This can be disabled with the `pp.mathlib.binderPredicates` option.
-/

public meta section

namespace PiNotation
open Lean hiding binderIdent
open Lean.Parser Term
open Lean.PrettyPrinter.Delaborator
open Mathlib

/-- Dependent function type (a "pi type"). The notation `Π x : α, β x` can
also be written as `(x : α) → β x`. -/
-- A direct copy of forall notation but with `Π`/`Pi` instead of `∀`/`Forall`.
@[term_parser]
/--
Definition of `piNotation` / `piNotation` 的定义

English:
definition piNotation
  body: leading_parser:leadPrec
  unicodeSymbol "Π" "PiType" >>
  many1 (ppSpace >> (binderIdent <|> bracketedBinder)) >>
  optType >> ", " >> termParser

中文:
定义 piNotation
  定义体: leading_parser:leadPrec
  unicodeSymbol "Π" "PiType" >>
  many1 (ppSpace >> (binderIdent <|> bracketedBinder)) >>
  optType >> ", " >> termParser

Depends on / 依赖: leadPrec, leading_parser
-/
def piNotation := leading_parser:leadPrec
  unicodeSymbol "Π" "PiType" >>
  many1 (ppSpace >> (binderIdent <|> bracketedBinder)) >>
  optType >> ", " >> termParser

/-- Dependent function type (a "pi type"). The notation `Π x ∈ s, β x` is
short for `Π x, x ∈ s → β x`. -/
-- A copy of forall notation from `Batteries.Util.ExtendedBinder` for pi notation
syntax "Π " binderIdent binderPred ", " term : term

macro_rules
  | `(Π $x:ident $pred:binderPred, $p) => `(Π $x:ident, satisfies_binder_pred% $x $pred -> $p)
  | `(Π _ $pred:binderPred, $p) => `(Π x, satisfies_binder_pred% x $pred -> $p)

/--
Definition of `replacePiNotation` / `replacePiNotation` 的定义

English:
definition replacePiNotation
  signature: : Lean.Macro

中文:
定义 replacePiNotation
  签名: : Lean.Macro
-/
@[macro PiNotation.piNotation] def replacePiNotation : Lean.Macro
  | .node info _ args => return .node info ``Lean.Parser.Term.forall args
  | _ => Lean.Macro.throwUnsupported

/-- Override the Lean 4 pi notation delaborator with one that prints cute binders
such as `∀ ε > 0`. -/
@[delab forallE]
/--
Definition of `delabPi` / `delabPi` 的定义

English:
definition delabPi
  signature: : Delab
  body: whenPPOption getPPBinderPredicates whenPPOption Lean.getPPNotation do
  let stx ← delabForall
  match stx with
  | `(forall ($i:ident : $_), $j:ident in $s -> $body) =>
    if i == j then `(forall $i:ident in $s, $body) else pure stx
  | `(forall ($x:ident : $_), $y:ident > $z -> $body) =>
    if x 

中文:
定义 delabPi
  签名: : Delab
  定义体: whenPPOption getPPBinderPredicates whenPPOption Lean.getPPNotation do
  let stx ← delabForall
  match stx with
  | `(forall ($i:ident : $_), $j:ident in $s -> $body) =>
    if i == j then `(forall $i:ident in $s, $body) else pure stx
  | `(forall ($x:ident : $_), $y:ident > $z -> $body) =>
    if x 

Depends on / 依赖: Lean.getPPNotation, getPPBinderPredicates, getPPNotation, whenPPOption
-/
def delabPi : Delab := whenPPOption getPPBinderPredicates whenPPOption Lean.getPPNotation do
  let stx ← delabForall
  match stx with
  | `(forall ($i:ident : $_), $j:ident in $s -> $body) =>
    if i == j then `(forall $i:ident in $s, $body) else pure stx
  | `(forall ($x:ident : $_), $y:ident > $z -> $body) =>
    if x == y then `(forall $x:ident > $z, $body) else pure stx
  | `(forall ($x:ident : $_), $y:ident < $z -> $body) =>
    if x == y then `(forall $x:ident < $z, $body) else pure stx
  | `(forall ($x:ident : $_), $y:ident >= $z -> $body) =>
    if x == y then `(forall $x:ident >= $z, $body) else pure stx
  | `(forall ($x:ident : $_), $y:ident <= $z -> $body) =>
    if x == y then `(forall $x:ident <= $z, $body) else pure stx
  | `(Π ($i:ident : $_), $j:ident in $s -> $body) =>
    if i == j then `(Π $i:ident in $s, $body) else pure stx
  | `(forall ($i:ident : $_), $j:ident ∉ $s -> $body) =>
    if i == j then `(forall $i:ident ∉ $s, $body) else pure stx
  | `(forall ($i:ident : $_), $j:ident subseteq $s -> $body) =>
    if i == j then `(forall $i:ident subseteq $s, $body) else pure stx
  | `(forall ($i:ident : $_), $j:ident ⊂ $s -> $body) =>
    if i == j then `(forall $i:ident ⊂ $s, $body) else pure stx
  | `(forall ($i:ident : $_), $j:ident ⊇ $s -> $body) =>
    if i == j then `(forall $i:ident ⊇ $s, $body) else pure stx
  | `(forall ($i:ident : $_), $j:ident ⊃ $s -> $body) =>
    if i == j then `(forall $i:ident ⊃ $s, $body) else pure stx
  | _ => pure stx

/-- Override the Lean 4 pi notation delaborator with one that uses `Π` and prints
cute binders such as `∀ ε > 0`.
Note that this takes advantage of the fact that `(x : α) → p x` notation is
never used for propositions, so we can match on this result and rewrite it. -/
@[scoped delab forallE]
/--
Definition of `delabPi'` / `delabPi'` 的定义

English:
definition delabPi'
  signature: : Delab
  body: whenPPOption Lean.getPPNotation do
  -- Use delabForall as a backup if `pp.mathlib.binderPredicates` is false.
let stx ← delabPi > delabForall
  -- Replacements
  let stx : Term ←
    match stx with
    | `($group:bracketedBinder -> $body) => `(Π $group:bracketedBinder, $body)
    | _ => pure stx
  

中文:
定义 delabPi'
  签名: : Delab
  定义体: whenPPOption Lean.getPPNotation do
  -- Use delabForall as a backup if `pp.mathlib.binderPredicates` is false.
let stx ← delabPi > delabForall
  -- Replacements
  let stx : Term ←
    match stx with
    | `($group:bracketedBinder -> $body) => `(Π $group:bracketedBinder, $body)
    | _ => pure stx
  

Depends on / 依赖: Lean.getPPNotation, getPPNotation, whenPPOption
-/
def delabPi' : Delab := whenPPOption Lean.getPPNotation do
  -- Use delabForall as a backup if `pp.mathlib.binderPredicates` is false.
let stx ← delabPi > delabForall
  -- Replacements
  let stx : Term ←
    match stx with
    | `($group:bracketedBinder -> $body) => `(Π $group:bracketedBinder, $body)
    | _ => pure stx
  -- Merging
  match stx with
  | `(Π $group, Π $groups*, $body) => `(Π $group $groups*, $body)
  | _ => pure stx

end PiNotation

section existential
open Lean Parser Term PrettyPrinter Delaborator

/-- Delaborator for existential quantifier, including extended binders. -/
-- TODO: reduce the duplication in this code
@[app_delab Exists]
/--
Definition of `exists_delab` / `exists_delab` 的定义

English:
definition exists_delab
  signature: : Delab
  body: whenPPOption Lean.getPPNotation do
  let #[ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.wi

中文:
定义 存在_delab
  签名: : Delab
  定义体: whenPPOption Lean.getPPNotation do
  let #[ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.wi

Depends on / 依赖: Lean.getPPNotation, getPPNotation, whenPPOption
-/
def exists_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(exists (_ : $dom), $body)
      else if prop || ppTypes then
        `(exists ($x:ident : $dom), $body)
      else
        `(exists $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    if ← getPPOption Mathlib.getPPBinderPredicates then
      match stx with
      | `(exists $i:ident, $j:ident in $s ∧ $body)
      | `(exists ($i:ident : $_), $j:ident in $s ∧ $body) =>
        if i == j then `(exists $i:ident in $s, $body) else pure stx
      | `(exists $x:ident, $y:ident > $z ∧ $body)
      | `(exists ($x:ident : $_), $y:ident > $z ∧ $body) =>
        if x == y then `(exists $x:ident > $z, $body) else pure stx
      | `(exists $x:ident, $y:ident < $z ∧ $body)
      | `(exists ($x:ident : $_), $y:ident < $z ∧ $body) =>
        if x == y then `(exists $x:ident < $z, $body) else pure stx
      | `(exists $x:ident, $y:ident >= $z ∧ $body)
      | `(exists ($x:ident : $_), $y:ident >= $z ∧ $body) =>
        if x == y then `(exists $x:ident >= $z, $body) else pure stx
      | `(exists $x:ident, $y:ident <= $z ∧ $body)
      | `(exists ($x:ident : $_), $y:ident <= $z ∧ $body) =>
        if x == y then `(exists $x:ident <= $z, $body) else pure stx
      | `(exists $x:ident, $y:ident ∉ $z ∧ $body)
      | `(exists ($x:ident : $_), $y:ident ∉ $z ∧ $body) => do
        if x == y then `(exists $x:ident ∉ $z, $body) else pure stx
      | `(exists $x:ident, $y:ident subseteq $z ∧ $body)
      | `(exists ($x:ident : $_), $y:ident subseteq $z ∧ $body) =>
        if x == y then `(exists $x:ident subseteq $z, $body) else pure stx
      | `(exists $x:ident, $y:ident ⊂ $z ∧ $body)
      | `(exists ($x:ident : $_), $y:ident ⊂ $z ∧ $body) =>
        if x == y then `(exists $x:ident ⊂ $z, $body) else pure stx
      | `(exists $x:ident, $y:ident ⊇ $z ∧ $body)
      | `(exists ($x:ident : $_), $y:ident ⊇ $z ∧ $body) =>
        if x == y then `(exists $x:ident ⊇ $z, $body) else pure stx
      | `(exists $x:ident, $y:ident ⊃ $z ∧ $body)
      | `(exists ($x:ident : $_), $y:ident ⊃ $z ∧ $body) =>
        if x == y then `(exists $x:ident ⊃ $z, $body) else pure stx
      | _ => pure stx
    else
      pure stx
  match stx with
  | `(exists $group:bracketedExplicitBinders, exists $[$groups:bracketedExplicitBinders]*, $body) =>
    `(exists $group $groups*, $body)
  | `(exists $b:binderIdent, exists $[$bs:binderIdent]*, $body) => `(exists $b:binderIdent $[$bs]*, $body)
  | _ => pure stx
end existential

open Lean Lean.PrettyPrinter.Delaborator

/--
Definition of `delabNotIn` / `delabNotIn` 的定义

English:
definition delabNotIn
  body: whenPPOption Lean.getPPNotation do
  let #[f] := (← SubExpr.getExpr).getAppArgs | failure
guard f.isAppOfArity ``Membership.mem 5
let stx₁ ← SubExpr.withAppArg SubExpr.withNaryArg 3 delab
let stx₂ ← SubExpr.withAppArg SubExpr.withNaryArg 4 delab
  return ← `($stx₂ ∉ $stx₁)

中文:
定义 delabNotIn
  定义体: whenPPOption Lean.getPPNotation do
  let #[f] := (← SubExpr.getExpr).getAppArgs | failure
guard f.isAppOfArity ``Membership.mem 5
let stx₁ ← SubExpr.withAppArg SubExpr.withNaryArg 3 delab
let stx₂ ← SubExpr.withAppArg SubExpr.withNaryArg 4 delab
  return ← `($stx₂ ∉ $stx₁)
-/
@[app_delab Not] def delabNotIn := whenPPOption Lean.getPPNotation do
  let #[f] := (← SubExpr.getExpr).getAppArgs | failure
guard f.isAppOfArity ``Membership.mem 5
let stx₁ ← SubExpr.withAppArg SubExpr.withNaryArg 3 delab
let stx₂ ← SubExpr.withAppArg SubExpr.withNaryArg 4 delab
  return ← `($stx₂ ∉ $stx₁)
