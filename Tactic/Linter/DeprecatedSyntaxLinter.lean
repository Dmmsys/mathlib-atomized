/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jeremy Tan, Adomas Baliuka
-/
module

public meta import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header -- shake: keep
public import Lean.Parser.Command

/-!
# Linter against deprecated syntax

`refine'`, `cases'` and `induction'` provide backward-compatible implementations of their
unprimed equivalents in Lean 3 –`refine`, `cases` and `induction` respectively.
They have been superseded by Lean 4 tactics:

* `refine` and `apply` replace `refine'`. While they are similar, they handle metavariables
  slightly differently; this means that they are not completely interchangeable, nor can one
  completely replace another. However, `refine` and `apply` are more readable and (heuristically)
  tend to be more efficient on average.
* `obtain`, `rcases` and `cases` replace `cases'`. Unlike the replacement tactics, `cases'`
  does not require the variables it introduces to be separated by case, which hinders readability.
* `induction` replaces `induction'` for similar reasons to `cases` and `cases'`.

The `admit` tactic is a synonym for the much more common `sorry`, so the latter should be preferred.

The `native_decide` tactic is not allowed in mathlib, as it trusts the entire Lean compiler
(and not just the Lean kernel). Because the latter is large and complicated, at present it is
probably possible to prove `False` using `native_decide`.

This linter is an incentive to discourage uses of such deprecated syntax, without being a ban.
It is not inherently limited to tactics.
-/

meta section

open Lean Elab Linter

namespace Mathlib.Linter.Style

/-- The option `linter.style.refine` of the deprecated syntax linter flags usages of
the `refine'` tactic.

The tactics `refine`, `apply` and `refine'` are similar, but they handle metavariables slightly
differently. This means that they are not completely interchangeable, nor can one completely
replace another. However, `refine` and `apply` are more readable and (heuristically) tend to be
more efficient on average.
-/
public register_option linter.style.refine : Bool := {
  defValue := false
  descr := "enable the refine linter"
}

/-- The option `linter.style.cases` of the deprecated syntax linter flags usages of
the `cases'` tactic, which is a backward-compatible version of Lean 3's `cases` tactic.
Unlike `obtain`, `rcases` and Lean 4's `cases`, variables introduced by `cases'` are not
required to be separated by case, which hinders readability.
-/
public register_option linter.style.cases : Bool := {
  defValue := false
  descr := "enable the cases linter"
}

/-- The option `linter.style.induction` of the deprecated syntax linter flags usages of
the `induction'` tactic, which is a backward-compatible version of Lean 3's `induction` tactic.
Unlike Lean 4's `induction`, variables introduced by `induction'` are not
required to be separated by case, which hinders readability.
-/
public register_option linter.style.induction : Bool := {
  defValue := false
  descr := "enable the induction linter"
}

/-- The option `linter.style.admit` of the deprecated syntax linter flags usages of
the `admit` tactic, which is a synonym for the much more common `sorry`. -/
public register_option linter.style.admit : Bool := {
  defValue := false
  descr := "enable the admit linter"
}

/-- The option `linter.style.nativeDecide` of the deprecated syntax linter flags usages of
the `native_decide` tactic, which is disallowed in mathlib. -/
-- Note: this linter is purely for user information. Running `lean4checker` in CI catches *any*
-- additional axioms that are introduced (not just `ofReduceBool`): the point of this check is to
-- alert the user quickly, not to be airtight.
public register_option linter.style.nativeDecide : Bool := {
  defValue := false
  descr := "enable the nativeDecide linter"
}

/-- The option `linter.style.maxHeartbeats` of the deprecated syntax linter flags usages of
`set_option <name-containing-maxHeartbeats> n in cmd` that do not add a comment explaining
the reason for the modification of the `maxHeartbeats`.

This includes `set_option maxHeartbeats n in` and `set_option synthInstance.maxHeartbeats n in`.
-/
public register_option linter.style.maxHeartbeats : Bool := {
  defValue := false
  descr := "enable the maxHeartbeats linter"
}

/--
Definition of `getSetOptionMaxHeartbeatsComment` / `getSetOptionMaxHeartbeatsComment` 的定义

English:
definition getSetOptionMaxHeartbeatsComment
  signature: : Syntax -> Option (Name × Nat × Substring.Raw)
  body: mh.getId
    if !opt.components.contains `maxHeartbeats then
      none
    else
      if let some inAtom := stx.find? (·.getAtomVal == "in") then
        inAtom.getTrailing?.map (opt, n.getNat, ·)
      else
        -- This branch should be unreachable.
        some default
  | _ => none

中文:
定义 getSetOptionMaxHeartbeatsComment
  签名: : Syntax -> 选项类型 (Name × 自然数 × Substring.Raw)
  定义体: mh.getId
    if !opt.components.contains `maxHeartbeats then
      none
    else
      if let some inAtom := stx.find? (·.getAtomVal == "in") then
        inAtom.getTrailing?.map (opt, n.getNat, ·)
      else
        -- This branch should be unreachable.
        some default
  | _ => none

Depends on / 依赖: mh.getId
-/
def getSetOptionMaxHeartbeatsComment : Syntax -> Option (Name × Nat × Substring.Raw)
  | stx@`(command|set_option $mh $n:num in $_) =>
    let opt := mh.getId
    if !opt.components.contains `maxHeartbeats then
      none
    else
      if let some inAtom := stx.find? (·.getAtomVal == "in") then
        inAtom.getTrailing?.map (opt, n.getNat, ·)
      else
        -- This branch should be unreachable.
        some default
  | _ => none

/--
Definition of `isDecideNative` / `isDecideNative` 的定义

English:
definition isDecideNative
  signature: (stx : Syntax )
  body: match stx with
  | .node _ ``Lean.Parser.Tactic.decide args =>
    -- The configuration passed to the tactic call.
    let config := args[1]![0]
    -- Check all configuration arguments in order to determine the final
    -- toggling of the native decide option.
    if let (.node _ _ config_args) :=

中文:
定义 isDecide自然数ive
  签名: (stx : Syntax )
  定义体: match stx with
  | .node _ ``Lean.Parser.Tactic.decide args =>
    -- The configuration passed to the tactic call.
    let config := args[1]![0]
    -- Check all configuration arguments in order to determine the final
    -- toggling of the native decide option.
    if let (.node _ _ config_args) :=

Depends on / 依赖: Lean.Parser.Tactic.decide, Parser, Tactic
-/
def isDecideNative (stx : Syntax ) : Bool :=
  match stx with
  | .node _ ``Lean.Parser.Tactic.decide args =>
    -- The configuration passed to the tactic call.
    let config := args[1]![0]
    -- Check all configuration arguments in order to determine the final
    -- toggling of the native decide option.
    if let (.node _ _ config_args) := config then
      let natives := config_args.filterMap (match ·[0] with
        | `(Parser.Tactic.posConfigItem| +native) => some true
        | `(Parser.Tactic.negConfigItem| -native) => some false
        | `(Parser.Tactic.valConfigItem| (config := {native := true})) => some true
        | `(Parser.Tactic.valConfigItem| (config := {native := false})) => some false
        | _ => none)
      natives.back? == some true
    else
      false
  | _ => false

/-- `getDeprecatedSyntax t` returns all usages of deprecated syntax in the input syntax `t`. -/
partial
/--
Definition of `getDeprecatedSyntax` / `getDeprecatedSyntax` 的定义

English:
definition getDeprecatedSyntax
  signature: : Syntax -> Array (SyntaxNodeKind × Syntax × MessageData)
  body: args.flatMap getDeprecatedSyntax
    match kind with
    | ``Lean.Parser.Tactic.refine' =>
      rargs.push (kind, stx,
        "The `refine'` tactic is discouraged: \
         please strongly consider using `refine` or `apply` instead.")
    | `Mathlib.Tactic.cases' =>
      rargs.push (kind, stx,


中文:
定义 getDeprecatedSyntax
  签名: : Syntax -> 数组 (SyntaxNodeKind × Syntax × MessageData)
  定义体: args.flatMap getDeprecatedSyntax
    match kind with
    | ``Lean.Parser.Tactic.refine' =>
      rargs.push (kind, stx,
        "The `refine'` tactic is discouraged: \
         please strongly consider using `refine` or `apply` instead.")
    | `Mathlib.Tactic.cases' =>
      rargs.push (kind, stx,


Depends on / 依赖: args.flatMap, flatMap, getDeprecatedSyntax
-/
def getDeprecatedSyntax : Syntax -> Array (SyntaxNodeKind × Syntax × MessageData)
  | stx@(.node _ kind args) =>
    let rargs := args.flatMap getDeprecatedSyntax
    match kind with
    | ``Lean.Parser.Tactic.refine' =>
      rargs.push (kind, stx,
        "The `refine'` tactic is discouraged: \
         please strongly consider using `refine` or `apply` instead.")
    | `Mathlib.Tactic.cases' =>
      rargs.push (kind, stx,
        "The `cases'` tactic is discouraged: \
         please strongly consider using `obtain`, `rcases` or `cases` instead.")
    | `Mathlib.Tactic.induction' =>
      rargs.push (kind, stx,
        "The `induction'` tactic is discouraged: \
         please strongly consider using `induction` instead.")
    | ``Lean.Parser.Tactic.tacticAdmit =>
      rargs.push (kind, stx,
        "The `admit` tactic is discouraged: \
         please strongly consider using the synonymous `sorry` instead.")
    | ``Lean.Parser.Tactic.decide =>
      if isDecideNative stx then
        rargs.push (kind, stx, "Using `decide +native` is not allowed in mathlib: \
        because it trusts the entire Lean compiler (not just the Lean kernel), \
        it could quite possibly be used to prove false.")
      else
        rargs
    | ``Lean.Parser.Tactic.nativeDecide =>
      rargs.push (kind, stx, "Using `native_decide` is not allowed in mathlib: \
        because it trusts the entire Lean compiler (not just the Lean kernel), \
        it could quite possibly be used to prove false.")
    | ``Lean.Parser.Command.in =>
      match getSetOptionMaxHeartbeatsComment stx with
      | none => rargs
      | some (opt, n, trailing) =>
        -- Since we are now seeing the currently outermost `maxHeartbeats` option,
        -- we remove all subsequent potential flags and only decide whether to lint or not
        -- based on whether the current option has a comment.
        let rargs := rargs.filter (·.1 != `MaxHeartbeats)
        if trailing.toString.trimAsciiStart.isEmpty then
          rargs.push (`MaxHeartbeats, stx,
            s!"Please, add a comment explaining the need for modifying the maxHeartbeat limit, \
              as in\nset_option {opt} {n} in\n-- reason for change\n...")
        else
          rargs
    | _ => rargs
  | _ => default

/--
Definition of `deprecatedSyntaxLinter` / `deprecatedSyntaxLinter` 的定义

English:
definition deprecatedSyntaxLinter
  signature: : Linter where run stx
  body: do
  unless getLinterValue linter.style.refine (← getLinterOptions) ||
      getLinterValue linter.style.cases (← getLinterOptions) ||
      getLinterValue linter.style.induction (← getLinterOptions) ||
      getLinterValue linter.style.admit (← getLinterOptions) ||
      getLinterValue linter.style

中文:
定义 deprecatedSyntaxLinter
  签名: : Linter where run stx
  定义体: do
  unless getLinterValue linter.style.refine (← getLinterOptions) ||
      getLinterValue linter.style.cases (← getLinterOptions) ||
      getLinterValue linter.style.induction (← getLinterOptions) ||
      getLinterValue linter.style.admit (← getLinterOptions) ||
      getLinterValue linter.style
-/
def deprecatedSyntaxLinter : Linter where run stx := do
  unless getLinterValue linter.style.refine (← getLinterOptions) ||
      getLinterValue linter.style.cases (← getLinterOptions) ||
      getLinterValue linter.style.induction (← getLinterOptions) ||
      getLinterValue linter.style.admit (← getLinterOptions) ||
      getLinterValue linter.style.maxHeartbeats (← getLinterOptions) ||
      getLinterValue linter.style.nativeDecide (← getLinterOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  let deprecations := getDeprecatedSyntax stx
  -- Using `withSetOptionIn` here, allows the linter to parse also the "leading" `set_option`s
  -- but then flagging them only if the corresponding option is still set after elaborating the
  -- leading `set_option`s.
  -- In particular, this means that the linter "sees" `set_option maxHeartbeats 10 in ...`,
  -- records it in `deprecations` and then acts on it, according to the correct options.
  (withSetOptionIn fun _ => do
    for (kind, stx', msg) in deprecations do
      match kind with
      | ``Lean.Parser.Tactic.refine' => Linter.logLintIf linter.style.refine stx' msg
      | `Mathlib.Tactic.cases' => Linter.logLintIf linter.style.cases stx' msg
      | `Mathlib.Tactic.induction' => Linter.logLintIf linter.style.induction stx' msg
      | ``Lean.Parser.Tactic.tacticAdmit => Linter.logLintIf linter.style.admit stx' msg
      | ``Lean.Parser.Tactic.nativeDecide | ``Lean.Parser.Tactic.decide =>
        Linter.logLintIf linter.style.nativeDecide stx' msg
      | `MaxHeartbeats => Linter.logLintIf linter.style.maxHeartbeats stx' msg
      | _ => continue) stx

initialize addLinter deprecatedSyntaxLinter

end Mathlib.Linter.Style
