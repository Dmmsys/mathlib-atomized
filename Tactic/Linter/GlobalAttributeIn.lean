/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/
module

public meta import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header -- shake: keep
public import Lean.Message

/-!
# Linter for `attribute [...] in` declarations

Linter for global attributes created via `attribute [...] in` declarations.

The syntax `attribute [instance] instName in` can be used to accidentally create a global instance.
This is **not** obvious from reading the code, and in fact happened twice during the port,
hence, we lint against it.

*Example*: before this was discovered, `Mathlib/Topology/Category/TopCat/Basic.lean`
contained the following code:
```
attribute [instance] HasForget.instFunLike in
instance (X Y : TopCat.{u}) : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe f := f
```
Despite the `in`, this makes `HasForget.instFunLike` a global instance.

This seems to apply to all attributes. For example:
```lean
theorem what : False := sorry

attribute [simp] what in
#guard true

-- the `simp` attribute persists
example : False := by simp -- `simp` finds `what`

theorem who {x y : Nat} : x = y := sorry

attribute [ext] who in
#guard true

-- the `ext` attribute persists
example {x y : Nat} : x = y := by ext
```
Therefore, we lint against this pattern on all instances.

For *removing* attributes, the `in` works as expected.
```lean
/--
error: failed to synthesize
  Add Nat
-/

#guard_msgs in
attribute [-instance] instAddNat in
#synth Add Nat

-- the `instance` persists
/-- info: instAddNat -/
#guard_msgs in
#synth Add Nat

@[simp]
/--
theorem `what` / 定理 `what`

English:
theorem what
  statement: False
  proof: sorry

中文:
定理 what
  结论: 假
  证明: sorry
-/
theorem what : False := sorry

/-- error: simp made no progress -/
#guard_msgs in
attribute [-simp] what in
example : False := by simp

-- the `simp` attribute persists
#guard_msgs in
example : False := by simp
```
-/

meta section

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- Lint on any occurrence of `attribute [...] name in` which is not `local` or `scoped`:
these are a footgun, as the attribute is applied *globally* (despite the `in`). -/
public register_option linter.globalAttributeIn : Bool := {
  defValue := true
  descr := "enable the globalAttributeIn linter"
}

namespace globalAttributeInLinter

/--
Definition of `getLinterGlobalAttributeIn` / `getLinterGlobalAttributeIn` 的定义

English:
definition getLinterGlobalAttributeIn
  signature: (o : LinterOptions)
  body: getLinterValue linter.globalAttributeIn o

中文:
定义 getLinterGlobalAttributeIn
  签名: (o : LinterOptions)
  定义体: getLinterValue linter.globalAttributeIn o

Depends on / 依赖: getLinterValue, globalAttributeIn, linter, linter.globalAttributeIn
-/
def getLinterGlobalAttributeIn (o : LinterOptions) : Bool :=
  getLinterValue linter.globalAttributeIn o

/--
Definition of `getGlobalAttributesIn?` / `getGlobalAttributesIn?` 的定义

English:
definition getGlobalAttributesIn?
  signature: : Syntax -> Option (Ident × Array (TSyntax `attr))
  body: x.getElems.filterMap fun a => match a.raw with
      | `(Parser.Command.eraseAttr| -$_) => none
      | `(Parser.Term.attrInstance| local $_attr:attr) => none
      | `(Parser.Term.attrInstance| scoped $_attr:attr) => none
      | `(attr| $a) => some a
    (id, xs)
  | _ => default

中文:
定义 getGlobalAttributesIn?
  签名: : Syntax -> 选项类型 (Ident × 数组 (TSyntax `attr))
  定义体: x.getElems.filterMap fun a => match a.raw with
      | `(Parser.Command.eraseAttr| -$_) => none
      | `(Parser.Term.attrInstance| local $_attr:attr) => none
      | `(Parser.Term.attrInstance| scoped $_attr:attr) => none
      | `(attr| $a) => some a
    (id, xs)
  | _ => default

Depends on / 依赖: a.raw, filterMap, getElems, x.getElems.filterMap
-/
def getGlobalAttributesIn? : Syntax -> Option (Ident × Array (TSyntax `attr))
  | `(attribute [$x,*] $id in $_) =>
    let xs := x.getElems.filterMap fun a => match a.raw with
      | `(Parser.Command.eraseAttr| -$_) => none
      | `(Parser.Term.attrInstance| local $_attr:attr) => none
      | `(Parser.Term.attrInstance| scoped $_attr:attr) => none
      | `(attr| $a) => some a
    (id, xs)
  | _ => default

/--
Definition of `globalAttributeIn` / `globalAttributeIn` 的定义

English:
definition globalAttributeIn
  signature: : Linter where run
  body: withSetOptionIn fun stx => do
  unless getLinterGlobalAttributeIn (← getLinterOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for s in stx.topDown do
    if let some (id, nonScopedNorLocal) := getGlobalAttributesIn? s then
      for attr in nonScopedNorLocal do
        Linter.logLint linter.globalAttributeIn attr m!
          "Despite the `in`, the attribute '{attr}' is added globally to '{id}'\n\
          please remove the `in` or make this a `local {attr}`"

中文:
定义 globalAttributeIn
  签名: : Linter where run
  定义体: withSetOptionIn fun stx => do
  unless getLinterGlobalAttributeIn (← getLinterOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for s in stx.topDown do
    if let some (id, nonScopedNorLocal) := getGlobalAttributesIn? s then
      for attr in nonScopedNorLocal do
        Linter.logLint linter.globalAttributeIn attr m!
          "Despite the `in`, the attribute '{attr}' is added globally to '{id}'\n\
          please remove the `in` or make this a `local {attr}`"

Depends on / 依赖: withSetOptionIn
-/
def globalAttributeIn : Linter where run := withSetOptionIn fun stx => do
  unless getLinterGlobalAttributeIn (← getLinterOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for s in stx.topDown do
    if let some (id, nonScopedNorLocal) := getGlobalAttributesIn? s then
      for attr in nonScopedNorLocal do
        Linter.logLint linter.globalAttributeIn attr m!
          "Despite the `in`, the attribute '{attr}' is added globally to '{id}'\n\
          please remove the `in` or make this a `local {attr}`"

initialize addLinter globalAttributeIn

end globalAttributeInLinter

end Mathlib.Linter
