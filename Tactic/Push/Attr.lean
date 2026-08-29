/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init
public import Lean.Meta.Tactic.Simp

/-!
# The `@[push]` attribute for the `push` and `pull` tactics

This file defines the `@[push]` attribute, so that it can be used without importing
the tactic itself.
-/

public meta section

namespace Mathlib.Tactic.Push

open Lean Meta

/--
Inductive type `Head` / 归纳类型 `Head`

English:
inductive Head
  parameters: where
  constructors (3):
    - const: (c : Name)
    - lambda: 
    - forall: 

中文:
归纳类型 Head
  参数: where
  构造子 (3 个):
    - const: (c : Name)
    - lambda: 
    - forall: 
-/
inductive Head where
| const (c : Name)
| lambda
| forall
deriving Inhabited, BEq

/--
Definition of `Head.toString` / `Head.toString` 的定义

English:
definition Head.toString
  signature: : Head -> String

中文:
定义 Head.toString
  签名: : Head -> String
-/
def Head.toString : Head -> String
  | .const c => c.toString
  | .lambda => "fun"
  | .forall => "Forall"

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString Head
  body: ⟨Head.toString⟩

中文:
实例 :
  签名: ToString Head
  定义体: ⟨Head.toString⟩

Depends on / 依赖: Head.toString, toString
-/
instance : ToString Head := ⟨Head.toString⟩

/--
Definition of `Head.ofExpr?` / `Head.ofExpr?` 的定义

English:
definition Head.ofExpr?
  signature: : Expr -> Option Head

中文:
定义 Head.ofExpr?
  签名: : Expr -> Option Head
-/
def Head.ofExpr? : Expr -> Option Head
  | .app f _ => f.getAppFn.constName?.map .const
  | .lam .. => some .lambda
  | .forallE .. => some .forall
  | _ => none

/-- The `push` environment extension -/
initialize pushExt : SimpleScopedEnvExtension SimpTheorem (DiscrTree SimpTheorem) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun d e => d.insertKeyValue e.keys e
  }

/--
Definition of `isPullThm` / `isPullThm` 的定义

English:
definition isPullThm
  signature: (declName : Name) (inv : Bool)
  body: do
  let cinfo ← getConstInfo declName
  forallTelescope cinfo.type fun _ type => do
    let some (lhs, rhs) := type.eqOrIff? | return none
    let (lhs, rhs) := if inv then (rhs, lhs) else (lhs, rhs)
    let some head := Head.ofExpr? rhs | return none
    if Head.ofExpr? lhs != some head && contain

中文:
定义 isPullThm
  签名: (declName : Name) (inv : 布尔)
  定义体: do
  let cinfo ← getConstInfo declName
  forallTelescope cinfo.type fun _ type => do
    let some (lhs, rhs) := type.eqOrIff? | return none
    let (lhs, rhs) := if inv then (rhs, lhs) else (lhs, rhs)
    let some head := Head.ofExpr? rhs | return none
    if Head.ofExpr? lhs != some head && contain
-/
def isPullThm (declName : Name) (inv : Bool) : MetaM (Option Head) := do
  let cinfo ← getConstInfo declName
  forallTelescope cinfo.type fun _ type => do
    let some (lhs, rhs) := type.eqOrIff? | return none
    let (lhs, rhs) := if inv then (rhs, lhs) else (lhs, rhs)
    let some head := Head.ofExpr? rhs | return none
    if Head.ofExpr? lhs != some head && containsHead lhs head then
      return head
    return none
where
  /-- Checks if the expression has the head in any subexpression.
  We don't need to check this for `.lambda`, because the term being a function
  is sufficient for `pull fun _ ↦ _` to be applicable. -/
  containsHead (e : Expr) : Head -> Bool
  | .const c => e.containsConst (· == c)
  | .lambda => true
  | .forall => (e.find? (· matches .forallE ..)).isSome

/--
Definition of `PullTheorem` / `PullTheorem` 的定义

English:
abbreviation PullTheorem
  body: SimpTheorem × Head

中文:
缩写 PullTheorem
  定义体: SimpTheorem × Head

Depends on / 依赖: SimpTheorem
-/
abbrev PullTheorem := SimpTheorem × Head

/-- The `pull` environment extension -/
initialize pullExt : SimpleScopedEnvExtension PullTheorem (DiscrTree PullTheorem) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun d e => d.insertKeyValue e.1.keys e
  }

/--
The `push` attribute is used to tag lemmas that "push" a constant into an expression.

For example:
```lean
@[push] theorem log_mul (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y
@[push] theorem log_abs : log |x| = log x

@[push] theorem not_imp (p q : Prop) : ¬(p → q) ↔ p ∧ ¬q
@[push] theorem not_iff (p q : Prop) : ¬(p ↔ q) ↔ (p ∧ ¬q) ∨ (¬p ∧ q)
@[push] theorem not_not (p : Prop) : ¬ ¬p ↔ p
@[push] theorem not_le : ¬a ≤ b ↔ b < a
```

Note that some `push` lemmas don't push the constant away from the head (`log_abs`) and
some `push` lemmas cancel the constant out (`not_not` and `not_le`).
For the other lemmas that are "genuine" `push` lemmas, a `pull` attribute is automatically added
in the reverse direction. To not add a `pull` tag, use `@[push only]`.

To tag the reverse direction of the lemma, use `@[push ←]`.
-/
syntax (name := pushAttr) "push" (" ←" <|> " <-")? (&" only")? (ppSpace prio)? : attr

@[inherit_doc pushAttr]
initialize registerBuiltinAttribute {
  name := `pushAttr
  descr := "attribute for push"
  add := fun declName stx kind => MetaM.run' do
    -- Make sure `mkSimpTheoremFromConst` aux decls are sufficiently visible, like in
    -- `addSimpTheorem`.
    withExporting (isExporting := !isPrivateName declName) do
    let inv := !stx[1].isNone
    let isOnly := !stx[2].isNone
    let prio ← getAttrParamOptPrio stx[3]
    let #[thm] ← mkSimpTheoremFromConst declName (inv := inv) (prio := prio) |
      throwError "couldn't generate a simp theorem for `push`"
    pushExt.add thm
    unless isOnly do
      let inv := !inv -- the `pull` lemma is added in the reverse direction
      if let some head ← isPullThm declName inv then
        let #[thm] ← mkSimpTheoremFromConst declName (inv := inv) (prio := prio) |
          throwError "couldn't generate a simp theorem for `pull`"
        pullExt.add (thm, head)
}

end Mathlib.Tactic.Push
