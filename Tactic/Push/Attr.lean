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

/-- The type for a constant to be pushed by `push`. -/
/-
**Mathlib.Tactic.Push.Head** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.Push`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type for a constant to be pushed by `push`.
-/
inductive Head where
| const (c : Name)
| lambda
| forall
deriving Inhabited, BEq

/-- Converts a `Head` to a string. -/
/-
**Mathlib.Tactic.Push.Head.toString** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Pu
sh.Head`。
形式化陈述：Mathlib.Tactic.Push.Head → String
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `Head` to a string.
-/
def Head.toString : Head → String
  | .const c => c.toString
  | .lambda => "fun"
  | .forall => "Forall"
/-
**Mathlib.Tactic.Push.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Push`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ToString Head := ⟨Head.toString⟩

/-- Returns the head of an expression. -/
/-
**Mathlib.Tactic.Push.Head.ofExpr** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Push
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the head of an expression.
-/
def Head.ofExpr? : Expr → Option Head
  | .app f _ => f.getAppFn.constName?.map .const
  | .lam .. => some .lambda
  | .forallE .. => some .forall
  | _ => none

/-- The `push` environment extension -/
initialize pushExt : SimpleScopedEnvExtension SimpTheorem (DiscrTree SimpTheorem) ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := fun d e => d.insertKeyValue e.keys e
  }

/--
Checks if the theorem is suitable for the `pull` tactic. That is,
check if it is of the form `x = f ...` where `x` contains the head `f`,
but `f` is not the head of `x`.
-/
/-
**Mathlib.Tactic.Push.isPullThm** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Push`。
形式化陈述：isPullThm (declName : Name) (inv : Bool) : MetaM (Option Head)
参数：declName : Name；inv : Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Checks if the theorem is suitable for the `pull` tactic. That is,
check if it is of the form `x = f ...` where `x` contains the head `f`,
but `f` is not the head of `x`.
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
  containsHead (e : Expr) : Head → Bool
  | .const c => e.containsConst (· == c)
  | .lambda => true
  | .forall => (e.find? (· matches .forallE ..)).isSome

/-- A theorem for the `pull` tactic -/
/-
**Mathlib.Tactic.Push.PullTheorem** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Tactic.Pu
sh`。
形式化陈述：PullTheorem
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A theorem for the `pull` tactic
-/
abbrev PullTheorem := SimpTheorem × Head

/-- The `pull` environment extension -/
initialize pullExt : SimpleScopedEnvExtension PullTheorem (DiscrTree PullTheorem) ←
  registerSimpleScopedEnvExtension {
    initial  := {}
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

