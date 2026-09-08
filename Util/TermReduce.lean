/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Gabriel Ebner, Yuyang Zhao
-/
module

public meta import Lean.Meta.Tactic.Delta
public import Mathlib.Init

/-!
# Term elaborators for reduction
-/

public meta section

namespace Mathlib.Util.TermReduce

open Lean Elab Term Meta

/-!
The `beta% f x1 ... xn` term elaborator elaborates the expression
`f x1 ... xn` and then does one level of beta reduction.
That is, if `f` is a lambda then it will substitute its arguments.

The purpose of this is to support substitutions in notations such as
`∀ i, beta% p i` so that `p i` gets beta reduced when `p` is a lambda.
-/

/-- `beta% t` elaborates `t` and then if the result is in the form
`f x1 ... xn` where `f` is a (nested) lambda expression,
it will substitute all of its arguments by beta reduction.
This does not recursively do beta reduction, nor will it do
beta reduction of subexpressions.

In particular, `t` is elaborated, its metavariables are instantiated,
and then `Lean.Expr.headBeta` is applied. -/
syntax (name := betaStx) "beta% " term : term

@[term_elab betaStx, inherit_doc betaStx]
/-
**Mathlib.Util.TermReduce.elabBeta** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Util.TermR
educe`。
形式化陈述：elabBeta : TermElab
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def elabBeta : TermElab := fun stx expectedType? =>
  match stx with
  | `(beta% $t) => do
    let e ← elabTerm t expectedType?
    return (← instantiateMVars e).headBeta
  | _ => throwUnsupportedSyntax

/-- `delta% t` elaborates to a head-delta reduced version of `t`. -/
syntax (name := deltaStx) "delta% " term : term

@[term_elab deltaStx, inherit_doc deltaStx]
/-
**Mathlib.Util.TermReduce.elabDelta** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Util.Term
Reduce`。
形式化陈述：elabDelta : TermElab
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def elabDelta : TermElab := fun stx expectedType? =>
  match stx with
  | `(delta% $t) => do
    let t ← withSynthesize (postpone := .partial) do
      elabTerm t expectedType?
    synthesizeSyntheticMVars
    let t ← instantiateMVars t
    let some t ← withoutExporting do delta? t | throwError "cannot delta reduce {t}"
    pure t
  | _ => throwUnsupportedSyntax

/-- `zeta% t` elaborates to a zeta and zeta-delta reduced version of `t`. -/
syntax (name := zetaStx) "zeta% " term : term

@[term_elab zetaStx, inherit_doc zetaStx]
/-
**Mathlib.Util.TermReduce.elabZeta** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Util.TermR
educe`。
形式化陈述：elabZeta : TermElab
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def elabZeta : TermElab := fun stx expectedType? =>
  match stx with
  | `(zeta% $t) => do
    let t ← withSynthesize (postpone := .partial) do
      elabTerm t expectedType?
    synthesizeSyntheticMVars
    let t ← instantiateMVars t
    let t ← zetaReduce t
    pure t
  | _ => throwUnsupportedSyntax

/-- `reduceProj% t` apply `Expr.reduceProjStruct?` to all subexpressions of `t`. -/
syntax (name := reduceProjStx) "reduceProj% " term : term

@[term_elab reduceProjStx, inherit_doc reduceProjStx]
/-
**Mathlib.Util.TermReduce.elabReduceProj** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Util
.TermReduce`。
形式化陈述：elabReduceProj : TermElab
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def elabReduceProj : TermElab := fun stx expectedType? =>
  match stx with
  | `(reduceProj% $t) => do
    let t ← withSynthesize (postpone := .partial) do
      elabTerm t expectedType?
    synthesizeSyntheticMVars
    let t ← instantiateMVars t
    let t ← Lean.Core.transform t (post := fun e ↦ do
      return .continue (← Expr.reduceProjStruct? e))
    pure t
  | _ => throwUnsupportedSyntax

end Mathlib.Util.TermReduce

