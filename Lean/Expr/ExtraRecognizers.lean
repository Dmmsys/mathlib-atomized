/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Set.CoeSort
import Lean.Expr

/-!
# Additional Expr recognizers needing theory imports

-/

public section

namespace Lean.Expr

/--
Definition of `coeTypeSet?` / `coeTypeSet?` 的定义

English:
definition coeTypeSet?
  signature: (e : Expr)
  body: do
  if e.isAppOfArity ``Set.Elem 2 then
    return e.appArg!
  else if e.isAppOfArity ``Subtype 2 then
    let .lam _ _ body _ := e.appArg! | failure
guard body.isAppOfArity ``Membership.mem 5
    let #[_, _, inst, .bvar 0, s] := body.getAppArgs | failure
guard inst.isAppOfArity ``Set.instMembershi

中文:
定义 coeTypeSet?
  签名: (e : Expr)
  定义体: do
  if e.isAppOfArity ``Set.Elem 2 then
    return e.appArg!
  else if e.isAppOfArity ``Subtype 2 then
    let .lam _ _ body _ := e.appArg! | failure
guard body.isAppOfArity ``Membership.mem 5
    let #[_, _, inst, .bvar 0, s] := body.getAppArgs | failure
guard inst.isAppOfArity ``Set.instMembershi
-/
def coeTypeSet? (e : Expr) : Option Expr := do
  if e.isAppOfArity ``Set.Elem 2 then
    return e.appArg!
  else if e.isAppOfArity ``Subtype 2 then
    let .lam _ _ body _ := e.appArg! | failure
guard body.isAppOfArity ``Membership.mem 5
    let #[_, _, inst, .bvar 0, s] := body.getAppArgs | failure
guard inst.isAppOfArity ``Set.instMembership 1
    return s
  else
    failure

end Lean.Expr
