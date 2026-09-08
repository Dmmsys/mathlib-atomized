/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public meta import Lean.Elab.SyntheticMVars
public import Mathlib.Init

/-!
# The `without_cdot()` elaborator
-/

public meta section

namespace Lean.Elab.Term

open Parser

/-
**Lean.Elab.Term.withoutCDotContents** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Term`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def withoutCDotContents : Parser :=
  withoutPosition <|
    withoutForbidden (termParser >> optional (" :" >> optional (ppSpace >> termParser)))

/-- A set of parentheses, supporting type ascriptions, which does not process `·`.

Primarily, this is useful when quoting user-provided syntax inside parentheses, as it prevents `·`s
from the caller being interpreted in the context of `()`s from the macro. -/
@[term_parser]
/-
**Lean.Elab.Term.withoutCDot** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Term`。
形式化陈述：withoutCDot
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of parentheses, supporting type ascriptions, which does not process `·`.

Primarily, this is useful when quoting user-provided syntax inside parentheses, 
as it prevents `·`s
from the caller being interpreted in the context of `()`s from the macro.
-/
def withoutCDot := leading_parser
  "without_cdot(" >> withoutCDotContents >> ")"

/-- Implementation detail of `withoutCDot` -/
@[term_parser]
/-
**Lean.Elab.Term.withoutCDotImpl** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Term`。
形式化陈述：withoutCDotImpl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail of `withoutCDot`
-/
def withoutCDotImpl := leading_parser
  "without_cdot_impl(" >> withoutCDotContents >> ")"

-- The `no_implicit_lambda%`s here are to emulate the behavior of `blockImplicitLambda`
macro_rules
  | `(without_cdot($e :)) => `(no_implicit_lambda% without_cdot_impl($e :))
  | `(without_cdot($e : $ty)) => `(no_implicit_lambda% without_cdot_impl($e : $ty))
  | `(without_cdot($e)) => `(without_cdot_impl($e))

@[term_elab withoutCDotImpl, inherit_doc withoutCDot]
/-
**Lean.Elab.Term.elabWithoutCDot** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Term`。
形式化陈述：elabWithoutCDot : TermElab -- copied from `elabTypeAscription` | `(without
_cdot_impl($e : $type)), _ => do let type ← withSynthesize (postpone
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def elabWithoutCDot : TermElab
  -- copied from `elabTypeAscription`
  | `(without_cdot_impl($e : $type)), _ => do
    let type ← withSynthesize (postpone := .yes) <| elabType type
    let e ← elabTerm e type
    ensureHasType type e
  | `(without_cdot_impl($e :)), expectedType? => do
    let e ← withSynthesize (postpone := .no) <| elabTerm e none
    ensureHasType expectedType? e
  | `(without_cdot_impl($e)), expectedType? => do
    elabTerm e expectedType?
  | _, _ => throwUnsupportedSyntax

end Lean.Elab.Term

