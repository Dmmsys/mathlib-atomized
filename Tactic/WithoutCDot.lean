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

/--
Definition of `withoutCDotContents` / `withoutCDotContents` 的定义

English:
definition withoutCDotContents
  signature: : Parser
  body: withoutPosition
    withoutForbidden (termParser >> optional (" :" >> optional (ppSpace >> termParser)))

中文:
定义 withoutCDotContents
  签名: : Parser
  定义体: withoutPosition
    withoutForbidden (termParser >> optional (" :" >> optional (ppSpace >> termParser)))
-/
private def withoutCDotContents : Parser :=
withoutPosition
    withoutForbidden (termParser >> optional (" :" >> optional (ppSpace >> termParser)))

/-- A set of parentheses, supporting type ascriptions, which does not process `·`.

Primarily, this is useful when quoting user-provided syntax inside parentheses, as it prevents `·`s
from the caller being interpreted in the context of `()`s from the macro. -/
@[term_parser]
/--
Definition of `withoutCDot` / `withoutCDot` 的定义

English:
definition withoutCDot
  body: leading_parser
  "without_cdot(" >> withoutCDotContents >> ")"

中文:
定义 withoutCDot
  定义体: leading_parser
  "without_cdot(" >> withoutCDotContents >> ")"

Depends on / 依赖: leading_parser
-/
def withoutCDot := leading_parser
  "without_cdot(" >> withoutCDotContents >> ")"

/-- Implementation detail of `withoutCDot` -/
@[term_parser]
/--
Definition of `withoutCDotImpl` / `withoutCDotImpl` 的定义

English:
definition withoutCDotImpl
  body: leading_parser
  "without_cdot_impl(" >> withoutCDotContents >> ")"

中文:
定义 withoutCDotImpl
  定义体: leading_parser
  "without_cdot_impl(" >> withoutCDotContents >> ")"

Depends on / 依赖: leading_parser
-/
def withoutCDotImpl := leading_parser
  "without_cdot_impl(" >> withoutCDotContents >> ")"

-- The `no_implicit_lambda%`s here are to emulate the behavior of `blockImplicitLambda`
macro_rules
  | `(without_cdot($e :)) => `(no_implicit_lambda% without_cdot_impl($e :))
  | `(without_cdot($e : $ty)) => `(no_implicit_lambda% without_cdot_impl($e : $ty))
  | `(without_cdot($e)) => `(without_cdot_impl($e))

@[term_elab withoutCDotImpl, inherit_doc withoutCDot]
/--
Definition of `elabWithoutCDot` / `elabWithoutCDot` 的定义

English:
definition elabWithoutCDot
  signature: : TermElab

中文:
定义 elabWithoutCDot
  签名: : TermElab

Depends on / 依赖: elabType
-/
def elabWithoutCDot : TermElab
  -- copied from `elabTypeAscription`
  | `(without_cdot_impl($e : $type)), _ => do
let type ← withSynthesize (postpone := .yes) elabType type
    let e ← elabTerm e type
    ensureHasType type e
  | `(without_cdot_impl($e :)), expectedType? => do
let e ← withSynthesize (postpone := .no) elabTerm e none
    ensureHasType expectedType? e
  | `(without_cdot_impl($e)), expectedType? => do
    elabTerm e expectedType?
  | _, _ => throwUnsupportedSyntax

end Lean.Elab.Term
