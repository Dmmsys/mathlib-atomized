/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Init

/-!
Mathlib-specific pretty printer options.
-/

public meta section

namespace Mathlib

open Lean

/--
The `pp.mathlib.binderPredicates` option is used to control whether mathlib pretty printers
should use binder predicate notation (such as `∀ x < 2, p x`).
-/
register_option pp.mathlib.binderPredicates : Bool := {
  defValue := true
  descr := "(pretty printer) pretty prints binders such as \
    `forall (x : α) (x < 2), p x` as `forall x < 2, p x`"
}

/--
Definition of `getPPBinderPredicates` / `getPPBinderPredicates` 的定义

English:
definition getPPBinderPredicates
  signature: (o : Options)
  body: o.get pp.mathlib.binderPredicates.name (!getPPAll o)

中文:
定义 getPPBinderPredicates
  签名: (o : Options)
  定义体: o.get pp.mathlib.binderPredicates.name (!getPPAll o)

Depends on / 依赖: binderPredicates, getPPAll, mathlib, o.get, pp.mathlib.binderPredicates.name
-/
def getPPBinderPredicates (o : Options) : Bool :=
  o.get pp.mathlib.binderPredicates.name (!getPPAll o)

end Mathlib
