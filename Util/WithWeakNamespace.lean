/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam, Gabriel Ebner
-/
module

public import Mathlib.Init

/-!
# Defines `with_weak_namespace` command.

Changes the current namespace without causing scoped things to go out of scope.
-/

public meta section

namespace Lean.Elab.Command

/-- Adds the name to the namespace, `_root_`-aware.
```
resolveNamespace `A `B.b == `A.B.b
resolveNamespace `A `_root_.B.c == `B.c
```
-/
/-
**Lean.Elab.Command.resolveNamespace** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Comman
d`。
形式化陈述：Name → Name → Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adds the name to the namespace, `_root_`-aware.
```
resolveNamespace `A `B.b == `A.B.b
resolveNamespace `A `_root_.B.c == `B.c
```
-/
def resolveNamespace (ns : Name) : Name → Name
  | `_root_ => Name.anonymous
  | Name.str n s .. => Name.mkStr (resolveNamespace ns n) s
  | Name.num n i .. => Name.mkNum (resolveNamespace ns n) i
  | Name.anonymous => ns

/-- Changes the current namespace without causing scoped things to go out of scope -/
/-
**Lean.Elab.Command.withWeakNamespace** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Comma
nd`。
形式化陈述：withWeakNamespace {α : Type} (ns : Name) (m : CommandElabM α) : CommandEla
bM α
参数：ns : Name；m : CommandElabM α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Changes the current namespace without causing scoped things to go out of scope
-/
def withWeakNamespace {α : Type} (ns : Name) (m : CommandElabM α) : CommandElabM α := do
  let old ← getCurrNamespace
  let ns := resolveNamespace old ns
  modify fun s ↦ { s with env := s.env.registerNamespace ns }
  modifyScope ({ · with currNamespace := ns })
  try m finally modifyScope ({ · with currNamespace := old })

/-- Changes the current namespace without causing scoped things to go out of scope -/
elab "with_weak_namespace " ns:ident cmd:command : command =>
  withWeakNamespace ns.getId (elabCommand cmd)

end Lean.Elab.Command

