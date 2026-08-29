/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public meta import Lean.Meta.Tactic.Simp.Types
public import Mathlib.Init
public import Qq

/-! # Additional simp utilities

This file adds additional tools for metaprogramming with the `simp` tactic

-/

public meta section

open Lean Meta Qq

namespace Lean.Meta.Simp

/-- `Qq` version of `Lean.Meta.Simp.Methods.discharge?`, which avoids having to use `~q` matching
on the proof expression returned by `discharge?`

`dischargeQ? (a : Q(Prop))` attempts to prove `a` using the discharger, returning
`some (pf : Q(a))` if a proof is found and `none` otherwise. -/
@[inline]
/--
Definition of `Methods.dischargeQ?` / `Methods.dischargeQ?` 的定义

English:
definition Methods.dischargeQ?
  signature: (M : Methods) (a : Q(Prop))
  body: M.discharge? a

中文:
定义 Methods.dischargeQ?
  签名: (M : Methods) (a : Q(命题))
  定义体: M.discharge? a

Depends on / 依赖: M.discharge, discharge
-/
def Methods.dischargeQ? (M : Methods) (a : Q(Prop)) : SimpM Option Q($a) := M.discharge? a

end Lean.Meta.Simp
