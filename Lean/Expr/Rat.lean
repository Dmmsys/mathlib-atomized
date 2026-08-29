/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
module

public import Mathlib.Init
public import Lean.ToExpr

/-!
# Additional operations on Expr and rational numbers

This file defines some operations involving `Expr` and rational numbers.

## Main definitions

* `Lean.Expr.isExplicitNumber`: is an expression a number in normal form?
  This includes natural numbers, integers and rationals.
-/

public section

namespace Lean.Expr

/--
Definition of `rat?` / `rat?` 的定义

English:
definition rat?
  signature: (e : Expr)
  body: do
  if e.isAppOfArity ``Div.div 4 then
    let d ← e.appArg!.nat?
    guard (d != 1)
    let n ← e.appFn!.appArg!.int?
    let q := mkRat n d
    guard (q.den = d)
    pure q
  else
    e.int?

中文:
定义 rat?
  签名: (e : Expr)
  定义体: do
  if e.isAppOfArity ``Div.div 4 then
    let d ← e.appArg!.nat?
    guard (d != 1)
    let n ← e.appFn!.appArg!.int?
    let q := mkRat n d
    guard (q.den = d)
    pure q
  else
    e.int?
-/
def rat? (e : Expr) : Option Rat := do
  if e.isAppOfArity ``Div.div 4 then
    let d ← e.appArg!.nat?
    guard (d != 1)
    let n ← e.appFn!.appArg!.int?
    let q := mkRat n d
    guard (q.den = d)
    pure q
  else
    e.int?

/--
Definition of `isExplicitNumber` / `isExplicitNumber` 的定义

English:
definition isExplicitNumber
  signature: : Expr -> Bool

中文:
定义 isExplicitNumber
  签名: : Expr -> 布尔
-/
def isExplicitNumber : Expr -> Bool
  | .lit _ => true
  | .mdata _ e => isExplicitNumber e
  | e => e.rat?.isSome

end Lean.Expr
