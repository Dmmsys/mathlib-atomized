/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init

/-!
# Additions to `Lean.Meta.DiscrTree`
-/

@[expose] public section

namespace Lean.Meta.DiscrTree

/--
Definition of `getSubexpressionMatches` / `getSubexpressionMatches` 的定义

English:
definition getSubexpressionMatches
  signature: {α : Type}
  body: do
  match e with
  | .bvar _ => return #[]
  | .forallE _ _ _ _ => forallTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
pure acc ++ (← d.getSubexpressionMatches (← inferType arg)))
        (← d.getSubexpressionMatches body).reverse)
  | .lam _ _ _ _
  | .letE _ _ _ _ _ => lam

中文:
定义 getSubexpressionMatches
  签名: {α : 类型}
  定义体: do
  match e with
  | .bvar _ => return #[]
  | .forallE _ _ _ _ => forallTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
pure acc ++ (← d.getSubexpressionMatches (← inferType arg)))
        (← d.getSubexpressionMatches body).reverse)
  | .lam _ _ _ _
  | .letE _ _ _ _ _ => lam
-/
partial def getSubexpressionMatches {α : Type}
    (d : DiscrTree α) (e : Expr) : MetaM (Array α) := do
  match e with
  | .bvar _ => return #[]
  | .forallE _ _ _ _ => forallTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
pure acc ++ (← d.getSubexpressionMatches (← inferType arg)))
        (← d.getSubexpressionMatches body).reverse)
  | .lam _ _ _ _
  | .letE _ _ _ _ _ => lambdaLetTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
pure acc ++ (← d.getSubexpressionMatches (← inferType arg)))
        (← d.getSubexpressionMatches body).reverse)
  | _ =>
    e.foldlM (fun a f => do
pure a ++ (← d.getSubexpressionMatches f)) (← d.getMatch e).reverse

/--
Definition of `keysSpecific` / `keysSpecific` 的定义

English:
definition keysSpecific
  signature: (keys : Array DiscrTree.Key)
  body: keys != #[Key.star] && keys != #[Key.const ``Eq 3, Key.star, Key.star, Key.star]

中文:
定义 keysSpecific
  签名: (keys : 数组 DiscrTree.Key)
  定义体: keys != #[Key.star] && keys != #[Key.const ``Eq 3, Key.star, Key.star, Key.star]

Depends on / 依赖: Key.const, Key.star
-/
def keysSpecific (keys : Array DiscrTree.Key) : Bool :=
  keys != #[Key.star] && keys != #[Key.const ``Eq 3, Key.star, Key.star, Key.star]

end Lean.Meta.DiscrTree
