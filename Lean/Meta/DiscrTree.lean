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
Find keys which match the expression, or some subexpression.

Note that repeated subexpressions will be visited each time they appear,
making this operation potentially very expensive.
It would be good to solve this problem!

Implementation: we reverse the results from `getMatch`,
so that we return lemmas matching larger subexpressions first,
and amongst those we return more specific lemmas first.
-/
/-
**Lean.Meta.DiscrTree.getSubexpressionMatches** 是 Mathlib 中的一个不透明定义，位于命名空间 `Lean
.Meta.DiscrTree`。
形式化陈述：{α : Type} → Meta.DiscrTree α → Expr → MetaM (Array α)
参数：Array α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Find keys which match the expression, or some subexpression.

Note that repeated subexpressions will be visited each time they appear,
making this operation potentially very expensive.
It would be good to solve this problem!

Implementation: we reverse the results from `getMatch`,
so that we return lemmas matching larger subexpressions first,
and amongst those we return more specific lemmas first.
-/
partial def getSubexpressionMatches {α : Type}
    (d : DiscrTree α) (e : Expr) : MetaM (Array α) := do
  match e with
  | .bvar _ => return #[]
  | .forallE _ _ _ _ => forallTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
          pure <| acc ++ (← d.getSubexpressionMatches (← inferType arg)))
        (← d.getSubexpressionMatches body).reverse)
  | .lam _ _ _ _
  | .letE _ _ _ _ _ => lambdaLetTelescope e (fun args body => do
      args.foldlM (fun acc arg => do
          pure <| acc ++ (← d.getSubexpressionMatches (← inferType arg)))
        (← d.getSubexpressionMatches body).reverse)
  | _ =>
    e.foldlM (fun a f => do
      pure <| a ++ (← d.getSubexpressionMatches f)) (← d.getMatch e).reverse

/--
Check if a `keys : Array DiscTree.Key` is "specific",
i.e. something other than `[*]` or `[=, *, *, *]`.
-/
/-
**Lean.Meta.DiscrTree.keysSpecific** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Meta.DiscrTre
e`。
形式化陈述：keysSpecific (keys : Array DiscrTree.Key) : Bool
参数：keys : Array DiscrTree.Key。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Check if a `keys : Array DiscTree.Key` is "specific",
i.e. something other than `[*]` or `[=, *, *, *]`.
-/
def keysSpecific (keys : Array DiscrTree.Key) : Bool :=
  keys != #[Key.star] && keys != #[Key.const ``Eq 3, Key.star, Key.star, Key.star]

end Lean.Meta.DiscrTree

