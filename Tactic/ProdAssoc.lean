/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public meta import Mathlib.Lean.Expr.Basic
public import Mathlib.Logic.Equiv.Defs
public meta import Mathlib.Tactic.Simps.Basic

/-!
# Associativity of products

This file constructs a term elaborator for "obvious" equivalences between iterated products.
For example,
```lean
(prod_assoc% : (α × β) × (γ × δ) ≃ α × (β × γ) × δ)
```
gives the "obvious" equivalence between `(α × β) × (γ × δ)` and `α × (β × γ) × δ`.
-/

public meta section

namespace Lean.Expr

open Lean Meta

/--
Inductive type `ProdTree` / 归纳类型 `ProdTree`

English:
inductive ProdTree
  parameters: where
  constructors (2):
    - type: (tp : Expr) (l : Level)
    - prod: (fst snd : ProdTree) (lfst lsnd : Level)

中文:
归纳类型 ProdTree
  参数: where
  构造子 (2 个):
    - type: (tp : Expr) (l : Level)
    - prod: (fst snd : ProdTree) (lfst lsnd : Level)
-/
inductive ProdTree where
  | type (tp : Expr) (l : Level)
  | prod (fst snd : ProdTree) (lfst lsnd : Level)
deriving Repr

/--
Definition of `ProdTree.getType` / `ProdTree.getType` 的定义

English:
definition ProdTree.getType
  signature: : ProdTree -> Expr

中文:
定义 ProdTree.getType
  签名: : ProdTree -> Expr
-/
def ProdTree.getType : ProdTree -> Expr
  | type tp _ => tp
  | prod fst snd u v => mkAppN (.const ``Prod [u,v]) #[fst.getType, snd.getType]

/--
Definition of `ProdTree.size` / `ProdTree.size` 的定义

English:
definition ProdTree.size
  signature: : ProdTree -> Nat

中文:
定义 ProdTree.size
  签名: : ProdTree -> 自然数
-/
def ProdTree.size : ProdTree -> Nat
  | type _ _ => 1
  | prod fst snd _ _ => fst.size + snd.size

/--
Definition of `ProdTree.components` / `ProdTree.components` 的定义

English:
definition ProdTree.components
  signature: : ProdTree -> List Expr

中文:
定义 ProdTree.components
  签名: : ProdTree -> List Expr

Depends on / 依赖: X.mkProdTree, Y.mkProdTree, consumeMData, e.consumeMData, indentExpr, inferType, mkProdTree, return, throwError
-/
def ProdTree.components : ProdTree -> List Expr
  | type tp _ => [tp]
  | prod fst snd _ _ => fst.components ++ snd.components

/--
Definition of `mkProdTree` / `mkProdTree` 的定义

English:
definition mkProdTree
  signature: (e : Expr)
  body: match e.consumeMData with
    | .app (.app (.const ``Prod [u,v]) X) Y => do
        return .prod (← X.mkProdTree) (← Y.mkProdTree) u v
    | X => do
      let some u := (← whnfD <| ← inferType X).type? | throwError "Not a type{indentExpr X}"
      return .type X u

中文:
定义 mkProdTree
  签名: (e : Expr)
  定义体: match e.consumeMData with
    | .app (.app (.const ``Prod [u,v]) X) Y => do
        return .prod (← X.mkProdTree) (← Y.mkProdTree) u v
    | X => do
      let some u := (← whnfD <| ← inferType X).type? | throwError "Not a type{indentExpr X}"
      return .type X u
-/
partial def mkProdTree (e : Expr) : MetaM ProdTree :=
  match e.consumeMData with
    | .app (.app (.const ``Prod [u,v]) X) Y => do
        return .prod (← X.mkProdTree) (← Y.mkProdTree) u v
    | X => do
      let some u := (← whnfD <| ← inferType X).type? | throwError "Not a type{indentExpr X}"
      return .type X u

/--
Definition of `ProdTree.unpack` / `ProdTree.unpack` 的定义

English:
definition ProdTree.unpack
  signature: (t : Expr)

中文:
定义 ProdTree.unpack
  签名: (t : Expr)
-/
def ProdTree.unpack (t : Expr) : ProdTree -> MetaM (List Expr)
  | type _ _ => return [t]
  | prod fst snd u v => do
let fst' ← fst.unpack mkAppN (.const ``Prod.fst [u,v]) #[fst.getType, snd.getType, t]
let snd' ← snd.unpack mkAppN (.const ``Prod.snd [u,v]) #[fst.getType, snd.getType, t]
      return fst' ++ snd'

/--
Definition of `ProdTree.pack` / `ProdTree.pack` 的定义

English:
definition ProdTree.pack
  signature: (ts : List Expr)
  body: fst.size
    let sndSize := snd.size
    unless ts.length == fstSize + sndSize do throwError "Failed due to size mismatch."
.toArray.toList let tsfst := ts.toArray[:fstSize]
.toArray.toList let tssnd := ts.toArray[fstSize:]
    let mk : Expr := mkAppN (.const ``Prod.mk [u,v]) #[fst.getType, snd.getT

中文:
定义 ProdTree.pack
  签名: (ts : List Expr)
  定义体: fst.size
    let sndSize := snd.size
    unless ts.length == fstSize + sndSize do throwError "Failed due to size mismatch."
.toArray.toList let tsfst := ts.toArray[:fstSize]
.toArray.toList let tssnd := ts.toArray[fstSize:]
    let mk : Expr := mkAppN (.const ``Prod.mk [u,v]) #[fst.getType, snd.getT

Depends on / 依赖: fst.size
-/
def ProdTree.pack (ts : List Expr) : ProdTree -> MetaM Expr
  | type _ _ => do
    match ts with
      | [] => throwError "Can't pack the empty list."
      | [a] => return a
      | _ => throwError "Failed due to size mismatch."
  | prod fst snd u v => do
    let fstSize := fst.size
    let sndSize := snd.size
    unless ts.length == fstSize + sndSize do throwError "Failed due to size mismatch."
.toArray.toList let tsfst := ts.toArray[:fstSize]
.toArray.toList let tssnd := ts.toArray[fstSize:]
    let mk : Expr := mkAppN (.const ``Prod.mk [u,v]) #[fst.getType, snd.getType]
    return .app (.app mk (← fst.pack tsfst)) (← snd.pack tssnd)

/--
Definition of `ProdTree.convertTo` / `ProdTree.convertTo` 的定义

English:
definition ProdTree.convertTo
  signature: (P1 P2 : ProdTree) (e : Expr)
  body: return ← P2.pack ← P1.unpack e

中文:
定义 ProdTree.convertTo
  签名: (P1 P2 : ProdTree) (e : Expr)
  定义体: return ← P2.pack ← P1.unpack e

Depends on / 依赖: P1.unpack, P2.pack, return, unpack
-/
def ProdTree.convertTo (P1 P2 : ProdTree) (e : Expr) : MetaM Expr :=
return ← P2.pack ← P1.unpack e

/--
Definition of `mkProdFun` / `mkProdFun` 的定义

English:
definition mkProdFun
  signature: (a b : Expr)
  body: do
  let pa ← a.mkProdTree
  let pb ← b.mkProdTree
  unless pa.components.length == pb.components.length do
    throwError "The number of components in{indentD a}\nand{indentD b}\nmust match."
  for (x,y) in pa.components.zip pb.components do
    unless ← isDefEq x y do
      throwError "Component{i

中文:
定义 mkProdFun
  签名: (a b : Expr)
  定义体: do
  let pa ← a.mkProdTree
  let pb ← b.mkProdTree
  unless pa.components.length == pb.components.length do
    throwError "The number of components in{indentD a}\nand{indentD b}\nmust match."
  for (x,y) in pa.components.zip pb.components do
    unless ← isDefEq x y do
      throwError "Component{i
-/
def mkProdFun (a b : Expr) : MetaM Expr := do
  let pa ← a.mkProdTree
  let pb ← b.mkProdTree
  unless pa.components.length == pb.components.length do
    throwError "The number of components in{indentD a}\nand{indentD b}\nmust match."
  for (x,y) in pa.components.zip pb.components do
    unless ← isDefEq x y do
      throwError "Component{indentD x}\nis not definitionally equal to component{indentD y}."
  withLocalDeclD `t a fun fvar => do
    mkLambdaFVars #[fvar] (← pa.convertTo pb fvar)

/--
Definition of `mkProdEquiv` / `mkProdEquiv` 的定义

English:
definition mkProdEquiv
  signature: (a b : Expr)
  body: do
  let some u := (← whnfD <| ← inferType a).type? | throwError "Not a type{indentExpr a}"
  let some v := (← whnfD <| ← inferType b).type? | throwError "Not a type{indentExpr b}"
  return mkAppN (.const ``Equiv.mk [.succ u,.succ v])
    #[a, b, ← mkProdFun a b, ← mkProdFun b a,
      .app (.const 

中文:
定义 mkProdEquiv
  签名: (a b : Expr)
  定义体: do
  let some u := (← whnfD <| ← inferType a).type? | throwError "Not a type{indentExpr a}"
  let some v := (← whnfD <| ← inferType b).type? | throwError "Not a type{indentExpr b}"
  return mkAppN (.const ``Equiv.mk [.succ u,.succ v])
    #[a, b, ← mkProdFun a b, ← mkProdFun b a,
      .app (.const 
-/
def mkProdEquiv (a b : Expr) : MetaM Expr := do
  let some u := (← whnfD <| ← inferType a).type? | throwError "Not a type{indentExpr a}"
  let some v := (← whnfD <| ← inferType b).type? | throwError "Not a type{indentExpr b}"
  return mkAppN (.const ``Equiv.mk [.succ u,.succ v])
    #[a, b, ← mkProdFun a b, ← mkProdFun b a,
      .app (.const ``rfl [.succ u]) a,
      .app (.const ``rfl [.succ v]) b]

/-- IMPLEMENTATION: Syntax used in the implementation of `prod_assoc%`.
This elaborator postpones if there are metavariables in the expected type,
and to propagate the fact that this elaborator produces an `Equiv`,
the `prod_assoc%` macro sets things up with a type ascription.
This enables using `prod_assoc%` with, for example `Equiv.trans` dot notation. -/
syntax (name := prodAssocStx) "prod_assoc_internal%" : term

open Elab Term in
/-- Elaborator for `prod_assoc%`. -/
@[term_elab prodAssocStx]
/--
Definition of `elabProdAssoc` / `elabProdAssoc` 的定义

English:
definition elabProdAssoc
  signature: : TermElab
  body: fun stx expectedType? => do
  match stx with
  | `(prod_assoc_internal%) => do
    let some expectedType ← tryPostponeIfHasMVars? expectedType?
          | throwError "expected type must be known"
    let .app (.app (.const ``Equiv _) a) b := expectedType
          | throwError "Expected type{indent

中文:
定义 elabProdAssoc
  签名: : TermElab
  定义体: fun stx expectedType? => do
  match stx with
  | `(prod_assoc_internal%) => do
    let some expectedType ← tryPostponeIfHasMVars? expectedType?
          | throwError "expected type must be known"
    let .app (.app (.const ``Equiv _) a) b := expectedType
          | throwError "Expected type{indent

Depends on / 依赖: expectedType
-/
def elabProdAssoc : TermElab := fun stx expectedType? => do
  match stx with
  | `(prod_assoc_internal%) => do
    let some expectedType ← tryPostponeIfHasMVars? expectedType?
          | throwError "expected type must be known"
    let .app (.app (.const ``Equiv _) a) b := expectedType
          | throwError "Expected type{indentD expectedType}\nis not of the form `α ≃ β`."
    mkProdEquiv a b
  | _ => throwUnsupportedSyntax

/--
`prod_assoc%` elaborates to the "obvious" equivalence between iterated products of types,
regardless of how the products are parenthesized.
The `prod_assoc%` term uses the expected type when elaborating.
For example, `(prod_assoc% : (α × β) × (γ × δ) ≃ α × (β × γ) × δ)`.

The elaborator can handle holes in the expected type,
so long as they eventually get filled by unification.
```lean
example : (α × β) × (γ × δ) ≃ α × (β × γ) × δ :=
  (prod_assoc% : _ ≃ α × β × γ × δ).trans prod_assoc%
```
-/
macro "prod_assoc%" : term => `((prod_assoc_internal% : _ ≃ _))

end Lean.Expr
