/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Mathlib.Algebra.GroupWithZero.Nat
public meta import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Tactic.Linarith.Datatypes

/-!
# Parsing input expressions into linear form

`linarith` computes the linear form of its input expressions,
assuming (without justification) that the type of these expressions
is a commutative semiring.
It identifies atoms up to ring-equivalence: that is, `(y*3)*x` will be identified `3*(x*y)`,
where the monomial `x*y` is the linear atom.

* Variables are represented by natural numbers.
* Monomials are represented by `Monom := TreeMap ℕ ℕ`.
  The monomial `1` is represented by the empty map.
* Linear combinations of monomials are represented by `Sum := TreeMap Monom ℤ`.

All input expressions are converted to `Sum`s, preserving the map from expressions to variables.
We then discard the monomial information, mapping each distinct monomial to a natural number.
The resulting `TreeMap ℕ ℤ` represents the ring-normalized linear form of the expression.
This is ultimately converted into a `Linexp` in the obvious way.

`linearFormsAndMaxVar` is the main entry point into this file. Everything else is contained.
-/

public meta section

open Std (TreeMap)

section
open Lean Elab Tactic Meta

/--
Definition of `List.findDefeq` / `List.findDefeq` 的定义

English:
definition List.findDefeq
  signature: {v : Type} (red : TransparencyMode) (m : List (Expr × v)) (e : Expr)
  body: do
  if let some (_, n) ← m.findM? fun ⟨e', _⟩ => withTransparency red (isDefEq e e') then
    return n
  else
    failure

中文:
定义 列表.findDefeq
  签名: {v : 类型} (red : TransparencyMode) (m : 列表 (Expr × v)) (e : Expr)
  定义体: do
  if let some (_, n) ← m.findM? fun ⟨e', _⟩ => withTransparency red (isDefEq e e') then
    return n
  else
    failure
-/
def List.findDefeq {v : Type} (red : TransparencyMode) (m : List (Expr × v)) (e : Expr) :
    MetaM v := do
  if let some (_, n) ← m.findM? fun ⟨e', _⟩ => withTransparency red (isDefEq e e') then
    return n
  else
    failure
end

/--
We introduce a local instance allowing addition of `TreeMap`s,
removing any keys with value zero.
We don't need to prove anything about this addition, as it is only used in meta code.
-/
local instance {α β : Type*} {c : α -> α -> Ordering} [Add β] [Zero β] [DecidableEq β] :
    Add (TreeMap α β c) where
  add := fun f g => (f.mergeWith (fun _ b b' => b + b') g).filter (fun _ b => b != 0)

namespace Mathlib.Tactic.Linarith

/-! ### Parsing datatypes -/

/--
Definition of `Monom` / `Monom` 的定义

English:
abbreviation Monom
  signature: : Type
  body: TreeMap Nat Nat

中文:
缩写 Monom
  签名: : 类型
  定义体: TreeMap Nat Nat

Depends on / 依赖: TreeMap
-/
abbrev Monom : Type := TreeMap Nat Nat

/--
Definition of `Monom.one` / `Monom.one` 的定义

English:
definition Monom.one
  signature: : Monom
  body: TreeMap.empty

中文:
定义 Monom.one
  签名: : Monom
  定义体: TreeMap.empty

Depends on / 依赖: TreeMap, TreeMap.empty
-/
def Monom.one : Monom := TreeMap.empty

/--
Definition of `Monom.lt` / `Monom.lt` 的定义

English:
definition Monom.lt
  signature: : Monom -> Monom -> Bool
  body: fun a b =>
    ((a.keys : List Nat) < b.keys) ||
      (((a.keys : List Nat) = b.keys) && ((a.values : List Nat) < b.values))

中文:
定义 Monom.lt
  签名: : Monom -> Monom -> 布尔值
  定义体: fun a b =>
    ((a.keys : List Nat) < b.keys) ||
      (((a.keys : List Nat) = b.keys) && ((a.values : List Nat) < b.values))

Depends on / 依赖: a.keys, a.values, b.keys, b.values, values
-/
def Monom.lt : Monom -> Monom -> Bool :=
  fun a b =>
    ((a.keys : List Nat) < b.keys) ||
      (((a.keys : List Nat) = b.keys) && ((a.values : List Nat) < b.values))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ord Monom
  body: if x.lt y then .lt else if x == y then .eq else .gt

中文:
实例 :
  签名: 序 Monom
  定义体: if x.lt y then .lt else if x == y then .eq else .gt

Depends on / 依赖: x.lt
-/
instance : Ord Monom where
  compare x y := if x.lt y then .lt else if x == y then .eq else .gt

/--
Definition of `Sum` / `Sum` 的定义

English:
abbreviation Sum
  signature: : Type
  body: TreeMap Monom Int

中文:
缩写 和
  签名: : 类型
  定义体: TreeMap Monom Int

Depends on / 依赖: TreeMap
-/
abbrev Sum : Type := TreeMap Monom Int

/--
Definition of `Sum.one` / `Sum.one` 的定义

English:
definition Sum.one
  signature: : Sum
  body: TreeMap.empty.insert Monom.one 1

中文:
定义 和.one
  签名: : 和
  定义体: TreeMap.empty.insert Monom.one 1

Depends on / 依赖: Monom.one, TreeMap, TreeMap.empty.insert, insert
-/
def Sum.one : Sum := TreeMap.empty.insert Monom.one 1

/--
Definition of `Sum.scaleByMonom` / `Sum.scaleByMonom` 的定义

English:
definition Sum.scaleByMonom
  signature: (s : Sum) (m : Monom)
  body: s.foldr (fun m' coeff sm => sm.insert (m + m') coeff) TreeMap.empty

中文:
定义 和.scaleByMonom
  签名: (s : 和) (m : Monom)
  定义体: s.foldr (fun m' coeff sm => sm.insert (m + m') coeff) TreeMap.empty

Depends on / 依赖: TreeMap, TreeMap.empty, insert, s.foldr, sm.insert
-/
def Sum.scaleByMonom (s : Sum) (m : Monom) : Sum :=
  s.foldr (fun m' coeff sm => sm.insert (m + m') coeff) TreeMap.empty

/--
Definition of `Sum.mul` / `Sum.mul` 的定义

English:
definition Sum.mul
  signature: (s1 s2 : Sum)
  body: s1.foldr (fun mn coeff sm => sm + ((s2.scaleByMonom mn).map (fun _ v => v * coeff)))
    TreeMap.empty

中文:
定义 和.mul
  签名: (s1 s2 : 和)
  定义体: s1.foldr (fun mn coeff sm => sm + ((s2.scaleByMonom mn).map (fun _ v => v * coeff)))
    TreeMap.empty

Depends on / 依赖: TreeMap, TreeMap.empty, s1.foldr, s2.scaleByMonom, scaleByMonom
-/
def Sum.mul (s1 s2 : Sum) : Sum :=
  s1.foldr (fun mn coeff sm => sm + ((s2.scaleByMonom mn).map (fun _ v => v * coeff)))
    TreeMap.empty

/--
Definition of `Sum.pow` / `Sum.pow` 的定义

English:
definition Sum.pow
  signature: (s : Sum)
  body: n >>> 1
    let a := s.pow m
    if n &&& 1 = 0 then
      a.mul a
    else
.mul s a.mul a

中文:
定义 和.pow
  签名: (s : 和)
  定义体: n >>> 1
    let a := s.pow m
    if n &&& 1 = 0 then
      a.mul a
    else
.mul s a.mul a
-/
partial def Sum.pow (s : Sum) : Nat -> Sum
  | 0 => Sum.one
  | 1 => s
  | n =>
    let m := n >>> 1
    let a := s.pow m
    if n &&& 1 = 0 then
      a.mul a
    else
.mul s a.mul a

/--
Definition of `SumOfMonom` / `SumOfMonom` 的定义

English:
definition SumOfMonom
  signature: (m : Monom)
  body: TreeMap.empty.insert m 1

中文:
定义 SumOfMonom
  签名: (m : Monom)
  定义体: TreeMap.empty.insert m 1

Depends on / 依赖: TreeMap, TreeMap.empty.insert, insert
-/
def SumOfMonom (m : Monom) : Sum :=
  TreeMap.empty.insert m 1

/--
Definition of `one` / `one` 的定义

English:
definition one
  signature: : Monom
  body: TreeMap.empty

中文:
定义 one
  签名: : Monom
  定义体: TreeMap.empty

Depends on / 依赖: TreeMap, TreeMap.empty
-/
def one : Monom := TreeMap.empty

/--
Definition of `scalar` / `scalar` 的定义

English:
definition scalar
  signature: (z : Int)
  body: TreeMap.empty.insert one z

中文:
定义 scalar
  签名: (z : 整数)
  定义体: TreeMap.empty.insert one z

Depends on / 依赖: TreeMap, TreeMap.empty.insert, insert
-/
def scalar (z : Int) : Sum :=
  TreeMap.empty.insert one z

/--
Definition of `var` / `var` 的定义

English:
definition var
  signature: (n : Nat)
  body: TreeMap.empty.insert (TreeMap.empty.insert n 1) 1

中文:
定义 var
  签名: (n : 自然数)
  定义体: TreeMap.empty.insert (TreeMap.empty.insert n 1) 1

Depends on / 依赖: TreeMap, TreeMap.empty.insert, insert
-/
def var (n : Nat) : Sum :=
  TreeMap.empty.insert (TreeMap.empty.insert n 1) 1


/-! ### Parsing algorithms -/

open Lean Elab Tactic Meta

-- The natural number is just the index in the list,
-- and we could reimplement to just use `List Expr` if desired.
/--
Definition of `ExprMap` / `ExprMap` 的定义

English:
abbreviation ExprMap
  body: List (Expr × Nat)

中文:
缩写 ExprMap
  定义体: List (Expr × Nat)
-/
abbrev ExprMap := List (Expr × Nat)

/--
Definition of `linearFormOfAtom` / `linearFormOfAtom` 的定义

English:
definition linearFormOfAtom
  signature: (red : TransparencyMode) (m : ExprMap) (e : Expr)
  body: do
  try
    let k ← m.findDefeq red e
    return (m, var k)
  catch _ =>
    let n := m.length + 1
    return ((e, n)::m, var n)

中文:
定义 linearFormOfAtom
  签名: (red : TransparencyMode) (m : ExprMap) (e : Expr)
  定义体: do
  try
    let k ← m.findDefeq red e
    return (m, var k)
  catch _ =>
    let n := m.length + 1
    return ((e, n)::m, var n)
-/
def linearFormOfAtom (red : TransparencyMode) (m : ExprMap) (e : Expr) : MetaM (ExprMap × Sum) := do
  try
    let k ← m.findDefeq red e
    return (m, var k)
  catch _ =>
    let n := m.length + 1
    return ((e, n)::m, var n)


/--
Definition of `linearFormOfExpr` / `linearFormOfExpr` 的定义

English:
definition linearFormOfExpr
  signature: (red : TransparencyMode) (m : ExprMap) (e : Expr)
  body: do
  let e ← whnfR e
  match e.numeral? with
  | some 0 => return ⟨m, TreeMap.empty⟩
  | some (n + 1) => return ⟨m, scalar (n + 1)⟩
  | none =>
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormO

中文:
定义 linearFormOfExpr
  签名: (red : TransparencyMode) (m : ExprMap) (e : Expr)
  定义体: do
  let e ← whnfR e
  match e.numeral? with
  | some 0 => return ⟨m, TreeMap.empty⟩
  | some (n + 1) => return ⟨m, scalar (n + 1)⟩
  | none =>
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormO
-/
partial def linearFormOfExpr (red : TransparencyMode) (m : ExprMap) (e : Expr) :
    MetaM (ExprMap × Sum) := do
  let e ← whnfR e
  match e.numeral? with
  | some 0 => return ⟨m, TreeMap.empty⟩
  | some (n + 1) => return ⟨m, scalar (n + 1)⟩
  | none =>
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormOfExpr red m1 e2
    return (m2, comp1.mul comp2)
  | (``HAdd.hAdd, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormOfExpr red m1 e2
    return (m2, comp1 + comp2)
  | (``HSub.hSub, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormOfExpr red m1 e2
    return (m2, comp1 + comp2.map (fun _ v => -v))
  | (``Neg.neg, #[_, _, e]) => do
    let (m1, comp) ← linearFormOfExpr red m e
    return (m1, comp.map (fun _ v => -v))
  | (``HPow.hPow, #[_, _, _, _, a, n]) => do
    match n.numeral? with
    | some n => do
      let (m1, comp) ← linearFormOfExpr red m a
      return (m1, comp.pow n)
    | none => linearFormOfAtom red m e
  | _ => linearFormOfAtom red m e

/--
Definition of `elimMonom` / `elimMonom` 的定义

English:
definition elimMonom
  signature: (s : Sum) (m : TreeMap Monom Nat)
  body: s.foldr (fun mn coeff ⟨map, out⟩ =>
    match map[mn]? with
    | some n => ⟨map, out.insert n coeff⟩
    | none =>
      let n := map.size
      ⟨map.insert mn n, out.insert n coeff⟩)
    (m, TreeMap.empty)

中文:
定义 elimMonom
  签名: (s : 和) (m : TreeMap Monom 自然数)
  定义体: s.foldr (fun mn coeff ⟨map, out⟩ =>
    match map[mn]? with
    | some n => ⟨map, out.insert n coeff⟩
    | none =>
      let n := map.size
      ⟨map.insert mn n, out.insert n coeff⟩)
    (m, TreeMap.empty)

Depends on / 依赖: TreeMap, TreeMap.empty, insert, map.insert, map.size, out.insert, s.foldr
-/
def elimMonom (s : Sum) (m : TreeMap Monom Nat) : TreeMap Monom Nat × TreeMap Nat Int :=
  s.foldr (fun mn coeff ⟨map, out⟩ =>
    match map[mn]? with
    | some n => ⟨map, out.insert n coeff⟩
    | none =>
      let n := map.size
      ⟨map.insert mn n, out.insert n coeff⟩)
    (m, TreeMap.empty)

/--
Definition of `toComp` / `toComp` 的定义

English:
definition toComp
  signature: (red : TransparencyMode) (e : Expr) (e_map : ExprMap) (monom_map : TreeMap Monom Nat)
  body: do
  let (iq, e) ← parseCompAndExpr e
  let (m', comp') ← linearFormOfExpr red e_map e
  let ⟨nm, mm'⟩ := elimMonom comp' monom_map
  -- Note: we use `.reverse` as `Linexp.get` assumes the monomial are in descending order
  return ⟨⟨iq, mm'.toList.reverse⟩, m', nm⟩

中文:
定义 toComp
  签名: (red : TransparencyMode) (e : Expr) (e_map : ExprMap) (monom_map : TreeMap Monom 自然数)
  定义体: do
  let (iq, e) ← parseCompAndExpr e
  let (m', comp') ← linearFormOfExpr red e_map e
  let ⟨nm, mm'⟩ := elimMonom comp' monom_map
  -- Note: we use `.reverse` as `Linexp.get` assumes the monomial are in descending order
  return ⟨⟨iq, mm'.toList.reverse⟩, m', nm⟩
-/
def toComp (red : TransparencyMode) (e : Expr) (e_map : ExprMap) (monom_map : TreeMap Monom Nat) :
    MetaM (Comp × ExprMap × TreeMap Monom Nat) := do
  let (iq, e) ← parseCompAndExpr e
  let (m', comp') ← linearFormOfExpr red e_map e
  let ⟨nm, mm'⟩ := elimMonom comp' monom_map
  -- Note: we use `.reverse` as `Linexp.get` assumes the monomial are in descending order
  return ⟨⟨iq, mm'.toList.reverse⟩, m', nm⟩

/--
Definition of `toCompFold` / `toCompFold` 的定义

English:
definition toCompFold
  signature: (red : TransparencyMode)

中文:
定义 toCompFold
  签名: (red : TransparencyMode)
-/
def toCompFold (red : TransparencyMode) : ExprMap -> List Expr -> TreeMap Monom Nat ->
    MetaM (List Comp × ExprMap × TreeMap Monom Nat)
| m, [], mm => return ([], m, mm)
| m, (h::t), mm => do
    let (c, m', mm') ← toComp red h m mm
    let (l, mp, mm') ← toCompFold red m' t mm'
    return (c::l, mp, mm')

/--
Definition of `linearFormsAndMaxVar` / `linearFormsAndMaxVar` 的定义

English:
definition linearFormsAndMaxVar
  signature: (red : TransparencyMode) (pfs : List Expr)
  body: do
  let pftps ← (pfs.mapM inferType)
  let (l, _, map) ← toCompFold red [] pftps TreeMap.empty
  trace[linarith.detail] "monomial map: {map.toList.map fun ⟨k,v⟩ => (k.toList, v)}"
  return (l, map.size - 1)

中文:
定义 linearFormsAndMaxVar
  签名: (red : TransparencyMode) (pfs : 列表 Expr)
  定义体: do
  let pftps ← (pfs.mapM inferType)
  let (l, _, map) ← toCompFold red [] pftps TreeMap.empty
  trace[linarith.detail] "monomial map: {map.toList.map fun ⟨k,v⟩ => (k.toList, v)}"
  return (l, map.size - 1)
-/
def linearFormsAndMaxVar (red : TransparencyMode) (pfs : List Expr) :
    MetaM (List Comp × Nat) := do
  let pftps ← (pfs.mapM inferType)
  let (l, _, map) ← toCompFold red [] pftps TreeMap.empty
  trace[linarith.detail] "monomial map: {map.toList.map fun ⟨k,v⟩ => (k.toList, v)}"
  return (l, map.size - 1)

end Mathlib.Tactic.Linarith
