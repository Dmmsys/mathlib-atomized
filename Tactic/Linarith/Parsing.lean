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
`findDefeq red m e` looks for a key in `m` that is defeq to `e` (up to transparency `red`),
and returns the value associated with this key if it exists.
Otherwise, it fails.
-/
/-
**List.findDefeq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：List.findDefeq {v : Type} (red : TransparencyMode) (m : List (Expr × v)) (
e : Expr) : MetaM v
参数：red : TransparencyMode；m : List (Expr × v)；e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`findDefeq red m e` looks for a key in `m` that is defeq to `e` (up to transpare
ncy `red`),
and returns the value associated with this key if it exists.
Otherwise, it fails.
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
local instance {α β : Type*} {c : α → α → Ordering} [Add β] [Zero β] [DecidableEq β] :
    Add (TreeMap α β c) where
  add := fun f g => (f.mergeWith (fun _ b b' => b + b') g).filter (fun _ b => b ≠ 0)

namespace Mathlib.Tactic.Linarith

/-! ### Parsing datatypes -/

/-- Variables (represented by natural numbers) map to their power. -/
/-
**Mathlib.Tactic.Linarith.Monom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Tactic.Lina
rith`。
形式化陈述：Monom : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variables (represented by natural numbers) map to their power.
-/
abbrev Monom : Type := TreeMap ℕ ℕ

/-- `1` is represented by the empty monomial, the product of no variables. -/
/-
**Mathlib.Tactic.Linarith.Monom.one** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Li
narith.Monom`。
形式化陈述：Mathlib.Tactic.Linarith.Monom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`1` is represented by the empty monomial, the product of no variables.
-/
def Monom.one : Monom := TreeMap.empty

/-- Compare monomials by first comparing their keys and then their powers. -/
/-
**Mathlib.Tactic.Linarith.Monom.lt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Lin
arith.Monom`。
形式化陈述：Mathlib.Tactic.Linarith.Monom → Mathlib.Tactic.Linarith.Monom → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compare monomials by first comparing their keys and then their powers.
-/
def Monom.lt : Monom → Monom → Bool :=
  fun a b =>
    ((a.keys : List ℕ) < b.keys) ||
      (((a.keys : List ℕ) = b.keys) && ((a.values : List ℕ) < b.values))
/-
**Mathlib.Tactic.Linarith.** 是 Mathlib 中的一个实例，位于命名空间 `Mathlib.Tactic.Linarith`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ord Monom where
  compare x y := if x.lt y then .lt else if x == y then .eq else .gt

/-- Linear combinations of monomials are represented by mapping monomials to coefficients. -/
/-
**Mathlib.Tactic.Linarith.Sum** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Tactic.Linari
th`。
形式化陈述：Sum : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear combinations of monomials are represented by mapping monomials to coeffic
ients.
-/
abbrev Sum : Type := TreeMap Monom ℤ

/-- `1` is represented as the singleton sum of the monomial `Monom.one` with coefficient 1. -/
/-
**Mathlib.Tactic.Linarith.Sum.one** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Lina
rith.Sum`。
形式化陈述：Mathlib.Tactic.Linarith.Sum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`1` is represented as the singleton sum of the monomial `Monom.one` with coeffic
ient 1.
-/
def Sum.one : Sum := TreeMap.empty.insert Monom.one 1

/-- `Sum.scaleByMonom s m` multiplies every monomial in `s` by `m`. -/
/-
**Mathlib.Tactic.Linarith.Sum.scaleByMonom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ta
ctic.Linarith.Sum`。
形式化陈述：Mathlib.Tactic.Linarith.Sum → Mathlib.Tactic.Linarith.Monom → Mathlib.Tact
ic.Linarith.Sum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sum.scaleByMonom s m` multiplies every monomial in `s` by `m`.
-/
def Sum.scaleByMonom (s : Sum) (m : Monom) : Sum :=
  s.foldr (fun m' coeff sm => sm.insert (m + m') coeff) TreeMap.empty

/-- `sum.mul s1 s2` distributes the multiplication of two sums. -/
/-
**Mathlib.Tactic.Linarith.Sum.mul** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Lina
rith.Sum`。
形式化陈述：Mathlib.Tactic.Linarith.Sum → Mathlib.Tactic.Linarith.Sum → Mathlib.Tactic
.Linarith.Sum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sum.mul s1 s2` distributes the multiplication of two sums.
-/
def Sum.mul (s1 s2 : Sum) : Sum :=
  s1.foldr (fun mn coeff sm => sm + ((s2.scaleByMonom mn).map (fun _ v => v * coeff)))
    TreeMap.empty

/-- The `n`th power of `s : Sum` is the `n`-fold product of `s`, with `s.pow 0 = Sum.one`. -/
/-
**Mathlib.Tactic.Linarith.Sum.pow** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tactic.L
inarith.Sum`。
形式化陈述：Mathlib.Tactic.Linarith.Sum → ℕ → Mathlib.Tactic.Linarith.Sum
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th power of `s : Sum` is the `n`-fold product of `s`, with `s.pow 0 = Sum
.one`.
-/
partial def Sum.pow (s : Sum) : ℕ → Sum
  | 0 => Sum.one
  | 1 => s
  | n =>
    let m := n >>> 1
    let a := s.pow m
    if n &&& 1 = 0 then
      a.mul a
    else
      a.mul a |>.mul s

/-- `SumOfMonom m` lifts `m` to a sum with coefficient `1`. -/
/-
**Mathlib.Tactic.Linarith.SumOfMonom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.L
inarith`。
形式化陈述：SumOfMonom (m : Monom) : Sum
参数：m : Monom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SumOfMonom m` lifts `m` to a sum with coefficient `1`.
-/
def SumOfMonom (m : Monom) : Sum :=
  TreeMap.empty.insert m 1

/-- The unit monomial `one` is represented by the empty TreeMap. -/
/-
**Mathlib.Tactic.Linarith.one** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Linarith
`。
形式化陈述：one : Monom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit monomial `one` is represented by the empty TreeMap.
-/
def one : Monom := TreeMap.empty

/-- A scalar `z` is represented by a `Sum` with coefficient `z` and monomial `one` -/
/-
**Mathlib.Tactic.Linarith.scalar** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Linar
ith`。
形式化陈述：scalar (z : Int) : Sum
参数：z : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scalar `z` is represented by a `Sum` with coefficient `z` and monomial `one`
-/
def scalar (z : ℤ) : Sum :=
  TreeMap.empty.insert one z

/-- A single variable `n` is represented by a sum with coefficient `1` and monomial `n`. -/
/-
**Mathlib.Tactic.Linarith.var** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Linarith
`。
形式化陈述：var (n : Nat) : Sum
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A single variable `n` is represented by a sum with coefficient `1` and monomial 
`n`.
-/
def var (n : ℕ) : Sum :=
  TreeMap.empty.insert (TreeMap.empty.insert n 1) 1


/-! ### Parsing algorithms -/

open Lean Elab Tactic Meta

/--
`ExprMap` is used to record atomic expressions which have been seen while processing inequality
expressions.
-/
-- The natural number is just the index in the list,
-- and we could reimplement to just use `List Expr` if desired.
/-
**Mathlib.Tactic.Linarith.ExprMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Tactic.Li
narith`。
形式化陈述：ExprMap
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev ExprMap := List (Expr × ℕ)

/--
`linearFormOfAtom red map e` is the atomic case for `linear_form_of_expr`.
If `e` appears with index `k` in `map`, it returns the singleton sum `var k`.
Otherwise it updates `map`, adding `e` with index `n`, and returns the singleton sum `var n`.
-/
/-
**Mathlib.Tactic.Linarith.linearFormOfAtom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ta
ctic.Linarith`。
形式化陈述：linearFormOfAtom (red : TransparencyMode) (m : ExprMap) (e : Expr) : MetaM
 (ExprMap × Sum)
参数：red : TransparencyMode；m : ExprMap；e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`linearFormOfAtom red map e` is the atomic case for `linear_form_of_expr`.
If `e` appears with index `k` in `map`, it returns the singleton sum `var k`.
Otherwise it updates `map`, adding `e` with index `n`, and returns the singleton
 sum `var n`.
-/
def linearFormOfAtom (red : TransparencyMode) (m : ExprMap) (e : Expr) : MetaM (ExprMap × Sum) := do
  try
    let k ← m.findDefeq red e
    return (m, var k)
  catch _ =>
    let n := m.length + 1
    return ((e, n)::m, var n)

/--
`linearFormOfExpr red map e` computes the linear form of `e`.

`map` is a lookup map from atomic expressions to variable numbers.
If a new atomic expression is encountered, it is added to the map with a new number.
It matches atomic expressions up to reducibility given by `red`.

Because it matches up to definitional equality, this function must be in the `MetaM` monad,
and forces some functions that call it into `MetaM` as well.
-/

/-
**Mathlib.Tactic.Linarith.linearFormOfExpr** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib
.Tactic.Linarith`。
形式化陈述：Meta.TransparencyMode →   Mathlib.Tactic.Linarith.ExprMap → Expr → MetaM (
Mathlib.Tactic.Linarith.ExprMap × Mathlib.Tactic.Linarith.Sum)
参数：Mathlib.Tactic.Linarith.ExprMap × Mathlib.Tactic.Linarith.Sum。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`linearFormOfExpr red map e` computes the linear form of `e`.

`map` is a lookup map from atomic expressions to variable numbers.
If a new atomic expression is encountered, it is added to the map with a new num
ber.
It matches atomic expressions up to reducibility given by `red`.

Because it matches up to definitional equality, this function must be in the `Me
taM` monad,
and forces some functions that call it into `MetaM` as well.
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
`elimMonom s map` eliminates the monomial level of the `Sum` `s`.

`map` is a lookup map from monomials to variable numbers.
The output `TreeMap ℕ ℤ` has the same structure as `s : Sum`,
but each monomial key is replaced with its index according to `map`.
If any new monomials are encountered, they are assigned variable numbers and `map` is updated.
-/
/-
**Mathlib.Tactic.Linarith.elimMonom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Li
narith`。
形式化陈述：elimMonom (s : Sum) (m : TreeMap Monom Nat) : TreeMap Monom Nat × TreeMap 
Nat Int
参数：s : Sum；m : TreeMap Monom Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`elimMonom s map` eliminates the monomial level of the `Sum` `s`.

`map` is a lookup map from monomials to variable numbers.
The output `TreeMap ℕ ℤ` has the same structure as `s : Sum`,
but each monomial key is replaced with its index according to `map`.
If any new monomials are encountered, they are assigned variable numbers and `ma
p` is updated.
-/
def elimMonom (s : Sum) (m : TreeMap Monom ℕ) : TreeMap Monom ℕ × TreeMap ℕ ℤ :=
  s.foldr (fun mn coeff ⟨map, out⟩ ↦
    match map[mn]? with
    | some n => ⟨map, out.insert n coeff⟩
    | none =>
      let n := map.size
      ⟨map.insert mn n, out.insert n coeff⟩)
    (m, TreeMap.empty)

/--
`toComp red e e_map monom_map` converts an expression of the form `t < 0`, `t ≤ 0`, or `t = 0`
into a `comp` object.

`e_map` maps atomic expressions to indices; `monom_map` maps monomials to indices.
Both of these are updated during processing and returned.
-/
/-
**Mathlib.Tactic.Linarith.toComp** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.Linar
ith`。
形式化陈述：toComp (red : TransparencyMode) (e : Expr) (e_map : ExprMap) (monom_map : 
TreeMap Monom Nat) : MetaM (Comp × ExprMap × TreeMap Monom Nat)
参数：red : TransparencyMode；e : Expr；e_map : ExprMap；monom_map : TreeMap Monom Nat
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toComp red e e_map monom_map` converts an expression of the form `t < 0`, `t ≤ 
0`, or `t = 0`
into a `comp` object.

`e_map` maps atomic expressions to indices; `monom_map` maps monomials to indice
s.
Both of these are updated during processing and returned.
-/
def toComp (red : TransparencyMode) (e : Expr) (e_map : ExprMap) (monom_map : TreeMap Monom ℕ) :
    MetaM (Comp × ExprMap × TreeMap Monom ℕ) := do
  let (iq, e) ← parseCompAndExpr e
  let (m', comp') ← linearFormOfExpr red e_map e
  let ⟨nm, mm'⟩ := elimMonom comp' monom_map
  -- Note: we use `.reverse` as `Linexp.get` assumes the monomial are in descending order
  return ⟨⟨iq, mm'.toList.reverse⟩, m', nm⟩

/--
`toCompFold red e_map exprs monom_map` folds `toComp` over `exprs`,
updating `e_map` and `monom_map` as it goes.
-/
/-
**Mathlib.Tactic.Linarith.toCompFold** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.L
inarith`。
形式化陈述：Meta.TransparencyMode →   Mathlib.Tactic.Linarith.ExprMap →     List Expr 
→       Std.TreeMap Mathlib.Tactic.Linarith.Monom ℕ compare →         MetaM     
      (List Mathlib.Tactic.Linarith.Comp ×             Mathlib.Tactic.Linarith.E
xprMap × Std.TreeMap Mathlib.Tactic.Linarith.Monom ℕ compare)
参数：List Mathlib.Tactic.Linarith.Comp ×             Mathlib.Tactic.Linarith.ExprM
ap × Std.TreeMap Mathlib.Tactic.Linarith.Monom ℕ compare。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toCompFold red e_map exprs monom_map` folds `toComp` over `exprs`,
updating `e_map` and `monom_map` as it goes.
-/
def toCompFold (red : TransparencyMode) : ExprMap → List Expr → TreeMap Monom ℕ →
    MetaM (List Comp × ExprMap × TreeMap Monom ℕ)
| m, [],     mm => return ([], m, mm)
| m, (h::t), mm => do
    let (c, m', mm') ← toComp red h m mm
    let (l, mp, mm') ← toCompFold red m' t mm'
    return (c::l, mp, mm')

/--
`linearFormsAndMaxVar red pfs` is the main interface for computing the linear forms of a list
of expressions. Given a list `pfs` of proofs of comparisons, it produces a list `c` of `Comp`s of
the same length, such that `c[i]` represents the linear form of the type of `pfs[i]`.

It also returns the largest variable index that appears in comparisons in `c`.
-/
/-
**Mathlib.Tactic.Linarith.linearFormsAndMaxVar** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Tactic.Linarith`。
形式化陈述：linearFormsAndMaxVar (red : TransparencyMode) (pfs : List Expr) : MetaM (L
ist Comp × Nat)
参数：red : TransparencyMode；pfs : List Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`linearFormsAndMaxVar red pfs` is the main interface for computing the linear fo
rms of a list
of expressions. Given a list `pfs` of proofs of comparisons, it produces a list 
`c` of `Comp`s of
the same length, such that `c[i]` represents the linear form of the type of `pfs
[i]`.

It also returns the largest variable index that appears in comparisons in `c`.
-/
def linearFormsAndMaxVar (red : TransparencyMode) (pfs : List Expr) :
    MetaM (List Comp × ℕ) := do
  let pftps ← (pfs.mapM inferType)
  let (l, _, map) ← toCompFold red [] pftps TreeMap.empty
  trace[linarith.detail] "monomial map: {map.toList.map fun ⟨k,v⟩ => (k.toList, v)}"
  return (l, map.size - 1)

end Mathlib.Tactic.Linarith

