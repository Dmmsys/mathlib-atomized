/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.Seq.Basic
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Majorized
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Corecursion

/-!

# Multiseries definitions

In this file, we define the multiseries and its main properties: sortedness and approximation.
A multiseries in a basis `[b₁, ..., bₙ]` represents a multivariate series:
it is a formal series made from monomials `b₁ ^ e₁ * ... * bₙ ^ eₙ` where `e₁, ..., eₙ` are real
numbers. We treat multivariate series in a basis `[b₁, ..., bₙ]` as a univariate series in the
variable `b₁` (`basis_hd`) with coefficients being multiseries
in the basis `[b₂, ..., bₙ]` (`basis_tl`).

## Main definitions

* `Basis` is the list of functions used to construct monomials in multiseries.
* `Multiseries basis_hd basis_tl` is the type of multiseries in a basis `basis_hd :: basis_tl`.
* `MultiseriesExpansion basis` is a multiseries expansion of some function `f : ℝ → ℝ`.
  If `basis = []`, then the multiseries represents a constant function, otherwise it is
  a pair of a multiseries `ms : Multiseries basis_hd basis_tl` and a function `f : ℝ → ℝ`.
* `Multiseries.Sorted ms` means that at each level of `ms` as a nested tree all exponents are
  strictly decreasing.
* `MultiseriesExpansion.Approximates ms` means that the multiseries `ms` can be used to obtain
  an asymptotical approximation of its attached function.

## Implementation details

* `Multiseries basis_hd basis_tl` is defined as a `Seq (ℝ × MultiseriesExpansion basis_tl)`, so
  we need to port some `Seq` API to `Multiseries`.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Filter Stream' Topology

/-- List of functions used to construct monomials in multiseries. -/
/-
**Tactic.ComputeAsymptotics.Basis** 是 Mathlib 中的一个缩写定义，位于命名空间 `Tactic.ComputeAsy
mptotics`。
形式化陈述：Basis
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
List of functions used to construct monomials in multiseries.
-/
abbrev Basis := List (ℝ → ℝ)

/-- Multiseries representing a given function `f : ℝ → ℝ`.
`MultiseriesExpansion []` is just `ℝ`: multiseries representing constant functions.
Otherwise it is a pair of a `Multiseries basis_hd basis_tl` and a function `ℝ → ℝ`. We call
the former an expansion of the latter.

Note: most of the theory can be formulated in terms of `Multiseries`, but we need to explicitly
store the approximated function to be able to use the eventual zeroness oracle at the trimming step.
-/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion** 是 Mathlib 中的一个定义，位于命名空间 `Tact
ic.ComputeAsymptotics`。
形式化陈述：MultiseriesExpansion (basis : Basis) : Type
参数：basis : Basis。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiseries representing a given function `f : ℝ → ℝ`.
`MultiseriesExpansion []` is just `ℝ`: multiseries representing constant functio
ns.
Otherwise it is a pair of a `Multiseries basis_hd basis_tl` and a function `ℝ → 
ℝ`. We call
the former an expansion of the latter.

Note: most of the theory can be formulated in terms of `Multiseries`, but we nee
d to explicitly
store the approximated function to be able to use the eventual zeroness oracle a
t the trimming step.
-/
def MultiseriesExpansion (basis : Basis) : Type :=
  match basis with
  | [] => ℝ
  | .cons _ basis_tl => Seq (ℝ × MultiseriesExpansion basis_tl) × (ℝ → ℝ)

namespace MultiseriesExpansion

set_option linter.unusedVariables false in
/-- Multiseries in a basis `basis_hd :: basis_tl`. It is a generalisation of asymptotic expansions.
A multiseries in a basis `[b₁, ..., bₙ]` is a formal series made from monomials
`b₁ ^ e₁ * ... * bₙ ^ eₙ` where `e₁, ..., eₙ` are real numbers. We treat multivariate series in
a basis `[b₁, ..., bₙ]` as a univariate series in the variable `b₁` (`basis_hd`) with coefficients
being multiseries in the basis `[b₂, ..., bₙ]` (`basis_tl`). We represent such a series as a lazy
list (`Seq`) of pairs `(exp, coef)` where `exp` is the exponent of `b₁` and `coef` is the
coefficient (a multiseries in `basis_tl`).

`MultiseriesExpansion` is a `Multiseries` with an attached real function.
-/
@[nolint unusedArguments]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries** 是 Mathlib 中的一个定义，
位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：Multiseries (basis_hd : Real -> Real) (basis_tl : Basis) : Type
参数：basis_hd : Real -> Real；basis_tl : Basis。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiseries in a basis `basis_hd :: basis_tl`. It is a generalisation of asympto
tic expansions.
A multiseries in a basis `[b₁, ..., bₙ]` is a formal series made from monomials
`b₁ ^ e₁ * ... * bₙ ^ eₙ` where `e₁, ..., eₙ` are real numbers. We treat multiva
riate series in
a basis `[b₁, ..., bₙ]` as a univariate series in the variable `b₁` (`basis_hd`)
 with coefficients
being multiseries in the basis `[b₂, ..., bₙ]` (`basis_tl`). We represent such a
 series as a lazy
list (`Seq`) of pairs `(exp, coef)` where `exp` is the exponent of `b₁` and `coe
f` is the
coefficient (a multiseries in `basis_tl`).

`MultiseriesExpansion` is a `Multiseries` with an attached real function.
-/
def Multiseries (basis_hd : ℝ → ℝ) (basis_tl : Basis) : Type :=
  Seq (ℝ × MultiseriesExpansion basis_tl)

namespace Multiseries

/-- Converts a `Multiseries basis_hd basis_tl` to a `Seq (ℝ × MultiseriesExpansion basis_tl)`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.toSeq** 是 Mathlib 中
的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：toSeq {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) : Seq (Real
 × MultiseriesExpansion basis_tl)
参数：ms : Multiseries basis_hd basis_tl。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `Multiseries basis_hd basis_tl` to a `Seq (ℝ × MultiseriesExpansion b
asis_tl)`.
-/
def toSeq {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Seq (ℝ × MultiseriesExpansion basis_tl) :=
  ms

/-- The empty multiseries. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.nil** 是 Mathlib 中的一
个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：nil {basis_hd basis_tl} : Multiseries basis_hd basis_tl
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty multiseries.
-/
def nil {basis_hd basis_tl} : Multiseries basis_hd basis_tl := Seq.nil

/-- Prepend a monomial to a multiseries. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons** 是 Mathlib 中的
一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：cons {basis_hd basis_tl} (exp : Real) (coef : MultiseriesExpansion basis_t
l) (tl : Multiseries basis_hd basis_tl) : Multiseries basis_hd basis_tl
参数：exp : Real；coef : MultiseriesExpansion basis_tl；tl : Multiseries basis_hd bas
is_tl。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prepend a monomial to a multiseries.
-/
def cons {basis_hd basis_tl} (exp : ℝ) (coef : MultiseriesExpansion basis_tl)
    (tl : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd basis_tl :=
  Seq.cons (exp, coef) tl

/-- Recursion principle for `Multiseries basis_hd basis_tl`. It is equivalent to
`Stream'.Seq.recOn` but provides some convenience. -/
@[cases_eliminator]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.recOn** 是 Mathlib 中
的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：recOn {basis_hd basis_tl} {motive : Multiseries basis_hd basis_tl -> Sort*
} (ms : Multiseries basis_hd basis_tl) (nil : motive nil) (cons : forall exp coe
f (tl : Multiseries basis_hd basis_tl), motive (cons exp coef tl)) : motive ms
参数：ms : Multiseries basis_hd basis_tl；nil : motive nil；cons : forall exp coef (t
l : Multiseries basis_hd basis_tl), motive (cons exp coef tl)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle for `Multiseries basis_hd basis_tl`. It is equivalent to
`Stream'.Seq.recOn` but provides some convenience.
-/
def recOn {basis_hd basis_tl} {motive : Multiseries basis_hd basis_tl → Sort*}
    (ms : Multiseries basis_hd basis_tl) (nil : motive nil)
    (cons : ∀ exp coef (tl : Multiseries basis_hd basis_tl), motive (cons exp coef tl)) :
    motive ms := Stream'.Seq.recOn _ nil fun _ _ ↦ cons _ _ _

/-- Destruct a multiseries into a triple `(exp, coef, tl)`, where `exp` is the leading exponent,
`coef` is the leading coefficient, and `tl` is the tail. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.destruct** 是 Mathli
b 中的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：destruct {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) : Option
 (Real × MultiseriesExpansion basis_tl × Multiseries basis_hd basis_tl)
参数：ms : Multiseries basis_hd basis_tl。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Destruct a multiseries into a triple `(exp, coef, tl)`, where `exp` is the leadi
ng exponent,
`coef` is the leading coefficient, and `tl` is the tail.
-/
def destruct {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Option (ℝ × MultiseriesExpansion basis_tl × Multiseries basis_hd basis_tl) :=
  (Seq.destruct ms).map (fun ((exp, coef), tl) => (exp, coef, tl))

/-- The head of a multiseries, i.e. the first two entries of the tuple returned by `destruct`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.head** 是 Mathlib 中的
一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：head {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) : Option (Re
al × MultiseriesExpansion basis_tl)
参数：ms : Multiseries basis_hd basis_tl。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The head of a multiseries, i.e. the first two entries of the tuple returned by `
destruct`.
-/
def head {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    Option (ℝ × MultiseriesExpansion basis_tl) :=
  Seq.head ms

/-- The tail of a multiseries, i.e. the last entry of the tuple returned by `destruct`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.tail** 是 Mathlib 中的
一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：tail {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) : Multiserie
s basis_hd basis_tl
参数：ms : Multiseries basis_hd basis_tl。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tail of a multiseries, i.e. the last entry of the tuple returned by `destruc
t`.
-/
def tail {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) : Multiseries basis_hd basis_tl :=
  Seq.tail ms

/-- Given two functions `f : ℝ → ℝ` and
`g : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl'`, apply them to exponents and
coefficients of a multiseries. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.map** 是 Mathlib 中的一
个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：map {basis_hd basis_tl basis_hd' basis_tl'} (f : Real -> Real) (g : Multis
eriesExpansion basis_tl -> MultiseriesExpansion basis_tl') (ms : Multiseries bas
is_hd basis_tl) : Multiseries basis_hd' basis_tl'
参数：f : Real -> Real；g : MultiseriesExpansion basis_tl -> MultiseriesExpansion ba
sis_tl'；ms : Multiseries basis_hd basis_tl。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two functions `f : ℝ → ℝ` and
`g : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl'`, apply them
 to exponents and
coefficients of a multiseries.
-/
def map {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → ℝ)
    (g : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl')
    (ms : Multiseries basis_hd basis_tl) :
    Multiseries basis_hd' basis_tl' :=
  Seq.map (fun (exp, coef) ↦ (f exp, g coef)) ms

/-- Corecursor for `Multiseries basis_hd basis_tl`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.corec** 是 Mathlib 中
的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：corec {β : Type*} {basis_hd} {basis_tl} (f : β -> Option (Real × Multiseri
esExpansion basis_tl × β)) (b : β) : Multiseries basis_hd basis_tl
参数：f : β -> Option (Real × MultiseriesExpansion basis_tl × β)；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Corecursor for `Multiseries basis_hd basis_tl`.
-/
def corec {β : Type*} {basis_hd} {basis_tl}
    (f : β → Option (ℝ × MultiseriesExpansion basis_tl × β)) (b : β) :
    Multiseries basis_hd basis_tl :=
  Seq.corec (fun a => (f a).map (fun (exp, coef, next) => ((exp, coef), next))) b

/-- An operation on multiseries called a "friend" if any `n`-prefix of its output depends only on
the `n`-prefix of the input. Such operations can be used in the tail of (non-primitive) corecursive
definitions. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation**
 是 Mathlib 中的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multise
ries`。
形式化陈述：FriendlyOperation {basis_hd basis_tl} (op : Multiseries basis_hd basis_tl 
-> Multiseries basis_hd basis_tl) : Prop
参数：op : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An operation on multiseries called a "friend" if any `n`-prefix of its output de
pends only on
the `n`-prefix of the input. Such operations can be used in the tail of (non-pri
mitive) corecursive
definitions.
-/
def FriendlyOperation {basis_hd basis_tl}
    (op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl) : Prop :=
  Seq.FriendlyOperation op

/-- A family of friendly operations on multiseries indexed by a type `γ`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperationCl
ass** 是 Mathlib 中的一个归纳类型，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.
Multiseries`。
形式化陈述：{basis_hd : ℝ → ℝ} →   {basis_tl : Tactic.ComputeAsymptotics.Basis} →     
{γ : Type u_1} →       (γ →           Tactic.ComputeAsymptotics.MultiseriesExpan
sion.Multiseries basis_hd basis_tl →             Tactic.ComputeAsymptotics.Multi
seriesExpansion.Multiseries basis_hd basis_tl) →         Prop
参数：γ →           Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basi
s_hd basis_tl →             Tactic.ComputeAsymptotics.MultiseriesExpansion.Multi
series basis_hd basis_tl。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of friendly operations on multiseries indexed by a type `γ`.
-/
class FriendlyOperationClass {basis_hd basis_tl} {γ : Type*}
    (op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl) : Prop
    extends Seq.FriendlyOperationClass op
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperationCl
ass.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansio
n.Multiseries.FriendlyOperationClass`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} {γ : Typ
e u_1}   {op :     γ →       Tactic.ComputeAsymptotics.MultiseriesExpansion.Mult
iseries basis_hd basis_tl →         Tactic.ComputeAsymptotics.MultiseriesExpansi
on.Multiseries basis_hd basis_tl},   (∀ (c : γ), Tactic.ComputeAsymptotics.Multi
seriesExpansion.Multiseries.FriendlyOperation (op c)) →     Tactic.ComputeAsympt
otics.MultiseriesExpansion.Multiseries.FriendlyOperationClass op
参数：∀ (c : γ), Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Friendl
yOperation (op c)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem FriendlyOperationClass.mk' {basis_hd basis_tl} {γ : Type*}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h : ∀ c, FriendlyOperation (op c)) :
    FriendlyOperationClass op := by
  suffices Seq.FriendlyOperationClass op by constructor
  exact ⟨h⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.destruct_eq_destruc
t_map** 是 Mathlib 中的一个引理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.
Multiseries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma destruct_eq_destruct_map {basis_hd basis_tl}
    (s : Stream'.Seq (ℝ × MultiseriesExpansion basis_tl)) :
    s.destruct = (Multiseries.destruct (basis_hd := basis_hd) s).map
      (fun (exp, coef, tl) => ((exp, coef), tl)) := by
  simp only [destruct, Option.map_map]
  exact Option.map_id_apply.symm

set_option backward.isDefEq.respectTransparency false in
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation.c
oind_comp_friend_left** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Multi
seriesExpansion.Multiseries.FriendlyOperation`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   {op : 
    Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl
 →       Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd bas
is_tl}   (motive :     (Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseri
es basis_hd basis_tl →         Tactic.ComputeAsymptotics.MultiseriesExpansion.Mu
ltiseries basis_hd basis_tl) →       Prop),   motive op →     (∀         (op :  
         Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd bas
is_tl →             Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries b
asis_hd basis_tl),         motive op →           ∃ T,             ∀ (s : Tactic.
ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl),         
      (op s).destruct =                 Option.map                   (fun x =>  
                   match x with                     | (exp, coef, opf, op') => (
exp, coef, ↑opf (↑op' s.tail)))                   (T s.head)) →       Tactic.Com
puteAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation op
参数：motive :     (Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basi
s_hd basis_tl →         Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseri
es basis_hd basis_tl) →       Prop；∀         (op :           Tactic.ComputeAsymp
totics.MultiseriesExpansion.Multiseries basis_hd basis_tl →             Tactic.C
omputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl),         m
otive op →           ∃ T,             ∀ (s : Tactic.ComputeAsymptotics.Multiseri
esExpansion.Multiseries basis_hd basis_tl),               (op s).destruct =     
            Option.map                   (fun x =>                     match x w
ith                     | (exp, coef, opf, op') => (exp, coef, ↑opf (↑op' s.tail
)))                   (T s.head)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.coind_comp_friend_left`：
∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α} (motive : (Stream'.Seq α →
 Stream'.Seq α) → Prop),   motive op →     (∀ (op : Stream'.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs.0.Tactic.Com
puteAsymptotics.MultiseriesExpansion.Multiseries.destruct_eq_destruct_map`：∀ {ba
sis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   (s : Stream'.Seq 
(ℝ × Tactic.ComputeAsymptotics.MultiseriesExpansion bas…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
-/
theorem FriendlyOperation.coind_comp_friend_left {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (motive : (Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl) → Prop)
    (h_base : motive op)
    (h_step : ∀ op, motive op → ∃ T : Option (ℝ × MultiseriesExpansion basis_tl) →
        Option (ℝ × MultiseriesExpansion basis_tl × Subtype FriendlyOperation × Subtype motive),
      ∀ s, (op s).destruct =
        (T s.head).map (fun (exp, coef, opf, op') => (exp, coef, opf.val <| op'.val (s.tail)))) :
    FriendlyOperation op := by
  refine Seq.FriendlyOperation.coind_comp_friend_left motive h_base (fun op h_op ↦ ?_)
  obtain ⟨T, hT⟩ := h_step op h_op
  use fun hd? ↦ (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  rw [destruct_eq_destruct_map, hT s]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation.c
oind_comp_friend_right** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Mult
iseriesExpansion.Multiseries.FriendlyOperation`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   {op : 
    Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl
 →       Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd bas
is_tl}   (motive :     (Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseri
es basis_hd basis_tl →         Tactic.ComputeAsymptotics.MultiseriesExpansion.Mu
ltiseries basis_hd basis_tl) →       Prop),   motive op →     (∀         (op :  
         Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd bas
is_tl →             Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries b
asis_hd basis_tl),         motive op →           ∃ T,             ∀ (s : Tactic.
ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl),         
      (op s).destruct =                 Option.map                   (fun x =>  
                   match x with                     | (exp, coef, opf, op') => (
exp, coef, ↑op' (↑opf s.tail)))                   (T s.head)) →       Tactic.Com
puteAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation op
参数：motive :     (Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basi
s_hd basis_tl →         Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseri
es basis_hd basis_tl) →       Prop；∀         (op :           Tactic.ComputeAsymp
totics.MultiseriesExpansion.Multiseries basis_hd basis_tl →             Tactic.C
omputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl),         m
otive op →           ∃ T,             ∀ (s : Tactic.ComputeAsymptotics.Multiseri
esExpansion.Multiseries basis_hd basis_tl),               (op s).destruct =     
            Option.map                   (fun x =>                     match x w
ith                     | (exp, coef, opf, op') => (exp, coef, ↑op' (↑opf s.tail
)))                   (T s.head)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.coind_comp_friend_right`
：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α} (motive : (Stream'.Seq α 
→ Stream'.Seq α) → Prop),   motive op →     (∀ (op : Stream'.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs.0.Tactic.Com
puteAsymptotics.MultiseriesExpansion.Multiseries.destruct_eq_destruct_map`：∀ {ba
sis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   (s : Stream'.Seq 
(ℝ × Tactic.ComputeAsymptotics.MultiseriesExpansion bas…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
-/
theorem FriendlyOperation.coind_comp_friend_right {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (motive : (Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl) → Prop)
    (h_base : motive op)
    (h_step : ∀ op, motive op → ∃ T : Option (ℝ × MultiseriesExpansion basis_tl) →
        Option (ℝ × MultiseriesExpansion basis_tl × Subtype FriendlyOperation × Subtype motive),
      ∀ s, (op s).destruct =
        (T s.head).map (fun (exp, coef, opf, op') => (exp, coef, op'.val <| opf.val (s.tail)))) :
    FriendlyOperation op := by
  refine Seq.FriendlyOperation.coind_comp_friend_right motive h_base (fun op h_op ↦ ?_)
  obtain ⟨T, hT⟩ := h_step op h_op
  use fun hd? ↦ (T hd?).map (fun (exp, coef, opf, op') => ((exp, coef), opf, op'))
  intro s
  rw [destruct_eq_destruct_map, hT s]
  simp
  rfl

/-- Non-primitive corecursor for `Multiseries basis_hd basis_tl` allowing to use a friendly
operation in the tail of the corecursive definition. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.gcorec** 是 Mathlib 
中的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：gcorec {β γ : Type*} {basis_hd} {basis_tl} (F : β -> Option (Real × Multis
eriesExpansion basis_tl × γ × β)) (op : γ -> Multiseries basis_hd basis_tl -> Mu
ltiseries basis_hd basis_tl) [FriendlyOperationClass op] (b : β) : Multiseries b
asis_hd basis_tl
参数：F : β -> Option (Real × MultiseriesExpansion basis_tl × γ × β)；op : γ -> Mult
iseries basis_hd basis_tl -> Multiseries basis_hd basis_tl；b : β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOpera
tionClass.toFriendlyOperationClass`：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.Comp
uteAsymptotics.Basis} {γ : Type u_1}   {op :     γ →       Tactic.ComputeAsympto
tics.Multiseries…

--- 原说明 ---
Non-primitive corecursor for `Multiseries basis_hd basis_tl` allowing to use a f
riendly
operation in the tail of the corecursive definition.
-/
noncomputable def gcorec {β γ : Type*} {basis_hd} {basis_tl}
    (F : β → Option (ℝ × MultiseriesExpansion basis_tl × γ × β))
    (op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl)
    [FriendlyOperationClass op]
    (b : β) :
    Multiseries basis_hd basis_tl :=
  Seq.gcorec (fun a => (F a).map (fun (exp, coef, c, next) => ((exp, coef), c, next))) op b
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.** 是 Mathlib 中的一个实例
，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (basis_hd basis_tl) : Inhabited (Multiseries basis_hd basis_tl) where
  default := (default : Seq (ℝ × MultiseriesExpansion basis_tl))
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.** 是 Mathlib 中的一个实例
，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {basis_hd basis_tl} :
    Membership (ℝ × MultiseriesExpansion basis_tl) (Multiseries basis_hd basis_tl) where
  mem ms x := x ∈ ms.toSeq
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.eq_of_bisim** 是 Mat
hlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：eq_of_bisim {basis_hd : Real -> Real} {basis_tl : Basis} {x y : Multiserie
s basis_hd basis_tl} (motive : Multiseries basis_hd basis_tl -> Multiseries basi
s_hd basis_tl -> Prop) (base : motive x y) (step : forall x y, motive x y -> (x 
= .nil ∧ y = .nil) ∨ exists exp coef, exists (x' y' : Multiseries basis_hd basis
_tl), x = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') : x = y
参数：motive : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl -> Pr
op；base : motive x y；step : forall x y, motive x y -> (x = .nil ∧ y = .nil) ∨ ex
ists exp coef, exists (x' y' : Multiseries basis_hd basis_tl), x = cons exp coef
 x' ∧ y = cons exp coef y' ∧ motive x' y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.eq_of_bisim'`：eq_of_bisim' {s₁ s₂ : Seq α} (motive : Seq α -
> Seq α -> Prop) (base : motive s₁ s₂) (step : forall s₁ s₂, motive s₁ s₂ -> (s₁
 = nil ∧ s₂ = …
-/
theorem eq_of_bisim {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x y : Multiseries basis_hd basis_tl}
    (motive : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = .nil ∧ y = .nil) ∨ ∃ exp coef,
      ∃ (x' y' : Multiseries basis_hd basis_tl),
      x = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') :
    x = y := Seq.eq_of_bisim' motive base (by grind [nil, cons])
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.eq_of_bisim_strong*
* 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multis
eries`。
形式化陈述：eq_of_bisim_strong {basis_hd : Real -> Real} {basis_tl : Basis} {x y : Mul
tiseries basis_hd basis_tl} (motive : Multiseries basis_hd basis_tl -> Multiseri
es basis_hd basis_tl -> Prop) (base : motive x y) (step : forall x y, motive x y
 -> (x = y) ∨ exists exp coef, exists (x' y' : Multiseries basis_hd basis_tl), x
 = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') : x = y
参数：motive : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl -> Pr
op；base : motive x y；step : forall x y, motive x y -> (x = y) ∨ exists exp coef,
 exists (x' y' : Multiseries basis_hd basis_tl), x = cons exp coef x' ∧ y = cons
 exp coef y' ∧ motive x' y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.eq_of_bisim_strong`：eq_of_bisim_strong {s₁ s₂ : Seq α} (moti
ve : Seq α -> Seq α -> Prop) (base : motive s₁ s₂) (step : forall s₁ s₂, motive 
s₁ s₂ -> (s₁ = s₂) ∨…
-/
theorem eq_of_bisim_strong {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {x y : Multiseries basis_hd basis_tl}
    (motive : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = y) ∨ ∃ exp coef,
      ∃ (x' y' : Multiseries basis_hd basis_tl),
      x = cons exp coef x' ∧ y = cons exp coef y' ∧ motive x' y') :
    x = y := Seq.eq_of_bisim_strong motive base (by grind [nil, cons])
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperationCl
ass.FriendlyOperation** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Multi
seriesExpansion.Multiseries.FriendlyOperationClass`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} {γ : Typ
e u_1}   {op :     γ →       Tactic.ComputeAsymptotics.MultiseriesExpansion.Mult
iseries basis_hd basis_tl →         Tactic.ComputeAsymptotics.MultiseriesExpansi
on.Multiseries basis_hd basis_tl}   [h : Tactic.ComputeAsymptotics.MultiseriesEx
pansion.Multiseries.FriendlyOperationClass op] (c : γ),   Tactic.ComputeAsymptot
ics.MultiseriesExpansion.Multiseries.FriendlyOperation (op c)
参数：c : γ；op c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass.friend`：∀ {α : Type
 u_1} {γ : Type u_3} {F : γ → Stream'.Seq α → Stream'.Seq α}   [self : Tactic.Co
mputeAsymptotics.Seq.FriendlyOperationClass F] (c…
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOpera
tionClass.toFriendlyOperationClass`：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.Comp
uteAsymptotics.Basis} {γ : Type u_1}   {op :     γ →       Tactic.ComputeAsympto
tics.Multiseries…
-/
theorem FriendlyOperationClass.FriendlyOperation {basis_hd basis_tl} {γ : Type*}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    [h : FriendlyOperationClass op]
    (c : γ) :
    FriendlyOperation (op c) :=
  h.friend c

/-- Decomposes a friendly operation by the head of the input sequence. Returns `none` if the output
is `nil`, or `some (exp, coef, op')` where `(exp, coef)` is the head of the output and
`op'` is a friendly operation mapping the tail of the input to the tail of the output. See
`destruct_apply_eq_unfold` for the correctness statement. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation.u
nfold** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.
Multiseries.FriendlyOperation`。
形式化陈述：{basis_hd : ℝ → ℝ} →   {basis_tl : Tactic.ComputeAsymptotics.Basis} →     
{op :         Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_h
d basis_tl →           Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiserie
s basis_hd basis_tl} →       Tactic.ComputeAsymptotics.MultiseriesExpansion.Mult
iseries.FriendlyOperation op →         Option (ℝ × Tactic.ComputeAsymptotics.Mul
tiseriesExpansion basis_tl) →           Option             (ℝ ×               Ta
ctic.ComputeAsymptotics.MultiseriesExpansion basis_tl ×                 Subtype 
Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation)
参数：ℝ × Tactic.ComputeAsymptotics.MultiseriesExpansion basis_tl；ℝ ×              
 Tactic.ComputeAsymptotics.MultiseriesExpansion basis_tl ×                 Subty
pe Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Decomposes a friendly operation by the head of the input sequence. Returns `none
` if the output
is `nil`, or `some (exp, coef, op')` where `(exp, coef)` is the head of the outp
ut and
`op'` is a friendly operation mapping the tail of the input to the tail of the o
utput. See
`destruct_apply_eq_unfold` for the correctness statement.
-/
def FriendlyOperation.unfold {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h : FriendlyOperation op) (hd? : Option (ℝ × MultiseriesExpansion basis_tl)) :
    Option (ℝ × MultiseriesExpansion basis_tl × Subtype (
      @Multiseries.FriendlyOperation basis_hd basis_tl)) :=
  Seq.FriendlyOperation.unfold h hd? |>.map (fun ((exp, coef), op') ↦ (exp, coef, op'))

set_option backward.isDefEq.respectTransparency false in
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation.d
estruct_apply_eq_unfold** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.Mul
tiseriesExpansion.Multiseries.FriendlyOperation`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   {op : 
    Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl
 →       Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd bas
is_tl}   (h : Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Friendl
yOperation op)   (ms : Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiserie
s basis_hd basis_tl),   (op ms).destruct =     Option.map       (fun x =>       
  match x with         | (exp, coef, op') => (exp, coef, ↑op' ms.tail))       (h
.unfold ms.head)
参数：h : Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperat
ion op；ms : Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd 
basis_tl；op ms；fun x =>         match x with         | (exp, coef, op') => (exp,
 coef, ↑op' ms.tail)；h.unfold ms.head。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.destruct_apply_eq_unfold
`：∀ {α : Type u_1} {op : Stream'.Seq α → Stream'.Seq α} (h : Tactic.ComputeAsymp
totics.Seq.FriendlyOperation op)   {s : Stream'.Seq α},   (op …
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem FriendlyOperation.destruct_apply_eq_unfold {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h : FriendlyOperation op) (ms : Multiseries basis_hd basis_tl) :
      destruct (op ms) = (h.unfold ms.head).map
        (fun (exp, coef, op') ↦ (exp, coef, op'.val ms.tail)) := by
  unfold Multiseries.destruct
  simp [Seq.FriendlyOperation.destruct_apply_eq_unfold h, FriendlyOperation.unfold, head]
  cases Seq.FriendlyOperation.unfold h (Seq.head ms) <;> rfl
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation.h
ead_eq_head** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpa
nsion.Multiseries.FriendlyOperation`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   {op : 
    Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl
 →       Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd bas
is_tl},   Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOpe
ration op →     ∀ {x y : Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiser
ies basis_hd basis_tl},       x.head = y.head → (op x).head = (op y).head
参数：op x；op y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.op_head_eq`：∀ {α : Type 
u_1} {op : Stream'.Seq α → Stream'.Seq α},   Tactic.ComputeAsymptotics.Seq.Frien
dlyOperation op →     ∀ {s t : Stream'.Seq α}, s…
-/
theorem FriendlyOperation.head_eq_head {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h : FriendlyOperation op) {x y : Multiseries basis_hd basis_tl}
    (h_head : x.head = y.head) : (op x).head = (op y).head :=
  Seq.FriendlyOperation.op_head_eq h h_head
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation.i
d** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Mult
iseries.FriendlyOperation`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis},   Tacti
c.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.id`：∀ {α : Type u_1}, Ta
ctic.ComputeAsymptotics.Seq.FriendlyOperation id
-/
theorem FriendlyOperation.id {basis_hd basis_tl} :
    FriendlyOperation (id : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl) :=
  Seq.FriendlyOperation.id
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation.c
omp** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Mu
ltiseries.FriendlyOperation`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   {op₁ o
p₂ :     Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd bas
is_tl →       Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_h
d basis_tl},   Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Friend
lyOperation op₁ →     Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries
.FriendlyOperation op₂ →       Tactic.ComputeAsymptotics.MultiseriesExpansion.Mu
ltiseries.FriendlyOperation (op₁ ∘ op₂)
参数：op₁ ∘ op₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.comp`：∀ {α : Type u_1} {
op op' : Stream'.Seq α → Stream'.Seq α},   Tactic.ComputeAsymptotics.Seq.Friendl
yOperation op →     Tactic.ComputeAsymptot…
-/
theorem FriendlyOperation.comp {basis_hd basis_tl}
    {op₁ op₂ : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h₁ : FriendlyOperation op₁) (h₂ : FriendlyOperation op₂) :
    FriendlyOperation (op₁ ∘ op₂) :=
  Seq.FriendlyOperation.comp h₁ h₂
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation.c
onst** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.M
ultiseries.FriendlyOperation`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   {s : T
actic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl},   
Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation fun
 x => s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.const`：∀ {α : Type u_1} 
{s : Stream'.Seq α}, Tactic.ComputeAsymptotics.Seq.FriendlyOperation fun x => s
-/
theorem FriendlyOperation.const {basis_hd basis_tl} {s : Multiseries basis_hd basis_tl} :
    FriendlyOperation (fun _ ↦ s) :=
  Seq.FriendlyOperation.const
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation.i
te** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Mul
tiseries.FriendlyOperation`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   {op₁ o
p₂ :     Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd bas
is_tl →       Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_h
d basis_tl},   Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Friend
lyOperation op₁ →     Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries
.FriendlyOperation op₂ →       ∀ {P : Option (ℝ × Tactic.ComputeAsymptotics.Mult
iseriesExpansion basis_tl) → Prop} [inst : DecidablePred P],         Tactic.Comp
uteAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation fun ms =>     
      if P ms.head then op₁ ms else op₂ ms
参数：ℝ × Tactic.ComputeAsymptotics.MultiseriesExpansion basis_tl。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.ite`：∀ {α : Type u_1} {o
p₁ op₂ : Stream'.Seq α → Stream'.Seq α},   Tactic.ComputeAsymptotics.Seq.Friendl
yOperation op₁ →     Tactic.ComputeAsympt…
-/
theorem FriendlyOperation.ite {basis_hd basis_tl}
    {op₁ op₂ : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    (h₁ : FriendlyOperation op₁) (h₂ : FriendlyOperation op₂)
    {P : Option (ℝ × MultiseriesExpansion basis_tl) → Prop} [DecidablePred P] :
    FriendlyOperation (fun ms ↦ if P ms.head then op₁ ms else op₂ ms) :=
  Seq.FriendlyOperation.ite h₁ h₂
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation.c
ons** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Mu
ltiseries.FriendlyOperation`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} (exp : ℝ
)   (coef : Tactic.ComputeAsymptotics.MultiseriesExpansion basis_tl),   Tactic.C
omputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation     (Tactic
.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons exp coef)
参数：exp : ℝ；coef : Tactic.ComputeAsymptotics.MultiseriesExpansion basis_tl；Tactic
.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons exp coef。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.cons`：∀ {α : Type u_1} (
hd : α), Tactic.ComputeAsymptotics.Seq.FriendlyOperation (Stream'.Seq.cons hd)
-/
theorem FriendlyOperation.cons {basis_hd basis_tl} (exp : ℝ)
    (coef : MultiseriesExpansion basis_tl) :
    FriendlyOperation (cons (basis_hd := basis_hd) exp coef) :=
  Seq.FriendlyOperation.cons _
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperation.c
ons_tail** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansi
on.Multiseries.FriendlyOperation`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   {op : 
    Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl
 →       Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd bas
is_tl}   {exp : ℝ} {coef : Tactic.ComputeAsymptotics.MultiseriesExpansion basis_
tl},   Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperat
ion op →     Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Friendly
Operation fun ms =>       (op (Tactic.ComputeAsymptotics.MultiseriesExpansion.Mu
ltiseries.cons exp coef ms)).tail
参数：op (Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons exp coef 
ms)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperation.cons_tail`：∀ {α : Type u
_1} {op : Stream'.Seq α → Stream'.Seq α} {hd : α},   Tactic.ComputeAsymptotics.S
eq.FriendlyOperation op →     Tactic.ComputeAsy…
-/
theorem FriendlyOperation.cons_tail {basis_hd basis_tl}
    {op : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    (h : FriendlyOperation op) :
    FriendlyOperation (fun ms ↦ (op (.cons exp coef ms)).tail) :=
  Seq.FriendlyOperation.cons_tail h
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperationCl
ass.comp** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansi
on.Multiseries.FriendlyOperationClass`。
形式化陈述：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} {γ : Typ
e u_1} {γ' : Type u_2} {g : γ' → γ}   {op :     γ →       Tactic.ComputeAsymptot
ics.MultiseriesExpansion.Multiseries basis_hd basis_tl →         Tactic.ComputeA
symptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl}   [h : Tactic.Com
puteAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperationClass op],   T
actic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOperationClass
 fun c => op (g c)
参数：g c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass.comp`：∀ {α : Type u
_1} {γ : Type u_3} {γ' : Type u_4} (F : γ → Stream'.Seq α → Stream'.Seq α) (g : 
γ' → γ)   [h : Tactic.ComputeAsymptotics.Seq.Fr…
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOpera
tionClass.toFriendlyOperationClass`：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.Comp
uteAsymptotics.Basis} {γ : Type u_1}   {op :     γ →       Tactic.ComputeAsympto
tics.Multiseries…
-/
theorem FriendlyOperationClass.comp {basis_hd basis_tl} {γ γ' : Type*}
    {g : γ' → γ}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    [h : FriendlyOperationClass op] : FriendlyOperationClass (fun c ↦ op (g c)) := by
  have : Seq.FriendlyOperationClass (fun c ↦ op (g c)) := Seq.FriendlyOperationClass.comp _ _
  constructor
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.eq_of_bisim_friend*
* 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multis
eries`。
形式化陈述：eq_of_bisim_friend {γ : Type*} {basis_hd : Real -> Real} {basis_tl : Basis
} {op : γ -> Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl} [Fr
iendlyOperationClass op] {x y : Multiseries basis_hd basis_tl} (motive : Multise
ries basis_hd basis_tl -> Multiseries basis_hd basis_tl -> Prop) (base : motive 
x y) (step : forall x y, motive x y -> (x = y) ∨ exists exp coef, exists (c : γ)
 (x' y' : Multiseries basis_hd basis_tl), x = cons exp coef (op c x') ∧ y = cons
 exp coef (op c y') ∧ moti
参数：motive : Multiseries basis_hd basis_tl -> Multiseries basis_hd basis_tl -> Pr
op；base : motive x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.Seq.FriendlyOperationClass.eq_of_bisim`：∀ {α :
 Type u_1} {γ : Type u_3} {s t : Stream'.Seq α} {op : γ → Stream'.Seq α → Stream
'.Seq α}   [Tactic.ComputeAsymptotics.Seq.FriendlyOper…
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOpera
tionClass.toFriendlyOperationClass`：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.Comp
uteAsymptotics.Basis} {γ : Type u_1}   {op :     γ →       Tactic.ComputeAsympto
tics.Multiseries…
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_bisim_friend {γ : Type*} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    [FriendlyOperationClass op]
    {x y : Multiseries basis_hd basis_tl}
    (motive : Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = y) ∨ ∃ exp coef,
      ∃ (c : γ) (x' y' : Multiseries basis_hd basis_tl),
      x = cons exp coef (op c x') ∧ y = cons exp coef (op c y') ∧ motive x' y') :
    x = y := by
  apply Seq.FriendlyOperationClass.eq_of_bisim (op := op) motive base
  peel step with x y ih h
  obtain h | ⟨exp, coef, c, x', y', rfl, rfl, h_next⟩ := h
  · simp [h]
  right
  use (exp, coef), x', y', c
  simpa [cons]

section simp

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons_ne_nil** 是 Mat
hlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：cons_ne_nil {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real} {coe
f : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} : cons e
xp coef tl != .nil
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.cons_ne_nil`：cons_ne_nil {x : α} {s : Seq α} : (cons x s) !=
 .nil
-/
theorem cons_ne_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    cons exp coef tl ≠ .nil := by
  intro h
  simp only [cons, nil] at h
  apply Seq.cons_ne_nil h

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.nil_ne_cons** 是 Mat
hlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：nil_ne_cons {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real} {coe
f : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} : .nil !
= cons exp coef tl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons_ne_nil`：
cons_ne_nil {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real} {coef : Mu
ltiseriesExpansion basis_tl} {tl : Multiseries basis_hd basi…
-/
theorem nil_ne_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    .nil ≠ cons exp coef tl := cons_ne_nil.symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons_eq_cons** 是 Ma
thlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`
。
形式化陈述：cons_eq_cons {basis_hd : Real -> Real} {basis_tl : Basis} {exp1 exp2 : Rea
l} {coef1 coef2 : MultiseriesExpansion basis_tl} {tl1 tl2 : Multiseries basis_hd
 basis_tl} : cons exp1 coef1 tl1 = cons exp2 coef2 tl2 ↔ exp1 = exp2 ∧ coef1 = c
oef2 ∧ tl1 = tl2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.cons.eq_1`：∀ 
{basis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis} (exp : ℝ)   (coe
f : Tactic.ComputeAsymptotics.MultiseriesExpansion basis_t…
· 使用定理 `Stream'.Seq.cons_eq_cons`：cons_eq_cons {x x' : α} {s s' : Seq α} : (cons
 x s = cons x' s') ↔ (x = x' ∧ s = s')
-/
theorem cons_eq_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp1 exp2 : ℝ}
    {coef1 coef2 : MultiseriesExpansion basis_tl} {tl1 tl2 : Multiseries basis_hd basis_tl} :
    cons exp1 coef1 tl1 = cons exp2 coef2 tl2 ↔ exp1 = exp2 ∧ coef1 = coef2 ∧ tl1 = tl2 := by
  rw [cons, cons, Seq.cons_eq_cons]
  grind
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.corec_nil** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：corec_nil {β : Type*} {basis_hd} {basis_tl} {f : β -> Option (Real × Multi
seriesExpansion basis_tl × β)} {b : β} (h : f b = none) : corec f b = (nil : Mul
tiseries basis_hd basis_tl)
参数：Real × MultiseriesExpansion basis_tl × β；h : f b = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.corec_nil`：corec_nil (f : β -> Option (α × β)) (b : β) (h : 
f b = .none) : corec f b = nil
-/
theorem corec_nil {β : Type*} {basis_hd} {basis_tl}
    {f : β → Option (ℝ × MultiseriesExpansion basis_tl × β)} {b : β} (h : f b = none) :
    corec f b = (nil : Multiseries basis_hd basis_tl) := by
  simp only [corec, nil]
  rw [Seq.corec_nil]
  simpa
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.corec_cons** 是 Math
lib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：corec_cons {β : Type*} {basis_hd} {basis_tl} {exp : Real} {coef : Multiser
iesExpansion basis_tl} {next : β} {f : β -> Option (Real × MultiseriesExpansion 
basis_tl × β)} {b : β} (h : f b = some (exp, coef, next)) : (corec f b : Multise
ries basis_hd basis_tl) = cons exp coef (corec f next)
参数：Real × MultiseriesExpansion basis_tl × β；h : f b = some (exp, coef, next)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.corec_cons`：corec_cons {f : β -> Option (α × β)} {b : β} {x 
: α} {s : β} (h : f b = .some (x, s)) : corec f b = cons x (corec f s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem corec_cons {β : Type*} {basis_hd} {basis_tl} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {next : β}
    {f : β → Option (ℝ × MultiseriesExpansion basis_tl × β)} {b : β}
    (h : f b = some (exp, coef, next)) :
    (corec f b : Multiseries basis_hd basis_tl) = cons exp coef (corec f next) := by
  simp only [corec, cons]
  rw [Seq.corec_cons]
  simpa

set_option backward.isDefEq.respectTransparency false in
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.gcorec_nil** 是 Math
lib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：gcorec_nil {β γ : Type*} {basis_hd} {basis_tl} {F : β -> Option (Real × Mu
ltiseriesExpansion basis_tl × γ × β)} {op : γ -> Multiseries basis_hd basis_tl -
> Multiseries basis_hd basis_tl} [FriendlyOperationClass op] {b : β} (h : F b = 
none) : gcorec F op b = nil
参数：Real × MultiseriesExpansion basis_tl × γ × β；h : F b = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOpera
tionClass.toFriendlyOperationClass`：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.Comp
uteAsymptotics.Basis} {γ : Type u_1}   {op :     γ →       Tactic.ComputeAsympto
tics.Multiseries…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.Seq.gcorec_nil`：gcorec_nil {F : β -> Option (α
 × γ × β)} {op : γ -> Seq α -> Seq α} [FriendlyOperationClass op] {b : β} (h : F
 b = none) : gcorec F op b = n…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gcorec_nil {β γ : Type*} {basis_hd} {basis_tl}
    {F : β → Option (ℝ × MultiseriesExpansion basis_tl × γ × β)}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    [FriendlyOperationClass op] {b : β}
    (h : F b = none) :
    gcorec F op b = nil := by
  unfold gcorec
  rw [Seq.gcorec_nil]
  · simp [nil]
  · simpa

set_option backward.isDefEq.respectTransparency false in
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.gcorec_some** 是 Mat
hlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：gcorec_some {β γ : Type*} {basis_hd} {basis_tl} {F : β -> Option (Real × M
ultiseriesExpansion basis_tl × γ × β)} {op : γ -> Multiseries basis_hd basis_tl 
-> Multiseries basis_hd basis_tl} [FriendlyOperationClass op] {b : β} {exp : Rea
l} {coef : MultiseriesExpansion basis_tl} {c : γ} {next : β} (h : F b = some (ex
p, coef, c, next)) : gcorec F op b = cons exp coef (op c (gcorec F op next))
参数：Real × MultiseriesExpansion basis_tl × γ × β；h : F b = some (exp, coef, c, ne
xt)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.FriendlyOpera
tionClass.toFriendlyOperationClass`：∀ {basis_hd : ℝ → ℝ} {basis_tl : Tactic.Comp
uteAsymptotics.Basis} {γ : Type u_1}   {op :     γ →       Tactic.ComputeAsympto
tics.Multiseries…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.Seq.gcorec_some`：gcorec_some {F : β -> Option 
(α × γ × β)} {op : γ -> Seq α -> Seq α} [FriendlyOperationClass op] {b : β} {a :
 α} {c : γ} {b' : β} (h : F b =…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Tactic.ComputeAsymptotics.Seq.gcorec.congr_simp`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} (F F_1 : β → Option (α × γ × β)),   F = F_1 →     ∀ (op 
op_1 : γ → Stream'.Seq α → Stream'.Se…
-/
theorem gcorec_some {β γ : Type*} {basis_hd} {basis_tl}
    {F : β → Option (ℝ × MultiseriesExpansion basis_tl × γ × β)}
    {op : γ → Multiseries basis_hd basis_tl → Multiseries basis_hd basis_tl}
    [FriendlyOperationClass op] {b : β}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {c : γ} {next : β}
    (h : F b = some (exp, coef, c, next)) :
    gcorec F op b = cons exp coef (op c (gcorec F op next)) := by
  unfold gcorec
  rw [Seq.gcorec_some]
  · simp [cons]
    rfl
  · simpa

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.destruct_nil** 是 Ma
thlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`
。
形式化陈述：destruct_nil {basis_hd : Real -> Real} {basis_tl : Basis} : destruct (nil 
: Multiseries basis_hd basis_tl) = none
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem destruct_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    destruct (nil : Multiseries basis_hd basis_tl) = none := by
  simp [destruct, nil]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.destruct_cons** 是 M
athlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries
`。
形式化陈述：destruct_cons {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real} {c
oef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} : dest
ruct (cons exp coef tl) = some (exp, coef, tl)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.destruct_cons`：∀ {α : Type u} (a : α) (s : Stream'.Seq α), (
Stream'.Seq.cons a s).destruct = some (a, s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem destruct_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    destruct (cons exp coef tl) = some (exp, coef, tl) := by
  simp [destruct, cons]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.destruct_eq_none** 
是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiser
ies`。
形式化陈述：destruct_eq_none {basis_hd : Real -> Real} {basis_tl : Basis} {ms : Multis
eries basis_hd basis_tl} (h : destruct ms = none) : ms = nil
参数：h : destruct ms = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.destruct_eq_none`：destruct_eq_none {s : Seq α} : destruct s 
= none -> s = nil
-/
theorem destruct_eq_none {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    (h : destruct ms = none) : ms = nil := by
  apply Stream'.Seq.destruct_eq_none
  simpa [destruct] using h

set_option backward.isDefEq.respectTransparency false in
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.destruct_eq_cons** 
是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiser
ies`。
形式化陈述：destruct_eq_cons {basis_hd : Real -> Real} {basis_tl : Basis} {ms : Multis
eries basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl} {tl
 : Multiseries basis_hd basis_tl} (h : destruct ms = some (exp, coef, tl)) : ms 
= cons exp coef tl
参数：h : destruct ms = some (exp, coef, tl)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.destruct_eq_cons`：destruct_eq_cons {s : Seq α} {a s'} : dest
ruct s = some (a, s') -> s = cons a s'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs.0.Tactic.Com
puteAsymptotics.MultiseriesExpansion.Multiseries.destruct_eq_destruct_map`：∀ {ba
sis_hd : ℝ → ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   (s : Stream'.Seq 
(ℝ × Tactic.ComputeAsymptotics.MultiseriesExpansion bas…
-/
theorem destruct_eq_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : destruct ms = some (exp, coef, tl)) : ms = cons exp coef tl := by
  apply Stream'.Seq.destruct_eq_cons
  rw [destruct_eq_destruct_map, h]
  rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.head_nil** 是 Mathli
b 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：head_nil {basis_hd : Real -> Real} {basis_tl : Basis} : (nil : Multiseries
 basis_hd basis_tl).head = none
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem head_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (nil : Multiseries basis_hd basis_tl).head = none := by
  simp [head, nil]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.head_cons** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：head_cons {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real} {coef 
: MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} : (cons ex
p coef tl).head = some (exp, coef)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.head_cons`：head_cons (a : α) (s) : head (cons a s) = some a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem head_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).head = some (exp, coef) := by
  simp [head, cons]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.tail_nil** 是 Mathli
b 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：tail_nil {basis_hd : Real -> Real} {basis_tl : Basis} : (nil : Multiseries
 basis_hd basis_tl).tail = nil
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tail_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    (nil : Multiseries basis_hd basis_tl).tail = nil := by
  simp [tail, nil]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.tail_cons** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：tail_cons {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real} {coef 
: MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} : (cons ex
p coef tl).tail = tl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tail_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).tail = tl := by
  simp [tail, cons]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.map_nil** 是 Mathlib
 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：map_nil {basis_hd basis_tl basis_hd' basis_tl'} (f : Real -> Real) (g : Mu
ltiseriesExpansion basis_tl -> MultiseriesExpansion basis_tl') : (nil : Multiser
ies basis_hd basis_tl).map f g = (nil : Multiseries basis_hd' basis_tl')
参数：f : Real -> Real；g : MultiseriesExpansion basis_tl -> MultiseriesExpansion ba
sis_tl'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_nil {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → ℝ)
    (g : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl') :
    (nil : Multiseries basis_hd basis_tl).map f g = (nil : Multiseries basis_hd' basis_tl') := by
  simp [map, nil]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.map_cons** 是 Mathli
b 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：map_cons {basis_hd basis_tl basis_hd' basis_tl'} (f : Real -> Real) (g : M
ultiseriesExpansion basis_tl -> MultiseriesExpansion basis_tl') {exp : Real} {co
ef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} : (cons
 exp coef tl).map f g = cons (basis_hd
参数：f : Real -> Real；g : MultiseriesExpansion basis_tl -> MultiseriesExpansion ba
sis_tl'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.map_cons`：∀ {α : Type u} {β : Type v} (f : α → β) (a : α) (s
 : Stream'.Seq α),   Stream'.Seq.map f (Stream'.Seq.cons a s) = Stream'.Seq.cons
 (f a) (St…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_cons {basis_hd basis_tl basis_hd' basis_tl'} (f : ℝ → ℝ)
    (g : MultiseriesExpansion basis_tl → MultiseriesExpansion basis_tl') {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).map f g = cons (basis_hd := basis_hd')
      (f exp) (g coef) (map f g tl) := by
  simp [map, cons]

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.map_id** 是 Mathlib 
中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：map_id {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) : ms.map (
fun exp => exp) (fun coef => coef) = ms
参数：ms : Multiseries basis_hd basis_tl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.map_id`：∀ {α : Type u} (s : Stream'.Seq α), Stream'.Seq.map 
id s = s
-/
theorem map_id {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    ms.map (fun exp => exp) (fun coef => coef) = ms :=
  Stream'.Seq.map_id ms

set_option backward.isDefEq.respectTransparency false in
@[simp← ]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.map_comp** 是 Mathli
b 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：map_comp {b₁ b₂ b₃ bs₁ bs₂ bs₃} (f₁ : Real -> Real) (g₁ : MultiseriesExpan
sion bs₁ -> MultiseriesExpansion bs₂) (f₂ : Real -> Real) (g₂ : MultiseriesExpan
sion bs₂ -> MultiseriesExpansion bs₃) (ms : Multiseries b₁ bs₁) : (ms.map (f₂ ∘ 
f₁) (g₂ ∘ g₁) : Multiseries b₃ bs₃) = (ms.map f₁ g₁ : Multiseries b₂ bs₂).map f₂
 g₂
参数：f₁ : Real -> Real；g₁ : MultiseriesExpansion bs₁ -> MultiseriesExpansion bs₂；f
₂ : Real -> Real；g₂ : MultiseriesExpansion bs₂ -> MultiseriesExpansion bs₃；ms : 
Multiseries b₁ bs₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem map_comp {b₁ b₂ b₃ bs₁ bs₂ bs₃}
    (f₁ : ℝ → ℝ) (g₁ : MultiseriesExpansion bs₁ → MultiseriesExpansion bs₂)
    (f₂ : ℝ → ℝ) (g₂ : MultiseriesExpansion bs₂ → MultiseriesExpansion bs₃)
    (ms : Multiseries b₁ bs₁) :
    (ms.map (f₂ ∘ f₁) (g₂ ∘ g₁) : Multiseries b₃ bs₃) =
    (ms.map f₁ g₁ : Multiseries b₂ bs₂).map f₂ g₂ := by
  simp [map, ← Stream'.Seq.map_comp]
  rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.notMem_nil** 是 Math
lib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：notMem_nil {basis_hd : Real -> Real} {basis_tl : Basis} {x : Real × Multis
eriesExpansion basis_tl} : x ∉ (nil : Multiseries basis_hd basis_tl)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.notMem_nil`：notMem_nil (a : α) : a ∉ @nil α
-/
theorem notMem_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x : ℝ × MultiseriesExpansion basis_tl} :
    x ∉ (nil : Multiseries basis_hd basis_tl) :=
  Seq.notMem_nil _

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.mem_cons_iff** 是 Ma
thlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`
。
形式化陈述：mem_cons_iff {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real} {co
ef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} {x : Re
al × MultiseriesExpansion basis_tl} : x in cons exp coef tl ↔ x = (exp, coef) ∨ 
x in tl
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.mem_cons_iff`：mem_cons_iff {a b : α} {s : Seq α} : a in cons
 b s ↔ a = b ∨ a in s
-/
theorem mem_cons_iff {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {x : ℝ × MultiseriesExpansion basis_tl} :
    x ∈ cons exp coef tl ↔ x = (exp, coef) ∨ x ∈ tl :=
  Seq.mem_cons_iff

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Pairwise_nil** 是 Ma
thlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`
。
形式化陈述：Pairwise_nil {basis_hd : Real -> Real} {basis_tl : Basis} {R} : Seq.Pairwi
se R (nil : Multiseries basis_hd basis_tl)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem Pairwise_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {R} :
    Seq.Pairwise R (nil : Multiseries basis_hd basis_tl) := by
  simp [nil]

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Pairwise_cons_nil**
 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multise
ries`。
形式化陈述：Pairwise_cons_nil {basis_hd : Real -> Real} {basis_tl : Basis} {R exp coef
} : Seq.Pairwise R (cons exp coef (nil : Multiseries basis_hd basis_tl))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem Pairwise_cons_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {R exp coef} :
    Seq.Pairwise R (cons exp coef (nil : Multiseries basis_hd basis_tl)) := by
  simp [cons, nil]

end simp

end Multiseries

/-- Convert a real number to a multiseries in an empty basis. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.ofReal** 是 Mathlib 中的一个定义，位于命名空
间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：ofReal (c : Real) : MultiseriesExpansion []
参数：c : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a real number to a multiseries in an empty basis.
-/
def ofReal (c : ℝ) : MultiseriesExpansion [] := c

/-- Convert a multiseries in an empty basis to a real number. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.toReal** 是 Mathlib 中的一个定义，位于命名空
间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：toReal (ms : MultiseriesExpansion []) : Real
参数：ms : MultiseriesExpansion []。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a multiseries in an empty basis to a real number.
-/
def toReal (ms : MultiseriesExpansion []) : ℝ := ms

/-- Convert a multiseries in a non-empty basis to a sequence of pairs `(exp, coef)`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.seq** 是 Mathlib 中的一个定义，位于命名空间 `
Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：seq {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl))
 : Multiseries basis_hd basis_tl
参数：ms : MultiseriesExpansion (basis_hd :: basis_tl)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a multiseries in a non-empty basis to a sequence of pairs `(exp, coef)`.
-/
def seq {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    Multiseries basis_hd basis_tl :=
  ms.1

/-- Convert a multiseries to a function. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.toFun** 是 Mathlib 中的一个定义，位于命名空间
 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：toFun {basis : Basis} (ms : MultiseriesExpansion basis) : Real -> Real
参数：ms : MultiseriesExpansion basis。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a multiseries to a function.
-/
def toFun {basis : Basis} (ms : MultiseriesExpansion basis) : ℝ → ℝ :=
  match basis with
  | [] => fun _ ↦ ms.toReal
  | .cons _ _ =>  ms.2

/-- Constructs a multiseries from a `Multiseries basis_hd basis_tl` and a function. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.mk** 是 Mathlib 中的一个定义，位于命名空间 `T
actic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：mk {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : Real -> Re
al) : MultiseriesExpansion (basis_hd :: basis_tl)
参数：s : Multiseries basis_hd basis_tl；f : Real -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a multiseries from a `Multiseries basis_hd basis_tl` and a function.
-/
def mk {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : ℝ → ℝ) :
    MultiseriesExpansion (basis_hd :: basis_tl) :=
  (s, f)

/-- Recursion principle for `MultiseriesExpansion (basis_hd :: basis_tl)`. -/
@[cases_eliminator]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.recOn** 是 Mathlib 中的一个定义，位于命名空间
 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：recOn {basis_hd basis_tl} {motive : MultiseriesExpansion (basis_hd :: basi
s_tl) -> Sort*} (nil : forall f, motive (mk .nil f)) (cons : forall exp coef tl 
f, motive (.mk (.cons exp coef tl) f)) (ms : MultiseriesExpansion (basis_hd :: b
asis_tl)) : motive ms
参数：basis_hd :: basis_tl；nil : forall f, motive (mk .nil f)；cons : forall exp coe
f tl f, motive (.mk (.cons exp coef tl) f)；ms : MultiseriesExpansion (basis_hd :
: basis_tl)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle for `MultiseriesExpansion (basis_hd :: basis_tl)`.
-/
def recOn {basis_hd basis_tl} {motive : MultiseriesExpansion (basis_hd :: basis_tl) → Sort*}
    (nil : ∀ f, motive (mk .nil f))
    (cons : ∀ exp coef tl f, motive (.mk (.cons exp coef tl) f))
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : motive ms := by
  let ⟨s, f⟩ := ms
  cases s with
  | nil => apply nil
  | cons hd tl => apply cons
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.** 是 Mathlib 中的一个实例，位于命名空间 `Tac
tic.ComputeAsymptotics.MultiseriesExpansion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (basis : Basis) : Inhabited (MultiseriesExpansion basis) :=
  match basis with
  | [] => ⟨(default : ℝ)⟩
  | List.cons basis_hd basis_tl => ⟨(default : Multiseries basis_hd basis_tl × (ℝ → ℝ))⟩
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.eq_mk** 是 Mathlib 中的一个定理，位于命名空间
 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：eq_mk {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl
)) : ms = mk ms.seq ms.toFun
参数：ms : MultiseriesExpansion (basis_hd :: basis_tl)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_mk {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    ms = mk ms.seq ms.toFun := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.mk_eq_mk_iff** 是 Mathlib 中的一个定理
，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：mk_eq_mk_iff {basis_hd basis_tl} (s t : Multiseries basis_hd basis_tl) (f 
g : Real -> Real) : mk (basis_hd
参数：s t : Multiseries basis_hd basis_tl；f g : Real -> Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.mk.eq_1`：∀ {basis_hd : ℝ 
→ ℝ} {basis_tl : Tactic.ComputeAsymptotics.Basis}   (s : Tactic.ComputeAsymptoti
cs.MultiseriesExpansion.Multiseries basis_hd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_eq_mk_iff {basis_hd basis_tl} (s t : Multiseries basis_hd basis_tl) (f g : ℝ → ℝ) :
    mk (basis_hd := basis_hd) s f = mk (basis_hd := basis_hd) t g ↔ s = t ∧ f = g where
  mp h := by rwa [mk, mk, Prod.mk_inj] at h
  mpr h := by simp [h]

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.ms_eq_mk_iff** 是 Mathlib 中的一个定理
，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：ms_eq_mk_iff {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: b
asis_tl)) (s : Multiseries basis_hd basis_tl) (f : Real -> Real) : ms = mk s f ↔
 ms.seq = s ∧ ms.toFun = f
参数：ms : MultiseriesExpansion (basis_hd :: basis_tl)；s : Multiseries basis_hd bas
is_tl；f : Real -> Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.eq_mk`：eq_mk {basis_hd ba
sis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : ms = mk ms.seq ms.t
oFun
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.mk_eq_mk_iff`：mk_eq_mk_if
f {basis_hd basis_tl} (s t : Multiseries basis_hd basis_tl) (f g : Real -> Real)
 : mk (basis_hd
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ms_eq_mk_iff {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl))
    (s : Multiseries basis_hd basis_tl) (f : ℝ → ℝ) : ms = mk s f ↔ ms.seq = s ∧ ms.toFun = f := by
  conv => lhs; lhs; rw [eq_mk ms]
  rw [mk_eq_mk_iff]

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.mk_eq_mk_iff_iff** 是 Mathlib 中的
一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：mk_eq_mk_iff_iff {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd 
:: basis_tl)) (s : Multiseries basis_hd basis_tl) (f : Real -> Real) : mk s f = 
ms ↔ ms.seq = s ∧ ms.toFun = f
参数：ms : MultiseriesExpansion (basis_hd :: basis_tl)；s : Multiseries basis_hd bas
is_tl；f : Real -> Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.ms_eq_mk_iff`：ms_eq_mk_if
f {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl)) (s : Mu
ltiseries basis_hd basis_tl) (f : Real -> Real) :…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_mk_iff_iff {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl))
    (s : Multiseries basis_hd basis_tl) (f : ℝ → ℝ) :
    mk s f = ms ↔ ms.seq = s ∧ ms.toFun = f := by
  rw [@Eq.comm _ (mk s f) ms, ms_eq_mk_iff]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.ext_iff** 是 Mathlib 中的一个定理，位于命名
空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：ext_iff {basis_hd basis_tl} (ms₁ ms₂ : MultiseriesExpansion (basis_hd :: b
asis_tl)) : ms₁ = ms₂ ↔ ms₁.seq = ms₂.seq ∧ ms₁.toFun = ms₂.toFun where mp h
参数：ms₁ ms₂ : MultiseriesExpansion (basis_hd :: basis_tl)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.eq_mk`：eq_mk {basis_hd ba
sis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : ms = mk ms.seq ms.t
oFun
-/
theorem ext_iff {basis_hd basis_tl}
    (ms₁ ms₂ : MultiseriesExpansion (basis_hd :: basis_tl)) :
    ms₁ = ms₂ ↔ ms₁.seq = ms₂.seq ∧ ms₁.toFun = ms₂.toFun where
  mp h := by simp [h]
  mpr h := by
    rw [eq_mk ms₁, eq_mk ms₂]
    simp [h]

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.ofReal_toReal** 是 Mathlib 中的一个定
理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：ofReal_toReal (x : Real) : (ofReal x).toReal = x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofReal_toReal (x : ℝ) : (ofReal x).toReal = x := rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.toReal_ofReal** 是 Mathlib 中的一个定
理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：toReal_ofReal (ms : MultiseriesExpansion []) : ofReal ms.toReal = ms
参数：ms : MultiseriesExpansion []。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toReal_ofReal (ms : MultiseriesExpansion []) : ofReal ms.toReal = ms := rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.const_toFun** 是 Mathlib 中的一个定理，
位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：const_toFun (ms : MultiseriesExpansion []) : ms.toFun = fun _ => ms.toReal
参数：ms : MultiseriesExpansion []。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_toFun (ms : MultiseriesExpansion []) : ms.toFun = fun _ ↦ ms.toReal := rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.mk_toFun** 是 Mathlib 中的一个定理，位于命
名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：mk_toFun {basis_hd basis_tl} {s : Multiseries basis_hd basis_tl} {f : Real
 -> Real} : (mk (basis_hd
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_toFun {basis_hd basis_tl} {s : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} :
    (mk (basis_hd := basis_hd) s f).toFun = f := rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.mk_seq** 是 Mathlib 中的一个定理，位于命名空
间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：mk_seq {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : Real -
> Real) : (mk (basis_hd
参数：s : Multiseries basis_hd basis_tl；f : Real -> Real。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_seq {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f : ℝ → ℝ) :
    (mk (basis_hd := basis_hd) s f).seq = s := rfl

/-- Replace the function attached to a multiseries. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.replaceFun** 是 Mathlib 中的一个定义，位
于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：replaceFun {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: bas
is_tl)) (f : Real -> Real) : MultiseriesExpansion (basis_hd :: basis_tl)
参数：ms : MultiseriesExpansion (basis_hd :: basis_tl)；f : Real -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Replace the function attached to a multiseries.
-/
def replaceFun {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd :: basis_tl))
    (f : ℝ → ℝ) : MultiseriesExpansion (basis_hd :: basis_tl) :=
  mk ms.seq f

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.mk_replaceFun** 是 Mathlib 中的一个定
理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：mk_replaceFun {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) (f g
 : Real -> Real) : (mk (basis_hd
参数：s : Multiseries basis_hd basis_tl；f g : Real -> Real。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_replaceFun {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl)
    (f g : ℝ → ℝ) :
    (mk (basis_hd := basis_hd) s f).replaceFun g = mk (basis_hd := basis_hd) s g :=
  rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.replaceFun_toFun** 是 Mathlib 中的
一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：replaceFun_toFun {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd 
:: basis_tl)) (f : Real -> Real) : (ms.replaceFun f).toFun = f
参数：ms : MultiseriesExpansion (basis_hd :: basis_tl)；f : Real -> Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replaceFun_toFun {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) (f : ℝ → ℝ) :
    (ms.replaceFun f).toFun = f := rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.replaceFun_seq** 是 Mathlib 中的一个
定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：replaceFun_seq {basis_hd basis_tl} (ms : MultiseriesExpansion (basis_hd ::
 basis_tl)) (f : Real -> Real) : (ms.replaceFun f).seq = ms.seq
参数：ms : MultiseriesExpansion (basis_hd :: basis_tl)；f : Real -> Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replaceFun_seq {basis_hd basis_tl}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) (f : ℝ → ℝ) :
    (ms.replaceFun f).seq = ms.seq := rfl

section leadingExp

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}
  {ms : MultiseriesExpansion (basis_hd :: basis_tl)}

namespace Multiseries

/-- The leading exponent of a multiseries with non-empty basis. For `ms = []` it is `⊥`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.leadingExp** 是 Math
lib 中的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：leadingExp (s : Multiseries basis_hd basis_tl) : WithBot Real
参数：s : Multiseries basis_hd basis_tl。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The leading exponent of a multiseries with non-empty basis. For `ms = []` it is 
`⊥`.
-/
def leadingExp (s : Multiseries basis_hd basis_tl) : WithBot ℝ :=
  match s.head with
  | none => ⊥
  | some (exp, _) => exp

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.leadingExp_nil** 是 
Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiserie
s`。
形式化陈述：leadingExp_nil : (nil : Multiseries basis_hd basis_tl).leadingExp = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leadingExp_nil : (nil : Multiseries basis_hd basis_tl).leadingExp = ⊥ :=
  rfl

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.leadingExp_cons** 是
 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseri
es`。
形式化陈述：leadingExp_cons {exp : Real} {coef : MultiseriesExpansion basis_tl} {tl : 
Multiseries basis_hd basis_tl} : (cons exp coef tl).leadingExp = exp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leadingExp_cons {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).leadingExp = exp :=
  rfl

/-- `ms.leadingExp = ⊥` iff `ms = []`. -/
@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.leadingExp_eq_bot**
 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multise
ries`。
形式化陈述：leadingExp_eq_bot (s : Multiseries basis_hd basis_tl) : s.leadingExp = ⊥ ↔
 s = nil
参数：s : Multiseries basis_hd basis_tl。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`ms.leadingExp = ⊥` iff `ms = []`.
-/
theorem leadingExp_eq_bot (s : Multiseries basis_hd basis_tl) :
    s.leadingExp = ⊥ ↔ s = nil := by
  cases s <;> simp

end Multiseries

/-- The leading exponent of a multiseries with non-empty basis. For `ms = []` it is `⊥`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.leadingExp** 是 Mathlib 中的一个定义，位
于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：leadingExp (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : WithBot Re
al
参数：ms : MultiseriesExpansion (basis_hd :: basis_tl)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The leading exponent of a multiseries with non-empty basis. For `ms = []` it is 
`⊥`.
-/
def leadingExp (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : WithBot ℝ :=
  ms.seq.leadingExp

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.leadingExp_def** 是 Mathlib 中的一个
定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：leadingExp_def (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : leadin
gExp ms = ms.seq.leadingExp
参数：ms : MultiseriesExpansion (basis_hd :: basis_tl)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leadingExp_def (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    leadingExp ms = ms.seq.leadingExp := rfl

end leadingExp

section Sorted

/-- Auxiliary instance for the order on pairs `(exp, coef)` used below to define `Sorted` in terms
of `Stream'.Seq.Pairwise`. `(exp₁, coef₁) ≤ (exp₂, coef₂)` iff `exp₁ ≤ exp₂`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.** 是 Mathlib 中的一个实例，位于命名空间 `Tac
tic.ComputeAsymptotics.MultiseriesExpansion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary instance for the order on pairs `(exp, coef)` used below to define `So
rted` in terms
of `Stream'.Seq.Pairwise`. `(exp₁, coef₁) ≤ (exp₂, coef₂)` iff `exp₁ ≤ exp₂`.
-/
scoped instance {basis} : Preorder (ℝ × MultiseriesExpansion basis) := Preorder.lift Prod.fst
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.lt_iff_lt** 是 Mathlib 中的一个定理，位于
命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem lt_iff_lt {basis} {exp1 exp2 : ℝ} {coef1 coef2 : MultiseriesExpansion basis} :
    (exp1, coef1) < (exp2, coef2) ↔ exp1 < exp2 := by
  rfl

/-- A multiseries `ms` is `Sorted` when the exponents at each of its levels are sorted. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted** 是 Mathlib 中的一个归纳类型，位于命
名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：{basis : Tactic.ComputeAsymptotics.Basis} → Tactic.ComputeAsymptotics.Mult
iseriesExpansion basis → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiseries `ms` is `Sorted` when the exponents at each of its levels are sort
ed.
-/
inductive Sorted : {basis : Basis} → (MultiseriesExpansion basis) → Prop
| const (ms : MultiseriesExpansion []) : ms.Sorted
| seq {hd} {tl} (ms : MultiseriesExpansion (hd :: tl))
    (h_coef : ∀ x ∈ ms.seq, x.2.Sorted)
    (h_Pairwise : Seq.Pairwise (· > ·) ms.seq) : ms.Sorted

/-- A multiseries `ms` is `Sorted` when the exponents at each of its levels are sorted. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Sorted** 是 Mathlib 
中的一个定义，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries`。
形式化陈述：{basis_hd : ℝ → ℝ} →   {basis_tl : Tactic.ComputeAsymptotics.Basis} →     
Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries basis_hd basis_tl → P
rop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiseries `ms` is `Sorted` when the exponents at each of its levels are sort
ed.
-/
def Multiseries.Sorted {basis_hd basis_tl} (s : Multiseries basis_hd basis_tl) : Prop :=
  (mk s 0).Sorted (basis := basis_hd :: basis_tl)

variable {basis_hd : ℝ → ℝ} {basis_tl : Basis}

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.sorted_iff_seq_sorted** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：sorted_iff_seq_sorted {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
 ms.Sorted ↔ ms.seq.Sorted where mp h
参数：basis_hd :: basis_tl。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem sorted_iff_seq_sorted {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    ms.Sorted ↔ ms.seq.Sorted where
  mp h := by
    cases h with | seq _ h_coef h_Pairwise =>
    constructor
    · simpa using h_coef
    · simpa using h_Pairwise
  mpr h := by
    cases h with | seq _ h_coef h_Pairwise =>
    constructor
    · simpa using h_coef
    · simpa using h_Pairwise

namespace Multiseries.Sorted

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Sorted.nil** 是 Math
lib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.So
rted`。
形式化陈述：nil : Sorted (nil : Multiseries basis_hd basis_tl)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem nil : Sorted (nil : Multiseries basis_hd basis_tl) := by
  constructor <;> simp

/-- `[(exp, coef)]` is `Sorted` when `coef` is `Sorted`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Sorted.cons_nil** 是
 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseri
es.Sorted`。
形式化陈述：cons_nil {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion bas
is_tl} (h_coef : coef.Sorted) : Sorted (cons exp coef (.nil : Multiseries basis_
hd basis_tl))
参数：h_coef : coef.Sorted。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
`[(exp, coef)]` is `Sorted` when `coef` is `Sorted`.
-/
theorem cons_nil {basis_hd basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    (h_coef : coef.Sorted) :
    Sorted (cons exp coef (.nil : Multiseries basis_hd basis_tl)) := by
  constructor
  · simpa
  · simp
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Sorted.cons** 是 Mat
hlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.S
orted`。
形式化陈述：cons {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_t
l} {tl : Multiseries basis_hd basis_tl} (h_coef : coef.Sorted) (h_comp : leading
Exp tl < exp) (h_tl : tl.Sorted) : Sorted (cons exp coef tl)
参数：h_coef : coef.Sorted；h_comp : leadingExp tl < exp；h_tl : tl.Sorted。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Stream'.Seq.Pairwise_cons_nil`：Pairwise_cons_nil {R : α -> α -> Prop} {h
d : α} : Pairwise R (cons hd nil)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.Seq.Pairwise.cons_cons_of_trans`：∀ {α : Type u} {R : α → α → Pro
p} [IsTrans α R] {hd tl_hd : α} {tl_tl : Stream'.Seq α},   R hd tl_hd →     Stre
am'.Seq.Pairwise R (Stream'.S…
· 使用定理 `instIsTransGt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 < x1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem cons {basis_hd basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl}
    (h_coef : coef.Sorted)
    (h_comp : leadingExp tl < exp)
    (h_tl : tl.Sorted) :
    Sorted (cons exp coef tl) := by
  cases h_tl with | seq _ h_tl_coef h_tl_tl =>
  constructor
  · simp at h_tl_coef ⊢
    grind
  · cases tl
    · exact Seq.Pairwise_cons_nil
    · exact h_tl_tl.cons_cons_of_trans (by simpa [lt_iff_lt] using h_comp)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `cons (exp, coef) tl` is `Sorted`, then `coef` and `tl` are `Sorted`, and the
leading exponent of `tl` is less than `exp`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Sorted.elim_cons** 
是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiser
ies.Sorted`。
形式化陈述：elim_cons {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion ba
sis_tl} {tl : Multiseries basis_hd basis_tl} (h : (Multiseries.cons exp coef tl)
.Sorted) : coef.Sorted ∧ leadingExp tl < exp ∧ tl.Sorted
参数：h : (Multiseries.cons exp coef tl).Sorted。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.Seq.Pairwise.cons_elim`：∀ {α : Type u} {R : α → α → Prop} {hd : 
α} {tl : Stream'.Seq α},   Stream'.Seq.Pairwise R (Stream'.Seq.cons hd tl) → (∀ 
x ∈ tl, R hd x) ∧ St…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
If `cons (exp, coef) tl` is `Sorted`, then `coef` and `tl` are `Sorted`, and the
leading exponent of `tl` is less than `exp`.
-/
theorem elim_cons {basis_hd basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} (h : (Multiseries.cons exp coef tl).Sorted) :
    coef.Sorted ∧ leadingExp tl < exp ∧ tl.Sorted := by
  cases h with | seq _ h_coef h_Pairwise =>
  constructor
  · simpa using h_coef (exp, coef) (by simp)
  cases tl with
  | nil => simp
  | cons tl_exp tl_coef tl_tl =>
  obtain ⟨h_all, h_Pairwise⟩ := h_Pairwise.cons_elim
  constructor
  · simp only [leadingExp_cons, WithBot.coe_lt_coe]
    exact h_all (tl_exp, tl_coef) (by simp [Multiseries.cons])
  · exact Sorted.seq _ (fun x hx ↦ h_coef _ (by simp_all)) h_Pairwise
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Sorted.tail** 是 Mat
hlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.S
orted`。
形式化陈述：tail {ms : Multiseries basis_hd basis_tl} (h : ms.Sorted) : ms.tail.Sorted
参数：h : ms.Sorted。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.tail_nil`：tai
l_nil {basis_hd : Real -> Real} {basis_tl : Basis} : (nil : Multiseries basis_hd
 basis_tl).tail = nil
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.tail_cons`：ta
il_cons {basis_hd : Real -> Real} {basis_tl : Basis} {exp : Real} {coef : Multis
eriesExpansion basis_tl} {tl : Multiseries basis_hd basis_…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Sorted.elim_c
ons`：elim_cons {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion bas
is_tl} {tl : Multiseries basis_hd basis_tl} (h : (Multiseries.con…
-/
theorem tail {ms : Multiseries basis_hd basis_tl} (h : ms.Sorted) :
    ms.tail.Sorted := by
  cases ms with
  | nil => simp
  | cons exp coef tl => simpa using h.elim_cons.right.right

/-- Coinduction principle for proving `Sorted`. Given a predicate `motive` on multiseries,
if `motive ms` holds (base case) and the predicate "survives" destruction of its argument, then
`ms` is `Sorted`. Here "survives" means that if `x = cons (exp, coef) tl`, then `motive x` must
imply `coef.Sorted`, `tl.leadingExp < exp`, and `motive tl`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Sorted.coind** 是 Ma
thlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.
Sorted`。
形式化陈述：coind {s : Multiseries basis_hd basis_tl} (motive : (ms : Multiseries basi
s_hd basis_tl) -> Prop) (h_base : motive s) (h_step : forall exp coef tl, motive
 (.cons exp coef tl) -> coef.Sorted ∧ leadingExp tl < exp ∧ motive tl) : s.Sorte
d
参数：motive : (ms : Multiseries basis_hd basis_tl) -> Prop；h_base : motive s；h_ste
p : forall exp coef tl, motive (.cons exp coef tl) -> coef.Sorted ∧ leadingExp t
l < exp ∧ motive tl。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.all_coind`：all_coind {s : Seq α} {p : α -> Prop} (motive : S
eq α -> Prop) (base : motive s) (step : forall hd tl, motive (.cons hd tl) -> p 
hd ∧ motive…
· 使用定理 `Stream'.Seq.Pairwise.coind_trans`：∀ {α : Type u} {R : α → α → Prop} [IsT
rans α R] {s : Stream'.Seq α} (motive : Stream'.Seq α → Prop),   motive s →     
(∀ (hd : α) (tl : Stre…
· 使用定理 `instIsTransGt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 < x1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gt_iff_lt`：∀ {α : Type u_1} [inst : LT α] {x y : α}, x > y ↔ y < x
· 使用定理 `_private.Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs.0.Tactic.Com
puteAsymptotics.MultiseriesExpansion.lt_iff_lt`：∀ {basis : Tactic.ComputeAsympto
tics.Basis} {exp1 exp2 : ℝ}   {coef1 coef2 : Tactic.ComputeAsymptotics.Multiseri
esExpansion basis}, (exp1, c…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Stream'.Seq.head_cons`：head_cons (a : α) (s) : head (cons a s) = some a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)

--- 原说明 ---
Coinduction principle for proving `Sorted`. Given a predicate `motive` on multis
eries,
if `motive ms` holds (base case) and the predicate "survives" destruction of its
 argument, then
`ms` is `Sorted`. Here "survives" means that if `x = cons (exp, coef) tl`, then 
`motive x` must
imply `coef.Sorted`, `tl.leadingExp < exp`, and `motive tl`.
-/
theorem coind {s : Multiseries basis_hd basis_tl}
    (motive : (ms : Multiseries basis_hd basis_tl) → Prop)
    (h_base : motive s)
    (h_step : ∀ exp coef tl, motive (.cons exp coef tl) →
        coef.Sorted ∧
        leadingExp tl < exp ∧
        motive tl) :
    s.Sorted := by
  constructor
  · apply Seq.all_coind
    · exact h_base
    · intro (exp, coef) tl h
      grind [h_step exp coef tl h]
  · apply Seq.Pairwise.coind_trans
    · exact h_base
    · intro (exp, coef) tl h
      constructor
      · intro (tl_exp, tl_coef) h_tl
        rw [gt_iff_lt, lt_iff_lt]
        replace h_step := (h_step exp coef tl h).right.left
        cases tl <;> simp [leadingExp, head] at h_tl h_step
        grind
      · grind [h_step exp coef tl h]

end Multiseries.Sorted

namespace Sorted

/-- `[]` is `Sorted`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted.nil** 是 Mathlib 中的一个定理，位
于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted`。
形式化陈述：nil (f : Real -> Real) : Sorted (basis
参数：f : Real -> Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
`[]` is `Sorted`.
-/
theorem nil (f : ℝ → ℝ) : Sorted (basis := basis_hd :: basis_tl) (mk .nil f) := by
  simp

/-- `[(exp, coef)]` is `Sorted` when `coef` is `Sorted`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted.cons_nil** 是 Mathlib 中的一
个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted`。
形式化陈述：cons_nil {exp : Real} {coef : MultiseriesExpansion basis_tl} {f : Real -> 
Real} (h_coef : coef.Sorted) : Sorted (basis
参数：h_coef : coef.Sorted。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Sorted.cons_n
il`：cons_nil {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion basis
_tl} (h_coef : coef.Sorted) : Sorted (cons exp coef (.nil : Mult…

--- 原说明 ---
`[(exp, coef)]` is `Sorted` when `coef` is `Sorted`.
-/
theorem cons_nil {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {f : ℝ → ℝ}
    (h_coef : coef.Sorted) :
    Sorted (basis := basis_hd :: basis_tl) (mk (.cons exp coef .nil) f) := by
  simp [Multiseries.Sorted.cons_nil h_coef]

/-- `cons (exp, coef) tl` is `Sorted` when `coef` and `tl` are `Sorted` and the leading
exponent of `tl` is less than `exp`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted.cons** 是 Mathlib 中的一个定理，
位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted`。
形式化陈述：cons {exp : Real} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries
 basis_hd basis_tl} {f : Real -> Real} (h_coef : coef.Sorted) (h_comp : tl.leadi
ngExp < exp) (h_tl : tl.Sorted) : Sorted (basis
参数：h_coef : coef.Sorted；h_comp : tl.leadingExp < exp；h_tl : tl.Sorted。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Sorted.cons`：
cons {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl} {tl
 : Multiseries basis_hd basis_tl} (h_coef : coef.Sorted) (h_…

--- 原说明 ---
`cons (exp, coef) tl` is `Sorted` when `coef` and `tl` are `Sorted` and the lead
ing
exponent of `tl` is less than `exp`.
-/
theorem cons {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl}
    {f : ℝ → ℝ}
    (h_coef : coef.Sorted)
    (h_comp : tl.leadingExp < exp)
    (h_tl : tl.Sorted) :
    Sorted (basis := basis_hd :: basis_tl) (mk (.cons exp coef tl) f) := by
  simp [Multiseries.Sorted.cons h_coef h_comp h_tl]

/-- If `cons (exp, coef) tl` is `Sorted`, then `coef` and `tl` are `Sorted`, and the
leading exponent of `tl` is less than `exp`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted.elim_cons** 是 Mathlib 中的
一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted`。
形式化陈述：elim_cons {exp : Real} {coef : MultiseriesExpansion basis_tl} {tl : Multis
eries basis_hd basis_tl} {f : Real -> Real} (h : Sorted (basis
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Multiseries.Sorted.elim_c
ons`：elim_cons {basis_hd basis_tl} {exp : Real} {coef : MultiseriesExpansion bas
is_tl} {tl : Multiseries basis_hd basis_tl} (h : (Multiseries.con…

--- 原说明 ---
If `cons (exp, coef) tl` is `Sorted`, then `coef` and `tl` are `Sorted`, and the
leading exponent of `tl` is less than `exp`.
-/
theorem elim_cons {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ}
    (h : Sorted (basis := basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) :
    coef.Sorted ∧ tl.leadingExp < exp ∧ tl.Sorted := by
  apply Multiseries.Sorted.elim_cons (by simpa using h)
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted.replaceFun** 是 Mathlib 中
的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Sorted`。
形式化陈述：replaceFun {ms : MultiseriesExpansion (basis_hd :: basis_tl)} {f : Real ->
 Real} (h_sorted : ms.Sorted) : (ms.replaceFun f).Sorted
参数：basis_hd :: basis_tl；h_sorted : ms.Sorted。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replaceFun {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    {f : ℝ → ℝ} (h_sorted : ms.Sorted) :
    (ms.replaceFun f).Sorted := by
  simpa using h_sorted

end Sorted

end Sorted

section Approximates

/-- Coinductive predicate stating that `ms` approximates its attached function on `basis`.
* If `basis = []`, i.e. `ms` is just a real number, `Approximates` holds unconditionally.
* If `basis = basis_hd :: basis_tl` and `ms = nil`, then `f =ᶠ[atTop] 0`.
* If `basis = basis_hd :: basis_tl` and `ms = cons exp coef tl`, then
  `f` is `Majorized` with exponent `exp` by `basis_hd`,
  `coef` approximates its attached function, and
  `tl` approximates `f - basis_hd ^ exp * coef.toFun`.
-/
coinductive Approximates : {basis : Basis} → (ms : MultiseriesExpansion basis) → Prop
/-- Constant multiseries always approximates its attached function. -/
| const (ms : MultiseriesExpansion []) : Approximates ms
/-- Empty multiseries approximates (eventually) zero function. -/
| nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ} (hf : f =ᶠ[atTop] 0) :
  Approximates (mk (@Multiseries.nil basis_hd basis_tl) f)
/-- `cons (exp, coef) tl` approximates `f` when `coef` approximates some function `fC`, `f` is
majorized with exponent `exp` by `basis_hd`, and `tl` approximates `f - fC * basis_hd ^ exp`. -/
| cons {basis_hd f : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl}
    (h_coef : Approximates coef) (h_maj : Majorized f basis_hd exp)
    (h_tl : Approximates (mk tl (f - basis_hd ^ exp * coef.toFun))) :
  Approximates (mk (.cons exp coef tl) f)

variable {f basis_hd : ℝ → ℝ} {basis_tl : Basis}

attribute [simp] Approximates.const

namespace Approximates

/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.coind** 是 Mathlib 
中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates`。
形式化陈述：coind {ms : MultiseriesExpansion (basis_hd :: basis_tl)} (motive : Multise
riesExpansion (basis_hd :: basis_tl) -> Prop) (h_base : motive ms) (h_step : for
all ms, motive ms -> (ms.seq = .nil ∧ ms.toFun =ᶠ[atTop] 0) ∨ (exists exp coef t
l, ms.seq = .cons exp coef tl ∧ coef.Approximates ∧ Majorized ms.toFun basis_hd 
exp ∧ motive (mk (basis_hd
参数：basis_hd :: basis_tl；motive : MultiseriesExpansion (basis_hd :: basis_tl) -> 
Prop；h_base : motive ms。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.coinduct`：∀ 
(pred : {basis : Tactic.ComputeAsymptotics.Basis} → Tactic.ComputeAsymptotics.Mu
ltiseriesExpansion basis → Prop),   (∀ {basis : Tactic.Com…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem coind {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    (motive : MultiseriesExpansion (basis_hd :: basis_tl) → Prop)
    (h_base : motive ms)
    (h_step : ∀ ms, motive ms →
      (ms.seq = .nil ∧ ms.toFun =ᶠ[atTop] 0) ∨
      (∃ exp coef tl, ms.seq = .cons exp coef tl ∧
        coef.Approximates ∧
        Majorized ms.toFun basis_hd exp ∧
        motive (mk (basis_hd := basis_hd) tl (ms.toFun - basis_hd ^ exp * coef.toFun)))) :
    ms.Approximates := by
  apply coinduct fun {basis} ms =>
    ms.Approximates ∨ ∃ (h_basis : basis = basis_hd :: basis_tl), (motive (h_basis ▸ ms))
  · rintro basis ms (h_ms | ⟨rfl, h_ms⟩)
    · cases h_ms <;> grind
    simp only [reduceCtorEq, List.cons.injEq, ↓existsAndEq, and_true, heq_eq_eq, ms_eq_mk_iff,
      true_and, exists_eq_right_right', exists_and_left, false_or] at h_ms ⊢
    rcases h_step _ h_ms with h_step | ⟨exp, coef, tl, h_seq, h_coef, h_maj, h_tl⟩
    · grind
    · refine .inr ⟨basis_hd, ms.toFun, basis_tl, exp, coef, by simpa, ‹_›, tl, ?_⟩
      simp
      grind
  · grind

/-- If `[]` approximates `f`, then `f = 0` eventually. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.elim_nil** 是 Mathl
ib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates`。
形式化陈述：elim_nil (h : @Approximates (basis_hd :: basis_tl) (mk .nil f)) : f =ᶠ[atT
op] 0
参数：h : @Approximates (basis_hd :: basis_tl) (mk .nil f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False

--- 原说明 ---
If `[]` approximates `f`, then `f = 0` eventually.
-/
theorem elim_nil (h : @Approximates (basis_hd :: basis_tl) (mk .nil f)) :
    f =ᶠ[atTop] 0 := by
  generalize h_ms : (mk .nil f) = ms at h
  cases h <;> simp at h_ms; grind

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.nil_iff** 是 Mathli
b 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates`。
形式化陈述：nil_iff {f : Real -> Real} : (mk (basis_hd
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.elim_nil`：el
im_nil (h : @Approximates (basis_hd :: basis_tl) (mk .nil f)) : f =ᶠ[atTop] 0
-/
theorem nil_iff {f : ℝ → ℝ} :
    (mk (basis_hd := basis_hd) (basis_tl := basis_tl) .nil f).Approximates ↔ f =ᶠ[atTop] 0 :=
  ⟨elim_nil, nil⟩

/-- If `cons (exp, coef) tl` approximates `f`, then `f` can be Majorized with exponent `exp`, and
there exists function `fC` such that `coef` approximates `fC` and `tl` approximates
`f - fC * basis_hd ^ exp`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.elim_cons** 是 Math
lib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates`。
形式化陈述：elim_cons {exp : Real} {coef : MultiseriesExpansion basis_tl} {tl : Multis
eries basis_hd basis_tl} (h : Approximates (basis
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
If `cons (exp, coef) tl` approximates `f`, then `f` can be Majorized with expone
nt `exp`, and
there exists function `fC` such that `coef` approximates `fC` and `tl` approxima
tes
`f - fC * basis_hd ^ exp`.
-/
theorem elim_cons {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : Approximates (basis := basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) :
    coef.Approximates ∧
    Majorized f basis_hd exp ∧
    (mk (basis_hd := basis_hd) tl (f - basis_hd ^ exp * coef.toFun)).Approximates := by
  generalize h_ms : (mk (.cons exp coef tl) f) = ms at h
  cases h <;> simp at h_ms; grind

/-- One can replace `f` in `Approximates` with the function that eventually equals `f`. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.replaceFun** 是 Mat
hlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates`
。
形式化陈述：replaceFun {ms : MultiseriesExpansion (basis_hd :: basis_tl)} {f : Real ->
 Real} (h_equiv : ms.toFun =ᶠ[atTop] f) (h_approx : ms.Approximates) : (ms.repla
ceFun f).Approximates
参数：basis_hd :: basis_tl；h_equiv : ms.toFun =ᶠ[atTop] f；h_approx : ms.Approximate
s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.coind`：coind
 {ms : MultiseriesExpansion (basis_hd :: basis_tl)} (motive : MultiseriesExpansi
on (basis_hd :: basis_tl) -> Prop) (h_base : motive ms)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.elim_cons`：e
lim_cons {exp : Real} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries b
asis_hd basis_tl} (h : Approximates (basis
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Tactic.ComputeAsymptotics.Majorized.of_eventuallyEq`：of_eventuallyEq (h_
eq : g =ᶠ[atTop] f) (h : Majorized f b exp) : Majorized g b exp
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.mk_toFun`：mk_toFun {basis
_hd basis_tl} {s : Multiseries basis_hd basis_tl} {f : Real -> Real} : (mk (basi
s_hd
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'

--- 原说明 ---
One can replace `f` in `Approximates` with the function that eventually equals `
f`.
-/
theorem replaceFun {ms : MultiseriesExpansion (basis_hd :: basis_tl)} {f : ℝ → ℝ}
    (h_equiv : ms.toFun =ᶠ[atTop] f) (h_approx : ms.Approximates) :
    (ms.replaceFun f).Approximates := by
  let motive (ms : MultiseriesExpansion (basis_hd :: basis_tl)) : Prop :=
      ∃ (ms' : MultiseriesExpansion (basis_hd :: basis_tl)) (f' : ℝ → ℝ),
      ms = ms'.replaceFun f' ∧ ms'.Approximates ∧ ms'.toFun =ᶠ[atTop] f'
  apply Approximates.coind motive ⟨ms, f, by grind⟩
  rintro _ ⟨ms, f, rfl, h_approx, h_eq⟩
  cases ms with
  | nil g =>
    simp only [nil_iff, mk_toFun, mk_replaceFun, mk_seq, true_and,
      Multiseries.nil_ne_cons, false_and, exists_const, or_false] at h_approx h_eq ⊢
    grw [← h_eq, h_approx]
  | cons exp coef tl g =>
    obtain ⟨h_coef, h_maj, h_tl⟩ := h_approx.elim_cons
    refine .inr ⟨exp, coef, tl, ?_⟩
    simp only [mk_replaceFun, mk_seq, h_coef, mk_toFun, true_and]
    simp only [mk_toFun] at h_eq
    refine ⟨h_maj.of_eventuallyEq h_eq.symm, mk tl (g - basis_hd ^ exp * coef.toFun), _, rfl,
      h_tl, ?_⟩
    grw [mk_toFun, h_eq]

/-- If `f` can be approximated by multiseries with negative leading exponent, then
it tends to zero. -/
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.neg_leadingExp_ten
dsto_zero** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpans
ion.Approximates`。
形式化陈述：neg_leadingExp_tendsto_zero {basis_hd : Real -> Real} {basis_tl : Basis} {
ms : MultiseriesExpansion (basis_hd :: basis_tl)} (h_neg : ms.leadingExp < 0) (h
_approx : ms.Approximates) : Tendsto ms.toFun atTop (𝓝 0)
参数：basis_hd :: basis_tl；h_neg : ms.leadingExp < 0；h_approx : ms.Approximates。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.elim_nil`：el
im_nil (h : @Approximates (basis_hd :: basis_tl) (mk .nil f)) : f =ᶠ[atTop] 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.elim_cons`：e
lim_cons {exp : Real} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries b
asis_hd basis_tl} (h : Approximates (basis
· 使用定理 `Tactic.ComputeAsymptotics.Majorized.tendsto_zero_of_neg`：tendsto_zero_of
_neg (h_lt : exp < 0) (h : Majorized f b exp) : Tendsto f atTop (𝓝 0)

--- 原说明 ---
If `f` can be approximated by multiseries with negative leading exponent, then
it tends to zero.
-/
theorem neg_leadingExp_tendsto_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
    (h_neg : ms.leadingExp < 0) (h_approx : ms.Approximates) :
    Tendsto ms.toFun atTop (𝓝 0) := by
  cases ms
  · exact Tendsto.congr' h_approx.elim_nil.symm tendsto_const_nhds
  · obtain ⟨h_coef, h_maj, h_tl⟩ := h_approx.elim_cons
    simp only [leadingExp_def, mk_seq, Multiseries.leadingExp_cons, WithBot.coe_lt_zero] at h_neg
    exact Majorized.tendsto_zero_of_neg h_neg h_maj
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.nil_tendsto_zero**
 是 Mathlib 中的一个定理，位于命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approxi
mates`。
形式化陈述：nil_tendsto_zero {basis_hd : Real -> Real} {basis_tl : Basis} {f : Real ->
 Real} (h : MultiseriesExpansion.Approximates (basis
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tactic.ComputeAsymptotics.MultiseriesExpansion.Approximates.neg_leadingE
xp_tendsto_zero`：neg_leadingExp_tendsto_zero {basis_hd : Real -> Real} {basis_tl
 : Basis} {ms : MultiseriesExpansion (basis_hd :: basis_tl)} (h_neg : ms.lead…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem nil_tendsto_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    (h : MultiseriesExpansion.Approximates (basis := basis_hd :: basis_tl) (mk .nil f)) :
    Tendsto f atTop (𝓝 0) :=
  neg_leadingExp_tendsto_zero (by simp) h

end Approximates

/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.** 是 Mathlib 中的一个实例，位于命名空间 `Tac
tic.ComputeAsymptotics.MultiseriesExpansion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (basis_hd : ℝ → ℝ) (basis_tl : Basis) :
    Setoid (MultiseriesExpansion (basis_hd :: basis_tl)) where
  r x y := x.seq = y.seq ∧ x.toFun =ᶠ[atTop] y.toFun
  iseqv := ⟨by simp, by grind [EventuallyEq.symm], by grind [EventuallyEq.trans]⟩

@[simp]
/-
**Tactic.ComputeAsymptotics.MultiseriesExpansion.equiv_def** 是 Mathlib 中的一个定理，位于
命名空间 `Tactic.ComputeAsymptotics.MultiseriesExpansion`。
形式化陈述：equiv_def {x y : MultiseriesExpansion (basis_hd :: basis_tl)} : x ≈ y ↔ x.
seq = y.seq ∧ x.toFun =ᶠ[atTop] y.toFun
参数：basis_hd :: basis_tl。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem equiv_def {x y : MultiseriesExpansion (basis_hd :: basis_tl)} :
    x ≈ y ↔ x.seq = y.seq ∧ x.toFun =ᶠ[atTop] y.toFun := by
  rfl

end Approximates

end MultiseriesExpansion

end Tactic.ComputeAsymptotics

