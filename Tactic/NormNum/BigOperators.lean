/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Floris van Doorn
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic  -- shake: keep (Qq dependency)
public import Mathlib.Tactic.NormNum.Basic

/-!
# `norm_num` plugin for big operators

This file adds `norm_num` plugins for `Finset.prod` and `Finset.sum`.

The driving part of this plugin is `Mathlib.Meta.NormNum.evalFinsetBigop`.
We repeatedly use `Finset.proveEmptyOrCons` to try to find a proof that the given set is empty,
or that it consists of one element inserted into a strict subset, and evaluate the big operator
on that subset until the set is completely exhausted.

## See also

* The `fin_cases` tactic has similar scope: splitting out a finite collection into its elements.

## Porting notes

This plugin is noticeably less powerful than the equivalent version in Mathlib 3: the design of
`norm_num` means plugins have to return numerals, rather than a generic expression.
In particular, we can't use the plugin on sums containing variables.
(See also the TODO note "To support variables".)

## TODO

* Support intervals: `Finset.Ico`, `Finset.Icc`, ...
* To support variables, like in Mathlib 3, turn this into a standalone tactic that unfolds
  the sum/prod, without computing its numeric value (using the `ring` tactic to do some
  normalization?)
-/

public meta section

namespace Mathlib.Meta

open Lean
open Meta
open Qq

variable {u v : Level}

/-- This represents the result of trying to determine whether the given expression `n : Q(ℕ)`
is either `zero` or `succ`. -/
/-
**Mathlib.Meta.Nat.UnifyZeroOrSuccResult** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Me
ta.Nat`。
形式化陈述：Q(ℕ) → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This represents the result of trying to determine whether the given expression `
n : Q(ℕ)`
is either `zero` or `succ`.
-/
inductive Nat.UnifyZeroOrSuccResult (n : Q(ℕ))
  /-- `n` unifies with `0` -/
  | zero (pf : $n =Q 0)
  /-- `n` unifies with `succ n'` for this specific `n'` -/
  | succ (n' : Q(ℕ)) (pf : $n =Q Nat.succ $n')

/-- Determine whether the expression `n : Q(ℕ)` unifies with `0` or `Nat.succ n'`.

We do not use `norm_num` functionality because we want definitional equality,
not propositional equality, for use in dependent types.

Fails if neither of the options succeed.
-/
/-
**Mathlib.Meta.Nat.unifyZeroOrSucc** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Nat`。
形式化陈述：(n : Q(ℕ)) → MetaM (Mathlib.Meta.Nat.UnifyZeroOrSuccResult n)
参数：ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Determine whether the expression `n : Q(ℕ)` unifies with `0` or `Nat.succ n'`.

We do not use `norm_num` functionality because we want definitional equality,
not propositional equality, for use in dependent types.

Fails if neither of the options succeed.
-/
def Nat.unifyZeroOrSucc (n : Q(ℕ)) : MetaM (Nat.UnifyZeroOrSuccResult n) := do
  match ← isDefEqQ n q(0) with
  | .defEq pf => return .zero pf
  | .notDefEq => do
    let n' : Q(ℕ) ← mkFreshExprMVar q(ℕ)
    let ⟨(_pf : $n =Q Nat.succ $n')⟩ ← assertDefEqQ n q(Nat.succ $n')
    let (.some (n'_val : Q(ℕ))) ← getExprMVarAssignment? n'.mvarId! |
      throwError "could not figure out value of `?n` from `{n} =?= Nat.succ ?n`"
    pure (.succ n'_val ⟨⟩)

/-- This represents the result of trying to determine whether the given expression
`s : Q(List $α)` is either empty or consists of an element inserted into a strict subset. -/
/-
**Mathlib.Meta.List.ProveNilOrConsResult** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Me
ta.List`。
形式化陈述：{u : Level} → {α : Q(Type u)} → Q(List «$α») → Type
参数：Type u；List «$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This represents the result of trying to determine whether the given expression
`s : Q(List $α)` is either empty or consists of an element inserted into a stric
t subset.
-/
inductive List.ProveNilOrConsResult {α : Q(Type u)} (s : Q(List $α))
  /-- The set is Nil. -/
  | nil (pf : Q($s = []))
  /-- The set equals `a` inserted into the strict subset `s'`. -/
  | cons (a : Q($α)) (s' : Q(List $α)) (pf : Q($s = List.cons $a $s'))

/-- If `s` unifies with `t`, convert a result for `s` to a result for `t`.

If `s` does not unify with `t`, this results in a type-incorrect proof.
-/
/-
**Mathlib.Meta.List.ProveNilOrConsResult.uncheckedCast** 是 Mathlib 中的一个定义，位于命名空间
 `Mathlib.Meta.List.ProveNilOrConsResult`。
形式化陈述：{u v : Level} →   {α : Q(Type u)} →     {β : Q(Type v)} →       (s : Q(Lis
t «$α»)) →         (t : Q(List «$β»)) → Mathlib.Meta.List.ProveNilOrConsResult s
 → Mathlib.Meta.List.ProveNilOrConsResult t
参数：Type u；Type v；s : Q(List «$α»)；t : Q(List «$β»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` unifies with `t`, convert a result for `s` to a result for `t`.

If `s` does not unify with `t`, this results in a type-incorrect proof.
-/
def List.ProveNilOrConsResult.uncheckedCast {α : Q(Type u)} {β : Q(Type v)}
    (s : Q(List $α)) (t : Q(List $β)) :
    List.ProveNilOrConsResult s → List.ProveNilOrConsResult t
  | .nil pf => .nil pf
  | .cons a s' pf => .cons a s' pf

/-- If `s = t` and we can get the result for `t`, then we can get the result for `s`.
-/
/-
**Mathlib.Meta.List.ProveNilOrConsResult.eq_trans** 是 Mathlib 中的一个定义，位于命名空间 `Mat
hlib.Meta.List.ProveNilOrConsResult`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {s t : Q(List «$α»)} →       Q(«$s» 
= «$t») → Mathlib.Meta.List.ProveNilOrConsResult t → Mathlib.Meta.List.ProveNilO
rConsResult s
参数：Type u；List «$α»；«$s» = «$t»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s = t` and we can get the result for `t`, then we can get the result for `s`
.
-/
def List.ProveNilOrConsResult.eq_trans {α : Q(Type u)} {s t : Q(List $α)}
    (eq : Q($s = $t)) :
    List.ProveNilOrConsResult t → List.ProveNilOrConsResult s
  | .nil pf => .nil q(Eq.trans $eq $pf)
  | .cons a s' pf => .cons a s' q(Eq.trans $eq $pf)
/-
**Mathlib.Meta.List.range_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.List`。
形式化陈述：∀ {n : ℕ}, Mathlib.Meta.NormNum.IsNat n 0 → List.range n = []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `List.range_zero`：List.range 0 = []
-/
lemma List.range_zero' {n : ℕ} (pn : NormNum.IsNat n 0) :
    List.range n = [] := by rw [pn.out, Nat.cast_zero, List.range_zero]
/-
**Mathlib.Meta.List.range_succ_eq_map'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.L
ist`。
形式化陈述：∀ {n nn n' : ℕ}, Mathlib.Meta.NormNum.IsNat n nn → nn = n'.succ → List.ran
ge n = 0 :: List.map Nat.succ (List.range n')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
· 使用定理 `List.range_succ_eq_map`：∀ {n : ℕ}, List.range (n + 1) = 0 :: List.map Na
t.succ (List.range n)
-/
lemma List.range_succ_eq_map' {n nn n' : ℕ} (pn : NormNum.IsNat n nn) (pn' : nn = Nat.succ n') :
    List.range n = 0 :: List.map Nat.succ (List.range n') := by
  rw [pn.out, Nat.cast_id, pn', List.range_succ_eq_map]

set_option linter.unusedVariables false in
/-- Either show the expression `s : Q(List α)` is Nil, or remove one element from it.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
/-
**Mathlib.Meta.List.proveNilOrCons** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Meta.Li
st`。
形式化陈述：{u : Level} → {α : Q(Type u)} → (s : Q(List «$α»)) → MetaM (Mathlib.Meta.L
ist.ProveNilOrConsResult s)
参数：Type u；s : Q(List «$α»)；Mathlib.Meta.List.ProveNilOrConsResult s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Either show the expression `s : Q(List α)` is Nil, or remove one element from it
.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
partial def List.proveNilOrCons {u : Level} {α : Q(Type u)} (s : Q(List $α)) :
    MetaM (List.ProveNilOrConsResult s) :=
  s.withApp fun e a =>
  match (e, e.constName, a) with
  | (_, ``EmptyCollection.emptyCollection, _) => haveI : $s =Q {} := ⟨⟩; pure (.nil q(.refl []))
  | (_, ``List.nil, _) => haveI : $s =Q [] := ⟨⟩; pure (.nil q(rfl))
  | (_, ``List.cons, #[_, (a : Q($α)), (s' : Q(List $α))]) =>
    haveI : $s =Q $a :: $s' := ⟨⟩; pure (.cons a s' q(rfl))
  | (_, ``List.range, #[(n : Q(ℕ))]) =>
    have s : Q(List ℕ) := s; .uncheckedCast _ _ <$> show MetaM (ProveNilOrConsResult s) from do
    let ⟨nn, pn⟩ ← NormNum.deriveNat n _
    haveI' : $s =Q .range $n := ⟨⟩
    let nnL := nn.natLit!
    if nnL = 0 then
      haveI' : $nn =Q 0 := ⟨⟩
      return .nil q(List.range_zero' $pn)
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      have : $nn =Q .succ $n' := ⟨⟩
      return .cons _ _ q(List.range_succ_eq_map' $pn (.refl $nn))
  | (_, ``List.finRange, #[(n : Q(ℕ))]) =>
    have s : Q(List (Fin $n)) := s
    .uncheckedCast _ _ <$> show MetaM (ProveNilOrConsResult s) from do
    haveI' : $s =Q .finRange $n := ⟨⟩
    return match ← Nat.unifyZeroOrSucc n with -- We want definitional equality on `n`.
    | .zero _pf => .nil q(List.finRange_zero)
    | .succ n' _pf => .cons _ _ q(List.finRange_succ)
  | (.const ``List.map [v, _], _, #[(β : Q(Type v)), _, (f : Q($β → $α)), (xxs : Q(List $β))]) => do
    haveI' : $s =Q ($xxs).map $f := ⟨⟩
    return match ← List.proveNilOrCons xxs with
    | .nil pf => .nil q(($pf ▸ List.map_nil : List.map _ _ = _))
    | .cons x xs pf => .cons q($f $x) q(($xs).map $f)
      q(($pf ▸ List.map_cons : List.map _ _ = _))
  | (_, fn, args) =>
    throwError "List.proveNilOrCons: unsupported List expression {s} ({fn}, {args})"

/-- This represents the result of trying to determine whether the given expression
`s : Q(Multiset $α)` is either empty or consists of an element inserted into a strict subset. -/
/-
**Mathlib.Meta.Multiset.ProveZeroOrConsResult** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathl
ib.Meta.Multiset`。
形式化陈述：{u : Level} → {α : Q(Type u)} → Q(Multiset «$α») → Type
参数：Type u；Multiset «$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This represents the result of trying to determine whether the given expression
`s : Q(Multiset $α)` is either empty or consists of an element inserted into a s
trict subset.
-/
inductive Multiset.ProveZeroOrConsResult {α : Q(Type u)} (s : Q(Multiset $α))
  /-- The set is zero. -/
  | zero (pf : Q($s = 0))
  /-- The set equals `a` inserted into the strict subset `s'`. -/
  | cons (a : Q($α)) (s' : Q(Multiset $α)) (pf : Q($s = Multiset.cons $a $s'))

/-- If `s` unifies with `t`, convert a result for `s` to a result for `t`.

If `s` does not unify with `t`, this results in a type-incorrect proof.
-/
/-
**Mathlib.Meta.Multiset.ProveZeroOrConsResult.uncheckedCast** 是 Mathlib 中的一个定义，位
于命名空间 `Mathlib.Meta.Multiset.ProveZeroOrConsResult`。
形式化陈述：{u v : Level} →   {α : Q(Type u)} →     {β : Q(Type v)} →       (s : Q(Mul
tiset «$α»)) →         (t : Q(Multiset «$β»)) →           Mathlib.Meta.Multiset.
ProveZeroOrConsResult s → Mathlib.Meta.Multiset.ProveZeroOrConsResult t
参数：Type u；Type v；s : Q(Multiset «$α»)；t : Q(Multiset «$β»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` unifies with `t`, convert a result for `s` to a result for `t`.

If `s` does not unify with `t`, this results in a type-incorrect proof.
-/
def Multiset.ProveZeroOrConsResult.uncheckedCast {α : Q(Type u)} {β : Q(Type v)}
    (s : Q(Multiset $α)) (t : Q(Multiset $β)) :
    Multiset.ProveZeroOrConsResult s → Multiset.ProveZeroOrConsResult t
  | .zero pf => .zero pf
  | .cons a s' pf => .cons a s' pf

/-- If `s = t` and we can get the result for `t`, then we can get the result for `s`.
-/
/-
**Mathlib.Meta.Multiset.ProveZeroOrConsResult.eq_trans** 是 Mathlib 中的一个定义，位于命名空间
 `Mathlib.Meta.Multiset.ProveZeroOrConsResult`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {s t : Q(Multiset «$α»)} →       Q(«
$s» = «$t») → Mathlib.Meta.Multiset.ProveZeroOrConsResult t → Mathlib.Meta.Multi
set.ProveZeroOrConsResult s
参数：Type u；Multiset «$α»；«$s» = «$t»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s = t` and we can get the result for `t`, then we can get the result for `s`
.
-/
def Multiset.ProveZeroOrConsResult.eq_trans {α : Q(Type u)} {s t : Q(Multiset $α)}
    (eq : Q($s = $t)) :
    Multiset.ProveZeroOrConsResult t → Multiset.ProveZeroOrConsResult s
  | .zero pf => .zero q(Eq.trans $eq $pf)
  | .cons a s' pf => .cons a s' q(Eq.trans $eq $pf)
/-
**Mathlib.Meta.Multiset.insert_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.M
ultiset`。
形式化陈述：∀ {α : Type u_1} (a : α) (s : Multiset α), insert a s = a ::ₘ s
参数：a : α；s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Multiset.insert_eq_cons {α : Type*} (a : α) (s : Multiset α) :
    insert a s = Multiset.cons a s :=
  rfl
/-
**Mathlib.Meta.Multiset.range_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Mult
iset`。
形式化陈述：∀ {n : ℕ}, Mathlib.Meta.NormNum.IsNat n 0 → Multiset.range n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Multiset.range_zero`：range_zero : range 0 = 0
-/
lemma Multiset.range_zero' {n : ℕ} (pn : NormNum.IsNat n 0) :
    Multiset.range n = 0 := by rw [pn.out, Nat.cast_zero, Multiset.range_zero]
/-
**Mathlib.Meta.Multiset.range_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Mult
iset`。
形式化陈述：∀ {n nn n' : ℕ}, Mathlib.Meta.NormNum.IsNat n nn → nn = n'.succ → Multiset
.range n = n' ::ₘ Multiset.range n'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
· 使用定理 `Multiset.range_succ`：range_succ (n : Nat) : range (succ n) = n ::ₘ range
 n
-/
lemma Multiset.range_succ' {n nn n' : ℕ} (pn : NormNum.IsNat n nn) (pn' : nn = Nat.succ n') :
    Multiset.range n = n' ::ₘ Multiset.range n' := by
  rw [pn.out, Nat.cast_id, pn', Multiset.range_succ]

/-- Either show the expression `s : Q(Multiset α)` is Zero, or remove one element from it.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
/-
**Mathlib.Meta.Multiset.proveZeroOrCons** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.
Multiset`。
形式化陈述：{u : Level} → {α : Q(Type u)} → (s : Q(Multiset «$α»)) → MetaM (Mathlib.Me
ta.Multiset.ProveZeroOrConsResult s)
参数：Type u；s : Q(Multiset «$α»)；Mathlib.Meta.Multiset.ProveZeroOrConsResult s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Either show the expression `s : Q(Multiset α)` is Zero, or remove one element fr
om it.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
partial def Multiset.proveZeroOrCons {α : Q(Type u)} (s : Q(Multiset $α)) :
    MetaM (Multiset.ProveZeroOrConsResult s) :=
  match s.getAppFnArgs with
  | (``EmptyCollection.emptyCollection, _) => haveI : $s =Q {} := ⟨⟩; pure (.zero q(rfl))
  | (``Zero.zero, _) => haveI : $s =Q 0 := ⟨⟩; pure (.zero q(rfl))
  | (``Multiset.cons, #[_, (a : Q($α)), (s' : Q(Multiset $α))]) =>
    haveI : $s =Q .cons $a $s' := ⟨⟩
    pure (.cons a s' q(rfl))
  | (``Multiset.ofList, #[_, (val : Q(List $α))]) => do
    haveI : $s =Q .ofList $val := ⟨⟩
    return match ← List.proveNilOrCons val with
    | .nil pf => .zero q($pf ▸ Multiset.coe_nil : Multiset.ofList _ = _)
    | .cons a s' pf => .cons a q($s') q($pf ▸ Multiset.cons_coe $a $s' : Multiset.ofList _ = _)
  | (``Multiset.range, #[(n : Q(ℕ))]) => do
    have s : Q(Multiset ℕ) := s; .uncheckedCast _ _ <$> show MetaM (ProveZeroOrConsResult s) from do
    let ⟨nn, pn⟩ ← NormNum.deriveNat n _
    haveI' : $s =Q .range $n := ⟨⟩
    let nnL := nn.natLit!
    if nnL = 0 then
      haveI' : $nn =Q 0 := ⟨⟩
      return .zero q(Multiset.range_zero' $pn)
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      haveI' : $nn =Q ($n').succ := ⟨⟩
      return .cons _ _ q(Multiset.range_succ' $pn rfl)
  | (fn, args) =>
    throwError "Multiset.proveZeroOrCons: unsupported multiset expression {s} ({fn}, {args})"

/-- This represents the result of trying to determine whether the given expression
`s : Q(Finset $α)` is either empty or consists of an element inserted into a strict subset. -/
/-
**Mathlib.Meta.Finset.ProveEmptyOrConsResult** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathli
b.Meta.Finset`。
形式化陈述：{u : Level} → {α : Q(Type u)} → Q(Finset «$α») → Type
参数：Type u；Finset «$α»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This represents the result of trying to determine whether the given expression
`s : Q(Finset $α)` is either empty or consists of an element inserted into a str
ict subset.
-/
inductive Finset.ProveEmptyOrConsResult {α : Q(Type u)} (s : Q(Finset $α))
  /-- The set is empty. -/
  | empty (pf : Q($s = ∅))
  /-- The set equals `a` inserted into the strict subset `s'`. -/
  | cons (a : Q($α)) (s' : Q(Finset $α)) (h : Q($a ∉ $s')) (pf : Q($s = Finset.cons $a $s' $h))

/-- If `s` unifies with `t`, convert a result for `s` to a result for `t`.

If `s` does not unify with `t`, this results in a type-incorrect proof.
-/
/-
**Mathlib.Meta.Finset.ProveEmptyOrConsResult.uncheckedCast** 是 Mathlib 中的一个定义，位于
命名空间 `Mathlib.Meta.Finset.ProveEmptyOrConsResult`。
形式化陈述：{u v : Level} →   {α : Q(Type u)} →     {β : Q(Type v)} →       (s : Q(Fin
set «$α»)) →         (t : Q(Finset «$β»)) →           Mathlib.Meta.Finset.ProveE
mptyOrConsResult s → Mathlib.Meta.Finset.ProveEmptyOrConsResult t
参数：Type u；Type v；s : Q(Finset «$α»)；t : Q(Finset «$β»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` unifies with `t`, convert a result for `s` to a result for `t`.

If `s` does not unify with `t`, this results in a type-incorrect proof.
-/
def Finset.ProveEmptyOrConsResult.uncheckedCast {α : Q(Type u)} {β : Q(Type v)}
    (s : Q(Finset $α)) (t : Q(Finset $β)) :
    Finset.ProveEmptyOrConsResult s → Finset.ProveEmptyOrConsResult t
  | .empty pf => .empty pf
  | .cons a s' h pf => .cons a s' h pf

/-- If `s = t` and we can get the result for `t`, then we can get the result for `s`.
-/
/-
**Mathlib.Meta.Finset.ProveEmptyOrConsResult.eq_trans** 是 Mathlib 中的一个定义，位于命名空间 
`Mathlib.Meta.Finset.ProveEmptyOrConsResult`。
形式化陈述：{u : Level} →   {α : Q(Type u)} →     {s t : Q(Finset «$α»)} →       Q(«$s
» = «$t») → Mathlib.Meta.Finset.ProveEmptyOrConsResult t → Mathlib.Meta.Finset.P
roveEmptyOrConsResult s
参数：Type u；Finset «$α»；«$s» = «$t»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s = t` and we can get the result for `t`, then we can get the result for `s`
.
-/
def Finset.ProveEmptyOrConsResult.eq_trans {α : Q(Type u)} {s t : Q(Finset $α)}
    (eq : Q($s = $t)) :
    Finset.ProveEmptyOrConsResult t → Finset.ProveEmptyOrConsResult s
  | .empty pf => .empty q(Eq.trans $eq $pf)
  | .cons a s' h pf => .cons a s' h q(Eq.trans $eq $pf)
/-
**Mathlib.Meta.Finset.insert_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Fin
set`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s : Finset α) (h : a ∉ s)
, insert a s = Finset.cons a s h
参数：a : α；s : Finset α；h : a ∉ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Finset.insert_eq_cons {α : Type*} [DecidableEq α] (a : α) (s : Finset α) (h : a ∉ s) :
    insert a s = Finset.cons a s h := by
  simp
/-
**Mathlib.Meta.Finset.range_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Finset
`。
形式化陈述：∀ {n : ℕ}, Mathlib.Meta.NormNum.IsNat n 0 → Finset.range n = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Finset.range_zero`：range_zero : range 0 = ∅
-/
lemma Finset.range_zero' {n : ℕ} (pn : NormNum.IsNat n 0) :
    Finset.range n = {} := by rw [pn.out, Nat.cast_zero, Finset.range_zero]
/-
**Mathlib.Meta.Finset.range_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Finset
`。
形式化陈述：∀ {n nn n' : ℕ}, Mathlib.Meta.NormNum.IsNat n nn → nn = n'.succ → Finset.r
ange n = Finset.cons n' (Finset.range n') ⋯
参数：Finset.range n'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_range_self`：notMem_range_self : n ∉ range n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用定理 `Mathlib.Meta.Finset.insert_eq_cons`：∀ {α : Type u_1} [inst : DecidableEq
 α] (a : α) (s : Finset α) (h : a ∉ s), insert a s = Finset.cons a s h
-/
lemma Finset.range_succ' {n nn n' : ℕ} (pn : NormNum.IsNat n nn) (pn' : nn = Nat.succ n') :
    Finset.range n = Finset.cons n' (Finset.range n') Finset.notMem_range_self := by
  rw [pn.out, Nat.cast_id, pn', Finset.range_add_one, Finset.insert_eq_cons]
/-
**Mathlib.Meta.Finset.univ_eq_elems** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Fins
et`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] (elems : Finset α), (∀ (x : α), x ∈ el
ems) → Finset.univ = elems
参数：elems : Finset α；∀ (x : α), x ∈ elems。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
lemma Finset.univ_eq_elems {α : Type*} [Fintype α] (elems : Finset α)
    (complete : ∀ x : α, x ∈ elems) :
    Finset.univ = elems := by
  ext x; simpa using complete x

/-- Either show the expression `s : Q(Finset α)` is empty, or remove one element from it.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
/-
**Mathlib.Meta.Finset.proveEmptyOrCons** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Met
a.Finset`。
形式化陈述：{u : Level} → {α : Q(Type u)} → (s : Q(Finset «$α»)) → MetaM (Mathlib.Meta
.Finset.ProveEmptyOrConsResult s)
参数：Type u；s : Q(Finset «$α»)；Mathlib.Meta.Finset.ProveEmptyOrConsResult s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Either show the expression `s : Q(Finset α)` is empty, or remove one element fro
m it.

Fails if we cannot determine which of the alternatives apply to the expression.
-/
partial def Finset.proveEmptyOrCons {α : Q(Type u)} (s : Q(Finset $α)) :
    MetaM (ProveEmptyOrConsResult s) :=
  match s.getAppFnArgs with
  | (``EmptyCollection.emptyCollection, _) => haveI : $s =Q {} := ⟨⟩; pure (.empty q(rfl))
  | (``Finset.cons, #[_, (a : Q($α)), (s' : Q(Finset $α)), (h : Q($a ∉ $s'))]) =>
    haveI : $s =Q .cons $a $s' $h := ⟨⟩
    pure (.cons a s' h q(.refl $s))
  | (``Finset.mk, #[_, (val : Q(Multiset $α)), (nd : Q(Multiset.Nodup $val))]) => do
    match ← Multiset.proveZeroOrCons val with
    | .zero pf => pure <| .empty (q($pf ▸ Finset.mk_zero) : Q(Finset.mk $val $nd = ∅))
    | .cons a s' pf => do
      let h : Q(Multiset.Nodup ($a ::ₘ $s')) := q($pf ▸ $nd)
      let nd' : Q(Multiset.Nodup $s') := q((Multiset.nodup_cons.mp $h).2)
      let h' : Q($a ∉ $s') := q((Multiset.nodup_cons.mp $h).1)
      return (.cons a q(Finset.mk $s' $nd') h'
        (q($pf ▸ Finset.mk_cons $h) : Q(Finset.mk $val $nd = Finset.cons $a ⟨$s', $nd'⟩ $h')))
  | (``Finset.range, #[(n : Q(ℕ))]) =>
    have s : Q(Finset ℕ) := s; .uncheckedCast _ _ <$> show MetaM (ProveEmptyOrConsResult s) from do
    let ⟨nn, pn⟩ ← NormNum.deriveNat n _
    haveI' : $s =Q .range $n := ⟨⟩
    let nnL := nn.natLit!
    if nnL = 0 then
      haveI : $nn =Q 0 := ⟨⟩
      return .empty q(Finset.range_zero' $pn)
    else
      have n' : Q(ℕ) := mkRawNatLit (nnL - 1)
      haveI' : $nn =Q ($n').succ := ⟨⟩
      return .cons n' _ _ q(Finset.range_succ' $pn (.refl $nn))
  | (``Finset.univ, #[_, (instFT : Q(Fintype $α))]) => do
    haveI' : $s =Q .univ := ⟨⟩
    match (← whnfI instFT).getAppFnArgs with
    | (``Fintype.mk, #[_, (elems : Q(Finset $α)), (complete : Q(∀ x : $α, x ∈ $elems))]) => do
      let res ← Finset.proveEmptyOrCons elems
      pure <| res.eq_trans q(Finset.univ_eq_elems $elems $complete)
    | e =>
      throwError "Finset.proveEmptyOrCons: could not determine elements of Fintype instance {e}"
  | (fn, args) =>
    throwError "Finset.proveEmptyOrCons: unsupported finset expression {s} ({fn}, {args})"

namespace NormNum

/-- If `a = b` and we can evaluate `b`, then we can evaluate `a`. -/
/-
**Mathlib.Meta.NormNum.Result.eq_trans** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.N
ormNum.Result`。
形式化陈述：{u : Level} →   {α : Q(Type u)} → {a b : Q(«$α»)} → Q(«$a» = «$b») → Mathl
ib.Meta.NormNum.Result b → Mathlib.Meta.NormNum.Result a
参数：Type u；«$α»；«$a» = «$b»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a = b` and we can evaluate `b`, then we can evaluate `a`.
-/
def Result.eq_trans {α : Q(Type u)} {a b : Q($α)} (eq : Q($a = $b)) : Result b → Result a
  | .isBool true proof =>
    have a : Q(Prop) := a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q($b) := proof
    Result.isTrue (x := a) q($eq ▸ $proof)
  | .isBool false proof =>
    have a : Q(Prop) := a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q(¬ $b) := proof
  Result.isFalse (x := a) q($eq ▸ $proof)
  | .isNat inst lit proof => Result.isNat inst lit q($eq ▸ $proof)
  | .isNegNat inst lit proof => Result.isNegNat inst lit q($eq ▸ $proof)
  | .isNNRat inst q n d proof => Result.isNNRat inst q n d q($eq ▸ $proof)
  | .isNegNNRat inst q n d proof => Result.isNegNNRat inst q n d q($eq ▸ $proof)
/-
**Mathlib.Meta.NormNum.Finset.sum_empty** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum.Finset`。
形式化陈述：∀ {β : Type u_1} {α : Type u_2} [inst : CommSemiring β] (f : α → β), Mathl
ib.Meta.NormNum.IsNat (∅.sum f) 0
参数：f : α → β；∅.sum f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma Finset.sum_empty {β α : Type*} [CommSemiring β] (f : α → β) :
    IsNat (Finset.sum ∅ f) 0 :=
  ⟨by simp⟩
/-
**Mathlib.Meta.NormNum.Finset.prod_empty** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta
.NormNum.Finset`。
形式化陈述：∀ {β : Type u_1} {α : Type u_2} [inst : CommSemiring β] (f : α → β), Mathl
ib.Meta.NormNum.IsNat (∅.prod f) 1
参数：f : α → β；∅.prod f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma Finset.prod_empty {β α : Type*} [CommSemiring β] (f : α → β) :
    IsNat (Finset.prod ∅ f) 1 :=
  ⟨by simp⟩

/-- Evaluate a big operator applied to a finset by repeating `proveEmptyOrCons` until
we exhaust all elements of the set. -/
/-
**Mathlib.Meta.NormNum.evalFinsetBigop** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Met
a.NormNum`。
形式化陈述：{u v : Level} →   {α : Q(Type u)} →     {β : Q(Type v)} →       (op : Q(Fi
nset «$α» → («$α» → «$β») → «$β»)) →         (f : Q(«$α» → «$β»)) →           Ma
thlib.Meta.NormNum.Result q(«$op» Finset.empty «$f») →             ({a : Q(«$α»)
} →                 {s' : Q(Finset «$α»)} →                   {h : Q(«$a» ∉ «$s'
»)} →                     Mathlib.Meta.NormNum.Result q(«$f» «$a») →            
           Mathlib.Meta.NormNum.Result q(«$op» «$s'» «$f») →                    
     MetaM (Mathlib.Meta.NormNum.Result q(«$op» (Finset.cons «$a» «$s'» «$h») «$
f»))) →               (s : Q(Finset «$α»)) → MetaM (Mathlib.Meta.NormNum.Result 
q(«$op» «$s» «$f»))
参数：Type u；Type v；op : Q(Finset «$α» → («$α» → «$β») → «$β»)；f : Q(«$α» → «$β»)；«
$op» Finset.empty «$f»；{a : Q(«$α»)} →                 {s' : Q(Finset «$α»)} →  
                 {h : Q(«$a» ∉ «$s'»)} →                     Mathlib.Meta.NormNu
m.Result q(«$f» «$a») →                       Mathlib.Meta.NormNum.Result q(«$op
» «$s'» «$f») →                         MetaM (Mathlib.Meta.NormNum.Result q(«$o
p» (Finset.cons «$a» «$s'» «$h») «$f»))；s : Q(Finset «$α»)；Mathlib.Meta.NormNum.
Result q(«$op» «$s» «$f»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluate a big operator applied to a finset by repeating `proveEmptyOrCons` unti
l
we exhaust all elements of the set.
-/
partial def evalFinsetBigop {α : Q(Type u)} {β : Q(Type v)}
    (op : Q(Finset $α → ($α → $β) → $β))
    (f : Q($α → $β))
    (res_empty : Result q($op Finset.empty $f))
    (res_cons : {a : Q($α)} -> {s' : Q(Finset $α)} -> {h : Q($a ∉ $s')} ->
      Result (α := β) q($f $a) -> Result (α := β) q($op $s' $f) ->
      MetaM (Result (α := β) q($op (Finset.cons $a $s' $h) $f))) :
    (s : Q(Finset $α)) → MetaM (Result (α := β) q($op $s $f))
  | s => do
    match ← Finset.proveEmptyOrCons s with
    | .empty pf => pure <| res_empty.eq_trans q(congr_fun (congr_arg _ $pf) _)
    | .cons a s' h pf => do
      let fa : Q($β) := Expr.betaRev f #[a]
      let res_fa ← derive fa
      let res_op_s' : Result q($op $s' $f) ← evalFinsetBigop op f res_empty @res_cons s'
      let res ← res_cons res_fa res_op_s'
      let eq : Q($op $s $f = $op (Finset.cons $a $s' $h) $f) := q(congr_fun (congr_arg _ $pf) _)
      pure (res.eq_trans eq)

attribute [local instance] monadLiftOptionMetaM in
/-- `norm_num` plugin for evaluating products of finsets.

If your finset is not supported, you can add it to the match in `Finset.proveEmptyOrCons`.
-/
@[norm_num @Finset.prod _ _ _ _ _]
/-
**Mathlib.Meta.NormNum.evalFinsetProd** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` plugin for evaluating products of finsets.

If your finset is not supported, you can add it to the match in `Finset.proveEmp
tyOrCons`.
-/
partial def evalFinsetProd : NormNumExt where eval {u β} e := do
  let .app (.app (.app (.app (.app (.const ``Finset.prod [v, _]) α) β') _) s) f ←
    whnfR e | failure
  guard <| ← withNewMCtxDepth <| isDefEq β β'
  have α : Q(Type v) := α
  have s : Q(Finset $α) := s
  have f : Q($α → $β) := f
  let instCS : Q(CommSemiring $β) ← synthInstanceQ q(CommSemiring $β) <|>
    throwError "not a commutative semiring: {β}"
  let instS : Q(Semiring $β) := q(CommSemiring.toSemiring)
  -- Have to construct this expression manually, `q(1)` doesn't parse correctly:
  let n : Q(ℕ) := .lit (.natVal 1)
  let pf : Q(IsNat (Finset.prod ∅ $f) $n) := q(@Finset.prod_empty $β $α $instCS $f)
  let res_empty := Result.isNat _ n pf

  evalFinsetBigop q(Finset.prod) f res_empty (fun {a s' h} res_fa res_prod_s' ↦ do
      let fa : Q($β) := Expr.app f a
      let res ← res_fa.mul res_prod_s'
      let eq : Q(Finset.prod (Finset.cons $a $s' $h) $f = $fa * Finset.prod $s' $f) :=
        q(Finset.prod_cons $h)
      pure <| res.eq_trans eq)
    s

attribute [local instance] monadLiftOptionMetaM in
/-- `norm_num` plugin for evaluating sums of finsets.

If your finset is not supported, you can add it to the match in `Finset.proveEmptyOrCons`.
-/
@[norm_num @Finset.sum _ _ _ _ _]
/-
**Mathlib.Meta.NormNum.evalFinsetSum** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`norm_num` plugin for evaluating sums of finsets.

If your finset is not supported, you can add it to the match in `Finset.proveEmp
tyOrCons`.
-/
partial def evalFinsetSum : NormNumExt where eval {u β} e := do
  let .app (.app (.app (.app (.app (.const ``Finset.sum [v, _]) α) β') _) s) f ←
    whnfR e | failure
  guard <| ← withNewMCtxDepth <| isDefEq β β'
  have α : Q(Type v) := α
  have s : Q(Finset $α) := s
  have f : Q($α → $β) := f
  let instCS : Q(CommSemiring $β) ← synthInstanceQ q(CommSemiring $β) <|>
    throwError "not a commutative semiring: {β}"
  let pf : Q(IsNat (Finset.sum ∅ $f) (nat_lit 0)) := q(@Finset.sum_empty $β $α $instCS $f)
  let res_empty := Result.isNat _ _ q($pf)

  evalFinsetBigop q(Finset.sum) f res_empty (fun {a s' h} res_fa res_sum_s' ↦ do
      let fa : Q($β) := Expr.app f a
      let res ← res_fa.add res_sum_s'
      let eq : Q(Finset.sum (Finset.cons $a $s' $h) $f = $fa + Finset.sum $s' $f) :=
        q(Finset.sum_cons $h)
      pure <| res.eq_trans eq)
    s

end NormNum

end Meta

end Mathlib

