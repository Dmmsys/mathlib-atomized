/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Brendan Murphy
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Function.OfArity

/-!
# Currying and uncurrying of n-ary functions

A function of `n` arguments can either be written as `f a₁ a₂ ⋯ aₙ` or `f' ![a₁, a₂, ⋯, aₙ]`.
This file provides the currying and uncurrying operations that convert between the two, as
n-ary generalizations of the binary `curry` and `uncurry`.

## Main definitions

* `Function.OfArity.uncurry`: convert an `n`-ary function to a function from `Fin n → α`.
* `Function.OfArity.curry`: convert a function from `Fin n → α` to an `n`-ary function.
* `Function.FromTypes.uncurry`: convert an `p`-ary heterogeneous function to a
  function from `(i : Fin n) → p i`.
* `Function.FromTypes.curry`: convert a function from `(i : Fin n) → p i` to a
  `p`-ary heterogeneous function.

-/

@[expose] public section

universe u v w w'

namespace Function.FromTypes

open Matrix (vecCons vecHead vecTail vecEmpty)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: : {n : Nat} -> {p : Fin n -> Type u} -> {τ : Type u} ->

中文:
定义 uncurry
  签名: : {n : 自然数} -> {p : Fin n -> 类型u} -> {τ : 类型u} ->
-/
def uncurry : {n : Nat} -> {p : Fin n -> Type u} -> {τ : Type u} ->
    (f : Function.FromTypes p τ) -> ((i : Fin n) -> p i) -> τ
  | 0 , _, _, f => fun _ => f
  | _ + 1, _, _, f => fun args => (f (args 0)).uncurry (args ∘' Fin.succ)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: : {n : Nat} -> {p : Fin n -> Type u} -> {τ : Type u} ->

中文:
定义 curry
  签名: : {n : 自然数} -> {p : Fin n -> 类型u} -> {τ : 类型u} ->
-/
def curry : {n : Nat} -> {p : Fin n -> Type u} -> {τ : Type u} ->
    (((i : Fin n) -> p i) -> τ) -> Function.FromTypes p τ
  | 0 , _, _, f => f isEmptyElim
  | _ + 1, _, _, f => fun a => curry (fun args => f (Fin.cons a args))

@[simp]
/--
theorem `uncurry_apply_cons` / 定理 `uncurry_apply_cons`

English:
theorem uncurry_apply_cons
  statement: {n : Nat} {α} {p : Fin n -> Type u} {τ : Type u}
  proof: rfl

@[simp low]

中文:
定理 uncurry_apply_cons
  结论: {n : 自然数} {α} {p : Fin n -> 类型u} {τ : 类型u}
  证明: rfl

@[simp low]
-/
theorem uncurry_apply_cons {n : Nat} {α} {p : Fin n -> Type u} {τ : Type u}
    (f : Function.FromTypes (vecCons α p) τ) (a : α) (args : (i : Fin n) -> p i) :
    uncurry f (Fin.cons a args) = @uncurry _ p _ (f a) args := rfl

@[simp low]
/--
theorem `uncurry_apply_succ` / 定理 `uncurry_apply_succ`

English:
theorem uncurry_apply_succ
  statement: {n : Nat} {p : Fin (n + 1) -> Type u} {τ : Type u}
  proof: rfl

@[simp]

中文:
定理 uncurry_apply_succ
  结论: {n : 自然数} {p : Fin (n + 1) -> 类型u} {τ : 类型u}
  证明: rfl

@[simp]
-/
theorem uncurry_apply_succ {n : Nat} {p : Fin (n + 1) -> Type u} {τ : Type u}
    (f : Function.FromTypes p τ) (args : (i : Fin (n + 1)) -> p i) :
    uncurry f args = uncurry (f (args 0)) (Fin.tail args) := rfl

@[simp]
/--
theorem `curry_apply_cons` / 定理 `curry_apply_cons`

English:
theorem curry_apply_cons
  statement: {n : Nat} {α} {p : Fin n -> Type u} {τ : Type u}
  proof: rfl

@[simp low]

中文:
定理 curry_apply_cons
  结论: {n : 自然数} {α} {p : Fin n -> 类型u} {τ : 类型u}
  证明: rfl

@[simp low]
-/
theorem curry_apply_cons {n : Nat} {α} {p : Fin n -> Type u} {τ : Type u}
    (f : ((i : Fin (n + 1)) -> (vecCons α p) i) -> τ) (a : α) :
    curry f a = @curry _ p _ (f ∘' Fin.cons a :) := rfl

@[simp low]
/--
theorem `curry_apply_succ` / 定理 `curry_apply_succ`

English:
theorem curry_apply_succ
  statement: {n : Nat} {p : Fin (n + 1) -> Type u} {τ : Type u}
  proof: rfl

中文:
定理 curry_apply_succ
  结论: {n : 自然数} {p : Fin (n + 1) -> 类型u} {τ : 类型u}
  证明: rfl
-/
theorem curry_apply_succ {n : Nat} {p : Fin (n + 1) -> Type u} {τ : Type u}
    (f : ((i : Fin (n + 1)) -> p i) -> τ) (a : p 0) :
    curry f a = curry (f ∘ Fin.cons a) := rfl

variable {n : Nat} {p : Fin n -> Type u} {τ : Type u}

@[simp]
/--
theorem `curry_uncurry` / 定理 `curry_uncurry`

English:
theorem curry_uncurry
  given: (f : Function.FromTypes p τ)
  statement: curry (uncurry f) = f
  proof: by
  induction n with
  | zero => rfl
  | succ n ih => exact funext (ih <| f ·)

@[simp]

中文:
定理 curry_uncurry
  条件: (f : Function.FromTypes p τ)
  结论: curry (uncurry f) = f
  证明: by
  induction n with
  | zero => rfl
  | succ n ih => exact funext (ih <| f ·)

@[simp]
-/
theorem curry_uncurry (f : Function.FromTypes p τ) : curry (uncurry f) = f := by
  induction n with
  | zero => rfl
  | succ n ih => exact funext (ih <| f ·)

@[simp]
/--
theorem `uncurry_curry` / 定理 `uncurry_curry`

English:
theorem uncurry_curry
  given: (f : ((i : Fin n) -> p i) -> τ)
  proof: by
  ext args
  induction n with
  | zero => exact congrArg f (Subsingleton.allEq _ _)
  | succ n ih => exact Eq.trans (ih _ _) (congrArg f (Fin.cons_self_tail args))

中文:
定理 uncurry_curry
  条件: (f : ((i : Fin n) -> p i) -> τ)
  证明: by
  ext args
  induction n with
  | zero => exact congrArg f (Subsingleton.allEq _ _)
  | succ n ih => exact Eq.trans (ih _ _) (congrArg f (Fin.cons_self_tail args))

Depends on / 依赖: Eq.trans, Fin.cons_self_tail, Subsingleton, Subsingleton.allEq, cons_self_tail
-/
theorem uncurry_curry (f : ((i : Fin n) -> p i) -> τ) :
    uncurry (curry f) = f := by
  ext args
  induction n with
  | zero => exact congrArg f (Subsingleton.allEq _ _)
  | succ n ih => exact Eq.trans (ih _ _) (congrArg f (Fin.cons_self_tail args))

/-- `Equiv.curry` for `p`-ary heterogeneous functions. -/
@[simps]
/--
Definition of `curryEquiv` / `curryEquiv` 的定义

English:
definition curryEquiv
  signature: (p : Fin n -> Type u)
  body: curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

中文:
定义 curryEquiv
  签名: (p : Fin n -> 类型u)
  定义体: curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
-/
def curryEquiv (p : Fin n -> Type u) : (((i : Fin n) -> p i) -> τ) ≃ FromTypes p τ where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

/--
lemma `curry_two_eq_curry` / 引理 `curry_two_eq_curry`

English:
lemma curry_two_eq_curry
  statement: {p : Fin 2 -> Type u} {τ : Type u}
  proof: rfl

中文:
引理 curry_two_eq_curry
  结论: {p : Fin 2 -> 类型u} {τ : 类型u}
  证明: rfl
-/
lemma curry_two_eq_curry {p : Fin 2 -> Type u} {τ : Type u}
    (f : ((i : Fin 2) -> p i) -> τ) :
    curry f = Function.curry (f ∘ (piFinTwoEquiv p).symm) := rfl

/--
lemma `uncurry_two_eq_uncurry` / 引理 `uncurry_two_eq_uncurry`

English:
lemma uncurry_two_eq_uncurry
  statement: (p : Fin 2 -> Type u) (τ : Type u)
  proof: rfl

中文:
引理 uncurry_two_eq_uncurry
  结论: (p : Fin 2 -> 类型u) (τ : 类型u)
  证明: rfl
-/
lemma uncurry_two_eq_uncurry (p : Fin 2 -> Type u) (τ : Type u)
    (f : Function.FromTypes p τ) :
    uncurry f = Function.uncurry f ∘ piFinTwoEquiv p := rfl

end Function.FromTypes

namespace Function.OfArity

variable {α β : Type u}

/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: {n} (f : Function.OfArity α β n)
  body: FromTypes.uncurry f

中文:
定义 uncurry
  签名: {n} (f : Function.OfArity α β n)
  定义体: FromTypes.uncurry f

Depends on / 依赖: FromTypes, FromTypes.uncurry, uncurry
-/
def uncurry {n} (f : Function.OfArity α β n) : (Fin n -> α) -> β := FromTypes.uncurry f

/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: {n} (f : (Fin n -> α) -> β)
  body: FromTypes.curry f

@[simp]

中文:
定义 curry
  签名: {n} (f : (Fin n -> α) -> β)
  定义体: FromTypes.curry f

@[simp]

Depends on / 依赖: FromTypes, FromTypes.curry
-/
def curry {n} (f : (Fin n -> α) -> β) : Function.OfArity α β n := FromTypes.curry f

@[simp]
/--
theorem `curry_uncurry` / 定理 `curry_uncurry`

English:
theorem curry_uncurry
  given: {n} (f : Function.OfArity α β n)
  proof: FromTypes.curry_uncurry f

@[simp]

中文:
定理 curry_uncurry
  条件: {n} (f : Function.OfArity α β n)
  证明: FromTypes.curry_uncurry f

@[simp]

Depends on / 依赖: FromTypes, FromTypes.curry_uncurry, curry_uncurry
-/
theorem curry_uncurry {n} (f : Function.OfArity α β n) :
    curry (uncurry f) = f := FromTypes.curry_uncurry f

@[simp]
/--
theorem `uncurry_curry` / 定理 `uncurry_curry`

English:
theorem uncurry_curry
  given: {n} (f : (Fin n -> α) -> β)
  proof: FromTypes.uncurry_curry f

中文:
定理 uncurry_curry
  条件: {n} (f : (Fin n -> α) -> β)
  证明: FromTypes.uncurry_curry f

Depends on / 依赖: FromTypes, FromTypes.uncurry_curry, uncurry_curry
-/
theorem uncurry_curry {n} (f : (Fin n -> α) -> β) :
    uncurry (curry f) = f := FromTypes.uncurry_curry f

/-- `Equiv.curry` for n-ary functions. -/
@[simps!]
/--
Definition of `curryEquiv` / `curryEquiv` 的定义

English:
definition curryEquiv
  signature: (n : Nat)
  body: FromTypes.curryEquiv _

中文:
定义 curryEquiv
  签名: (n : 自然数)
  定义体: FromTypes.curryEquiv _

Depends on / 依赖: FromTypes, FromTypes.curryEquiv, curryEquiv
-/
def curryEquiv (n : Nat) : ((Fin n -> α) -> β) ≃ OfArity α β n :=
  FromTypes.curryEquiv _

/--
lemma `curry_two_eq_curry` / 引理 `curry_two_eq_curry`

English:
lemma curry_two_eq_curry
  given: {α β : Type u} (f : ((i : Fin 2) -> α) -> β)
  proof: FromTypes.curry_two_eq_curry f

中文:
引理 curry_two_eq_curry
  条件: {α β : 类型u} (f : ((i : Fin 2) -> α) -> β)
  证明: FromTypes.curry_two_eq_curry f

Depends on / 依赖: FromTypes, FromTypes.curry_two_eq_curry, curry_two_eq_curry
-/
lemma curry_two_eq_curry {α β : Type u} (f : ((i : Fin 2) -> α) -> β) :
    curry f = Function.curry (f ∘ (finTwoArrowEquiv α).symm) :=
  FromTypes.curry_two_eq_curry f

/--
lemma `uncurry_two_eq_uncurry` / 引理 `uncurry_two_eq_uncurry`

English:
lemma uncurry_two_eq_uncurry
  given: {α β : Type u} (f : OfArity α β 2)
  proof: FromTypes.uncurry_two_eq_uncurry _ _ f

中文:
引理 uncurry_two_eq_uncurry
  条件: {α β : 类型u} (f : OfArity α β 2)
  证明: FromTypes.uncurry_two_eq_uncurry _ _ f

Depends on / 依赖: FromTypes, FromTypes.uncurry_two_eq_uncurry, uncurry_two_eq_uncurry
-/
lemma uncurry_two_eq_uncurry {α β : Type u} (f : OfArity α β 2) :
    uncurry f = Function.uncurry f ∘ (finTwoArrowEquiv α) :=
  FromTypes.uncurry_two_eq_uncurry _ _ f

end Function.OfArity
