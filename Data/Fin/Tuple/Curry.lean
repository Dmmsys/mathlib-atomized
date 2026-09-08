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
/-- Uncurry all the arguments of `Function.FromTypes p τ` to get
a function from a tuple.

Note this can be used on raw functions if used. -/
/-
**Function.FromTypes.uncurry** 是 Mathlib 中的一个定义，位于命名空间 `Function.FromTypes`。
形式化陈述：{n : ℕ} → {p : Fin n → Type u} → {τ : Type u} → Function.FromTypes p τ → (
(i : Fin n) → p i) → τ
参数：(i : Fin n) → p i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uncurry all the arguments of `Function.FromTypes p τ` to get
a function from a tuple.

Note this can be used on raw functions if used.
-/
def uncurry : {n : ℕ} → {p : Fin n → Type u} → {τ : Type u} →
    (f : Function.FromTypes p τ) → ((i : Fin n) → p i) → τ
  | 0    , _, _, f => fun _    => f
  | _ + 1, _, _, f => fun args => (f (args 0)).uncurry (args ∘' Fin.succ)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Curry all the arguments of `Function.FromTypes p τ` to get a function from a tuple. -/
/-
**Function.FromTypes.curry** 是 Mathlib 中的一个定义，位于命名空间 `Function.FromTypes`。
形式化陈述：{n : ℕ} → {p : Fin n → Type u} → {τ : Type u} → (((i : Fin n) → p i) → τ) 
→ Function.FromTypes p τ
参数：((i : Fin n) → p i) → τ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Curry all the arguments of `Function.FromTypes p τ` to get a function from a tup
le.
-/
def curry : {n : ℕ} → {p : Fin n → Type u} → {τ : Type u} →
    (((i : Fin n) → p i) → τ) → Function.FromTypes p τ
  | 0    , _, _, f => f isEmptyElim
  | _ + 1, _, _, f => fun a => curry (fun args => f (Fin.cons a args))

@[simp]
/-
**Function.FromTypes.uncurry_apply_cons** 是 Mathlib 中的一个定理，位于命名空间 `Function.From
Types`。
形式化陈述：uncurry_apply_cons {n : Nat} {α} {p : Fin n -> Type u} {τ : Type u} (f : F
unction.FromTypes (vecCons α p) τ) (a : α) (args : (i : Fin n) -> p i) : uncurry
 f (Fin.cons a args) = @uncurry _ p _ (f a) args
参数：f : Function.FromTypes (vecCons α p) τ；a : α；args : (i : Fin n) -> p i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurry_apply_cons {n : ℕ} {α} {p : Fin n → Type u} {τ : Type u}
    (f : Function.FromTypes (vecCons α p) τ) (a : α) (args : (i : Fin n) → p i) :
    uncurry f (Fin.cons a args) = @uncurry _ p _ (f a) args := rfl

@[simp low]
/-
**Function.FromTypes.uncurry_apply_succ** 是 Mathlib 中的一个定理，位于命名空间 `Function.From
Types`。
形式化陈述：uncurry_apply_succ {n : Nat} {p : Fin (n + 1) -> Type u} {τ : Type u} (f :
 Function.FromTypes p τ) (args : (i : Fin (n + 1)) -> p i) : uncurry f args = un
curry (f (args 0)) (Fin.tail args)
参数：n + 1；f : Function.FromTypes p τ；args : (i : Fin (n + 1)) -> p i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uncurry_apply_succ {n : ℕ} {p : Fin (n + 1) → Type u} {τ : Type u}
    (f : Function.FromTypes p τ) (args : (i : Fin (n + 1)) → p i) :
    uncurry f args = uncurry (f (args 0)) (Fin.tail args) := rfl

@[simp]
/-
**Function.FromTypes.curry_apply_cons** 是 Mathlib 中的一个定理，位于命名空间 `Function.FromTy
pes`。
形式化陈述：curry_apply_cons {n : Nat} {α} {p : Fin n -> Type u} {τ : Type u} (f : ((i
 : Fin (n + 1)) -> (vecCons α p) i) -> τ) (a : α) : curry f a = @curry _ p _ (f 
∘' Fin.cons a :)
参数：f : ((i : Fin (n + 1)) -> (vecCons α p) i) -> τ；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curry_apply_cons {n : ℕ} {α} {p : Fin n → Type u} {τ : Type u}
    (f : ((i : Fin (n + 1)) → (vecCons α p) i) → τ) (a : α) :
    curry f a = @curry _ p _ (f ∘' Fin.cons a :) := rfl

@[simp low]
/-
**Function.FromTypes.curry_apply_succ** 是 Mathlib 中的一个定理，位于命名空间 `Function.FromTy
pes`。
形式化陈述：curry_apply_succ {n : Nat} {p : Fin (n + 1) -> Type u} {τ : Type u} (f : (
(i : Fin (n + 1)) -> p i) -> τ) (a : p 0) : curry f a = curry (f ∘ Fin.cons a)
参数：n + 1；f : ((i : Fin (n + 1)) -> p i) -> τ；a : p 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem curry_apply_succ {n : ℕ} {p : Fin (n + 1) → Type u} {τ : Type u}
    (f : ((i : Fin (n + 1)) → p i) → τ) (a : p 0) :
    curry f a = curry (f ∘ Fin.cons a) := rfl

variable {n : ℕ} {p : Fin n → Type u} {τ : Type u}

@[simp]
/-
**Function.FromTypes.curry_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `Function.FromTypes
`。
形式化陈述：curry_uncurry (f : Function.FromTypes p τ) : curry (uncurry f) = f
参数：f : Function.FromTypes p τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem curry_uncurry (f : Function.FromTypes p τ) : curry (uncurry f) = f := by
  induction n with
  | zero => rfl
  | succ n ih => exact funext (ih <| f ·)

@[simp]
/-
**Function.FromTypes.uncurry_curry** 是 Mathlib 中的一个定理，位于命名空间 `Function.FromTypes
`。
形式化陈述：uncurry_curry (f : ((i : Fin n) -> p i) -> τ) : uncurry (curry f) = f
参数：f : ((i : Fin n) -> p i) -> τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.cons_self_tail`：cons_self_tail : cons (q 0) (tail q) = q
-/
theorem uncurry_curry (f : ((i : Fin n) → p i) → τ) :
    uncurry (curry f) = f := by
  ext args
  induction n with
  | zero => exact congrArg f (Subsingleton.allEq _ _)
  | succ n ih => exact Eq.trans (ih _ _) (congrArg f (Fin.cons_self_tail args))

/-- `Equiv.curry` for `p`-ary heterogeneous functions. -/
@[simps]
/-
**Function.FromTypes.curryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Function.FromTypes`。
形式化陈述：curryEquiv (p : Fin n -> Type u) : (((i : Fin n) -> p i) -> τ) ≃ FromTypes
 p τ where toFun
参数：p : Fin n -> Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Function.FromTypes.uncurry_curry`：uncurry_curry (f : ((i : Fin n) -> p i
) -> τ) : uncurry (curry f) = f
· 使用定理 `Function.FromTypes.curry_uncurry`：curry_uncurry (f : Function.FromTypes 
p τ) : curry (uncurry f) = f

--- 原说明 ---
`Equiv.curry` for `p`-ary heterogeneous functions.
-/
def curryEquiv (p : Fin n → Type u) : (((i : Fin n) → p i) → τ) ≃ FromTypes p τ where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
/-
**Function.FromTypes.curry_two_eq_curry** 是 Mathlib 中的一个引理，位于命名空间 `Function.From
Types`。
形式化陈述：curry_two_eq_curry {p : Fin 2 -> Type u} {τ : Type u} (f : ((i : Fin 2) ->
 p i) -> τ) : curry f = Function.curry (f ∘ (piFinTwoEquiv p).symm)
参数：f : ((i : Fin 2) -> p i) -> τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma curry_two_eq_curry {p : Fin 2 → Type u} {τ : Type u}
    (f : ((i : Fin 2) → p i) → τ) :
    curry f = Function.curry (f ∘ (piFinTwoEquiv p).symm) := rfl
/-
**Function.FromTypes.uncurry_two_eq_uncurry** 是 Mathlib 中的一个引理，位于命名空间 `Function.
FromTypes`。
形式化陈述：uncurry_two_eq_uncurry (p : Fin 2 -> Type u) (τ : Type u) (f : Function.Fr
omTypes p τ) : uncurry f = Function.uncurry f ∘ piFinTwoEquiv p
参数：p : Fin 2 -> Type u；τ : Type u；f : Function.FromTypes p τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uncurry_two_eq_uncurry (p : Fin 2 → Type u) (τ : Type u)
    (f : Function.FromTypes p τ) :
    uncurry f = Function.uncurry f ∘ piFinTwoEquiv p := rfl

end Function.FromTypes

namespace Function.OfArity

variable {α β : Type u}

/-- Uncurry all the arguments of `Function.OfArity α n` to get a function from a tuple.

Note this can be used on raw functions if used. -/
/-
**Function.OfArity.uncurry** 是 Mathlib 中的一个定义，位于命名空间 `Function.OfArity`。
形式化陈述：uncurry {n} (f : Function.OfArity α β n) : (Fin n -> α) -> β
参数：f : Function.OfArity α β n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uncurry all the arguments of `Function.OfArity α n` to get a function from a tup
le.

Note this can be used on raw functions if used.
-/
def uncurry {n} (f : Function.OfArity α β n) : (Fin n → α) → β := FromTypes.uncurry f

/-- Curry all the arguments of `Function.OfArity α β n` to get a function from a tuple. -/
/-
**Function.OfArity.curry** 是 Mathlib 中的一个定义，位于命名空间 `Function.OfArity`。
形式化陈述：curry {n} (f : (Fin n -> α) -> β) : Function.OfArity α β n
参数：f : (Fin n -> α) -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Curry all the arguments of `Function.OfArity α β n` to get a function from a tup
le.
-/
def curry {n} (f : (Fin n → α) → β) : Function.OfArity α β n := FromTypes.curry f

@[simp]
/-
**Function.OfArity.curry_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `Function.OfArity`。
形式化陈述：curry_uncurry {n} (f : Function.OfArity α β n) : curry (uncurry f) = f
参数：f : Function.OfArity α β n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.FromTypes.curry_uncurry`：curry_uncurry (f : Function.FromTypes 
p τ) : curry (uncurry f) = f
-/
theorem curry_uncurry {n} (f : Function.OfArity α β n) :
    curry (uncurry f) = f := FromTypes.curry_uncurry f

@[simp]
/-
**Function.OfArity.uncurry_curry** 是 Mathlib 中的一个定理，位于命名空间 `Function.OfArity`。
形式化陈述：uncurry_curry {n} (f : (Fin n -> α) -> β) : uncurry (curry f) = f
参数：f : (Fin n -> α) -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.FromTypes.uncurry_curry`：uncurry_curry (f : ((i : Fin n) -> p i
) -> τ) : uncurry (curry f) = f
-/
theorem uncurry_curry {n} (f : (Fin n → α) → β) :
    uncurry (curry f) = f := FromTypes.uncurry_curry f

/-- `Equiv.curry` for n-ary functions. -/
@[simps!]
/-
**Function.OfArity.curryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Function.OfArity`。
形式化陈述：curryEquiv (n : Nat) : ((Fin n -> α) -> β) ≃ OfArity α β n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.curry` for n-ary functions.
-/
def curryEquiv (n : ℕ) : ((Fin n → α) → β) ≃ OfArity α β n :=
  FromTypes.curryEquiv _
/-
**Function.OfArity.curry_two_eq_curry** 是 Mathlib 中的一个引理，位于命名空间 `Function.OfArit
y`。
形式化陈述：curry_two_eq_curry {α β : Type u} (f : ((i : Fin 2) -> α) -> β) : curry f 
= Function.curry (f ∘ (finTwoArrowEquiv α).symm)
参数：f : ((i : Fin 2) -> α) -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.FromTypes.curry_two_eq_curry`：curry_two_eq_curry {p : Fin 2 -> 
Type u} {τ : Type u} (f : ((i : Fin 2) -> p i) -> τ) : curry f = Function.curry 
(f ∘ (piFinTwoEquiv p).symm…
-/
lemma curry_two_eq_curry {α β : Type u} (f : ((i : Fin 2) → α) → β) :
    curry f = Function.curry (f ∘ (finTwoArrowEquiv α).symm) :=
  FromTypes.curry_two_eq_curry f
/-
**Function.OfArity.uncurry_two_eq_uncurry** 是 Mathlib 中的一个引理，位于命名空间 `Function.Of
Arity`。
形式化陈述：uncurry_two_eq_uncurry {α β : Type u} (f : OfArity α β 2) : uncurry f = Fu
nction.uncurry f ∘ (finTwoArrowEquiv α)
参数：f : OfArity α β 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.FromTypes.uncurry_two_eq_uncurry`：uncurry_two_eq_uncurry (p : F
in 2 -> Type u) (τ : Type u) (f : Function.FromTypes p τ) : uncurry f = Function
.uncurry f ∘ piFinTwoEquiv p
-/
lemma uncurry_two_eq_uncurry {α β : Type u} (f : OfArity α β 2) :
    uncurry f = Function.uncurry f ∘ (finTwoArrowEquiv α) :=
  FromTypes.uncurry_two_eq_uncurry _ _ f

end Function.OfArity

