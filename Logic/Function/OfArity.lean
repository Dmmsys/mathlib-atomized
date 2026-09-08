/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Function.FromTypes

/-! # Function types of a given arity

This provides `Function.OfArity`, such that `OfArity α β 2 = α → α → β`.
Note that it is often preferable to use `(Fin n → α) → β` in place of `OfArity n α β`.

## Main definitions

* `Function.OfArity α β n`: `n`-ary function `α → α → ... → β`. Defined inductively.
* `Function.OfArity.const α b n`: `n`-ary constant function equal to `b`.
-/

@[expose] public section

universe u

namespace Function

/-- The type of `n`-ary functions `α → α → ... → β`.

Note that this is not universe polymorphic, as this would require that when `n=0` we produce either
`Unit → β` or `ULift β`. -/
/-
**Function.OfArity** 是 Mathlib 中的一个缩写定义，位于命名空间 `Function`。
形式化陈述：OfArity (α β : Type u) (n : Nat) : Type u
参数：α β : Type u；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `n`-ary functions `α → α → ... → β`.

Note that this is not universe polymorphic, as this would require that when `n=0
` we produce either
`Unit → β` or `ULift β`.
-/
abbrev OfArity (α β : Type u) (n : ℕ) : Type u := FromTypes (fun (_ : Fin n) => α) β

@[simp]
/-
**Function.ofArity_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：ofArity_zero (α β : Type u) : OfArity α β 0 = β
参数：α β : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.fromTypes_zero`：fromTypes_zero (p : Fin 0 -> Type u) (τ : Type 
u) : FromTypes p τ = τ
-/
theorem ofArity_zero (α β : Type u) : OfArity α β 0 = β := fromTypes_zero _ _

@[simp]
/-
**Function.ofArity_succ** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：ofArity_succ (α β : Type u) (n : Nat) : OfArity α β n.succ = (α -> OfArity
 α β n)
参数：α β : Type u；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.fromTypes_succ`：fromTypes_succ {n} (p : Fin (n + 1) -> Type u) 
(τ : Type u) : FromTypes p τ = (vecHead p -> FromTypes (vecTail p) τ)
-/
theorem ofArity_succ (α β : Type u) (n : ℕ) :
    OfArity α β n.succ = (α → OfArity α β n) := fromTypes_succ _ _

namespace OfArity

/-- Constant `n`-ary function with value `b`. -/
/-
**Function.OfArity.const** 是 Mathlib 中的一个定义，位于命名空间 `Function.OfArity`。
形式化陈述：const (α : Type u) {β : Type u} (b : β) (n : Nat) : OfArity α β n
参数：α : Type u；b : β；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constant `n`-ary function with value `b`.
-/
def const (α : Type u) {β : Type u} (b : β) (n : ℕ) : OfArity α β n :=
  FromTypes.const (fun _ => α) b

@[simp]
/-
**Function.OfArity.const_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.OfArity`。
形式化陈述：const_zero (α : Type u) {β : Type u} (b : β) : const α b 0 = b
参数：α : Type u；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.FromTypes.const_zero`：const_zero (p : Fin 0 -> Type u) {τ : Typ
e u} (t : τ) : const p t = t
-/
theorem const_zero (α : Type u) {β : Type u} (b : β) : const α b 0 = b :=
  FromTypes.const_zero (fun _ => α) b

@[simp]
/-
**Function.OfArity.const_succ** 是 Mathlib 中的一个定理，位于命名空间 `Function.OfArity`。
形式化陈述：const_succ (α : Type u) {β : Type u} (b : β) (n : Nat) : const α b n.succ 
= fun _ => const _ b n
参数：α : Type u；b : β；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.FromTypes.const_succ`：const_succ {n} (p : Fin (n + 1) -> Type u
) {τ : Type u} (t : τ) : const p t = fun _ => const (vecTail p) t
-/
theorem const_succ (α : Type u) {β : Type u} (b : β) (n : ℕ) :
    const α b n.succ = fun _ => const _ b n :=
  FromTypes.const_succ (fun _ => α) b
/-
**Function.OfArity.const_succ_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.OfArity`
。
形式化陈述：const_succ_apply (α : Type u) {β : Type u} (b : β) (n : Nat) (x : α) : con
st α b n.succ x = const _ b n
参数：α : Type u；b : β；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.FromTypes.const_succ_apply`：const_succ_apply {n} (p : Fin (n + 
1) -> Type u) {τ : Type u} (t : τ) (x : p 0) : const p t x = const (vecTail p) t
-/
theorem const_succ_apply (α : Type u) {β : Type u} (b : β) (n : ℕ) (x : α) :
    const α b n.succ x = const _ b n := FromTypes.const_succ_apply _ b x
/-
**Function.OfArity.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `Function.OfArity`。
形式化陈述：inhabited {α β n} [Inhabited β] : Inhabited (OfArity α β n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited {α β n} [Inhabited β] : Inhabited (OfArity α β n) :=
  inferInstanceAs (Inhabited (FromTypes (fun _ => α) β))

end OfArity

namespace FromTypes

/-
**Function.FromTypes.fromTypes_fin_const** 是 Mathlib 中的一个引理，位于命名空间 `Function.Fro
mTypes`。
形式化陈述：fromTypes_fin_const (α β : Type u) (n : Nat) : FromTypes (fun (_ : Fin n) 
=> α) β = OfArity α β n
参数：α β : Type u；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromTypes_fin_const (α β : Type u) (n : ℕ) :
    FromTypes (fun (_ : Fin n) => α) β = OfArity α β n := rfl

/-- The definitional equality between heterogeneous functions with constant
domain and `n`-ary functions with that domain. -/
/-
**Function.FromTypes.fromTypes_fin_const_equiv** 是 Mathlib 中的一个定义，位于命名空间 `Functi
on.FromTypes`。
形式化陈述：fromTypes_fin_const_equiv (α β : Type u) (n : Nat) : FromTypes (fun (_ : F
in n) => α) β ≃ OfArity α β n
参数：α β : Type u；n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The definitional equality between heterogeneous functions with constant
domain and `n`-ary functions with that domain.
-/
def fromTypes_fin_const_equiv (α β : Type u) (n : ℕ) :
    FromTypes (fun (_ : Fin n) => α) β ≃ OfArity α β n := .refl _

end FromTypes

end Function

