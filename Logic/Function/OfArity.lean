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

/--
Definition of `OfArity` / `OfArity` 的定义

English:
abbreviation OfArity
  signature: (α β : Type u) (n : Nat)
  body: FromTypes (fun (_ : Fin n) => α) β

@[simp]

中文:
缩写 OfArity
  签名: (α β : 类型u) (n : 自然数)
  定义体: FromTypes (fun (_ : Fin n) => α) β

@[simp]

Depends on / 依赖: FromTypes
-/
abbrev OfArity (α β : Type u) (n : Nat) : Type u := FromTypes (fun (_ : Fin n) => α) β

@[simp]
/--
theorem `ofArity_zero` / 定理 `ofArity_zero`

English:
theorem ofArity_zero
  given: (α β : Type u)
  statement: OfArity α β 0 = β
  proof: fromTypes_zero _ _

@[simp]

中文:
定理 ofArity_zero
  条件: (α β : 类型u)
  结论: OfArity α β 0 = β
  证明: fromTypes_zero _ _

@[simp]

Depends on / 依赖: fromTypes_zero
-/
theorem ofArity_zero (α β : Type u) : OfArity α β 0 = β := fromTypes_zero _ _

@[simp]
/--
theorem `ofArity_succ` / 定理 `ofArity_succ`

English:
theorem ofArity_succ
  given: (α β : Type u) (n : Nat)
  proof: fromTypes_succ _ _

中文:
定理 ofArity_succ
  条件: (α β : 类型u) (n : 自然数)
  证明: fromTypes_succ _ _

Depends on / 依赖: fromTypes_succ
-/
theorem ofArity_succ (α β : Type u) (n : Nat) :
    OfArity α β n.succ = (α -> OfArity α β n) := fromTypes_succ _ _

namespace OfArity

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (α : Type u) {β : Type u} (b : β) (n : Nat)
  body: FromTypes.const (fun _ => α) b

@[simp]

中文:
定义 const
  签名: (α : 类型u) {β : 类型u} (b : β) (n : 自然数)
  定义体: FromTypes.const (fun _ => α) b

@[simp]

Depends on / 依赖: FromTypes, FromTypes.const
-/
def const (α : Type u) {β : Type u} (b : β) (n : Nat) : OfArity α β n :=
  FromTypes.const (fun _ => α) b

@[simp]
/--
theorem `const_zero` / 定理 `const_zero`

English:
theorem const_zero
  given: (α : Type u) {β : Type u} (b : β)
  statement: const α b 0 = b
  proof: FromTypes.const_zero (fun _ => α) b

@[simp]

中文:
定理 const_zero
  条件: (α : 类型u) {β : 类型u} (b : β)
  结论: const α b 0 = b
  证明: FromTypes.const_zero (fun _ => α) b

@[simp]

Depends on / 依赖: FromTypes, FromTypes.const_zero, const_zero
-/
theorem const_zero (α : Type u) {β : Type u} (b : β) : const α b 0 = b :=
  FromTypes.const_zero (fun _ => α) b

@[simp]
/--
theorem `const_succ` / 定理 `const_succ`

English:
theorem const_succ
  given: (α : Type u) {β : Type u} (b : β) (n : Nat)
  proof: FromTypes.const_succ (fun _ => α) b

中文:
定理 const_succ
  条件: (α : 类型u) {β : 类型u} (b : β) (n : 自然数)
  证明: FromTypes.const_succ (fun _ => α) b

Depends on / 依赖: FromTypes, FromTypes.const_succ, const_succ
-/
theorem const_succ (α : Type u) {β : Type u} (b : β) (n : Nat) :
    const α b n.succ = fun _ => const _ b n :=
  FromTypes.const_succ (fun _ => α) b

/--
theorem `const_succ_apply` / 定理 `const_succ_apply`

English:
theorem const_succ_apply
  given: (α : Type u) {β : Type u} (b : β) (n : Nat) (x : α)
  proof: FromTypes.const_succ_apply _ b x

中文:
定理 const_succ_apply
  条件: (α : 类型u) {β : 类型u} (b : β) (n : 自然数) (x : α)
  证明: FromTypes.const_succ_apply _ b x

Depends on / 依赖: FromTypes, FromTypes.const_succ_apply, const_succ_apply
-/
theorem const_succ_apply (α : Type u) {β : Type u} (b : β) (n : Nat) (x : α) :
    const α b n.succ x = const _ b n := FromTypes.const_succ_apply _ b x

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: {α β n} [Inhabited β]
  body: inferInstanceAs (Inhabited (FromTypes (fun _ => α) β))

中文:
实例 inhabited
  签名: {α β n} [Inhabited β]
  定义体: inferInstanceAs (Inhabited (FromTypes (fun _ => α) β))

Depends on / 依赖: FromTypes, Inhabited
-/
instance inhabited {α β n} [Inhabited β] : Inhabited (OfArity α β n) :=
  inferInstanceAs (Inhabited (FromTypes (fun _ => α) β))

end OfArity

namespace FromTypes

/--
lemma `fromTypes_fin_const` / 引理 `fromTypes_fin_const`

English:
lemma fromTypes_fin_const
  given: (α β : Type u) (n : Nat)
  proof: rfl

中文:
引理 fromTypes_fin_const
  条件: (α β : 类型u) (n : 自然数)
  证明: rfl
-/
lemma fromTypes_fin_const (α β : Type u) (n : Nat) :
    FromTypes (fun (_ : Fin n) => α) β = OfArity α β n := rfl

/--
Definition of `fromTypes_fin_const_equiv` / `fromTypes_fin_const_equiv` 的定义

English:
definition fromTypes_fin_const_equiv
  signature: (α β : Type u) (n : Nat)
  body: .refl _

中文:
定义 fromTypes_fin_const_equiv
  签名: (α β : 类型u) (n : 自然数)
  定义体: .refl _
-/
def fromTypes_fin_const_equiv (α β : Type u) (n : Nat) :
    FromTypes (fun (_ : Fin n) => α) β ≃ OfArity α β n := .refl _

end FromTypes

end Function
