/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Vector.Basic
public import Mathlib.Logic.Equiv.Finset

/-!
# Encodability of Pi types

This file provides instances of `Encodable` for types of vectors and (dependent) functions:

* `Encodable.List.Vector.encodable`: vectors of length `n` (represented by lists) are encodable
* `Encodable.finArrow`: vectors of length `n` (represented by `Fin`-indexed functions) are encodable
* `Encodable.fintypeArrow`, `Encodable.fintypePi`: (dependent) functions with
  finite domain and countable codomain are encodable
-/

@[expose] public section

open List (Vector)
open Nat List

namespace Encodable

variable {α : Type*}

/-- If `α` is encodable, then so is `Vector α n`. -/
/-
**Encodable.List.Vector.encodable** 是 Mathlib 中的一个定义，位于命名空间 `Encodable.List.Vect
or`。
形式化陈述：{α : Type u_1} → [Encodable α] → {n : ℕ} → Encodable (List.Vector α n)
参数：List.Vector α n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is encodable, then so is `Vector α n`.
-/
instance List.Vector.encodable [Encodable α] {n} : Encodable (List.Vector α n) :=
  inferInstanceAs <| Encodable (Subtype _)

/-- If `α` is countable, then so is `Vector α n`. -/
/-
**Encodable.List.Vector.countable** 是 Mathlib 中的一个定理，位于命名空间 `Encodable.List.Vect
or`。
形式化陈述：∀ {α : Type u_1} [Countable α] {n : ℕ}, Countable (List.Vector α n)
参数：List.Vector α n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is countable, then so is `Vector α n`.
-/
instance List.Vector.countable [Countable α] {n} : Countable (List.Vector α n) :=
  inferInstanceAs <| Countable (Subtype _)

/-- If `α` is encodable, then so is `Fin n → α`. -/
/-
**Encodable.finArrow** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
形式化陈述：finArrow [Encodable α] {n} : Encodable (Fin n -> α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α` is encodable, then so is `Fin n → α`.
-/
instance finArrow [Encodable α] {n} : Encodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm
/-
**Encodable.finPi** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
形式化陈述：finPi (n) (π : Fin n -> Type*) [forall i, Encodable (π i)] : Encodable (fo
rall i, π i)
参数：n；π : Fin n -> Type*；π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finPi (n) (π : Fin n → Type*) [∀ i, Encodable (π i)] : Encodable (∀ i, π i) :=
  ofEquiv _ (Equiv.piEquivSubtypeSigma (Fin n) π)

-- TODO: Unify with `fintypePi` and find a better name
/-- When `α` is finite and `β` is encodable, `α → β` is encodable too. Because the encoding is not
unique, we wrap it in `Trunc` to preserve computability. -/
/-
**Encodable.fintypeArrow** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：fintypeArrow (α : Type*) (β : Type*) [DecidableEq α] [Fintype α] [Encodabl
e β] : Trunc (Encodable (α -> β))
参数：α : Type*；β : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
When `α` is finite and `β` is encodable, `α → β` is encodable too. Because the e
ncoding is not
unique, we wrap it in `Trunc` to preserve computability.
-/
def fintypeArrow (α : Type*) (β : Type*) [DecidableEq α] [Fintype α] [Encodable β] :
    Trunc (Encodable (α → β)) :=
  (Fintype.truncEquivFin α).map fun f =>
    Encodable.ofEquiv (Fin (Fintype.card α) → β) <| Equiv.arrowCongr f (Equiv.refl _)

/-- When `α` is finite and all `π a` are encodable, `Π a, π a` is encodable too. Because the
encoding is not unique, we wrap it in `Trunc` to preserve computability. -/
/-
**Encodable.fintypePi** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：fintypePi (α : Type*) (π : α -> Type*) [DecidableEq α] [Fintype α] [forall
 a, Encodable (π a)] : Trunc (Encodable (forall a, π a))
参数：α : Type*；π : α -> Type*；π a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `α` is finite and all `π a` are encodable, `Π a, π a` is encodable too. Bec
ause the
encoding is not unique, we wrap it in `Trunc` to preserve computability.
-/
def fintypePi (α : Type*) (π : α → Type*) [DecidableEq α] [Fintype α] [∀ a, Encodable (π a)] :
    Trunc (Encodable (∀ a, π a)) :=
  (Fintype.truncEncodable α).bind fun a =>
    (@fintypeArrow α (Σ a, π a) _ _ (@Sigma.encodable _ _ a _)).bind fun f =>
      Trunc.mk <|
        @Encodable.ofEquiv _ _ (@Subtype.encodable _ _ f _)
          (Equiv.piEquivSubtypeSigma α π)

/-- If `α` and `β` are encodable and `α` is a fintype, then `α → β` is encodable as well. -/
/-
**Encodable.fintypeArrowOfEncodable** 是 Mathlib 中的一个实例，位于命名空间 `Encodable`。
形式化陈述：fintypeArrowOfEncodable {α β : Type*} [Encodable α] [Fintype α] [Encodable
 β] : Encodable (α -> β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
If `α` and `β` are encodable and `α` is a fintype, then `α → β` is encodable as 
well.
-/
instance fintypeArrowOfEncodable {α β : Type*} [Encodable α] [Fintype α] [Encodable β] :
    Encodable (α → β) :=
  ofEquiv (Fin (Fintype.card α) → β) <| Equiv.arrowCongr fintypeEquivFin (Equiv.refl _)

end Encodable

