/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Sym.Basic

/-!
# `Vector α n` and `Sym α n` are fintypes when `α` is.
-/

public section

open List (Vector)

variable {α : Type*}

namespace List.Vector

/-
**List.Vector.** 是 Mathlib 中的一个实例，位于命名空间 `List.Vector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] {n : ℕ} : Finite (List.Vector α n) :=
  Finite.of_equiv _ (Equiv.vectorEquivFin _ _).symm
/-
**List.Vector.** 是 Mathlib 中的一个实例，位于命名空间 `List.Vector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype α] {n : ℕ} : Fintype (List.Vector α n) :=
  fast_instance% Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm

end List.Vector

namespace Sym.Sym'

/-
**Sym.Sym.** 是 Mathlib 中的一个实例，位于命名空间 `Sym.Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] {n : ℕ} : Finite (Sym.Sym' α n) :=
  inferInstanceAs <| Finite (Quotient _)
/-
**Sym.Sym.instFintype** 是 Mathlib 中的一个实例，位于命名空间 `Sym.Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFintype [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym.Sym' α n) :=
  inferInstanceAs <| Fintype (Quotient _)

end Sym.Sym'

namespace Sym

/-
**Sym.** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] {n : ℕ} : Finite (Sym α n) :=
  Finite.of_equiv _ Sym.symEquivSym'.symm
/-
**Sym.instFintype** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
形式化陈述：instFintype [DecidableEq α] [Fintype α] {n : Nat} : Fintype (Sym α n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance instFintype [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym α n) :=
  fast_instance% Fintype.ofEquiv _ Sym.symEquivSym'.symm

end Sym

