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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] {n
  body: Finite.of_equiv _ (Equiv.vectorEquivFin _ _).symm

中文:
实例 [有限
  签名: α] {n
  定义体: Finite.of_equiv _ (Equiv.vectorEquivFin _ _).symm

Depends on / 依赖: Equiv.vectorEquivFin, Finite, Finite.of_equiv, of_equiv, vectorEquivFin
-/
instance [Finite α] {n : Nat} : Finite (List.Vector α n) :=
  Finite.of_equiv _ (Equiv.vectorEquivFin _ _).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: α] {n
  body: fast_instance% Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm

中文:
实例 [有限类型
  签名: α] {n
  定义体: fast_instance% Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm

Depends on / 依赖: Equiv.vectorEquivFin, Fintype, Fintype.ofEquiv, fast_instance, ofEquiv, vectorEquivFin
-/
instance [Fintype α] {n : Nat} : Fintype (List.Vector α n) :=
  fast_instance% Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm

end List.Vector

namespace Sym.Sym'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] {n
  body: inferInstanceAs Finite (Quotient _)

中文:
实例 [有限
  签名: α] {n
  定义体: inferInstanceAs Finite (Quotient _)

Depends on / 依赖: Finite, Quotient
-/
instance [Finite α] {n : Nat} : Finite (Sym.Sym' α n) :=
inferInstanceAs Finite (Quotient _)

/--
Instance `instFintype` / 实例 `instFintype`

English:
instance instFintype
  signature: [DecidableEq α] [Fintype α] {n : Nat}
  body: inferInstanceAs Fintype (Quotient _)

中文:
实例 instFintype
  签名: [DecidableEq α] [有限类型 α] {n : 自然数}
  定义体: inferInstanceAs Fintype (Quotient _)

Depends on / 依赖: Fintype, Quotient
-/
instance instFintype [DecidableEq α] [Fintype α] {n : Nat} : Fintype (Sym.Sym' α n) :=
inferInstanceAs Fintype (Quotient _)

end Sym.Sym'

namespace Sym

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] {n
  body: Finite.of_equiv _ Sym.symEquivSym'.symm

中文:
实例 [有限
  签名: α] {n
  定义体: Finite.of_equiv _ Sym.symEquivSym'.symm

Depends on / 依赖: Finite, Finite.of_equiv, Sym.symEquivSym, of_equiv, symEquivSym
-/
instance [Finite α] {n : Nat} : Finite (Sym α n) :=
  Finite.of_equiv _ Sym.symEquivSym'.symm

/--
Instance `instFintype` / 实例 `instFintype`

English:
instance instFintype
  signature: [DecidableEq α] [Fintype α] {n : Nat}
  body: fast_instance% Fintype.ofEquiv _ Sym.symEquivSym'.symm

中文:
实例 instFintype
  签名: [DecidableEq α] [有限类型 α] {n : 自然数}
  定义体: fast_instance% Fintype.ofEquiv _ Sym.symEquivSym'.symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, Sym.symEquivSym, fast_instance, ofEquiv, symEquivSym
-/
instance instFintype [DecidableEq α] [Fintype α] {n : Nat} : Fintype (Sym α n) :=
  fast_instance% Fintype.ofEquiv _ Sym.symEquivSym'.symm

end Sym
