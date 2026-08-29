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

/--
Instance `List.Vector.encodable` / 实例 `List.Vector.encodable`

English:
instance List.Vector.encodable
  signature: [Encodable α] {n}
  body: inferInstanceAs Encodable (Subtype _)

中文:
实例 List.Vector.encodable
  签名: [Encodable α] {n}
  定义体: inferInstanceAs Encodable (Subtype _)

Depends on / 依赖: Encodable, Subtype
-/
instance List.Vector.encodable [Encodable α] {n} : Encodable (List.Vector α n) :=
inferInstanceAs Encodable (Subtype _)

/--
Instance `List.Vector.countable` / 实例 `List.Vector.countable`

English:
instance List.Vector.countable
  signature: [Countable α] {n}
  body: inferInstanceAs Countable (Subtype _)

中文:
实例 List.Vector.countable
  签名: [Countable α] {n}
  定义体: inferInstanceAs Countable (Subtype _)

Depends on / 依赖: Countable, Subtype
-/
instance List.Vector.countable [Countable α] {n} : Countable (List.Vector α n) :=
inferInstanceAs Countable (Subtype _)

/--
Instance `finArrow` / 实例 `finArrow`

English:
instance finArrow
  signature: [Encodable α] {n}
  body: ofEquiv _ (Equiv.vectorEquivFin _ _).symm

中文:
实例 finArrow
  签名: [Encodable α] {n}
  定义体: ofEquiv _ (Equiv.vectorEquivFin _ _).symm

Depends on / 依赖: Equiv.vectorEquivFin, ofEquiv, vectorEquivFin
-/
instance finArrow [Encodable α] {n} : Encodable (Fin n -> α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm

/--
Instance `finPi` / 实例 `finPi`

English:
instance finPi
  signature: (n) (π : Fin n -> Type*) [forall i, Encodable (π i)]
  body: ofEquiv _ (Equiv.piEquivSubtypeSigma (Fin n) π)

中文:
实例 finPi
  签名: (n) (π : Fin n -> 类型) [对任意 i, Encodable (π i)]
  定义体: ofEquiv _ (Equiv.piEquivSubtypeSigma (Fin n) π)

Depends on / 依赖: Equiv.piEquivSubtypeSigma, ofEquiv, piEquivSubtypeSigma
-/
instance finPi (n) (π : Fin n -> Type*) [forall i, Encodable (π i)] : Encodable (forall i, π i) :=
  ofEquiv _ (Equiv.piEquivSubtypeSigma (Fin n) π)

-- TODO: Unify with `fintypePi` and find a better name
/--
Definition of `fintypeArrow` / `fintypeArrow` 的定义

English:
definition fintypeArrow
  signature: (α : Type*) (β : Type*) [DecidableEq α] [Fintype α] [Encodable β]
  body: (Fintype.truncEquivFin α).map fun f =>
Encodable.ofEquiv (Fin (Fintype.card α) -> β) Equiv.arrowCongr f (Equiv.refl _)

中文:
定义 fintypeArrow
  签名: (α : 类型) (β : 类型) [DecidableEq α] [Fintype α] [Encodable β]
  定义体: (Fintype.truncEquivFin α).map fun f =>
Encodable.ofEquiv (Fin (Fintype.card α) -> β) Equiv.arrowCongr f (Equiv.refl _)

Depends on / 依赖: Encodable, Encodable.ofEquiv, Equiv.arrowCongr, Equiv.refl, Fintype, Fintype.card, Fintype.truncEquivFin, arrowCongr, ofEquiv, truncEquivFin
-/
def fintypeArrow (α : Type*) (β : Type*) [DecidableEq α] [Fintype α] [Encodable β] :
    Trunc (Encodable (α -> β)) :=
  (Fintype.truncEquivFin α).map fun f =>
Encodable.ofEquiv (Fin (Fintype.card α) -> β) Equiv.arrowCongr f (Equiv.refl _)

/--
Definition of `fintypePi` / `fintypePi` 的定义

English:
definition fintypePi
  signature: (α : Type*) (π : α -> Type*) [DecidableEq α] [Fintype α] [forall a, Encodable (π a)]
  body: (Fintype.truncEncodable α).bind fun a =>
    (@fintypeArrow α (Σ a, π a) _ _ (@Sigma.encodable _ _ a _)).bind fun f =>
Trunc.mk
        @Encodable.ofEquiv _ _ (@Subtype.encodable _ _ f _)
          (Equiv.piEquivSubtypeSigma α π)

中文:
定义 fintypePi
  签名: (α : 类型) (π : α -> 类型) [DecidableEq α] [Fintype α] [对任意 a, Encodable (π a)]
  定义体: (Fintype.truncEncodable α).bind fun a =>
    (@fintypeArrow α (Σ a, π a) _ _ (@Sigma.encodable _ _ a _)).bind fun f =>
Trunc.mk
        @Encodable.ofEquiv _ _ (@Subtype.encodable _ _ f _)
          (Equiv.piEquivSubtypeSigma α π)

Depends on / 依赖: Encodable, Encodable.ofEquiv, Equiv.piEquivSubtypeSigma, Fintype, Fintype.truncEncodable, Sigma.encodable, Subtype, Subtype.encodable, Trunc.mk, encodable, fintypeArrow, ofEquiv, piEquivSubtypeSigma, truncEncodable
-/
def fintypePi (α : Type*) (π : α -> Type*) [DecidableEq α] [Fintype α] [forall a, Encodable (π a)] :
    Trunc (Encodable (forall a, π a)) :=
  (Fintype.truncEncodable α).bind fun a =>
    (@fintypeArrow α (Σ a, π a) _ _ (@Sigma.encodable _ _ a _)).bind fun f =>
Trunc.mk
        @Encodable.ofEquiv _ _ (@Subtype.encodable _ _ f _)
          (Equiv.piEquivSubtypeSigma α π)

/--
Instance `fintypeArrowOfEncodable` / 实例 `fintypeArrowOfEncodable`

English:
instance fintypeArrowOfEncodable
  signature: {α β : Type*} [Encodable α] [Fintype α] [Encodable β]
  body: ofEquiv (Fin (Fintype.card α) -> β) Equiv.arrowCongr fintypeEquivFin (Equiv.refl _)

中文:
实例 fintypeArrowOfEncodable
  签名: {α β : 类型} [Encodable α] [Fintype α] [Encodable β]
  定义体: ofEquiv (Fin (Fintype.card α) -> β) Equiv.arrowCongr fintypeEquivFin (Equiv.refl _)

Depends on / 依赖: Equiv.arrowCongr, Equiv.refl, Fintype, Fintype.card, arrowCongr, fintypeEquivFin, ofEquiv
-/
instance fintypeArrowOfEncodable {α β : Type*} [Encodable α] [Fintype α] [Encodable β] :
    Encodable (α -> β) :=
ofEquiv (Fin (Fintype.card α) -> β) Equiv.arrowCongr fintypeEquivFin (Equiv.refl _)

end Encodable
