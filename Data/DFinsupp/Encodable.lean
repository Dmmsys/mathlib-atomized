/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.DFinsupp.Defs
public import Mathlib.Logic.Encodable.Pi
/-!
# `Encodable` and `Countable` instances for `Π₀ i, α i`

In this file we provide instances for `Encodable (Π₀ i, α i)` and `Countable (Π₀ i, α i)`.
-/

public section

variable {ι : Type*} {α : ι -> Type*} [forall i, Zero (α i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Encodable
  signature: ι] [forall i, Encodable (α i)] [forall i (x : α i), Decidable (x != 0)] :
  body: letI : DecidableEq ι := Encodable.decidableEqOfEncodable _
  letI : forall s : Finset ι, Encodable (forall i : s, {x : α i // x != 0}) := fun _ =>
.ofEquiv _ .piCongrLeft' _ Encodable.fintypeEquivFin
  .ofEquiv _ DFinsupp.sigmaFinsetFunEquiv

中文:
实例 [Encodable
  签名: ι] [对任意 i, Encodable (α i)] [对任意 i (x : α i), Decidable (x != 0)] :
  定义体: letI : DecidableEq ι := Encodable.decidableEqOfEncodable _
  letI : forall s : Finset ι, Encodable (forall i : s, {x : α i // x != 0}) := fun _ =>
.ofEquiv _ .piCongrLeft' _ Encodable.fintypeEquivFin
  .ofEquiv _ DFinsupp.sigmaFinsetFunEquiv

Depends on / 依赖: DFinsupp, DFinsupp.sigmaFinsetFunEquiv, DecidableEq, Encodable, Encodable.decidableEqOfEncodable, Encodable.fintypeEquivFin, Finset, decidableEqOfEncodable, fintypeEquivFin, ofEquiv, piCongrLeft, sigmaFinsetFunEquiv
-/
instance [Encodable ι] [forall i, Encodable (α i)] [forall i (x : α i), Decidable (x != 0)] :
    Encodable (Π₀ i, α i) :=
  letI : DecidableEq ι := Encodable.decidableEqOfEncodable _
  letI : forall s : Finset ι, Encodable (forall i : s, {x : α i // x != 0}) := fun _ =>
.ofEquiv _ .piCongrLeft' _ Encodable.fintypeEquivFin
  .ofEquiv _ DFinsupp.sigmaFinsetFunEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: ι] [forall i, Countable (α i)] : Countable (Π₀ i, α i)
  body: by
  classical
    let _ := Encodable.ofCountable ι
    let _ := fun i => Encodable.ofCountable (α i)
    infer_instance

中文:
实例 [Countable
  签名: ι] [对任意 i, Countable (α i)] : Countable (Π₀ i, α i)
  定义体: by
  classical
    let _ := Encodable.ofCountable ι
    let _ := fun i => Encodable.ofCountable (α i)
    infer_instance

Depends on / 依赖: Encodable, Encodable.ofCountable, classical, infer_instance, ofCountable
-/
instance [Countable ι] [forall i, Countable (α i)] : Countable (Π₀ i, α i) := by
  classical
    let _ := Encodable.ofCountable ι
    let _ := fun i => Encodable.ofCountable (α i)
    infer_instance
