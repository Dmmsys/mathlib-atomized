/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes
-/
module

public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.Valuation.Basic

/-!
# `multiplicity` of a prime in an integral domain as an additive valuation
-/

@[expose] public section

variable {R : Type*} [CommRing R] [IsDomain R] {p : R}

/--
Definition of `multiplicity_addValuation` / `multiplicity_addValuation` 的定义

English:
definition multiplicity_addValuation
  signature: (hp : Prime p)
  body: AddValuation.of (emultiplicity p) (emultiplicity_zero _)
    (emultiplicity_of_one_right hp.not_isUnit)
      (fun _ _ => min_le_emultiplicity_add) fun _ _ => emultiplicity_mul hp

@[simp]

中文:
定义 multiplicity_addValuation
  签名: (hp : Prime p)
  定义体: AddValuation.of (emultiplicity p) (emultiplicity_zero _)
    (emultiplicity_of_one_right hp.not_isUnit)
      (fun _ _ => min_le_emultiplicity_add) fun _ _ => emultiplicity_mul hp

@[simp]

Depends on / 依赖: AddValuation, AddValuation.of, emultiplicity, emultiplicity_mul, emultiplicity_of_one_right, emultiplicity_zero, hp.not_isUnit, min_le_emultiplicity_add, not_isUnit
-/
noncomputable def multiplicity_addValuation (hp : Prime p) : AddValuation R Nat∞ :=
  AddValuation.of (emultiplicity p) (emultiplicity_zero _)
    (emultiplicity_of_one_right hp.not_isUnit)
      (fun _ _ => min_le_emultiplicity_add) fun _ _ => emultiplicity_mul hp

@[simp]
/--
theorem `multiplicity_addValuation_apply` / 定理 `multiplicity_addValuation_apply`

English:
theorem multiplicity_addValuation_apply
  given: {hp : Prime p} {r : R}
  proof: rfl

中文:
定理 multiplicity_addValuation_apply
  条件: {hp : Prime p} {r : R}
  证明: rfl
-/
theorem multiplicity_addValuation_apply {hp : Prime p} {r : R} :
    multiplicity_addValuation hp r = emultiplicity p r :=
  rfl
