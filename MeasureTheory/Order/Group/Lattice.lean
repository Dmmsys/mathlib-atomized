/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurability results on groups with a lattice structure.

## Tags

measurable function, group, lattice operation
-/

public section

variable {α β : Type*} [Lattice α] [Group α] [MeasurableSpace α]
  [MeasurableSpace β] {f : β -> α}

@[to_additive]
/--
theorem `measurable_oneLePart` / 定理 `measurable_oneLePart`

English:
theorem measurable_oneLePart
  given: [MeasurableSup α]
  statement: Measurable (oneLePart : α -> α)
  proof: measurable_sup_const _

@[to_additive (attr := fun_prop)]

中文:
定理 measurable_oneLePart
  条件: [MeasurableSup α]
  结论: Measurable (oneLePart : α -> α)
  证明: measurable_sup_const _

@[to_additive (attr := fun_prop)]

Depends on / 依赖: measurable_sup_const
-/
theorem measurable_oneLePart [MeasurableSup α] : Measurable (oneLePart : α -> α) :=
  measurable_sup_const _

@[to_additive (attr := fun_prop)]
/--
theorem `Measurable.oneLePart` / 定理 `Measurable.oneLePart`

English:
theorem Measurable.oneLePart
  given: [MeasurableSup α] (hf : Measurable f)
  proof: measurable_oneLePart.comp hf

@[to_additive (attr := fun_prop)]

中文:
定理 Measurable.oneLePart
  条件: [MeasurableSup α] (hf : Measurable f)
  证明: measurable_oneLePart.comp hf

@[to_additive (attr := fun_prop)]
-/
protected theorem Measurable.oneLePart [MeasurableSup α] (hf : Measurable f) :
    Measurable fun x => oneLePart (f x) :=
  measurable_oneLePart.comp hf

@[to_additive (attr := fun_prop)]
/--
theorem `AEMeasurable.oneLePart` / 定理 `AEMeasurable.oneLePart`

English:
theorem AEMeasurable.oneLePart
  statement: {μ : MeasureTheory.Measure β} [MeasurableSup α]
  proof: hf.sup_const 1

中文:
定理 AEMeasurable.oneLePart
  结论: {μ : MeasureTheory.Measure β} [MeasurableSup α]
  证明: hf.sup_const 1
-/
protected theorem AEMeasurable.oneLePart {μ : MeasureTheory.Measure β} [MeasurableSup α]
    (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => oneLePart (f x)) μ :=
  hf.sup_const 1

variable [MeasurableInv α]

@[to_additive]
/--
theorem `measurable_leOnePart` / 定理 `measurable_leOnePart`

English:
theorem measurable_leOnePart
  given: [MeasurableSup α]
  statement: Measurable (leOnePart : α -> α)
  proof: (measurable_sup_const _).comp measurable_inv

@[to_additive (attr := fun_prop)]

中文:
定理 measurable_leOnePart
  条件: [MeasurableSup α]
  结论: Measurable (leOnePart : α -> α)
  证明: (measurable_sup_const _).comp measurable_inv

@[to_additive (attr := fun_prop)]

Depends on / 依赖: measurable_inv, measurable_sup_const
-/
theorem measurable_leOnePart [MeasurableSup α] : Measurable (leOnePart : α -> α) :=
  (measurable_sup_const _).comp measurable_inv

@[to_additive (attr := fun_prop)]
/--
theorem `Measurable.leOnePart` / 定理 `Measurable.leOnePart`

English:
theorem Measurable.leOnePart
  given: [MeasurableSup α] (hf : Measurable f)
  proof: measurable_leOnePart.comp hf

@[to_additive (attr := fun_prop)]

中文:
定理 Measurable.leOnePart
  条件: [MeasurableSup α] (hf : Measurable f)
  证明: measurable_leOnePart.comp hf

@[to_additive (attr := fun_prop)]
-/
protected theorem Measurable.leOnePart [MeasurableSup α] (hf : Measurable f) :
    Measurable fun x => leOnePart (f x) :=
  measurable_leOnePart.comp hf

@[to_additive (attr := fun_prop)]
/--
theorem `AEMeasurable.leOnePart` / 定理 `AEMeasurable.leOnePart`

English:
theorem AEMeasurable.leOnePart
  statement: {μ : MeasureTheory.Measure β} [MeasurableSup α]
  proof: hf.inv.sup_const 1

中文:
定理 AEMeasurable.leOnePart
  结论: {μ : MeasureTheory.Measure β} [MeasurableSup α]
  证明: hf.inv.sup_const 1
-/
protected theorem AEMeasurable.leOnePart {μ : MeasureTheory.Measure β} [MeasurableSup α]
    (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => leOnePart (f x)) μ :=
  hf.inv.sup_const 1

variable [MeasurableSup₂ α]

@[to_additive]
/--
theorem `measurable_mabs` / 定理 `measurable_mabs`

English:
theorem measurable_mabs
  statement: Measurable (mabs : α -> α)
  proof: measurable_id'.sup measurable_inv

@[to_additive (attr := fun_prop)]

中文:
定理 measurable_mabs
  结论: Measurable (mabs : α -> α)
  证明: measurable_id'.sup measurable_inv

@[to_additive (attr := fun_prop)]

Depends on / 依赖: measurable_id, measurable_inv
-/
theorem measurable_mabs : Measurable (mabs : α -> α) :=
  measurable_id'.sup measurable_inv

@[to_additive (attr := fun_prop)]
/--
theorem `Measurable.mabs` / 定理 `Measurable.mabs`

English:
theorem Measurable.mabs
  given: (hf : Measurable f)
  statement: Measurable fun x => mabs (f x)
  proof: measurable_mabs.comp hf

@[to_additive (attr := fun_prop)]

中文:
定理 Measurable.mabs
  条件: (hf : Measurable f)
  结论: Measurable fun x => mabs (f x)
  证明: measurable_mabs.comp hf

@[to_additive (attr := fun_prop)]
-/
protected theorem Measurable.mabs (hf : Measurable f) : Measurable fun x => mabs (f x) :=
  measurable_mabs.comp hf

@[to_additive (attr := fun_prop)]
/--
theorem `AEMeasurable.mabs` / 定理 `AEMeasurable.mabs`

English:
theorem AEMeasurable.mabs
  given: {μ : MeasureTheory.Measure β} (hf : AEMeasurable f μ)
  proof: measurable_mabs.comp_aemeasurable hf

中文:
定理 AEMeasurable.mabs
  条件: {μ : MeasureTheory.Measure β} (hf : AEMeasurable f μ)
  证明: measurable_mabs.comp_aemeasurable hf
-/
protected theorem AEMeasurable.mabs {μ : MeasureTheory.Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => mabs (f x)) μ :=
  measurable_mabs.comp_aemeasurable hf
