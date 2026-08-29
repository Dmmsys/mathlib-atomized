/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Init

/-!
# `ULift` and `PLift`
-/

public section

/--
theorem `ULift.down_injective` / 定理 `ULift.down_injective`

English:
theorem ULift.down_injective
  given: {α : Type*}
  statement: Function.Injective (@ULift.down α)

中文:
定理 ULift.down_injective
  条件: {α : 类型}
  结论: Function.Injective (@ULift.down α)
-/
theorem ULift.down_injective {α : Type*} : Function.Injective (@ULift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr

/--
theorem `ULift.down_inj` / 定理 `ULift.down_inj`

English:
theorem ULift.down_inj
  given: {α : Type*} {a b : ULift α}
  statement: a.down = b.down ↔ a = b
  proof: ⟨fun h => ULift.down_injective h, fun h => by rw [h]⟩

中文:
定理 ULift.down_inj
  条件: {α : 类型} {a b : ULift α}
  结论: a.down = b.down ↔ a = b
  证明: ⟨fun h => ULift.down_injective h, fun h => by rw [h]⟩
-/
@[simp] theorem ULift.down_inj {α : Type*} {a b : ULift α} : a.down = b.down ↔ a = b :=
  ⟨fun h => ULift.down_injective h, fun h => by rw [h]⟩

variable {α : Sort*}

/--
theorem `PLift.down_injective` / 定理 `PLift.down_injective`

English:
theorem PLift.down_injective
  statement: Function.Injective (@PLift.down α)

中文:
定理 PLift.down_injective
  结论: Function.Injective (@PLift.down α)
-/
theorem PLift.down_injective : Function.Injective (@PLift.down α)
  | ⟨a⟩, ⟨b⟩, _ => by congr

/--
theorem `PLift.down_inj` / 定理 `PLift.down_inj`

English:
theorem PLift.down_inj
  given: {a b : PLift α}
  statement: a.down = b.down ↔ a = b
  proof: ⟨fun h => PLift.down_injective h, fun h => by rw [h]⟩

中文:
定理 PLift.down_inj
  条件: {a b : PLift α}
  结论: a.down = b.down ↔ a = b
  证明: ⟨fun h => PLift.down_injective h, fun h => by rw [h]⟩
-/
@[simp] theorem PLift.down_inj {a b : PLift α} : a.down = b.down ↔ a = b :=
  ⟨fun h => PLift.down_injective h, fun h => by rw [h]⟩
