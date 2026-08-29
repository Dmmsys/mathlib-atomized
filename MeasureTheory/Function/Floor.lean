/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of `⌊x⌋` etc

In this file we prove that `Int.floor`, `Int.ceil`, `Int.fract`, `Nat.floor`, and `Nat.ceil` are
measurable under some assumptions on the (semi)ring.
-/

public section


open Set

section FloorRing

variable {α R : Type*} [MeasurableSpace α] [Ring R] [LinearOrder R] [FloorRing R]
  [TopologicalSpace R] [OrderTopology R] [MeasurableSpace R]

/--
theorem `Int.measurable_floor` / 定理 `Int.measurable_floor`

English:
theorem Int.measurable_floor
  given: [OpensMeasurableSpace R]
  statement: Measurable (Int.floor : R -> Int)
  proof: measurable_to_countable fun x => by
    simpa only [Int.preimage_floor_singleton] using measurableSet_Ico

@[fun_prop]

中文:
定理 Int.measurable_floor
  条件: [OpensMeasurableSpace R]
  结论: Measurable (整数.floor : R -> 整数)
  证明: measurable_to_countable fun x => by
    simpa only [Int.preimage_floor_singleton] using measurableSet_Ico

@[fun_prop]

Depends on / 依赖: Int.preimage_floor_singleton, measurableSet_Ico, measurable_to_countable, preimage_floor_singleton
-/
theorem Int.measurable_floor [OpensMeasurableSpace R] : Measurable (Int.floor : R -> Int) :=
  measurable_to_countable fun x => by
    simpa only [Int.preimage_floor_singleton] using measurableSet_Ico

@[fun_prop]
/--
theorem `Measurable.floor` / 定理 `Measurable.floor`

English:
theorem Measurable.floor
  given: [OpensMeasurableSpace R] {f : α -> R} (hf : Measurable f)
  proof: Int.measurable_floor.comp hf

中文:
定理 Measurable.floor
  条件: [OpensMeasurableSpace R] {f : α -> R} (hf : Measurable f)
  证明: Int.measurable_floor.comp hf

Depends on / 依赖: Int.measurable_floor.comp, measurable_floor
-/
theorem Measurable.floor [OpensMeasurableSpace R] {f : α -> R} (hf : Measurable f) :
    Measurable fun x => ⌊f x⌋ :=
  Int.measurable_floor.comp hf

/--
theorem `Int.measurable_ceil` / 定理 `Int.measurable_ceil`

English:
theorem Int.measurable_ceil
  given: [OpensMeasurableSpace R]
  statement: Measurable (Int.ceil : R -> Int)
  proof: measurable_to_countable fun x => by
    simpa only [Int.preimage_ceil_singleton] using measurableSet_Ioc

@[fun_prop]

中文:
定理 Int.measurable_ceil
  条件: [OpensMeasurableSpace R]
  结论: Measurable (整数.ceil : R -> 整数)
  证明: measurable_to_countable fun x => by
    simpa only [Int.preimage_ceil_singleton] using measurableSet_Ioc

@[fun_prop]

Depends on / 依赖: Int.preimage_ceil_singleton, measurableSet_Ioc, measurable_to_countable, preimage_ceil_singleton
-/
theorem Int.measurable_ceil [OpensMeasurableSpace R] : Measurable (Int.ceil : R -> Int) :=
  measurable_to_countable fun x => by
    simpa only [Int.preimage_ceil_singleton] using measurableSet_Ioc

@[fun_prop]
/--
theorem `Measurable.ceil` / 定理 `Measurable.ceil`

English:
theorem Measurable.ceil
  given: [OpensMeasurableSpace R] {f : α -> R} (hf : Measurable f)
  proof: Int.measurable_ceil.comp hf

中文:
定理 Measurable.ceil
  条件: [OpensMeasurableSpace R] {f : α -> R} (hf : Measurable f)
  证明: Int.measurable_ceil.comp hf

Depends on / 依赖: Int.measurable_ceil.comp, measurable_ceil
-/
theorem Measurable.ceil [OpensMeasurableSpace R] {f : α -> R} (hf : Measurable f) :
    Measurable fun x => ⌈f x⌉ :=
  Int.measurable_ceil.comp hf

/--
theorem `measurable_fract` / 定理 `measurable_fract`

English:
theorem measurable_fract
  given: [IsStrictOrderedRing R] [BorelSpace R]
  proof: by
  intro s hs
  rw [Int.preimage_fract]
  exact MeasurableSet.iUnion fun z => measurable_id.sub_const _ (hs.inter measurableSet_Ico)

@[fun_prop]

中文:
定理 measurable_fract
  条件: [IsStrictOrderedRing R] [BorelSpace R]
  证明: by
  intro s hs
  rw [Int.preimage_fract]
  exact MeasurableSet.iUnion fun z => measurable_id.sub_const _ (hs.inter measurableSet_Ico)

@[fun_prop]

Depends on / 依赖: Int.preimage_fract, MeasurableSet, MeasurableSet.iUnion, hs.inter, iUnion, measurableSet_Ico, measurable_id, measurable_id.sub_const, preimage_fract, sub_const
-/
theorem measurable_fract [IsStrictOrderedRing R] [BorelSpace R] :
    Measurable (Int.fract : R -> R) := by
  intro s hs
  rw [Int.preimage_fract]
  exact MeasurableSet.iUnion fun z => measurable_id.sub_const _ (hs.inter measurableSet_Ico)

@[fun_prop]
/--
theorem `Measurable.fract` / 定理 `Measurable.fract`

English:
theorem Measurable.fract
  given: [IsStrictOrderedRing R] [BorelSpace R] {f : α -> R} (hf : Measurable f)
  proof: measurable_fract.comp hf

中文:
定理 Measurable.fract
  条件: [IsStrictOrderedRing R] [BorelSpace R] {f : α -> R} (hf : Measurable f)
  证明: measurable_fract.comp hf

Depends on / 依赖: measurable_fract, measurable_fract.comp
-/
theorem Measurable.fract [IsStrictOrderedRing R] [BorelSpace R] {f : α -> R} (hf : Measurable f) :
    Measurable fun x => Int.fract (f x) :=
  measurable_fract.comp hf

/--
theorem `MeasurableSet.image_fract` / 定理 `MeasurableSet.image_fract`

English:
theorem MeasurableSet.image_fract
  statement: [IsStrictOrderedRing R] [BorelSpace R]
  proof: by
  simp only [Int.image_fract, sub_eq_add_neg, image_add_right']
  exact MeasurableSet.iUnion fun m => (measurable_add_const _ hs).inter measurableSet_Ico

中文:
定理 MeasurableSet.image_fract
  结论: [IsStrictOrderedRing R] [BorelSpace R]
  证明: by
  simp only [Int.image_fract, sub_eq_add_neg, image_add_right']
  exact MeasurableSet.iUnion fun m => (measurable_add_const _ hs).inter measurableSet_Ico

Depends on / 依赖: Int.image_fract, MeasurableSet, MeasurableSet.iUnion, iUnion, image_add_right, image_fract, measurableSet_Ico, measurable_add_const, sub_eq_add_neg
-/
theorem MeasurableSet.image_fract [IsStrictOrderedRing R] [BorelSpace R]
    {s : Set R} (hs : MeasurableSet s) :
    MeasurableSet (Int.fract '' s) := by
  simp only [Int.image_fract, sub_eq_add_neg, image_add_right']
  exact MeasurableSet.iUnion fun m => (measurable_add_const _ hs).inter measurableSet_Ico

end FloorRing

section FloorSemiring

variable {α R : Type*} [MeasurableSpace α] [Semiring R] [LinearOrder R] [FloorSemiring R]
  [TopologicalSpace R] [OrderTopology R] [MeasurableSpace R] [OpensMeasurableSpace R] {f : α -> R}

/--
theorem `Nat.measurable_floor` / 定理 `Nat.measurable_floor`

English:
theorem Nat.measurable_floor
  given: [IsStrictOrderedRing R]
  statement: Measurable (Nat.floor : R -> Nat)
  proof: measurable_to_countable fun n => by
    rcases eq_or_ne ⌊n⌋₊ 0 with h | h <;> simp [h, Nat.preimage_floor_of_ne_zero, -floor_eq_zero]

@[fun_prop]

中文:
定理 Nat.measurable_floor
  条件: [IsStrictOrderedRing R]
  结论: Measurable (自然数.floor : R -> 自然数)
  证明: measurable_to_countable fun n => by
    rcases eq_or_ne ⌊n⌋₊ 0 with h | h <;> simp [h, Nat.preimage_floor_of_ne_zero, -floor_eq_zero]

@[fun_prop]

Depends on / 依赖: Nat.preimage_floor_of_ne_zero, eq_or_ne, floor_eq_zero, measurable_to_countable, preimage_floor_of_ne_zero
-/
theorem Nat.measurable_floor [IsStrictOrderedRing R] : Measurable (Nat.floor : R -> Nat) :=
  measurable_to_countable fun n => by
    rcases eq_or_ne ⌊n⌋₊ 0 with h | h <;> simp [h, Nat.preimage_floor_of_ne_zero, -floor_eq_zero]

@[fun_prop]
/--
theorem `Measurable.nat_floor` / 定理 `Measurable.nat_floor`

English:
theorem Measurable.nat_floor
  given: [IsStrictOrderedRing R] (hf : Measurable f)
  proof: Nat.measurable_floor.comp hf

中文:
定理 Measurable.nat_floor
  条件: [IsStrictOrderedRing R] (hf : Measurable f)
  证明: Nat.measurable_floor.comp hf

Depends on / 依赖: Nat.measurable_floor.comp, measurable_floor
-/
theorem Measurable.nat_floor [IsStrictOrderedRing R] (hf : Measurable f) :
    Measurable fun x => ⌊f x⌋₊ :=
  Nat.measurable_floor.comp hf

/--
theorem `Nat.measurable_ceil` / 定理 `Nat.measurable_ceil`

English:
theorem Nat.measurable_ceil
  statement: Measurable (Nat.ceil : R -> Nat)
  proof: measurable_to_countable fun n => by
    rcases eq_or_ne ⌈n⌉₊ 0 with h | h <;> simp_all [Nat.preimage_ceil_of_ne_zero, -ceil_eq_zero]

@[fun_prop]

中文:
定理 Nat.measurable_ceil
  结论: Measurable (自然数.ceil : R -> 自然数)
  证明: measurable_to_countable fun n => by
    rcases eq_or_ne ⌈n⌉₊ 0 with h | h <;> simp_all [Nat.preimage_ceil_of_ne_zero, -ceil_eq_zero]

@[fun_prop]

Depends on / 依赖: Nat.preimage_ceil_of_ne_zero, ceil_eq_zero, eq_or_ne, measurable_to_countable, preimage_ceil_of_ne_zero
-/
theorem Nat.measurable_ceil : Measurable (Nat.ceil : R -> Nat) :=
  measurable_to_countable fun n => by
    rcases eq_or_ne ⌈n⌉₊ 0 with h | h <;> simp_all [Nat.preimage_ceil_of_ne_zero, -ceil_eq_zero]

@[fun_prop]
/--
theorem `Measurable.nat_ceil` / 定理 `Measurable.nat_ceil`

English:
theorem Measurable.nat_ceil
  given: (hf : Measurable f)
  statement: Measurable fun x => ⌈f x⌉₊
  proof: Nat.measurable_ceil.comp hf

中文:
定理 Measurable.nat_ceil
  条件: (hf : Measurable f)
  结论: Measurable fun x => ⌈f x⌉₊
  证明: Nat.measurable_ceil.comp hf

Depends on / 依赖: Nat.measurable_ceil.comp, measurable_ceil
-/
theorem Measurable.nat_ceil (hf : Measurable f) : Measurable fun x => ⌈f x⌉₊ :=
  Nat.measurable_ceil.comp hf

end FloorSemiring
