/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.Map

/-!
# Definitions about invariant measures

In this file we define typeclasses for measures invariant under (scalar) multiplication.

- `MeasureTheory.SMulInvariantMeasure M α μ`
  says that the measure `μ` is invariant under scalar multiplication by `c : M`;
- `MeasureTheory.VAddInvariantMeasure M α μ` is the additive version of this typeclass;
- `MeasureTheory.Measure.IsMulLeftInvariant μ`, `MeasureTheory.Measure.IsMulRightInvariant μ`
  say that the measure `μ` is invariant under multiplication on the left and on the right,
  respectively.
- `MeasureTheory.Measure.IsAddLeftInvariant μ`, `MeasureTheory.Measure.IsAddRightInvariant μ`
  are the additive versions of these typeclasses.

For basic facts about the first two typeclasses, see `Mathlib/MeasureTheory/Group/Action`.
For facts about left/right-invariant measures, see `Mathlib/MeasureTheory/Group/Measure`.

## Implementation Notes

The `smul`/`vadd` typeclasses and the left/right multiplication typeclasses
were defined by different people with different tastes,
so the former explicitly use measures of the preimages,
while the latter use `MeasureTheory.Measure.map`.

If the left/right multiplication is measurable
(which is the case in most if not all interesting examples),
these definitions are equivalent.

The definitions that use `MeasureTheory.Measure.map`
imply that the left (resp., right) multiplication is `AEMeasurable`.
-/

public section

assert_not_exists Module.Basis

namespace MeasureTheory

/--
Definition of `VAddInvariantMeasure` / `VAddInvariantMeasure` 的定义

English:
class VAddInvariantMeasure
  parameters: (M α : Type*) [VAdd M α] {_ : MeasurableSpace α} (μ : Measure α)
  axioms and operations (1):
    - measure_preimage_vadd : forall (c : M) ⦃s : Set α⦄, MeasurableSet s -> μ ((fun x => c +ᵥ x) ⁻¹' s) = μ s

中文:
类 向量加不变测度
  参数: (M α : 类型) [向量加法 M α] {_ : 可测空间 α} (μ : 测度 α)
  公理与运算 (1 个):
    - measure_preimage_vadd : 对任意 (c : M) ⦃s : 集合 α⦄, 可测集 s -> μ ((fun x => c +ᵥ x) ⁻¹' s) = μ s
-/
class VAddInvariantMeasure (M α : Type*) [VAdd M α] {_ : MeasurableSpace α} (μ : Measure α) :
  Prop where
  measure_preimage_vadd : forall (c : M) ⦃s : Set α⦄, MeasurableSet s -> μ ((fun x => c +ᵥ x) ⁻¹' s) = μ s

/-- A measure `μ : Measure α` is invariant under a multiplicative action of `M` on `α` if for any
measurable set `s : Set α` and `c : M`, the measure of its preimage under `fun x => c • x` is equal
to the measure of `s`. -/
@[to_additive, mk_iff smulInvariantMeasure_iff]
/--
Definition of `SMulInvariantMeasure` / `SMulInvariantMeasure` 的定义

English:
class SMulInvariantMeasure
  parameters: (M α : Type*) [SMul M α] {_ : MeasurableSpace α} (μ : Measure α)
  axioms and operations (1):
    - measure_preimage_smul : forall (c : M) ⦃s : Set α⦄, MeasurableSet s -> μ ((fun x => c • x) ⁻¹' s) = μ s

中文:
类 标量乘不变测度
  参数: (M α : 类型) [标量乘法 M α] {_ : 可测空间 α} (μ : 测度 α)
  公理与运算 (1 个):
    - measure_preimage_smul : 对任意 (c : M) ⦃s : 集合 α⦄, 可测集 s -> μ ((fun x => c • x) ⁻¹' s) = μ s
-/
class SMulInvariantMeasure (M α : Type*) [SMul M α] {_ : MeasurableSpace α} (μ : Measure α) :
  Prop where
  measure_preimage_smul : forall (c : M) ⦃s : Set α⦄, MeasurableSet s -> μ ((fun x => c • x) ⁻¹' s) = μ s

attribute [to_additive] smulInvariantMeasure_iff

namespace Measure

variable {G : Type*} [MeasurableSpace G]

/--
Definition of `IsAddLeftInvariant` / `IsAddLeftInvariant` 的定义

English:
class IsAddLeftInvariant
  parameters: [Add G] (μ : Measure G)
  axioms and operations (1):
    - map_add_left_eq_self : forall g : G, map (g + ·) μ = μ

中文:
类 是加法左不变
  参数: [加法 G] (μ : 测度 G)
  公理与运算 (1 个):
    - map_add_left_eq_self : 对任意 g : G, map (g + ·) μ = μ
-/
class IsAddLeftInvariant [Add G] (μ : Measure G) : Prop where
  map_add_left_eq_self : forall g : G, map (g + ·) μ = μ

/-- A measure `μ` on a measurable group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself. -/
@[to_additive existing]
/--
Definition of `IsMulLeftInvariant` / `IsMulLeftInvariant` 的定义

English:
class IsMulLeftInvariant
  parameters: [Mul G] (μ : Measure G)
  axioms and operations (1):
    - map_mul_left_eq_self : forall g : G, map (g * ·) μ = μ

中文:
类 是MulLeftInvariant
  参数: [乘法 G] (μ : 测度 G)
  公理与运算 (1 个):
    - map_mul_left_eq_self : 对任意 g : G, map (g * ·) μ = μ
-/
class IsMulLeftInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_left_eq_self : forall g : G, map (g * ·) μ = μ

/--
Definition of `IsAddRightInvariant` / `IsAddRightInvariant` 的定义

English:
class IsAddRightInvariant
  parameters: [Add G] (μ : Measure G)
  axioms and operations (1):
    - map_add_right_eq_self : forall g : G, map (· + g) μ = μ

中文:
类 是加法右不变
  参数: [加法 G] (μ : 测度 G)
  公理与运算 (1 个):
    - map_add_right_eq_self : 对任意 g : G, map (· + g) μ = μ
-/
class IsAddRightInvariant [Add G] (μ : Measure G) : Prop where
  map_add_right_eq_self : forall g : G, map (· + g) μ = μ

/-- A measure `μ` on a measurable group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself. -/
@[to_additive existing]
/--
Definition of `IsMulRightInvariant` / `IsMulRightInvariant` 的定义

English:
class IsMulRightInvariant
  parameters: [Mul G] (μ : Measure G)
  axioms and operations (1):
    - map_mul_right_eq_self : forall g : G, map (· * g) μ = μ

中文:
类 是MulRightInvariant
  参数: [乘法 G] (μ : 测度 G)
  公理与运算 (1 个):
    - map_mul_right_eq_self : 对任意 g : G, map (· * g) μ = μ
-/
class IsMulRightInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_right_eq_self : forall g : G, map (· * g) μ = μ

variable {μ : Measure G}

@[to_additive]
/--
Instance `IsMulLeftInvariant.smulInvariantMeasure` / 实例 `IsMulLeftInvariant.smulInvariantMeasure`

English:
instance IsMulLeftInvariant.smulInvariantMeasure
  signature: [Mul G] [IsMulLeftInvariant μ]
  body: ⟨fun _x _s hs => measure_preimage_of_map_eq_self (map_mul_left_eq_self _) hs.nullMeasurableSet⟩

@[to_additive]

中文:
实例 是MulLeftInvariant.smulInvariantMeasure
  签名: [乘法 G] [是MulLeftInvariant μ]
  定义体: ⟨fun _x _s hs => measure_preimage_of_map_eq_self (map_mul_left_eq_self _) hs.nullMeasurableSet⟩

@[to_additive]

Depends on / 依赖: hs.nullMeasurableSet, map_mul_left_eq_self, measure_preimage_of_map_eq_self, nullMeasurableSet
-/
instance IsMulLeftInvariant.smulInvariantMeasure [Mul G] [IsMulLeftInvariant μ] :
    SMulInvariantMeasure G G μ :=
  ⟨fun _x _s hs => measure_preimage_of_map_eq_self (map_mul_left_eq_self _) hs.nullMeasurableSet⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: G] (s
  body: ⟨fun ⟨x, _⟩ _ h => IsMulLeftInvariant.smulInvariantMeasure.1 x h⟩

@[to_additive]

中文:
实例 [幺半群
  签名: G] (s
  定义体: ⟨fun ⟨x, _⟩ _ h => IsMulLeftInvariant.smulInvariantMeasure.1 x h⟩

@[to_additive]

Depends on / 依赖: IsMulLeftInvariant, IsMulLeftInvariant.smulInvariantMeasure, smulInvariantMeasure
-/
instance [Monoid G] (s : Submonoid G) [IsMulLeftInvariant μ] :
    SMulInvariantMeasure {x // x in s} G μ :=
  ⟨fun ⟨x, _⟩ _ h => IsMulLeftInvariant.smulInvariantMeasure.1 x h⟩

@[to_additive]
/--
Instance `IsMulRightInvariant.toSMulInvariantMeasure_op` / 实例 `IsMulRightInvariant.toSMulInvariantMeasure_op`

English:
instance IsMulRightInvariant.toSMulInvariantMeasure_op
  signature: [Mul G] [μ.IsMulRightInvariant]
  body: ⟨fun _x _s hs => measure_preimage_of_map_eq_self (map_mul_right_eq_self _) hs.nullMeasurableSet⟩

中文:
实例 是MulRightInvariant.toSMulInvariantMeasure_op
  签名: [乘法 G] [μ.是MulRightInvariant]
  定义体: ⟨fun _x _s hs => measure_preimage_of_map_eq_self (map_mul_right_eq_self _) hs.nullMeasurableSet⟩

Depends on / 依赖: hs.nullMeasurableSet, map_mul_right_eq_self, measure_preimage_of_map_eq_self, nullMeasurableSet
-/
instance IsMulRightInvariant.toSMulInvariantMeasure_op [Mul G] [μ.IsMulRightInvariant] :
    SMulInvariantMeasure Gᵐᵒᵖ G μ :=
  ⟨fun _x _s hs => measure_preimage_of_map_eq_self (map_mul_right_eq_self _) hs.nullMeasurableSet⟩

end Measure

end MeasureTheory
