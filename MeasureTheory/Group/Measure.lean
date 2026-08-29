/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.Complement
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Group.Pointwise
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.ContinuousMap.CocompactMap

/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: measures that are left or right invariant w.r.t. multiplication.
* We define the measure `μ.inv : A ↦ μ(A⁻¹)` and show that it is right invariant iff
  `μ` is left invariant.
* We define a class `IsHaarMeasure μ`, requiring that the measure `μ` is left-invariant, finite
  on compact sets, and positive on open sets.

We also give analogues of all these notions in the additive world.
-/

@[expose] public section


noncomputable section

open scoped NNReal ENNReal Pointwise Topology

open Inv Set Function MeasureTheory.Measure Filter

variable {G H : Type*} [MeasurableSpace G] [MeasurableSpace H]

namespace MeasureTheory

section Mul

variable [Mul G] {μ : Measure G}

@[to_additive]
/--
theorem `map_mul_left_eq_self` / 定理 `map_mul_left_eq_self`

English:
theorem map_mul_left_eq_self
  given: (μ : Measure G) [IsMulLeftInvariant μ] (g : G)
  proof: IsMulLeftInvariant.map_mul_left_eq_self g

@[to_additive]

中文:
定理 map_mul_left_eq_self
  条件: (μ : 测度 G) [是MulLeftInvariant μ] (g : G)
  证明: IsMulLeftInvariant.map_mul_left_eq_self g

@[to_additive]

Depends on / 依赖: AlgEquivClass, AlgEquivClass.toAlgEquiv, IsMulLeftInvariant, IsMulLeftInvariant.map_mul_left_eq_self, P.map, RingEquivClass, RingEquivClass.toRingEquiv, _comap_eq, inertiaDeg, map_comap_of_equiv, map_mul_left_eq_self, p.inertiaDeg, toAlgEquiv, toRingEquiv
-/
theorem map_mul_left_eq_self (μ : Measure G) [IsMulLeftInvariant μ] (g : G) :
    map (g * ·) μ = μ :=
  IsMulLeftInvariant.map_mul_left_eq_self g

@[to_additive]
/--
theorem `map_mul_right_eq_self` / 定理 `map_mul_right_eq_self`

English:
theorem map_mul_right_eq_self
  given: (μ : Measure G) [IsMulRightInvariant μ] (g : G)
  statement: map (· * g) μ = μ
  proof: IsMulRightInvariant.map_mul_right_eq_self g

@[to_additive MeasureTheory.isAddLeftInvariant_smul]

中文:
定理 map_mul_right_eq_self
  条件: (μ : 测度 G) [是MulRightInvariant μ] (g : G)
  结论: map (· * g) μ = μ
  证明: IsMulRightInvariant.map_mul_right_eq_self g

@[to_additive MeasureTheory.isAddLeftInvariant_smul]

Depends on / 依赖: Algebra, Algebra.finrank_eq_of_equiv_equiv, IsMulRightInvariant, IsMulRightInvariant.map_mul_right_eq_self, RingEquiv, RingEquiv.quotientBot, dif_pos, eq_bot_of_liesOver_bot, finrank_eq_of_equiv_equiv, inertiaDeg, map_mul_right_eq_self, over_def, quotEquivOfEq, quotientBot, replace
-/
theorem map_mul_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ :=
  IsMulRightInvariant.map_mul_right_eq_self g

@[to_additive MeasureTheory.isAddLeftInvariant_smul]
/--
Instance `isMulLeftInvariant_smul` / 实例 `isMulLeftInvariant_smul`

English:
instance isMulLeftInvariant_smul
  signature: [IsMulLeftInvariant μ] (c : Real>=0∞)
  body: ⟨fun g => by rw [Measure.map_smul, map_mul_left_eq_self]⟩

@[to_additive MeasureTheory.isAddRightInvariant_smul]

中文:
实例 isMulLeftInvariant_smul
  签名: [是MulLeftInvariant μ] (c : 实数>=0∞)
  定义体: ⟨fun g => by rw [Measure.map_smul, map_mul_left_eq_self]⟩

@[to_additive MeasureTheory.isAddRightInvariant_smul]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.of_algebraMap_eq, LiesOver, LiesOver.trans, Measure, Measure.map_smul, Q.LiesOver, Quotient, Submodule, Submodule.Quotient.quot_mk_eq_mk, _algebraMap, algebraMap_apply, finrank_top_le_finrank_of_isScalarTower, inertiaDeg, map_mul_left_eq_self, map_smul, of_algebraMap_eq, quot_mk_eq_mk
-/
instance isMulLeftInvariant_smul [IsMulLeftInvariant μ] (c : Real>=0∞) : IsMulLeftInvariant (c • μ) :=
  ⟨fun g => by rw [Measure.map_smul, map_mul_left_eq_self]⟩

@[to_additive MeasureTheory.isAddRightInvariant_smul]
/--
Instance `isMulRightInvariant_smul` / 实例 `isMulRightInvariant_smul`

English:
instance isMulRightInvariant_smul
  signature: [IsMulRightInvariant μ] (c : Real>=0∞)
  body: ⟨fun g => by rw [Measure.map_smul, map_mul_right_eq_self]⟩

@[to_additive MeasureTheory.isAddLeftInvariant_smul_nnreal]

中文:
实例 isMulRightInvariant_smul
  签名: [是MulRightInvariant μ] (c : 实数>=0∞)
  定义体: ⟨fun g => by rw [Measure.map_smul, map_mul_right_eq_self]⟩

@[to_additive MeasureTheory.isAddLeftInvariant_smul_nnreal]

Depends on / 依赖: Measure, Measure.map_smul, map_mul_right_eq_self, map_smul
-/
instance isMulRightInvariant_smul [IsMulRightInvariant μ] (c : Real>=0∞) :
    IsMulRightInvariant (c • μ) :=
  ⟨fun g => by rw [Measure.map_smul, map_mul_right_eq_self]⟩

@[to_additive MeasureTheory.isAddLeftInvariant_smul_nnreal]
/--
Instance `isMulLeftInvariant_smul_nnreal` / 实例 `isMulLeftInvariant_smul_nnreal`

English:
instance isMulLeftInvariant_smul_nnreal
  signature: [IsMulLeftInvariant μ] (c : Real>=0)
  body: MeasureTheory.isMulLeftInvariant_smul (c : Real>=0∞)

@[to_additive MeasureTheory.isAddRightInvariant_smul_nnreal]

中文:
实例 isMulLeftInvariant_smul_nnreal
  签名: [是MulLeftInvariant μ] (c : 实数>=0)
  定义体: MeasureTheory.isMulLeftInvariant_smul (c : Real>=0∞)

@[to_additive MeasureTheory.isAddRightInvariant_smul_nnreal]

Depends on / 依赖: MeasureTheory, MeasureTheory.isMulLeftInvariant_smul, isMulLeftInvariant_smul
-/
instance isMulLeftInvariant_smul_nnreal [IsMulLeftInvariant μ] (c : Real>=0) :
    IsMulLeftInvariant (c • μ) :=
  MeasureTheory.isMulLeftInvariant_smul (c : Real>=0∞)

@[to_additive MeasureTheory.isAddRightInvariant_smul_nnreal]
/--
Instance `isMulRightInvariant_smul_nnreal` / 实例 `isMulRightInvariant_smul_nnreal`

English:
instance isMulRightInvariant_smul_nnreal
  signature: [IsMulRightInvariant μ] (c : Real>=0)
  body: MeasureTheory.isMulRightInvariant_smul (c : Real>=0∞)

中文:
实例 isMulRightInvariant_smul_nnreal
  签名: [是MulRightInvariant μ] (c : 实数>=0)
  定义体: MeasureTheory.isMulRightInvariant_smul (c : Real>=0∞)

Depends on / 依赖: MeasureTheory, MeasureTheory.isMulRightInvariant_smul, Nat.prime_iff_prime_int.mp, absNorm_eq_pow_inertiaDeg, isMulRightInvariant_smul, prime_iff_prime_int
-/
instance isMulRightInvariant_smul_nnreal [IsMulRightInvariant μ] (c : Real>=0) :
    IsMulRightInvariant (c • μ) :=
  MeasureTheory.isMulRightInvariant_smul (c : Real>=0∞)

section MeasurableMul

variable [MeasurableMul G]

@[to_additive]
/--
theorem `measurePreserving_mul_left` / 定理 `measurePreserving_mul_left`

English:
theorem measurePreserving_mul_left
  given: (μ : Measure G) [IsMulLeftInvariant μ] (g : G)
  proof: ⟨measurable_const_mul g, map_mul_left_eq_self μ g⟩

@[to_additive]

中文:
定理 measurePreserving_mul_left
  条件: (μ : 测度 G) [是MulLeftInvariant μ] (g : G)
  证明: ⟨measurable_const_mul g, map_mul_left_eq_self μ g⟩

@[to_additive]

Depends on / 依赖: Algebra, I.over_def, Ideal.Quotient.algebraQuotientOfLEComap, IsScalarTower, IsScalarTower.of_algebraMap_eq, LiesOver, LiesOver.trans, P.over_def, Quotient, algebraQuotientOfLEComap, dif_pos, inertiaDeg, map_mul_left_eq_self, measurable_const_mul, of_algebraMap_eq, over_def
-/
theorem measurePreserving_mul_left (μ : Measure G) [IsMulLeftInvariant μ] (g : G) :
    MeasurePreserving (g * ·) μ μ :=
  ⟨measurable_const_mul g, map_mul_left_eq_self μ g⟩

@[to_additive]
/--
theorem `MeasurePreserving.mul_left` / 定理 `MeasurePreserving.mul_left`

English:
theorem MeasurePreserving.mul_left
  statement: (μ : Measure G) [IsMulLeftInvariant μ] (g : G) {X : Type*}
  proof: (measurePreserving_mul_left μ g).comp hf

@[to_additive]

中文:
定理 保测.mul_left
  结论: (μ : 测度 G) [是MulLeftInvariant μ] (g : G) {X : 类型}
  证明: (measurePreserving_mul_left μ g).comp hf

@[to_additive]

Depends on / 依赖: measurePreserving_mul_left
-/
theorem MeasurePreserving.mul_left (μ : Measure G) [IsMulLeftInvariant μ] (g : G) {X : Type*}
    [MeasurableSpace X] {μ' : Measure X} {f : X -> G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => g * f x) μ' μ :=
  (measurePreserving_mul_left μ g).comp hf

@[to_additive]
/--
theorem `measurePreserving_mul_right` / 定理 `measurePreserving_mul_right`

English:
theorem measurePreserving_mul_right
  given: (μ : Measure G) [IsMulRightInvariant μ] (g : G)
  proof: ⟨measurable_mul_const g, map_mul_right_eq_self μ g⟩

@[to_additive]

中文:
定理 measurePreserving_mul_right
  条件: (μ : 测度 G) [是MulRightInvariant μ] (g : G)
  证明: ⟨measurable_mul_const g, map_mul_right_eq_self μ g⟩

@[to_additive]

Depends on / 依赖: Nat.sSup_def, convert, map_mul_right_eq_self, measurable_mul_const, sSup_def
-/
theorem measurePreserving_mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) :
    MeasurePreserving (· * g) μ μ :=
  ⟨measurable_mul_const g, map_mul_right_eq_self μ g⟩

@[to_additive]
/--
theorem `MeasurePreserving.mul_right` / 定理 `MeasurePreserving.mul_right`

English:
theorem MeasurePreserving.mul_right
  statement: (μ : Measure G) [IsMulRightInvariant μ] (g : G) {X : Type*}
  proof: (measurePreserving_mul_right μ g).comp hf

@[to_additive]

中文:
定理 保测.mul_right
  结论: (μ : 测度 G) [是MulRightInvariant μ] (g : G) {X : 类型}
  证明: (measurePreserving_mul_right μ g).comp hf

@[to_additive]

Depends on / 依赖: dif_neg, measurePreserving_mul_right
-/
theorem MeasurePreserving.mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) {X : Type*}
    [MeasurableSpace X] {μ' : Measure X} {f : X -> G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => f x * g) μ' μ :=
  (measurePreserving_mul_right μ g).comp hf

@[to_additive]
/--
Instance `Subgroup.smulInvariantMeasure` / 实例 `Subgroup.smulInvariantMeasure`

English:
instance Subgroup.smulInvariantMeasure
  signature: {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
  body: ⟨fun y s hs => by convert! SMulInvariantMeasure.measure_preimage_smul (μ := μ) (y : G) hs⟩

中文:
实例 子群.smulInvariantMeasure
  签名: {G α : 类型} [群 G] [乘法作用 G α] [可测空间 α]
  定义体: ⟨fun y s hs => by convert! SMulInvariantMeasure.measure_preimage_smul (μ := μ) (y : G) hs⟩

Depends on / 依赖: Ideal.pow_le_pow_right, Nat.find, Nat.find_min, Nat.find_spec, SMulInvariantMeasure, SMulInvariantMeasure.measure_preimage_smul, _eq_find, classical, convert, find_min, find_spec, h.not_ge, hk.trans, le_antisymm, le_of_not_gt, measure_preimage_smul, not_ge, pow_le_pow_right, ramificationIdx
-/
instance Subgroup.smulInvariantMeasure {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    {μ : Measure α} [SMulInvariantMeasure G α μ] (H : Subgroup G) : SMulInvariantMeasure H α μ :=
  ⟨fun y s hs => by convert! SMulInvariantMeasure.measure_preimage_smul (μ := μ) (y : G) hs⟩

/-- An alternative way to prove that `μ` is left invariant under multiplication. -/
@[to_additive /-- An alternative way to prove that `μ` is left invariant under addition. -/]
/--
theorem `forall_measure_preimage_mul_iff` / 定理 `forall_measure_preimage_mul_iff`

English:
theorem forall_measure_preimage_mul_iff
  given: (μ : Measure G)
  proof: by
  trans forall g, map (g * ·) μ = μ
  · simp_rw [Measure.ext_iff]
    refine forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => ?_
    rw [map_apply (measurable_const_mul g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

中文:
定理 对任意_measure_preimage_mul_iff
  条件: (μ : 测度 G)
  证明: by
  trans forall g, map (g * ·) μ = μ
  · simp_rw [Measure.ext_iff]
    refine forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => ?_
    rw [map_apply (measurable_const_mul g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

Depends on / 依赖: Ideal.pow_le_pow_right, Measure, Measure.ext_iff, Nat.find_min, Nat.lt_succ_iff, _eq_find, classical, ext_iff, find_min, forall_congr, hk.trans, le_of_not_gt, lt_succ_iff, map_apply, measurable_const_mul, pow_le_pow_right, ramificationIdx, simp_rw
-/
theorem forall_measure_preimage_mul_iff (μ : Measure G) :
    (forall (g : G) (A : Set G), MeasurableSet A -> μ ((fun h => g * h) ⁻¹' A) = μ A) ↔
      IsMulLeftInvariant μ := by
  trans forall g, map (g * ·) μ = μ
  · simp_rw [Measure.ext_iff]
    refine forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => ?_
    rw [map_apply (measurable_const_mul g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

/-- An alternative way to prove that `μ` is right invariant under multiplication. -/
@[to_additive /-- An alternative way to prove that `μ` is right invariant under addition. -/]
/--
theorem `forall_measure_preimage_mul_right_iff` / 定理 `forall_measure_preimage_mul_right_iff`

English:
theorem forall_measure_preimage_mul_right_iff
  given: (μ : Measure G)
  proof: by
  trans forall g, map (· * g) μ = μ
  · simp_rw [Measure.ext_iff]
    refine forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => ?_
    rw [map_apply (measurable_mul_const g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

@[to_additive]

中文:
定理 对任意_measure_preimage_mul_right_iff
  条件: (μ : 测度 G)
  证明: by
  trans forall g, map (· * g) μ = μ
  · simp_rw [Measure.ext_iff]
    refine forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => ?_
    rw [map_apply (measurable_mul_const g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

@[to_additive]

Depends on / 依赖: Measure, Measure.ext_iff, dif_neg, ext_iff, forall_congr, lt_succ_self, map_apply, measurable_mul_const, n.lt_succ_self.not_ge, not_exists, not_exists.mpr, not_ge, simp_rw
-/
theorem forall_measure_preimage_mul_right_iff (μ : Measure G) :
    (forall (g : G) (A : Set G), MeasurableSet A -> μ ((fun h => h * g) ⁻¹' A) = μ A) ↔
      IsMulRightInvariant μ := by
  trans forall g, map (· * g) μ = μ
  · simp_rw [Measure.ext_iff]
    refine forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => ?_
    rw [map_apply (measurable_mul_const g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

@[to_additive]
/--
Instance `Measure.prod.instIsMulLeftInvariant` / 实例 `Measure.prod.instIsMulLeftInvariant`

English:
instance Measure.prod.instIsMulLeftInvariant
  signature: [IsMulLeftInvariant μ] [SFinite μ] {H : Type*}
  body: by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map (g * ·) (h * ·)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_const_mul g) (measurable_const_mul h)]; rw [map_mul_left_eq_self μ g]; rw [map_mul_left_eq_self ν h]

@[to_additive]

中文:
实例 测度.乘积.instIsMulLeftInvariant
  签名: [是MulLeftInvariant μ] [SFinite μ] {H : 类型}
  定义体: by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map (g * ·) (h * ·)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_const_mul g) (measurable_const_mul h)]; rw [map_mul_left_eq_self μ g]; rw [map_mul_left_eq_self ν h]

@[to_additive]

Depends on / 依赖: Prod.map, _spec, map_mul_left_eq_self, map_prod_map, measurable_const_mul, ramificationIdx
-/
instance Measure.prod.instIsMulLeftInvariant [IsMulLeftInvariant μ] [SFinite μ] {H : Type*}
    [Mul H] {mH : MeasurableSpace H} {ν : Measure H} [MeasurableMul H] [IsMulLeftInvariant ν]
    [SFinite ν] : IsMulLeftInvariant (μ.prod ν) := by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map (g * ·) (h * ·)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_const_mul g) (measurable_const_mul h)]; rw [map_mul_left_eq_self μ g]; rw [map_mul_left_eq_self ν h]

@[to_additive]
/--
Instance `Measure.prod.instIsMulRightInvariant` / 实例 `Measure.prod.instIsMulRightInvariant`

English:
instance Measure.prod.instIsMulRightInvariant
  signature: [IsMulRightInvariant μ] [SFinite μ] {H : Type*}
  body: by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map (· * g) (· * h)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_mul_const g) (measurable_mul_const h)]; rw [map_mul_right_eq_self μ g]; rw [map_mul_right_eq_self ν h]

@[to_additive]

中文:
实例 测度.乘积.instIsMulRightInvariant
  签名: [是MulRightInvariant μ] [SFinite μ] {H : 类型}
  定义体: by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map (· * g) (· * h)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_mul_const g) (measurable_mul_const h)]; rw [map_mul_right_eq_self μ g]; rw [map_mul_right_eq_self ν h]

@[to_additive]

Depends on / 依赖: Prod.map, _of_not_le, le_bot_iff, le_bot_iff.not.mpr, map_eq_bot_iff_of_injective, map_mul_right_eq_self, map_prod_map, measurable_mul_const, not.mpr, ramificationIdx
-/
instance Measure.prod.instIsMulRightInvariant [IsMulRightInvariant μ] [SFinite μ] {H : Type*}
    [Mul H] {mH : MeasurableSpace H} {ν : Measure H} [MeasurableMul H] [IsMulRightInvariant ν]
    [SFinite ν] : IsMulRightInvariant (μ.prod ν) := by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map (· * g) (· * h)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_mul_const g) (measurable_mul_const h)]; rw [map_mul_right_eq_self μ g]; rw [map_mul_right_eq_self ν h]

@[to_additive]
/--
theorem `isMulLeftInvariant_map` / 定理 `isMulLeftInvariant_map`

English:
theorem isMulLeftInvariant_map
  statement: {H : Type*} [MeasurableSpace H] [Mul H] [MeasurableMul H]
  proof: by
  refine ⟨fun h => ?_⟩
  rw [map_map (measurable_const_mul _) hf]
  obtain ⟨g, rfl⟩ := h_surj h
  conv_rhs => rw [← map_mul_left_eq_self μ g]
  rw [map_map hf (measurable_const_mul _)]
  congr 2
  ext y
  simp only [comp_apply, map_mul]

中文:
定理 isMulLeftInvariant_map
  结论: {H : 类型} [可测空间 H] [乘法 H] [MeasurableMul H]
  证明: by
  refine ⟨fun h => ?_⟩
  rw [map_map (measurable_const_mul _) hf]
  obtain ⟨g, rfl⟩ := h_surj h
  conv_rhs => rw [← map_mul_left_eq_self μ g]
  rw [map_map hf (measurable_const_mul _)]
  congr 2
  ext y
  simp only [comp_apply, map_mul]

Depends on / 依赖: _spec, comp_apply, conv_rhs, h_surj, map_map, map_mul, map_mul_left_eq_self, measurable_const_mul, ramificationIdx
-/
theorem isMulLeftInvariant_map {H : Type*} [MeasurableSpace H] [Mul H] [MeasurableMul H]
    [IsMulLeftInvariant μ] (f : G ->ₙ* H) (hf : Measurable f) (h_surj : Surjective f) :
    IsMulLeftInvariant (Measure.map f μ) := by
  refine ⟨fun h => ?_⟩
  rw [map_map (measurable_const_mul _) hf]
  obtain ⟨g, rfl⟩ := h_surj h
  conv_rhs => rw [← map_mul_left_eq_self μ g]
  rw [map_map hf (measurable_const_mul _)]
  congr 2
  ext y
  simp only [comp_apply, map_mul]

end MeasurableMul

end Mul

section Semigroup

variable [Semigroup G] [MeasurableMul G] {μ : Measure G}

/-- The image of a left invariant measure under a left action is left invariant, assuming that
the action preserves multiplication. -/
@[to_additive /-- The image of a left invariant measure under a left additive action is left
invariant, assuming that the action preserves addition. -/]
/--
theorem `isMulLeftInvariant_map_smul` / 定理 `isMulLeftInvariant_map_smul`

English:
theorem isMulLeftInvariant_map_smul
  proof: (forall_measure_preimage_mul_iff _).1 fun x _ hs =>
    (smulInvariantMeasure_map_smul μ a).measure_preimage_smul x hs

中文:
定理 isMulLeftInvariant_map_smul
  证明: (forall_measure_preimage_mul_iff _).1 fun x _ hs =>
    (smulInvariantMeasure_map_smul μ a).measure_preimage_smul x hs

Depends on / 依赖: forall_measure_preimage_mul_iff, measure_preimage_smul, smulInvariantMeasure_map_smul
-/
theorem isMulLeftInvariant_map_smul
    {α} [SMul α G] [SMulCommClass α G G] [MeasurableConstSMul α G]
    [IsMulLeftInvariant μ] (a : α) :
    IsMulLeftInvariant (map (a • · : G -> G) μ) :=
  (forall_measure_preimage_mul_iff _).1 fun x _ hs =>
    (smulInvariantMeasure_map_smul μ a).measure_preimage_smul x hs

/-- The image of a right invariant measure under a left action is right invariant, assuming that
the action preserves multiplication. -/
@[to_additive /-- The image of a right invariant measure under a left additive action is right
invariant, assuming that the action preserves addition. -/]
/--
theorem `isMulRightInvariant_map_smul` / 定理 `isMulRightInvariant_map_smul`

English:
theorem isMulRightInvariant_map_smul
  proof: (forall_measure_preimage_mul_right_iff _).1 fun x _ hs =>
    (smulInvariantMeasure_map_smul μ a).measure_preimage_smul (MulOpposite.op x) hs

中文:
定理 isMulRightInvariant_map_smul
  证明: (forall_measure_preimage_mul_right_iff _).1 fun x _ hs =>
    (smulInvariantMeasure_map_smul μ a).measure_preimage_smul (MulOpposite.op x) hs

Depends on / 依赖: MulOpposite, MulOpposite.op, forall_measure_preimage_mul_right_iff, measure_preimage_smul, smulInvariantMeasure_map_smul
-/
theorem isMulRightInvariant_map_smul
    {α} [SMul α G] [SMulCommClass α Gᵐᵒᵖ G] [MeasurableConstSMul α G]
    [IsMulRightInvariant μ] (a : α) :
    IsMulRightInvariant (map (a • · : G -> G) μ) :=
  (forall_measure_preimage_mul_right_iff _).1 fun x _ hs =>
    (smulInvariantMeasure_map_smul μ a).measure_preimage_smul (MulOpposite.op x) hs

/-- The image of a left invariant measure under right multiplication is left invariant. -/
@[to_additive isMulLeftInvariant_map_add_right
/-- The image of a left invariant measure under right addition is left invariant. -/]
/--
Instance `isMulLeftInvariant_map_mul_right` / 实例 `isMulLeftInvariant_map_mul_right`

English:
instance isMulLeftInvariant_map_mul_right
  signature: [IsMulLeftInvariant μ] (g : G)
  body: isMulLeftInvariant_map_smul (MulOpposite.op g)

中文:
实例 isMulLeftInvariant_map_mul_right
  签名: [是MulLeftInvariant μ] (g : G)
  定义体: isMulLeftInvariant_map_smul (MulOpposite.op g)

Depends on / 依赖: MulOpposite, MulOpposite.op, isMulLeftInvariant_map_smul
-/
instance isMulLeftInvariant_map_mul_right [IsMulLeftInvariant μ] (g : G) :
    IsMulLeftInvariant (map (· * g) μ) :=
  isMulLeftInvariant_map_smul (MulOpposite.op g)

/-- The image of a right invariant measure under left multiplication is right invariant. -/
@[to_additive isMulRightInvariant_map_add_left
/-- The image of a right invariant measure under left addition is right invariant. -/]
/--
Instance `isMulRightInvariant_map_mul_left` / 实例 `isMulRightInvariant_map_mul_left`

English:
instance isMulRightInvariant_map_mul_left
  signature: [IsMulRightInvariant μ] (g : G)
  body: isMulRightInvariant_map_smul g

中文:
实例 isMulRightInvariant_map_mul_left
  签名: [是MulRightInvariant μ] (g : G)
  定义体: isMulRightInvariant_map_smul g

Depends on / 依赖: isMulRightInvariant_map_smul
-/
instance isMulRightInvariant_map_mul_left [IsMulRightInvariant μ] (g : G) :
    IsMulRightInvariant (map (g * ·) μ) :=
  isMulRightInvariant_map_smul g

end Semigroup

section DivInvMonoid

variable [DivInvMonoid G]

@[to_additive]
/--
theorem `map_div_right_eq_self` / 定理 `map_div_right_eq_self`

English:
theorem map_div_right_eq_self
  given: (μ : Measure G) [IsMulRightInvariant μ] (g : G)
  proof: by simp_rw [div_eq_mul_inv, map_mul_right_eq_self μ g⁻¹]

中文:
定理 map_div_right_eq_self
  条件: (μ : 测度 G) [是MulRightInvariant μ] (g : G)
  证明: by simp_rw [div_eq_mul_inv, map_mul_right_eq_self μ g⁻¹]

Depends on / 依赖: AlgHom, AlgHom.comp_algebraMap, Ideal.map_le_iff_le_comap, Ideal.map_pow, RingEquiv, RingEquiv.symm, RingEquiv.symm_symm, Set.mem_ofPred_eq, comap_coe, comap_comap, comp_algebraMap, div_eq_mul_inv, e.toAlgHom_toRingHom, e.toRingEquiv_toRingHom, map_comap_of_equiv, map_le_iff_le_comap, map_mul_right_eq_self, map_pow, mem_ofPred_eq, ramificationIdx
-/
theorem map_div_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) :
    map (· / g) μ = μ := by simp_rw [div_eq_mul_inv, map_mul_right_eq_self μ g⁻¹]

end DivInvMonoid

section Group

variable [Group G] [MeasurableMul G]

@[to_additive]
/--
theorem `measurePreserving_div_right` / 定理 `measurePreserving_div_right`

English:
theorem measurePreserving_div_right
  given: (μ : Measure G) [IsMulRightInvariant μ] (g : G)
  proof: by simp_rw [div_eq_mul_inv, measurePreserving_mul_right μ g⁻¹]

中文:
定理 measurePreserving_div_right
  条件: (μ : 测度 G) [是MulRightInvariant μ] (g : G)
  证明: by simp_rw [div_eq_mul_inv, measurePreserving_mul_right μ g⁻¹]

Depends on / 依赖: AlgEquivClass, AlgEquivClass.toAlgEquiv, P.map, P.map_comap_of_equiv, RingEquivClass, RingEquivClass.toRingEquiv, _comap_eq, div_eq_mul_inv, map_comap_of_equiv, measurePreserving_mul_right, p.ramificationIdx, ramificationIdx, simp_rw, toAlgEquiv, toRingEquiv
-/
theorem measurePreserving_div_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) :
    MeasurePreserving (· / g) μ μ := by simp_rw [div_eq_mul_inv, measurePreserving_mul_right μ g⁻¹]

/-- We shorten this from `measure_preimage_mul_left`, since left invariant is the preferred option
  for measures in this formalization. -/
@[to_additive (attr := simp)
/-- We shorten this from `measure_preimage_add_left`, since left invariant is the preferred option
for measures in this formalization. -/]
/--
theorem `measure_preimage_mul` / 定理 `measure_preimage_mul`

English:
theorem measure_preimage_mul
  given: (μ : Measure G) [IsMulLeftInvariant μ] (g : G) (A : Set G)
  proof: calc
    μ ((fun h => g * h) ⁻¹' A) = map (fun h => g * h) μ A :=
      ((MeasurableEquiv.mulLeft g).map_apply A).symm
    _ = μ A := by rw [map_mul_left_eq_self μ g]

@[to_additive (attr := simp)]

中文:
定理 measure_preimage_mul
  条件: (μ : 测度 G) [是MulLeftInvariant μ] (g : G) (A : 集合 G)
  证明: calc
    μ ((fun h => g * h) ⁻¹' A) = map (fun h => g * h) μ A :=
      ((MeasurableEquiv.mulLeft g).map_apply A).symm
    _ = μ A := by rw [map_mul_left_eq_self μ g]

@[to_additive (attr := simp)]

Depends on / 依赖: Ideal.pow_le_pow_right, Ideal.ramificationIdx, MeasurableEquiv, MeasurableEquiv.mulLeft, Nat.find, Nat.find_min, Nat.find_spec, Nat.succ_le_iff.mpr, _eq_find, _eq_zero, classical, find_min, find_spec, h2k.le, hk.trans, map_apply, map_mul_left_eq_self, mulLeft, p.map, pow_le_pow_right
-/
theorem measure_preimage_mul (μ : Measure G) [IsMulLeftInvariant μ] (g : G) (A : Set G) :
    μ ((fun h => g * h) ⁻¹' A) = μ A :=
  calc
    μ ((fun h => g * h) ⁻¹' A) = map (fun h => g * h) μ A :=
      ((MeasurableEquiv.mulLeft g).map_apply A).symm
    _ = μ A := by rw [map_mul_left_eq_self μ g]

@[to_additive (attr := simp)]
/--
theorem `measure_preimage_mul_right` / 定理 `measure_preimage_mul_right`

English:
theorem measure_preimage_mul_right
  given: (μ : Measure G) [IsMulRightInvariant μ] (g : G) (A : Set G)
  proof: calc
    μ ((fun h => h * g) ⁻¹' A) = map (fun h => h * g) μ A :=
      ((MeasurableEquiv.mulRight g).map_apply A).symm
    _ = μ A := by rw [map_mul_right_eq_self μ g]

@[to_additive]

中文:
定理 measure_preimage_mul_right
  条件: (μ : 测度 G) [是MulRightInvariant μ] (g : G) (A : 集合 G)
  证明: calc
    μ ((fun h => h * g) ⁻¹' A) = map (fun h => h * g) μ A :=
      ((MeasurableEquiv.mulRight g).map_apply A).symm
    _ = μ A := by rw [map_mul_right_eq_self μ g]

@[to_additive]

Depends on / 依赖: AtPrime, Ideal.map_eq_bot, Ideal.map_map, Ideal.map_mono, Ideal.map_pow, Ideal.ramificationIdx, IsNoetherian, IsNoetherian.noetherian, IsScalarTower, IsScalarTower.algebraMap_eq, Localization, Localization.AtPrime, Localization.AtPrime.map_eq_maximalIdeal, MeasurableEquiv, MeasurableEquiv.mulRight, Submodule, Submodule.eq_bot_of_le_smul_of_le_jacobson_bot, _ne_one_iff, algebraMap, algebraMap_eq
-/
theorem measure_preimage_mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) (A : Set G) :
    μ ((fun h => h * g) ⁻¹' A) = μ A :=
  calc
    μ ((fun h => h * g) ⁻¹' A) = map (fun h => h * g) μ A :=
      ((MeasurableEquiv.mulRight g).map_apply A).symm
    _ = μ A := by rw [map_mul_right_eq_self μ g]

@[to_additive]
/--
theorem `map_mul_left_ae` / 定理 `map_mul_left_ae`

English:
theorem map_mul_left_ae
  given: (μ : Measure G) [IsMulLeftInvariant μ] (x : G)
  proof: ((MeasurableEquiv.mulLeft x).map_ae μ).trans congr_arg ae map_mul_left_eq_self μ x

@[to_additive]

中文:
定理 map_mul_left_ae
  条件: (μ : 测度 G) [是MulLeftInvariant μ] (x : G)
  证明: ((MeasurableEquiv.mulLeft x).map_ae μ).trans congr_arg ae map_mul_left_eq_self μ x

@[to_additive]

Depends on / 依赖: IsMulTorsionFree, IsMulTorsionFree.pow_right_injective, MeasurableEquiv, MeasurableEquiv.mulLeft, _spec, congr_arg, le_antisymm, map_ae, map_mul_left_eq_self, mulLeft, one_eq_top, pow_le_self, pow_one, ramificationIdx, two_ne_zero
-/
theorem map_mul_left_ae (μ : Measure G) [IsMulLeftInvariant μ] (x : G) :
    Filter.map (fun h => x * h) (ae μ) = ae μ :=
((MeasurableEquiv.mulLeft x).map_ae μ).trans congr_arg ae map_mul_left_eq_self μ x

@[to_additive]
/--
theorem `map_mul_right_ae` / 定理 `map_mul_right_ae`

English:
theorem map_mul_right_ae
  given: (μ : Measure G) [IsMulRightInvariant μ] (x : G)
  proof: ((MeasurableEquiv.mulRight x).map_ae μ).trans congr_arg ae map_mul_right_eq_self μ x

@[to_additive]

中文:
定理 map_mul_right_ae
  条件: (μ : 测度 G) [是MulRightInvariant μ] (x : G)
  证明: ((MeasurableEquiv.mulRight x).map_ae μ).trans congr_arg ae map_mul_right_eq_self μ x

@[to_additive]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, MeasurableEquiv, MeasurableEquiv.mulRight, Nat.sSup_of_not_bddAbove, algebraMap_eq, comap_mono, congr_arg, csSup_le_csSup, h.imp_symm, imp_symm, map_ae, map_le_iff_le_comap, map_map, map_mul_right_eq_self, mulRight, ramificationIdx, sSup_of_not_bddAbove, simp_rw
-/
theorem map_mul_right_ae (μ : Measure G) [IsMulRightInvariant μ] (x : G) :
    Filter.map (fun h => h * x) (ae μ) = ae μ :=
((MeasurableEquiv.mulRight x).map_ae μ).trans congr_arg ae map_mul_right_eq_self μ x

@[to_additive]
/--
theorem `map_div_right_ae` / 定理 `map_div_right_ae`

English:
theorem map_div_right_ae
  given: (μ : Measure G) [IsMulRightInvariant μ] (x : G)
  proof: ((MeasurableEquiv.divRight x).map_ae μ).trans congr_arg ae map_div_right_eq_self μ x

@[to_additive]

中文:
定理 map_div_right_ae
  条件: (μ : 测度 G) [是MulRightInvariant μ] (x : G)
  证明: ((MeasurableEquiv.divRight x).map_ae μ).trans congr_arg ae map_div_right_eq_self μ x

@[to_additive]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.divRight, congr_arg, divRight, map_ae, map_div_right_eq_self
-/
theorem map_div_right_ae (μ : Measure G) [IsMulRightInvariant μ] (x : G) :
    Filter.map (fun t => t / x) (ae μ) = ae μ :=
((MeasurableEquiv.divRight x).map_ae μ).trans congr_arg ae map_div_right_eq_self μ x

@[to_additive]
/--
theorem `eventually_mul_left_iff` / 定理 `eventually_mul_left_iff`

English:
theorem eventually_mul_left_iff
  given: (μ : Measure G) [IsMulLeftInvariant μ] (t : G) {p : G -> Prop}
  proof: by
  conv_rhs => rw [Filter.Eventually, ← map_mul_left_ae μ t]
  rfl

@[to_additive]

中文:
定理 eventually_mul_left_iff
  条件: (μ : 测度 G) [是MulLeftInvariant μ] (t : G) {p : G -> 命题}
  证明: by
  conv_rhs => rw [Filter.Eventually, ← map_mul_left_ae μ t]
  rfl

@[to_additive]

Depends on / 依赖: Eventually, Filter, Filter.Eventually, Ideal.ramificationIdx, Ideal.zero_eq_bot, UniqueFactorizationMonoid, UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors, _eq_normalizedFactors_count, _of_not_le, conv_rhs, emultiplicity_eq_count_normalizedFactors, irreducible_iff_prime, irreducible_iff_prime.mpr, le_bot_iff, le_bot_iff.mp, map_mul_left_ae, multiplicity_eq_of_emultiplicity_eq_some, multiplicity_zero_eq_zero_of_ne_zero, normalize_eq, prime_of_isPrime
-/
theorem eventually_mul_left_iff (μ : Measure G) [IsMulLeftInvariant μ] (t : G) {p : G -> Prop} :
    (forallᵐ x ∂μ, p (t * x)) ↔ forallᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_mul_left_ae μ t]
  rfl

@[to_additive]
/--
theorem `eventually_mul_right_iff` / 定理 `eventually_mul_right_iff`

English:
theorem eventually_mul_right_iff
  given: (μ : Measure G) [IsMulRightInvariant μ] (t : G) {p : G -> Prop}
  proof: by
  conv_rhs => rw [Filter.Eventually, ← map_mul_right_ae μ t]
  rfl

@[to_additive]

中文:
定理 eventually_mul_right_iff
  条件: (μ : 测度 G) [是MulRightInvariant μ] (t : G) {p : G -> 命题}
  证明: by
  conv_rhs => rw [Filter.Eventually, ← map_mul_right_ae μ t]
  rfl

@[to_additive]

Depends on / 依赖: Eventually, Filter, Filter.Eventually, IsDedekindDomain, IsDedekindDomain.ramificationIdx, _eq_normalizedFactors_count, conv_rhs, factors_eq_normalizedFactors, map_mul_right_ae, ramificationIdx
-/
theorem eventually_mul_right_iff (μ : Measure G) [IsMulRightInvariant μ] (t : G) {p : G -> Prop} :
    (forallᵐ x ∂μ, p (x * t)) ↔ forallᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_mul_right_ae μ t]
  rfl

@[to_additive]
/--
theorem `eventually_div_right_iff` / 定理 `eventually_div_right_iff`

English:
theorem eventually_div_right_iff
  given: (μ : Measure G) [IsMulRightInvariant μ] (t : G) {p : G -> Prop}
  proof: by
  conv_rhs => rw [Filter.Eventually, ← map_div_right_ae μ t]
  rfl

@[to_additive AddSubgroup.index_mul_measure]

中文:
定理 eventually_div_right_iff
  条件: (μ : 测度 G) [是MulRightInvariant μ] (t : G) {p : G -> 命题}
  证明: by
  conv_rhs => rw [Filter.Eventually, ← map_div_right_ae μ t]
  rfl

@[to_additive AddSubgroup.index_mul_measure]

Depends on / 依赖: Eventually, Filter, Filter.Eventually, Ideal.dvd_iff_le.mpr, Ideal.prime_of_isPrime, IsDedekindDomain, IsDedekindDomain.ramificationIdx, Multiset, Multiset.count_ne_zero, _eq_normalizedFactors_count, associated_iff_eq, associated_iff_eq.mp, conv_rhs, count_ne_zero, dvd_iff_le, exists_mem_normalizedFactors_of_dvd, irreducible, le_bot_iff, le_bot_iff.mp, map_div_right_ae
-/
theorem eventually_div_right_iff (μ : Measure G) [IsMulRightInvariant μ] (t : G) {p : G -> Prop} :
    (forallᵐ x ∂μ, p (x / t)) ↔ forallᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_div_right_ae μ t]
  rfl

@[to_additive AddSubgroup.index_mul_measure]
/--
lemma `Subgroup.index_mul_measure` / 引理 `Subgroup.index_mul_measure`

English:
lemma Subgroup.index_mul_measure
  statement: (H : Subgroup G) [H.FiniteIndex] (hH : MeasurableSet (H : Set G))
  proof: by
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  calc
    H.index * μ H = ∑' a : s, μ (a.val • H) := by simp [measure_smul, hs.encard_left]
    _ = μ univ := by
      rw [← measure_iUnion _ fun _ => hH.const_smul _]
      · simp [hs.mul_eq]
      · exact fun a b hab => hs.pairwiseDisjoint_smul a.2 b.2 (Subtype.val_injective.ne hab)

中文:
引理 子群.index_mul_measure
  结论: (H : 子群 G) [H.FiniteIndex] (hH : 可测集 (H : 集合 G))
  证明: by
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  calc
    H.index * μ H = ∑' a : s, μ (a.val • H) := by simp [measure_smul, hs.encard_left]
    _ = μ univ := by
      rw [← measure_iUnion _ fun _ => hH.const_smul _]
      · simp [hs.mul_eq]
      · exact fun a b hab => hs.pairwiseDisjoint_smul a.2 b.2 (Subtype.val_injective.ne hab)

Depends on / 依赖: Finite, H.exists_isComplement_left, H.index, IsDedekindDomain, IsDedekindDomain.ramificationIdx, Subtype, Subtype.val_injective.ne, _ne_zero, a.val, const_smul, encard_left, exists_isComplement_left, finite_left_iff, hH.const_smul, hs.encard_left, hs.finite_left_iff.mpr, hs.mul_eq, hs.pairwiseDisjoint_smul, le_of_eq, liesOver_iff
-/
lemma Subgroup.index_mul_measure (H : Subgroup G) [H.FiniteIndex] (hH : MeasurableSet (H : Set G))
    (μ : Measure G) [IsMulLeftInvariant μ] : H.index * μ H = μ univ := by
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  calc
    H.index * μ H = ∑' a : s, μ (a.val • H) := by simp [measure_smul, hs.encard_left]
    _ = μ univ := by
      rw [← measure_iUnion _ fun _ => hH.const_smul _]
      · simp [hs.mul_eq]
      · exact fun a b hab => hs.pairwiseDisjoint_smul a.2 b.2 (Subtype.val_injective.ne hab)

end Group

namespace Measure

-- TODO: noncomputable has to be specified explicitly. https://github.com/leanprover-community/mathlib4/issues/1074 (item 8)

/-- The measure `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive /-- The measure `A ↦ μ (- A)`, where `- A` is the pointwise negation of `A`. -/]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def inv [Inv G] (μ : Measure G)
  body: Measure.map inv μ

中文:
定义 noncomputable
  签名: def inv [取逆 G] (μ : 测度 G)
  定义体: Measure.map inv μ

Depends on / 依赖: AtPrime, Ideal.dvd_iff_le.mpr, Ideal.map_map, Ideal.map_mul, Ideal.mul_mono_right, IsScalarTower, IsScalarTower.algebraMap_eq, Localization, Localization.AtPrime, Localization.AtPrime.map_eq_maximalIdea, _eq_one_of_map_localization, _ne_one_iff, algebraMap, algebraMap_eq, dvd_iff_le, ha.trans_le, map_eq_maximalIdea, map_map, map_mul, mul_mono_right
-/
protected noncomputable def inv [Inv G] (μ : Measure G) : Measure G :=
  Measure.map inv μ

/--
Definition of `IsNegInvariant` / `IsNegInvariant` 的定义

English:
class IsNegInvariant
  parameters: [Neg G] (μ : Measure G)
  axioms and operations (1):
    - neg_eq_self : μ.neg = μ

中文:
类 是NegInvariant
  参数: [取负 G] (μ : 测度 G)
  公理与运算 (1 个):
    - neg_eq_self : μ.neg = μ

Depends on / 依赖: _le_ramificationIdx, _ne_zero_of_liesOver, liesOver_iff, p.ramificationIdx, ramificationIdx
-/
class IsNegInvariant [Neg G] (μ : Measure G) : Prop where
  neg_eq_self : μ.neg = μ

/-- A measure is invariant under inversion if `μ⁻¹ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (A⁻¹) = μ A`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive existing]
/--
Definition of `IsInvInvariant` / `IsInvInvariant` 的定义

English:
class IsInvInvariant
  parameters: [Inv G] (μ : Measure G)
  axioms and operations (1):
    - inv_eq_self : μ.inv = μ

中文:
类 是InvInvariant
  参数: [取逆 G] (μ : 测度 G)
  公理与运算 (1 个):
    - inv_eq_self : μ.inv = μ
-/
class IsInvInvariant [Inv G] (μ : Measure G) : Prop where
  inv_eq_self : μ.inv = μ

section Inv

variable [Inv G]

@[to_additive]
/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (μ : Measure G)
  statement: μ.inv = Measure.map inv μ
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_def
  条件: (μ : 测度 G)
  结论: μ.inv = 测度.map inv μ
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_def (μ : Measure G) : μ.inv = Measure.map inv μ := rfl

@[to_additive (attr := simp)]
/--
theorem `inv_eq_self` / 定理 `inv_eq_self`

English:
theorem inv_eq_self
  given: (μ : Measure G) [IsInvInvariant μ]
  statement: μ.inv = μ
  proof: IsInvInvariant.inv_eq_self

@[to_additive (attr := simp)]

中文:
定理 inv_eq_self
  条件: (μ : 测度 G) [是InvInvariant μ]
  结论: μ.inv = μ
  证明: IsInvInvariant.inv_eq_self

@[to_additive (attr := simp)]

Depends on / 依赖: DimensionLEOne, IsDedekindDomain, IsDedekindDomain.ramificationIdx, IsInvInvariant, IsInvInvariant.inv_eq_self, IsMaximal, IsScalarTower, IsScalarTower.algebraMap_eq, P.IsMaximal, Ring.DimensionLEOne.maximalOfPrime, _eq_no, _eq_normalizedFactors_count, algebraMap, algebraMap_eq, inv_eq_self, map_map, maximalOfPrime, ne_bot_of_le_ne_bot, ne_bot_of_map_ne_bot, ramificationIdx
-/
theorem inv_eq_self (μ : Measure G) [IsInvInvariant μ] : μ.inv = μ :=
  IsInvInvariant.inv_eq_self

@[to_additive (attr := simp)]
/--
theorem `map_inv_eq_self` / 定理 `map_inv_eq_self`

English:
theorem map_inv_eq_self
  given: (μ : Measure G) [IsInvInvariant μ]
  statement: map Inv.inv μ = μ
  proof: IsInvInvariant.inv_eq_self

中文:
定理 map_inv_eq_self
  条件: (μ : 测度 G) [是InvInvariant μ]
  结论: map 取逆.inv μ = μ
  证明: IsInvInvariant.inv_eq_self

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, IsInvInvariant, IsInvInvariant.inv_eq_self, IsPrime, IsTorsionFree, Module, Module.IsTorsionFree, Module.IsTorsionFree.of_smul_eq_zero, P.IsPrime, _algebra_tower, algebraMap_eq_zero_iff, algebra_compatible_smul, eq_or_ne, inv_eq_self, isPrime_of_liesOver, le_of_eq, map_le_iff_le_comap, map_le_iff_le_comap.mpr, map_ne_bot_of_ne_bot
-/
theorem map_inv_eq_self (μ : Measure G) [IsInvInvariant μ] : map Inv.inv μ = μ :=
  IsInvInvariant.inv_eq_self

variable [MeasurableInv G]

@[to_additive]
/--
theorem `measurePreserving_inv` / 定理 `measurePreserving_inv`

English:
theorem measurePreserving_inv
  given: (μ : Measure G) [IsInvInvariant μ]
  statement: MeasurePreserving Inv.inv μ μ
  proof: ⟨measurable_inv, map_inv_eq_self μ⟩

@[to_additive]

中文:
定理 measurePreserving_inv
  条件: (μ : 测度 G) [是InvInvariant μ]
  结论: 保测 取逆.inv μ μ
  证明: ⟨measurable_inv, map_inv_eq_self μ⟩

@[to_additive]

Depends on / 依赖: map_inv_eq_self, measurable_inv
-/
theorem measurePreserving_inv (μ : Measure G) [IsInvInvariant μ] : MeasurePreserving Inv.inv μ μ :=
  ⟨measurable_inv, map_inv_eq_self μ⟩

@[to_additive]
/--
Instance `inv.instSFinite` / 实例 `inv.instSFinite`

English:
instance inv.instSFinite
  signature: (μ : Measure G) [SFinite μ]
  body: by
  rw [Measure.inv]; infer_instance

中文:
实例 inv.instSFinite
  签名: (μ : 测度 G) [SFinite μ]
  定义体: by
  rw [Measure.inv]; infer_instance

Depends on / 依赖: Measure, Measure.inv, infer_instance
-/
instance inv.instSFinite (μ : Measure G) [SFinite μ] : SFinite μ.inv := by
  rw [Measure.inv]; infer_instance

end Inv

section InvolutiveInv

variable [InvolutiveInv G] [MeasurableInv G]

@[to_additive (attr := simp)]
/--
theorem `inv_apply` / 定理 `inv_apply`

English:
theorem inv_apply
  given: (μ : Measure G) (s : Set G)
  statement: μ.inv s = μ s⁻¹
  proof: (MeasurableEquiv.inv G).map_apply s

@[to_additive (attr := simp)]

中文:
定理 inv_apply
  条件: (μ : 测度 G) (s : 集合 G)
  结论: μ.inv s = μ s⁻¹
  证明: (MeasurableEquiv.inv G).map_apply s

@[to_additive (attr := simp)]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.inv, map_apply
-/
theorem inv_apply (μ : Measure G) (s : Set G) : μ.inv s = μ s⁻¹ :=
  (MeasurableEquiv.inv G).map_apply s

@[to_additive (attr := simp)]
/--
theorem `inv_inv` / 定理 `inv_inv`

English:
theorem inv_inv
  given: (μ : Measure G)
  statement: μ.inv.inv = μ
  proof: (MeasurableEquiv.inv G).map_symm_map

@[to_additive (attr := simp)]

中文:
定理 inv_inv
  条件: (μ : 测度 G)
  结论: μ.inv.inv = μ
  证明: (MeasurableEquiv.inv G).map_symm_map

@[to_additive (attr := simp)]
-/
protected theorem inv_inv (μ : Measure G) : μ.inv.inv = μ :=
  (MeasurableEquiv.inv G).map_symm_map

@[to_additive (attr := simp)]
/--
theorem `measure_inv` / 定理 `measure_inv`

English:
theorem measure_inv
  given: (μ : Measure G) [IsInvInvariant μ] (A : Set G)
  statement: μ A⁻¹ = μ A
  proof: by
  rw [← inv_apply]; rw [inv_eq_self]

@[to_additive]

中文:
定理 measure_inv
  条件: (μ : 测度 G) [是InvInvariant μ] (A : 集合 G)
  结论: μ A⁻¹ = μ A
  证明: by
  rw [← inv_apply]; rw [inv_eq_self]

@[to_additive]

Depends on / 依赖: inv_apply, inv_eq_self
-/
theorem measure_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) : μ A⁻¹ = μ A := by
  rw [← inv_apply]; rw [inv_eq_self]

@[to_additive]
/--
theorem `measure_preimage_inv` / 定理 `measure_preimage_inv`

English:
theorem measure_preimage_inv
  given: (μ : Measure G) [IsInvInvariant μ] (A : Set G)
  proof: μ.measure_inv A

@[to_additive]

中文:
定理 measure_preimage_inv
  条件: (μ : 测度 G) [是InvInvariant μ] (A : 集合 G)
  证明: μ.measure_inv A

@[to_additive]

Depends on / 依赖: measure_inv
-/
theorem measure_preimage_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) :
    μ (Inv.inv ⁻¹' A) = μ A :=
  μ.measure_inv A

@[to_additive]
/--
Instance `inv.instSigmaFinite` / 实例 `inv.instSigmaFinite`

English:
instance inv.instSigmaFinite
  signature: (μ : Measure G) [SigmaFinite μ]
  body: (MeasurableEquiv.inv G).sigmaFinite_map

中文:
实例 inv.instSigmaFinite
  签名: (μ : 测度 G) [σ有限 μ]
  定义体: (MeasurableEquiv.inv G).sigmaFinite_map

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.inv, sigmaFinite_map
-/
instance inv.instSigmaFinite (μ : Measure G) [SigmaFinite μ] : SigmaFinite μ.inv :=
  (MeasurableEquiv.inv G).sigmaFinite_map

end InvolutiveInv

section DivisionMonoid

variable [DivisionMonoid G] [MeasurableMul G] [MeasurableInv G] {μ : Measure G}

@[to_additive]
/--
Instance `inv.instIsMulRightInvariant` / 实例 `inv.instIsMulRightInvariant`

English:
instance inv.instIsMulRightInvariant
  signature: [IsMulLeftInvariant μ]
  body: by
  constructor
  intro g
  conv_rhs => rw [← map_mul_left_eq_self μ g⁻¹]
  simp_rw [Measure.inv, map_map (measurable_mul_const g) measurable_inv,
    map_map measurable_inv (measurable_const_mul g⁻¹), Function.comp_def, mul_inv_rev, inv_inv]

@[to_additive]

中文:
实例 inv.instIsMulRightInvariant
  签名: [是MulLeftInvariant μ]
  定义体: by
  constructor
  intro g
  conv_rhs => rw [← map_mul_left_eq_self μ g⁻¹]
  simp_rw [Measure.inv, map_map (measurable_mul_const g) measurable_inv,
    map_map measurable_inv (measurable_const_mul g⁻¹), Function.comp_def, mul_inv_rev, inv_inv]

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, Measure, Measure.inv, comp_def, conv_rhs, inv_inv, map_map, map_mul_left_eq_self, measurable_const_mul, measurable_inv, measurable_mul_const, mul_inv_rev, simp_rw
-/
instance inv.instIsMulRightInvariant [IsMulLeftInvariant μ] : IsMulRightInvariant μ.inv := by
  constructor
  intro g
  conv_rhs => rw [← map_mul_left_eq_self μ g⁻¹]
  simp_rw [Measure.inv, map_map (measurable_mul_const g) measurable_inv,
    map_map measurable_inv (measurable_const_mul g⁻¹), Function.comp_def, mul_inv_rev, inv_inv]

@[to_additive]
/--
Instance `inv.instIsMulLeftInvariant` / 实例 `inv.instIsMulLeftInvariant`

English:
instance inv.instIsMulLeftInvariant
  signature: [IsMulRightInvariant μ]
  body: by
  constructor
  intro g
  conv_rhs => rw [← map_mul_right_eq_self μ g⁻¹]
  simp_rw [Measure.inv, map_map (measurable_const_mul g) measurable_inv,
    map_map measurable_inv (measurable_mul_const g⁻¹), Function.comp_def, mul_inv_rev, inv_inv]

@[to_additive]

中文:
实例 inv.instIsMulLeftInvariant
  签名: [是MulRightInvariant μ]
  定义体: by
  constructor
  intro g
  conv_rhs => rw [← map_mul_right_eq_self μ g⁻¹]
  simp_rw [Measure.inv, map_map (measurable_const_mul g) measurable_inv,
    map_map measurable_inv (measurable_mul_const g⁻¹), Function.comp_def, mul_inv_rev, inv_inv]

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, Measure, Measure.inv, comp_def, conv_rhs, inv_inv, map_map, map_mul_right_eq_self, measurable_const_mul, measurable_inv, measurable_mul_const, mul_inv_rev, simp_rw
-/
instance inv.instIsMulLeftInvariant [IsMulRightInvariant μ] : IsMulLeftInvariant μ.inv := by
  constructor
  intro g
  conv_rhs => rw [← map_mul_right_eq_self μ g⁻¹]
  simp_rw [Measure.inv, map_map (measurable_const_mul g) measurable_inv,
    map_map measurable_inv (measurable_mul_const g⁻¹), Function.comp_def, mul_inv_rev, inv_inv]

@[to_additive]
/--
theorem `measurePreserving_div_left` / 定理 `measurePreserving_div_left`

English:
theorem measurePreserving_div_left
  statement: (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
  proof: by
  simp_rw [div_eq_mul_inv]
  exact (measurePreserving_mul_left μ g).comp (measurePreserving_inv μ)

@[to_additive]

中文:
定理 measurePreserving_div_left
  结论: (μ : 测度 G) [是InvInvariant μ] [是MulLeftInvariant μ]
  证明: by
  simp_rw [div_eq_mul_inv]
  exact (measurePreserving_mul_left μ g).comp (measurePreserving_inv μ)

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, measurePreserving_inv, measurePreserving_mul_left, simp_rw
-/
theorem measurePreserving_div_left (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : MeasurePreserving (fun t => g / t) μ μ := by
  simp_rw [div_eq_mul_inv]
  exact (measurePreserving_mul_left μ g).comp (measurePreserving_inv μ)

@[to_additive]
/--
theorem `map_div_left_eq_self` / 定理 `map_div_left_eq_self`

English:
theorem map_div_left_eq_self
  given: (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G)
  proof: (measurePreserving_div_left μ g).map_eq

@[to_additive]

中文:
定理 map_div_left_eq_self
  条件: (μ : 测度 G) [是InvInvariant μ] [是MulLeftInvariant μ] (g : G)
  证明: (measurePreserving_div_left μ g).map_eq

@[to_additive]

Depends on / 依赖: map_eq, measurePreserving_div_left
-/
theorem map_div_left_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) :
    map (fun t => g / t) μ = μ :=
  (measurePreserving_div_left μ g).map_eq

@[to_additive]
/--
theorem `measurePreserving_mul_right_inv` / 定理 `measurePreserving_mul_right_inv`

English:
theorem measurePreserving_mul_right_inv
  statement: (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
  proof: (measurePreserving_inv μ).comp measurePreserving_mul_left μ g

@[to_additive]

中文:
定理 measurePreserving_mul_right_inv
  结论: (μ : 测度 G) [是InvInvariant μ] [是MulLeftInvariant μ]
  证明: (measurePreserving_inv μ).comp measurePreserving_mul_left μ g

@[to_additive]

Depends on / 依赖: measurePreserving_inv, measurePreserving_mul_left
-/
theorem measurePreserving_mul_right_inv (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : MeasurePreserving (fun t => (g * t)⁻¹) μ μ :=
(measurePreserving_inv μ).comp measurePreserving_mul_left μ g

@[to_additive]
/--
theorem `map_mul_right_inv_eq_self` / 定理 `map_mul_right_inv_eq_self`

English:
theorem map_mul_right_inv_eq_self
  statement: (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
  proof: (measurePreserving_mul_right_inv μ g).map_eq

中文:
定理 map_mul_right_inv_eq_self
  结论: (μ : 测度 G) [是InvInvariant μ] [是MulLeftInvariant μ]
  证明: (measurePreserving_mul_right_inv μ g).map_eq

Depends on / 依赖: map_eq, measurePreserving_mul_right_inv
-/
theorem map_mul_right_inv_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : map (fun t => (g * t)⁻¹) μ = μ :=
  (measurePreserving_mul_right_inv μ g).map_eq

end DivisionMonoid

section Group

variable [Group G] {μ : Measure G}

section MeasurableMul

variable [MeasurableMul G]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (count : Measure G).IsMulLeftInvariant
  body: by
    ext s hs
    rw [count_apply hs]; rw [map_apply (measurable_const_mul _) hs]; rw [count_apply (measurable_const_mul _ hs)]; rw [encard_preimage_of_bijective (Group.mulLeft_bijective _)]

@[to_additive]

中文:
实例 :
  签名: (count : 测度 G).是MulLeftInvariant
  定义体: by
    ext s hs
    rw [count_apply hs]; rw [map_apply (measurable_const_mul _) hs]; rw [count_apply (measurable_const_mul _ hs)]; rw [encard_preimage_of_bijective (Group.mulLeft_bijective _)]

@[to_additive]

Depends on / 依赖: Group.mulLeft_bijective, count_apply, encard_preimage_of_bijective, map_apply, measurable_const_mul, mulLeft_bijective
-/
instance : (count : Measure G).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    ext s hs
    rw [count_apply hs]; rw [map_apply (measurable_const_mul _) hs]; rw [count_apply (measurable_const_mul _ hs)]; rw [encard_preimage_of_bijective (Group.mulLeft_bijective _)]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (count : Measure G).IsMulRightInvariant
  body: by
    ext s hs
    rw [count_apply hs]; rw [map_apply (measurable_mul_const _) hs]; rw [count_apply (measurable_mul_const _ hs)]; rw [encard_preimage_of_bijective (Group.mulRight_bijective _)]

中文:
实例 :
  签名: (count : 测度 G).是MulRightInvariant
  定义体: by
    ext s hs
    rw [count_apply hs]; rw [map_apply (measurable_mul_const _) hs]; rw [count_apply (measurable_mul_const _ hs)]; rw [encard_preimage_of_bijective (Group.mulRight_bijective _)]

Depends on / 依赖: Group.mulRight_bijective, count_apply, encard_preimage_of_bijective, map_apply, measurable_mul_const, mulRight_bijective
-/
instance : (count : Measure G).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    ext s hs
    rw [count_apply hs]; rw [map_apply (measurable_mul_const _) hs]; rw [count_apply (measurable_mul_const _ hs)]; rw [encard_preimage_of_bijective (Group.mulRight_bijective _)]

/- TODO: To avoid repeating the proofs, the following two lemmas should be consequences of
a similar result about `SMulInvariantMeasure`. -/

@[to_additive]
/--
theorem `IsMulLeftInvariant.comap` / 定理 `IsMulLeftInvariant.comap`

English:
theorem IsMulLeftInvariant.comap
  statement: {H} [Group H] {mH : MeasurableSpace H} [MeasurableMul H]
  proof: by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [hf.comap_apply]
    have : f '' (g * ·) ⁻¹' s = (f g * ·) ⁻¹' f '' s := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        exact ⟨g⁻¹ * y, by simp [yins], by simp [hy]⟩
    rw [this]; rw [← map_apply (by fun_prop)]; rw [IsMulLeftInvariant.map_mul_left_eq_self]
    exact hf.measurableSet_image.mpr hs

@[to_additive]

中文:
定理 是MulLeftInvariant.comap
  结论: {H} [群 H] {mH : 可测空间 H} [MeasurableMul H]
  证明: by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [hf.comap_apply]
    have : f '' (g * ·) ⁻¹' s = (f g * ·) ⁻¹' f '' s := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        exact ⟨g⁻¹ * y, by simp [yins], by simp [hy]⟩
    rw [this]; rw [← map_apply (by fun_prop)]; rw [IsMulLeftInvariant.map_mul_left_eq_self]
    exact hf.measurableSet_image.mpr hs

@[to_additive]
-/
protected theorem IsMulLeftInvariant.comap {H} [Group H] {mH : MeasurableSpace H} [MeasurableMul H]
    (μ : Measure H) [IsMulLeftInvariant μ] {f : G ->* H} (hf : MeasurableEmbedding f) :
    (μ.comap f).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [hf.comap_apply]
    have : f '' (g * ·) ⁻¹' s = (f g * ·) ⁻¹' f '' s := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        exact ⟨g⁻¹ * y, by simp [yins], by simp [hy]⟩
    rw [this]; rw [← map_apply (by fun_prop)]; rw [IsMulLeftInvariant.map_mul_left_eq_self]
    exact hf.measurableSet_image.mpr hs

@[to_additive]
/--
theorem `IsMulRightInvariant.comap` / 定理 `IsMulRightInvariant.comap`

English:
theorem IsMulRightInvariant.comap
  statement: {H} [Group H] {mH : MeasurableSpace H} [MeasurableMul H]
  proof: by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [hf.comap_apply]
    have : f '' (· * g) ⁻¹' s = (· * f g) ⁻¹' f '' s := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y * g, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        exact ⟨y * g⁻¹, by simp [yins], by simp [hy]⟩
    rw [this]; rw [← map_apply (by fun_prop)]; rw [IsMulRightInvariant.map_mul_right_eq_self]
    exact hf.measurableSet_image.mpr hs

中文:
定理 是MulRightInvariant.comap
  结论: {H} [群 H] {mH : 可测空间 H} [MeasurableMul H]
  证明: by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [hf.comap_apply]
    have : f '' (· * g) ⁻¹' s = (· * f g) ⁻¹' f '' s := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y * g, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        exact ⟨y * g⁻¹, by simp [yins], by simp [hy]⟩
    rw [this]; rw [← map_apply (by fun_prop)]; rw [IsMulRightInvariant.map_mul_right_eq_self]
    exact hf.measurableSet_image.mpr hs
-/
protected theorem IsMulRightInvariant.comap {H} [Group H] {mH : MeasurableSpace H} [MeasurableMul H]
    (μ : Measure H) [IsMulRightInvariant μ] {f : G ->* H} (hf : MeasurableEmbedding f) :
    (μ.comap f).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [hf.comap_apply]
    have : f '' (· * g) ⁻¹' s = (· * f g) ⁻¹' f '' s := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y * g, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        exact ⟨y * g⁻¹, by simp [yins], by simp [hy]⟩
    rw [this]; rw [← map_apply (by fun_prop)]; rw [IsMulRightInvariant.map_mul_right_eq_self]
    exact hf.measurableSet_image.mpr hs

end MeasurableMul

variable [MeasurableInv G]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (count : Measure G).IsInvInvariant
  body: by ext s hs; rw [count_apply hs, inv_apply, count_apply hs.inv, encard_inv]

中文:
实例 :
  签名: (count : 测度 G).是InvInvariant
  定义体: by ext s hs; rw [count_apply hs, inv_apply, count_apply hs.inv, encard_inv]

Depends on / 依赖: count_apply, encard_inv, hs.inv, inv_apply
-/
instance : (count : Measure G).IsInvInvariant where
  inv_eq_self := by ext s hs; rw [count_apply hs, inv_apply, count_apply hs.inv, encard_inv]

variable [MeasurableMul G]

@[to_additive]
/--
theorem `map_div_left_ae` / 定理 `map_div_left_ae`

English:
theorem map_div_left_ae
  given: (μ : Measure G) [IsMulLeftInvariant μ] [IsInvInvariant μ] (x : G)
  proof: ((MeasurableEquiv.divLeft x).map_ae μ).trans congr_arg ae map_div_left_eq_self μ x

中文:
定理 map_div_left_ae
  条件: (μ : 测度 G) [是MulLeftInvariant μ] [是InvInvariant μ] (x : G)
  证明: ((MeasurableEquiv.divLeft x).map_ae μ).trans congr_arg ae map_div_left_eq_self μ x

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.divLeft, congr_arg, divLeft, map_ae, map_div_left_eq_self
-/
theorem map_div_left_ae (μ : Measure G) [IsMulLeftInvariant μ] [IsInvInvariant μ] (x : G) :
    Filter.map (fun t => x / t) (ae μ) = ae μ :=
((MeasurableEquiv.divLeft x).map_ae μ).trans congr_arg ae map_div_left_eq_self μ x

end Group

end Measure

section IsTopologicalGroup

variable [TopologicalSpace G] [BorelSpace G] {μ : Measure G} [Group G]

@[to_additive]
/--
Instance `Measure.IsFiniteMeasureOnCompacts.inv` / 实例 `Measure.IsFiniteMeasureOnCompacts.inv`

English:
instance Measure.IsFiniteMeasureOnCompacts.inv
  signature: [ContinuousInv G] [IsFiniteMeasureOnCompacts μ]
  body: IsFiniteMeasureOnCompacts.map μ (Homeomorph.inv G)

@[to_additive]

中文:
实例 测度.紧集上有限测度.inv
  签名: [连续取逆 G] [紧集上有限测度 μ]
  定义体: IsFiniteMeasureOnCompacts.map μ (Homeomorph.inv G)

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.inv, IsFiniteMeasureOnCompacts, IsFiniteMeasureOnCompacts.map
-/
instance Measure.IsFiniteMeasureOnCompacts.inv [ContinuousInv G] [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts μ.inv :=
  IsFiniteMeasureOnCompacts.map μ (Homeomorph.inv G)

@[to_additive]
/--
Instance `Measure.IsOpenPosMeasure.inv` / 实例 `Measure.IsOpenPosMeasure.inv`

English:
instance Measure.IsOpenPosMeasure.inv
  signature: [ContinuousInv G] [IsOpenPosMeasure μ]
  body: (Homeomorph.inv G).continuous.isOpenPosMeasure_map (Homeomorph.inv G).surjective

@[to_additive]

中文:
实例 测度.是OpenPosMeasure.inv
  签名: [连续取逆 G] [是OpenPosMeasure μ]
  定义体: (Homeomorph.inv G).continuous.isOpenPosMeasure_map (Homeomorph.inv G).surjective

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.inv, continuous, continuous.isOpenPosMeasure_map, isOpenPosMeasure_map, surjective
-/
instance Measure.IsOpenPosMeasure.inv [ContinuousInv G] [IsOpenPosMeasure μ] :
    IsOpenPosMeasure μ.inv :=
  (Homeomorph.inv G).continuous.isOpenPosMeasure_map (Homeomorph.inv G).surjective

@[to_additive]
/--
Instance `Measure.Regular.inv` / 实例 `Measure.Regular.inv`

English:
instance Measure.Regular.inv
  signature: [ContinuousInv G] [Regular μ]
  body: Regular.map (Homeomorph.inv G)

@[to_additive]

中文:
实例 测度.正则.inv
  签名: [连续取逆 G] [正则 μ]
  定义体: Regular.map (Homeomorph.inv G)

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.inv, Regular, Regular.map
-/
instance Measure.Regular.inv [ContinuousInv G] [Regular μ] : Regular μ.inv :=
  Regular.map (Homeomorph.inv G)

@[to_additive]
/--
Instance `Measure.InnerRegular.inv` / 实例 `Measure.InnerRegular.inv`

English:
instance Measure.InnerRegular.inv
  signature: [ContinuousInv G] [InnerRegular μ]
  body: InnerRegular.map (Homeomorph.inv G)

中文:
实例 测度.内正则.inv
  签名: [连续取逆 G] [内正则 μ]
  定义体: InnerRegular.map (Homeomorph.inv G)

Depends on / 依赖: Homeomorph, Homeomorph.inv, InnerRegular, InnerRegular.map
-/
instance Measure.InnerRegular.inv [ContinuousInv G] [InnerRegular μ] : InnerRegular μ.inv :=
  InnerRegular.map (Homeomorph.inv G)

/-- The image of an inner regular measure under map of a left action is again inner regular. -/
@[to_additive
/-- The image of an inner regular measure under map of a left additive action is again
inner regular -/]
/--
Instance `innerRegular_map_smul` / 实例 `innerRegular_map_smul`

English:
instance innerRegular_map_smul
  signature: {α} [Monoid α] [MulAction α G] [ContinuousConstSMul α G]
  body: InnerRegular.map_of_continuous (continuous_const_smul a)

中文:
实例 innerRegular_map_smul
  签名: {α} [幺半群 α] [乘法作用 α G] [连续常数标量乘法 α G]
  定义体: InnerRegular.map_of_continuous (continuous_const_smul a)

Depends on / 依赖: InnerRegular, InnerRegular.map_of_continuous, continuous_const_smul, map_of_continuous
-/
instance innerRegular_map_smul {α} [Monoid α] [MulAction α G] [ContinuousConstSMul α G]
    [InnerRegular μ] (a : α) : InnerRegular (Measure.map (a • · : G -> G) μ) :=
  InnerRegular.map_of_continuous (continuous_const_smul a)

/-- The image of an inner regular measure under left multiplication is again inner regular. -/
@[to_additive
/-- The image of an inner regular measure under left addition is again inner regular. -/]
/--
Instance `innerRegular_map_mul_left` / 实例 `innerRegular_map_mul_left`

English:
instance innerRegular_map_mul_left
  signature: [IsTopologicalGroup G] [InnerRegular μ] (g : G)
  body: InnerRegular.map_of_continuous (continuous_const_mul g)

中文:
实例 innerRegular_map_mul_left
  签名: [是拓扑群 G] [内正则 μ] (g : G)
  定义体: InnerRegular.map_of_continuous (continuous_const_mul g)

Depends on / 依赖: InnerRegular, InnerRegular.map_of_continuous, continuous_const_mul, map_of_continuous
-/
instance innerRegular_map_mul_left [IsTopologicalGroup G] [InnerRegular μ] (g : G) :
    InnerRegular (Measure.map (g * ·) μ) := InnerRegular.map_of_continuous (continuous_const_mul g)

/-- The image of an inner regular measure under right multiplication is again inner regular. -/
@[to_additive
/-- The image of an inner regular measure under right addition is again inner regular. -/]
/--
Instance `innerRegular_map_mul_right` / 实例 `innerRegular_map_mul_right`

English:
instance innerRegular_map_mul_right
  signature: [IsTopologicalGroup G] [InnerRegular μ] (g : G)
  body: InnerRegular.map_of_continuous (continuous_mul_const g)

中文:
实例 innerRegular_map_mul_right
  签名: [是拓扑群 G] [内正则 μ] (g : G)
  定义体: InnerRegular.map_of_continuous (continuous_mul_const g)

Depends on / 依赖: InnerRegular, InnerRegular.map_of_continuous, continuous_mul_const, map_of_continuous
-/
instance innerRegular_map_mul_right [IsTopologicalGroup G] [InnerRegular μ] (g : G) :
    InnerRegular (Measure.map (· * g) μ) := InnerRegular.map_of_continuous (continuous_mul_const g)

variable [IsTopologicalGroup G]

@[to_additive]
/--
theorem `regular_inv_iff` / 定理 `regular_inv_iff`

English:
theorem regular_inv_iff
  statement: μ.inv.Regular ↔ μ.Regular
  proof: Regular.map_iff (Homeomorph.inv G)

@[to_additive]

中文:
定理 regular_inv_iff
  结论: μ.inv.正则 ↔ μ.正则
  证明: Regular.map_iff (Homeomorph.inv G)

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.inv, Regular, Regular.map_iff, map_iff
-/
theorem regular_inv_iff : μ.inv.Regular ↔ μ.Regular :=
  Regular.map_iff (Homeomorph.inv G)

@[to_additive]
/--
theorem `innerRegular_inv_iff` / 定理 `innerRegular_inv_iff`

English:
theorem innerRegular_inv_iff
  statement: μ.inv.InnerRegular ↔ μ.InnerRegular
  proof: InnerRegular.map_iff (Homeomorph.inv G)

中文:
定理 innerRegular_inv_iff
  结论: μ.inv.内正则 ↔ μ.内正则
  证明: InnerRegular.map_iff (Homeomorph.inv G)

Depends on / 依赖: Homeomorph, Homeomorph.inv, InnerRegular, InnerRegular.map_iff, map_iff
-/
theorem innerRegular_inv_iff : μ.inv.InnerRegular ↔ μ.InnerRegular :=
  InnerRegular.map_iff (Homeomorph.inv G)

/-- Continuity of the measure of translates of a compact set: Given a compact set `k` in a
topological group, for `g` close enough to the origin, `μ (g • k \ k)` is arbitrarily small. -/
@[to_additive /-- Continuity of the measure of translates of a compact set: Given a compact set `k`
in an additive topological group, for `g` close enough to the origin, `μ (g +ᵥ k \ k)` is
arbitrarily small. -/]
/--
lemma `eventually_nhds_one_measure_smul_sdiff_lt` / 引理 `eventually_nhds_one_measure_smul_sdiff_lt`

English:
lemma eventually_nhds_one_measure_smul_sdiff_lt
  statement: [LocallyCompactSpace G]
  proof: by
  obtain ⟨U, hUk, hU, hμUk⟩ : exists (U : Set G), k subseteq U ∧ IsOpen U ∧ μ U < μ k + ε :=
    hk.exists_isOpen_lt_add hε
  obtain ⟨V, hV1, hVkU⟩ : exists V in 𝓝 (1 : G), V * k subseteq U := compact_open_separated_mul_left hk hU hUk
  filter_upwards [hV1] with g hg
  calc
    μ (g • k \ k) <= μ (U \ k) := by
      gcongr
      exact (smul_set_subset_smul hg).trans hVkU
    _ < ε := measure_sdiff_lt_of_lt_add h'k.nullMeasurableSet hUk hk.measure_lt_top.ne hμUk

@[deprecated (since := "2026-06-03")]
alias eventually_nhds_one_measure_smul_diff_lt := eventually_nhds_one_measure_smul_sdiff_lt

中文:
引理 eventually_nhds_one_measure_smul_sdiff_lt
  结论: [局部紧空间 G]
  证明: by
  obtain ⟨U, hUk, hU, hμUk⟩ : exists (U : Set G), k subseteq U ∧ IsOpen U ∧ μ U < μ k + ε :=
    hk.exists_isOpen_lt_add hε
  obtain ⟨V, hV1, hVkU⟩ : exists V in 𝓝 (1 : G), V * k subseteq U := compact_open_separated_mul_left hk hU hUk
  filter_upwards [hV1] with g hg
  calc
    μ (g • k \ k) <= μ (U \ k) := by
      gcongr
      exact (smul_set_subset_smul hg).trans hVkU
    _ < ε := measure_sdiff_lt_of_lt_add h'k.nullMeasurableSet hUk hk.measure_lt_top.ne hμUk

@[deprecated (since := "2026-06-03")]
alias eventually_nhds_one_measure_smul_diff_lt := eventually_nhds_one_measure_smul_sdiff_lt

Depends on / 依赖: IsOpen, compact_open_separated_mul_left, exists_isOpen_lt_add, filter_upwards, hk.exists_isOpen_lt_add, hk.measure_lt_top.ne, k.nullMeasurableSet, measure_lt_top, measure_sdiff_lt_of_lt_add, nullMeasurableSet, smul_set_subset_smul, subseteq
-/
lemma eventually_nhds_one_measure_smul_sdiff_lt [LocallyCompactSpace G]
    [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ] {k : Set G}
    (hk : IsCompact k) (h'k : IsClosed k) {ε : Real>=0∞} (hε : ε != 0) :
    forallᶠ g in 𝓝 (1 : G), μ (g • k \ k) < ε := by
  obtain ⟨U, hUk, hU, hμUk⟩ : exists (U : Set G), k subseteq U ∧ IsOpen U ∧ μ U < μ k + ε :=
    hk.exists_isOpen_lt_add hε
  obtain ⟨V, hV1, hVkU⟩ : exists V in 𝓝 (1 : G), V * k subseteq U := compact_open_separated_mul_left hk hU hUk
  filter_upwards [hV1] with g hg
  calc
    μ (g • k \ k) <= μ (U \ k) := by
      gcongr
      exact (smul_set_subset_smul hg).trans hVkU
    _ < ε := measure_sdiff_lt_of_lt_add h'k.nullMeasurableSet hUk hk.measure_lt_top.ne hμUk

@[deprecated (since := "2026-06-03")]
alias eventually_nhds_one_measure_smul_diff_lt := eventually_nhds_one_measure_smul_sdiff_lt

/-- Continuity of the measure of translates of a compact set:
Given a closed compact set `k` in a topological group,
the measure of `g • k \ k` tends to zero as `g` tends to `1`. -/
@[to_additive /-- Continuity of the measure of translates of a compact set:
Given a closed compact set `k` in an additive topological group,
the measure of `g +ᵥ k \ k` tends to zero as `g` tends to `0`. -/]
/--
lemma `tendsto_measure_smul_sdiff_isCompact_isClosed` / 引理 `tendsto_measure_smul_sdiff_isCompact_isClosed`

English:
lemma tendsto_measure_smul_sdiff_isCompact_isClosed
  statement: [LocallyCompactSpace G]
  proof: ENNReal.nhds_zero_basis.tendsto_right_iff.mpr fun _ h =>
    eventually_nhds_one_measure_smul_sdiff_lt hk h'k h.ne'

@[deprecated (since := "2026-06-03")]
alias tendsto_measure_smul_diff_isCompact_isClosed := tendsto_measure_smul_sdiff_isCompact_isClosed

中文:
引理 tendsto_measure_smul_sdiff_isCompact_isClosed
  结论: [局部紧空间 G]
  证明: ENNReal.nhds_zero_basis.tendsto_right_iff.mpr fun _ h =>
    eventually_nhds_one_measure_smul_sdiff_lt hk h'k h.ne'

@[deprecated (since := "2026-06-03")]
alias tendsto_measure_smul_diff_isCompact_isClosed := tendsto_measure_smul_sdiff_isCompact_isClosed

Depends on / 依赖: ENNReal, ENNReal.nhds_zero_basis.tendsto_right_iff.mpr, eventually_nhds_one_measure_smul_sdiff_lt, h.ne, nhds_zero_basis, tendsto_right_iff
-/
lemma tendsto_measure_smul_sdiff_isCompact_isClosed [LocallyCompactSpace G]
    [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ] {k : Set G}
    (hk : IsCompact k) (h'k : IsClosed k) :
    Tendsto (fun g : G => μ (g • k \ k)) (𝓝 1) (𝓝 0) :=
ENNReal.nhds_zero_basis.tendsto_right_iff.mpr fun _ h =>
    eventually_nhds_one_measure_smul_sdiff_lt hk h'k h.ne'

@[deprecated (since := "2026-06-03")]
alias tendsto_measure_smul_diff_isCompact_isClosed := tendsto_measure_smul_sdiff_isCompact_isClosed

section IsMulLeftInvariant
variable [IsMulLeftInvariant μ]

/-- If a left-invariant measure gives positive mass to a compact set, then it gives positive mass to
any open set. -/
@[to_additive
/-- If a left-invariant measure gives positive mass to a compact set, then it gives positive mass to
any open set. -/]
/--
theorem `isOpenPosMeasure_of_mulLeftInvariant_of_compact` / 定理 `isOpenPosMeasure_of_mulLeftInvariant_of_compact`

English:
theorem isOpenPosMeasure_of_mulLeftInvariant_of_compact
  statement: (K : Set G) (hK : IsCompact K)
  proof: by
  refine ⟨fun U hU hne => ?_⟩
  contrapose h
  rw [← nonpos_iff_eq_zero]
  rw [← hU.interior_eq] at hne
  obtain ⟨t, hKt⟩ : exists t : Finset G, K subseteq ⋃ (g : G) (_ : g in t), (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK hne
  calc
    μ K <= μ (⋃ (g : G) (_ : g in t), (fun h : G => g * h) ⁻¹' U) := measure_mono hKt
    _ <= ∑ g in t, μ ((fun h : G => g * h) ⁻¹' U) := measure_biUnion_finset_le _ _
    _ = 0 := by simp [measure_preimage_mul, h]

中文:
定理 isOpenPosMeasure_of_mulLeftInvariant_of_compact
  结论: (K : 集合 G) (hK : 是紧集 K)
  证明: by
  refine ⟨fun U hU hne => ?_⟩
  contrapose h
  rw [← nonpos_iff_eq_zero]
  rw [← hU.interior_eq] at hne
  obtain ⟨t, hKt⟩ : exists t : Finset G, K subseteq ⋃ (g : G) (_ : g in t), (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK hne
  calc
    μ K <= μ (⋃ (g : G) (_ : g in t), (fun h : G => g * h) ⁻¹' U) := measure_mono hKt
    _ <= ∑ g in t, μ ((fun h : G => g * h) ⁻¹' U) := measure_biUnion_finset_le _ _
    _ = 0 := by simp [measure_preimage_mul, h]

Depends on / 依赖: Finset, compact_covered_by_mul_left_translates, contrapose, hU.interior_eq, interior_eq, measure_biUnion_finset_le, measure_mono, measure_preimage_mul, nonpos_iff_eq_zero, subseteq
-/
theorem isOpenPosMeasure_of_mulLeftInvariant_of_compact (K : Set G) (hK : IsCompact K)
    (h : μ K != 0) : IsOpenPosMeasure μ := by
  refine ⟨fun U hU hne => ?_⟩
  contrapose h
  rw [← nonpos_iff_eq_zero]
  rw [← hU.interior_eq] at hne
  obtain ⟨t, hKt⟩ : exists t : Finset G, K subseteq ⋃ (g : G) (_ : g in t), (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK hne
  calc
    μ K <= μ (⋃ (g : G) (_ : g in t), (fun h : G => g * h) ⁻¹' U) := measure_mono hKt
    _ <= ∑ g in t, μ ((fun h : G => g * h) ⁻¹' U) := measure_biUnion_finset_le _ _
    _ = 0 := by simp [measure_preimage_mul, h]

/-- A nonzero left-invariant regular measure gives positive mass to any open set. -/
@[to_additive /-- A nonzero left-invariant regular measure gives positive mass to any open set. -/]
instance (priority := 80) isOpenPosMeasure_of_mulLeftInvariant_of_regular [Regular μ] [NeZero μ] :
    IsOpenPosMeasure μ :=
  let ⟨K, hK, h2K⟩ := Regular.exists_isCompact_not_null.mpr (NeZero.ne μ)
  isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK h2K

/-- A nonzero left-invariant inner regular measure gives positive mass to any open set. -/
@[to_additive
/-- A nonzero left-invariant inner regular measure gives positive mass to any open set. -/]
instance (priority := 80) isOpenPosMeasure_of_mulLeftInvariant_of_innerRegular
    [InnerRegular μ] [NeZero μ] :
    IsOpenPosMeasure μ :=
  let ⟨K, hK, h2K⟩ := InnerRegular.exists_isCompact_not_null.mpr (NeZero.ne μ)
  isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK h2K

@[to_additive]
/--
theorem `null_iff_of_isMulLeftInvariant` / 定理 `null_iff_of_isMulLeftInvariant`

English:
theorem null_iff_of_isMulLeftInvariant
  given: [Regular μ] {s : Set G} (hs : IsOpen s)
  proof: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp only [or_false, hs.measure_eq_zero_iff μ, NeZero.ne μ]

@[to_additive]

中文:
定理 null_iff_of_isMulLeftInvariant
  条件: [正则 μ] {s : 集合 G} (hs : 是开集 s)
  证明: by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp only [or_false, hs.measure_eq_zero_iff μ, NeZero.ne μ]

@[to_additive]

Depends on / 依赖: NeZero, NeZero.ne, eq_zero_or_neZero, hs.measure_eq_zero_iff, measure_eq_zero_iff, or_false
-/
theorem null_iff_of_isMulLeftInvariant [Regular μ] {s : Set G} (hs : IsOpen s) :
    μ s = 0 ↔ s = ∅ ∨ μ = 0 := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp only [or_false, hs.measure_eq_zero_iff μ, NeZero.ne μ]

@[to_additive]
/--
theorem `measure_ne_zero_iff_nonempty_of_isMulLeftInvariant` / 定理 `measure_ne_zero_iff_nonempty_of_isMulLeftInvariant`

English:
theorem measure_ne_zero_iff_nonempty_of_isMulLeftInvariant
  statement: [Regular μ] (hμ : μ != 0) {s : Set G}
  proof: by
  simpa [null_iff_of_isMulLeftInvariant (μ := μ) hs, hμ] using nonempty_iff_ne_empty.symm

@[to_additive]

中文:
定理 measure_ne_zero_iff_nonempty_of_isMulLeftInvariant
  结论: [正则 μ] (hμ : μ != 0) {s : 集合 G}
  证明: by
  simpa [null_iff_of_isMulLeftInvariant (μ := μ) hs, hμ] using nonempty_iff_ne_empty.symm

@[to_additive]

Depends on / 依赖: nonempty_iff_ne_empty, nonempty_iff_ne_empty.symm, null_iff_of_isMulLeftInvariant
-/
theorem measure_ne_zero_iff_nonempty_of_isMulLeftInvariant [Regular μ] (hμ : μ != 0) {s : Set G}
    (hs : IsOpen s) : μ s != 0 ↔ s.Nonempty := by
  simpa [null_iff_of_isMulLeftInvariant (μ := μ) hs, hμ] using nonempty_iff_ne_empty.symm

@[to_additive]
/--
theorem `measure_pos_iff_nonempty_of_isMulLeftInvariant` / 定理 `measure_pos_iff_nonempty_of_isMulLeftInvariant`

English:
theorem measure_pos_iff_nonempty_of_isMulLeftInvariant
  statement: [Regular μ] (h3μ : μ != 0) {s : Set G}
  proof: pos_iff_ne_zero.trans measure_ne_zero_iff_nonempty_of_isMulLeftInvariant h3μ hs

中文:
定理 measure_pos_iff_nonempty_of_isMulLeftInvariant
  结论: [正则 μ] (h3μ : μ != 0) {s : 集合 G}
  证明: pos_iff_ne_zero.trans measure_ne_zero_iff_nonempty_of_isMulLeftInvariant h3μ hs

Depends on / 依赖: measure_ne_zero_iff_nonempty_of_isMulLeftInvariant, pos_iff_ne_zero, pos_iff_ne_zero.trans
-/
theorem measure_pos_iff_nonempty_of_isMulLeftInvariant [Regular μ] (h3μ : μ != 0) {s : Set G}
    (hs : IsOpen s) : 0 < μ s ↔ s.Nonempty :=
pos_iff_ne_zero.trans measure_ne_zero_iff_nonempty_of_isMulLeftInvariant h3μ hs

/-- If a left-invariant measure gives finite mass to a nonempty open set, then it gives finite mass
to any compact set. -/
@[to_additive
/-- If a left-invariant measure gives finite mass to a nonempty open set, then it gives finite mass
to any compact set. -/]
/--
theorem `measure_lt_top_of_isCompact_of_isMulLeftInvariant` / 定理 `measure_lt_top_of_isCompact_of_isMulLeftInvariant`

English:
theorem measure_lt_top_of_isCompact_of_isMulLeftInvariant
  statement: (U : Set G) (hU : IsOpen U)
  proof: by
  rw [← hU.interior_eq] at h'U
  obtain ⟨t, hKt⟩ : exists t : Finset G, K subseteq ⋃ g in t, (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK h'U
exact (measure_mono hKt).trans_lt measure_biUnion_lt_top t.finite_toSet by simp [h.lt_top]

中文:
定理 measure_lt_top_of_isCompact_of_isMulLeftInvariant
  结论: (U : 集合 G) (hU : 是开集 U)
  证明: by
  rw [← hU.interior_eq] at h'U
  obtain ⟨t, hKt⟩ : exists t : Finset G, K subseteq ⋃ g in t, (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK h'U
exact (measure_mono hKt).trans_lt measure_biUnion_lt_top t.finite_toSet by simp [h.lt_top]

Depends on / 依赖: Finset, compact_covered_by_mul_left_translates, finite_toSet, h.lt_top, hU.interior_eq, interior_eq, lt_top, measure_biUnion_lt_top, measure_mono, subseteq, t.finite_toSet, trans_lt
-/
theorem measure_lt_top_of_isCompact_of_isMulLeftInvariant (U : Set G) (hU : IsOpen U)
    (h'U : U.Nonempty) (h : μ U != ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞ := by
  rw [← hU.interior_eq] at h'U
  obtain ⟨t, hKt⟩ : exists t : Finset G, K subseteq ⋃ g in t, (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK h'U
exact (measure_mono hKt).trans_lt measure_biUnion_lt_top t.finite_toSet by simp [h.lt_top]

/-- If a left-invariant measure gives finite mass to a set with nonempty interior, then
it gives finite mass to any compact set. -/
@[to_additive
/-- If a left-invariant measure gives finite mass to a set with nonempty interior, then it gives
finite mass to any compact set. -/]
/--
theorem `measure_lt_top_of_isCompact_of_isMulLeftInvariant'` / 定理 `measure_lt_top_of_isCompact_of_isMulLeftInvariant'`

English:
theorem measure_lt_top_of_isCompact_of_isMulLeftInvariant'
  statement: {U : Set G}
  proof: measure_lt_top_of_isCompact_of_isMulLeftInvariant (interior U) isOpen_interior hU
    ((measure_mono interior_subset).trans_lt (lt_top_iff_ne_top.2 h)).ne hK

中文:
定理 measure_lt_top_of_isCompact_of_isMulLeftInvariant'
  结论: {U : 集合 G}
  证明: measure_lt_top_of_isCompact_of_isMulLeftInvariant (interior U) isOpen_interior hU
    ((measure_mono interior_subset).trans_lt (lt_top_iff_ne_top.2 h)).ne hK

Depends on / 依赖: interior, interior_subset, isOpen_interior, lt_top_iff_ne_top, measure_lt_top_of_isCompact_of_isMulLeftInvariant, measure_mono, trans_lt
-/
theorem measure_lt_top_of_isCompact_of_isMulLeftInvariant' {U : Set G}
    (hU : (interior U).Nonempty) (h : μ U != ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞ :=
  measure_lt_top_of_isCompact_of_isMulLeftInvariant (interior U) isOpen_interior hU
    ((measure_mono interior_subset).trans_lt (lt_top_iff_ne_top.2 h)).ne hK

/-- In a noncompact locally compact group, a left-invariant measure which is positive
on open sets has infinite mass. -/
@[to_additive (attr := simp)
/-- In a noncompact locally compact additive group, a left-invariant measure which is positive on
open sets has infinite mass. -/]
/--
theorem `measure_univ_of_isMulLeftInvariant` / 定理 `measure_univ_of_isMulLeftInvariant`

English:
theorem measure_univ_of_isMulLeftInvariant
  statement: [WeaklyLocallyCompactSpace G] [NoncompactSpace G]
  proof: by
  /- Consider a closed compact set `K` with nonempty interior. For any compact set `L`, one may
    find `g = g (L)` such that `L` is disjoint from `g • K`. Iterating this, one finds
    infinitely many translates of `K` which are disjoint from each other. As they all have the
    same positive mass, it follows that the space has infinite measure. -/
  obtain ⟨K, K1, hK, Kclosed⟩ : exists K in 𝓝 (1 : G), IsCompact K ∧ IsClosed K :=
    exists_mem_nhds_isCompact_isClosed 1
  have K_pos : 0 < μ K := measure_pos_of_mem_nhds μ K1
  have A : forall L : Set G, IsCompact L -> exists g : G, Disjoint L (g • K) := fun L hL =>
    exists_disjoint_smul_of_isCompact hL hK
  choose! g hg using A
  set L : Nat -> Set G := fun n => (fun T => T union g T • K)^[n] K
  have Lcompact : forall n, IsCompact (L n) := fun n => by
    induction n with
    | zero => exact hK
    | succ n IH =>
      simp_rw [L, iterate_succ']
      apply IsCompact.union IH (hK.smul (g (L n)))
  have Lclosed : forall n, IsClosed (L n) := fun n => by
    induction n with
    | zero => exact Kclosed
    | succ n IH =>
      simp_rw [L, iterate_succ']
      apply IsClosed.union IH (Kclosed.smul (g (L n)))
  have M : forall n, μ (L n) = (n + 1 : Nat) * μ K := fun n => by
    induction n with
    | zero => simp only [L, one_mul, Nat.cast_one, iterate_zero, id, Nat.zero_add]
    | succ n IH =>
      calc
        μ (L (n + 1)) = μ (L n) + μ (g (L n) • K) := by
          simp_rw [L, iterate_succ']
          exact measure_union' (hg _ (Lcompact _)) (Lclosed _).measurableSet
        _ = (n + 1 + 1 : Nat) * μ K := by
          simp only [IH, measure_smul, add_mul, Nat.cast_add, Nat.cast_one, one_mul]
  have N : Tendsto (fun n => μ (L n)) atTop (𝓝 (∞ * μ K)) := by
    simp_rw [M]
    apply ENNReal.Tendsto.mul_const _ (Or.inl ENNReal.top_ne_zero)
    exact ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat _)
  simp only [ENNReal.top_mul', K_pos.ne', if_false] at N
  apply top_le_iff.1
  exact le_of_tendsto' N fun n => measure_mono (subset_univ _)

@[to_additive]

中文:
定理 measure_univ_of_isMulLeftInvariant
  结论: [WeaklyLocallyCompact空间 G] [Noncompact空间 G]
  证明: by
  /- Consider a closed compact set `K` with nonempty interior. For any compact set `L`, one may
    find `g = g (L)` such that `L` is disjoint from `g • K`. Iterating this, one finds
    infinitely many translates of `K` which are disjoint from each other. As they all have the
    same positive mass, it follows that the space has infinite measure. -/
  obtain ⟨K, K1, hK, Kclosed⟩ : exists K in 𝓝 (1 : G), IsCompact K ∧ IsClosed K :=
    exists_mem_nhds_isCompact_isClosed 1
  have K_pos : 0 < μ K := measure_pos_of_mem_nhds μ K1
  have A : forall L : Set G, IsCompact L -> exists g : G, Disjoint L (g • K) := fun L hL =>
    exists_disjoint_smul_of_isCompact hL hK
  choose! g hg using A
  set L : Nat -> Set G := fun n => (fun T => T union g T • K)^[n] K
  have Lcompact : forall n, IsCompact (L n) := fun n => by
    induction n with
    | zero => exact hK
    | succ n IH =>
      simp_rw [L, iterate_succ']
      apply IsCompact.union IH (hK.smul (g (L n)))
  have Lclosed : forall n, IsClosed (L n) := fun n => by
    induction n with
    | zero => exact Kclosed
    | succ n IH =>
      simp_rw [L, iterate_succ']
      apply IsClosed.union IH (Kclosed.smul (g (L n)))
  have M : forall n, μ (L n) = (n + 1 : Nat) * μ K := fun n => by
    induction n with
    | zero => simp only [L, one_mul, Nat.cast_one, iterate_zero, id, Nat.zero_add]
    | succ n IH =>
      calc
        μ (L (n + 1)) = μ (L n) + μ (g (L n) • K) := by
          simp_rw [L, iterate_succ']
          exact measure_union' (hg _ (Lcompact _)) (Lclosed _).measurableSet
        _ = (n + 1 + 1 : Nat) * μ K := by
          simp only [IH, measure_smul, add_mul, Nat.cast_add, Nat.cast_one, one_mul]
  have N : Tendsto (fun n => μ (L n)) atTop (𝓝 (∞ * μ K)) := by
    simp_rw [M]
    apply ENNReal.Tendsto.mul_const _ (Or.inl ENNReal.top_ne_zero)
    exact ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat _)
  simp only [ENNReal.top_mul', K_pos.ne', if_false] at N
  apply top_le_iff.1
  exact le_of_tendsto' N fun n => measure_mono (subset_univ _)

@[to_additive]
-/
theorem measure_univ_of_isMulLeftInvariant [WeaklyLocallyCompactSpace G] [NoncompactSpace G]
    (μ : Measure G) [IsOpenPosMeasure μ] [μ.IsMulLeftInvariant] : μ univ = ∞ := by
  /- Consider a closed compact set `K` with nonempty interior. For any compact set `L`, one may
    find `g = g (L)` such that `L` is disjoint from `g • K`. Iterating this, one finds
    infinitely many translates of `K` which are disjoint from each other. As they all have the
    same positive mass, it follows that the space has infinite measure. -/
  obtain ⟨K, K1, hK, Kclosed⟩ : exists K in 𝓝 (1 : G), IsCompact K ∧ IsClosed K :=
    exists_mem_nhds_isCompact_isClosed 1
  have K_pos : 0 < μ K := measure_pos_of_mem_nhds μ K1
  have A : forall L : Set G, IsCompact L -> exists g : G, Disjoint L (g • K) := fun L hL =>
    exists_disjoint_smul_of_isCompact hL hK
  choose! g hg using A
  set L : Nat -> Set G := fun n => (fun T => T union g T • K)^[n] K
  have Lcompact : forall n, IsCompact (L n) := fun n => by
    induction n with
    | zero => exact hK
    | succ n IH =>
      simp_rw [L, iterate_succ']
      apply IsCompact.union IH (hK.smul (g (L n)))
  have Lclosed : forall n, IsClosed (L n) := fun n => by
    induction n with
    | zero => exact Kclosed
    | succ n IH =>
      simp_rw [L, iterate_succ']
      apply IsClosed.union IH (Kclosed.smul (g (L n)))
  have M : forall n, μ (L n) = (n + 1 : Nat) * μ K := fun n => by
    induction n with
    | zero => simp only [L, one_mul, Nat.cast_one, iterate_zero, id, Nat.zero_add]
    | succ n IH =>
      calc
        μ (L (n + 1)) = μ (L n) + μ (g (L n) • K) := by
          simp_rw [L, iterate_succ']
          exact measure_union' (hg _ (Lcompact _)) (Lclosed _).measurableSet
        _ = (n + 1 + 1 : Nat) * μ K := by
          simp only [IH, measure_smul, add_mul, Nat.cast_add, Nat.cast_one, one_mul]
  have N : Tendsto (fun n => μ (L n)) atTop (𝓝 (∞ * μ K)) := by
    simp_rw [M]
    apply ENNReal.Tendsto.mul_const _ (Or.inl ENNReal.top_ne_zero)
    exact ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat _)
  simp only [ENNReal.top_mul', K_pos.ne', if_false] at N
  apply top_le_iff.1
  exact le_of_tendsto' N fun n => measure_mono (subset_univ _)

@[to_additive]
/--
lemma `_root_.MeasurableSet.mul_closure_one_eq` / 引理 `_root_.MeasurableSet.mul_closure_one_eq`

English:
lemma _root_.MeasurableSet.mul_closure_one_eq
  given: {s : Set G} (hs : MeasurableSet s)
  proof: by
  induction s, hs using MeasurableSet.induction_on_open with
  | isOpen U hU => exact hU.mul_closure_one_eq
  | compl t _ iht => exact compl_mul_closure_one_eq_iff.2 iht
  | iUnion f _ _ ihf => simp_rw [iUnion_mul f, ihf]

@[to_additive (attr := simp)]

中文:
引理 _root_.可测集.mul_closure_one_eq
  条件: {s : 集合 G} (hs : 可测集 s)
  证明: by
  induction s, hs using MeasurableSet.induction_on_open with
  | isOpen U hU => exact hU.mul_closure_one_eq
  | compl t _ iht => exact compl_mul_closure_one_eq_iff.2 iht
  | iUnion f _ _ ihf => simp_rw [iUnion_mul f, ihf]

@[to_additive (attr := simp)]

Depends on / 依赖: MeasurableSet, MeasurableSet.induction_on_open, compl_mul_closure_one_eq_iff, hU.mul_closure_one_eq, iUnion, iUnion_mul, induction_on_open, isOpen, mul_closure_one_eq, simp_rw
-/
lemma _root_.MeasurableSet.mul_closure_one_eq {s : Set G} (hs : MeasurableSet s) :
    s * (closure {1} : Set G) = s := by
  induction s, hs using MeasurableSet.induction_on_open with
  | isOpen U hU => exact hU.mul_closure_one_eq
  | compl t _ iht => exact compl_mul_closure_one_eq_iff.2 iht
  | iUnion f _ _ ihf => simp_rw [iUnion_mul f, ihf]

@[to_additive (attr := simp)]
/--
lemma `measure_mul_closure_one` / 引理 `measure_mul_closure_one`

English:
lemma measure_mul_closure_one
  given: (s : Set G) (μ : Measure G)
  proof: by
  apply le_antisymm ?_ (measure_mono (subset_mul_closure_one s))
  conv_rhs => rw [measure_eq_iInf]
  simp only [le_iInf_iff]
  intro t kt t_meas
  apply measure_mono
  rw [← t_meas.mul_closure_one_eq]
  exact smul_subset_smul_right kt

中文:
引理 measure_mul_closure_one
  条件: (s : 集合 G) (μ : 测度 G)
  证明: by
  apply le_antisymm ?_ (measure_mono (subset_mul_closure_one s))
  conv_rhs => rw [measure_eq_iInf]
  simp only [le_iInf_iff]
  intro t kt t_meas
  apply measure_mono
  rw [← t_meas.mul_closure_one_eq]
  exact smul_subset_smul_right kt

Depends on / 依赖: conv_rhs, le_antisymm, le_iInf_iff, measure_eq_iInf, measure_mono, mul_closure_one_eq, smul_subset_smul_right, subset_mul_closure_one, t_meas, t_meas.mul_closure_one_eq
-/
lemma measure_mul_closure_one (s : Set G) (μ : Measure G) :
    μ (s * (closure {1} : Set G)) = μ s := by
  apply le_antisymm ?_ (measure_mono (subset_mul_closure_one s))
  conv_rhs => rw [measure_eq_iInf]
  simp only [le_iInf_iff]
  intro t kt t_meas
  apply measure_mono
  rw [← t_meas.mul_closure_one_eq]
  exact smul_subset_smul_right kt

end IsMulLeftInvariant

@[to_additive]
/--
lemma `innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group` / 引理 `innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group`

English:
lemma innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group
  given: [h : InnerRegularCompactLTTop μ]
  proof: by
  intro s ⟨s_meas, μs⟩ r hr
  rcases h.innerRegular ⟨s_meas, μs⟩ r hr with ⟨K, Ks, K_comp, hK⟩
  refine ⟨closure K, ?_, ⟨K_comp.closure, isClosed_closure⟩, ?_⟩
  · exact IsCompact.closure_subset_measurableSet K_comp s_meas Ks
  · rwa [K_comp.measure_closure]

中文:
引理 innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group
  条件: [h : InnerRegularCompactLTTop μ]
  证明: by
  intro s ⟨s_meas, μs⟩ r hr
  rcases h.innerRegular ⟨s_meas, μs⟩ r hr with ⟨K, Ks, K_comp, hK⟩
  refine ⟨closure K, ?_, ⟨K_comp.closure, isClosed_closure⟩, ?_⟩
  · exact IsCompact.closure_subset_measurableSet K_comp s_meas Ks
  · rwa [K_comp.measure_closure]

Depends on / 依赖: IsCompact, IsCompact.closure_subset_measurableSet, K_comp, K_comp.closure, K_comp.measure_closure, closure, closure_subset_measurableSet, h.innerRegular, innerRegular, isClosed_closure, measure_closure, s_meas
-/
lemma innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group [h : InnerRegularCompactLTTop μ] :
    InnerRegularWRT μ (fun s => IsCompact s ∧ IsClosed s) (fun s => MeasurableSet s ∧ μ s != ∞) := by
  intro s ⟨s_meas, μs⟩ r hr
  rcases h.innerRegular ⟨s_meas, μs⟩ r hr with ⟨K, Ks, K_comp, hK⟩
  refine ⟨closure K, ?_, ⟨K_comp.closure, isClosed_closure⟩, ?_⟩
  · exact IsCompact.closure_subset_measurableSet K_comp s_meas Ks
  · rwa [K_comp.measure_closure]

end IsTopologicalGroup

section CommSemigroup

variable [CommSemigroup G]

/-- In an abelian group every left invariant measure is also right-invariant.
  We don't declare the converse as an instance, since that would loop type-class inference, and
  we use `IsMulLeftInvariant` as the default hypothesis in abelian groups. -/
@[to_additive IsAddLeftInvariant.isAddRightInvariant
/-- In an abelian additive group every left invariant measure is also right-invariant. We don't
declare the converse as an instance, since that would loop type-class inference, and we use
`IsAddLeftInvariant` as the default hypothesis in abelian groups. -/]
instance (priority := 100) IsMulLeftInvariant.isMulRightInvariant {μ : Measure G}
    [IsMulLeftInvariant μ] : IsMulRightInvariant μ :=
  ⟨fun g => by simp_rw [mul_comm, map_mul_left_eq_self]⟩

end CommSemigroup

section Haar

namespace Measure

/--
Definition of `IsAddHaarMeasure` / `IsAddHaarMeasure` 的定义

English:
class IsAddHaarMeasure
  parameters: {G : Type*} [AddGroup G] [TopologicalSpace G] [MeasurableSpace G]
  extends: IsFiniteMeasureOnCompacts μ, IsAddLeftInvariant μ, IsOpenPosMeasure μ
  (no additional axioms)

中文:
类 是加法Haar测度
  参数: {G : 类型} [加法群 G] [拓扑空间 G] [可测空间 G]
  继承: 紧集上有限测度 μ, 是加法左不变 μ, 是OpenPosMeasure μ
  (无附加公理)
-/
class IsAddHaarMeasure {G : Type*} [AddGroup G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) : Prop
    extends IsFiniteMeasureOnCompacts μ, IsAddLeftInvariant μ, IsOpenPosMeasure μ

/-- A measure on a group is a Haar measure if it is left-invariant, and gives finite mass to
compact sets and positive mass to open sets.

Textbooks generally require an additional regularity assumption to ensure nice behavior on
arbitrary locally compact groups. Use `[IsHaarMeasure μ] [Regular μ]` or
`[IsHaarMeasure μ] [InnerRegular μ]` in these situations. Note that a Haar measure in our
sense is automatically regular and inner regular on second countable locally compact groups, as
checked just below this definition. -/
@[to_additive existing]
/--
Definition of `IsHaarMeasure` / `IsHaarMeasure` 的定义

English:
class IsHaarMeasure
  parameters: {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  extends: IsFiniteMeasureOnCompacts μ, IsMulLeftInvariant μ, IsOpenPosMeasure μ
  (no additional axioms)

中文:
类 是Haar测度
  参数: {G : 类型} [群 G] [拓扑空间 G] [可测空间 G]
  继承: 紧集上有限测度 μ, 是MulLeftInvariant μ, 是OpenPosMeasure μ
  (无附加公理)
-/
class IsHaarMeasure {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) : Prop
    extends IsFiniteMeasureOnCompacts μ, IsMulLeftInvariant μ, IsOpenPosMeasure μ

variable [Group G] [TopologicalSpace G] (μ : Measure G) [IsHaarMeasure μ]

@[to_additive (attr := simp)]
/--
theorem `haar_singleton` / 定理 `haar_singleton`

English:
theorem haar_singleton
  given: [ContinuousMul G] [BorelSpace G] (g : G)
  statement: μ {g} = μ {(1 : G)}
  proof: by
  convert! measure_preimage_mul μ g⁻¹ _
  simp only [mul_one, preimage_mul_left_singleton, inv_inv]

@[to_additive IsAddHaarMeasure.smul]

中文:
定理 haar_singleton
  条件: [连续乘法 G] [Borel空间 G] (g : G)
  结论: μ {g} = μ {(1 : G)}
  证明: by
  convert! measure_preimage_mul μ g⁻¹ _
  simp only [mul_one, preimage_mul_left_singleton, inv_inv]

@[to_additive IsAddHaarMeasure.smul]

Depends on / 依赖: convert, inv_inv, measure_preimage_mul, mul_one, preimage_mul_left_singleton
-/
theorem haar_singleton [ContinuousMul G] [BorelSpace G] (g : G) : μ {g} = μ {(1 : G)} := by
  convert! measure_preimage_mul μ g⁻¹ _
  simp only [mul_one, preimage_mul_left_singleton, inv_inv]

@[to_additive IsAddHaarMeasure.smul]
/--
theorem `IsHaarMeasure.smul` / 定理 `IsHaarMeasure.smul`

English:
theorem IsHaarMeasure.smul
  given: {c : Real>=0∞} (cpos : c != 0) (ctop : c != ∞)
  statement: IsHaarMeasure (c • μ)
  proof: { lt_top_of_isCompact := fun _K hK => ENNReal.mul_lt_top ctop.lt_top hK.measure_lt_top
    toIsOpenPosMeasure := isOpenPosMeasure_smul μ cpos }

@[to_additive IsAddHaarMeasure.nnreal_smul]

中文:
定理 是Haar测度.smul
  条件: {c : 实数>=0∞} (cpos : c != 0) (ctop : c != ∞)
  结论: 是Haar测度 (c • μ)
  证明: { lt_top_of_isCompact := fun _K hK => ENNReal.mul_lt_top ctop.lt_top hK.measure_lt_top
    toIsOpenPosMeasure := isOpenPosMeasure_smul μ cpos }

@[to_additive IsAddHaarMeasure.nnreal_smul]

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, ctop.lt_top, hK.measure_lt_top, isOpenPosMeasure_smul, lt_top, lt_top_of_isCompact, measure_lt_top, mul_lt_top, toIsOpenPosMeasure
-/
theorem IsHaarMeasure.smul {c : Real>=0∞} (cpos : c != 0) (ctop : c != ∞) : IsHaarMeasure (c • μ) :=
  { lt_top_of_isCompact := fun _K hK => ENNReal.mul_lt_top ctop.lt_top hK.measure_lt_top
    toIsOpenPosMeasure := isOpenPosMeasure_smul μ cpos }

@[to_additive IsAddHaarMeasure.nnreal_smul]
/--
lemma `IsHaarMeasure.nnreal_smul` / 引理 `IsHaarMeasure.nnreal_smul`

English:
lemma IsHaarMeasure.nnreal_smul
  given: {c : Real>=0} (hc : c != 0)
  statement: IsHaarMeasure (c • μ)
  proof: .smul _ (by simp [hc]) (Option.some_ne_none _)

中文:
引理 是Haar测度.nnreal_smul
  条件: {c : 实数>=0} (hc : c != 0)
  结论: 是Haar测度 (c • μ)
  证明: .smul _ (by simp [hc]) (Option.some_ne_none _)

Depends on / 依赖: Option.some_ne_none, some_ne_none
-/
lemma IsHaarMeasure.nnreal_smul {c : Real>=0} (hc : c != 0) : IsHaarMeasure (c • μ) :=
  .smul _ (by simp [hc]) (Option.some_ne_none _)

/-- If a left-invariant measure gives positive mass to some compact set with nonempty interior, then
it is a Haar measure. -/
@[to_additive
/-- If a left-invariant measure gives positive mass to some compact set with nonempty interior, then
it is an additive Haar measure. -/]
/--
theorem `isHaarMeasure_of_isCompact_nonempty_interior` / 定理 `isHaarMeasure_of_isCompact_nonempty_interior`

English:
theorem isHaarMeasure_of_isCompact_nonempty_interior
  statement: [IsTopologicalGroup G] [BorelSpace G]
  proof: { lt_top_of_isCompact := fun _L hL =>
      measure_lt_top_of_isCompact_of_isMulLeftInvariant' h'K h' hL
    toIsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK h }

中文:
定理 isHaarMeasure_of_isCompact_nonempty_interior
  结论: [是拓扑群 G] [Borel空间 G]
  证明: { lt_top_of_isCompact := fun _L hL =>
      measure_lt_top_of_isCompact_of_isMulLeftInvariant' h'K h' hL
    toIsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK h }

Depends on / 依赖: isOpenPosMeasure_of_mulLeftInvariant_of_compact, lt_top_of_isCompact, measure_lt_top_of_isCompact_of_isMulLeftInvariant, toIsOpenPosMeasure
-/
theorem isHaarMeasure_of_isCompact_nonempty_interior [IsTopologicalGroup G] [BorelSpace G]
    (μ : Measure G) [IsMulLeftInvariant μ] (K : Set G) (hK : IsCompact K)
    (h'K : (interior K).Nonempty) (h : μ K != 0) (h' : μ K != ∞) : IsHaarMeasure μ :=
  { lt_top_of_isCompact := fun _L hL =>
      measure_lt_top_of_isCompact_of_isMulLeftInvariant' h'K h' hL
    toIsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK h }

/-- The image of a Haar measure under a continuous surjective proper group homomorphism is again
a Haar measure. See also `MulEquiv.isHaarMeasure_map` and `ContinuousMulEquiv.isHaarMeasure_map`. -/
@[to_additive
/-- The image of an additive Haar measure under a continuous surjective proper additive group
homomorphism is again an additive Haar measure. See also `AddEquiv.isAddHaarMeasure_map`,
`ContinuousAddEquiv.isAddHaarMeasure_map` and `ContinuousLinearEquiv.isAddHaarMeasure_map`. -/]
/--
theorem `isHaarMeasure_map` / 定理 `isHaarMeasure_map`

English:
theorem isHaarMeasure_map
  statement: [BorelSpace G] [ContinuousMul G] {H : Type*} [Group H]
  proof: { toIsMulLeftInvariant := isMulLeftInvariant_map f.toMulHom hf.measurable h_surj
    lt_top_of_isCompact := by
      intro K hK
      rw [← hK.measure_closure]; rw [map_apply hf.measurable isClosed_closure.measurableSet]
      set g : CocompactMap G H := ⟨⟨f, hf⟩, h_prop⟩
      exact IsCompact.measure_lt_top (g.isCompact_preimage_of_isClosed hK.closure isClosed_closure)
    toIsOpenPosMeasure := hf.isOpenPosMeasure_map h_surj }

@[to_additive]

中文:
定理 isHaarMeasure_map
  结论: [Borel空间 G] [连续乘法 G] {H : 类型} [群 H]
  证明: { toIsMulLeftInvariant := isMulLeftInvariant_map f.toMulHom hf.measurable h_surj
    lt_top_of_isCompact := by
      intro K hK
      rw [← hK.measure_closure]; rw [map_apply hf.measurable isClosed_closure.measurableSet]
      set g : CocompactMap G H := ⟨⟨f, hf⟩, h_prop⟩
      exact IsCompact.measure_lt_top (g.isCompact_preimage_of_isClosed hK.closure isClosed_closure)
    toIsOpenPosMeasure := hf.isOpenPosMeasure_map h_surj }

@[to_additive]

Depends on / 依赖: CocompactMap, IsCompact, IsCompact.measure_lt_top, closure, f.toMulHom, g.isCompact_preimage_of_isClosed, hK.closure, hK.measure_closure, h_prop, h_surj, hf.isOpenPosMeasure_map, hf.measurable, isClosed_closure, isClosed_closure.measurableSet, isCompact_preimage_of_isClosed, isMulLeftInvariant_map, isOpenPosMeasure_map, lt_top_of_isCompact, map_apply, measurable
-/
theorem isHaarMeasure_map [BorelSpace G] [ContinuousMul G] {H : Type*} [Group H]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [IsTopologicalGroup H]
    (f : G ->* H) (hf : Continuous f) (h_surj : Surjective f)
    (h_prop : Tendsto f (cocompact G) (cocompact H)) : IsHaarMeasure (Measure.map f μ) :=
  { toIsMulLeftInvariant := isMulLeftInvariant_map f.toMulHom hf.measurable h_surj
    lt_top_of_isCompact := by
      intro K hK
      rw [← hK.measure_closure]; rw [map_apply hf.measurable isClosed_closure.measurableSet]
      set g : CocompactMap G H := ⟨⟨f, hf⟩, h_prop⟩
      exact IsCompact.measure_lt_top (g.isCompact_preimage_of_isClosed hK.closure isClosed_closure)
    toIsOpenPosMeasure := hf.isOpenPosMeasure_map h_surj }

@[to_additive]
/--
theorem `IsHaarMeasure.comap` / 定理 `IsHaarMeasure.comap`

English:
theorem IsHaarMeasure.comap
  statement: [BorelSpace G] [MeasurableMul G]
  proof: (IsMulLeftInvariant.comap μ hf.measurableEmbedding).map_mul_left_eq_self
  lt_top_of_isCompact := (IsFiniteMeasureOnCompacts.comap' μ hf.continuous
    hf.measurableEmbedding).lt_top_of_isCompact
  open_pos := (IsOpenPosMeasure.comap μ hf).open_pos

中文:
定理 是Haar测度.comap
  结论: [Borel空间 G] [MeasurableMul G]
  证明: (IsMulLeftInvariant.comap μ hf.measurableEmbedding).map_mul_left_eq_self
  lt_top_of_isCompact := (IsFiniteMeasureOnCompacts.comap' μ hf.continuous
    hf.measurableEmbedding).lt_top_of_isCompact
  open_pos := (IsOpenPosMeasure.comap μ hf).open_pos
-/
protected theorem IsHaarMeasure.comap [BorelSpace G] [MeasurableMul G]
    [Group H] [TopologicalSpace H] [BorelSpace H] {mH : MeasurableMul H}
    (μ : Measure H) [IsHaarMeasure μ] {f : G ->* H} (hf : Topology.IsOpenEmbedding f) :
    (μ.comap f).IsHaarMeasure where
  map_mul_left_eq_self := (IsMulLeftInvariant.comap μ hf.measurableEmbedding).map_mul_left_eq_self
  lt_top_of_isCompact := (IsFiniteMeasureOnCompacts.comap' μ hf.continuous
    hf.measurableEmbedding).lt_top_of_isCompact
  open_pos := (IsOpenPosMeasure.comap μ hf).open_pos

/-- The image of a finite Haar measure under a continuous surjective group homomorphism is again
a Haar measure. See also `isHaarMeasure_map`. -/
@[to_additive
/-- The image of a finite additive Haar measure under a continuous surjective additive group
homomorphism is again an additive Haar measure. See also `isAddHaarMeasure_map`. -/]
/--
theorem `isHaarMeasure_map_of_isFiniteMeasure` / 定理 `isHaarMeasure_map_of_isFiniteMeasure`

English:
theorem isHaarMeasure_map_of_isFiniteMeasure
  proof: isMulLeftInvariant_map f.toMulHom hf.measurable h_surj
  toIsOpenPosMeasure := hf.isOpenPosMeasure_map h_surj

中文:
定理 isHaarMeasure_map_of_isFiniteMeasure
  证明: isMulLeftInvariant_map f.toMulHom hf.measurable h_surj
  toIsOpenPosMeasure := hf.isOpenPosMeasure_map h_surj

Depends on / 依赖: f.toMulHom, h_surj, hf.measurable, isMulLeftInvariant_map, measurable, toMulHom
-/
theorem isHaarMeasure_map_of_isFiniteMeasure
    [BorelSpace G] [ContinuousMul G] {H : Type*} [Group H]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [ContinuousMul H]
    [IsFiniteMeasure μ] (f : G ->* H) (hf : Continuous f) (h_surj : Surjective f) :
    IsHaarMeasure (Measure.map f μ) where
  toIsMulLeftInvariant := isMulLeftInvariant_map f.toMulHom hf.measurable h_surj
  toIsOpenPosMeasure := hf.isOpenPosMeasure_map h_surj

/-- The image of a Haar measure under map of a left action is again a Haar measure. -/
@[to_additive
/-- The image of a Haar measure under map of a left additive action is again a Haar measure -/]
/--
Instance `isHaarMeasure_map_smul` / 实例 `isHaarMeasure_map_smul`

English:
instance isHaarMeasure_map_smul
  signature: {α} [BorelSpace G] [IsTopologicalGroup G]
  body: isMulLeftInvariant_map_smul _
  lt_top_of_isCompact K hK := by
    let F := (Homeomorph.smul a (α := G)).toMeasurableEquiv
    change map F μ K < ∞
    rw [F.map_apply K]
exact IsCompact.measure_lt_top (Homeomorph.isCompact_preimage (Homeomorph.smul a)).2 hK
  toIsOpenPosMeasure :=
    (continuous_const_smul a).isOpenPosMeasure_map (MulAction.surjective a)

中文:
实例 isHaarMeasure_map_smul
  签名: {α} [Borel空间 G] [是拓扑群 G]
  定义体: isMulLeftInvariant_map_smul _
  lt_top_of_isCompact K hK := by
    let F := (Homeomorph.smul a (α := G)).toMeasurableEquiv
    change map F μ K < ∞
    rw [F.map_apply K]
exact IsCompact.measure_lt_top (Homeomorph.isCompact_preimage (Homeomorph.smul a)).2 hK
  toIsOpenPosMeasure :=
    (continuous_const_smul a).isOpenPosMeasure_map (MulAction.surjective a)

Depends on / 依赖: isMulLeftInvariant_map_smul
-/
instance isHaarMeasure_map_smul {α} [BorelSpace G] [IsTopologicalGroup G]
    [Group α] [MulAction α G] [SMulCommClass α G G] [ContinuousConstSMul α G] (a : α) :
    IsHaarMeasure (Measure.map (a • · : G -> G) μ) where
  toIsMulLeftInvariant := isMulLeftInvariant_map_smul _
  lt_top_of_isCompact K hK := by
    let F := (Homeomorph.smul a (α := G)).toMeasurableEquiv
    change map F μ K < ∞
    rw [F.map_apply K]
exact IsCompact.measure_lt_top (Homeomorph.isCompact_preimage (Homeomorph.smul a)).2 hK
  toIsOpenPosMeasure :=
    (continuous_const_smul a).isOpenPosMeasure_map (MulAction.surjective a)

/-- The image of a Haar measure under right multiplication is again a Haar measure. -/
@[to_additive isHaarMeasure_map_add_right
  /-- The image of a Haar measure under right addition is again a Haar measure. -/]
/--
Instance `isHaarMeasure_map_mul_right` / 实例 `isHaarMeasure_map_mul_right`

English:
instance isHaarMeasure_map_mul_right
  signature: [BorelSpace G] [IsTopologicalGroup G] (g : G)
  body: isHaarMeasure_map_smul μ (MulOpposite.op g)

中文:
实例 isHaarMeasure_map_mul_right
  签名: [Borel空间 G] [是拓扑群 G] (g : G)
  定义体: isHaarMeasure_map_smul μ (MulOpposite.op g)

Depends on / 依赖: MulOpposite, MulOpposite.op, isHaarMeasure_map_smul
-/
instance isHaarMeasure_map_mul_right [BorelSpace G] [IsTopologicalGroup G] (g : G) :
    IsHaarMeasure (Measure.map (· * g) μ) :=
  isHaarMeasure_map_smul μ (MulOpposite.op g)

/-- A convenience wrapper for `MeasureTheory.Measure.isHaarMeasure_map`. -/
@[to_additive /-- A convenience wrapper for `MeasureTheory.Measure.isAddHaarMeasure_map`. -/]
nonrec theorem _root_.MulEquiv.isHaarMeasure_map [BorelSpace G] [ContinuousMul G] {H : Type*}
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [IsTopologicalGroup H] (e : G ≃* H) (he : Continuous e) (hesymm : Continuous e.symm) :
    IsHaarMeasure (Measure.map e μ) :=
  let f : G ≃ₜ H := .mk e he hesymm
  -- We need to write `e.toMonoidHom` instead of just `e`, to avoid unification issues.
  isHaarMeasure_map μ e.toMonoidHom he e.surjective f.isClosedEmbedding.tendsto_cocompact

/--
A convenience wrapper for `MeasureTheory.Measure.isHaarMeasure_map`.
-/
@[to_additive /-- A convenience wrapper for `MeasureTheory.Measure.isAddHaarMeasure_map`. -/]
/--
Instance `_root_.ContinuousMulEquiv.isHaarMeasure_map` / 实例 `_root_.ContinuousMulEquiv.isHaarMeasure_map`

English:
instance _root_.ContinuousMulEquiv.isHaarMeasure_map
  signature: [BorelSpace G] [IsTopologicalGroup G]
  body: e.toMulEquiv.isHaarMeasure_map μ e.continuous e.symm.continuous

中文:
实例 _root_.连续乘法等价.isHaarMeasure_map
  签名: [Borel空间 G] [是拓扑群 G]
  定义体: e.toMulEquiv.isHaarMeasure_map μ e.continuous e.symm.continuous

Depends on / 依赖: continuous, e.continuous, e.symm.continuous, e.toMulEquiv.isHaarMeasure_map, isHaarMeasure_map, toMulEquiv
-/
instance _root_.ContinuousMulEquiv.isHaarMeasure_map [BorelSpace G] [IsTopologicalGroup G]
    {H : Type*} [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [IsTopologicalGroup H] (e : G ≃ₜ* H) : (μ.map e).IsHaarMeasure :=
  e.toMulEquiv.isHaarMeasure_map μ e.continuous e.symm.continuous

/--
Instance `_root_.ContinuousLinearEquiv.isAddHaarMeasure_map` / 实例 `_root_.ContinuousLinearEquiv.isAddHaarMeasure_map`

English:
instance _root_.ContinuousLinearEquiv.isAddHaarMeasure_map
  body: AddEquiv.isAddHaarMeasure_map _ (L : E ≃+ F) L.continuous L.symm.continuous

中文:
实例 _root_.连续线性等价.isAddHaarMeasure_map
  定义体: AddEquiv.isAddHaarMeasure_map _ (L : E ≃+ F) L.continuous L.symm.continuous

Depends on / 依赖: AddEquiv, AddEquiv.isAddHaarMeasure_map, L.continuous, L.symm.continuous, continuous, isAddHaarMeasure_map
-/
instance _root_.ContinuousLinearEquiv.isAddHaarMeasure_map
    {E F R S : Type*} [Semiring R] [Semiring S]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module S F]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace F]
    [IsTopologicalAddGroup F]
    {σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (L : E ≃SL[σ] F) (μ : Measure E) [IsAddHaarMeasure μ] :
    IsAddHaarMeasure (μ.map L) :=
  AddEquiv.isAddHaarMeasure_map _ (L : E ≃+ F) L.continuous L.symm.continuous

/-- A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority] -/
@[to_additive
/-- A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority] -/]
instance (priority := 100) IsHaarMeasure.sigmaFinite [SigmaCompactSpace G] : SigmaFinite μ :=
  ⟨⟨{ set := compactCovering G
        set_mem := fun _ => mem_univ _
finite := fun n => IsCompact.measure_lt_top isCompact_compactCovering G n
        spanning := iUnion_compactCovering G }⟩⟩

@[to_additive]
/--
Instance `prod.instIsHaarMeasure` / 实例 `prod.instIsHaarMeasure`

English:
instance prod.instIsHaarMeasure
  signature: {G : Type*} [Group G] [TopologicalSpace G] {_ : MeasurableSpace G}

中文:
实例 乘积.instIsHaarMeasure
  签名: {G : 类型} [群 G] [拓扑空间 G] {_ : 可测空间 G}
-/
instance prod.instIsHaarMeasure {G : Type*} [Group G] [TopologicalSpace G] {_ : MeasurableSpace G}
    {H : Type*} [Group H] [TopologicalSpace H] {_ : MeasurableSpace H} (μ : Measure G)
    (ν : Measure H) [IsHaarMeasure μ] [IsHaarMeasure ν] [SFinite μ] [SFinite ν]
    [MeasurableMul G] [MeasurableMul H] : IsHaarMeasure (μ.prod ν) where

/-- If the neutral element of a group is not isolated, then a Haar measure on this group has value
zero on singletons.

The additive version of this instance applies in particular to show that an additive Haar
measure on a nontrivial finite-dimensional real vector space has no atom. -/
@[to_additive
/-- If the zero element of an additive group is not isolated, then an additive Haar measure on this
group has value zero on singletons.

This applies in particular to show that an additive Haar measure on a nontrivial
finite-dimensional real vector space has no atom. -/]
instance (priority := 100) IsHaarMeasure.nullSingletonClass [IsTopologicalGroup G] [BorelSpace G]
    [T1Space G] [WeaklyLocallyCompactSpace G] [(𝓝[!=] (1 : G)).NeBot] (μ : Measure G)
    [μ.IsHaarMeasure] : NullSingletonClass μ := by
  cases eq_or_ne (μ 1) 0 with
  | inl h => constructor; simpa
  | inr h =>
    obtain ⟨K, K_compact, K_nhds⟩ : exists K : Set G, IsCompact K ∧ K in 𝓝 1 := exists_compact_mem_nhds 1
    have K_inf : Set.Infinite K := infinite_of_mem_nhds (1 : G) K_nhds
    exact absurd (K_inf.meas_eq_top ⟨_, h, fun x _ => (haar_singleton _ _).ge⟩)
      K_compact.measure_lt_top.ne

@[deprecated (since := "2026-06-09")]
alias IsHaarMeasure.noAtoms := IsHaarMeasure.nullSingletonClass

/--
Instance `IsAddHaarMeasure.domSMul` / 实例 `IsAddHaarMeasure.domSMul`

English:
instance IsAddHaarMeasure.domSMul
  signature: {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
  body: (DistribMulAction.toAddEquiv _ (DomMulAct.mk.symm g⁻¹)).isAddHaarMeasure_map _
    (continuous_const_smul _) (continuous_const_smul _)

中文:
实例 是加法Haar测度.domSMul
  签名: {G A : 类型} [群 G] [加法交换群 A] [分配乘法作用 G A]
  定义体: (DistribMulAction.toAddEquiv _ (DomMulAct.mk.symm g⁻¹)).isAddHaarMeasure_map _
    (continuous_const_smul _) (continuous_const_smul _)

Depends on / 依赖: DistribMulAction, DistribMulAction.toAddEquiv, DomMulAct, DomMulAct.mk.symm, continuous_const_smul, isAddHaarMeasure_map, toAddEquiv
-/
instance IsAddHaarMeasure.domSMul {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [IsTopologicalAddGroup A]
    [ContinuousConstSMul G A] {μ : Measure A} [μ.IsAddHaarMeasure] (g : Gᵈᵐᵃ) :
    (g • μ).IsAddHaarMeasure :=
  (DistribMulAction.toAddEquiv _ (DomMulAct.mk.symm g⁻¹)).isAddHaarMeasure_map _
    (continuous_const_smul _) (continuous_const_smul _)

end Measure

end Haar

end MeasureTheory
