/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Nat

/-!
# Topology on the rational numbers

The structure of a metric space on `ℚ` is introduced in this file, induced from `ℝ`.
-/

public section

open Filter Metric Set Topology

namespace Rat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace Rat
  body: fast_instance% MetricSpace.induced (↑) Rat.cast_injective Real.metricSpace

中文:
实例 :
  签名: MetricSpace Rat
  定义体: fast_instance% MetricSpace.induced (↑) Rat.cast_injective Real.metricSpace

Depends on / 依赖: MetricSpace, MetricSpace.induced, Rat.cast_injective, Real.metricSpace, cast_injective, fast_instance, induced, metricSpace
-/
instance : MetricSpace Rat :=
  fast_instance% MetricSpace.induced (↑) Rat.cast_injective Real.metricSpace

/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  given: (x y : Rat)
  statement: dist x y = |(x : Real) - y|
  proof: rfl

@[norm_cast, simp]

中文:
定理 dist_eq
  条件: (x y : Rat)
  结论: dist x y = |(x : 实数) - y|
  证明: rfl

@[norm_cast, simp]
-/
theorem dist_eq (x y : Rat) : dist x y = |(x : Real) - y| := rfl

@[norm_cast, simp]
/--
theorem `dist_cast` / 定理 `dist_cast`

English:
theorem dist_cast
  given: (x y : Rat)
  statement: dist (x : Real) y = dist x y
  proof: rfl

中文:
定理 dist_cast
  条件: (x y : Rat)
  结论: dist (x : 实数) y = dist x y
  证明: rfl
-/
theorem dist_cast (x y : Rat) : dist (x : Real) y = dist x y :=
  rfl

/--
theorem `uniformContinuous_coe_real` / 定理 `uniformContinuous_coe_real`

English:
theorem uniformContinuous_coe_real
  statement: UniformContinuous ((↑) : Rat -> Real)
  proof: uniformContinuous_comap

中文:
定理 uniformContinuous_coe_real
  结论: UniformContinuous ((↑) : Rat -> 实数)
  证明: uniformContinuous_comap

Depends on / 依赖: uniformContinuous_comap
-/
theorem uniformContinuous_coe_real : UniformContinuous ((↑) : Rat -> Real) :=
  uniformContinuous_comap

/--
theorem `isUniformEmbedding_coe_real` / 定理 `isUniformEmbedding_coe_real`

English:
theorem isUniformEmbedding_coe_real
  statement: IsUniformEmbedding ((↑) : Rat -> Real)
  proof: isUniformEmbedding_comap Rat.cast_injective

中文:
定理 isUniformEmbedding_coe_real
  结论: IsUniformEmbedding ((↑) : Rat -> 实数)
  证明: isUniformEmbedding_comap Rat.cast_injective

Depends on / 依赖: Rat.cast_injective, cast_injective, isUniformEmbedding_comap
-/
theorem isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : Rat -> Real) :=
  isUniformEmbedding_comap Rat.cast_injective

/--
theorem `isDenseEmbedding_coe_real` / 定理 `isDenseEmbedding_coe_real`

English:
theorem isDenseEmbedding_coe_real
  statement: IsDenseEmbedding ((↑) : Rat -> Real)
  proof: isUniformEmbedding_coe_real.isDenseEmbedding Rat.denseRange_cast

中文:
定理 isDenseEmbedding_coe_real
  结论: IsDenseEmbedding ((↑) : Rat -> 实数)
  证明: isUniformEmbedding_coe_real.isDenseEmbedding Rat.denseRange_cast

Depends on / 依赖: Rat.denseRange_cast, denseRange_cast, isDenseEmbedding, isUniformEmbedding_coe_real, isUniformEmbedding_coe_real.isDenseEmbedding
-/
theorem isDenseEmbedding_coe_real : IsDenseEmbedding ((↑) : Rat -> Real) :=
  isUniformEmbedding_coe_real.isDenseEmbedding Rat.denseRange_cast

/--
theorem `isEmbedding_coe_real` / 定理 `isEmbedding_coe_real`

English:
theorem isEmbedding_coe_real
  statement: IsEmbedding ((↑) : Rat -> Real)
  proof: isDenseEmbedding_coe_real.isEmbedding

中文:
定理 isEmbedding_coe_real
  结论: IsEmbedding ((↑) : Rat -> 实数)
  证明: isDenseEmbedding_coe_real.isEmbedding

Depends on / 依赖: isDenseEmbedding_coe_real, isDenseEmbedding_coe_real.isEmbedding, isEmbedding
-/
theorem isEmbedding_coe_real : IsEmbedding ((↑) : Rat -> Real) :=
  isDenseEmbedding_coe_real.isEmbedding

/--
theorem `continuous_coe_real` / 定理 `continuous_coe_real`

English:
theorem continuous_coe_real
  statement: Continuous ((↑) : Rat -> Real)
  proof: uniformContinuous_coe_real.continuous

中文:
定理 continuous_coe_real
  结论: Continuous ((↑) : Rat -> 实数)
  证明: uniformContinuous_coe_real.continuous

Depends on / 依赖: continuous, uniformContinuous_coe_real, uniformContinuous_coe_real.continuous
-/
theorem continuous_coe_real : Continuous ((↑) : Rat -> Real) :=
  uniformContinuous_coe_real.continuous

end Rat

@[norm_cast, simp]
/--
theorem `Nat.dist_cast_rat` / 定理 `Nat.dist_cast_rat`

English:
theorem Nat.dist_cast_rat
  given: (x y : Nat)
  statement: dist (x : Rat) y = dist x y
  proof: by
  rw [← Nat.dist_cast_real]; rw [← Rat.dist_cast]; congr

中文:
定理 Nat.dist_cast_rat
  条件: (x y : 自然数)
  结论: dist (x : Rat) y = dist x y
  证明: by
  rw [← Nat.dist_cast_real]; rw [← Rat.dist_cast]; congr

Depends on / 依赖: Nat.dist_cast_real, Rat.dist_cast, dist_cast, dist_cast_real
-/
theorem Nat.dist_cast_rat (x y : Nat) : dist (x : Rat) y = dist x y := by
  rw [← Nat.dist_cast_real]; rw [← Rat.dist_cast]; congr

/--
theorem `Nat.isUniformEmbedding_coe_rat` / 定理 `Nat.isUniformEmbedding_coe_rat`

English:
theorem Nat.isUniformEmbedding_coe_rat
  statement: IsUniformEmbedding ((↑) : Nat -> Rat)
  proof: isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one by simpa using Nat.pairwise_one_le_dist

中文:
定理 Nat.isUniformEmbedding_coe_rat
  结论: IsUniformEmbedding ((↑) : 自然数 -> Rat)
  证明: isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one by simpa using Nat.pairwise_one_le_dist

Depends on / 依赖: Nat.pairwise_one_le_dist, isUniformEmbedding_bot_of_pairwise_le_dist, pairwise_one_le_dist, zero_lt_one
-/
theorem Nat.isUniformEmbedding_coe_rat : IsUniformEmbedding ((↑) : Nat -> Rat) :=
isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one by simpa using Nat.pairwise_one_le_dist

/--
theorem `Nat.isClosedEmbedding_coe_rat` / 定理 `Nat.isClosedEmbedding_coe_rat`

English:
theorem Nat.isClosedEmbedding_coe_rat
  statement: IsClosedEmbedding ((↑) : Nat -> Rat)
  proof: isClosedEmbedding_of_pairwise_le_dist zero_lt_one by simpa using Nat.pairwise_one_le_dist

@[norm_cast, simp]

中文:
定理 Nat.isClosedEmbedding_coe_rat
  结论: IsClosedEmbedding ((↑) : 自然数 -> Rat)
  证明: isClosedEmbedding_of_pairwise_le_dist zero_lt_one by simpa using Nat.pairwise_one_le_dist

@[norm_cast, simp]

Depends on / 依赖: Nat.pairwise_one_le_dist, isClosedEmbedding_of_pairwise_le_dist, pairwise_one_le_dist, zero_lt_one
-/
theorem Nat.isClosedEmbedding_coe_rat : IsClosedEmbedding ((↑) : Nat -> Rat) :=
isClosedEmbedding_of_pairwise_le_dist zero_lt_one by simpa using Nat.pairwise_one_le_dist

@[norm_cast, simp]
/--
theorem `Int.dist_cast_rat` / 定理 `Int.dist_cast_rat`

English:
theorem Int.dist_cast_rat
  given: (x y : Int)
  statement: dist (x : Rat) y = dist x y
  proof: by
  rw [← Int.dist_cast_real]; rw [← Rat.dist_cast]; congr

中文:
定理 Int.dist_cast_rat
  条件: (x y : 整数)
  结论: dist (x : Rat) y = dist x y
  证明: by
  rw [← Int.dist_cast_real]; rw [← Rat.dist_cast]; congr

Depends on / 依赖: Int.dist_cast_real, Rat.dist_cast, dist_cast, dist_cast_real
-/
theorem Int.dist_cast_rat (x y : Int) : dist (x : Rat) y = dist x y := by
  rw [← Int.dist_cast_real]; rw [← Rat.dist_cast]; congr

/--
theorem `Int.isUniformEmbedding_coe_rat` / 定理 `Int.isUniformEmbedding_coe_rat`

English:
theorem Int.isUniformEmbedding_coe_rat
  statement: IsUniformEmbedding ((↑) : Int -> Rat)
  proof: isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one by simpa using Int.pairwise_one_le_dist

中文:
定理 Int.isUniformEmbedding_coe_rat
  结论: IsUniformEmbedding ((↑) : 整数 -> Rat)
  证明: isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one by simpa using Int.pairwise_one_le_dist

Depends on / 依赖: Int.pairwise_one_le_dist, isUniformEmbedding_bot_of_pairwise_le_dist, pairwise_one_le_dist, zero_lt_one
-/
theorem Int.isUniformEmbedding_coe_rat : IsUniformEmbedding ((↑) : Int -> Rat) :=
isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one by simpa using Int.pairwise_one_le_dist

/--
theorem `Int.isClosedEmbedding_coe_rat` / 定理 `Int.isClosedEmbedding_coe_rat`

English:
theorem Int.isClosedEmbedding_coe_rat
  statement: IsClosedEmbedding ((↑) : Int -> Rat)
  proof: isClosedEmbedding_of_pairwise_le_dist zero_lt_one by simpa using Int.pairwise_one_le_dist

中文:
定理 Int.isClosedEmbedding_coe_rat
  结论: IsClosedEmbedding ((↑) : 整数 -> Rat)
  证明: isClosedEmbedding_of_pairwise_le_dist zero_lt_one by simpa using Int.pairwise_one_le_dist

Depends on / 依赖: Int.pairwise_one_le_dist, isClosedEmbedding_of_pairwise_le_dist, pairwise_one_le_dist, zero_lt_one
-/
theorem Int.isClosedEmbedding_coe_rat : IsClosedEmbedding ((↑) : Int -> Rat) :=
isClosedEmbedding_of_pairwise_le_dist zero_lt_one by simpa using Int.pairwise_one_le_dist

namespace Rat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoncompactSpace Rat
  body: Int.isClosedEmbedding_coe_rat.noncompactSpace

中文:
实例 :
  签名: NoncompactSpace Rat
  定义体: Int.isClosedEmbedding_coe_rat.noncompactSpace

Depends on / 依赖: Int.isClosedEmbedding_coe_rat.noncompactSpace, isClosedEmbedding_coe_rat, noncompactSpace
-/
instance : NoncompactSpace Rat := Int.isClosedEmbedding_coe_rat.noncompactSpace

/--
theorem `uniformContinuous_add` / 定理 `uniformContinuous_add`

English:
theorem uniformContinuous_add
  statement: UniformContinuous fun p : Rat × Rat => p.1 + p.2
  proof: Rat.isUniformEmbedding_coe_real.isUniformInducing.uniformContinuous_iff.2 by
    simp only [Function.comp_def, Rat.cast_add]
    exact Real.uniformContinuous_add.comp
      (Rat.uniformContinuous_coe_real.prodMap Rat.uniformContinuous_coe_real)

中文:
定理 uniformContinuous_add
  结论: UniformContinuous fun p : Rat × Rat => p.1 + p.2
  证明: Rat.isUniformEmbedding_coe_real.isUniformInducing.uniformContinuous_iff.2 by
    simp only [Function.comp_def, Rat.cast_add]
    exact Real.uniformContinuous_add.comp
      (Rat.uniformContinuous_coe_real.prodMap Rat.uniformContinuous_coe_real)

Depends on / 依赖: Function, Function.comp_def, Rat.cast_add, Rat.isUniformEmbedding_coe_real.isUniformInducing.uniformContinuous_iff, Rat.uniformContinuous_coe_real, Rat.uniformContinuous_coe_real.prodMap, Real.uniformContinuous_add.comp, cast_add, comp_def, isUniformEmbedding_coe_real, isUniformInducing, prodMap, uniformContinuous_add, uniformContinuous_coe_real, uniformContinuous_iff
-/
theorem uniformContinuous_add : UniformContinuous fun p : Rat × Rat => p.1 + p.2 :=
Rat.isUniformEmbedding_coe_real.isUniformInducing.uniformContinuous_iff.2 by
    simp only [Function.comp_def, Rat.cast_add]
    exact Real.uniformContinuous_add.comp
      (Rat.uniformContinuous_coe_real.prodMap Rat.uniformContinuous_coe_real)

/--
theorem `uniformContinuous_neg` / 定理 `uniformContinuous_neg`

English:
theorem uniformContinuous_neg
  statement: UniformContinuous (@Neg.neg Rat _)
  proof: Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by
      simpa only [abs_sub_comm, dist_eq, cast_neg, neg_sub_neg] using h⟩

中文:
定理 uniformContinuous_neg
  结论: UniformContinuous (@Neg.neg Rat _)
  证明: Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by
      simpa only [abs_sub_comm, dist_eq, cast_neg, neg_sub_neg] using h⟩

Depends on / 依赖: Metric, Metric.uniformContinuous_iff, abs_sub_comm, cast_neg, dist_eq, neg_sub_neg, uniformContinuous_iff
-/
theorem uniformContinuous_neg : UniformContinuous (@Neg.neg Rat _) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by
      simpa only [abs_sub_comm, dist_eq, cast_neg, neg_sub_neg] using h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsUniformAddGroup Rat
  body: IsUniformAddGroup.mk' Rat.uniformContinuous_add Rat.uniformContinuous_neg

中文:
实例 :
  签名: IsUniformAddGroup Rat
  定义体: IsUniformAddGroup.mk' Rat.uniformContinuous_add Rat.uniformContinuous_neg

Depends on / 依赖: IsUniformAddGroup, IsUniformAddGroup.mk, Rat.uniformContinuous_add, Rat.uniformContinuous_neg, uniformContinuous_add, uniformContinuous_neg
-/
instance : IsUniformAddGroup Rat :=
  IsUniformAddGroup.mk' Rat.uniformContinuous_add Rat.uniformContinuous_neg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalAddGroup Rat
  body: inferInstance

中文:
实例 :
  签名: IsTopologicalAddGroup Rat
  定义体: inferInstance
-/
instance : IsTopologicalAddGroup Rat := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTopology Rat
  body: induced_orderTopology _ Rat.cast_lt exists_rat_btwn

中文:
实例 :
  签名: OrderTopology Rat
  定义体: induced_orderTopology _ Rat.cast_lt exists_rat_btwn

Depends on / 依赖: Rat.cast_lt, cast_lt, exists_rat_btwn, induced_orderTopology
-/
instance : OrderTopology Rat := induced_orderTopology _ Rat.cast_lt exists_rat_btwn

/--
theorem `uniformContinuous_abs` / 定理 `uniformContinuous_abs`

English:
theorem uniformContinuous_abs
  statement: UniformContinuous (abs : Rat -> Rat)
  proof: Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun _ _ h =>
      lt_of_le_of_lt (by simpa [Rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _) h⟩

中文:
定理 uniformContinuous_abs
  结论: UniformContinuous (abs : Rat -> Rat)
  证明: Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun _ _ h =>
      lt_of_le_of_lt (by simpa [Rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _) h⟩

Depends on / 依赖: Metric, Metric.uniformContinuous_iff, Rat.dist_eq, abs_abs_sub_abs_le_abs_sub, dist_eq, lt_of_le_of_lt, uniformContinuous_iff
-/
theorem uniformContinuous_abs : UniformContinuous (abs : Rat -> Rat) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun _ _ h =>
      lt_of_le_of_lt (by simpa [Rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _) h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalRing Rat
  body: inferInstance

nonrec theorem totallyBounded_Icc (a b : Rat) : TotallyBounded (Icc a b) := by
  simpa only [preimage_cast_Icc]
    using totallyBounded_preimage Rat.isUniformEmbedding_coe_real.isUniformInducing
      (totallyBounded_Icc (a : Real) b)

中文:
实例 :
  签名: IsTopologicalRing Rat
  定义体: inferInstance

nonrec theorem totallyBounded_Icc (a b : Rat) : TotallyBounded (Icc a b) := by
  simpa only [preimage_cast_Icc]
    using totallyBounded_preimage Rat.isUniformEmbedding_coe_real.isUniformInducing
      (totallyBounded_Icc (a : Real) b)
-/
instance : IsTopologicalRing Rat := inferInstance

nonrec theorem totallyBounded_Icc (a b : Rat) : TotallyBounded (Icc a b) := by
  simpa only [preimage_cast_Icc]
    using totallyBounded_preimage Rat.isUniformEmbedding_coe_real.isUniformInducing
      (totallyBounded_Icc (a : Real) b)

end Rat

namespace NNRat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace Rat>=0
  body: inferInstanceAs MetricSpace (Subtype _)

中文:
实例 :
  签名: MetricSpace Rat>=0
  定义体: inferInstanceAs MetricSpace (Subtype _)

Depends on / 依赖: MetricSpace, Subtype
-/
instance : MetricSpace Rat>=0 :=
inferInstanceAs MetricSpace (Subtype _)

set_option linter.style.whitespace false in -- linter false positive
@[simp ←, push_cast]
/--
lemma `dist_eq` / 引理 `dist_eq`

English:
lemma dist_eq
  given: (p q : Rat>=0)
  statement: dist p q = dist (p : Rat) (q : Rat)
  proof: rfl

中文:
引理 dist_eq
  条件: (p q : Rat>=0)
  结论: dist p q = dist (p : Rat) (q : Rat)
  证明: rfl
-/
lemma dist_eq (p q : Rat>=0) : dist p q = dist (p : Rat) (q : Rat) := rfl

set_option linter.style.whitespace false in -- linter false positive
@[simp ←, push_cast]
/--
lemma `nndist_eq` / 引理 `nndist_eq`

English:
lemma nndist_eq
  given: (p q : Rat>=0)
  statement: nndist p q = nndist (p : Rat) (q : Rat)
  proof: rfl

中文:
引理 nndist_eq
  条件: (p q : Rat>=0)
  结论: nndist p q = nndist (p : Rat) (q : Rat)
  证明: rfl
-/
lemma nndist_eq (p q : Rat>=0) : nndist p q = nndist (p : Rat) (q : Rat) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalSemiring Rat>=0
  body: continuousAdd_induced Nonneg.coeRingHom
  toContinuousMul := continuousMul_induced Nonneg.coeRingHom

中文:
实例 :
  签名: IsTopologicalSemiring Rat>=0
  定义体: continuousAdd_induced Nonneg.coeRingHom
  toContinuousMul := continuousMul_induced Nonneg.coeRingHom

Depends on / 依赖: Nonneg, Nonneg.coeRingHom, coeRingHom, continuousAdd_induced
-/
instance : IsTopologicalSemiring Rat>=0 where
  toContinuousAdd := continuousAdd_induced Nonneg.coeRingHom
  toContinuousMul := continuousMul_induced Nonneg.coeRingHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSub Rat>=0
  body: ⟨Continuous.subtype_mk (by fun_prop) _⟩

中文:
实例 :
  签名: ContinuousSub Rat>=0
  定义体: ⟨Continuous.subtype_mk (by fun_prop) _⟩

Depends on / 依赖: Continuous, Continuous.subtype_mk, fun_prop, subtype_mk
-/
instance : ContinuousSub Rat>=0 := ⟨Continuous.subtype_mk (by fun_prop) _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTopology Rat>=0
  body: orderTopology_of_ordConnected (t := Set.Ici 0)

中文:
实例 :
  签名: OrderTopology Rat>=0
  定义体: orderTopology_of_ordConnected (t := Set.Ici 0)

Depends on / 依赖: Set.Ici, orderTopology_of_ordConnected
-/
instance : OrderTopology Rat>=0 := orderTopology_of_ordConnected (t := Set.Ici 0)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousInv₀ Rat>=0
  body: inferInstance

中文:
实例 :
  签名: ContinuousInv₀ Rat>=0
  定义体: inferInstance
-/
instance : ContinuousInv₀ Rat>=0 := inferInstance

-- Special case of `IsBoundedSMul.continuousSMul` but this shortcut instance reduces dependencies
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSMul Rat Real
  body: continuous_induced_dom.fst'.smul (M := Real) (X := Real) continuous_snd

中文:
实例 :
  签名: ContinuousSMul Rat 实数
  定义体: continuous_induced_dom.fst'.smul (M := Real) (X := Real) continuous_snd

Depends on / 依赖: continuous_induced_dom, continuous_induced_dom.fst, continuous_snd
-/
instance : ContinuousSMul Rat Real where
  continuous_smul := continuous_induced_dom.fst'.smul (M := Real) (X := Real) continuous_snd

instance {R : Type*} [TopologicalSpace R] [MulAction Rat R] [MulAction Rat>=0 R] [IsScalarTower Rat>=0 Rat R]
    [ContinuousSMul Rat R] : ContinuousSMul Rat>=0 R where
  continuous_smul := by
    conv in _ • _ => rw [← NNRat.cast_smul_eq_nnqsmul Rat]
    fun_prop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSMul Rat>=0 NNReal
  body: Continuous.subtype_mk (by fun_prop) _

中文:
实例 :
  签名: ContinuousSMul Rat>=0 NN实数
  定义体: Continuous.subtype_mk (by fun_prop) _

Depends on / 依赖: Continuous, Continuous.subtype_mk, fun_prop, subtype_mk
-/
instance : ContinuousSMul Rat>=0 NNReal where
  continuous_smul := Continuous.subtype_mk (by fun_prop) _

end NNRat
