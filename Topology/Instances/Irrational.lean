/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Rat.Encodable
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Topology of irrational numbers

In this file we prove the following theorems:

* `IsGδ.setOfPred_irrational`, `dense_irrational`, `eventually_residual_irrational`: irrational
  numbers form a dense Gδ set;

* `Irrational.eventually_forall_le_dist_cast_div`,
  `Irrational.eventually_forall_le_dist_cast_div_of_denom_le`;
  `Irrational.eventually_forall_le_dist_cast_rat_of_denom_le`: a sufficiently small neighborhood of
  an irrational number is disjoint with the set of rational numbers with bounded denominator.

We also provide `OrderTopology`, `NoMinOrder`, `NoMaxOrder`, and `DenselyOrdered`
instances for `{x // Irrational x}`.

## Tags

irrational, residual
-/

public section


open Set Filter Metric

open Filter Topology

/--
theorem `IsGδ.setOfPred_irrational` / 定理 `IsGδ.setOfPred_irrational`

English:
theorem IsGδ.setOfPred_irrational
  statement: IsGδ { x | Irrational x }
  proof: (countable_range _).isGδ_compl

@[deprecated (since := "2026-07-09")] alias IsGδ.setOf_irrational := IsGδ.setOfPred_irrational

中文:
定理 IsGδ.setOfPred_irrational
  结论: IsGδ { x | Irrational x }
  证明: (countable_range _).isGδ_compl

@[deprecated (since := "2026-07-09")] alias IsGδ.setOf_irrational := IsGδ.setOfPred_irrational
-/
protected theorem IsGδ.setOfPred_irrational : IsGδ { x | Irrational x } :=
  (countable_range _).isGδ_compl

@[deprecated (since := "2026-07-09")] alias IsGδ.setOf_irrational := IsGδ.setOfPred_irrational


/--
theorem `dense_irrational` / 定理 `dense_irrational`

English:
theorem dense_irrational
  statement: Dense { x : Real | Irrational x }
  proof: by
  refine Real.isTopologicalBasis_Ioo_rat.dense_iff.2 ?_
  simp only [mem_iUnion, mem_singleton_iff, exists_prop, forall_exists_index, and_imp]
  rintro _ a b hlt rfl _
  rw [inter_comm]
  exact exists_irrational_btwn (Rat.cast_lt.2 hlt)

中文:
定理 dense_irrational
  结论: Dense { x : 实数 | Irrational x }
  证明: by
  refine Real.isTopologicalBasis_Ioo_rat.dense_iff.2 ?_
  simp only [mem_iUnion, mem_singleton_iff, exists_prop, forall_exists_index, and_imp]
  rintro _ a b hlt rfl _
  rw [inter_comm]
  exact exists_irrational_btwn (Rat.cast_lt.2 hlt)

Depends on / 依赖: Rat.cast_lt, Real.isTopologicalBasis_Ioo_rat.dense_iff, and_imp, cast_lt, dense_iff, exists_irrational_btwn, exists_prop, forall_exists_index, inter_comm, isTopologicalBasis_Ioo_rat, mem_iUnion, mem_singleton_iff
-/
theorem dense_irrational : Dense { x : Real | Irrational x } := by
  refine Real.isTopologicalBasis_Ioo_rat.dense_iff.2 ?_
  simp only [mem_iUnion, mem_singleton_iff, exists_prop, forall_exists_index, and_imp]
  rintro _ a b hlt rfl _
  rw [inter_comm]
  exact exists_irrational_btwn (Rat.cast_lt.2 hlt)

/--
theorem `eventually_residual_irrational` / 定理 `eventually_residual_irrational`

English:
theorem eventually_residual_irrational
  statement: forallᶠ x in residual Real, Irrational x
  proof: residual_of_dense_Gδ .setOfPred_irrational dense_irrational

中文:
定理 eventually_residual_irrational
  结论: 对任意ᶠ x in residual 实数, Irrational x
  证明: residual_of_dense_Gδ .setOfPred_irrational dense_irrational

Depends on / 依赖: dense_irrational, setOfPred_irrational
-/
theorem eventually_residual_irrational : forallᶠ x in residual Real, Irrational x :=
  residual_of_dense_Gδ .setOfPred_irrational dense_irrational

namespace Irrational

variable {x : Real}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTopology { x // Irrational x }
  body: induced_orderTopology _ Iff.rfl @fun _ _ hlt =>
    let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
    ⟨⟨z, hz⟩, hxz, hzy⟩

中文:
实例 :
  签名: OrderTopology { x // Irrational x }
  定义体: induced_orderTopology _ Iff.rfl @fun _ _ hlt =>
    let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
    ⟨⟨z, hz⟩, hxz, hzy⟩

Depends on / 依赖: Iff.rfl, exists_irrational_btwn, induced_orderTopology
-/
instance : OrderTopology { x // Irrational x } :=
induced_orderTopology _ Iff.rfl @fun _ _ hlt =>
    let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
    ⟨⟨z, hz⟩, hxz, hzy⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoMaxOrder { x // Irrational x }
  body: ⟨fun ⟨x, hx⟩ => ⟨⟨x + (1 : Nat), hx.add_natCast 1⟩, by simp⟩⟩

中文:
实例 :
  签名: NoMaxOrder { x // Irrational x }
  定义体: ⟨fun ⟨x, hx⟩ => ⟨⟨x + (1 : Nat), hx.add_natCast 1⟩, by simp⟩⟩

Depends on / 依赖: add_natCast, hx.add_natCast
-/
instance : NoMaxOrder { x // Irrational x } :=
  ⟨fun ⟨x, hx⟩ => ⟨⟨x + (1 : Nat), hx.add_natCast 1⟩, by simp⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoMinOrder { x // Irrational x }
  body: ⟨fun ⟨x, hx⟩ => ⟨⟨x - (1 : Nat), hx.sub_natCast 1⟩, by simp⟩⟩

中文:
实例 :
  签名: NoMinOrder { x // Irrational x }
  定义体: ⟨fun ⟨x, hx⟩ => ⟨⟨x - (1 : Nat), hx.sub_natCast 1⟩, by simp⟩⟩

Depends on / 依赖: hx.sub_natCast, sub_natCast
-/
instance : NoMinOrder { x // Irrational x } :=
  ⟨fun ⟨x, hx⟩ => ⟨⟨x - (1 : Nat), hx.sub_natCast 1⟩, by simp⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DenselyOrdered { x // Irrational x }
  body: ⟨fun _ _ hlt =>
    let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
    ⟨⟨z, hz⟩, hxz, hzy⟩⟩

中文:
实例 :
  签名: DenselyOrdered { x // Irrational x }
  定义体: ⟨fun _ _ hlt =>
    let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
    ⟨⟨z, hz⟩, hxz, hzy⟩⟩

Depends on / 依赖: exists_irrational_btwn
-/
instance : DenselyOrdered { x // Irrational x } :=
  ⟨fun _ _ hlt =>
    let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
    ⟨⟨z, hz⟩, hxz, hzy⟩⟩

/--
theorem `eventually_forall_le_dist_cast_div` / 定理 `eventually_forall_le_dist_cast_div`

English:
theorem eventually_forall_le_dist_cast_div
  given: (hx : Irrational x) (n : Nat)
  proof: by
  have A : IsClosed (range (fun m => (n : Real)⁻¹ * m : Int -> Real)) :=
    ((isClosedMap_smul₀ (n⁻¹ : Real)).comp Int.isClosedEmbedding_coe_real.isClosedMap).isClosed_range
  have B : x ∉ range (fun m => (n : Real)⁻¹ * m : Int -> Real) := by
    rintro ⟨m, rfl⟩
    simp at hx
  rcases Metric.me

中文:
定理 eventually_forall_le_dist_cast_div
  条件: (hx : Irrational x) (n : 自然数)
  证明: by
  have A : IsClosed (range (fun m => (n : Real)⁻¹ * m : Int -> Real)) :=
    ((isClosedMap_smul₀ (n⁻¹ : Real)).comp Int.isClosedEmbedding_coe_real.isClosedMap).isClosed_range
  have B : x ∉ range (fun m => (n : Real)⁻¹ * m : Int -> Real) := by
    rintro ⟨m, rfl⟩
    simp at hx
  rcases Metric.me

Depends on / 依赖: A.isOpen_compl.mem_nhds, Int.isClosedEmbedding_coe_real.isClosedMap, IsClosed, Metric, Metric.mem_nhds_iff, ball_subset_ball, dist_comm, div_eq_inv_mul, ge_mem_nhds, isClosedEmbedding_coe_real, isClosedMap, isClosed_range, isOpen_compl, mem_nhds, mem_nhds_iff, not_lt
-/
theorem eventually_forall_le_dist_cast_div (hx : Irrational x) (n : Nat) :
    forallᶠ ε : Real in 𝓝 0, forall m : Int, ε <= dist x (m / n) := by
  have A : IsClosed (range (fun m => (n : Real)⁻¹ * m : Int -> Real)) :=
    ((isClosedMap_smul₀ (n⁻¹ : Real)).comp Int.isClosedEmbedding_coe_real.isClosedMap).isClosed_range
  have B : x ∉ range (fun m => (n : Real)⁻¹ * m : Int -> Real) := by
    rintro ⟨m, rfl⟩
    simp at hx
  rcases Metric.mem_nhds_iff.1 (A.isOpen_compl.mem_nhds B) with ⟨ε, ε0, hε⟩
  refine (ge_mem_nhds ε0).mono fun δ hδ m => not_lt.1 fun hlt => ?_
  rw [dist_comm] at hlt
  refine hε (ball_subset_ball hδ hlt) ⟨m, ?_⟩
  simp [div_eq_inv_mul]

/--
theorem `eventually_forall_le_dist_cast_div_of_denom_le` / 定理 `eventually_forall_le_dist_cast_div_of_denom_le`

English:
theorem eventually_forall_le_dist_cast_div_of_denom_le
  given: (hx : Irrational x) (n : Nat)
  proof: (finite_le_nat n).eventually_all.2 fun k _ => hx.eventually_forall_le_dist_cast_div k

中文:
定理 eventually_forall_le_dist_cast_div_of_denom_le
  条件: (hx : Irrational x) (n : 自然数)
  证明: (finite_le_nat n).eventually_all.2 fun k _ => hx.eventually_forall_le_dist_cast_div k

Depends on / 依赖: eventually_all, eventually_forall_le_dist_cast_div, finite_le_nat, hx.eventually_forall_le_dist_cast_div
-/
theorem eventually_forall_le_dist_cast_div_of_denom_le (hx : Irrational x) (n : Nat) :
    forallᶠ ε : Real in 𝓝 0, forall k <= n, forall (m : Int), ε <= dist x (m / k) :=
  (finite_le_nat n).eventually_all.2 fun k _ => hx.eventually_forall_le_dist_cast_div k

/--
theorem `eventually_forall_le_dist_cast_rat_of_den_le` / 定理 `eventually_forall_le_dist_cast_rat_of_den_le`

English:
theorem eventually_forall_le_dist_cast_rat_of_den_le
  given: (hx : Irrational x) (n : Nat)
  proof: (hx.eventually_forall_le_dist_cast_div_of_denom_le n).mono fun ε H r hr => by
    simpa only [Rat.cast_def] using H r.den hr r.num

中文:
定理 eventually_forall_le_dist_cast_rat_of_den_le
  条件: (hx : Irrational x) (n : 自然数)
  证明: (hx.eventually_forall_le_dist_cast_div_of_denom_le n).mono fun ε H r hr => by
    simpa only [Rat.cast_def] using H r.den hr r.num

Depends on / 依赖: Rat.cast_def, cast_def, eventually_forall_le_dist_cast_div_of_denom_le, hx.eventually_forall_le_dist_cast_div_of_denom_le, r.den, r.num
-/
theorem eventually_forall_le_dist_cast_rat_of_den_le (hx : Irrational x) (n : Nat) :
    forallᶠ ε : Real in 𝓝 0, forall r : Rat, r.den <= n -> ε <= dist x r :=
  (hx.eventually_forall_le_dist_cast_div_of_denom_le n).mono fun ε H r hr => by
    simpa only [Rat.cast_def] using H r.den hr r.num

end Irrational
