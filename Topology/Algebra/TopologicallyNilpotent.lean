/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.RingTheory.Ideal.Basic

/-! # Topologically nilpotent elements

Let `M` be a monoid with zero `M`, endowed with a topology.

* `IsTopologicallyNilpotent a` says that `a : M` is *topologically nilpotent*,
  i.e., its powers converge to zero.

* `IsTopologicallyNilpotent.map`:
  The image of a topologically nilpotent element under a continuous morphism of
  monoids with zero endowed with a topology is topologically nilpotent.

* `IsTopologicallyNilpotent.zero`: `0` is topologically nilpotent.

Let `R` be a commutative ring with a linear topology.

* `IsTopologicallyNilpotent.mul_left`: if `a : R` is topologically nilpotent,
  then `a*b` is topologically nilpotent.

* `IsTopologicallyNilpotent.mul_right`: if `a : R` is topologically nilpotent,
  then `a * b` is topologically nilpotent.

* `IsTopologicallyNilpotent.add`: if `a b : R` are topologically nilpotent,
  then `a + b` is topologically nilpotent.

These lemmas are actually deduced from their analogues for commuting elements of rings.

-/

@[expose] public section

open Filter

open scoped Topology

/--
Definition of `IsTopologicallyNilpotent` / `IsTopologicallyNilpotent` 的定义

English:
definition IsTopologicallyNilpotent
  body: Tendsto (a ^ ·) atTop (𝓝 0)

中文:
定义 IsTopologicallyNilpotent
  定义体: Tendsto (a ^ ·) atTop (𝓝 0)

Depends on / 依赖: Tendsto
-/
def IsTopologicallyNilpotent
    {R : Type*} [MonoidWithZero R] [TopologicalSpace R] (a : R) : Prop :=
  Tendsto (a ^ ·) atTop (𝓝 0)

namespace IsTopologicallyNilpotent

section MonoidWithZero

variable {R S : Type*} [TopologicalSpace R] [MonoidWithZero R]
  [MonoidWithZero S] [TopologicalSpace S]

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S]
  proof: by
  unfold IsTopologicallyNilpotent at ha ⊢
  simp_rw [← map_pow]
  exact (map_zero φ ▸ hφ.tendsto 0).comp ha

中文:
定理 map
  结论: {F : 类型} [FunLike F R S] [MonoidWithZeroHomClass F R S]
  证明: by
  unfold IsTopologicallyNilpotent at ha ⊢
  simp_rw [← map_pow]
  exact (map_zero φ ▸ hφ.tendsto 0).comp ha

Depends on / 依赖: IsTopologicallyNilpotent, map_pow, map_zero, simp_rw, tendsto
-/
theorem map {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S]
    {φ : F} (hφ : Continuous φ) {a : R} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (φ a) := by
  unfold IsTopologicallyNilpotent at ha ⊢
  simp_rw [← map_pow]
  exact (map_zero φ ▸ hφ.tendsto 0).comp ha

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: IsTopologicallyNilpotent (0 : R)
  proof: tendsto_atTop_of_eventually_const (i₀ := 1)
    (fun _ hi => by rw [zero_pow (Nat.ne_zero_iff_zero_lt.mpr hi)])

中文:
定理 zero
  结论: IsTopologicallyNilpotent (0 : R)
  证明: tendsto_atTop_of_eventually_const (i₀ := 1)
    (fun _ hi => by rw [zero_pow (Nat.ne_zero_iff_zero_lt.mpr hi)])

Depends on / 依赖: Nat.ne_zero_iff_zero_lt.mpr, ne_zero_iff_zero_lt, tendsto_atTop_of_eventually_const, zero_pow
-/
theorem zero : IsTopologicallyNilpotent (0 : R) :=
  tendsto_atTop_of_eventually_const (i₀ := 1)
    (fun _ hi => by rw [zero_pow (Nat.ne_zero_iff_zero_lt.mpr hi)])

/--
theorem `_root_.IsNilpotent.isTopologicallyNilpotent` / 定理 `_root_.IsNilpotent.isTopologicallyNilpotent`

English:
theorem _root_.IsNilpotent.isTopologicallyNilpotent
  given: {a : R} (ha : IsNilpotent a)
  proof: by
  obtain ⟨n, hn⟩ := ha
  apply tendsto_atTop_of_eventually_const (i₀ := n)
  intro i hi
  rw [← Nat.add_sub_of_le hi]; rw [pow_add]; rw [hn]; rw [zero_mul]

中文:
定理 _root_.IsNilpotent.isTopologicallyNilpotent
  条件: {a : R} (ha : IsNilpotent a)
  证明: by
  obtain ⟨n, hn⟩ := ha
  apply tendsto_atTop_of_eventually_const (i₀ := n)
  intro i hi
  rw [← Nat.add_sub_of_le hi]; rw [pow_add]; rw [hn]; rw [zero_mul]

Depends on / 依赖: Nat.add_sub_of_le, add_sub_of_le, pow_add, tendsto_atTop_of_eventually_const, zero_mul
-/
theorem _root_.IsNilpotent.isTopologicallyNilpotent {a : R} (ha : IsNilpotent a) :
    IsTopologicallyNilpotent a := by
  obtain ⟨n, hn⟩ := ha
  apply tendsto_atTop_of_eventually_const (i₀ := n)
  intro i hi
  rw [← Nat.add_sub_of_le hi]; rw [pow_add]; rw [hn]; rw [zero_mul]

/--
theorem `exists_pow_mem_of_mem_nhds` / 定理 `exists_pow_mem_of_mem_nhds`

English:
theorem exists_pow_mem_of_mem_nhds
  statement: {a : R} (ha : IsTopologicallyNilpotent a)
  proof: (ha.eventually_mem hv).exists

中文:
定理 exists_pow_mem_of_mem_nhds
  结论: {a : R} (ha : IsTopologicallyNilpotent a)
  证明: (ha.eventually_mem hv).exists

Depends on / 依赖: eventually_mem, ha.eventually_mem
-/
theorem exists_pow_mem_of_mem_nhds {a : R} (ha : IsTopologicallyNilpotent a)
    {v : Set R} (hv : v in 𝓝 0) :
    exists n, a ^ n in v :=
  (ha.eventually_mem hv).exists

end MonoidWithZero

section Ring

variable {R : Type*} [TopologicalSpace R] [Ring R]

/--
theorem `mul_right_of_commute` / 定理 `mul_right_of_commute`

English:
theorem mul_right_of_commute
  statement: [IsLinearTopology Rᵐᵒᵖ R]
  proof: by
  simp_rw [IsTopologicallyNilpotent, hab.mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_left _ _ ha

中文:
定理 mul_right_of_commute
  结论: [IsLinearTopology Rᵐᵒᵖ R]
  证明: by
  simp_rw [IsTopologicallyNilpotent, hab.mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_left _ _ ha

Depends on / 依赖: IsLinearTopology, IsLinearTopology.tendsto_mul_zero_of_left, IsTopologicallyNilpotent, hab.mul_pow, mul_pow, simp_rw, tendsto_mul_zero_of_left
-/
theorem mul_right_of_commute [IsLinearTopology Rᵐᵒᵖ R]
    {a b : R} (ha : IsTopologicallyNilpotent a) (hab : Commute a b) :
    IsTopologicallyNilpotent (a * b) := by
  simp_rw [IsTopologicallyNilpotent, hab.mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_left _ _ ha

/--
theorem `mul_left_of_commute` / 定理 `mul_left_of_commute`

English:
theorem mul_left_of_commute
  statement: [IsLinearTopology R R] {a b : R}
  proof: by
  simp_rw [IsTopologicallyNilpotent, hab.mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_right _ _ hb

中文:
定理 mul_left_of_commute
  结论: [IsLinearTopology R R] {a b : R}
  证明: by
  simp_rw [IsTopologicallyNilpotent, hab.mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_right _ _ hb

Depends on / 依赖: IsLinearTopology, IsLinearTopology.tendsto_mul_zero_of_right, IsTopologicallyNilpotent, hab.mul_pow, mul_pow, simp_rw, tendsto_mul_zero_of_right
-/
theorem mul_left_of_commute [IsLinearTopology R R] {a b : R}
    (hb : IsTopologicallyNilpotent b) (hab : Commute a b) :
    IsTopologicallyNilpotent (a * b) := by
  simp_rw [IsTopologicallyNilpotent, hab.mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_right _ _ hb

/--
theorem `add_of_commute` / 定理 `add_of_commute`

English:
theorem add_of_commute
  statement: [IsLinearTopology R R] {a b : R}
  proof: by
  simp only [IsTopologicallyNilpotent, atTop_basis.tendsto_iff IsLinearTopology.hasBasis_ideal,
    true_and]
  intro I I_mem_nhds
  obtain ⟨na, ha⟩ := ha.exists_pow_mem_of_mem_nhds I_mem_nhds
  obtain ⟨nb, hb⟩ := hb.exists_pow_mem_of_mem_nhds I_mem_nhds
  exact ⟨na + nb, fun m hm =>
    I.add_po

中文:
定理 add_of_commute
  结论: [IsLinearTopology R R] {a b : R}
  证明: by
  simp only [IsTopologicallyNilpotent, atTop_basis.tendsto_iff IsLinearTopology.hasBasis_ideal,
    true_and]
  intro I I_mem_nhds
  obtain ⟨na, ha⟩ := ha.exists_pow_mem_of_mem_nhds I_mem_nhds
  obtain ⟨nb, hb⟩ := hb.exists_pow_mem_of_mem_nhds I_mem_nhds
  exact ⟨na + nb, fun m hm =>
    I.add_po

Depends on / 依赖: I.add_pow_mem_of_pow_mem_of_le_of_commute, I_mem_nhds, IsLinearTopology, IsLinearTopology.hasBasis_ideal, IsTopologicallyNilpotent, Nat.le_add_right, add_pow_mem_of_pow_mem_of_le_of_commute, atTop_basis, atTop_basis.tendsto_iff, exists_pow_mem_of_mem_nhds, ha.exists_pow_mem_of_mem_nhds, hasBasis_ideal, hb.exists_pow_mem_of_mem_nhds, le_add_right, le_trans, tendsto_iff, true_and
-/
theorem add_of_commute [IsLinearTopology R R] {a b : R}
    (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) (h : Commute a b) :
    IsTopologicallyNilpotent (a + b) := by
  simp only [IsTopologicallyNilpotent, atTop_basis.tendsto_iff IsLinearTopology.hasBasis_ideal,
    true_and]
  intro I I_mem_nhds
  obtain ⟨na, ha⟩ := ha.exists_pow_mem_of_mem_nhds I_mem_nhds
  obtain ⟨nb, hb⟩ := hb.exists_pow_mem_of_mem_nhds I_mem_nhds
  exact ⟨na + nb, fun m hm =>
    I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb (le_trans hm (Nat.le_add_right _ _)) h⟩

end Ring

section CommRing

variable {R : Type*} [TopologicalSpace R] [CommRing R] [IsLinearTopology R R]

/--
theorem `mul_right` / 定理 `mul_right`

English:
theorem mul_right
  given: {a : R} (ha : IsTopologicallyNilpotent a) (b : R)
  proof: ha.mul_right_of_commute (Commute.all ..)

中文:
定理 mul_right
  条件: {a : R} (ha : IsTopologicallyNilpotent a) (b : R)
  证明: ha.mul_right_of_commute (Commute.all ..)

Depends on / 依赖: Commute, Commute.all, ha.mul_right_of_commute, mul_right_of_commute
-/
theorem mul_right {a : R} (ha : IsTopologicallyNilpotent a) (b : R) :
    IsTopologicallyNilpotent (a * b) :=
  ha.mul_right_of_commute (Commute.all ..)

/--
theorem `mul_left` / 定理 `mul_left`

English:
theorem mul_left
  given: (a : R) {b : R} (hb : IsTopologicallyNilpotent b)
  proof: hb.mul_left_of_commute (Commute.all ..)

中文:
定理 mul_left
  条件: (a : R) {b : R} (hb : IsTopologicallyNilpotent b)
  证明: hb.mul_left_of_commute (Commute.all ..)

Depends on / 依赖: Commute, Commute.all, hb.mul_left_of_commute, mul_left_of_commute
-/
theorem mul_left (a : R) {b : R} (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a * b) :=
  hb.mul_left_of_commute (Commute.all ..)

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b)
  proof: ha.add_of_commute hb (Commute.all ..)

中文:
定理 add
  条件: {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b)
  证明: ha.add_of_commute hb (Commute.all ..)

Depends on / 依赖: Commute, Commute.all, add_of_commute, ha.add_of_commute
-/
theorem add {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) :=
  ha.add_of_commute hb (Commute.all ..)

variable (R) in
/-- The topological nilradical of a ring with a linear topology -/
@[simps]
/--
Definition of `_root_.topologicalNilradical` / `_root_.topologicalNilradical` 的定义

English:
definition _root_.topologicalNilradical
  signature: : Ideal R where
  body: {a | IsTopologicallyNilpotent a}
  add_mem' := add
  zero_mem' := zero
  smul_mem' := mul_left

中文:
定义 _root_.topologicalNilradical
  签名: : Ideal R where
  定义体: {a | IsTopologicallyNilpotent a}
  add_mem' := add
  zero_mem' := zero
  smul_mem' := mul_left

Depends on / 依赖: IsTopologicallyNilpotent
-/
def _root_.topologicalNilradical : Ideal R where
  carrier := {a | IsTopologicallyNilpotent a}
  add_mem' := add
  zero_mem' := zero
  smul_mem' := mul_left

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_topologicalNilradical_iff` / 定理 `mem_topologicalNilradical_iff`

English:
theorem mem_topologicalNilradical_iff
  given: {a : R}
  proof: by
  simp [topologicalNilradical]

中文:
定理 mem_topologicalNilradical_iff
  条件: {a : R}
  证明: by
  simp [topologicalNilradical]

Depends on / 依赖: topologicalNilradical
-/
theorem mem_topologicalNilradical_iff {a : R} :
    a in topologicalNilradical R ↔ IsTopologicallyNilpotent a := by
  simp [topologicalNilradical]

end CommRing

end IsTopologicallyNilpotent
