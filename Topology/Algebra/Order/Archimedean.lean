/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.GroupTheory.Archimedean
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Topology on archimedean groups and fields

In this file we prove the following theorems:

- `Rat.denseRange_cast`: the coercion from `ℚ` to a linear ordered archimedean field has dense
  range;

- `AddSubgroup.dense_of_not_isolated_zero`, `AddSubgroup.dense_of_no_min`: two sufficient conditions
  for a subgroup of an archimedean linear ordered additive commutative group to be dense;

- `AddSubgroup.dense_or_cyclic`: an additive subgroup of an archimedean linear ordered additive
  commutative group `G` with order topology either is dense in `G` or is a cyclic subgroup.
-/

public section

open Set

/--
theorem `Rat.denseRange_cast` / 定理 `Rat.denseRange_cast`

English:
theorem Rat.denseRange_cast
  statement: {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  proof: dense_of_exists_between fun _ _ h => Set.exists_range_iff.2 exists_rat_btwn h

中文:
定理 有理数.denseRange_cast
  结论: {𝕜} [域 𝕜] [线性序 𝕜] [是StrictOrdered环 𝕜]
  证明: dense_of_exists_between fun _ _ h => Set.exists_range_iff.2 exists_rat_btwn h

Depends on / 依赖: Set.exists_range_iff, dense_of_exists_between, exists_range_iff, exists_rat_btwn
-/
theorem Rat.denseRange_cast {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [Archimedean 𝕜] : DenseRange ((↑) : Rat -> 𝕜) :=
dense_of_exists_between fun _ _ h => Set.exists_range_iff.2 exists_rat_btwn h

namespace Subgroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
  [TopologicalSpace G] [OrderTopology G]
  [MulArchimedean G]

/-- A subgroup of an archimedean linear ordered multiplicative commutative group with order
topology is dense provided that for all `ε > 1` there exists an element of the subgroup
that belongs to `(1, ε)`. -/
@[to_additive /-- An additive subgroup of an archimedean linear ordered additive commutative group
with order topology is dense provided that for all positive `ε` there exists a positive element of
the subgroup that is less than `ε`. -/]
/--
theorem `dense_of_not_isolated_one` / 定理 `dense_of_not_isolated_one`

English:
theorem dense_of_not_isolated_one
  given: (S : Subgroup G) (hS : forall ε > 1, exists g in S, g in Ioo 1 ε)
  proof: by
  cases subsingleton_or_nontrivial G
  · refine fun x => _root_.subset_closure ?_
    rw [Subsingleton.elim x 1]
    exact one_mem S
  refine dense_of_exists_between fun a b hlt => ?_
  rcases hS (b / a) (one_lt_div'.2 hlt) with ⟨g, hgS, hg0, hg⟩
  rcases (existsUnique_add_zpow_mem_Ioc hg0 1 a).exists with ⟨m, hm⟩
  rw [one_mul] at hm
  refine ⟨g ^ m, zpow_mem hgS _, hm.1, hm.2.trans_lt ?_⟩
  rwa [lt_div_iff_mul_lt'] at hg

中文:
定理 dense_of_not_isolated_one
  条件: (S : 子群 G) (hS : 对任意 ε > 1, 存在 g in S, g in 开区间 1 ε)
  证明: by
  cases subsingleton_or_nontrivial G
  · refine fun x => _root_.subset_closure ?_
    rw [Subsingleton.elim x 1]
    exact one_mem S
  refine dense_of_exists_between fun a b hlt => ?_
  rcases hS (b / a) (one_lt_div'.2 hlt) with ⟨g, hgS, hg0, hg⟩
  rcases (existsUnique_add_zpow_mem_Ioc hg0 1 a).exists with ⟨m, hm⟩
  rw [one_mul] at hm
  refine ⟨g ^ m, zpow_mem hgS _, hm.1, hm.2.trans_lt ?_⟩
  rwa [lt_div_iff_mul_lt'] at hg

Depends on / 依赖: Subsingleton, Subsingleton.elim, _root_, _root_.subset_closure, dense_of_exists_between, existsUnique_add_zpow_mem_Ioc, lt_div_iff_mul_lt, one_lt_div, one_mem, one_mul, subset_closure, subsingleton_or_nontrivial, trans_lt, zpow_mem
-/
theorem dense_of_not_isolated_one (S : Subgroup G) (hS : forall ε > 1, exists g in S, g in Ioo 1 ε) :
    Dense (S : Set G) := by
  cases subsingleton_or_nontrivial G
  · refine fun x => _root_.subset_closure ?_
    rw [Subsingleton.elim x 1]
    exact one_mem S
  refine dense_of_exists_between fun a b hlt => ?_
  rcases hS (b / a) (one_lt_div'.2 hlt) with ⟨g, hgS, hg0, hg⟩
  rcases (existsUnique_add_zpow_mem_Ioc hg0 1 a).exists with ⟨m, hm⟩
  rw [one_mul] at hm
  refine ⟨g ^ m, zpow_mem hgS _, hm.1, hm.2.trans_lt ?_⟩
  rwa [lt_div_iff_mul_lt'] at hg

/-- Let `S` be a nontrivial subgroup in an archimedean linear ordered multiplicative commutative
group `G` with order topology. If the set of elements of `S` that are greater than one
does not have a minimal element, then `S` is dense `G`. -/
@[to_additive /-- Let `S` be a nontrivial additive subgroup in an archimedean linear ordered
additive commutative group `G` with order topology. If the set of positive elements of `S` does not
have a minimal element, then `S` is dense `G`. -/]
/--
theorem `dense_of_no_min` / 定理 `dense_of_no_min`

English:
theorem dense_of_no_min
  statement: (S : Subgroup G) (hbot : S != ⊥)
  proof: by
  refine S.dense_of_not_isolated_one fun ε ε1 => ?_
  contrapose! H
  exact exists_isLeast_one_lt hbot ε1 (disjoint_left.2 H)

中文:
定理 dense_of_no_min
  结论: (S : 子群 G) (hbot : S != ⊥)
  证明: by
  refine S.dense_of_not_isolated_one fun ε ε1 => ?_
  contrapose! H
  exact exists_isLeast_one_lt hbot ε1 (disjoint_left.2 H)

Depends on / 依赖: S.dense_of_not_isolated_one, contrapose, dense_of_not_isolated_one, disjoint_left, exists_isLeast_one_lt
-/
theorem dense_of_no_min (S : Subgroup G) (hbot : S != ⊥)
    (H : ¬exists a : G, IsLeast { g : G | g in S ∧ 1 < g } a) : Dense (S : Set G) := by
  refine S.dense_of_not_isolated_one fun ε ε1 => ?_
  contrapose! H
  exact exists_isLeast_one_lt hbot ε1 (disjoint_left.2 H)

/-- A subgroup of an archimedean linear ordered multiplicative commutative group `G` with order
topology either is dense in `G` or is a cyclic subgroup. -/
@[to_additive dense_or_cyclic
/-- An additive subgroup of an archimedean linear ordered additive commutative group `G`
with order topology either is dense in `G` or is a cyclic subgroup. -/]
/--
theorem `dense_or_cyclic` / 定理 `dense_or_cyclic`

English:
theorem dense_or_cyclic
  given: (S : Subgroup G)
  statement: Dense (S : Set G) ∨ exists a : G, S = closure {a}
  proof: by
  refine (em _).imp (dense_of_not_isolated_one S) fun h => ?_
  push Not at h
  rcases h with ⟨ε, ε1, hε⟩
  exact cyclic_of_isolated_one ε1 (disjoint_left.2 hε)

中文:
定理 dense_or_cyclic
  条件: (S : 子群 G)
  结论: 稠密 (S : 集合 G) ∨ 存在 a : G, S = closure {a}
  证明: by
  refine (em _).imp (dense_of_not_isolated_one S) fun h => ?_
  push Not at h
  rcases h with ⟨ε, ε1, hε⟩
  exact cyclic_of_isolated_one ε1 (disjoint_left.2 hε)

Depends on / 依赖: cyclic_of_isolated_one, dense_of_not_isolated_one, disjoint_left
-/
theorem dense_or_cyclic (S : Subgroup G) : Dense (S : Set G) ∨ exists a : G, S = closure {a} := by
  refine (em _).imp (dense_of_not_isolated_one S) fun h => ?_
  push Not at h
  rcases h with ⟨ε, ε1, hε⟩
  exact cyclic_of_isolated_one ε1 (disjoint_left.2 hε)

variable [Nontrivial G] [DenselyOrdered G]

/-- In a nontrivial densely linear ordered archimedean topological multiplicative group,
a subgroup is either dense or is cyclic, but not both.

For a non-exclusive `Or` version with weaker assumptions, see `Subgroup.dense_or_cyclic` above. -/
@[to_additive dense_xor_cyclic
/-- In a nontrivial densely linear ordered archimedean topological additive group,
a subgroup is either dense or is cyclic, but not both.

For a non-exclusive `Or` version with weaker assumptions, see `AddSubgroup.dense_or_cyclic` above.
-/]
/--
theorem `dense_xor_cyclic` / 定理 `dense_xor_cyclic`

English:
theorem dense_xor_cyclic
  given: (s : Subgroup G)
  proof: by
  if hd : Dense (s : Set G) then
    simp only [hd, xor_true]
    rintro ⟨a, rfl⟩
    exact not_denseRange_zpow hd
  else
    simp only [hd, xor_false, id, zpowers_eq_closure]
    exact s.dense_or_cyclic.resolve_left hd

@[to_additive (attr := deprecated dense_xor_cyclic (since := "2026-04-27"))]
alias dense_xor'_cyclic := dense_xor_cyclic

@[to_additive]

中文:
定理 dense_xor_cyclic
  条件: (s : 子群 G)
  证明: by
  if hd : Dense (s : Set G) then
    simp only [hd, xor_true]
    rintro ⟨a, rfl⟩
    exact not_denseRange_zpow hd
  else
    simp only [hd, xor_false, id, zpowers_eq_closure]
    exact s.dense_or_cyclic.resolve_left hd

@[to_additive (attr := deprecated dense_xor_cyclic (since := "2026-04-27"))]
alias dense_xor'_cyclic := dense_xor_cyclic

@[to_additive]

Depends on / 依赖: dense_or_cyclic, not_denseRange_zpow, resolve_left, s.dense_or_cyclic.resolve_left, xor_false, xor_true, zpowers_eq_closure
-/
theorem dense_xor_cyclic (s : Subgroup G) :
    Xor (Dense (s : Set G)) (exists a, s = .zpowers a) := by
  if hd : Dense (s : Set G) then
    simp only [hd, xor_true]
    rintro ⟨a, rfl⟩
    exact not_denseRange_zpow hd
  else
    simp only [hd, xor_false, id, zpowers_eq_closure]
    exact s.dense_or_cyclic.resolve_left hd

@[to_additive (attr := deprecated dense_xor_cyclic (since := "2026-04-27"))]
alias dense_xor'_cyclic := dense_xor_cyclic

@[to_additive]
/--
theorem `dense_iff_ne_zpowers` / 定理 `dense_iff_ne_zpowers`

English:
theorem dense_iff_ne_zpowers
  given: {s : Subgroup G}
  proof: by
  simp [xor_iff_iff_not.1 s.dense_xor_cyclic]

中文:
定理 dense_iff_ne_zpowers
  条件: {s : 子群 G}
  证明: by
  simp [xor_iff_iff_not.1 s.dense_xor_cyclic]

Depends on / 依赖: dense_xor_cyclic, s.dense_xor_cyclic, xor_iff_iff_not
-/
theorem dense_iff_ne_zpowers {s : Subgroup G} :
    Dense (s : Set G) ↔ forall a, s != .zpowers a := by
  simp [xor_iff_iff_not.1 s.dense_xor_cyclic]

end Subgroup
