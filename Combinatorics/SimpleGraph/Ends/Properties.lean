/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
public import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Properties of the ends of graphs

This file is meant to contain results about the ends of (locally finite connected) graphs.

-/

public section


variable {V : Type} (G : SimpleGraph V)

namespace SimpleGraph

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: V] : IsEmpty G.end where
  body: by
    rintro ⟨s, _⟩
    cases nonempty_fintype V
    obtain ⟨v, h⟩ := (s <| Opposite.op Finset.univ).nonempty
    exact Set.disjoint_iff.mp (s _).disjoint_right
        ⟨by simp only [Finset.coe_univ, Set.mem_univ], h⟩

中文:
实例 [有限
  签名: V] : 是空 G.end where
  定义体: by
    rintro ⟨s, _⟩
    cases nonempty_fintype V
    obtain ⟨v, h⟩ := (s <| Opposite.op Finset.univ).nonempty
    exact Set.disjoint_iff.mp (s _).disjoint_right
        ⟨by simp only [Finset.coe_univ, Set.mem_univ], h⟩

Depends on / 依赖: Finset, Finset.coe_univ, Finset.univ, Opposite, Opposite.op, Set.disjoint_iff.mp, Set.mem_univ, coe_univ, disjoint_iff, disjoint_right, mem_univ, nonempty, nonempty_fintype
-/
instance [Finite V] : IsEmpty G.end where
  false := by
    rintro ⟨s, _⟩
    cases nonempty_fintype V
    obtain ⟨v, h⟩ := (s <| Opposite.op Finset.univ).nonempty
    exact Set.disjoint_iff.mp (s _).disjoint_right
        ⟨by simp only [Finset.coe_univ, Set.mem_univ], h⟩

/--
lemma `end_componentCompl_infinite` / 引理 `end_componentCompl_infinite`

English:
lemma end_componentCompl_infinite
  given: (e : G.end) (K : (Finset V)ᵒᵖ)
  proof: by
  refine (e.val K).infinite_iff_in_all_ranges.mpr (fun L h => ?_)
  change Opposite.unop K subseteq Opposite.unop (Opposite.op L) at h
  exact ⟨e.val (Opposite.op L), (e.prop (CategoryTheory.opHomOfLE h))⟩

中文:
引理 end_componentCompl_infinite
  条件: (e : G.end) (K : (有限集 V)ᵒᵖ)
  证明: by
  refine (e.val K).infinite_iff_in_all_ranges.mpr (fun L h => ?_)
  change Opposite.unop K subseteq Opposite.unop (Opposite.op L) at h
  exact ⟨e.val (Opposite.op L), (e.prop (CategoryTheory.opHomOfLE h))⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.opHomOfLE, Opposite, Opposite.op, Opposite.unop, e.prop, e.val, infinite_iff_in_all_ranges, infinite_iff_in_all_ranges.mpr, opHomOfLE, subseteq
-/
lemma end_componentCompl_infinite (e : G.end) (K : (Finset V)ᵒᵖ) :
    ((e : (j : (Finset V)ᵒᵖ) -> G.componentComplFunctor.obj j) K).supp.Infinite := by
  refine (e.val K).infinite_iff_in_all_ranges.mpr (fun L h => ?_)
  change Opposite.unop K subseteq Opposite.unop (Opposite.op L) at h
  exact ⟨e.val (Opposite.op L), (e.prop (CategoryTheory.opHomOfLE h))⟩

/--
Instance `componentComplFunctor_nonempty_of_infinite` / 实例 `componentComplFunctor_nonempty_of_infinite`

English:
instance componentComplFunctor_nonempty_of_infinite
  signature: [Infinite V] (K : (Finset V)ᵒᵖ)
  body: G.componentCompl_nonempty_of_infinite K.unop

中文:
实例 componentComplFunctor_nonempty_of_infinite
  签名: [无限 V] (K : (有限集 V)ᵒᵖ)
  定义体: G.componentCompl_nonempty_of_infinite K.unop

Depends on / 依赖: G.componentCompl_nonempty_of_infinite, K.unop, componentCompl_nonempty_of_infinite
-/
instance componentComplFunctor_nonempty_of_infinite [Infinite V] (K : (Finset V)ᵒᵖ) :
    Nonempty (G.componentComplFunctor.obj K) := G.componentCompl_nonempty_of_infinite K.unop

/--
Instance `componentComplFunctor_finite` / 实例 `componentComplFunctor_finite`

English:
instance componentComplFunctor_finite
  signature: [LocallyFinite G] [Fact G.Preconnected]
  body: G.componentCompl_finite K.unop

中文:
实例 componentComplFunctor_finite
  签名: [局部有限 G] [Fact G.预连通]
  定义体: G.componentCompl_finite K.unop

Depends on / 依赖: G.componentCompl_finite, K.unop, componentCompl_finite
-/
instance componentComplFunctor_finite [LocallyFinite G] [Fact G.Preconnected]
    (K : (Finset V)ᵒᵖ) : Finite (G.componentComplFunctor.obj K) := G.componentCompl_finite K.unop

/--
lemma `nonempty_ends_of_infinite` / 引理 `nonempty_ends_of_infinite`

English:
lemma nonempty_ends_of_infinite
  given: [LocallyFinite G] [Fact G.Preconnected] [Infinite V]
  proof: by
  apply nonempty_sections_of_finite_inverse_system G.componentComplFunctor

中文:
引理 nonempty_ends_of_infinite
  条件: [局部有限 G] [Fact G.预连通] [无限 V]
  证明: by
  apply nonempty_sections_of_finite_inverse_system G.componentComplFunctor

Depends on / 依赖: G.componentComplFunctor, componentComplFunctor, nonempty_sections_of_finite_inverse_system
-/
lemma nonempty_ends_of_infinite [LocallyFinite G] [Fact G.Preconnected] [Infinite V] :
    G.end.Nonempty := by
  apply nonempty_sections_of_finite_inverse_system G.componentComplFunctor

end SimpleGraph
