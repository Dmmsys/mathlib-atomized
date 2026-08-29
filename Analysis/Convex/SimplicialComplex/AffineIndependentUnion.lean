/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Simplicial complexes from affinely independent points

This file provides constructions for simplicial complexes where the vertices
are affinely independent.

## Main declarations

* `Geometry.SimplicialComplex.ofAffineIndependent`: Construct a simplicial complex from a
  downward-closed set of faces whose union of vertices is affinely independent.
* `Geometry.SimplicialComplex.onFinsupp`: Construct a simplicial complex on `ι →₀ 𝕜` from a
  downward-closed set of finite subsets of `ι`, using the standard basis vectors.
* `Geometry.SimplicialComplex.ofSimpleGraph`: Construct a simplicial complex from a simple graph,
  where vertices of the graph are 0-simplices and edges are 1-simplices.
-/

@[expose] public section

open Finset Set

namespace Geometry

namespace AbstractSimplicialComplex

/--
Definition of `ofSimpleGraph` / `ofSimpleGraph` 的定义

English:
definition ofSimpleGraph
  signature: {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι)
  body: ({s : Finset ι | exists v, s = {v}}) union Sym2.toFinset '' G.edgeSet
  isRelLowerSet_faces := by
    intro s hs
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_image] at hs
    rcases hs with ⟨v, rfl⟩ | ⟨e, he, rfl⟩
    · simp
    · constructor
      · exact Finset.nonempty_iff_ne_empty.mp

中文:
定义 ofSimpleGraph
  签名: {ι : 类型} [DecidableEq ι] (G : SimpleGraph ι)
  定义体: ({s : Finset ι | exists v, s = {v}}) union Sym2.toFinset '' G.edgeSet
  isRelLowerSet_faces := by
    intro s hs
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_image] at hs
    rcases hs with ⟨v, rfl⟩ | ⟨e, he, rfl⟩
    · simp
    · constructor
      · exact Finset.nonempty_iff_ne_empty.mp

Depends on / 依赖: Finset, G.edgeSet, Sym2.toFinset, edgeSet, toFinset
-/
def ofSimpleGraph {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) :
    AbstractSimplicialComplex ι where
  faces := ({s : Finset ι | exists v, s = {v}}) union Sym2.toFinset '' G.edgeSet
  isRelLowerSet_faces := by
    intro s hs
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_image] at hs
    rcases hs with ⟨v, rfl⟩ | ⟨e, he, rfl⟩
    · simp
    · constructor
      · exact Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty e)
      · intro b hb_sub hb_nonempty
        by_cases h : b.card = 1 <;>
          grind [Finset.card_eq_one, Finset.eq_of_subset_of_card_le hb_sub, Sym2.card_toFinset]
  singleton_mem := by
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_image]
    intro v
    exact Or.inl ⟨v, rfl⟩

end AbstractSimplicialComplex

namespace SimplicialComplex

/--
Definition of `ofAffineIndependent` / `ofAffineIndependent` 的定义

English:
definition ofAffineIndependent
  signature: {𝕜 E}
  body: abstract
  indep {s} hs := indep.mono (Set.subset_biUnion_of_mem hs)
  inter_subset_convexHull {s t} hs ht := by
    apply subset_of_eq
    rw [AffineIndependent.convexHull_inter (R := 𝕜) (s := s union t)]
    · apply indep.mono
      simp only [Finset.coe_union]
      exact Set.union_subset (Set.su

中文:
定义 ofAffineIndependent
  签名: {𝕜 E}
  定义体: abstract
  indep {s} hs := indep.mono (Set.subset_biUnion_of_mem hs)
  inter_subset_convexHull {s t} hs ht := by
    apply subset_of_eq
    rw [AffineIndependent.convexHull_inter (R := 𝕜) (s := s union t)]
    · apply indep.mono
      simp only [Finset.coe_union]
      exact Set.union_subset (Set.su

Depends on / 依赖: abstract
-/
def ofAffineIndependent {𝕜 E}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DecidableEq E] [AddCommGroup E] [Module 𝕜 E]
    (abstract : PreAbstractSimplicialComplex E)
    (indep : AffineIndependent 𝕜 (Subtype.val : (⋃ s in abstract.faces, (s : Set E)) -> E)) :
    SimplicialComplex 𝕜 E where
  toPreAbstractSimplicialComplex := abstract
  indep {s} hs := indep.mono (Set.subset_biUnion_of_mem hs)
  inter_subset_convexHull {s t} hs ht := by
    apply subset_of_eq
    rw [AffineIndependent.convexHull_inter (R := 𝕜) (s := s union t)]
    · apply indep.mono
      simp only [Finset.coe_union]
      exact Set.union_subset (Set.subset_biUnion_of_mem hs) (Set.subset_biUnion_of_mem ht)
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right

/--
Definition of `onFinsupp` / `onFinsupp` 的定义

English:
definition onFinsupp
  signature: {𝕜 ι : Type*} [DecidableEq ι]
  body: ofAffineIndependent (𝕜 := 𝕜) (E := ι ->₀ 𝕜)
    (abstract.map (fun i => Finsupp.single i (1 : 𝕜)))
    (by
      refine (Finsupp.linearIndependent_single_one 𝕜 ι).affineIndependent.range.mono fun x hx => ?_
      simp only [Set.mem_iUnion, Finset.mem_coe] at hx
      obtain ⟨_, ⟨_, _, rfl⟩, hx⟩ := h

中文:
定义 onFinsupp
  签名: {𝕜 ι : 类型} [DecidableEq ι]
  定义体: ofAffineIndependent (𝕜 := 𝕜) (E := ι ->₀ 𝕜)
    (abstract.map (fun i => Finsupp.single i (1 : 𝕜)))
    (by
      refine (Finsupp.linearIndependent_single_one 𝕜 ι).affineIndependent.range.mono fun x hx => ?_
      simp only [Set.mem_iUnion, Finset.mem_coe] at hx
      obtain ⟨_, ⟨_, _, rfl⟩, hx⟩ := h

Depends on / 依赖: Finset, Finset.mem_coe, Finsupp, Finsupp.linearIndependent_single_one, Finsupp.single, Set.mem_iUnion, abstract, abstract.map, affineIndependent, affineIndependent.range.mono, linearIndependent_single_one, mem_coe, mem_iUnion, ofAffineIndependent, single
-/
noncomputable def onFinsupp {𝕜 ι : Type*} [DecidableEq ι]
    [DecidableEq 𝕜] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (abstract : PreAbstractSimplicialComplex ι) :
    SimplicialComplex 𝕜 (ι ->₀ 𝕜) :=
  ofAffineIndependent (𝕜 := 𝕜) (E := ι ->₀ 𝕜)
    (abstract.map (fun i => Finsupp.single i (1 : 𝕜)))
    (by
      refine (Finsupp.linearIndependent_single_one 𝕜 ι).affineIndependent.range.mono fun x hx => ?_
      simp only [Set.mem_iUnion, Finset.mem_coe] at hx
      obtain ⟨_, ⟨_, _, rfl⟩, hx⟩ := hx
      grind)

/--
Definition of `ofSimpleGraph` / `ofSimpleGraph` 的定义

English:
definition ofSimpleGraph
  signature: {𝕜 V : Type*} [DecidableEq V] [DecidableEq 𝕜]
  body: onFinsupp (AbstractSimplicialComplex.ofSimpleGraph G).toPreAbstractSimplicialComplex

中文:
定义 ofSimpleGraph
  签名: {𝕜 V : 类型} [DecidableEq V] [DecidableEq 𝕜]
  定义体: onFinsupp (AbstractSimplicialComplex.ofSimpleGraph G).toPreAbstractSimplicialComplex

Depends on / 依赖: AbstractSimplicialComplex, AbstractSimplicialComplex.ofSimpleGraph, ofSimpleGraph, onFinsupp, toPreAbstractSimplicialComplex
-/
noncomputable def ofSimpleGraph {𝕜 V : Type*} [DecidableEq V] [DecidableEq 𝕜]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (G : SimpleGraph V) :
    SimplicialComplex 𝕜 (V ->₀ 𝕜) :=
  onFinsupp (AbstractSimplicialComplex.ofSimpleGraph G).toPreAbstractSimplicialComplex

end SimplicialComplex

end Geometry
