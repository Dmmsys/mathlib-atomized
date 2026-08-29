/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Sigma-algebra on simple graphs

In this file, we pull back the sigma-algebra on `V → V → Prop` to a sigma-algebra on
`SimpleGraph V` and prove that common operations are measurable.
-/

public section

open MeasureTheory
open scoped Finset

namespace SimpleGraph
variable {V : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MeasurableSpace (SimpleGraph V)
  body: .comap Adj inferInstance

中文:
实例 :
  签名: MeasurableSpace (SimpleGraph V)
  定义体: .comap Adj inferInstance
-/
instance : MeasurableSpace (SimpleGraph V) := .comap Adj inferInstance

/--
lemma `measurable_iff_adj` / 引理 `measurable_iff_adj`

English:
lemma measurable_iff_adj
  given: {Ω : Type*} {m : MeasurableSpace Ω} {G : Ω -> SimpleGraph V}
  proof: by
  simp [measurable_comap_iff, measurable_pi_iff]

@[fun_prop]

中文:
引理 measurable_iff_adj
  条件: {Ω : 类型} {m : MeasurableSpace Ω} {G : Ω -> SimpleGraph V}
  证明: by
  simp [measurable_comap_iff, measurable_pi_iff]

@[fun_prop]

Depends on / 依赖: measurable_comap_iff, measurable_pi_iff
-/
lemma measurable_iff_adj {Ω : Type*} {m : MeasurableSpace Ω} {G : Ω -> SimpleGraph V} :
    Measurable G ↔ forall u v, Measurable fun ω => (G ω).Adj u v := by
  simp [measurable_comap_iff, measurable_pi_iff]

@[fun_prop]
/--
lemma `measurable_adj` / 引理 `measurable_adj`

English:
lemma measurable_adj
  statement: Measurable (Adj : SimpleGraph V -> V -> V -> Prop)
  proof: comap_measurable _

@[fun_prop]

中文:
引理 measurable_adj
  结论: Measurable (Adj : SimpleGraph V -> V -> V -> 命题)
  证明: comap_measurable _

@[fun_prop]

Depends on / 依赖: comap_measurable
-/
lemma measurable_adj : Measurable (Adj : SimpleGraph V -> V -> V -> Prop) := comap_measurable _

@[fun_prop]
/--
lemma `measurable_edgeSet` / 引理 `measurable_edgeSet`

English:
lemma measurable_edgeSet
  statement: Measurable (edgeSet : SimpleGraph V -> Set (Sym2 V))
  proof: measurable_set_iff.2 by rintro ⟨u, v⟩; simp only [mem_edgeSet]; fun_prop

@[simp, fun_prop]

中文:
引理 measurable_edgeSet
  结论: Measurable (edgeSet : SimpleGraph V -> Set (Sym2 V))
  证明: measurable_set_iff.2 by rintro ⟨u, v⟩; simp only [mem_edgeSet]; fun_prop

@[simp, fun_prop]

Depends on / 依赖: fun_prop, measurable_set_iff, mem_edgeSet
-/
lemma measurable_edgeSet : Measurable (edgeSet : SimpleGraph V -> Set (Sym2 V)) :=
measurable_set_iff.2 by rintro ⟨u, v⟩; simp only [mem_edgeSet]; fun_prop

@[simp, fun_prop]
/--
lemma `measurable_fromEdgeSet` / 引理 `measurable_fromEdgeSet`

English:
lemma measurable_fromEdgeSet
  statement: Measurable (fromEdgeSet : Set (Sym2 V) -> SimpleGraph V)
  proof: by
  simp only [measurable_iff_adj, fromEdgeSet_adj, ne_eq]; fun_prop

中文:
引理 measurable_fromEdgeSet
  结论: Measurable (fromEdgeSet : Set (Sym2 V) -> SimpleGraph V)
  证明: by
  simp only [measurable_iff_adj, fromEdgeSet_adj, ne_eq]; fun_prop

Depends on / 依赖: fromEdgeSet_adj, fun_prop, measurable_iff_adj, ne_eq
-/
lemma measurable_fromEdgeSet : Measurable (fromEdgeSet : Set (Sym2 V) -> SimpleGraph V) := by
  simp only [measurable_iff_adj, fromEdgeSet_adj, ne_eq]; fun_prop

/--
lemma `measurableEmbedding_edgeSet` / 引理 `measurableEmbedding_edgeSet`

English:
lemma measurableEmbedding_edgeSet
  given: [Countable V]
  proof: edgeSet_injective
  measurable := measurable_edgeSet
  measurableSet_image' s hs := by
    simp only [← measurable_mem, Set.mem_image, edgeSet_eq_iff, ↓existsAndEq, true_and,
      Set.disjoint_right]
refine .and (hs.mem.comp measurable_fromEdgeSet) .forall fun e => .imp ?_ ?_ <;> fun_prop

中文:
引理 measurableEmbedding_edgeSet
  条件: [Countable V]
  证明: edgeSet_injective
  measurable := measurable_edgeSet
  measurableSet_image' s hs := by
    simp only [← measurable_mem, Set.mem_image, edgeSet_eq_iff, ↓existsAndEq, true_and,
      Set.disjoint_right]
refine .and (hs.mem.comp measurable_fromEdgeSet) .forall fun e => .imp ?_ ?_ <;> fun_prop

Depends on / 依赖: edgeSet_injective
-/
lemma measurableEmbedding_edgeSet [Countable V] :
    MeasurableEmbedding (edgeSet : SimpleGraph V -> Set (Sym2 V)) where
  injective := edgeSet_injective
  measurable := measurable_edgeSet
  measurableSet_image' s hs := by
    simp only [← measurable_mem, Set.mem_image, edgeSet_eq_iff, ↓existsAndEq, true_and,
      Set.disjoint_right]
refine .and (hs.mem.comp measurable_fromEdgeSet) .forall fun e => .imp ?_ ?_ <;> fun_prop

end SimpleGraph
