/-
Copyright (c) 2025 Jasper Mulder-Sohn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent, Jasper Mulder-Sohn
-/
module

public import Mathlib.Data.Set.Pairwise.Lattice
public import Mathlib.Order.Preorder.Chain

/-!
# Pairwise results for chains

In this file `Pairwise` results are applied to chains of sets.
-/

public section

open Set

variable {α β : Type*} {c : Set (Set α)} {r : α -> α -> Prop}
variable (hc : IsChain (· subseteq ·) c)

namespace IsChain

include hc

/--
lemma `pairwise_iUnion₂` / 引理 `pairwise_iUnion₂`

English:
lemma pairwise_iUnion₂
  statement: (⋃ s in c, s).Pairwise r ↔ forall s in c, s.Pairwise r
  proof: pairwise_iUnion₂_iff hc.directedOn

中文:
引理 pairwise_iUnion₂
  结论: (⋃ s in c, s).Pairwise r ↔ 对任意 s in c, s.Pairwise r
  证明: pairwise_iUnion₂_iff hc.directedOn

Depends on / 依赖: directedOn, hc.directedOn
-/
lemma pairwise_iUnion₂ : (⋃ s in c, s).Pairwise r ↔ forall s in c, s.Pairwise r :=
  pairwise_iUnion₂_iff hc.directedOn

/--
lemma `pairwiseDisjoint_iUnion₂` / 引理 `pairwiseDisjoint_iUnion₂`

English:
lemma pairwiseDisjoint_iUnion₂
  given: [PartialOrder β] [OrderBot β] (f : α -> β)
  proof: hc.pairwise_iUnion₂

中文:
引理 pairwiseDisjoint_iUnion₂
  条件: [PartialOrder β] [OrderBot β] (f : α -> β)
  证明: hc.pairwise_iUnion₂

Depends on / 依赖: hc.pairwise_iUnion
-/
lemma pairwiseDisjoint_iUnion₂ [PartialOrder β] [OrderBot β] (f : α -> β) :
    (⋃ s in c, s).PairwiseDisjoint f ↔ forall s in c, s.PairwiseDisjoint f :=
  hc.pairwise_iUnion₂

/--
lemma `pairwise_sUnion` / 引理 `pairwise_sUnion`

English:
lemma pairwise_sUnion
  statement: (⋃₀ c).Pairwise r ↔ forall s in c, s.Pairwise r
  proof: Set.pairwise_sUnion hc.directedOn

中文:
引理 pairwise_sUnion
  结论: (⋃₀ c).Pairwise r ↔ 对任意 s in c, s.Pairwise r
  证明: Set.pairwise_sUnion hc.directedOn

Depends on / 依赖: Set.pairwise_sUnion, directedOn, hc.directedOn, pairwise_sUnion
-/
lemma pairwise_sUnion : (⋃₀ c).Pairwise r ↔ forall s in c, s.Pairwise r :=
  Set.pairwise_sUnion hc.directedOn

/--
lemma `pairwiseDisjoint_sUnion` / 引理 `pairwiseDisjoint_sUnion`

English:
lemma pairwiseDisjoint_sUnion
  given: [PartialOrder β] [OrderBot β] (f : α -> β)
  proof: hc.pairwise_sUnion

中文:
引理 pairwiseDisjoint_sUnion
  条件: [PartialOrder β] [OrderBot β] (f : α -> β)
  证明: hc.pairwise_sUnion

Depends on / 依赖: hc.pairwise_sUnion, pairwise_sUnion
-/
lemma pairwiseDisjoint_sUnion [PartialOrder β] [OrderBot β] (f : α -> β) :
    (⋃₀ c).PairwiseDisjoint f ↔ forall s in c, s.PairwiseDisjoint f :=
  hc.pairwise_sUnion

end IsChain
