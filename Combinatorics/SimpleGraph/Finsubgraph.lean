/-
Copyright (c) 2022 Joanna Choules. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joanna Choules
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Homomorphisms from finite subgraphs

This file defines the type of finite subgraphs of a `SimpleGraph` and proves a compactness result
for homomorphisms to a finite codomain.

## Main statements

* `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`: If every finite subgraph of a (possibly
  infinite) graph `G` has a homomorphism to some finite graph `F`, then there is also a homomorphism
  `G →g F`.

## Notation

`→fg` is a module-local variant on `→g` where the domain is a finite subgraph of some supergraph
`G`.

## Implementation notes

The proof here uses compactness as formulated in `nonempty_sections_of_finite_inverse_system`. For
finite subgraphs `G'' ≤ G'`, the inverse system `finsubgraphHomFunctor` restricts homomorphisms
`G' →fg F` to domain `G''`.
-/

@[expose] public section


open Set CategoryTheory

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {F : SimpleGraph W}

namespace SimpleGraph

/--
Definition of `Finsubgraph` / `Finsubgraph` 的定义

English:
abbreviation Finsubgraph
  signature: (G : SimpleGraph V)
  body: { G' : G.Subgraph // G'.verts.Finite }

中文:
缩写 Finsubgraph
  签名: (G : 简单图 V)
  定义体: { G' : G.Subgraph // G'.verts.Finite }

Depends on / 依赖: Finite, G.Subgraph, Subgraph, verts.Finite
-/
abbrev Finsubgraph (G : SimpleGraph V) :=
  { G' : G.Subgraph // G'.verts.Finite }

/--
Definition of `FinsubgraphHom` / `FinsubgraphHom` 的定义

English:
abbreviation FinsubgraphHom
  signature: (G' : G.Finsubgraph) (F : SimpleGraph W)
  body: G'.val.coe ->g F

local infixl:50 " ->fg " => FinsubgraphHom

中文:
缩写 FinsubgraphHom
  签名: (G' : G.Finsubgraph) (F : 简单图 W)
  定义体: G'.val.coe ->g F

local infixl:50 " ->fg " => FinsubgraphHom

Depends on / 依赖: val.coe
-/
abbrev FinsubgraphHom (G' : G.Finsubgraph) (F : SimpleGraph W) :=
  G'.val.coe ->g F

local infixl:50 " ->fg " => FinsubgraphHom

namespace Finsubgraph

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot G.Finsubgraph
  body: ⟨⊥, finite_empty⟩
  bot_le _ := bot_le (α := G.Subgraph)

中文:
实例 :
  签名: 有底序 G.Finsubgraph
  定义体: ⟨⊥, finite_empty⟩
  bot_le _ := bot_le (α := G.Subgraph)

Depends on / 依赖: finite_empty
-/
instance : OrderBot G.Finsubgraph where
  bot := ⟨⊥, finite_empty⟩
  bot_le _ := bot_le (α := G.Subgraph)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max G.Finsubgraph
  body: ⟨fun G₁ G₂ => ⟨G₁ ⊔ G₂, G₁.2.union G₂.2⟩⟩

中文:
实例 :
  签名: 最大值 G.Finsubgraph
  定义体: ⟨fun G₁ G₂ => ⟨G₁ ⊔ G₂, G₁.2.union G₂.2⟩⟩
-/
instance : Max G.Finsubgraph :=
  ⟨fun G₁ G₂ => ⟨G₁ ⊔ G₂, G₁.2.union G₂.2⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min G.Finsubgraph
  body: ⟨fun G₁ G₂ => ⟨G₁ ⊓ G₂, G₁.2.subset inter_subset_left⟩⟩

中文:
实例 :
  签名: 最小值 G.Finsubgraph
  定义体: ⟨fun G₁ G₂ => ⟨G₁ ⊓ G₂, G₁.2.subset inter_subset_left⟩⟩

Depends on / 依赖: inter_subset_left, subset
-/
instance : Min G.Finsubgraph :=
  ⟨fun G₁ G₂ => ⟨G₁ ⊓ G₂, G₁.2.subset inter_subset_left⟩⟩

/--
Instance `instSDiff` / 实例 `instSDiff`

English:
instance instSDiff
  signature: : SDiff G.Finsubgraph where
  body: ⟨G₁ \ G₂, G₁.2.subset (Subgraph.verts_mono sdiff_le)⟩

中文:
实例 instSDiff
  签名: : 对称差 G.Finsubgraph where
  定义体: ⟨G₁ \ G₂, G₁.2.subset (Subgraph.verts_mono sdiff_le)⟩

Depends on / 依赖: Subgraph, Subgraph.verts_mono, sdiff_le, subset, verts_mono
-/
instance instSDiff : SDiff G.Finsubgraph where
  sdiff G₁ G₂ := ⟨G₁ \ G₂, G₁.2.subset (Subgraph.verts_mono sdiff_le)⟩

/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: (⊥ : G.Finsubgraph) = (⊥ : G.Subgraph)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_bot
  结论: (⊥ : G.Finsubgraph) = (⊥ : G.子图)
  证明: rfl

@[simp, norm_cast]
-/
@[simp, norm_cast] lemma coe_bot : (⊥ : G.Finsubgraph) = (⊥ : G.Subgraph) := rfl

@[simp, norm_cast]
/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: (G₁ G₂ : G.Finsubgraph)
  statement: ↑(G₁ ⊔ G₂) = (G₁ ⊔ G₂ : G.Subgraph)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_sup
  条件: (G₁ G₂ : G.Finsubgraph)
  结论: ↑(G₁ ⊔ G₂) = (G₁ ⊔ G₂ : G.子图)
  证明: rfl

@[simp, norm_cast]
-/
lemma coe_sup (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⊔ G₂) = (G₁ ⊔ G₂ : G.Subgraph) := rfl

@[simp, norm_cast]
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (G₁ G₂ : G.Finsubgraph)
  statement: ↑(G₁ ⊓ G₂) = (G₁ ⊓ G₂ : G.Subgraph)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_inf
  条件: (G₁ G₂ : G.Finsubgraph)
  结论: ↑(G₁ ⊓ G₂) = (G₁ ⊓ G₂ : G.子图)
  证明: rfl

@[simp, norm_cast]
-/
lemma coe_inf (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⊓ G₂) = (G₁ ⊓ G₂ : G.Subgraph) := rfl

@[simp, norm_cast]
/--
lemma `coe_sdiff` / 引理 `coe_sdiff`

English:
lemma coe_sdiff
  given: (G₁ G₂ : G.Finsubgraph)
  statement: ↑(G₁ \ G₂) = (G₁ \ G₂ : G.Subgraph)
  proof: rfl

中文:
引理 coe_sdiff
  条件: (G₁ G₂ : G.Finsubgraph)
  结论: ↑(G₁ \ G₂) = (G₁ \ G₂ : G.子图)
  证明: rfl
-/
lemma coe_sdiff (G₁ G₂ : G.Finsubgraph) : ↑(G₁ \ G₂) = (G₁ \ G₂ : G.Subgraph) := rfl

/--
Instance `instGeneralizedCoheytingAlgebra` / 实例 `instGeneralizedCoheytingAlgebra`

English:
instance instGeneralizedCoheytingAlgebra
  signature: : GeneralizedCoheytingAlgebra G.Finsubgraph
  body: Subtype.coe_injective.generalizedCoheytingAlgebra _ .rfl .rfl coe_sup coe_inf coe_bot coe_sdiff

中文:
实例 instGeneralizedCoheytingAlgebra
  签名: : GeneralizedCoheyting代数 G.Finsubgraph
  定义体: Subtype.coe_injective.generalizedCoheytingAlgebra _ .rfl .rfl coe_sup coe_inf coe_bot coe_sdiff

Depends on / 依赖: Subtype, Subtype.coe_injective.generalizedCoheytingAlgebra, coe_bot, coe_inf, coe_injective, coe_sdiff, coe_sup, generalizedCoheytingAlgebra
-/
instance instGeneralizedCoheytingAlgebra : GeneralizedCoheytingAlgebra G.Finsubgraph :=
  Subtype.coe_injective.generalizedCoheytingAlgebra _ .rfl .rfl coe_sup coe_inf coe_bot coe_sdiff

section Finite
variable [Finite V]

/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: : Top G.Finsubgraph where top
  body: ⟨⊤, finite_univ⟩

中文:
实例 instTop
  签名: : 顶元素 G.Finsubgraph where top
  定义体: ⟨⊤, finite_univ⟩

Depends on / 依赖: finite_univ
-/
instance instTop : Top G.Finsubgraph where top := ⟨⊤, finite_univ⟩
/--
Instance `instCompl` / 实例 `instCompl`

English:
instance instCompl
  signature: : Compl G.Finsubgraph where compl G'
  body: ⟨G'ᶜ, Set.toFinite _⟩

中文:
实例 instCompl
  签名: : 补集 G.Finsubgraph where compl G'
  定义体: ⟨G'ᶜ, Set.toFinite _⟩

Depends on / 依赖: Set.toFinite, toFinite
-/
instance instCompl : Compl G.Finsubgraph where compl G' := ⟨G'ᶜ, Set.toFinite _⟩
/--
Instance `instHNot` / 实例 `instHNot`

English:
instance instHNot
  signature: : HNot G.Finsubgraph where hnot G'
  body: ⟨￢G', Set.toFinite _⟩

中文:
实例 instHNot
  签名: : HNot G.Finsubgraph where hnot G'
  定义体: ⟨￢G', Set.toFinite _⟩

Depends on / 依赖: Set.toFinite, toFinite
-/
instance instHNot : HNot G.Finsubgraph where hnot G' := ⟨￢G', Set.toFinite _⟩
/--
Instance `instHImp` / 实例 `instHImp`

English:
instance instHImp
  signature: : HImp G.Finsubgraph where himp G₁ G₂
  body: ⟨G₁ ⇨ G₂, Set.toFinite _⟩

中文:
实例 instHImp
  签名: : HImp G.Finsubgraph where himp G₁ G₂
  定义体: ⟨G₁ ⇨ G₂, Set.toFinite _⟩

Depends on / 依赖: Set.toFinite, toFinite
-/
instance instHImp : HImp G.Finsubgraph where himp G₁ G₂ := ⟨G₁ ⇨ G₂, Set.toFinite _⟩
/--
Instance `instSupSet` / 实例 `instSupSet`

English:
instance instSupSet
  signature: : SupSet G.Finsubgraph where sSup s
  body: ⟨⨆ G in s, ↑G, Set.toFinite _⟩

中文:
实例 instSupSet
  签名: : 上确界集 G.Finsubgraph where sSup s
  定义体: ⟨⨆ G in s, ↑G, Set.toFinite _⟩

Depends on / 依赖: Set.toFinite, toFinite
-/
instance instSupSet : SupSet G.Finsubgraph where sSup s := ⟨⨆ G in s, ↑G, Set.toFinite _⟩
/--
Instance `instInfSet` / 实例 `instInfSet`

English:
instance instInfSet
  signature: : InfSet G.Finsubgraph where sInf s
  body: ⟨⨅ G in s, ↑G, Set.toFinite _⟩

中文:
实例 instInfSet
  签名: : 下确界集 G.Finsubgraph where sInf s
  定义体: ⟨⨅ G in s, ↑G, Set.toFinite _⟩

Depends on / 依赖: Set.toFinite, toFinite
-/
instance instInfSet : InfSet G.Finsubgraph where sInf s := ⟨⨅ G in s, ↑G, Set.toFinite _⟩

/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: (⊤ : G.Finsubgraph) = (⊤ : G.Subgraph)
  proof: rfl

中文:
引理 coe_top
  结论: (⊤ : G.Finsubgraph) = (⊤ : G.子图)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_top : (⊤ : G.Finsubgraph) = (⊤ : G.Subgraph) := rfl
/--
lemma `coe_compl` / 引理 `coe_compl`

English:
lemma coe_compl
  given: (G' : G.Finsubgraph)
  statement: ↑(G'ᶜ) = (G'ᶜ : G.Subgraph)
  proof: rfl

中文:
引理 coe_compl
  条件: (G' : G.Finsubgraph)
  结论: ↑(G'ᶜ) = (G'ᶜ : G.子图)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_compl (G' : G.Finsubgraph) : ↑(G'ᶜ) = (G'ᶜ : G.Subgraph) := rfl
/--
lemma `coe_hnot` / 引理 `coe_hnot`

English:
lemma coe_hnot
  given: (G' : G.Finsubgraph)
  statement: ↑(￢G') = (￢G' : G.Subgraph)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_hnot
  条件: (G' : G.Finsubgraph)
  结论: ↑(￢G') = (￢G' : G.子图)
  证明: rfl

@[simp, norm_cast]
-/
@[simp, norm_cast] lemma coe_hnot (G' : G.Finsubgraph) : ↑(￢G') = (￢G' : G.Subgraph) := rfl

@[simp, norm_cast]
/--
lemma `coe_himp` / 引理 `coe_himp`

English:
lemma coe_himp
  given: (G₁ G₂ : G.Finsubgraph)
  statement: ↑(G₁ ⇨ G₂) = (G₁ ⇨ G₂ : G.Subgraph)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_himp
  条件: (G₁ G₂ : G.Finsubgraph)
  结论: ↑(G₁ ⇨ G₂) = (G₁ ⇨ G₂ : G.子图)
  证明: rfl

@[simp, norm_cast]
-/
lemma coe_himp (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⇨ G₂) = (G₁ ⇨ G₂ : G.Subgraph) := rfl

@[simp, norm_cast]
/--
lemma `coe_sSup` / 引理 `coe_sSup`

English:
lemma coe_sSup
  given: (s : Set G.Finsubgraph)
  statement: sSup s = (⨆ G in s, G : G.Subgraph)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_sSup
  条件: (s : 集合 G.Finsubgraph)
  结论: sSup s = (⨆ G in s, G : G.子图)
  证明: rfl

@[simp, norm_cast]
-/
lemma coe_sSup (s : Set G.Finsubgraph) : sSup s = (⨆ G in s, G : G.Subgraph) := rfl

@[simp, norm_cast]
/--
lemma `coe_sInf` / 引理 `coe_sInf`

English:
lemma coe_sInf
  given: (s : Set G.Finsubgraph)
  statement: sInf s = (⨅ G in s, G : G.Subgraph)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_sInf
  条件: (s : 集合 G.Finsubgraph)
  结论: sInf s = (⨅ G in s, G : G.子图)
  证明: rfl

@[simp, norm_cast]
-/
lemma coe_sInf (s : Set G.Finsubgraph) : sInf s = (⨅ G in s, G : G.Subgraph) := rfl

@[simp, norm_cast]
/--
lemma `coe_iSup` / 引理 `coe_iSup`

English:
lemma coe_iSup
  given: {ι : Sort*} (f : ι -> G.Finsubgraph)
  statement: ⨆ i, f i = (⨆ i, f i : G.Subgraph)
  proof: by
  rw [iSup]; rw [coe_sSup]; rw [iSup_range]

@[simp, norm_cast]

中文:
引理 coe_iSup
  条件: {ι : 类型层*} (f : ι -> G.Finsubgraph)
  结论: ⨆ i, f i = (⨆ i, f i : G.子图)
  证明: by
  rw [iSup]; rw [coe_sSup]; rw [iSup_range]

@[simp, norm_cast]

Depends on / 依赖: coe_sSup, iSup_range
-/
lemma coe_iSup {ι : Sort*} (f : ι -> G.Finsubgraph) : ⨆ i, f i = (⨆ i, f i : G.Subgraph) := by
  rw [iSup]; rw [coe_sSup]; rw [iSup_range]

@[simp, norm_cast]
/--
lemma `coe_iInf` / 引理 `coe_iInf`

English:
lemma coe_iInf
  given: {ι : Sort*} (f : ι -> G.Finsubgraph)
  statement: ⨅ i, f i = (⨅ i, f i : G.Subgraph)
  proof: by
  rw [iInf]; rw [coe_sInf]; rw [iInf_range]

中文:
引理 coe_iInf
  条件: {ι : 类型层*} (f : ι -> G.Finsubgraph)
  结论: ⨅ i, f i = (⨅ i, f i : G.子图)
  证明: by
  rw [iInf]; rw [coe_sInf]; rw [iInf_range]

Depends on / 依赖: coe_sInf, iInf_range
-/
lemma coe_iInf {ι : Sort*} (f : ι -> G.Finsubgraph) : ⨅ i, f i = (⨅ i, f i : G.Subgraph) := by
  rw [iInf]; rw [coe_sInf]; rw [iInf_range]

/--
Instance `instCompletelyDistribLattice` / 实例 `instCompletelyDistribLattice`

English:
instance instCompletelyDistribLattice
  signature: : CompletelyDistribLattice G.Finsubgraph
  body: Subtype.coe_injective.completelyDistribLattice _ .rfl .rfl coe_sup coe_inf coe_sSup coe_sInf
    coe_top coe_bot coe_compl coe_himp coe_hnot coe_sdiff

中文:
实例 instCompletelyDistribLattice
  签名: : 余mpletelyDistrib格 G.Finsubgraph
  定义体: Subtype.coe_injective.completelyDistribLattice _ .rfl .rfl coe_sup coe_inf coe_sSup coe_sInf
    coe_top coe_bot coe_compl coe_himp coe_hnot coe_sdiff

Depends on / 依赖: Subtype, Subtype.coe_injective.completelyDistribLattice, coe_bot, coe_compl, coe_himp, coe_hnot, coe_inf, coe_injective, coe_sInf, coe_sSup, coe_sdiff, coe_sup, coe_top, completelyDistribLattice
-/
instance instCompletelyDistribLattice : CompletelyDistribLattice G.Finsubgraph :=
  Subtype.coe_injective.completelyDistribLattice _ .rfl .rfl coe_sup coe_inf coe_sSup coe_sInf
    coe_top coe_bot coe_compl coe_himp coe_hnot coe_sdiff

end Finite
end Finsubgraph

/--
Definition of `singletonFinsubgraph` / `singletonFinsubgraph` 的定义

English:
definition singletonFinsubgraph
  signature: (v : V)
  body: ⟨SimpleGraph.singletonSubgraph _ v, by simp⟩

中文:
定义 singletonFinsubgraph
  签名: (v : V)
  定义体: ⟨SimpleGraph.singletonSubgraph _ v, by simp⟩

Depends on / 依赖: SimpleGraph, SimpleGraph.singletonSubgraph, singletonSubgraph
-/
def singletonFinsubgraph (v : V) : G.Finsubgraph :=
  ⟨SimpleGraph.singletonSubgraph _ v, by simp⟩

/--
Definition of `finsubgraphOfAdj` / `finsubgraphOfAdj` 的定义

English:
definition finsubgraphOfAdj
  signature: {u v : V} (e : G.Adj u v)
  body: ⟨SimpleGraph.subgraphOfAdj _ e, by simp⟩

中文:
定义 finsubgraphOfAdj
  签名: {u v : V} (e : G.伴随 u v)
  定义体: ⟨SimpleGraph.subgraphOfAdj _ e, by simp⟩

Depends on / 依赖: SimpleGraph, SimpleGraph.subgraphOfAdj, subgraphOfAdj
-/
def finsubgraphOfAdj {u v : V} (e : G.Adj u v) : G.Finsubgraph :=
  ⟨SimpleGraph.subgraphOfAdj _ e, by simp⟩

-- Lemmas establishing the ordering between edge- and vertex-generated subgraphs.
/--
theorem `singletonFinsubgraph_le_adj_left` / 定理 `singletonFinsubgraph_le_adj_left`

English:
theorem singletonFinsubgraph_le_adj_left
  given: {u v : V} {e : G.Adj u v}
  proof: by
  simp [singletonFinsubgraph, finsubgraphOfAdj]

中文:
定理 singletonFinsubgraph_le_adj_left
  条件: {u v : V} {e : G.伴随 u v}
  证明: by
  simp [singletonFinsubgraph, finsubgraphOfAdj]

Depends on / 依赖: finsubgraphOfAdj, singletonFinsubgraph
-/
theorem singletonFinsubgraph_le_adj_left {u v : V} {e : G.Adj u v} :
    singletonFinsubgraph u <= finsubgraphOfAdj e := by
  simp [singletonFinsubgraph, finsubgraphOfAdj]

/--
theorem `singletonFinsubgraph_le_adj_right` / 定理 `singletonFinsubgraph_le_adj_right`

English:
theorem singletonFinsubgraph_le_adj_right
  given: {u v : V} {e : G.Adj u v}
  proof: by
  simp [singletonFinsubgraph, finsubgraphOfAdj]

中文:
定理 singletonFinsubgraph_le_adj_right
  条件: {u v : V} {e : G.伴随 u v}
  证明: by
  simp [singletonFinsubgraph, finsubgraphOfAdj]

Depends on / 依赖: finsubgraphOfAdj, singletonFinsubgraph
-/
theorem singletonFinsubgraph_le_adj_right {u v : V} {e : G.Adj u v} :
    singletonFinsubgraph v <= finsubgraphOfAdj e := by
  simp [singletonFinsubgraph, finsubgraphOfAdj]

/--
Definition of `FinsubgraphHom.restrict` / `FinsubgraphHom.restrict` 的定义

English:
definition FinsubgraphHom.restrict
  signature: {G' G'' : G.Finsubgraph} (h : G'' <= G') (f : G' ->fg F)
  body: by
  refine ⟨fun ⟨v, hv⟩ => f.toFun ⟨v, h.1 hv⟩, ?_⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
  exact f.map_rel' (h.2 huv)

中文:
定义 FinsubgraphHom.restrict
  签名: {G' G'' : G.Finsubgraph} (h : G'' <= G') (f : G' ->fg F)
  定义体: by
  refine ⟨fun ⟨v, hv⟩ => f.toFun ⟨v, h.1 hv⟩, ?_⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
  exact f.map_rel' (h.2 huv)

Depends on / 依赖: f.map_rel, f.toFun, map_rel
-/
def FinsubgraphHom.restrict {G' G'' : G.Finsubgraph} (h : G'' <= G') (f : G' ->fg F) : G'' ->fg F := by
  refine ⟨fun ⟨v, hv⟩ => f.toFun ⟨v, h.1 hv⟩, ?_⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
  exact f.map_rel' (h.2 huv)

/--
Definition of `finsubgraphHomFunctor` / `finsubgraphHomFunctor` 的定义

English:
definition finsubgraphHomFunctor
  signature: (G : SimpleGraph V) (F : SimpleGraph W)
  body: G'.unop ->fg F
  map g := ↾(fun f => f.restrict (CategoryTheory.leOfHom g.unop))

中文:
定义 finsubgraphHomFunctor
  签名: (G : 简单图 V) (F : 简单图 W)
  定义体: G'.unop ->fg F
  map g := ↾(fun f => f.restrict (CategoryTheory.leOfHom g.unop))
-/
def finsubgraphHomFunctor (G : SimpleGraph V) (F : SimpleGraph W) :
    G.Finsubgraphᵒᵖ ⥤ Type (max u v) where
  obj G' := G'.unop ->fg F
  map g := ↾(fun f => f.restrict (CategoryTheory.leOfHom g.unop))

/--
theorem `nonempty_hom_of_forall_finite_subgraph_hom` / 定理 `nonempty_hom_of_forall_finite_subgraph_hom`

English:
theorem nonempty_hom_of_forall_finite_subgraph_hom
  statement: [Finite W]
  proof: by
  -- Obtain a `Fintype` instance for `W`.
  cases nonempty_fintype W
  -- Establish the required interface instances.
  have : forall G' : G.Finsubgraphᵒᵖ, Nonempty ((finsubgraphHomFunctor G F).obj G') := fun G' =>
    ⟨h G'.unop G'.unop.property⟩
  have : forall G' : G.Finsubgraphᵒᵖ, Fintype ((finsubgraphHomFunctor G F).obj G') := by
    intro G'
    haveI : Fintype (G'.unop.val.verts : Type u) := G'.unop.property.fintype
    haveI : Fintype (↥G'.unop.val.verts -> W) := by classical exact Pi.instFintype
    exact Fintype.ofInjective (fun f => f.toFun) RelHom.coe_fn_injective
  -- Use compactness to obtain a section.
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (finsubgraphHomFunctor G F)
  refine ⟨⟨fun v => ?_, ?_⟩⟩
  · -- Map each vertex using the homomorphism provided for its singleton subgraph.
    exact
      (u (Opposite.op (singletonFinsubgraph v))).toFun
        ⟨v, by
          unfold singletonFinsubgraph
          simp⟩
  · -- Prove that the above mapping preserves adjacency.
    intro v v' e
    simp only
    /- The homomorphism for each edge's singleton subgraph agrees with those for its source and
        target vertices. -/
    have hv : Opposite.op (finsubgraphOfAdj e) ⟶ Opposite.op (singletonFinsubgraph v) :=
      Quiver.Hom.op (CategoryTheory.homOfLE singletonFinsubgraph_le_adj_left)
    have hv' : Opposite.op (finsubgraphOfAdj e) ⟶ Opposite.op (singletonFinsubgraph v') :=
      Quiver.Hom.op (CategoryTheory.homOfLE singletonFinsubgraph_le_adj_right)
    rw [← hu hv]; rw [← hu hv']
    -- Porting note: was `apply Hom.map_adj`
    apply Hom.map_adj (u _) ?_
    -- `v` and `v'` are definitionally adjacent in `finsubgraphOfAdj e`
    simp [finsubgraphOfAdj]

中文:
定理 nonempty_hom_of_对任意_finite_subgraph_hom
  结论: [有限 W]
  证明: by
  -- Obtain a `Fintype` instance for `W`.
  cases nonempty_fintype W
  -- Establish the required interface instances.
  have : forall G' : G.Finsubgraphᵒᵖ, Nonempty ((finsubgraphHomFunctor G F).obj G') := fun G' =>
    ⟨h G'.unop G'.unop.property⟩
  have : forall G' : G.Finsubgraphᵒᵖ, Fintype ((finsubgraphHomFunctor G F).obj G') := by
    intro G'
    haveI : Fintype (G'.unop.val.verts : Type u) := G'.unop.property.fintype
    haveI : Fintype (↥G'.unop.val.verts -> W) := by classical exact Pi.instFintype
    exact Fintype.ofInjective (fun f => f.toFun) RelHom.coe_fn_injective
  -- Use compactness to obtain a section.
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (finsubgraphHomFunctor G F)
  refine ⟨⟨fun v => ?_, ?_⟩⟩
  · -- Map each vertex using the homomorphism provided for its singleton subgraph.
    exact
      (u (Opposite.op (singletonFinsubgraph v))).toFun
        ⟨v, by
          unfold singletonFinsubgraph
          simp⟩
  · -- Prove that the above mapping preserves adjacency.
    intro v v' e
    simp only
    /- The homomorphism for each edge's singleton subgraph agrees with those for its source and
        target vertices. -/
    have hv : Opposite.op (finsubgraphOfAdj e) ⟶ Opposite.op (singletonFinsubgraph v) :=
      Quiver.Hom.op (CategoryTheory.homOfLE singletonFinsubgraph_le_adj_left)
    have hv' : Opposite.op (finsubgraphOfAdj e) ⟶ Opposite.op (singletonFinsubgraph v') :=
      Quiver.Hom.op (CategoryTheory.homOfLE singletonFinsubgraph_le_adj_right)
    rw [← hu hv]; rw [← hu hv']
    -- Porting note: was `apply Hom.map_adj`
    apply Hom.map_adj (u _) ?_
    -- `v` and `v'` are definitionally adjacent in `finsubgraphOfAdj e`
    simp [finsubgraphOfAdj]
-/
theorem nonempty_hom_of_forall_finite_subgraph_hom [Finite W]
    (h : forall G' : G.Subgraph, G'.verts.Finite -> G'.coe ->g F) : Nonempty (G ->g F) := by
  -- Obtain a `Fintype` instance for `W`.
  cases nonempty_fintype W
  -- Establish the required interface instances.
  have : forall G' : G.Finsubgraphᵒᵖ, Nonempty ((finsubgraphHomFunctor G F).obj G') := fun G' =>
    ⟨h G'.unop G'.unop.property⟩
  have : forall G' : G.Finsubgraphᵒᵖ, Fintype ((finsubgraphHomFunctor G F).obj G') := by
    intro G'
    haveI : Fintype (G'.unop.val.verts : Type u) := G'.unop.property.fintype
    haveI : Fintype (↥G'.unop.val.verts -> W) := by classical exact Pi.instFintype
    exact Fintype.ofInjective (fun f => f.toFun) RelHom.coe_fn_injective
  -- Use compactness to obtain a section.
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (finsubgraphHomFunctor G F)
  refine ⟨⟨fun v => ?_, ?_⟩⟩
  · -- Map each vertex using the homomorphism provided for its singleton subgraph.
    exact
      (u (Opposite.op (singletonFinsubgraph v))).toFun
        ⟨v, by
          unfold singletonFinsubgraph
          simp⟩
  · -- Prove that the above mapping preserves adjacency.
    intro v v' e
    simp only
    /- The homomorphism for each edge's singleton subgraph agrees with those for its source and
        target vertices. -/
    have hv : Opposite.op (finsubgraphOfAdj e) ⟶ Opposite.op (singletonFinsubgraph v) :=
      Quiver.Hom.op (CategoryTheory.homOfLE singletonFinsubgraph_le_adj_left)
    have hv' : Opposite.op (finsubgraphOfAdj e) ⟶ Opposite.op (singletonFinsubgraph v') :=
      Quiver.Hom.op (CategoryTheory.homOfLE singletonFinsubgraph_le_adj_right)
    rw [← hu hv]; rw [← hu hv']
    -- Porting note: was `apply Hom.map_adj`
    apply Hom.map_adj (u _) ?_
    -- `v` and `v'` are definitionally adjacent in `finsubgraphOfAdj e`
    simp [finsubgraphOfAdj]

end SimpleGraph
