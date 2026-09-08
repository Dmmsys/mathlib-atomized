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

/-- The subtype of `G.subgraph` comprising those subgraphs with finite vertex sets. -/
/-
**SimpleGraph.Finsubgraph** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：Finsubgraph (G : SimpleGraph V)
参数：G : SimpleGraph V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subtype of `G.subgraph` comprising those subgraphs with finite vertex sets.
-/
abbrev Finsubgraph (G : SimpleGraph V) :=
  { G' : G.Subgraph // G'.verts.Finite }

/-- A graph homomorphism from a finite subgraph of G to F. -/
/-
**SimpleGraph.FinsubgraphHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：FinsubgraphHom (G' : G.Finsubgraph) (F : SimpleGraph W)
参数：G' : G.Finsubgraph；F : SimpleGraph W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph homomorphism from a finite subgraph of G to F.
-/
abbrev FinsubgraphHom (G' : G.Finsubgraph) (F : SimpleGraph W) :=
  G'.val.coe →g F

local infixl:50 " →fg " => FinsubgraphHom

namespace Finsubgraph

/-
**SimpleGraph.Finsubgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Finsubgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot G.Finsubgraph where
  bot := ⟨⊥, finite_empty⟩
  bot_le _ := bot_le (α := G.Subgraph)
/-
**SimpleGraph.Finsubgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Finsubgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max G.Finsubgraph :=
  ⟨fun G₁ G₂ => ⟨G₁ ⊔ G₂, G₁.2.union G₂.2⟩⟩
/-
**SimpleGraph.Finsubgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Finsubgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min G.Finsubgraph :=
  ⟨fun G₁ G₂ => ⟨G₁ ⊓ G₂, G₁.2.subset inter_subset_left⟩⟩
/-
**SimpleGraph.Finsubgraph.instSDiff** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Finsu
bgraph`。
形式化陈述：instSDiff : SDiff G.Finsubgraph where sdiff G₁ G₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSDiff : SDiff G.Finsubgraph where
  sdiff G₁ G₂ := ⟨G₁ \ G₂, G₁.2.subset (Subgraph.verts_mono sdiff_le)⟩
/-
**SimpleGraph.Finsubgraph.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Finsubg
raph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V}, ↑⊥ = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_bot : (⊥ : G.Finsubgraph) = (⊥ : G.Subgraph) := rfl

@[simp, norm_cast]
/-
**SimpleGraph.Finsubgraph.coe_sup** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Finsubg
raph`。
形式化陈述：coe_sup (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⊔ G₂) = (G₁ ⊔ G₂ : G.Subgraph)
参数：G₁ G₂ : G.Finsubgraph。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sup (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⊔ G₂) = (G₁ ⊔ G₂ : G.Subgraph) := rfl

@[simp, norm_cast]
/-
**SimpleGraph.Finsubgraph.coe_inf** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Finsubg
raph`。
形式化陈述：coe_inf (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⊓ G₂) = (G₁ ⊓ G₂ : G.Subgraph)
参数：G₁ G₂ : G.Finsubgraph。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_inf (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⊓ G₂) = (G₁ ⊓ G₂ : G.Subgraph) := rfl

@[simp, norm_cast]
/-
**SimpleGraph.Finsubgraph.coe_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Finsu
bgraph`。
形式化陈述：coe_sdiff (G₁ G₂ : G.Finsubgraph) : ↑(G₁ \ G₂) = (G₁ \ G₂ : G.Subgraph)
参数：G₁ G₂ : G.Finsubgraph。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sdiff (G₁ G₂ : G.Finsubgraph) : ↑(G₁ \ G₂) = (G₁ \ G₂ : G.Subgraph) := rfl
/-
**SimpleGraph.Finsubgraph.instGeneralizedCoheytingAlgebra** 是 Mathlib 中的一个实例，位于命
名空间 `SimpleGraph.Finsubgraph`。
形式化陈述：instGeneralizedCoheytingAlgebra : GeneralizedCoheytingAlgebra G.Finsubgrap
h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Finsubgraph.coe_sup`：coe_sup (G₁ G₂ : G.Finsubgraph) : ↑(G₁ 
⊔ G₂) = (G₁ ⊔ G₂ : G.Subgraph)
· 使用引理 `SimpleGraph.Finsubgraph.coe_inf`：coe_inf (G₁ G₂ : G.Finsubgraph) : ↑(G₁ 
⊓ G₂) = (G₁ ⊓ G₂ : G.Subgraph)
· 使用定理 `SimpleGraph.Finsubgraph.coe_bot`：∀ {V : Type u} {G : SimpleGraph V}, ↑⊥ 
= ⊥
· 使用引理 `SimpleGraph.Finsubgraph.coe_sdiff`：coe_sdiff (G₁ G₂ : G.Finsubgraph) : ↑
(G₁ \ G₂) = (G₁ \ G₂ : G.Subgraph)
-/
instance instGeneralizedCoheytingAlgebra : GeneralizedCoheytingAlgebra G.Finsubgraph :=
  Subtype.coe_injective.generalizedCoheytingAlgebra _ .rfl .rfl coe_sup coe_inf coe_bot coe_sdiff

section Finite
variable [Finite V]

/-
**SimpleGraph.Finsubgraph.instTop** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Finsubg
raph`。
形式化陈述：instTop : Top G.Finsubgraph where top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
instance instTop : Top G.Finsubgraph where top := ⟨⊤, finite_univ⟩
/-
**SimpleGraph.Finsubgraph.instCompl** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Finsu
bgraph`。
形式化陈述：instCompl : Compl G.Finsubgraph where compl G'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompl : Compl G.Finsubgraph where compl G' := ⟨G'ᶜ, Set.toFinite _⟩
/-
**SimpleGraph.Finsubgraph.instHNot** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Finsub
graph`。
形式化陈述：instHNot : HNot G.Finsubgraph where hnot G'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHNot : HNot G.Finsubgraph where hnot G' := ⟨￢G', Set.toFinite _⟩
/-
**SimpleGraph.Finsubgraph.instHImp** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Finsub
graph`。
形式化陈述：instHImp : HImp G.Finsubgraph where himp G₁ G₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHImp : HImp G.Finsubgraph where himp G₁ G₂ := ⟨G₁ ⇨ G₂, Set.toFinite _⟩
/-
**SimpleGraph.Finsubgraph.instSupSet** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Fins
ubgraph`。
形式化陈述：instSupSet : SupSet G.Finsubgraph where sSup s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSupSet : SupSet G.Finsubgraph where sSup s := ⟨⨆ G ∈ s, ↑G, Set.toFinite _⟩
/-
**SimpleGraph.Finsubgraph.instInfSet** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Fins
ubgraph`。
形式化陈述：instInfSet : InfSet G.Finsubgraph where sInf s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInfSet : InfSet G.Finsubgraph where sInf s := ⟨⨅ G ∈ s, ↑G, Set.toFinite _⟩
/-
**SimpleGraph.Finsubgraph.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Finsubg
raph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : Finite V], ↑⊤ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_top : (⊤ : G.Finsubgraph) = (⊤ : G.Subgraph) := rfl
/-
**SimpleGraph.Finsubgraph.coe_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Finsu
bgraph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : Finite V] (G' : G.Finsubgraph),
 ↑G'ᶜ = (↑G')ᶜ
参数：G' : G.Finsubgraph；↑G'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_compl (G' : G.Finsubgraph) : ↑(G'ᶜ) = (G'ᶜ : G.Subgraph) := rfl
/-
**SimpleGraph.Finsubgraph.coe_hnot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Finsub
graph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : Finite V] (G' : G.Finsubgraph),
 ↑(￢G') = ￢↑G'
参数：G' : G.Finsubgraph；￢G'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_hnot (G' : G.Finsubgraph) : ↑(￢G') = (￢G' : G.Subgraph) := rfl

@[simp, norm_cast]
/-
**SimpleGraph.Finsubgraph.coe_himp** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Finsub
graph`。
形式化陈述：coe_himp (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⇨ G₂) = (G₁ ⇨ G₂ : G.Subgraph)
参数：G₁ G₂ : G.Finsubgraph。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_himp (G₁ G₂ : G.Finsubgraph) : ↑(G₁ ⇨ G₂) = (G₁ ⇨ G₂ : G.Subgraph) := rfl

@[simp, norm_cast]
/-
**SimpleGraph.Finsubgraph.coe_sSup** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Finsub
graph`。
形式化陈述：coe_sSup (s : Set G.Finsubgraph) : sSup s = (⨆ G in s, G : G.Subgraph)
参数：s : Set G.Finsubgraph。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sSup (s : Set G.Finsubgraph) : sSup s = (⨆ G ∈ s, G : G.Subgraph) := rfl

@[simp, norm_cast]
/-
**SimpleGraph.Finsubgraph.coe_sInf** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Finsub
graph`。
形式化陈述：coe_sInf (s : Set G.Finsubgraph) : sInf s = (⨅ G in s, G : G.Subgraph)
参数：s : Set G.Finsubgraph。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sInf (s : Set G.Finsubgraph) : sInf s = (⨅ G ∈ s, G : G.Subgraph) := rfl

@[simp, norm_cast]
/-
**SimpleGraph.Finsubgraph.coe_iSup** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Finsub
graph`。
形式化陈述：coe_iSup {ι : Sort*} (f : ι -> G.Finsubgraph) : ⨆ i, f i = (⨆ i, f i : G.S
ubgraph)
参数：f : ι -> G.Finsubgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用引理 `SimpleGraph.Finsubgraph.coe_sSup`：coe_sSup (s : Set G.Finsubgraph) : sSu
p s = (⨆ G in s, G : G.Subgraph)
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
lemma coe_iSup {ι : Sort*} (f : ι → G.Finsubgraph) : ⨆ i, f i = (⨆ i, f i : G.Subgraph) := by
  rw [iSup, coe_sSup, iSup_range]

@[simp, norm_cast]
/-
**SimpleGraph.Finsubgraph.coe_iInf** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Finsub
graph`。
形式化陈述：coe_iInf {ι : Sort*} (f : ι -> G.Finsubgraph) : ⨅ i, f i = (⨅ i, f i : G.S
ubgraph)
参数：f : ι -> G.Finsubgraph。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用引理 `SimpleGraph.Finsubgraph.coe_sInf`：coe_sInf (s : Set G.Finsubgraph) : sIn
f s = (⨅ G in s, G : G.Subgraph)
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
lemma coe_iInf {ι : Sort*} (f : ι → G.Finsubgraph) : ⨅ i, f i = (⨅ i, f i : G.Subgraph) := by
  rw [iInf, coe_sInf, iInf_range]
/-
**SimpleGraph.Finsubgraph.instCompletelyDistribLattice** 是 Mathlib 中的一个实例，位于命名空间
 `SimpleGraph.Finsubgraph`。
形式化陈述：instCompletelyDistribLattice : CompletelyDistribLattice G.Finsubgraph
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Finsubgraph.coe_sup`：coe_sup (G₁ G₂ : G.Finsubgraph) : ↑(G₁ 
⊔ G₂) = (G₁ ⊔ G₂ : G.Subgraph)
· 使用引理 `SimpleGraph.Finsubgraph.coe_inf`：coe_inf (G₁ G₂ : G.Finsubgraph) : ↑(G₁ 
⊓ G₂) = (G₁ ⊓ G₂ : G.Subgraph)
· 使用引理 `SimpleGraph.Finsubgraph.coe_sSup`：coe_sSup (s : Set G.Finsubgraph) : sSu
p s = (⨆ G in s, G : G.Subgraph)
· 使用引理 `SimpleGraph.Finsubgraph.coe_sInf`：coe_sInf (s : Set G.Finsubgraph) : sIn
f s = (⨅ G in s, G : G.Subgraph)
· 使用定理 `SimpleGraph.Finsubgraph.coe_top`：∀ {V : Type u} {G : SimpleGraph V} [ins
t : Finite V], ↑⊤ = ⊤
· 使用定理 `SimpleGraph.Finsubgraph.coe_bot`：∀ {V : Type u} {G : SimpleGraph V}, ↑⊥ 
= ⊥
· 使用定理 `SimpleGraph.Finsubgraph.coe_compl`：∀ {V : Type u} {G : SimpleGraph V} [i
nst : Finite V] (G' : G.Finsubgraph), ↑G'ᶜ = (↑G')ᶜ
· 使用引理 `SimpleGraph.Finsubgraph.coe_himp`：coe_himp (G₁ G₂ : G.Finsubgraph) : ↑(G
₁ ⇨ G₂) = (G₁ ⇨ G₂ : G.Subgraph)
· 使用定理 `SimpleGraph.Finsubgraph.coe_hnot`：∀ {V : Type u} {G : SimpleGraph V} [in
st : Finite V] (G' : G.Finsubgraph), ↑(￢G') = ￢↑G'
· 使用引理 `SimpleGraph.Finsubgraph.coe_sdiff`：coe_sdiff (G₁ G₂ : G.Finsubgraph) : ↑
(G₁ \ G₂) = (G₁ \ G₂ : G.Subgraph)
-/
instance instCompletelyDistribLattice : CompletelyDistribLattice G.Finsubgraph :=
  Subtype.coe_injective.completelyDistribLattice _ .rfl .rfl coe_sup coe_inf coe_sSup coe_sInf
    coe_top coe_bot coe_compl coe_himp coe_hnot coe_sdiff

end Finite
end Finsubgraph

/-- The finite subgraph of G generated by a single vertex. -/
/-
**SimpleGraph.singletonFinsubgraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：singletonFinsubgraph (v : V) : G.Finsubgraph
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finite subgraph of G generated by a single vertex.
-/
def singletonFinsubgraph (v : V) : G.Finsubgraph :=
  ⟨SimpleGraph.singletonSubgraph _ v, by simp⟩

/-- The finite subgraph of G generated by a single edge. -/
/-
**SimpleGraph.finsubgraphOfAdj** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：finsubgraphOfAdj {u v : V} (e : G.Adj u v) : G.Finsubgraph
参数：e : G.Adj u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finite subgraph of G generated by a single edge.
-/
def finsubgraphOfAdj {u v : V} (e : G.Adj u v) : G.Finsubgraph :=
  ⟨SimpleGraph.subgraphOfAdj _ e, by simp⟩

-- Lemmas establishing the ordering between edge- and vertex-generated subgraphs.
/-
**SimpleGraph.singletonFinsubgraph_le_adj_left** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：singletonFinsubgraph_le_adj_left {u v : V} {e : G.Adj u v} : singletonFins
ubgraph u <= finsubgraphOfAdj e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.subgraphOfAdj_verts`：∀ {V : Type u} (G : SimpleGraph V) {v w
 : V} (hvw : G.Adj v w), (G.subgraphOfAdj hvw).verts = {v, w}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem singletonFinsubgraph_le_adj_left {u v : V} {e : G.Adj u v} :
    singletonFinsubgraph u ≤ finsubgraphOfAdj e := by
  simp [singletonFinsubgraph, finsubgraphOfAdj]
/-
**SimpleGraph.singletonFinsubgraph_le_adj_right** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：singletonFinsubgraph_le_adj_right {u v : V} {e : G.Adj u v} : singletonFin
subgraph v <= finsubgraphOfAdj e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.subgraphOfAdj_verts`：∀ {V : Type u} (G : SimpleGraph V) {v w
 : V} (hvw : G.Adj v w), (G.subgraphOfAdj hvw).verts = {v, w}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem singletonFinsubgraph_le_adj_right {u v : V} {e : G.Adj u v} :
    singletonFinsubgraph v ≤ finsubgraphOfAdj e := by
  simp [singletonFinsubgraph, finsubgraphOfAdj]

/-- Given a homomorphism from a subgraph to `F`, construct its restriction to a sub-subgraph. -/
/-
**SimpleGraph.FinsubgraphHom.restrict** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Fin
subgraphHom`。
形式化陈述：{V : Type u} →   {W : Type v} →     {G : SimpleGraph V} →       {F : Simpl
eGraph W} →         {G' G'' : G.Finsubgraph} → G'' ≤ G' → SimpleGraph.Finsubgrap
hHom G' F → SimpleGraph.FinsubgraphHom G'' F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a homomorphism from a subgraph to `F`, construct its restriction to a sub-
subgraph.
-/
def FinsubgraphHom.restrict {G' G'' : G.Finsubgraph} (h : G'' ≤ G') (f : G' →fg F) : G'' →fg F := by
  refine ⟨fun ⟨v, hv⟩ => f.toFun ⟨v, h.1 hv⟩, ?_⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
  exact f.map_rel' (h.2 huv)

/-- The inverse system of finite homomorphisms. -/
/-
**SimpleGraph.finsubgraphHomFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：finsubgraphHomFunctor (G : SimpleGraph V) (F : SimpleGraph W) : G.Finsubgr
aphᵒᵖ ⥤ Type (max u v) where obj G'
参数：G : SimpleGraph V；F : SimpleGraph W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse system of finite homomorphisms.
-/
def finsubgraphHomFunctor (G : SimpleGraph V) (F : SimpleGraph W) :
    G.Finsubgraphᵒᵖ ⥤ Type (max u v) where
  obj G' := G'.unop →fg F
  map g := ↾(fun f ↦ f.restrict (CategoryTheory.leOfHom g.unop))

/-- If every finite subgraph of a graph `G` has a homomorphism to a finite graph `F`, then there is
a homomorphism from the whole of `G` to `F`. -/
/-
**SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph`。
形式化陈述：nonempty_hom_of_forall_finite_subgraph_hom [Finite W] (h : forall G' : G.S
ubgraph, G'.verts.Finite -> G'.coe ->g F) : Nonempty (G ->g F)
参数：h : forall G' : G.Subgraph, G'.verts.Finite -> G'.coe ->g F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `RelHom.coe_fn_injective`：coe_fn_injective : Injective fun (f : r ->r s) 
=> (f : α -> β)
· 使用定理 `nonempty_sections_of_finite_inverse_system`：nonempty_sections_of_finite_
inverse_system {J : Type u} [Preorder J] [IsDirectedOrder J] (F : Jᵒᵖ ⥤ Type v) 
[forall j : Jᵒᵖ, Finite (F.obj j…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.singletonSubgraph_verts`：∀ {V : Type u} (G : SimpleGraph V) 
(v : V), (G.singletonSubgraph v).verts = {v}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.singletonFinsubgraph_le_adj_left`：singletonFinsubgraph_le_ad
j_left {u v : V} {e : G.Adj u v} : singletonFinsubgraph u <= finsubgraphOfAdj e
· 使用定理 `SimpleGraph.singletonFinsubgraph_le_adj_right`：singletonFinsubgraph_le_a
dj_right {u v : V} {e : G.Adj u v} : singletonFinsubgraph v <= finsubgraphOfAdj 
e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `SimpleGraph.Subgraph.coe_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' : G
.Subgraph) (v w : ↑G'.verts), G'.coe.Adj v w = G'.Adj ↑v ↑w
· 使用定理 `SimpleGraph.subgraphOfAdj_adj`：∀ {V : Type u} (G : SimpleGraph V) {v w :
 V} (hvw : G.Adj v w) (a b : V),   (G.subgraphOfAdj hvw).Adj a b = (s(v, w) = s(
a, b))

--- 原说明 ---
If every finite subgraph of a graph `G` has a homomorphism to a finite graph `F`
, then there is
a homomorphism from the whole of `G` to `F`.
-/
theorem nonempty_hom_of_forall_finite_subgraph_hom [Finite W]
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe →g F) : Nonempty (G →g F) := by
  -- Obtain a `Fintype` instance for `W`.
  cases nonempty_fintype W
  -- Establish the required interface instances.
  have : ∀ G' : G.Finsubgraphᵒᵖ, Nonempty ((finsubgraphHomFunctor G F).obj G') := fun G' =>
    ⟨h G'.unop G'.unop.property⟩
  have : ∀ G' : G.Finsubgraphᵒᵖ, Fintype ((finsubgraphHomFunctor G F).obj G') := by
    intro G'
    haveI : Fintype (G'.unop.val.verts : Type u) := G'.unop.property.fintype
    haveI : Fintype (↥G'.unop.val.verts → W) := by classical exact Pi.instFintype
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
    rw [← hu hv, ← hu hv']
    -- Porting note: was `apply Hom.map_adj`
    apply Hom.map_adj (u _) ?_
    -- `v` and `v'` are definitionally adjacent in `finsubgraphOfAdj e`
    simp [finsubgraphOfAdj]

end SimpleGraph

