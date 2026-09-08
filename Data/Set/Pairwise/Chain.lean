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

variable {α β : Type*} {c : Set (Set α)} {r : α → α → Prop}
variable (hc : IsChain (· ⊆ ·) c)

namespace IsChain

include hc

/-
**IsChain.pairwise_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `IsChain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pairwise_iUnion₂ : (⋃ s ∈ c, s).Pairwise r ↔ ∀ s ∈ c, s.Pairwise r :=
  pairwise_iUnion₂_iff hc.directedOn
/-
**IsChain.pairwiseDisjoint_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `IsChain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pairwiseDisjoint_iUnion₂ [PartialOrder β] [OrderBot β] (f : α → β) :
    (⋃ s ∈ c, s).PairwiseDisjoint f ↔ ∀ s ∈ c, s.PairwiseDisjoint f :=
  hc.pairwise_iUnion₂
/-
**IsChain.pairwise_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `IsChain`。
形式化陈述：pairwise_sUnion : (⋃₀ c).Pairwise r ↔ forall s in c, s.Pairwise r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_sUnion`：pairwise_sUnion {r : α -> α -> Prop} {s : Set (Set 
α)} (hd : DirectedOn (· subseteq ·) s) : (⋃₀ s).Pairwise r ↔ forall a in s, Set.
Pairwise …
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
-/
lemma pairwise_sUnion : (⋃₀ c).Pairwise r ↔ ∀ s ∈ c, s.Pairwise r :=
  Set.pairwise_sUnion hc.directedOn
/-
**IsChain.pairwiseDisjoint_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `IsChain`。
形式化陈述：pairwiseDisjoint_sUnion [PartialOrder β] [OrderBot β] (f : α -> β) : (⋃₀ c
).PairwiseDisjoint f ↔ forall s in c, s.PairwiseDisjoint f
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsChain.pairwise_sUnion`：pairwise_sUnion : (⋃₀ c).Pairwise r ↔ forall s 
in c, s.Pairwise r
-/
lemma pairwiseDisjoint_sUnion [PartialOrder β] [OrderBot β] (f : α → β) :
    (⋃₀ c).PairwiseDisjoint f ↔ ∀ s ∈ c, s.PairwiseDisjoint f :=
  hc.pairwise_sUnion

end IsChain

