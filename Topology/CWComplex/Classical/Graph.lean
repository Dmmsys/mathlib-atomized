/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Combinatorics.Graph.Basic

/-!
# 1-skeletons of CW complexes as graphs

In this file we define the 1-skeleton of a CW complex as a graph.

## Main definitions
* `CWComplex.OneSkeletonGraph`: the 1-skeleton of a CW complex as a graph.

-/

public section

open Metric Set Graph

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/-- The 1-skeleton of a CW complex as a graph. -/
@[expose, simps]
/-
**Topology.CWComplex.OneSkeletonGraph** 是 Mathlib 中的一个定义，位于命名空间 `Topology.CWComp
lex`。
形式化陈述：{X : Type u_1} →   [inst : TopologicalSpace X] →     (C : Set X) →       [
inst_1 : Topology.CWComplex C] → Graph (Topology.RelCWComplex.cell C 0) (Topolog
y.RelCWComplex.cell C 1)
参数：C : Set X；Topology.RelCWComplex.cell C 0；Topology.RelCWComplex.cell C 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 1-skeleton of a CW complex as a graph.
-/
def CWComplex.OneSkeletonGraph (C : Set X) [CWComplex C] : Graph (cell C 0) (cell C 1) where
  vertexSet := univ
  edgeSet := univ
  IsLink e x y := cellFrontier 1 e = closedCell 0 x ∪ closedCell 0 y
  isLink_symm := by grind [symm_def]
  eq_or_eq_of_isLink_of_isLink e x y z w h1 h2 := by
    simp_rw [closedCell_zero_eq_singleton] at h1 h2
    rw [h1] at h2
    simp only [(RelCWComplex.injective_map_zero C).eq_iff, union_singleton, pair_eq_pair_iff] at h2
    tauto
  left_mem_of_isLink _ _ _ _ := mem_univ _
  edge_mem_iff_exists_isLink e := by
    simp only [mem_univ, true_iff]
    exact exists_cellFrontier_one_eq e

namespace CWComplex.OneSkeletonGraph

variable {C : Set X} [CWComplex C]

/-
**Topology.CWComplex.OneSkeletonGraph.isLink_iff_pair** 是 Mathlib 中的一个引理，位于命名空间 
`Topology.CWComplex.OneSkeletonGraph`。
形式化陈述：isLink_iff_pair (e : cell C 1) (x y : cell C 0) : (OneSkeletonGraph C).IsL
ink e x y ↔ cellFrontier 1 e = {map 0 x ![], map 0 y ![]}
参数：e : cell C 1；x y : cell C 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.CWComplex.OneSkeletonGraph_isLink`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] (C : Set X) [inst_1 : Topology.CWComplex C]   (e : Topology.Rel
CWComplex.cell C 1) (x y : Topol…
· 使用定理 `Topology.CWComplex.closedCell_zero_eq_singleton`：∀ {X : Type u_1} [t : T
opologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   {j : Topol
ogy.RelCWComplex.cell C 0}, Topology.…
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLink_iff_pair (e : cell C 1) (x y : cell C 0) :
    (OneSkeletonGraph C).IsLink e x y ↔ cellFrontier 1 e = {map 0 x ![], map 0 y ![]} := by
  rw [OneSkeletonGraph_isLink, closedCell_zero_eq_singleton, closedCell_zero_eq_singleton,
    singleton_union]
/-
**Topology.CWComplex.OneSkeletonGraph.exists_isLoopAt_iff** 是 Mathlib 中的一个引理，位于命
名空间 `Topology.CWComplex.OneSkeletonGraph`。
形式化陈述：exists_isLoopAt_iff (e : cell C 1) : (exists x : cell C 0, (OneSkeletonGra
ph C).IsLoopAt e x) ↔ exists x : cell C 0, cellFrontier 1 e = closedCell 0 x
参数：e : cell C 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma exists_isLoopAt_iff (e : cell C 1) : (∃ x : cell C 0, (OneSkeletonGraph C).IsLoopAt e x) ↔
      ∃ x : cell C 0, cellFrontier 1 e = closedCell 0 x := by
  refine exists_congr fun x ↦ ?_
  change cellFrontier 1 e = closedCell 0 x ∪ closedCell 0 x ↔ _
  rw [union_self]
/-
**Topology.CWComplex.OneSkeletonGraph.exists_isLoopAt_iff_subsingleton** 是 Mathl
ib 中的一个引理，位于命名空间 `Topology.CWComplex.OneSkeletonGraph`。
形式化陈述：exists_isLoopAt_iff_subsingleton (e : cell C 1) : (exists x : cell C 0, (O
neSkeletonGraph C).IsLoopAt e x) ↔ (cellFrontier 1 e).Subsingleton
参数：e : cell C 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.CWComplex.OneSkeletonGraph.exists_isLoopAt_iff`：exists_isLoopAt
_iff (e : cell C 1) : (exists x : cell C 0, (OneSkeletonGraph C).IsLoopAt e x) ↔
 exists x : cell C 0, cellFrontier 1 e = clos…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Topology.CWComplex.closedCell_zero_eq_singleton`：∀ {X : Type u_1} [t : T
opologicalSpace X] {C D : Set X} [inst : Topology.RelCWComplex C D]   {j : Topol
ogy.RelCWComplex.cell C 0}, Topology.…
· 使用定理 `Topology.CWComplex.exists_cellFrontier_one_eq`：∀ {X : Type u_1} [t : Top
ologicalSpace X] {C : Set X} [inst : Topology.CWComplex C]   (e : Topology.RelCW
Complex.cell C 1),   ∃ x y,     Top…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Topology.RelCWComplex.injective_map_zero`：∀ {X : Type u_1} [t : Topologi
calSpace X] {D : Set X} (C : Set X) [inst : Topology.RelCWComplex C D],   Functi
on.Injective fun x => ↑(Topolo…
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma exists_isLoopAt_iff_subsingleton (e : cell C 1) :
    (∃ x : cell C 0, (OneSkeletonGraph C).IsLoopAt e x) ↔ (cellFrontier 1 e).Subsingleton := by
  rw [exists_isLoopAt_iff]
  refine ⟨fun ⟨x, hx⟩ => by simp [closedCell_zero_eq_singleton, hx], fun h => ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_cellFrontier_one_eq e
  simp only [closedCell_zero_eq_singleton, union_singleton] at hxy
  obtain rfl : x = y := RelCWComplex.injective_map_zero C <| (hxy ▸ h) (by simp) (by simp)
  exact ⟨x, by simp [hxy, closedCell_zero_eq_singleton]⟩
/-
**Topology.CWComplex.OneSkeletonGraph.not_exists_isLoopAt_iff_nontrivial** 是 Mat
hlib 中的一个引理，位于命名空间 `Topology.CWComplex.OneSkeletonGraph`。
形式化陈述：not_exists_isLoopAt_iff_nontrivial (e : cell C 1) : ¬(exists x : cell C 0,
 (OneSkeletonGraph C).IsLoopAt e x) ↔ (cellFrontier 1 e).Nontrivial
参数：e : cell C 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Topology.CWComplex.OneSkeletonGraph.exists_isLoopAt_iff_subsingleton`：ex
ists_isLoopAt_iff_subsingleton (e : cell C 1) : (exists x : cell C 0, (OneSkelet
onGraph C).IsLoopAt e x) ↔ (cellFrontier 1 e).Subsingleton
· 使用定理 `Set.not_subsingleton_iff`：not_subsingleton_iff : ¬s.Subsingleton ↔ s.Non
trivial
-/
lemma not_exists_isLoopAt_iff_nontrivial (e : cell C 1) :
    ¬(∃ x : cell C 0, (OneSkeletonGraph C).IsLoopAt e x) ↔ (cellFrontier 1 e).Nontrivial :=
  (exists_isLoopAt_iff_subsingleton e).not.trans not_subsingleton_iff

@[simp]
/-
**Topology.CWComplex.OneSkeletonGraph.adj_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topolog
y.CWComplex.OneSkeletonGraph`。
形式化陈述：adj_iff (x y : cell C 0) : (OneSkeletonGraph C).Adj x y ↔ exists e : cell 
C 1, cellFrontier 1 e = closedCell 0 x union closedCell 0 y
参数：x y : cell C 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma adj_iff (x y : cell C 0) : (OneSkeletonGraph C).Adj x y ↔
    ∃ e : cell C 1, cellFrontier 1 e = closedCell 0 x ∪ closedCell 0 y := Iff.rfl

end CWComplex.OneSkeletonGraph

end Topology

