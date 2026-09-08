/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Intersection and union of graphs

This file defines the lattice-like structures on graphs.

## Main results

- `SemilatticeInf (Graph α β)`

## Implementation notes

Intersections are defined here as the maximal mutual subgraph of the given graphs.
This has the effect of, when taking the intersection of non-compatible graphs,
**any non-compatible edges are removed**.

## TODO

+ Add `ConditionallyCompleteCompleteLatticeInf (Graph α β)` after splitting
  `ConditionallyCompleteCompleteLattice`.

-/

public section

open Function Set

variable {α β : Type*} {x y : α} {e : β} {G H : Graph α β}

namespace Graph

/-- The infimum of two graphs `G` and `H`. The edges are precisely those on which `G` and `H` agree,
and the edge set is a subset of `E(G) ∩ E(H)`, with equality if `G` and `H` are compatible. -/
/-
**Graph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of two graphs `G` and `H`. The edges are precisely those on which `G
` and `H` agree,
and the edge set is a subset of `E(G) ∩ E(H)`, with equality if `G` and `H` are 
compatible.
-/
instance : SemilatticeInf (Graph α β) where
  inf G H := {
    vertexSet := V(G) ∩ V(H)
    edgeSet := {e ∈ E(G) ∩ E(H) | ∀ x y, G.IsLink e x y ↔ H.IsLink e x y}
    IsLink e x y := G.IsLink e x y ∧ H.IsLink e x y
    isLink_symm _ _ := { symm _ _ h := ⟨h.1.symm, h.2.symm⟩ }
    eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
    edge_mem_iff_exists_isLink e := by
      simp only [edgeSet_eq_setOfPred_exists_isLink, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨⟨⟨x, y, hexy⟩, ⟨z, w, hezw⟩⟩, h⟩ ↦ ⟨x, y, hexy, by rwa [← h]⟩,
        fun ⟨x, y, hfG, hfH⟩ ↦ ⟨⟨⟨_, _, hfG⟩, ⟨_, _, hfH⟩⟩,
        fun z w ↦ by rw [hfG.isLink_iff_sym2_eq, hfH.isLink_iff_sym2_eq]⟩⟩
    left_mem_of_isLink e x y h := ⟨h.1.left_mem, h.2.left_mem⟩}
  inf_le_left G H := {
    vertexSet_mono := inter_subset_left
    isLink_mono := by simp +contextual}
  inf_le_right G H := {
    vertexSet_mono := inter_subset_right
    isLink_mono := by simp +contextual}
  le_inf H G₁ G₂ h₁ h₂ := {
    vertexSet_mono := subset_inter h₁.vertexSet_mono h₂.vertexSet_mono
    isLink_mono e x y h := by simp [h₁.isLink_mono h, h₂.isLink_mono h]}
/-
**Graph.vertexSet_inf** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (G H : Graph α β), (G ⊓ H).vertexSet = G.v
ertexSet ∩ H.vertexSet
参数：G H : Graph α β；G ⊓ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma vertexSet_inf (G H : Graph α β) : V(G ⊓ H) = V(G) ∩ V(H) := rfl
/-
**Graph.edgeSet_inf** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：edgeSet_inf (G H : Graph α β) : E(G ⊓ H) = {e in E(G) inter E(H) | forall 
x y, G.IsLink e x y ↔ H.IsLink e x y}
参数：G H : Graph α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edgeSet_inf (G H : Graph α β) :
    E(G ⊓ H) = {e ∈ E(G) ∩ E(H) | ∀ x y, G.IsLink e x y ↔ H.IsLink e x y} := rfl
/-
**Graph.inf_isLink** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G H : Graph α β},   (G 
⊓ H).IsLink e x y ↔ G.IsLink e x y ∧ H.IsLink e x y
参数：G ⊓ H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma inf_isLink : (G ⊓ H).IsLink e x y ↔ G.IsLink e x y ∧ H.IsLink e x y := Iff.rfl

@[simp]
/-
**Graph.inf_inc_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：inf_inc_iff : (G ⊓ H).Inc e x ↔ exists y, G.IsLink e x y ∧ H.IsLink e x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inf_inc_iff : (G ⊓ H).Inc e x ↔ ∃ y, G.IsLink e x y ∧ H.IsLink e x y := by
  simp [Inc]

@[simp]
/-
**Graph.inf_isLoopAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：inf_isLoopAt_iff : (G ⊓ H).IsLoopAt e x ↔ G.IsLoopAt e x ∧ H.IsLoopAt e x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inf_isLoopAt_iff : (G ⊓ H).IsLoopAt e x ↔ G.IsLoopAt e x ∧ H.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
/-
**Graph.inf_isNonloopAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：inf_isNonloopAt_iff : (G ⊓ H).IsNonloopAt e x ↔ exists y != x, G.IsLink e 
x y ∧ H.IsLink e x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inf_isNonloopAt_iff : (G ⊓ H).IsNonloopAt e x ↔ ∃ y ≠ x, G.IsLink e x y ∧ H.IsLink e x y := by
  simp [IsNonloopAt]

@[simp]
/-
**Graph.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, Disjoint G H ↔ Disjoint
 G.vertexSet H.vertexSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Graph.vertexSet_eq_empty_iff`：vertexSet_eq_empty_iff : V(G) = ∅ ↔ G = ⊥
· 使用定理 `Graph.vertexSet_inf`：∀ {α : Type u_1} {β : Type u_2} (G H : Graph α β), 
(G ⊓ H).vertexSet = G.vertexSet ∩ H.vertexSet
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma disjoint_iff : Disjoint G H ↔ Disjoint V(G) V(H) := by
  rw [disjoint_iff, ← vertexSet_eq_empty_iff, vertexSet_inf, disjoint_iff_inter_eq_empty]
/-
**Graph.Compatible.edgeSet_inf** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, G.Compatible H → (G ⊓ H
).edgeSet = G.edgeSet ∩ H.edgeSet
参数：G ⊓ H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Graph.edgeSet_inf`：edgeSet_inf (G H : Graph α β) : E(G ⊓ H) = {e in E(G)
 inter E(H) | forall x y, G.IsLink e x y ↔ H.IsLink e x y}
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Graph.Compatible.isLink_congr`：∀ {α : Type u_1} {β : Type u_2} {e : β} {
G H : Graph α β},   e ∈ G.edgeSet → e ∈ H.edgeSet → G.Compatible H → ∀ {x y : α}
, G.IsLink e x y ↔ …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma Compatible.edgeSet_inf (h : G.Compatible H) : E(G ⊓ H) = E(G) ∩ E(H) := by
  rw [G.edgeSet_inf]
  exact le_antisymm (fun e he ↦ he.1) fun e he ↦ ⟨he, fun _ _ ↦ h.isLink_congr he.1 he.2⟩

end Graph

