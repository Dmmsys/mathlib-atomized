/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Deletion of edges and vertices

This file defines the deletion of edges and vertices from a graph.

## Main definitions

- `restrict`: the subgraph of `G` restricted to the edges in `F` without
  removing vertices
- `deleteEdges`: the subgraph of `G` with the edges in `F` deleted
- `induce`: the subgraph of `G` induced by the set `X` of vertices
- `deleteVerts` : the graph obtained from `G` by deleting the set `X` of vertices

## Tags

graphs, edge deletion, vertex deletion
-/

public section

variable {α β : Type*} {x y : α} {e : β} {G H : Graph α β} {F F₀ : Set β} {X : Set α}

open Set Function

namespace Graph

/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[expose, simps (attr := grind =)]
/-
**Graph.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：restrict (G : Graph α β) (E₀ : Set β) : Graph α β where vertexSet
参数：G : Graph α β；E₀ : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices
-/
def restrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vertexSet := V(G)
  edgeSet := E(G) ∩ E₀
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm e he := { symm x y h := ⟨h.1, h.2.symm⟩ }
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.2.left_eq_or_eq h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h ↦ by simp [G.exists_isLink_of_mem_edgeSet h.1, h.2],
    fun ⟨x, y, h⟩ ↦ ⟨h.2.edge_mem, h.1⟩⟩

@[simp]
/-
**Graph.restrict_le** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_le {E₀ : Set β} : G.restrict E₀ <= G where vertexSet_mono
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Graph.restrict_isLink`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β) (
E₀ : Set β) (e : β) (x y : α),   (G.restrict E₀).IsLink e x y = (e ∈ E₀ ∧ G.IsLi
nk e x y)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma restrict_le {E₀ : Set β} : G.restrict E₀ ≤ G where
  vertexSet_mono := le_rfl
  isLink_mono := by simp

@[simp]
/-
**Graph.restrict_eq_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_eq_self_iff (G : Graph α β) (E₀ : Set β) : G.restrict E₀ = G ↔ E(
G) subseteq E₀
参数：G : Graph α β；E₀ : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.edgeSet_restrict`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β) 
(E₀ : Set β), (G.restrict E₀).edgeSet = G.edgeSet ∩ E₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Graph.IsSubgraph.edgeSet_mono`：∀ {α : Type u_1} {β : Type u_2} {G H : Gr
aph α β}, H ≤ G → H.edgeSet ⊆ G.edgeSet
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Graph.Compatible.ext`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph α β
},   H₁.vertexSet = H₂.vertexSet → H₁.edgeSet = H₂.edgeSet → H₁.Compatible H₂ → 
H₁ = H₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Graph.vertexSet_restrict`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β
) (E₀ : Set β), (G.restrict E₀).vertexSet = G.vertexSet
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Graph.Compatible.of_le`：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β
}, H ≤ G → H.Compatible G
· 使用引理 `Graph.restrict_le`：restrict_le {E₀ : Set β} : G.restrict E₀ <= G where v
ertexSet_mono
-/
lemma restrict_eq_self_iff (G : Graph α β) (E₀ : Set β) : G.restrict E₀ = G ↔ E(G) ⊆ E₀ :=
  ⟨fun h ↦ by simpa using h.ge.edgeSet_mono,
    fun h ↦ (Compatible.of_le restrict_le).ext (by simp) (by simpa)⟩

@[simp]
/-
**Graph.restrict_self** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_self (G : Graph α β) : G.restrict E(G) = G
参数：G : Graph α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.ext`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph α β
},   H₁.vertexSet = H₂.vertexSet → H₁.edgeSet = H₂.edgeSet → H₁.Compatible H₂ → 
H₁ = H₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.edgeSet_restrict`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β) 
(E₀ : Set β), (G.restrict E₀).edgeSet = G.edgeSet ∩ E₀
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Graph.Compatible.of_le_le`：∀ {α : Type u_1} {β : Type u_2} {G H₁ H₂ : Gr
aph α β}, H₁ ≤ G → H₂ ≤ G → H₁.Compatible H₂
-/
lemma restrict_self (G : Graph α β) : G.restrict E(G) = G :=
  (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl (by simp)

@[simp]
/-
**Graph.restrict_edgeSet_inter** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_edgeSet_inter (G : Graph α β) (F : Set β) : G.restrict (E(G) inte
r F) = G.restrict F
参数：G : Graph α β；F : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.ext`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph α β
},   H₁.vertexSet = H₂.vertexSet → H₁.edgeSet = H₂.edgeSet → H₁.Compatible H₂ → 
H₁ = H₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.vertexSet_restrict`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β
) (E₀ : Set β), (G.restrict E₀).vertexSet = G.vertexSet
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Graph.edgeSet_restrict`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β) 
(E₀ : Set β), (G.restrict E₀).edgeSet = G.edgeSet ∩ E₀
· 使用定理 `Graph.Compatible.of_le_le`：∀ {α : Type u_1} {β : Type u_2} {G H₁ H₂ : Gr
aph α β}, H₁ ≤ G → H₂ ≤ G → H₁.Compatible H₂
-/
lemma restrict_edgeSet_inter (G : Graph α β) (F : Set β) : G.restrict (E(G) ∩ F) = G.restrict F :=
  (Compatible.of_le_le (G := G) (by simp) (by simp)).ext (by simp) (by simp)

@[simp]
/-
**Graph.restrict_inter_edgeSet** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_inter_edgeSet (G : Graph α β) (F : Set β) : G.restrict (F inter E
(G)) = G.restrict F
参数：G : Graph α β；F : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `Graph.restrict_edgeSet_inter`：restrict_edgeSet_inter (G : Graph α β) (F 
: Set β) : G.restrict (E(G) inter F) = G.restrict F
-/
lemma restrict_inter_edgeSet (G : Graph α β) (F : Set β) :
    G.restrict (F ∩ E(G)) = G.restrict F := by
  rw [inter_comm, restrict_edgeSet_inter]

@[gcongr]
/-
**Graph.restrict_mono_left** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_mono_left (h : H <= G) (F : Set β) : H.restrict F <= G.restrict F
参数：h : H <= G；F : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Graph.Compatible.le_iff`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph 
α β},   H₁.Compatible H₂ → (H₁ ≤ H₂ ↔ H₁.vertexSet ⊆ H₂.vertexSet ∧ H₁.edgeSet ⊆
 H₂.edgeSet)
· 使用定理 `Graph.Compatible.of_le_le`：∀ {α : Type u_1} {β : Type u_2} {G H₁ H₂ : Gr
aph α β}, H₁ ≤ G → H₂ ≤ G → H₁.Compatible H₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Graph.restrict_le`：restrict_le {E₀ : Set β} : G.restrict E₀ <= G where v
ertexSet_mono
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.vertexSet_restrict`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β
) (E₀ : Set β), (G.restrict E₀).vertexSet = G.vertexSet
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Graph.edgeSet_restrict`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β) 
(E₀ : Set β), (G.restrict E₀).edgeSet = G.edgeSet ∩ E₀
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Graph.IsSubgraph.edgeSet_mono`：∀ {α : Type u_1} {β : Type u_2} {G H : Gr
aph α β}, H ≤ G → H.edgeSet ⊆ G.edgeSet
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma restrict_mono_left (h : H ≤ G) (F : Set β) : H.restrict F ≤ G.restrict F := by
  refine (Compatible.of_le_le (G := G) (restrict_le.trans h) (by simp)).le_iff.mpr ⟨?_, ?_⟩
  · simpa using h.vertexSet_mono
  simp [inter_subset_left.trans h.edgeSet_mono]

@[gcongr]
/-
**Graph.restrict_mono_right** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_mono_right (G : Graph α β) (hss : F₀ subseteq F) : G.restrict F₀ 
<= G.restrict F where vertexSet_mono
参数：G : Graph α β；hss : F₀ subseteq F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma restrict_mono_right (G : Graph α β) (hss : F₀ ⊆ F) : G.restrict F₀ ≤ G.restrict F where
  vertexSet_mono := subset_rfl
  isLink_mono _ _ _ := fun h ↦ ⟨hss h.1, h.2⟩

@[simp, grind =]
/-
**Graph.restrict_inc** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_inc : (G.restrict F).Inc e x ↔ G.Inc e x ∧ e in F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Graph.restrict_isLink`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β) (
E₀ : Set β) (e : β) (x y : α),   (G.restrict E₀).IsLink e x y = (e ∈ E₀ ∧ G.IsLi
nk e x y)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrict_inc : (G.restrict F).Inc e x ↔ G.Inc e x ∧ e ∈ F := by
  simp [Inc, and_comm]

@[simp, grind =]
/-
**Graph.restrict_isLoopAt** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_isLoopAt : (G.restrict F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e in F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.restrict_isLink`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β) (
E₀ : Set β) (e : β) (x y : α),   (G.restrict E₀).IsLink e x y = (e ∈ E₀ ∧ G.IsLi
nk e x y)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrict_isLoopAt : (G.restrict F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∈ F := by
  simp [← isLink_self_iff, and_comm]

@[simp]
/-
**Graph.restrict_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_restrict (G : Graph α β) (F₁ F₂ : Set β) : (G.restrict F₁).restri
ct F₂ = G.restrict (F₁ inter F₂)
参数：G : Graph α β；F₁ F₂ : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.ext`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph α β
},   H₁.vertexSet = H₂.vertexSet → H₁.edgeSet = H₂.edgeSet → H₁.Compatible H₂ → 
H₁ = H₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.vertexSet_restrict`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β
) (E₀ : Set β), (G.restrict E₀).vertexSet = G.vertexSet
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Graph.edgeSet_restrict`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β) 
(E₀ : Set β), (G.restrict E₀).edgeSet = G.edgeSet ∩ E₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Graph.Compatible.of_le_le`：∀ {α : Type u_1} {β : Type u_2} {G H₁ H₂ : Gr
aph α β}, H₁ ≤ G → H₂ ≤ G → H₁.Compatible H₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Graph.restrict_le`：restrict_le {E₀ : Set β} : G.restrict E₀ <= G where v
ertexSet_mono
-/
lemma restrict_restrict (G : Graph α β) (F₁ F₂ : Set β) :
    (G.restrict F₁).restrict F₂ = G.restrict (F₁ ∩ F₂) := by
  refine (Compatible.of_le_le (G := G) (restrict_le.trans (by simp)) (by simp)).ext (by simp) ?_
  simp only [edgeSet_restrict]
  rw [← inter_assoc, inter_comm _ F₂]

/-- Delete a set `F` of edges from `G`. This is a special case of `restrict`,
but we define it with `copy` so that the edge set is definitionally equal to `E(G) \ F`. -/
@[expose, simps! (attr := grind =)]
/-
**Graph.deleteEdges** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：deleteEdges (G : Graph α β) (F : Set β) : Graph α β
参数：G : Graph α β；F : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Delete a set `F` of edges from `G`. This is a special case of `restrict`,
but we define it with `copy` so that the edge set is definitionally equal to `E(
G) \ F`.
-/
def deleteEdges (G : Graph α β) (F : Set β) : Graph α β :=
  (G.restrict (E(G) \ F)).copy (edgeSet := E(G) \ F)
  (IsLink := fun e x y ↦ G.IsLink e x y ∧ e ∉ F) rfl (by simp)
  (fun e x y ↦ by
    simp only [restrict_isLink, mem_sdiff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ ↦ h.edge_mem)

@[simp]
/-
**Graph.restrict_edgeSet_sdiff_eq_deleteEdges** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_edgeSet_sdiff_eq_deleteEdges (G : Graph α β) (F : Set β) : .symm 
G.restrict (E(G) \ F) = G.deleteEdges F
参数：G : Graph α β；F : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Graph.copy_eq`：copy_eq (G : Graph α β) {V : Set α} {E : Set β} {IsLink :
 β -> α -> α -> Prop} (hV : V(G) = V) (hE : E(G) = E) (h_isLink : forall e x y, 
G.I…
-/
lemma restrict_edgeSet_sdiff_eq_deleteEdges (G : Graph α β) (F : Set β) :
    G.restrict (E(G) \ F) = G.deleteEdges F := copy_eq .. |>.symm

@[deprecated (since := "2026-06-03")]
alias restrict_edgeSet_diff_eq_deleteEdges := restrict_edgeSet_sdiff_eq_deleteEdges

@[simp]
/-
**Graph.deleteEdges_le** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：deleteEdges_le : G.deleteEdges F <= G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma deleteEdges_le : G.deleteEdges F ≤ G := by
  simp [← restrict_edgeSet_sdiff_eq_deleteEdges]
/-
**Graph.restrict_eq_deleteEdges** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：restrict_eq_deleteEdges (G : Graph α β) (F : Set β) : G.restrict F = G.del
eteEdges (E(G) \ F)
参数：G : Graph α β；F : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.ext`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph α β
},   H₁.vertexSet = H₂.vertexSet → H₁.edgeSet = H₂.edgeSet → H₁.Compatible H₂ → 
H₁ = H₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.edgeSet_restrict`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β) 
(E₀ : Set β), (G.restrict E₀).edgeSet = G.edgeSet ∩ E₀
· 使用定理 `Graph.edgeSet_deleteEdges`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α 
β) (F : Set β), (G.deleteEdges F).edgeSet = G.edgeSet \ F
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Graph.Compatible.of_le_le`：∀ {α : Type u_1} {β : Type u_2} {G H₁ H₂ : Gr
aph α β}, H₁ ≤ G → H₂ ≤ G → H₁.Compatible H₂
· 使用引理 `Graph.restrict_le`：restrict_le {E₀ : Set β} : G.restrict E₀ <= G where v
ertexSet_mono
· 使用引理 `Graph.deleteEdges_le`：deleteEdges_le : G.deleteEdges F <= G
-/
lemma restrict_eq_deleteEdges (G : Graph α β) (F : Set β) :
    G.restrict F = G.deleteEdges (E(G) \ F) :=
  (Compatible.of_le_le restrict_le deleteEdges_le).ext rfl (by simp)

@[simp, grind =]
/-
**Graph.deleteEdges_empty** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：deleteEdges_empty : G.deleteEdges ∅ = G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用引理 `Graph.restrict_self`：restrict_self (G : Graph α β) : G.restrict E(G) = G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deleteEdges_empty : G.deleteEdges ∅ = G := by
  simp [← restrict_edgeSet_sdiff_eq_deleteEdges]

@[gcongr]
/-
**Graph.deleteEdges_mono_left** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：deleteEdges_mono_left (h : H <= G) (F : Set β) : H.deleteEdges F <= G.dele
teEdges F
参数：h : H <= G；F : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Graph.restrict_mono_left`：restrict_mono_left (h : H <= G) (F : Set β) : 
H.restrict F <= G.restrict F
· 使用引理 `Graph.restrict_mono_right`：restrict_mono_right (G : Graph α β) (hss : F₀
 subseteq F) : G.restrict F₀ <= G.restrict F where vertexSet_mono
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
· 使用定理 `Graph.IsSubgraph.edgeSet_mono`：∀ {α : Type u_1} {β : Type u_2} {G H : Gr
aph α β}, H ≤ G → H.edgeSet ⊆ G.edgeSet
-/
lemma deleteEdges_mono_left (h : H ≤ G) (F : Set β) : H.deleteEdges F ≤ G.deleteEdges F := by
  simp_rw [← restrict_edgeSet_sdiff_eq_deleteEdges]
  refine (restrict_mono_left h (E(H) \ F)).trans (G.restrict_mono_right ?_)
  exact sdiff_subset_sdiff_left h.edgeSet_mono

@[simp, grind =]
/-
**Graph.deleteEdges_inc** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：deleteEdges_inc : (G.deleteEdges F).Inc e x ↔ G.Inc e x ∧ e ∉ F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Graph.deleteEdges_isLink`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β
) (F : Set β) (e : β) (x y : α),   (G.deleteEdges F).IsLink e x y = (G.IsLink e 
x y ∧ e ∉ F)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma deleteEdges_inc : (G.deleteEdges F).Inc e x ↔ G.Inc e x ∧ e ∉ F := by
  simp [Inc, and_comm]

@[simp, grind =]
/-
**Graph.deleteEdges_isLoopAt** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：deleteEdges_isLoopAt : (G.deleteEdges F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e
 ∉ F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Graph.IsLoopAt.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β}
 {G : Graph α β}, G.IsLoopAt e x → e ∈ G.edgeSet
-/
lemma deleteEdges_isLoopAt : (G.deleteEdges F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∉ F := by
  simp only [← restrict_edgeSet_sdiff_eq_deleteEdges, restrict_isLoopAt, mem_sdiff,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[simp]
/-
**Graph.deleteEdges_deleteEdges** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：deleteEdges_deleteEdges (G : Graph α β) (F₁ F₂ : Set β) : (G.deleteEdges F
₁).deleteEdges F₂ = G.deleteEdges (F₁ union F₂)
参数：G : Graph α β；F₁ F₂ : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用引理 `Graph.restrict_inter_edgeSet`：restrict_inter_edgeSet (G : Graph α β) (F 
: Set β) : G.restrict (F inter E(G)) = G.restrict F
· 使用定理 `Graph.edgeSet_restrict`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β) 
(E₀ : Set β), (G.restrict E₀).edgeSet = G.edgeSet ∩ E₀
· 使用引理 `Graph.restrict_restrict`：restrict_restrict (G : Graph α β) (F₁ F₂ : Set 
β) : (G.restrict F₁).restrict F₂ = G.restrict (F₁ inter F₂)
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
-/
lemma deleteEdges_deleteEdges (G : Graph α β) (F₁ F₂ : Set β) :
    (G.deleteEdges F₁).deleteEdges F₂ = G.deleteEdges (F₁ ∪ F₂) := by
  simp only [← restrict_edgeSet_sdiff_eq_deleteEdges, sdiff_eq_compl_inter, restrict_inter_edgeSet,
    edgeSet_restrict, restrict_restrict, compl_union]
  rw [← inter_comm, inter_comm F₁ᶜ, inter_assoc, inter_assoc, inter_self, inter_comm,
    inter_assoc, inter_comm, restrict_inter_edgeSet, inter_comm]

/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case) -/
@[expose, simps! (attr := grind =) vertexSet isLink]
/-
**Graph.induce** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Graph α β → Set α → Graph α β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case)
-/
protected def induce (G : Graph α β) (X : Set α) : Graph α β where
  vertexSet := X
  IsLink e x y := G.IsLink e x y ∧ x ∈ X ∧ y ∈ X
  isLink_symm := by simp +contextual [symm_def, G.isLink_comm]
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
/-
**Graph.induce_le** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：induce_le (hX : X subseteq V(G)) : G.induce X <= G
参数：hX : X subseteq V(G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma induce_le (hX : X ⊆ V(G)) : G.induce X ≤ G := ⟨hX, fun _ _ _ h ↦ h.1⟩

@[simp, grind =]
/-
**Graph.induce_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：induce_le_iff : G.induce X <= G ↔ X subseteq V(G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
· 使用引理 `Graph.induce_le`：induce_le (hX : X subseteq V(G)) : G.induce X <= G
-/
lemma induce_le_iff : G.induce X ≤ G ↔ X ⊆ V(G) := ⟨(·.vertexSet_mono), induce_le⟩
/-
**Graph.edgeSet_induce** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：edgeSet_induce (G : Graph α β) (X : Set α) : E(G.induce X) = {e | exists x
 y, G.IsLink e x y ∧ x in X ∧ y in X}
参数：G : Graph α β；X : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edgeSet_induce (G : Graph α β) (X : Set α) :
    E(G.induce X) = {e | ∃ x y, G.IsLink e x y ∧ x ∈ X ∧ y ∈ X} := rfl

@[simp, grind =]
/-
**Graph.induce_vertexSet** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：induce_vertexSet (G : Graph α β) : G.induce V(G) = G
参数：G : Graph α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.ext`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph α β
},   H₁.vertexSet = H₂.vertexSet → H₁.edgeSet = H₂.edgeSet → H₁.Compatible H₂ → 
H₁ = H₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Graph.exists_isLink_of_mem_edgeSet`：exists_isLink_of_mem_edgeSet (h : e 
in E(G)) : exists x y, G.IsLink e x y
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `Graph.IsLink.right_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β
} {G : Graph α β}, G.IsLink e x y → y ∈ G.vertexSet
· 使用定理 `Graph.Compatible.of_le_le`：∀ {α : Type u_1} {β : Type u_2} {G H₁ H₂ : Gr
aph α β}, H₁ ≤ G → H₂ ≤ G → H₁.Compatible H₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma induce_vertexSet (G : Graph α β) : G.induce V(G) = G := by
  refine (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl <| Set.ext fun e ↦
    ⟨fun ⟨_, _, h⟩ ↦ h.1.edge_mem, fun h ↦ ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, h.left_mem, h.right_mem⟩

/-- The graph obtained from `G` by deleting a set of vertices. -/
/-
**Graph.deleteVerts** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：deleteVerts (G : Graph α β) (X : Set α) : Graph α β
参数：G : Graph α β；X : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph obtained from `G` by deleting a set of vertices.
-/
def deleteVerts (G : Graph α β) (X : Set α) : Graph α β := G.induce (V(G) \ X)

@[simp, grind =]
/-
**Graph.vertexSet_deleteVerts** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：vertexSet_deleteVerts (G : Graph α β) (X : Set α) : V(G.deleteVerts X) = V
(G) \ X
参数：G : Graph α β；X : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma vertexSet_deleteVerts (G : Graph α β) (X : Set α) : V(G.deleteVerts X) = V(G) \ X := by
  unfold deleteVerts
  rfl

@[simp, grind =]
/-
**Graph.deleteVerts_isLink** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：deleteVerts_isLink (G : Graph α β) (X : Set α) : (G.deleteVerts X).IsLink 
e x y ↔ (G.IsLink e x y ∧ x ∉ X ∧ y ∉ X)
参数：G : Graph α β；X : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.induce_isLink`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β) (X 
: Set α) (e : β) (x y : α),   (G.induce X).IsLink e x y = (G.IsLink e x y ∧ x ∈ 
X ∧ y ∈ X…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Graph.IsLink.right_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β
} {G : Graph α β}, G.IsLink e x y → y ∈ G.vertexSet
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma deleteVerts_isLink (G : Graph α β) (X : Set α) :
    (G.deleteVerts X).IsLink e x y ↔ (G.IsLink e x y ∧ x ∉ X ∧ y ∉ X) := by
  simp only [deleteVerts, induce_isLink, mem_sdiff, and_congr_right_iff]
  exact fun h ↦ by simp [h.left_mem, h.right_mem]

@[simp]
/-
**Graph.edgeSet_deleteVerts** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：edgeSet_deleteVerts (G : Graph α β) (X : Set α) : E(G.deleteVerts X) = {e 
| exists x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X}
参数：G : Graph α β；X : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Graph.edgeSet_eq_setOfPred_exists_isLink`：edgeSet_eq_setOfPred_exists_is
Link : E(G) = {e | exists x y, G.IsLink e x y}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edgeSet_deleteVerts (G : Graph α β) (X : Set α) :
    E(G.deleteVerts X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X} := by
  simp [edgeSet_eq_setOfPred_exists_isLink]

@[simp, grind =]
/-
**Graph.deleteVerts_empty** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：deleteVerts_empty (G : Graph α β) : G.deleteVerts (∅ : Set α) = G
参数：G : Graph α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_empty`：sdiff_empty {s : Set α} : s \ ∅ = s
· 使用引理 `Graph.induce_vertexSet`：induce_vertexSet (G : Graph α β) : G.induce V(G)
 = G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma deleteVerts_empty (G : Graph α β) : G.deleteVerts (∅ : Set α) = G := by
  simp [deleteVerts]
/-
**Graph.deleteVerts_le** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β} {X : Set α}, G.deleteVerts
 X ≤ G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Graph.induce_le`：induce_le (hX : X subseteq V(G)) : G.induce X <= G
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
@[simp] lemma deleteVerts_le : G.deleteVerts X ≤ G := G.induce_le sdiff_subset

end Graph

