/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Snir Broshi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# LineGraph

## Main definitions

* `SimpleGraph.lineGraph` is the line graph of a simple graph `G`, with vertices as the edges of `G`
  and two vertices of the line graph adjacent if the corresponding edges share a vertex in `G`.

## Tags

line graph
-/

@[expose] public section

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}

variable (G) in
/--
The line graph of a simple graph `G` has its vertex set as the edges of `G`, and two vertices of
the line graph are adjacent if the corresponding edges share a vertex in `G`.
-/
/-
**SimpleGraph.lineGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：lineGraph : SimpleGraph G.edgeSet where Adj e₁ e₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The line graph of a simple graph `G` has its vertex set as the edges of `G`, and
 two vertices of
the line graph are adjacent if the corresponding edges share a vertex in `G`.
-/
def lineGraph : SimpleGraph G.edgeSet where
  Adj e₁ e₂ := e₁ ≠ e₂ ∧ (e₁ ∩ e₂ : Set V).Nonempty
  symm.symm e₁ e₂ hadj := by rwa [ne_comm, Set.inter_comm]
/-
**SimpleGraph.lineGraph_adj_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：lineGraph_adj_iff_exists {e₁ e₂ : G.edgeSet} : (G.lineGraph).Adj e₁ e₂ ↔ e
₁ != e₂ ∧ exists v, v in (e₁ : Sym2 V) ∧ v in (e₂ : Sym2 V)
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.mk.congr_simp`：∀ {V : Type u} (Adj Adj_1 : V → V → Prop) (e_
Adj : Adj = Adj_1) (symm : Std.Symm Adj) (loopless : Std.Irrefl Adj),   { Adj :=
 Adj, symm := s…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lineGraph_adj_iff_exists {e₁ e₂ : G.edgeSet} :
    (G.lineGraph).Adj e₁ e₂ ↔ e₁ ≠ e₂ ∧ ∃ v, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V) := by
  simp [Set.Nonempty, lineGraph]
/-
**SimpleGraph.lineGraph_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1}, ⊥.lineGraph = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.edgeSet_bot`：edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅
-/
@[simp] lemma lineGraph_bot : (⊥ : SimpleGraph V).lineGraph = ⊥ := by aesop (add simp lineGraph)

set_option backward.isDefEq.respectTransparency false in
/-- Lift a copy between graphs to an embedding between their line graphs -/
/-
**SimpleGraph.Copy.toLineGraphEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.C
opy`。
形式化陈述：{V : Type u_1} → {V' : Type u_2} → {G : SimpleGraph V} → {G' : SimpleGraph
 V'} → G.Copy G' → G.lineGraph ↪g G'.lineGraph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a copy between graphs to an embedding between their line graphs
-/
def Copy.toLineGraphEmbedding (f : Copy G G') : G.lineGraph ↪g G'.lineGraph where
  toFun e := ⟨e.val.map f, by rcases e with ⟨⟨⟩, h⟩; exact f.toHom.map_adj h⟩
  inj' _ _ h := SetCoe.ext <| Sym2.map.injective f.injective <| Subtype.mk.inj h
  map_rel_iff' := by
    simp only [lineGraph, Function.Embedding.coeFn_mk, Sym2.coe_map, ne_eq]
    refine .and ?_ <| Set.image_inter f.injective ▸ Set.image_nonempty
    rw [Subtype.mk.injEq, Subtype.mk.injEq]
    exact Sym2.map.injective f.injective |>.eq_iff.not
/-
**SimpleGraph.IsIndContained.lineGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Is
IndContained`。
形式化陈述：∀ {V : Type u_1} {V' : Type u_2} {G : SimpleGraph V} {G' : SimpleGraph V'}
,   G.IsIndContained G' → G.lineGraph.IsIndContained G'.lineGraph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsIndContained.lineGraph (h : G ⊴ G') : G.lineGraph ⊴ G'.lineGraph :=
  ⟨h.some.toCopy.toLineGraphEmbedding⟩
/-
**SimpleGraph.IsContained.isIndContained_lineGraph** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.IsContained`。
形式化陈述：∀ {V : Type u_1} {V' : Type u_2} {G : SimpleGraph V} {G' : SimpleGraph V'}
,   G.IsContained G' → G.lineGraph.IsIndContained G'.lineGraph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsContained.isIndContained_lineGraph (h : G ⊑ G') : G.lineGraph ⊴ G'.lineGraph :=
  ⟨h.some.toLineGraphEmbedding⟩

/-- Lift a copy between graphs to a copy between their line graphs -/
/-
**SimpleGraph.Copy.lineGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Copy`。
形式化陈述：{V : Type u_1} →   {V' : Type u_2} → {G : SimpleGraph V} → {G' : SimpleGra
ph V'} → G.Copy G' → G.lineGraph.Copy G'.lineGraph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a copy between graphs to a copy between their line graphs
-/
def Copy.lineGraph (f : Copy G G') : Copy G.lineGraph G'.lineGraph :=
  f.toLineGraphEmbedding.toCopy
/-
**SimpleGraph.IsContained.lineGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsCon
tained`。
形式化陈述：∀ {V : Type u_1} {V' : Type u_2} {G : SimpleGraph V} {G' : SimpleGraph V'}
,   G.IsContained G' → G.lineGraph.IsContained G'.lineGraph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsContained.lineGraph (h : G ⊑ G') : G.lineGraph ⊑ G'.lineGraph :=
  ⟨h.some.lineGraph⟩

/-- Lift an isomorphism between graphs to an isomorphism between their line graphs -/
/-
**SimpleGraph.Iso.lineGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：{V : Type u_1} → {V' : Type u_2} → {G : SimpleGraph V} → {G' : SimpleGraph
 V'} → G ≃g G' → G.lineGraph ≃g G'.lineGraph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift an isomorphism between graphs to an isomorphism between their line graphs
-/
def Iso.lineGraph (f : G ≃g G') : G.lineGraph ≃g G'.lineGraph where
  toFun := f.toCopy.lineGraph
  invFun := f.symm.toCopy.lineGraph
  left_inv _ := by simp [Copy.lineGraph, Copy.toLineGraphEmbedding, Sym2.map_map]
  right_inv _ := by simp [Copy.lineGraph, Copy.toLineGraphEmbedding, Sym2.map_map]
  map_rel_iff' := Copy.toLineGraphEmbedding f.toCopy |>.map_rel_iff

open Function.Embedding in
/-
**SimpleGraph.map_lineGraph_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：map_lineGraph_le_of_le {G' : SimpleGraph V} (h : G <= G') : G.lineGraph.ma
p (subtype _) <= G'.lineGraph.map (subtype _)
参数：h : G <= G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
-/
theorem map_lineGraph_le_of_le {G' : SimpleGraph V} (h : G ≤ G') :
    G.lineGraph.map (subtype _) ≤ G'.lineGraph.map (subtype _) := by
  rintro _ _ ⟨hne', ⟨⟨⟩, h₁⟩, ⟨⟨⟩, h₂⟩, ⟨hne, hinter⟩, rfl, rfl⟩
  exact ⟨hne', ⟨⟨_, h h₁⟩, ⟨_, h h₂⟩, ⟨(hne <| Subtype.ext <| Subtype.mk.inj ·), hinter⟩, rfl, rfl⟩⟩

@[deprecated (since := "2026-03-26")] alias IsSubgraph.lineGraph := map_lineGraph_le_of_le

end SimpleGraph

