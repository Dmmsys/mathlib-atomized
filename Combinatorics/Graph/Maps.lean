/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Peter Nelson
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Maps between graphs

This file defines vertex map between graphs `Graph α β`. Morphisms between graphs will also be
defined in this file in the future.

## Main definitions

* `map`: the map on graphs induced by a function on vertices `f : α → α'`

## TODO

* Morphisms between graphs

-/

public section

variable {α α' α'' β : Type*} {G H : Graph α β} {f g : α → α'} {u v : α} {e : β} {x y : α'}

open Set Relation

namespace Graph

section Map

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set by applying a function `f : α → α'`
  to each vertex. Edges between identified vertices become loops. -/
@[expose, simps! (attr := grind =)]
/-
**Graph.map** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：map (f : α -> α') (G : Graph α β) : Graph α' β where vertexSet
参数：f : α -> α'；G : Graph α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map `G : Graph α β` to a `Graph α' β` with the same edge set by applying a funct
ion `f : α → α'`
  to each vertex. Edges between identified vertices become loops.
-/
def map (f : α → α') (G : Graph α β) : Graph α' β where
  vertexSet := f '' V(G)
  edgeSet := E(G)
  IsLink e := Relation.Map (G.IsLink e) f f
  isLink_symm _ he := have := G.isLink_symm he; .map f
  eq_or_eq_of_isLink_of_isLink := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq hzw <;> simp
  edge_mem_iff_exists_isLink e := by
    refine ⟨fun h ↦ ?_, fun ⟨_, _, _, _, h, _, _⟩ ↦ h.edge_mem⟩
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h
    exact ⟨_, _, _, _, hxy, rfl, rfl⟩
  left_mem_of_isLink := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ h.left_mem
/-
**Graph.IsLink.map** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} {G : Graph α β} {u v : α} 
{e : β} (f : α → α'),   G.IsLink e u v → (Graph.map f G).IsLink e (f u) (f v)
参数：f : α → α'；Graph.map f G；f u；f v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma IsLink.map (f : α → α') (h : G.IsLink e u v) : (G.map f).IsLink e (f u) (f v) :=
  ⟨u, v, h, rfl, rfl⟩

@[simp]
/-
**Graph.map_inc** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：map_inc (f : α -> α') : (G.map f).Inc e x ↔ exists v, G.Inc e v ∧ x = f v
参数：f : α -> α'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Graph.map_isLink`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} (f : α
 → α') (G : Graph α β) (e : β) (a a_1 : α'),   (Graph.map f G).IsLink e a a_1 = 
Relati…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma map_inc (f : α → α') : (G.map f).Inc e x ↔ ∃ v, G.Inc e v ∧ x = f v := by
  simp only [Inc, map_isLink, map_apply]
  tauto
/-
**Graph.Inc.map** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} {G : Graph α β} {v : α} {e
 : β} (f : α → α'),   G.Inc e v → (Graph.map f G).Inc e (f v)
参数：f : α → α'；Graph.map f G；f v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.map`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} {G : G
raph α β} {u v : α} {e : β} (f : α → α'),   G.IsLink e u v → (Graph.map f G).IsL
ink e …
-/
protected lemma Inc.map (f : α → α') (h : G.Inc e v) : (G.map f).Inc e (f v) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨f w, hw.map f⟩

@[simp]
/-
**Graph.map_isLoopAt** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：map_isLoopAt (f : α -> α') : (G.map f).IsLoopAt e x ↔ exists u v, G.IsLink
 e u v ∧ f u = x ∧ f v = x
参数：f : α -> α'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma map_isLoopAt (f : α → α') :
    (G.map f).IsLoopAt e x ↔ ∃ u v, G.IsLink e u v ∧ f u = x ∧ f v = x := Iff.rfl
/-
**Graph.IsLoopAt.map** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLoopAt`。
形式化陈述：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} {G : Graph α β} {v : α} {e
 : β} (f : α → α'),   G.IsLoopAt e v → (Graph.map f G).IsLoopAt e (f v)
参数：f : α → α'；Graph.map f G；f v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.map`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} {G : G
raph α β} {u v : α} {e : β} (f : α → α'),   G.IsLink e u v → (Graph.map f G).IsL
ink e …
-/
protected lemma IsLoopAt.map (f : α → α') (h : G.IsLoopAt e v) : (G.map f).IsLoopAt e (f v) :=
  IsLink.map f h

@[simp]
/-
**Graph.map_adj** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：map_adj (f : α -> α') : (G.map f).Adj x y ↔ Relation.Map G.Adj f f x y
参数：f : α -> α'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Graph.map_isLink`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} (f : α
 → α') (G : Graph α β) (e : β) (a a_1 : α'),   (Graph.map f G).IsLink e a a_1 = 
Relati…
-/
lemma map_adj (f : α → α') : (G.map f).Adj x y ↔ Relation.Map G.Adj f f x y := by
  simp only [Adj, map_isLink, map_apply]
  tauto
/-
**Graph.Adj.map** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Adj`。
形式化陈述：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} {G : Graph α β} {u v : α} 
(f : α → α'),   G.Adj u v → (Graph.map f G).Adj (f u) (f v)
参数：f : α → α'；Graph.map f G；f u；f v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.map`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} {G : G
raph α β} {u v : α} {e : β} (f : α → α'),   G.IsLink e u v → (Graph.map f G).IsL
ink e …
-/
protected lemma Adj.map (f : α → α') (h : G.Adj u v) : (G.map f).Adj (f u) (f v) := by
  obtain ⟨e, h⟩ := h
  exact ⟨e, h.map f⟩
/-
**Graph.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_4} {G : Graph α β}, Graph.map id G = G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.ext`：∀ {α : Type u_1} {β : Type u_2} {G₁ G₂ : Graph α β},   G₁.ver
texSet = G₂.vertexSet → (∀ (e : β) (x y : α), G₁.IsLink e x y ↔ G₂.IsLink e x y…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.vertexSet_map`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} (f 
: α → α') (G : Graph α β),   (Graph.map f G).vertexSet = f '' G.vertexSet
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Graph.map_isLink`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} (f : α
 → α') (G : Graph α β) (e : β) (a a_1 : α'),   (Graph.map f G).IsLink e a a_1 = 
Relati…
· 使用定理 `Relation.map_id_id`：∀ {α : Type u_1} {β : Type u_2} (r : α → β → Prop), 
Relation.Map r id id = r
-/
@[simp] lemma map_id : G.map id = G := by ext a b c <;> simp

@[simp]
/-
**Graph.map_map** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：map_map (f : α -> α') (f' : α' -> α'') : (G.map f).map f' = G.map (f' ∘ f)
参数：f : α -> α'；f' : α' -> α''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.ext`：∀ {α : Type u_1} {β : Type u_2} {G₁ G₂ : Graph α β},   G₁.ver
texSet = G₂.vertexSet → (∀ (e : β) (x y : α), G₁.IsLink e x y ↔ G₂.IsLink e x y…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Graph.vertexSet_map`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} (f 
: α → α') (G : Graph α β),   (Graph.map f G).vertexSet = f '' G.vertexSet
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Graph.map_isLink`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} (f : α
 → α') (G : Graph α β) (e : β) (a a_1 : α'),   (Graph.map f G).IsLink e a a_1 = 
Relati…
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma map_map (f : α → α') (f' : α' → α'') : (G.map f).map f' = G.map (f' ∘ f) := by
  ext a b c <;> simp [map_apply]

@[gcongr]
/-
**Graph.IsSubgraph.map** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph`。
形式化陈述：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} {G H : Graph α β} (f : α →
 α'), G ≤ H → Graph.map f G ≤ Graph.map f H
参数：f : α → α'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Relation.map_mono`：map_mono {r s : α -> β -> Prop} {f : α -> γ} {g : β -
> δ} (h : r <= s) : Relation.Map r f g <= Relation.Map s f g
· 使用定理 `Graph.IsSubgraph.isLink_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : Gra
ph α β}, H.IsSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, H.IsLink e x y → G.IsLink e x y
-/
protected lemma IsSubgraph.map (f : α → α') (h : G ≤ H) : G.map f ≤ H.map f where
  vertexSet_mono v := by grind [h.vertexSet_mono]
  isLink_mono e := map_mono <| h.isLink_mono (e := e)
alias map_mono := IsSubgraph.map

@[gcongr]
/-
**Graph.IsSpanningSubgraph.map** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSpanningSubgra
ph`。
形式化陈述：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} {G H : Graph α β} (f : α →
 α'), G ≤s H → Graph.map f G ≤s Graph.map f H
参数：f : α → α'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsSubgraph.map`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} {G
 H : Graph α β} (f : α → α'), G ≤ H → Graph.map f G ≤ Graph.map f H
· 使用定理 `Graph.IsSpanningSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Grap
h α β}, H ≤s G → H.IsSubgraph G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.vertexSet_map`：∀ {α : Type u_1} {α' : Type u_2} {β : Type u_4} (f 
: α → α') (G : Graph α β),   (Graph.map f G).vertexSet = f '' G.vertexSet
· 使用定理 `Graph.IsSpanningSubgraph.vertexSet_eq`：∀ {α : Type u_1} {β : Type u_2} {
H G : Graph α β}, H ≤s G → H.vertexSet = G.vertexSet
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma IsSpanningSubgraph.map (f : α → α') (hsle : G ≤s H) : G.map f ≤s H.map f where
  le := hsle.le.map f
  vertexSet_eq := by simp [hsle.vertexSet_eq]

@[gcongr only]
/-
**Graph.map_eq_of_eqOn** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：map_eq_of_eqOn (h : EqOn f g V(G)) : G.map f = G.map g
参数：h : EqOn f g V(G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.ext`：∀ {α : Type u_1} {β : Type u_2} {G₁ G₂ : Graph α β},   G₁.ver
texSet = G₂.vertexSet → (∀ (e : β) (x y : α), G₁.IsLink e x y ↔ G₂.IsLink e x y…
-/
lemma map_eq_of_eqOn (h : EqOn f g V(G)) : G.map f = G.map g := by
  refine Graph.ext (by grind) fun _ _ _ ↦ ⟨fun ⟨_, _, hvw, _, _⟩ ↦ ?_, fun ⟨_, _, hvw, _, _⟩ ↦ ?_⟩
  <;> grind [h hvw.left_mem, h hvw.right_mem, hvw.map]

end Map

end Graph

