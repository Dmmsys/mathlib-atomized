/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rémi Bottinelli, Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Mapping walks between graphs

Functions that map walks between different graphs.

## Main definitions

* `SimpleGraph.Walk.map`: The map on walks induced by a graph homomorphism
* `SimpleGraph.Walk.mapLe`: Map a walk to a supergraph
* `SimpleGraph.Walk.transfer`: Map a walk to another graph that contains its edges
* `SimpleGraph.Walk.induce`:
  Map a walk that's fully contained in a set of vertices to the subgraph induced by that set
* `SimpleGraph.Walk.toDeleteEdges`:
  Map a walk that avoids a set of edges to the subgraph with those edges deleted
* `SimpleGraph.Walk.toDeleteEdge`:
  Map a walk that avoids an edge to the subgraph with that edge deleted

## Tags
walks
-/

@[expose] public section

namespace SimpleGraph

namespace Walk

universe u v w
variable {V : Type u} {V' : Type v} {V'' : Type w}
variable {G : SimpleGraph V} {G' : SimpleGraph V'} {G'' : SimpleGraph V''}

/-! ### Mapping walks -/

/-- Given a graph homomorphism, map walks to walks. -/
/-
**SimpleGraph.Walk.map** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} →   {V' : Type v} →     {G : SimpleGraph V} → {G' : SimpleGra
ph V'} → (f : G →g G') → {u v : V} → G.Walk u v → G'.Walk (f u) (f v)
参数：f : G →g G'；f u；f v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a graph homomorphism, map walks to walks.
-/
protected def map (f : G →g G') {u v : V} : G.Walk u v → G'.Walk (f u) (f v)
  | nil => nil
  | cons h p => cons (f.map_adj h) (p.map f)

variable (f : G →g G') (f' : G' →g G'') {u v u' v' w : V} (p : G.Walk u v)

@[simp]
/-
**SimpleGraph.Walk.map_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：map_nil : (nil : G.Walk u u).map f = nil
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_nil : (nil : G.Walk u u).map f = nil := rfl

@[simp]
/-
**SimpleGraph.Walk.map_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：map_cons {w : V} (h : G.Adj w u) : (cons h p).map f = cons (f.map_adj h) (
p.map f)
参数：h : G.Adj w u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_cons {w : V} (h : G.Adj w u) : (cons h p).map f = cons (f.map_adj h) (p.map f) := rfl

@[simp]
/-
**SimpleGraph.Walk.map_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：map_copy (hu : u = u') (hv : v = v') : (p.copy hu hv).map f = (p.map f).co
py (hu ▸ rfl) (hv ▸ rfl)
参数：hu : u = u'；hv : v = v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_copy (hu : u = u') (hv : v = v') :
    (p.copy hu hv).map f = (p.map f).copy (hu ▸ rfl) (hv ▸ rfl) := by
  subst_vars
  rfl

@[simp]
/-
**SimpleGraph.Walk.map_id** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：map_id (p : G.Walk u v) : p.map Hom.id = p
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
-/
theorem map_id (p : G.Walk u v) : p.map Hom.id = p := by
  induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.map_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：map_map : (p.map f).map f' = p.map (f'.comp f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
-/
theorem map_map : (p.map f).map f' = p.map (f'.comp f) := by
  induction p <;> simp [*]

/-- Unlike categories, for graphs vertex equality is an important notion, so needing to be able to
work with equality of graph homomorphisms is a necessary evil. -/
/-
**SimpleGraph.Walk.map_eq_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：map_eq_of_eq {f : G ->g G'} (f' : G ->g G') (h : f = f') : p.map f = (p.ma
p f').copy (h ▸ rfl) (h ▸ rfl)
参数：f' : G ->g G'；h : f = f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Unlike categories, for graphs vertex equality is an important notion, so needing
 to be able to
work with equality of graph homomorphisms is a necessary evil.
-/
theorem map_eq_of_eq {f : G →g G'} (f' : G →g G') (h : f = f') :
    p.map f = (p.map f').copy (h ▸ rfl) (h ▸ rfl) := by
  subst_vars
  rfl

variable {p} in
@[simp]
/-
**SimpleGraph.Walk.nil_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：nil_map_iff : (p.map f).Nil ↔ p.Nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
-/
theorem nil_map_iff : (p.map f).Nil ↔ p.Nil := by
  cases p <;> simp

@[deprecated nil_map_iff (since := "2026-05-12")]
/-
**SimpleGraph.Walk.map_eq_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：map_eq_nil_iff {p : G.Walk u u} : p.map f = nil ↔ p = nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
-/
theorem map_eq_nil_iff {p : G.Walk u u} : p.map f = nil ↔ p = nil := by cases p <;> simp

@[simp]
/-
**SimpleGraph.Walk.length_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_map : (p.map f).length = p.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem length_map : (p.map f).length = p.length := by induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.map_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：map_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) : (p.append q).ma
p f = (p.map f).append (q.map f)
参数：p : G.Walk u v；q : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
-/
theorem map_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).map f = (p.map f).append (q.map f) := by induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.reverse_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：reverse_map : (p.map f).reverse = p.reverse.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.reverse_cons`：reverse_cons {u v w : V} (h : G.Adj u v) 
(p : G.Walk v w) : (cons h p).reverse = p.reverse.append (cons h.symm nil)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.map_append`：map_append {u v w : V} (p : G.Walk u v) (q 
: G.Walk v w) : (p.append q).map f = (p.map f).append (q.map f)
-/
theorem reverse_map : (p.map f).reverse = p.reverse.map f := by induction p <;> simp [map_append, *]

@[simp]
/-
**SimpleGraph.Walk.support_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_map : (p.map f).support = p.support.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem support_map : (p.map f).support = p.support.map f := by induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.darts_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_map : (p.map f).darts = p.darts.map f.mapDart
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `SimpleGraph.Dart.adj`：∀ {V : Type u_1} {G : SimpleGraph V} (self : G.Dar
t), G.Adj self.toProd.1 self.toProd.2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
theorem darts_map : (p.map f).darts = p.darts.map f.mapDart := by induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.edges_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_map : (p.map f).edges = p.edges.map (Sym2.map f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
theorem edges_map : (p.map f).edges = p.edges.map (Sym2.map f) := by
  induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.edgeSet_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edgeSet_map : (p.map f).edgeSet = Sym2.map f '' p.edgeSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.edges_map`：edges_map : (p.map f).edges = p.edges.map (S
ym2.map f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_map : (p.map f).edgeSet = Sym2.map f '' p.edgeSet := by ext; simp

@[simp]
/-
**SimpleGraph.Walk.getVert_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：getVert_map (n : Nat) : (p.map f).getVert n = f (p.getVert n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem getVert_map (n : ℕ) : (p.map f).getVert n = f (p.getVert n) := by
  induction p generalizing n <;> cases n <;> simp [*]
/-
**SimpleGraph.Walk.map_injective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：map_injective_of_injective {f : G ->g G'} (hinj : Function.Injective f) (u
 v : V) : Function.Injective (Walk.map f : G.Walk u v -> G'.Walk (f u) (f v))
参数：hinj : Function.Injective f；u v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.cons.injEq`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V} (h : G.Adj u v) (p : G.Walk v w) (v_1 : V) (h_1 : G.Adj u v_1)   (p_1 : G.Wa
lk v_1 w), (Simpl…
-/
theorem map_injective_of_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Walk.map f : G.Walk u v → G'.Walk (f u) (f v)) := by
  intro p p' h
  induction p with
  | nil => cases p' <;> simp at h ⊢
  | cons _ _ ih =>
    cases p' with
    | nil => simp at h
    | cons _ _ =>
      simp only [map_cons, cons.injEq] at h
      grind

section mapLe

variable {G' : SimpleGraph V} (h : G ≤ G') {u v : V} (p : G.Walk u v)

/-- The specialization of `SimpleGraph.Walk.map` for mapping walks to supergraphs. -/
/-
**SimpleGraph.Walk.mapLe** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：mapLe : G'.Walk u v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The specialization of `SimpleGraph.Walk.map` for mapping walks to supergraphs.
-/
abbrev mapLe : G'.Walk u v :=
  p.map (.ofLE h)
/-
**SimpleGraph.Walk.length_mapLe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_mapLe : (p.mapLe h).length = p.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_map`：length_map : (p.map f).length = p.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_mapLe : (p.mapLe h).length = p.length := by
  simp
/-
**SimpleGraph.Walk.support_mapLe_eq_support** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：support_mapLe_eq_support : (p.mapLe h).support = p.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_map`：support_map : (p.map f).support = p.suppor
t.map f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma support_mapLe_eq_support : (p.mapLe h).support = p.support := by
  simp
/-
**SimpleGraph.Walk.edges_mapLe_eq_edges** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：edges_mapLe_eq_edges : (p.mapLe h).edges = p.edges
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.edges_map`：edges_map : (p.map f).edges = p.edges.map (S
ym2.map f)
· 使用定理 `Sym2.map_id`：map_id : map (@id α) = id
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edges_mapLe_eq_edges : (p.mapLe h).edges = p.edges := by
  simp
/-
**SimpleGraph.Walk.edgeSet_mapLe_eq_edgeSet** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：edgeSet_mapLe_eq_edgeSet : (p.mapLe h).edgeSet = p.edgeSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.edgeSet_map`：edgeSet_map : (p.map f).edgeSet = Sym2.map
 f '' p.edgeSet
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Sym2.map_congr`：map_congr {f g : α -> β} {s : Sym2 α} (h : forall x in s
, f x = g x) : map f s = map g s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Sym2.map_id'`：map_id' : (map fun x : α => x) = id
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edgeSet_mapLe_eq_edgeSet : (p.mapLe h).edgeSet = p.edgeSet := by
  simp
/-
**SimpleGraph.Walk.reverse_mapLe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：reverse_mapLe : (p.mapLe h).reverse = p.reverse.mapLe h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.reverse_map`：reverse_map : (p.map f).reverse = p.revers
e.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem reverse_mapLe : (p.mapLe h).reverse = p.reverse.mapLe h := by
  simp
/-
**SimpleGraph.Walk.mapLe_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：mapLe_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) : (p.append q).
mapLe h = (p.mapLe h).append (q.mapLe h)
参数：p : G.Walk u v；q : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.map_append`：map_append {u v w : V} (p : G.Walk u v) (q 
: G.Walk v w) : (p.append q).map f = (p.map f).append (q.map f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapLe_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).mapLe h = (p.mapLe h).append (q.mapLe h) := by
  simp

end mapLe

/-! ### Transferring between graphs -/

/-- The walk `p` transferred to lie in `H`, given that `H` contains its edges. -/
@[simp]
/-
**SimpleGraph.Walk.transfer** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} →   {G : SimpleGraph V} → {u v : V} → (p : G.Walk u v) → (H :
 SimpleGraph V) → (∀ e ∈ p.edges, e ∈ H.edgeSet) → H.Walk u v
参数：p : G.Walk u v；H : SimpleGraph V；∀ e ∈ p.edges, e ∈ H.edgeSet。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The walk `p` transferred to lie in `H`, given that `H` contains its edges.
-/
protected def transfer {u v : V} (p : G.Walk u v)
    (H : SimpleGraph V) (h : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) : H.Walk u v :=
  match p with
  | nil => nil
  | cons' u v w _ p =>
    cons (h s(u, v) (by simp)) (p.transfer H fun e he => h e (by simp [he]))
/-
**SimpleGraph.Walk.transfer_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：transfer_self : p.transfer G p.edges_subset_edgeSet = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.edges_subset_edgeSet`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
-/
theorem transfer_self : p.transfer G p.edges_subset_edgeSet = p := by
  induction p <;> simp [*]

variable {H : SimpleGraph V}
/-
**SimpleGraph.Walk.transfer_eq_map_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：transfer_eq_map_ofLE (hp) (GH : G <= H) : p.transfer H hp = p.map (.ofLE G
H)
参数：hp；GH : G <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
-/
theorem transfer_eq_map_ofLE (hp) (GH : G ≤ H) : p.transfer H hp = p.map (.ofLE GH) := by
  induction p <;> simp [*]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SimpleGraph.Walk.edges_transfer** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_transfer (hp) : (p.transfer H hp).edges = p.edges
参数：hp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem edges_transfer (hp) : (p.transfer H hp).edges = p.edges := by
  induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.edgeSet_transfer** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：edgeSet_transfer (hp) : (p.transfer H hp).edgeSet = p.edgeSet
参数：hp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.edges_transfer`：edges_transfer (hp) : (p.transfer H hp)
.edges = p.edges
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_transfer (hp) : (p.transfer H hp).edgeSet = p.edgeSet := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SimpleGraph.Walk.support_transfer** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：support_transfer (hp) : (p.transfer H hp).support = p.support
参数：hp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem support_transfer (hp) : (p.transfer H hp).support = p.support := by
  induction p <;> simp [*]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SimpleGraph.Walk.length_transfer** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_transfer (hp) : (p.transfer H hp).length = p.length
参数：hp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem length_transfer (hp) : (p.transfer H hp).length = p.length := by
  induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.transfer_transfer** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：transfer_transfer (hp) {K : SimpleGraph V} (hp') : (p.transfer H hp).trans
fer K hp' = p.transfer K (p.edges_transfer hp ▸ hp')
参数：hp；hp'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.edges_transfer`：edges_transfer (hp) : (p.transfer H hp)
.edges = p.edges
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.transfer.eq_1`：∀ {V : Type u} {G : SimpleGraph V} {u : 
V} (H : SimpleGraph V) (h_2 : ∀ e ∈ SimpleGraph.Walk.nil.edges, e ∈ H.edgeSet), 
  SimpleGraph.Walk.n…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
-/
theorem transfer_transfer (hp) {K : SimpleGraph V} (hp') :
    (p.transfer H hp).transfer K hp' = p.transfer K (p.edges_transfer hp ▸ hp') := by
  induction p <;> simp [*]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SimpleGraph.Walk.transfer_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：transfer_append {w : V} (q : G.Walk v w) (hpq) : (p.append q).transfer H h
pq = (p.transfer H fun e he => hpq _ (by simp [he])).append (q.transfer H fun e 
he => hpq _ (by simp [he]))
参数：q : G.Walk v w；hpq。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.transfer.eq_2`：∀ {V : Type u} {G : SimpleGraph V} {u v 
: V} (H : SimpleGraph V) (v_2 : V) (h_2 : G.Adj u v_2) (p_2 : G.Walk v_2 v)   (h
_3 : ∀ e ∈ (SimpleGr…
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
-/
theorem transfer_append {w : V} (q : G.Walk v w) (hpq) :
    (p.append q).transfer H hpq =
      (p.transfer H fun e he => hpq _ (by simp [he])).append
        (q.transfer H fun e he => hpq _ (by simp [he])) := by
  induction p <;> simp [*]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SimpleGraph.Walk.reverse_transfer** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：reverse_transfer (hp) : (p.transfer H hp).reverse = p.reverse.transfer H (
by simp only [edges_reverse, List.mem_reverse]; exact hp)
参数：hp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.transfer.eq_1`：∀ {V : Type u} {G : SimpleGraph V} {u : 
V} (H : SimpleGraph V) (h_2 : ∀ e ∈ SimpleGraph.Walk.nil.edges, e ∈ H.edgeSet), 
  SimpleGraph.Walk.n…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Walk.reverse_cons`：reverse_cons {u v w : V} (h : G.Adj u v) 
(p : G.Walk v w) : (cons h p).reverse = p.reverse.append (cons h.symm nil)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.transfer.congr_simp`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V} (p p_1 : G.Walk u v) (e_p : p = p_1) (H : SimpleGraph V)   (h : ∀ e ∈
 p.edges, e ∈ H.edgeSet), …
· 使用定理 `SimpleGraph.Walk.transfer_append`：transfer_append {w : V} (q : G.Walk v 
w) (hpq) : (p.append q).transfer H hpq = (p.transfer H fun e he => hpq _ (by sim
p [he])).append (q.tra…
-/
theorem reverse_transfer (hp) :
    (p.transfer H hp).reverse =
      p.reverse.transfer H (by simp only [edges_reverse, List.mem_reverse]; exact hp) := by
  induction p <;> simp [*]

/-! ### Inducing a walk -/

variable {s s' : Set V}

variable (s) in
/-- A walk in `G` which is fully contained in a set `s` of vertices lifts to a walk of `G[s]`. -/
/-
**SimpleGraph.Walk.induce** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} →   {G : SimpleGraph V} →     (s : Set V) →       {u v : V} →
 (w : G.Walk u v) → (hw : ∀ x ∈ w.support, x ∈ s) → (SimpleGraph.induce s G).Wal
k ⟨u, ⋯⟩ ⟨v, ⋯⟩
参数：s : Set V；w : G.Walk u v；hw : ∀ x ∈ w.support, x ∈ s；SimpleGraph.induce s G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A walk in `G` which is fully contained in a set `s` of vertices lifts to a walk 
of `G[s]`.
-/
protected def induce {u v : V} :
    ∀ (w : G.Walk u v) (hw : ∀ x ∈ w.support, x ∈ s),
      (G.induce s).Walk ⟨u, hw _ w.start_mem_support⟩ ⟨v, hw _ w.end_mem_support⟩
  | nil, hw => nil
  | cons (v := u') huu' w, hw => .cons (induce_adj.2 huu') <| w.induce <| by simp_all
/-
**SimpleGraph.Walk.induce_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {s : Set V} (hw : ∀ x ∈ SimpleG
raph.Walk.nil.support, x ∈ s),   SimpleGraph.Walk.induce s SimpleGraph.Walk.nil 
hw = SimpleGraph.Walk.nil
参数：hw : ∀ x ∈ SimpleGraph.Walk.nil.support, x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.start_mem_support`：start_mem_support {u v : V} (p : G.W
alk u v) : u in p.support
· 使用定理 `SimpleGraph.Walk.end_mem_support`：end_mem_support {u v : V} (p : G.Walk 
u v) : v in p.support
-/
@[simp] lemma induce_nil (hw) : (.nil : G.Walk u u).induce s hw = .nil := rfl
/-
**SimpleGraph.Walk.induce_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v u' : V} {s : Set V} (huu' : G.Adj 
u u') (w : G.Walk u' v)   (hw : ∀ x ∈ (SimpleGraph.Walk.cons huu' w).support, x 
∈ s),   SimpleGraph.Walk.induce s (SimpleGraph.Walk.cons huu' w) hw = SimpleGrap
h.Walk.cons ⋯ (SimpleGraph.Walk.induce s w ⋯)
参数：huu' : G.Adj u u'；w : G.Walk u' v；hw : ∀ x ∈ (SimpleGraph.Walk.cons huu' w).s
upport, x ∈ s；SimpleGraph.Walk.cons huu' w；SimpleGraph.Walk.induce s w ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.start_mem_support`：start_mem_support {u v : V} (p : G.W
alk u v) : u in p.support
· 使用定理 `SimpleGraph.Walk.end_mem_support`：end_mem_support {u v : V} (p : G.Walk 
u v) : v in p.support
-/
@[simp] lemma induce_cons (huu' : G.Adj u u') (w : G.Walk u' v) (hw) :
    (w.cons huu').induce s hw = .cons (induce_adj.2 huu') (w.induce s <| by simp_all) := rfl
/-
**SimpleGraph.Walk.support_induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {s : Set V} {u v : V} (w : G.Walk u v) 
(hw : ∀ x ∈ w.support, x ∈ s),   (SimpleGraph.Walk.induce s w hw).support = w.su
pport.attachWith (Membership.mem s) hw
参数：w : G.Walk u v；hw : ∀ x ∈ w.support, x ∈ s；SimpleGraph.Walk.induce s w hw；Mem
bership.mem s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.start_mem_support`：start_mem_support {u v : V} (p : G.W
alk u v) : u in p.support
· 使用定理 `SimpleGraph.Walk.end_mem_support`：end_mem_support {u v : V} (p : G.Walk 
u v) : v in p.support
-/
@[simp] lemma support_induce {u v : V} :
    ∀ (w : G.Walk u v) (hw), (w.induce s hw).support = w.support.attachWith _ hw
  | .nil, hw => rfl
  | .cons (v := u') hu w, hw => by simp [support_induce]
/-
**SimpleGraph.Walk.map_induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {s : Set V} {u v : V} (w : G.Walk u v) 
(hw : ∀ x ∈ w.support, x ∈ s),   SimpleGraph.Walk.map (SimpleGraph.Embedding.ind
uce s).toHom (SimpleGraph.Walk.induce s w hw) = w
参数：w : G.Walk u v；hw : ∀ x ∈ w.support, x ∈ s；SimpleGraph.Embedding.induce s；Sim
pleGraph.Walk.induce s w hw。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.start_mem_support`：start_mem_support {u v : V} (p : G.W
alk u v) : u in p.support
· 使用定理 `SimpleGraph.Walk.end_mem_support`：end_mem_support {u v : V} (p : G.Walk 
u v) : v in p.support
-/
@[simp] lemma map_induce {u v : V} :
    ∀ (w : G.Walk u v) (hw), (w.induce s hw).map (Embedding.induce _).toHom = w
  | .nil, hw => rfl
  | .cons (v := u') huu' w, hw => by simp [map_induce]

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.Walk.map_induce_induceHomOfLE** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：map_induce_induceHomOfLE (hs : s subseteq s') {u v : V} : forall (w : G.Wa
lk u v) (hw), (w.induce s hw).map (G.induceHomOfLE hs).toHom = w.induce s' (subs
et_trans hw hs) | .nil, hw => rfl | .cons (v
参数：hs : s subseteq s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.start_mem_support`：start_mem_support {u v : V} (p : G.W
alk u v) : u in p.support
· 使用定理 `SimpleGraph.Walk.end_mem_support`：end_mem_support {u v : V} (p : G.Walk 
u v) : v in p.support
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
-/
lemma map_induce_induceHomOfLE (hs : s ⊆ s') {u v : V} : ∀ (w : G.Walk u v) (hw),
    (w.induce s hw).map (G.induceHomOfLE hs).toHom = w.induce s' (subset_trans hw hs)
  | .nil, hw => rfl
  | .cons (v := u') huu' w, hw => by simp [map_induce_induceHomOfLE]

/-! ## Deleting edges -/

/-- Given a walk that avoids a set of edges, produce a walk in the graph
with those edges deleted. -/
/-
**SimpleGraph.Walk.toDeleteEdges** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：toDeleteEdges (s : Set (Sym2 V)) {v w : V} (p : G.Walk v w) (hp : forall e
, e in p.edges -> e ∉ s) : (G.deleteEdges s).Walk v w
参数：s : Set (Sym2 V)；p : G.Walk v w；hp : forall e, e in p.edges -> e ∉ s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a walk that avoids a set of edges, produce a walk in the graph
with those edges deleted.
-/
abbrev toDeleteEdges (s : Set (Sym2 V)) {v w : V} (p : G.Walk v w)
    (hp : ∀ e, e ∈ p.edges → e ∉ s) : (G.deleteEdges s).Walk v w :=
  p.transfer _ <| by
    simp only [edgeSet_deleteEdges, Set.mem_sdiff]
    exact fun e ep => ⟨edges_subset_edgeSet p ep, hp e ep⟩

@[simp]
/-
**SimpleGraph.Walk.toDeleteEdges_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：toDeleteEdges_nil (s : Set (Sym2 V)) {v : V} (hp) : (Walk.nil : G.Walk v v
).toDeleteEdges s hp = Walk.nil
参数：s : Set (Sym2 V)；hp。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDeleteEdges_nil (s : Set (Sym2 V)) {v : V} (hp) :
    (Walk.nil : G.Walk v v).toDeleteEdges s hp = Walk.nil := rfl

@[simp]
/-
**SimpleGraph.Walk.toDeleteEdges_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：toDeleteEdges_cons (s : Set (Sym2 V)) {u v w : V} (h : G.Adj u v) (p : G.W
alk v w) (hp) : (Walk.cons h p).toDeleteEdges s hp = Walk.cons (deleteEdges_adj.
mpr ⟨h, hp _ (List.Mem.head _)⟩) (p.toDeleteEdges s fun _ he => hp _ <| List.Mem
.tail _ he)
参数：s : Set (Sym2 V)；h : G.Adj u v；p : G.Walk v w；hp。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDeleteEdges_cons (s : Set (Sym2 V)) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) (hp) :
    (Walk.cons h p).toDeleteEdges s hp =
      Walk.cons (deleteEdges_adj.mpr ⟨h, hp _ (List.Mem.head _)⟩)
        (p.toDeleteEdges s fun _ he => hp _ <| List.Mem.tail _ he) :=
  rfl

/-- Given a walk that avoids an edge, create a walk in the subgraph with that edge deleted.
This is an abbreviation for `SimpleGraph.Walk.toDeleteEdges`. -/
/-
**SimpleGraph.Walk.toDeleteEdge** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：toDeleteEdge (e : Sym2 V) (p : G.Walk v w) (hp : e ∉ p.edges) : (G.deleteE
dges {e}).Walk v w
参数：e : Sym2 V；p : G.Walk v w；hp : e ∉ p.edges。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a walk that avoids an edge, create a walk in the subgraph with that edge d
eleted.
This is an abbreviation for `SimpleGraph.Walk.toDeleteEdges`.
-/
abbrev toDeleteEdge (e : Sym2 V) (p : G.Walk v w) (hp : e ∉ p.edges) :
    (G.deleteEdges {e}).Walk v w :=
  p.toDeleteEdges {e} (fun _ ↦ by contrapose; simp +contextual [hp])

@[simp]
/-
**SimpleGraph.Walk.map_toDeleteEdges_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：map_toDeleteEdges_eq (s : Set (Sym2 V)) {p : G.Walk v w} (hp) : Walk.map (
.ofLE (G.deleteEdges_le s)) (p.toDeleteEdges s hp) = p
参数：s : Set (Sym2 V)；hp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.deleteEdges_le`：deleteEdges_le (s : Set (Sym2 V)) : G.delete
Edges s <= G
· 使用定理 `SimpleGraph.Walk.edges_subset_edgeSet`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.edges_transfer`：edges_transfer (hp) : (p.transfer H hp)
.edges = p.edges
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.transfer_eq_map_ofLE`：transfer_eq_map_ofLE (hp) (GH : G
 <= H) : p.transfer H hp = p.map (.ofLE GH)
· 使用定理 `SimpleGraph.Walk.transfer_transfer`：transfer_transfer (hp) {K : SimpleGr
aph V} (hp') : (p.transfer H hp).transfer K hp' = p.transfer K (p.edges_transfer
 hp ▸ hp')
· 使用定理 `SimpleGraph.Walk.transfer_self`：transfer_self : p.transfer G p.edges_sub
set_edgeSet = p
-/
theorem map_toDeleteEdges_eq (s : Set (Sym2 V)) {p : G.Walk v w} (hp) :
    Walk.map (.ofLE (G.deleteEdges_le s)) (p.toDeleteEdges s hp) = p := by
  rw [← transfer_eq_map_ofLE, transfer_transfer, transfer_self]
  apply edges_transfer _ _ ▸ p.edges_subset_edgeSet

end Walk

end SimpleGraph

