/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# Local graph operations

This file defines some single-graph operations that modify a finite number of vertices
and proves basic theorems about them. When the graph itself has a finite number of vertices
we also prove theorems about the number of edges in the modified graphs.

## Main definitions

* `G.replaceVertex s t` is `G` with `t` replaced by a copy of `s`,
  removing the `s-t` edge if present.
* `edge s t` is the graph with a single `s-t` edge. Adding this edge to a graph `G` is then
  `G ⊔ edge s t`.
-/

@[expose] public section


open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (s t : V)

section ReplaceVertex

variable [DecidableEq V]

/-- The graph formed by forgetting `t`'s neighbours and instead giving it those of `s`. The `s-t`
edge is removed if present. -/
/-
**SimpleGraph.replaceVertex** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：replaceVertex : SimpleGraph V where Adj v w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph formed by forgetting `t`'s neighbours and instead giving it those of `
s`. The `s-t`
edge is removed if present.
-/
def replaceVertex : SimpleGraph V where
  Adj v w := if v = t then if w = t then False else G.Adj s w
                      else if w = t then G.Adj v s else G.Adj v w
  symm.symm v w := by split_ifs <;> simp [adj_comm]

/-- There is never an `s-t` edge in `G.replaceVertex s t`. -/
/-
**SimpleGraph.not_adj_replaceVertex_same** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：not_adj_replaceVertex_same : ¬(G.replaceVertex s t).Adj s t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.mk.congr_simp`：∀ {V : Type u} (Adj Adj_1 : V → V → Prop) (e_
Adj : Adj = Adj_1) (symm : Std.Symm Adj) (loopless : Std.Irrefl Adj),   { Adj :=
 Adj, symm := s…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
There is never an `s-t` edge in `G.replaceVertex s t`.
-/
lemma not_adj_replaceVertex_same : ¬(G.replaceVertex s t).Adj s t := by simp [replaceVertex]
/-
**SimpleGraph.replaceVertex_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) (s : V) [inst : DecidableEq V], G.rep
laceVertex s s = G
参数：G : SimpleGraph V；s : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
-/
@[simp] lemma replaceVertex_self : G.replaceVertex s s = G := by
  ext; unfold replaceVertex; aesop (add simp or_iff_not_imp_left)

variable {t}

/-- Except possibly for `t`, the neighbours of `s` in `G.replaceVertex s t` are its neighbours in
`G`. -/
/-
**SimpleGraph.adj_replaceVertex_iff_of_ne_left** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：adj_replaceVertex_iff_of_ne_left {w : V} (hw : w != t) : (G.replaceVertex 
s t).Adj s w ↔ G.Adj s w
参数：hw : w != t。
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
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `SimpleGraph.mk.congr_simp`：∀ {V : Type u} (Adj Adj_1 : V → V → Prop) (e_
Adj : Adj = Adj_1) (symm : Std.Symm Adj) (loopless : Std.Irrefl Adj),   { Adj :=
 Adj, symm := s…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Except possibly for `t`, the neighbours of `s` in `G.replaceVertex s t` are its 
neighbours in
`G`.
-/
lemma adj_replaceVertex_iff_of_ne_left {w : V} (hw : w ≠ t) :
    (G.replaceVertex s t).Adj s w ↔ G.Adj s w := by simp [replaceVertex, hw]

/-- Except possibly for itself, the neighbours of `t` in `G.replaceVertex s t` are the neighbours of
`s` in `G`. -/
/-
**SimpleGraph.adj_replaceVertex_iff_of_ne_right** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph`。
形式化陈述：adj_replaceVertex_iff_of_ne_right {w : V} (hw : w != t) : (G.replaceVertex
 s t).Adj t w ↔ G.Adj s w
参数：hw : w != t。
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
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `SimpleGraph.mk.congr_simp`：∀ {V : Type u} (Adj Adj_1 : V → V → Prop) (e_
Adj : Adj = Adj_1) (symm : Std.Symm Adj) (loopless : Std.Irrefl Adj),   { Adj :=
 Adj, symm := s…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Except possibly for itself, the neighbours of `t` in `G.replaceVertex s t` are t
he neighbours of
`s` in `G`.
-/
lemma adj_replaceVertex_iff_of_ne_right {w : V} (hw : w ≠ t) :
    (G.replaceVertex s t).Adj t w ↔ G.Adj s w := by simp [replaceVertex, hw]

/-- Adjacency in `G.replaceVertex s t` which does not involve `t` is the same as that of `G`. -/
/-
**SimpleGraph.adj_replaceVertex_iff_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：adj_replaceVertex_iff_of_ne {v w : V} (hv : v != t) (hw : w != t) : (G.rep
laceVertex s t).Adj v w ↔ G.Adj v w
参数：hv : v != t；hw : w != t。
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
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `SimpleGraph.mk.congr_simp`：∀ {V : Type u} (Adj Adj_1 : V → V → Prop) (e_
Adj : Adj = Adj_1) (symm : Std.Symm Adj) (loopless : Std.Irrefl Adj),   { Adj :=
 Adj, symm := s…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Adjacency in `G.replaceVertex s t` which does not involve `t` is the same as tha
t of `G`.
-/
lemma adj_replaceVertex_iff_of_ne {v w : V} (hv : v ≠ t) (hw : w ≠ t) :
    (G.replaceVertex s t).Adj v w ↔ G.Adj v w := by simp [replaceVertex, hv, hw]

variable {s}
/-
**SimpleGraph.edgeSet_replaceVertex_of_not_adj** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：edgeSet_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t)
.edgeSet = G.edgeSet \ G.incidenceSet t union (s(·, t)) '' (G.neighborSet s)
参数：hn : ¬G.Adj s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.inductionOn`：∀ {α : Type u_1} {f : Sym2 α → Prop} (i : Sym2 α), (∀ 
(x y : α), f s(x, y)) → f i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `SimpleGraph.adj_comm`：adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem edgeSet_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t).edgeSet =
    G.edgeSet \ G.incidenceSet t ∪ (s(·, t)) '' (G.neighborSet s) := by
  ext e; refine e.inductionOn ?_
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_sdiff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by grind]
/-
**SimpleGraph.edgeSet_replaceVertex_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：edgeSet_replaceVertex_of_adj (ha : G.Adj s t) : (G.replaceVertex s t).edge
Set = (G.edgeSet \ G.incidenceSet t union (s(·, t)) '' (G.neighborSet s)) \ {s(t
, t)}
参数：ha : G.Adj s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.inductionOn`：∀ {α : Type u_1} {f : Sym2 α → Prop} (i : Sym2 α), (∀ 
(x y : α), f s(x, y)) → f i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `SimpleGraph.adj_comm`：adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem edgeSet_replaceVertex_of_adj (ha : G.Adj s t) : (G.replaceVertex s t).edgeSet =
    (G.edgeSet \ G.incidenceSet t ∪ (s(·, t)) '' (G.neighborSet s)) \ {s(t, t)} := by
  ext e; refine e.inductionOn ?_
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_sdiff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by grind]

variable [Fintype V] [DecidableRel G.Adj]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableRel (G.replaceVertex s t).Adj := inferInstanceAs <| DecidableRel (mk _ _ _).Adj
/-
**SimpleGraph.edgeFinset_replaceVertex_of_not_adj** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s
 t).edgeFinset = G.edgeFinset \ G.incidenceFinset t union (G.neighborFinset s).i
mage (s(·, t))
参数：hn : ¬G.Adj s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_edgeFinset`：coe_edgeFinset : (G.edgeFinset : Set (Sym2 V
)) = G.edgeSet
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `SimpleGraph.coe_incidenceFinset`：coe_incidenceFinset [DecidableEq V] : (
G.incidenceFinset v : Set (Sym2 V)) = G.incidenceSet v
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `SimpleGraph.coe_neighborFinset`：coe_neighborFinset : (G.neighborFinset v
 : Set V) = G.neighborSet v
· 使用定理 `SimpleGraph.edgeSet_replaceVertex_of_not_adj`：edgeSet_replaceVertex_of_n
ot_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t).edgeSet = G.edgeSet \ G.inciden
ceSet t union (s(·, t)) '' (G.neig…
-/
theorem edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t).edgeFinset =
    G.edgeFinset \ G.incidenceFinset t ∪ (G.neighborFinset s).image (s(·, t)) := by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_replaceVertex_of_not_adj hn
/-
**SimpleGraph.edgeFinset_replaceVertex_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) : (G.replaceVertex s t).e
dgeFinset = (G.edgeFinset \ G.incidenceFinset t union (G.neighborFinset s).image
 (s(·, t))) \ {s(t, t)}
参数：ha : G.Adj s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_edgeFinset`：coe_edgeFinset : (G.edgeFinset : Set (Sym2 V
)) = G.edgeSet
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `SimpleGraph.coe_incidenceFinset`：coe_incidenceFinset [DecidableEq V] : (
G.incidenceFinset v : Set (Sym2 V)) = G.incidenceSet v
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `SimpleGraph.coe_neighborFinset`：coe_neighborFinset : (G.neighborFinset v
 : Set V) = G.neighborSet v
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `SimpleGraph.edgeSet_replaceVertex_of_adj`：edgeSet_replaceVertex_of_adj (
ha : G.Adj s t) : (G.replaceVertex s t).edgeSet = (G.edgeSet \ G.incidenceSet t 
union (s(·, t)) '' (G.neighbor…
-/
theorem edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) : (G.replaceVertex s t).edgeFinset =
    (G.edgeFinset \ G.incidenceFinset t ∪ (G.neighborFinset s).image (s(·, t))) \ {s(t, t)} := by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_replaceVertex_of_adj ha
/-
**SimpleGraph.disjoint_sdiff_neighborFinset_image** 是 Mathlib 中的一个引理，位于命名空间 `Sim
pleGraph`。
形式化陈述：disjoint_sdiff_neighborFinset_image : Disjoint (G.edgeFinset \ G.incidence
Finset t) ((G.neighborFinset s).image (s(·, t)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjoint_iff_ne`：disjoint_iff_ne : Disjoint s t ↔ forall a in s, 
forall b in t, a != b
· 使用定理 `SimpleGraph.mem_incidenceFinset`：mem_incidenceFinset [DecidableEq V] (e 
: Sym2 V) : e in G.incidenceFinset v ↔ e in G.incidenceSet v
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma disjoint_sdiff_neighborFinset_image :
    Disjoint (G.edgeFinset \ G.incidenceFinset t) ((G.neighborFinset s).image (s(·, t))) := by
  rw [disjoint_iff_ne]
  intro e he
  have : t ∉ e := by
    rw [mem_sdiff, mem_incidenceFinset] at he
    obtain ⟨_, h⟩ := he
    contrapose h
    simp_all [incidenceSet]
  aesop
/-
**SimpleGraph.card_edgeFinset_replaceVertex_of_not_adj** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph`。
形式化陈述：card_edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : #(G.replaceVe
rtex s t).edgeFinset = #G.edgeFinset + G.degree s - G.degree t
参数：hn : ¬G.Adj s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_edgeFinset`：coe_edgeFinset : (G.edgeFinset : Set (Sym2 V
)) = G.edgeSet
· 使用定理 `SimpleGraph.edgeFinset_replaceVertex_of_not_adj`：edgeFinset_replaceVerte
x_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t).edgeFinset = G.edgeFinset
 \ G.incidenceFinset t union (G.neigh…
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用引理 `SimpleGraph.disjoint_sdiff_neighborFinset_image`：disjoint_sdiff_neighbor
Finset_image : Disjoint (G.edgeFinset \ G.incidenceFinset t) ((G.neighborFinset 
s).image (s(·, t)))
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_comm`：∀ {n m k : ℕ}, k ≤ n → n + m - k = n - k + m
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `SimpleGraph.card_incidenceFinset_eq_degree`：card_incidenceFinset_eq_degr
ee [DecidableEq V] : #(G.incidenceFinset v) = G.degree v
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.card_neighborFinset_eq_degree`：card_neighborFinset_eq_degree
 : #(G.neighborFinset v) = G.degree v
-/
theorem card_edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) :
    #(G.replaceVertex s t).edgeFinset = #G.edgeFinset + G.degree s - G.degree t := by
  have inc : G.incidenceFinset t ⊆ G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_not_adj hn,
    card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image, card_sdiff_of_subset inc,
    ← Nat.sub_add_comm <| card_le_card inc, card_incidenceFinset_eq_degree]
  congr 2
  rw [card_image_of_injective, card_neighborFinset_eq_degree]
  unfold Function.Injective
  aesop
/-
**SimpleGraph.card_edgeFinset_replaceVertex_of_adj** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：card_edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) : #(G.replaceVertex 
s t).edgeFinset = #G.edgeFinset + G.degree s - G.degree t - 1
参数：ha : G.Adj s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_edgeFinset`：coe_edgeFinset : (G.edgeFinset : Set (Sym2 V
)) = G.edgeSet
· 使用定理 `SimpleGraph.edgeFinset_replaceVertex_of_adj`：edgeFinset_replaceVertex_of
_adj (ha : G.Adj s t) : (G.replaceVertex s t).edgeFinset = (G.edgeFinset \ G.inc
idenceFinset t union (G.neighborF…
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用引理 `SimpleGraph.disjoint_sdiff_neighborFinset_image`：disjoint_sdiff_neighbor
Finset_image : Disjoint (G.edgeFinset \ G.incidenceFinset t) ((G.neighborFinset 
s).image (s(·, t)))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_comm`：∀ {n m k : ℕ}, k ≤ n → n + m - k = n - k + m
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `SimpleGraph.card_incidenceFinset_eq_degree`：card_incidenceFinset_eq_degr
ee [DecidableEq V] : #(G.incidenceFinset v) = G.degree v
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.card_neighborFinset_eq_degree`：card_neighborFinset_eq_degree
 : #(G.neighborFinset v) = G.degree v
-/
theorem card_edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) :
    #(G.replaceVertex s t).edgeFinset = #G.edgeFinset + G.degree s - G.degree t - 1 := by
  have inc : G.incidenceFinset t ⊆ G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_adj ha, card_sdiff_of_subset (by simp [ha]),
    card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image, card_sdiff_of_subset inc,
    ← Nat.sub_add_comm <| card_le_card inc, card_incidenceFinset_eq_degree]
  congr 2
  rw [card_image_of_injective, card_neighborFinset_eq_degree]
  unfold Function.Injective
  aesop

end ReplaceVertex

section AddEdge

/-- The graph with a single `s-t` edge. It is empty iff `s = t`. -/
/-
**SimpleGraph.edge** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：edge : SimpleGraph V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph with a single `s-t` edge. It is empty iff `s = t`.
-/
def edge : SimpleGraph V := fromEdgeSet {s(s, t)}

@[grind =]
/-
**SimpleGraph.edge_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edge_adj (v w : V) : (edge s t).Adj v w ↔ (v = s ∧ w = t ∨ v = t ∧ w = s) 
∧ v != w
参数：v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edge.eq_1`：∀ {V : Type u_1} (s t : V), SimpleGraph.edge s t 
= SimpleGraph.fromEdgeSet {s(s, t)}
· 使用定理 `SimpleGraph.fromEdgeSet_adj`：fromEdgeSet_adj : (fromEdgeSet s).Adj v w ↔
 s(v, w) in s ∧ v != w
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Sym2.eq_iff`：eq_iff {x y z w : α} : s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ 
x = w ∧ y = z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma edge_adj (v w : V) : (edge s t).Adj v w ↔ (v = s ∧ w = t ∨ v = t ∧ w = s) ∧ v ≠ w := by
  rw [edge, fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff]
/-
**SimpleGraph.adj_edge** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_edge {v w : V} : (edge s t).Adj v w ↔ s(s, t) = s(v, w) ∧ v != w
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adj_edge {v w : V} : (edge s t).Adj v w ↔ s(s, t) = s(v, w) ∧ v ≠ w := by
  grind
/-
**SimpleGraph.edge_comm** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edge_comm : edge s t = edge t s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edge.eq_1`：∀ {V : Type u_1} (s t : V), SimpleGraph.edge s t 
= SimpleGraph.fromEdgeSet {s(s, t)}
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
-/
lemma edge_comm : edge s t = edge t s := by
  rw [edge, edge, Sym2.eq_swap]
/-
**SimpleGraph.edge_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) (s t : V), SimpleGraph.edge s t ≤ G ↔
 {s(s, t)} \ Sym2.diagSet ⊆ G.edgeSet
参数：G : SimpleGraph V；s t : V；s, t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma edge_le : edge s t ≤ G ↔ {s(s, t)} \ Sym2.diagSet ⊆ G.edgeSet := by simp [edge]

variable [DecidableEq V] in
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableRel (edge s t).Adj := fun _ _ ↦ by
  rw [edge_adj]; infer_instance

@[simp]
/-
**SimpleGraph.edge_self_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edge_self_eq_bot : edge s s = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.edge_adj`：edge_adj (v w : V) : (edge s t).Adj v w ↔ (v = s ∧
 w = t ∨ v = t ∧ w = s) ∧ v != w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma edge_self_eq_bot : edge s s = ⊥ := by
  ext; rw [edge_adj]; simp_all
/-
**SimpleGraph.sup_edge_self** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：sup_edge_self : G ⊔ edge s s = G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.edge_self_eq_bot`：edge_self_eq_bot : edge s s = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sup_edge_self : G ⊔ edge s s = G := by simp
/-
**SimpleGraph.lt_sup_edge** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：lt_sup_edge (hne : s != t) (hn : ¬ G.Adj s t) : G < G ⊔ edge s t
参数：hne : s != t；hn : ¬ G.Adj s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `left_lt_sup`：left_lt_sup : a < a ⊔ b ↔ ¬b <= a
· 使用引理 `SimpleGraph.edge_adj`：edge_adj (v w : V) : (edge s t).Adj v w ↔ (v = s ∧
 w = t ∨ v = t ∧ w = s) ∧ v != w
-/
lemma lt_sup_edge (hne : s ≠ t) (hn : ¬ G.Adj s t) : G < G ⊔ edge s t :=
  left_lt_sup.2 fun h ↦ hn <| h <| (edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
/-
**SimpleGraph.edge_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edge_le_iff {v w : V} : edge v w <= G ↔ v = w ∨ G.Adj v w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SimpleGraph.edge_self_eq_bot`：edge_self_eq_bot : edge s s = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma edge_le_iff {v w : V} : edge v w ≤ G ↔ v = w ∨ G.Adj v w := by
  obtain h | h := eq_or_ne v w
  · simp [h]
  · refine ⟨fun h ↦ .inr <| h (by simp_all [edge_adj]), fun hadj v' w' hvw' ↦ ?_⟩
    grind [adj_symm]

@[simp]
/-
**SimpleGraph.edgeSet_edge** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_edge (v w : V) : (edge v w).edgeSet = {s(v, w)} \ Sym2.diagSet
参数：v w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edgeSet_edge (v w : V) : (edge v w).edgeSet = {s(v, w)} \ Sym2.diagSet := by simp [edge]
/-
**SimpleGraph.edgeSet_edge_subset** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_edge_subset {v w : V} : (edge v w).edgeSet subseteq {s(v, w)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma edgeSet_edge_subset {v w : V} : (edge v w).edgeSet ⊆ {s(v, w)} := by simp [edge]

variable {s t}
/-
**SimpleGraph.edgeSet_edge_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeSet_edge_of_ne (h : s != t) : (edge s t).edgeSet = {s(s, t)}
参数：h : s != t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
-/
lemma edgeSet_edge_of_ne (h : s ≠ t) : (edge s t).edgeSet = {s(s, t)} := by simpa [edge]

@[deprecated (since := "2026-03-18")] alias edge_edgeSet_of_ne := edgeSet_edge_of_ne
/-
**SimpleGraph.sup_edge_of_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：sup_edge_of_adj (h : G.Adj s t) : G ⊔ edge s t = G
参数：h : G.Adj s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sup_edge_of_adj (h : G.Adj s t) : G ⊔ edge s t = G := by
  simp [h]
/-
**SimpleGraph.deleteEdges_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {u v : V} {s : Set (Sym2 V)}, s(u, v) ∈ s → (SimpleGraph.
edge u v).deleteEdges s = ⊥
参数：Sym2 V；u, v；SimpleGraph.edge u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.deleteEdges_fromEdgeSet`：∀ {V : Type u_1} (s t : Set (Sym2 V
)), (SimpleGraph.fromEdgeSet s).deleteEdges t = SimpleGraph.fromEdgeSet (s \ t)
· 使用定理 `SimpleGraph.fromEdgeSet_sdiff`：fromEdgeSet_sdiff (s t : Set (Sym2 V)) : 
fromEdgeSet (s \ t) = fromEdgeSet s \ fromEdgeSet t
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
@[simp] lemma deleteEdges_edge {u v : V} {s : Set (Sym2 V)} (h : s(u, v) ∈ s) :
    (edge u v).deleteEdges s = ⊥ := by simp [edge, Set.sdiff_subset_iff, h]
/-
**SimpleGraph.disjoint_edge** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：disjoint_edge {u v : V} : Disjoint G (edge u v) ↔ ¬G.Adj u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.edge_self_eq_bot`：edge_self_eq_bot : edge s s = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SimpleGraph.edgeSet_edge_of_ne`：edgeSet_edge_of_ne (h : s != t) : (edge 
s t).edgeSet = {s(s, t)}
-/
lemma disjoint_edge {u v : V} : Disjoint G (edge u v) ↔ ¬G.Adj u v := by
  rcases eq_or_ne u v with rfl | h
  · simp [edge_self_eq_bot]
  simp [← disjoint_edgeSet, edgeSet_edge_of_ne h]
/-
**SimpleGraph.sdiff_edge** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：sdiff_edge {u v : V} (h : ¬G.Adj u v) : G \ edge u v = G
参数：h : ¬G.Adj u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma sdiff_edge {u v : V} (h : ¬G.Adj u v) : G \ edge u v = G := by
  simp [disjoint_edge, h]
/-
**SimpleGraph.biSup_fromEdgeSet_singleton_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：biSup_fromEdgeSet_singleton_eq : ⨆ e in G.edgeSet, fromEdgeSet {e} = G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_iSup`：edgeSet_iSup {ι : Sort*} {f : ι -> SimpleGraph
 V} : (⨆ i, f i).edgeSet = ⋃ i, (f i).edgeSet
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `SimpleGraph.edgeSet_subset_compl_diagSet`：edgeSet_subset_compl_diagSet :
 G.edgeSet subseteq Sym2.diagSetᶜ
-/
theorem biSup_fromEdgeSet_singleton_eq : ⨆ e ∈ G.edgeSet, fromEdgeSet {e} = G := by
  simp_rw [← edgeSet_inj, ← iSup_subtype'', edgeSet_iSup, edgeSet_fromEdgeSet, ← Set.iUnion_sdiff,
    Set.iUnion_coe_set, Set.biUnion_of_singleton]
  exact Set.disjoint_left.mpr G.edgeSet_subset_compl_diagSet |>.sdiff_eq_left
/-
**SimpleGraph.sSup_edge_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：sSup_edge_eq : sSup { edge u v | (u : V) (v : V) (_ : G.Adj u v) } = G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.biSup_fromEdgeSet_singleton_eq`：biSup_fromEdgeSet_singleton_
eq : ⨆ e in G.edgeSet, fromEdgeSet {e} = G
-/
theorem sSup_edge_eq : sSup { edge u v | (u : V) (v : V) (_ : G.Adj u v) } = G := by
  refine .trans ?_ G.biSup_fromEdgeSet_singleton_eq
  simp_rw [edge, ← iSup_subtype'', iSup, Set.range, Subtype.exists, Sym2.exists, mem_edgeSet]
/-
**SimpleGraph.Subgraph.spanningCoe_sup_edge_le** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Subgraph`。
形式化陈述：∀ {V : Type u_1} (G : SimpleGraph V) {s t : V} {H : (G ⊔ SimpleGraph.edge 
s t).Subgraph}, ¬H.Adj s t → H.spanningCoe ≤ G
参数：G : SimpleGraph V；G ⊔ SimpleGraph.edge s t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subgraph.spanningCoe_sup_edge_le {H : Subgraph (G ⊔ edge s t)} (h : ¬ H.Adj s t) :
    H.spanningCoe ≤ G := by
  intro v w hvw
  grind [adj_congr_of_sym2]

variable [Fintype V] [DecidableRel G.Adj]

variable [DecidableEq V] in
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Fintype (edge s t).edgeSet := by rw [edge]; infer_instance
/-
**SimpleGraph.edgeFinset_sup_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：edgeFinset_sup_edge [Fintype (edgeSet (G ⊔ edge s t))] (hn : ¬G.Adj s t) (
h : s != t) : (G ⊔ edge s t).edgeFinset = G.edgeFinset.cons s(s, t) (by simp_all
)
参数：edgeSet (G ⊔ edge s t)；hn : ¬G.Adj s t；h : s != t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `SimpleGraph.edgeSet_sup`：edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet un
ion G₂.edgeSet
· 使用引理 `SimpleGraph.edgeSet_edge_of_ne`：edgeSet_edge_of_ne (h : s != t) : (edge 
s t).edgeSet = {s(s, t)}
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.toFinset_insert`：toFinset_insert [DecidableEq α] {a : α} {s : Set α}
 [Fintype (insert a s : Set α)] [Fintype s] : (insert a s).toFinset = insert a s
.toFinset
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edgeFinset_sup_edge [Fintype (edgeSet (G ⊔ edge s t))] (hn : ¬G.Adj s t) (h : s ≠ t) :
    (G ⊔ edge s t).edgeFinset = G.edgeFinset.cons s(s, t) (by simp_all) := by
  classical
  simp [edgeFinset, edgeSet_edge_of_ne h]
/-
**SimpleGraph.card_edgeFinset_sup_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：card_edgeFinset_sup_edge [Fintype (edgeSet (G ⊔ edge s t))] (hn : ¬G.Adj s
 t) (h : s != t) : #(G ⊔ edge s t).edgeFinset = #G.edgeFinset + 1
参数：edgeSet (G ⊔ edge s t)；hn : ¬G.Adj s t；h : s != t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeFinset_sup_edge`：edgeFinset_sup_edge [Fintype (edgeSet (
G ⊔ edge s t))] (hn : ¬G.Adj s t) (h : s != t) : (G ⊔ edge s t).edgeFinset = G.e
dgeFinset.cons s(s, t…
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
-/
theorem card_edgeFinset_sup_edge [Fintype (edgeSet (G ⊔ edge s t))] (hn : ¬G.Adj s t) (h : s ≠ t) :
    #(G ⊔ edge s t).edgeFinset = #G.edgeFinset + 1 := by
  rw [G.edgeFinset_sup_edge hn h, card_cons]

end AddEdge

end SimpleGraph

