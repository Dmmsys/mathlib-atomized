/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
## Main definitions

* `SimpleGraph.Reachable` for the relation of whether there exists
  a walk between a given pair of vertices

* `SimpleGraph.Preconnected` and `SimpleGraph.Connected` are predicates
  on simple graphs for whether every vertex can be reached from every other,
  and in the latter case, whether the vertex type is nonempty.

* `SimpleGraph.ConnectedComponent` is the type of connected components of
  a given graph.

* `SimpleGraph.IsBridge` for whether an edge is a bridge edge

## Main statements

* `SimpleGraph.isBridge_iff_forall_cycle_notMem` characterizes bridges as the edges not
  contained in any cycle.

## Tags
trails, paths, cycles, bridge edges
-/

@[expose] public section

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

/-! ## `Reachable` and `Connected` -/

/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `Relation.ReflTransGen` of `G.Adj`.
See `SimpleGraph.reachable_iff_reflTransGen`. -/
/-
**SimpleGraph.Reachable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：Reachable (u v : V) : Prop
参数：u v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two vertices are *reachable* if there is a walk between them.
This is equivalent to `Relation.ReflTransGen` of `G.Adj`.
See `SimpleGraph.reachable_iff_reflTransGen`.
-/
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)

variable {G}
/-
**SimpleGraph.reachable_iff_nonempty_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：reachable_iff_nonempty_univ {u v : V} : G.Reachable u v ↔ (Set.univ : Set 
(G.Walk u v)).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nonempty_iff_univ_nonempty`：nonempty_iff_univ_nonempty : Nonempty α 
↔ (univ : Set α).Nonempty
-/
theorem reachable_iff_nonempty_univ {u v : V} :
    G.Reachable u v ↔ (Set.univ : Set (G.Walk u v)).Nonempty :=
  Set.nonempty_iff_univ_nonempty
/-
**SimpleGraph.not_reachable_iff_isEmpty_walk** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：not_reachable_iff_isEmpty_walk {u v : V} : ¬G.Reachable u v ↔ IsEmpty (G.W
alk u v)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
-/
lemma not_reachable_iff_isEmpty_walk {u v : V} : ¬G.Reachable u v ↔ IsEmpty (G.Walk u v) :=
  not_nonempty_iff
/-
**SimpleGraph.Reachable.elim** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Reachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {p : Prop} {u v : V}, G.Reachable u v →
 (∀ (a : G.Walk u v), p) → p
参数：∀ (a : G.Walk u v), p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
-/
protected theorem Reachable.elim {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Walk u v → p) : p :=
  Nonempty.elim h hp
/-
**SimpleGraph.Reachable.elim_path** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Reachab
le`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {p : Prop} {u v : V}, G.Reachable u v →
 (∀ (a : G.Path u v), p) → p
参数：∀ (a : G.Path u v), p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.elim`：∀ {V : Type u} {G : SimpleGraph V} {p : Prop
} {u v : V}, G.Reachable u v → (∀ (a : G.Walk u v), p) → p
-/
protected theorem Reachable.elim_path {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Path u v → p) : p := by classical exact h.elim fun q => hp q.toPath
/-
**SimpleGraph.Walk.reachable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Walk u v), G.Reachable
 u v
参数：p : G.Walk u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Walk.reachable {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : G.Reachable u v :=
  ⟨p⟩
/-
**SimpleGraph.Adj.reachable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Adj u v → G.Reachable u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
 (p : G.Walk u v), G.Reachable u v
-/
protected theorem Adj.reachable {u v : V} (h : G.Adj u v) : G.Reachable u v :=
  h.toWalk.reachable
/-
**SimpleGraph.adj_le_reachable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_le_reachable (G : SimpleGraph V) : G.Adj <= G.Reachable
参数：G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
-/
theorem adj_le_reachable (G : SimpleGraph V) : G.Adj ≤ G.Reachable :=
  fun _ _ ↦ Adj.reachable

@[refl]
/-
**SimpleGraph.Reachable.refl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Reachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} (u : V), G.Reachable u u
参数：u : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Reachable.refl (u : V) : G.Reachable u u := ⟨Walk.nil⟩
/-
**SimpleGraph.Reachable.rfl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Reachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V}, G.Reachable u u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.refl`：∀ {V : Type u} {G : SimpleGraph V} (u : V), 
G.Reachable u u
-/
@[simp] protected theorem Reachable.rfl {u : V} : G.Reachable u u := Reachable.refl _

@[symm]
/-
**SimpleGraph.Reachable.symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Reachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Reachable u v → G.Reachabl
e v u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.elim`：∀ {V : Type u} {G : SimpleGraph V} {p : Prop
} {u v : V}, G.Reachable u v → (∀ (a : G.Walk u v), p) → p
-/
protected theorem Reachable.symm {u v : V} (huv : G.Reachable u v) : G.Reachable v u :=
  huv.elim fun p => ⟨p.reverse⟩
/-
**SimpleGraph.reachable_comm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：reachable_comm {u v : V} : G.Reachable u v ↔ G.Reachable v u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
-/
theorem reachable_comm {u v : V} : G.Reachable u v ↔ G.Reachable v u :=
  ⟨Reachable.symm, Reachable.symm⟩

@[trans]
/-
**SimpleGraph.Reachable.trans** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Reachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V}, G.Reachable u v → G.Reacha
ble v w → G.Reachable u w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.elim`：∀ {V : Type u} {G : SimpleGraph V} {p : Prop
} {u v : V}, G.Reachable u v → (∀ (a : G.Walk u v), p) → p
-/
protected theorem Reachable.trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w :=
  huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩
/-
**SimpleGraph.reachable_iff_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：reachable_iff_reflTransGen (u v : V) : G.Reachable u v ↔ Relation.ReflTran
sGen G.Adj u v
参数：u v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.trans`：trans (hab : ReflTransGen r a b) (hbc : Ref
lTransGen r b c) : ReflTransGen r a c
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
· 使用定理 `SimpleGraph.Reachable.refl`：∀ {V : Type u} {G : SimpleGraph V} (u : V), 
G.Reachable u u
· 使用定理 `SimpleGraph.Reachable.trans`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V}, G.Reachable u v → G.Reachable v w → G.Reachable u w
-/
theorem reachable_iff_reflTransGen (u v : V) :
    G.Reachable u v ↔ Relation.ReflTransGen G.Adj u v := by
  constructor
  · rintro ⟨h⟩
    induction h with
    | nil => rfl
    | cons h' _ ih => exact (Relation.ReflTransGen.single h').trans ih
  · intro h
    induction h with
    | refl => rfl
    | tail _ ha hr => exact Reachable.trans hr ⟨Walk.cons ha Walk.nil⟩
/-
**SimpleGraph.reachable_eq_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：reachable_eq_reflTransGen : G.Reachable = Relation.ReflTransGen G.Adj
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.reachable_iff_reflTransGen`：reachable_iff_reflTransGen (u v 
: V) : G.Reachable u v ↔ Relation.ReflTransGen G.Adj u v
-/
theorem reachable_eq_reflTransGen : G.Reachable = Relation.ReflTransGen G.Adj := by
  ext
  exact reachable_iff_reflTransGen ..
/-
**SimpleGraph.reachable_fromEdgeSet_eq_reflTransGen_toRel** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph`。
形式化陈述：reachable_fromEdgeSet_eq_reflTransGen_toRel {s : Set (Sym2 V)} : (fromEdge
Set s).Reachable = Relation.ReflTransGen (Sym2.ToRel s)
参数：Sym2 V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.reachable_eq_reflTransGen`：reachable_eq_reflTransGen : G.Rea
chable = Relation.ReflTransGen G.Adj
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Relation.transGen_reflGen`：∀ {α : Type u_1} {r : α → α → Prop}, Relation
.TransGen (Relation.ReflGen r) = Relation.ReflTransGen r
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
theorem reachable_fromEdgeSet_eq_reflTransGen_toRel {s : Set (Sym2 V)} :
    (fromEdgeSet s).Reachable = Relation.ReflTransGen (Sym2.ToRel s) := by
  rw [reachable_eq_reflTransGen, ← Relation.transGen_reflGen, ← Relation.transGen_reflGen]
  congr 1
  ext
  simpa [Relation.reflGen_iff] using by tauto
/-
**SimpleGraph.reachable_fromEdgeSet_fromRel_eq_reflTransGen** 是 Mathlib 中的一个定理，位
于命名空间 `SimpleGraph`。
形式化陈述：reachable_fromEdgeSet_fromRel_eq_reflTransGen {r : V -> V -> Prop} (sym : 
Std.Symm r) : (fromEdgeSet <| Sym2.fromRel sym).Reachable = Relation.ReflTransGe
n r
参数：sym : Std.Symm r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.reachable_fromEdgeSet_eq_reflTransGen_toRel`：reachable_fromE
dgeSet_eq_reflTransGen_toRel {s : Set (Sym2 V)} : (fromEdgeSet s).Reachable = Re
lation.ReflTransGen (Sym2.ToRel s)
-/
theorem reachable_fromEdgeSet_fromRel_eq_reflTransGen {r : V → V → Prop} (sym : Std.Symm r) :
    (fromEdgeSet <| Sym2.fromRel sym).Reachable = Relation.ReflTransGen r :=
  reachable_fromEdgeSet_eq_reflTransGen_toRel
/-
**SimpleGraph.Reachable.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Reachable`。
形式化陈述：∀ {V : Type u} {V' : Type v} {u v : V} {G : SimpleGraph V} {G' : SimpleGra
ph V'} (f : G →g G'),   G.Reachable u v → G'.Reachable (f u) (f v)
参数：f : G →g G'；f u；f v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.elim`：∀ {V : Type u} {G : SimpleGraph V} {p : Prop
} {u v : V}, G.Reachable u v → (∀ (a : G.Walk u v), p) → p
-/
protected theorem Reachable.map {u v : V} {G : SimpleGraph V} {G' : SimpleGraph V'} (f : G →g G')
    (h : G.Reachable u v) : G'.Reachable (f u) (f v) :=
  h.elim fun p => ⟨p.map f⟩

@[gcongr, mono]
/-
**SimpleGraph.Reachable.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Reachable`。
形式化陈述：∀ {V : Type u} {u v : V} {G G' : SimpleGraph V}, G ≤ G' → G.Reachable u v 
→ G'.Reachable u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
-/
protected lemma Reachable.mono {u v : V} {G G' : SimpleGraph V}
    (h : G ≤ G') (Guv : G.Reachable u v) : G'.Reachable u v := Guv.map (.ofLE h)

@[gcongr, mono]
/-
**SimpleGraph.Reachable.mono'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Reachable`。
形式化陈述：∀ {V : Type u} {G G' : SimpleGraph V}, G ≤ G' → G.Reachable ≤ G'.Reachable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.mono`：∀ {V : Type u} {u v : V} {G G' : SimpleGraph
 V}, G ≤ G' → G.Reachable u v → G'.Reachable u v
-/
theorem Reachable.mono' {G G' : SimpleGraph V} (h : G ≤ G') : G.Reachable ≤ G'.Reachable :=
  fun _ _ ↦ Reachable.mono h
/-
**SimpleGraph.Reachable.exists_isPath** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Rea
chable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Reachable u v → ∃ p, p.IsP
ath
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Path.isPath`：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p
 : G.Path u v), (↑p).IsPath
-/
theorem Reachable.exists_isPath {u v} (hr : G.Reachable u v) : ∃ p : G.Walk u v, p.IsPath := by
  classical
  obtain ⟨W⟩ := hr
  exact ⟨_, Path.isPath W.toPath⟩
/-
**SimpleGraph.Iso.reachable_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'} {φ 
: G ≃g G'} {u v : V},   G'.Reachable (φ u) (φ v) ↔ G.Reachable u v
参数：φ u；φ v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem Iso.reachable_iff {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u v : V} :
    G'.Reachable (φ u) (φ v) ↔ G.Reachable u v :=
  ⟨fun r => φ.left_inv u ▸ φ.left_inv v ▸ r.map φ.symm.toHom, Reachable.map φ.toHom⟩
/-
**SimpleGraph.Iso.symm_apply_reachable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Is
o`。
形式化陈述：∀ {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'} {φ 
: G ≃g G'} {u : V} {v : V'},   G.Reachable (φ.symm v) u ↔ G'.Reachable v (φ u)
参数：φ.symm v；φ u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Iso.reachable_iff`：∀ {V : Type u} {V' : Type v} {G : SimpleG
raph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u v : V},   G'.Reachable (φ u) (φ v
) ↔ G.Reachable u v
· 使用定理 `RelIso.apply_symm_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : β), e (e.symm x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Iso.symm_apply_reachable {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u : V}
    {v : V'} : G.Reachable (φ.symm v) u ↔ G'.Reachable v (φ u) := by
  rw [← Iso.reachable_iff, RelIso.apply_symm_apply]
/-
**SimpleGraph.Reachable.mem_subgraphVerts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Reachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {H : G.Subgraph},   G.Reachab
le u v → (∀ v ∈ H.verts, ∀ (w : V), G.Adj v w → H.Adj v w) → u ∈ H.verts → v ∈ H
.verts
参数：∀ v ∈ H.verts, ∀ (w : V), G.Adj v w → H.Adj v w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected.0.Simp
leGraph.Reachable.mem_subgraphVerts.aux`：∀ {V : Type u} {G : SimpleGraph V} {v :
 V} {H : G.Subgraph},   (∀ v ∈ H.verts, ∀ (w : V), G.Adj v w → H.Adj v w) → ∀ {v
' : V}, v' ∈ H.verts …
-/
lemma Reachable.mem_subgraphVerts {u v} {H : G.Subgraph} (hr : G.Reachable u v)
    (h : ∀ v ∈ H.verts, ∀ w, G.Adj v w → H.Adj v w)
    (hu : u ∈ H.verts) : v ∈ H.verts := by
  let rec aux {v' : V} (hv' : v' ∈ H.verts) (p : G.Walk v' v) : v ∈ H.verts := by
    by_cases hnp : p.Nil
    · exact hnp.eq ▸ hv'
    exact aux (H.edge_vert (h _ hv' _ (Walk.adj_snd hnp)).symm) p.tail
  termination_by p.length
  decreasing_by {
    rw [← Walk.length_tail_add_one hnp]
    lia
  }
  exact aux hu hr.some

variable (G)
/-
**SimpleGraph.reachable_is_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：reachable_is_equivalence : Equivalence G.Reachable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.refl`：∀ {V : Type u} {G : SimpleGraph V} (u : V), 
G.Reachable u u
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
· 使用定理 `SimpleGraph.Reachable.trans`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V}, G.Reachable u v → G.Reachable v w → G.Reachable u w
-/
theorem reachable_is_equivalence : Equivalence G.Reachable :=
  Equivalence.mk (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)

/-- Distinct vertices are not reachable in the empty graph. -/
@[simp]
/-
**SimpleGraph.reachable_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：reachable_bot {u v : V} : (⊥ : SimpleGraph V).Reachable u v ↔ u = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.elim`：∀ {V : Type u} {G : SimpleGraph V} {p : Prop
} {u v : V}, G.Reachable u v → (∀ (a : G.Walk u v), p) → p
· 使用定理 `SimpleGraph.Reachable.rfl`：∀ {V : Type u} {G : SimpleGraph V} {u : V}, G
.Reachable u u

--- 原说明 ---
Distinct vertices are not reachable in the empty graph.
-/
lemma reachable_bot {u v : V} : (⊥ : SimpleGraph V).Reachable u v ↔ u = v :=
  ⟨fun h ↦ h.elim fun p ↦ match p with | .nil => rfl, fun h ↦ h ▸ .rfl⟩
/-
**SimpleGraph.reachable_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} {u v : V}, (SimpleGraph.completeGraph V).Reachable u v
参数：SimpleGraph.completeGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma reachable_top {u v : V} : (completeGraph V).Reachable u v := by
  obtain rfl | huv := eq_or_ne u v
  · simp
  · exact ⟨.cons huv .nil⟩

@[nontriviality]
/-
**SimpleGraph.Reachable.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.R
eachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [Subsingleton V] {u v : V}, G.Reachable
 u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `SimpleGraph.Reachable.refl`：∀ {V : Type u} {G : SimpleGraph V} (u : V), 
G.Reachable u u
-/
lemma Reachable.of_subsingleton {G : SimpleGraph V} [Subsingleton V] {u v : V} :
    G.Reachable u v := by
  rw [Subsingleton.allEq u v]
/-
**SimpleGraph.Reachable.nonempty_neighborSet_left** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Reachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, u ≠ v → G.Reachable u v → (G
.neighborSet u).Nonempty
参数：G.neighborSet u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Reachable.nonempty_neighborSet_left {G : SimpleGraph V} {u v : V} (huv : u ≠ v)
    (hreach : G.Reachable u v) : (G.neighborSet u).Nonempty := by
  obtain ⟨_ | @⟨u, x, v, hadj, w'⟩⟩ := hreach
  · contradiction
  · exact ⟨x, hadj⟩
/-
**SimpleGraph.Reachable.nonempty_neighborSet_right** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Reachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, u ≠ v → G.Reachable u v → (G
.neighborSet v).Nonempty
参数：G.neighborSet v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.nonempty_neighborSet_left`：∀ {V : Type u} {G : Sim
pleGraph V} {u v : V}, u ≠ v → G.Reachable u v → (G.neighborSet u).Nonempty
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
-/
lemma Reachable.nonempty_neighborSet_right {G : SimpleGraph V} {u v : V} (huv : u ≠ v)
    (hreach : G.Reachable u v) : (G.neighborSet v).Nonempty :=
  hreach.symm.nonempty_neighborSet_left huv.symm
/-
**SimpleGraph.Reachable.degree_pos_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.R
eachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} [inst : Fintype ↑(G.neighborS
et u)],   u ≠ v → G.Reachable u v → 0 < G.degree u
参数：G.neighborSet u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.degree_pos_iff_nonempty`：degree_pos_iff_nonempty : 0 < G.deg
ree v ↔ (G.neighborSet v).Nonempty
· 使用定理 `SimpleGraph.Reachable.nonempty_neighborSet_left`：∀ {V : Type u} {G : Sim
pleGraph V} {u v : V}, u ≠ v → G.Reachable u v → (G.neighborSet u).Nonempty
-/
lemma Reachable.degree_pos_left {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet u)]
    (huv : u ≠ v) (hreach : G.Reachable u v) : 0 < G.degree u :=
  degree_pos_iff_nonempty.mpr (hreach.nonempty_neighborSet_left huv)
/-
**SimpleGraph.Reachable.degree_pos_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Reachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} [inst : Fintype ↑(G.neighborS
et v)],   u ≠ v → G.Reachable u v → 0 < G.degree v
参数：G.neighborSet v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.degree_pos_left`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} [inst : Fintype ↑(G.neighborSet u)],   u ≠ v → G.Reachable u v → 0 <
 G.degree u
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
-/
lemma Reachable.degree_pos_right {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet v)]
    (huv : u ≠ v) (hreach : G.Reachable u v) : 0 < G.degree v :=
  hreach.symm.degree_pos_left huv.symm
/-
**SimpleGraph.Reachable.of_isUniversal** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Re
achable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} (v : V), G.IsUniversal u → G.Re
achable u v
参数：v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.rfl`：∀ {V : Type u} {G : SimpleGraph V} {u : V}, G
.Reachable u u
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
-/
lemma Reachable.of_isUniversal {G : SimpleGraph V} {u : V} (v : V) (h : G.IsUniversal u) :
    G.Reachable u v := by
  by_cases! h' : u = v
  · exact h' ▸ Reachable.rfl
  · exact (h h').reachable
/-
**SimpleGraph.not_reachable_of_neighborSet_left_eq_empty** 是 Mathlib 中的一个引理，位于命名
空间 `SimpleGraph`。
形式化陈述：not_reachable_of_neighborSet_left_eq_empty {G : SimpleGraph V} {u v : V} (
huv : u != v) (hu : G.neighborSet u = ∅) : ¬G.Reachable u v
参数：huv : u != v；hu : G.neighborSet u = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.Reachable.nonempty_neighborSet_left`：∀ {V : Type u} {G : Sim
pleGraph V} {u v : V}, u ≠ v → G.Reachable u v → (G.neighborSet u).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
-/
lemma not_reachable_of_neighborSet_left_eq_empty {G : SimpleGraph V} {u v : V} (huv : u ≠ v)
    (hu : G.neighborSet u = ∅) : ¬G.Reachable u v :=
  (Reachable.nonempty_neighborSet_left huv).mt (Set.not_nonempty_iff_eq_empty.mpr hu)
/-
**SimpleGraph.not_reachable_of_neighborSet_right_eq_empty** 是 Mathlib 中的一个引理，位于命
名空间 `SimpleGraph`。
形式化陈述：not_reachable_of_neighborSet_right_eq_empty {G : SimpleGraph V} {u v : V} 
(huv : u != v) (hv : G.neighborSet v = ∅) : ¬G.Reachable u v
参数：huv : u != v；hv : G.neighborSet v = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.not_reachable_of_neighborSet_left_eq_empty`：not_reachable_of
_neighborSet_left_eq_empty {G : SimpleGraph V} {u v : V} (huv : u != v) (hu : G.
neighborSet u = ∅) : ¬G.Reachable u v
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
-/
lemma not_reachable_of_neighborSet_right_eq_empty {G : SimpleGraph V} {u v : V} (huv : u ≠ v)
    (hv : G.neighborSet v = ∅) : ¬G.Reachable u v :=
  fun r ↦ not_reachable_of_neighborSet_left_eq_empty huv.symm hv r.symm
/-
**SimpleGraph.not_reachable_of_left_degree_zero** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph`。
形式化陈述：not_reachable_of_left_degree_zero {G : SimpleGraph V} {u v : V} [Fintype (
G.neighborSet u)] (huv : u != v) (hu : G.degree u = 0) : ¬G.Reachable u v
参数：G.neighborSet u；huv : u != v；hu : G.degree u = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.Reachable.degree_pos_left`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} [inst : Fintype ↑(G.neighborSet u)],   u ≠ v → G.Reachable u v → 0 <
 G.degree u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_reachable_of_left_degree_zero {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet u)]
    (huv : u ≠ v) (hu : G.degree u = 0) : ¬G.Reachable u v :=
  (Reachable.degree_pos_left huv).mt (by simp [hu])
/-
**SimpleGraph.not_reachable_of_right_degree_zero** 是 Mathlib 中的一个引理，位于命名空间 `Simp
leGraph`。
形式化陈述：not_reachable_of_right_degree_zero {G : SimpleGraph V} {u v : V} [Fintype 
(G.neighborSet v)] (huv : u != v) (hu : G.degree v = 0) : ¬G.Reachable u v
参数：G.neighborSet v；huv : u != v；hu : G.degree v = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.reachable_comm`：reachable_comm {u v : V} : G.Reachable u v ↔
 G.Reachable v u
· 使用引理 `SimpleGraph.not_reachable_of_left_degree_zero`：not_reachable_of_left_deg
ree_zero {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet u)] (huv : u != v
) (hu : G.degree u = 0) : ¬G.Reacha…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma not_reachable_of_right_degree_zero {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet v)]
    (huv : u ≠ v) (hu : G.degree v = 0) : ¬G.Reachable u v := by
  rw [reachable_comm]
  exact not_reachable_of_left_degree_zero huv.symm hu

/-- The equivalence relation on vertices given by `SimpleGraph.Reachable`. -/
@[instance_reducible]
/-
**SimpleGraph.reachableSetoid** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：reachableSetoid : Setoid V
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.reachable_is_equivalence`：reachable_is_equivalence : Equival
ence G.Reachable

--- 原说明 ---
The equivalence relation on vertices given by `SimpleGraph.Reachable`.
-/
def reachableSetoid : Setoid V := Setoid.mk _ G.reachable_is_equivalence

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
/-
**SimpleGraph.Preconnected** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：Preconnected : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph is preconnected if every pair of vertices is reachable from one another.
-/
def Preconnected : Prop := ∀ u v : V, G.Reachable u v
/-
**SimpleGraph.Preconnected.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Preconnect
ed`。
形式化陈述：∀ {V : Type u} {V' : Type v} {G : SimpleGraph V} {H : SimpleGraph V'} (f :
 G →g H),   Function.Surjective ⇑f → G.Preconnected → H.Preconnected
参数：f : G →g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall₂`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}
,   Function.Surjective f → ∀ {p : β → β → Prop}, (∀ (y₁ y₂ : β), p y₁ y₂) ↔ ∀ (
x₁ x₂ : α), p (f …
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem Preconnected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Preconnected) : H.Preconnected :=
  hf.forall₂.2 fun _ _ => Nonempty.map (Walk.map _) <| hG _ _

@[gcongr, mono]
/-
**SimpleGraph.Preconnected.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Preconnec
ted`。
形式化陈述：∀ {V : Type u} {G G' : SimpleGraph V}, G ≤ G' → G.Preconnected → G'.Precon
nected
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.mono`：∀ {V : Type u} {u v : V} {G G' : SimpleGraph
 V}, G ≤ G' → G.Reachable u v → G'.Reachable u v
-/
protected lemma Preconnected.mono {G G' : SimpleGraph V} (h : G ≤ G') (hG : G.Preconnected) :
    G'.Preconnected := fun u v => (hG u v).mono h
/-
**SimpleGraph.preconnected_iff_reachable_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph`。
形式化陈述：preconnected_iff_reachable_eq_top : G.Preconnected ↔ G.Reachable = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma preconnected_iff_reachable_eq_top : G.Preconnected ↔ G.Reachable = ⊤ := by
  aesop (add simp Preconnected)
/-
**SimpleGraph.preconnected_bot_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph`。
形式化陈述：preconnected_bot_iff_subsingleton : (⊥ : SimpleGraph V).Preconnected ↔ Sub
singleton V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma preconnected_bot_iff_subsingleton : (⊥ : SimpleGraph V).Preconnected ↔ Subsingleton V := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [Preconnected]⟩
  contrapose! h
  simp [nontrivial_iff.mp h, Preconnected, reachable_bot]
/-
**SimpleGraph.preconnected_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：preconnected_bot [Subsingleton V] : (⊥ : SimpleGraph V).Preconnected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.preconnected_bot_iff_subsingleton`：preconnected_bot_iff_subs
ingleton : (⊥ : SimpleGraph V).Preconnected ↔ Subsingleton V
-/
lemma preconnected_bot [Subsingleton V] : (⊥ : SimpleGraph V).Preconnected :=
  preconnected_bot_iff_subsingleton.mpr ‹_›
/-
**SimpleGraph.not_preconnected_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：not_preconnected_bot [Nontrivial V] : ¬(⊥ : SimpleGraph V).Preconnected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.preconnected_bot_iff_subsingleton`：preconnected_bot_iff_subs
ingleton : (⊥ : SimpleGraph V).Preconnected ↔ Subsingleton V
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
-/
lemma not_preconnected_bot [Nontrivial V] : ¬(⊥ : SimpleGraph V).Preconnected :=
  preconnected_bot_iff_subsingleton.not.mpr <| not_subsingleton_iff_nontrivial.mpr ‹_›
/-
**SimpleGraph.preconnected_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u}, ⊤.Preconnected
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Reachable.refl`：∀ {V : Type u} {G : SimpleGraph V} (u : V), 
G.Reachable u u
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
-/
@[simp] lemma preconnected_top : (⊤ : SimpleGraph V).Preconnected := fun x y => by
  if h : x = y then rw [h] else exact Adj.reachable h

@[nontriviality]
/-
**SimpleGraph.Preconnected.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Preconnected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [Subsingleton V], G.Preconnected
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.of_subsingleton`：∀ {V : Type u} {G : SimpleGraph V
} [Subsingleton V] {u v : V}, G.Reachable u v
-/
lemma Preconnected.of_subsingleton {G : SimpleGraph V} [Subsingleton V] : G.Preconnected :=
  fun _ _ ↦ .of_subsingleton
/-
**SimpleGraph.Iso.preconnected_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u} {V' : Type v} {G : SimpleGraph V} {H : SimpleGraph V'} (e :
 G ≃g H), G.Preconnected ↔ H.Preconnected
参数：e : G ≃g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Preconnected.map`：∀ {V : Type u} {V' : Type v} {G : SimpleGr
aph V} {H : SimpleGraph V'} (f : G →g H),   Function.Surjective ⇑f → G.Preconnec
ted → H.Preconnect…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem Iso.preconnected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Preconnected ↔ H.Preconnected :=
  ⟨Preconnected.map e.toHom e.toEquiv.surjective,
    Preconnected.map e.symm.toHom e.symm.toEquiv.surjective⟩

@[simp]
/-
**SimpleGraph.Preconnected.support_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Preconnected`。
形式化陈述：∀ {V : Type u} [Nontrivial V] {G : SimpleGraph V}, G.Preconnected → G.supp
ort = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Preconnected.support_eq_univ [Nontrivial V] {G : SimpleGraph V}
    (h : G.Preconnected) : G.support = Set.univ := by
  simp only [Set.eq_univ_iff_forall]
  intro v
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨p⟩ := h v w
  cases p with
  | nil => contradiction
  | @cons _ w => exact ⟨w, ‹_›⟩

@[simp]
/-
**SimpleGraph.Preconnected.not_isIsolated** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Preconnected`。
形式化陈述：∀ {V : Type u} [Nontrivial V] {G : SimpleGraph V}, G.Preconnected → ∀ (v :
 V), ¬G.IsIsolated v
参数：v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Preconnected.support_eq_univ`：∀ {V : Type u} [Nontrivial V] 
{G : SimpleGraph V}, G.Preconnected → G.support = Set.univ
-/
lemma Preconnected.not_isIsolated [Nontrivial V] {G : SimpleGraph V} (hG : G.Preconnected) (v : V) :
    ¬ G.IsIsolated v := by simp [← mem_support_iff_not_isIsolated, hG]
/-
**SimpleGraph.Preconnected.degree_pos_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Preconnected`。
形式化陈述：∀ {V : Type u} [Nontrivial V] {G : SimpleGraph V},   G.Preconnected → ∀ (v
 : V) [inst : Fintype ↑(G.neighborSet v)], 0 < G.degree v
参数：v : V；G.neighborSet v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Preconnected.support_eq_univ`：∀ {V : Type u} [Nontrivial V] 
{G : SimpleGraph V}, G.Preconnected → G.support = Set.univ
-/
lemma Preconnected.degree_pos_of_nontrivial [Nontrivial V] {G : SimpleGraph V} (h : G.Preconnected)
    (v : V) [Fintype (G.neighborSet v)] : 0 < G.degree v := by
  simp [degree_pos_iff_mem_support, h.support_eq_univ]
/-
**SimpleGraph.Preconnected.minDegree_pos_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.Preconnected`。
形式化陈述：∀ {V : Type u} [Nontrivial V] [inst : Fintype V] {G : SimpleGraph V} [inst
_1 : DecidableRel G.Adj],   G.Preconnected → 0 < G.minDegree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.exists_minimal_degree_vertex`：exists_minimal_degree_vertex [
DecidableRel G.Adj] [Nonempty V] : exists v, G.minDegree = G.degree v
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Preconnected.degree_pos_of_nontrivial`：∀ {V : Type u} [Nontr
ivial V] {G : SimpleGraph V},   G.Preconnected → ∀ (v : V) [inst : Fintype ↑(G.n
eighborSet v)], 0 < G.degree v
-/
lemma Preconnected.minDegree_pos_of_nontrivial [Nontrivial V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (h : G.Preconnected) : 0 < G.minDegree := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  exact h.degree_pos_of_nontrivial v
/-
**SimpleGraph.adj_of_mem_walk_support** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：adj_of_mem_walk_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp
 : ¬p.Nil) {x : V} (hx : x in p.support) : exists y in p.support, G.Adj x y
参数：p : G.Walk u v；hp : ¬p.Nil；hx : x in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adj_of_mem_walk_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) {x : V}
    (hx : x ∈ p.support) : ∃ y ∈ p.support, G.Adj x y := by
  induction p with grind [Walk.nil_iff_support_eq, Walk.cons_tail_support, adj_comm]
/-
**SimpleGraph.mem_support_of_mem_walk_support** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph`。
形式化陈述：mem_support_of_mem_walk_support {G : SimpleGraph V} {u v : V} (p : G.Walk 
u v) (hp : ¬p.Nil) {w : V} (hw : w in p.support) : w in G.support
参数：p : G.Walk u v；hp : ¬p.Nil；hw : w in p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.adj_of_mem_walk_support`：adj_of_mem_walk_support {G : Simple
Graph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) {x : V} (hx : x in p.support) 
: exists y in p.support, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.mem_support`：mem_support {v : V} : v in G.support ↔ exists w
, G.Adj v w
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mem_support_of_mem_walk_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil)
    {w : V} (hw : w ∈ p.support) : w ∈ G.support := by
  obtain ⟨y, hy⟩ := adj_of_mem_walk_support p hp hw
  exact (mem_support G).mpr ⟨y, hy.right⟩
/-
**SimpleGraph.mem_support_of_reachable** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_support_of_reachable {G : SimpleGraph V} {u v : V} (huv : u != v) (h :
 G.Reachable u v) : u in G.support
参数：huv : u != v；h : G.Reachable u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.not_nil_of_ne`：not_nil_of_ne {p : G.Walk v w} : v != w 
-> ¬ p.Nil
· 使用引理 `SimpleGraph.mem_support_of_mem_walk_support`：mem_support_of_mem_walk_sup
port {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) {w : V} (hw : 
w in p.support) : w in G.support
· 使用定理 `SimpleGraph.Walk.start_mem_support`：start_mem_support {u v : V} (p : G.W
alk u v) : u in p.support
-/
lemma mem_support_of_reachable {G : SimpleGraph V} {u v : V} (huv : u ≠ v) (h : G.Reachable u v) :
    u ∈ G.support := by
  let p : G.Walk u v := Classical.choice h
  have hp : ¬p.Nil := Walk.not_nil_of_ne huv
  exact mem_support_of_mem_walk_support p hp p.start_mem_support
/-
**SimpleGraph.Preconnected.exists_isPath** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Preconnected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V}, G.Preconnected → ∀ (u v : V), ∃ p, p.I
sPath
参数：u v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.exists_isPath`：∀ {V : Type u} {G : SimpleGraph V} 
{u v : V}, G.Reachable u v → ∃ p, p.IsPath
-/
theorem Preconnected.exists_isPath {G : SimpleGraph V} (h : G.Preconnected) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath :=
  (h u v).exists_isPath

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
/-
**SimpleGraph.Connected** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u} → SimpleGraph V → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff 
it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnec
ted u v`.
-/
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V]
/-
**SimpleGraph.connected_iff_exists_forall_reachable** 是 Mathlib 中的一个引理，位于命名空间 `S
impleGraph`。
形式化陈述：connected_iff_exists_forall_reachable : G.Connected ↔ exists v, forall w, 
G.Reachable v w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.connected_iff`：∀ {V : Type u} (G : SimpleGraph V), G.Connect
ed ↔ G.Preconnected ∧ Nonempty V
· 使用定理 `SimpleGraph.Reachable.trans`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V}, G.Reachable u v → G.Reachable v w → G.Reachable u w
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
-/
lemma connected_iff_exists_forall_reachable : G.Connected ↔ ∃ v, ∀ w, G.Reachable v w := by
  rw [connected_iff]
  constructor
  · rintro ⟨hp, ⟨v⟩⟩
    exact ⟨v, fun w => hp v w⟩
  · rintro ⟨v, h⟩
    exact ⟨fun u w => (h u).symm.trans (h w), ⟨v⟩⟩
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun G.Connected fun _ => ∀ u v : V, G.Reachable u v := ⟨fun h => h.preconnected⟩
/-
**SimpleGraph.Connected.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Connected`。
形式化陈述：∀ {V : Type u} {V' : Type v} {G : SimpleGraph V} {H : SimpleGraph V'} (f :
 G →g H),   Function.Surjective ⇑f → G.Connected → H.Connected
参数：f : G →g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Preconnected.map`：∀ {V : Type u} {V' : Type v} {G : SimpleGr
aph V} {H : SimpleGraph V'} (f : G →g H),   Function.Surjective ⇑f → G.Preconnec
ted → H.Preconnect…
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
-/
theorem Connected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Connected) : H.Connected :=
  haveI := hG.nonempty.map f
  ⟨hG.preconnected.map f hf⟩

@[gcongr, mono]
/-
**SimpleGraph.Connected.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Connected`。
形式化陈述：∀ {V : Type u} {G G' : SimpleGraph V}, G ≤ G' → G.Connected → G'.Connected
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Preconnected.mono`：∀ {V : Type u} {G G' : SimpleGraph V}, G 
≤ G' → G.Preconnected → G'.Preconnected
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
-/
protected lemma Connected.mono {G G' : SimpleGraph V} (h : G ≤ G')
    (hG : G.Connected) : G'.Connected where
  preconnected := hG.preconnected.mono h
  nonempty := hG.nonempty
/-
**SimpleGraph.Connected.exists_isPath** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Con
nected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V}, G.Connected → ∀ (u v : V), ∃ p, p.IsPa
th
参数：u v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.exists_isPath`：∀ {V : Type u} {G : SimpleGraph V} 
{u v : V}, G.Reachable u v → ∃ p, p.IsPath
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
-/
theorem Connected.exists_isPath {G : SimpleGraph V} (h : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath :=
  (h u v).exists_isPath
/-
**SimpleGraph.connected_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：connected_bot_iff : (⊥ : SimpleGraph V).Connected ↔ Subsingleton V ∧ Nonem
pty V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma connected_bot_iff : (⊥ : SimpleGraph V).Connected ↔ Subsingleton V ∧ Nonempty V := by
  simp [preconnected_bot_iff_subsingleton, connected_iff]
/-
**SimpleGraph.not_connected_bot** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：not_connected_bot [Nontrivial V] : ¬(⊥ : SimpleGraph V).Connected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_connected_bot [Nontrivial V] : ¬(⊥ : SimpleGraph V).Connected := by
  simp [not_preconnected_bot, connected_iff]
/-
**SimpleGraph.connected_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：connected_top_iff : (completeGraph V).Connected ↔ Nonempty V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma connected_top_iff : (completeGraph V).Connected ↔ Nonempty V := by simp [connected_iff]
/-
**SimpleGraph.connected_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} [Nonempty V], (SimpleGraph.completeGraph V).Connected
参数：SimpleGraph.completeGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.connected_top_iff`：connected_top_iff : (completeGraph V).Con
nected ↔ Nonempty V
-/
@[simp] lemma connected_top [Nonempty V] : (completeGraph V).Connected := by rwa [connected_top_iff]

@[nontriviality]
/-
**SimpleGraph.Connected.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.C
onnected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [Nonempty V] [Subsingleton V], G.Connec
ted
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Preconnected.of_subsingleton`：∀ {V : Type u} {G : SimpleGrap
h V} [Subsingleton V], G.Preconnected
-/
lemma Connected.of_subsingleton {G : SimpleGraph V} [Nonempty V] [Subsingleton V] :
    G.Connected :=
  ⟨.of_subsingleton⟩
/-
**SimpleGraph.Iso.connected_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：∀ {V : Type u} {V' : Type v} {G : SimpleGraph V} {H : SimpleGraph V'} (e :
 G ≃g H), G.Connected ↔ H.Connected
参数：e : G ≃g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.map`：∀ {V : Type u} {V' : Type v} {G : SimpleGraph
 V} {H : SimpleGraph V'} (f : G →g H),   Function.Surjective ⇑f → G.Connected → 
H.Connected
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem Iso.connected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Connected ↔ H.Connected :=
  ⟨Connected.map e.toHom e.toEquiv.surjective, Connected.map e.symm.toHom e.symm.toEquiv.surjective⟩
/-
**SimpleGraph.reachable_or_compl_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：reachable_or_compl_adj (u v : V) : G.Reachable u v ∨ Gᶜ.Adj u v
参数：u v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `SimpleGraph.Reachable.rfl`：∀ {V : Type u} {G : SimpleGraph V} {u : V}, G
.Reachable u u
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
-/
lemma reachable_or_compl_adj (u v : V) : G.Reachable u v ∨ Gᶜ.Adj u v :=
  or_iff_not_imp_left.mpr fun huv ↦ ⟨fun heq ↦ huv <| heq ▸ Reachable.rfl, mt Adj.reachable huv⟩
/-
**SimpleGraph.reachable_or_reachable_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：reachable_or_reachable_compl (u v w : V) : G.Reachable u v ∨ Gᶜ.Reachable 
u w
参数：u v w : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `SimpleGraph.reachable_or_compl_adj`：reachable_or_compl_adj (u v : V) : G
.Reachable u v ∨ Gᶜ.Adj u v
· 使用定理 `SimpleGraph.Reachable.trans`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V}, G.Reachable u v → G.Reachable v w → G.Reachable u w
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
-/
theorem reachable_or_reachable_compl (u v w : V) : G.Reachable u v ∨ Gᶜ.Reachable u w := by
  refine or_iff_not_imp_left.mpr fun huv ↦ ?_
  by_cases huw : G.Reachable u w
  · have huv' := G.reachable_or_compl_adj .. |>.resolve_left huv
    have hvw' := G.reachable_or_compl_adj .. |>.resolve_left fun hvw ↦ huv <| huw.trans hvw.symm
    exact huv'.reachable.trans hvw'.reachable
  exact G.reachable_or_compl_adj .. |>.resolve_left huw |>.reachable
/-
**SimpleGraph.connected_or_preconnected_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：connected_or_preconnected_compl : G.Connected ∨ Gᶜ.Preconnected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `SimpleGraph.connected_iff_exists_forall_reachable`：connected_iff_exists_
forall_reachable : G.Connected ↔ exists v, forall w, G.Reachable v w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `SimpleGraph.reachable_or_reachable_compl`：reachable_or_reachable_compl (
u v w : V) : G.Reachable u v ∨ Gᶜ.Reachable u w
-/
theorem connected_or_preconnected_compl : G.Connected ∨ Gᶜ.Preconnected := by
  rw [or_iff_not_imp_left, G.connected_iff_exists_forall_reachable]
  intro h u v
  push Not at h
  have ⟨w, huw⟩ := h u
  exact reachable_or_reachable_compl .. |>.resolve_left huw
/-
**SimpleGraph.connected_or_connected_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：connected_or_connected_compl [Nonempty V] : G.Connected ∨ Gᶜ.Connected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `SimpleGraph.connected_or_preconnected_compl`：connected_or_preconnected_c
ompl : G.Connected ∨ Gᶜ.Preconnected
-/
theorem connected_or_connected_compl [Nonempty V] : G.Connected ∨ Gᶜ.Connected :=
  G.connected_or_preconnected_compl.elim .inl (.inr ⟨·⟩)

variable {G v} in
/-
**SimpleGraph.Connected.of_isUniversal** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Co
nnected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V}, G.IsUniversal v → G.Connected
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.connected_iff`：∀ {V : Type u} (G : SimpleGraph V), G.Connect
ed ↔ G.Preconnected ∧ Nonempty V
· 使用定理 `SimpleGraph.Reachable.trans`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V}, G.Reachable u v → G.Reachable v w → G.Reachable u w
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
· 使用定理 `SimpleGraph.Reachable.of_isUniversal`：∀ {V : Type u} {G : SimpleGraph V}
 {u : V} (v : V), G.IsUniversal u → G.Reachable u v
-/
lemma Connected.of_isUniversal (h : G.IsUniversal v) : G.Connected := by
  refine connected_iff _ |>.mpr ⟨fun u w ↦ ?_, ⟨v⟩⟩
  exact (Reachable.of_isUniversal u h).symm.trans (Reachable.of_isUniversal w h)

/-- The quotient of `V` by the `SimpleGraph.Reachable` relation gives the connected
components of a graph. -/
/-
**SimpleGraph.ConnectedComponent** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：ConnectedComponent
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient of `V` by the `SimpleGraph.Reachable` relation gives the connected
components of a graph.
-/
def ConnectedComponent := Quot G.Reachable

/-- Gives the connected component containing a particular vertex. -/
/-
**SimpleGraph.connectedComponentMk** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：connectedComponentMk (v : V) : G.ConnectedComponent
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Gives the connected component containing a particular vertex.
-/
def connectedComponentMk (v : V) : G.ConnectedComponent := Quot.mk G.Reachable v

variable {G G' G''}

namespace ConnectedComponent

@[simps]
/-
**SimpleGraph.ConnectedComponent.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGrap
h.ConnectedComponent`。
形式化陈述：inhabited [Inhabited V] : Inhabited G.ConnectedComponent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited [Inhabited V] : Inhabited G.ConnectedComponent :=
  ⟨G.connectedComponentMk default⟩
/-
**SimpleGraph.ConnectedComponent.isEmpty** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.
ConnectedComponent`。
形式化陈述：isEmpty [IsEmpty V] : IsEmpty G.ConnectedComponent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isEmpty [IsEmpty V] : IsEmpty G.ConnectedComponent := Quot.instIsEmpty
/-
**SimpleGraph.ConnectedComponent.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Connect
edComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton V] : Subsingleton G.ConnectedComponent := Quot.Subsingleton
/-
**SimpleGraph.ConnectedComponent.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Connect
edComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique V] : Unique G.ConnectedComponent := Quot.instUnique
/-
**SimpleGraph.ConnectedComponent.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Connect
edComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty V] : Nonempty G.ConnectedComponent := Nonempty.map G.connectedComponentMk ‹_›
/-
**SimpleGraph.ConnectedComponent.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Connect
edComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite V] : Finite G.ConnectedComponent := Quot.finite _

@[elab_as_elim]
/-
**SimpleGraph.ConnectedComponent.ind** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Conn
ectedComponent`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {β : G.ConnectedComponent → Prop},   (∀
 (v : V), β (G.connectedComponentMk v)) → ∀ (c : G.ConnectedComponent), β c
参数：∀ (v : V), β (G.connectedComponentMk v)；c : G.ConnectedComponent。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem ind {β : G.ConnectedComponent → Prop}
    (h : ∀ v : V, β (G.connectedComponentMk v)) (c : G.ConnectedComponent) : β c :=
  Quot.ind h c

@[elab_as_elim]
/-
**SimpleGraph.ConnectedComponent.ind** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Conn
ectedComponent`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {β : G.ConnectedComponent → Prop},   (∀
 (v : V), β (G.connectedComponentMk v)) → ∀ (c : G.ConnectedComponent), β c
参数：∀ (v : V), β (G.connectedComponentMk v)；c : G.ConnectedComponent。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem ind₂ {β : G.ConnectedComponent → G.ConnectedComponent → Prop}
    (h : ∀ v w : V, β (G.connectedComponentMk v) (G.connectedComponentMk w))
    (c d : G.ConnectedComponent) : β c d :=
  Quot.induction_on₂ c d h
/-
**SimpleGraph.ConnectedComponent.sound** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Co
nnectedComponent`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v w : V}, G.Reachable v w → G.connecte
dComponentMk v = G.connectedComponentMk w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem sound {v w : V} :
    G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk w :=
  Quot.sound
/-
**SimpleGraph.ConnectedComponent.exact** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Co
nnectedComponent`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v w : V}, G.connectedComponentMk v = G
.connectedComponentMk w → G.Reachable v w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
-/
protected theorem exact {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w → G.Reachable v w :=
  @Quotient.exact _ G.reachableSetoid _ _

@[simp]
/-
**SimpleGraph.ConnectedComponent.eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Conne
ctedComponent`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v w : V}, G.connectedComponentMk v = G
.connectedComponentMk w ↔ G.Reachable v w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
-/
protected theorem eq {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w :=
  @Quotient.eq' _ G.reachableSetoid _ _
/-
**SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj** 是 Mathlib 中的一个
定理，位于命名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：connectedComponentMk_eq_of_adj {v w : V} (a : G.Adj v w) : G.connectedComp
onentMk v = G.connectedComponentMk w
参数：a : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.sound`：∀ {V : Type u} {G : SimpleGraph V}
 {v w : V}, G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk 
w
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
-/
theorem connectedComponentMk_eq_of_adj {v w : V} (a : G.Adj v w) :
    G.connectedComponentMk v = G.connectedComponentMk w :=
  ConnectedComponent.sound a.reachable

/-- The `ConnectedComponent` specialization of `Quot.lift`. Provides the stronger
assumption that the vertices are connected by a path. -/
/-
**SimpleGraph.ConnectedComponent.lift** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Con
nectedComponent`。
形式化陈述：{V : Type u} →   {G : SimpleGraph V} →     {β : Sort u_1} → (f : V → β) → 
(∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w) → G.ConnectedComponent → β
参数：f : V → β；∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ConnectedComponent` specialization of `Quot.lift`. Provides the stronger
assumption that the vertices are connected by a path.
-/
protected def lift {β : Sort*} (f : V → β)
    (h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w) : G.ConnectedComponent → β :=
  Quot.lift f fun v w (h' : G.Reachable v w) => h'.elim_path fun hp => h v w hp hp.2

@[simp]
/-
**SimpleGraph.ConnectedComponent.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
ConnectedComponent`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {β : Sort u_1} {f : V → β} {h : ∀ (v w 
: V) (p : G.Walk v w), p.IsPath → f v = f w}   {v : V}, SimpleGraph.ConnectedCom
ponent.lift f h (G.connectedComponentMk v) = f v
参数：v w : V；p : G.Walk v w；G.connectedComponentMk v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem lift_mk {β : Sort*} {f : V → β}
    {h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w} {v : V} :
    ConnectedComponent.lift f h (G.connectedComponentMk v) = f v :=
  rfl
/-
**SimpleGraph.ConnectedComponent.** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Connect
edComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «exists» {p : G.ConnectedComponent → Prop} :
    (∃ c : G.ConnectedComponent, p c) ↔ ∃ v, p (G.connectedComponentMk v) :=
  Quot.mk_surjective.exists
/-
**SimpleGraph.ConnectedComponent.** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Connect
edComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «forall» {p : G.ConnectedComponent → Prop} :
    (∀ c : G.ConnectedComponent, p c) ↔ ∀ v, p (G.connectedComponentMk v) :=
  Quot.mk_surjective.forall
/-
**SimpleGraph.ConnectedComponent._root_.SimpleGraph.Preconnected.subsingleton_co
nnectedComponent** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.ConnectedComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.Preconnected.subsingleton_connectedComponent (h : G.Preconnected) :
    Subsingleton G.ConnectedComponent :=
  ⟨ConnectedComponent.ind₂ fun v w => ConnectedComponent.sound (h v w)⟩

/-- This is `Quot.recOn` specialized to connected components.
For convenience, it strengthens the assumptions in the hypothesis
to provide a path between the vertices. -/
@[elab_as_elim]
/-
**SimpleGraph.ConnectedComponent.recOn** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Co
nnectedComponent`。
形式化陈述：recOn {motive : G.ConnectedComponent -> Sort*} (c : G.ConnectedComponent) 
(f : (v : V) -> motive (G.connectedComponentMk v)) (h : forall (u v : V) (p : G.
Walk u v) (_ : p.IsPath), ConnectedComponent.sound p.reachable ▸ f u = f v) : mo
tive c
参数：c : G.ConnectedComponent；f : (v : V) -> motive (G.connectedComponentMk v)；h :
 forall (u v : V) (p : G.Walk u v) (_ : p.IsPath), ConnectedComponent.sound p.re
achable ▸ f u = f v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is `Quot.recOn` specialized to connected components.
For convenience, it strengthens the assumptions in the hypothesis
to provide a path between the vertices.
-/
def recOn
    {motive : G.ConnectedComponent → Sort*}
    (c : G.ConnectedComponent)
    (f : (v : V) → motive (G.connectedComponentMk v))
    (h : ∀ (u v : V) (p : G.Walk u v) (_ : p.IsPath),
      ConnectedComponent.sound p.reachable ▸ f u = f v) :
    motive c :=
  Quot.recOn c f fun u v r => r.elim_path fun p => h u v p p.2

/-- The map on connected components induced by a graph homomorphism. -/
/-
**SimpleGraph.ConnectedComponent.map** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Conn
ectedComponent`。
形式化陈述：map (φ : G ->g G') (C : G.ConnectedComponent) : G'.ConnectedComponent
参数：φ : G ->g G'；C : G.ConnectedComponent。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map on connected components induced by a graph homomorphism.
-/
def map (φ : G →g G') (C : G.ConnectedComponent) : G'.ConnectedComponent :=
  C.lift (fun v => G'.connectedComponentMk (φ v)) fun _ _ p _ =>
    ConnectedComponent.eq.mpr (p.map φ).reachable

@[simp]
/-
**SimpleGraph.ConnectedComponent.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.C
onnectedComponent`。
形式化陈述：map_mk (φ : G ->g G') (v : V) : (G.connectedComponentMk v).map φ = G'.conn
ectedComponentMk (φ v)
参数：φ : G ->g G'；v : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk (φ : G →g G') (v : V) :
    (G.connectedComponentMk v).map φ = G'.connectedComponentMk (φ v) :=
  rfl

@[simp]
/-
**SimpleGraph.ConnectedComponent.map_id** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.C
onnectedComponent`。
形式化陈述：map_id (C : ConnectedComponent G) : C.map Hom.id = C
参数：C : ConnectedComponent G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.ind`：∀ {V : Type u} {G : SimpleGraph V} {
β : G.ConnectedComponent → Prop},   (∀ (v : V), β (G.connectedComponentMk v)) → 
∀ (c : G.ConnectedCompon…
-/
theorem map_id (C : ConnectedComponent G) : C.map Hom.id = C := C.ind (fun _ => rfl)

@[simp]
/-
**SimpleGraph.ConnectedComponent.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.ConnectedComponent`。
形式化陈述：map_comp (C : G.ConnectedComponent) (φ : G ->g G') (ψ : G' ->g G'') : (C.m
ap φ).map ψ = C.map (ψ.comp φ)
参数：C : G.ConnectedComponent；φ : G ->g G'；ψ : G' ->g G''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.ind`：∀ {V : Type u} {G : SimpleGraph V} {
β : G.ConnectedComponent → Prop},   (∀ (v : V), β (G.connectedComponentMk v)) → 
∀ (c : G.ConnectedCompon…
-/
theorem map_comp (C : G.ConnectedComponent) (φ : G →g G') (ψ : G' →g G'') :
    (C.map φ).map ψ = C.map (ψ.comp φ) :=
  C.ind (fun _ => rfl)

@[simp]
/-
**SimpleGraph.ConnectedComponent.surjective_map_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.ConnectedComponent`。
形式化陈述：surjective_map_ofLE {G' : SimpleGraph V} (h : G <= G') : (map <| Hom.ofLE 
h).Surjective
参数：h : G <= G'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem surjective_map_ofLE {G' : SimpleGraph V} (h : G ≤ G') : (map <| Hom.ofLE h).Surjective :=
  Quot.ind fun v ↦ ⟨G.connectedComponentMk v, rfl⟩

variable {φ : G ≃g G'} {v : V} {v' : V'}

@[simp]
/-
**SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp** 是 Mathlib 中
的一个定理，位于命名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：iso_image_comp_eq_map_iff_eq_comp {C : G.ConnectedComponent} : G'.connecte
dComponentMk (φ v) = C.map ↑(↑φ : G ↪g G') ↔ G.connectedComponentMk v = C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.ind`：∀ {V : Type u} {G : SimpleGraph V} {
β : G.ConnectedComponent → Prop},   (∀ (v : V), β (G.connectedComponentMk v)) → 
∀ (c : G.ConnectedCompon…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iso_image_comp_eq_map_iff_eq_comp {C : G.ConnectedComponent} :
    G'.connectedComponentMk (φ v) = C.map ↑(↑φ : G ↪g G') ↔ G.connectedComponentMk v = C := by
  refine C.ind fun u => ?_
  simp only [Iso.reachable_iff, ConnectedComponent.map_mk, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding, ConnectedComponent.eq]

@[simp]
/-
**SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map** 是 Mathlib 中的
一个定理，位于命名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：iso_inv_image_comp_eq_iff_eq_map {C : G.ConnectedComponent} : G.connectedC
omponentMk (φ.symm v') = C ↔ G'.connectedComponentMk v' = C.map φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.ind`：∀ {V : Type u} {G : SimpleGraph V} {
β : G.ConnectedComponent → Prop},   (∀ (v : V), β (G.connectedComponentMk v)) → 
∀ (c : G.ConnectedCompon…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iso_inv_image_comp_eq_iff_eq_map {C : G.ConnectedComponent} :
    G.connectedComponentMk (φ.symm v') = C ↔ G'.connectedComponentMk v' = C.map φ := by
  refine C.ind fun u => ?_
  simp only [Iso.symm_apply_reachable, ConnectedComponent.eq, ConnectedComponent.map_mk,
    RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding]

end ConnectedComponent

namespace Iso

/-- An isomorphism of graphs induces a bijection of connected components. -/
@[simps]
/-
**SimpleGraph.Iso.connectedComponentEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph
.Iso`。
形式化陈述：connectedComponentEquiv (φ : G ≃g G') : G.ConnectedComponent ≃ G'.Connecte
dComponent where toFun
参数：φ : G ≃g G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of graphs induces a bijection of connected components.
-/
def connectedComponentEquiv (φ : G ≃g G') : G.ConnectedComponent ≃ G'.ConnectedComponent where
  toFun := ConnectedComponent.map φ
  invFun := ConnectedComponent.map φ.symm
  left_inv C := C.ind (fun v => congr_arg G.connectedComponentMk (Equiv.left_inv φ.toEquiv v))
  right_inv C := C.ind (fun v => congr_arg G'.connectedComponentMk (Equiv.right_inv φ.toEquiv v))

@[simp]
/-
**SimpleGraph.Iso.connectedComponentEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Iso`。
形式化陈述：connectedComponentEquiv_refl : (Iso.refl : G ≃g G).connectedComponentEquiv
 = Equiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem connectedComponentEquiv_refl :
    (Iso.refl : G ≃g G).connectedComponentEquiv = Equiv.refl _ := by
  ext ⟨v⟩
  rfl

@[simp]
/-
**SimpleGraph.Iso.connectedComponentEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Iso`。
形式化陈述：connectedComponentEquiv_symm (φ : G ≃g G') : φ.symm.connectedComponentEqui
v = φ.connectedComponentEquiv.symm
参数：φ : G ≃g G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem connectedComponentEquiv_symm (φ : G ≃g G') :
    φ.symm.connectedComponentEquiv = φ.connectedComponentEquiv.symm := by
  ext ⟨_⟩
  rfl

@[simp]
/-
**SimpleGraph.Iso.connectedComponentEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Iso`。
形式化陈述：connectedComponentEquiv_trans (φ : G ≃g G') (φ' : G' ≃g G'') : connectedCo
mponentEquiv (φ.trans φ') = φ.connectedComponentEquiv.trans φ'.connectedComponen
tEquiv
参数：φ : G ≃g G'；φ' : G' ≃g G''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem connectedComponentEquiv_trans (φ : G ≃g G') (φ' : G' ≃g G'') :
    connectedComponentEquiv (φ.trans φ') =
    φ.connectedComponentEquiv.trans φ'.connectedComponentEquiv := by
  ext ⟨_⟩
  rfl

end Iso

namespace ConnectedComponent

/-- The set of vertices in a connected component of a graph. -/
/-
**SimpleGraph.ConnectedComponent.supp** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Con
nectedComponent`。
形式化陈述：supp (C : G.ConnectedComponent)
参数：C : G.ConnectedComponent。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of vertices in a connected component of a graph.
-/
def supp (C : G.ConnectedComponent) :=
  { v | G.connectedComponentMk v = C }

@[ext]
/-
**SimpleGraph.ConnectedComponent.supp_injective** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.ConnectedComponent`。
形式化陈述：supp_injective : Function.Injective (ConnectedComponent.supp : G.Connected
Component -> Set V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.ind₂`：∀ {V : Type u} {G : SimpleGraph V} 
{β : G.ConnectedComponent → G.ConnectedComponent → Prop},   (∀ (v w : V), β (G.c
onnectedComponentMk v) (G…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.reachable_comm`：reachable_comm {u v : V} : G.Reachable u v ↔
 G.Reachable v u
· 使用定理 `SimpleGraph.Reachable.refl`：∀ {V : Type u} {G : SimpleGraph V} (u : V), 
G.Reachable u u
-/
theorem supp_injective :
    Function.Injective (ConnectedComponent.supp : G.ConnectedComponent → Set V) := by
  refine ConnectedComponent.ind₂ ?_
  simp only [ConnectedComponent.supp, Set.ext_iff, ConnectedComponent.eq, Set.mem_ofPred_eq]
  intro v w h
  rw [reachable_comm, h]

@[simp]
/-
**SimpleGraph.ConnectedComponent.supp_inj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.ConnectedComponent`。
形式化陈述：supp_inj {C D : G.ConnectedComponent} : C.supp = D.supp ↔ C = D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SimpleGraph.ConnectedComponent.supp_injective`：supp_injective : Function
.Injective (ConnectedComponent.supp : G.ConnectedComponent -> Set V)
-/
theorem supp_inj {C D : G.ConnectedComponent} : C.supp = D.supp ↔ C = D :=
  ConnectedComponent.supp_injective.eq_iff
/-
**SimpleGraph.ConnectedComponent.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Connect
edComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike G.ConnectedComponent V where
  coe := ConnectedComponent.supp
  coe_injective := ConnectedComponent.supp_injective

@[simp]
/-
**SimpleGraph.ConnectedComponent.mem_supp_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.ConnectedComponent`。
形式化陈述：mem_supp_iff (C : G.ConnectedComponent) (v : V) : v in C.supp ↔ G.connecte
dComponentMk v = C
参数：C : G.ConnectedComponent；v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_supp_iff (C : G.ConnectedComponent) (v : V) :
    v ∈ C.supp ↔ G.connectedComponentMk v = C :=
  Iff.rfl
/-
**SimpleGraph.ConnectedComponent.mem_supp_congr_adj** 是 Mathlib 中的一个引理，位于命名空间 `S
impleGraph.ConnectedComponent`。
形式化陈述：mem_supp_congr_adj {v w : V} (c : G.ConnectedComponent) (hadj : G.Adj v w)
 : v in c.supp ↔ w in c.supp
参数：c : G.ConnectedComponent；hadj : G.Adj v w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj`：connected
ComponentMk_eq_of_adj {v w : V} (a : G.Adj v w) : G.connectedComponentMk v = G.c
onnectedComponentMk w
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
lemma mem_supp_congr_adj {v w : V} (c : G.ConnectedComponent) (hadj : G.Adj v w) :
    v ∈ c.supp ↔ w ∈ c.supp := by
  simp only [ConnectedComponent.mem_supp_iff] at *
  constructor <;> intro h <;> simp only [← h] <;> apply connectedComponentMk_eq_of_adj
  · exact hadj.symm
  · exact hadj
/-
**SimpleGraph.ConnectedComponent.connectedComponentMk_mem** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：connectedComponentMk_mem {v : V} : v in G.connectedComponentMk v
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem connectedComponentMk_mem {v : V} : v ∈ G.connectedComponentMk v :=
  rfl
/-
**SimpleGraph.ConnectedComponent.nonempty_supp** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.ConnectedComponent`。
形式化陈述：nonempty_supp (C : G.ConnectedComponent) : C.supp.Nonempty
参数：C : G.ConnectedComponent。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
-/
theorem nonempty_supp (C : G.ConnectedComponent) : C.supp.Nonempty := C.exists_rep

/-- The equivalence between connected components, induced by an isomorphism of graphs,
itself defines an equivalence on the supports of each connected component.
-/
/-
**SimpleGraph.ConnectedComponent.isoEquivSupp** 是 Mathlib 中的一个定义，位于命名空间 `SimpleG
raph.ConnectedComponent`。
形式化陈述：isoEquivSupp (φ : G ≃g G') (C : G.ConnectedComponent) : C.supp ≃ (φ.connec
tedComponentEquiv C).supp where toFun v
参数：φ : G ≃g G'；C : G.ConnectedComponent。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between connected components, induced by an isomorphism of graph
s,
itself defines an equivalence on the supports of each connected component.
-/
def isoEquivSupp (φ : G ≃g G') (C : G.ConnectedComponent) :
    C.supp ≃ (φ.connectedComponentEquiv C).supp where
  toFun v := ⟨φ v, ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr v.prop⟩
  invFun v' := ⟨φ.symm v', ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map.mpr v'.prop⟩
  left_inv v := Subtype.ext (φ.toEquiv.left_inv ↑v)
  right_inv v := Subtype.ext (φ.toEquiv.right_inv ↑v)
/-
**SimpleGraph.ConnectedComponent.mem_coe_supp_of_adj** 是 Mathlib 中的一个引理，位于命名空间 `
SimpleGraph.ConnectedComponent`。
形式化陈述：mem_coe_supp_of_adj {v w : V} {H : Subgraph G} {c : ConnectedComponent H.c
oe} (hv : v in (↑) '' (c : Set H.verts)) (hw : w in H.verts) (hadj : H.Adj v w) 
: w in (↑) '' (c : Set H.verts)
参数：hv : v in (↑) '' (c : Set H.verts)；hw : w in H.verts；hadj : H.Adj v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.ConnectedComponent.mem_supp_iff`：mem_supp_iff (C : G.Connect
edComponent) (v : V) : v in C.supp ↔ G.connectedComponentMk v = C
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj`：connected
ComponentMk_eq_of_adj {v w : V} (a : G.Adj v w) : G.connectedComponentMk v = G.c
onnectedComponentMk w
· 使用定理 `SimpleGraph.Subgraph.Adj.coe`：∀ {V : Type u} {G : SimpleGraph V} {H : G.
Subgraph} {u v : V} (h : H.Adj u v), H.coe.Adj ⟨u, ⋯⟩ ⟨v, ⋯⟩
· 使用定理 `SimpleGraph.Subgraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {G' : 
G.Subgraph} {u v : V}, G'.Adj u v → G'.Adj v u
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mem_coe_supp_of_adj {v w : V} {H : Subgraph G} {c : ConnectedComponent H.coe}
    (hv : v ∈ (↑) '' (c : Set H.verts)) (hw : w ∈ H.verts)
    (hadj : H.Adj v w) : w ∈ (↑) '' (c : Set H.verts) := by
  obtain ⟨_, h⟩ := hv
  use ⟨w, hw⟩
  rw [← (mem_supp_iff _ _).mp h.1]
  exact ⟨connectedComponentMk_eq_of_adj <| Subgraph.Adj.coe <| h.2 ▸ hadj.symm, rfl⟩
/-
**SimpleGraph.ConnectedComponent.eq_of_common_vertex** 是 Mathlib 中的一个引理，位于命名空间 `
SimpleGraph.ConnectedComponent`。
形式化陈述：eq_of_common_vertex {v : V} {c c' : ConnectedComponent G} (hc : v in c.sup
p) (hc' : v in c'.supp) : c = c'
参数：hc : v in c.supp；hc' : v in c'.supp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma eq_of_common_vertex {v : V} {c c' : ConnectedComponent G} (hc : v ∈ c.supp)
    (hc' : v ∈ c'.supp) : c = c' := by
  simp only [mem_supp_iff] at *
  rw [← hc, ← hc']
/-
**SimpleGraph.ConnectedComponent.connectedComponentMk_supp_subset_supp** 是 Mathl
ib 中的一个引理，位于命名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：connectedComponentMk_supp_subset_supp {G'} {v : V} (h : G <= G') (c' : G'.
ConnectedComponent) (hc' : v in c'.supp) : (G.connectedComponentMk v).supp subse
teq c'.supp
参数：h : G <= G'；c' : G'.ConnectedComponent；hc' : v in c'.supp。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.ConnectedComponent.sound`：∀ {V : Type u} {G : SimpleGraph V}
 {v w : V}, G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk 
w
· 使用定理 `SimpleGraph.Reachable.mono`：∀ {V : Type u} {u v : V} {G G' : SimpleGraph
 V}, G ≤ G' → G.Reachable u v → G'.Reachable u v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma connectedComponentMk_supp_subset_supp {G'} {v : V} (h : G ≤ G') (c' : G'.ConnectedComponent)
    (hc' : v ∈ c'.supp) : (G.connectedComponentMk v).supp ⊆ c'.supp := by
  intro v' hv'
  simp only [mem_supp_iff, ConnectedComponent.eq] at hv' ⊢
  rw [ConnectedComponent.sound (hv'.mono h)]
  exact hc'
/-
**SimpleGraph.ConnectedComponent.biUnion_supp_eq_supp** 是 Mathlib 中的一个引理，位于命名空间 
`SimpleGraph.ConnectedComponent`。
形式化陈述：biUnion_supp_eq_supp {G G' : SimpleGraph V} (h : G <= G') (c' : ConnectedC
omponent G') : ⋃ (c : ConnectedComponent G) (_ : c.supp subseteq c'.supp), c.sup
p = c'.supp
参数：h : G <= G'；c' : ConnectedComponent G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SimpleGraph.ConnectedComponent.connectedComponentMk_supp_subset_supp`：co
nnectedComponentMk_supp_subset_supp {G'} {v : V} (h : G <= G') (c' : G'.Connecte
dComponent) (hc' : v in c'.supp) : (G.connectedComponentMk…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma biUnion_supp_eq_supp {G G' : SimpleGraph V} (h : G ≤ G') (c' : ConnectedComponent G') :
    ⋃ (c : ConnectedComponent G) (_ : c.supp ⊆ c'.supp), c.supp = c'.supp := by
  ext v
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨_, ⟨hi, hi'⟩⟩ ↦ hi hi', ?_⟩
  intro hv
  use G.connectedComponentMk v
  use c'.connectedComponentMk_supp_subset_supp h hv
  simp only [mem_supp_iff]
/-
**SimpleGraph.ConnectedComponent.top_supp_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Sim
pleGraph.ConnectedComponent`。
形式化陈述：top_supp_eq_univ (c : ConnectedComponent (⊤ : SimpleGraph V)) : c.supp = (
Set.univ : Set V)
参数：c : ConnectedComponent (⊤ : SimpleGraph V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.exists_rep`：∀ {α : Sort u} {r : α → α → Prop} (q : Quot r), ∃ a, Qu
ot.mk r a = q
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SimpleGraph.ConnectedComponent.sound`：∀ {V : Type u} {G : SimpleGraph V}
 {v w : V}, G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk 
w
-/
lemma top_supp_eq_univ (c : ConnectedComponent (⊤ : SimpleGraph V)) :
    c.supp = (Set.univ : Set V) := by
  obtain ⟨w, rfl⟩ := c.exists_rep
  ext v
  simpa [-ConnectedComponent.eq] using! ConnectedComponent.sound (G := ⊤)
/-
**SimpleGraph.ConnectedComponent.reachable_of_mem_supp** 是 Mathlib 中的一个引理，位于命名空间
 `SimpleGraph.ConnectedComponent`。
形式化陈述：reachable_of_mem_supp {G : SimpleGraph V} (C : G.ConnectedComponent) {u v 
: V} (hu : u in C.supp) (hv : v in C.supp) : G.Reachable u v
参数：C : G.ConnectedComponent；hu : u in C.supp；hv : v in C.supp。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.exact`：∀ {V : Type u} {G : SimpleGraph V}
 {v w : V}, G.connectedComponentMk v = G.connectedComponentMk w → G.Reachable v 
w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.ConnectedComponent.mem_supp_iff`：mem_supp_iff (C : G.Connect
edComponent) (v : V) : v in C.supp ↔ G.connectedComponentMk v = C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma reachable_of_mem_supp {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ C.supp) : G.Reachable u v := by
  rw [mem_supp_iff] at hu hv
  exact ConnectedComponent.exact (hv ▸ hu)
/-
**SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp** 是 Mathlib 中的一个引理，位于命
名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：mem_supp_of_adj_mem_supp {G : SimpleGraph V} (C : G.ConnectedComponent) {u
 v : V} (hu : u in C.supp) (hadj : G.Adj u v) : v in C.supp
参数：C : G.ConnectedComponent；hu : u in C.supp；hadj : G.Adj u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.ConnectedComponent.mem_supp_congr_adj`：mem_supp_congr_adj {v
 w : V} (c : G.ConnectedComponent) (hadj : G.Adj v w) : v in c.supp ↔ w in c.sup
p
-/
lemma mem_supp_of_adj_mem_supp {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C.supp) (hadj : G.Adj u v) : v ∈ C.supp := (mem_supp_congr_adj C hadj).mp hu

/--
Given a connected component `C` of a simple graph `G`, produce the induced graph on `C`.
The declaration `connected_toSimpleGraph` shows it is connected, and `toSimpleGraph_hom`
provides the homomorphism back to `G`.
-/
/-
**SimpleGraph.ConnectedComponent.toSimpleGraph** 是 Mathlib 中的一个定义，位于命名空间 `Simple
Graph.ConnectedComponent`。
形式化陈述：toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) : SimpleGraph
 C
参数：C : G.ConnectedComponent。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a connected component `C` of a simple graph `G`, produce the induced graph
 on `C`.
The declaration `connected_toSimpleGraph` shows it is connected, and `toSimpleGr
aph_hom`
provides the homomorphism back to `G`.
-/
def toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) : SimpleGraph C := G.induce C.supp

/-- Homomorphism from a connected component graph to the original graph. -/
/-
**SimpleGraph.ConnectedComponent.toSimpleGraph_hom** 是 Mathlib 中的一个定义，位于命名空间 `Si
mpleGraph.ConnectedComponent`。
形式化陈述：toSimpleGraph_hom {G : SimpleGraph V} (C : G.ConnectedComponent) : C.toSim
pleGraph ->g G where toFun u
参数：C : G.ConnectedComponent。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homomorphism from a connected component graph to the original graph.
-/
def toSimpleGraph_hom {G : SimpleGraph V} (C : G.ConnectedComponent) : C.toSimpleGraph →g G where
  toFun u := u.val
  map_rel' := id
/-
**SimpleGraph.ConnectedComponent.toSimpleGraph_hom_apply** 是 Mathlib 中的一个引理，位于命名
空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：toSimpleGraph_hom_apply {G : SimpleGraph V} (C : G.ConnectedComponent) (u 
: C) : C.toSimpleGraph_hom u = u.val
参数：C : G.ConnectedComponent；u : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSimpleGraph_hom_apply {G : SimpleGraph V} (C : G.ConnectedComponent) (u : C) :
    C.toSimpleGraph_hom u = u.val := rfl
/-
**SimpleGraph.ConnectedComponent.toSimpleGraph_adj** 是 Mathlib 中的一个引理，位于命名空间 `Si
mpleGraph.ConnectedComponent`。
形式化陈述：toSimpleGraph_adj {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
 (hu : u in C) (hv : v in C) : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨v, hv⟩ ↔ G.Adj u v
参数：C : G.ConnectedComponent；hu : u in C；hv : v in C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toSimpleGraph_adj {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V} (hu : u ∈ C)
    (hv : v ∈ C) : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨v, hv⟩ ↔ G.Adj u v := by
  simp [toSimpleGraph]
/-
**SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph** 是 Mathlib 中的一个引
理，位于命名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：adj_spanningCoe_toSimpleGraph {v w : V} (C : G.ConnectedComponent) : C.toS
impleGraph.spanningCoe.Adj v w ↔ v in C.supp ∧ G.Adj v w
参数：C : G.ConnectedComponent。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.ConnectedComponent.mem_supp_congr_adj`：mem_supp_congr_adj {v
 w : V} (c : G.ConnectedComponent) (hadj : G.Adj v w) : v in c.supp ↔ w in c.sup
p
-/
lemma adj_spanningCoe_toSimpleGraph {v w : V} (C : G.ConnectedComponent) :
    C.toSimpleGraph.spanningCoe.Adj v w ↔ v ∈ C.supp ∧ G.Adj v w := by
  apply Iff.intro
  · intro h
    simp_all only [map_adj, SetLike.coe_sort_coe, Subtype.exists, mem_supp_iff]
    obtain ⟨_, a, _, _, h₁, rfl, rfl⟩ := h
    exact ⟨a, h₁⟩
  · simp only [toSimpleGraph, map_adj, comap_adj, Embedding.subtype_apply, Subtype.exists,
      exists_and_left, and_imp]
    intro h hadj
    exact ⟨v, h, w, hadj, rfl, (C.mem_supp_congr_adj hadj).mp h, rfl⟩

/-- Get the walk between two vertices in a connected component from a walk in the original graph.
This is used in `reachable_toSimpleGraph`. -/
/-
**SimpleGraph.ConnectedComponent.walk_toSimpleGraph** 是 Mathlib 中的一个定义，位于命名空间 `S
impleGraph.ConnectedComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the walk between two vertices in a connected component from a walk in the or
iginal graph.
This is used in `reachable_toSimpleGraph`.
-/
private def walk_toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) (p : G.Walk u v) : C.toSimpleGraph.Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  cases p with
  | nil => exact Walk.nil
  | @cons v w u h p =>
    have hw : w ∈ C := C.mem_supp_of_adj_mem_supp hu h
    have h' : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨w, hw⟩ := h
    exact Walk.cons h' (C.walk_toSimpleGraph hw hv p)

/-- There is a walk between every pair of vertices in a connected component. -/
/-
**SimpleGraph.ConnectedComponent.reachable_toSimpleGraph** 是 Mathlib 中的一个引理，位于命名
空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：reachable_toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) {u 
v : V} (hu : u in C) (hv : v in C) : C.toSimpleGraph.Reachable ⟨u, hu⟩ ⟨v, hv⟩
参数：C : G.ConnectedComponent；hu : u in C；hv : v in C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
 (p : G.Walk u v), G.Reachable u v
· 使用引理 `SimpleGraph.ConnectedComponent.reachable_of_mem_supp`：reachable_of_mem_s
upp {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V} (hu : u in C.supp) 
(hv : v in C.supp) : G.Reachable u v

--- 原说明 ---
There is a walk between every pair of vertices in a connected component.
-/
lemma reachable_toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) : C.toSimpleGraph.Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
  Walk.reachable (C.walk_toSimpleGraph hu hv (C.reachable_of_mem_supp hu hv).some)
/-
**SimpleGraph.ConnectedComponent.connected_toSimpleGraph** 是 Mathlib 中的一个引理，位于命名
空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：connected_toSimpleGraph (C : ConnectedComponent G) : (C.toSimpleGraph).Con
nected where preconnected
参数：C : ConnectedComponent G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.ConnectedComponent.reachable_toSimpleGraph`：reachable_toSimp
leGraph {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V} (hu : u in C) (
hv : v in C) : C.toSimpleGraph.Reachable ⟨u,…
· 使用定理 `Quot.out_eq`：Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q
.out = q
-/
lemma connected_toSimpleGraph (C : ConnectedComponent G) : (C.toSimpleGraph).Connected where
  preconnected := by
    intro ⟨u, hu⟩ ⟨v, hv⟩
    exact C.reachable_toSimpleGraph hu hv
  nonempty := ⟨C.out, C.out_eq⟩
/-
**SimpleGraph.ConnectedComponent.maximal_connected_induce_supp** 是 Mathlib 中的一个定
理，位于命名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：maximal_connected_induce_supp (C : G.ConnectedComponent) : Maximal (G.indu
ce · |>.Connected) C.supp
参数：C : G.ConnectedComponent。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.ind`：∀ {V : Type u} {G : SimpleGraph V} {
β : G.ConnectedComponent → Prop},   (∀ (v : V), β (G.connectedComponentMk v)) → 
∀ (c : G.ConnectedCompon…
· 使用引理 `SimpleGraph.ConnectedComponent.connected_toSimpleGraph`：connected_toSimp
leGraph (C : ConnectedComponent G) : (C.toSimpleGraph).Connected where preconnec
ted
· 使用定理 `SimpleGraph.ConnectedComponent.sound`：∀ {V : Type u} {G : SimpleGraph V}
 {v w : V}, G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk 
w
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
-/
theorem maximal_connected_induce_supp (C : G.ConnectedComponent) :
    Maximal (G.induce · |>.Connected) C.supp := by
  refine C.ind fun v ↦ ?_
  refine ⟨connected_toSimpleGraph _, fun s hconn hle u hu ↦ ConnectedComponent.sound ?_⟩
  exact hconn.preconnected ⟨u, hu⟩ ⟨v, hle rfl⟩ |>.map <| Embedding.induce s |>.toHom
/-
**SimpleGraph.ConnectedComponent.maximal_connected_induce_iff** 是 Mathlib 中的一个定理
，位于命名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：maximal_connected_induce_iff (s : Set V) : Maximal (G.induce · |>.Connecte
d) s ↔ exists C : G.ConnectedComponent, C.supp = s
参数：s : Set V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
· 使用定理 `SimpleGraph.ConnectedComponent.sound`：∀ {V : Type u} {G : SimpleGraph V}
 {v w : V}, G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk 
w
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `SimpleGraph.ConnectedComponent.connected_toSimpleGraph`：connected_toSimp
leGraph (C : ConnectedComponent G) : (C.toSimpleGraph).Connected where preconnec
ted
· 使用定理 `SimpleGraph.ConnectedComponent.maximal_connected_induce_supp`：maximal_co
nnected_induce_supp (C : G.ConnectedComponent) : Maximal (G.induce · |>.Connecte
d) C.supp
-/
theorem maximal_connected_induce_iff (s : Set V) :
    Maximal (G.induce · |>.Connected) s ↔ ∃ C : G.ConnectedComponent, C.supp = s := by
  refine ⟨fun ⟨hconn, h⟩ ↦ ?_, fun ⟨C, h⟩ ↦ ?_⟩
  · have ⟨v, hv⟩ := hconn.nonempty
    suffices s ≤ (G.connectedComponentMk v).supp from
      ⟨G.connectedComponentMk v, le_antisymm (h (connected_toSimpleGraph _) this) this⟩
    exact fun u hu ↦ ConnectedComponent.sound <|
      hconn.preconnected ⟨u, hu⟩ ⟨v, hv⟩ |>.map <| Embedding.induce s |>.toHom
  · exact h ▸ maximal_connected_induce_supp _

end ConnectedComponent

/-- Given graph homomorphisms from each connected component of `G` to `H`, this is the graph
homomorphism from `G` to `H`. -/
@[simps]
/-
**SimpleGraph.homOfConnectedComponents** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：homOfConnectedComponents (G : SimpleGraph V) {H : SimpleGraph V'} (C : (c 
: G.ConnectedComponent) -> c.toSimpleGraph ->g H) : G ->g H where toFun
参数：G : SimpleGraph V；C : (c : G.ConnectedComponent) -> c.toSimpleGraph ->g H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.connectedComponentMk_mem`：connectedCompon
entMk_mem {v : V} : v in G.connectedComponentMk v

--- 原说明 ---
Given graph homomorphisms from each connected component of `G` to `H`, this is t
he graph
homomorphism from `G` to `H`.
-/
def homOfConnectedComponents (G : SimpleGraph V) {H : SimpleGraph V'}
    (C : (c : G.ConnectedComponent) → c.toSimpleGraph →g H) : G →g H where
  toFun := fun x ↦ (C (G.connectedComponentMk x)) ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
  map_rel' := fun hab ↦ by
    have h : (G.connectedComponentMk _).toSimpleGraph.Adj ⟨_, rfl⟩
        ⟨_, ((G.connectedComponentMk _).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using! hab
    convert (C (G.connectedComponentMk _)).map_rel h using 3 <;>
      rw [ConnectedComponent.connectedComponentMk_eq_of_adj hab]

-- TODO: Extract as lemma about general equivalence relation
/-
**SimpleGraph.pairwise_disjoint_supp_connectedComponent** 是 Mathlib 中的一个引理，位于命名空
间 `SimpleGraph`。
形式化陈述：pairwise_disjoint_supp_connectedComponent (G : SimpleGraph V) : Pairwise f
un c c' : ConnectedComponent G => Disjoint c.supp c'.supp
参数：G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.ConnectedComponent.mem_supp_iff`：mem_supp_iff (C : G.Connect
edComponent) (v : V) : v in C.supp ↔ G.connectedComponentMk v = C
-/
lemma pairwise_disjoint_supp_connectedComponent (G : SimpleGraph V) :
    Pairwise fun c c' : ConnectedComponent G ↦ Disjoint c.supp c'.supp := by
  simp_rw [Set.disjoint_left]
  intro _ _ h a hsx hsy
  rw [ConnectedComponent.mem_supp_iff] at hsx hsy
  rw [hsx] at hsy
  exact h hsy

-- TODO: Extract as lemma about general equivalence relation
/-
**SimpleGraph.iUnion_connectedComponentSupp** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
形式化陈述：iUnion_connectedComponentSupp (G : SimpleGraph V) : ⋃ c : G.ConnectedCompo
nent, c.supp = Set.univ
参数：G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma iUnion_connectedComponentSupp (G : SimpleGraph V) :
    ⋃ c : G.ConnectedComponent, c.supp = Set.univ := by
  refine Set.eq_univ_of_forall fun v ↦ ⟨G.connectedComponentMk v, ?_⟩
  simp only [Set.mem_range, SetLike.mem_coe]
  exact ⟨⟨G.connectedComponentMk v, rfl⟩, rfl⟩
/-
**SimpleGraph.Preconnected.set_univ_walk_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Preconnected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V}, G.Preconnected → ∀ (u v : V), Set.univ
.Nonempty
参数：u v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_iff_univ_nonempty`：nonempty_iff_univ_nonempty : Nonempty α 
↔ (univ : Set α).Nonempty
-/
theorem Preconnected.set_univ_walk_nonempty (hconn : G.Preconnected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  rw [← Set.nonempty_iff_univ_nonempty]
  exact hconn u v
/-
**SimpleGraph.Connected.set_univ_walk_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Connected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V}, G.Connected → ∀ (u v : V), Set.univ.No
nempty
参数：u v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Preconnected.set_univ_walk_nonempty`：∀ {V : Type u} {G : Sim
pleGraph V}, G.Preconnected → ∀ (u v : V), Set.univ.Nonempty
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
-/
theorem Connected.set_univ_walk_nonempty (hconn : G.Connected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty :=
  hconn.preconnected.set_univ_walk_nonempty u v
/-
**SimpleGraph.Preconnected.exists_adj_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Preconnected`。
形式化陈述：∀ {V : Type u} [Nontrivial V] {G : SimpleGraph V}, G.Preconnected → ∀ (v :
 V), ∃ u, G.Adj v u
参数：v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用引理 `SimpleGraph.Walk.not_nil_of_ne`：not_nil_of_ne {p : G.Walk v w} : v != w 
-> ¬ p.Nil
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma Preconnected.exists_adj_of_nontrivial [Nontrivial V] {G : SimpleGraph V} (h : G.Preconnected)
    (v : V) : ∃ u, G.Adj v u := by
  have ⟨u, huv⟩ := exists_ne v
  have ⟨w⟩ := h v u
  exact ⟨_, w.adj_snd <| w.not_nil_of_ne huv.symm⟩

/-! ### Bridge edges -/

section BridgeEdges
variable {u v : V}

/-- An edge of a graph is a *bridge* if without it, its incident vertices
are not reachable from one another. -/
/-
**SimpleGraph.IsBridge** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsBridge (G : SimpleGraph V) (e : Sym2 V) : Prop
参数：G : SimpleGraph V；e : Sym2 V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An edge of a graph is a *bridge* if without it, its incident vertices
are not reachable from one another.
-/
def IsBridge (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun v w ↦ ¬ (G.deleteEdges {e}).Reachable v w, by simp [reachable_comm]⟩ e
/-
**SimpleGraph.isBridge_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isBridge_iff {u v : V} : G.IsBridge s(u, v) ↔ ¬ (G.deleteEdges {s(u, v)}).
Reachable u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBridge_iff {u v : V} :
    G.IsBridge s(u, v) ↔ ¬ (G.deleteEdges {s(u, v)}).Reachable u v := .rfl
/-
**SimpleGraph.IsBridge.of_not_reachable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.I
sBridge`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, ¬G.Reachable u v → G.IsBridg
e s(u, v)
参数：u, v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.mono`：∀ {V : Type u} {u v : V} {G G' : SimpleGraph
 V}, G ≤ G' → G.Reachable u v → G'.Reachable u v
· 使用引理 `SimpleGraph.deleteEdges_le`：deleteEdges_le (s : Set (Sym2 V)) : G.delete
Edges s <= G
-/
@[simp] lemma IsBridge.of_not_reachable (huv : ¬ G.Reachable u v) :
    G.IsBridge s(u, v) := fun h ↦ huv <| h.mono <| deleteEdges_le _
/-
**SimpleGraph.IsBridge.reachable_iff_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsBridge`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.IsBridge s(u, v) → (G.Reac
hable u v ↔ G.Adj u v)
参数：u, v；G.Reachable u v ↔ G.Adj u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.mem_edgeSet`：mem_edgeSet : s(v, w) in G.edgeSet ↔ G.Adj v w
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用引理 `SimpleGraph.deleteEdges_le`：deleteEdges_le (s : Set (Sym2 V)) : G.delete
Edges s <= G
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
-/
theorem IsBridge.reachable_iff_adj (h : G.IsBridge s(u, v)) : G.Reachable u v ↔ G.Adj u v := by
  refine ⟨fun hreach ↦ G.mem_edgeSet.mp ?_, Adj.reachable⟩
  have : G.deleteEdges {s(u, v)} < G := deleteEdges_le _ |>.lt_of_ne <| by grind [isBridge_iff]
  grind [edgeSet_strict_mono this, edgeSet_deleteEdges]
/-
**SimpleGraph.IsBridge.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsBridg
e`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {e : Sym2 V}, G.IsBridge e → Nontrivial
 V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.deleteEdges_of_subset_diagSet`：∀ {V : Type u_1} {s : Set (Sy
m2 V)} (G : SimpleGraph V), s ⊆ Sym2.diagSet → G.deleteEdges s = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsBridge.nontrivial {e : Sym2 V} (he : G.IsBridge e) : Nontrivial V := by
  cases e with | h u v; exact ⟨u, v, by rintro rfl; simp [IsBridge] at he⟩

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.reachable_deleteEdges_iff_exists_walk** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph`。
形式化陈述：reachable_deleteEdges_iff_exists_walk {v w v' w' : V} : (G.deleteEdges {s(
v, w)}).Reachable v' w' ↔ exists p : G.Walk v' w', s(v, w) ∉ p.edges
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.edges_map`：edges_map : (p.map f).edges = p.edges.map (S
ym2.map f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sym2.map_congr`：map_congr {f g : α -> β} {s : Sym2 α} (h : forall x in s
, f x = g x) : map f s = map g s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Sym2.map_id'`：map_id' : (map fun x : α => x) = id
· 使用定理 `SimpleGraph.edgeSet_deleteEdges`：edgeSet_deleteEdges (s : Set (Sym2 V)) 
: (G.deleteEdges s).edgeSet = G.edgeSet \ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `SimpleGraph.Walk.edges_subset_edgeSet`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem reachable_deleteEdges_iff_exists_walk {v w v' w' : V} :
    (G.deleteEdges {s(v, w)}).Reachable v' w' ↔ ∃ p : G.Walk v' w', s(v, w) ∉ p.edges := by
  constructor
  · rintro ⟨p⟩
    use p.map (.ofLE (by simp))
    simp_rw [Walk.edges_map, List.mem_map, Hom.ofLE_apply, Sym2.map_id', id]
    rintro ⟨e, h, rfl⟩
    simpa using p.edges_subset_edgeSet h
  · rintro ⟨p, h⟩
    refine ⟨p.transfer _ fun e ep => ?_⟩
    rw [edgeSet_deleteEdges]
    exact ⟨p.edges_subset_edgeSet ep, fun h' => h (h' ▸ ep)⟩

@[deprecated (since := "2026-03-18")]
alias reachable_delete_edges_iff_exists_walk := reachable_deleteEdges_iff_exists_walk
/-
**SimpleGraph.isBridge_iff_forall_walk_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：isBridge_iff_forall_walk_mem_edges {v w : V} : G.IsBridge s(v, w) ↔ forall
 p : G.Walk v w, s(v, w) in p.edges
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isBridge_iff`：isBridge_iff {u v : V} : G.IsBridge s(u, v) ↔ 
¬ (G.deleteEdges {s(u, v)}).Reachable u v
· 使用定理 `SimpleGraph.reachable_deleteEdges_iff_exists_walk`：reachable_deleteEdges
_iff_exists_walk {v w v' w' : V} : (G.deleteEdges {s(v, w)}).Reachable v' w' ↔ e
xists p : G.Walk v' w', s(v, w) ∉ p.edg…
· 使用定理 `Classical.not_exists_not`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, ¬p x) 
↔ ∀ (x : α), p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBridge_iff_forall_walk_mem_edges {v w : V} :
    G.IsBridge s(v, w) ↔ ∀ p : G.Walk v w, s(v, w) ∈ p.edges := by
  rw [isBridge_iff, reachable_deleteEdges_iff_exists_walk, not_exists_not]

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_adj_and_forall_walk_mem_edges := isBridge_iff_forall_walk_mem_edges
/-
**SimpleGraph.reachable_deleteEdges_iff_exists_cycle.aux** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph.reachable_deleteEdges_iff_exists_cycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : DecidableEq V] {u v w : V},   (
∀ (p : G.Walk v w), s(v, w) ∈ p.edges) →     ∀ (c : G.Walk u u), c.IsTrail → ∀ (
he : s(v, w) ∈ c.edges), w ∈ (c.takeUntil v ⋯).support → False
参数：∀ (p : G.Walk v w), s(v, w) ∈ p.edges；c : G.Walk u u；he : s(v, w) ∈ c.edges；c
.takeUntil v ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.fst_mem_support_of_mem_edges`：fst_mem_support_of_mem_ed
ges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) : t in p.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.disjoint_of_nodup_append`：disjoint_of_nodup_append {l₁ l₂ : List α}
 (d : Nodup (l₁ ++ l₂)) : Disjoint l₁ l₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.edges_append`：edges_append {u v w : V} (p : G.Walk u v)
 (p' : G.Walk v w) : (p.append p').edges = p.edges ++ p'.edges
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.nodup_append_comm`：nodup_append_comm {l₁ l₂ : List α} : Nodup (l₁ +
+ l₂) ↔ Nodup (l₂ ++ l₁)
· 使用定理 `SimpleGraph.Walk.isTrail_def`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} (p : G.Walk u v), p.IsTrail ↔ p.edges.Nodup
· 使用定理 `List.mem_reverse`：∀ {α : Type u_1} {x : α} {as : List α}, x ∈ as.reverse
 ↔ x ∈ as
· 使用定理 `SimpleGraph.Walk.edges_reverse`：edges_reverse {u v : V} (p : G.Walk u v)
 : p.reverse.edges = p.edges.reverse
-/
theorem reachable_deleteEdges_iff_exists_cycle.aux [DecidableEq V] {u v w : V}
    (hb : ∀ p : G.Walk v w, s(v, w) ∈ p.edges) (c : G.Walk u u) (hc : c.IsTrail)
    (he : s(v, w) ∈ c.edges)
    (hw : w ∈ (c.takeUntil v (c.fst_mem_support_of_mem_edges he)).support) : False := by
  have hv := c.fst_mem_support_of_mem_edges he
  -- decompose c into
  --      puw     pwv     pvu
  --   u ----> w ----> v ----> u
  let puw := (c.takeUntil v hv).takeUntil w hw
  let pwv := (c.takeUntil v hv).dropUntil w hw
  let pvu := c.dropUntil v hv
  have : c = (puw.append pwv).append pvu := by simp [puw, pwv, pvu]
  -- We have two walks from v to w
  --      pvu     puw
  --   v ----> u ----> w
  --   |               ^
  --    `-------------'
  --      pwv.reverse
  -- so they both contain the edge s(v, w), but that's a contradiction since c is a trail.
  have hbq := hb (pvu.append puw)
  have hpq' := hb pwv.reverse
  rw [Walk.edges_reverse, List.mem_reverse] at hpq'
  rw [Walk.isTrail_def, this, Walk.edges_append, Walk.edges_append, List.nodup_append_comm,
    ← List.append_assoc, ← Walk.edges_append] at hc
  exact List.disjoint_of_nodup_append hc hbq hpq'
/-
**SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle** 是 Mathlib 中的一个定理
，位于命名空间 `SimpleGraph`。
形式化陈述：adj_and_reachable_delete_edges_iff_exists_cycle {v w : V} : G.Adj v w ∧ (G
.deleteEdges {s(v, w)}).Reachable v w ↔ exists (u : V) (p : G.Walk u u), p.IsCyc
le ∧ s(v, w) in p.edges
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.reachable_deleteEdges_iff_exists_walk`：reachable_deleteEdges
_iff_exists_walk {v w v' w' : V} : (G.deleteEdges {s(v, w)}).Reachable v' w' ↔ e
xists p : G.Walk v' w', s(v, w) ∉ p.edg…
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Path.cons_isCycle`：cons_isCycle {u v : V} (p : G.Path v u) (
h : G.Adj u v) (he : s(u, v) ∉ (p : G.Walk v u).edges) : (Walk.cons h ↑p).IsCycl
e
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
· 使用定理 `SimpleGraph.Walk.edges_toPath_subset_edges`：edges_toPath_subset_edges (p
 : G.Walk u v) : (p.toPath : G.Walk u v).edges subseteq p.edges
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `SimpleGraph.Walk.adj_of_mem_edges`：adj_of_mem_edges {u v x y : V} (p : G
.Walk u v) (h : s(x, y) in p.edges) : G.Adj x y
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `SimpleGraph.Walk.edges_reverse`：edges_reverse {u v : V} (p : G.Walk u v)
 : p.reverse.edges = p.edges.reverse
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SimpleGraph.Walk.fst_mem_support_of_mem_edges`：fst_mem_support_of_mem_ed
ges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) : t in p.support
· 使用定理 `SimpleGraph.reachable_deleteEdges_iff_exists_cycle.aux`：∀ {V : Type u} {
G : SimpleGraph V} [inst : DecidableEq V] {u v w : V},   (∀ (p : G.Walk v w), s(
v, w) ∈ p.edges) →     ∀ (c : G.Walk u u), c…
· 使用定理 `SimpleGraph.Walk.IsTrail.rotate`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} [inst : DecidableEq V] {c : G.Walk v v} (hu : u ∈ c.support),   c.IsTrail 
→ (c.rotate u hu).IsT…
· 使用定理 `SimpleGraph.Walk.IsCircuit.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCircuit → p.IsTrail
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
· 使用定理 `List.IsRotated.mem_iff`：∀ {α : Type u} {l l' : List α}, l ~r l' → ∀ {a :
 α}, a ∈ l ↔ a ∈ l'
· 使用定理 `SimpleGraph.Walk.rotate_edges`：rotate_edges (c : G.Walk v v) (u : V) (h)
 : (c.rotate u h).edges ~r c.edges
· 使用定理 `SimpleGraph.Walk.start_mem_support`：start_mem_support {u v : V} (p : G.W
alk u v) : u in p.support
-/
theorem adj_and_reachable_delete_edges_iff_exists_cycle {v w : V} :
    G.Adj v w ∧ (G.deleteEdges {s(v, w)}).Reachable v w ↔
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges := by
  classical
  rw [reachable_deleteEdges_iff_exists_walk]
  constructor
  · rintro ⟨h, p, hp⟩
    refine ⟨w, Walk.cons h.symm p.toPath, ?_, ?_⟩
    · apply Path.cons_isCycle
      rw [Sym2.eq_swap]
      intro h
      cases hp (Walk.edges_toPath_subset_edges p h)
    · simp
  · rintro ⟨u, c, hc, he⟩
    refine ⟨c.adj_of_mem_edges he, ?_⟩
    by_contra! hb
    have hb' : ∀ p : G.Walk w v, s(w, v) ∈ p.edges := by
      intro p
      simpa [Sym2.eq_swap] using hb p.reverse
    have hvc : v ∈ c.support := Walk.fst_mem_support_of_mem_edges c he
    refine reachable_deleteEdges_iff_exists_cycle.aux hb' (c.rotate v hvc) (hc.isTrail.rotate hvc)
      ?_ (Walk.start_mem_support _)
    rwa [(c.rotate_edges v hvc).mem_iff, Sym2.eq_swap]
/-
**SimpleGraph.isBridge_iff_forall_cycle_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：isBridge_iff_forall_cycle_notMem {e : Sym2 V} (he : e in G.edgeSet) : G.Is
Bridge e ↔ forall ⦃u : V⦄ (p : G.Walk u u), p.IsCycle -> e ∉ p.edges
参数：he : e in G.edgeSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBridge_iff_forall_cycle_notMem {e : Sym2 V} (he : e ∈ G.edgeSet) :
    G.IsBridge e ↔ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → e ∉ p.edges := by
  obtain ⟨v, w⟩ := e
  contrapose
  simp_all [isBridge_iff, ← adj_and_reachable_delete_edges_iff_exists_cycle]

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_adj_and_forall_cycle_notMem := isBridge_iff_forall_cycle_notMem
/-
**SimpleGraph.IsBridge.notMem_edges_of_isCycle** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.IsBridge`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {e : Sym2 V} {u : V} {p : G.Walk u u}, 
G.IsBridge e → p.IsCycle → e ∉ p.edges
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.isBridge_iff_forall_cycle_notMem`：isBridge_iff_forall_cycle_
notMem {e : Sym2 V} (he : e in G.edgeSet) : G.IsBridge e ↔ forall ⦃u : V⦄ (p : G
.Walk u u), p.IsCycle -> e ∉ p.edg…
· 使用定理 `SimpleGraph.Walk.edges_subset_edgeSet`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
-/
lemma IsBridge.notMem_edges_of_isCycle {e : Sym2 V} {u : V} {p : G.Walk u u}
    (he : G.IsBridge e) (hp : p.IsCycle) : e ∉ p.edges :=
  fun hep ↦ (isBridge_iff_forall_cycle_notMem <| p.edges_subset_edgeSet hep).mp he _ hp hep

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_mem_and_forall_cycle_notMem := isBridge_iff_forall_cycle_notMem

/-- Deleting a non-bridge edge from a connected graph preserves connectedness. -/
/-
**SimpleGraph.Connected.connected_delete_edge_of_not_isBridge** 是 Mathlib 中的一个定理
，位于命名空间 `SimpleGraph.Connected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V}, G.Connected → ∀ {x y : V}, ¬G.IsBridge
 s(x, y) → (G.deleteEdges {s(x, y)}).Connected
参数：x, y；G.deleteEdges {s(x, y)}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em'`：em' (p : Prop) : ¬p ∨ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.deleteEdges.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (s : 
Set (Sym2 V)), G.deleteEdges s = G \ SimpleGraph.fromEdgeSet s
· 使用定理 `Disjoint.sdiff_eq_left`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlg
ebra α] {a b : α}, Disjoint a b → a \ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.connected_iff_exists_forall_reachable`：connected_iff_exists_
forall_reachable : G.Connected ↔ exists v, forall w, G.Reachable v w
· 使用定理 `SimpleGraph.Connected.exists_isPath`：∀ {V : Type u} {G : SimpleGraph V},
 G.Connected → ∀ (u v : V), ∃ p, p.IsPath
· 使用定理 `SimpleGraph.Walk.snd_mem_support_of_mem_edges`：snd_mem_support_of_mem_ed
ges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) : u in p.support
· 使用引理 `SimpleGraph.Walk.endpoint_notMem_support_takeUntil`：endpoint_notMem_supp
ort_takeUntil {p : G.Walk u v} (hp : p.IsPath) (hw : w in p.support) (h : v != w
) : v ∉ (p.takeUntil w hw).support
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `SimpleGraph.Walk.fst_mem_support_of_mem_edges`：fst_mem_support_of_mem_ed
ges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) : t in p.support
· 使用定理 `SimpleGraph.Reachable.trans`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V}, G.Reachable u v → G.Reachable v w → G.Reachable u w
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u

--- 原说明 ---
Deleting a non-bridge edge from a connected graph preserves connectedness.
-/
lemma Connected.connected_delete_edge_of_not_isBridge (hG : G.Connected) {x y : V}
    (h : ¬ G.IsBridge s(x, y)) : (G.deleteEdges {s(x, y)}).Connected := by
  classical
  simp only [isBridge_iff, not_not] at h
  obtain hxy | hxy := em' <| G.Adj x y
  · rwa [deleteEdges, Disjoint.sdiff_eq_left (by simpa)]
  refine (connected_iff_exists_forall_reachable _).2 ⟨x, fun w ↦ ?_⟩
  obtain ⟨P, hP⟩ := hG.exists_isPath w x
  obtain heP | heP := em' <| s(x, y) ∈ P.edges
  · exact ⟨(P.toDeleteEdges {s(x, y)} (by grind)).reverse⟩
  have hyP := P.snd_mem_support_of_mem_edges heP
  let P₁ := P.takeUntil y hyP
  have hxP₁ := Walk.endpoint_notMem_support_takeUntil hP hyP hxy.ne
  have heP₁ : s(x, y) ∉ P₁.edges := fun h ↦ hxP₁ <| P₁.fst_mem_support_of_mem_edges h
  exact h.trans (.symm ⟨P₁.toDeleteEdges {s(x, y)} (by grind)⟩)
/-
**SimpleGraph.IsBridge.anti** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsBridge`。
形式化陈述：∀ {V : Type u} {G G' : SimpleGraph V} {e : Sym2 V}, G ≤ G' → G'.IsBridge e
 → G.IsBridge e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isBridge_iff`：isBridge_iff {u v : V} : G.IsBridge s(u, v) ↔ 
¬ (G.deleteEdges {s(u, v)}).Reachable u v
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.Reachable.mono`：∀ {V : Type u} {u v : V} {G G' : SimpleGraph
 V}, G ≤ G' → G.Reachable u v → G'.Reachable u v
· 使用引理 `SimpleGraph.deleteEdges_mono`：deleteEdges_mono (h : G <= H) : G.deleteEd
ges s <= H.deleteEdges s
-/
theorem IsBridge.anti {G' : SimpleGraph V} {e : Sym2 V} (hG : G ≤ G') (h : G'.IsBridge e) :
    G.IsBridge e := by obtain ⟨a, b⟩ := e; rw [isBridge_iff] at ⊢ h; grw [hG]; assumption

@[deprecated (since := "2026-05-16")] alias IsBridge.anti_of_mem_edgeSet := IsBridge.anti
/-
**SimpleGraph.isBridge_sup_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, (G ⊔ SimpleGraph.edge u v).I
sBridge s(u, v) ↔ G.IsBridge s(u, v)
参数：G ⊔ SimpleGraph.edge u v；u, v；u, v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.deleteEdges_sup`：∀ {V : Type u_1} (G H : SimpleGraph V) (s :
 Set (Sym2 V)), (G ⊔ H).deleteEdges s = G.deleteEdges s ⊔ H.deleteEdges s
· 使用定理 `SimpleGraph.deleteEdges_edge`：∀ {V : Type u_1} {u v : V} {s : Set (Sym2 
V)}, s(u, v) ∈ s → (SimpleGraph.edge u v).deleteEdges s = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isBridge_sup_edge : (G ⊔ edge u v).IsBridge s(u, v) ↔ G.IsBridge s(u, v) := by
  simp [isBridge_iff, deleteEdges_sup]
/-
**SimpleGraph.isBridge_deleteEdges_singleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {e : Sym2 V}, (G.deleteEdges {e}).IsBri
dge e ↔ G.IsBridge e
参数：G.deleteEdges {e}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.deleteEdges_deleteEdges`：deleteEdges_deleteEdges (s s' : Set
 (Sym2 V)) : (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s union s')
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isBridge_deleteEdges_singleton {e : Sym2 V} :
    (G.deleteEdges {e}).IsBridge e ↔ G.IsBridge e := by
  induction e with | h u v; simp [isBridge_iff]

@[deprecated "Use `isBridge_sup_edge` and `IsBridge.of_not_reachable`" (since := "2026-06-04")]
/-
**SimpleGraph.IsBridge.sup_edge_of_not_reachable** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.IsBridge`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, ¬G.Reachable u v → (G ⊔ Simp
leGraph.edge u v).IsBridge s(u, v)
参数：G ⊔ SimpleGraph.edge u v；u, v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.isBridge_sup_edge`：∀ {V : Type u} {G : SimpleGraph V} {u v :
 V}, (G ⊔ SimpleGraph.edge u v).IsBridge s(u, v) ↔ G.IsBridge s(u, v)
· 使用定理 `SimpleGraph.IsBridge.of_not_reachable`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V}, ¬G.Reachable u v → G.IsBridge s(u, v)
-/
theorem IsBridge.sup_edge_of_not_reachable {u v : V} (h : ¬G.Reachable u v) :
    (G ⊔ edge u v).IsBridge s(u, v) := isBridge_sup_edge.mpr (of_not_reachable h)

@[deprecated (since := "2026-03-18")]
alias IsBridge.sup_fromEdgeSet_of_not_reachable := IsBridge.sup_edge_of_not_reachable

/-- Connecting two unreachable vertices by an edge preserves existing bridges,
provided the bridge is already an edge. -/
/-
**SimpleGraph.IsBridge.sup_edge_of_not_reachable_of_isBridge** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph.IsBridge`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {e : Sym2 V},   ¬G.Reachable 
u v → G.IsBridge e → e ∈ G.edgeSet → (G ⊔ SimpleGraph.edge u v).IsBridge e
参数：G ⊔ SimpleGraph.edge u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.isBridge_iff_forall_cycle_notMem`：isBridge_iff_forall_cycle_
notMem {e : Sym2 V} (he : e in G.edgeSet) : G.IsBridge e ↔ forall ⦃u : V⦄ (p : G
.Walk u u), p.IsCycle -> e ∉ p.edg…
· 使用定理 `SimpleGraph.edgeSet_mono`：∀ {V : Type u} {G₁ G₂ : SimpleGraph V}, G₁ ≤ G
₂ → G₁.edgeSet ⊆ G₂.edgeSet
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `SimpleGraph.Walk.edges_subset_edgeSet`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
· 使用定理 `SimpleGraph.edgeSet_sup`：edgeSet_sup : (G₁ ⊔ G₂).edgeSet = G₁.edgeSet un
ion G₂.edgeSet
· 使用定理 `SimpleGraph.Reachable.mono`：∀ {V : Type u} {u v : V} {G G' : SimpleGraph
 V}, G ≤ G' → G.Reachable u v → G'.Reachable u v
· 使用定理 `sdiff_le_iff'`：sdiff_le_iff' [GeneralizedCoheytingAlgebra α] {a b c : α}
 : a \ b <= c ↔ a <= c ⊔ b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle`：adj_and_rea
chable_delete_edges_iff_exists_cycle {v w : V} : G.Adj v w ∧ (G.deleteEdges {s(v
, w)}).Reachable v w ↔ exists (u : V) (p : G.Walk…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `SimpleGraph.edgeSet_edge`：edgeSet_edge (v w : V) : (edge v w).edgeSet = 
{s(v, w)} \ Sym2.diagSet
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.IsCycle.transfer`：∀ {V : Type u} {G : SimpleGraph V} {u
 : V} {H : SimpleGraph V} {q : G.Walk u u},   q.IsCycle → ∀ (hq : ∀ e ∈ q.edges,
 e ∈ H.edgeSet), (q.tra…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.edges_transfer`：edges_transfer (hp) : (p.transfer H hp)
.edges = p.edges

--- 原说明 ---
Connecting two unreachable vertices by an edge preserves existing bridges,
provided the bridge is already an edge.
-/
theorem IsBridge.sup_edge_of_not_reachable_of_isBridge {u v : V} {e : Sym2 V}
    (h : ¬G.Reachable u v) (hb : G.IsBridge e) (he : e ∈ G.edgeSet) :
    (G ⊔ edge u v).IsBridge e := by
  refine (isBridge_iff_forall_cycle_notMem (edgeSet_mono le_sup_left he)).mpr ?_
  refine fun w p hp hpe ↦ (isBridge_iff_forall_cycle_notMem he).mp hb
    (p.transfer G fun e' he' ↦ ?_) (hp.transfer _) (Walk.edges_transfer p _ ▸ hpe)
  refine edgeSet_sup .. ▸ Walk.edges_subset_edgeSet _ he' |>.elim id fun h' ↦ h ?_ |>.elim
  exact .mono (sdiff_le_iff'.mpr le_rfl) <|
    adj_and_reachable_delete_edges_iff_exists_cycle.mpr ⟨_, p, by simp_all⟩ |>.right

@[deprecated (since := "2026-03-18")]
alias IsBridge.sup_fromEdgeSet_of_not_reachable_of_isBridge :=
  IsBridge.sup_edge_of_not_reachable_of_isBridge

end BridgeEdges

/-!
### 2-reachability

In this section, we prove results about 2-connected components of a graph, but without naming them.
-/

namespace Walk
variable {u v x y : V} {w : G.Walk u v}

/-- A walk between two vertices separated by a set of edges must go through one of those edges. -/
/-
**SimpleGraph.Walk.exists_mem_edges_of_not_reachable_deleteEdges** 是 Mathlib 中的一
个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：exists_mem_edges_of_not_reachable_deleteEdges (w : G.Walk u v) {s : Set (S
ym2 V)} (huv : ¬ (G.deleteEdges s).Reachable u v) : exists e in s, e in w.edges
参数：w : G.Walk u v；Sym2 V；huv : ¬ (G.deleteEdges s).Reachable u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a

--- 原说明 ---
A walk between two vertices separated by a set of edges must go through one of t
hose edges.
-/
lemma exists_mem_edges_of_not_reachable_deleteEdges (w : G.Walk u v) {s : Set (Sym2 V)}
    (huv : ¬ (G.deleteEdges s).Reachable u v) : ∃ e ∈ s, e ∈ w.edges := by
  contrapose! huv; exact ⟨w.toDeleteEdges _ fun _ ↦ imp_not_comm.1 <| huv _⟩

/-- A walk between two vertices separated by an edge must go through that edge. -/
/-
**SimpleGraph.Walk.mem_edges_of_not_reachable_deleteEdges** 是 Mathlib 中的一个引理，位于命
名空间 `SimpleGraph.Walk`。
形式化陈述：mem_edges_of_not_reachable_deleteEdges (w : G.Walk u v) {e : Sym2 V} (huv 
: ¬ (G.deleteEdges {e}).Reachable u v) : e in w.edges
参数：w : G.Walk u v；huv : ¬ (G.deleteEdges {e}).Reachable u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SimpleGraph.Walk.exists_mem_edges_of_not_reachable_deleteEdges`：exists_m
em_edges_of_not_reachable_deleteEdges (w : G.Walk u v) {s : Set (Sym2 V)} (huv :
 ¬ (G.deleteEdges s).Reachable u v) : exists e in s,…

--- 原说明 ---
A walk between two vertices separated by an edge must go through that edge.
-/
lemma mem_edges_of_not_reachable_deleteEdges (w : G.Walk u v) {e : Sym2 V}
    (huv : ¬ (G.deleteEdges {e}).Reachable u v) : e ∈ w.edges := by
  simpa using w.exists_mem_edges_of_not_reachable_deleteEdges huv

/-- A trail doesn't go through an edge that disconnects one of its endpoints from the endpoints of
the trail. -/
/-
**SimpleGraph.Walk.IsTrail.not_mem_edges_of_not_reachable** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v x y : V} {w : G.Walk u v},   w.IsT
rail → ¬(G.deleteEdges {s(x, y)}).Reachable u y → ¬(G.deleteEdges {s(x, y)}).Rea
chable v y → s(x, y) ∉ w.edges
参数：G.deleteEdges {s(x, y)}；G.deleteEdges {s(x, y)}；x, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsTrail.disjoint_edges_takeUntil_dropUntil`：∀ {V : Type
 u} {G : SimpleGraph V} {u v : V} [inst : DecidableEq V] {x : V} {w : G.Walk u v
},   w.IsTrail → ∀ (hx : x ∈ w.support), (w.takeU…
· 使用定理 `SimpleGraph.Walk.snd_mem_support_of_mem_edges`：snd_mem_support_of_mem_ed
ges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) : u in p.support
· 使用引理 `SimpleGraph.Walk.mem_edges_of_not_reachable_deleteEdges`：mem_edges_of_no
t_reachable_deleteEdges (w : G.Walk u v) {e : Sym2 V} (huv : ¬ (G.deleteEdges {e
}).Reachable u v) : e in w.edges
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.edges_reverse`：edges_reverse {u v : V} (p : G.Walk u v)
 : p.reverse.edges = p.edges.reverse

--- 原说明 ---
A trail doesn't go through an edge that disconnects one of its endpoints from th
e endpoints of
the trail.
-/
lemma IsTrail.not_mem_edges_of_not_reachable (hw : w.IsTrail)
    (huy : ¬ (G.deleteEdges {s(x, y)}).Reachable u y)
    (hvy : ¬ (G.deleteEdges {s(x, y)}).Reachable v y) : s(x, y) ∉ w.edges := by
  classical
  exact fun hxy ↦ hw.disjoint_edges_takeUntil_dropUntil (w.snd_mem_support_of_mem_edges hxy)
    ((w.takeUntil y _).mem_edges_of_not_reachable_deleteEdges huy)
    (by simpa using (w.dropUntil y _).reverse.mem_edges_of_not_reachable_deleteEdges hvy)

/-- A trail doesn't go through a vertex that is disconnected from its endpoints by an edge. -/
/-
**SimpleGraph.Walk.IsTrail.not_mem_support_of_not_reachable** 是 Mathlib 中的一个定理，位
于命名空间 `SimpleGraph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v x y : V} {w : G.Walk u v},   w.IsT
rail → ¬(G.deleteEdges {s(x, y)}).Reachable u y → ¬(G.deleteEdges {s(x, y)}).Rea
chable v y → y ∉ w.support
参数：G.deleteEdges {s(x, y)}；G.deleteEdges {s(x, y)}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsTrail.not_mem_edges_of_not_reachable`：∀ {V : Type u} 
{G : SimpleGraph V} {u v x y : V} {w : G.Walk u v},   w.IsTrail → ¬(G.deleteEdge
s {s(x, y)}).Reachable u y → ¬(G.deleteEdges …
· 使用定理 `SimpleGraph.Walk.edges_takeUntil_subset_edges`：edges_takeUntil_subset_ed
ges (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).edges subseteq p.e
dges
· 使用引理 `SimpleGraph.Walk.mem_edges_of_not_reachable_deleteEdges`：mem_edges_of_no
t_reachable_deleteEdges (w : G.Walk u v) {e : Sym2 V} (huv : ¬ (G.deleteEdges {e
}).Reachable u v) : e in w.edges

--- 原说明 ---
A trail doesn't go through a vertex that is disconnected from its endpoints by a
n edge.
-/
lemma IsTrail.not_mem_support_of_not_reachable (hw : w.IsTrail)
    (huy : ¬ (G.deleteEdges {s(x, y)}).Reachable u y)
    (hvy : ¬ (G.deleteEdges {s(x, y)}).Reachable v y) : y ∉ w.support := by
  classical
  exact fun hy ↦ hw.not_mem_edges_of_not_reachable huy hvy <| w.edges_takeUntil_subset_edges hy <|
    mem_edges_of_not_reachable_deleteEdges (w.takeUntil y hy) huy

/-- A trail doesn't go through any leaf vertex, except possibly at its endpoints. -/
/-
**SimpleGraph.Walk.IsTrail.not_mem_support_of_subsingleton_neighborSet** 是 Mathl
ib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v x : V} {w : G.Walk u v},   w.IsTra
il → x ≠ u → x ≠ v → (G.neighborSet x).Subsingleton → x ∉ w.support
参数：G.neighborSet x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.adj_of_mem_walk_support`：adj_of_mem_walk_support {G : Simple
Graph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) {x : V} (hx : x in p.support) 
: exists y in p.support, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SimpleGraph.Walk.IsTrail.not_mem_support_of_not_reachable`：∀ {V : Type u
} {G : SimpleGraph V} {u v x y : V} {w : G.Walk u v},   w.IsTrail → ¬(G.deleteEd
ges {s(x, y)}).Reachable u y → ¬(G.deleteEdges …
· 使用引理 `SimpleGraph.Walk.snd_reverse`：snd_reverse (p : G.Walk u v) : p.reverse.s
nd = p.penultimate
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用引理 `SimpleGraph.Walk.not_nil_of_ne`：not_nil_of_ne {p : G.Walk v w} : v != w 
-> ¬ p.Nil

--- 原说明 ---
A trail doesn't go through any leaf vertex, except possibly at its endpoints.
-/
lemma IsTrail.not_mem_support_of_subsingleton_neighborSet (hw : w.IsTrail) (hxu : x ≠ u)
    (hxv : x ≠ v) (hx : (G.neighborSet x).Subsingleton) : x ∉ w.support := by
  rintro hxw
  obtain ⟨y, -, hxy⟩ := adj_of_mem_walk_support w (by rintro ⟨⟩; simp_all) hxw
  refine hw.not_mem_support_of_not_reachable (x := y) ?_ ?_ hxw <;>
  · rintro ⟨p⟩
    obtain ⟨hx₂, -, hy₂⟩ : G.Adj x p.penultimate ∧ _ ∧ ¬p.penultimate = y := by
      simpa using p.reverse.adj_snd (not_nil_of_ne ‹_›)
    exact hy₂ <| hx hx₂ hxy

end Walk

/-- Removing leaves from a connected graph keeps it connected. -/
/-
**SimpleGraph.Preconnected.induce_of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Preconnected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V},   G.Preconnected → ∀ {s : Set V}, (∀ v
 ∉ s, (G.neighborSet v).Subsingleton) → (SimpleGraph.induce s G).Preconnected
参数：∀ v ∉ s, (G.neighborSet v).Subsingleton；SimpleGraph.induce s G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Preconnected.exists_isPath`：∀ {V : Type u} {G : SimpleGraph 
V}, G.Preconnected → ∀ (u v : V), ∃ p, p.IsPath
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `SimpleGraph.Walk.IsTrail.not_mem_support_of_subsingleton_neighborSet`：∀ 
{V : Type u} {G : SimpleGraph V} {u v x : V} {w : G.Walk u v},   w.IsTrail → x ≠
 u → x ≠ v → (G.neighborSet x).Subsingleton → x ∉ w.suppor…
· 使用定理 `SimpleGraph.Walk.IsPath.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.IsTrail
· 使用定理 `SimpleGraph.Walk.start_mem_support`：start_mem_support {u v : V} (p : G.W
alk u v) : u in p.support
· 使用定理 `SimpleGraph.Walk.end_mem_support`：end_mem_support {u v : V} (p : G.Walk 
u v) : v in p.support
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
Removing leaves from a connected graph keeps it connected.
-/
lemma Preconnected.induce_of_degree_eq_one (hG : G.Preconnected) {s : Set V}
    (hs : ∀ v ∉ s, (G.neighborSet v).Subsingleton) : (G.induce s).Preconnected := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨p, hp⟩ := hG.exists_isPath u v
  constructor
  convert! p.induce s _
  rintro w hwp
  by_contra hws
  exact hp.not_mem_support_of_subsingleton_neighborSet (by grind) (by grind) (hs _ hws) hwp

end SimpleGraph

