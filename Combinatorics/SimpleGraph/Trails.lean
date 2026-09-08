/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!

# Trails and Eulerian trails

This module contains additional theory about trails, including Eulerian trails (also known
as Eulerian circuits).

## Main definitions

* `SimpleGraph.Walk.IsEulerian` is the predicate that a trail is an Eulerian trail.
* `SimpleGraph.Walk.IsTrail.even_countP_edges_iff` gives a condition on the number of edges
  in a trail that can be incident to a given vertex.
* `SimpleGraph.Walk.IsEulerian.even_degree_iff` gives a condition on the degrees of vertices
  when there exists an Eulerian trail.
* `SimpleGraph.Walk.IsEulerian.card_odd_degree` gives the possible numbers of odd-degree
  vertices when there exists an Eulerian trail.

## TODO

* Prove that there exists an Eulerian trail when the conclusion to
  `SimpleGraph.Walk.IsEulerian.card_odd_degree` holds.

## Tags

Eulerian trails

-/

@[expose] public section


namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace Walk

/-- The edges of a trail as a finset, since each edge in a trail appears exactly once. -/
/-
**SimpleGraph.Walk.IsTrail.edgesFinset** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Wa
lk.IsTrail`。
形式化陈述：{V : Type u_1} → {G : SimpleGraph V} → {u v : V} → {p : G.Walk u v} → p.Is
Trail → Finset (Sym2 V)
参数：Sym2 V。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsTrail.edges_nodup`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V} {p : G.Walk u v}, p.IsTrail → p.edges.Nodup

--- 原说明 ---
The edges of a trail as a finset, since each edge in a trail appears exactly onc
e.
-/
abbrev IsTrail.edgesFinset {u v : V} {p : G.Walk u v} (h : p.IsTrail) : Finset (Sym2 V) :=
  ⟨p.edges, h.edges_nodup⟩

variable [DecidableEq V]
/-
**SimpleGraph.Walk.IsTrail.even_countP_edges_iff** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : DecidableEq V] {u v : V} {p :
 G.Walk u v},   p.IsTrail → ∀ (x : V), Even (List.countP (fun e => decide (x ∈ e
)) p.edges) ↔ u ≠ v → x ≠ u ∧ x ≠ v
参数：x : V；List.countP (fun e => decide (x ∈ e)) p.edges。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.countP_cons`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : List α}, 
  List.countP p (a :: l) = List.countP p l + if p a = true then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Nat.even_add_one`：∀ {n : ℕ}, Even (n + 1) ↔ ¬Even n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.Walk.isTrail_cons`：isTrail_cons {u v w : V} (h : G.Adj u v) 
(p : G.Walk v w) : (cons h p).IsTrail ↔ p.IsTrail ∧ s(u, v) ∉ p.edges
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Std.Irrefl.irrefl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Irrefl 
r] (a : α), ¬r a a
· 使用定理 `SimpleGraph.loopless`：∀ {V : Type u} (self : SimpleGraph V), Std.Irrefl 
self.Adj
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem IsTrail.even_countP_edges_iff {u v : V} {p : G.Walk u v} (ht : p.IsTrail) (x : V) :
    Even (p.edges.countP fun e => x ∈ e) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  induction p with
  | nil => simp
  | cons huv p ih =>
    rw [isTrail_cons] at ht
    specialize ih ht.1
    simp only [List.countP_cons, Ne, edges_cons, Sym2.mem_iff]
    split_ifs with h
    · rw [decide_eq_true_eq] at h
      obtain (rfl | rfl) := h
      · rw [Nat.even_add_one, ih]
        simp only [huv.ne, imp_false, Ne, not_false_iff, true_and, not_forall,
          Classical.not_not, exists_prop, not_true, false_and,
          and_iff_right_iff_imp]
        rintro rfl rfl
        exact G.loopless.irrefl _ huv
      · have := huv.ne; grind
    · grind

/-- An *Eulerian trail* (also known as an "Eulerian path") is a walk
`p` that visits every edge exactly once.  The lemma `SimpleGraph.Walk.IsEulerian.IsTrail` shows
that these are trails.

Combine with `p.IsCircuit` to get an Eulerian circuit (also known as an "Eulerian cycle"). -/
/-
**SimpleGraph.Walk.IsEulerian** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：IsEulerian {u v : V} (p : G.Walk u v) : Prop
参数：p : G.Walk u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An *Eulerian trail* (also known as an "Eulerian path") is a walk
`p` that visits every edge exactly once.  The lemma `SimpleGraph.Walk.IsEulerian
.IsTrail` shows
that these are trails.

Combine with `p.IsCircuit` to get an Eulerian circuit (also known as an "Euleria
n cycle").
-/
def IsEulerian {u v : V} (p : G.Walk u v) : Prop :=
  ∀ e, e ∈ G.edgeSet → p.edges.count e = 1
/-
**SimpleGraph.Walk.IsEulerian.isTrail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k.IsEulerian`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : DecidableEq V] {u v : V} {p :
 G.Walk u v}, p.IsEulerian → p.IsTrail
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isTrail_def`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} (p : G.Walk u v), p.IsTrail ↔ p.edges.Nodup
· 使用定理 `List.nodup_iff_count_le_one`：nodup_iff_count_le_one [BEq α] [LawfulBEq α
] {l : List α} : Nodup l ↔ forall a, count a l <= 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `SimpleGraph.Walk.edges_subset_edgeSet`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.count_eq_zero_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBE
q α] {a : α} {l : List α}, a ∉ l → List.count a l = 0
-/
theorem IsEulerian.isTrail {u v : V} {p : G.Walk u v} (h : p.IsEulerian) : p.IsTrail := by
  rw [isTrail_def, List.nodup_iff_count_le_one]
  intro e
  by_cases he : e ∈ p.edges
  · exact (h e (edges_subset_edgeSet _ he)).le
  · simp [List.count_eq_zero_of_not_mem he]
/-
**SimpleGraph.Walk.IsEulerian.mem_edges_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk.IsEulerian`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : DecidableEq V] {u v : V} {p :
 G.Walk u v},   p.IsEulerian → ∀ {e : Sym2 V}, e ∈ p.edges ↔ e ∈ G.edgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.edges_subset_edgeSet`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem IsEulerian.mem_edges_iff {u v : V} {p : G.Walk u v} (h : p.IsEulerian) {e : Sym2 V} :
    e ∈ p.edges ↔ e ∈ G.edgeSet :=
  ⟨fun h => p.edges_subset_edgeSet h,
   fun he => by simpa [Nat.succ_le_iff] using (h e he).ge⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The edge set of an Eulerian graph is finite. -/
@[instance_reducible]
/-
**SimpleGraph.Walk.IsEulerian.fintypeEdgeSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGr
aph.Walk.IsEulerian`。
形式化陈述：{V : Type u_1} →   {G : SimpleGraph V} → [inst : DecidableEq V] → {u v : V
} → {p : G.Walk u v} → p.IsEulerian → Fintype ↑G.edgeSet
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsEulerian.isTrail`：∀ {V : Type u_1} {G : SimpleGraph V
} [inst : DecidableEq V] {u v : V} {p : G.Walk u v}, p.IsEulerian → p.IsTrail

--- 原说明 ---
The edge set of an Eulerian graph is finite.
-/
def IsEulerian.fintypeEdgeSet {u v : V} {p : G.Walk u v} (h : p.IsEulerian) :
    Fintype G.edgeSet :=
  Fintype.ofFinset h.isTrail.edgesFinset fun e => by
    simp only [Finset.mem_mk, Multiset.mem_coe, h.mem_edges_iff]
/-
**SimpleGraph.Walk.IsTrail.isEulerian_of_forall_mem** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : DecidableEq V] {u v : V} {p :
 G.Walk u v},   p.IsTrail → (∀ e ∈ G.edgeSet, e ∈ p.edges) → p.IsEulerian
参数：∀ e ∈ G.edgeSet, e ∈ p.edges。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Walk.IsTrail.edges_nodup`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V} {p : G.Walk u v}, p.IsTrail → p.edges.Nodup
-/
theorem IsTrail.isEulerian_of_forall_mem {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (hc : ∀ e, e ∈ G.edgeSet → e ∈ p.edges) : p.IsEulerian := fun e he =>
  List.count_eq_one_of_mem h.edges_nodup (hc e he)
/-
**SimpleGraph.Walk.isEulerian_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isEulerian_iff {u v : V} (p : G.Walk u v) : p.IsEulerian ↔ p.IsTrail ∧ for
all e, e in G.edgeSet -> e in p.edges
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsEulerian.isTrail`：∀ {V : Type u_1} {G : SimpleGraph V
} [inst : DecidableEq V] {u v : V} {p : G.Walk u v}, p.IsEulerian → p.IsTrail
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.IsEulerian.mem_edges_iff`：∀ {V : Type u_1} {G : SimpleG
raph V} [inst : DecidableEq V] {u v : V} {p : G.Walk u v},   p.IsEulerian → ∀ {e
 : Sym2 V}, e ∈ p.edges ↔ e ∈ G…
· 使用定理 `SimpleGraph.Walk.IsTrail.isEulerian_of_forall_mem`：∀ {V : Type u_1} {G :
 SimpleGraph V} [inst : DecidableEq V] {u v : V} {p : G.Walk u v},   p.IsTrail →
 (∀ e ∈ G.edgeSet, e ∈ p.edges) → p.IsE…
-/
theorem isEulerian_iff {u v : V} (p : G.Walk u v) :
    p.IsEulerian ↔ p.IsTrail ∧ ∀ e, e ∈ G.edgeSet → e ∈ p.edges := by
  constructor
  · intro h
    exact ⟨h.isTrail, fun _ => h.mem_edges_iff.mpr⟩
  · rintro ⟨h, hl⟩
    exact h.isEulerian_of_forall_mem hl
/-
**SimpleGraph.Walk.IsTrail.isEulerian_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Walk.IsTrail`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : DecidableEq V] {u v : V} {p :
 G.Walk u v},   p.IsTrail → (p.IsEulerian ↔ p.edgeSet = G.edgeSet)
参数：p.IsEulerian ↔ p.edgeSet = G.edgeSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `SimpleGraph.Walk.edges_subset_edgeSet`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isEulerian_iff`：isEulerian_iff {u v : V} (p : G.Walk u 
v) : p.IsEulerian ↔ p.IsTrail ∧ forall e, e in G.edgeSet -> e in p.edges
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsTrail.isEulerian_iff {u v : V} {p : G.Walk u v} (hp : p.IsTrail) :
    p.IsEulerian ↔ p.edgeSet = G.edgeSet :=
  ⟨fun h ↦ Set.Subset.antisymm p.edges_subset_edgeSet (p.isEulerian_iff.mp h).2,
   fun h ↦ p.isEulerian_iff.mpr ⟨hp, by simp [← h]⟩⟩
/-
**SimpleGraph.Walk.IsEulerian.edgeSet_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk.IsEulerian`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : DecidableEq V] {u v : V} {p :
 G.Walk u v},   p.IsEulerian → p.edgeSet = G.edgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.IsTrail.isEulerian_iff`：∀ {V : Type u_1} {G : SimpleGra
ph V} [inst : DecidableEq V] {u v : V} {p : G.Walk u v},   p.IsTrail → (p.IsEule
rian ↔ p.edgeSet = G.edgeSet)
· 使用定理 `SimpleGraph.Walk.IsEulerian.isTrail`：∀ {V : Type u_1} {G : SimpleGraph V
} [inst : DecidableEq V] {u v : V} {p : G.Walk u v}, p.IsEulerian → p.IsTrail
-/
theorem IsEulerian.edgeSet_eq {u v : V} {p : G.Walk u v} (h : p.IsEulerian) :
    p.edgeSet = G.edgeSet := by
  rwa [← h.isTrail.isEulerian_iff]

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.Walk.IsEulerian.edgesFinset_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk.IsEulerian`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : DecidableEq V] [inst_1 : Fint
ype ↑G.edgeSet] {u v : V} {p : G.Walk u v}   (h : p.IsEulerian), ⋯.edgesFinset =
 G.edgeFinset
参数：h : p.IsEulerian。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `SimpleGraph.Walk.IsEulerian.isTrail`：∀ {V : Type u_1} {G : SimpleGraph V
} [inst : DecidableEq V] {u v : V} {p : G.Walk u v}, p.IsEulerian → p.IsTrail
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.IsTrail.edges_nodup`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V} {p : G.Walk u v}, p.IsTrail → p.edges.Nodup
· 使用定理 `SimpleGraph.Walk.IsEulerian.mem_edges_iff`：∀ {V : Type u_1} {G : SimpleG
raph V} [inst : DecidableEq V] {u v : V} {p : G.Walk u v},   p.IsEulerian → ∀ {e
 : Sym2 V}, e ∈ p.edges ↔ e ∈ G…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsEulerian.edgesFinset_eq [Fintype G.edgeSet] {u v : V} {p : G.Walk u v}
    (h : p.IsEulerian) : h.isTrail.edgesFinset = G.edgeFinset := by
  ext e
  simp [h.mem_edges_iff]
/-
**SimpleGraph.Walk.IsEulerian.even_degree_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk.IsEulerian`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : DecidableEq V] {x u v : V} {p
 : G.Walk u v},   p.IsEulerian → ∀ [inst : Fintype V] [inst_1 : DecidableRel G.A
dj], Even (G.degree x) ↔ u ≠ v → x ≠ u ∧ x ≠ v
参数：G.degree x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_countP`：coe_countP (l : List α) : countP p l = l.countP p
· 使用定理 `Multiset.countP_eq_card_filter`：countP_eq_card_filter (s) : countP p s =
 card (filter p s)
· 使用定理 `SimpleGraph.card_incidenceFinset_eq_degree`：card_incidenceFinset_eq_degr
ee [DecidableEq V] : #(G.incidenceFinset v) = G.degree v
· 使用定理 `SimpleGraph.Walk.IsEulerian.isTrail`：∀ {V : Type u_1} {G : SimpleGraph V
} [inst : DecidableEq V] {u v : V} {p : G.Walk u v}, p.IsEulerian → p.IsTrail
· 使用定理 `SimpleGraph.Walk.IsEulerian.edgesFinset_eq`：∀ {V : Type u_1} {G : Simple
Graph V} [inst : DecidableEq V] [inst_1 : Fintype ↑G.edgeSet] {u v : V} {p : G.W
alk u v}   (h : p.IsEulerian), ⋯…
· 使用定理 `SimpleGraph.incidenceFinset_eq_filter`：incidenceFinset_eq_filter [Decida
bleEq V] [Fintype G.edgeSet] : G.incidenceFinset v = {e in G.edgeFinset | v in e
}
· 使用定理 `SimpleGraph.Walk.IsTrail.even_countP_edges_iff`：∀ {V : Type u_1} {G : Si
mpleGraph V} [inst : DecidableEq V] {u v : V} {p : G.Walk u v},   p.IsTrail → ∀ 
(x : V), Even (List.countP (fun e =>…
-/
theorem IsEulerian.even_degree_iff {x u v : V} {p : G.Walk u v} (ht : p.IsEulerian) [Fintype V]
    [DecidableRel G.Adj] : Even (G.degree x) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
  convert! ht.isTrail.even_countP_edges_iff x
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter, ← card_incidenceFinset_eq_degree]
  change Multiset.card _ = _
  congr 1
  convert_to! _ = (ht.isTrail.edgesFinset.filter (x ∈ ·)).val
  rw [ht.edgesFinset_eq, G.incidenceFinset_eq_filter x]
/-
**SimpleGraph.Walk.IsEulerian.card_filter_odd_degree** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.Walk.IsEulerian`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : DecidableEq V] [inst_1 : Fint
ype V] [inst_2 : DecidableRel G.Adj] {u v : V}   {p : G.Walk u v}, p.IsEulerian 
→ ∀ {s : Finset V}, s = {v | Odd (G.degree v)} → s.card = 0 ∨ s.card = 2
参数：G.degree v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SimpleGraph.Walk.IsEulerian.even_degree_iff`：∀ {V : Type u_1} {G : Simpl
eGraph V} [inst : DecidableEq V] {x u v : V} {p : G.Walk u v},   p.IsEulerian → 
∀ [inst : Fintype V] [inst_1 : De…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Finset.filter_false`：∀ {α : Type u_1} {h : DecidablePred fun x => False}
 (s : Finset α), {x ∈ s | False} = ∅
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsEulerian.card_filter_odd_degree [Fintype V] [DecidableRel G.Adj] {u v : V}
    {p : G.Walk u v} (ht : p.IsEulerian) {s} (h : s = ({ v | Odd (G.degree v) } : Finset V)) :
    s.card = 0 ∨ s.card = 2 := by
  subst s
  simp only [← Nat.not_even_iff_odd, Finset.card_eq_zero]
  simp only [ht.even_degree_iff, Ne, not_forall, not_and, Classical.not_not, exists_prop]
  obtain rfl | hn := eq_or_ne u v
  · simp
  · right
    convert_to _ = ({u, v} : Finset V).card
    · simp [hn]
    · congr
      ext x
      simp [hn, imp_iff_not_or]
/-
**SimpleGraph.Walk.IsEulerian.card_odd_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk.IsEulerian`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [inst : DecidableEq V] [inst_1 : Fint
ype V] [inst_2 : DecidableRel G.Adj] {u v : V}   {p : G.Walk u v}, p.IsEulerian 
→ Fintype.card ↑{v | Odd (G.degree v)} = 0 ∨ Fintype.card ↑{v | Odd (G.degree v)
} = 2
参数：G.degree v；G.degree v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `SimpleGraph.Walk.IsEulerian.card_filter_odd_degree`：∀ {V : Type u_1} {G 
: SimpleGraph V} [inst : DecidableEq V] [inst_1 : Fintype V] [inst_2 : Decidable
Rel G.Adj] {u v : V}   {p : G.Walk u v},…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.toFinset_ofPred`：toFinset_ofPred [Fintype α] (p : α -> Prop) [Decida
blePred p] [Fintype { x | p x }] : Set.toFinset {x | p x} = Finset.univ.filter p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsEulerian.card_odd_degree [Fintype V] [DecidableRel G.Adj] {u v : V} {p : G.Walk u v}
    (ht : p.IsEulerian) :
    Fintype.card { v | Odd (G.degree v) } = 0 ∨ Fintype.card { v | Odd (G.degree v) } = 2 := by
  rw [← Set.toFinset_card]
  apply IsEulerian.card_filter_odd_degree ht
  simp

end Walk

end SimpleGraph

