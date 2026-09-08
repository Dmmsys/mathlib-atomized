/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity

/-!
# Triangles in graphs

A *triangle* in a simple graph is a `3`-clique, namely a set of three vertices that are
pairwise adjacent.

This module defines and proves properties about triangles in simple graphs.

## Main declarations

* `SimpleGraph.FarFromTriangleFree`: Predicate for a graph such that one must remove a lot of edges
  from it for it to become triangle-free. This is the crux of the Triangle Removal Lemma.

## TODO

* Generalise `FarFromTriangleFree` to other graphs, to state and prove the Graph Removal Lemma.
-/

@[expose] public section

open Finset Nat
open Fintype (card)

namespace SimpleGraph

variable {α β 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {G H : SimpleGraph α} {ε δ : 𝕜}

section LocallyLinear

/-- A graph has edge-disjoint triangles if each edge belongs to at most one triangle. -/
/-
**SimpleGraph.EdgeDisjointTriangles** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：EdgeDisjointTriangles (G : SimpleGraph α) : Prop
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph has edge-disjoint triangles if each edge belongs to at most one triangle
.
-/
def EdgeDisjointTriangles (G : SimpleGraph α) : Prop :=
  (G.cliqueSet 3).Pairwise fun x y ↦ (x ∩ y : Set α).Subsingleton

/-- A graph is locally linear if each edge belongs to exactly one triangle. -/
/-
**SimpleGraph.LocallyLinear** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：LocallyLinear (G : SimpleGraph α) : Prop
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph is locally linear if each edge belongs to exactly one triangle.
-/
def LocallyLinear (G : SimpleGraph α) : Prop :=
  G.EdgeDisjointTriangles ∧ ∀ ⦃x y⦄, G.Adj x y → ∃ s, G.IsNClique 3 s ∧ x ∈ s ∧ y ∈ s
/-
**SimpleGraph.LocallyLinear.edgeDisjointTriangles** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.LocallyLinear`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α}, G.LocallyLinear → G.EdgeDisjointTria
ngles
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected lemma LocallyLinear.edgeDisjointTriangles : G.LocallyLinear → G.EdgeDisjointTriangles :=
  And.left

nonrec lemma EdgeDisjointTriangles.mono (h : G ≤ H) (hH : H.EdgeDisjointTriangles) :
    G.EdgeDisjointTriangles := hH.mono <| cliqueSet_mono h
/-
**SimpleGraph.edgeDisjointTriangles_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1}, ⊥.EdgeDisjointTriangles
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.cliqueSet_bot`：cliqueSet_bot (hn : 1 < n) : (⊥ : SimpleGraph
 α).cliqueSet n = ∅
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
@[simp] lemma edgeDisjointTriangles_bot : (⊥ : SimpleGraph α).EdgeDisjointTriangles := by
  simp [EdgeDisjointTriangles]
/-
**SimpleGraph.locallyLinear_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1}, ⊥.LocallyLinear
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma locallyLinear_bot : (⊥ : SimpleGraph α).LocallyLinear := by simp [LocallyLinear]
/-
**SimpleGraph.EdgeDisjointTriangles.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.E
dgeDisjointTriangles`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} (f : α ↪ β),   G.EdgeD
isjointTriangles → (SimpleGraph.map (⇑f) G).EdgeDisjointTriangles
参数：f : α ↪ β；SimpleGraph.map (⇑f) G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.EdgeDisjointTriangles.eq_1`：∀ {α : Type u_1} (G : SimpleGrap
h α),   G.EdgeDisjointTriangles = (G.cliqueSet 3).Pairwise fun x y => (↑x ∩ ↑y).
Subsingleton
· 使用定理 `SimpleGraph.cliqueSet_map`：cliqueSet_map (hn : n != 1) (G : SimpleGraph 
α) (f : α ↪ β) : (G.map f).cliqueSet n = map f '' G.cliqueSet n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.InjOn.pairwise_image`：∀ {α : Type u_1} {ι : Type u_4} {r : α → α → P
rop} {f : ι → α} {s : Set ι},   Set.InjOn f s → ((f '' s).Pairwise r ↔ s.Pairwis
e (Function.on…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finset.map_injective`：map_injective (f : α ↪ β) : Injective (map f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `Finset.map_inter`：map_inter [DecidableEq α] [DecidableEq β] {f : α ↪ β} 
(s₁ s₂ : Finset α) : (s₁ inter s₂).map f = s₁.map f inter s₂.map f
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
-/
lemma EdgeDisjointTriangles.map (f : α ↪ β) (hG : G.EdgeDisjointTriangles) :
    (G.map f).EdgeDisjointTriangles := by
  rw [EdgeDisjointTriangles, cliqueSet_map (by simp : 3 ≠ 1),
    (Finset.map_injective f).injOn.pairwise_image]
  classical
  rintro s hs t ht hst
  dsimp [Function.onFun]
  rw [← coe_inter, ← map_inter, coe_map, coe_inter]
  exact (hG hs ht hst).image _
/-
**SimpleGraph.LocallyLinear.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.LocallyLi
near`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} (f : α ↪ β),   G.Local
lyLinear → (SimpleGraph.map (⇑f) G).LocallyLinear
参数：f : α ↪ β；SimpleGraph.map (⇑f) G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.EdgeDisjointTriangles.map`：∀ {α : Type u_1} {β : Type u_2} {
G : SimpleGraph α} (f : α ↪ β),   G.EdgeDisjointTriangles → (SimpleGraph.map (⇑f
) G).EdgeDisjointTriangles
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.IsNClique.map`：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGr
aph α} {n : ℕ} {s : Finset α},   G.IsNClique n s → ∀ {f : α ↪ β}, (SimpleGraph.m
ap (⇑f) G).IsNC…
· 使用定理 `Finset.mem_map_of_mem`：mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a
 in s -> f a in s.map f
-/
lemma LocallyLinear.map (f : α ↪ β) (hG : G.LocallyLinear) : (G.map f).LocallyLinear := by
  refine ⟨hG.1.map _, ?_⟩
  rintro _ _ ⟨-, a, b, h, rfl, rfl⟩
  obtain ⟨s, hs, ha, hb⟩ := hG.2 h
  exact ⟨s.map f, hs.map, mem_map_of_mem _ ha, mem_map_of_mem _ hb⟩
/-
**SimpleGraph.locallyLinear_comap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph β} {e : α ≃ β},   (Simple
Graph.comap (⇑e) G).LocallyLinear ↔ G.LocallyLinear
参数：SimpleGraph.comap (⇑e) G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.comap_map_eq`：comap_map_eq (f : V ↪ W) (G : SimpleGraph V) :
 (G.map f).comap f = G
· 使用引理 `SimpleGraph.comap_symm`：comap_symm (G : SimpleGraph V) (e : V ≃ W) : G.c
omap e.symm.toEmbedding = G.map e.toEmbedding
· 使用引理 `SimpleGraph.map_symm`：map_symm (G : SimpleGraph W) (e : V ≃ W) : G.map e
.symm.toEmbedding = G.comap e.toEmbedding
· 使用定理 `SimpleGraph.LocallyLinear.map`：∀ {α : Type u_1} {β : Type u_2} {G : Simp
leGraph α} (f : α ↪ β),   G.LocallyLinear → (SimpleGraph.map (⇑f) G).LocallyLine
ar
· 使用定理 `Equiv.coe_toEmbedding`：coe_toEmbedding : (f.toEmbedding : α -> β) = f
-/
@[simp] lemma locallyLinear_comap {G : SimpleGraph β} {e : α ≃ β} :
    (G.comap e).LocallyLinear ↔ G.LocallyLinear := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← comap_map_eq e.symm.toEmbedding G, comap_symm, map_symm]
    exact h.map _
  · rw [← Equiv.coe_toEmbedding, ← map_symm]
    exact LocallyLinear.map _
/-
**SimpleGraph.edgeDisjointTriangles_iff_mem_sym2_subsingleton** 是 Mathlib 中的一个引理
，位于命名空间 `SimpleGraph`。
形式化陈述：edgeDisjointTriangles_iff_mem_sym2_subsingleton : G.EdgeDisjointTriangles 
↔ forall ⦃e : Sym2 α⦄, ¬ e.IsDiag -> {s in G.cliqueSet 3 | e in (s : Finset α).s
ym2}.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym2.forall`：∀ {α : Type u_4} {f : Sym2 α → Prop}, (∀ (x : Sym2 α), f x)
 ↔ ∀ (x y : α), f s(x, y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Sym2.mk_isDiag_iff`：mk_isDiag_iff {x y : α} : IsDiag s(x, y) ↔ x = y
· 使用定理 `Set.Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a b : 
α}, s.Pairwise r → a ∈ s → b ∈ s → ¬r a b → a = b
· 使用定理 `Set.Nontrivial.not_subsingleton`：∀ {α : Type u} {s : Set α}, s.Nontrivia
l → ¬s.Subsingleton
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `Set.not_nontrivial_iff`：not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingle
ton
-/
lemma edgeDisjointTriangles_iff_mem_sym2_subsingleton :
    G.EdgeDisjointTriangles ↔
      ∀ ⦃e : Sym2 α⦄, ¬ e.IsDiag → {s ∈ G.cliqueSet 3 | e ∈ (s : Finset α).sym2}.Subsingleton := by
  classical
  have (a b) (hab : a ≠ b) : {s ∈ (G.cliqueSet 3 : Set (Finset α)) | s(a, b) ∈ (s : Finset α).sym2}
    = {s | G.Adj a b ∧ ∃ c, G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c}} := by
    ext s
    simp only [mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp, forall_eq,
      mem_cliqueSet_iff, Set.mem_ofPred_eq,
      is3Clique_iff]
    constructor
    · rintro ⟨⟨c, d, e, hcd, hce, hde, rfl⟩, hab⟩
      simp only [mem_insert, mem_singleton] at hab
      obtain ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ := hab
      any_goals
        simp only [*, adj_comm, true_and, Ne, not_true] at *
      any_goals
        first
        | exact ⟨c, by aesop⟩
        | exact ⟨d, by aesop⟩
        | exact ⟨e, by aesop⟩
        | simp only [*, true_and] at *
          exact ⟨c, by aesop⟩
        | simp only [*, true_and] at *
          exact ⟨d, by aesop⟩
        | simp only [*, true_and] at *
          exact ⟨e, by aesop⟩
    · rintro ⟨hab, c, hac, hbc, rfl⟩
      refine ⟨⟨a, b, c, ?_⟩, ?_⟩ <;> simp [*]
  constructor
  · rw [Sym2.forall]
    rintro hG a b hab
    simp only [Sym2.mk_isDiag_iff] at hab
    rw [this _ _ (Sym2.mk_isDiag_iff.not.2 hab)]
    rintro _ ⟨hab, c, hac, hbc, rfl⟩ _ ⟨-, d, had, hbd, rfl⟩
    refine hG.eq ?_ ?_ (Set.Nontrivial.not_subsingleton ⟨a, ?_, b, ?_, hab.ne⟩) <;>
      simp [is3Clique_triple_iff, *]
  · simp only [EdgeDisjointTriangles, is3Clique_iff, Set.Pairwise, mem_cliqueSet_iff, Ne,
      forall_exists_index, and_imp, ← Set.not_nontrivial_iff (s := _ ∩ _), not_imp_not,
      Set.Nontrivial, Set.mem_inter_iff, mem_coe]
    rintro hG _ a b c hab hac hbc rfl _ d e f hde hdf hef rfl g hg₁ hg₂ h hh₁ hh₂ hgh
    refine hG (Sym2.mk_isDiag_iff.not.2 hgh) ⟨⟨a, b, c, ?_⟩, by simpa using And.intro hg₁ hh₁⟩
      ⟨⟨d, e, f, ?_⟩, by simpa using And.intro hg₂ hh₂⟩ <;> simp [*]

alias ⟨EdgeDisjointTriangles.mem_sym2_subsingleton, _⟩ :=
  edgeDisjointTriangles_iff_mem_sym2_subsingleton

variable [DecidableEq α] [Fintype α] [DecidableRel G.Adj]
/-
**SimpleGraph.EdgeDisjointTriangles.instDecidable** 是 Mathlib 中的一个定义，位于命名空间 `Sim
pleGraph.EdgeDisjointTriangles`。
形式化陈述：{α : Type u_1} →   {G : SimpleGraph α} → [DecidableEq α] → [Fintype α] → [
DecidableRel G.Adj] → Decidable G.EdgeDisjointTriangles
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance EdgeDisjointTriangles.instDecidable : Decidable G.EdgeDisjointTriangles :=
  decidable_of_iff ((G.cliqueFinset 3 : Set (Finset α)).Pairwise fun x y ↦ (#(x ∩ y) ≤ 1)) <| by
    simp only [coe_cliqueFinset, EdgeDisjointTriangles, Finset.card_le_one, ← coe_inter]; rfl
/-
**SimpleGraph.LocallyLinear.instDecidable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph
.LocallyLinear`。
形式化陈述：{α : Type u_1} → {G : SimpleGraph α} → [DecidableEq α] → [Fintype α] → [De
cidableRel G.Adj] → Decidable G.LocallyLinear
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance LocallyLinear.instDecidable : Decidable G.LocallyLinear :=
  inferInstanceAs (Decidable (_ ∧ _))
/-
**SimpleGraph.EdgeDisjointTriangles.card_edgeFinset_le** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.EdgeDisjointTriangles`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} [inst : DecidableEq α] [inst_1 : Fint
ype α] [inst_2 : DecidableRel G.Adj],   G.EdgeDisjointTriangles → 3 * (G.cliqueF
inset 3).card ≤ G.edgeFinset.card
参数：G.cliqueFinset 3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.card_mul_le_card_mul`：card_mul_le_card_mul [forall a b, Decidable
 (r a b)] (hm : forall a in s, m <= #(t.bipartiteAbove r a)) (hn : forall b in t
, #(s.bipartiteBe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.bipartiteAbove.congr_simp`：∀ {α : Type u_2} {β : Type u_3} (r r_1
 : α → β → Prop),   r = r_1 →     ∀ (t t_1 : Finset β),       t = t_1 →         
∀ (a a_1 : α),        …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_eq_three`：card_eq_three : #s = 3 ↔ exists x y z, x != y ∧ x 
!= z ∧ y != z ∧ s = {x, y, z}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `SimpleGraph.EdgeDisjointTriangles.mem_sym2_subsingleton`：∀ {α : Type u_1
} {G : SimpleGraph α},   G.EdgeDisjointTriangles → ∀ ⦃e : Sym2 α⦄, ¬e.IsDiag → {
s | s ∈ G.cliqueSet 3 ∧ e ∈ s.sym2}.Subsingle…
（共 33 条，此处仅展示前 30 条）
-/
lemma EdgeDisjointTriangles.card_edgeFinset_le (hG : G.EdgeDisjointTriangles) :
    3 * #(G.cliqueFinset 3) ≤ #G.edgeFinset := by
  rw [mul_comm, ← mul_one #G.edgeFinset]
  refine card_mul_le_card_mul (fun s e ↦ e ∈ s.sym2) ?_ (fun e he ↦ ?_)
  · simp only [is3Clique_iff, mem_cliqueFinset_iff, mem_sym2_iff, forall_exists_index, and_imp]
    rintro _ a b c hab hac hbc rfl
    have : #{s(a, b), s(a, c), s(b, c)} = 3 := by
      refine card_eq_three.2 ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> simp [hab.ne, hac.ne, hbc.ne]
    rw [← this]
    refine card_mono ?_
    simp [insert_subset, *]
  · simpa only [card_le_one, mem_bipartiteBelow, and_imp, Set.Subsingleton, Set.mem_ofPred_eq,
      mem_cliqueFinset_iff, mem_cliqueSet_iff]
      using hG.mem_sym2_subsingleton (G.not_isDiag_of_mem_edgeSet <| mem_edgeFinset.1 he)
/-
**SimpleGraph.LocallyLinear.card_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.LocallyLinear`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} [inst : DecidableEq α] [inst_1 : Fint
ype α] [inst_2 : DecidableRel G.Adj],   G.LocallyLinear → G.edgeFinset.card = 3 
* (G.cliqueFinset 3).card
参数：G.cliqueFinset 3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `SimpleGraph.EdgeDisjointTriangles.card_edgeFinset_le`：∀ {α : Type u_1} {
G : SimpleGraph α} [inst : DecidableEq α] [inst_1 : Fintype α] [inst_2 : Decidab
leRel G.Adj],   G.EdgeDisjointTriangles → …
· 使用定理 `SimpleGraph.LocallyLinear.edgeDisjointTriangles`：∀ {α : Type u_1} {G : S
impleGraph α}, G.LocallyLinear → G.EdgeDisjointTriangles
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.card_mul_le_card_mul`：card_mul_le_card_mul [forall a b, Decidable
 (r a b)] (hm : forall a in s, m <= #(t.bipartiteAbove r a)) (hn : forall b in t
, #(s.bipartiteBe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.bipartiteAbove.congr_simp`：∀ {α : Type u_2} {β : Type u_3} (r r_1
 : α → β → Prop),   r = r_1 →     ∀ (t t_1 : Finset β),       t = t_1 →         
∀ (a a_1 : α),        …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.bipartiteBelow.congr_simp`：∀ {α : Type u_2} {β : Type u_3} (r r_1
 : α → β → Prop),   r = r_1 →     ∀ (s s_1 : Finset α),       s = s_1 →         
∀ (b b_1 : β),        …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_insert_le`：card_insert_le (a : α) (s : Finset α) : #(insert 
a s) <= #s + 1
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
-/
lemma LocallyLinear.card_edgeFinset (hG : G.LocallyLinear) :
    #G.edgeFinset = 3 * #(G.cliqueFinset 3) := by
  refine hG.edgeDisjointTriangles.card_edgeFinset_le.antisymm' ?_
  rw [← mul_comm, ← mul_one #_]
  refine card_mul_le_card_mul (fun e s ↦ e ∈ s.sym2) ?_ ?_
  · simpa [Sym2.forall, Nat.one_le_iff_ne_zero, -Finset.card_eq_zero, Finset.card_ne_zero,
        Finset.Nonempty]
      using hG.2
  simp only [mem_cliqueFinset_iff, is3Clique_iff, forall_exists_index, and_imp]
  rintro _ a b c hab hac hbc rfl
  calc
    _ ≤ #{s(a, b), s(a, c), s(b, c)} := card_le_card ?_
    _ ≤ 3 := (card_insert_le _ _).trans (succ_le_succ <| (card_insert_le _ _).trans_eq <| by
      rw [card_singleton])
  simp only [subset_iff, Sym2.forall, mem_sym2_iff, mem_bipartiteBelow, mem_insert,
    mem_edgeFinset, mem_singleton, and_imp, mem_edgeSet, Sym2.mem_iff, forall_eq_or_imp,
    forall_eq]
  rintro d e hde (rfl | rfl | rfl) (rfl | rfl | rfl) <;> simp [*] at *

end LocallyLinear

variable (G ε)
variable [Fintype α] [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- A simple graph is *`ε`-far from triangle-free* if one must remove at least
`ε * (card α) ^ 2` edges to make it triangle-free. -/
/-
**SimpleGraph.FarFromTriangleFree** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：FarFromTriangleFree : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple graph is *`ε`-far from triangle-free* if one must remove at least
`ε * (card α) ^ 2` edges to make it triangle-free.
-/
def FarFromTriangleFree : Prop := G.DeleteFar (fun H ↦ H.CliqueFree 3) <| ε * (card α ^ 2 : ℕ)

variable {G ε}

omit [IsStrictOrderedRing 𝕜] in
/-
**SimpleGraph.farFromTriangleFree_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：farFromTriangleFree_iff : G.FarFromTriangleFree ε ↔ forall ⦃H : SimpleGrap
h α⦄, [DecidableRel H.Adj] -> H <= G -> H.CliqueFree 3 -> ε * (card α ^ 2 : Nat)
 <= #G.edgeFinset - #H.edgeFinset
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.deleteFar_iff`：deleteFar_iff [Fintype (Sym2 V)] : G.DeleteFa
r p r ↔ forall ⦃H : SimpleGraph _⦄ [DecidableRel H.Adj], H <= G -> p H -> r <= #
G.edgeFinset - …
-/
theorem farFromTriangleFree_iff :
    G.FarFromTriangleFree ε ↔ ∀ ⦃H : SimpleGraph α⦄, [DecidableRel H.Adj] → H ≤ G → H.CliqueFree 3 →
      ε * (card α ^ 2 : ℕ) ≤ #G.edgeFinset - #H.edgeFinset := deleteFar_iff

alias ⟨farFromTriangleFree.le_card_sub_card, _⟩ := farFromTriangleFree_iff

nonrec theorem FarFromTriangleFree.mono (hε : G.FarFromTriangleFree ε) (h : δ ≤ ε) :
    G.FarFromTriangleFree δ := hε.mono <| by gcongr

section DecidableEq

variable [DecidableEq α]

omit [IsStrictOrderedRing 𝕜] in
/-
**SimpleGraph.FarFromTriangleFree.cliqueFinset_nonempty'** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph.FarFromTriangleFree`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
{G H : SimpleGraph α} {ε : 𝕜}   [inst_2 : Fintype α] [inst_3 : DecidableRel G.Ad
j] [inst_4 : DecidableRel H.Adj] [inst_5 : DecidableEq α],   H ≤ G →     G.FarFr
omTriangleFree ε →       ↑G.edgeFinset.card - ↑H.edgeFinset.card < ε * ↑(Fintype
.card α ^ 2) → (H.cliqueFinset 3).Nonempty
参数：Fintype.card α ^ 2；H.cliqueFinset 3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nonempty_of_ne_empty`：nonempty_of_ne_empty {s : Finset α} (h : s 
!= ∅) : s.Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `SimpleGraph.cliqueFinset_eq_empty_iff`：cliqueFinset_eq_empty_iff : G.cli
queFinset n = ∅ ↔ G.CliqueFree n
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `SimpleGraph.DeleteFar.le_card_sub_card`：∀ {V : Type u_1} {G : SimpleGrap
h V} {𝕜 : Type u_2} [inst : Ring 𝕜] [inst_1 : PartialOrder 𝕜]   [inst_2 : Fintyp
e ↑G.edgeSet] {p : SimpleGra…
-/
theorem FarFromTriangleFree.cliqueFinset_nonempty' (hH : H ≤ G) (hG : G.FarFromTriangleFree ε)
    (hcard : #G.edgeFinset - #H.edgeFinset < ε * (card α ^ 2 : ℕ)) :
    (H.cliqueFinset 3).Nonempty :=
  nonempty_of_ne_empty <|
    cliqueFinset_eq_empty_iff.not.2 fun hH' => (hG.le_card_sub_card hH hH').not_gt hcard
/-
**SimpleGraph.farFromTriangleFree_of_disjoint_triangles_aux** 是 Mathlib 中的一个引理，位
于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma farFromTriangleFree_of_disjoint_triangles_aux {tris : Finset (Finset α)}
    (htris : tris ⊆ G.cliqueFinset 3)
    (pd : (tris : Set (Finset α)).Pairwise fun x y ↦ (x ∩ y : Set α).Subsingleton) (hHG : H ≤ G)
    (hH : H.CliqueFree 3) : #tris ≤ #G.edgeFinset - #H.edgeFinset := by
  rw [← card_sdiff_of_subset (edgeFinset_mono hHG), ← card_attach]
  by_contra! hG
  have ⦃t⦄ (ht : t ∈ tris) :
    ∃ x y, x ∈ t ∧ y ∈ t ∧ x ≠ y ∧ s(x, y) ∈ G.edgeFinset \ H.edgeFinset := by
    by_contra! h
    refine hH t ?_
    simp only [not_and, mem_sdiff, not_not, mem_edgeFinset, mem_edgeSet] at h
    obtain ⟨x, y, z, xy, xz, yz, rfl⟩ := is3Clique_iff.1 (mem_cliqueFinset_iff.1 <| htris ht)
    rw [is3Clique_triple_iff]
    refine ⟨h _ _ ?_ ?_ xy.ne xy, h _ _ ?_ ?_ xz.ne xz, h _ _ ?_ ?_ yz.ne yz⟩ <;> simp
  choose fx fy hfx hfy hfne fmem using this
  let f (t : {x // x ∈ tris}) : Sym2 α := s(fx t.2, fy t.2)
  have hf (x) (_ : x ∈ tris.attach) : f x ∈ G.edgeFinset \ H.edgeFinset := fmem _
  obtain ⟨⟨t₁, ht₁⟩, -, ⟨t₂, ht₂⟩, -, tne, t : s(_, _) = s(_, _)⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to hG hf
  dsimp at t
  have i := pd ht₁ ht₂ (Subtype.val_injective.ne tne)
  rw [Sym2.eq_iff] at t
  obtain t | t := t
  · exact hfne _ (i ⟨hfx ht₁, t.1.symm ▸ hfx ht₂⟩ ⟨hfy ht₁, t.2.symm ▸ hfy ht₂⟩)
  · exact hfne _ (i ⟨hfx ht₁, t.1.symm ▸ hfy ht₂⟩ ⟨hfy ht₁, t.2.symm ▸ hfx ht₂⟩)

/-- If there are `ε * (card α)^2` disjoint triangles, then the graph is `ε`-far from being
triangle-free. -/
/-
**SimpleGraph.farFromTriangleFree_of_disjoint_triangles** 是 Mathlib 中的一个引理，位于命名空
间 `SimpleGraph`。
形式化陈述：farFromTriangleFree_of_disjoint_triangles (tris : Finset (Finset α)) (htri
s : tris subseteq G.cliqueFinset 3) (pd : (tris : Set (Finset α)).Pairwise fun x
 y => (x inter y : Set α).Subsingleton) (tris_big : ε * (card α ^ 2 : Nat) <= #t
ris) : G.FarFromTriangleFree ε
参数：tris : Finset (Finset α)；htris : tris subseteq G.cliqueFinset 3；pd : (tris : 
Set (Finset α)).Pairwise fun x y => (x inter y : Set α).Subsingleton；tris_big : 
ε * (card α ^ 2 : Nat) <= #tris。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.farFromTriangleFree_iff`：farFromTriangleFree_iff : G.FarFrom
TriangleFree ε ↔ forall ⦃H : SimpleGraph α⦄, [DecidableRel H.Adj] -> H <= G -> H
.CliqueFree 3 -> ε * (car…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `SimpleGraph.edgeFinset_mono`：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V} [i
nst : Fintype ↑G₁.edgeSet] [inst_1 : Fintype ↑G₂.edgeSet],   G₁ ≤ G₂ → G₁.edgeFi
nset ⊆ G₂.edgeFin…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Triangle.Basic.0.SimpleGraph.
farFromTriangleFree_of_disjoint_triangles_aux`：∀ {α : Type u_1} {G H : SimpleGra
ph α} [inst : Fintype α] [inst_1 : DecidableRel G.Adj] [inst_2 : DecidableRel H.
Adj]   [inst_3 : DecidableE…

--- 原说明 ---
If there are `ε * (card α)^2` disjoint triangles, then the graph is `ε`-far from
 being
triangle-free.
-/
lemma farFromTriangleFree_of_disjoint_triangles (tris : Finset (Finset α))
    (htris : tris ⊆ G.cliqueFinset 3)
    (pd : (tris : Set (Finset α)).Pairwise fun x y ↦ (x ∩ y : Set α).Subsingleton)
    (tris_big : ε * (card α ^ 2 : ℕ) ≤ #tris) :
    G.FarFromTriangleFree ε := by
  rw [farFromTriangleFree_iff]
  intro H _ hG hH
  rw [← Nat.cast_sub (card_le_card <| edgeFinset_mono hG)]
  exact tris_big.trans
    (Nat.cast_le.2 <| farFromTriangleFree_of_disjoint_triangles_aux htris pd hG hH)
/-
**SimpleGraph.EdgeDisjointTriangles.farFromTriangleFree** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.EdgeDisjointTriangles`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   {ε : 𝕜} [inst_3 : Fintype α] [inst
_4 : DecidableRel G.Adj] [inst_5 : DecidableEq α],   G.EdgeDisjointTriangles → ε
 * ↑(Fintype.card α ^ 2) ≤ ↑(G.cliqueFinset 3).card → G.FarFromTriangleFree ε
参数：Fintype.card α ^ 2；G.cliqueFinset 3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.farFromTriangleFree_of_disjoint_triangles`：farFromTriangleFr
ee_of_disjoint_triangles (tris : Finset (Finset α)) (htris : tris subseteq G.cli
queFinset 3) (pd : (tris : Set (Finset α)).…
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_cliqueFinset`：coe_cliqueFinset (n : Nat) : (G.cliqueFins
et n : Set (Finset α)) = G.cliqueSet n
-/
protected lemma EdgeDisjointTriangles.farFromTriangleFree (hG : G.EdgeDisjointTriangles)
    (tris_big : ε * (card α ^ 2 : ℕ) ≤ #(G.cliqueFinset 3)) :
    G.FarFromTriangleFree ε :=
  farFromTriangleFree_of_disjoint_triangles _ Subset.rfl (by simpa using! hG) tris_big

end DecidableEq

variable [Nonempty α]

/-
**SimpleGraph.FarFromTriangleFree.lt_half** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.FarFromTriangleFree`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   {ε : 𝕜} [inst_3 : Fintype α] [inst
_4 : DecidableRel G.Adj] [Nonempty α], G.FarFromTriangleFree ε → ε < 2⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_right`：lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : 
b * a < c * a) (a0 : 0 <= a) : b < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `SimpleGraph.DeleteFar.le_card_edgeFinset`：∀ {V : Type u_1} {G : SimpleGr
aph V} {𝕜 : Type u_2} [inst : Ring 𝕜] [inst_1 : PartialOrder 𝕜]   [inst_2 : Fint
ype ↑G.edgeSet] {p : SimpleGra…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `SimpleGraph.card_edgeFinset_le_card_choose_two`：card_edgeFinset_le_card_
choose_two : #G.edgeFinset <= (Fintype.card V).choose 2
· 使用引理 `Nat.choose_lt_pow_div`：choose_lt_pow_div (hn : n != 0) (hk : 2 <= k) : (
n.choose k : α) < (n ^ k : α) / k !
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
lemma FarFromTriangleFree.lt_half (hε : G.FarFromTriangleFree ε) : ε < 2⁻¹ := by
  refine lt_of_mul_lt_mul_right (α := 𝕜) (a := Fintype.card α ^ 2) ?_ (by positivity)
  calc
        ε * Fintype.card α ^ 2
    _ ≤ #G.edgeFinset := by simpa using hε.le_card_edgeFinset (by simp)
    _ ≤ (Fintype.card α).choose 2 := by gcongr; exact card_edgeFinset_le_card_choose_two
    _ < 2⁻¹ * Fintype.card α ^ 2 := by
      simpa [← div_eq_inv_mul] using Nat.choose_lt_pow_div (by positivity) le_rfl
/-
**SimpleGraph.FarFromTriangleFree.lt_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
FarFromTriangleFree`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   {ε : 𝕜} [inst_3 : Fintype α] [inst
_4 : DecidableRel G.Adj] [Nonempty α], G.FarFromTriangleFree ε → ε < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.FarFromTriangleFree.lt_half`：∀ {α : Type u_1} {𝕜 : Type u_3}
 [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {G : SimpleGr
aph α}   {ε : 𝕜} [inst_3 : Fi…
· 使用定理 `two_inv_lt_one`：two_inv_lt_one : (2⁻¹ : α) < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
lemma FarFromTriangleFree.lt_one (hG : G.FarFromTriangleFree ε) : ε < 1 :=
  hG.lt_half.trans two_inv_lt_one
/-
**SimpleGraph.FarFromTriangleFree.nonpos** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
FarFromTriangleFree`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   {ε : 𝕜} [inst_3 : Fintype α] [inst
_4 : DecidableRel G.Adj] [Nonempty α],   G.FarFromTriangleFree ε → G.CliqueFree 
3 → ε ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.empty_subset`：empty_subset (s : Finset α) : ∅ subseteq s
· 使用定理 `nonpos_of_mul_nonpos_left`：nonpos_of_mul_nonpos_left [PosMulStrictMono R
] (h : a * b <= 0) (hb : 0 < b) : a <= 0
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.deleteEdges_empty`：deleteEdges_empty : G.deleteEdges ∅ = G
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `sq_pos_of_pos`：sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a 
^ 2
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
-/
theorem FarFromTriangleFree.nonpos (h₀ : G.FarFromTriangleFree ε) (h₁ : G.CliqueFree 3) :
    ε ≤ 0 := by
  have := h₀ (empty_subset _)
  rw [coe_empty, Finset.card_empty, cast_zero, deleteEdges_empty] at this
  exact nonpos_of_mul_nonpos_left (this h₁) (cast_pos.2 <| sq_pos_of_pos Fintype.card_pos)
/-
**SimpleGraph.CliqueFree.not_farFromTriangleFree** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.CliqueFree`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   {ε : 𝕜} [inst_3 : Fintype α] [inst
_4 : DecidableRel G.Adj] [Nonempty α],   G.CliqueFree 3 → 0 < ε → ¬G.FarFromTria
ngleFree ε
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `SimpleGraph.FarFromTriangleFree.nonpos`：∀ {α : Type u_1} {𝕜 : Type u_3} 
[inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {G : SimpleGra
ph α}   {ε : 𝕜} [inst_3 : Fi…
-/
theorem CliqueFree.not_farFromTriangleFree (hG : G.CliqueFree 3) (hε : 0 < ε) :
    ¬G.FarFromTriangleFree ε := fun h => (h.nonpos hG).not_gt hε
/-
**SimpleGraph.FarFromTriangleFree.not_cliqueFree** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.FarFromTriangleFree`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   {ε : 𝕜} [inst_3 : Fintype α] [inst
_4 : DecidableRel G.Adj] [Nonempty α],   G.FarFromTriangleFree ε → 0 < ε → ¬G.Cl
iqueFree 3
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `SimpleGraph.FarFromTriangleFree.nonpos`：∀ {α : Type u_1} {𝕜 : Type u_3} 
[inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {G : SimpleGra
ph α}   {ε : 𝕜} [inst_3 : Fi…
-/
theorem FarFromTriangleFree.not_cliqueFree (hG : G.FarFromTriangleFree ε) (hε : 0 < ε) :
    ¬G.CliqueFree 3 := fun h => (hG.nonpos h).not_gt hε
/-
**SimpleGraph.FarFromTriangleFree.cliqueFinset_nonempty** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.FarFromTriangleFree`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_3} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] 
[IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   {ε : 𝕜} [inst_3 : Fintype α] [inst
_4 : DecidableRel G.Adj] [Nonempty α] [inst_6 : DecidableEq α],   G.FarFromTrian
gleFree ε → 0 < ε → (G.cliqueFinset 3).Nonempty
参数：G.cliqueFinset 3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nonempty_of_ne_empty`：nonempty_of_ne_empty {s : Finset α} (h : s 
!= ∅) : s.Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `SimpleGraph.cliqueFinset_eq_empty_iff`：cliqueFinset_eq_empty_iff : G.cli
queFinset n = ∅ ↔ G.CliqueFree n
· 使用定理 `SimpleGraph.FarFromTriangleFree.not_cliqueFree`：∀ {α : Type u_1} {𝕜 : Ty
pe u_3} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {G : S
impleGraph α}   {ε : 𝕜} [inst_3 : Fi…
-/
theorem FarFromTriangleFree.cliqueFinset_nonempty [DecidableEq α]
    (hG : G.FarFromTriangleFree ε) (hε : 0 < ε) : (G.cliqueFinset 3).Nonempty :=
  nonempty_of_ne_empty <| cliqueFinset_eq_empty_iff.not.2 <| hG.not_cliqueFree hε

end SimpleGraph

