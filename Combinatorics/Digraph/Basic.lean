/-
Copyright (c) 2024 Kyle Miller, Jack Cheverton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Jack Cheverton, Jeremy Tan
-/
module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Data.Fintype.Pi

/-!
# Digraphs

This module defines directed graphs on a vertex type `V`,
which is the same notion as a relation `V → V → Prop`.
While this might be too simple of a notion to deserve the grandeur of a new definition,
the intention here is to develop relations using the language of graph theory.

Note that in this treatment, a digraph may have self loops.

The type `Digraph V` is structurally equivalent to `Quiver.{0} V`,
but a difference between these is that `Quiver` is a class —
its purpose is to attach a quiver structure to a particular type `V`.
In contrast, for `Digraph V` we are interested in working with the entire lattice
of digraphs on `V`.

## Main definitions

* `Digraph` is a structure for relations. Unlike `SimpleGraph`, the relation does not need to be
  symmetric or irreflexive.

* `CompleteAtomicBooleanAlgebra` instance: Under the subgraph relation, `Digraph` forms a
  `CompleteAtomicBooleanAlgebra`. In other words, this is the complete lattice of spanning subgraphs
  of the complete graph.
-/

@[expose] public section

open Finset Function

/--
A digraph is a relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.

In this treatment, a digraph may have self-loops.
-/
@[ext]
/-
**Digraph** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A digraph is a relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.

In this treatment, a digraph may have self-loops.
-/
structure Digraph (V : Type*) where
  /-- The adjacency relation of a digraph. -/
  Adj : V → V → Prop

/--
Constructor for digraphs using a Boolean function.
This is useful for creating a digraph with a decidable `Adj` relation,
and it's used in the construction of the `Fintype (Digraph V)` instance.
-/
@[simps]
/-
**Digraph.mk'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Digraph.mk' {V : Type*} : (V -> V -> Bool) ↪ Digraph V where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for digraphs using a Boolean function.
This is useful for creating a digraph with a decidable `Adj` relation,
and it's used in the construction of the `Fintype (Digraph V)` instance.
-/
def Digraph.mk' {V : Type*} : (V → V → Bool) ↪ Digraph V where
  toFun x := ⟨fun v w ↦ x v w⟩
  inj' adj adj' := by
    simp_rw [mk.injEq]
    intro h
    funext v w
    simpa only [eq_iff_iff, Bool.coe_iff_coe] using congr($h v w)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {V : Type*} (adj : V → V → Bool) : DecidableRel (Digraph.mk' adj).Adj :=
  inferInstanceAs <| DecidableRel (fun v w ↦ adj v w)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {V : Type*} [DecidableEq V] [Fintype V] : Fintype (Digraph V) :=
  Fintype.ofBijective Digraph.mk' <| by
    classical
    refine ⟨Embedding.injective _, ?_⟩
    intro G
    use fun v w ↦ G.Adj v w
    ext v w
    simp

namespace Digraph

/--
The complete digraph on a type `V` (denoted by `⊤`)
is the digraph whose vertices are all adjacent.
Note that every vertex is adjacent to itself in `⊤`.
-/
/-
**Digraph.completeDigraph** 是 Mathlib 中的一个定义，位于命名空间 `Digraph`。
形式化陈述：(V : Type u_1) → Digraph V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complete digraph on a type `V` (denoted by `⊤`)
is the digraph whose vertices are all adjacent.
Note that every vertex is adjacent to itself in `⊤`.
-/
protected def completeDigraph (V : Type*) : Digraph V where Adj := ⊤

/--
The empty digraph on a type `V` (denoted by `⊥`)
is the digraph such that no pairs of vertices are adjacent.
Note that `⊥` is called the empty digraph because it has no edges.
-/
/-
**Digraph.emptyDigraph** 是 Mathlib 中的一个定义，位于命名空间 `Digraph`。
形式化陈述：(V : Type u_1) → Digraph V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty digraph on a type `V` (denoted by `⊥`)
is the digraph such that no pairs of vertices are adjacent.
Note that `⊥` is called the empty digraph because it has no edges.
-/
protected def emptyDigraph (V : Type*) : Digraph V where Adj _ _ := False

/--
Two vertices are adjacent in the complete bipartite digraph on two vertex types
if and only if they are not from the same side.
Any bipartite digraph may be regarded as a subgraph of one of these.
-/
@[simps]
/-
**Digraph.completeBipartiteGraph** 是 Mathlib 中的一个定义，位于命名空间 `Digraph`。
形式化陈述：completeBipartiteGraph (V W : Type*) : Digraph (Sum V W) where Adj v w
参数：V W : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two vertices are adjacent in the complete bipartite digraph on two vertex types
if and only if they are not from the same side.
Any bipartite digraph may be regarded as a subgraph of one of these.
-/
def completeBipartiteGraph (V W : Type*) : Digraph (Sum V W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft

variable {ι : Sort*} {V : Type*} (G : Digraph V) {a b : V}
/-
**Digraph.adj_injective** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：adj_injective : Injective (Adj : Digraph V -> V -> V -> Prop)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Digraph.ext`：∀ {V : Type u_1} {x y : Digraph V}, x.Adj = y.Adj → x = y
-/
theorem adj_injective : Injective (Adj : Digraph V → V → V → Prop) := fun _ _ ↦ Digraph.ext
/-
**Digraph.adj_inj** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：∀ {V : Type u_2} {G H : Digraph V}, G.Adj = H.Adj ↔ G = H
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Digraph.ext_iff`：∀ {V : Type u_1} {x y : Digraph V}, x = y ↔ x.Adj = y.A
dj
-/
@[simp] theorem adj_inj {G H : Digraph V} : G.Adj = H.Adj ↔ G = H := Digraph.ext_iff.symm

section Order

/--
The relation that one `Digraph` is a spanning subgraph of another.
Note that `Digraph.IsSubgraph G H` should be spelled `G ≤ H`.
-/
/-
**Digraph.IsSubgraph** 是 Mathlib 中的一个定义，位于命名空间 `Digraph`。
形式化陈述：{V : Type u_2} → Digraph V → Digraph V → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation that one `Digraph` is a spanning subgraph of another.
Note that `Digraph.IsSubgraph G H` should be spelled `G ≤ H`.
-/
protected def IsSubgraph (x y : Digraph V) : Prop :=
  ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

/-- For digraphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`. -/
/-
**Digraph.** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For digraphs `G`, `H`, `G ≤ H` iff `∀ a b, G.Adj a b → H.Adj a b`.
-/
instance : LE (Digraph V) := ⟨Digraph.IsSubgraph⟩

@[simp]
/-
**Digraph.isSubgraph_eq_le** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：isSubgraph_eq_le : (Digraph.IsSubgraph : Digraph V -> Digraph V -> Prop) =
 (· <= ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isSubgraph_eq_le : (Digraph.IsSubgraph : Digraph V → Digraph V → Prop) = (· ≤ ·) := rfl

/-- The supremum of two digraphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
/-
**Digraph.** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supremum of two digraphs `x ⊔ y` has edges where either `x` or `y` have edge
s.
-/
instance : Max (Digraph V) where
  max x y := { Adj := x.Adj ⊔ y.Adj }

@[simp]
/-
**Digraph.sup_adj** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj 
v w
参数：x y : Digraph V；v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sup_adj (x y : Digraph V) (v w : V) : (x ⊔ y).Adj v w ↔ x.Adj v w ∨ y.Adj v w := Iff.rfl

/-- The infimum of two digraphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
/-
**Digraph.** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of two digraphs `x ⊓ y` has edges where both `x` and `y` have edges.
-/
instance : Min (Digraph V) where
  min x y := { Adj := x.Adj ⊓ y.Adj }

@[simp]
/-
**Digraph.inf_adj** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj 
v w
参数：x y : Digraph V；v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inf_adj (x y : Digraph V) (v w : V) : (x ⊓ y).Adj v w ↔ x.Adj v w ∧ y.Adj v w := Iff.rfl

/-- We define `Gᶜ` to be the `Digraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent. -/
/-
**Digraph.** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `Gᶜ` to be the `Digraph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjace
nt.
-/
instance : Compl (Digraph V) where
  compl G := { Adj := fun v w ↦ ¬G.Adj v w }
/-
**Digraph.compl_adj** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：∀ {V : Type u_2} (G : Digraph V) (v w : V), Gᶜ.Adj v w ↔ ¬G.Adj v w
参数：G : Digraph V；v w : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem compl_adj (G : Digraph V) (v w : V) : Gᶜ.Adj v w ↔ ¬G.Adj v w := Iff.rfl

/-- The difference of two digraphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
/-
**Digraph.sdiff** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
形式化陈述：sdiff : SDiff (Digraph V) where sdiff x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The difference of two digraphs `x \ y` has the edges of `x` with the edges of `y
` removed.
-/
instance sdiff : SDiff (Digraph V) where
  sdiff x y := { Adj := x.Adj \ y.Adj }

@[simp]
/-
**Digraph.sdiff_adj** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：sdiff_adj (x y : Digraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.A
dj v w
参数：x y : Digraph V；v w : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sdiff_adj (x y : Digraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w := Iff.rfl
/-
**Digraph.supSet** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
形式化陈述：supSet : SupSet (Digraph V) where sSup s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance supSet : SupSet (Digraph V) where
  sSup s := { Adj := fun a b ↦ ∃ G ∈ s, Adj G a b }
/-
**Digraph.infSet** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
形式化陈述：infSet : InfSet (Digraph V) where sInf s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance infSet : InfSet (Digraph V) where
  sInf s := { Adj := fun a b ↦ (∀ ⦃G⦄, G ∈ s → Adj G a b) }

@[simp]
/-
**Digraph.sSup_adj** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：sSup_adj {s : Set (Digraph V)} : (sSup s).Adj a b ↔ exists G in s, Adj G a
 b
参数：Digraph V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sSup_adj {s : Set (Digraph V)} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b := Iff.rfl

@[simp]
/-
**Digraph.sInf_adj** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：sInf_adj {s : Set (Digraph V)} : (sInf s).Adj a b ↔ forall G in s, Adj G a
 b
参数：Digraph V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sInf_adj {s : Set (Digraph V)} : (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b := Iff.rfl

@[simp]
/-
**Digraph.iSup_adj** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：iSup_adj {f : ι -> Digraph V} : (⨆ i, f i).Adj a b ↔ exists i, (f i).Adj a
 b
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
theorem iSup_adj {f : ι → Digraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by simp [iSup]

@[simp]
/-
**Digraph.iInf_adj** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：iInf_adj {f : ι -> Digraph V} : (⨅ i, f i).Adj a b ↔ (forall i, (f i).Adj 
a b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iInf_adj {f : ι → Digraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) := by simp [iInf]
/-
**Digraph.** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Digraph V) := fast_instance% PartialOrder.lift _ adj_injective
/-
**Digraph.distribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
形式化陈述：distribLattice : DistribLattice (Digraph V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribLattice : DistribLattice (Digraph V) := fast_instance%
  adj_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl
/-
**Digraph.completeAtomicBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
形式化陈述：completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Digraph V) wh
ere top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra (Digraph V) where
  top := Digraph.completeDigraph V
  bot := Digraph.emptyDigraph V
  le_top _ _ _ _ := trivial
  bot_le _ _ _ h := h.elim
  inf_compl_le_bot _ _ _ h := absurd h.1 h.2
  top_le_sup_compl G v w _ := by tauto
  isLUB_sSup _ := ⟨fun G hG _ _ hab ↦ ⟨G, hG, hab⟩, fun _ hG _ _ ⟨_, hH, hab⟩ ↦ hG hH hab⟩
  isGLB_sInf _ := ⟨fun _ hG _ _ hab ↦ hab hG, fun _ hG _ _ hab _ hH ↦ hG hH hab⟩
  iInf_iSup_eq f := by ext; simp [Classical.skolem]
/-
**Digraph.top_adj** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：∀ {V : Type u_2} (v w : V), ⊤.Adj v w
参数：v w : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
@[simp] theorem top_adj (v w : V) : (⊤ : Digraph V).Adj v w := trivial
/-
**Digraph.bot_adj** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：∀ {V : Type u_2} (v w : V), ⊥.Adj v w ↔ False
参数：v w : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem bot_adj (v w : V) : (⊥ : Digraph V).Adj v w ↔ False := Iff.rfl
/-
**Digraph.completeDigraph_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：∀ (V : Type u_3), Digraph.completeDigraph V = ⊤
参数：V : Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem completeDigraph_eq_top (V : Type*) : Digraph.completeDigraph V = ⊤ := rfl
/-
**Digraph.emptyDigraph_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Digraph`。
形式化陈述：∀ (V : Type u_3), Digraph.emptyDigraph V = ⊥
参数：V : Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem emptyDigraph_eq_bot (V : Type*) : Digraph.emptyDigraph V = ⊥ := rfl
/-
**Digraph.** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simps] instance (V : Type*) : Inhabited (Digraph V) := ⟨⊥⟩
/-
**Digraph.** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty V] : Unique (Digraph V) where
  default := ⊥
  uniq G := by ext1; congr!
/-
**Digraph.** 是 Mathlib 中的一个实例，位于命名空间 `Digraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty V] : Nontrivial (Digraph V) := by
  use ⊥, ⊤
  have v := Classical.arbitrary V
  exact ne_of_apply_ne (·.Adj v v) (by simp)

section Decidable

variable (V) (H : Digraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

/-
**Digraph.Bot.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `Digraph.Bot`。
形式化陈述：(V : Type u_2) → DecidableRel ⊥.Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bot.adjDecidable : DecidableRel (⊥ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ False
/-
**Digraph.Sup.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `Digraph.Sup`。
形式化陈述：(V : Type u_2) → (G H : Digraph V) → [DecidableRel G.Adj] → [DecidableRel 
H.Adj] → DecidableRel (G ⊔ H).Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∨ H.Adj v w
/-
**Digraph.Inf.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `Digraph.Inf`。
形式化陈述：(V : Type u_2) → (G H : Digraph V) → [DecidableRel G.Adj] → [DecidableRel 
H.Adj] → DecidableRel (G ⊓ H).Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ H.Adj v w
/-
**Digraph.SDiff.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `Digraph.SDiff`。
形式化陈述：(V : Type u_2) → (G H : Digraph V) → [DecidableRel G.Adj] → [DecidableRel 
H.Adj] → DecidableRel (G \ H).Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SDiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w ↦ G.Adj v w ∧ ¬H.Adj v w
/-
**Digraph.Top.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `Digraph.Top`。
形式化陈述：(V : Type u_2) → DecidableRel ⊤.Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Top.adjDecidable : DecidableRel (⊤ : Digraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ ↦ True
/-
**Digraph.Compl.adjDecidable** 是 Mathlib 中的一个定义，位于命名空间 `Digraph.Compl`。
形式化陈述：(V : Type u_2) → (G : Digraph V) → [DecidableRel G.Adj] → DecidableRel Gᶜ.
Adj
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w ↦ ¬G.Adj v w

end Decidable

end Order

end Digraph

