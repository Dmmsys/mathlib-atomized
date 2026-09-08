/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Order.SuccPred.Relation
public import Mathlib.Tactic.FinCases

/-!
# The Hasse diagram as a graph

This file defines the Hasse diagram of an order (graph of `CovBy`, the covering relation) and the
path graph on `n` vertices.

## Main declarations

* `SimpleGraph.hasse`: Hasse diagram of an order.
* `SimpleGraph.pathGraph`: Path graph on `n` vertices.
-/

@[expose] public section


open Order OrderDual Relation

namespace SimpleGraph

variable (α β : Type*)

section Preorder

variable [Preorder α]

/-- The Hasse diagram of an order as a simple graph. The graph of the covering relation. -/
/-
**SimpleGraph.hasse** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：hasse : SimpleGraph α where Adj a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hasse diagram of an order as a simple graph. The graph of the covering relat
ion.
-/
def hasse : SimpleGraph α where
  Adj a b := a ⋖ b ∨ b ⋖ a

variable {α β} {a b : α}

@[simp]
/-
**SimpleGraph.hasse_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：hasse_adj : (hasse α).Adj a b ↔ a ⋖ b ∨ b ⋖ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasse_adj : (hasse α).Adj a b ↔ a ⋖ b ∨ b ⋖ a :=
  Iff.rfl

/-- `αᵒᵈ` and `α` have the same Hasse diagram. -/
/-
**SimpleGraph.hasseDualIso** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：hasseDualIso : hasse αᵒᵈ ≃g hasse α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`αᵒᵈ` and `α` have the same Hasse diagram.
-/
def hasseDualIso : hasse αᵒᵈ ≃g hasse α :=
  { ofDual with map_rel_iff' := by simp [or_comm] }

@[simp]
/-
**SimpleGraph.hasseDualIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：hasseDualIso_apply (a : αᵒᵈ) : hasseDualIso a = ofDual a
参数：a : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasseDualIso_apply (a : αᵒᵈ) : hasseDualIso a = ofDual a :=
  rfl

@[simp]
/-
**SimpleGraph.hasseDualIso_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：hasseDualIso_symm_apply (a : α) : hasseDualIso.symm a = toDual a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasseDualIso_symm_apply (a : α) : hasseDualIso.symm a = toDual a :=
  rfl

/-- The Hasse diagram of a preorder is triangle-free. This is the graph-theoretic formulation of
`not_covBy_of_lt_of_lt`: if `a ⋖ b` and `b ⋖ c` then `¬a ⋖ c`. -/
/-
**SimpleGraph.cliqueFree_hasse_three** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFree_hasse_three : (hasse α).CliqueFree 3
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_three`：card_eq_three : #s = 3 ↔ exists x y z, x != y ∧ x 
!= z ∧ y != z ∧ s = {x, y, z}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The Hasse diagram of a preorder is triangle-free. This is the graph-theoretic fo
rmulation of
`not_covBy_of_lt_of_lt`: if `a ⋖ b` and `b ⋖ c` then `¬a ⋖ c`.
-/
theorem cliqueFree_hasse_three : (hasse α).CliqueFree 3 := by
  classical
  intro s ⟨hc, hcard⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := s.card_eq_three.mp hcard
  have := hc (by simp) (by simp) hab
  have := hc (by simp) (by simp) hbc
  have := hc (by simp) (by simp) hac
  grind [hasse_adj, CovBy]

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β]

@[simp]
/-
**SimpleGraph.hasse_prod** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：hasse_prod : hasse (α × β) = hasse α □ hasse β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasse_prod : hasse (α × β) = hasse α □ hasse β := by
  ext x y
  simp_rw [boxProd_adj, hasse_adj, Prod.covBy_iff, or_and_right, @eq_comm _ y.1, @eq_comm _ y.2,
    or_or_or_comm]

end PartialOrder

section LinearOrder

variable [LinearOrder α]

/-
**SimpleGraph.hasse_preconnected_of_succ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：hasse_preconnected_of_succ [SuccOrder α] [IsSuccArchimedean α] : (hasse α)
.Preconnected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.reachable_iff_reflTransGen`：reachable_iff_reflTransGen (u v 
: V) : G.Reachable u v ↔ Relation.ReflTransGen G.Adj u v
· 使用定理 `reflTransGen_of_succ`：reflTransGen_of_succ (r : α -> α -> Prop) {n m : α
} (h1 : forall i in Ico n m, r i (succ i)) (h2 : forall i in Ico m n, r (succ i)
 i) : Refl…
· 使用定理 `Order.covBy_succ_of_not_isMax`：covBy_succ_of_not_isMax (h : ¬IsMax a) : 
a ⋖ succ a
· 使用定理 `LT.lt.not_isMax`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem hasse_preconnected_of_succ [SuccOrder α] [IsSuccArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen]
  exact
    reflTransGen_of_succ _ (fun c hc => Or.inl <| covBy_succ_of_not_isMax hc.2.not_isMax)
      fun c hc => Or.inr <| covBy_succ_of_not_isMax hc.2.not_isMax
/-
**SimpleGraph.hasse_preconnected_of_pred** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：hasse_preconnected_of_pred [PredOrder α] [IsPredArchimedean α] : (hasse α)
.Preconnected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.reachable_iff_reflTransGen`：reachable_iff_reflTransGen (u v 
: V) : G.Reachable u v ↔ Relation.ReflTransGen G.Adj u v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Relation.reflTransGen_swap`：reflTransGen_swap : ReflTransGen (swap r) a 
b ↔ ReflTransGen r b a
· 使用定理 `reflTransGen_of_pred`：reflTransGen_of_pred (r : α -> α -> Prop) {n m : α
} (h1 : forall i in Ioc m n, r i (pred i)) (h2 : forall i in Ioc n m, r (pred i)
 i) : Refl…
· 使用定理 `Order.pred_covBy_of_not_isMin`：∀ {α : Type u_1} [inst : Preorder α] [ins
t_1 : PredOrder α] {a : α}, ¬IsMin a → Order.pred a ⋖ a
· 使用定理 `LT.lt.not_isMin`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a →
 ¬IsMin a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem hasse_preconnected_of_pred [PredOrder α] [IsPredArchimedean α] : (hasse α).Preconnected :=
  fun a b => by
  rw [reachable_iff_reflTransGen, ← reflTransGen_swap]
  exact
    reflTransGen_of_pred _ (fun c hc => Or.inl <| pred_covBy_of_not_isMin hc.1.not_isMin)
      fun c hc => Or.inr <| pred_covBy_of_not_isMin hc.1.not_isMin

end LinearOrder

/-- The path graph on `n` vertices. -/
/-
**SimpleGraph.pathGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：pathGraph (n : Nat) : SimpleGraph (Fin n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The path graph on `n` vertices.
-/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  hasse _
/-
**SimpleGraph.pathGraph_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：pathGraph_adj {n : Nat} {u v : Fin n} : (pathGraph n).Adj u v ↔ u.val + 1 
= v.val ∨ v.val + 1 = u.val
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
theorem pathGraph_adj {n : ℕ} {u v : Fin n} :
    (pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val := by simp [pathGraph, hasse]
/-
**SimpleGraph.pathGraph_preconnected** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：pathGraph_preconnected (n : Nat) : (pathGraph n).Preconnected
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.hasse_preconnected_of_succ`：hasse_preconnected_of_succ [Succ
Order α] [IsSuccArchimedean α] : (hasse α).Preconnected
· 使用定理 `WellFoundedGT.toIsSuccArchimedean`：∀ {α : Type u_1} [inst : PartialOrder
 α] [h : WellFoundedGT α] [inst_1 : SuccOrder α], IsSuccArchimedean α
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_gt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedGT α],
 IsWellOrder α fun x1 x2 => x2 < x1
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem pathGraph_preconnected (n : ℕ) : (pathGraph n).Preconnected :=
  hasse_preconnected_of_succ _
/-
**SimpleGraph.pathGraph_connected** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：pathGraph_connected (n : Nat) : (pathGraph (n + 1)).Connected
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.pathGraph_preconnected`：pathGraph_preconnected (n : Nat) : (
pathGraph n).Preconnected
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem pathGraph_connected (n : ℕ) : (pathGraph (n + 1)).Connected :=
  ⟨pathGraph_preconnected _⟩
/-
**SimpleGraph.pathGraph_two_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：pathGraph_two_eq_top : pathGraph 2 = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem pathGraph_two_eq_top : pathGraph 2 = ⊤ := by
  ext u v
  fin_cases u <;> fin_cases v <;> simp [pathGraph]

namespace Walk

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V} (w : G.Walk u v)

/-- The subgraph of a walk contains the path graph with the same number of vertices -/
/-
**SimpleGraph.Walk.pathGraphHomToSubgraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph
.Walk`。
形式化陈述：pathGraphHomToSubgraph : pathGraph (w.length + 1) ->g w.toSubgraph.coe whe
re toFun n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgraph of a walk contains the path graph with the same number of vertices
-/
def pathGraphHomToSubgraph : pathGraph (w.length + 1) →g w.toSubgraph.coe where
  toFun n := ⟨w.support[n], w.mem_verts_toSubgraph.mpr <| List.getElem_mem _⟩
  map_rel' {a b} h := by
    grind [support_getElem_eq_getVert, Subgraph.coe_adj, pathGraph_adj, toSubgraph_adj_getVert,
      Subgraph.Adj.symm]

/-- A walk induces a homomorphism from a path graph to the graph -/
/-
**SimpleGraph.Walk.pathGraphHom** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：pathGraphHom : pathGraph (w.length + 1) ->g G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A walk induces a homomorphism from a path graph to the graph
-/
def pathGraphHom : pathGraph (w.length + 1) →g G :=
  w.toSubgraph.hom.comp w.pathGraphHomToSubgraph

variable {w} in
/-- The subgraph of a path is isomorphic to the path graph with the same number of vertices -/
/-
**SimpleGraph.Walk.IsPath.pathGraphIsoToSubgraph** 是 Mathlib 中的一个定义，位于命名空间 `Simp
leGraph.Walk.IsPath`。
形式化陈述：{V : Type u_3} →   [DecidableEq V] →     {G : SimpleGraph V} →       {u v 
: V} → {w : G.Walk u v} → w.IsPath → SimpleGraph.pathGraph (w.length + 1) ≃g w.t
oSubgraph.coe
参数：w.length + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgraph of a path is isomorphic to the path graph with the same number of v
ertices
-/
def IsPath.pathGraphIsoToSubgraph (hw : w.IsPath) :
    pathGraph (w.length + 1) ≃g w.toSubgraph.coe where
  toFun := w.pathGraphHomToSubgraph
  invFun v := ⟨w.support.idxOf v.val, by grind [w.mem_verts_toSubgraph]⟩
  left_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk, hw.support_nodup]
  right_inv := by grind [pathGraphHomToSubgraph, RelHom.coeFn_mk]
  map_rel_iff' := by
    refine ⟨fun hadj ↦ ?_, w.pathGraphHomToSubgraph.map_rel'⟩
    grind [w.toSubgraph_adj_iff.mp hadj, pathGraph_adj, getVert_eq_getD_support,
      pathGraphHomToSubgraph, RelHom.coeFn_mk, hw.support_nodup.getElem_inj_iff]

variable {w} in
/-- A path induces an injective homomorphism from a path graph to the graph -/
/-
**SimpleGraph.Walk.IsPath.pathGraphCopy** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.W
alk.IsPath`。
形式化陈述：{V : Type u_3} →   [DecidableEq V] →     {G : SimpleGraph V} → {u v : V} →
 {w : G.Walk u v} → w.IsPath → (SimpleGraph.pathGraph (w.length + 1)).Copy G
参数：SimpleGraph.pathGraph (w.length + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path induces an injective homomorphism from a path graph to the graph
-/
def IsPath.pathGraphCopy (hw : w.IsPath) : Copy (pathGraph <| w.length + 1) G :=
  w.toSubgraph.coeCopy.comp hw.pathGraphIsoToSubgraph.toCopy

variable {w} in
omit [DecidableEq V] in
/-
**SimpleGraph.Walk.IsPath.isContained_pathGraph** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u_3} {G : SimpleGraph V} {u v : V} {w : G.Walk u v},   w.IsPat
h → (SimpleGraph.pathGraph (w.length + 1)).IsContained G
参数：SimpleGraph.pathGraph (w.length + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsPath.isContained_pathGraph (hw : w.IsPath) : pathGraph (w.length + 1) ⊑ G := by
  classical
  exact ⟨hw.pathGraphCopy⟩

end Walk

end SimpleGraph

