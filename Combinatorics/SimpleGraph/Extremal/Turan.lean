/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Order.Partition.Equipartition

/-!
# Turán's theorem

In this file we prove Turán's theorem, the first important result of extremal graph theory,
which states that the `r + 1`-cliquefree graph on `n` vertices with the most edges is the complete
`r`-partite graph with part sizes as equal as possible (`turanGraph n r`).

The forward direction of the proof performs "Zykov symmetrisation", which first shows
constructively that non-adjacency is an equivalence relation in a maximal graph, so it must be
complete multipartite with the parts being the equivalence classes. Then basic manipulations
show that the graph is isomorphic to the Turán graph for the given parameters.

For the reverse direction we first show that a Turán-maximal graph exists, then transfer
the property through `turanGraph n r` using the isomorphism provided by the forward direction.

## Main declarations

* `SimpleGraph.IsTuranMaximal`: `G.IsTuranMaximal r` means that `G` has the most number of edges for
  its number of vertices while still being `r + 1`-cliquefree.
* `SimpleGraph.turanGraph n r`: The canonical `r + 1`-cliquefree Turán graph on `n` vertices.
* `SimpleGraph.IsTuranMaximal.finpartition`: The result of Zykov symmetrisation, a finpartition of
  the vertices such that two vertices are in the same part iff they are non-adjacent.
* `SimpleGraph.IsTuranMaximal.nonempty_iso_turanGraph`: The forward direction, an isomorphism
  between `G` satisfying `G.IsTuranMaximal r` and `turanGraph n r`.
* `isTuranMaximal_of_iso`: the reverse direction, `G.IsTuranMaximal r` given the isomorphism.
* `isTuranMaximal_iff_nonempty_iso_turanGraph`: Turán's theorem in full.

## References

* https://en.wikipedia.org/wiki/Turán%27s_theorem
-/

@[expose] public section

open Finset Fintype

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {n r : ℕ}

variable (G) in
/-- An `r + 1`-cliquefree graph is `r`-Turán-maximal if any other `r + 1`-cliquefree graph on
the same vertex set has the same or fewer number of edges. -/
/-
**SimpleGraph.IsTuranMaximal** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsTuranMaximal (r : Nat) : Prop
参数：r : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `r + 1`-cliquefree graph is `r`-Turán-maximal if any other `r + 1`-cliquefree
 graph on
the same vertex set has the same or fewer number of edges.
-/
def IsTuranMaximal (r : ℕ) : Prop := G.IsExtremal (CliqueFree · (r + 1))

section Defs

variable {H : SimpleGraph V}

/-- The canonical `r + 1`-cliquefree Turán graph on `n` vertices. -/
/-
**SimpleGraph.turanGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：turanGraph (n r : Nat) : SimpleGraph (Fin n) where Adj v w
参数：n r : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `r + 1`-cliquefree Turán graph on `n` vertices.
-/
def turanGraph (n r : ℕ) : SimpleGraph (Fin n) where Adj v w := v % r ≠ w % r
/-
**SimpleGraph.turanGraph_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：turanGraph_adj {v w} : (turanGraph n r).Adj v w ↔ v % r != w % r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma turanGraph_adj {v w} : (turanGraph n r).Adj v w ↔ v % r ≠ w % r :=
  .rfl
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableRel (turanGraph n r).Adj :=
  inferInstanceAs (DecidableRel fun v w : Fin n ↦ v % r ≠ w % r)

@[simp]
/-
**SimpleGraph.turanGraph_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：turanGraph_zero : turanGraph n 0 = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.mk.congr_simp`：∀ {V : Type u} (Adj Adj_1 : V → V → Prop) (e_
Adj : Adj = Adj_1) (symm : Std.Symm Adj) (loopless : Std.Irrefl Adj),   { Adj :=
 Adj, symm := s…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma turanGraph_zero : turanGraph n 0 = ⊤ := by simp [turanGraph, Fin.val_inj, Top.top]

@[simp]
/-
**SimpleGraph.turanGraph_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：turanGraph_eq_top : turanGraph n r = ⊤ ↔ r = 0 ∨ n <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.mk.injEq`：∀ {n : ℕ} (val : ℕ) (isLt : val < n) (val_1 : ℕ) (isLt_1 :
 val_1 < n), (⟨val, isLt⟩ = ⟨val_1, isLt_1⟩) = (val = val_1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Fin.val_inj`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b ↔ a = b
（共 31 条，此处仅展示前 30 条）
-/
theorem turanGraph_eq_top : turanGraph n r = ⊤ ↔ r = 0 ∨ n ≤ r := by
  simp_rw [SimpleGraph.ext_iff, funext_iff, turanGraph, top_adj, eq_iff_iff, not_iff_not]
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h
    use ⟨0, (Nat.pos_of_ne_zero h.1).trans h.2⟩, ⟨r, h.2⟩
    simp [h.1.symm]
  · rintro (rfl | h) a b
    · simp [Fin.val_inj]
    · rw [Nat.mod_eq_of_lt (a.2.trans_le h), Nat.mod_eq_of_lt (b.2.trans_le h), Fin.val_inj]
/-
**SimpleGraph.turanGraph_cliqueFree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：turanGraph_cliqueFree (hr : 0 < r) : (turanGraph n r).CliqueFree (r + 1)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.cliqueFree_iff`：cliqueFree_iff {n : Nat} : G.CliqueFree n ↔ 
IsEmpty (Copy (completeGraph <| Fin n) G)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Fintype.exists_ne_map_eq_of_card_lt`：exists_ne_map_eq_of_card_lt (f : α 
-> β) (h : Fintype.card β < Fintype.card α) : exists x y, x != y ∧ f x = f y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.mk.injEq`：∀ {n : ℕ} (val : ℕ) (isLt : val < n) (val_1 : ℕ) (isLt_1 :
 val_1 < n), (⟨val, isLt⟩ = ⟨val_1, isLt_1⟩) = (val = val_1)
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
-/
theorem turanGraph_cliqueFree (hr : 0 < r) : (turanGraph n r).CliqueFree (r + 1) := by
  rw [cliqueFree_iff]
  by_contra! ⟨f⟩
  obtain ⟨x, y, d, c⟩ := exists_ne_map_eq_of_card_lt (fun x ↦
    (⟨(f x).1 % r, Nat.mod_lt _ hr⟩ : Fin r)) (by simp)
  rw [Fin.mk.injEq] at c
  exact absurd c <| f.toHom.map_adj d

/-- An `r + 1`-cliquefree Turán-maximal graph is _not_ `r`-cliquefree
if it can accommodate such a clique. -/
/-
**SimpleGraph.not_cliqueFree_of_isTuranMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：not_cliqueFree_of_isTuranMaximal (hn : r <= card V) (hG : G.IsTuranMaximal
 r) : ¬G.CliqueFree r
参数：hn : r <= card V；hG : G.IsTuranMaximal r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.exists_subset_card_eq`：exists_subset_card_eq (hns : n <= #s) : ex
ists t subseteq s, #t = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.IsExtremal.le_iff_eq`：∀ {V : Type u_1} [inst : Fintype V] {G
 : SimpleGraph V} [inst_1 : DecidableRel G.Adj] {p : SimpleGraph V → Prop},   G.
IsExtremal p → ∀ {H : …
· 使用定理 `SimpleGraph.CliqueFree.sup_edge`：∀ {α : Type u_1} {G : SimpleGraph α} {n
 : ℕ},   G.CliqueFree n → ∀ (v w : α), (G ⊔ SimpleGraph.edge v w).CliqueFree (n 
+ 1)
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.edge_adj`：edge_adj (v w : V) : (edge s t).Adj v w ↔ (v = s ∧
 w = t ∨ v = t ∧ w = s) ∧ v != w

--- 原说明 ---
An `r + 1`-cliquefree Turán-maximal graph is _not_ `r`-cliquefree
if it can accommodate such a clique.
-/
theorem not_cliqueFree_of_isTuranMaximal (hn : r ≤ card V) (hG : G.IsTuranMaximal r) :
    ¬G.CliqueFree r := by
  rintro h
  obtain ⟨K, _, rfl⟩ := exists_subset_card_eq hn
  obtain ⟨a, -, b, -, hab, hGab⟩ : ∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ ¬ G.Adj a b := by
    simpa only [isNClique_iff, IsClique, Set.Pairwise, mem_coe, ne_eq, and_true, not_forall,
      exists_prop, exists_and_right] using h K
  exact hGab <| le_sup_right.trans_eq ((hG.le_iff_eq <| h.sup_edge _ _).1 le_sup_left).symm <|
    (edge_adj ..).2 ⟨Or.inl ⟨rfl, rfl⟩, hab⟩
/-
**SimpleGraph.exists_isTuranMaximal** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：exists_isTuranMaximal (hr : 0 < r) : exists H : SimpleGraph V, exists _ : 
DecidableRel H.Adj, H.IsTuranMaximal r
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.cliqueFree_bot`：cliqueFree_bot (h : 2 <= n) : (⊥ : SimpleGra
ph α).CliqueFree n
-/
lemma exists_isTuranMaximal (hr : 0 < r) :
    ∃ H : SimpleGraph V, ∃ _ : DecidableRel H.Adj, H.IsTuranMaximal r := by
  simpa [IsTuranMaximal, exists_isExtremal_iff_exists] using ⟨⊥, cliqueFree_bot (by lia)⟩

end Defs

namespace IsTuranMaximal

variable {s t u : V}

/-- In a Turán-maximal graph, non-adjacent vertices have the same degree. -/
/-
**SimpleGraph.IsTuranMaximal.degree_eq_of_not_adj** 是 Mathlib 中的一个引理，位于命名空间 `Sim
pleGraph.IsTuranMaximal`。
形式化陈述：degree_eq_of_not_adj (h : G.IsTuranMaximal r) (hn : ¬G.Adj s t) : G.degree
 s = G.degree t
参数：h : G.IsTuranMaximal r；hn : ¬G.Adj s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `SimpleGraph.CliqueFree.replaceVertex`：∀ {α : Type u_1} {G : SimpleGraph 
α} {n : ℕ} [inst : DecidableEq α],   G.CliqueFree n → ∀ (s t : α), (G.replaceVer
tex s t).CliqueFree n
· 使用定理 `SimpleGraph.card_edgeFinset_replaceVertex_of_not_adj`：card_edgeFinset_re
placeVertex_of_not_adj (hn : ¬G.Adj s t) : #(G.replaceVertex s t).edgeFinset = #
G.edgeFinset + G.degree s - G.degree t
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `SimpleGraph.adj_comm`：adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `SimpleGraph.IsExtremal.eq_1`：∀ {V : Type u_1} [inst : Fintype V] (G : Si
mpleGraph V) [inst_1 : DecidableRel G.Adj] (p : SimpleGraph V → Prop),   G.IsExt
remal p =     (p …
· 使用定理 `SimpleGraph.IsTuranMaximal.eq_1`：∀ {V : Type u_1} [inst : Fintype V] (G 
: SimpleGraph V) [inst_1 : DecidableRel G.Adj] (r : ℕ),   G.IsTuranMaximal r = G
.IsExtremal fun x => …

--- 原说明 ---
In a Turán-maximal graph, non-adjacent vertices have the same degree.
-/
lemma degree_eq_of_not_adj (h : G.IsTuranMaximal r) (hn : ¬G.Adj s t) :
    G.degree s = G.degree t := by
  rw [IsTuranMaximal, IsExtremal] at h; contrapose! h; intro cf
  wlog hd : G.degree t < G.degree s generalizing G t s
  · replace hd : G.degree s < G.degree t := lt_of_le_of_ne (le_of_not_gt hd) h
    exact this (by rwa [adj_comm] at hn) hd.ne' cf hd
  classical
  use G.replaceVertex s t, inferInstance, cf.replaceVertex s t
  have := G.card_edgeFinset_replaceVertex_of_not_adj hn
  lia

/-- In a Turán-maximal graph, non-adjacency is transitive. -/
/-
**SimpleGraph.IsTuranMaximal.not_adj_trans** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h.IsTuranMaximal`。
形式化陈述：not_adj_trans (h : G.IsTuranMaximal r) (hts : ¬G.Adj t s) (hsu : ¬G.Adj s 
u) : ¬G.Adj t u
参数：h : G.IsTuranMaximal r；hts : ¬G.Adj t s；hsu : ¬G.Adj s u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用引理 `SimpleGraph.IsTuranMaximal.degree_eq_of_not_adj`：degree_eq_of_not_adj (h
 : G.IsTuranMaximal r) (hn : ¬G.Adj s t) : G.degree s = G.degree t
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.CliqueFree.replaceVertex`：∀ {α : Type u_1} {G : SimpleGraph 
α} {n : ℕ} [inst : DecidableEq α],   G.CliqueFree n → ∀ (s t : α), (G.replaceVer
tex s t).CliqueFree n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.adj_replaceVertex_iff_of_ne`：adj_replaceVertex_iff_of_ne {v 
w : V} (hv : v != t) (hw : w != t) : (G.replaceVertex s t).Adj v w ↔ G.Adj v w
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SimpleGraph.card_edgeFinset_replaceVertex_of_not_adj`：card_edgeFinset_re
placeVertex_of_not_adj (hn : ¬G.Adj s t) : #(G.replaceVertex s t).edgeFinset = #
G.edgeFinset + G.degree s - G.degree t
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `SimpleGraph.degree.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (v : V) [i
nst : Fintype ↑(G.neighborSet v)], G.degree v = (G.neighborFinset v).card
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
In a Turán-maximal graph, non-adjacency is transitive.
-/
lemma not_adj_trans (h : G.IsTuranMaximal r) (hts : ¬G.Adj t s) (hsu : ¬G.Adj s u) :
    ¬G.Adj t u := by
  have hst : ¬G.Adj s t := fun a ↦ hts a.symm
  have dst := h.degree_eq_of_not_adj hst
  have dsu := h.degree_eq_of_not_adj hsu
  rw [IsTuranMaximal, IsExtremal] at h; contrapose! h; intro cf
  classical
  use (G.replaceVertex s t).replaceVertex s u, inferInstance,
    (cf.replaceVertex s t).replaceVertex s u
  have nst : s ≠ t := fun a ↦ hsu (a ▸ h)
  have ntu : t ≠ u := G.ne_of_adj h
  have := (G.adj_replaceVertex_iff_of_ne s nst ntu.symm).not.mpr hsu
  rw [card_edgeFinset_replaceVertex_of_not_adj _ this,
    card_edgeFinset_replaceVertex_of_not_adj _ hst, dst, Nat.add_sub_cancel]
  have l1 : (G.replaceVertex s t).degree s = G.degree s := by
    unfold degree; congr 1; ext v
    simp_rw [mem_neighborFinset]
    by_cases eq : v = t
    · simpa only [eq, not_adj_replaceVertex_same, false_iff]
    · rw [G.adj_replaceVertex_iff_of_ne s nst eq]
  have l2 : (G.replaceVertex s t).degree u = G.degree u - 1 := by
    rw [degree, degree, ← card_singleton t, ← card_sdiff_of_subset (by simp [h.symm])]
    congr 1; ext v
    simp_rw [mem_neighborFinset, mem_sdiff, mem_singleton, replaceVertex]
    split_ifs <;> simp_all [adj_comm]
  have l3 : 0 < G.degree u := by rw [G.degree_pos_iff_exists_adj u]; use t, h.symm
  lia

variable (h : G.IsTuranMaximal r)
include h

/-- In a Turán-maximal graph, non-adjacency is an equivalence relation. -/
/-
**SimpleGraph.IsTuranMaximal.equivalence_not_adj** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.IsTuranMaximal`。
形式化陈述：equivalence_not_adj : Equivalence (¬G.Adj · ·) where refl
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `SimpleGraph.IsTuranMaximal.not_adj_trans`：not_adj_trans (h : G.IsTuranMa
ximal r) (hts : ¬G.Adj t s) (hsu : ¬G.Adj s u) : ¬G.Adj t u

--- 原说明 ---
In a Turán-maximal graph, non-adjacency is an equivalence relation.
-/
theorem equivalence_not_adj : Equivalence (¬G.Adj · ·) where
  refl := by simp
  symm := by simp [adj_comm]
  trans := h.not_adj_trans

/-- The non-adjacency setoid over the vertices of a Turán-maximal graph
induced by `equivalence_not_adj`. -/
@[instance_reducible]
/-
**SimpleGraph.IsTuranMaximal.setoid** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.IsTur
anMaximal`。
形式化陈述：setoid : Setoid V
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsTuranMaximal.equivalence_not_adj`：equivalence_not_adj : Eq
uivalence (¬G.Adj · ·) where refl

--- 原说明 ---
The non-adjacency setoid over the vertices of a Turán-maximal graph
induced by `equivalence_not_adj`.
-/
def setoid : Setoid V := ⟨_, h.equivalence_not_adj⟩
/-
**SimpleGraph.IsTuranMaximal.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.IsTuranMaxi
mal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableRel h.setoid.r :=
  inferInstanceAs <| DecidableRel (¬G.Adj · ·)

/-- The finpartition derived from `h.setoid`. -/
/-
**SimpleGraph.IsTuranMaximal.finpartition** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph
.IsTuranMaximal`。
形式化陈述：finpartition [DecidableEq V] : Finpartition (univ : Finset V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finpartition derived from `h.setoid`.
-/
def finpartition [DecidableEq V] : Finpartition (univ : Finset V) := Finpartition.ofSetoid h.setoid
/-
**SimpleGraph.IsTuranMaximal.not_adj_iff_part_eq** 是 Mathlib 中的一个引理，位于命名空间 `Simp
leGraph.IsTuranMaximal`。
形式化陈述：not_adj_iff_part_eq [DecidableEq V] : ¬G.Adj s t ↔ h.finpartition.part s =
 h.finpartition.part t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.mem_part_ofSetoid_iff_rel`：mem_part_ofSetoid_iff_rel {s : S
etoid α} [DecidableRel s.r] {b : α} : b in (ofSetoid s).part a ↔ s a b
· 使用引理 `Finpartition.mem_part_iff_part_eq_part`：mem_part_iff_part_eq_part {b : α
} (ha : a in s) (hb : b in s) : a in P.part b ↔ P.part a = P.part b
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma not_adj_iff_part_eq [DecidableEq V] :
    ¬G.Adj s t ↔ h.finpartition.part s = h.finpartition.part t := by
  change h.setoid.r s t ↔ _
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  let fp := h.finpartition
  change t ∈ fp.part s ↔ fp.part s = fp.part t
  rw [fp.mem_part_iff_part_eq_part (mem_univ t) (mem_univ s), eq_comm]
/-
**SimpleGraph.IsTuranMaximal.degree_eq_card_sub_part_card** 是 Mathlib 中的一个引理，位于命
名空间 `SimpleGraph.IsTuranMaximal`。
形式化陈述：degree_eq_card_sub_part_card [DecidableEq V] : G.degree s = card V - #(h.f
inpartition.part s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_tsub_of_add_eq`：eq_tsub_of_add_eq (h : a + c = b) : a = b - c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.card_filter_add_card_filter_not`：card_filter_add_card_filter_not 
(p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] : #(s.filter p) +
 #(s.filter fun a => ¬ p a) …
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finpartition.mem_part_ofSetoid_iff_rel`：mem_part_ofSetoid_iff_rel {s : S
etoid α} [DecidableRel s.r] {b : α} : b in (ofSetoid s).part a ↔ s a b
-/
lemma degree_eq_card_sub_part_card [DecidableEq V] :
    G.degree s = card V - #(h.finpartition.part s) :=
  calc
    _ = #{t | G.Adj s t} := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = card V - #{t | ¬G.Adj s t} :=
      eq_tsub_of_add_eq (card_filter_add_card_filter_not _)
    _ = _ := by
      congr; ext; rw [mem_filter]
      convert! Finpartition.mem_part_ofSetoid_iff_rel.symm
      simp +instances [setoid]

/-- The parts of a Turán-maximal graph form an equipartition. -/
/-
**SimpleGraph.IsTuranMaximal.isEquipartition** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.IsTuranMaximal`。
形式化陈述：isEquipartition [DecidableEq V] : h.finpartition.IsEquipartition
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `Finpartition.not_isEquipartition`：not_isEquipartition : ¬P.IsEquipartiti
on ↔ exists a in P.parts, exists b in P.parts, #b + 1 < #a
· 使用定理 `Finpartition.nonempty_of_mem_parts`：nonempty_of_mem_parts {a : Finset α}
 (ha : a in P.parts) : a.Nonempty
· 使用定理 `SimpleGraph.IsTuranMaximal.eq_1`：∀ {V : Type u_1} [inst : Fintype V] (G 
: SimpleGraph V) [inst_1 : DecidableRel G.Adj] (r : ℕ),   G.IsTuranMaximal r = G
.IsExtremal fun x => …
· 使用定理 `SimpleGraph.IsExtremal.eq_1`：∀ {V : Type u_1} [inst : Fintype V] (G : Si
mpleGraph V) [inst_1 : DecidableRel G.Adj] (p : SimpleGraph V → Prop),   G.IsExt
remal p =     (p …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.CliqueFree.replaceVertex`：∀ {α : Type u_1} {G : SimpleGraph 
α} {n : ℕ} [inst : DecidableEq α],   G.CliqueFree n → ∀ (s t : α), (G.replaceVer
tex s t).CliqueFree n
· 使用引理 `Finpartition.part_eq_of_mem`：part_eq_of_mem (ht : t in P.parts) (hat : a
 in t) : P.part a = t
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `SimpleGraph.IsTuranMaximal.not_adj_iff_part_eq`：not_adj_iff_part_eq [Dec
idableEq V] : ¬G.Adj s t ↔ h.finpartition.part s = h.finpartition.part t
· 使用定理 `SimpleGraph.card_edgeFinset_replaceVertex_of_adj`：card_edgeFinset_replac
eVertex_of_adj (ha : G.Adj s t) : #(G.replaceVertex s t).edgeFinset = #G.edgeFin
set + G.degree s - G.degree t - 1
· 使用引理 `SimpleGraph.IsTuranMaximal.degree_eq_card_sub_part_card`：degree_eq_card_
sub_part_card [DecidableEq V] : G.degree s = card V - #(h.finpartition.part s)
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ

--- 原说明 ---
The parts of a Turán-maximal graph form an equipartition.
-/
theorem isEquipartition [DecidableEq V] : h.finpartition.IsEquipartition := by
  set fp := h.finpartition
  by_contra hn
  rw [Finpartition.not_isEquipartition] at hn
  obtain ⟨large, hl, small, hs, ineq⟩ := hn
  obtain ⟨w, hw⟩ := fp.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := fp.nonempty_of_mem_parts hs
  apply absurd h
  rw [IsTuranMaximal, IsExtremal]; push Not; intro cf
  use G.replaceVertex v w, inferInstance, cf.replaceVertex v w
  have large_eq := fp.part_eq_of_mem hl hw
  have small_eq := fp.part_eq_of_mem hs hv
  have ha : G.Adj v w := by
    by_contra hn; rw [h.not_adj_iff_part_eq, small_eq, large_eq] at hn
    rw [hn] at ineq; lia
  rw [G.card_edgeFinset_replaceVertex_of_adj ha,
    degree_eq_card_sub_part_card h, small_eq, degree_eq_card_sub_part_card h, large_eq]
  have : #large ≤ card V := by simpa using card_le_card large.subset_univ
  lia
/-
**SimpleGraph.IsTuranMaximal.card_parts_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h.IsTuranMaximal`。
形式化陈述：card_parts_le [DecidableEq V] : #h.finpartition.parts <= r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Finpartition.exists_subset_part_bijOn`：exists_subset_part_bijOn : exists
 r subseteq s, Set.BijOn P.part r P.parts
· 使用定理 `SimpleGraph.IsNClique.not_cliqueFree`：∀ {α : Type u_1} {G : SimpleGraph 
α} {n : ℕ} {s : Finset α}, G.IsNClique n s → ¬G.CliqueFree n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.IsTuranMaximal.not_adj_iff_part_eq`：not_adj_iff_part_eq [Dec
idableEq V] : ¬G.Adj s t ↔ h.finpartition.part s = h.finpartition.part t
· 使用定理 `SimpleGraph.CliqueFree.mono`：∀ {α : Type u_1} {G : SimpleGraph α} {m n :
 ℕ}, m ≤ n → G.CliqueFree m → G.CliqueFree n
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.card_eq_of_equiv`：Finset.card_eq_of_equiv {s : Finset α} {t : Fin
set β} (i : s ≃ t) : #s = #t
-/
lemma card_parts_le [DecidableEq V] : #h.finpartition.parts ≤ r := by
  by_contra! l
  obtain ⟨z, -, hz⟩ := h.finpartition.exists_subset_part_bijOn
  have ncf : ¬G.CliqueFree #z := by
    refine IsNClique.not_cliqueFree ⟨fun v hv w hw hn ↦ ?_, rfl⟩
    contrapose hn
    exact hz.injOn hv hw (by rwa [← h.not_adj_iff_part_eq])
  rw [Finset.card_eq_of_equiv hz.equiv] at ncf
  exact absurd (h.1.mono (Nat.succ_le_of_lt l)) ncf

/-- There are `min n r` parts in a graph on `n` vertices satisfying `G.IsTuranMaximal r`.
`min` handles the `n < r` case, when `G` is complete but still `r + 1`-cliquefree
for having insufficiently many vertices. -/
/-
**SimpleGraph.IsTuranMaximal.card_parts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.I
sTuranMaximal`。
形式化陈述：card_parts [DecidableEq V] : #h.finpartition.parts = min (card V) r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `Finpartition.card_parts_le_card`：card_parts_le_card : #P.parts <= #s
· 使用引理 `SimpleGraph.IsTuranMaximal.card_parts_le`：card_parts_le [DecidableEq V] 
: #h.finpartition.parts <= r
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`：exists_ne_map_eq_of_card_
lt_of_maps_to (hc : #t < #s) {f : α -> β} (hf : Set.MapsTo f s t) : exists x in 
s, exists y in s, x != y ∧ f x = f …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lt_min_iff`：lt_min_iff : a < min b c ↔ a < b ∧ a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finpartition.part_mem`：part_mem : P.part a in P.parts ↔ a in s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `SimpleGraph.IsTuranMaximal.eq_1`：∀ {V : Type u_1} [inst : Fintype V] (G 
: SimpleGraph V) [inst_1 : DecidableRel G.Adj] (r : ℕ),   G.IsTuranMaximal r = G
.IsExtremal fun x => …
· 使用定理 `SimpleGraph.IsExtremal.eq_1`：∀ {V : Type u_1} [inst : Fintype V] (G : Si
mpleGraph V) [inst_1 : DecidableRel G.Adj] (p : SimpleGraph V → Prop),   G.IsExt
remal p =     (p …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `SimpleGraph.IsTuranMaximal.not_adj_iff_part_eq`：not_adj_iff_part_eq [Dec
idableEq V] : ¬G.Adj s t ↔ h.finpartition.part s = h.finpartition.part t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.CliqueFree.sup_edge`：∀ {α : Type u_1} {G : SimpleGraph α} {n
 : ℕ},   G.CliqueFree n → ∀ (v w : α), (G ⊔ SimpleGraph.edge v w).CliqueFree (n 
+ 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `SimpleGraph.card_edgeFinset_sup_edge`：card_edgeFinset_sup_edge [Fintype 
(edgeSet (G ⊔ edge s t))] (hn : ¬G.Adj s t) (h : s != t) : #(G ⊔ edge s t).edgeF
inset = #G.edgeFinset + 1
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1

--- 原说明 ---
There are `min n r` parts in a graph on `n` vertices satisfying `G.IsTuranMaxima
l r`.
`min` handles the `n < r` case, when `G` is complete but still `r + 1`-cliquefre
e
for having insufficiently many vertices.
-/
theorem card_parts [DecidableEq V] : #h.finpartition.parts = min (card V) r := by
  set fp := h.finpartition
  apply le_antisymm (le_min fp.card_parts_le_card h.card_parts_le)
  by_contra! l
  rw [lt_min_iff] at l
  obtain ⟨x, -, y, -, hn, he⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to l.1 fun a _ ↦ fp.part_mem.2 (mem_univ a)
  apply absurd h
  rw [IsTuranMaximal, IsExtremal]; push Not; rintro -
  have cf : G.CliqueFree r := by
    simp_rw [← cliqueFinset_eq_empty_iff, cliqueFinset, filter_eq_empty_iff, mem_univ,
      forall_true_left, isNClique_iff, and_comm, not_and, isClique_iff, Set.Pairwise]
    intro z zc; push Not; simp_rw [h.not_adj_iff_part_eq]
    exact exists_ne_map_eq_of_card_lt_of_maps_to (zc.symm ▸ l.2) fun a _ ↦
      fp.part_mem.2 (mem_univ a)
  use G ⊔ edge x y, inferInstance, cf.sup_edge x y
  convert! Nat.lt_add_one #G.edgeFinset
  convert! G.card_edgeFinset_sup_edge _ hn
  rwa [h.not_adj_iff_part_eq]

set_option backward.isDefEq.respectTransparency.types false in
/-- **Turán's theorem**, forward direction.

Any `r + 1`-cliquefree Turán-maximal graph on `n` vertices is isomorphic to `turanGraph n r`. -/
/-
**SimpleGraph.IsTuranMaximal.nonempty_iso_turanGraph** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.IsTuranMaximal`。
形式化陈述：nonempty_iso_turanGraph : Nonempty (G ≃g turanGraph (card V) r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.IsEquipartition.exists_partPreservingEquiv`：∀ {α : Type u_1
} [inst : DecidableEq α] {s : Finset α} {P : Finpartition s},   P.IsEquipartitio
n → ∃ f, ∀ (a b : ↥s), P.part ↑a = P.part ↑b …
· 使用定理 `SimpleGraph.IsTuranMaximal.isEquipartition`：isEquipartition [DecidableEq
 V] : h.finpartition.IsEquipartition
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.subtypeUnivEquiv_symm_apply`：∀ {α : Sort u_9} {p : α → Prop} (h : 
∀ (x : α), p x) (x : α), (Equiv.subtypeUnivEquiv h).symm x = ⟨x, ⋯⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用引理 `SimpleGraph.IsTuranMaximal.not_adj_iff_part_eq`：not_adj_iff_part_eq [Dec
idableEq V] : ¬G.Adj s t ↔ h.finpartition.part s = h.finpartition.part t
· 使用定理 `SimpleGraph.IsTuranMaximal.card_parts`：card_parts [DecidableEq V] : #h.f
inpartition.parts = min (card V) r
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c

--- 原说明 ---
**Turán's theorem**, forward direction.

Any `r + 1`-cliquefree Turán-maximal graph on `n` vertices is isomorphic to `tur
anGraph n r`.
-/
theorem nonempty_iso_turanGraph :
    Nonempty (G ≃g turanGraph (card V) r) := by
  classical
  obtain ⟨zm, zp⟩ := h.isEquipartition.exists_partPreservingEquiv
  use (Equiv.subtypeUnivEquiv mem_univ).symm.trans zm
  intro a b
  simp_rw [turanGraph_adj, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply]
  have := zp ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩
  rw [← h.not_adj_iff_part_eq] at this
  rw [← not_iff_not, not_ne_iff, this, card_parts]
  rcases le_or_gt r (card V) with c | c
  · rw [min_eq_right c]; rfl
  · have lc : ∀ x, zm ⟨x, _⟩ < card V := fun x ↦ (zm ⟨x, mem_univ x⟩).2
    rw [min_eq_left c.le, Nat.mod_eq_of_lt (lc a), Nat.mod_eq_of_lt (lc b),
      ← Nat.mod_eq_of_lt ((lc a).trans c), ← Nat.mod_eq_of_lt ((lc b).trans c)]; rfl

end IsTuranMaximal

/-- **Turán's theorem**, reverse direction.

Any graph isomorphic to `turanGraph n r` is itself Turán-maximal if `0 < r`. -/
/-
**SimpleGraph.isTuranMaximal_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isTuranMaximal_of_iso (f : G ≃g turanGraph n r) (hr : 0 < r) : G.IsTuranMa
ximal r
参数：f : G ≃g turanGraph n r；hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_isTuranMaximal`：exists_isTuranMaximal (hr : 0 < r) : 
exists H : SimpleGraph V, exists _ : DecidableRel H.Adj, H.IsTuranMaximal r
· 使用定理 `SimpleGraph.IsTuranMaximal.nonempty_iso_turanGraph`：nonempty_iso_turanGr
aph : Nonempty (G ≃g turanGraph (card V) r)
· 使用定理 `SimpleGraph.CliqueFree.comap`：∀ {α : Type u_1} {β : Type u_2} {G : Simpl
eGraph α} {n : ℕ} {H : SimpleGraph β},   H.IsContained G → G.CliqueFree n → H.Cl
iqueFree n
· 使用定理 `SimpleGraph.Iso.isContained`：∀ {V : Type u_1} {W : Type u_2} {G : Simple
Graph V} {H : SimpleGraph W} (e : G ≃g H), G.IsContained H
· 使用定理 `SimpleGraph.turanGraph_cliqueFree`：turanGraph_cliqueFree (hr : 0 < r) : 
(turanGraph n r).CliqueFree (r + 1)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.Iso.card_edgeFinset_eq`：card_edgeFinset_eq (f : G ≃g G') [Fi
ntype G.edgeSet] [Fintype G'.edgeSet] : #G.edgeFinset = #G'.edgeFinset
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `SimpleGraph.Iso.card_eq`：card_eq [Fintype V] [Fintype W] : Fintype.card 
V = Fintype.card W

--- 原说明 ---
**Turán's theorem**, reverse direction.

Any graph isomorphic to `turanGraph n r` is itself Turán-maximal if `0 < r`.
-/
theorem isTuranMaximal_of_iso (f : G ≃g turanGraph n r) (hr : 0 < r) : G.IsTuranMaximal r := by
  obtain ⟨J, _, j⟩ := exists_isTuranMaximal (V := V) hr
  obtain ⟨g⟩ := j.nonempty_iso_turanGraph
  rw [f.card_eq, Fintype.card_fin] at g
  use (turanGraph_cliqueFree (n := n) hr).comap f.isContained,
    fun H _ cf ↦ (f.symm.comp g).card_edgeFinset_eq ▸ j.2 cf

/-- Turán-maximality with `0 < r` transfers across graph isomorphisms. -/
/-
**SimpleGraph.IsTuranMaximal.iso** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsTuranM
aximal`。
形式化陈述：∀ {V : Type u_1} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : Decidabl
eRel G.Adj] {r : ℕ} {W : Type u_2}   [inst_2 : Fintype W] {H : SimpleGraph W} [i
nst_3 : DecidableRel H.Adj],   G.IsTuranMaximal r → ∀ (f : G ≃g H), 0 < r → H.Is
TuranMaximal r
参数：f : G ≃g H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.isTuranMaximal_of_iso`：isTuranMaximal_of_iso (f : G ≃g turan
Graph n r) (hr : 0 < r) : G.IsTuranMaximal r
· 使用定理 `SimpleGraph.IsTuranMaximal.nonempty_iso_turanGraph`：nonempty_iso_turanGr
aph : Nonempty (G ≃g turanGraph (card V) r)

--- 原说明 ---
Turán-maximality with `0 < r` transfers across graph isomorphisms.
-/
theorem IsTuranMaximal.iso {W : Type*} [Fintype W] {H : SimpleGraph W}
    [DecidableRel H.Adj] (h : G.IsTuranMaximal r) (f : G ≃g H) (hr : 0 < r) : H.IsTuranMaximal r :=
  isTuranMaximal_of_iso (h.nonempty_iso_turanGraph.some.comp f.symm) hr

/-- For `0 < r`, `turanGraph n r` is Turán-maximal. -/
/-
**SimpleGraph.isTuranMaximal_turanGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isTuranMaximal_turanGraph (hr : 0 < r) : (turanGraph n r).IsTuranMaximal r
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.isTuranMaximal_of_iso`：isTuranMaximal_of_iso (f : G ≃g turan
Graph n r) (hr : 0 < r) : G.IsTuranMaximal r

--- 原说明 ---
For `0 < r`, `turanGraph n r` is Turán-maximal.
-/
theorem isTuranMaximal_turanGraph (hr : 0 < r) : (turanGraph n r).IsTuranMaximal r :=
  isTuranMaximal_of_iso Iso.refl hr

/-- **Turán's theorem**. `turanGraph n r` is, up to isomorphism, the unique
`r + 1`-cliquefree Turán-maximal graph on `n` vertices. -/
/-
**SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph`。
形式化陈述：isTuranMaximal_iff_nonempty_iso_turanGraph (hr : 0 < r) : G.IsTuranMaximal
 r ↔ Nonempty (G ≃g turanGraph (card V) r)
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsTuranMaximal.nonempty_iso_turanGraph`：nonempty_iso_turanGr
aph : Nonempty (G ≃g turanGraph (card V) r)
· 使用定理 `SimpleGraph.isTuranMaximal_of_iso`：isTuranMaximal_of_iso (f : G ≃g turan
Graph n r) (hr : 0 < r) : G.IsTuranMaximal r

--- 原说明 ---
**Turán's theorem**. `turanGraph n r` is, up to isomorphism, the unique
`r + 1`-cliquefree Turán-maximal graph on `n` vertices.
-/
theorem isTuranMaximal_iff_nonempty_iso_turanGraph (hr : 0 < r) :
    G.IsTuranMaximal r ↔ Nonempty (G ≃g turanGraph (card V) r) :=
  ⟨fun h ↦ h.nonempty_iso_turanGraph, fun h ↦ isTuranMaximal_of_iso h.some hr⟩

variable {α : Type*} [Fintype α] [Nontrivial α]
/-
**SimpleGraph.isExtremal_top_free_iff_isTuranMaximal** 是 Mathlib 中的一个引理，位于命名空间 `
SimpleGraph`。
形式化陈述：isExtremal_top_free_iff_isTuranMaximal : G.IsExtremal (⊤ : SimpleGraph α).
Free ↔ G.IsTuranMaximal (card α - 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.sub_one_add_one`：∀ {a : ℕ}, a ≠ 0 → a - 1 + 1 = a
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isExtremal_top_free_iff_isTuranMaximal :
    G.IsExtremal (⊤ : SimpleGraph α).Free ↔ G.IsTuranMaximal (card α - 1) := by
  simp_rw [IsTuranMaximal, IsExtremal,
    Nat.sub_one_add_one Fintype.card_ne_zero, cliqueFree_iff_top_free]
/-
**SimpleGraph.isExtremal_top_free_turanGraph** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：isExtremal_top_free_turanGraph : (turanGraph n (card α - 1)).IsExtremal (⊤
 : SimpleGraph α).Free
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.isExtremal_top_free_iff_isTuranMaximal`：isExtremal_top_free_
iff_isTuranMaximal : G.IsExtremal (⊤ : SimpleGraph α).Free ↔ G.IsTuranMaximal (c
ard α - 1)
· 使用定理 `SimpleGraph.isTuranMaximal_turanGraph`：isTuranMaximal_turanGraph (hr : 0
 < r) : (turanGraph n r).IsTuranMaximal r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.sub_pos_iff_lt`：∀ {n m : ℕ}, 0 < n - m ↔ m < n
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
-/
lemma isExtremal_top_free_turanGraph :
    (turanGraph n (card α - 1)).IsExtremal (⊤ : SimpleGraph α).Free := by
  rw [isExtremal_top_free_iff_isTuranMaximal]
  exact isTuranMaximal_turanGraph (Nat.sub_pos_iff_lt.mpr Fintype.one_lt_card)

/-- The extremal numbers of `⊤` are equal to the number of edges in `turanGraph`. -/
/-
**SimpleGraph.extremalNumber_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：extremalNumber_top : extremalNumber n (⊤ : SimpleGraph α) = #(turanGraph n
 (card α - 1)).edgeFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用引理 `SimpleGraph.card_edgeFinset_of_isExtremal_free`：card_edgeFinset_of_isExt
remal_free (h : G.IsExtremal H.Free) : #G.edgeFinset = extremalNumber (card V) H
· 使用引理 `SimpleGraph.isExtremal_top_free_turanGraph`：isExtremal_top_free_turanGra
ph : (turanGraph n (card α - 1)).IsExtremal (⊤ : SimpleGraph α).Free

--- 原说明 ---
The extremal numbers of `⊤` are equal to the number of edges in `turanGraph`.
-/
theorem extremalNumber_top :
    extremalNumber n (⊤ : SimpleGraph α) = #(turanGraph n (card α - 1)).edgeFinset := by
  conv =>
    enter [1, 1]
    rw [← Fintype.card_fin n]
  exact (card_edgeFinset_of_isExtremal_free isExtremal_top_free_turanGraph).symm

/-- The `turanGraph` is, up to isomorphism, the unique extremal graph forbidding `⊤`.

This is **Turán's theorem** restated in terms of the extremal numbers of `⊤`.
See `SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`. -/
/-
**SimpleGraph.card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph*
* 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph : (⊤ : S
impleGraph α).Free G ∧ #G.edgeFinset = extremalNumber (card V) (⊤ : SimpleGraph 
α) ↔ Nonempty (G ≃g turanGraph (card V) (card α - 1))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`：isTuranMaximal_i
ff_nonempty_iso_turanGraph (hr : 0 < r) : G.IsTuranMaximal r ↔ Nonempty (G ≃g tu
ranGraph (card V) r)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.sub_pos_iff_lt`：∀ {n m : ℕ}, 0 < n - m ↔ m < n
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用引理 `SimpleGraph.isExtremal_top_free_iff_isTuranMaximal`：isExtremal_top_free_
iff_isTuranMaximal : G.IsExtremal (⊤ : SimpleGraph α).Free ↔ G.IsTuranMaximal (c
ard α - 1)
· 使用定理 `SimpleGraph.isExtremal_free_iff`：isExtremal_free_iff : G.IsExtremal H.Fr
ee ↔ H.Free G ∧ #G.edgeFinset = extremalNumber (card V) H
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `turanGraph` is, up to isomorphism, the unique extremal graph forbidding `⊤`
.

This is **Turán's theorem** restated in terms of the extremal numbers of `⊤`.
See `SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`.
-/
theorem card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph :
    (⊤ : SimpleGraph α).Free G ∧ #G.edgeFinset = extremalNumber (card V) (⊤ : SimpleGraph α)
      ↔ Nonempty (G ≃g turanGraph (card V) (card α - 1)) := by
  rw [← isTuranMaximal_iff_nonempty_iso_turanGraph (Nat.sub_pos_iff_lt.mpr one_lt_card),
    ← isExtremal_top_free_iff_isTuranMaximal, isExtremal_free_iff]

/-! ### Number of edges in the Turán graph -/

/-
**SimpleGraph.sum_ne_add_mod_eq_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Number of edges in the Turán graph
-/
private lemma sum_ne_add_mod_eq_sub_one {c : ℕ} :
    ∑ w ∈ range r, (if c % r ≠ (n + w) % r then 1 else 0) = r - 1 := by
  rcases r.eq_zero_or_pos with rfl | hr; · simp
  suffices #{i ∈ range r | c % r = (n + i) % r} = 1 by
    rw [← card_filter, ← this]; apply Nat.eq_sub_of_add_eq'
    rw [card_filter_add_card_filter_not, card_range]
  apply le_antisymm
  · change #{i ∈ range r | _ ≡ _ [MOD r]} ≤ 1
    rw [card_le_one_iff]; intro w x mw mx
    simp only [mem_filter, mem_range] at mw mx
    have := mw.2.symm.trans mx.2
    rw [Nat.ModEq.add_iff_left rfl] at this
    change w % r = x % r at this
    rwa [Nat.mod_eq_of_lt mw.1, Nat.mod_eq_of_lt mx.1] at this
  · rw [one_le_card]; use ((r - 1) * n + c) % r
    simp only [mem_filter, mem_range]; refine ⟨Nat.mod_lt _ hr, ?_⟩
    rw [Nat.add_mod_mod, ← add_assoc, ← one_add_mul, show 1 + (r - 1) = r by lia,
      Nat.mul_add_mod_self_left]

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.card_edgeFinset_turanGraph_add** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：card_edgeFinset_turanGraph_add : #(turanGraph (n + r) r).edgeFinset = #(tu
ranGraph n r).edgeFinset + n * (r - 1) + r.choose 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SimpleGraph.neighborFinset_eq_filter`：neighborFinset_eq_filter {v : V} [
DecidableRel G.Adj] : G.neighborFinset v = ({w | G.Adj v w} : Finset _)
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Finset.card_filter`：card_filter (p) [DecidablePred p] (s : Finset ι) : #
{i in s | p i} = ∑ i in s, ite (p i) 1 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.sum_univ_eq_sum_range`：∀ {α : Type u_1} [inst : AddCommMonoid α] (f 
: ℕ → α) (n : ℕ), ∑ i, f ↑i = ∑ i ∈ Finset.range n, f i
· 使用定理 `Finset.sum_range_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ →
 M) (n m : ℕ),   ∑ x ∈ Finset.range (n + m), f x = ∑ x ∈ Finset.range n, f x + ∑
 x ∈ Finse…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
（共 35 条，此处仅展示前 30 条）
-/
lemma card_edgeFinset_turanGraph_add :
    #(turanGraph (n + r) r).edgeFinset =
    #(turanGraph n r).edgeFinset + n * (r - 1) + r.choose 2 := by
  rw [← mul_right_inj' two_ne_zero]
  simp_rw [mul_add, ← sum_degrees_eq_twice_card_edges,
    degree, neighborFinset_eq_filter, turanGraph, card_filter]
  conv_lhs =>
    enter [2, v]
    rw [Fin.sum_univ_eq_sum_range fun w ↦ if v % r ≠ w % r then 1 else 0, sum_range_add]
  rw [sum_add_distrib,
    Fin.sum_univ_eq_sum_range fun v ↦ ∑ w ∈ range n, if v % r ≠ w % r then 1 else 0,
    Fin.sum_univ_eq_sum_range fun v ↦ ∑ w ∈ range r, if v % r ≠ (n + w) % r then 1 else 0,
    sum_range_add, sum_range_add, add_assoc, add_assoc]
  congr 1; · simp [← Fin.sum_univ_eq_sum_range]
  rw [← add_assoc, sum_comm]; simp_rw [ne_comm, ← two_mul]; congr
  · conv_rhs => rw [← card_range n, ← smul_eq_mul, ← sum_const]
    congr!; exact sum_ne_add_mod_eq_sub_one
  · rw [mul_comm 2, Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self r)]
    conv_rhs => enter [1]; rw [← card_range r]
    rw [← smul_eq_mul, ← sum_const]
    congr!; exact sum_ne_add_mod_eq_sub_one

/-- The exact formula for the number of edges in `turanGraph n r`. -/
/-
**SimpleGraph.card_edgeFinset_turanGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：card_edgeFinset_turanGraph {n r : Nat} : #(turanGraph n r).edgeFinset = (n
 ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.card_edgeFinset_turanGraph._unary`：∀ {r : ℕ} (n : ℕ),   (Sim
pleGraph.turanGraph n r).edgeFinset.card = (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 
* r) + (n % r).choose 2

--- 原说明 ---
The exact formula for the number of edges in `turanGraph n r`.
-/
theorem card_edgeFinset_turanGraph {n r : ℕ} :
    #(turanGraph n r).edgeFinset =
    (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [Nat.mod_zero, tsub_self, zero_mul, Nat.zero_div, zero_add]
    have := card_edgeFinset_top_eq_card_choose_two (V := Fin n)
    rw [Fintype.card_fin] at this; convert! this; exact turanGraph_zero
  · have ring₁ (n) : (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) =
        n % r * (n / r) * (r - 1) + r * (r - 1) * (n / r) ^ 2 / 2 := by
      nth_rw 1 [← Nat.mod_add_div n r, Nat.sq_sub_sq, add_tsub_cancel_left,
        show (n % r + r * (n / r) + n % r) * (r * (n / r)) * (r - 1) =
          (2 * ((n % r) * (n / r) * (r - 1)) + r * (r - 1) * (n / r) ^ 2) * r by grind]
      rw [Nat.mul_div_mul_right _ _ hr, Nat.mul_add_div zero_lt_two]
    rcases lt_or_ge n r with h | h
    · rw [Nat.mod_eq_of_lt h, tsub_self, zero_mul, Nat.zero_div, zero_add]
      have := card_edgeFinset_top_eq_card_choose_two (V := Fin n)
      rw [Fintype.card_fin] at this; convert! this
      rw [turanGraph_eq_top]; exact .inr h.le
    · let n' := n - r
      have n'r : n = n' + r := by lia
      rw [n'r, card_edgeFinset_turanGraph_add, card_edgeFinset_turanGraph, ring₁, ring₁,
        add_rotate, ← add_assoc, Nat.add_mod_right, Nat.add_div_right _ hr]
      congr 1
      have rd : 2 ∣ r * (r - 1) := (Nat.even_mul_pred_self _).two_dvd
      rw [← Nat.div_mul_right_comm rd, ← Nat.div_mul_right_comm rd, ← Nat.choose_two_right]
      have ring₂ : n' % r * (n' / r + 1) * (r - 1) + r.choose 2 * (n' / r + 1) ^ 2 =
          n' % r * (n' / r + 1) * (r - 1) + r.choose 2 +
          r.choose 2 * 2 * (n' / r) + r.choose 2 * (n' / r) ^ 2 := by grind
      rw [ring₂, ← add_assoc]; congr 1
      rw [← add_rotate, ← add_rotate _ _ (r.choose 2)]; congr 1
      rw [Nat.choose_two_right, Nat.div_mul_cancel rd, mul_add_one, add_mul, ← add_assoc,
        ← add_rotate, add_comm _ (_ * _)]; congr 1
      rw [← mul_rotate, ← add_mul, add_comm, mul_comm _ r, Nat.div_add_mod n' r]

/-- A looser (but simpler than `card_edgeFinset_turanGraph`) bound on the number of edges in
`turanGraph n r`. -/
/-
**SimpleGraph.mul_card_edgeFinset_turanGraph_le** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：mul_card_edgeFinset_turanGraph_le : 2 * r * #(turanGraph n r).edgeFinset <
= (r - 1) * n ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.card_edgeFinset_turanGraph`：card_edgeFinset_turanGraph {n r 
: Nat} : #(turanGraph n r).edgeFinset = (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r
) + (n % r).choose 2
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.mul_div_le`：∀ (m n : ℕ), n * (m / n) ≤ m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `tsub_mul`：tsub_mul [MulRightMono R] (a b c : R) : (a - b) * c = a * c - 
b * c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_comm`：∀ {n m k : ℕ}, k ≤ n → n + m - k = n - k + m
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.mod_le`：∀ (x y : ℕ), x % y ≤ x
· 使用定理 `Nat.sub_le_iff_le_add`：∀ {a b c : ℕ}, a - b ≤ c ↔ a ≤ c + b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.add_le_add_iff_left`：∀ {m k n : ℕ}, n + m ≤ n + k ↔ m ≤ k
· 使用定理 `Nat.choose_two_right`：choose_two_right (n : Nat) : choose n 2 = n * (n -
 1) / 2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mul_div_assoc`：∀ {k n : ℕ} (m : ℕ), k ∣ n → m * n / k = m * (n / k)
· 使用定理 `Even.two_dvd`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → 2 ∣
 a
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
A looser (but simpler than `card_edgeFinset_turanGraph`) bound on the number of 
edges in
`turanGraph n r`.
-/
theorem mul_card_edgeFinset_turanGraph_le :
    2 * r * #(turanGraph n r).edgeFinset ≤ (r - 1) * n ^ 2 := by
  grw [card_edgeFinset_turanGraph, mul_add, Nat.mul_div_le]
  rw [tsub_mul, ← Nat.sub_add_comm]; swap
  · grw [Nat.mod_le]
    exact Nat.zero_le _
  rw [Nat.sub_le_iff_le_add, mul_comm, Nat.add_le_add_iff_left, Nat.choose_two_right,
    ← Nat.mul_div_assoc _ (Nat.even_mul_pred_self _).two_dvd, mul_assoc,
    mul_div_cancel_left₀ _ two_ne_zero, ← mul_assoc, ← mul_rotate, sq, ← mul_rotate (r - 1)]
  gcongr ?_ * _
  rcases r.eq_zero_or_pos with rfl | hr; · lia
  rw [Nat.sub_one_mul, Nat.sub_one_mul, mul_comm]
  exact Nat.sub_le_sub_left (Nat.mod_lt _ hr).le _
/-
**SimpleGraph.CliqueFree.card_edgeFinset_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.CliqueFree`。
形式化陈述：∀ {V : Type u_1} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : Decidabl
eRel G.Adj] {r : ℕ},   G.CliqueFree (r + 1) →     have n := Fintype.card V;     
G.edgeFinset.card ≤ (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2
参数：r + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.mod_zero`：∀ (a : ℕ), a % 0 = a
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `SimpleGraph.card_edgeFinset_le_card_choose_two`：card_edgeFinset_le_card_
choose_two : #G.edgeFinset <= (Fintype.card V).choose 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.exists_isTuranMaximal`：exists_isTuranMaximal (hr : 0 < r) : 
exists H : SimpleGraph V, exists _ : DecidableRel H.Adj, H.IsTuranMaximal r
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SimpleGraph.Iso.card_edgeFinset_eq`：card_edgeFinset_eq (f : G ≃g G') [Fi
ntype G.edgeSet] [Fintype G'.edgeSet] : #G.edgeFinset = #G'.edgeFinset
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`：isTuranMaximal_i
ff_nonempty_iso_turanGraph (hr : 0 < r) : G.IsTuranMaximal r ↔ Nonempty (G ≃g tu
ranGraph (card V) r)
· 使用定理 `SimpleGraph.card_edgeFinset_turanGraph`：card_edgeFinset_turanGraph {n r 
: Nat} : #(turanGraph n r).edgeFinset = (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r
) + (n % r).choose 2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem CliqueFree.card_edgeFinset_le (cf : G.CliqueFree (r + 1)) :
    let n := Fintype.card V;
    #G.edgeFinset ≤ (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [cliqueFree_one, ← Fintype.card_eq_zero_iff] at cf
    simp_rw [zero_tsub, mul_zero, Nat.mod_zero, Nat.div_zero, zero_add]
    exact card_edgeFinset_le_card_choose_two
  · obtain ⟨H, _, maxH⟩ := exists_isTuranMaximal (V := V) hr
    convert! maxH.2 cf
    rw [((isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp maxH).some.card_edgeFinset_eq,
      card_edgeFinset_turanGraph]

end SimpleGraph

