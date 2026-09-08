/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Graph cliques

This file defines cliques in simple graphs.
A clique is a set of vertices that are pairwise adjacent.

## Main declarations

* `SimpleGraph.IsClique`: Predicate for a set of vertices to be a clique.
* `SimpleGraph.IsNClique`: Predicate for a set of vertices to be an `n`-clique.
* `SimpleGraph.cliqueFinset`: Finset of `n`-cliques of a graph.
* `SimpleGraph.CliqueFree`: Predicate for a graph to have no `n`-cliques.
-/

@[expose] public section

open Finset Fintype Function SimpleGraph.Walk

namespace SimpleGraph

variable {α β : Type*} (G H : SimpleGraph α)

/-! ### Cliques -/


section Clique

variable {s t : Set α}

/-- A clique in a graph is a set of vertices that are pairwise adjacent. -/
/-
**SimpleGraph.IsClique** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsClique (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A clique in a graph is a set of vertices that are pairwise adjacent.
-/
abbrev IsClique (s : Set α) : Prop :=
  s.Pairwise G.Adj
/-
**SimpleGraph.isClique_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_iff : G.IsClique s ↔ s.Pairwise G.Adj
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClique_iff : G.IsClique s ↔ s.Pairwise G.Adj :=
  Iff.rfl
/-
**SimpleGraph.not_isClique_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：not_isClique_iff : ¬ G.IsClique s ↔ exists (v w : s), v != w ∧ ¬ G.Adj v w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Pairwise.eq_1`：∀ {α : Type u_1} (s : Set α) (r : α → α → Prop), s.Pa
irwise r = ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → x ≠ y → r x y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma not_isClique_iff : ¬ G.IsClique s ↔ ∃ (v w : s), v ≠ w ∧ ¬ G.Adj v w := by
  aesop (add simp [isClique_iff, Set.Pairwise])

variable {G} in
@[simp]
/-
**SimpleGraph.induce_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：induce_eq_top : G.induce s = ⊤ ↔ G.IsClique s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isClique_iff`：isClique_iff : G.IsClique s ↔ s.Pairwise G.Adj
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.induce_adj`：induce_adj {s : Set V} {u v : s} : (G.induce s).
Adj u v ↔ G.Adj u v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
-/
theorem induce_eq_top : G.induce s = ⊤ ↔ G.IsClique s := by
  rw [isClique_iff]
  refine ⟨fun h u hu v hv hne ↦ ?_, fun h ↦ ?_⟩
  · simpa [← induce_adj (u := ⟨u, hu⟩) (v := ⟨v, hv⟩), h]
  · ext ⟨v, hv⟩ ⟨w, hw⟩
    simpa using ⟨Adj.ne, h hv hw⟩

/-- A clique is a set of vertices whose induced graph is complete. -/
@[deprecated induce_eq_top (since := "2026-04-23")]
/-
**SimpleGraph.isClique_iff_induce_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_iff_induce_eq : G.IsClique s ↔ G.induce s = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SimpleGraph.induce_eq_top`：induce_eq_top : G.induce s = ⊤ ↔ G.IsClique s

--- 原说明 ---
A clique is a set of vertices whose induced graph is complete.
-/
theorem isClique_iff_induce_eq : G.IsClique s ↔ G.induce s = ⊤ :=
  induce_eq_top.symm
/-
**SimpleGraph.isClique_iff_isChain_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_iff_isChain_adj : G.IsClique s ↔ IsChain G.Adj s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Std.Symm.iff`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Symm r] (x y : α)
, r x y ↔ r y x
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClique_iff_isChain_adj : G.IsClique s ↔ IsChain G.Adj s := by
  simp [IsChain, G.symm.iff]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsClique s) :=
  decidable_of_iff' _ G.isClique_iff

variable {G H} {a b : α}
/-
**SimpleGraph.isClique_empty** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_empty : G.IsClique ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma isClique_empty : G.IsClique ∅ := by simp
/-
**SimpleGraph.isClique_singleton** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_singleton (a : α) : G.IsClique {a}
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma isClique_singleton (a : α) : G.IsClique {a} := by simp
/-
**SimpleGraph.IsClique.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Is
Clique`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {G : SimpleGraph α}, s.Subsingleton → G.IsCli
que s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
-/
theorem IsClique.of_subsingleton {G : SimpleGraph α} (hs : s.Subsingleton) : G.IsClique s :=
  hs.pairwise G.Adj
/-
**SimpleGraph.isClique_pair** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_pair : G.IsClique {a, b} ↔ a != b -> G.Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
· 使用定理 `Set.pairwise_pair_of_symm`：pairwise_pair_of_symm [Std.Symm r] : Set.Pair
wise {a, b} r ↔ a != b -> r a b
-/
lemma isClique_pair : G.IsClique {a, b} ↔ a ≠ b → G.Adj a b :=
  have := G.symm
  Set.pairwise_pair_of_symm

@[simp]
/-
**SimpleGraph.isClique_insert** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_insert : G.IsClique (insert a s) ↔ G.IsClique s ∧ forall b in s, 
a != b -> G.Adj a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
· 使用定理 `Set.pairwise_insert_of_symm`：pairwise_insert_of_symm [Std.Symm r] : (ins
ert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, a != b -> r a b
-/
lemma isClique_insert : G.IsClique (insert a s) ↔ G.IsClique s ∧ ∀ b ∈ s, a ≠ b → G.Adj a b :=
  have := G.symm
  Set.pairwise_insert_of_symm
/-
**SimpleGraph.isClique_insert_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_insert_of_notMem (ha : a ∉ s) : G.IsClique (insert a s) ↔ G.IsCli
que s ∧ forall b in s, G.Adj a b
参数：ha : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
· 使用定理 `Set.pairwise_insert_of_symm_of_notMem`：pairwise_insert_of_symm_of_notMem
 [Std.Symm r] (ha : a ∉ s) : (insert a s).Pairwise r ↔ s.Pairwise r ∧ forall b i
n s, r a b
-/
lemma isClique_insert_of_notMem (ha : a ∉ s) :
    G.IsClique (insert a s) ↔ G.IsClique s ∧ ∀ b ∈ s, G.Adj a b :=
  have := G.symm
  Set.pairwise_insert_of_symm_of_notMem ha
/-
**SimpleGraph.IsClique.insert** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsClique`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {s : Set α} {a : α},   G.IsClique s →
 (∀ b ∈ s, a ≠ b → G.Adj a b) → G.IsClique (insert a s)
参数：∀ b ∈ s, a ≠ b → G.Adj a b；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
· 使用定理 `Set.Pairwise.insert_of_symm`：∀ {α : Type u_1} {r : α → α → Prop} {s : Se
t α} {a : α} [Std.Symm r],   s.Pairwise r → (∀ b ∈ s, a ≠ b → r a b) → (insert a
 s).Pairwise r
-/
lemma IsClique.insert (hs : G.IsClique s) (h : ∀ b ∈ s, a ≠ b → G.Adj a b) :
    G.IsClique (insert a s) :=
  have := G.symm
  hs.insert_of_symm h

@[gcongr]
/-
**SimpleGraph.IsClique.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsClique`。
形式化陈述：∀ {α : Type u_1} {G H : SimpleGraph α} {s : Set α}, G ≤ H → G.IsClique s →
 H.IsClique s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
-/
theorem IsClique.mono (h : G ≤ H) : G.IsClique s → H.IsClique s := Set.Pairwise.mono' h

@[gcongr]
/-
**SimpleGraph.IsClique.subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsClique`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {s t : Set α}, t ⊆ s → G.IsClique s →
 G.IsClique t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
-/
theorem IsClique.subset (h : t ⊆ s) : G.IsClique s → G.IsClique t := Set.Pairwise.mono h

variable (s) in
@[simp]
/-
**SimpleGraph.IsClique.top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsClique`。
形式化陈述：∀ {α : Type u_1} (s : Set α), ⊤.IsClique s
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem IsClique.top : (⊤ : SimpleGraph α).IsClique s :=
  fun _ _ _ _ ↦ id

@[simp]
/-
**SimpleGraph.isClique_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_bot_iff : (⊥ : SimpleGraph α).IsClique s ↔ (s : Set α).Subsinglet
on
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_bot_iff`：pairwise_bot_iff : s.Pairwise (⊥ : α -> α -> Prop)
 ↔ (s : Set α).Subsingleton
-/
theorem isClique_bot_iff : (⊥ : SimpleGraph α).IsClique s ↔ (s : Set α).Subsingleton :=
  Set.pairwise_bot_iff

alias ⟨IsClique.subsingleton, _⟩ := isClique_bot_iff

@[simp]
/-
**SimpleGraph.isClique_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_univ : G.IsClique .univ ↔ G = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.pairwise_univ`：pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise 
r
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SimpleGraph.eq_top_iff_forall_ne_adj`：eq_top_iff_forall_ne_adj : G = ⊤ ↔
 forall a b : V, a != b -> G.Adj a b
-/
theorem isClique_univ : G.IsClique .univ ↔ G = ⊤ :=
  Set.pairwise_univ.trans G.eq_top_iff_forall_ne_adj.symm
/-
**SimpleGraph.IsClique.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsClique`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {s : Set α},   G.IsCli
que s → ∀ {f : α ↪ β}, (SimpleGraph.map (⇑f) G).IsClique (⇑f '' s)
参数：SimpleGraph.map (⇑f) G；⇑f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
protected theorem IsClique.map (h : G.IsClique s) {f : α ↪ β} : (G.map f).IsClique (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  exact ⟨hab, a, b, h ha hb <| ne_of_apply_ne _ hab, rfl, rfl⟩
/-
**SimpleGraph.IsClique.inter_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsCliqu
e`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {s : Set α}, G.IsClique s → ∀ (t : Se
t α), G.IsClique (s ∩ t)
参数：t : Set α；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.inter_left`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, s.Pairwise r → ∀ (t : Set α), (s ∩ t).Pairwise r
-/
theorem IsClique.inter_left {s : Set α} (hs : G.IsClique s) (t : Set α) : G.IsClique <| s ∩ t :=
  Set.Pairwise.inter_left hs t
/-
**SimpleGraph.IsClique.inter_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsCliq
ue`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {s : Set α}, G.IsClique s → ∀ (t : Se
t α), G.IsClique (t ∩ s)
参数：t : Set α；t ∩ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.inter_right`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α
}, s.Pairwise r → ∀ (t : Set α), (t ∩ s).Pairwise r
-/
theorem IsClique.inter_right {s : Set α} (hs : G.IsClique s) (t : Set α) : G.IsClique <| t ∩ s :=
  Set.Pairwise.inter_right hs t
/-
**SimpleGraph.isClique_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_sUnion {S : Set (Set α)} (hd : DirectedOn (· subseteq ·) S) : G.I
sClique (⋃₀ S) ↔ forall s in S, G.IsClique s
参数：Set α；hd : DirectedOn (· subseteq ·) S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_sUnion`：pairwise_sUnion {r : α -> α -> Prop} {s : Set (Set 
α)} (hd : DirectedOn (· subseteq ·) s) : (⋃₀ s).Pairwise r ↔ forall a in s, Set.
Pairwise …
-/
theorem isClique_sUnion {S : Set (Set α)} (hd : DirectedOn (· ⊆ ·) S) :
    G.IsClique (⋃₀ S) ↔ ∀ s ∈ S, G.IsClique s :=
  Set.pairwise_sUnion hd
/-
**SimpleGraph.isClique_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_iUnion {ι : Type*} {s : ι -> Set α} (hd : Directed (· subseteq ·)
 s) : G.IsClique (⋃ i, s i) ↔ forall i, G.IsClique (s i)
参数：hd : Directed (· subseteq ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_iUnion`：pairwise_iUnion {f : κ -> Set α} (hd : Directed (· 
subseteq ·) f) : (⋃ n, f n).Pairwise r ↔ forall n, (f n).Pairwise r
-/
theorem isClique_iUnion {ι : Type*} {s : ι → Set α} (hd : Directed (· ⊆ ·) s) :
    G.IsClique (⋃ i, s i) ↔ ∀ i, G.IsClique (s i) :=
  Set.pairwise_iUnion hd
/-
**SimpleGraph.isClique_map_iff_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：isClique_map_iff_of_nontrivial {f : α ↪ β} {t : Set β} (ht : t.Nontrivial)
 : (G.map f).IsClique t ↔ exists (s : Set α), G.IsClique s ∧ f '' s = t
参数：ht : t.Nontrivial。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
· 使用定理 `Set.Nontrivial.exists_ne`：∀ {α : Type u} {s : Set α}, s.Nontrivial → ∀ (
z : α), ∃ x ∈ s, x ≠ z
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `SimpleGraph.IsClique.map`：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGra
ph α} {s : Set α},   G.IsClique s → ∀ {f : α ↪ β}, (SimpleGraph.map (⇑f) G).IsCl
ique (⇑f '' s)
-/
theorem isClique_map_iff_of_nontrivial {f : α ↪ β} {t : Set β} (ht : t.Nontrivial) :
    (G.map f).IsClique t ↔ ∃ (s : Set α), G.IsClique s ∧ f '' s = t := by
  refine ⟨fun h ↦ ⟨f ⁻¹' t, ?_, ?_⟩, by rintro ⟨x, hs, rfl⟩; exact hs.map⟩
  · rintro x (hx : f x ∈ t) y (hy : f y ∈ t) hne
    obtain ⟨-, u, v, huv, hux, hvy⟩ := h hx hy (by simpa)
    rw [EmbeddingLike.apply_eq_iff_eq] at hux hvy
    rwa [← hux, ← hvy]
  rw [Set.image_preimage_eq_iff]
  intro x hxt
  obtain ⟨y, hyt, hyne⟩ := ht.exists_ne x
  obtain ⟨-, u, v, -, rfl, rfl⟩ := h hyt hxt hyne
  exact Set.mem_range_self _
/-
**SimpleGraph.isClique_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_map_iff {f : α ↪ β} {t : Set β} : (G.map f).IsClique t ↔ t.Subsin
gleton ∨ exists (s : Set α), G.IsClique s ∧ f '' s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_or_nontrivial`：∀ {α : Type u} (s : Set α), s.Subsinglet
on ∨ s.Nontrivial
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `SimpleGraph.isClique_map_iff_of_nontrivial`：isClique_map_iff_of_nontrivi
al {f : α ↪ β} {t : Set β} (ht : t.Nontrivial) : (G.map f).IsClique t ↔ exists (
s : Set α), G.IsClique s ∧ f '' …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nontrivial.not_subsingleton`：∀ {α : Type u} {s : Set α}, s.Nontrivia
l → ¬s.Subsingleton
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem isClique_map_iff {f : α ↪ β} {t : Set β} :
    (G.map f).IsClique t ↔ t.Subsingleton ∨ ∃ (s : Set α), G.IsClique s ∧ f '' s = t := by
  obtain (ht | ht) := t.subsingleton_or_nontrivial
  · simp [IsClique.of_subsingleton, ht]
  simp [isClique_map_iff_of_nontrivial ht, ht.not_subsingleton]
/-
**SimpleGraph.isClique_map_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {s : Set α} {f : α ↪ β
},   (SimpleGraph.map (⇑f) G).IsClique (⇑f '' s) ↔ G.IsClique s
参数：SimpleGraph.map (⇑f) G；⇑f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isClique_map_iff`：isClique_map_iff {f : α ↪ β} {t : Set β} :
 (G.map f).IsClique t ↔ t.Subsingleton ∨ exists (s : Set α), G.IsClique s ∧ f ''
 s = t
· 使用定理 `Function.Injective.subsingleton_image_iff`：∀ {α : Type u_1} {β : Type u_
2} {f : α → β},   Function.Injective f → ∀ {s : Set α}, (f '' s).Subsingleton ↔ 
s.Subsingleton
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Set.subsingleton_or_nontrivial`：∀ {α : Type u} (s : Set α), s.Subsinglet
on ∨ s.Nontrivial
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_eq_image`：image_eq_image {f : α -> β} (hf : Injective f) : f '
' s = f '' t ↔ s = t
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Set.Nontrivial.not_subsingleton`：∀ {α : Type u} {s : Set α}, s.Nontrivia
l → ¬s.Subsingleton
-/
@[simp] theorem isClique_map_image_iff {f : α ↪ β} :
    (G.map f).IsClique (f '' s) ↔ G.IsClique s := by
  rw [isClique_map_iff, f.injective.subsingleton_image_iff]
  obtain (hs | hs) := s.subsingleton_or_nontrivial
  · simp [hs, IsClique.of_subsingleton]
  simp [or_iff_right hs.not_subsingleton, Set.image_eq_image f.injective]
/-
**SimpleGraph.isClique_induce_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_induce_iff {s : Set α} {t : Set s} : (G.induce s).IsClique t ↔ G.
IsClique (Subtype.val '' t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Pairwise.eq_1`：∀ {α : Type u_1} (s : Set α) (r : α → α → Prop), s.Pa
irwise r = ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → x ≠ y → r x y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClique_induce_iff {s : Set α} {t : Set s} :
    (G.induce s).IsClique t ↔ G.IsClique (Subtype.val '' t) := by
  simp [Set.Pairwise]

variable {f : α ↪ β} {t : Finset β}
/-
**SimpleGraph.isClique_map_finset_iff_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph`。
形式化陈述：isClique_map_finset_iff_of_nontrivial (ht : t.Nontrivial) : (G.map f).IsCl
ique t ↔ exists (s : Finset α), G.IsClique s ∧ s.map f = t
参数：ht : t.Nontrivial。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isClique_map_iff_of_nontrivial`：isClique_map_iff_of_nontrivi
al {f : α ↪ β} {t : Set β} (ht : t.Nontrivial) : (G.map f).IsClique t ↔ exists (
s : Set α), G.IsClique s ∧ f '' …
· 使用定理 `Set.Finite.exists_finset_coe`：∀ {α : Type u} {s : Set α}, s.Finite → ∃ s
', ↑s' = s
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `SimpleGraph.IsClique.map`：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGra
ph α} {s : Set α},   G.IsClique s → ∀ {f : α ↪ β}, (SimpleGraph.map (⇑f) G).IsCl
ique (⇑f '' s)
-/
theorem isClique_map_finset_iff_of_nontrivial (ht : t.Nontrivial) :
    (G.map f).IsClique t ↔ ∃ (s : Finset α), G.IsClique s ∧ s.map f = t := by
  constructor
  · rw [isClique_map_iff_of_nontrivial (by simpa)]
    rintro ⟨s, hs, hst⟩
    obtain ⟨s, rfl⟩ := Set.Finite.exists_finset_coe <|
      (show s.Finite from Set.Finite.of_finite_image (by simp [hst]) f.injective.injOn)
    exact ⟨s,hs, Finset.coe_inj.1 (by simpa)⟩
  rintro ⟨s, hs, rfl⟩
  simpa using hs.map (f := f)
/-
**SimpleGraph.isClique_map_finset_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_map_finset_iff : (G.map f).IsClique t ↔ #t <= 1 ∨ exists (s : Fin
set α), G.IsClique s ∧ s.map f = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `SimpleGraph.IsClique.of_subsingleton`：∀ {α : Type u_1} {s : Set α} {G : 
SimpleGraph α}, s.Subsingleton → G.IsClique s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_le_one`：card_le_one : #s <= 1 ↔ forall a in s, forall b in s
, a = b
· 使用定理 `SimpleGraph.isClique_map_finset_iff_of_nontrivial`：isClique_map_finset_i
ff_of_nontrivial (ht : t.Nontrivial) : (G.map f).IsClique t ↔ exists (s : Finset
 α), G.IsClique s ∧ s.map f = t
· 使用定理 `Finset.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < #s ↔
 s.Nontrivial
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClique_map_finset_iff :
    (G.map f).IsClique t ↔ #t ≤ 1 ∨ ∃ (s : Finset α), G.IsClique s ∧ s.map f = t := by
  obtain (ht | ht) := le_or_gt #t 1
  · simp only [ht, true_or, iff_true]
    exact IsClique.of_subsingleton <| card_le_one.1 ht
  rw [isClique_map_finset_iff_of_nontrivial, ← not_lt]
  · simp [ht]
  exact Finset.one_lt_card_iff_nontrivial.mp ht
/-
**SimpleGraph.IsClique.finsetMap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsClique
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {f : α ↪ β} {s : Finse
t α},   G.IsClique ↑s → (SimpleGraph.map (⇑f) G).IsClique ↑(Finset.map f s)
参数：SimpleGraph.map (⇑f) G；Finset.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
-/
protected theorem IsClique.finsetMap {f : α ↪ β} {s : Finset α} (h : G.IsClique s) :
    (G.map f).IsClique (s.map f) := by
  simpa

/-- If a set of vertices `A` is a clique in subgraph of `G` induced by a superset of `A`,
its embedding is a clique in `G`. -/
/-
**SimpleGraph.IsClique.of_induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsClique
`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {S : G.Subgraph} {F : Set α} {A : Set
 ↑F},   (S.induce F).coe.IsClique A → G.IsClique (Subtype.val '' A)
参数：S.induce F；Subtype.val '' A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Pairwise.eq_1`：∀ {α : Type u_1} (s : Set α) (r : α → α → Prop), s.Pa
irwise r = ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → x ≠ y → r x y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b

--- 原说明 ---
If a set of vertices `A` is a clique in subgraph of `G` induced by a superset of
 `A`,
its embedding is a clique in `G`.
-/
theorem IsClique.of_induce {S : Subgraph G} {F : Set α} {A : Set F}
    (c : (S.induce F).coe.IsClique A) : G.IsClique (Subtype.val '' A) := by
  simp only [Set.Pairwise, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  intro _ ⟨_, ainA⟩ _ ⟨_, binA⟩ anb
  exact S.adj_sub (c ainA binA (Subtype.coe_ne_coe.mp anb)).2.2
/-
**SimpleGraph.IsClique.sdiff_of_sup_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsClique`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {v w : α} {s : Set α}, (G ⊔ SimpleGra
ph.edge v w).IsClique s → G.IsClique (s \ {v})
参数：G ⊔ SimpleGraph.edge v w；s \ {v}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma IsClique.sdiff_of_sup_edge {v w : α} {s : Set α} (hc : (G ⊔ edge v w).IsClique s) :
    G.IsClique (s \ {v}) := by
  intro _ hx _ hy hxy
  have := hc hx.1 hy.1 hxy
  simp_all [sup_adj, edge_adj]
/-
**SimpleGraph.isClique_sup_edge_of_ne_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
形式化陈述：isClique_sup_edge_of_ne_sdiff {v w : α} {s : Set α} (h : v != w) (hv : G.I
sClique (s \ {v})) (hw : G.IsClique (s \ {w})) : (G ⊔ edge v w).IsClique s
参数：h : v != w；hv : G.IsClique (s \ {v})；hw : G.IsClique (s \ {w})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsClique.mono`：∀ {α : Type u_1} {G H : SimpleGraph α} {s : S
et α}, G ≤ H → G.IsClique s → H.IsClique s
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma isClique_sup_edge_of_ne_sdiff {v w : α} {s : Set α} (h : v ≠ w) (hv : G.IsClique (s \ {v}))
    (hw : G.IsClique (s \ {w})) : (G ⊔ edge v w).IsClique s := by
  intro x hx y hy hxy
  by_cases h' : x ∈ s \ {v} ∧ y ∈ s \ {v} ∨ x ∈ s \ {w} ∧ y ∈ s \ {w}
  · obtain (⟨hx, hy⟩ | ⟨hx, hy⟩) := h'
    · exact hv.mono le_sup_left hx hy hxy
    · exact hw.mono le_sup_left hx hy hxy
  · exact Or.inr ⟨by by_cases x = v <;> aesop, hxy⟩
/-
**SimpleGraph.isClique_sup_edge_of_ne_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：isClique_sup_edge_of_ne_iff {v w : α} {s : Set α} (h : v != w) : (G ⊔ edge
 v w).IsClique s ↔ G.IsClique (s \ {v}) ∧ G.IsClique (s \ {w})
参数：h : v != w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsClique.sdiff_of_sup_edge`：∀ {α : Type u_1} {G : SimpleGrap
h α} {v w : α} {s : Set α}, (G ⊔ SimpleGraph.edge v w).IsClique s → G.IsClique (
s \ {v})
· 使用引理 `SimpleGraph.edge_comm`：edge_comm : edge s t = edge t s
· 使用引理 `SimpleGraph.isClique_sup_edge_of_ne_sdiff`：isClique_sup_edge_of_ne_sdiff
 {v w : α} {s : Set α} (h : v != w) (hv : G.IsClique (s \ {v})) (hw : G.IsClique
 (s \ {w})) : (G ⊔ edge v w).Is…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isClique_sup_edge_of_ne_iff {v w : α} {s : Set α} (h : v ≠ w) :
    (G ⊔ edge v w).IsClique s ↔ G.IsClique (s \ {v}) ∧ G.IsClique (s \ {w}) :=
  ⟨fun h' ↦ ⟨h'.sdiff_of_sup_edge, (edge_comm .. ▸ h').sdiff_of_sup_edge⟩,
    fun h' ↦ isClique_sup_edge_of_ne_sdiff h h'.1 h'.2⟩

/-- The vertices in a copy of `⊤` are a clique. -/
/-
**SimpleGraph.isClique_range_copy_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_range_copy_top (f : Copy (⊤ : SimpleGraph β) G) : G.IsClique (Set
.range f)
参数：f : Copy (⊤ : SimpleGraph β) G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Copy.topEmbedding_apply`：∀ {V : Type u_1} {α : Type u_4} {G 
: SimpleGraph V} (f : ⊤.Copy G) (a : α), f.topEmbedding a = f a
· 使用定理 `SimpleGraph.Embedding.map_adj_iff`：∀ {V : Type u_1} {W : Type u_2} {G : 
SimpleGraph V} {G' : SimpleGraph W} (f : G ↪g G') {v w : V},   G'.Adj (f v) (f w
) ↔ G.Adj v w
· 使用定理 `SimpleGraph.top_adj`：top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v
 != w
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Function.Embedding.apply_eq_iff_eq`：apply_eq_iff_eq {α β} (f : α ↪ β) (x
 y : α) : f x = f y ↔ x = y
· 使用定理 `RelEmbedding.coe_toEmbedding`：coe_toEmbedding {f : r ↪r s} : ((f : r ↪r 
s).toEmbedding : α -> β) = f

--- 原说明 ---
The vertices in a copy of `⊤` are a clique.
-/
theorem isClique_range_copy_top (f : Copy (⊤ : SimpleGraph β) G) :
    G.IsClique (Set.range f) := by
  intro _ ⟨_, h⟩ _ ⟨_, h'⟩ nh
  rw [← h, ← Copy.topEmbedding_apply, ← h', ← Copy.topEmbedding_apply] at nh ⊢
  rwa [← f.topEmbedding.coe_toEmbedding, (f.topEmbedding.apply_eq_iff_eq _ _).ne,
    ← top_adj, ← f.topEmbedding.map_adj_iff] at nh

end Clique

/-! ### `n`-cliques -/


section NClique

variable {n : ℕ} {s : Finset α}

/-- An `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
/-
**SimpleGraph.IsNClique** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{α : Type u_1} → SimpleGraph α → ℕ → Finset α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `n`-clique in a graph is a set of `n` vertices which are pairwise connected.
-/
structure IsNClique (n : ℕ) (s : Finset α) : Prop where
  isClique : G.IsClique s
  card_eq : #s = n
/-
**SimpleGraph.isNClique_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isNClique_iff : G.IsNClique n s ↔ G.IsClique s ∧ #s = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isNClique_iff : G.IsNClique n s ↔ G.IsClique s ∧ #s = n :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} :
    Decidable (G.IsNClique n s) :=
  decidable_of_iff' _ G.isNClique_iff

variable {G H} {a b c : α}
/-
**SimpleGraph.isNClique_empty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {n : ℕ}, G.IsNClique n ∅ ↔ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isNClique_empty : G.IsNClique n ∅ ↔ n = 0 := by simp [isNClique_iff, eq_comm]

@[simp]
/-
**SimpleGraph.isNClique_singleton** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isNClique_singleton : G.IsNClique n {a} ↔ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isNClique_singleton : G.IsNClique n {a} ↔ n = 1 := by simp [isNClique_iff, eq_comm]
/-
**SimpleGraph.IsNClique.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsNClique`。
形式化陈述：∀ {α : Type u_1} {G H : SimpleGraph α} {n : ℕ} {s : Finset α}, G ≤ H → G.I
sNClique n s → H.IsNClique n s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `SimpleGraph.IsClique.mono`：∀ {α : Type u_1} {G H : SimpleGraph α} {s : S
et α}, G ≤ H → G.IsClique s → H.IsClique s
-/
theorem IsNClique.mono (h : G ≤ H) : G.IsNClique n s → H.IsNClique n s := by
  simp_rw [isNClique_iff]
  exact And.imp_left (IsClique.mono h)
/-
**SimpleGraph.IsNClique.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsNClique`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {n : ℕ} {s : Finset α}
,   G.IsNClique n s → ∀ {f : α ↪ β}, (SimpleGraph.map (⇑f) G).IsNClique n (Finse
t.map f s)
参数：SimpleGraph.map (⇑f) G；Finset.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `SimpleGraph.IsClique.map`：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGra
ph α} {s : Set α},   G.IsClique s → ∀ {f : α ↪ β}, (SimpleGraph.map (⇑f) G).IsCl
ique (⇑f '' s)
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
-/
protected theorem IsNClique.map (h : G.IsNClique n s) {f : α ↪ β} :
    (G.map f).IsNClique n (s.map f) :=
  ⟨by rw [coe_map]; exact h.1.map, (card_map _).trans h.2⟩
/-
**SimpleGraph.isNClique_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isNClique_map_iff (hn : 1 < n) {t : Finset β} {f : α ↪ β} : (G.map f).IsNC
lique n t ↔ exists s : Finset α, G.IsNClique n s ∧ s.map f = t
参数：hn : 1 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isNClique_iff`：isNClique_iff : G.IsNClique n s ↔ G.IsClique 
s ∧ #s = n
· 使用定理 `SimpleGraph.isClique_map_finset_iff`：isClique_map_finset_iff : (G.map f)
.IsClique t ↔ #t <= 1 ∨ exists (s : Finset α), G.IsClique s ∧ s.map f = t
· 使用定理 `or_and_right`：∀ {a b c : Prop}, (a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
-/
theorem isNClique_map_iff (hn : 1 < n) {t : Finset β} {f : α ↪ β} :
    (G.map f).IsNClique n t ↔ ∃ s : Finset α, G.IsNClique n s ∧ s.map f = t := by
  rw [isNClique_iff, isClique_map_finset_iff, or_and_right,
    or_iff_right (by rintro ⟨h', rfl⟩; exact h'.not_gt hn)]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, rfl⟩
    simp [isNClique_iff, hs]
  rintro ⟨s, hs, rfl⟩
  simp [hs.card_eq, hs.isClique]

@[simp]
/-
**SimpleGraph.isNClique_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isNClique_bot_iff : (⊥ : SimpleGraph α).IsNClique n s ↔ n <= 1 ∧ #s = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isNClique_iff`：isNClique_iff : G.IsNClique n s ↔ G.IsClique 
s ∧ #s = n
· 使用定理 `SimpleGraph.isClique_bot_iff`：isClique_bot_iff : (⊥ : SimpleGraph α).IsC
lique s ↔ (s : Set α).Subsingleton
· 使用定理 `and_congr_left`：∀ {c a b : Prop}, (c → (a ↔ b)) → (a ∧ c ↔ b ∧ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finset.card_le_one`：card_le_one : #s <= 1 ↔ forall a in s, forall b in s
, a = b
-/
theorem isNClique_bot_iff : (⊥ : SimpleGraph α).IsNClique n s ↔ n ≤ 1 ∧ #s = n := by
  rw [isNClique_iff, isClique_bot_iff]
  refine and_congr_left ?_
  rintro rfl
  exact card_le_one.symm

@[simp]
/-
**SimpleGraph.isNClique_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isNClique_zero : G.IsNClique 0 s ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNClique_zero : G.IsNClique 0 s ↔ s = ∅ := by
  simp only [isNClique_iff, Finset.card_eq_zero, and_iff_right_iff_imp]; rintro rfl; simp

@[simp]
/-
**SimpleGraph.isNClique_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isNClique_one : G.IsNClique 1 s ↔ exists a, s = {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNClique_one : G.IsNClique 1 s ↔ ∃ a, s = {a} := by
  simp only [isNClique_iff, card_eq_one, and_iff_right_iff_imp]; rintro ⟨a, rfl⟩; simp

section DecidableEq

variable [DecidableEq α]

/-
**SimpleGraph.IsNClique.insert** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsNClique`
。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {n : ℕ} {s : Finset α} {a : α} [inst 
: DecidableEq α],   G.IsNClique n s → (∀ b ∈ s, G.Adj a b) → G.IsNClique (n + 1)
 (insert a s)
参数：∀ b ∈ s, G.Adj a b；n + 1；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `SimpleGraph.IsClique.insert`：∀ {α : Type u_1} {G : SimpleGraph α} {s : S
et α} {a : α},   G.IsClique s → (∀ b ∈ s, a ≠ b → G.Adj a b) → G.IsClique (inser
t a s)
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
-/
protected theorem IsNClique.insert (hs : G.IsNClique n s) (h : ∀ b ∈ s, G.Adj a b) :
    G.IsNClique (n + 1) (insert a s) := by
  constructor
  · push_cast
    exact hs.1.insert fun b hb _ => h _ hb
  · rw [card_insert_of_notMem fun ha => (h _ ha).ne rfl, hs.2]
/-
**SimpleGraph.IsNClique.erase_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsNC
lique`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {n : ℕ} {s : Finset α} {a : α} [inst 
: DecidableEq α],   G.IsNClique n s → a ∈ s → G.IsNClique (n - 1) (s.erase a)
参数：n - 1；s.erase a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsClique.subset`：∀ {α : Type u_1} {G : SimpleGraph α} {s t :
 Set α}, t ⊆ s → G.IsClique s → G.IsClique t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
-/
lemma IsNClique.erase_of_mem (hs : G.IsNClique n s) (ha : a ∈ s) :
    G.IsNClique (n - 1) (s.erase a) where
  isClique := hs.isClique.subset <| by simp
  card_eq := by rw [card_erase_of_mem ha, hs.2]
/-
**SimpleGraph.IsNClique.insert_erase** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsNC
lique`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {n : ℕ} {s : Finset α} {a b : α} [ins
t : DecidableEq α],   G.IsNClique n s → (∀ w ∈ s \ {b}, G.Adj a w) → b ∈ s → G.I
sNClique n (insert a (s.erase b))
参数：∀ w ∈ s \ {b}, G.Adj a w；insert a (s.erase b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.isNClique_zero`：isNClique_zero : G.IsNClique 0 s ↔ s = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.IsNClique.insert`：∀ {α : Type u_1} {G : SimpleGraph α} {n : 
ℕ} {s : Finset α} {a : α} [inst : DecidableEq α],   G.IsNClique n s → (∀ b ∈ s, 
G.Adj a b) → G.IsN…
· 使用定理 `SimpleGraph.IsNClique.erase_of_mem`：∀ {α : Type u_1} {G : SimpleGraph α}
 {n : ℕ} {s : Finset α} {a : α} [inst : DecidableEq α],   G.IsNClique n s → a ∈ 
s → G.IsNClique (n - 1) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
protected lemma IsNClique.insert_erase
    (hs : G.IsNClique n s) (ha : ∀ w ∈ s \ {b}, G.Adj a w) (hb : b ∈ s) :
    G.IsNClique n (insert a (erase s b)) := by
  cases n with
  | zero => exact False.elim <| notMem_empty _ (isNClique_zero.1 hs ▸ hb)
  | succ _ => exact (hs.erase_of_mem hb).insert fun w h ↦ by aesop
/-
**SimpleGraph.is3Clique_triple_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：is3Clique_triple_iff : G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G
.Adj b c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem is3Clique_triple_iff : G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;>
    simp [isNClique_iff, and_rotate, *]
/-
**SimpleGraph.is3Clique_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：is3Clique_iff : G.IsNClique 3 s ↔ exists a b c, G.Adj a b ∧ G.Adj a c ∧ G.
Adj b c ∧ s = {a, b, c}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_three`：card_eq_three : #s = 3 ↔ exists x y z, x != y ∧ x 
!= z ∧ y != z ∧ s = {x, y, z}
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SimpleGraph.is3Clique_triple_iff`：is3Clique_triple_iff : G.IsNClique 3 {
a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem is3Clique_iff :
    G.IsNClique 3 s ↔ ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨a, b, c, -, -, -, hs⟩ := card_eq_three.1 h.card_eq
    refine ⟨a, b, c, ?_⟩
    rwa [hs, eq_self_iff_true, and_true, is3Clique_triple_iff.symm, ← hs]
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is3Clique_triple_iff.2 ⟨hab, hbc, hca⟩

end DecidableEq

/-
**SimpleGraph.is3Clique_iff_exists_cycle_length_three** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：is3Clique_iff_exists_cycle_length_three : (exists s : Finset α, G.IsNCliqu
e 3 s) ↔ exists (u : α) (w : G.Walk u u), w.IsCycle ∧ w.length = 3
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
-/
theorem is3Clique_iff_exists_cycle_length_three :
    (∃ s : Finset α, G.IsNClique 3 s) ↔ ∃ (u : α) (w : G.Walk u u), w.IsCycle ∧ w.length = 3 := by
  classical
  simp_rw [is3Clique_iff, isCycle_def]
  exact
    ⟨(fun ⟨_, a, _, _, hab, hac, hbc, _⟩ => ⟨a, cons hab (cons hbc (cons hac.symm nil)), by aesop⟩),
    (fun ⟨_, .cons hab (.cons hbc (.cons hca nil)), _, _⟩ => ⟨_, _, _, _, hab, hca.symm, hbc, rfl⟩)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- If a set of vertices `A` is an `n`-clique in subgraph of `G` induced by a superset of `A`,
its embedding is an `n`-clique in `G`. -/
/-
**SimpleGraph.IsNClique.of_induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsNCliq
ue`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {S : G.Subgraph} {F : Set α} {s : Fin
set { x // x ∈ F }} {n : ℕ},   (S.induce F).coe.IsNClique n s → G.IsNClique n (F
inset.map { toFun := Subtype.val, inj' := ⋯ } s)
参数：S.induce F；Finset.map { toFun := Subtype.val, inj' := ⋯ } s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isNClique_iff`：isNClique_iff : G.IsNClique n s ↔ G.IsClique 
s ∧ #s = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `SimpleGraph.IsClique.of_induce`：∀ {α : Type u_1} {G : SimpleGraph α} {S 
: G.Subgraph} {F : Set α} {A : Set ↑F},   (S.induce F).coe.IsClique A → G.IsCliq
ue (Subtype.val '' A…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a set of vertices `A` is an `n`-clique in subgraph of `G` induced by a supers
et of `A`,
its embedding is an `n`-clique in `G`.
-/
theorem IsNClique.of_induce {S : Subgraph G} {F : Set α} {s : Finset { x // x ∈ F }} {n : ℕ}
    (cc : (S.induce F).coe.IsNClique n s) :
    G.IsNClique n (Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s) := by
  rw [isNClique_iff] at cc ⊢
  simp only [coe_map, card_map]
  exact ⟨cc.left.of_induce, cc.right⟩

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**SimpleGraph.IsNClique.erase_of_sup_edge_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.IsNClique`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} [inst : DecidableEq α] {v w : α} {s :
 Finset α} {n : ℕ},   (G ⊔ SimpleGraph.edge v w).IsNClique n s → v ∈ s → G.IsNCl
ique (n - 1) (s.erase v)
参数：G ⊔ SimpleGraph.edge v w；n - 1；s.erase v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsClique.sdiff_of_sup_edge`：∀ {α : Type u_1} {G : SimpleGrap
h α} {v w : α} {s : Set α}, (G ⊔ SimpleGraph.edge v w).IsClique s → G.IsClique (
s \ {v})
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
-/
lemma IsNClique.erase_of_sup_edge_of_mem [DecidableEq α] {v w : α} {s : Finset α} {n : ℕ}
    (hc : (G ⊔ edge v w).IsNClique n s) (hx : v ∈ s) : G.IsNClique (n - 1) (s.erase v) where
  isClique := coe_erase v _ ▸ hc.1.sdiff_of_sup_edge
  card_eq  := by rw [card_erase_of_mem hx, hc.2]

/-- The vertices in a copy of `⊤ : SimpleGraph β` are a `card β`-clique. -/
/-
**SimpleGraph.isNClique_map_copy_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isNClique_map_copy_top [Fintype β] (f : Copy (⊤ : SimpleGraph β) G) : G.Is
NClique (card β) (univ.map f.toEmbedding)
参数：f : Copy (⊤ : SimpleGraph β) G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isNClique_iff`：isNClique_iff : G.IsNClique n s ↔ G.IsClique 
s ∧ #s = n
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `SimpleGraph.isClique_range_copy_top`：isClique_range_copy_top (f : Copy (
⊤ : SimpleGraph β) G) : G.IsClique (Set.range f)

--- 原说明 ---
The vertices in a copy of `⊤ : SimpleGraph β` are a `card β`-clique.
-/
theorem isNClique_map_copy_top [Fintype β] (f : Copy (⊤ : SimpleGraph β) G) :
    G.IsNClique (card β) (univ.map f.toEmbedding) := by
  rw [isNClique_iff, card_map, card_univ, coe_map, coe_univ, Set.image_univ]
  exact ⟨isClique_range_copy_top f, rfl⟩
/-
**SimpleGraph.isNClique_induce_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isNClique_induce_iff (s : Set α) (t : Finset s) (n : Nat) : (G.induce s).I
sNClique n t ↔ G.IsNClique n (t.map (.subtype _))
参数：s : Set α；t : Finset s；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isNClique_induce_iff (s : Set α) (t : Finset s) (n : ℕ) :
    (G.induce s).IsNClique n t ↔ G.IsNClique n (t.map (.subtype _)) := by
  simp [isNClique_iff, isClique_induce_iff]

end NClique

/-! ### Graphs without cliques -/


section CliqueFree

variable {m n : ℕ}

/-- `G.CliqueFree n` means that `G` has no `n`-cliques. -/
/-
**SimpleGraph.CliqueFree** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：CliqueFree (n : Nat) : Prop
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.CliqueFree n` means that `G` has no `n`-cliques.
-/
def CliqueFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNClique n t

variable {G H} {s : Finset α}
/-
**SimpleGraph.IsNClique.not_cliqueFree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Is
NClique`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {n : ℕ} {s : Finset α}, G.IsNClique n
 s → ¬G.CliqueFree n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsNClique.not_cliqueFree (hG : G.IsNClique n s) : ¬G.CliqueFree n :=
  fun h ↦ h _ hG
/-
**SimpleGraph.IsContained.not_cliqueFree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsContained`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {n : ℕ}, (SimpleGraph.completeGraph (
Fin n)).IsContained G → ¬G.CliqueFree n
参数：SimpleGraph.completeGraph (Fin n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.isNClique_map_copy_top`：isNClique_map_copy_top [Fintype β] (
f : Copy (⊤ : SimpleGraph β) G) : G.IsNClique (card β) (univ.map f.toEmbedding)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
theorem IsContained.not_cliqueFree {n : ℕ} (h : completeGraph (Fin n) ⊑ G) : ¬G.CliqueFree n := by
  have := isNClique_map_copy_top h.some
  rw [Fintype.card_fin] at this
  exact (· _ this)

@[deprecated (since := "2026-02-21")]
alias not_cliqueFree_of_top_embedding := IsContained.not_cliqueFree

/-- An embedding of a complete graph that witnesses the fact that the graph is not clique-free. -/
/-
**SimpleGraph.topEmbeddingOfNotCliqueFree** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph
`。
形式化陈述：topEmbeddingOfNotCliqueFree {n : Nat} (h : ¬G.CliqueFree n) : completeGrap
h (Fin n) ↪g G
参数：h : ¬G.CliqueFree n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An embedding of a complete graph that witnesses the fact that the graph is not c
lique-free.
-/
noncomputable def topEmbeddingOfNotCliqueFree {n : ℕ} (h : ¬G.CliqueFree n) :
    completeGraph (Fin n) ↪g G := by
  unfold CliqueFree at h
  push Not at h
  apply Embedding.induce (h.choose : Set α) |>.comp
  rw [G.induce_eq_top.mpr h.choose_spec.isClique]
  exact Embedding.completeGraph <| Finset.equivFinOfCardEq h.choose_spec.card_eq |>.symm.toEmbedding
/-
**SimpleGraph.not_cliqueFree_iff_top_isContained** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：not_cliqueFree_iff_top_isContained (n : Nat) : ¬G.CliqueFree n ↔ completeG
raph (Fin n) ⊑ G
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Embedding.isContained`：∀ {V : Type u_1} {W : Type u_2} {G : 
SimpleGraph V} {H : SimpleGraph W} (f : G ↪g H), G.IsContained H
· 使用定理 `SimpleGraph.IsContained.not_cliqueFree`：∀ {α : Type u_1} {G : SimpleGrap
h α} {n : ℕ}, (SimpleGraph.completeGraph (Fin n)).IsContained G → ¬G.CliqueFree 
n
-/
theorem not_cliqueFree_iff_top_isContained (n : ℕ) : ¬G.CliqueFree n ↔ completeGraph (Fin n) ⊑ G :=
  ⟨(topEmbeddingOfNotCliqueFree · |>.isContained), IsContained.not_cliqueFree⟩

@[deprecated (since := "2026-03-23")] alias not_cliqueFree_iff := not_cliqueFree_iff_top_isContained
/-
**SimpleGraph.cliqueFree_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFree_iff {n : Nat} : G.CliqueFree n ↔ IsEmpty (Copy (completeGraph <
| Fin n) G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.not_cliqueFree_iff_top_isContained`：not_cliqueFree_iff_top_i
sContained (n : Nat) : ¬G.CliqueFree n ↔ completeGraph (Fin n) ⊑ G
-/
theorem cliqueFree_iff {n : ℕ} : G.CliqueFree n ↔ IsEmpty (Copy (completeGraph <| Fin n) G) := by
  contrapose!
  exact not_cliqueFree_iff_top_isContained n

/-- A simple graph has no `card β`-cliques iff it does not contain `⊤ : SimpleGraph β`. -/
/-
**SimpleGraph.cliqueFree_iff_top_free** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFree_iff_top_free {β : Type*} [Fintype β] : G.CliqueFree (card β) ↔ 
(⊤ : SimpleGraph β).Free G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `SimpleGraph.not_free`：not_free : ¬A.Free B ↔ A ⊑ B
· 使用定理 `SimpleGraph.not_cliqueFree_iff_top_isContained`：not_cliqueFree_iff_top_i
sContained (n : Nat) : ¬G.CliqueFree n ↔ completeGraph (Fin n) ⊑ G
· 使用定理 `SimpleGraph.isContained_congr`：isContained_congr (e₁ : A ≃g H) (e₂ : B ≃
g G) : A ⊑ B ↔ H ⊑ G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A simple graph has no `card β`-cliques iff it does not contain `⊤ : SimpleGraph 
β`.
-/
theorem cliqueFree_iff_top_free {β : Type*} [Fintype β] :
    G.CliqueFree (card β) ↔ (⊤ : SimpleGraph β).Free G := by
  rw [← not_iff_not, not_free, not_cliqueFree_iff_top_isContained,
    isContained_congr (Iso.completeGraph (equivFin β)) Iso.refl]
/-
**SimpleGraph.IsContained.not_cliqueFree_card** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.IsContained`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} [inst : Fintype α],   (SimpleGraph.co
mpleteGraph α).IsContained G → ¬G.CliqueFree (Fintype.card α)
参数：SimpleGraph.completeGraph α；Fintype.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.not_cliqueFree_iff_top_isContained`：not_cliqueFree_iff_top_i
sContained (n : Nat) : ¬G.CliqueFree n ↔ completeGraph (Fin n) ⊑ G
· 使用定理 `SimpleGraph.IsContained.trans`：∀ {α : Type u_4} {β : Type u_5} {γ : Type
 u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   A.IsContain
ed B → B.IsContaine…
· 使用定理 `SimpleGraph.Iso.isContained'`：∀ {V : Type u_1} {W : Type u_2} {G : Simpl
eGraph V} {H : SimpleGraph W} (e : G ≃g H), H.IsContained G
-/
theorem IsContained.not_cliqueFree_card [Fintype α] (f : completeGraph α ⊑ G) :
    ¬G.CliqueFree (card α) := by
  rw [not_cliqueFree_iff_top_isContained]
  exact (Iso.completeGraph <| equivFin α).isContained'.trans f

@[deprecated (since := "2026-02-21")]
alias not_cliqueFree_card_of_top_embedding := IsContained.not_cliqueFree_card
/-
**SimpleGraph.not_cliqueFree_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α}, ¬G.CliqueFree 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.isNClique_empty`：∀ {α : Type u_1} {G : SimpleGraph α} {n : ℕ
}, G.IsNClique n ∅ ↔ n = 0
-/
@[simp] lemma not_cliqueFree_zero : ¬ G.CliqueFree 0 :=
  fun h ↦ h ∅ <| isNClique_empty.mpr rfl

@[simp]
/-
**SimpleGraph.cliqueFree_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFree_bot (h : 2 <= n) : (⊥ : SimpleGraph α).CliqueFree n
参数：h : 2 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.isNClique_bot_iff`：isNClique_bot_iff : (⊥ : SimpleGraph α).I
sNClique n s ↔ n <= 1 ∧ #s = n
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
-/
theorem cliqueFree_bot (h : 2 ≤ n) : (⊥ : SimpleGraph α).CliqueFree n := by
  intro t ht
  have := le_trans h (isNClique_bot_iff.1 ht).1
  contradiction

@[gcongr]
/-
**SimpleGraph.CliqueFree.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.CliqueFree`
。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {m n : ℕ}, m ≤ n → G.CliqueFree m → G
.CliqueFree n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.exists_subset_card_eq`：exists_subset_card_eq (hns : n <= #s) : ex
ists t subseteq s, #t = n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
· 使用定理 `SimpleGraph.IsClique.subset`：∀ {α : Type u_1} {G : SimpleGraph α} {s t :
 Set α}, t ⊆ s → G.IsClique s → G.IsClique t
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
-/
theorem CliqueFree.mono (h : m ≤ n) : G.CliqueFree m → G.CliqueFree n := by
  intro hG s hs
  obtain ⟨t, hts, ht⟩ := exists_subset_card_eq (h.trans hs.card_eq.ge)
  exact hG _ ⟨hs.isClique.subset hts, ht⟩

@[gcongr]
/-
**SimpleGraph.CliqueFree.anti** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.CliqueFree`
。
形式化陈述：∀ {α : Type u_1} {G H : SimpleGraph α} {n : ℕ}, G ≤ H → H.CliqueFree n → G
.CliqueFree n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.IsNClique.mono`：∀ {α : Type u_1} {G H : SimpleGraph α} {n : 
ℕ} {s : Finset α}, G ≤ H → G.IsNClique n s → H.IsNClique n s
-/
theorem CliqueFree.anti (h : G ≤ H) : H.CliqueFree n → G.CliqueFree n :=
  forall_imp fun _ ↦ mt <| IsNClique.mono h

/-- If a graph is cliquefree, any graph that is contained in it is also cliquefree. -/
@[gcongr only]
/-
**SimpleGraph.CliqueFree.comap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.CliqueFree
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {n : ℕ} {H : SimpleGra
ph β},   H.IsContained G → G.CliqueFree n → H.CliqueFree n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.not_cliqueFree_iff_top_isContained`：not_cliqueFree_iff_top_i
sContained (n : Nat) : ¬G.CliqueFree n ↔ completeGraph (Fin n) ⊑ G
· 使用定理 `SimpleGraph.IsContained.trans`：∀ {α : Type u_4} {β : Type u_5} {γ : Type
 u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   A.IsContain
ed B → B.IsContaine…

--- 原说明 ---
If a graph is cliquefree, any graph that is contained in it is also cliquefree.
-/
theorem CliqueFree.comap {H : SimpleGraph β} (hle : H ⊑ G) (h : G.CliqueFree n) :
    H.CliqueFree n := by
  contrapose h
  rw [not_cliqueFree_iff_top_isContained] at h ⊢
  exact h.trans hle
/-
**SimpleGraph.cliqueFree_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {n : ℕ} {f : α ↪ β} [N
onempty α],   (SimpleGraph.map (⇑f) G).CliqueFree n ↔ G.CliqueFree n
参数：SimpleGraph.map (⇑f) G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_one_iff_eq_zero_or_eq_one`：∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `trivial`：True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.isNClique_map_iff`：isNClique_map_iff (hn : 1 < n) {t : Finse
t β} {f : α ↪ β} : (G.map f).IsNClique n t ↔ exists s : Finset α, G.IsNClique n 
s ∧ s.map f = t
-/
@[simp] theorem cliqueFree_map_iff {f : α ↪ β} [Nonempty α] :
    (G.map f).CliqueFree n ↔ G.CliqueFree n := by
  obtain (hle | hlt) := le_or_gt n 1
  · obtain (rfl | rfl) := Nat.le_one_iff_eq_zero_or_eq_one.1 hle
    · simp [CliqueFree]
    simp [CliqueFree, show ∃ (_ : β), True from ⟨f (Classical.arbitrary _), trivial⟩]
  simp [CliqueFree, isNClique_map_iff hlt]

/-- See `SimpleGraph.cliqueFree_of_chromaticNumber_lt` for a tighter bound. -/
/-
**SimpleGraph.cliqueFree_of_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFree_of_card_lt [Fintype α] (hc : card α < n) : G.CliqueFree n
参数：hc : card α < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.cliqueFree_iff`：cliqueFree_iff {n : Nat} : G.CliqueFree n ↔ 
IsEmpty (Copy (completeGraph <| Fin n) G)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_le_of_embedding`：card_le_of_embedding (f : α ↪ β) : card α 
<= card β

--- 原说明 ---
See `SimpleGraph.cliqueFree_of_chromaticNumber_lt` for a tighter bound.
-/
theorem cliqueFree_of_card_lt [Fintype α] (hc : card α < n) : G.CliqueFree n := by
  rw [cliqueFree_iff]
  contrapose! hc
  simpa only [Fintype.card_fin] using card_le_of_embedding hc.some.toEmbedding

/-- A complete `r`-partite graph has no `n`-cliques for `r < n`. -/
/-
**SimpleGraph.cliqueFree_completeMultipartiteGraph** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：cliqueFree_completeMultipartiteGraph {ι : Type*} [Fintype ι] (V : ι -> Typ
e*) (hc : card ι < n) : (completeMultipartiteGraph V).CliqueFree n
参数：V : ι -> Type*；hc : card ι < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.cliqueFree_iff`：cliqueFree_iff {n : Nat} : G.CliqueFree n ↔ 
IsEmpty (Copy (completeGraph <| Fin n) G)
· 使用定理 `isEmpty_iff`：isEmpty_iff : IsEmpty α ↔ α -> False
· 使用定理 `Fintype.exists_ne_map_eq_of_card_lt`：exists_ne_map_eq_of_card_lt (f : α 
-> β) (h : Fintype.card β < Fintype.card α) : exists x y, x != y ∧ f x = f y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SimpleGraph.top_adj`：top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v
 != w
· 使用定理 `SimpleGraph.comap_adj`：∀ {V : Type u_1} {W : Type u_2} {u v : V} {G : Si
mpleGraph W} {f : V → W},   (SimpleGraph.comap f G).Adj u v ↔ G.Adj (f u) (f v)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Embedding.map_adj_iff`：∀ {V : Type u_1} {W : Type u_2} {G : 
SimpleGraph V} {G' : SimpleGraph W} (f : G ↪g G') {v w : V},   G'.Adj (f v) (f w
) ↔ G.Adj v w

--- 原说明 ---
A complete `r`-partite graph has no `n`-cliques for `r < n`.
-/
theorem cliqueFree_completeMultipartiteGraph {ι : Type*} [Fintype ι] (V : ι → Type*)
    (hc : card ι < n) : (completeMultipartiteGraph V).CliqueFree n := by
  rw [cliqueFree_iff, isEmpty_iff]
  intro f
  obtain ⟨v, w, hn, he⟩ := exists_ne_map_eq_of_card_lt (Sigma.fst ∘ f) (by simp [hc])
  rw [← top_adj, ← f.topEmbedding.map_adj_iff, comap_adj, top_adj] at hn
  exact absurd he hn

namespace completeMultipartiteGraph

variable {ι : Type*} (V : ι → Type*)

set_option backward.isDefEq.respectTransparency.types false in
/-- Embedding of the complete graph on `ι` into `completeMultipartiteGraph` on `ι` nonempty parts -/
@[simps]
/-
**SimpleGraph.completeMultipartiteGraph.topEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `
SimpleGraph.completeMultipartiteGraph`。
形式化陈述：topEmbedding (f : forall (i : ι), V i) : (⊤ : SimpleGraph ι) ↪g completeMu
ltipartiteGraph V where toFun
参数：f : forall (i : ι), V i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of the complete graph on `ι` into `completeMultipartiteGraph` on `ι` n
onempty parts
-/
def topEmbedding (f : ∀ (i : ι), V i) :
    (⊤ : SimpleGraph ι) ↪g completeMultipartiteGraph V where
  toFun := fun i ↦ ⟨i, f i⟩
  inj' := fun _ _ h ↦ (Sigma.mk.inj_iff.1 h).1
  map_rel_iff' := by simp
/-
**SimpleGraph.completeMultipartiteGraph.not_cliqueFree_of_le_card** 是 Mathlib 中的
一个定理，位于命名空间 `SimpleGraph.completeMultipartiteGraph`。
形式化陈述：not_cliqueFree_of_le_card [Fintype ι] (f : forall (i : ι), V i) (hc : n <=
 card ι) : ¬ (completeMultipartiteGraph V).CliqueFree n
参数：f : forall (i : ι), V i；hc : n <= card ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.cliqueFree_iff`：cliqueFree_iff {n : Nat} : G.CliqueFree n ↔ 
IsEmpty (Copy (completeGraph <| Fin n) G)
· 使用定理 `SimpleGraph.CliqueFree.mono`：∀ {α : Type u_1} {G : SimpleGraph α} {m n :
 ℕ}, m ≤ n → G.CliqueFree m → G.CliqueFree n
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem not_cliqueFree_of_le_card [Fintype ι] (f : ∀ (i : ι), V i) (hc : n ≤ card ι) :
    ¬ (completeMultipartiteGraph V).CliqueFree n :=
  fun hf ↦ (cliqueFree_iff.1 <| hf.mono hc).elim' <|
    topEmbedding V f |>.toCopy.comp (Iso.completeGraph (equivFin ι).symm).toCopy
/-
**SimpleGraph.completeMultipartiteGraph.not_cliqueFree_of_infinite** 是 Mathlib 中
的一个定理，位于命名空间 `SimpleGraph.completeMultipartiteGraph`。
形式化陈述：not_cliqueFree_of_infinite [Infinite ι] (f : forall (i : ι), V i) : ¬ (com
pleteMultipartiteGraph V).CliqueFree n
参数：f : forall (i : ι), V i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsContained.not_cliqueFree`：∀ {α : Type u_1} {G : SimpleGrap
h α} {n : ℕ}, (SimpleGraph.completeGraph (Fin n)).IsContained G → ¬G.CliqueFree 
n
· 使用定理 `SimpleGraph.Embedding.isContained`：∀ {V : Type u_1} {W : Type u_2} {G : 
SimpleGraph V} {H : SimpleGraph W} (f : G ↪g H), G.IsContained H
-/
theorem not_cliqueFree_of_infinite [Infinite ι] (f : ∀ (i : ι), V i) :
    ¬ (completeMultipartiteGraph V).CliqueFree n :=
  (topEmbedding V f |>.comp <| .completeGraph <| Fin.valEmbedding.trans <| Infinite.natEmbedding ι)
    |>.isContained.not_cliqueFree
/-
**SimpleGraph.completeMultipartiteGraph.not_cliqueFree_of_le_enatCard** 是 Mathli
b 中的一个定理，位于命名空间 `SimpleGraph.completeMultipartiteGraph`。
形式化陈述：not_cliqueFree_of_le_enatCard (f : forall (i : ι), V i) (hc : n <= ENat.ca
rd ι) : ¬ (completeMultipartiteGraph V).CliqueFree n
参数：f : forall (i : ι), V i；hc : n <= ENat.card ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.completeMultipartiteGraph.not_cliqueFree_of_infinite`：not_cl
iqueFree_of_infinite [Infinite ι] (f : forall (i : ι), V i) : ¬ (completeMultipa
rtiteGraph V).CliqueFree n
· 使用定理 `SimpleGraph.completeMultipartiteGraph.not_cliqueFree_of_le_card`：not_cli
queFree_of_le_card [Fintype ι] (f : forall (i : ι), V i) (hc : n <= card ι) : ¬ 
(completeMultipartiteGraph V).CliqueFree n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
-/
theorem not_cliqueFree_of_le_enatCard (f : ∀ (i : ι), V i) (hc : n ≤ ENat.card ι) :
    ¬ (completeMultipartiteGraph V).CliqueFree n := by
  by_cases h : Infinite ι
  · exact not_cliqueFree_of_infinite V f
  · have : Fintype ι := fintypeOfNotInfinite h
    rw [ENat.card_eq_coe_fintype_card, Nat.cast_le] at hc
    exact not_cliqueFree_of_le_card V f hc

end completeMultipartiteGraph

/-- Clique-freeness is preserved by `replaceVertex`. -/
/-
**SimpleGraph.CliqueFree.replaceVertex** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Cl
iqueFree`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {n : ℕ} [inst : DecidableEq α],   G.C
liqueFree n → ∀ (s t : α), (G.replaceVertex s t).CliqueFree n
参数：s t : α；G.replaceVertex s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.not_cliqueFree_iff_top_isContained`：not_cliqueFree_iff_top_i
sContained (n : Nat) : ¬G.CliqueFree n ↔ completeGraph (Fin n) ⊑ G
· 使用定理 `SimpleGraph.replaceVertex_self`：∀ {V : Type u_1} (G : SimpleGraph V) (s 
: V) [inst : DecidableEq V], G.replaceVertex s s = G
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Embedding.isContained`：∀ {V : Type u_1} {W : Type u_2} {G : 
SimpleGraph V} {H : SimpleGraph W} (f : G ↪g H), G.IsContained H
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Embedding.apply_eq_iff_eq`：apply_eq_iff_eq {α β} (f : α ↪ β) (x
 y : α) : f x = f y ↔ x = y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `SimpleGraph.adj_replaceVertex_iff_of_ne`：adj_replaceVertex_iff_of_ne {v 
w : V} (hv : v != t) (hw : w != t) : (G.replaceVertex s t).Adj v w ↔ G.Adj v w

--- 原说明 ---
Clique-freeness is preserved by `replaceVertex`.
-/
protected theorem CliqueFree.replaceVertex [DecidableEq α] (h : G.CliqueFree n) (s t : α) :
    (G.replaceVertex s t).CliqueFree n := by
  contrapose h
  have ⟨φ, hφ⟩ := topEmbeddingOfNotCliqueFree h
  rw [not_cliqueFree_iff_top_isContained]
  by_cases mt : t ∈ Set.range φ
  · obtain ⟨x, hx⟩ := mt
    by_cases ms : s ∈ Set.range φ
    · obtain ⟨y, hy⟩ := ms
      have e := @hφ x y
      simp_rw [hx, hy, adj_comm, not_adj_replaceVertex_same, top_adj, false_iff, not_ne_iff] at e
      rwa [← hx, e, hy, replaceVertex_self, not_cliqueFree_iff_top_isContained] at h
    · unfold replaceVertex at hφ
      refine Embedding.isContained ⟨φ.setValue x s, fun {a b} ↦ ?_⟩
      simp only [Embedding.coeFn_mk, Embedding.setValue, not_exists.mp ms, ite_false]
      rw [apply_ite (G.Adj · _), apply_ite (G.Adj _ ·), apply_ite (G.Adj _ ·)]
      convert! @hφ a b <;> simp only [← φ.apply_eq_iff_eq, SimpleGraph.irrefl, hx]
  · refine Embedding.isContained ⟨φ, ?_⟩
    simp_rw [Set.mem_range, not_exists, ← ne_eq] at mt
    conv at hφ => enter [a, b]; rw [G.adj_replaceVertex_iff_of_ne _ (mt a) (mt b)]
    exact hφ

@[simp]
/-
**SimpleGraph.cliqueFree_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFree_one : G.CliqueFree 1 ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cliqueFree_one : G.CliqueFree 1 ↔ IsEmpty α := by
  simp [CliqueFree, isEmpty_iff]

@[simp]
/-
**SimpleGraph.cliqueFree_two** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFree_two : G.CliqueFree 2 ↔ G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `SimpleGraph.cliqueFree_bot`：cliqueFree_bot (h : 2 <= n) : (⊥ : SimpleGra
ph α).CliqueFree n
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cliqueFree_two : G.CliqueFree 2 ↔ G = ⊥ := by
  classical
  constructor
  · simp_rw [← edgeSet_eq_empty, Set.eq_empty_iff_forall_notMem, Sym2.forall, mem_edgeSet]
    exact fun h a b hab => h _ ⟨by simpa [hab.ne], card_pair hab.ne⟩
  · rintro rfl
    exact cliqueFree_bot le_rfl
/-
**SimpleGraph.CliqueFree.mem_of_sup_edge_isNClique** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.CliqueFree`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {x y : α} {t : Finset α} {n : ℕ},   G
.CliqueFree n → (G ⊔ SimpleGraph.edge x y).IsNClique n t → x ∈ t
参数：G ⊔ SimpleGraph.edge x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
· 使用引理 `Set.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s {a} 
↔ a ∉ s
· 使用定理 `SimpleGraph.IsClique.sdiff_of_sup_edge`：∀ {α : Type u_1} {G : SimpleGrap
h α} {v w : α} {s : Set α}, (G ⊔ SimpleGraph.edge v w).IsClique s → G.IsClique (
s \ {v})
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
-/
lemma CliqueFree.mem_of_sup_edge_isNClique {x y : α} {t : Finset α} {n : ℕ} (h : G.CliqueFree n)
    (hc : (G ⊔ edge x y).IsNClique n t) : x ∈ t := by
  by_contra hf
  have ht : (t : Set α) \ {x} = t := sdiff_eq_left.mpr <| Set.disjoint_singleton_right.mpr hf
  exact h t ⟨ht ▸ hc.1.sdiff_of_sup_edge, hc.2⟩

/-- Adding an edge increases the clique number by at most one. -/
/-
**SimpleGraph.CliqueFree.sup_edge** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.CliqueF
ree`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {n : ℕ},   G.CliqueFree n → ∀ (v w : 
α), (G ⊔ SimpleGraph.edge v w).CliqueFree (n + 1)
参数：v w : α；G ⊔ SimpleGraph.edge v w；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsNClique.not_cliqueFree`：∀ {α : Type u_1} {G : SimpleGraph 
α} {n : ℕ} {s : Finset α}, G.IsNClique n s → ¬G.CliqueFree n
· 使用定理 `SimpleGraph.IsNClique.erase_of_sup_edge_of_mem`：∀ {α : Type u_1} {G : Si
mpleGraph α} [inst : DecidableEq α] {v w : α} {s : Finset α} {n : ℕ},   (G ⊔ Sim
pleGraph.edge v w).IsNClique n s → v…
· 使用定理 `SimpleGraph.CliqueFree.mem_of_sup_edge_isNClique`：∀ {α : Type u_1} {G : 
SimpleGraph α} {x y : α} {t : Finset α} {n : ℕ},   G.CliqueFree n → (G ⊔ SimpleG
raph.edge x y).IsNClique n t → x ∈ t
· 使用定理 `SimpleGraph.CliqueFree.mono`：∀ {α : Type u_1} {G : SimpleGraph α} {m n :
 ℕ}, m ≤ n → G.CliqueFree m → G.CliqueFree n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ

--- 原说明 ---
Adding an edge increases the clique number by at most one.
-/
protected theorem CliqueFree.sup_edge (h : G.CliqueFree n) (v w : α) :
    (G ⊔ edge v w).CliqueFree (n + 1) := by
  classical
  exact fun _ hs ↦ (hs.erase_of_sup_edge_of_mem <|
    (h.mono n.le_succ).mem_of_sup_edge_isNClique hs).not_cliqueFree h
/-
**SimpleGraph.IsNClique.exists_not_adj_of_cliqueFree_succ** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.IsNClique`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {n : ℕ} {s : Finset α},   G.IsNClique
 n s → G.CliqueFree (n + 1) → ∀ (x : α), ∃ y ∈ s, ¬G.Adj x y
参数：n + 1；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `SimpleGraph.IsNClique.not_cliqueFree`：∀ {α : Type u_1} {G : SimpleGraph 
α} {n : ℕ} {s : Finset α}, G.IsNClique n s → ¬G.CliqueFree n
· 使用定理 `SimpleGraph.IsNClique.insert`：∀ {α : Type u_1} {G : SimpleGraph α} {n : 
ℕ} {s : Finset α} {a : α} [inst : DecidableEq α],   G.IsNClique n s → (∀ b ∈ s, 
G.Adj a b) → G.IsN…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma IsNClique.exists_not_adj_of_cliqueFree_succ (hc : G.IsNClique n s)
    (h : G.CliqueFree (n + 1)) (x : α) : ∃ y, y ∈ s ∧ ¬ G.Adj x y := by
  classical
  by_contra! hf
  exact (hc.insert hf).not_cliqueFree h
/-
**SimpleGraph.exists_of_maximal_cliqueFree_not_adj** 是 Mathlib 中的一个引理，位于命名空间 `Si
mpleGraph`。
形式化陈述：exists_of_maximal_cliqueFree_not_adj [DecidableEq α] (h : Maximal (fun H =
> H.CliqueFree (n + 1)) G) {x y : α} (hne : x != y) (hn : ¬ G.Adj x y) : exists 
s, x ∉ s ∧ y ∉ s ∧ G.IsNClique n (insert x s) ∧ G.IsNClique n (insert y s)
参数：h : Maximal (fun H => H.CliqueFree (n + 1)) G；hne : x != y；hn : ¬ G.Adj x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_forall_not`：not_forall_not : (¬forall x, ¬p x) ↔ exists x, p x
· 使用定理 `Maximal.not_prop_of_gt`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst 
: Preorder α], Maximal P x → x < y → ¬P y
· 使用引理 `SimpleGraph.lt_sup_edge`：lt_sup_edge (hne : s != t) (hn : ¬ G.Adj s t) :
 G < G ⊔ edge s t
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.erase_right_comm`：erase_right_comm {a b : α} {s : Finset α} : era
se (erase s a) b = erase (erase s b) a
· 使用定理 `SimpleGraph.CliqueFree.mem_of_sup_edge_isNClique`：∀ {α : Type u_1} {G : 
SimpleGraph α} {x y : α} {t : Finset α} {n : ℕ},   G.CliqueFree n → (G ⊔ SimpleG
raph.edge x y).IsNClique n t → x ∈ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `SimpleGraph.edge_comm`：edge_comm : edge s t = edge t s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.mem_erase_of_ne_of_mem`：mem_erase_of_ne_of_mem : a != b -> a in s
 -> a in erase s b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SimpleGraph.IsNClique.erase_of_sup_edge_of_mem`：∀ {α : Type u_1} {G : Si
mpleGraph α} [inst : DecidableEq α] {v w : α} {s : Finset α} {n : ℕ},   (G ⊔ Sim
pleGraph.edge v w).IsNClique n s → v…
-/
lemma exists_of_maximal_cliqueFree_not_adj [DecidableEq α]
    (h : Maximal (fun H ↦ H.CliqueFree (n + 1)) G) {x y : α} (hne : x ≠ y) (hn : ¬ G.Adj x y) :
    ∃ s, x ∉ s ∧ y ∉ s ∧ G.IsNClique n (insert x s) ∧ G.IsNClique n (insert y s) := by
  obtain ⟨t, hc⟩ := not_forall_not.1 <| h.not_prop_of_gt <| G.lt_sup_edge _ _ hne hn
  use (t.erase x).erase y, erase_right_comm (a := x) ▸ (notMem_erase _ _), notMem_erase _ _
  have h1 := h.1.mem_of_sup_edge_isNClique hc
  have h2 := h.1.mem_of_sup_edge_isNClique (edge_comm .. ▸ hc)
  rw [insert_erase <| mem_erase_of_ne_of_mem hne.symm h2, erase_right_comm,
      insert_erase <| mem_erase_of_ne_of_mem hne h1]
  exact ⟨(edge_comm .. ▸ hc).erase_of_sup_edge_of_mem h2, hc.erase_of_sup_edge_of_mem h1⟩

end CliqueFree

section CliqueFreeOn
variable {s s₁ s₂ : Set α} {a : α} {m n : ℕ}

/-- `G.CliqueFreeOn s n` means that `G` has no `n`-cliques contained in `s`. -/
/-
**SimpleGraph.CliqueFreeOn** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：CliqueFreeOn (G : SimpleGraph α) (s : Set α) (n : Nat) : Prop
参数：G : SimpleGraph α；s : Set α；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.CliqueFreeOn s n` means that `G` has no `n`-cliques contained in `s`.
-/
def CliqueFreeOn (G : SimpleGraph α) (s : Set α) (n : ℕ) : Prop :=
  ∀ ⦃t⦄, ↑t ⊆ s → ¬G.IsNClique n t
/-
**SimpleGraph.CliqueFreeOn.subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.CliqueF
reeOn`。
形式化陈述：∀ {α : Type u_1} (G : SimpleGraph α) {s₁ s₂ : Set α} {n : ℕ}, s₁ ⊆ s₂ → G.
CliqueFreeOn s₂ n → G.CliqueFreeOn s₁ n
参数：G : SimpleGraph α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem CliqueFreeOn.subset (hs : s₁ ⊆ s₂) (h₂ : G.CliqueFreeOn s₂ n) : G.CliqueFreeOn s₁ n :=
  fun _t hts => h₂ <| hts.trans hs
/-
**SimpleGraph.CliqueFreeOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.CliqueFre
eOn`。
形式化陈述：∀ {α : Type u_1} (G : SimpleGraph α) {s : Set α} {m n : ℕ}, m ≤ n → G.Cliq
ueFreeOn s m → G.CliqueFreeOn s n
参数：G : SimpleGraph α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.exists_subset_card_eq`：exists_subset_card_eq (hns : n <= #s) : ex
ists t subseteq s, #t = n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `SimpleGraph.IsClique.subset`：∀ {α : Type u_1} {G : SimpleGraph α} {s t :
 Set α}, t ⊆ s → G.IsClique s → G.IsClique t
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
-/
theorem CliqueFreeOn.mono (hmn : m ≤ n) (hG : G.CliqueFreeOn s m) : G.CliqueFreeOn s n := by
  rintro t hts ht
  obtain ⟨u, hut, hu⟩ := exists_subset_card_eq (hmn.trans ht.card_eq.ge)
  exact hG ((coe_subset.2 hut).trans hts) ⟨ht.isClique.subset hut, hu⟩
/-
**SimpleGraph.CliqueFreeOn.anti** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.CliqueFre
eOn`。
形式化陈述：∀ {α : Type u_1} (G H : SimpleGraph α) {s : Set α} {n : ℕ}, G ≤ H → H.Cliq
ueFreeOn s n → G.CliqueFreeOn s n
参数：G H : SimpleGraph α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsNClique.mono`：∀ {α : Type u_1} {G H : SimpleGraph α} {n : 
ℕ} {s : Finset α}, G ≤ H → G.IsNClique n s → H.IsNClique n s
-/
theorem CliqueFreeOn.anti (hGH : G ≤ H) (hH : H.CliqueFreeOn s n) : G.CliqueFreeOn s n :=
  fun _t hts ht => hH hts <| ht.mono hGH

@[simp]
/-
**SimpleGraph.cliqueFreeOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFreeOn_empty : G.CliqueFreeOn ∅ n ↔ n != 0
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
theorem cliqueFreeOn_empty : G.CliqueFreeOn ∅ n ↔ n ≠ 0 := by
  simp [CliqueFreeOn, Set.subset_empty_iff]

@[simp]
/-
**SimpleGraph.cliqueFreeOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFreeOn_singleton : G.CliqueFreeOn {a} n ↔ 1 < n
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 32 条，此处仅展示前 30 条）
-/
theorem cliqueFreeOn_singleton : G.CliqueFreeOn {a} n ↔ 1 < n := by
  obtain _ | _ | n := n <;>
    simp [CliqueFreeOn, isNClique_iff, ← subset_singleton_iff', (Nat.succ_ne_zero _).symm]

@[simp]
/-
**SimpleGraph.cliqueFreeOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFreeOn_univ : G.CliqueFreeOn Set.univ n ↔ G.CliqueFree n
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cliqueFreeOn_univ : G.CliqueFreeOn Set.univ n ↔ G.CliqueFree n := by
  simp [CliqueFree, CliqueFreeOn]
/-
**SimpleGraph.CliqueFree.cliqueFreeOn** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Cli
queFree`。
形式化陈述：∀ {α : Type u_1} (G : SimpleGraph α) {s : Set α} {n : ℕ}, G.CliqueFree n →
 G.CliqueFreeOn s n
参数：G : SimpleGraph α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem CliqueFree.cliqueFreeOn (hG : G.CliqueFree n) : G.CliqueFreeOn s n :=
  fun _t _ ↦ hG _
/-
**SimpleGraph.cliqueFreeOn_of_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFreeOn_of_card_lt {s : Finset α} (h : #s < n) : G.CliqueFreeOn s n
参数：h : #s < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
-/
theorem cliqueFreeOn_of_card_lt {s : Finset α} (h : #s < n) : G.CliqueFreeOn s n :=
  fun _t hts ht => h.not_ge <| ht.2.symm.trans_le <| card_mono hts

-- TODO: Restate using `SimpleGraph.IndepSet` once we have it
@[simp]
/-
**SimpleGraph.cliqueFreeOn_two** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFreeOn_two : G.CliqueFreeOn s 2 ↔ s.Pairwise (G.Adjᶜ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cliqueFreeOn_two : G.CliqueFreeOn s 2 ↔ s.Pairwise (G.Adjᶜ) := by
  classical
  refine ⟨fun h a ha b hb _ hab => h ?_ ⟨by simpa [hab.ne], card_pair hab.ne⟩, ?_⟩
  · push_cast
    exact Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hb⟩
  simp only [CliqueFreeOn, isNClique_iff, card_eq_two, not_and, not_exists]
  rintro h t hst ht a b hab rfl
  simp only [coe_insert, coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff] at hst
  refine h hst.1 hst.2 hab (ht ?_ ?_ hab) <;> simp
/-
**SimpleGraph.CliqueFreeOn.of_succ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Clique
FreeOn`。
形式化陈述：∀ {α : Type u_1} (G : SimpleGraph α) {s : Set α} {a : α} {n : ℕ},   G.Cliq
ueFreeOn s (n + 1) → a ∈ s → G.CliqueFreeOn (s ∩ G.neighborSet a) n
参数：G : SimpleGraph α；n + 1；s ∩ G.neighborSet a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `SimpleGraph.IsNClique.insert`：∀ {α : Type u_1} {G : SimpleGraph α} {n : 
ℕ} {s : Finset α} {a : α} [inst : DecidableEq α],   G.IsNClique n s → (∀ b ∈ s, 
G.Adj a b) → G.IsN…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem CliqueFreeOn.of_succ (hs : G.CliqueFreeOn s (n + 1)) (ha : a ∈ s) :
    G.CliqueFreeOn (s ∩ G.neighborSet a) n := by
  classical
  refine fun t hts ht => hs ?_ (ht.insert fun b hb => (hts hb).2)
  push_cast
  exact Set.insert_subset_iff.2 ⟨ha, hts.trans Set.inter_subset_left⟩
/-
**SimpleGraph.cliqueFree_induce_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFree_induce_iff (s : Set α) (n : Nat) : (G.induce s).CliqueFree n ↔ 
G.CliqueFreeOn s n
参数：s : Set α；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.filter_eq_self`：∀ {α : Type u_1} {p : α → Prop} [inst : Decidable
Pred p] {s : Finset α}, Finset.filter p s = s ↔ ∀ x ∈ s, p x
· 使用定理 `Finset.subtype_map`：subtype_map (p : α -> Prop) [DecidablePred p] {s : F
inset α} : (s.subtype p).map (Embedding.subtype _) = s.filter p
· 使用定理 `Finset.map_subtype_subset`：map_subtype_subset {t : Set α} (s : Finset t)
 : ↑(s.map (Embedding.subtype _)) subseteq t
-/
theorem cliqueFree_induce_iff (s : Set α) (n : ℕ) :
    (G.induce s).CliqueFree n ↔ G.CliqueFreeOn s n := by
  classical
  simp only [CliqueFree, isNClique_induce_iff]
  refine ⟨fun h t ht ↦ ?_, (· <| map_subtype_subset ·)⟩
  have := h <| t.subtype _
  rwa [← filter_eq_self.mpr ht, ← subtype_map]

end CliqueFreeOn

/-! ### Set of cliques -/


section CliqueSet

variable {n : ℕ} {s : Finset α}

/-- The `n`-cliques in a graph as a set. -/
/-
**SimpleGraph.cliqueSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueSet (n : Nat) : Set (Finset α)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-cliques in a graph as a set.
-/
def cliqueSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNClique n s }

variable {G H}

@[simp]
/-
**SimpleGraph.mem_cliqueSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_cliqueSet_iff : s in G.cliqueSet n ↔ G.IsNClique n s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cliqueSet_iff : s ∈ G.cliqueSet n ↔ G.IsNClique n s :=
  Iff.rfl

@[simp]
/-
**SimpleGraph.cliqueSet_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueSet_eq_empty_iff : G.cliqueSet n = ∅ ↔ G.CliqueFree n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cliqueSet_eq_empty_iff : G.cliqueSet n = ∅ ↔ G.CliqueFree n := by
  simp_rw [CliqueFree, Set.eq_empty_iff_forall_notMem, mem_cliqueSet_iff]

protected alias ⟨_, CliqueFree.cliqueSet⟩ := cliqueSet_eq_empty_iff

@[gcongr, mono]
/-
**SimpleGraph.cliqueSet_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueSet_mono (h : G <= H) : G.cliqueSet n subseteq H.cliqueSet n
参数：h : G <= H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsNClique.mono`：∀ {α : Type u_1} {G H : SimpleGraph α} {n : 
ℕ} {s : Finset α}, G ≤ H → G.IsNClique n s → H.IsNClique n s
-/
theorem cliqueSet_mono (h : G ≤ H) : G.cliqueSet n ⊆ H.cliqueSet n :=
  fun _ ↦ IsNClique.mono h
/-
**SimpleGraph.cliqueSet_mono'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueSet_mono' (h : G <= H) : G.cliqueSet <= H.cliqueSet
参数：h : G <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.cliqueSet_mono`：cliqueSet_mono (h : G <= H) : G.cliqueSet n 
subseteq H.cliqueSet n
-/
theorem cliqueSet_mono' (h : G ≤ H) : G.cliqueSet ≤ H.cliqueSet :=
  fun _ ↦ cliqueSet_mono h

@[simp]
/-
**SimpleGraph.cliqueSet_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueSet_zero (G : SimpleGraph α) : G.cliqueSet 0 = {∅}
参数：G : SimpleGraph α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cliqueSet_zero (G : SimpleGraph α) : G.cliqueSet 0 = {∅} := Set.ext fun s => by simp

@[simp]
/-
**SimpleGraph.cliqueSet_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueSet_one (G : SimpleGraph α) : G.cliqueSet 1 = Set.range singleton
参数：G : SimpleGraph α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cliqueSet_one (G : SimpleGraph α) : G.cliqueSet 1 = Set.range singleton :=
  Set.ext fun s => by simp [eq_comm]

@[simp]
/-
**SimpleGraph.cliqueSet_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueSet_bot (hn : 1 < n) : (⊥ : SimpleGraph α).cliqueSet n = ∅
参数：hn : 1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.CliqueFree.cliqueSet`：∀ {α : Type u_1} {G : SimpleGraph α} {
n : ℕ}, G.CliqueFree n → G.cliqueSet n = ∅
· 使用定理 `SimpleGraph.cliqueFree_bot`：cliqueFree_bot (h : 2 <= n) : (⊥ : SimpleGra
ph α).CliqueFree n
-/
theorem cliqueSet_bot (hn : 1 < n) : (⊥ : SimpleGraph α).cliqueSet n = ∅ :=
  (cliqueFree_bot hn).cliqueSet

@[simp]
/-
**SimpleGraph.cliqueSet_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueSet_map (hn : n != 1) (G : SimpleGraph α) (f : α ↪ β) : (G.map f).cl
iqueSet n = map f '' G.cliqueSet n
参数：hn : n != 1；G : SimpleGraph α；f : α ↪ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.image_preimage`：image_preimage [DecidableEq β] (f : α -> β) (s : 
Finset β) [forall x, Decidable (x in Set.range f)] (hf : Set.InjOn f (f ⁻¹' ↑s))
 : image f …
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用引理 `Finset.exists_mem_ne`：exists_mem_ne (hs : 1 < #s) (a : α) : exists b in 
s, b != a
· 使用定理 `Ne.lt_of_le'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≠ b 
→ b ≤ a → b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.map_adj_apply`：map_adj_apply {G : SimpleGraph V} {f : V ↪ W}
 {a b : V} : (G.map f).Adj (f a) (f b) ↔ G.Adj a b
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `SimpleGraph.IsNClique.map`：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGr
aph α} {n : ℕ} {s : Finset α},   G.IsNClique n s → ∀ {f : α ↪ β}, (SimpleGraph.m
ap (⇑f) G).IsNC…
-/
theorem cliqueSet_map (hn : n ≠ 1) (G : SimpleGraph α) (f : α ↪ β) :
    (G.map f).cliqueSet n = map f '' G.cliqueSet n := by
  ext s
  constructor
  · rintro ⟨hs, rfl⟩
    have hs' : (s.preimage f f.injective.injOn).map f = s := by
      classical
      rw [map_eq_image, image_preimage, filter_true_of_mem]
      rintro a ha
      obtain ⟨b, hb, hba⟩ := exists_mem_ne (hn.lt_of_le' <| Finset.card_pos.2 ⟨a, ha⟩) a
      obtain ⟨-, c, _, _, hc, _⟩ := hs ha hb hba.symm
      exact ⟨c, hc⟩
    refine ⟨s.preimage f f.injective.injOn, ⟨?_, by rw [← card_map f, hs']⟩, hs'⟩
    rw [coe_preimage]
    exact fun a ha b hb hab => map_adj_apply.1 (hs ha hb <| f.injective.ne hab)
  · rintro ⟨s, hs, rfl⟩
    exact hs.map

@[simp]
/-
**SimpleGraph.cliqueSet_map_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueSet_map_of_equiv (G : SimpleGraph α) (e : α ≃ β) (n : Nat) : (G.map 
e).cliqueSet n = map e.toEmbedding '' G.cliqueSet n
参数：G : SimpleGraph α；e : α ≃ β；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.cliqueSet_one`：cliqueSet_one (G : SimpleGraph α) : G.cliqueS
et 1 = Set.range singleton
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `Finset.map_singleton`：map_singleton (f : α ↪ β) (a : α) : map f {a} = {f
 a}
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.cliqueSet_map`：cliqueSet_map (hn : n != 1) (G : SimpleGraph 
α) (f : α ↪ β) : (G.map f).cliqueSet n = map f '' G.cliqueSet n
-/
theorem cliqueSet_map_of_equiv (G : SimpleGraph α) (e : α ≃ β) (n : ℕ) :
    (G.map e).cliqueSet n = map e.toEmbedding '' G.cliqueSet n := by
  obtain rfl | hn := eq_or_ne n 1
  · ext
    simp [e.exists_congr_left]
  · simpa using cliqueSet_map hn G e.toEmbedding

end CliqueSet

/-! ### Clique number -/


section CliqueNumber

variable {α : Type*} {G : SimpleGraph α}

/-- The maximum number of vertices in a clique of a graph `G`. -/
/-
**SimpleGraph.cliqueNum** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueNum (G : SimpleGraph α) : Nat
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximum number of vertices in a clique of a graph `G`.
-/
noncomputable def cliqueNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNClique n s}
/-
**SimpleGraph.finite_cliqueNum_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma finite_cliqueNum_bddAbove [Finite α] : BddAbove {n | ∃ s, G.IsNClique n s} := by
  have := ofFinite α
  use card α
  rintro y ⟨s, syc⟩
  rw [isNClique_iff] at syc
  rw [← syc.right]
  exact Finset.card_le_card (Finset.subset_univ s)
/-
**SimpleGraph.IsClique.card_le_cliqueNum** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsClique`。
形式化陈述：∀ {α : Type u_3} {G : SimpleGraph α} [Finite α] {t : Finset α} {tc : G.IsC
lique ↑t}, t.card ≤ G.cliqueNum
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Clique.0.SimpleGraph.finite_c
liqueNum_bddAbove`：∀ {α : Type u_3} {G : SimpleGraph α} [Finite α], BddAbove {n 
| ∃ s, G.IsNClique n s}
-/
lemma IsClique.card_le_cliqueNum [Finite α] {t : Finset α} {tc : G.IsClique t} :
    #t ≤ G.cliqueNum := by
  exact le_csSup G.finite_cliqueNum_bddAbove (Exists.intro t ⟨tc, rfl⟩)
/-
**SimpleGraph.exists_isNClique_cliqueNum** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：exists_isNClique_cliqueNum : exists s, G.IsNClique G.cliqueNum s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sSup_mem`：sSup_mem {s : Set Nat} (h₁ : s.Nonempty) (h₂ : BddAbove s)
 : sSup s in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
-/
lemma exists_isNClique_cliqueNum : ∃ s, G.IsNClique G.cliqueNum s := by
  by_cases h : BddAbove {n | ∃ s, G.IsNClique n s}
  · exact Nat.sSup_mem ⟨0, by simp⟩ h
  · simp [cliqueNum, h]
/-
**SimpleGraph.cliqueNum_induce_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueNum_induce_le [Finite α] (s : Set α) : (G.induce s).cliqueNum <= G.c
liqueNum
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_isNClique_cliqueNum`：exists_isNClique_cliqueNum : exi
sts s, G.IsNClique G.cliqueNum s
· 使用定理 `SimpleGraph.IsClique.card_le_cliqueNum`：∀ {α : Type u_3} {G : SimpleGrap
h α} [Finite α] {t : Finset α} {tc : G.IsClique ↑t}, t.card ≤ G.cliqueNum
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isNClique_induce_iff`：isNClique_induce_iff (s : Set α) (t : 
Finset s) (n : Nat) : (G.induce s).IsNClique n t ↔ G.IsNClique n (t.map (.subtyp
e _))
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
-/
theorem cliqueNum_induce_le [Finite α] (s : Set α) :
    (G.induce s).cliqueNum ≤ G.cliqueNum := by
  have ⟨t', tc⟩ := (G.induce s).exists_isNClique_cliqueNum
  rw [isNClique_induce_iff] at tc
  exact tc.card_eq ▸ tc.isClique.card_le_cliqueNum

/-- A maximum clique in a graph `G` is a clique with the largest possible size. -/
-- TODO: replace with `MaximalFor (G.IsClique ∘ (↑)) card s`
/-
**SimpleGraph.IsMaximumClique** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{α : Type u_3} → [Finite α] → SimpleGraph α → Finset α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure IsMaximumClique [Finite α] (G : SimpleGraph α) (s : Finset α) : Prop where
  isClique : G.IsClique s
  maximum : ∀ t : Finset α, G.IsClique t → #t ≤ #s
/-
**SimpleGraph.isMaximumClique_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isMaximumClique_iff [Finite α] {s : Finset α} : G.IsMaximumClique s ↔ G.Is
Clique s ∧ forall t : Finset α, G.IsClique t -> #t <= #s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsMaximumClique.isClique`：∀ {α : Type u_3} [inst : Finite α]
 {G : SimpleGraph α} {s : Finset α}, G.IsMaximumClique s → G.IsClique ↑s
· 使用定理 `SimpleGraph.IsMaximumClique.maximum`：∀ {α : Type u_3} [inst : Finite α] 
{G : SimpleGraph α} {s : Finset α},   G.IsMaximumClique s → ∀ (t : Finset α), G.
IsClique ↑t → t.card ≤ s.…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isMaximumClique_iff [Finite α] {s : Finset α} :
    G.IsMaximumClique s ↔ G.IsClique s ∧ ∀ t : Finset α, G.IsClique t → #t ≤ #s :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- A maximal clique in a graph `G` is a clique that cannot be extended by adding more vertices. -/
/-
**SimpleGraph.isMaximalClique_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isMaximalClique_iff {s : Set α} : Maximal G.IsClique s ↔ G.IsClique s ∧ fo
rall t : Set α, G.IsClique t -> s subseteq t -> t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A maximal clique in a graph `G` is a clique that cannot be extended by adding mo
re vertices.
-/
theorem isMaximalClique_iff {s : Set α} :
    Maximal G.IsClique s ↔ G.IsClique s ∧ ∀ t : Set α, G.IsClique t → s ⊆ t → t ⊆ s :=
  Iff.rfl
/-
**SimpleGraph.IsMaximumClique.isMaximalClique** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.IsMaximumClique`。
形式化陈述：∀ {α : Type u_3} {G : SimpleGraph α} [inst : Finite α] (s : Finset α), G.I
sMaximumClique s → Maximal G.IsClique ↑s
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsMaximumClique.isClique`：∀ {α : Type u_3} [inst : Finite α]
 {G : SimpleGraph α} {s : Finset α}, G.IsMaximumClique s → G.IsClique ↑s
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.IsMaximumClique.maximum`：∀ {α : Type u_3} [inst : Finite α] 
{G : SimpleGraph α} {s : Finset α},   G.IsMaximumClique s → ∀ (t : Finset α), G.
IsClique ↑t → t.card ≤ s.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `ssubset_of_ne_of_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [i
nst : PartialOrder α] {a b : α}, a ≠ b → a ⊆ b → a ⊂ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.subset_toFinset`：subset_toFinset {s : Finset α} [Fintype t] : s subs
eteq t.toFinset ↔ ↑s subseteq t
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
lemma IsMaximumClique.isMaximalClique [Finite α] (s : Finset α) (M : G.IsMaximumClique s) :
    Maximal G.IsClique s :=
  ⟨ M.isClique,
    fun t ht hsub => by
      by_contra hc
      have fint := ofFinite t
      have ne : s ≠ t.toFinset := fun a ↦ by subst a; simp_all[Set.coe_toFinset, not_true_eq_false]
      have hle : #t.toFinset ≤ #s := M.maximum t.toFinset (by simp [Set.coe_toFinset, ht])
      have hlt : #s < #t.toFinset :=
        card_lt_card (ssubset_of_ne_of_subset ne (Set.subset_toFinset.mpr hsub))
      exact lt_irrefl _ (lt_of_lt_of_le hlt hle) ⟩
/-
**SimpleGraph.maximumClique_card_eq_cliqueNum** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph`。
形式化陈述：maximumClique_card_eq_cliqueNum [Finite α] (s : Finset α) (sm : G.IsMaximu
mClique s) : #s = G.cliqueNum
参数：s : Finset α；sm : G.IsMaximumClique s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_isNClique_cliqueNum`：exists_isNClique_cliqueNum : exi
sts s, G.IsNClique G.cliqueNum s
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `SimpleGraph.IsClique.card_le_cliqueNum`：∀ {α : Type u_3} {G : SimpleGrap
h α} [Finite α] {t : Finset α} {tc : G.IsClique ↑t}, t.card ≤ G.cliqueNum
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma maximumClique_card_eq_cliqueNum [Finite α] (s : Finset α) (sm : G.IsMaximumClique s) :
    #s = G.cliqueNum := by
  obtain ⟨sc, sm⟩ := sm
  obtain ⟨t, tc, tcard⟩ := G.exists_isNClique_cliqueNum
  exact eq_of_le_of_not_lt sc.card_le_cliqueNum (by simp [← tcard, sm t tc])
/-
**SimpleGraph.maximumClique_exists** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：maximumClique_exists [Finite α] : exists (s : Finset α), G.IsMaximumClique
 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_isNClique_cliqueNum`：exists_isNClique_cliqueNum : exi
sts s, G.IsNClique G.cliqueNum s
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `SimpleGraph.IsClique.card_le_cliqueNum`：∀ {α : Type u_3} {G : SimpleGrap
h α} [Finite α] {t : Finset α} {tc : G.IsClique ↑t}, t.card ≤ G.cliqueNum
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
-/
lemma maximumClique_exists [Finite α] : ∃ (s : Finset α), G.IsMaximumClique s := by
  obtain ⟨s, snc⟩ := G.exists_isNClique_cliqueNum
  exact ⟨s, ⟨snc.isClique, fun t ht => snc.card_eq.symm ▸ ht.card_le_cliqueNum⟩⟩

end CliqueNumber

/-! ### Finset of cliques -/


section CliqueFinset

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α}

/-- The `n`-cliques in a graph as a finset. -/
/-
**SimpleGraph.cliqueFinset** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFinset (n : Nat) : Finset (Finset α)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-cliques in a graph as a finset.
-/
def cliqueFinset (n : ℕ) : Finset (Finset α) := {s | G.IsNClique n s}

variable {G} in
@[simp]
/-
**SimpleGraph.mem_cliqueFinset_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_cliqueFinset_iff : s in G.cliqueFinset n ↔ G.IsNClique n s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem mem_cliqueFinset_iff : s ∈ G.cliqueFinset n ↔ G.IsNClique n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _

@[simp, norm_cast]
/-
**SimpleGraph.coe_cliqueFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：coe_cliqueFinset (n : Nat) : (G.cliqueFinset n : Set (Finset α)) = G.cliqu
eSet n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SimpleGraph.mem_cliqueFinset_iff`：mem_cliqueFinset_iff : s in G.cliqueFi
nset n ↔ G.IsNClique n s
-/
theorem coe_cliqueFinset (n : ℕ) : (G.cliqueFinset n : Set (Finset α)) = G.cliqueSet n :=
  Set.ext fun _ ↦ mem_cliqueFinset_iff

variable {G}

@[simp]
/-
**SimpleGraph.cliqueFinset_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFinset_eq_empty_iff : G.cliqueFinset n = ∅ ↔ G.CliqueFree n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cliqueFinset_eq_empty_iff : G.cliqueFinset n = ∅ ↔ G.CliqueFree n := by
  simp_rw [CliqueFree, eq_empty_iff_forall_notMem, mem_cliqueFinset_iff]

protected alias ⟨_, CliqueFree.cliqueFinset⟩ := cliqueFinset_eq_empty_iff
/-
**SimpleGraph.card_cliqueFinset_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：card_cliqueFinset_le : #(G.cliqueFinset n) <= (card α).choose n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.card_powersetCard`：card_powersetCard (n : Nat) (s : Finset α) : c
ard (powersetCard n s) = Nat.choose (card s) n
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
-/
theorem card_cliqueFinset_le : #(G.cliqueFinset n) ≤ (card α).choose n := by
  rw [← card_univ, ← card_powersetCard]
  refine card_mono fun s => ?_
  simpa [mem_powersetCard_univ] using IsNClique.card_eq

variable [DecidableRel H.Adj]

@[gcongr, mono]
/-
**SimpleGraph.cliqueFinset_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFinset_mono (h : G <= H) : G.cliqueFinset n subseteq H.cliqueFinset 
n
参数：h : G <= H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.monotone_filter_right`：∀ {α : Type u_1} (s : Finset α) ⦃p q : α →
 Prop⦄ [inst : DecidablePred p] [inst_1 : DecidablePred q],   (∀ a ∈ s, p a → q 
a) → Finset.filter…
· 使用定理 `SimpleGraph.IsNClique.mono`：∀ {α : Type u_1} {G H : SimpleGraph α} {n : 
ℕ} {s : Finset α}, G ≤ H → G.IsNClique n s → H.IsNClique n s
-/
theorem cliqueFinset_mono (h : G ≤ H) : G.cliqueFinset n ⊆ H.cliqueFinset n :=
  monotone_filter_right _ fun _ _ ↦ IsNClique.mono h

variable [Fintype β] [DecidableEq β] (G)

@[simp]
/-
**SimpleGraph.cliqueFinset_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFinset_map (f : α ↪ β) (hn : n != 1) : (G.map f).cliqueFinset n = (G
.cliqueFinset n).map ⟨map f, Finset.map_injective _⟩
参数：f : α ↪ β；hn : n != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Finset.map_injective`：map_injective (f : α ↪ β) : Injective (map f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_cliqueFinset`：coe_cliqueFinset (n : Nat) : (G.cliqueFins
et n : Set (Finset α)) = G.cliqueSet n
· 使用定理 `SimpleGraph.cliqueSet_map`：cliqueSet_map (hn : n != 1) (G : SimpleGraph 
α) (f : α ↪ β) : (G.map f).cliqueSet n = map f '' G.cliqueSet n
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cliqueFinset_map (f : α ↪ β) (hn : n ≠ 1) :
    (G.map f).cliqueFinset n = (G.cliqueFinset n).map ⟨map f, Finset.map_injective _⟩ :=
  coe_injective <| by
    simp_rw [coe_cliqueFinset, cliqueSet_map hn, coe_map, coe_cliqueFinset, Embedding.coeFn_mk]

@[simp]
/-
**SimpleGraph.cliqueFinset_map_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cliqueFinset_map_of_equiv (e : α ≃ β) (n : Nat) : (G.map e).cliqueFinset n
 = (G.cliqueFinset n).map ⟨map e.toEmbedding, Finset.map_injective _⟩
参数：e : α ≃ β；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Finset.map_injective`：map_injective (f : α ↪ β) : Injective (map f)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.coe_cliqueFinset`：coe_cliqueFinset (n : Nat) : (G.cliqueFins
et n : Set (Finset α)) = G.cliqueSet n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `SimpleGraph.cliqueSet_map_of_equiv`：cliqueSet_map_of_equiv (G : SimpleGr
aph α) (e : α ≃ β) (n : Nat) : (G.map e).cliqueSet n = map e.toEmbedding '' G.cl
iqueSet n
-/
theorem cliqueFinset_map_of_equiv (e : α ≃ β) (n : ℕ) : (G.map e).cliqueFinset n =
      (G.cliqueFinset n).map ⟨map e.toEmbedding, Finset.map_injective _⟩ :=
  coe_injective <| by push_cast; exact cliqueSet_map_of_equiv _ _ _

end CliqueFinset

/-! ### Independent Sets -/

section IndepSet

variable {s : Set α}

/-- An independent set in a graph is a set of vertices that are pairwise not adjacent. -/
@[wikidata Q1060343]
/-
**SimpleGraph.IsIndepSet** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsIndepSet (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An independent set in a graph is a set of vertices that are pairwise not adjacen
t.
-/
abbrev IsIndepSet (s : Set α) : Prop :=
  s.Pairwise (fun v w ↦ ¬G.Adj v w)
/-
**SimpleGraph.isIndepSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isIndepSet_iff : G.IsIndepSet s ↔ s.Pairwise (fun v w => ¬G.Adj v w)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isIndepSet_iff : G.IsIndepSet s ↔ s.Pairwise (fun v w ↦ ¬G.Adj v w) :=
  .rfl
/-
**SimpleGraph.isIndepSet_iff_isAntichain_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：isIndepSet_iff_isAntichain_adj : G.IsIndepSet s ↔ IsAntichain G.Adj s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isIndepSet_iff_isAntichain_adj : G.IsIndepSet s ↔ IsAntichain G.Adj s :=
  .rfl

/-- An independent set is a clique in the complement graph and vice versa. -/
/-
**SimpleGraph.isClique_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} (G : SimpleGraph α) {s : Set α}, Gᶜ.IsClique s ↔ G.IsInde
pSet s
参数：G : SimpleGraph α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isIndepSet_iff`：isIndepSet_iff : G.IsIndepSet s ↔ s.Pairwise
 (fun v w => ¬G.Adj v w)
· 使用定理 `SimpleGraph.isClique_iff`：isClique_iff : G.IsClique s ↔ s.Pairwise G.Adj
· 使用定理 `Set.Pairwise.eq_1`：∀ {α : Type u_1} (s : Set α) (r : α → α → Prop), s.Pa
irwise r = ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → x ≠ y → r x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An independent set is a clique in the complement graph and vice versa.
-/
@[simp] theorem isClique_compl : Gᶜ.IsClique s ↔ G.IsIndepSet s := by
  rw [isIndepSet_iff, isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]

/-- An independent set in the complement graph is a clique and vice versa. -/
/-
**SimpleGraph.isIndepSet_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} (G : SimpleGraph α) {s : Set α}, Gᶜ.IsIndepSet s ↔ G.IsCl
ique s
参数：G : SimpleGraph α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isIndepSet_iff`：isIndepSet_iff : G.IsIndepSet s ↔ s.Pairwise
 (fun v w => ¬G.Adj v w)
· 使用定理 `SimpleGraph.isClique_iff`：isClique_iff : G.IsClique s ↔ s.Pairwise G.Adj
· 使用定理 `Set.Pairwise.eq_1`：∀ {α : Type u_1} (s : Set α) (r : α → α → Prop), s.Pa
irwise r = ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → x ≠ y → r x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An independent set in the complement graph is a clique and vice versa.
-/
@[simp] theorem isIndepSet_compl : Gᶜ.IsIndepSet s ↔ G.IsClique s := by
  rw [isIndepSet_iff, isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsIndepSet s) :=
  decidable_of_iff' _ G.isIndepSet_iff

/-- If `s` is an independent set, its complement meets every edge of `G`. -/
/-
**SimpleGraph.IsIndepSet.nonempty_mem_compl_mem_edge** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.IsIndepSet`。
形式化陈述：∀ {α : Type u_1} (G : SimpleGraph α) {s : Set α},   G.IsIndepSet s → ∀ {e 
: Sym2 α}, e ∈ G.edgeSet → {b | b ∈ sᶜ ∧ b ∈ e}.Nonempty
参数：G : SimpleGraph α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_notMem`：not_notMem : ¬a ∉ s ↔ a in s
· 使用定理 `not_and'`：∀ {a b : Prop}, ¬(a ∧ b) ↔ b → ¬a
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym2.mem_mk_left`：mem_mk_left (x y : α) : x in s(x, y)
· 使用定理 `Sym2.mem_mk_right`：mem_mk_right (x y : α) : y in s(x, y)
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b

--- 原说明 ---
If `s` is an independent set, its complement meets every edge of `G`.
-/
lemma IsIndepSet.nonempty_mem_compl_mem_edge {s : Set α} (indA : G.IsIndepSet s) {e}
    (he : e ∈ G.edgeSet) : { b ∈ sᶜ | b ∈ e }.Nonempty := by
  obtain ⟨v, w⟩ := e
  by_contra! c
  refine indA ?_ ?_ he.ne he
  · exact Set.not_notMem.mp <| not_and'.mp (c ▸ Set.notMem_empty v) <| Sym2.mem_mk_left ..
  · exact Set.not_notMem.mp <| not_and'.mp (c ▸ Set.notMem_empty w) <| Sym2.mem_mk_right ..

/-- The neighbors of a vertex `v` form an independent set in a triangle free graph `G`. -/
/-
**SimpleGraph.isIndepSet_neighborSet_of_triangleFree** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph`。
形式化陈述：isIndepSet_neighborSet_of_triangleFree (h : G.CliqueFree 3) (v : α) : G.Is
IndepSet (G.neighborSet v)
参数：h : G.CliqueFree 3；v : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Set.Pairwise.eq_1`：∀ {α : Type u_1} (s : Set α) (r : α → α → Prop), s.Pa
irwise r = ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → x ≠ y → r x y
· 使用定理 `SimpleGraph.IsIndepSet.eq_1`：∀ {α : Type u_1} (G : SimpleGraph α) (s : S
et α), G.IsIndepSet s = s.Pairwise fun v w => ¬G.Adj v w
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.is3Clique_triple_iff`：is3Clique_triple_iff : G.IsNClique 3 {
a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The neighbors of a vertex `v` form an independent set in a triangle free graph `
G`.
-/
theorem isIndepSet_neighborSet_of_triangleFree (h : G.CliqueFree 3) (v : α) :
    G.IsIndepSet (G.neighborSet v) := by
  classical
  by_contra nind
  rw [IsIndepSet, Set.Pairwise] at nind
  push Not at nind
  simp_rw [mem_neighborSet] at nind
  obtain ⟨j, avj, k, avk, _, ajk⟩ := nind
  exact h {v, j, k} (is3Clique_triple_iff.mpr (by simp [avj, avk, ajk]))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The embedding of an independent set of an induced subgraph of the subgraph `G` is an independent
set in `G` and vice versa. -/
/-
**SimpleGraph.isIndepSet_induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isIndepSet_induce {F : Set α} {s : Set F} : ((⊤ : Subgraph G).induce F).co
e.IsIndepSet s ↔ G.IsIndepSet (Subtype.val '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The embedding of an independent set of an induced subgraph of the subgraph `G` i
s an independent
set in `G` and vice versa.
-/
theorem isIndepSet_induce {F : Set α} {s : Set F} :
    ((⊤ : Subgraph G).induce F).coe.IsIndepSet s ↔ G.IsIndepSet (Subtype.val '' s) := by
  simp [Set.Pairwise]

end IndepSet

/-! ### N-Independent sets -/


section NIndepSet

variable {n : ℕ} {s : Finset α}

/-- An `n`-independent set in a graph is a set of `n` vertices which are pairwise nonadjacent. -/
@[mk_iff]
/-
**SimpleGraph.IsNIndepSet** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{α : Type u_1} → SimpleGraph α → ℕ → Finset α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `n`-independent set in a graph is a set of `n` vertices which are pairwise no
nadjacent.
-/
structure IsNIndepSet (n : ℕ) (s : Finset α) : Prop where
  isIndepSet : G.IsIndepSet s
  card_eq : s.card = n

/-- An `n`-independent set is an `n`-clique in the complement graph and vice versa. -/
/-
**SimpleGraph.isNClique_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} (G : SimpleGraph α) {n : ℕ} {s : Finset α}, Gᶜ.IsNClique 
n s ↔ G.IsNIndepSet n s
参数：G : SimpleGraph α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isNIndepSet_iff`：∀ {α : Type u_1} (G : SimpleGraph α) (n : ℕ
) (s : Finset α), G.IsNIndepSet n s ↔ G.IsIndepSet ↑s ∧ s.card = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An `n`-independent set is an `n`-clique in the complement graph and vice versa.
-/
@[simp] theorem isNClique_compl : Gᶜ.IsNClique n s ↔ G.IsNIndepSet n s := by
  rw [isNIndepSet_iff]
  simp [isNClique_iff]

/-- An `n`-independent set in the complement graph is an `n`-clique and vice versa. -/
/-
**SimpleGraph.isNIndepSet_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} (G : SimpleGraph α) {n : ℕ} {s : Finset α}, Gᶜ.IsNIndepSe
t n s ↔ G.IsNClique n s
参数：G : SimpleGraph α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.isNClique_iff`：isNClique_iff : G.IsNClique n s ↔ G.IsClique 
s ∧ #s = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An `n`-independent set in the complement graph is an `n`-clique and vice versa.
-/
@[simp] theorem isNIndepSet_compl : Gᶜ.IsNIndepSet n s ↔ G.IsNClique n s := by
  rw [isNClique_iff]
  simp [isNIndepSet_iff]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} :
    Decidable (G.IsNIndepSet n s) :=
  decidable_of_iff' _ (G.isNIndepSet_iff n s)

set_option backward.isDefEq.respectTransparency false in
/-- The embedding of an `n`-independent set of an induced subgraph of the subgraph `G` is an
`n`-independent set in `G` and vice versa. -/
/-
**SimpleGraph.isNIndepSet_induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isNIndepSet_induce {F : Set α} {s : Finset { x // x in F }} {n : Nat} : ((
⊤ : Subgraph G).induce F).coe.IsNIndepSet n ↑s ↔ G.IsNIndepSet n (Finset.map ⟨Su
btype.val, Subtype.val_injective⟩ s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.isIndepSet_induce`：isIndepSet_induce {F : Set α} {s : Set F}
 : ((⊤ : Subgraph G).induce F).coe.IsIndepSet s ↔ G.IsIndepSet (Subtype.val '' s
)
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The embedding of an `n`-independent set of an induced subgraph of the subgraph `
G` is an
`n`-independent set in `G` and vice versa.
-/
theorem isNIndepSet_induce {F : Set α} {s : Finset { x // x ∈ F }} {n : ℕ} :
    ((⊤ : Subgraph G).induce F).coe.IsNIndepSet n ↑s ↔
    G.IsNIndepSet n (Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s) := by
  simp [isNIndepSet_iff, (isIndepSet_induce)]

end NIndepSet

/-! ### Graphs without independent sets -/


section IndepSetFree

variable {n : ℕ}

/-- `G.IndepSetFree n` means that `G` has no `n`-independent sets. -/
/-
**SimpleGraph.IndepSetFree** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IndepSetFree (n : Nat) : Prop
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.IndepSetFree n` means that `G` has no `n`-independent sets.
-/
def IndepSetFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNIndepSet n t

/-- A graph is `n`-independent set free iff its complement is `n`-clique free. -/
/-
**SimpleGraph.cliqueFree_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} (G : SimpleGraph α) {n : ℕ}, Gᶜ.CliqueFree n ↔ G.IndepSet
Free n
参数：G : SimpleGraph α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A graph is `n`-independent set free iff its complement is `n`-clique free.
-/
@[simp] theorem cliqueFree_compl : Gᶜ.CliqueFree n ↔ G.IndepSetFree n := by
  simp [IndepSetFree, CliqueFree]

/-- A graph's complement is `n`-independent set free iff it is `n`-clique free. -/
/-
**SimpleGraph.indepSetFree_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_1} (G : SimpleGraph α) {n : ℕ}, Gᶜ.IndepSetFree n ↔ G.Clique
Free n
参数：G : SimpleGraph α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A graph's complement is `n`-independent set free iff it is `n`-clique free.
-/
@[simp] theorem indepSetFree_compl : Gᶜ.IndepSetFree n ↔ G.CliqueFree n := by
  simp [IndepSetFree, CliqueFree]

/-- `G.IndepSetFreeOn s n` means that `G` has no `n`-independent sets contained in `s`. -/
/-
**SimpleGraph.IndepSetFreeOn** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IndepSetFreeOn (G : SimpleGraph α) (s : Set α) (n : Nat) : Prop
参数：G : SimpleGraph α；s : Set α；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.IndepSetFreeOn s n` means that `G` has no `n`-independent sets contained in `
s`.
-/
def IndepSetFreeOn (G : SimpleGraph α) (s : Set α) (n : ℕ) : Prop :=
  ∀ ⦃t⦄, ↑t ⊆ s → ¬G.IsNIndepSet n t

end IndepSetFree

/-! ### Set of independent sets -/


section IndepSetSet

variable {n : ℕ} {s : Finset α}

/-- The `n`-independent sets in a graph as a set. -/
/-
**SimpleGraph.indepSetSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：indepSetSet (n : Nat) : Set (Finset α)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-independent sets in a graph as a set.
-/
def indepSetSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNIndepSet n s }

variable {G}

@[simp]
/-
**SimpleGraph.mem_indepSetSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_indepSetSet_iff : s in G.indepSetSet n ↔ G.IsNIndepSet n s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_indepSetSet_iff : s ∈ G.indepSetSet n ↔ G.IsNIndepSet n s :=
  Iff.rfl

end IndepSetSet

/-! ### Independence Number -/


section IndepNumber

variable {α : Type*} {G : SimpleGraph α}

/-- The maximal number of vertices of an independent set in a graph `G`. -/
/-
**SimpleGraph.indepNum** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：indepNum (G : SimpleGraph α) : Nat
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal number of vertices of an independent set in a graph `G`.
-/
noncomputable def indepNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNIndepSet n s}
/-
**SimpleGraph.cliqueNum_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_3} {G : SimpleGraph α}, Gᶜ.cliqueNum = G.indepNum
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma cliqueNum_compl : Gᶜ.cliqueNum = G.indepNum := by
  simp [indepNum, cliqueNum]
/-
**SimpleGraph.indepNum_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_3} {G : SimpleGraph α}, Gᶜ.indepNum = G.cliqueNum
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma indepNum_compl : Gᶜ.indepNum = G.cliqueNum := by
  simp [indepNum, cliqueNum]
/-
**SimpleGraph.IsIndepSet.card_le_indepNum** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.IsIndepSet`。
形式化陈述：∀ {α : Type u_3} {G : SimpleGraph α} [Finite α] {t : Finset α}, G.IsIndepS
et ↑t → t.card ≤ G.indepNum
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.IsClique.card_le_cliqueNum`：∀ {α : Type u_3} {G : SimpleGrap
h α} [Finite α] {t : Finset α} {tc : G.IsClique ↑t}, t.card ≤ G.cliqueNum
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.isClique_compl`：∀ {α : Type u_1} (G : SimpleGraph α) {s : Se
t α}, Gᶜ.IsClique s ↔ G.IsIndepSet s
-/
theorem IsIndepSet.card_le_indepNum
    [Finite α] {t : Finset α} (tc : G.IsIndepSet t) : #t ≤ G.indepNum := by
  rw [← isClique_compl] at tc
  simp_rw [indepNum, ← isNClique_compl]
  exact tc.card_le_cliqueNum
/-
**SimpleGraph.exists_isNIndepSet_indepNum** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：exists_isNIndepSet_indepNum : exists s, G.IsNIndepSet G.indepNum s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SimpleGraph.exists_isNClique_cliqueNum`：exists_isNClique_cliqueNum : exi
sts s, G.IsNClique G.cliqueNum s
-/
lemma exists_isNIndepSet_indepNum : ∃ s, G.IsNIndepSet G.indepNum s := by
  simp_rw [indepNum, ← isNClique_compl]
  exact exists_isNClique_cliqueNum

/-- An independent set in a graph `G` such that there is no independent set with more vertices. -/
-- TODO: replace with `MaximalFor (G.IsIndepSet ∘ (↑)) card s`
@[mk_iff]
/-
**SimpleGraph.IsMaximumIndepSet** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{α : Type u_3} → [Finite α] → SimpleGraph α → Finset α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure IsMaximumIndepSet [Finite α] (G : SimpleGraph α) (s : Finset α) : Prop where
  isIndepSet : G.IsIndepSet s
  maximum : ∀ t : Finset α, G.IsIndepSet t → #t ≤ #s
/-
**SimpleGraph.isMaximumClique_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_3} {G : SimpleGraph α} [inst : Finite α] (s : Finset α), Gᶜ.
IsMaximumClique s ↔ G.IsMaximumIndepSet s
参数：s : Finset α。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isMaximumClique_compl [Finite α] (s : Finset α) :
    Gᶜ.IsMaximumClique s ↔ G.IsMaximumIndepSet s := by
  simp [isMaximumIndepSet_iff, isMaximumClique_iff]
/-
**SimpleGraph.isMaximumIndepSet_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_3} {G : SimpleGraph α} [inst : Finite α] (s : Finset α), Gᶜ.
IsMaximumIndepSet s ↔ G.IsMaximumClique s
参数：s : Finset α。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isMaximumIndepSet_compl [Finite α] (s : Finset α) :
    Gᶜ.IsMaximumIndepSet s ↔ G.IsMaximumClique s := by
  simp [isMaximumIndepSet_iff, isMaximumClique_iff]

/-- An independent set in a graph `G` that cannot be extended by adding more vertices. -/
/-
**SimpleGraph.isMaximalIndepSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isMaximalIndepSet_iff {s : Set α} : Maximal G.IsIndepSet s ↔ G.IsIndepSet 
s ∧ forall t : Set α, G.IsIndepSet t -> s subseteq t -> t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An independent set in a graph `G` that cannot be extended by adding more vertice
s.
-/
theorem isMaximalIndepSet_iff {s : Set α} :
    Maximal G.IsIndepSet s ↔ G.IsIndepSet s ∧ ∀ t : Set α, G.IsIndepSet t → s ⊆ t → t ⊆ s :=
  Iff.rfl
/-
**SimpleGraph.isMaximalClique_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_3} {G : SimpleGraph α} (s : Finset α), Maximal Gᶜ.IsClique ↑
s ↔ Maximal G.IsIndepSet ↑s
参数：s : Finset α。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isMaximalClique_compl (s : Finset α) :
    Maximal Gᶜ.IsClique s ↔ Maximal G.IsIndepSet s := by
  simp [isMaximalIndepSet_iff, isMaximalClique_iff]
/-
**SimpleGraph.isMaximalIndepSet_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {α : Type u_3} {G : SimpleGraph α} (s : Finset α), Maximal Gᶜ.IsIndepSet
 ↑s ↔ Maximal G.IsClique ↑s
参数：s : Finset α。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isMaximalIndepSet_compl (s : Finset α) :
    Maximal Gᶜ.IsIndepSet s ↔ Maximal G.IsClique s := by
  simp [isMaximalIndepSet_iff, isMaximalClique_iff]
/-
**SimpleGraph.IsMaximumIndepSet.isMaximalIndepSet** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.IsMaximumIndepSet`。
形式化陈述：∀ {α : Type u_3} {G : SimpleGraph α} [inst : Finite α] (s : Finset α), G.I
sMaximumIndepSet s → Maximal G.IsIndepSet ↑s
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.isMaximalClique_compl`：∀ {α : Type u_3} {G : SimpleGraph α} 
(s : Finset α), Maximal Gᶜ.IsClique ↑s ↔ Maximal G.IsIndepSet ↑s
· 使用定理 `SimpleGraph.IsMaximumClique.isMaximalClique`：∀ {α : Type u_3} {G : Simpl
eGraph α} [inst : Finite α] (s : Finset α), G.IsMaximumClique s → Maximal G.IsCl
ique ↑s
· 使用定理 `SimpleGraph.isMaximumClique_compl`：∀ {α : Type u_3} {G : SimpleGraph α} 
[inst : Finite α] (s : Finset α), Gᶜ.IsMaximumClique s ↔ G.IsMaximumIndepSet s
-/
lemma IsMaximumIndepSet.isMaximalIndepSet
    [Finite α] (s : Finset α) (M : G.IsMaximumIndepSet s) : Maximal G.IsIndepSet s := by
  rw [← isMaximalClique_compl]
  rw [← isMaximumClique_compl] at M
  exact IsMaximumClique.isMaximalClique s M
/-
**SimpleGraph.maximumIndepSet_card_eq_indepNum** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：maximumIndepSet_card_eq_indepNum [Finite α] (t : Finset α) (tmc : G.IsMaxi
mumIndepSet t) : #t = G.indepNum
参数：t : Finset α；tmc : G.IsMaximumIndepSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SimpleGraph.maximumClique_card_eq_cliqueNum`：maximumClique_card_eq_cliqu
eNum [Finite α] (s : Finset α) (sm : G.IsMaximumClique s) : #s = G.cliqueNum
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.isMaximumClique_compl`：∀ {α : Type u_3} {G : SimpleGraph α} 
[inst : Finite α] (s : Finset α), Gᶜ.IsMaximumClique s ↔ G.IsMaximumIndepSet s
-/
theorem maximumIndepSet_card_eq_indepNum
    [Finite α] (t : Finset α) (tmc : G.IsMaximumIndepSet t) : #t = G.indepNum := by
  rw [← isMaximumClique_compl] at tmc
  simp_rw [indepNum, ← isNClique_compl]
  exact Gᶜ.maximumClique_card_eq_cliqueNum t tmc
/-
**SimpleGraph.maximumIndepSet_exists** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：maximumIndepSet_exists [Finite α] : exists (s : Finset α), G.IsMaximumInde
pSet s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma maximumIndepSet_exists [Finite α] : ∃ (s : Finset α), G.IsMaximumIndepSet s := by
  simp [← isMaximumClique_compl, maximumClique_exists]

end IndepNumber

/-! ### Finset of independent sets -/


section IndepSetFinset

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α}

/-- The `n`-independent sets in a graph as a finset. -/
/-
**SimpleGraph.indepSetFinset** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：indepSetFinset (n : Nat) : Finset (Finset α)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-independent sets in a graph as a finset.
-/
def indepSetFinset (n : ℕ) : Finset (Finset α) := {s | G.IsNIndepSet n s}

variable {G} in
@[simp]
/-
**SimpleGraph.mem_indepSetFinset_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：mem_indepSetFinset_iff : s in G.indepSetFinset n ↔ G.IsNIndepSet n s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem mem_indepSetFinset_iff : s ∈ G.indepSetFinset n ↔ G.IsNIndepSet n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _

end IndepSetFinset

end SimpleGraph

