/-
Copyright (c) 2025 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Hall's Marriage Theorem

This file derives Hall's Marriage Theorem for bipartite graphs from the combinatorial formulation in
`Mathlib/Combinatorics/Hall/Basic.lean`.

## Main statements

* `exists_isMatching_of_forall_ncard_le`: Hall's marriage theorem for a matching on a single
  partition of a bipartite graph.
* `exists_isPerfectMatching_of_forall_ncard_le`: Hall's marriage theorem for a perfect matching on a
  bipartite graph.

## Tags

Hall's Marriage Theorem
-/

public section

open Function

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Given a partition `p` and a function `f` mapping vertices in `p` to the other partition, create
the subgraph including only the edges between `x` and `f x` for all `x` in `p`. -/
private
/-
**SimpleGraph.hall_subgraph** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：hall_subgraph {p : Set V} [DecidablePred (· in p)] (f : p -> V) (h₁ : fora
ll x : p, f x ∉ p) (h₂ : forall x : p, G.Adj x (f x)) : Subgraph G where verts
参数：· in p；f : p -> V；h₁ : forall x : p, f x ∉ p；h₂ : forall x : p, G.Adj x (f x)
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev hall_subgraph {p : Set V} [DecidablePred (· ∈ p)] (f : p → V) (h₁ : ∀ x : p, f x ∉ p)
    (h₂ : ∀ x : p, G.Adj x (f x)) : Subgraph G where
  verts := p ∪ Set.range f
  Adj v w :=
    if h : v ∈ p then f ⟨v, h⟩ = w
    else if h : w ∈ p then f ⟨w, h⟩ = v
    else False
  adj_sub {v w} h := by
    split_ifs at h
    · exact h ▸ h₂ ⟨v, by assumption⟩
    · exact h ▸ h₂ ⟨w, by assumption⟩ |>.symm
  edge_vert := by grind
  symm.symm := by grind

variable [G.LocallyFinite] {p₁ p₂ : Set V}

/-- This is the version of **Hall's marriage theorem** for bipartite graphs that finds a matching
for a single partition given that the neighborhood-condition only holds for elements of that
partition. -/
/-
**SimpleGraph.exists_isMatching_of_forall_ncard_le** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：exists_isMatching_of_forall_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂) (h₂ : 
forall s subseteq p₁, s.ncard <= (⋃ x in s, G.neighborSet x).ncard) : exists M :
 Subgraph G, p₁ subseteq M.verts ∧ M.IsMatching
参数：h₁ : G.IsBipartiteWith p₁ p₂；h₂ : forall s subseteq p₁, s.ncard <= (⋃ x in s,
 G.neighborSet x).ncard。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.all_card_le_biUnion_card_iff_exists_injective`：Finset.all_card_le
_biUnion_card_iff_exists_injective {ι : Type u} {α : Type v} [DecidableEq α] (t 
: ι -> Finset α) : (forall s : Finset ι, #…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Set.ncard_coe_finset`：∀ {α : Type u_1} (s : Finset α), (↑s).ncard = s.ca
rd
· 使用定理 `Disjoint.notMem_of_mem_right`：∀ {α : Type u} {s t : Set α}, Disjoint s t
 → ∀ ⦃a : α⦄, a ∈ t → a ∉ s
· 使用定理 `SimpleGraph.IsBipartiteWith.disjoint`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V}, G.IsBipartiteWith s t → Disjoint s t
· 使用定理 `SimpleGraph.isBipartiteWith_neighborSet_subset`：isBipartiteWith_neighbor
Set_subset (h : G.IsBipartiteWith s t) (hv : v in s) : G.neighborSet v subseteq 
t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `SimpleGraph.mem_neighborFinset`：mem_neighborFinset (w : V) : w in G.neig
hborFinset v ↔ G.Adj v w
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
This is the version of **Hall's marriage theorem** for bipartite graphs that fin
ds a matching
for a single partition given that the neighborhood-condition only holds for elem
ents of that
partition.
-/
theorem exists_isMatching_of_forall_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : Subgraph G, p₁ ⊆ M.verts ∧ M.IsMatching := by
  classical
  obtain ⟨f, hf₁, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun (x : p₁) ↦ G.neighborFinset x) |>.mp fun s ↦ by
    have := h₂ (s.image Subtype.val) (by simp)
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ Subtype.val_injective] at this
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
  have (x : p₁) : f x ∉ p₁ := h₁.disjoint |>.notMem_of_mem_right <|
    isBipartiteWith_neighborSet_subset h₁ x.2 <| Set.mem_toFinset.mp <| hf₂ x
  use hall_subgraph f this (fun v ↦ G.mem_neighborFinset _ _ |>.mp <| hf₂ v)
  refine ⟨by simp, fun v hv ↦ ?_⟩
  simp only [Set.mem_union, Set.mem_range, Subtype.exists] at hv ⊢
  rcases hv with h' | ⟨x, hx₁, hx₂⟩
  · exact ⟨f ⟨v, h'⟩, by simp_all⟩
  · use x
    have := hx₂ ▸ this ⟨x, hx₁⟩
    simp only [this, ↓reduceDIte, hx₁, hx₂, dite_else_false, forall_exists_index, true_and]
    exact fun _ _ k ↦ Subtype.ext_iff.mp <| hf₁ (hx₂ ▸ k)
/-
**SimpleGraph.union_eq_univ_of_forall_ncard_le** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph`。
形式化陈述：union_eq_univ_of_forall_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂) (h₂ : fora
ll s : Set V, s.ncard <= (⋃ x in s, G.neighborSet x).ncard) : p₁ union p₂ = Set.
univ
参数：h₁ : G.IsBipartiteWith p₁ p₂；h₂ : forall s : Set V, s.ncard <= (⋃ x in s, G.n
eighborSet x).ncard。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.all_card_le_biUnion_card_iff_exists_injective`：Finset.all_card_le
_biUnion_card_iff_exists_injective {ι : Type u} {α : Type v} [DecidableEq α] (t 
: ι -> Finset α) : (forall s : Finset ι, #…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `SimpleGraph.IsBipartiteWith.mem_of_adj`：∀ {V : Type u_1} {G : SimpleGrap
h V} {s t : Set V},   G.IsBipartiteWith s t → ∀ ⦃v w : V⦄, G.Adj v w → v ∈ s ∧ w
 ∈ t ∨ v ∈ t ∧ w ∈ s
· 使用定理 `SimpleGraph.mem_neighborFinset`：mem_neighborFinset (w : V) : w in G.neig
hborFinset v ↔ G.Adj v w
-/
lemma union_eq_univ_of_forall_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) : p₁ ∪ p₂ = Set.univ := by
  classical
  obtain ⟨f, _, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun x ↦ G.neighborFinset x) |>.mp fun s ↦ by
    have := h₂ s
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
  refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
  have := h₁.mem_of_adj <| G.mem_neighborFinset _ _ |>.mp (hf₂ x)
  grind
/-
**SimpleGraph.exists_bijective_of_forall_ncard_le** 是 Mathlib 中的一个引理，位于命名空间 `Sim
pleGraph`。
形式化陈述：exists_bijective_of_forall_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂) (h₂ : f
orall s : Set V, s.ncard <= (⋃ x in s, G.neighborSet x).ncard) : exists (h : p₁ 
-> p₂), Function.Bijective h ∧ forall (a : p₁), G.Adj a (h a)
参数：h₁ : G.IsBipartiteWith p₁ p₂；h₂ : forall s : Set V, s.ncard <= (⋃ x in s, G.n
eighborSet x).ncard。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.all_card_le_biUnion_card_iff_exists_injective`：Finset.all_card_le
_biUnion_card_iff_exists_injective {ι : Type u} {α : Type v} [DecidableEq α] (t 
: ι -> Finset α) : (forall s : Finset ι, #…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Disjoint.notMem_of_mem_right`：∀ {α : Type u} {s t : Set α}, Disjoint s t
 → ∀ ⦃a : α⦄, a ∈ t → a ∉ s
· 使用定理 `SimpleGraph.IsBipartiteWith.disjoint`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V}, G.IsBipartiteWith s t → Disjoint s t
· 使用定理 `SimpleGraph.isBipartiteWith_neighborSet_subset`：isBipartiteWith_neighbor
Set_subset (h : G.IsBipartiteWith s t) (hv : v in s) : G.neighborSet v subseteq 
t
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `Disjoint.notMem_of_mem_left`：∀ {α : Type u} {s t : Set α}, Disjoint s t 
→ ∀ ⦃a : α⦄, a ∈ s → a ∉ t
· 使用定理 `SimpleGraph.IsBipartiteWith.symm`：∀ {V : Type u_1} {G : SimpleGraph V} {
s t : Set V}, G.IsBipartiteWith s t → G.IsBipartiteWith t s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SimpleGraph.union_eq_univ_of_forall_ncard_le`：union_eq_univ_of_forall_nc
ard_le (h₁ : G.IsBipartiteWith p₁ p₂) (h₂ : forall s : Set V, s.ncard <= (⋃ x in
 s, G.neighborSet x).ncard) : p₁ u…
· 使用定理 `Function.Embedding.schroeder_bernstein_of_rel`：schroeder_bernstein_of_re
l {f : α -> β} {g : β -> α} (hf : Function.Injective f) (hg : Function.Injective
 g) (R : α -> β -> Prop) (hp₁ : for…
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `SimpleGraph.mem_neighborFinset`：mem_neighborFinset (w : V) : w in G.neig
hborFinset v ↔ G.Adj v w
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
lemma exists_bijective_of_forall_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ (h : p₁ → p₂), Function.Bijective h ∧ ∀ (a : p₁), G.Adj a (h a) := by
  classical
  obtain ⟨f, hf₁, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun x ↦ G.neighborFinset x) |>.mp fun s ↦ by
    have := h₂ s
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
  have (x : V) (h : x ∈ p₁) : f x ∉ p₁ := h₁.disjoint |>.notMem_of_mem_right <|
    isBipartiteWith_neighborSet_subset h₁ h <| Set.mem_toFinset.mp <| hf₂ x
  have (x : V) (h : x ∈ p₂) : f x ∉ p₂ := h₁.disjoint |>.notMem_of_mem_left <|
    isBipartiteWith_neighborSet_subset h₁.symm h <| Set.mem_toFinset.mp <| hf₂ x
  have (x : V) : f x ∈ p₁ ∨ f x ∈ p₂ := by
    simp [union_eq_univ_of_forall_ncard_le h₁ h₂, p₁.mem_union (f x) p₂ |>.mp]
  let f' (x : p₁) : p₂ := ⟨f x, by grind⟩
  let g' (x : p₂) : p₁ := ⟨f x, by grind⟩
  refine Embedding.schroeder_bernstein_of_rel (f := f') (g := g') ?_ ?_ (fun x y ↦ G.Adj x y) ?_ ?_
  · exact Injective.of_comp (f := Subtype.val) <| hf₁.comp Subtype.val_injective
  · exact Injective.of_comp (f := Subtype.val) <| hf₁.comp Subtype.val_injective
  · exact fun v ↦ mem_neighborFinset _ _ _ |>.mp (hf₂ v)
  · exact fun v ↦ mem_neighborFinset _ _ _ |>.mp (hf₂ v) |>.symm

/-- This is the version of **Hall's marriage theorem** for bipartite graphs that finds a perfect
matching given that the neighborhood-condition holds globally. -/
/-
**SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph`。
形式化陈述：exists_isPerfectMatching_of_forall_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂)
 (h₂ : forall s : Set V, s.ncard <= (⋃ x in s, G.neighborSet x).ncard) : exists 
M : Subgraph G, M.IsPerfectMatching
参数：h₁ : G.IsBipartiteWith p₁ p₂；h₂ : forall s : Set V, s.ncard <= (⋃ x in s, G.n
eighborSet x).ncard。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_bijective_of_forall_ncard_le`：exists_bijective_of_for
all_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂) (h₂ : forall s : Set V, s.ncard <= (
⋃ x in s, G.neighborSet x).ncard) : e…
· 使用定理 `Disjoint.notMem_of_mem_right`：∀ {α : Type u} {s t : Set α}, Disjoint s t
 → ∀ ⦃a : α⦄, a ∈ t → a ∉ s
· 使用定理 `SimpleGraph.IsBipartiteWith.disjoint`：∀ {V : Type u_1} {G : SimpleGraph 
V} {s t : Set V}, G.IsBipartiteWith s t → Disjoint s t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Subtype.coe_image_univ`：coe_image_univ (s : Set α) : ((↑) : s -> α) '' S
et.univ = s
· 使用引理 `SimpleGraph.union_eq_univ_of_forall_ncard_le`：union_eq_univ_of_forall_nc
ard_le (h₁ : G.IsBipartiteWith p₁ p₂) (h₂ : forall s : Set V, s.ncard <= (⋃ x in
 s, G.neighborSet x).ncard) : p₁ u…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Function.Bijective.existsUnique`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Bijective f → ∀ (b : β), ∃! a, f a = b
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `existsUnique_eq'`：∀ {α : Sort u_1} {a' : α}, ∃! a, a' = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Subgraph.isSpanning_iff`：isSpanning_iff {G' : Subgraph G} : 
G'.IsSpanning ↔ G'.verts = Set.univ

--- 原说明 ---
This is the version of **Hall's marriage theorem** for bipartite graphs that fin
ds a perfect
matching given that the neighborhood-condition holds globally.
-/
theorem exists_isPerfectMatching_of_forall_ncard_le
    (h₁ : G.IsBipartiteWith p₁ p₂) (h₂ : ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : Subgraph G, M.IsPerfectMatching := by
  classical
  obtain ⟨b, hb₁, hb₂⟩ := exists_bijective_of_forall_ncard_le h₁ h₂
  use hall_subgraph (fun v ↦ b v) (fun v ↦ h₁.disjoint.notMem_of_mem_right (b v).property) hb₂
  have : p₁ ∪ Set.range (fun v ↦ (b v).1) = Set.univ := by
    rw [Set.range_comp', hb₁.surjective.range_eq, Subtype.coe_image_univ]
    exact union_eq_univ_of_forall_ncard_le h₁ h₂
  refine ⟨fun v _ ↦ ?_, Subgraph.isSpanning_iff.mpr this⟩
  simp only [dite_else_false]
  split
  · exact existsUnique_eq'
  · obtain ⟨x, _⟩ := hb₁.existsUnique ⟨v, by grind⟩
    exact ⟨x, by grind⟩

end SimpleGraph

