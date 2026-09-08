/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Combinatorics.SimpleGraph.UniversalVerts
public import Mathlib.Data.Fintype.Card

/-!
# Tutte's theorem

## Main definitions

* `SimpleGraph.IsTutteViolator G u` is a set of vertices `u` such that the amount of
  odd components left after deleting `u` from `G` is larger than the number of vertices in `u`.
  This certifies non-existence of a perfect matching.

## Main results

* `SimpleGraph.tutte` states Tutte's theorem: A graph has a perfect matching, if and
  only if no Tutte violators exist.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G G' : SimpleGraph V} {u x v' w : V}

/-- A set certifying non-existence of a perfect matching -/
/-
**SimpleGraph.IsTutteViolator** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsTutteViolator (G : SimpleGraph V) (u : Set V) : Prop
参数：G : SimpleGraph V；u : Set V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set certifying non-existence of a perfect matching
-/
def IsTutteViolator (G : SimpleGraph V) (u : Set V) : Prop :=
  u.ncard < ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents.ncard

/-- This lemma shows an alternating cycle exists in a specific subcase of the proof
of Tutte's theorem. -/
/-
**SimpleGraph.tutte_exists_isAlternating_isCycles** 是 Mathlib 中的一个引理，位于命名空间 `Sim
pleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma shows an alternating cycle exists in a specific subcase of the proof
of Tutte's theorem.
-/
private lemma tutte_exists_isAlternating_isCycles {x b a c : V} {M : Subgraph (G ⊔ edge a c)}
    (p : G'.Walk a x) (hp : p.IsPath) (hcalt : G'.IsAlternating M.spanningCoe)
    (hM2nadj : ¬M.Adj x a) (hpac : p.toSubgraph.Adj a c) (hnpxb : ¬p.toSubgraph.Adj x b)
    (hM2ac : M.Adj a c) (hgadj : G.Adj x a) (hnxc : x ≠ c) (hnab : a ≠ b)
    (hle : p.toSubgraph.spanningCoe ≤ G ⊔ edge a c)
    (aux : (c' : V) → c' ≠ a → p.toSubgraph.Adj c' x → M.Adj c' x) :
    ∃ G', G'.IsAlternating M.spanningCoe ∧ G'.IsCycles ∧
      ¬ G'.Adj x b ∧ G'.Adj a c ∧ G' ≤ G ⊔ edge a c := by
  refine ⟨p.toSubgraph.spanningCoe ⊔ edge x a, (hcalt.spanningCoe p.toSubgraph).sup_edge (by simpa)
    (fun u' hu'x hadj ↦ ?_) aux, ?_, ?_, by aesop, sup_le_iff.mpr ⟨hle, fun v w hvw ↦ ?_⟩⟩
  · simpa [← hp.snd_of_toSubgraph_adj hadj, hp.snd_of_toSubgraph_adj hpac]
  · refine hp.isCycles_spanningCoe_toSubgraph_sup_edge hgadj.ne.symm fun hadj ↦ ?_
    rw [← Walk.mem_edges_toSubgraph, Subgraph.mem_edgeSet] at hadj
    simp [← hp.snd_of_toSubgraph_adj hadj.symm, hp.snd_of_toSubgraph_adj hpac] at hnxc
  · simp +contextual [hnpxb, edge_adj, hnab.symm]
  · simpa [edge_adj, adj_congr_of_sym2 _ ((adj_edge _ _).mp hvw).1.symm] using .inl hgadj

variable [Finite V]
/-
**SimpleGraph.IsTutteViolator.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsTutt
eViolator`。
形式化陈述：∀ {V : Type u_1} {G G' : SimpleGraph V} [Finite V] {u : Set V}, G ≤ G' → G
'.IsTutteViolator u → G.IsTutteViolator u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.ncard_oddComponents_mono`：ncard_oddComponents_mono [Finite V
] {G' : SimpleGraph V} (h : G <= G') : G'.oddComponents.ncard <= G.oddComponents
.ncard
· 使用引理 `SimpleGraph.Subgraph.deleteVerts_mono'`：deleteVerts_mono' {G' : SimpleGr
aph V} (u : Set V) (h : G <= G') : ((⊤ : Subgraph G).deleteVerts u).coe <= ((⊤ :
 Subgraph G').deleteVerts u)…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
lemma IsTutteViolator.mono {u : Set V} (h : G ≤ G') (ht : G'.IsTutteViolator u) :
    G.IsTutteViolator u := by
  simp only [IsTutteViolator] at *
  have := ncard_oddComponents_mono _ (Subgraph.deleteVerts_mono' (G := G) (G' := G') u h)
  simp only [oddComponents] at *
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `lia` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `lia` -/
  exact lt_of_lt_of_le ht this

/-- Given a graph in which the universal vertices do not violate Tutte's condition,
if the graph decomposes into cliques, there exists a matching that covers
everything except some universal vertices.

This lemma is marked private, because
it is strictly weaker than `IsPerfectMatching.exists_of_isClique_supp`. -/
/-
**SimpleGraph.Subgraph.IsMatching.exists_verts_compl_subset_universalVerts** 是 M
athlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a graph in which the universal vertices do not violate Tutte's condition,
if the graph decomposes into cliques, there exists a matching that covers
everything except some universal vertices.

This lemma is marked private, because
it is strictly weaker than `IsPerfectMatching.exists_of_isClique_supp`.
-/
private lemma Subgraph.IsMatching.exists_verts_compl_subset_universalVerts
    (h : ¬IsTutteViolator G G.universalVerts)
    (h' : ∀ (K : G.deleteUniversalVerts.coe.ConnectedComponent),
      G.deleteUniversalVerts.coe.IsClique K.supp) :
    ∃ M : Subgraph G, M.IsMatching ∧ M.vertsᶜ ⊆ G.universalVerts := by
  have hrep := ConnectedComponent.Represents.image_out G.deleteUniversalVerts.coe.oddComponents
  -- First we match one node from each odd component to a universal vertex
  obtain ⟨t, ht, M1, hM1⟩ := Subgraph.IsMatching.exists_of_universalVerts
      (disjoint_image_val_universalVerts _).symm (by
        simp only [IsTutteViolator, not_lt] at h
        rwa [Set.ncard_image_of_injective _ Subtype.val_injective, hrep.ncard_eq])
  -- Then we match all other nodes in components internally
  have exists_complMatch (K : G.deleteUniversalVerts.coe.ConnectedComponent) :
      ∃ M : Subgraph G, M.verts = Subtype.val '' K.supp \ M1.verts ∧ M.IsMatching := by
    have : G.IsClique (Subtype.val '' K.supp \ M1.verts) :=
      ((h' K).of_induce).subset Set.sdiff_subset
    rw [← this.even_iff_exists_isMatching (Set.toFinite _), hM1.1]
    exact even_ncard_image_val_supp_sdiff_image_val_rep_union _ ht hrep
  choose complMatch hcomplMatch_compl hcomplMatch_match using exists_complMatch
  let M2 : Subgraph G := ⨆ K, complMatch K
  have hM2 : M2.IsMatching := by
    refine .iSup hcomplMatch_match fun i j hij ↦ (?_ : Disjoint _ _)
    rw [(hcomplMatch_match i).support_eq_verts, hcomplMatch_compl i,
        (hcomplMatch_match j).support_eq_verts, hcomplMatch_compl j]
    exact Set.disjoint_of_subset Set.sdiff_subset Set.sdiff_subset <|
      Set.disjoint_image_of_injective Subtype.val_injective <|
        SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hij
  have disjointM12 : Disjoint M1.support M2.support := by
    rw [hM1.2.support_eq_verts, hM2.support_eq_verts, Subgraph.verts_iSup,
      Set.disjoint_iUnion_right]
    exact fun K ↦ hcomplMatch_compl K ▸ Set.disjoint_sdiff_right
  -- The only vertices left are indeed contained in universalVerts
  have : (M1.verts ∪ M2.verts)ᶜ ⊆ G.universalVerts := by
    rw [Set.compl_subset_comm, Set.compl_eq_univ_sdiff]
    intro v hv
    by_cases h : v ∈ M1.verts
    · exact M1.verts.mem_union_left _ h
    right
    simp only [Subgraph.verts_iSup, Set.mem_iUnion, M2,
      hcomplMatch_compl]
    use G.deleteUniversalVerts.coe.connectedComponentMk ⟨v, hv⟩
    aesop
  exact ⟨M1 ⊔ M2, hM1.2.sup hM2 disjointM12, this⟩

/-- If the universal vertices of a graph `G` decompose `G` into cliques such that the Tutte isn't
violated, then `G` has a perfect matching. -/
/-
**SimpleGraph.Subgraph.IsPerfectMatching.exists_of_isClique_supp** 是 Mathlib 中的一
个定理，位于命名空间 `SimpleGraph.Subgraph.IsPerfectMatching`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [Finite V],   Even (Nat.card V) →    
 ¬G.IsTutteViolator G.universalVerts →       (∀ (K : G.deleteUniversalVerts.coe.
ConnectedComponent), G.deleteUniversalVerts.coe.IsClique K.supp) →         ∃ M, 
M.IsPerfectMatching
参数：Nat.card V；∀ (K : G.deleteUniversalVerts.coe.ConnectedComponent), G.deleteUni
versalVerts.coe.IsClique K.supp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Tutte.0.SimpleGraph.Subgraph.
IsMatching.exists_verts_compl_subset_universalVerts`：∀ {V : Type u_1} {G : Simpl
eGraph V} [Finite V],   ¬G.IsTutteViolator G.universalVerts →     (∀ (K : G.dele
teUniversalVerts.coe.ConnectedCom…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.IsClique.even_iff_exists_isMatching`：∀ {V : Type u_1} {G : S
impleGraph V} {u : Set V},   G.IsClique u → u.Finite → (Even u.ncard ↔ ∃ M, M.ve
rts = u ∧ M.IsMatching)
· 使用定理 `SimpleGraph.IsClique.subset`：∀ {α : Type u_1} {G : SimpleGraph α} {s t :
 Set α}, t ⊆ s → G.IsClique s → G.IsClique t
· 使用引理 `SimpleGraph.isClique_universalVerts`：isClique_universalVerts (G : Simple
Graph V) : G.IsClique G.universalVerts
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用引理 `Set.even_ncard_compl_iff`：even_ncard_compl_iff [Finite α] (heven : Even 
(Nat.card α)) (s : Set α) : Even sᶜ.ncard ↔ Even s.ncard
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.IsMatching.even_card`：∀ {V : Type u_1} {G : SimpleG
raph V} {M : G.Subgraph} [inst : Fintype ↑M.verts],   M.IsMatching → Even M.vert
s.toFinset.card
· 使用定理 `SimpleGraph.Subgraph.IsMatching.sup`：∀ {V : Type u_1} {G : SimpleGraph V
} {M M' : G.Subgraph},   M.IsMatching → M'.IsMatching → Disjoint M.support M'.su
pport → (M ⊔ M').IsMatchi…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Subgraph.IsMatching.support_eq_verts`：∀ {V : Type u_1} {G : 
SimpleGraph V} {M : G.Subgraph}, M.IsMatching → M.support = M.verts
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.Subgraph.isSpanning_iff`：isSpanning_iff {G' : Subgraph G} : 
G'.IsSpanning ↔ G'.verts = Set.univ
· 使用定理 `SimpleGraph.Subgraph.verts_sup`：verts_sup (G₁ G₂ : G.Subgraph) : (G₁ ⊔ G
₂).verts = G₁.verts union G₂.verts
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ

--- 原说明 ---
If the universal vertices of a graph `G` decompose `G` into cliques such that th
e Tutte isn't
violated, then `G` has a perfect matching.
-/
theorem Subgraph.IsPerfectMatching.exists_of_isClique_supp
    (hveven : Even (Nat.card V)) (h : ¬G.IsTutteViolator G.universalVerts)
    (h' : ∀ (K : G.deleteUniversalVerts.coe.ConnectedComponent),
      G.deleteUniversalVerts.coe.IsClique K.supp) :
    ∃ (M : Subgraph G), M.IsPerfectMatching := by
  classical
  cases nonempty_fintype V
  obtain ⟨M, hM, hsub⟩ := IsMatching.exists_verts_compl_subset_universalVerts h h'
  obtain ⟨M', hM'⟩ := ((G.isClique_universalVerts.subset hsub).even_iff_exists_isMatching
    (Set.toFinite _)).mp (by simpa [Set.even_ncard_compl_iff hveven, -Set.toFinset_card,
      ← Set.ncard_eq_toFinset_card'] using hM.even_card)
  refine ⟨M ⊔ M', hM.sup hM'.2 ?_, ?_⟩
  · simp [hM.support_eq_verts, hM'.2.support_eq_verts, hM'.1, disjoint_compl_right]
  · rw [Subgraph.isSpanning_iff, Subgraph.verts_sup, hM'.1]
    exact M.verts.union_compl_self
/-
**SimpleGraph.IsTutteViolator.empty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsTut
teViolator`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [Finite V], Odd (Nat.card V) → G.IsTu
tteViolator ∅
参数：Nat.card V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.IsTutteViolator.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (
u : Set V),   G.IsTutteViolator u = (u.ncard < (⊤.deleteVerts u).coe.oddComponen
ts.ncard)
· 使用定理 `Set.ncard_empty`：∀ (α : Type u_3), ∅.ncard = 0
· 使用引理 `Odd.pos`：Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
 [Nontrivial R] {a : R} : Odd a -> 0 < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.odd_ncard_oddComponents`：odd_ncard_oddComponents [Finite V] 
: Odd G.oddComponents.ncard ↔ Odd (Nat.card V)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Subgraph.deleteVerts_empty`：deleteVerts_empty : G'.deleteVer
ts ∅ = G'
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
-/
theorem IsTutteViolator.empty (hodd : Odd (Nat.card V)) : G.IsTutteViolator ∅ := by
  rw [IsTutteViolator, Set.ncard_empty]
  exact ((odd_ncard_oddComponents _).mpr <| by simpa using hodd).pos

/-- Proves the necessity part of Tutte's theorem -/
/-
**SimpleGraph.not_isTutteViolator_of_isPerfectMatching** 是 Mathlib 中的一个引理，位于命名空间
 `SimpleGraph`。
形式化陈述：not_isTutteViolator_of_isPerfectMatching {M : Subgraph G} (hM : M.IsPerfec
tMatching) (u : Set V) : ¬G.IsTutteViolator u
参数：hM : M.IsPerfectMatching；u : Set V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `SimpleGraph.Subgraph.IsMatching.eq_of_adj_right`：∀ {V : Type u_1} {G : S
impleGraph V} {M : G.Subgraph} {u v w : V}, M.IsMatching → M.Adj u w → M.Adj v w
 → u = v
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.ConnectedComponent.eq_of_common_vertex`：eq_of_common_vertex 
{v : V} {c c' : ConnectedComponent G} (hc : v in c.supp) (hc' : v in c'.supp) : 
c = c'
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `SimpleGraph.ConnectedComponent.odd_matches_node_outside`：odd_matches_nod
e_outside [Finite V] {u : Set V} (hM : M.IsPerfectMatching) (c : (Subgraph.delet
eVerts ⊤ u).coe.oddComponents) : existsᵉ (w i…

--- 原说明 ---
Proves the necessity part of Tutte's theorem
-/
lemma not_isTutteViolator_of_isPerfectMatching {M : Subgraph G} (hM : M.IsPerfectMatching)
    (u : Set V) :
    ¬G.IsTutteViolator u := by
  choose f hf g hgf hg using ConnectedComponent.odd_matches_node_outside hM (u := u)
  have hfinj : f.Injective := fun c d hcd ↦ by
    replace hcd : g c = g d := Subtype.val_injective <| hM.1.eq_of_adj_right (hgf c) (hcd ▸ hgf d)
    exact Subtype.val_injective <| ConnectedComponent.eq_of_common_vertex (hg c) (hcd ▸ hg d)
  simpa [IsTutteViolator] using!
    Nat.card_le_card_of_injective (fun c ↦ ⟨f c, hf c⟩) (fun c d ↦ by simp [hfinj.eq_iff])

open scoped symmDiff

/-- This lemma constructs a perfect matching on `G` from two near-matchings. -/
/-
**SimpleGraph.tutte_exists_isPerfectMatching_of_near_matchings** 是 Mathlib 中的一个定
理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma constructs a perfect matching on `G` from two near-matchings.
-/
private theorem tutte_exists_isPerfectMatching_of_near_matchings {x a b c : V}
    {M1 : Subgraph (G ⊔ edge x b)} {M2 : Subgraph (G ⊔ edge a c)} (hxa : G.Adj x a)
    (hab : G.Adj a b) (hnGxb : ¬G.Adj x b) (hnGac : ¬G.Adj a c) (hnxb : x ≠ b) (hnxc : x ≠ c)
    (hnac : a ≠ c) (hnbc : b ≠ c) (hM1 : M1.IsPerfectMatching) (hM2 : M2.IsPerfectMatching) :
    ∃ (M : Subgraph G), M.IsPerfectMatching := by
  classical
  -- If either matching does not contain their extra edge, we just use it as a perfect matching
  by_cases hM1xb : ¬M1.Adj x b
  · use G.toSubgraph M1.spanningCoe (M1.spanningCoe_sup_edge_le _ hM1xb)
    exact (Subgraph.IsPerfectMatching.toSubgraph_iff (M1.spanningCoe_sup_edge_le _ hM1xb)).mpr hM1
  by_cases hM2ac : ¬M2.Adj a c
  · use G.toSubgraph M2.spanningCoe (M2.spanningCoe_sup_edge_le _ hM2ac)
    exact (Subgraph.IsPerfectMatching.toSubgraph_iff (M2.spanningCoe_sup_edge_le _ hM2ac)).mpr hM2
  simp only [not_not] at hM1xb hM2ac
  -- Neither matching contains the edge that would make the other matching of G perfect
  have hM1nac : ¬M1.Adj a c := fun h ↦ by simpa [hnGac, edge_adj, hnac, hxa.ne, hnbc.symm, hab.ne]
    using h.adj_sub
  have hsupG : G ⊔ edge x b ⊔ (G ⊔ edge a c) = (G ⊔ edge a c) ⊔ edge x b := by grind
  -- We state conditions for our cycle that hold in all cases and show that this suffices
  suffices ∃ (G' : SimpleGraph V), G'.IsAlternating M2.spanningCoe ∧ G'.IsCycles ∧ ¬G'.Adj x b ∧
      G'.Adj a c ∧ G' ≤ G ⊔ edge a c by
    obtain ⟨G', hG', hG'cyc, hG'xb, hnG'ac, hle⟩ := this
    have : M2.spanningCoe ∆ G' ≤ G := by
      apply Disjoint.left_le_of_le_sup_right (symmDiff_le (le_sup_of_le_right M2.spanningCoe_le)
        (le_sup_of_le_right hle))
      simp [disjoint_edge, symmDiff_def, hM2ac, hnG'ac]
    use (G.toSubgraph (symmDiff M2.spanningCoe G') this)
    apply hM2.symmDiff_of_isAlternating hG' hG'cyc
  -- We consider the symmetric difference of the two matchings
  let cycles := M1.spanningCoe ∆ M2.spanningCoe
  have hcalt : cycles.IsAlternating M2.spanningCoe := hM1.isAlternating_symmDiff_right hM2
  have hcycles := Subgraph.IsPerfectMatching.symmDiff_isCycles hM1 hM2
  have hcac : cycles.Adj a c := by simp [cycles, symmDiff_def, hM2ac, hM1nac]
  have hM1sub := Subgraph.spanningCoe_le M1
  have hM2sub := Subgraph.spanningCoe_le M2
  -- We consider the cycle that contains the vertex `c`
  have induce_le : ((cycles.connectedComponentMk c).toSimpleGraph).spanningCoe ≤
      (G ⊔ edge a c) ⊔ edge x b := by
    refine le_trans (spanningCoe_induce_le cycles (cycles.connectedComponentMk c).supp) ?_
    simp only [← hsupG, cycles]
    exact le_trans (by apply symmDiff_le_sup) (sup_le_sup hM1sub hM2sub)
  -- If that cycle does not contain the vertex `x`, we use it as an alternating cycle
  by_cases! hxc : x ∉ (cycles.connectedComponentMk c).supp
  · use (cycles.connectedComponentMk c).toSimpleGraph.spanningCoe
    refine ⟨hcalt.mono (spanningCoe_induce_le cycles (cycles.connectedComponentMk c).supp), ?_⟩
    simp only [ConnectedComponent.adj_spanningCoe_toSimpleGraph, hxc, hcac, false_and,
      not_false_eq_true, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, and_true,
      true_and, hcac.reachable]
    refine ⟨hcycles.toSimpleGraph (cycles.connectedComponentMk c),
      Disjoint.left_le_of_le_sup_right induce_le ?_⟩
    rw [disjoint_edge]
    rw [ConnectedComponent.adj_spanningCoe_toSimpleGraph]
    simp_all
  have hacc := ((cycles.connectedComponentMk c).mem_supp_congr_adj hcac.symm).mp rfl
  have (G : SimpleGraph V) : LocallyFinite G := fun _ ↦ Fintype.ofFinite _
  have hnM2 (x' : V) (h : x' ≠ c) : ¬ M2.Adj x' a := by
    rw [M2.adj_comm]
    exact hM2.1.not_adj_left_of_ne h.symm hM2ac
  -- Else we construct a path that contain the edge `a c`, but not the edge `x b`
  obtain ⟨x', hx', p, hp, hpac, hnpxb⟩ :
      ∃ x' ∈ ({x, b} : Finset V), ∃ (p : cycles.Walk a x'), p.IsPath ∧
        p.toSubgraph.Adj a c ∧ ¬p.toSubgraph.Adj x b := by
    obtain ⟨p, hp⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hacc
      ⟨_, hcac⟩
    obtain ⟨p', hp'⟩ := hp.1.exists_isCycle_snd_verts_eq (by
      rwa [hp.1.adj_toSubgraph_iff_of_isCycles hcycles (hp.2 ▸ hacc)])
    obtain ⟨x', hx', hx'p, htw⟩ := Walk.exists_mem_support_forall_mem_support_imp_eq {x, b} <| by
      use x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, true_or, true_and]
      rwa [← @Walk.mem_verts_toSubgraph, hp'.2.2, hp.2]
    refine ⟨x', hx', p'.takeUntil x' hx'p, hp'.1.isPath_takeUntil hx'p, ?_, fun h ↦ ?_⟩; swap
    · simp [htw _ (by simp) (Walk.mem_support_of_adj_toSubgraph h.symm),
        htw _ (by simp) (Walk.mem_support_of_adj_toSubgraph h)] at hnxb
    have : (p'.takeUntil x' hx'p).toSubgraph.Adj a (p'.takeUntil x' hx'p).snd := by
      apply Walk.toSubgraph_adj_snd
      rw [Walk.nil_takeUntil]
      grind
    rwa [Walk.snd_takeUntil, hp'.2.1] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    obtain rfl | rfl := hx'
    exacts [hxa.ne, hab.ne.symm]
  -- We show this path satisfies all requirements
  have hle : p.toSubgraph.spanningCoe ≤ G ⊔ edge a c := by
    rw [← sdiff_edge _ (by simpa : ¬p.toSubgraph.spanningCoe.Adj x b), sdiff_le_iff']
    intro v w hvw
    apply hsupG ▸ sup_le_sup hM1sub hM2sub
    have := p.toSubgraph.spanningCoe_le hvw
    simp only [cycles, symmDiff_def] at this
    aesop
  -- Helper condition to show that `p` ends with an edge in `M2`
  have aux {x' : V} (hx' : x' ∈ ({x, b} : Set V)) (c' : V) (hc : c' ≠ a)
      (hadj : p.toSubgraph.Adj c' x') : M2.Adj c' x' := by
    refine (hadj.adj_sub.resolve_left fun hl ↦ hnpxb ?_).1
    obtain ⟨w, -, hw⟩ := hM1.1 (hM1.2 x')
    obtain rfl | rfl := hx'
    · rw [hw _ hM1xb, ← hw _ hl.1.symm]
      exact hadj.symm
    · rw [hw _ hM1xb.symm, ← hw _ hl.1.symm]
      exact hadj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
  obtain rfl | rfl := hx'
  · exact tutte_exists_isAlternating_isCycles p hp hcalt (hnM2 x' hnxc) hpac hnpxb hM2ac
      hxa hnxc hab.ne hle (aux (by simp))
  · conv =>
      enter [1, G', 2, 2, 1, 1]
      rw [adj_comm]
    rw [Subgraph.adj_comm] at hnpxb
    exact tutte_exists_isAlternating_isCycles p hp hcalt (hnM2 _ hnbc) hpac hnpxb hM2ac
      hab.symm hnbc hxa.ne.symm hle (aux (by simp))

set_option backward.isDefEq.respectTransparency.types false in
/-- From a graph on an even number of vertices with no perfect matching, we can remove an odd number
of vertices such that there are more odd components in the resulting graph than vertices we removed.

This is the sufficiency side of Tutte's theorem. -/
/-
**SimpleGraph.exists_isTutteViolator** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：exists_isTutteViolator (h : forall (M : G.Subgraph), ¬M.IsPerfectMatching)
 (hvEven : Even (Nat.card V)) : exists u, G.IsTutteViolator u
参数：h : forall (M : G.Subgraph), ¬M.IsPerfectMatching；hvEven : Even (Nat.card V)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用引理 `SimpleGraph.exists_maximal_isMatchingFree`：exists_maximal_isMatchingFree
 [Finite V] (h : G.IsMatchingFree) : exists Gmax : SimpleGraph V, G <= Gmax ∧ Gm
ax.IsMatchingFree ∧ forall G', …
· 使用定理 `SimpleGraph.IsTutteViolator.mono`：∀ {V : Type u_1} {G G' : SimpleGraph V
} [Finite V] {u : Set V}, G ≤ G' → G'.IsTutteViolator u → G.IsTutteViolator u
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `SimpleGraph.Subgraph.IsPerfectMatching.exists_of_isClique_supp`：∀ {V : T
ype u_1} {G : SimpleGraph V} [Finite V],   Even (Nat.card V) →     ¬G.IsTutteVio
lator G.universalVerts →       (∀ (K : G.deleteUnive…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ncard_eq_toFinset_card'`：ncard_eq_toFinset_card' (s : Set α) [Fintyp
e s] : s.ncard = s.toFinset.card
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.not_isClique_iff`：not_isClique_iff : ¬ G.IsClique s ↔ exists
 (v w : s), v != w ∧ ¬ G.Adj v w
· 使用定理 `SimpleGraph.Reachable.exists_path_of_dist`：∀ {V : Type u_1} {G : SimpleG
raph V} {u v : V}, G.Reachable u v → ∃ p, p.IsPath ∧ p.length = G.dist u v
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用引理 `SimpleGraph.ConnectedComponent.connected_toSimpleGraph`：connected_toSimp
leGraph (C : ConnectedComponent G) : (C.toSimpleGraph).Connected where preconnec
ted
· 使用定理 `SimpleGraph.Walk.exists_adj_adj_not_adj_ne`：∀ {V : Type u_1} {G : Simple
Graph V} {v w : V} {p : G.Walk v w},   p.length = G.dist v w → 1 < G.dist v w → 
∃ x a b, G.Adj x a ∧ G.Adj a b ∧…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.Reachable.one_lt_dist_of_ne_of_not_adj`：∀ {V : Type u_1} {G 
: SimpleGraph V} {u v : V}, G.Reachable u v → u ≠ v → ¬G.Adj u v → 1 < G.dist u 
v
· 使用定理 `SimpleGraph.Walk.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
 (p : G.Walk u v), G.Reachable u v
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SimpleGraph.Subgraph.coe_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' : G
.Subgraph) (v w : ↑G'.verts), G'.coe.Adj v w = G'.Adj ↑v ↑w
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `left_lt_sup`：left_lt_sup : a < a ⊔ b ↔ ¬b <= a
· 使用引理 `SimpleGraph.edge_le_iff`：edge_le_iff {v w : V} : edge v w <= G ↔ v = w ∨
 G.Adj v w
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
From a graph on an even number of vertices with no perfect matching, we can remo
ve an odd number
of vertices such that there are more odd components in the resulting graph than 
vertices we removed.

This is the sufficiency side of Tutte's theorem.
-/
lemma exists_isTutteViolator (h : ∀ (M : G.Subgraph), ¬M.IsPerfectMatching)
    (hvEven : Even (Nat.card V)) :
    ∃ u, G.IsTutteViolator u := by
  classical
  cases nonempty_fintype V
  -- It suffices to consider the edge-maximal case
  obtain ⟨Gmax, hSubgraph, hMatchingFree, hMaximal⟩ := exists_maximal_isMatchingFree h
  refine ⟨Gmax.universalVerts, .mono hSubgraph ?_⟩
  by_contra! hc
  simp only [IsTutteViolator, Set.ncard_eq_toFinset_card', Set.toFinset_card] at hc
  by_cases! h' : ∀ (K : ConnectedComponent Gmax.deleteUniversalVerts.coe),
      Gmax.deleteUniversalVerts.coe.IsClique K.supp
  · -- Deleting universal vertices splits the graph into cliques
    rw [Fintype.card_eq_nat_card] at hc
    simp_rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq] at hc
    push Not at hc
    obtain ⟨M, hM⟩ := Subgraph.IsPerfectMatching.exists_of_isClique_supp hvEven
      (by simpa [IsTutteViolator] using hc) h'
    exact hMatchingFree M hM
  · -- Deleting universal vertices does not result in only cliques
    obtain ⟨K, hK⟩ := h'
    obtain ⟨x, y, hxy⟩ := (not_isClique_iff _).mp hK
    obtain ⟨p, hp⟩ := Reachable.exists_path_of_dist (K.connected_toSimpleGraph x y)
    obtain ⟨x, a, b, hxa, hxb, hnadjxb, hnxb⟩ := Walk.exists_adj_adj_not_adj_ne hp.2
      (p.reachable.one_lt_dist_of_ne_of_not_adj hxy.1 hxy.2)
    simp only [ConnectedComponent.toSimpleGraph, deleteUniversalVerts, universalVerts,
      Subgraph.verts_top, comap_adj, Function.Embedding.coe_subtype,
      Subgraph.coe_adj, Subgraph.induce_adj, Subtype.coe_prop, Subgraph.top_adj, true_and]
      at hxa hxb hnadjxb
    obtain ⟨c, hc⟩ : ∃ (c : V), (a : V) ≠ c ∧ ¬ Gmax.Adj a c := by
      simpa [universalVerts, IsUniversal] using a.1.2.2
    have hbnec : b.val.val ≠ c := by rintro rfl; exact hc.2 hxb
    obtain ⟨_, hG1⟩ := hMaximal _ <| left_lt_sup.mpr (by
      rw [edge_le_iff (v := x.1.1) (w := b.1.1)]
      simp [hnadjxb, Subtype.val_injective.ne <| Subtype.val_injective.ne hnxb])
    obtain ⟨_, hG2⟩ := hMaximal _ <| left_lt_sup.mpr (by
      rwa [edge_le_iff (v := a.1.1) (w := c), not_or])
    have hcnex : x.val.val ≠ c := by rintro rfl; exact hc.2 hxa.symm
    obtain ⟨Mcon, hMcon⟩ := tutte_exists_isPerfectMatching_of_near_matchings hxa
      hxb hnadjxb (fun hadj ↦ hc.2 hadj) (by lia) hcnex hc.1 hbnec hG1 hG2
    exact hMatchingFree Mcon hMcon

/-- **Tutte's theorem**

A graph has a perfect matching if and only if: For every subset `u` of vertices, removing this
subset induces at most `u.ncard` components of odd size. This is formally stated using the
predicate `IsTutteViolator`, which is satisfied exactly when this condition does not hold. -/
/-
**SimpleGraph.tutte** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：tutte : (exists M : Subgraph G, M.IsPerfectMatching) ↔ forall u, ¬ G.IsTut
teViolator u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.not_isTutteViolator_of_isPerfectMatching`：not_isTutteViolato
r_of_isPerfectMatching {M : Subgraph G} (hM : M.IsPerfectMatching) (u : Set V) :
 ¬G.IsTutteViolator u
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.IsTutteViolator.empty`：∀ {V : Type u_1} {G : SimpleGraph V} 
[Finite V], Odd (Nat.card V) → G.IsTutteViolator ∅
· 使用引理 `SimpleGraph.exists_isTutteViolator`：exists_isTutteViolator (h : forall (
M : G.Subgraph), ¬M.IsPerfectMatching) (hvEven : Even (Nat.card V)) : exists u, 
G.IsTutteViolator u
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_odd_iff_even`：∀ {n : ℕ}, ¬Odd n ↔ Even n

--- 原说明 ---
**Tutte's theorem**

A graph has a perfect matching if and only if: For every subset `u` of vertices,
 removing this
subset induces at most `u.ncard` components of odd size. This is formally stated
 using the
predicate `IsTutteViolator`, which is satisfied exactly when this condition does
 not hold.
-/
theorem tutte : (∃ M : Subgraph G, M.IsPerfectMatching) ↔ ∀ u, ¬ G.IsTutteViolator u := by
  refine ⟨by rintro ⟨M, hM⟩; apply not_isTutteViolator_of_isPerfectMatching hM, ?_⟩
  contrapose!
  intro h
  by_cases hvOdd : Odd (Nat.card V)
  · exact ⟨∅, .empty hvOdd⟩
  · exact exists_isTutteViolator h (Nat.not_odd_iff_even.mp hvOdd)

end SimpleGraph

