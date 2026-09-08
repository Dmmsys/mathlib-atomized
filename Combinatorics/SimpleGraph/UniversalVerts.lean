/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Universal Vertices

This file defines the set of universal vertices: those vertices that are connected
to all others. In addition, it describes results when considering connected components
of the graph where universal vertices are deleted. This particular graph plays a role
in the proof of Tutte's Theorem.

## Main definitions

* `G.universalVerts` is the set of vertices that are connected to all other vertices.
* `G.deleteUniversalVerts` is the subgraph of `G` with the universal vertices removed.
-/

@[expose] public section

assert_not_exists Field TwoSidedIdeal

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/--
The set of vertices that are connected to all other vertices.
-/
/-
**SimpleGraph.universalVerts** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：universalVerts (G : SimpleGraph V) : Set V
参数：G : SimpleGraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of vertices that are connected to all other vertices.
-/
def universalVerts (G : SimpleGraph V) : Set V := {v : V | G.IsUniversal v}
/-
**SimpleGraph.isClique_universalVerts** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isClique_universalVerts (G : SimpleGraph V) : G.IsClique G.universalVerts
参数：G : SimpleGraph V。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isClique_universalVerts (G : SimpleGraph V) : G.IsClique G.universalVerts :=
  fun _ hx _ _ hxy ↦ hx hxy

/--
The subgraph of `G` with the universal vertices removed.
-/
@[simps!]
/-
**SimpleGraph.deleteUniversalVerts** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：deleteUniversalVerts (G : SimpleGraph V) : Subgraph G
参数：G : SimpleGraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgraph of `G` with the universal vertices removed.
-/
def deleteUniversalVerts (G : SimpleGraph V) : Subgraph G :=
  (⊤ : Subgraph G).deleteVerts G.universalVerts
/-
**SimpleGraph.Subgraph.IsMatching.exists_of_universalVerts** 是 Mathlib 中的一个定理，位于
命名空间 `SimpleGraph.Subgraph.IsMatching`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} [Finite V] {s : Set V},   Disjoint G.
universalVerts s →     s.ncard ≤ G.universalVerts.ncard → ∃ t ⊆ G.universalVerts
, ∃ M, M.verts = s ∪ t ∧ M.IsMatching
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.exists_subset_card_eq`：exists_subset_card_eq {n : Nat} (hns : n <= s
.ncard) : exists t subseteq s, t.ncard = n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)
· 使用引理 `Set.cast_ncard`：cast_ncard {s : Set α} (hs : s.Finite) : (s.ncard : Card
inal) = Cardinal.mk s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Disjoint.ne_of_mem`：∀ {α : Type u} {s t : Set α}, Disjoint s t → ∀ ⦃a : 
α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ t → a ≠ b
· 使用定理 `SimpleGraph.Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv`：∀ {V :
 Type u_1} {G : SimpleGraph V} {s t : Set V},   Disjoint s t → ∀ (f : ↑s ≃ ↑t), 
(∀ (v : ↑s), G.Adj ↑v ↑(f v)) → ∃ M, M.verts = s ∪ t ∧…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
lemma Subgraph.IsMatching.exists_of_universalVerts [Finite V] {s : Set V}
    (h : Disjoint G.universalVerts s) (hc : s.ncard ≤ G.universalVerts.ncard) :
    ∃ t ⊆ G.universalVerts, ∃ (M : Subgraph G), M.verts = s ∪ t ∧ M.IsMatching := by
  obtain ⟨t, ht⟩ := Set.exists_subset_card_eq hc
  refine ⟨t, ht.1, ?_⟩
  obtain ⟨f⟩ : Nonempty (s ≃ t) := by
    rw [← Cardinal.eq, ← t.cast_ncard t.toFinite, ← s.cast_ncard s.toFinite, ht.2]
  let hd := Set.disjoint_of_subset_left ht.1 h
  have hadj (v : s) : G.Adj v (f v) := ht.1 (f v).2 (hd.ne_of_mem (f v).2 v.2) |>.symm
  exact Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hd.symm f hadj
/-
**SimpleGraph.disjoint_image_val_universalVerts** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph`。
形式化陈述：disjoint_image_val_universalVerts (s : Set G.deleteUniversalVerts.verts) :
 Disjoint (Subtype.val '' s) G.universalVerts
参数：s : Set G.deleteUniversalVerts.verts。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.deleteUniversalVerts_verts`：∀ {V : Type u_1} (G : SimpleGrap
h V), G.deleteUniversalVerts.verts = Set.univ \ G.universalVerts
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `Subtype.coe_image_subset`：coe_image_subset (s : Set α) (t : Set s) : ((↑
) : s -> α) '' t subseteq s
-/
lemma disjoint_image_val_universalVerts (s : Set G.deleteUniversalVerts.verts) :
    Disjoint (Subtype.val '' s) G.universalVerts := by
  simpa [← Set.disjoint_compl_right_iff_subset, Set.compl_eq_univ_sdiff] using
    Subtype.coe_image_subset _ s

/-- A component of the graph with universal vertices is even if we remove a set of representatives
of odd components and a subset of universal vertices.

This is because the number of vertices in the even components is not affected, and from odd
components exactly one vertex is removed. -/
/-
**SimpleGraph.even_ncard_image_val_supp_sdiff_image_val_rep_union** 是 Mathlib 中的
一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：even_ncard_image_val_supp_sdiff_image_val_rep_union {t : Set V} {s : Set G
.deleteUniversalVerts.verts} (K : G.deleteUniversalVerts.coe.ConnectedComponent)
 (h : t subseteq G.universalVerts) (hrep : ConnectedComponent.Represents s G.del
eteUniversalVerts.coe.oddComponents) : Even (Subtype.val '' K.supp \ (Subtype.va
l '' s union t)).ncard
参数：K : G.deleteUniversalVerts.coe.ConnectedComponent；h : t subseteq G.universalV
erts；hrep : ConnectedComponent.Represents s G.deleteUniversalVerts.coe.oddCompon
ents。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
· 使用引理 `Set.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subseteq u
) (d : Disjoint s u) : Disjoint s t
· 使用引理 `SimpleGraph.disjoint_image_val_universalVerts`：disjoint_image_val_univer
salVerts (s : Set G.deleteUniversalVerts.verts) : Disjoint (Subtype.val '' s) G.
universalVerts
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `Set.inter_sdiff_distrib_right`：inter_sdiff_distrib_right (s t u : Set α)
 : (s \ t) inter u = (s inter u) \ (t inter u)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `Set.sdiff_inter_self_eq_sdiff`：sdiff_inter_self_eq_sdiff {s t : Set α} :
 s \ (t inter s) = s \ t
· 使用定理 `Set.ncard_image_of_injective`：ncard_image_of_injective (s : Set α) (H : 
f.Injective) : (f '' s).ncard = s.ncard
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SimpleGraph.ConnectedComponent.even_ncard_supp_sdiff_rep`：∀ {V : Type u}
 {G : SimpleGraph V} {s : Set V} (K : G.ConnectedComponent),   SimpleGraph.Conne
ctedComponent.Represents s G.oddComponents → E…

--- 原说明 ---
A component of the graph with universal vertices is even if we remove a set of r
epresentatives
of odd components and a subset of universal vertices.

This is because the number of vertices in the even components is not affected, a
nd from odd
components exactly one vertex is removed.
-/
lemma even_ncard_image_val_supp_sdiff_image_val_rep_union {t : Set V}
    {s : Set G.deleteUniversalVerts.verts} (K : G.deleteUniversalVerts.coe.ConnectedComponent)
    (h : t ⊆ G.universalVerts)
    (hrep : ConnectedComponent.Represents s G.deleteUniversalVerts.coe.oddComponents) :
    Even (Subtype.val '' K.supp \ (Subtype.val '' s ∪ t)).ncard := by
  simp [-deleteUniversalVerts_verts, ← Set.sdiff_inter_sdiff,
    ← Set.image_sdiff Subtype.val_injective,
    sdiff_eq_left.mpr <| Set.disjoint_of_subset_right h (disjoint_image_val_universalVerts _),
    Set.inter_sdiff_distrib_right, ← Set.image_inter Subtype.val_injective,
    Set.ncard_image_of_injective _ Subtype.val_injective, K.even_ncard_supp_sdiff_rep hrep]

end SimpleGraph

