/-
Copyright (c) 2025 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.NatCard

import Mathlib.Tactic.ENatToNat

/-!
# Vertex cover

A *vertex cover* of a simple graph is a set of vertices such that every edge is incident to at least
one of the vertices in the set.

## Main definitions

* `SimpleGraph.IsVertexCover G c`: Predicate that `c` is a vertex cover of `G`.
* `SimpleGraph.vertexCoverNum G`: The vertex cover number, e.g. the size of a minimal vertex cover.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W}

section IsVertexCover

/-- `c` is a vertex cover of `G` if every edge in `G` is incident to at least one vertex in `c`. -/
/-
**SimpleGraph.IsVertexCover** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsVertexCover (G : SimpleGraph V) (c : Set V) : Prop
参数：G : SimpleGraph V；c : Set V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c` is a vertex cover of `G` if every edge in `G` is incident to at least one ve
rtex in `c`.
-/
def IsVertexCover (G : SimpleGraph V) (c : Set V) : Prop :=
  ∀ ⦃v w : V⦄, G.Adj v w → v ∈ c ∨ w ∈ c

@[simp]
/-
**SimpleGraph.isVertexCover_empty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isVertexCover_empty : IsVertexCover G ∅ ↔ G = ⊥
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
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isVertexCover_empty : IsVertexCover G ∅ ↔ G = ⊥ := by
  simp [IsVertexCover, eq_bot_iff_forall_not_adj]

@[simp]
/-
**SimpleGraph.isVertexCover_univ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isVertexCover_univ : IsVertexCover G .univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isVertexCover_univ : IsVertexCover G .univ := by
  simp [IsVertexCover]

@[simp]
/-
**SimpleGraph.isVertexCover_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isVertexCover_bot (c : Set V) : IsVertexCover ⊥ c
参数：c : Set V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isVertexCover_bot (c : Set V) : IsVertexCover ⊥ c := by
  simp [IsVertexCover]
/-
**SimpleGraph.IsVertexCover.subset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsVert
exCover`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {c d : Set V}, c ⊆ d → G.IsVertexCove
r c → G.IsVertexCover d
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsVertexCover.subset {c d : Set V} (hcd : c ⊆ d) (hc : IsVertexCover G c) :
    IsVertexCover G d := by
  grind [IsVertexCover]
/-
**SimpleGraph.IsVertexCover.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsVertex
Cover`。
形式化陈述：∀ {V : Type u_1} {G G' : SimpleGraph V} {c : Set V}, G ≤ G' → G'.IsVertexC
over c → G.IsVertexCover c
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsVertexCover.mono {c : Set V} (hG : G ≤ G') (hc : IsVertexCover G' c) :
    IsVertexCover G c :=
  fun _ _ hadj ↦ hc (hG hadj)

/-- A set `c` is a vertex cover iff the complement of `c` is an independent set. -/
@[simp]
/-
**SimpleGraph.isIndepSet_compl_iff_isVertexCover** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph`。
形式化陈述：isIndepSet_compl_iff_isVertexCover {c : Set V} : G.IsIndepSet cᶜ ↔ IsVerte
xCover G c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b

--- 原说明 ---
A set `c` is a vertex cover iff the complement of `c` is an independent set.
-/
theorem isIndepSet_compl_iff_isVertexCover {c : Set V} : G.IsIndepSet cᶜ ↔ IsVertexCover G c := by
  refine ⟨fun hi v w hadj ↦ ?_, by grind [IsVertexCover, Set.Pairwise]⟩
  by_contra! hh
  exact hi hh.1 hh.2 (Adj.ne hadj) hadj

@[simp]
/-
**SimpleGraph.isVertexCover_compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isVertexCover_compl {c : Set V} : G.IsVertexCover cᶜ ↔ G.IsIndepSet c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isVertexCover_compl {c : Set V} : G.IsVertexCover cᶜ ↔ G.IsIndepSet c := by
  simp [← isIndepSet_compl_iff_isVertexCover]
/-
**SimpleGraph.IsVertexCover.preimage** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsVe
rtexCover`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} {F
 : Type u_3} [inst : FunLike F V W]   [SimpleGraph.HomClass F G H] (f : F) {c : 
Set W}, H.IsVertexCover c → G.IsVertexCover (⇑f ⁻¹' c)
参数：f : F；⇑f ⁻¹' c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.map_rel`：∀ {F : Type u_5} {α : outParam (Type u_6)} {β : out
Param (Type u_7)} {r : outParam (α → α → Prop)}   {s : outParam (β → β → Prop)} 
{inst : F…
-/
theorem IsVertexCover.preimage {F : Type*} [FunLike F V W] [HomClass F G H]
    (f : F) {c : Set W} (hc : IsVertexCover H c) :
    IsVertexCover G (f ⁻¹' c) :=
  fun _ _ hadj ↦ hc (map_rel f hadj)

@[simp]
/-
**SimpleGraph.isVertexCover_preimage_iso** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：isVertexCover_preimage_iso (f : G ≃g H) {c : Set W} : IsVertexCover G (f ⁻
¹' c) ↔ IsVertexCover H c where mp h
参数：f : G ≃g H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `RelIso.surjective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s
 : β → β → Prop} (e : r ≃r s), Function.Surjective ⇑e
· 使用定理 `SimpleGraph.IsVertexCover.preimage`：∀ {V : Type u_1} {W : Type u_2} {G :
 SimpleGraph V} {H : SimpleGraph W} {F : Type u_3} [inst : FunLike F V W]   [Sim
pleGraph.HomClass F G H]…
· 使用定理 `RelIso.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r ≃r s) r s
-/
theorem isVertexCover_preimage_iso (f : G ≃g H) {c : Set W} :
    IsVertexCover G (f ⁻¹' c) ↔ IsVertexCover H c where
  mp h := by
    simpa [← RelIso.image_eq_preimage_symm, Set.image_preimage_eq _ f.surjective]
      using h.preimage f.symm
  mpr := .preimage f

@[simp]
/-
**SimpleGraph.isVertexCover_image_iso** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isVertexCover_image_iso (f : G ≃g H) {c : Set V} : IsVertexCover H (f '' c
) ↔ IsVertexCover G c
参数：f : G ≃g H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelIso.image_eq_preimage_symm`：RelIso.image_eq_preimage_symm (e : r ≃r s
) (t : Set α) : e '' t = e.symm ⁻¹' t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isVertexCover_image_iso (f : G ≃g H) {c : Set V} :
    IsVertexCover H (f '' c) ↔ IsVertexCover G c := by
  simp [RelIso.image_eq_preimage_symm]

end IsVertexCover

section vertexCoverNum

/-- The vertex cover number of `G` is the minimal number of vertices in a vertex cover of `G`. -/
/-
**SimpleGraph.vertexCoverNum** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：vertexCoverNum (G : SimpleGraph V) : Nat∞
参数：G : SimpleGraph V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertex cover number of `G` is the minimal number of vertices in a vertex cov
er of `G`.
-/
noncomputable def vertexCoverNum (G : SimpleGraph V) : ℕ∞ :=
  ⨅ (s : Set V) (_ : IsVertexCover G s), s.encard
/-
**SimpleGraph.vertexCoverNum_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：vertexCoverNum_le_iff {n : Nat∞} : vertexCoverNum G <= n ↔ forall (m : Nat
∞), (forall s, IsVertexCover G s -> m <= s.encard) -> m <= n
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
theorem vertexCoverNum_le_iff {n : ℕ∞} :
    vertexCoverNum G ≤ n ↔ ∀ (m : ℕ∞), (∀ s, IsVertexCover G s → m ≤ s.encard) → m ≤ n := by
  simp [vertexCoverNum, iInf_le_iff]
/-
**SimpleGraph.IsVertexCover.vertexCoverNum_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.IsVertexCover`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {c : Set V}, G.IsVertexCover c → G.ve
rtexCoverNum ≤ c.encard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.vertexCoverNum_le_iff`：vertexCoverNum_le_iff {n : Nat∞} : ve
rtexCoverNum G <= n ↔ forall (m : Nat∞), (forall s, IsVertexCover G s -> m <= s.
encard) -> m <= n
-/
theorem IsVertexCover.vertexCoverNum_le {c : Set V} (hc : IsVertexCover G c) :
    vertexCoverNum G ≤ c.encard :=
  vertexCoverNum_le_iff.mpr fun _ hm ↦ hm c hc
/-
**SimpleGraph.vertexCoverNum_exists** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：vertexCoverNum_exists (G) : exists s : Set V, s.encard = vertexCoverNum G 
∧ IsVertexCover G s
参数：G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `ENat.exists_eq_iInf`：exists_eq_iInf [Nonempty ι] (f : ι -> Nat∞) : exist
s a, f a = ⨅ x, f x
· 使用定理 `iInf_subtype`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α]
 {p : ι → Prop} {f : Subtype p → α},   iInf f = ⨅ i, ⨅ (h : p i), f ⟨i, h⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem vertexCoverNum_exists (G) :
    ∃ s : Set V, s.encard = vertexCoverNum G ∧ IsVertexCover G s := by
  have : Nonempty {s : Set V // IsVertexCover G s} := nonempty_subtype.mpr ⟨Set.univ, by simp⟩
  obtain ⟨s, hs⟩ := @ENat.exists_eq_iInf _ this (·.val.encard)
  exact ⟨s.val, hs ▸ iInf_subtype, s.property⟩
/-
**SimpleGraph.exists_of_le_vertexCoverNum** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：exists_of_le_vertexCoverNum (n : Nat) (h₁ : vertexCoverNum G <= n) (h₂ : n
 <= ENat.card V) : exists s : Set V, s.encard = n ∧ IsVertexCover G s
参数：n : Nat；h₁ : vertexCoverNum G <= n；h₂ : n <= ENat.card V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.vertexCoverNum_exists`：vertexCoverNum_exists (G) : exists s 
: Set V, s.encard = vertexCoverNum G ∧ IsVertexCover G s
· 使用定理 `Set.exists_superset_subset_encard_eq`：exists_superset_subset_encard_eq {
k : Nat∞} (hst : s subseteq t) (hsk : s.encard <= k) (hkt : k <= t.encard) : exi
sts r, s subseteq r ∧ r su…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
· 使用定理 `SimpleGraph.IsVertexCover.subset`：∀ {V : Type u_1} {G : SimpleGraph V} {
c d : Set V}, c ⊆ d → G.IsVertexCover c → G.IsVertexCover d
-/
theorem exists_of_le_vertexCoverNum (n : ℕ) (h₁ : vertexCoverNum G ≤ n)
    (h₂ : n ≤ ENat.card V) : ∃ s : Set V, s.encard = n ∧ IsVertexCover G s := by
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists G
  obtain ⟨r, hr₁, _, hr₃⟩ :=
    Set.exists_superset_subset_encard_eq (by simp) (le_of_eq_of_le hs₁ h₁) (Set.encard_univ _ ▸ h₂)
  exact ⟨r, hr₃, hs₂.subset hr₁⟩

@[simp]
/-
**SimpleGraph.vertexCoverNum_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：vertexCoverNum_bot : vertexCoverNum (emptyGraph V) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `SimpleGraph.IsVertexCover.vertexCoverNum_le`：∀ {V : Type u_1} {G : Simpl
eGraph V} {c : Set V}, G.IsVertexCover c → G.vertexCoverNum ≤ c.encard
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
-/
theorem vertexCoverNum_bot : vertexCoverNum (emptyGraph V) = 0 :=
  nonpos_iff_eq_zero.mp <| Set.encard_empty ▸ @IsVertexCover.vertexCoverNum_le V ⊥ ∅ (by simp)

@[simp]
/-
**SimpleGraph.vertexCoverNum_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：vertexCoverNum_of_subsingleton [Subsingleton V] : vertexCoverNum G = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.subsingleton_iff`：∀ {V : Type u}, Subsingleton (SimpleGraph 
V) ↔ Subsingleton V
· 使用定理 `SimpleGraph.vertexCoverNum_bot`：vertexCoverNum_bot : vertexCoverNum (emp
tyGraph V) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vertexCoverNum_of_subsingleton [Subsingleton V] : vertexCoverNum G = 0 := by
  simp [SimpleGraph.subsingleton_iff.mpr _ |>.allEq G ⊥]

@[simp]
/-
**SimpleGraph.vertexCoverNum_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：vertexCoverNum_eq_zero : vertexCoverNum G = 0 ↔ G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.vertexCoverNum_exists`：vertexCoverNum_exists (G) : exists s 
: Set V, s.encard = vertexCoverNum G ∧ IsVertexCover G s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.vertexCoverNum_bot`：vertexCoverNum_bot : vertexCoverNum (emp
tyGraph V) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem vertexCoverNum_eq_zero : vertexCoverNum G = 0 ↔ G = ⊥ := by
  refine ⟨fun h ↦ ?_, by simp_all⟩
  simpa [h] using vertexCoverNum_exists G
/-
**SimpleGraph.vertexCoverNum_le_card_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：vertexCoverNum_le_card_sub_one : vertexCoverNum G <= ENat.card V - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.vertexCoverNum_of_subsingleton`：vertexCoverNum_of_subsinglet
on [Subsingleton V] : vertexCoverNum G = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用引理 `ENat.forall_natCast_le_iff_le`：forall_natCast_le_iff_le : (forall a : Na
t, a <= m -> a <= n) ↔ m <= n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.encard_sdiff_singleton_of_mem`：encard_sdiff_singleton_of_mem (h : a 
in s) : (s \ {a}).encard = s.encard - 1
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
-/
theorem vertexCoverNum_le_card_sub_one : vertexCoverNum G ≤ ENat.card V - 1 := by
  nontriviality V
  obtain ⟨x⟩ := not_subsingleton_iff_nontrivial.mp (not_subsingleton V) |>.to_nonempty
  refine ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  simp only [vertexCoverNum, le_iInf_iff] at hn
  have := hn (Set.univ \ {x}) (by grind [IsVertexCover, Adj.ne'])
  simpa [Set.encard_sdiff_singleton_of_mem (Set.mem_univ _)] using this

@[simp]
/-
**SimpleGraph.vertexCoverNum_ne_top_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：vertexCoverNum_ne_top_of_finite [Finite V] : vertexCoverNum G != ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `SimpleGraph.vertexCoverNum_le_card_sub_one`：vertexCoverNum_le_card_sub_o
ne : vertexCoverNum G <= ENat.card V - 1
-/
theorem vertexCoverNum_ne_top_of_finite [Finite V] : vertexCoverNum G ≠ ⊤ :=
  ne_top_of_le_ne_top (by simpa) (@vertexCoverNum_le_card_sub_one V G)
/-
**SimpleGraph.vertexCoverNum_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：vertexCoverNum_lt_card [Nonempty V] [Finite V] : vertexCoverNum G < ENat.c
ard V
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENat.add_one_le_iff`：add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n
· 使用定理 `SimpleGraph.vertexCoverNum_ne_top_of_finite`：vertexCoverNum_ne_top_of_fi
nite [Finite V] : vertexCoverNum G != ⊤
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `SimpleGraph.vertexCoverNum_le_card_sub_one`：vertexCoverNum_le_card_sub_o
ne : vertexCoverNum G <= ENat.card V - 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.card_eq_coe_natCard`：card_eq_coe_natCard (α : Type*) [Finite α] : c
ard α = Nat.card α
· 使用定理 `Nat.add_le_of_le_sub`：∀ {a b c : ℕ}, b ≤ c → a ≤ c - b → a + b ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
-/
theorem vertexCoverNum_lt_card [Nonempty V] [Finite V] : vertexCoverNum G < ENat.card V := by
  refine (ENat.add_one_le_iff vertexCoverNum_ne_top_of_finite).mp ?_
  grw [vertexCoverNum_le_card_sub_one, ENat.card_eq_coe_natCard]
  enat_to_nat
  exact Nat.add_le_of_le_sub (Order.one_le_iff_pos.mpr Nat.card_pos) (le_refl _)
/-
**SimpleGraph.vertexCoverNum_le_encard_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：vertexCoverNum_le_encard_edgeSet : vertexCoverNum G <= G.edgeSet.encard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.edgeSet_eq_empty`：∀ {V : Type u} {G : SimpleGraph V}, G.edge
Set = ∅ ↔ G = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.edgeSet_bot`：edgeSet_bot : (⊥ : SimpleGraph V).edgeSet = ∅
· 使用定理 `SimpleGraph.vertexCoverNum_bot`：vertexCoverNum_bot : vertexCoverNum (emp
tyGraph V) = 0
· 使用定理 `Set.encard_empty`：∀ {α : Type u_1}, ∅.encard = 0
· 使用引理 `ENat.forall_natCast_le_iff_le`：forall_natCast_le_iff_le : (forall a : Na
t, a <= m -> a <= n) ↔ m <= n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem vertexCoverNum_le_encard_edgeSet : vertexCoverNum G ≤ G.edgeSet.encard := by
  by_cases h' : G.edgeSet = ∅
  · simp [h', SimpleGraph.edgeSet_eq_empty.mp]
  refine ENat.forall_natCast_le_iff_le.mp fun n hn ↦ ?_
  simp only [vertexCoverNum, le_iInf_iff] at hn
  have := hn ((·.out.1) '' G.edgeSet)
    (fun v w _ ↦ by grind [Sym2.out_fst_mem s(v, w), mem_edgeSet])
  grind [Set.encard_image_le]

@[simp]
/-
**SimpleGraph.vertexCoverNum_ne_top_of_finite_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：vertexCoverNum_ne_top_of_finite_edgeSet (h : G.edgeSet.Finite) : vertexCov
erNum G != ⊤
参数：h : G.edgeSet.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.encard_ne_top_iff`：encard_ne_top_iff : s.encard != ⊤ ↔ s.Finite
· 使用定理 `SimpleGraph.vertexCoverNum_le_encard_edgeSet`：vertexCoverNum_le_encard_e
dgeSet : vertexCoverNum G <= G.edgeSet.encard
-/
theorem vertexCoverNum_ne_top_of_finite_edgeSet (h : G.edgeSet.Finite) : vertexCoverNum G ≠ ⊤ :=
  ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr h) vertexCoverNum_le_encard_edgeSet

@[simp]
/-
**SimpleGraph.vertexCoverNum_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：vertexCoverNum_top : vertexCoverNum (completeGraph V) = ENat.card V - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.vertexCoverNum_of_subsingleton`：vertexCoverNum_of_subsinglet
on [Subsingleton V] : vertexCoverNum G = 0
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ENat.eq_of_forall_natCast_le_iff`：eq_of_forall_natCast_le_iff (hm : fora
ll a : Nat, a <= m ↔ a <= n) : m = n
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SimpleGraph.vertexCoverNum_le_card_sub_one`：vertexCoverNum_le_card_sub_o
ne : vertexCoverNum G <= ENat.card V - 1
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `SimpleGraph.exists_of_le_vertexCoverNum`：exists_of_le_vertexCoverNum (n 
: Nat) (h₁ : vertexCoverNum G <= n) (h₂ : n <= ENat.card V) : exists s : Set V, 
s.encard = n ∧ IsVertexCover …
· 使用定理 `ENat.le_sub_one_of_lt`：∀ {a b : ℕ∞}, a < b → a ≤ b - 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENat.add_one_le_iff`：add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.encard_sdiff`：encard_sdiff (h : s subseteq t) (hs : s.Finite) : (t \
 s).encard = t.encard - s.encard
· 使用定理 `Set.finite_of_encard_eq_coe`：finite_of_encard_eq_coe {k : Nat} (h : s.en
card = k) : s.Finite
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
· 使用定理 `ENat.le_sub_of_add_le_left`：∀ {a b c : ℕ∞}, a ≠ ⊤ → a + b ≤ c → b ≤ c - 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 43 条，此处仅展示前 30 条）
-/
theorem vertexCoverNum_top : vertexCoverNum (completeGraph V) = ENat.card V - 1 := by
  nontriviality V using tsub_eq_zero_of_le
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ⟨fun hn ↦ ?_, fun hn ↦ ?_⟩
  · grw [hn, vertexCoverNum_le_card_sub_one]
  by_contra! hh
  have : n - 1 ≤ ENat.card V := by
    grw [tsub_le_iff_right, hn]
    simp [add_assoc, one_add_one_eq_two]
  obtain ⟨t, ht₁, ht₂⟩ := exists_of_le_vertexCoverNum (n - 1) (ENat.le_sub_one_of_lt hh) this
  have : 1 < (Set.univ \ t).encard := by
    refine ENat.add_one_le_iff (by simp) |>.mp ?_
    rw [Set.encard_sdiff (by simp) (Set.finite_of_encard_eq_coe ht₁), Set.encard_univ]
    refine ENat.le_sub_of_add_le_left (by simp [ht₁]) ?_
    refine add_le_of_le_tsub_right_of_le (Order.add_one_le_of_lt ENat.one_lt_card) ?_
    grw [ht₁, ENat.natCast_sub, hn]
    simp [add_assoc, one_add_one_eq_two, le_tsub_add]
  obtain ⟨a, b, _, _, hne⟩ := Set.one_lt_encard_iff.mp <| this
  have := @ht₂ a b (by simp [hne])
  grind
/-
**SimpleGraph.IsContained.vertexCoverNum_le_vertexCoverNum** 是 Mathlib 中的一个定理，位于
命名空间 `SimpleGraph.IsContained`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W},  
 G.IsContained H → G.vertexCoverNum ≤ H.vertexCoverNum
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.vertexCoverNum_exists`：vertexCoverNum_exists (G) : exists s 
: Set V, s.encard = vertexCoverNum G ∧ IsVertexCover G s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.isIndepSet_iff_isAntichain_adj`：isIndepSet_iff_isAntichain_a
dj : G.IsIndepSet s ↔ IsAntichain G.Adj s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.isIndepSet_compl_iff_isVertexCover`：isIndepSet_compl_iff_isV
ertexCover {c : Set V} : G.IsIndepSet cᶜ ↔ IsVertexCover G c
· 使用定理 `IsAntichain.preimage`：preimage (hs : IsAntichain r s) {f : β -> α} (hf :
 Injective f) (h : forall ⦃a b⦄, r' a b -> r (f a) (f b)) : IsAntichain r' (f ⁻¹
' s)
· 使用定理 `RelHom.map_rel'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → Prop} {s :
 β → β → Prop} (self : r →r s) {a b : α},   r a b → s (self.toFun a) (self.toFun
 b)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `SimpleGraph.IsVertexCover.vertexCoverNum_le`：∀ {V : Type u_1} {G : Simpl
eGraph V} {c : Set V}, G.IsVertexCover c → G.vertexCoverNum ≤ c.encard
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Embedding.encard_le`：∀ {α : Type u_1} {β : Type u_2} {s : Set α
} {t : Set β} (e : ↑s ↪ ↑t), s.encard ≤ t.encard
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsContained.vertexCoverNum_le_vertexCoverNum (h : G ⊑ H) :
    vertexCoverNum G ≤ vertexCoverNum H := by
  have ⟨f, hf⟩ := h
  obtain ⟨s, hs₁, hs₂⟩ := vertexCoverNum_exists H
  have := H.isIndepSet_iff_isAntichain_adj.mp <| isIndepSet_compl_iff_isVertexCover.mpr hs₂
  have : IsAntichain G.Adj (f ⁻¹' sᶜ) := this.preimage hf (fun _ _ hadj ↦ f.map_rel' hadj)
  have : G.IsVertexCover (f ⁻¹' s) :=
    isIndepSet_compl_iff_isVertexCover.mp <| G.isIndepSet_iff_isAntichain_adj.mpr this
  grw [this.vertexCoverNum_le, ← hs₁]
  exact Function.Embedding.encard_le <| Function.Embedding.mk f hf |>.subtypeMap (by simp)

@[deprecated IsContained.vertexCoverNum_le_vertexCoverNum (since := "2026-01-07")]
/-
**SimpleGraph.vertexCoverNum_le_vertexCoverNum_of_injective** 是 Mathlib 中的一个定理，位
于命名空间 `SimpleGraph`。
形式化陈述：vertexCoverNum_le_vertexCoverNum_of_injective (f : G ->g H) (hf : Function
.Injective f) : vertexCoverNum G <= vertexCoverNum H
参数：f : G ->g H；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsContained.vertexCoverNum_le_vertexCoverNum`：∀ {V : Type u_
1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W},   G.IsContained H → G
.vertexCoverNum ≤ H.vertexCoverNum
-/
theorem vertexCoverNum_le_vertexCoverNum_of_injective (f : G →g H) (hf : Function.Injective f) :
    vertexCoverNum G ≤ vertexCoverNum H :=
  IsContained.vertexCoverNum_le_vertexCoverNum ⟨f, hf⟩

@[gcongr]
/-
**SimpleGraph.vertexCoverNum_mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：vertexCoverNum_mono (h : G <= G') : vertexCoverNum G <= vertexCoverNum G'
参数：h : G <= G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsContained.vertexCoverNum_le_vertexCoverNum`：∀ {V : Type u_
1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W},   G.IsContained H → G
.vertexCoverNum ≤ H.vertexCoverNum
· 使用定理 `SimpleGraph.IsContained.of_le`：∀ {V : Type u_1} {G₁ G₂ : SimpleGraph V},
 G₁ ≤ G₂ → G₁.IsContained G₂
-/
theorem vertexCoverNum_mono (h : G ≤ G') : vertexCoverNum G ≤ vertexCoverNum G' :=
  (IsContained.of_le h).vertexCoverNum_le_vertexCoverNum
/-
**SimpleGraph.vertexCoverNum_congr** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：vertexCoverNum_congr (f : G ≃g H) : vertexCoverNum G = vertexCoverNum H
参数：f : G ≃g H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimpleGraph.IsContained.vertexCoverNum_le_vertexCoverNum`：∀ {V : Type u_
1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W},   G.IsContained H → G
.vertexCoverNum ≤ H.vertexCoverNum
· 使用定理 `SimpleGraph.Iso.isContained`：∀ {V : Type u_1} {W : Type u_2} {G : Simple
Graph V} {H : SimpleGraph W} (e : G ≃g H), G.IsContained H
-/
theorem vertexCoverNum_congr (f : G ≃g H) : vertexCoverNum G = vertexCoverNum H :=
  le_antisymm f.isContained.vertexCoverNum_le_vertexCoverNum
    f.symm.isContained.vertexCoverNum_le_vertexCoverNum

end vertexCoverNum
end SimpleGraph

