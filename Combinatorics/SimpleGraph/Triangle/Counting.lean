/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Triangle counting lemma

In this file, we prove the triangle counting lemma.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

public section

-- TODO: This instance is bad because it creates data out of a Prop
attribute [-instance] decidableEq_of_subsingleton

open Finset Fintype

variable {α : Type*} (G : SimpleGraph α) [DecidableRel G.Adj] {ε : ℝ} {s t u : Finset α}

namespace SimpleGraph

/-- The vertices of `s` whose density in `t` is `ε` less than expected. -/
/-
**SimpleGraph.badVertices** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertices of `s` whose density in `t` is `ε` less than expected.
-/
private noncomputable def badVertices (ε : ℝ) (s t : Finset α) : Finset α :=
  {x ∈ s | #{y ∈ t | G.Adj x y} < (G.edgeDensity s t - ε) * #t}
/-
**SimpleGraph.card_interedges_badVertices_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma card_interedges_badVertices_le :
    #(Rel.interedges G.Adj (badVertices G ε s t) t) ≤
      #(badVertices G ε s t) * #t * (G.edgeDensity s t - ε) := by
  classical
  refine (Nat.cast_le.2 <| (card_le_card <| subset_of_eq (Rel.interedges_eq_biUnion _)).trans
    card_biUnion_le).trans ?_
  simp_rw [Nat.cast_sum, card_map, ← nsmul_eq_mul, smul_mul_assoc, mul_comm (#t : ℝ)]
  exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2.le
/-
**SimpleGraph.edgeDensity_badVertices_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma edgeDensity_badVertices_le (hε : 0 ≤ ε) (dst : 2 * ε ≤ G.edgeDensity s t) :
    G.edgeDensity (badVertices G ε s t) t ≤ G.edgeDensity s t - ε := by
  rw [edgeDensity_def]
  push_cast
  refine div_le_of_le_mul₀ (by positivity) (sub_nonneg_of_le <| by linarith) ?_
  rw [mul_comm]
  exact G.card_interedges_badVertices_le
/-
**SimpleGraph.card_badVertices_le** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma card_badVertices_le (dst : 2 * ε ≤ G.edgeDensity s t) (hst : G.IsUniform ε s t) :
    #(badVertices G ε s t) ≤ #s * ε := by
  have hε : ε ≤ 1 := (le_mul_of_one_le_left hst.pos.le (by simp)).trans
    (dst.trans <| mod_cast edgeDensity_le_one _ _ _)
  by_contra! h
  have : |(G.edgeDensity (badVertices G ε s t) t - G.edgeDensity s t : ℝ)| < ε :=
    hst (filter_subset _ _) Subset.rfl h.le (mul_le_of_le_one_right (Nat.cast_nonneg _) hε)
  rw [abs_sub_lt_iff] at this
  linarith [G.edgeDensity_badVertices_le hst.pos.le dst]

/-- A subset of the triangles constructed in a weird way to make them easy to count. -/
/-
**SimpleGraph.triangle_split_helper** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of the triangles constructed in a weird way to make them easy to count.
-/
private lemma triangle_split_helper [DecidableEq α] :
    (s \ (badVertices G ε s t ∪ badVertices G ε s u)).biUnion
      (fun x ↦ (G.interedges {y ∈ t | G.Adj x y} {y ∈ u | G.Adj x y}).image (x, ·)) ⊆
      (s ×ˢ t ×ˢ u).filter (fun (x, y, z) ↦ G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) := by
  rintro ⟨x, y, z⟩
  simp only [mem_filter, mem_product, mem_biUnion, mem_sdiff, mem_union,
    mem_image, Prod.exists, and_assoc, exists_imp, and_imp, Prod.mk_inj, mem_interedges_iff]
  rintro x hx - y z hy xy hz xz yz rfl rfl rfl
  exact ⟨hx, hy, hz, xy, xz, yz⟩
/-
**SimpleGraph.good_vertices_triangle_card** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma good_vertices_triangle_card [DecidableEq α] (dst : 2 * ε ≤ G.edgeDensity s t)
    (dsu : 2 * ε ≤ G.edgeDensity s u) (dtu : 2 * ε ≤ G.edgeDensity t u) (utu : G.IsUniform ε t u)
    (x : α) (hx : x ∈ s \ (badVertices G ε s t ∪ badVertices G ε s u)) :
    ε ^ 3 * #t * #u ≤ #((({y ∈ t | G.Adj x y} ×ˢ {y ∈ u | G.Adj x y}).filter
        fun (y, z) ↦ G.Adj y z).image (x, ·)) := by
  simp only [mem_sdiff, badVertices, mem_union, not_or, mem_filter, not_and_or, not_lt] at hx
  rw [← or_and_left, and_or_left] at hx
  simp only [false_or, and_not_self, mul_comm (_ - _)] at hx
  obtain ⟨-, hxY, hsu⟩ := hx
  have hY : #t * ε ≤ #{y ∈ t | G.Adj x y} := by
    refine le_trans ?_ hxY; gcongr; linarith
  have hZ : #u * ε ≤ #{y ∈ u | G.Adj x y} := by
    refine le_trans ?_ hsu; gcongr; linarith
  rw [card_image_of_injective _ (Prod.mk_right_injective _)]
  have := utu (filter_subset (G.Adj x) _) (filter_subset (G.Adj x) _) hY hZ
  have : ε ≤ G.edgeDensity {y ∈ t | G.Adj x y} {y ∈ u | G.Adj x y} := by
    rw [abs_sub_lt_iff] at this; linarith
  rw [edgeDensity_def] at this
  push_cast at this
  have hε := utu.pos.le
  refine le_trans ?_ (mul_le_of_le_div₀ (Nat.cast_nonneg _) (by positivity) this)
  refine Eq.trans_le ?_
    (mul_le_mul_of_nonneg_left (mul_le_mul hY hZ (by positivity) (by positivity)) hε)
  ring

/-- The **Triangle Counting Lemma**. If `G` is a graph and `s`, `t`, `u` are sets of vertices such
that each pair is `ε`-uniform and `2 * ε`-dense, then a proportion of at least
`(1 - 2 * ε) * ε ^ 3` of the triples `(a, b, c) ∈ s × t × u` are triangles. -/
/-
**SimpleGraph.triangle_counting'** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：triangle_counting' (dst : 2 * ε <= G.edgeDensity s t) (hst : G.IsUniform ε
 s t) (dsu : 2 * ε <= G.edgeDensity s u) (usu : G.IsUniform ε s u) (dtu : 2 * ε 
<= G.edgeDensity t u) (utu : G.IsUniform ε t u) : (1 - 2 * ε) * ε ^ 3 * #s * #t 
* #u <= #((s ×ˢ t ×ˢ u).filter fun (a, b, c) => G.Adj a b ∧ G.Adj a c ∧ G.Adj b 
c)
参数：dst : 2 * ε <= G.edgeDensity s t；hst : G.IsUniform ε s t；dsu : 2 * ε <= G.edg
eDensity s u；usu : G.IsUniform ε s u；dtu : 2 * ε <= G.edgeDensity t u；utu : G.Is
Uniform ε t u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Triangle.Counting.0.SimpleGra
ph.card_badVertices_le`：∀ {α : Type u_1} (G : SimpleGraph α) [inst : DecidableRe
l G.Adj] {ε : ℝ} {s t : Finset α},   2 * ε ≤ ↑(G.edgeDensity s t) → G.IsUniform 
ε s …
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Triangle.Counting.0.SimpleGra
ph.triangle_split_helper`：∀ {α : Type u_1} (G : SimpleGraph α) [inst : Decidable
Rel G.Adj] {ε : ℝ} {s t u : Finset α} [inst_1 : DecidableEq α],   ((s \ (SimpleG
raph.b…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用定理 `Function.onFun.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β 
→ β → φ) (g : α → β) (x y : α),   Function.onFun f g x y = f (g x) (g y)
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `SimpleGraph.IsUniform.pos`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Field
 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {G : SimpleGraph α}   [inst
_3 : DecidableR…
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `sub_le_sub_iff_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] [AddRightMono α] {b c : α} (a : α),   a - b ≤ a - c ↔ c ≤ b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
The **Triangle Counting Lemma**. If `G` is a graph and `s`, `t`, `u` are sets of
 vertices such
that each pair is `ε`-uniform and `2 * ε`-dense, then a proportion of at least
`(1 - 2 * ε) * ε ^ 3` of the triples `(a, b, c) ∈ s × t × u` are triangles.
-/
lemma triangle_counting'
    (dst : 2 * ε ≤ G.edgeDensity s t) (hst : G.IsUniform ε s t)
    (dsu : 2 * ε ≤ G.edgeDensity s u) (usu : G.IsUniform ε s u)
    (dtu : 2 * ε ≤ G.edgeDensity t u) (utu : G.IsUniform ε t u) :
    (1 - 2 * ε) * ε ^ 3 * #s * #t * #u ≤
      #((s ×ˢ t ×ˢ u).filter fun (a, b, c) ↦ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) := by
  classical
  have h₁ : #(badVertices G ε s t) ≤ #s * ε := G.card_badVertices_le dst hst
  have h₂ : #(badVertices G ε s u) ≤ #s * ε := G.card_badVertices_le dsu usu
  let X' := s \ (badVertices G ε s t ∪ badVertices G ε s u)
  have : X'.biUnion _ ⊆ (s ×ˢ t ×ˢ u).filter fun (a, b, c) ↦ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c :=
    triangle_split_helper _
  refine le_trans ?_ (Nat.cast_le.2 <| card_le_card this)
  rw [card_biUnion, Nat.cast_sum]
  · apply le_trans _ (card_nsmul_le_sum X' _ _ <| G.good_vertices_triangle_card dst dsu dtu utu)
    rw [nsmul_eq_mul]
    have := hst.pos.le
    suffices hX' : (1 - 2 * ε) * #s ≤ #X' by
      exact Eq.trans_le (by ring) (mul_le_mul_of_nonneg_right hX' <| by positivity)
    have i : badVertices G ε s t ∪ badVertices G ε s u ⊆ s :=
      union_subset (filter_subset _ _) (filter_subset _ _)
    rw [sub_mul, one_mul, card_sdiff_of_subset i, Nat.cast_sub (card_le_card i),
      sub_le_sub_iff_left, mul_assoc, mul_comm ε, two_mul]
    refine (Nat.cast_le.2 <| card_union_le _ _).trans ?_
    rw [Nat.cast_add]
    gcongr
  rintro a _ b _ t
  rw [Function.onFun, Finset.disjoint_left]
  simp only [Prod.forall, mem_image, not_exists, Prod.mk_inj,
    exists_imp, and_imp, not_and]
  aesop

variable [DecidableEq α]
/-
**SimpleGraph.triple_eq_triple_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma triple_eq_triple_of_mem (hst : Disjoint s t) (hsu : Disjoint s u) (htu : Disjoint t u)
    {x₁ x₂ y₁ y₂ z₁ z₂ : α} (h : ({x₁, y₁, z₁} : Finset α) = {x₂, y₂, z₂})
    (hx₁ : x₁ ∈ s) (hx₂ : x₂ ∈ s) (hy₁ : y₁ ∈ t) (hy₂ : y₂ ∈ t) (hz₁ : z₁ ∈ u) (hz₂ : z₂ ∈ u) :
    (x₁, y₁, z₁) = (x₂, y₂, z₂) := by
  simp only [Finset.Subset.antisymm_iff, subset_iff, mem_insert, mem_singleton, forall_eq_or_imp,
    forall_eq] at h
  grind [Finset.disjoint_left]

variable [Fintype α]

/-- The **Triangle Counting Lemma**. If `G` is a graph and `s`, `t`, `u` are disjoint sets of
vertices such that each pair is `ε`-uniform and `2 * ε`-dense, then `G` contains at least
`(1 - 2 * ε) * ε ^ 3 * |s| * |t| * |u|` triangles. -/
/-
**SimpleGraph.triangle_counting** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：triangle_counting (dst : 2 * ε <= G.edgeDensity s t) (ust : G.IsUniform ε 
s t) (hst : Disjoint s t) (dsu : 2 * ε <= G.edgeDensity s u) (usu : G.IsUniform 
ε s u) (hsu : Disjoint s u) (dtu : 2 * ε <= G.edgeDensity t u) (utu : G.IsUnifor
m ε t u) (htu : Disjoint t u) : (1 - 2 * ε) * ε ^ 3 * #s * #t * #u <= #(G.clique
Finset 3)
参数：dst : 2 * ε <= G.edgeDensity s t；ust : G.IsUniform ε s t；hst : Disjoint s t；d
su : 2 * ε <= G.edgeDensity s u；usu : G.IsUniform ε s u；hsu : Disjoint s u；dtu :
 2 * ε <= G.edgeDensity t u；utu : G.IsUniform ε t u；htu : Disjoint t u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `SimpleGraph.triangle_counting'`：triangle_counting' (dst : 2 * ε <= G.edg
eDensity s t) (hst : G.IsUniform ε s t) (dsu : 2 * ε <= G.edgeDensity s u) (usu 
: G.IsUniform ε s u)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.coe_cliqueFinset`：coe_cliqueFinset (n : Nat) : (G.cliqueFins
et n : Set (Finset α)) = G.cliqueSet n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Triangle.Counting.0.SimpleGra
ph.triple_eq_triple_of_mem`：∀ {α : Type u_1} {s t u : Finset α} [inst : Decidabl
eEq α],   Disjoint s t →     Disjoint s u →       Disjoint t u →         ∀ {x₁ x
₂ y₁ y₂ …

--- 原说明 ---
The **Triangle Counting Lemma**. If `G` is a graph and `s`, `t`, `u` are disjoin
t sets of
vertices such that each pair is `ε`-uniform and `2 * ε`-dense, then `G` contains
 at least
`(1 - 2 * ε) * ε ^ 3 * |s| * |t| * |u|` triangles.
-/
lemma triangle_counting
    (dst : 2 * ε ≤ G.edgeDensity s t) (ust : G.IsUniform ε s t) (hst : Disjoint s t)
    (dsu : 2 * ε ≤ G.edgeDensity s u) (usu : G.IsUniform ε s u) (hsu : Disjoint s u)
    (dtu : 2 * ε ≤ G.edgeDensity t u) (utu : G.IsUniform ε t u) (htu : Disjoint t u) :
    (1 - 2 * ε) * ε ^ 3 * #s * #t * #u ≤ #(G.cliqueFinset 3) := by
  apply (G.triangle_counting' dst ust dsu usu dtu utu).trans _
  rw [Nat.cast_le]
  refine card_le_card_of_injOn (fun (x, y, z) ↦ {x, y, z}) ?_ ?_
  · rintro ⟨x, y, z⟩
    simp +contextual [is3Clique_triple_iff]
  rintro ⟨x₁, y₁, z₁⟩ h₁ ⟨x₂, y₂, z₂⟩ h₂ t
  simp only [mem_coe, mem_filter, mem_product] at h₁ h₂
  apply triple_eq_triple_of_mem hst hsu htu t <;> tauto

end SimpleGraph

