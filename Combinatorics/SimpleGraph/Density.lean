/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Edge density

This file defines the number and density of edges of a relation/graph.

## Main declarations

Between two finsets of vertices,
* `Rel.interedges`: Finset of edges of a relation.
* `Rel.edgeDensity`: Edge density of a relation.
* `SimpleGraph.interedges`: Finset of edges of a graph.
* `SimpleGraph.edgeDensity`: Edge density of a graph.
-/

@[expose] public section

open Finset

variable {𝕜 ι κ α β : Type*}

/-! ### Density of a relation -/


namespace Rel

section Asymmetric

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  (r : α -> β -> Prop) [forall a, DecidablePred (r a)] {s s₁ s₂ : Finset α}
  {t t₁ t₂ : Finset β} {a : α} {b : β} {δ : 𝕜}

/--
Definition of `interedges` / `interedges` 的定义

English:
definition interedges
  signature: (s : Finset α) (t : Finset β)
  body: {e in s ×ˢ t | r e.1 e.2}

中文:
定义 interedges
  签名: (s : 有限集 α) (t : 有限集 β)
  定义体: {e in s ×ˢ t | r e.1 e.2}
-/
def interedges (s : Finset α) (t : Finset β) : Finset (α × β) := {e in s ×ˢ t | r e.1 e.2}

/--
Definition of `edgeDensity` / `edgeDensity` 的定义

English:
definition edgeDensity
  signature: (s : Finset α) (t : Finset β)
  body: #(interedges r s t) / (#s * #t)

中文:
定义 edgeDensity
  签名: (s : 有限集 α) (t : 有限集 β)
  定义体: #(interedges r s t) / (#s * #t)

Depends on / 依赖: interedges
-/
def edgeDensity (s : Finset α) (t : Finset β) : Rat := #(interedges r s t) / (#s * #t)

variable {r}

/--
theorem `mem_interedges_iff` / 定理 `mem_interedges_iff`

English:
theorem mem_interedges_iff
  given: {x : α × β}
  statement: x in interedges r s t ↔ x.1 in s ∧ x.2 in t ∧ r x.1 x.2
  proof: by
  rw [interedges]; rw [mem_filter]; rw [Finset.mem_product]; rw [and_assoc]

中文:
定理 mem_interedges_iff
  条件: {x : α × β}
  结论: x in interedges r s t ↔ x.1 in s ∧ x.2 in t ∧ r x.1 x.2
  证明: by
  rw [interedges]; rw [mem_filter]; rw [Finset.mem_product]; rw [and_assoc]

Depends on / 依赖: Finset, Finset.mem_product, and_assoc, interedges, mem_filter, mem_product
-/
theorem mem_interedges_iff {x : α × β} : x in interedges r s t ↔ x.1 in s ∧ x.2 in t ∧ r x.1 x.2 := by
  rw [interedges]; rw [mem_filter]; rw [Finset.mem_product]; rw [and_assoc]

/--
theorem `mk_mem_interedges_iff` / 定理 `mk_mem_interedges_iff`

English:
theorem mk_mem_interedges_iff
  statement: (a, b) in interedges r s t ↔ a in s ∧ b in t ∧ r a b
  proof: mem_interedges_iff

@[simp]

中文:
定理 mk_mem_interedges_iff
  结论: (a, b) in interedges r s t ↔ a in s ∧ b in t ∧ r a b
  证明: mem_interedges_iff

@[simp]

Depends on / 依赖: mem_interedges_iff
-/
theorem mk_mem_interedges_iff : (a, b) in interedges r s t ↔ a in s ∧ b in t ∧ r a b :=
  mem_interedges_iff

@[simp]
/--
theorem `interedges_empty_left` / 定理 `interedges_empty_left`

English:
theorem interedges_empty_left
  given: (t : Finset β)
  statement: interedges r ∅ t = ∅
  proof: by
  rw [interedges]; rw [Finset.empty_product]; rw [filter_empty]

中文:
定理 interedges_empty_left
  条件: (t : 有限集 β)
  结论: interedges r ∅ t = ∅
  证明: by
  rw [interedges]; rw [Finset.empty_product]; rw [filter_empty]

Depends on / 依赖: Finset, Finset.empty_product, empty_product, filter_empty, interedges
-/
theorem interedges_empty_left (t : Finset β) : interedges r ∅ t = ∅ := by
  rw [interedges]; rw [Finset.empty_product]; rw [filter_empty]

/--
theorem `interedges_mono` / 定理 `interedges_mono`

English:
theorem interedges_mono
  given: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁)
  statement: interedges r s₂ t₂ subseteq interedges r s₁ t₁
  proof: fun x => by
    simp_rw [mem_interedges_iff]
    exact fun h => ⟨hs h.1, ht h.2.1, h.2.2⟩

中文:
定理 interedges_mono
  条件: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁)
  结论: interedges r s₂ t₂ subseteq interedges r s₁ t₁
  证明: fun x => by
    simp_rw [mem_interedges_iff]
    exact fun h => ⟨hs h.1, ht h.2.1, h.2.2⟩

Depends on / 依赖: mem_interedges_iff, simp_rw
-/
theorem interedges_mono (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) : interedges r s₂ t₂ subseteq interedges r s₁ t₁ :=
  fun x => by
    simp_rw [mem_interedges_iff]
    exact fun h => ⟨hs h.1, ht h.2.1, h.2.2⟩

variable (r)

/--
theorem `card_interedges_add_card_interedges_compl` / 定理 `card_interedges_add_card_interedges_compl`

English:
theorem card_interedges_add_card_interedges_compl
  given: (s : Finset α) (t : Finset β)
  proof: by
  classical
  rw [← card_product]; rw [interedges]; rw [interedges]; rw [← card_union_of_disjoint]; rw [filter_union_filter_not_eq]
  exact disjoint_filter.2 fun _ _ => Classical.not_not.2

中文:
定理 card_interedges_add_card_interedges_compl
  条件: (s : 有限集 α) (t : 有限集 β)
  证明: by
  classical
  rw [← card_product]; rw [interedges]; rw [interedges]; rw [← card_union_of_disjoint]; rw [filter_union_filter_not_eq]
  exact disjoint_filter.2 fun _ _ => Classical.not_not.2

Depends on / 依赖: Classical, Classical.not_not, card_product, card_union_of_disjoint, classical, disjoint_filter, filter_union_filter_not_eq, interedges, not_not
-/
theorem card_interedges_add_card_interedges_compl (s : Finset α) (t : Finset β) :
    #(interedges r s t) + #(interedges (fun x y => ¬r x y) s t) = #s * #t := by
  classical
  rw [← card_product]; rw [interedges]; rw [interedges]; rw [← card_union_of_disjoint]; rw [filter_union_filter_not_eq]
  exact disjoint_filter.2 fun _ _ => Classical.not_not.2

/--
theorem `interedges_disjoint_left` / 定理 `interedges_disjoint_left`

English:
theorem interedges_disjoint_left
  given: {s s' : Finset α} (hs : Disjoint s s') (t : Finset β)
  proof: by
  rw [Finset.disjoint_left] at hs ⊢
  intro _ hx hy
  rw [mem_interedges_iff] at hx hy
  exact hs hx.1 hy.1

中文:
定理 interedges_disjoint_left
  条件: {s s' : 有限集 α} (hs : Disjoint s s') (t : 有限集 β)
  证明: by
  rw [Finset.disjoint_left] at hs ⊢
  intro _ hx hy
  rw [mem_interedges_iff] at hx hy
  exact hs hx.1 hy.1

Depends on / 依赖: Finset, Finset.disjoint_left, disjoint_left, mem_interedges_iff
-/
theorem interedges_disjoint_left {s s' : Finset α} (hs : Disjoint s s') (t : Finset β) :
    Disjoint (interedges r s t) (interedges r s' t) := by
  rw [Finset.disjoint_left] at hs ⊢
  intro _ hx hy
  rw [mem_interedges_iff] at hx hy
  exact hs hx.1 hy.1

/--
theorem `interedges_disjoint_right` / 定理 `interedges_disjoint_right`

English:
theorem interedges_disjoint_right
  given: (s : Finset α) {t t' : Finset β} (ht : Disjoint t t')
  proof: by
  rw [Finset.disjoint_left] at ht ⊢
  intro _ hx hy
  rw [mem_interedges_iff] at hx hy
  exact ht hx.2.1 hy.2.1

中文:
定理 interedges_disjoint_right
  条件: (s : 有限集 α) {t t' : 有限集 β} (ht : Disjoint t t')
  证明: by
  rw [Finset.disjoint_left] at ht ⊢
  intro _ hx hy
  rw [mem_interedges_iff] at hx hy
  exact ht hx.2.1 hy.2.1

Depends on / 依赖: Finset, Finset.disjoint_left, disjoint_left, mem_interedges_iff
-/
theorem interedges_disjoint_right (s : Finset α) {t t' : Finset β} (ht : Disjoint t t') :
    Disjoint (interedges r s t) (interedges r s t') := by
  rw [Finset.disjoint_left] at ht ⊢
  intro _ hx hy
  rw [mem_interedges_iff] at hx hy
  exact ht hx.2.1 hy.2.1

section DecidableEq

variable [DecidableEq α] [DecidableEq β]

/--
lemma `interedges_eq_biUnion` / 引理 `interedges_eq_biUnion`

English:
lemma interedges_eq_biUnion
  proof: by
  ext ⟨x, y⟩; simp [mem_interedges_iff]

中文:
引理 interedges_eq_biUnion
  证明: by
  ext ⟨x, y⟩; simp [mem_interedges_iff]

Depends on / 依赖: mem_interedges_iff
-/
lemma interedges_eq_biUnion :
    interedges r s t =
      s.biUnion fun x => {y in t | r x y}.map ⟨(x, ·), Prod.mk_right_injective x⟩ := by
  ext ⟨x, y⟩; simp [mem_interedges_iff]

/--
theorem `interedges_biUnion_left` / 定理 `interedges_biUnion_left`

English:
theorem interedges_biUnion_left
  given: (s : Finset ι) (t : Finset β) (f : ι -> Finset α)
  proof: by
  ext
  simp only [mem_biUnion, mem_interedges_iff, exists_and_right, ← and_assoc]

中文:
定理 interedges_biUnion_left
  条件: (s : 有限集 ι) (t : 有限集 β) (f : ι -> 有限集 α)
  证明: by
  ext
  simp only [mem_biUnion, mem_interedges_iff, exists_and_right, ← and_assoc]

Depends on / 依赖: and_assoc, exists_and_right, mem_biUnion, mem_interedges_iff
-/
theorem interedges_biUnion_left (s : Finset ι) (t : Finset β) (f : ι -> Finset α) :
    interedges r (s.biUnion f) t = s.biUnion fun a => interedges r (f a) t := by
  ext
  simp only [mem_biUnion, mem_interedges_iff, exists_and_right, ← and_assoc]

/--
theorem `interedges_biUnion_right` / 定理 `interedges_biUnion_right`

English:
theorem interedges_biUnion_right
  given: (s : Finset α) (t : Finset ι) (f : ι -> Finset β)
  proof: by
  ext a
  simp only [mem_interedges_iff, mem_biUnion]
  exact ⟨fun ⟨x₁, ⟨x₂, x₃, x₄⟩, x₅⟩ => ⟨x₂, x₃, x₁, x₄, x₅⟩,
    fun ⟨x₂, x₃, x₁, x₄, x₅⟩ => ⟨x₁, ⟨x₂, x₃, x₄⟩, x₅⟩⟩

中文:
定理 interedges_biUnion_right
  条件: (s : 有限集 α) (t : 有限集 ι) (f : ι -> 有限集 β)
  证明: by
  ext a
  simp only [mem_interedges_iff, mem_biUnion]
  exact ⟨fun ⟨x₁, ⟨x₂, x₃, x₄⟩, x₅⟩ => ⟨x₂, x₃, x₁, x₄, x₅⟩,
    fun ⟨x₂, x₃, x₁, x₄, x₅⟩ => ⟨x₁, ⟨x₂, x₃, x₄⟩, x₅⟩⟩

Depends on / 依赖: mem_biUnion, mem_interedges_iff
-/
theorem interedges_biUnion_right (s : Finset α) (t : Finset ι) (f : ι -> Finset β) :
    interedges r s (t.biUnion f) = t.biUnion fun b => interedges r s (f b) := by
  ext a
  simp only [mem_interedges_iff, mem_biUnion]
  exact ⟨fun ⟨x₁, ⟨x₂, x₃, x₄⟩, x₅⟩ => ⟨x₂, x₃, x₁, x₄, x₅⟩,
    fun ⟨x₂, x₃, x₁, x₄, x₅⟩ => ⟨x₁, ⟨x₂, x₃, x₄⟩, x₅⟩⟩

/--
theorem `interedges_biUnion` / 定理 `interedges_biUnion`

English:
theorem interedges_biUnion
  given: (s : Finset ι) (t : Finset κ) (f : ι -> Finset α) (g : κ -> Finset β)
  proof: by
  simp_rw [product_biUnion, interedges_biUnion_left, interedges_biUnion_right]

中文:
定理 interedges_biUnion
  条件: (s : 有限集 ι) (t : 有限集 κ) (f : ι -> 有限集 α) (g : κ -> 有限集 β)
  证明: by
  simp_rw [product_biUnion, interedges_biUnion_left, interedges_biUnion_right]

Depends on / 依赖: interedges_biUnion_left, interedges_biUnion_right, product_biUnion, simp_rw
-/
theorem interedges_biUnion (s : Finset ι) (t : Finset κ) (f : ι -> Finset α) (g : κ -> Finset β) :
    interedges r (s.biUnion f) (t.biUnion g) =
      (s ×ˢ t).biUnion fun ab => interedges r (f ab.1) (g ab.2) := by
  simp_rw [product_biUnion, interedges_biUnion_left, interedges_biUnion_right]

end DecidableEq

/--
theorem `card_interedges_le_mul` / 定理 `card_interedges_le_mul`

English:
theorem card_interedges_le_mul
  given: (s : Finset α) (t : Finset β)
  proof: (card_filter_le _ _).trans (card_product _ _).le

中文:
定理 card_interedges_le_mul
  条件: (s : 有限集 α) (t : 有限集 β)
  证明: (card_filter_le _ _).trans (card_product _ _).le

Depends on / 依赖: card_filter_le, card_product
-/
theorem card_interedges_le_mul (s : Finset α) (t : Finset β) :
    #(interedges r s t) <= #s * #t :=
  (card_filter_le _ _).trans (card_product _ _).le

/--
theorem `edgeDensity_nonneg` / 定理 `edgeDensity_nonneg`

English:
theorem edgeDensity_nonneg
  given: (s : Finset α) (t : Finset β)
  statement: 0 <= edgeDensity r s t
  proof: by
  apply div_nonneg <;> exact mod_cast Nat.zero_le _

中文:
定理 edgeDensity_nonneg
  条件: (s : 有限集 α) (t : 有限集 β)
  结论: 0 <= edgeDensity r s t
  证明: by
  apply div_nonneg <;> exact mod_cast Nat.zero_le _

Depends on / 依赖: Nat.zero_le, div_nonneg, mod_cast, zero_le
-/
theorem edgeDensity_nonneg (s : Finset α) (t : Finset β) : 0 <= edgeDensity r s t := by
  apply div_nonneg <;> exact mod_cast Nat.zero_le _

/--
theorem `edgeDensity_le_one` / 定理 `edgeDensity_le_one`

English:
theorem edgeDensity_le_one
  given: (s : Finset α) (t : Finset β)
  statement: edgeDensity r s t <= 1
  proof: by
  apply div_le_one_of_le₀
  · exact mod_cast card_interedges_le_mul r s t
  · exact mod_cast Nat.zero_le _

中文:
定理 edgeDensity_le_one
  条件: (s : 有限集 α) (t : 有限集 β)
  结论: edgeDensity r s t <= 1
  证明: by
  apply div_le_one_of_le₀
  · exact mod_cast card_interedges_le_mul r s t
  · exact mod_cast Nat.zero_le _

Depends on / 依赖: Nat.zero_le, card_interedges_le_mul, mod_cast, zero_le
-/
theorem edgeDensity_le_one (s : Finset α) (t : Finset β) : edgeDensity r s t <= 1 := by
  apply div_le_one_of_le₀
  · exact mod_cast card_interedges_le_mul r s t
  · exact mod_cast Nat.zero_le _

/--
theorem `edgeDensity_add_edgeDensity_compl` / 定理 `edgeDensity_add_edgeDensity_compl`

English:
theorem edgeDensity_add_edgeDensity_compl
  given: (hs : s.Nonempty) (ht : t.Nonempty)
  proof: by
  rw [edgeDensity]; rw [edgeDensity]; rw [← add_div]; rw [div_eq_one_iff_eq]
  · exact mod_cast card_interedges_add_card_interedges_compl r s t
  · exact mod_cast (mul_pos hs.card_pos ht.card_pos).ne'

@[simp]

中文:
定理 edgeDensity_add_edgeDensity_compl
  条件: (hs : s.非空) (ht : t.非空)
  证明: by
  rw [edgeDensity]; rw [edgeDensity]; rw [← add_div]; rw [div_eq_one_iff_eq]
  · exact mod_cast card_interedges_add_card_interedges_compl r s t
  · exact mod_cast (mul_pos hs.card_pos ht.card_pos).ne'

@[simp]

Depends on / 依赖: add_div, card_interedges_add_card_interedges_compl, card_pos, div_eq_one_iff_eq, edgeDensity, hs.card_pos, ht.card_pos, mod_cast, mul_pos
-/
theorem edgeDensity_add_edgeDensity_compl (hs : s.Nonempty) (ht : t.Nonempty) :
    edgeDensity r s t + edgeDensity (fun x y => ¬r x y) s t = 1 := by
  rw [edgeDensity]; rw [edgeDensity]; rw [← add_div]; rw [div_eq_one_iff_eq]
  · exact mod_cast card_interedges_add_card_interedges_compl r s t
  · exact mod_cast (mul_pos hs.card_pos ht.card_pos).ne'

@[simp]
/--
theorem `edgeDensity_empty_left` / 定理 `edgeDensity_empty_left`

English:
theorem edgeDensity_empty_left
  given: (t : Finset β)
  statement: edgeDensity r ∅ t = 0
  proof: by
  rw [edgeDensity]; rw [Finset.card_empty]; rw [Nat.cast_zero]; rw [zero_mul]; rw [div_zero]

@[simp]

中文:
定理 edgeDensity_empty_left
  条件: (t : 有限集 β)
  结论: edgeDensity r ∅ t = 0
  证明: by
  rw [edgeDensity]; rw [Finset.card_empty]; rw [Nat.cast_zero]; rw [zero_mul]; rw [div_zero]

@[simp]

Depends on / 依赖: Finset, Finset.card_empty, Nat.cast_zero, card_empty, cast_zero, div_zero, edgeDensity, zero_mul
-/
theorem edgeDensity_empty_left (t : Finset β) : edgeDensity r ∅ t = 0 := by
  rw [edgeDensity]; rw [Finset.card_empty]; rw [Nat.cast_zero]; rw [zero_mul]; rw [div_zero]

@[simp]
/--
theorem `edgeDensity_empty_right` / 定理 `edgeDensity_empty_right`

English:
theorem edgeDensity_empty_right
  given: (s : Finset α)
  statement: edgeDensity r s ∅ = 0
  proof: by
  rw [edgeDensity]; rw [Finset.card_empty]; rw [Nat.cast_zero]; rw [mul_zero]; rw [div_zero]

中文:
定理 edgeDensity_empty_right
  条件: (s : 有限集 α)
  结论: edgeDensity r s ∅ = 0
  证明: by
  rw [edgeDensity]; rw [Finset.card_empty]; rw [Nat.cast_zero]; rw [mul_zero]; rw [div_zero]

Depends on / 依赖: Finset, Finset.card_empty, Nat.cast_zero, card_empty, cast_zero, div_zero, edgeDensity, mul_zero
-/
theorem edgeDensity_empty_right (s : Finset α) : edgeDensity r s ∅ = 0 := by
  rw [edgeDensity]; rw [Finset.card_empty]; rw [Nat.cast_zero]; rw [mul_zero]; rw [div_zero]

/--
theorem `card_interedges_finpartition_left` / 定理 `card_interedges_finpartition_left`

English:
theorem card_interedges_finpartition_left
  given: [DecidableEq α] (P : Finpartition s) (t : Finset β)
  proof: by
  classical
  simp_rw [← P.biUnion_parts, interedges_biUnion_left, id]
  rw [card_biUnion]
  exact fun x hx y hy h => interedges_disjoint_left r (P.disjoint hx hy h) _

中文:
定理 card_interedges_finpartition_left
  条件: [DecidableEq α] (P : 有限分拆 s) (t : 有限集 β)
  证明: by
  classical
  simp_rw [← P.biUnion_parts, interedges_biUnion_left, id]
  rw [card_biUnion]
  exact fun x hx y hy h => interedges_disjoint_left r (P.disjoint hx hy h) _

Depends on / 依赖: P.biUnion_parts, P.disjoint, biUnion_parts, card_biUnion, classical, disjoint, interedges_biUnion_left, interedges_disjoint_left, simp_rw
-/
theorem card_interedges_finpartition_left [DecidableEq α] (P : Finpartition s) (t : Finset β) :
    #(interedges r s t) = ∑ a in P.parts, #(interedges r a t) := by
  classical
  simp_rw [← P.biUnion_parts, interedges_biUnion_left, id]
  rw [card_biUnion]
  exact fun x hx y hy h => interedges_disjoint_left r (P.disjoint hx hy h) _

/--
theorem `card_interedges_finpartition_right` / 定理 `card_interedges_finpartition_right`

English:
theorem card_interedges_finpartition_right
  given: [DecidableEq β] (s : Finset α) (P : Finpartition t)
  proof: by
  classical
  simp_rw [← P.biUnion_parts, interedges_biUnion_right, id]
  rw [card_biUnion]
  exact fun x hx y hy h => interedges_disjoint_right r _ (P.disjoint hx hy h)

中文:
定理 card_interedges_finpartition_right
  条件: [DecidableEq β] (s : 有限集 α) (P : 有限分拆 t)
  证明: by
  classical
  simp_rw [← P.biUnion_parts, interedges_biUnion_right, id]
  rw [card_biUnion]
  exact fun x hx y hy h => interedges_disjoint_right r _ (P.disjoint hx hy h)

Depends on / 依赖: P.biUnion_parts, P.disjoint, biUnion_parts, card_biUnion, classical, disjoint, interedges_biUnion_right, interedges_disjoint_right, simp_rw
-/
theorem card_interedges_finpartition_right [DecidableEq β] (s : Finset α) (P : Finpartition t) :
    #(interedges r s t) = ∑ b in P.parts, #(interedges r s b) := by
  classical
  simp_rw [← P.biUnion_parts, interedges_biUnion_right, id]
  rw [card_biUnion]
  exact fun x hx y hy h => interedges_disjoint_right r _ (P.disjoint hx hy h)

/--
theorem `card_interedges_finpartition` / 定理 `card_interedges_finpartition`

English:
theorem card_interedges_finpartition
  statement: [DecidableEq α] [DecidableEq β] (P : Finpartition s)
  proof: by
  rw [card_interedges_finpartition_left _ P]; rw [sum_product]
  congr; ext
  rw [card_interedges_finpartition_right]

中文:
定理 card_interedges_finpartition
  结论: [DecidableEq α] [DecidableEq β] (P : 有限分拆 s)
  证明: by
  rw [card_interedges_finpartition_left _ P]; rw [sum_product]
  congr; ext
  rw [card_interedges_finpartition_right]

Depends on / 依赖: card_interedges_finpartition_left, card_interedges_finpartition_right, sum_product
-/
theorem card_interedges_finpartition [DecidableEq α] [DecidableEq β] (P : Finpartition s)
    (Q : Finpartition t) :
    #(interedges r s t) = ∑ ab in P.parts ×ˢ Q.parts, #(interedges r ab.1 ab.2) := by
  rw [card_interedges_finpartition_left _ P]; rw [sum_product]
  congr; ext
  rw [card_interedges_finpartition_right]

/--
theorem `mul_edgeDensity_le_edgeDensity` / 定理 `mul_edgeDensity_le_edgeDensity`

English:
theorem mul_edgeDensity_le_edgeDensity
  statement: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hs₂ : s₂.Nonempty)
  proof: by
  have hst : (#s₂ : Rat) * #t₂ != 0 := by simp [hs₂.ne_empty, ht₂.ne_empty]
  rw [edgeDensity]; rw [edgeDensity]; rw [div_mul_div_comm]; rw [mul_comm]; rw [div_mul_div_cancel₀ hst]
  gcongr
  exact interedges_mono hs ht

中文:
定理 mul_edgeDensity_le_edgeDensity
  结论: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hs₂ : s₂.非空)
  证明: by
  have hst : (#s₂ : Rat) * #t₂ != 0 := by simp [hs₂.ne_empty, ht₂.ne_empty]
  rw [edgeDensity]; rw [edgeDensity]; rw [div_mul_div_comm]; rw [mul_comm]; rw [div_mul_div_cancel₀ hst]
  gcongr
  exact interedges_mono hs ht

Depends on / 依赖: div_mul_div_comm, edgeDensity, interedges_mono, mul_comm, ne_empty
-/
theorem mul_edgeDensity_le_edgeDensity (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hs₂ : s₂.Nonempty)
    (ht₂ : t₂.Nonempty) :
    (#s₂ : Rat) / #s₁ * (#t₂ / #t₁) * edgeDensity r s₂ t₂ <= edgeDensity r s₁ t₁ := by
  have hst : (#s₂ : Rat) * #t₂ != 0 := by simp [hs₂.ne_empty, ht₂.ne_empty]
  rw [edgeDensity]; rw [edgeDensity]; rw [div_mul_div_comm]; rw [mul_comm]; rw [div_mul_div_cancel₀ hst]
  gcongr
  exact interedges_mono hs ht

/--
theorem `edgeDensity_sub_edgeDensity_le_one_sub_mul` / 定理 `edgeDensity_sub_edgeDensity_le_one_sub_mul`

English:
theorem edgeDensity_sub_edgeDensity_le_one_sub_mul
  statement: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hs₂ : s₂.Nonempty)
  proof: by
  refine (sub_le_sub_left (mul_edgeDensity_le_edgeDensity r hs ht hs₂ ht₂) _).trans ?_
  refine le_trans ?_ (mul_le_of_le_one_right ?_ (edgeDensity_le_one r s₂ t₂))
  · rw [sub_mul, one_mul]
  refine sub_nonneg_of_le (mul_le_one₀ ?_ ?_ ?_)
  · exact div_le_one_of_le₀ ((@Nat.cast_le Rat).2 (card_le_card hs)) (Nat.cast_nonneg _)
  · apply div_nonneg <;> exact mod_cast Nat.zero_le _
  · exact div_le_one_of_le₀ ((@Nat.cast_le Rat).2 (card_le_card ht)) (Nat.cast_nonneg _)

中文:
定理 edgeDensity_sub_edgeDensity_le_one_sub_mul
  结论: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hs₂ : s₂.非空)
  证明: by
  refine (sub_le_sub_left (mul_edgeDensity_le_edgeDensity r hs ht hs₂ ht₂) _).trans ?_
  refine le_trans ?_ (mul_le_of_le_one_right ?_ (edgeDensity_le_one r s₂ t₂))
  · rw [sub_mul, one_mul]
  refine sub_nonneg_of_le (mul_le_one₀ ?_ ?_ ?_)
  · exact div_le_one_of_le₀ ((@Nat.cast_le Rat).2 (card_le_card hs)) (Nat.cast_nonneg _)
  · apply div_nonneg <;> exact mod_cast Nat.zero_le _
  · exact div_le_one_of_le₀ ((@Nat.cast_le Rat).2 (card_le_card ht)) (Nat.cast_nonneg _)

Depends on / 依赖: Nat.cast_le, Nat.cast_nonneg, Nat.zero_le, card_le_card, cast_le, cast_nonneg, div_nonneg, edgeDensity_le_one, le_trans, mod_cast, mul_edgeDensity_le_edgeDensity, mul_le_of_le_one_right, one_mul, sub_le_sub_left, sub_mul, sub_nonneg_of_le, zero_le
-/
theorem edgeDensity_sub_edgeDensity_le_one_sub_mul (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hs₂ : s₂.Nonempty)
    (ht₂ : t₂.Nonempty) :
    edgeDensity r s₂ t₂ - edgeDensity r s₁ t₁ <= 1 - #s₂ / #s₁ * (#t₂ / #t₁) := by
  refine (sub_le_sub_left (mul_edgeDensity_le_edgeDensity r hs ht hs₂ ht₂) _).trans ?_
  refine le_trans ?_ (mul_le_of_le_one_right ?_ (edgeDensity_le_one r s₂ t₂))
  · rw [sub_mul, one_mul]
  refine sub_nonneg_of_le (mul_le_one₀ ?_ ?_ ?_)
  · exact div_le_one_of_le₀ ((@Nat.cast_le Rat).2 (card_le_card hs)) (Nat.cast_nonneg _)
  · apply div_nonneg <;> exact mod_cast Nat.zero_le _
  · exact div_le_one_of_le₀ ((@Nat.cast_le Rat).2 (card_le_card ht)) (Nat.cast_nonneg _)

/--
theorem `abs_edgeDensity_sub_edgeDensity_le_one_sub_mul` / 定理 `abs_edgeDensity_sub_edgeDensity_le_one_sub_mul`

English:
theorem abs_edgeDensity_sub_edgeDensity_le_one_sub_mul
  statement: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁)
  proof: by
  refine abs_sub_le_iff.2 ⟨edgeDensity_sub_edgeDensity_le_one_sub_mul r hs ht hs₂ ht₂, ?_⟩
  rw [← add_sub_cancel_right (edgeDensity r s₁ t₁) (edgeDensity (fun x y => ¬r x y) s₁ t₁)]; rw [← add_sub_cancel_right (edgeDensity r s₂ t₂) (edgeDensity (fun x y => ¬r x y) s₂ t₂)]; rw [edgeDensity_add_edgeDensity_compl _ (hs₂.mono hs) (ht₂.mono ht)]; rw [edgeDensity_add_edgeDensity_compl _ hs₂ ht₂]; rw [sub_sub_sub_cancel_left]
  exact edgeDensity_sub_edgeDensity_le_one_sub_mul _ hs ht hs₂ ht₂

中文:
定理 abs_edgeDensity_sub_edgeDensity_le_one_sub_mul
  结论: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁)
  证明: by
  refine abs_sub_le_iff.2 ⟨edgeDensity_sub_edgeDensity_le_one_sub_mul r hs ht hs₂ ht₂, ?_⟩
  rw [← add_sub_cancel_right (edgeDensity r s₁ t₁) (edgeDensity (fun x y => ¬r x y) s₁ t₁)]; rw [← add_sub_cancel_right (edgeDensity r s₂ t₂) (edgeDensity (fun x y => ¬r x y) s₂ t₂)]; rw [edgeDensity_add_edgeDensity_compl _ (hs₂.mono hs) (ht₂.mono ht)]; rw [edgeDensity_add_edgeDensity_compl _ hs₂ ht₂]; rw [sub_sub_sub_cancel_left]
  exact edgeDensity_sub_edgeDensity_le_one_sub_mul _ hs ht hs₂ ht₂

Depends on / 依赖: abs_sub_le_iff, add_sub_cancel_right, edgeDensity, edgeDensity_add_edgeDensity_compl, edgeDensity_sub_edgeDensity_le_one_sub_mul, sub_sub_sub_cancel_left
-/
theorem abs_edgeDensity_sub_edgeDensity_le_one_sub_mul (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁)
    (hs₂ : s₂.Nonempty) (ht₂ : t₂.Nonempty) :
    |edgeDensity r s₂ t₂ - edgeDensity r s₁ t₁| <= 1 - #s₂ / #s₁ * (#t₂ / #t₁) := by
  refine abs_sub_le_iff.2 ⟨edgeDensity_sub_edgeDensity_le_one_sub_mul r hs ht hs₂ ht₂, ?_⟩
  rw [← add_sub_cancel_right (edgeDensity r s₁ t₁) (edgeDensity (fun x y => ¬r x y) s₁ t₁)]; rw [← add_sub_cancel_right (edgeDensity r s₂ t₂) (edgeDensity (fun x y => ¬r x y) s₂ t₂)]; rw [edgeDensity_add_edgeDensity_compl _ (hs₂.mono hs) (ht₂.mono ht)]; rw [edgeDensity_add_edgeDensity_compl _ hs₂ ht₂]; rw [sub_sub_sub_cancel_left]
  exact edgeDensity_sub_edgeDensity_le_one_sub_mul _ hs ht hs₂ ht₂

/--
theorem `abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq` / 定理 `abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq`

English:
theorem abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq
  statement: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁)
  proof: by
  have hδ' : 0 <= 2 * δ - δ ^ 2 := by
    rw [sub_nonneg]; rw [sq]
    gcongr
    exact hδ₁.le.trans (by simp)
  rw [← sub_pos] at hδ₁
  obtain rfl | hs₂' := s₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zero] at hs₂
    simpa [edgeDensity, (nonpos_of_mul_nonpos_right hs₂ hδ₁).antisymm (Nat.cast_nonneg _)] using hδ'
  obtain rfl | ht₂' := t₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zero] at ht₂
    simpa [edgeDensity, (nonpos_of_mul_nonpos_right ht₂ hδ₁).antisymm (Nat.cast_nonneg _)] using hδ'
  have hr : 2 * δ - δ ^ 2 = 1 - (1 - δ) * (1 - δ) := by ring
  rw [hr]
  norm_cast
  refine
    (Rat.cast_le.2 <| abs_edgeDensity_sub_edgeDensity_le_one_sub_mul r hs ht hs₂' ht₂').trans ?_
  push_cast
  have h₁ := hs₂'.mono hs
  have h₂ := ht₂'.mono ht
  gcongr
  · refine (le_div_iff₀ ?_).2 hs₂
    exact mod_cast h₁.card_pos
  · refine (le_div_iff₀ ?_).2 ht₂
    exact mod_cast h₂.card_pos

中文:
定理 abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq
  结论: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁)
  证明: by
  have hδ' : 0 <= 2 * δ - δ ^ 2 := by
    rw [sub_nonneg]; rw [sq]
    gcongr
    exact hδ₁.le.trans (by simp)
  rw [← sub_pos] at hδ₁
  obtain rfl | hs₂' := s₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zero] at hs₂
    simpa [edgeDensity, (nonpos_of_mul_nonpos_right hs₂ hδ₁).antisymm (Nat.cast_nonneg _)] using hδ'
  obtain rfl | ht₂' := t₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zero] at ht₂
    simpa [edgeDensity, (nonpos_of_mul_nonpos_right ht₂ hδ₁).antisymm (Nat.cast_nonneg _)] using hδ'
  have hr : 2 * δ - δ ^ 2 = 1 - (1 - δ) * (1 - δ) := by ring
  rw [hr]
  norm_cast
  refine
    (Rat.cast_le.2 <| abs_edgeDensity_sub_edgeDensity_le_one_sub_mul r hs ht hs₂' ht₂').trans ?_
  push_cast
  have h₁ := hs₂'.mono hs
  have h₂ := ht₂'.mono ht
  gcongr
  · refine (le_div_iff₀ ?_).2 hs₂
    exact mod_cast h₁.card_pos
  · refine (le_div_iff₀ ?_).2 ht₂
    exact mod_cast h₂.card_pos

Depends on / 依赖: Finset, Finset.card_empty, Nat.cast_nonneg, Nat.cast_zero, antisymm, card_empty, cast_nonneg, cast_zero, edgeDensity, eq_empty_or_nonempty, le.trans, nonpos_of_mul_nonpos_right, sub_nonneg, sub_pos
-/
theorem abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁)
    (hδ₀ : 0 <= δ) (hδ₁ : δ < 1) (hs₂ : (1 - δ) * #s₁ <= #s₂)
    (ht₂ : (1 - δ) * #t₁ <= #t₂) :
    |(edgeDensity r s₂ t₂ : 𝕜) - edgeDensity r s₁ t₁| <= 2 * δ - δ ^ 2 := by
  have hδ' : 0 <= 2 * δ - δ ^ 2 := by
    rw [sub_nonneg]; rw [sq]
    gcongr
    exact hδ₁.le.trans (by simp)
  rw [← sub_pos] at hδ₁
  obtain rfl | hs₂' := s₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zero] at hs₂
    simpa [edgeDensity, (nonpos_of_mul_nonpos_right hs₂ hδ₁).antisymm (Nat.cast_nonneg _)] using hδ'
  obtain rfl | ht₂' := t₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zero] at ht₂
    simpa [edgeDensity, (nonpos_of_mul_nonpos_right ht₂ hδ₁).antisymm (Nat.cast_nonneg _)] using hδ'
  have hr : 2 * δ - δ ^ 2 = 1 - (1 - δ) * (1 - δ) := by ring
  rw [hr]
  norm_cast
  refine
    (Rat.cast_le.2 <| abs_edgeDensity_sub_edgeDensity_le_one_sub_mul r hs ht hs₂' ht₂').trans ?_
  push_cast
  have h₁ := hs₂'.mono hs
  have h₂ := ht₂'.mono ht
  gcongr
  · refine (le_div_iff₀ ?_).2 hs₂
    exact mod_cast h₁.card_pos
  · refine (le_div_iff₀ ?_).2 ht₂
    exact mod_cast h₂.card_pos

/--
theorem `abs_edgeDensity_sub_edgeDensity_le_two_mul` / 定理 `abs_edgeDensity_sub_edgeDensity_le_two_mul`

English:
theorem abs_edgeDensity_sub_edgeDensity_le_two_mul
  statement: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hδ : 0 <= δ)
  proof: by
  rcases lt_or_ge δ 1 with h | h
  · exact (abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq r hs ht hδ h hscard htcard).trans
      ((sub_le_self_iff _).2 <| sq_nonneg δ)
  rw [two_mul]
  refine (abs_sub _ _).trans (add_le_add (le_trans ?_ h) (le_trans ?_ h)) <;>
    · rw [abs_of_nonneg]
      · exact mod_cast edgeDensity_le_one r _ _
      · exact mod_cast edgeDensity_nonneg r _ _

中文:
定理 abs_edgeDensity_sub_edgeDensity_le_two_mul
  结论: (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hδ : 0 <= δ)
  证明: by
  rcases lt_or_ge δ 1 with h | h
  · exact (abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq r hs ht hδ h hscard htcard).trans
      ((sub_le_self_iff _).2 <| sq_nonneg δ)
  rw [two_mul]
  refine (abs_sub _ _).trans (add_le_add (le_trans ?_ h) (le_trans ?_ h)) <;>
    · rw [abs_of_nonneg]
      · exact mod_cast edgeDensity_le_one r _ _
      · exact mod_cast edgeDensity_nonneg r _ _

Depends on / 依赖: abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq, abs_of_nonneg, abs_sub, add_le_add, edgeDensity_le_one, edgeDensity_nonneg, hscard, htcard, le_trans, lt_or_ge, mod_cast, sq_nonneg, sub_le_self_iff, two_mul
-/
theorem abs_edgeDensity_sub_edgeDensity_le_two_mul (hs : s₂ subseteq s₁) (ht : t₂ subseteq t₁) (hδ : 0 <= δ)
    (hscard : (1 - δ) * #s₁ <= #s₂) (htcard : (1 - δ) * #t₁ <= #t₂) :
    |(edgeDensity r s₂ t₂ : 𝕜) - edgeDensity r s₁ t₁| <= 2 * δ := by
  rcases lt_or_ge δ 1 with h | h
  · exact (abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq r hs ht hδ h hscard htcard).trans
      ((sub_le_self_iff _).2 <| sq_nonneg δ)
  rw [two_mul]
  refine (abs_sub _ _).trans (add_le_add (le_trans ?_ h) (le_trans ?_ h)) <;>
    · rw [abs_of_nonneg]
      · exact mod_cast edgeDensity_le_one r _ _
      · exact mod_cast edgeDensity_nonneg r _ _

end Asymmetric

section Symmetric

variable {r : α -> α -> Prop} [DecidableRel r] {s t : Finset α} {a b : α}

@[simp]
/--
theorem `swap_mem_interedges_iff` / 定理 `swap_mem_interedges_iff`

English:
theorem swap_mem_interedges_iff
  given: [Std.Symm r] {x : α × α}
  proof: by
  rw [mem_interedges_iff]; rw [mem_interedges_iff]; rw [Std.Symm.iff (r := r)]
  exact and_left_comm

中文:
定理 swap_mem_interedges_iff
  条件: [Std.Symm r] {x : α × α}
  证明: by
  rw [mem_interedges_iff]; rw [mem_interedges_iff]; rw [Std.Symm.iff (r := r)]
  exact and_left_comm

Depends on / 依赖: Std.Symm.iff, and_left_comm, mem_interedges_iff
-/
theorem swap_mem_interedges_iff [Std.Symm r] {x : α × α} :
    x.swap in interedges r s t ↔ x in interedges r t s := by
  rw [mem_interedges_iff]; rw [mem_interedges_iff]; rw [Std.Symm.iff (r := r)]
  exact and_left_comm

/--
theorem `mk_mem_interedges_comm` / 定理 `mk_mem_interedges_comm`

English:
theorem mk_mem_interedges_comm
  given: [Std.Symm r]
  proof: swap_mem_interedges_iff (x := (b, a))

中文:
定理 mk_mem_interedges_comm
  条件: [Std.Symm r]
  证明: swap_mem_interedges_iff (x := (b, a))

Depends on / 依赖: swap_mem_interedges_iff
-/
theorem mk_mem_interedges_comm [Std.Symm r] :
    (a, b) in interedges r s t ↔ (b, a) in interedges r t s :=
  swap_mem_interedges_iff (x := (b, a))

/--
theorem `card_interedges_comm` / 定理 `card_interedges_comm`

English:
theorem card_interedges_comm
  given: [Std.Symm r] (s t : Finset α)
  proof: Finset.card_bij (fun (x : α × α) _ => x.swap) (fun _ => swap_mem_interedges_iff.mpr)
    (fun _ _ _ _ h => Prod.swap_injective h) fun x h =>
    ⟨x.swap, swap_mem_interedges_iff.mpr h, x.swap_swap⟩

中文:
定理 card_interedges_comm
  条件: [Std.Symm r] (s t : 有限集 α)
  证明: Finset.card_bij (fun (x : α × α) _ => x.swap) (fun _ => swap_mem_interedges_iff.mpr)
    (fun _ _ _ _ h => Prod.swap_injective h) fun x h =>
    ⟨x.swap, swap_mem_interedges_iff.mpr h, x.swap_swap⟩

Depends on / 依赖: Finset, Finset.card_bij, Prod.swap_injective, card_bij, swap_injective, swap_mem_interedges_iff, swap_mem_interedges_iff.mpr, swap_swap, x.swap, x.swap_swap
-/
theorem card_interedges_comm [Std.Symm r] (s t : Finset α) :
    #(interedges r s t) = #(interedges r t s) :=
  Finset.card_bij (fun (x : α × α) _ => x.swap) (fun _ => swap_mem_interedges_iff.mpr)
    (fun _ _ _ _ h => Prod.swap_injective h) fun x h =>
    ⟨x.swap, swap_mem_interedges_iff.mpr h, x.swap_swap⟩

/--
theorem `edgeDensity_comm` / 定理 `edgeDensity_comm`

English:
theorem edgeDensity_comm
  given: [Std.Symm r] (s t : Finset α)
  proof: by
  rw [edgeDensity]; rw [mul_comm]; rw [card_interedges_comm]; rw [edgeDensity]

中文:
定理 edgeDensity_comm
  条件: [Std.Symm r] (s t : 有限集 α)
  证明: by
  rw [edgeDensity]; rw [mul_comm]; rw [card_interedges_comm]; rw [edgeDensity]

Depends on / 依赖: card_interedges_comm, edgeDensity, mul_comm
-/
theorem edgeDensity_comm [Std.Symm r] (s t : Finset α) :
    edgeDensity r s t = edgeDensity r t s := by
  rw [edgeDensity]; rw [mul_comm]; rw [card_interedges_comm]; rw [edgeDensity]

end Symmetric

end Rel

open Rel

/-! ### Density of a graph -/


namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] {s s₁ s₂ t t₁ t₂ : Finset α} {a b : α}

/--
Definition of `interedges` / `interedges` 的定义

English:
definition interedges
  signature: (s t : Finset α)
  body: Rel.interedges G.Adj s t

中文:
定义 interedges
  签名: (s t : 有限集 α)
  定义体: Rel.interedges G.Adj s t

Depends on / 依赖: G.Adj, Rel.interedges, interedges
-/
def interedges (s t : Finset α) : Finset (α × α) :=
  Rel.interedges G.Adj s t

/--
Definition of `edgeDensity` / `edgeDensity` 的定义

English:
definition edgeDensity
  signature: : Finset α -> Finset α -> Rat
  body: Rel.edgeDensity G.Adj

中文:
定义 edgeDensity
  签名: : 有限集 α -> 有限集 α -> 有理数
  定义体: Rel.edgeDensity G.Adj

Depends on / 依赖: G.Adj, Rel.edgeDensity, edgeDensity
-/
def edgeDensity : Finset α -> Finset α -> Rat :=
  Rel.edgeDensity G.Adj

/--
lemma `interedges_def` / 引理 `interedges_def`

English:
lemma interedges_def
  given: (s t : Finset α)
  statement: G.interedges s t = {e in s ×ˢ t | G.Adj e.1 e.2}
  proof: rfl

中文:
引理 interedges_def
  条件: (s t : 有限集 α)
  结论: G.interedges s t = {e in s ×ˢ t | G.伴随 e.1 e.2}
  证明: rfl
-/
lemma interedges_def (s t : Finset α) : G.interedges s t = {e in s ×ˢ t | G.Adj e.1 e.2} := rfl

/--
lemma `edgeDensity_def` / 引理 `edgeDensity_def`

English:
lemma edgeDensity_def
  given: (s t : Finset α)
  statement: G.edgeDensity s t = #(G.interedges s t) / (#s * #t)
  proof: rfl

中文:
引理 edgeDensity_def
  条件: (s t : 有限集 α)
  结论: G.edgeDensity s t = #(G.interedges s t) / (#s * #t)
  证明: rfl
-/
lemma edgeDensity_def (s t : Finset α) : G.edgeDensity s t = #(G.interedges s t) / (#s * #t) := rfl

/--
theorem `card_interedges_div_card` / 定理 `card_interedges_div_card`

English:
theorem card_interedges_div_card
  given: (s t : Finset α)
  proof: rfl

中文:
定理 card_interedges_div_card
  条件: (s t : 有限集 α)
  证明: rfl
-/
theorem card_interedges_div_card (s t : Finset α) :
    (#(G.interedges s t) : Rat) / (#s * #t) = G.edgeDensity s t :=
  rfl

/--
theorem `mem_interedges_iff` / 定理 `mem_interedges_iff`

English:
theorem mem_interedges_iff
  given: {x : α × α}
  statement: x in G.interedges s t ↔ x.1 in s ∧ x.2 in t ∧ G.Adj x.1 x.2
  proof: Rel.mem_interedges_iff

中文:
定理 mem_interedges_iff
  条件: {x : α × α}
  结论: x in G.interedges s t ↔ x.1 in s ∧ x.2 in t ∧ G.伴随 x.1 x.2
  证明: Rel.mem_interedges_iff

Depends on / 依赖: Rel.mem_interedges_iff, mem_interedges_iff
-/
theorem mem_interedges_iff {x : α × α} : x in G.interedges s t ↔ x.1 in s ∧ x.2 in t ∧ G.Adj x.1 x.2 :=
  Rel.mem_interedges_iff

/--
theorem `mk_mem_interedges_iff` / 定理 `mk_mem_interedges_iff`

English:
theorem mk_mem_interedges_iff
  statement: (a, b) in G.interedges s t ↔ a in s ∧ b in t ∧ G.Adj a b
  proof: Rel.mk_mem_interedges_iff

@[simp]

中文:
定理 mk_mem_interedges_iff
  结论: (a, b) in G.interedges s t ↔ a in s ∧ b in t ∧ G.伴随 a b
  证明: Rel.mk_mem_interedges_iff

@[simp]

Depends on / 依赖: Rel.mk_mem_interedges_iff, mk_mem_interedges_iff
-/
theorem mk_mem_interedges_iff : (a, b) in G.interedges s t ↔ a in s ∧ b in t ∧ G.Adj a b :=
  Rel.mk_mem_interedges_iff

@[simp]
/--
theorem `interedges_empty_left` / 定理 `interedges_empty_left`

English:
theorem interedges_empty_left
  given: (t : Finset α)
  statement: G.interedges ∅ t = ∅
  proof: Rel.interedges_empty_left _

中文:
定理 interedges_empty_left
  条件: (t : 有限集 α)
  结论: G.interedges ∅ t = ∅
  证明: Rel.interedges_empty_left _

Depends on / 依赖: Rel.interedges_empty_left, interedges_empty_left
-/
theorem interedges_empty_left (t : Finset α) : G.interedges ∅ t = ∅ :=
  Rel.interedges_empty_left _

/--
theorem `interedges_mono` / 定理 `interedges_mono`

English:
theorem interedges_mono
  statement: s₂ subseteq s₁ -> t₂ subseteq t₁ -> G.interedges s₂ t₂ subseteq G.interedges s₁ t₁
  proof: Rel.interedges_mono

中文:
定理 interedges_mono
  结论: s₂ subseteq s₁ -> t₂ subseteq t₁ -> G.interedges s₂ t₂ subseteq G.interedges s₁ t₁
  证明: Rel.interedges_mono

Depends on / 依赖: Rel.interedges_mono, interedges_mono
-/
theorem interedges_mono : s₂ subseteq s₁ -> t₂ subseteq t₁ -> G.interedges s₂ t₂ subseteq G.interedges s₁ t₁ :=
  Rel.interedges_mono

/--
theorem `interedges_disjoint_left` / 定理 `interedges_disjoint_left`

English:
theorem interedges_disjoint_left
  given: (hs : Disjoint s₁ s₂) (t : Finset α)
  proof: Rel.interedges_disjoint_left _ hs _

中文:
定理 interedges_disjoint_left
  条件: (hs : Disjoint s₁ s₂) (t : 有限集 α)
  证明: Rel.interedges_disjoint_left _ hs _

Depends on / 依赖: Rel.interedges_disjoint_left, interedges_disjoint_left
-/
theorem interedges_disjoint_left (hs : Disjoint s₁ s₂) (t : Finset α) :
    Disjoint (G.interedges s₁ t) (G.interedges s₂ t) :=
  Rel.interedges_disjoint_left _ hs _

/--
theorem `interedges_disjoint_right` / 定理 `interedges_disjoint_right`

English:
theorem interedges_disjoint_right
  given: (s : Finset α) (ht : Disjoint t₁ t₂)
  proof: Rel.interedges_disjoint_right _ _ ht

中文:
定理 interedges_disjoint_right
  条件: (s : 有限集 α) (ht : Disjoint t₁ t₂)
  证明: Rel.interedges_disjoint_right _ _ ht

Depends on / 依赖: Rel.interedges_disjoint_right, interedges_disjoint_right
-/
theorem interedges_disjoint_right (s : Finset α) (ht : Disjoint t₁ t₂) :
    Disjoint (G.interedges s t₁) (G.interedges s t₂) :=
  Rel.interedges_disjoint_right _ _ ht

section DecidableEq

variable [DecidableEq α]

/--
theorem `interedges_biUnion_left` / 定理 `interedges_biUnion_left`

English:
theorem interedges_biUnion_left
  given: (s : Finset ι) (t : Finset α) (f : ι -> Finset α)
  proof: Rel.interedges_biUnion_left _ _ _ _

中文:
定理 interedges_biUnion_left
  条件: (s : 有限集 ι) (t : 有限集 α) (f : ι -> 有限集 α)
  证明: Rel.interedges_biUnion_left _ _ _ _

Depends on / 依赖: Rel.interedges_biUnion_left, interedges_biUnion_left
-/
theorem interedges_biUnion_left (s : Finset ι) (t : Finset α) (f : ι -> Finset α) :
    G.interedges (s.biUnion f) t = s.biUnion fun a => G.interedges (f a) t :=
  Rel.interedges_biUnion_left _ _ _ _

/--
theorem `interedges_biUnion_right` / 定理 `interedges_biUnion_right`

English:
theorem interedges_biUnion_right
  given: (s : Finset α) (t : Finset ι) (f : ι -> Finset α)
  proof: Rel.interedges_biUnion_right _ _ _ _

中文:
定理 interedges_biUnion_right
  条件: (s : 有限集 α) (t : 有限集 ι) (f : ι -> 有限集 α)
  证明: Rel.interedges_biUnion_right _ _ _ _

Depends on / 依赖: Rel.interedges_biUnion_right, interedges_biUnion_right
-/
theorem interedges_biUnion_right (s : Finset α) (t : Finset ι) (f : ι -> Finset α) :
    G.interedges s (t.biUnion f) = t.biUnion fun b => G.interedges s (f b) :=
  Rel.interedges_biUnion_right _ _ _ _

/--
theorem `interedges_biUnion` / 定理 `interedges_biUnion`

English:
theorem interedges_biUnion
  given: (s : Finset ι) (t : Finset κ) (f : ι -> Finset α) (g : κ -> Finset α)
  proof: Rel.interedges_biUnion _ _ _ _ _

中文:
定理 interedges_biUnion
  条件: (s : 有限集 ι) (t : 有限集 κ) (f : ι -> 有限集 α) (g : κ -> 有限集 α)
  证明: Rel.interedges_biUnion _ _ _ _ _

Depends on / 依赖: Rel.interedges_biUnion, interedges_biUnion
-/
theorem interedges_biUnion (s : Finset ι) (t : Finset κ) (f : ι -> Finset α) (g : κ -> Finset α) :
    G.interedges (s.biUnion f) (t.biUnion g) =
      (s ×ˢ t).biUnion fun ab => G.interedges (f ab.1) (g ab.2) :=
  Rel.interedges_biUnion _ _ _ _ _

/--
theorem `card_interedges_add_card_interedges_compl` / 定理 `card_interedges_add_card_interedges_compl`

English:
theorem card_interedges_add_card_interedges_compl
  given: (h : Disjoint s t)
  proof: by
  rw [← card_product]; rw [interedges_def]; rw [interedges_def]
  have : {e in s ×ˢ t | Gᶜ.Adj e.1 e.2} = {e in s ×ˢ t | ¬G.Adj e.1 e.2} := by
    refine filter_congr fun x hx => ?_
    rw [mem_product] at hx
    rw [compl_adj]; rw [and_iff_right (h.forall_ne_finset hx.1 hx.2)]
  rw [this]; rw [← card_union_of_disjoint]; rw [filter_union_filter_not_eq]
  exact disjoint_filter.2 fun _ _ => Classical.not_not.2

中文:
定理 card_interedges_add_card_interedges_compl
  条件: (h : Disjoint s t)
  证明: by
  rw [← card_product]; rw [interedges_def]; rw [interedges_def]
  have : {e in s ×ˢ t | Gᶜ.Adj e.1 e.2} = {e in s ×ˢ t | ¬G.Adj e.1 e.2} := by
    refine filter_congr fun x hx => ?_
    rw [mem_product] at hx
    rw [compl_adj]; rw [and_iff_right (h.forall_ne_finset hx.1 hx.2)]
  rw [this]; rw [← card_union_of_disjoint]; rw [filter_union_filter_not_eq]
  exact disjoint_filter.2 fun _ _ => Classical.not_not.2

Depends on / 依赖: Classical, Classical.not_not, G.Adj, and_iff_right, card_product, card_union_of_disjoint, compl_adj, disjoint_filter, filter_congr, filter_union_filter_not_eq, forall_ne_finset, h.forall_ne_finset, interedges_def, mem_product, not_not
-/
theorem card_interedges_add_card_interedges_compl (h : Disjoint s t) :
    #(G.interedges s t) + #(Gᶜ.interedges s t) = #s * #t := by
  rw [← card_product]; rw [interedges_def]; rw [interedges_def]
  have : {e in s ×ˢ t | Gᶜ.Adj e.1 e.2} = {e in s ×ˢ t | ¬G.Adj e.1 e.2} := by
    refine filter_congr fun x hx => ?_
    rw [mem_product] at hx
    rw [compl_adj]; rw [and_iff_right (h.forall_ne_finset hx.1 hx.2)]
  rw [this]; rw [← card_union_of_disjoint]; rw [filter_union_filter_not_eq]
  exact disjoint_filter.2 fun _ _ => Classical.not_not.2

/--
theorem `edgeDensity_add_edgeDensity_compl` / 定理 `edgeDensity_add_edgeDensity_compl`

English:
theorem edgeDensity_add_edgeDensity_compl
  given: (hs : s.Nonempty) (ht : t.Nonempty) (h : Disjoint s t)
  proof: by
  rw [edgeDensity_def]; rw [edgeDensity_def]; rw [← add_div]; rw [div_eq_one_iff_eq]
  · exact mod_cast card_interedges_add_card_interedges_compl _ h
  · positivity

中文:
定理 edgeDensity_add_edgeDensity_compl
  条件: (hs : s.非空) (ht : t.非空) (h : Disjoint s t)
  证明: by
  rw [edgeDensity_def]; rw [edgeDensity_def]; rw [← add_div]; rw [div_eq_one_iff_eq]
  · exact mod_cast card_interedges_add_card_interedges_compl _ h
  · positivity

Depends on / 依赖: add_div, card_interedges_add_card_interedges_compl, div_eq_one_iff_eq, edgeDensity_def, mod_cast
-/
theorem edgeDensity_add_edgeDensity_compl (hs : s.Nonempty) (ht : t.Nonempty) (h : Disjoint s t) :
    G.edgeDensity s t + Gᶜ.edgeDensity s t = 1 := by
  rw [edgeDensity_def]; rw [edgeDensity_def]; rw [← add_div]; rw [div_eq_one_iff_eq]
  · exact mod_cast card_interedges_add_card_interedges_compl _ h
  · positivity

end DecidableEq

/--
theorem `card_interedges_le_mul` / 定理 `card_interedges_le_mul`

English:
theorem card_interedges_le_mul
  given: (s t : Finset α)
  statement: #(G.interedges s t) <= #s * #t
  proof: Rel.card_interedges_le_mul _ _ _

中文:
定理 card_interedges_le_mul
  条件: (s t : 有限集 α)
  结论: #(G.interedges s t) <= #s * #t
  证明: Rel.card_interedges_le_mul _ _ _

Depends on / 依赖: Rel.card_interedges_le_mul, card_interedges_le_mul
-/
theorem card_interedges_le_mul (s t : Finset α) : #(G.interedges s t) <= #s * #t :=
  Rel.card_interedges_le_mul _ _ _

/--
theorem `edgeDensity_nonneg` / 定理 `edgeDensity_nonneg`

English:
theorem edgeDensity_nonneg
  given: (s t : Finset α)
  statement: 0 <= G.edgeDensity s t
  proof: Rel.edgeDensity_nonneg _ _ _

中文:
定理 edgeDensity_nonneg
  条件: (s t : 有限集 α)
  结论: 0 <= G.edgeDensity s t
  证明: Rel.edgeDensity_nonneg _ _ _

Depends on / 依赖: Rel.edgeDensity_nonneg, edgeDensity_nonneg
-/
theorem edgeDensity_nonneg (s t : Finset α) : 0 <= G.edgeDensity s t :=
  Rel.edgeDensity_nonneg _ _ _

/--
theorem `edgeDensity_le_one` / 定理 `edgeDensity_le_one`

English:
theorem edgeDensity_le_one
  given: (s t : Finset α)
  statement: G.edgeDensity s t <= 1
  proof: Rel.edgeDensity_le_one _ _ _

@[simp]

中文:
定理 edgeDensity_le_one
  条件: (s t : 有限集 α)
  结论: G.edgeDensity s t <= 1
  证明: Rel.edgeDensity_le_one _ _ _

@[simp]

Depends on / 依赖: Rel.edgeDensity_le_one, edgeDensity_le_one
-/
theorem edgeDensity_le_one (s t : Finset α) : G.edgeDensity s t <= 1 :=
  Rel.edgeDensity_le_one _ _ _

@[simp]
/--
theorem `edgeDensity_empty_left` / 定理 `edgeDensity_empty_left`

English:
theorem edgeDensity_empty_left
  given: (t : Finset α)
  statement: G.edgeDensity ∅ t = 0
  proof: Rel.edgeDensity_empty_left _ _

@[simp]

中文:
定理 edgeDensity_empty_left
  条件: (t : 有限集 α)
  结论: G.edgeDensity ∅ t = 0
  证明: Rel.edgeDensity_empty_left _ _

@[simp]

Depends on / 依赖: Rel.edgeDensity_empty_left, edgeDensity_empty_left
-/
theorem edgeDensity_empty_left (t : Finset α) : G.edgeDensity ∅ t = 0 :=
  Rel.edgeDensity_empty_left _ _

@[simp]
/--
theorem `edgeDensity_empty_right` / 定理 `edgeDensity_empty_right`

English:
theorem edgeDensity_empty_right
  given: (s : Finset α)
  statement: G.edgeDensity s ∅ = 0
  proof: Rel.edgeDensity_empty_right _ _

@[simp]

中文:
定理 edgeDensity_empty_right
  条件: (s : 有限集 α)
  结论: G.edgeDensity s ∅ = 0
  证明: Rel.edgeDensity_empty_right _ _

@[simp]

Depends on / 依赖: Rel.edgeDensity_empty_right, edgeDensity_empty_right
-/
theorem edgeDensity_empty_right (s : Finset α) : G.edgeDensity s ∅ = 0 :=
  Rel.edgeDensity_empty_right _ _

@[simp]
/--
theorem `swap_mem_interedges_iff` / 定理 `swap_mem_interedges_iff`

English:
theorem swap_mem_interedges_iff
  given: {x : α × α}
  statement: x.swap in G.interedges s t ↔ x in G.interedges t s
  proof: have := G.symm
  Rel.swap_mem_interedges_iff

中文:
定理 swap_mem_interedges_iff
  条件: {x : α × α}
  结论: x.swap in G.interedges s t ↔ x in G.interedges t s
  证明: have := G.symm
  Rel.swap_mem_interedges_iff

Depends on / 依赖: G.symm, Rel.swap_mem_interedges_iff, swap_mem_interedges_iff
-/
theorem swap_mem_interedges_iff {x : α × α} : x.swap in G.interedges s t ↔ x in G.interedges t s :=
  have := G.symm
  Rel.swap_mem_interedges_iff

/--
theorem `mk_mem_interedges_comm` / 定理 `mk_mem_interedges_comm`

English:
theorem mk_mem_interedges_comm
  statement: (a, b) in G.interedges s t ↔ (b, a) in G.interedges t s
  proof: have := G.symm
  Rel.mk_mem_interedges_comm

中文:
定理 mk_mem_interedges_comm
  结论: (a, b) in G.interedges s t ↔ (b, a) in G.interedges t s
  证明: have := G.symm
  Rel.mk_mem_interedges_comm

Depends on / 依赖: G.symm, Rel.mk_mem_interedges_comm, mk_mem_interedges_comm
-/
theorem mk_mem_interedges_comm : (a, b) in G.interedges s t ↔ (b, a) in G.interedges t s :=
  have := G.symm
  Rel.mk_mem_interedges_comm

/--
theorem `edgeDensity_comm` / 定理 `edgeDensity_comm`

English:
theorem edgeDensity_comm
  given: (s t : Finset α)
  statement: G.edgeDensity s t = G.edgeDensity t s
  proof: have := G.symm
  Rel.edgeDensity_comm s t

中文:
定理 edgeDensity_comm
  条件: (s t : 有限集 α)
  结论: G.edgeDensity s t = G.edgeDensity t s
  证明: have := G.symm
  Rel.edgeDensity_comm s t

Depends on / 依赖: G.symm, Rel.edgeDensity_comm, edgeDensity_comm
-/
theorem edgeDensity_comm (s t : Finset α) : G.edgeDensity s t = G.edgeDensity t s :=
  have := G.symm
  Rel.edgeDensity_comm s t

end SimpleGraph

/- Porting note: Commented out `Tactic` namespace.
namespace Tactic

open Positivity

/-- Extension for the `positivity` tactic: `Rel.edgeDensity` and `SimpleGraph.edgeDensity` are
always nonnegative. -/
@[positivity]
unsafe def positivity_edge_density : expr -> tactic strictness
  | q(Rel.edgeDensity $(r) $(s) $(t)) =>
nonnegative < > mk_mapp `` Rel.edgeDensity_nonneg [none, none, r, none, s, t]
  | q(SimpleGraph.edgeDensity $(G) $(s) $(t)) =>
nonnegative < > mk_mapp `` SimpleGraph.edgeDensity_nonneg [none, G, none, s, t]
  | e =>
    pp e >>=
      fail ∘
        format.bracket "The expression `"
          "` isn't of the form `Rel.edgeDensity r s t` nor `SimpleGraph.edgeDensity G s t`"

end Tactic
-/
