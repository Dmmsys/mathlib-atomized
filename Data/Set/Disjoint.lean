/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Theorems about the `Disjoint` relation on `Set`.
-/

public section

assert_not_exists HeytingAlgebra RelIso

/-! ### Set coercion to a type -/

open Function

universe u v

namespace Set

variable {α : Type u} {s t u s₁ s₂ t₁ t₂ : Set α}



/--
theorem `disjoint_iff` / 定理 `disjoint_iff`

English:
theorem disjoint_iff
  statement: Disjoint s t ↔ s inter t subseteq ∅
  proof: disjoint_iff_inf_le

中文:
定理 disjoint_iff
  结论: Disjoint s t ↔ s inter t subseteq ∅
  证明: disjoint_iff_inf_le
-/
protected theorem disjoint_iff : Disjoint s t ↔ s inter t subseteq ∅ :=
  disjoint_iff_inf_le

/--
theorem `disjoint_iff_inter_eq_empty` / 定理 `disjoint_iff_inter_eq_empty`

English:
theorem disjoint_iff_inter_eq_empty
  statement: Disjoint s t ↔ s inter t = ∅
  proof: disjoint_iff

中文:
定理 disjoint_iff_inter_eq_empty
  结论: Disjoint s t ↔ s inter t = ∅
  证明: disjoint_iff

Depends on / 依赖: disjoint_iff
-/
theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s inter t = ∅ :=
  disjoint_iff

/--
theorem `_root_.Disjoint.inter_eq` / 定理 `_root_.Disjoint.inter_eq`

English:
theorem _root_.Disjoint.inter_eq
  statement: Disjoint s t -> s inter t = ∅
  proof: Disjoint.eq_bot

@[grind =]

中文:
定理 _root_.Disjoint.inter_eq
  结论: Disjoint s t -> s inter t = ∅
  证明: Disjoint.eq_bot

@[grind =]

Depends on / 依赖: Disjoint, Disjoint.eq_bot, eq_bot
-/
theorem _root_.Disjoint.inter_eq : Disjoint s t -> s inter t = ∅ :=
  Disjoint.eq_bot

@[grind =]
/--
theorem `disjoint_left` / 定理 `disjoint_left`

English:
theorem disjoint_left
  statement: Disjoint s t ↔ forall ⦃a⦄, a in s -> a ∉ t
  proof: disjoint_iff_inf_le.trans forall_congr' fun _ => not_and

alias ⟨_root_.Disjoint.notMem_of_mem_left, _⟩ := disjoint_left

中文:
定理 disjoint_left
  结论: Disjoint s t ↔ 对任意 ⦃a⦄, a in s -> a ∉ t
  证明: disjoint_iff_inf_le.trans forall_congr' fun _ => not_and

alias ⟨_root_.Disjoint.notMem_of_mem_left, _⟩ := disjoint_left

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.trans, forall_congr, not_and
-/
theorem disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> a ∉ t :=
disjoint_iff_inf_le.trans forall_congr' fun _ => not_and

alias ⟨_root_.Disjoint.notMem_of_mem_left, _⟩ := disjoint_left

/--
theorem `disjoint_right` / 定理 `disjoint_right`

English:
theorem disjoint_right
  statement: Disjoint s t ↔ forall ⦃a⦄, a in t -> a ∉ s
  proof: by rw [disjoint_comm, disjoint_left]

alias ⟨_root_.Disjoint.notMem_of_mem_right, _⟩ := disjoint_right

中文:
定理 disjoint_right
  结论: Disjoint s t ↔ 对任意 ⦃a⦄, a in t -> a ∉ s
  证明: by rw [disjoint_comm, disjoint_left]

alias ⟨_root_.Disjoint.notMem_of_mem_right, _⟩ := disjoint_right

Depends on / 依赖: disjoint_comm, disjoint_left
-/
theorem disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -> a ∉ s := by rw [disjoint_comm, disjoint_left]

alias ⟨_root_.Disjoint.notMem_of_mem_right, _⟩ := disjoint_right

/--
lemma `not_disjoint_iff` / 引理 `not_disjoint_iff`

English:
lemma not_disjoint_iff
  statement: ¬Disjoint s t ↔ exists x, x in s ∧ x in t
  proof: by grind

中文:
引理 not_disjoint_iff
  结论: ¬Disjoint s t ↔ 存在 x, x in s ∧ x in t
  证明: by grind
-/
lemma not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in s ∧ x in t := by grind

/--
lemma `not_disjoint_iff_nonempty_inter` / 引理 `not_disjoint_iff_nonempty_inter`

English:
lemma not_disjoint_iff_nonempty_inter
  statement: ¬ Disjoint s t ↔ (s inter t).Nonempty
  proof: not_disjoint_iff

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter

中文:
引理 not_disjoint_iff_nonempty_inter
  结论: ¬ Disjoint s t ↔ (s inter t).Nonempty
  证明: not_disjoint_iff

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter

Depends on / 依赖: not_disjoint_iff, stereographic
-/
lemma not_disjoint_iff_nonempty_inter : ¬ Disjoint s t ↔ (s inter t).Nonempty := not_disjoint_iff

alias ⟨_, Nonempty.not_disjoint⟩ := not_disjoint_iff_nonempty_inter

/--
lemma `disjoint_or_nonempty_inter` / 引理 `disjoint_or_nonempty_inter`

English:
lemma disjoint_or_nonempty_inter
  given: (s t : Set α)
  statement: Disjoint s t ∨ (s inter t).Nonempty
  proof: (em _).imp_right not_disjoint_iff_nonempty_inter.1

中文:
引理 disjoint_or_nonempty_inter
  条件: (s t : Set α)
  结论: Disjoint s t ∨ (s inter t).Nonempty
  证明: (em _).imp_right not_disjoint_iff_nonempty_inter.1

Depends on / 依赖: imp_right, not_disjoint_iff_nonempty_inter, stereographic
-/
lemma disjoint_or_nonempty_inter (s t : Set α) : Disjoint s t ∨ (s inter t).Nonempty :=
  (em _).imp_right not_disjoint_iff_nonempty_inter.1

/--
lemma `disjoint_iff_forall_ne` / 引理 `disjoint_iff_forall_ne`

English:
lemma disjoint_iff_forall_ne
  statement: Disjoint s t ↔ forall ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
  proof: by grind

alias ⟨_root_.Disjoint.ne_of_mem, _⟩ := disjoint_iff_forall_ne

中文:
引理 disjoint_iff_forall_ne
  结论: Disjoint s t ↔ 对任意 ⦃a⦄, a in s -> 对任意 ⦃b⦄, b in t -> a != b
  证明: by grind

alias ⟨_root_.Disjoint.ne_of_mem, _⟩ := disjoint_iff_forall_ne
-/
lemma disjoint_iff_forall_ne : Disjoint s t ↔ forall ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b := by grind

alias ⟨_root_.Disjoint.ne_of_mem, _⟩ := disjoint_iff_forall_ne

/--
lemma `disjoint_of_subset_left` / 引理 `disjoint_of_subset_left`

English:
lemma disjoint_of_subset_left
  given: (h : s subseteq u) (d : Disjoint u t)
  statement: Disjoint s t
  proof: d.mono_left h

中文:
引理 disjoint_of_subset_left
  条件: (h : s subseteq u) (d : Disjoint u t)
  结论: Disjoint s t
  证明: d.mono_left h

Depends on / 依赖: EuclideanSpace, EuclideanSpace.instChartedSpaceSphere, Fact.mk, d.mono_left, finrank_euclideanSpace_fin, instChartedSpaceSphere, mono_left
-/
lemma disjoint_of_subset_left (h : s subseteq u) (d : Disjoint u t) : Disjoint s t := d.mono_left h
/--
lemma `disjoint_of_subset_right` / 引理 `disjoint_of_subset_right`

English:
lemma disjoint_of_subset_right
  given: (h : t subseteq u) (d : Disjoint s u)
  statement: Disjoint s t
  proof: d.mono_right h

中文:
引理 disjoint_of_subset_right
  条件: (h : t subseteq u) (d : Disjoint s u)
  结论: Disjoint s t
  证明: d.mono_right h

Depends on / 依赖: d.mono_right, mono_right
-/
lemma disjoint_of_subset_right (h : t subseteq u) (d : Disjoint s u) : Disjoint s t := d.mono_right h

/--
lemma `disjoint_of_subset` / 引理 `disjoint_of_subset`

English:
lemma disjoint_of_subset
  given: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) (h : Disjoint s₂ t₂)
  statement: Disjoint s₁ t₁
  proof: h.mono hs ht

@[simp]

中文:
引理 disjoint_of_subset
  条件: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) (h : Disjoint s₂ t₂)
  结论: Disjoint s₁ t₁
  证明: h.mono hs ht

@[simp]

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.fromOrthogonalSpanSingleton, Submodule, Submodule.coe_norm, U.symm, coe_norm, fromOrthogonalSpanSingleton, h.mono, ne_zero_of_mem_unit_sphere, stereographic, v.val
-/
lemma disjoint_of_subset (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) (h : Disjoint s₂ t₂) : Disjoint s₁ t₁ :=
  h.mono hs ht

@[simp]
/--
lemma `disjoint_union_left` / 引理 `disjoint_union_left`

English:
lemma disjoint_union_left
  statement: Disjoint (s union t) u ↔ Disjoint s u ∧ Disjoint t u
  proof: disjoint_sup_left

@[simp]

中文:
引理 disjoint_union_left
  结论: Disjoint (s union t) u ↔ Disjoint s u ∧ Disjoint t u
  证明: disjoint_sup_left

@[simp]

Depends on / 依赖: disjoint_sup_left
-/
lemma disjoint_union_left : Disjoint (s union t) u ↔ Disjoint s u ∧ Disjoint t u := disjoint_sup_left

@[simp]
/--
lemma `disjoint_union_right` / 引理 `disjoint_union_right`

English:
lemma disjoint_union_right
  statement: Disjoint s (t union u) ↔ Disjoint s t ∧ Disjoint s u
  proof: disjoint_sup_right

中文:
引理 disjoint_union_right
  结论: Disjoint s (t union u) ↔ Disjoint s t ∧ Disjoint s u
  证明: disjoint_sup_right

Depends on / 依赖: EuclideanSpace, EuclideanSpace.instIsManifoldSphere, Fact.mk, disjoint_sup_right, finrank_euclideanSpace_fin, instIsManifoldSphere
-/
lemma disjoint_union_right : Disjoint s (t union u) ↔ Disjoint s t ∧ Disjoint s u := disjoint_sup_right

/--
lemma `disjoint_empty` / 引理 `disjoint_empty`

English:
lemma disjoint_empty
  given: (s : Set α)
  statement: Disjoint s ∅
  proof: disjoint_bot_right

中文:
引理 disjoint_empty
  条件: (s : Set α)
  结论: Disjoint s ∅
  证明: disjoint_bot_right
-/
@[simp] lemma disjoint_empty (s : Set α) : Disjoint s ∅ := disjoint_bot_right
/--
lemma `empty_disjoint` / 引理 `empty_disjoint`

English:
lemma empty_disjoint
  given: (s : Set α)
  statement: Disjoint ∅ s
  proof: disjoint_bot_left

中文:
引理 empty_disjoint
  条件: (s : Set α)
  结论: Disjoint ∅ s
  证明: disjoint_bot_left
-/
@[simp] lemma empty_disjoint (s : Set α) : Disjoint ∅ s := disjoint_bot_left

/--
lemma `univ_disjoint` / 引理 `univ_disjoint`

English:
lemma univ_disjoint
  statement: Disjoint univ s ↔ s = ∅
  proof: top_disjoint

中文:
引理 univ_disjoint
  结论: Disjoint univ s ↔ s = ∅
  证明: top_disjoint
-/
@[simp] lemma univ_disjoint : Disjoint univ s ↔ s = ∅ := top_disjoint
/--
lemma `disjoint_univ` / 引理 `disjoint_univ`

English:
lemma disjoint_univ
  statement: Disjoint s univ ↔ s = ∅
  proof: disjoint_top

中文:
引理 disjoint_univ
  结论: Disjoint s univ ↔ s = ∅
  证明: disjoint_top
-/
@[simp] lemma disjoint_univ : Disjoint s univ ↔ s = ∅ := disjoint_top

/--
theorem `disjoint_range_iff` / 定理 `disjoint_range_iff`

English:
theorem disjoint_range_iff
  given: {β γ : Sort*} {x : β -> α} {y : γ -> α}
  proof: by
  simp [Set.disjoint_iff_forall_ne]

中文:
定理 disjoint_range_iff
  条件: {β γ : Sort*} {x : β -> α} {y : γ -> α}
  证明: by
  simp [Set.disjoint_iff_forall_ne]

Depends on / 依赖: Set.disjoint_iff_forall_ne, disjoint_iff_forall_ne
-/
theorem disjoint_range_iff {β γ : Sort*} {x : β -> α} {y : γ -> α} :
    Disjoint (range x) (range y) ↔ forall i j, x i != y j := by
  simp [Set.disjoint_iff_forall_ne]

end Set

/-! ### Disjoint sets -/

variable {α : Type*} {s t u : Set α}

namespace Disjoint

/--
theorem `union_left` / 定理 `union_left`

English:
theorem union_left
  given: (hs : Disjoint s u) (ht : Disjoint t u)
  statement: Disjoint (s union t) u
  proof: hs.sup_left ht

中文:
定理 union_left
  条件: (hs : Disjoint s u) (ht : Disjoint t u)
  结论: Disjoint (s union t) u
  证明: hs.sup_left ht

Depends on / 依赖: hs.sup_left, sup_left
-/
theorem union_left (hs : Disjoint s u) (ht : Disjoint t u) : Disjoint (s union t) u :=
  hs.sup_left ht

/--
theorem `union_right` / 定理 `union_right`

English:
theorem union_right
  given: (ht : Disjoint s t) (hu : Disjoint s u)
  statement: Disjoint s (t union u)
  proof: ht.sup_right hu

中文:
定理 union_right
  条件: (ht : Disjoint s t) (hu : Disjoint s u)
  结论: Disjoint s (t union u)
  证明: ht.sup_right hu

Depends on / 依赖: ht.sup_right, sup_right
-/
theorem union_right (ht : Disjoint s t) (hu : Disjoint s u) : Disjoint s (t union u) :=
  ht.sup_right hu

/--
theorem `inter_left` / 定理 `inter_left`

English:
theorem inter_left
  given: (u : Set α) (h : Disjoint s t)
  statement: Disjoint (s inter u) t
  proof: h.inf_left _

中文:
定理 inter_left
  条件: (u : Set α) (h : Disjoint s t)
  结论: Disjoint (s inter u) t
  证明: h.inf_left _

Depends on / 依赖: h.inf_left, inf_left
-/
theorem inter_left (u : Set α) (h : Disjoint s t) : Disjoint (s inter u) t :=
  h.inf_left _

/--
theorem `inter_left'` / 定理 `inter_left'`

English:
theorem inter_left'
  given: (u : Set α) (h : Disjoint s t)
  statement: Disjoint (u inter s) t
  proof: h.inf_left' _

中文:
定理 inter_left'
  条件: (u : Set α) (h : Disjoint s t)
  结论: Disjoint (u inter s) t
  证明: h.inf_left' _

Depends on / 依赖: h.inf_left, inf_left
-/
theorem inter_left' (u : Set α) (h : Disjoint s t) : Disjoint (u inter s) t :=
  h.inf_left' _

/--
theorem `inter_right` / 定理 `inter_right`

English:
theorem inter_right
  given: (u : Set α) (h : Disjoint s t)
  statement: Disjoint s (t inter u)
  proof: h.inf_right _

中文:
定理 inter_right
  条件: (u : Set α) (h : Disjoint s t)
  结论: Disjoint s (t inter u)
  证明: h.inf_right _

Depends on / 依赖: h.inf_right, inf_right
-/
theorem inter_right (u : Set α) (h : Disjoint s t) : Disjoint s (t inter u) :=
  h.inf_right _

/--
theorem `inter_right'` / 定理 `inter_right'`

English:
theorem inter_right'
  given: (u : Set α) (h : Disjoint s t)
  statement: Disjoint s (u inter t)
  proof: h.inf_right' _

中文:
定理 inter_right'
  条件: (u : Set α) (h : Disjoint s t)
  结论: Disjoint s (u inter t)
  证明: h.inf_right' _

Depends on / 依赖: h.inf_right, inf_right
-/
theorem inter_right' (u : Set α) (h : Disjoint s t) : Disjoint s (u inter t) :=
  h.inf_right' _

/--
theorem `subset_left_of_subset_union` / 定理 `subset_left_of_subset_union`

English:
theorem subset_left_of_subset_union
  given: (h : s subseteq t union u) (hac : Disjoint s u)
  statement: s subseteq t
  proof: hac.left_le_of_le_sup_right h

中文:
定理 subset_left_of_subset_union
  条件: (h : s subseteq t union u) (hac : Disjoint s u)
  结论: s subseteq t
  证明: hac.left_le_of_le_sup_right h

Depends on / 依赖: hac.left_le_of_le_sup_right, left_le_of_le_sup_right
-/
theorem subset_left_of_subset_union (h : s subseteq t union u) (hac : Disjoint s u) : s subseteq t :=
  hac.left_le_of_le_sup_right h

/--
theorem `subset_right_of_subset_union` / 定理 `subset_right_of_subset_union`

English:
theorem subset_right_of_subset_union
  given: (h : s subseteq t union u) (hab : Disjoint s t)
  statement: s subseteq u
  proof: hab.left_le_of_le_sup_left h

中文:
定理 subset_right_of_subset_union
  条件: (h : s subseteq t union u) (hab : Disjoint s t)
  结论: s subseteq u
  证明: hab.left_le_of_le_sup_left h

Depends on / 依赖: hab.left_le_of_le_sup_left, left_le_of_le_sup_left
-/
theorem subset_right_of_subset_union (h : s subseteq t union u) (hab : Disjoint s t) : s subseteq u :=
  hab.left_le_of_le_sup_left h

end Disjoint

namespace Set

/--
theorem `mem_union_of_disjoint` / 定理 `mem_union_of_disjoint`

English:
theorem mem_union_of_disjoint
  given: (h : Disjoint s t) {x : α}
  statement: x in s union t ↔ Xor (x in s) (x in t)
  proof: by
  grind [Xor]

中文:
定理 mem_union_of_disjoint
  条件: (h : Disjoint s t) {x : α}
  结论: x in s union t ↔ Xor (x in s) (x in t)
  证明: by
  grind [Xor]
-/
theorem mem_union_of_disjoint (h : Disjoint s t) {x : α} : x in s union t ↔ Xor (x in s) (x in t) := by
  grind [Xor]

end Set
