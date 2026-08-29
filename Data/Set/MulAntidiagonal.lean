/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
module

public import Mathlib.Order.WellFoundedSet

/-! # Multiplication antidiagonal -/

@[expose] public section


namespace Set

variable {α : Type*}

section Mul

variable [Mul α] {s s₁ s₂ t t₁ t₂ : Set α} {a : α} {x : α × α}

/-- `Set.mulAntidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
that multiply to `a`. -/
@[to_additive
      /-- `Set.addAntidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that add to `a`. -/]
/--
Definition of `mulAntidiagonal` / `mulAntidiagonal` 的定义

English:
definition mulAntidiagonal
  signature: (s t : Set α) (a : α)
  body: { x | x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a }

@[to_additive (attr := simp)]

中文:
定义 mulAntidiagonal
  签名: (s t : 集合 α) (a : α)
  定义体: { x | x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a }

@[to_additive (attr := simp)]
-/
def mulAntidiagonal (s t : Set α) (a : α) : Set (α × α) :=
  { x | x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a }

@[to_additive (attr := simp)]
/--
theorem `mem_mulAntidiagonal` / 定理 `mem_mulAntidiagonal`

English:
theorem mem_mulAntidiagonal
  statement: x in mulAntidiagonal s t a ↔ x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_mulAntidiagonal
  结论: x in mulAntidiagonal s t a ↔ x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mulAntidiagonal : x in mulAntidiagonal s t a ↔ x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a :=
  Iff.rfl

@[to_additive]
/--
theorem `mulAntidiagonal_mono_left` / 定理 `mulAntidiagonal_mono_left`

English:
theorem mulAntidiagonal_mono_left
  given: (h : s₁ subseteq s₂)
  statement: mulAntidiagonal s₁ t a subseteq mulAntidiagonal s₂ t a
  proof: fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]

中文:
定理 mulAntidiagonal_mono_left
  条件: (h : s₁ subseteq s₂)
  结论: mulAntidiagonal s₁ t a subseteq mulAntidiagonal s₂ t a
  证明: fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]
-/
theorem mulAntidiagonal_mono_left (h : s₁ subseteq s₂) : mulAntidiagonal s₁ t a subseteq mulAntidiagonal s₂ t a :=
  fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]
/--
theorem `mulAntidiagonal_mono_right` / 定理 `mulAntidiagonal_mono_right`

English:
theorem mulAntidiagonal_mono_right
  given: (h : t₁ subseteq t₂)
  proof: fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩

中文:
定理 mulAntidiagonal_mono_right
  条件: (h : t₁ subseteq t₂)
  证明: fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩
-/
theorem mulAntidiagonal_mono_right (h : t₁ subseteq t₂) :
    mulAntidiagonal s t₁ a subseteq mulAntidiagonal s t₂ a := fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩

end Mul

-- The left-hand side is not in simp normal form, see variant below.
@[to_additive]
/--
theorem `swap_mem_mulAntidiagonal` / 定理 `swap_mem_mulAntidiagonal`

English:
theorem swap_mem_mulAntidiagonal
  given: [CommMagma α] {s t : Set α} {a : α} {x : α × α}
  proof: by
  simp [mul_comm, and_left_comm]

@[to_additive (attr := simp)]

中文:
定理 swap_mem_mulAntidiagonal
  条件: [交换原群 α] {s t : 集合 α} {a : α} {x : α × α}
  证明: by
  simp [mul_comm, and_left_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: and_left_comm, mul_comm
-/
theorem swap_mem_mulAntidiagonal [CommMagma α] {s t : Set α} {a : α} {x : α × α} :
    x.swap in Set.mulAntidiagonal s t a ↔ x in Set.mulAntidiagonal t s a := by
  simp [mul_comm, and_left_comm]

@[to_additive (attr := simp)]
/--
theorem `swap_mem_mulAntidiagonal_aux` / 定理 `swap_mem_mulAntidiagonal_aux`

English:
theorem swap_mem_mulAntidiagonal_aux
  given: [CommMagma α] {s t : Set α} {a : α} {x : α × α}
  proof: by
  simp [mul_comm, and_left_comm]

中文:
定理 swap_mem_mulAntidiagonal_aux
  条件: [交换原群 α] {s t : 集合 α} {a : α} {x : α × α}
  证明: by
  simp [mul_comm, and_left_comm]

Depends on / 依赖: and_left_comm, mul_comm
-/
theorem swap_mem_mulAntidiagonal_aux [CommMagma α] {s t : Set α} {a : α} {x : α × α} :
    x.snd in s ∧ x.fst in t ∧ x.snd * x.fst = a
      ↔ x in Set.mulAntidiagonal t s a := by
  simp [mul_comm, and_left_comm]


namespace MulAntidiagonal

section CancelCommMonoid

variable [CommMonoid α] [IsCancelMul α] {s t : Set α} {a : α} {x y : mulAntidiagonal s t a}

-- We have to translate the names manually because the namespace name `MulAntidiagonal`
-- does not match the declaration `mulAntidiagonal` that has the `to_additive` attribute.
@[to_additive Set.AddAntidiagonal.fst_eq_fst_iff_snd_eq_snd]
/--
theorem `fst_eq_fst_iff_snd_eq_snd` / 定理 `fst_eq_fst_iff_snd_eq_snd`

English:
theorem fst_eq_fst_iff_snd_eq_snd
  statement: (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2
  proof: ⟨fun h =>
    mul_left_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    mul_right_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

@[to_additive Set.AddAntidiagonal.eq_of_fst_eq_fst]

中文:
定理 fst_eq_fst_iff_snd_eq_snd
  结论: (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2
  证明: ⟨fun h =>
    mul_left_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    mul_right_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

@[to_additive Set.AddAntidiagonal.eq_of_fst_eq_fst]

Depends on / 依赖: mul_left_cancel, mul_right_cancel
-/
theorem fst_eq_fst_iff_snd_eq_snd : (x : α × α).1 = (y : α × α).1 ↔ (x : α × α).2 = (y : α × α).2 :=
  ⟨fun h =>
    mul_left_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    mul_right_cancel
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

@[to_additive Set.AddAntidiagonal.eq_of_fst_eq_fst]
/--
theorem `eq_of_fst_eq_fst` / 定理 `eq_of_fst_eq_fst`

English:
theorem eq_of_fst_eq_fst
  given: (h : (x : α × α).fst = (y : α × α).fst)
  statement: x = y
  proof: Subtype.ext Prod.ext h fst_eq_fst_iff_snd_eq_snd.1 h

@[to_additive Set.AddAntidiagonal.eq_of_snd_eq_snd]

中文:
定理 eq_of_fst_eq_fst
  条件: (h : (x : α × α).fst = (y : α × α).fst)
  结论: x = y
  证明: Subtype.ext Prod.ext h fst_eq_fst_iff_snd_eq_snd.1 h

@[to_additive Set.AddAntidiagonal.eq_of_snd_eq_snd]

Depends on / 依赖: Prod.ext, Subtype, Subtype.ext, fst_eq_fst_iff_snd_eq_snd
-/
theorem eq_of_fst_eq_fst (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
Subtype.ext Prod.ext h fst_eq_fst_iff_snd_eq_snd.1 h

@[to_additive Set.AddAntidiagonal.eq_of_snd_eq_snd]
/--
theorem `eq_of_snd_eq_snd` / 定理 `eq_of_snd_eq_snd`

English:
theorem eq_of_snd_eq_snd
  given: (h : (x : α × α).snd = (y : α × α).snd)
  statement: x = y
  proof: Subtype.ext Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

中文:
定理 eq_of_snd_eq_snd
  条件: (h : (x : α × α).snd = (y : α × α).snd)
  结论: x = y
  证明: Subtype.ext Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

Depends on / 依赖: Prod.ext, Subtype, Subtype.ext, fst_eq_fst_iff_snd_eq_snd
-/
theorem eq_of_snd_eq_snd (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
Subtype.ext Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [CommMonoid α] [PartialOrder α] [IsCancelMul α] [MulLeftMono α] [MulRightStrictMono α]
  (s t : Set α) (a : α) {x y : mulAntidiagonal s t a}

@[to_additive Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd]
/--
theorem `eq_of_fst_le_fst_of_snd_le_snd` / 定理 `eq_of_fst_le_fst_of_snd_le_snd`

English:
theorem eq_of_fst_le_fst_of_snd_le_snd
  statement: (h₁ : (x : α × α).1 <= (y : α × α).1)
  proof: eq_of_fst_eq_fst
    h₁.eq_of_not_lt fun hlt =>
(mul_lt_mul_of_lt_of_le hlt h₂).ne
        (mem_mulAntidiagonal.1 x.2).2.2.trans (mem_mulAntidiagonal.1 y.2).2.2.symm

中文:
定理 eq_of_fst_le_fst_of_snd_le_snd
  结论: (h₁ : (x : α × α).1 <= (y : α × α).1)
  证明: eq_of_fst_eq_fst
    h₁.eq_of_not_lt fun hlt =>
(mul_lt_mul_of_lt_of_le hlt h₂).ne
        (mem_mulAntidiagonal.1 x.2).2.2.trans (mem_mulAntidiagonal.1 y.2).2.2.symm

Depends on / 依赖: eq_of_fst_eq_fst, eq_of_not_lt, mem_mulAntidiagonal, mul_lt_mul_of_lt_of_le
-/
theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : α × α).1 <= (y : α × α).1)
    (h₂ : (x : α × α).2 <= (y : α × α).2) : x = y :=
eq_of_fst_eq_fst
    h₁.eq_of_not_lt fun hlt =>
(mul_lt_mul_of_lt_of_le hlt h₂).ne
        (mem_mulAntidiagonal.1 x.2).2.2.trans (mem_mulAntidiagonal.1 y.2).2.2.symm

variable {s t}

@[to_additive Set.AddAntidiagonal.finite_of_isPWO]
/--
theorem `finite_of_isPWO` / 定理 `finite_of_isPWO`

English:
theorem finite_of_isPWO
  given: (hs : s.IsPWO) (ht : t.IsPWO) (a)
  statement: (mulAntidiagonal s t a).Finite
  proof: by
  by_contra! h
  have h1 : (mulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· <= ·)) :=
    fun f => hs fun n => ⟨_, (mem_mulAntidiagonal.1 (f n).2).1⟩
  have h2 : (mulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· <= ·)) :=
    fun f => ht fun n => ⟨_, (mem_mulAntidiagonal.1 (f n).2).2.1⟩
  obtain ⟨g, hg⟩ :=
    h1.exists_monotone_subseq fun n => (h.natEmbedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 fun n => h.natEmbedding _ _
  refine mn.ne (g.injective <| (h.natEmbedding _).injective ?_)
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ mn.le) h2'

中文:
定理 finite_of_isPWO
  条件: (hs : s.IsPWO) (ht : t.IsPWO) (a)
  结论: (mulAntidiagonal s t a).有限
  证明: by
  by_contra! h
  have h1 : (mulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· <= ·)) :=
    fun f => hs fun n => ⟨_, (mem_mulAntidiagonal.1 (f n).2).1⟩
  have h2 : (mulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· <= ·)) :=
    fun f => ht fun n => ⟨_, (mem_mulAntidiagonal.1 (f n).2).2.1⟩
  obtain ⟨g, hg⟩ :=
    h1.exists_monotone_subseq fun n => (h.natEmbedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 fun n => h.natEmbedding _ _
  refine mn.ne (g.injective <| (h.natEmbedding _).injective ?_)
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ mn.le) h2'

Depends on / 依赖: PartiallyWellOrderedOn, Prod.fst, Prod.snd, exists_monotone_subseq, g.injective, h.natEmbedding, h1.exists_monotone_subseq, injective, mem_mulAntidiagonal, mn.ne, mulAntidiagonal, natEmbedding
-/
theorem finite_of_isPWO (hs : s.IsPWO) (ht : t.IsPWO) (a) : (mulAntidiagonal s t a).Finite := by
  by_contra! h
  have h1 : (mulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· <= ·)) :=
    fun f => hs fun n => ⟨_, (mem_mulAntidiagonal.1 (f n).2).1⟩
  have h2 : (mulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· <= ·)) :=
    fun f => ht fun n => ⟨_, (mem_mulAntidiagonal.1 (f n).2).2.1⟩
  obtain ⟨g, hg⟩ :=
    h1.exists_monotone_subseq fun n => (h.natEmbedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 fun n => h.natEmbedding _ _
  refine mn.ne (g.injective <| (h.natEmbedding _).injective ?_)
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ mn.le) h2'

end OrderedCancelCommMonoid

variable [CancelCommMonoid α] [LinearOrder α] [MulLeftMono α] [MulRightStrictMono α]

@[to_additive Set.AddAntidiagonal.finite_of_isWF]
/--
theorem `finite_of_isWF` / 定理 `finite_of_isWF`

English:
theorem finite_of_isWF
  statement: {s t : Set α} (hs : s.IsWF) (ht : t.IsWF)
  proof: finite_of_isPWO hs.isPWO ht.isPWO a

中文:
定理 finite_of_isWF
  结论: {s t : 集合 α} (hs : s.IsWF) (ht : t.IsWF)
  证明: finite_of_isPWO hs.isPWO ht.isPWO a

Depends on / 依赖: finite_of_isPWO, hs.isPWO, ht.isPWO
-/
theorem finite_of_isWF {s t : Set α} (hs : s.IsWF) (ht : t.IsWF)
    (a) : (mulAntidiagonal s t a).Finite :=
  finite_of_isPWO hs.isPWO ht.isPWO a

end MulAntidiagonal

end Set
