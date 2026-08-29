/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.Positivity.Basic

/-!
# Density of a finite set

This defines the density of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.dens s`: Density of `s : Finset α` in `α` as a nonnegative rational number.

## Implementation notes

There are many other ways to talk about the density of a finset and provide its API:
1. Use the uniform measure
2. Define finitely additive functions and generalise the `Finset.card` API to it. This could either
  be done with
  a. A structure `FinitelyAdditiveFun`
  b. A typeclass `IsFinitelyAdditiveFun`

Solution 1 would mean importing measure theory in simple files (not necessarily bad, but not
amazing), and every single API lemma would require the user to prove that all the sets they are
talking about are measurable in the trivial sigma-algebra (quite terrible user experience).

Solution 2 would mean that some API lemmas about density don't contain `dens` in their name because
they are general results about finitely additive functions. But not all lemmas would be like that
either since some really are `dens`-specific. Hence the user would need to think about whether the
lemma they are looking for is generally true for finitely additive measure or whether it is
`dens`-specific.

On top of this, solution 2.a would break dot notation on `Finset.dens` (possibly fixable by
introducing notation for `⇑Finset.dens`) and solution 2.b would run the risk of being bad
performance-wise.

These considerations more generally apply to `Finset.card` and `Finset.sum` and demonstrate that
overengineering basic definitions is likely to hinder user experience.
-/

@[expose] public section

-- TODO
-- assert_not_exists Ring

open Function Multiset Nat

variable {𝕜 α β : Type*} [Fintype α]

namespace Finset
variable {s t : Finset α} {a b : α}

/--
Definition of `dens` / `dens` 的定义

English:
definition dens
  signature: (s : Finset α)
  body: s.card / Fintype.card α

中文:
定义 dens
  签名: (s : Finset α)
  定义体: s.card / Fintype.card α

Depends on / 依赖: Fintype, Fintype.card, s.card
-/
def dens (s : Finset α) : Rat>=0 := s.card / Fintype.card α

/--
lemma `dens_eq_card_div_card` / 引理 `dens_eq_card_div_card`

English:
lemma dens_eq_card_div_card
  given: (s : Finset α)
  statement: dens s = s.card / Fintype.card α
  proof: rfl

中文:
引理 dens_eq_card_div_card
  条件: (s : Finset α)
  结论: dens s = s.card / Fintype.card α
  证明: rfl
-/
lemma dens_eq_card_div_card (s : Finset α) : dens s = s.card / Fintype.card α := rfl

/--
lemma `dens_empty` / 引理 `dens_empty`

English:
lemma dens_empty
  statement: dens (∅ : Finset α) = 0
  proof: by simp [dens]

中文:
引理 dens_empty
  结论: dens (∅ : Finset α) = 0
  证明: by simp [dens]
-/
@[simp] lemma dens_empty : dens (∅ : Finset α) = 0 := by simp [dens]

/--
lemma `dens_singleton` / 引理 `dens_singleton`

English:
lemma dens_singleton
  given: (a : α)
  statement: dens ({a} : Finset α) = (Fintype.card α : Rat>=0)⁻¹
  proof: by
  simp [dens]

中文:
引理 dens_singleton
  条件: (a : α)
  结论: dens ({a} : Finset α) = (Fintype.card α : Rat>=0)⁻¹
  证明: by
  simp [dens]
-/
@[simp] lemma dens_singleton (a : α) : dens ({a} : Finset α) = (Fintype.card α : Rat>=0)⁻¹ := by
  simp [dens]

/--
lemma `dens_cons` / 引理 `dens_cons`

English:
lemma dens_cons
  given: (h : a ∉ s)
  statement: (s.cons a h).dens = dens s + (Fintype.card α : Rat>=0)⁻¹
  proof: by
  simp [dens, add_div]

中文:
引理 dens_cons
  条件: (h : a ∉ s)
  结论: (s.cons a h).dens = dens s + (Fintype.card α : Rat>=0)⁻¹
  证明: by
  simp [dens, add_div]
-/
@[simp] lemma dens_cons (h : a ∉ s) : (s.cons a h).dens = dens s + (Fintype.card α : Rat>=0)⁻¹ := by
  simp [dens, add_div]

/--
lemma `dens_disjUnion` / 引理 `dens_disjUnion`

English:
lemma dens_disjUnion
  given: (s t : Finset α) (h)
  statement: dens (s.disjUnion t h) = dens s + dens t
  proof: by
  simp_rw [dens, card_disjUnion, Nat.cast_add, add_div]

中文:
引理 dens_disjUnion
  条件: (s t : Finset α) (h)
  结论: dens (s.disjUnion t h) = dens s + dens t
  证明: by
  simp_rw [dens, card_disjUnion, Nat.cast_add, add_div]
-/
@[simp] lemma dens_disjUnion (s t : Finset α) (h) : dens (s.disjUnion t h) = dens s + dens t := by
  simp_rw [dens, card_disjUnion, Nat.cast_add, add_div]

/--
lemma `dens_eq_zero` / 引理 `dens_eq_zero`

English:
lemma dens_eq_zero
  statement: dens s = 0 ↔ s = ∅
  proof: by
  simp +contextual [dens, Fintype.card_eq_zero_iff, eq_empty_of_isEmpty]

中文:
引理 dens_eq_zero
  结论: dens s = 0 ↔ s = ∅
  证明: by
  simp +contextual [dens, Fintype.card_eq_zero_iff, eq_empty_of_isEmpty]
-/
@[simp] lemma dens_eq_zero : dens s = 0 ↔ s = ∅ := by
  simp +contextual [dens, Fintype.card_eq_zero_iff, eq_empty_of_isEmpty]

/--
lemma `dens_ne_zero` / 引理 `dens_ne_zero`

English:
lemma dens_ne_zero
  statement: dens s != 0 ↔ s.Nonempty
  proof: dens_eq_zero.not.trans nonempty_iff_ne_empty.symm

中文:
引理 dens_ne_zero
  结论: dens s != 0 ↔ s.Nonempty
  证明: dens_eq_zero.not.trans nonempty_iff_ne_empty.symm

Depends on / 依赖: dens_eq_zero, dens_eq_zero.not.trans, nonempty_iff_ne_empty, nonempty_iff_ne_empty.symm
-/
lemma dens_ne_zero : dens s != 0 ↔ s.Nonempty := dens_eq_zero.not.trans nonempty_iff_ne_empty.symm

/--
lemma `dens_pos` / 引理 `dens_pos`

English:
lemma dens_pos
  statement: 0 < dens s ↔ s.Nonempty
  proof: pos_iff_ne_zero.trans dens_ne_zero

protected alias ⟨_, Nonempty.dens_pos⟩ := dens_pos
protected alias ⟨_, Nonempty.dens_ne_zero⟩ := dens_ne_zero

@[gcongr]

中文:
引理 dens_pos
  结论: 0 < dens s ↔ s.Nonempty
  证明: pos_iff_ne_zero.trans dens_ne_zero

protected alias ⟨_, Nonempty.dens_pos⟩ := dens_pos
protected alias ⟨_, Nonempty.dens_ne_zero⟩ := dens_ne_zero

@[gcongr]
-/
@[simp] lemma dens_pos : 0 < dens s ↔ s.Nonempty := pos_iff_ne_zero.trans dens_ne_zero

protected alias ⟨_, Nonempty.dens_pos⟩ := dens_pos
protected alias ⟨_, Nonempty.dens_ne_zero⟩ := dens_ne_zero

@[gcongr]
/--
lemma `dens_le_dens` / 引理 `dens_le_dens`

English:
lemma dens_le_dens
  given: (h : s subseteq t)
  statement: dens s <= dens t
  proof: div_le_div_of_nonneg_right (mod_cast card_mono h) by positivity

@[gcongr]

中文:
引理 dens_le_dens
  条件: (h : s subseteq t)
  结论: dens s <= dens t
  证明: div_le_div_of_nonneg_right (mod_cast card_mono h) by positivity

@[gcongr]

Depends on / 依赖: card_mono, div_le_div_of_nonneg_right, mod_cast
-/
lemma dens_le_dens (h : s subseteq t) : dens s <= dens t :=
div_le_div_of_nonneg_right (mod_cast card_mono h) by positivity

@[gcongr]
/--
lemma `dens_lt_dens` / 引理 `dens_lt_dens`

English:
lemma dens_lt_dens
  given: (h : s ⊂ t)
  statement: dens s < dens t
  proof: div_lt_div_of_pos_right (by gcongr) mod_cast calc
    0 <= #s := Nat.zero_le _
    _ < #t := by gcongr
    _ <= Fintype.card α := card_le_univ t

中文:
引理 dens_lt_dens
  条件: (h : s ⊂ t)
  结论: dens s < dens t
  证明: div_lt_div_of_pos_right (by gcongr) mod_cast calc
    0 <= #s := Nat.zero_le _
    _ < #t := by gcongr
    _ <= Fintype.card α := card_le_univ t

Depends on / 依赖: Fintype, Fintype.card, Nat.zero_le, card_le_univ, div_lt_div_of_pos_right, mod_cast, zero_le
-/
lemma dens_lt_dens (h : s ⊂ t) : dens s < dens t :=
div_lt_div_of_pos_right (by gcongr) mod_cast calc
    0 <= #s := Nat.zero_le _
    _ < #t := by gcongr
    _ <= Fintype.card α := card_le_univ t

/--
lemma `dens_mono` / 引理 `dens_mono`

English:
lemma dens_mono
  statement: Monotone (dens : Finset α -> Rat>=0)
  proof: fun _ _ => dens_le_dens

中文:
引理 dens_mono
  结论: Monotone (dens : Finset α -> Rat>=0)
  证明: fun _ _ => dens_le_dens
-/
@[mono] lemma dens_mono : Monotone (dens : Finset α -> Rat>=0) := fun _ _ => dens_le_dens
/--
lemma `dens_strictMono` / 引理 `dens_strictMono`

English:
lemma dens_strictMono
  statement: StrictMono (dens : Finset α -> Rat>=0)
  proof: fun _ _ => dens_lt_dens

中文:
引理 dens_strictMono
  结论: StrictMono (dens : Finset α -> Rat>=0)
  证明: fun _ _ => dens_lt_dens
-/
@[mono] lemma dens_strictMono : StrictMono (dens : Finset α -> Rat>=0) := fun _ _ => dens_lt_dens

/--
lemma `dens_map_le` / 引理 `dens_map_le`

English:
lemma dens_map_le
  given: [Fintype β] (f : α ↪ β)
  statement: dens (s.map f) <= dens s
  proof: by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  simp_rw [dens, card_map]
  gcongr
  · exact mod_cast Fintype.card_pos
  · exact Fintype.card_le_of_injective _ f.2

中文:
引理 dens_map_le
  条件: [Fintype β] (f : α ↪ β)
  结论: dens (s.map f) <= dens s
  证明: by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  simp_rw [dens, card_map]
  gcongr
  · exact mod_cast Fintype.card_pos
  · exact Fintype.card_le_of_injective _ f.2

Depends on / 依赖: Fintype, Fintype.card_le_of_injective, Fintype.card_pos, Subsingleton, Subsingleton.elim, card_le_of_injective, card_map, card_pos, isEmpty_or_nonempty, mod_cast, simp_rw
-/
lemma dens_map_le [Fintype β] (f : α ↪ β) : dens (s.map f) <= dens s := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  simp_rw [dens, card_map]
  gcongr
  · exact mod_cast Fintype.card_pos
  · exact Fintype.card_le_of_injective _ f.2

/--
lemma `dens_map_equiv` / 引理 `dens_map_equiv`

English:
lemma dens_map_equiv
  given: [Fintype β] (e : α ≃ β)
  statement: (s.map e.toEmbedding).dens = s.dens
  proof: by
  simp [dens, Fintype.card_congr e]

中文:
引理 dens_map_equiv
  条件: [Fintype β] (e : α ≃ β)
  结论: (s.map e.toEmbedding).dens = s.dens
  证明: by
  simp [dens, Fintype.card_congr e]
-/
@[simp] lemma dens_map_equiv [Fintype β] (e : α ≃ β) : (s.map e.toEmbedding).dens = s.dens := by
  simp [dens, Fintype.card_congr e]

/--
lemma `dens_image` / 引理 `dens_image`

English:
lemma dens_image
  given: [Fintype β] [DecidableEq β] {f : α -> β} (hf : Bijective f) (s : Finset α)
  proof: by
  simpa [map_eq_image, -dens_map_equiv] using dens_map_equiv (.ofBijective f hf)

中文:
引理 dens_image
  条件: [Fintype β] [DecidableEq β] {f : α -> β} (hf : Bijective f) (s : Finset α)
  证明: by
  simpa [map_eq_image, -dens_map_equiv] using dens_map_equiv (.ofBijective f hf)

Depends on / 依赖: dens_map_equiv, map_eq_image, ofBijective
-/
lemma dens_image [Fintype β] [DecidableEq β] {f : α -> β} (hf : Bijective f) (s : Finset α) :
    (s.image f).dens = s.dens := by
  simpa [map_eq_image, -dens_map_equiv] using dens_map_equiv (.ofBijective f hf)

/--
lemma `card_mul_dens` / 引理 `card_mul_dens`

English:
lemma card_mul_dens
  given: (s : Finset α)
  statement: Fintype.card α * s.dens = s.card
  proof: by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  rw [dens]; rw [mul_div_cancel₀]
  exact mod_cast Fintype.card_ne_zero

中文:
引理 card_mul_dens
  条件: (s : Finset α)
  结论: Fintype.card α * s.dens = s.card
  证明: by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  rw [dens]; rw [mul_div_cancel₀]
  exact mod_cast Fintype.card_ne_zero
-/
@[simp] lemma card_mul_dens (s : Finset α) : Fintype.card α * s.dens = s.card := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  rw [dens]; rw [mul_div_cancel₀]
  exact mod_cast Fintype.card_ne_zero

/--
lemma `dens_mul_card` / 引理 `dens_mul_card`

English:
lemma dens_mul_card
  given: (s : Finset α)
  statement: s.dens * Fintype.card α = s.card
  proof: by
  rw [mul_comm]; rw [card_mul_dens]

中文:
引理 dens_mul_card
  条件: (s : Finset α)
  结论: s.dens * Fintype.card α = s.card
  证明: by
  rw [mul_comm]; rw [card_mul_dens]
-/
@[simp] lemma dens_mul_card (s : Finset α) : s.dens * Fintype.card α = s.card := by
  rw [mul_comm]; rw [card_mul_dens]

section Semifield
variable [Semifield 𝕜] [CharZero 𝕜]

/--
lemma `natCast_card_mul_nnratCast_dens` / 引理 `natCast_card_mul_nnratCast_dens`

English:
lemma natCast_card_mul_nnratCast_dens
  given: (s : Finset α)
  proof: mod_cast s.card_mul_dens

中文:
引理 natCast_card_mul_nnratCast_dens
  条件: (s : Finset α)
  证明: mod_cast s.card_mul_dens
-/
@[simp] lemma natCast_card_mul_nnratCast_dens (s : Finset α) :
    (Fintype.card α * s.dens : 𝕜) = s.card := mod_cast s.card_mul_dens

/--
lemma `nnratCast_dens_mul_natCast_card` / 引理 `nnratCast_dens_mul_natCast_card`

English:
lemma nnratCast_dens_mul_natCast_card
  given: (s : Finset α)
  proof: mod_cast s.dens_mul_card

中文:
引理 nnratCast_dens_mul_natCast_card
  条件: (s : Finset α)
  证明: mod_cast s.dens_mul_card
-/
@[simp] lemma nnratCast_dens_mul_natCast_card (s : Finset α) :
    (s.dens * Fintype.card α : 𝕜) = s.card := mod_cast s.dens_mul_card

/--
lemma `nnratCast_dens` / 引理 `nnratCast_dens`

English:
lemma nnratCast_dens
  given: (s : Finset α)
  statement: (s.dens : 𝕜) = s.card / Fintype.card α
  proof: by
  simp [dens]

中文:
引理 nnratCast_dens
  条件: (s : Finset α)
  结论: (s.dens : 𝕜) = s.card / Fintype.card α
  证明: by
  simp [dens]
-/
@[norm_cast] lemma nnratCast_dens (s : Finset α) : (s.dens : 𝕜) = s.card / Fintype.card α := by
  simp [dens]

end Semifield

section Nonempty
variable [Nonempty α]

/--
lemma `dens_univ` / 引理 `dens_univ`

English:
lemma dens_univ
  statement: dens (univ : Finset α) = 1
  proof: by simp [dens, card_univ]

中文:
引理 dens_univ
  结论: dens (univ : Finset α) = 1
  证明: by simp [dens, card_univ]
-/
@[simp] lemma dens_univ : dens (univ : Finset α) = 1 := by simp [dens, card_univ]

/--
lemma `dens_eq_one` / 引理 `dens_eq_one`

English:
lemma dens_eq_one
  statement: dens s = 1 ↔ s = univ
  proof: by
  simp [dens, div_eq_one_iff_eq, card_eq_iff_eq_univ]

中文:
引理 dens_eq_one
  结论: dens s = 1 ↔ s = univ
  证明: by
  simp [dens, div_eq_one_iff_eq, card_eq_iff_eq_univ]
-/
@[simp] lemma dens_eq_one : dens s = 1 ↔ s = univ := by
  simp [dens, div_eq_one_iff_eq, card_eq_iff_eq_univ]

/--
lemma `dens_ne_one` / 引理 `dens_ne_one`

English:
lemma dens_ne_one
  statement: dens s != 1 ↔ s != univ
  proof: dens_eq_one.not

中文:
引理 dens_ne_one
  结论: dens s != 1 ↔ s != univ
  证明: dens_eq_one.not

Depends on / 依赖: dens_eq_one, dens_eq_one.not
-/
lemma dens_ne_one : dens s != 1 ↔ s != univ := dens_eq_one.not

end Nonempty

/--
lemma `dens_le_one` / 引理 `dens_le_one`

English:
lemma dens_le_one
  statement: s.dens <= 1
  proof: by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  · simpa using dens_le_dens s.subset_univ

中文:
引理 dens_le_one
  结论: s.dens <= 1
  证明: by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  · simpa using dens_le_dens s.subset_univ
-/
@[simp] lemma dens_le_one : s.dens <= 1 := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  · simpa using dens_le_dens s.subset_univ

section Lattice
variable [DecidableEq α]

/--
lemma `dens_union_add_dens_inter` / 引理 `dens_union_add_dens_inter`

English:
lemma dens_union_add_dens_inter
  given: (s t : Finset α)
  proof: by
  simp_rw [dens, ← add_div, ← Nat.cast_add, card_union_add_card_inter]

中文:
引理 dens_union_add_dens_inter
  条件: (s t : Finset α)
  证明: by
  simp_rw [dens, ← add_div, ← Nat.cast_add, card_union_add_card_inter]

Depends on / 依赖: Nat.cast_add, add_div, card_union_add_card_inter, cast_add, simp_rw
-/
lemma dens_union_add_dens_inter (s t : Finset α) :
    dens (s union t) + dens (s inter t) = dens s + dens t := by
  simp_rw [dens, ← add_div, ← Nat.cast_add, card_union_add_card_inter]

/--
lemma `dens_inter_add_dens_union` / 引理 `dens_inter_add_dens_union`

English:
lemma dens_inter_add_dens_union
  given: (s t : Finset α)
  proof: by rw [add_comm, dens_union_add_dens_inter]

中文:
引理 dens_inter_add_dens_union
  条件: (s t : Finset α)
  证明: by rw [add_comm, dens_union_add_dens_inter]

Depends on / 依赖: add_comm, dens_union_add_dens_inter
-/
lemma dens_inter_add_dens_union (s t : Finset α) :
    dens (s inter t) + dens (s union t) = dens s + dens t := by rw [add_comm, dens_union_add_dens_inter]

/--
lemma `dens_union_of_disjoint` / 引理 `dens_union_of_disjoint`

English:
lemma dens_union_of_disjoint
  given: (h : Disjoint s t)
  statement: dens (s union t) = dens s + dens t
  proof: by
  rw [← disjUnion_eq_union s t h]; rw [dens_disjUnion]

中文:
引理 dens_union_of_disjoint
  条件: (h : Disjoint s t)
  结论: dens (s union t) = dens s + dens t
  证明: by
  rw [← disjUnion_eq_union s t h]; rw [dens_disjUnion]
-/
@[simp] lemma dens_union_of_disjoint (h : Disjoint s t) : dens (s union t) = dens s + dens t := by
  rw [← disjUnion_eq_union s t h]; rw [dens_disjUnion]

/--
lemma `dens_sdiff_add_dens_eq_dens` / 引理 `dens_sdiff_add_dens_eq_dens`

English:
lemma dens_sdiff_add_dens_eq_dens
  given: (h : s subseteq t)
  statement: dens (t \ s) + dens s = dens t
  proof: by
  simp [dens, ← card_sdiff_add_card_eq_card h, add_div]

中文:
引理 dens_sdiff_add_dens_eq_dens
  条件: (h : s subseteq t)
  结论: dens (t \ s) + dens s = dens t
  证明: by
  simp [dens, ← card_sdiff_add_card_eq_card h, add_div]

Depends on / 依赖: add_div, card_sdiff_add_card_eq_card
-/
lemma dens_sdiff_add_dens_eq_dens (h : s subseteq t) : dens (t \ s) + dens s = dens t := by
  simp [dens, ← card_sdiff_add_card_eq_card h, add_div]

/--
lemma `dens_sdiff_add_dens` / 引理 `dens_sdiff_add_dens`

English:
lemma dens_sdiff_add_dens
  given: (s t : Finset α)
  statement: dens (s \ t) + dens t = (s union t).dens
  proof: by
  rw [← dens_union_of_disjoint sdiff_disjoint]; rw [sdiff_union_self_eq_union]

中文:
引理 dens_sdiff_add_dens
  条件: (s t : Finset α)
  结论: dens (s \ t) + dens t = (s union t).dens
  证明: by
  rw [← dens_union_of_disjoint sdiff_disjoint]; rw [sdiff_union_self_eq_union]

Depends on / 依赖: dens_union_of_disjoint, sdiff_disjoint, sdiff_union_self_eq_union
-/
lemma dens_sdiff_add_dens (s t : Finset α) : dens (s \ t) + dens t = (s union t).dens := by
  rw [← dens_union_of_disjoint sdiff_disjoint]; rw [sdiff_union_self_eq_union]

/--
lemma `dens_sdiff_comm` / 引理 `dens_sdiff_comm`

English:
lemma dens_sdiff_comm
  given: (h : card s = card t)
  statement: dens (s \ t) = dens (t \ s)
  proof: add_left_injective (dens t) by
    simp_rw [dens_sdiff_add_dens, union_comm s, ← dens_sdiff_add_dens, dens, h]

@[simp]

中文:
引理 dens_sdiff_comm
  条件: (h : card s = card t)
  结论: dens (s \ t) = dens (t \ s)
  证明: add_left_injective (dens t) by
    simp_rw [dens_sdiff_add_dens, union_comm s, ← dens_sdiff_add_dens, dens, h]

@[simp]

Depends on / 依赖: add_left_injective, dens_sdiff_add_dens, simp_rw, union_comm
-/
lemma dens_sdiff_comm (h : card s = card t) : dens (s \ t) = dens (t \ s) :=
add_left_injective (dens t) by
    simp_rw [dens_sdiff_add_dens, union_comm s, ← dens_sdiff_add_dens, dens, h]

@[simp]
/--
lemma `dens_sdiff_add_dens_inter` / 引理 `dens_sdiff_add_dens_inter`

English:
lemma dens_sdiff_add_dens_inter
  given: (s t : Finset α)
  statement: dens (s \ t) + dens (s inter t) = dens s
  proof: by
  rw [← dens_union_of_disjoint (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]

@[simp]

中文:
引理 dens_sdiff_add_dens_inter
  条件: (s t : Finset α)
  结论: dens (s \ t) + dens (s inter t) = dens s
  证明: by
  rw [← dens_union_of_disjoint (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]

@[simp]

Depends on / 依赖: dens_union_of_disjoint, disjoint_sdiff_inter, sdiff_union_inter
-/
lemma dens_sdiff_add_dens_inter (s t : Finset α) : dens (s \ t) + dens (s inter t) = dens s := by
  rw [← dens_union_of_disjoint (disjoint_sdiff_inter _ _)]; rw [sdiff_union_inter]

@[simp]
/--
lemma `dens_inter_add_dens_sdiff` / 引理 `dens_inter_add_dens_sdiff`

English:
lemma dens_inter_add_dens_sdiff
  given: (s t : Finset α)
  statement: dens (s inter t) + dens (s \ t) = dens s
  proof: by
  rw [add_comm]; rw [dens_sdiff_add_dens_inter]

中文:
引理 dens_inter_add_dens_sdiff
  条件: (s t : Finset α)
  结论: dens (s inter t) + dens (s \ t) = dens s
  证明: by
  rw [add_comm]; rw [dens_sdiff_add_dens_inter]

Depends on / 依赖: add_comm, dens_sdiff_add_dens_inter
-/
lemma dens_inter_add_dens_sdiff (s t : Finset α) : dens (s inter t) + dens (s \ t) = dens s := by
  rw [add_comm]; rw [dens_sdiff_add_dens_inter]

/--
lemma `dens_filter_add_dens_filter_not_eq_dens` / 引理 `dens_filter_add_dens_filter_not_eq_dens`

English:
lemma dens_filter_add_dens_filter_not_eq_dens
  statement: {α : Type*} [Fintype α] {s : Finset α}
  proof: by
  classical
  rw [← dens_union_of_disjoint (disjoint_filter_filter_not ..)]; rw [filter_union_filter_not_eq]

中文:
引理 dens_filter_add_dens_filter_not_eq_dens
  结论: {α : 类型} [Fintype α] {s : Finset α}
  证明: by
  classical
  rw [← dens_union_of_disjoint (disjoint_filter_filter_not ..)]; rw [filter_union_filter_not_eq]

Depends on / 依赖: classical, dens_union_of_disjoint, disjoint_filter_filter_not, filter_union_filter_not_eq
-/
lemma dens_filter_add_dens_filter_not_eq_dens {α : Type*} [Fintype α] {s : Finset α}
    (p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] :
    dens {a in s | p a} + dens {a in s | ¬ p a} = dens s := by
  classical
  rw [← dens_union_of_disjoint (disjoint_filter_filter_not ..)]; rw [filter_union_filter_not_eq]

/--
lemma `dens_union_le` / 引理 `dens_union_le`

English:
lemma dens_union_le
  given: (s t : Finset α)
  statement: dens (s union t) <= dens s + dens t
  proof: dens_union_add_dens_inter s t ▸ le_add_of_nonneg_right zero_le

中文:
引理 dens_union_le
  条件: (s t : Finset α)
  结论: dens (s union t) <= dens s + dens t
  证明: dens_union_add_dens_inter s t ▸ le_add_of_nonneg_right zero_le

Depends on / 依赖: dens_union_add_dens_inter, le_add_of_nonneg_right, zero_le
-/
lemma dens_union_le (s t : Finset α) : dens (s union t) <= dens s + dens t :=
  dens_union_add_dens_inter s t ▸ le_add_of_nonneg_right zero_le

/--
lemma `dens_le_dens_sdiff_add_dens` / 引理 `dens_le_dens_sdiff_add_dens`

English:
lemma dens_le_dens_sdiff_add_dens
  statement: dens s <= dens (s \ t) + dens t
  proof: dens_sdiff_add_dens s _ ▸ dens_le_dens subset_union_left

中文:
引理 dens_le_dens_sdiff_add_dens
  结论: dens s <= dens (s \ t) + dens t
  证明: dens_sdiff_add_dens s _ ▸ dens_le_dens subset_union_left

Depends on / 依赖: dens_le_dens, dens_sdiff_add_dens, subset_union_left
-/
lemma dens_le_dens_sdiff_add_dens : dens s <= dens (s \ t) + dens t :=
  dens_sdiff_add_dens s _ ▸ dens_le_dens subset_union_left

/--
lemma `dens_sdiff` / 引理 `dens_sdiff`

English:
lemma dens_sdiff
  given: (h : s subseteq t)
  statement: dens (t \ s) = dens t - dens s
  proof: eq_tsub_of_add_eq (dens_sdiff_add_dens_eq_dens h)

中文:
引理 dens_sdiff
  条件: (h : s subseteq t)
  结论: dens (t \ s) = dens t - dens s
  证明: eq_tsub_of_add_eq (dens_sdiff_add_dens_eq_dens h)

Depends on / 依赖: dens_sdiff_add_dens_eq_dens, eq_tsub_of_add_eq
-/
lemma dens_sdiff (h : s subseteq t) : dens (t \ s) = dens t - dens s :=
  eq_tsub_of_add_eq (dens_sdiff_add_dens_eq_dens h)

/--
lemma `le_dens_sdiff` / 引理 `le_dens_sdiff`

English:
lemma le_dens_sdiff
  given: (s t : Finset α)
  statement: dens t - dens s <= dens (t \ s)
  proof: tsub_le_iff_right.2 dens_le_dens_sdiff_add_dens

中文:
引理 le_dens_sdiff
  条件: (s t : Finset α)
  结论: dens t - dens s <= dens (t \ s)
  证明: tsub_le_iff_right.2 dens_le_dens_sdiff_add_dens

Depends on / 依赖: dens_le_dens_sdiff_add_dens, tsub_le_iff_right
-/
lemma le_dens_sdiff (s t : Finset α) : dens t - dens s <= dens (t \ s) :=
  tsub_le_iff_right.2 dens_le_dens_sdiff_add_dens

end Lattice
end Finset
