/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Minor.Restrict

/-!
# Some constructions of matroids

This file defines some very elementary examples of matroids, namely those with at most one base.

## Main definitions

* `emptyOn α` is the matroid on `α` with empty ground set.

For `E : Set α`, ...

* `loopyOn E` is the matroid on `E` whose elements are all loops, or equivalently in which `∅`
  is the only base.
* `freeOn E` is the 'free matroid' whose ground set `E` is the only base.
* For `I ⊆ E`, `uniqueBaseOn I E` is the matroid with ground set `E` in which `I` is the only base.

## Implementation details

To avoid the tedious process of certifying the matroid axioms for each of these easy examples,
we bootstrap the definitions starting with `emptyOn α` (which `simp` can prove is a matroid)
and then construct the other examples using duality and restriction.

-/

@[expose] public section

assert_not_exists Field

variable {α : Type*} {M : Matroid α} {E B I X R J : Set α}

namespace Matroid

open Set

section EmptyOn

/--
Definition of `emptyOn` / `emptyOn` 的定义

English:
definition emptyOn
  signature: (α : Type*)
  body: ∅
  IsBase := (· = ∅)
  Indep := (· = ∅)
  indep_iff' := by simp [subset_empty_iff]
  exists_isBase := ⟨∅, rfl⟩
  isBase_exchange := by rintro _ _ rfl; simp
  maximality := by rintro _ _ _ rfl -; exact ⟨∅, by simp [Maximal]⟩
  subset_ground := by simp

中文:
定义 emptyOn
  签名: (α : 类型)
  定义体: ∅
  IsBase := (· = ∅)
  Indep := (· = ∅)
  indep_iff' := by simp [subset_empty_iff]
  exists_isBase := ⟨∅, rfl⟩
  isBase_exchange := by rintro _ _ rfl; simp
  maximality := by rintro _ _ _ rfl -; exact ⟨∅, by simp [Maximal]⟩
  subset_ground := by simp
-/
def emptyOn (α : Type*) : Matroid α where
  E := ∅
  IsBase := (· = ∅)
  Indep := (· = ∅)
  indep_iff' := by simp [subset_empty_iff]
  exists_isBase := ⟨∅, rfl⟩
  isBase_exchange := by rintro _ _ rfl; simp
  maximality := by rintro _ _ _ rfl -; exact ⟨∅, by simp [Maximal]⟩
  subset_ground := by simp

/--
theorem `emptyOn_ground` / 定理 `emptyOn_ground`

English:
theorem emptyOn_ground
  statement: (emptyOn α).E = ∅
  proof: rfl

中文:
定理 emptyOn_ground
  结论: (emptyOn α).E = ∅
  证明: rfl
-/
@[simp] theorem emptyOn_ground : (emptyOn α).E = ∅ := rfl

/--
theorem `emptyOn_isBase_iff` / 定理 `emptyOn_isBase_iff`

English:
theorem emptyOn_isBase_iff
  statement: (emptyOn α).IsBase B ↔ B = ∅
  proof: Iff.rfl

中文:
定理 emptyOn_isBase_iff
  结论: (emptyOn α).IsBase B ↔ B = ∅
  证明: Iff.rfl
-/
@[simp] theorem emptyOn_isBase_iff : (emptyOn α).IsBase B ↔ B = ∅ := Iff.rfl

/--
theorem `emptyOn_indep_iff` / 定理 `emptyOn_indep_iff`

English:
theorem emptyOn_indep_iff
  statement: (emptyOn α).Indep I ↔ I = ∅
  proof: Iff.rfl

中文:
定理 emptyOn_indep_iff
  结论: (emptyOn α).Indep I ↔ I = ∅
  证明: Iff.rfl
-/
@[simp] theorem emptyOn_indep_iff : (emptyOn α).Indep I ↔ I = ∅ := Iff.rfl

/--
theorem `ground_eq_empty_iff` / 定理 `ground_eq_empty_iff`

English:
theorem ground_eq_empty_iff
  statement: (M.E = ∅) ↔ M = emptyOn α
  proof: by
  simp only [emptyOn, ext_iff_indep, iff_self_and]
  exact fun h => by simp [h, subset_empty_iff]

中文:
定理 ground_eq_empty_iff
  结论: (M.E = ∅) ↔ M = emptyOn α
  证明: by
  simp only [emptyOn, ext_iff_indep, iff_self_and]
  exact fun h => by simp [h, subset_empty_iff]

Depends on / 依赖: emptyOn, ext_iff_indep, iff_self_and, subset_empty_iff
-/
theorem ground_eq_empty_iff : (M.E = ∅) ↔ M = emptyOn α := by
  simp only [emptyOn, ext_iff_indep, iff_self_and]
  exact fun h => by simp [h, subset_empty_iff]

/--
theorem `emptyOn_dual_eq` / 定理 `emptyOn_dual_eq`

English:
theorem emptyOn_dual_eq
  statement: (emptyOn α)✶ = emptyOn α
  proof: by
  rw [← ground_eq_empty_iff]; rfl

中文:
定理 emptyOn_dual_eq
  结论: (emptyOn α)✶ = emptyOn α
  证明: by
  rw [← ground_eq_empty_iff]; rfl
-/
@[simp] theorem emptyOn_dual_eq : (emptyOn α)✶ = emptyOn α := by
  rw [← ground_eq_empty_iff]; rfl

/--
theorem `restrict_empty` / 定理 `restrict_empty`

English:
theorem restrict_empty
  given: (M : Matroid α)
  statement: M ↾ (∅ : Set α) = emptyOn α
  proof: by
  simp [← ground_eq_empty_iff]

中文:
定理 restrict_empty
  条件: (M : Matroid α)
  结论: M ↾ (∅ : Set α) = emptyOn α
  证明: by
  simp [← ground_eq_empty_iff]
-/
@[simp] theorem restrict_empty (M : Matroid α) : M ↾ (∅ : Set α) = emptyOn α := by
  simp [← ground_eq_empty_iff]

/--
theorem `eq_emptyOn_or_nonempty` / 定理 `eq_emptyOn_or_nonempty`

English:
theorem eq_emptyOn_or_nonempty
  given: (M : Matroid α)
  statement: M = emptyOn α ∨ Matroid.Nonempty M
  proof: by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_or_nonempty.elim Or.inl (fun h => Or.inr ⟨h⟩)

中文:
定理 eq_emptyOn_or_nonempty
  条件: (M : Matroid α)
  结论: M = emptyOn α ∨ Matroid.Nonempty M
  证明: by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_or_nonempty.elim Or.inl (fun h => Or.inr ⟨h⟩)

Depends on / 依赖: M.E.eq_empty_or_nonempty.elim, Or.inl, Or.inr, eq_empty_or_nonempty, ground_eq_empty_iff
-/
theorem eq_emptyOn_or_nonempty (M : Matroid α) : M = emptyOn α ∨ Matroid.Nonempty M := by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_or_nonempty.elim Or.inl (fun h => Or.inr ⟨h⟩)

/--
theorem `eq_emptyOn` / 定理 `eq_emptyOn`

English:
theorem eq_emptyOn
  given: [IsEmpty α] (M : Matroid α)
  statement: M = emptyOn α
  proof: by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_of_isEmpty

中文:
定理 eq_emptyOn
  条件: [IsEmpty α] (M : Matroid α)
  结论: M = emptyOn α
  证明: by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_of_isEmpty

Depends on / 依赖: M.E.eq_empty_of_isEmpty, eq_empty_of_isEmpty, ground_eq_empty_iff
-/
theorem eq_emptyOn [IsEmpty α] (M : Matroid α) : M = emptyOn α := by
  rw [← ground_eq_empty_iff]
  exact M.E.eq_empty_of_isEmpty

/--
Instance `finite_emptyOn` / 实例 `finite_emptyOn`

English:
instance finite_emptyOn
  signature: (α : Type*)
  body: ⟨finite_empty⟩

中文:
实例 finite_emptyOn
  签名: (α : 类型)
  定义体: ⟨finite_empty⟩

Depends on / 依赖: finite_empty
-/
instance finite_emptyOn (α : Type*) : (emptyOn α).Finite :=
  ⟨finite_empty⟩

end EmptyOn

section LoopyOn

/--
Definition of `loopyOn` / `loopyOn` 的定义

English:
definition loopyOn
  signature: (E : Set α)
  body: emptyOn α ↾ E

中文:
定义 loopyOn
  签名: (E : Set α)
  定义体: emptyOn α ↾ E

Depends on / 依赖: emptyOn
-/
def loopyOn (E : Set α) : Matroid α := emptyOn α ↾ E

/--
theorem `loopyOn_ground` / 定理 `loopyOn_ground`

English:
theorem loopyOn_ground
  given: (E : Set α)
  statement: (loopyOn E).E = E
  proof: rfl

中文:
定理 loopyOn_ground
  条件: (E : Set α)
  结论: (loopyOn E).E = E
  证明: rfl
-/
@[simp] theorem loopyOn_ground (E : Set α) : (loopyOn E).E = E := rfl

/--
theorem `loopyOn_empty` / 定理 `loopyOn_empty`

English:
theorem loopyOn_empty
  given: (α : Type*)
  statement: loopyOn (∅ : Set α) = emptyOn α
  proof: by
  rw [← ground_eq_empty_iff]; rw [loopyOn_ground]

中文:
定理 loopyOn_empty
  条件: (α : 类型)
  结论: loopyOn (∅ : Set α) = emptyOn α
  证明: by
  rw [← ground_eq_empty_iff]; rw [loopyOn_ground]
-/
@[simp] theorem loopyOn_empty (α : Type*) : loopyOn (∅ : Set α) = emptyOn α := by
  rw [← ground_eq_empty_iff]; rw [loopyOn_ground]

/--
theorem `loopyOn_indep_iff` / 定理 `loopyOn_indep_iff`

English:
theorem loopyOn_indep_iff
  statement: (loopyOn E).Indep I ↔ I = ∅
  proof: by
  simp only [loopyOn, restrict_indep_iff, emptyOn_indep_iff, and_iff_left_iff_imp]
  rintro rfl; apply empty_subset

中文:
定理 loopyOn_indep_iff
  结论: (loopyOn E).Indep I ↔ I = ∅
  证明: by
  simp only [loopyOn, restrict_indep_iff, emptyOn_indep_iff, and_iff_left_iff_imp]
  rintro rfl; apply empty_subset
-/
@[simp] theorem loopyOn_indep_iff : (loopyOn E).Indep I ↔ I = ∅ := by
  simp only [loopyOn, restrict_indep_iff, emptyOn_indep_iff, and_iff_left_iff_imp]
  rintro rfl; apply empty_subset

/--
theorem `eq_loopyOn_iff` / 定理 `eq_loopyOn_iff`

English:
theorem eq_loopyOn_iff
  statement: M = loopyOn E ↔ M.E = E ∧ forall X subseteq M.E, M.Indep X -> X = ∅
  proof: by
  simp only [ext_iff_indep, loopyOn_ground, loopyOn_indep_iff, and_congr_right_iff]
  rintro rfl
  refine ⟨fun h I hI => (h hI).1, fun h I hIE => ⟨h I hIE, by rintro rfl; simp⟩⟩

中文:
定理 eq_loopyOn_iff
  结论: M = loopyOn E ↔ M.E = E ∧ 对任意 X subseteq M.E, M.Indep X -> X = ∅
  证明: by
  simp only [ext_iff_indep, loopyOn_ground, loopyOn_indep_iff, and_congr_right_iff]
  rintro rfl
  refine ⟨fun h I hI => (h hI).1, fun h I hIE => ⟨h I hIE, by rintro rfl; simp⟩⟩

Depends on / 依赖: and_congr_right_iff, ext_iff_indep, loopyOn_ground, loopyOn_indep_iff
-/
theorem eq_loopyOn_iff : M = loopyOn E ↔ M.E = E ∧ forall X subseteq M.E, M.Indep X -> X = ∅ := by
  simp only [ext_iff_indep, loopyOn_ground, loopyOn_indep_iff, and_congr_right_iff]
  rintro rfl
  refine ⟨fun h I hI => (h hI).1, fun h I hIE => ⟨h I hIE, by rintro rfl; simp⟩⟩

/--
theorem `loopyOn_isBase_iff` / 定理 `loopyOn_isBase_iff`

English:
theorem loopyOn_isBase_iff
  statement: (loopyOn E).IsBase B ↔ B = ∅
  proof: by
  simp [Maximal, isBase_iff_maximal_indep]

中文:
定理 loopyOn_isBase_iff
  结论: (loopyOn E).IsBase B ↔ B = ∅
  证明: by
  simp [Maximal, isBase_iff_maximal_indep]
-/
@[simp] theorem loopyOn_isBase_iff : (loopyOn E).IsBase B ↔ B = ∅ := by
  simp [Maximal, isBase_iff_maximal_indep]

/--
theorem `loopyOn_isBasis_iff` / 定理 `loopyOn_isBasis_iff`

English:
theorem loopyOn_isBasis_iff
  statement: (loopyOn E).IsBasis I X ↔ I = ∅ ∧ X subseteq E
  proof: ⟨fun h => ⟨loopyOn_indep_iff.mp h.indep, h.subset_ground⟩,
    by rintro ⟨rfl, hX⟩; rw [isBasis_iff]; simp⟩

中文:
定理 loopyOn_isBasis_iff
  结论: (loopyOn E).IsBasis I X ↔ I = ∅ ∧ X subseteq E
  证明: ⟨fun h => ⟨loopyOn_indep_iff.mp h.indep, h.subset_ground⟩,
    by rintro ⟨rfl, hX⟩; rw [isBasis_iff]; simp⟩
-/
@[simp] theorem loopyOn_isBasis_iff : (loopyOn E).IsBasis I X ↔ I = ∅ ∧ X subseteq E :=
  ⟨fun h => ⟨loopyOn_indep_iff.mp h.indep, h.subset_ground⟩,
    by rintro ⟨rfl, hX⟩; rw [isBasis_iff]; simp⟩

/--
Instance `loopyOn_rankFinite` / 实例 `loopyOn_rankFinite`

English:
instance loopyOn_rankFinite
  signature: : RankFinite (loopyOn E)
  body: ⟨∅, by simp⟩

中文:
实例 loopyOn_rankFinite
  签名: : RankFinite (loopyOn E)
  定义体: ⟨∅, by simp⟩
-/
instance loopyOn_rankFinite : RankFinite (loopyOn E) :=
  ⟨∅, by simp⟩

/--
theorem `Finite.loopyOn_finite` / 定理 `Finite.loopyOn_finite`

English:
theorem Finite.loopyOn_finite
  given: (hE : E.Finite)
  statement: Matroid.Finite (loopyOn E)
  proof: ⟨hE⟩

中文:
定理 Finite.loopyOn_finite
  条件: (hE : E.Finite)
  结论: Matroid.Finite (loopyOn E)
  证明: ⟨hE⟩
-/
theorem Finite.loopyOn_finite (hE : E.Finite) : Matroid.Finite (loopyOn E) :=
  ⟨hE⟩

/--
theorem `loopyOn_restrict` / 定理 `loopyOn_restrict`

English:
theorem loopyOn_restrict
  given: (E R : Set α)
  statement: (loopyOn E) ↾ R = loopyOn R
  proof: by
  refine ext_indep rfl ?_
  simp only [restrict_ground_eq, restrict_indep_iff, loopyOn_indep_iff, and_iff_left_iff_imp]
  exact fun _ h _ => h

中文:
定理 loopyOn_restrict
  条件: (E R : Set α)
  结论: (loopyOn E) ↾ R = loopyOn R
  证明: by
  refine ext_indep rfl ?_
  simp only [restrict_ground_eq, restrict_indep_iff, loopyOn_indep_iff, and_iff_left_iff_imp]
  exact fun _ h _ => h
-/
@[simp] theorem loopyOn_restrict (E R : Set α) : (loopyOn E) ↾ R = loopyOn R := by
  refine ext_indep rfl ?_
  simp only [restrict_ground_eq, restrict_indep_iff, loopyOn_indep_iff, and_iff_left_iff_imp]
  exact fun _ h _ => h

/--
theorem `empty_isBase_iff` / 定理 `empty_isBase_iff`

English:
theorem empty_isBase_iff
  statement: M.IsBase ∅ ↔ M = loopyOn M.E
  proof: by
  simp only [isBase_iff_maximal_indep, Maximal, empty_indep, empty_subset,
    subset_empty_iff, true_implies, true_and, ext_iff_indep, loopyOn_ground,
    loopyOn_indep_iff]
  exact ⟨fun h I _ => ⟨@h _, fun hI => by simp [hI]⟩, fun h I hI => (h hI.subset_ground).1 hI⟩

中文:
定理 empty_isBase_iff
  结论: M.IsBase ∅ ↔ M = loopyOn M.E
  证明: by
  simp only [isBase_iff_maximal_indep, Maximal, empty_indep, empty_subset,
    subset_empty_iff, true_implies, true_and, ext_iff_indep, loopyOn_ground,
    loopyOn_indep_iff]
  exact ⟨fun h I _ => ⟨@h _, fun hI => by simp [hI]⟩, fun h I hI => (h hI.subset_ground).1 hI⟩

Depends on / 依赖: Maximal, empty_indep, empty_subset, ext_iff_indep, hI.subset_ground, isBase_iff_maximal_indep, loopyOn_ground, loopyOn_indep_iff, subset_empty_iff, subset_ground, true_and, true_implies
-/
theorem empty_isBase_iff : M.IsBase ∅ ↔ M = loopyOn M.E := by
  simp only [isBase_iff_maximal_indep, Maximal, empty_indep, empty_subset,
    subset_empty_iff, true_implies, true_and, ext_iff_indep, loopyOn_ground,
    loopyOn_indep_iff]
  exact ⟨fun h I _ => ⟨@h _, fun hI => by simp [hI]⟩, fun h I hI => (h hI.subset_ground).1 hI⟩

/--
theorem `eq_loopyOn_or_rankPos` / 定理 `eq_loopyOn_or_rankPos`

English:
theorem eq_loopyOn_or_rankPos
  given: (M : Matroid α)
  statement: M = loopyOn M.E ∨ RankPos M
  proof: by
  rw [← empty_isBase_iff]; rw [rankPos_iff]; apply em

中文:
定理 eq_loopyOn_or_rankPos
  条件: (M : Matroid α)
  结论: M = loopyOn M.E ∨ RankPos M
  证明: by
  rw [← empty_isBase_iff]; rw [rankPos_iff]; apply em

Depends on / 依赖: empty_isBase_iff, rankPos_iff
-/
theorem eq_loopyOn_or_rankPos (M : Matroid α) : M = loopyOn M.E ∨ RankPos M := by
  rw [← empty_isBase_iff]; rw [rankPos_iff]; apply em

/--
theorem `not_rankPos_iff` / 定理 `not_rankPos_iff`

English:
theorem not_rankPos_iff
  statement: ¬RankPos M ↔ M = loopyOn M.E
  proof: by
  rw [rankPos_iff]; rw [not_iff_comm]; rw [empty_isBase_iff]

中文:
定理 not_rankPos_iff
  结论: ¬RankPos M ↔ M = loopyOn M.E
  证明: by
  rw [rankPos_iff]; rw [not_iff_comm]; rw [empty_isBase_iff]

Depends on / 依赖: empty_isBase_iff, not_iff_comm, rankPos_iff
-/
theorem not_rankPos_iff : ¬RankPos M ↔ M = loopyOn M.E := by
  rw [rankPos_iff]; rw [not_iff_comm]; rw [empty_isBase_iff]

end LoopyOn

section FreeOn

/--
Definition of `freeOn` / `freeOn` 的定义

English:
definition freeOn
  signature: (E : Set α)
  body: (loopyOn E)✶

中文:
定义 freeOn
  签名: (E : Set α)
  定义体: (loopyOn E)✶

Depends on / 依赖: loopyOn
-/
def freeOn (E : Set α) : Matroid α := (loopyOn E)✶

/--
theorem `freeOn_ground` / 定理 `freeOn_ground`

English:
theorem freeOn_ground
  statement: (freeOn E).E = E
  proof: rfl

中文:
定理 freeOn_ground
  结论: (freeOn E).E = E
  证明: rfl
-/
@[simp] theorem freeOn_ground : (freeOn E).E = E := rfl

/--
theorem `freeOn_dual_eq` / 定理 `freeOn_dual_eq`

English:
theorem freeOn_dual_eq
  statement: (freeOn E)✶ = loopyOn E
  proof: by
  rw [freeOn]; rw [dual_dual]

中文:
定理 freeOn_dual_eq
  结论: (freeOn E)✶ = loopyOn E
  证明: by
  rw [freeOn]; rw [dual_dual]
-/
@[simp] theorem freeOn_dual_eq : (freeOn E)✶ = loopyOn E := by
  rw [freeOn]; rw [dual_dual]

/--
theorem `loopyOn_dual_eq` / 定理 `loopyOn_dual_eq`

English:
theorem loopyOn_dual_eq
  statement: (loopyOn E)✶ = freeOn E
  proof: rfl

中文:
定理 loopyOn_dual_eq
  结论: (loopyOn E)✶ = freeOn E
  证明: rfl
-/
@[simp] theorem loopyOn_dual_eq : (loopyOn E)✶ = freeOn E := rfl

/--
theorem `freeOn_empty` / 定理 `freeOn_empty`

English:
theorem freeOn_empty
  given: (α : Type*)
  statement: freeOn (∅ : Set α) = emptyOn α
  proof: by
  simp [freeOn]

中文:
定理 freeOn_empty
  条件: (α : 类型)
  结论: freeOn (∅ : Set α) = emptyOn α
  证明: by
  simp [freeOn]
-/
@[simp] theorem freeOn_empty (α : Type*) : freeOn (∅ : Set α) = emptyOn α := by
  simp [freeOn]

/--
theorem `freeOn_isBase_iff` / 定理 `freeOn_isBase_iff`

English:
theorem freeOn_isBase_iff
  statement: (freeOn E).IsBase B ↔ B = E
  proof: by
  simp only [freeOn, loopyOn_ground, dual_isBase_iff', loopyOn_isBase_iff, sdiff_eq_empty,
    ← subset_antisymm_iff, eq_comm (a := E)]

中文:
定理 freeOn_isBase_iff
  结论: (freeOn E).IsBase B ↔ B = E
  证明: by
  simp only [freeOn, loopyOn_ground, dual_isBase_iff', loopyOn_isBase_iff, sdiff_eq_empty,
    ← subset_antisymm_iff, eq_comm (a := E)]
-/
@[simp] theorem freeOn_isBase_iff : (freeOn E).IsBase B ↔ B = E := by
  simp only [freeOn, loopyOn_ground, dual_isBase_iff', loopyOn_isBase_iff, sdiff_eq_empty,
    ← subset_antisymm_iff, eq_comm (a := E)]

/--
theorem `freeOn_indep_iff` / 定理 `freeOn_indep_iff`

English:
theorem freeOn_indep_iff
  statement: (freeOn E).Indep I ↔ I subseteq E
  proof: by
  simp [indep_iff]

中文:
定理 freeOn_indep_iff
  结论: (freeOn E).Indep I ↔ I subseteq E
  证明: by
  simp [indep_iff]
-/
@[simp] theorem freeOn_indep_iff : (freeOn E).Indep I ↔ I subseteq E := by
  simp [indep_iff]

/--
theorem `freeOn_indep` / 定理 `freeOn_indep`

English:
theorem freeOn_indep
  given: (hIE : I subseteq E)
  statement: (freeOn E).Indep I
  proof: freeOn_indep_iff.2 hIE

中文:
定理 freeOn_indep
  条件: (hIE : I subseteq E)
  结论: (freeOn E).Indep I
  证明: freeOn_indep_iff.2 hIE

Depends on / 依赖: freeOn_indep_iff
-/
theorem freeOn_indep (hIE : I subseteq E) : (freeOn E).Indep I :=
  freeOn_indep_iff.2 hIE

/--
theorem `freeOn_isBasis_iff` / 定理 `freeOn_isBasis_iff`

English:
theorem freeOn_isBasis_iff
  statement: (freeOn E).IsBasis I X ↔ I = X ∧ X subseteq E
  proof: by
  use fun h => ⟨(freeOn_indep h.subset_ground).eq_of_isBasis h, h.subset_ground⟩
  rintro ⟨rfl, hIE⟩
  exact (freeOn_indep hIE).isBasis_self

中文:
定理 freeOn_isBasis_iff
  结论: (freeOn E).IsBasis I X ↔ I = X ∧ X subseteq E
  证明: by
  use fun h => ⟨(freeOn_indep h.subset_ground).eq_of_isBasis h, h.subset_ground⟩
  rintro ⟨rfl, hIE⟩
  exact (freeOn_indep hIE).isBasis_self
-/
@[simp] theorem freeOn_isBasis_iff : (freeOn E).IsBasis I X ↔ I = X ∧ X subseteq E := by
  use fun h => ⟨(freeOn_indep h.subset_ground).eq_of_isBasis h, h.subset_ground⟩
  rintro ⟨rfl, hIE⟩
  exact (freeOn_indep hIE).isBasis_self

/--
theorem `freeOn_isBasis'_iff` / 定理 `freeOn_isBasis'_iff`

English:
theorem freeOn_isBasis'_iff
  statement: (freeOn E).IsBasis' I X ↔ I = X inter E
  proof: by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [freeOn_isBasis_iff]; rw [freeOn_ground]; rw [and_iff_left inter_subset_right]

中文:
定理 freeOn_isBasis'_iff
  结论: (freeOn E).IsBasis' I X ↔ I = X inter E
  证明: by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [freeOn_isBasis_iff]; rw [freeOn_ground]; rw [and_iff_left inter_subset_right]
-/
@[simp] theorem freeOn_isBasis'_iff : (freeOn E).IsBasis' I X ↔ I = X inter E := by
  rw [isBasis'_iff_isBasis_inter_ground]; rw [freeOn_isBasis_iff]; rw [freeOn_ground]; rw [and_iff_left inter_subset_right]

/--
theorem `eq_freeOn_iff` / 定理 `eq_freeOn_iff`

English:
theorem eq_freeOn_iff
  statement: M = freeOn E ↔ M.E = E ∧ M.Indep E
  proof: by
  refine ⟨?_, fun h => ?_⟩
  · rintro rfl; simp
  simp only [ext_iff_indep, freeOn_ground, freeOn_indep_iff, h.1, true_and]
  exact fun I hIX => iff_of_true (h.2.subset hIX) hIX

中文:
定理 eq_freeOn_iff
  结论: M = freeOn E ↔ M.E = E ∧ M.Indep E
  证明: by
  refine ⟨?_, fun h => ?_⟩
  · rintro rfl; simp
  simp only [ext_iff_indep, freeOn_ground, freeOn_indep_iff, h.1, true_and]
  exact fun I hIX => iff_of_true (h.2.subset hIX) hIX

Depends on / 依赖: ext_iff_indep, freeOn_ground, freeOn_indep_iff, iff_of_true, subset, true_and
-/
theorem eq_freeOn_iff : M = freeOn E ↔ M.E = E ∧ M.Indep E := by
  refine ⟨?_, fun h => ?_⟩
  · rintro rfl; simp
  simp only [ext_iff_indep, freeOn_ground, freeOn_indep_iff, h.1, true_and]
  exact fun I hIX => iff_of_true (h.2.subset hIX) hIX

/--
theorem `ground_indep_iff_eq_freeOn` / 定理 `ground_indep_iff_eq_freeOn`

English:
theorem ground_indep_iff_eq_freeOn
  statement: M.Indep M.E ↔ M = freeOn M.E
  proof: by
  simp [eq_freeOn_iff]

中文:
定理 ground_indep_iff_eq_freeOn
  结论: M.Indep M.E ↔ M = freeOn M.E
  证明: by
  simp [eq_freeOn_iff]

Depends on / 依赖: eq_freeOn_iff
-/
theorem ground_indep_iff_eq_freeOn : M.Indep M.E ↔ M = freeOn M.E := by
  simp [eq_freeOn_iff]

/--
theorem `freeOn_restrict` / 定理 `freeOn_restrict`

English:
theorem freeOn_restrict
  given: (h : R subseteq E)
  statement: (freeOn E) ↾ R = freeOn R
  proof: by
  simp [h, eq_freeOn_iff]

中文:
定理 freeOn_restrict
  条件: (h : R subseteq E)
  结论: (freeOn E) ↾ R = freeOn R
  证明: by
  simp [h, eq_freeOn_iff]

Depends on / 依赖: eq_freeOn_iff
-/
theorem freeOn_restrict (h : R subseteq E) : (freeOn E) ↾ R = freeOn R := by
  simp [h, eq_freeOn_iff]

/--
theorem `restrict_eq_freeOn_iff` / 定理 `restrict_eq_freeOn_iff`

English:
theorem restrict_eq_freeOn_iff
  statement: M ↾ I = freeOn I ↔ M.Indep I
  proof: by
  rw [eq_freeOn_iff]; rw [and_iff_right M.restrict_ground_eq]; rw [restrict_indep_iff]; rw [and_iff_left Subset.rfl]

中文:
定理 restrict_eq_freeOn_iff
  结论: M ↾ I = freeOn I ↔ M.Indep I
  证明: by
  rw [eq_freeOn_iff]; rw [and_iff_right M.restrict_ground_eq]; rw [restrict_indep_iff]; rw [and_iff_left Subset.rfl]

Depends on / 依赖: M.restrict_ground_eq, Subset, Subset.rfl, and_iff_left, and_iff_right, eq_freeOn_iff, restrict_ground_eq, restrict_indep_iff
-/
theorem restrict_eq_freeOn_iff : M ↾ I = freeOn I ↔ M.Indep I := by
  rw [eq_freeOn_iff]; rw [and_iff_right M.restrict_ground_eq]; rw [restrict_indep_iff]; rw [and_iff_left Subset.rfl]

/--
theorem `Indep.restrict_eq_freeOn` / 定理 `Indep.restrict_eq_freeOn`

English:
theorem Indep.restrict_eq_freeOn
  given: (hI : M.Indep I)
  statement: M ↾ I = freeOn I
  proof: by
  rwa [restrict_eq_freeOn_iff]

中文:
定理 Indep.restrict_eq_freeOn
  条件: (hI : M.Indep I)
  结论: M ↾ I = freeOn I
  证明: by
  rwa [restrict_eq_freeOn_iff]

Depends on / 依赖: restrict_eq_freeOn_iff
-/
theorem Indep.restrict_eq_freeOn (hI : M.Indep I) : M ↾ I = freeOn I := by
  rwa [restrict_eq_freeOn_iff]

/--
Instance `freeOn_finitary` / 实例 `freeOn_finitary`

English:
instance freeOn_finitary
  signature: : Finitary (freeOn E)
  body: by
  simp only [finitary_iff, freeOn_indep_iff]
  exact fun I h e heI => by simpa using h {e} (by simpa)

中文:
实例 freeOn_finitary
  签名: : Finitary (freeOn E)
  定义体: by
  simp only [finitary_iff, freeOn_indep_iff]
  exact fun I h e heI => by simpa using h {e} (by simpa)

Depends on / 依赖: finitary_iff, freeOn_indep_iff
-/
instance freeOn_finitary : Finitary (freeOn E) := by
  simp only [finitary_iff, freeOn_indep_iff]
  exact fun I h e heI => by simpa using h {e} (by simpa)

/--
lemma `freeOn_rankPos` / 引理 `freeOn_rankPos`

English:
lemma freeOn_rankPos
  given: (hE : E.Nonempty)
  statement: RankPos (freeOn E)
  proof: by
  simp [rankPos_iff, hE.ne_empty.symm]

中文:
引理 freeOn_rankPos
  条件: (hE : E.Nonempty)
  结论: RankPos (freeOn E)
  证明: by
  simp [rankPos_iff, hE.ne_empty.symm]

Depends on / 依赖: hE.ne_empty.symm, ne_empty, rankPos_iff
-/
lemma freeOn_rankPos (hE : E.Nonempty) : RankPos (freeOn E) := by
  simp [rankPos_iff, hE.ne_empty.symm]

end FreeOn

section uniqueBaseOn

/--
Definition of `uniqueBaseOn` / `uniqueBaseOn` 的定义

English:
definition uniqueBaseOn
  signature: (I E : Set α)
  body: freeOn I ↾ E

中文:
定义 uniqueBaseOn
  签名: (I E : Set α)
  定义体: freeOn I ↾ E

Depends on / 依赖: freeOn
-/
def uniqueBaseOn (I E : Set α) : Matroid α := freeOn I ↾ E

/--
theorem `uniqueBaseOn_ground` / 定理 `uniqueBaseOn_ground`

English:
theorem uniqueBaseOn_ground
  statement: (uniqueBaseOn I E).E = E
  proof: rfl

中文:
定理 uniqueBaseOn_ground
  结论: (uniqueBaseOn I E).E = E
  证明: rfl
-/
@[simp] theorem uniqueBaseOn_ground : (uniqueBaseOn I E).E = E :=
  rfl

/--
theorem `uniqueBaseOn_isBase_iff` / 定理 `uniqueBaseOn_isBase_iff`

English:
theorem uniqueBaseOn_isBase_iff
  given: (hIE : I subseteq E)
  statement: (uniqueBaseOn I E).IsBase B ↔ B = I
  proof: by
  rw [uniqueBaseOn]; rw [isBase_restrict_iff']; rw [freeOn_isBasis'_iff]; rw [inter_eq_self_of_subset_right hIE]

中文:
定理 uniqueBaseOn_isBase_iff
  条件: (hIE : I subseteq E)
  结论: (uniqueBaseOn I E).IsBase B ↔ B = I
  证明: by
  rw [uniqueBaseOn]; rw [isBase_restrict_iff']; rw [freeOn_isBasis'_iff]; rw [inter_eq_self_of_subset_right hIE]

Depends on / 依赖: _iff, freeOn_isBasis, inter_eq_self_of_subset_right, isBase_restrict_iff, uniqueBaseOn
-/
theorem uniqueBaseOn_isBase_iff (hIE : I subseteq E) : (uniqueBaseOn I E).IsBase B ↔ B = I := by
  rw [uniqueBaseOn]; rw [isBase_restrict_iff']; rw [freeOn_isBasis'_iff]; rw [inter_eq_self_of_subset_right hIE]

/--
theorem `uniqueBaseOn_inter_ground_eq` / 定理 `uniqueBaseOn_inter_ground_eq`

English:
theorem uniqueBaseOn_inter_ground_eq
  given: (I E : Set α)
  proof: by
  simp only [uniqueBaseOn, restrict_eq_restrict_iff, freeOn_indep_iff, subset_inter_iff]
  tauto

中文:
定理 uniqueBaseOn_inter_ground_eq
  条件: (I E : Set α)
  证明: by
  simp only [uniqueBaseOn, restrict_eq_restrict_iff, freeOn_indep_iff, subset_inter_iff]
  tauto

Depends on / 依赖: freeOn_indep_iff, restrict_eq_restrict_iff, subset_inter_iff, uniqueBaseOn
-/
theorem uniqueBaseOn_inter_ground_eq (I E : Set α) :
    uniqueBaseOn (I inter E) E = uniqueBaseOn I E := by
  simp only [uniqueBaseOn, restrict_eq_restrict_iff, freeOn_indep_iff, subset_inter_iff]
  tauto

/--
theorem `uniqueBaseOn_indep_iff'` / 定理 `uniqueBaseOn_indep_iff'`

English:
theorem uniqueBaseOn_indep_iff'
  statement: (uniqueBaseOn I E).Indep J ↔ J subseteq I inter E
  proof: by
  rw [uniqueBaseOn]; rw [restrict_indep_iff]; rw [freeOn_indep_iff]; rw [subset_inter_iff]

中文:
定理 uniqueBaseOn_indep_iff'
  结论: (uniqueBaseOn I E).Indep J ↔ J subseteq I inter E
  证明: by
  rw [uniqueBaseOn]; rw [restrict_indep_iff]; rw [freeOn_indep_iff]; rw [subset_inter_iff]
-/
@[simp] theorem uniqueBaseOn_indep_iff' : (uniqueBaseOn I E).Indep J ↔ J subseteq I inter E := by
  rw [uniqueBaseOn]; rw [restrict_indep_iff]; rw [freeOn_indep_iff]; rw [subset_inter_iff]

/--
theorem `uniqueBaseOn_indep_iff` / 定理 `uniqueBaseOn_indep_iff`

English:
theorem uniqueBaseOn_indep_iff
  given: (hIE : I subseteq E)
  statement: (uniqueBaseOn I E).Indep J ↔ J subseteq I
  proof: by
  rw [uniqueBaseOn]; rw [restrict_indep_iff]; rw [freeOn_indep_iff]; rw [and_iff_left_iff_imp]
  exact fun h => h.trans hIE

中文:
定理 uniqueBaseOn_indep_iff
  条件: (hIE : I subseteq E)
  结论: (uniqueBaseOn I E).Indep J ↔ J subseteq I
  证明: by
  rw [uniqueBaseOn]; rw [restrict_indep_iff]; rw [freeOn_indep_iff]; rw [and_iff_left_iff_imp]
  exact fun h => h.trans hIE

Depends on / 依赖: and_iff_left_iff_imp, freeOn_indep_iff, h.trans, restrict_indep_iff, uniqueBaseOn
-/
theorem uniqueBaseOn_indep_iff (hIE : I subseteq E) : (uniqueBaseOn I E).Indep J ↔ J subseteq I := by
  rw [uniqueBaseOn]; rw [restrict_indep_iff]; rw [freeOn_indep_iff]; rw [and_iff_left_iff_imp]
  exact fun h => h.trans hIE

/--
theorem `uniqueBaseOn_isBasis_iff` / 定理 `uniqueBaseOn_isBasis_iff`

English:
theorem uniqueBaseOn_isBasis_iff
  given: (hX : X subseteq E)
  statement: (uniqueBaseOn I E).IsBasis J X ↔ J = X inter I
  proof: by
  rw [isBasis_iff_maximal]
  exact maximal_iff_eq (by simp [inter_subset_left.trans hX])
    (by simp +contextual)

中文:
定理 uniqueBaseOn_isBasis_iff
  条件: (hX : X subseteq E)
  结论: (uniqueBaseOn I E).IsBasis J X ↔ J = X inter I
  证明: by
  rw [isBasis_iff_maximal]
  exact maximal_iff_eq (by simp [inter_subset_left.trans hX])
    (by simp +contextual)

Depends on / 依赖: contextual, inter_subset_left, inter_subset_left.trans, isBasis_iff_maximal, maximal_iff_eq
-/
theorem uniqueBaseOn_isBasis_iff (hX : X subseteq E) : (uniqueBaseOn I E).IsBasis J X ↔ J = X inter I := by
  rw [isBasis_iff_maximal]
  exact maximal_iff_eq (by simp [inter_subset_left.trans hX])
    (by simp +contextual)

/--
theorem `uniqueBaseOn_inter_isBasis` / 定理 `uniqueBaseOn_inter_isBasis`

English:
theorem uniqueBaseOn_inter_isBasis
  given: (hX : X subseteq E)
  statement: (uniqueBaseOn I E).IsBasis (X inter I) X
  proof: by
  rw [uniqueBaseOn_isBasis_iff hX]

中文:
定理 uniqueBaseOn_inter_isBasis
  条件: (hX : X subseteq E)
  结论: (uniqueBaseOn I E).IsBasis (X inter I) X
  证明: by
  rw [uniqueBaseOn_isBasis_iff hX]

Depends on / 依赖: uniqueBaseOn_isBasis_iff
-/
theorem uniqueBaseOn_inter_isBasis (hX : X subseteq E) : (uniqueBaseOn I E).IsBasis (X inter I) X := by
  rw [uniqueBaseOn_isBasis_iff hX]

/--
theorem `uniqueBaseOn_dual_eq` / 定理 `uniqueBaseOn_dual_eq`

English:
theorem uniqueBaseOn_dual_eq
  given: (I E : Set α)
  proof: by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine ext_isBase rfl (fun B (hB : B subseteq E) => ?_)
  rw [dual_isBase_iff]; rw [uniqueBaseOn_isBase_iff inter_subset_right]; rw [uniqueBaseOn_isBase_iff sdiff_subset]; rw [uniqueBaseOn_ground]
  exact ⟨fun h => by rw [← sdiff_sdiff_cancel_left hB, h, sd

中文:
定理 uniqueBaseOn_dual_eq
  条件: (I E : Set α)
  证明: by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine ext_isBase rfl (fun B (hB : B subseteq E) => ?_)
  rw [dual_isBase_iff]; rw [uniqueBaseOn_isBase_iff inter_subset_right]; rw [uniqueBaseOn_isBase_iff sdiff_subset]; rw [uniqueBaseOn_ground]
  exact ⟨fun h => by rw [← sdiff_sdiff_cancel_left hB, h, sd
-/
@[simp] theorem uniqueBaseOn_dual_eq (I E : Set α) :
    (uniqueBaseOn I E)✶ = uniqueBaseOn (E \ I) E := by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine ext_isBase rfl (fun B (hB : B subseteq E) => ?_)
  rw [dual_isBase_iff]; rw [uniqueBaseOn_isBase_iff inter_subset_right]; rw [uniqueBaseOn_isBase_iff sdiff_subset]; rw [uniqueBaseOn_ground]
  exact ⟨fun h => by rw [← sdiff_sdiff_cancel_left hB, h, sdiff_inter_self_eq_sdiff],
    fun h => by rw [h, inter_comm I]; simp⟩

/--
theorem `uniqueBaseOn_self` / 定理 `uniqueBaseOn_self`

English:
theorem uniqueBaseOn_self
  given: (I : Set α)
  statement: uniqueBaseOn I I = freeOn I
  proof: by
  rw [uniqueBaseOn]; rw [freeOn_restrict rfl.subset]

中文:
定理 uniqueBaseOn_self
  条件: (I : Set α)
  结论: uniqueBaseOn I I = freeOn I
  证明: by
  rw [uniqueBaseOn]; rw [freeOn_restrict rfl.subset]
-/
@[simp] theorem uniqueBaseOn_self (I : Set α) : uniqueBaseOn I I = freeOn I := by
  rw [uniqueBaseOn]; rw [freeOn_restrict rfl.subset]

/--
theorem `uniqueBaseOn_empty` / 定理 `uniqueBaseOn_empty`

English:
theorem uniqueBaseOn_empty
  given: (I : Set α)
  statement: uniqueBaseOn ∅ I = loopyOn I
  proof: by
  rw [← dual_inj]; rw [uniqueBaseOn_dual_eq]; rw [sdiff_empty]; rw [uniqueBaseOn_self]; rw [loopyOn_dual_eq]

中文:
定理 uniqueBaseOn_empty
  条件: (I : Set α)
  结论: uniqueBaseOn ∅ I = loopyOn I
  证明: by
  rw [← dual_inj]; rw [uniqueBaseOn_dual_eq]; rw [sdiff_empty]; rw [uniqueBaseOn_self]; rw [loopyOn_dual_eq]
-/
@[simp] theorem uniqueBaseOn_empty (I : Set α) : uniqueBaseOn ∅ I = loopyOn I := by
  rw [← dual_inj]; rw [uniqueBaseOn_dual_eq]; rw [sdiff_empty]; rw [uniqueBaseOn_self]; rw [loopyOn_dual_eq]

/--
theorem `uniqueBaseOn_restrict'` / 定理 `uniqueBaseOn_restrict'`

English:
theorem uniqueBaseOn_restrict'
  given: (I E R : Set α)
  proof: by
  simp_rw [ext_iff_indep, restrict_ground_eq, uniqueBaseOn_ground, true_and,
    restrict_indep_iff, uniqueBaseOn_indep_iff', subset_inter_iff]
  tauto

中文:
定理 uniqueBaseOn_restrict'
  条件: (I E R : Set α)
  证明: by
  simp_rw [ext_iff_indep, restrict_ground_eq, uniqueBaseOn_ground, true_and,
    restrict_indep_iff, uniqueBaseOn_indep_iff', subset_inter_iff]
  tauto

Depends on / 依赖: ext_iff_indep, restrict_ground_eq, restrict_indep_iff, simp_rw, subset_inter_iff, true_and, uniqueBaseOn_ground, uniqueBaseOn_indep_iff
-/
theorem uniqueBaseOn_restrict' (I E R : Set α) :
    (uniqueBaseOn I E) ↾ R = uniqueBaseOn (I inter R inter E) R := by
  simp_rw [ext_iff_indep, restrict_ground_eq, uniqueBaseOn_ground, true_and,
    restrict_indep_iff, uniqueBaseOn_indep_iff', subset_inter_iff]
  tauto

/--
theorem `uniqueBaseOn_restrict` / 定理 `uniqueBaseOn_restrict`

English:
theorem uniqueBaseOn_restrict
  given: (h : I subseteq E) (R : Set α)
  proof: by
  rw [uniqueBaseOn_restrict']; rw [inter_right_comm]; rw [inter_eq_self_of_subset_left h]

中文:
定理 uniqueBaseOn_restrict
  条件: (h : I subseteq E) (R : Set α)
  证明: by
  rw [uniqueBaseOn_restrict']; rw [inter_right_comm]; rw [inter_eq_self_of_subset_left h]

Depends on / 依赖: inter_eq_self_of_subset_left, inter_right_comm, uniqueBaseOn_restrict
-/
theorem uniqueBaseOn_restrict (h : I subseteq E) (R : Set α) :
    (uniqueBaseOn I E) ↾ R = uniqueBaseOn (I inter R) R := by
  rw [uniqueBaseOn_restrict']; rw [inter_right_comm]; rw [inter_eq_self_of_subset_left h]

/--
lemma `uniqueBaseOn_rankFinite` / 引理 `uniqueBaseOn_rankFinite`

English:
lemma uniqueBaseOn_rankFinite
  given: (hI : I.Finite)
  statement: RankFinite (uniqueBaseOn I E)
  proof: by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine ⟨I inter E, ?_⟩
  rw [uniqueBaseOn_isBase_iff inter_subset_right]; rw [and_iff_right rfl]
  exact hI.subset inter_subset_left

中文:
引理 uniqueBaseOn_rankFinite
  条件: (hI : I.Finite)
  结论: RankFinite (uniqueBaseOn I E)
  证明: by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine ⟨I inter E, ?_⟩
  rw [uniqueBaseOn_isBase_iff inter_subset_right]; rw [and_iff_right rfl]
  exact hI.subset inter_subset_left

Depends on / 依赖: and_iff_right, hI.subset, inter_subset_left, inter_subset_right, subset, uniqueBaseOn_inter_ground_eq, uniqueBaseOn_isBase_iff
-/
lemma uniqueBaseOn_rankFinite (hI : I.Finite) : RankFinite (uniqueBaseOn I E) := by
  rw [← uniqueBaseOn_inter_ground_eq]
  refine ⟨I inter E, ?_⟩
  rw [uniqueBaseOn_isBase_iff inter_subset_right]; rw [and_iff_right rfl]
  exact hI.subset inter_subset_left

/--
Instance `uniqueBaseOn_finitary` / 实例 `uniqueBaseOn_finitary`

English:
instance uniqueBaseOn_finitary
  signature: : Finitary (uniqueBaseOn I E)
  body: by
  refine ⟨fun K hK => ?_⟩
  simp only [uniqueBaseOn_indep_iff'] at hK ⊢
exact fun e heK => singleton_subset_iff.1 hK _ (by simpa) (by simp)

中文:
实例 uniqueBaseOn_finitary
  签名: : Finitary (uniqueBaseOn I E)
  定义体: by
  refine ⟨fun K hK => ?_⟩
  simp only [uniqueBaseOn_indep_iff'] at hK ⊢
exact fun e heK => singleton_subset_iff.1 hK _ (by simpa) (by simp)

Depends on / 依赖: singleton_subset_iff, uniqueBaseOn_indep_iff
-/
instance uniqueBaseOn_finitary : Finitary (uniqueBaseOn I E) := by
  refine ⟨fun K hK => ?_⟩
  simp only [uniqueBaseOn_indep_iff'] at hK ⊢
exact fun e heK => singleton_subset_iff.1 hK _ (by simpa) (by simp)

/--
lemma `uniqueBaseOn_rankPos` / 引理 `uniqueBaseOn_rankPos`

English:
lemma uniqueBaseOn_rankPos
  given: (hIE : I subseteq E) (hI : I.Nonempty)
  statement: RankPos (uniqueBaseOn I E) where
  proof: by simpa [uniqueBaseOn_isBase_iff hIE] using Ne.symm hI.ne_empty

中文:
引理 uniqueBaseOn_rankPos
  条件: (hIE : I subseteq E) (hI : I.Nonempty)
  结论: RankPos (uniqueBaseOn I E) where
  证明: by simpa [uniqueBaseOn_isBase_iff hIE] using Ne.symm hI.ne_empty

Depends on / 依赖: Ne.symm, hI.ne_empty, ne_empty, uniqueBaseOn_isBase_iff
-/
lemma uniqueBaseOn_rankPos (hIE : I subseteq E) (hI : I.Nonempty) : RankPos (uniqueBaseOn I E) where
empty_not_isBase := by simpa [uniqueBaseOn_isBase_iff hIE] using Ne.symm hI.ne_empty

end uniqueBaseOn

end Matroid
