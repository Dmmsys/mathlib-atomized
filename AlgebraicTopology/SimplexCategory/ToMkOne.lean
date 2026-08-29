/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Morphisms to `⦋1⦌`

We define a bijective map `SimplexCategory.toMk₁ : Fin (n + 2) → `⦋n⦌ ⟶ ⦋1⦌`.
This is used in the file `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne`
in the study of simplices in the simplicial set `Δ[1]`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SimplexCategory


/--
lemma `toMk₁_apply_eq_zero_iff` / 引理 `toMk₁_apply_eq_zero_iff`

English:
lemma toMk₁_apply_eq_zero_iff
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1))
  proof: by
  simp [toMk₁_apply]

中文:
引理 toMk₁_apply_eq_zero_iff
  条件: {n : 自然数} (i : Fin (n + 2)) (j : Fin (n + 1))
  证明: by
  simp [toMk₁_apply]
-/
lemma toMk₁_apply_eq_zero_iff {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    dsimp% toMk₁ i j = 0 ↔ j.castSucc < i := by
  simp [toMk₁_apply]

/--
lemma `toMk₁_of_castSucc_lt` / 引理 `toMk₁_of_castSucc_lt`

English:
lemma toMk₁_of_castSucc_lt
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i)
  proof: by
  simpa [toMk₁_apply]

中文:
引理 toMk₁_of_castSucc_lt
  条件: {n : 自然数} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i)
  证明: by
  simpa [toMk₁_apply]
-/
lemma toMk₁_of_castSucc_lt {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    dsimp% toMk₁ i j = 0 := by
  simpa [toMk₁_apply]

/--
lemma `toMk₁_apply_eq_one_iff` / 引理 `toMk₁_apply_eq_one_iff`

English:
lemma toMk₁_apply_eq_one_iff
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1))
  proof: by
  simp [toMk₁_apply]

中文:
引理 toMk₁_apply_eq_one_iff
  条件: {n : 自然数} (i : Fin (n + 2)) (j : Fin (n + 1))
  证明: by
  simp [toMk₁_apply]
-/
lemma toMk₁_apply_eq_one_iff {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    dsimp% toMk₁ i j = 1 ↔ i <= j.castSucc := by
  simp [toMk₁_apply]

/--
lemma `toMk₁_of_le_castSucc` / 引理 `toMk₁_of_le_castSucc`

English:
lemma toMk₁_of_le_castSucc
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i <= j.castSucc)
  proof: by
  simpa [toMk₁_apply]

中文:
引理 toMk₁_of_le_castSucc
  条件: {n : 自然数} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i <= j.castSucc)
  证明: by
  simpa [toMk₁_apply]
-/
lemma toMk₁_of_le_castSucc {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i <= j.castSucc) :
    dsimp% toMk₁ i j = 1 := by
  simpa [toMk₁_apply]

/--
lemma `δ_comp_toMk₁_of_le` / 引理 `δ_comp_toMk₁_of_le`

English:
lemma δ_comp_toMk₁_of_le
  given: {n : Nat} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i <= j.castSucc)
  proof: by
  obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last
    (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))
  simp only [Fin.castSucc_le_castSucc_iff] at h
  rw [Fin.castPred_castSucc]
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i.castSucc (j.succAbove k) = _
  dsimp
  rw

中文:
引理 δ_comp_toMk₁_of_le
  条件: {n : 自然数} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i <= j.castSucc)
  证明: by
  obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last
    (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))
  simp only [Fin.castSucc_le_castSucc_iff] at h
  rw [Fin.castPred_castSucc]
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i.castSucc (j.succAbove k) = _
  dsimp
  rw

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, Fin.castPred_castSucc, Fin.castSucc_le_castSucc_iff, Fin.eq_castSucc_of_ne_last, Fin.eq_iff_eq_zero_iff, Fin.ne_last_of_lt, Fin.succAbove, castPred_castSucc, castSucc, castSucc_le_castSucc_iff, castSucc_lt_succ, eq_castSucc_of_ne_last, eq_iff_eq_zero_iff, hom_ext, i.castSucc, j.castSucc_lt_succ, j.succAbove, lt_of_le_of_lt, ne_last_of_lt
-/
lemma δ_comp_toMk₁_of_le {n : Nat} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i <= j.castSucc) :
    δ j ≫ toMk₁ i =
      toMk₁ (i.castPred (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))) := by
  obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last
    (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))
  simp only [Fin.castSucc_le_castSucc_iff] at h
  rw [Fin.castPred_castSucc]
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i.castSucc (j.succAbove k) = _
  dsimp
  rw [Fin.eq_iff_eq_zero_iff]; rw [toMk₁_apply_eq_zero_iff]; rw [toMk₁_apply_eq_zero_iff]
  grind [Fin.succAbove]

/--
lemma `δ_comp_toMk₁_of_lt` / 引理 `δ_comp_toMk₁_of_lt`

English:
lemma δ_comp_toMk₁_of_lt
  given: {n : Nat} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : j.castSucc < i)
  proof: by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  rw [Fin.pred_succ]
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i.succ (j.succAbove k) = _
  dsimp
  rw [Fin.eq_iff_eq_zero_iff]; rw [toMk₁_apply_eq_zero_iff]; rw [toMk₁_apply_eq_zero_iff]
  grind [Fin.succA

中文:
引理 δ_comp_toMk₁_of_lt
  条件: {n : 自然数} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : j.castSucc < i)
  证明: by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  rw [Fin.pred_succ]
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i.succ (j.succAbove k) = _
  dsimp
  rw [Fin.eq_iff_eq_zero_iff]; rw [toMk₁_apply_eq_zero_iff]; rw [toMk₁_apply_eq_zero_iff]
  grind [Fin.succA

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, Fin.eq_iff_eq_zero_iff, Fin.eq_succ_of_ne_zero, Fin.ne_zero_of_lt, Fin.pred_succ, Fin.succAbove, eq_iff_eq_zero_iff, eq_succ_of_ne_zero, hom_ext, i.succ, j.succAbove, ne_zero_of_lt, pred_succ, succAbove
-/
lemma δ_comp_toMk₁_of_lt {n : Nat} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : j.castSucc < i) :
    δ j ≫ toMk₁ i = toMk₁ (i.pred (Fin.ne_zero_of_lt h)) := by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  rw [Fin.pred_succ]
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i.succ (j.succAbove k) = _
  dsimp
  rw [Fin.eq_iff_eq_zero_iff]; rw [toMk₁_apply_eq_zero_iff]; rw [toMk₁_apply_eq_zero_iff]
  grind [Fin.succAbove]

/--
lemma `σ_comp_toMk₁_of_le` / 引理 `σ_comp_toMk₁_of_le`

English:
lemma σ_comp_toMk₁_of_le
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i <= j.castSucc)
  proof: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i (j.predAbove k) = _
  by_cases! hk : k < i
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is

中文:
引理 σ_comp_toMk₁_of_le
  条件: {n : 自然数} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i <= j.castSucc)
  证明: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i (j.predAbove k) = _
  by_cases! hk : k < i
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is

Depends on / 依赖: Before, ConcreteCategory, ConcreteCategory.hom_ext, Fin.castPred, Fin.predAbove_of_le_castSucc, Mathlib, adaptation_note, canonicalizer, castPred, closed, directed, github, github.com, hom_ext, j.predAbove, leanprover, minimization, normalizer, original, predAbove
-/
lemma σ_comp_toMk₁_of_le {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i <= j.castSucc) :
    σ j ≫ toMk₁ i = toMk₁ i.castSucc := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i (j.predAbove k) = _
  by_cases! hk : k < i
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was:
    `grind [Fin.castPred, Fin.predAbove_of_le_castSucc, toMk₁_of_castSucc_lt]` -/
    simp; grind [Fin.castPred, Fin.predAbove_of_le_castSucc, toMk₁_of_castSucc_lt]
  · dsimp
    rw [toMk₁_of_le_castSucc]; rw [toMk₁_of_le_castSucc _ _ (by simpa)]
    by_cases hk' : k <= j.castSucc
    · rwa [Fin.predAbove_of_le_castSucc _ _ hk', Fin.castSucc_castPred]
    · grind [Fin.predAbove]

/--
lemma `σ_comp_toMk₁_of_lt` / 引理 `σ_comp_toMk₁_of_lt`

English:
lemma σ_comp_toMk₁_of_lt
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i)
  proof: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i (j.predAbove k) = _
  by_cases! hk : i < k
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is

中文:
引理 σ_comp_toMk₁_of_lt
  条件: {n : 自然数} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i)
  证明: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i (j.predAbove k) = _
  by_cases! hk : i < k
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is

Depends on / 依赖: Before, ConcreteCategory, ConcreteCategory.hom_ext, Fin.predAbove_of_castSucc_lt, Mathlib, adaptation_note, canonicalizer, closed, directed, github, github.com, hom_ext, j.predAbove, leanprover, minimization, normalizer, original, predAbove, predAbove_of_castSucc_lt, problem
-/
lemma σ_comp_toMk₁_of_lt {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    σ j ≫ toMk₁ i = toMk₁ i.succ := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  change toMk₁ i (j.predAbove k) = _
  by_cases! hk : i < k
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was:
    `grind [Fin.predAbove_of_castSucc_lt, toMk₁_of_le_castSucc]` -/
    simp; grind [Fin.predAbove_of_castSucc_lt, toMk₁_of_le_castSucc]
  · dsimp
    rw [toMk₁_of_castSucc_lt i.succ k (by simpa)]; rw [toMk₁_of_castSucc_lt]
    by_cases hk' : j.castSucc < k
    · rwa [Fin.predAbove_of_castSucc_lt _ _ hk', Fin.castSucc_pred_lt_iff]
    · simp only [not_lt] at hk'
      rw [Fin.predAbove_of_le_castSucc _ _ hk']
      exact lt_of_le_of_lt (by simpa) h

/--
lemma `toMk₁_injective` / 引理 `toMk₁_injective`

English:
lemma toMk₁_injective
  given: {n : Nat}
  statement: Function.Injective (toMk₁ (n := n))
  proof: by
  intro i j h
  wlog hij : i < j generalizing i j
  · grind
  have := ConcreteCategory.congr_hom h ⟨i.1, lt_of_lt_of_le hij (by dsimp; lia)⟩
  simp [toMk₁_apply, if_pos hij] at this

中文:
引理 toMk₁_injective
  条件: {n : 自然数}
  结论: Function.Injective (toMk₁ (n := n))
  证明: by
  intro i j h
  wlog hij : i < j generalizing i j
  · grind
  have := ConcreteCategory.congr_hom h ⟨i.1, lt_of_lt_of_le hij (by dsimp; lia)⟩
  simp [toMk₁_apply, if_pos hij] at this

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, generalizing, if_pos, lt_of_lt_of_le
-/
lemma toMk₁_injective {n : Nat} : Function.Injective (toMk₁ (n := n)) := by
  intro i j h
  wlog hij : i < j generalizing i j
  · grind
  have := ConcreteCategory.congr_hom h ⟨i.1, lt_of_lt_of_le hij (by dsimp; lia)⟩
  simp [toMk₁_apply, if_pos hij] at this

/--
lemma `toMk₁_surjective` / 引理 `toMk₁_surjective`

English:
lemma toMk₁_surjective
  given: {n : Nat}
  statement: Function.Surjective (toMk₁ (n := n))
  proof: by
  intro f
  let S : Finset (Fin (n + 1)) := { i | f i = 1}
  by_cases hS : S.Nonempty
  · refine ⟨(S.min' hS).castSucc, ConcreteCategory.hom_ext _ _ (fun i => ?_)⟩
    dsimp [toMk₁_apply]
    split_ifs with h
    · have hi : i ∉ S := fun hi => by have := S.min'_le _ hi; grind
      #adaptation_no

中文:
引理 toMk₁_surjective
  条件: {n : 自然数}
  结论: Function.Surjective (toMk₁ (n := n))
  证明: by
  intro f
  let S : Finset (Fin (n + 1)) := { i | f i = 1}
  by_cases hS : S.Nonempty
  · refine ⟨(S.min' hS).castSucc, ConcreteCategory.hom_ext _ _ (fun i => ?_)⟩
    dsimp [toMk₁_apply]
    split_ifs with h
    · have hi : i ∉ S := fun hi => by have := S.min'_le _ hi; grind
      #adaptation_no

Depends on / 依赖: Before, ConcreteCategory, ConcreteCategory.hom_ext, Finset, Mathlib, Nonempty, S.Nonempty, S.min, adaptation_note, canonicalizer, castSucc, closed, directed, github, github.com, hom_ext, leanprover, normalizer, replacing, split_ifs
-/
lemma toMk₁_surjective {n : Nat} : Function.Surjective (toMk₁ (n := n)) := by
  intro f
  let S : Finset (Fin (n + 1)) := { i | f i = 1}
  by_cases hS : S.Nonempty
  · refine ⟨(S.min' hS).castSucc, ConcreteCategory.hom_ext _ _ (fun i => ?_)⟩
    dsimp [toMk₁_apply]
    split_ifs with h
    · have hi : i ∉ S := fun hi => by have := S.min'_le _ hi; grind
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
      the new canonicalizer; a minimization would help. The original proof was: `grind` -/
      simp [S] at hi; grind
    · simp only [Fin.castSucc_lt_castSucc_iff, Finset.lt_min'_iff, not_forall,
        not_lt] at h
      obtain ⟨j, hj, hij⟩ := h
      have := f.toOrderHom.monotone hij
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
      the new canonicalizer; a minimization would help. The original proof was:
      `grind [show f j ≤ f i from f.toOrderHom.monotone hij]` -/
      simp_all [ConcreteCategory.hom, S]
      grind
  · refine ⟨Fin.last _, ConcreteCategory.hom_ext _ _ (fun i => ?_)⟩
    dsimp [toMk₁_apply]
    rw [if_pos (by simp)]
    obtain ⟨j, hj⟩ : exists (j : Fin 2), f i = j := ⟨_, rfl⟩
    fin_cases j
    · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
      the new canonicalizer; a minimization would help. The original proof was: `grind` -/
      simp_all
    · exact (hS ⟨i, by simpa [S]⟩).elim

/--
lemma `toMk₁_bijective` / 引理 `toMk₁_bijective`

English:
lemma toMk₁_bijective
  given: {n : Nat}
  statement: Function.Bijective (toMk₁ (n := n))
  proof: ⟨toMk₁_injective, toMk₁_surjective⟩

中文:
引理 toMk₁_bijective
  条件: {n : 自然数}
  结论: Function.Bijective (toMk₁ (n := n))
  证明: ⟨toMk₁_injective, toMk₁_surjective⟩
-/
lemma toMk₁_bijective {n : Nat} : Function.Bijective (toMk₁ (n := n)) :=
  ⟨toMk₁_injective, toMk₁_surjective⟩

/-- The bijection `Fin (n + 2) ≃ (⦋n⦌ ⟶ ⦋1⦌)` which sends `i : Fin (n + 2)` to the
morphism `⦋n⦌ ⟶ ⦋1⦌` in the simplex category which corresponds to the monotone map
`Fin (n + 1) → Fin 2` which takes `i` times the value `0`. -/
@[simps! apply]
/--
Definition of `toMk₁Equiv` / `toMk₁Equiv` 的定义

English:
definition toMk₁Equiv
  signature: {n : Nat}
  body: Equiv.ofBijective _ toMk₁_bijective

中文:
定义 toMk₁Equiv
  签名: {n : 自然数}
  定义体: Equiv.ofBijective _ toMk₁_bijective

Depends on / 依赖: Equiv.ofBijective, ofBijective
-/
noncomputable def toMk₁Equiv {n : Nat} : Fin (n + 2) ≃ (⦋n⦌ ⟶ ⦋1⦌) :=
  Equiv.ofBijective _ toMk₁_bijective

end SimplexCategory
