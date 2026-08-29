/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama

/-!
## Lemmas on idempotent finitely generated ideals
-/

public section


namespace Ideal

/--
theorem `isIdempotentElem_iff_of_fg` / 定理 `isIdempotentElem_iff_of_fg`

English:
theorem isIdempotentElem_iff_of_fg
  given: {R : Type*} [CommRing R] (I : Ideal R) (h : I.FG)
  proof: by
  constructor
  · intro e
    obtain ⟨r, hr, hr'⟩ :=
      Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I I h
        (by
          rw [smul_eq_mul]
          exact e.ge)
    simp_rw [smul_eq_mul] at hr'
    refine ⟨r, hr' r hr, antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr

中文:
定理 isIdempotentElem_iff_of_fg
  条件: {R : 类型} [交换环 R] (I : 理想 R) (h : I.FG)
  证明: by
  constructor
  · intro e
    obtain ⟨r, hr, hr'⟩ :=
      Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I I h
        (by
          rw [smul_eq_mul]
          exact e.ge)
    simp_rw [smul_eq_mul] at hr'
    refine ⟨r, hr' r hr, antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr

Depends on / 依赖: Ideal.mem_span_singleton, Ideal.span_singleton_mul_span_singleton, IsIdempotentElem, Submodule, Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul, Submodule.span_singleton_le_iff_mem, antisymm, e.ge, exists_mem_and_smul_eq_self_of_fg_of_le_smul, he.eq, mem_span_singleton, mul_comm, simp_rw, smul_eq_mul, span_singleton_le_iff_mem, span_singleton_mul_span_singleton
-/
theorem isIdempotentElem_iff_of_fg {R : Type*} [CommRing R] (I : Ideal R) (h : I.FG) :
    IsIdempotentElem I ↔ exists e : R, IsIdempotentElem e ∧ I = R ∙ e := by
  constructor
  · intro e
    obtain ⟨r, hr, hr'⟩ :=
      Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I I h
        (by
          rw [smul_eq_mul]
          exact e.ge)
    simp_rw [smul_eq_mul] at hr'
    refine ⟨r, hr' r hr, antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr hr)⟩
    intro x hx
    rw [← hr' x hx]
    exact Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩
  · rintro ⟨e, he, rfl⟩
    simp [IsIdempotentElem, Ideal.span_singleton_mul_span_singleton, he.eq]

/--
theorem `isIdempotentElem_iff_eq_bot_or_top` / 定理 `isIdempotentElem_iff_eq_bot_or_top`

English:
theorem isIdempotentElem_iff_eq_bot_or_top
  statement: {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R)
  proof: by
  constructor
  · intro H
    obtain ⟨e, he, rfl⟩ := (I.isIdempotentElem_iff_of_fg h).mp H
    simp only [Ideal.submodule_span_eq, Ideal.span_singleton_eq_bot]
    apply Or.imp id _ (IsIdempotentElem.iff_eq_zero_or_one.mp he)
    rintro rfl
    simp
  · rintro (rfl | rfl) <;> simp [IsIdempotentEl

中文:
定理 isIdempotentElem_iff_eq_bot_or_top
  结论: {R : 类型} [交换环 R] [是整环 R] (I : 理想 R)
  证明: by
  constructor
  · intro H
    obtain ⟨e, he, rfl⟩ := (I.isIdempotentElem_iff_of_fg h).mp H
    simp only [Ideal.submodule_span_eq, Ideal.span_singleton_eq_bot]
    apply Or.imp id _ (IsIdempotentElem.iff_eq_zero_or_one.mp he)
    rintro rfl
    simp
  · rintro (rfl | rfl) <;> simp [IsIdempotentEl

Depends on / 依赖: I.isIdempotentElem_iff_of_fg, Ideal.span_singleton_eq_bot, Ideal.submodule_span_eq, IsIdempotentElem, IsIdempotentElem.iff_eq_zero_or_one.mp, Or.imp, iff_eq_zero_or_one, isIdempotentElem_iff_of_fg, span_singleton_eq_bot, submodule_span_eq
-/
theorem isIdempotentElem_iff_eq_bot_or_top {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R)
    (h : I.FG) : IsIdempotentElem I ↔ I = ⊥ ∨ I = ⊤ := by
  constructor
  · intro H
    obtain ⟨e, he, rfl⟩ := (I.isIdempotentElem_iff_of_fg h).mp H
    simp only [Ideal.submodule_span_eq, Ideal.span_singleton_eq_bot]
    apply Or.imp id _ (IsIdempotentElem.iff_eq_zero_or_one.mp he)
    rintro rfl
    simp
  · rintro (rfl | rfl) <;> simp [IsIdempotentElem]

end Ideal
