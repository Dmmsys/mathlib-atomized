/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.MvRatFunc.Rank
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Cardinality of a transcendence basis

This file concerns the cardinality of a transcendence basis.

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## Tags
transcendence basis, transcendence degree, transcendence

-/

public section

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u v w

open AlgebraicIndependent

open Cardinal

/--
theorem `IsTranscendenceBasis.lift_cardinalMk_eq_max_lift` / 定理 `IsTranscendenceBasis.lift_cardinalMk_eq_max_lift`

English:
theorem IsTranscendenceBasis.lift_cardinalMk_eq_max_lift
  proof: by
  let K := Algebra.adjoin F (Set.range x)
  suffices #E = #K by simp [K, this, ← lift_mk_eq'.2 ⟨hx.1.aevalEquiv.toEquiv⟩]
  have : Algebra.IsAlgebraic K E := hx.isAlgebraic
  refine le_antisymm ?_ (mk_le_of_injective Subtype.val_injective)
  have : Infinite K := hx.1.aevalEquiv.infinite_iff.1 inf

中文:
定理 IsTranscendenceBasis.lift_cardinalMk_eq_max_lift
  证明: by
  let K := Algebra.adjoin F (Set.range x)
  suffices #E = #K by simp [K, this, ← lift_mk_eq'.2 ⟨hx.1.aevalEquiv.toEquiv⟩]
  have : Algebra.IsAlgebraic K E := hx.isAlgebraic
  refine le_antisymm ?_ (mk_le_of_injective Subtype.val_injective)
  have : Infinite K := hx.1.aevalEquiv.infinite_iff.1 inf

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.IsAlgebraic.cardinalMk_le_max, Algebra.adjoin, Infinite, IsAlgebraic, Set.range, Subtype, Subtype.val_injective, adjoin, aevalEquiv, aevalEquiv.infinite_iff, aevalEquiv.toEquiv, aleph0_le_mk, cardinalMk_le_max, hx.isAlgebraic, infinite_iff, isAlgebraic, le_antisymm, lift_mk_eq
-/
theorem IsTranscendenceBasis.lift_cardinalMk_eq_max_lift
    {F : Type u} {E : Type v} [CommRing F] [Nontrivial F] [CommRing E] [IsDomain E] [Algebra F E]
    {ι : Type w} {x : ι -> E} [Nonempty ι] (hx : IsTranscendenceBasis F x) :
    lift.{max u w} #E = lift.{max v w} #F ⊔ lift.{max u v} #ι ⊔ ℵ₀ := by
  let K := Algebra.adjoin F (Set.range x)
  suffices #E = #K by simp [K, this, ← lift_mk_eq'.2 ⟨hx.1.aevalEquiv.toEquiv⟩]
  have : Algebra.IsAlgebraic K E := hx.isAlgebraic
  refine le_antisymm ?_ (mk_le_of_injective Subtype.val_injective)
  have : Infinite K := hx.1.aevalEquiv.infinite_iff.1 inferInstance
  simpa only [sup_eq_left.2 (aleph0_le_mk K)] using Algebra.IsAlgebraic.cardinalMk_le_max K E

/--
theorem `IsTranscendenceBasis.lift_rank_eq_max_lift` / 定理 `IsTranscendenceBasis.lift_rank_eq_max_lift`

English:
theorem IsTranscendenceBasis.lift_rank_eq_max_lift
  proof: by
  let K := IntermediateField.adjoin F (Set.range x)
  have : Algebra.IsAlgebraic K E := hx.isAlgebraic_field
  rw [← rank_mul_rank F K E]; rw [lift_mul]; rw [← hx.1.aevalEquivField.toLinearEquiv.lift_rank_eq]; rw [MvRatFunc.rank_eq_max_lift]; rw [lift_max]; rw [lift_max]; rw [lift_lift]; rw [lift

中文:
定理 IsTranscendenceBasis.lift_rank_eq_max_lift
  证明: by
  let K := IntermediateField.adjoin F (Set.range x)
  have : Algebra.IsAlgebraic K E := hx.isAlgebraic_field
  rw [← rank_mul_rank F K E]; rw [lift_mul]; rw [← hx.1.aevalEquivField.toLinearEquiv.lift_rank_eq]; rw [MvRatFunc.rank_eq_max_lift]; rw [lift_max]; rw [lift_max]; rw [lift_lift]; rw [lift

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.IsAlgebraic.cardinalMk_le_max, IntermediateField, IntermediateField.adjoin, IsAlgebraic, MvRatFunc, MvRatFunc.rank_eq_max_lift, Set.range, adjoin, aevalEquivField, aevalEquivField.toLinearEquiv.lift_rank_eq, cardinalMk_le_max, hx.isAlgebraic_field, isAlgebraic_field, le_sup_right, lift_aleph0, lift_le, lift_lift, lift_max
-/
theorem IsTranscendenceBasis.lift_rank_eq_max_lift
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {ι : Type w} {x : ι -> E} [Nonempty ι] (hx : IsTranscendenceBasis F x) :
    lift.{max u w} (Module.rank F E) = lift.{max v w} #F ⊔ lift.{max u v} #ι ⊔ ℵ₀ := by
  let K := IntermediateField.adjoin F (Set.range x)
  have : Algebra.IsAlgebraic K E := hx.isAlgebraic_field
  rw [← rank_mul_rank F K E]; rw [lift_mul]; rw [← hx.1.aevalEquivField.toLinearEquiv.lift_rank_eq]; rw [MvRatFunc.rank_eq_max_lift]; rw [lift_max]; rw [lift_max]; rw [lift_lift]; rw [lift_lift]; rw [lift_aleph0]
  refine mul_eq_left le_sup_right ((lift_le.2 ((rank_le_card K E).trans
    (Algebra.IsAlgebraic.cardinalMk_le_max K E))).trans_eq ?_) (by simp [rank_pos.ne'])
  simp [K, ← lift_mk_eq'.2 ⟨hx.1.aevalEquivField.toEquiv⟩]

/--
theorem `Algebra.Transcendental.rank_eq_cardinalMk` / 定理 `Algebra.Transcendental.rank_eq_cardinalMk`

English:
theorem Algebra.Transcendental.rank_eq_cardinalMk
  proof: by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' F E
  have := hx.nonempty_iff_transcendental.2 ‹_›
  simpa [← hx.lift_cardinalMk_eq_max_lift] using hx.lift_rank_eq_max_lift

中文:
定理 代数.超越.rank_eq_cardinalMk
  证明: by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' F E
  have := hx.nonempty_iff_transcendental.2 ‹_›
  simpa [← hx.lift_cardinalMk_eq_max_lift] using hx.lift_rank_eq_max_lift

Depends on / 依赖: exists_isTranscendenceBasis, hx.lift_cardinalMk_eq_max_lift, hx.lift_rank_eq_max_lift, hx.nonempty_iff_transcendental, lift_cardinalMk_eq_max_lift, lift_rank_eq_max_lift, nonempty_iff_transcendental
-/
theorem Algebra.Transcendental.rank_eq_cardinalMk
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [Algebra.Transcendental F E] :
    Module.rank F E = #E := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' F E
  have := hx.nonempty_iff_transcendental.2 ‹_›
  simpa [← hx.lift_cardinalMk_eq_max_lift] using hx.lift_rank_eq_max_lift

/--
theorem `IntermediateField.rank_sup_le` / 定理 `IntermediateField.rank_sup_le`

English:
theorem IntermediateField.rank_sup_le
  proof: by
  by_cases hA : Algebra.IsAlgebraic F A
  · exact rank_sup_le_of_isAlgebraic A B (Or.inl hA)
  by_cases hB : Algebra.IsAlgebraic F B
  · exact rank_sup_le_of_isAlgebraic A B (Or.inr hB)
  rw [← Algebra.transcendental_iff_not_isAlgebraic] at hA hB
  have : Algebra.Transcendental F ↥(A ⊔ B) := .rin

中文:
定理 中间域.rank_sup_le
  证明: by
  by_cases hA : Algebra.IsAlgebraic F A
  · exact rank_sup_le_of_isAlgebraic A B (Or.inl hA)
  by_cases hB : Algebra.IsAlgebraic F B
  · exact rank_sup_le_of_isAlgebraic A B (Or.inr hB)
  rw [← Algebra.transcendental_iff_not_isAlgebraic] at hA hB
  have : Algebra.Transcendental F ↥(A ⊔ B) := .rin

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.T, Algebra.Transcendental, Algebra.Transcendental.infinite, Algebra.transcendental_iff_not_isAlgebraic, Function, Function.surjective_id, IsAlgebraic, Or.inl, Or.inr, RingHom, RingHom.id, Transcendental, inclusion, inclusion_injective, infinite, le_sup_left, rank_sup_le_of_isAlgebraic, ringHom_of_comp_eq
-/
theorem IntermediateField.rank_sup_le
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] (A B : IntermediateField F E) :
    Module.rank F ↥(A ⊔ B) <= Module.rank F A * Module.rank F B := by
  by_cases hA : Algebra.IsAlgebraic F A
  · exact rank_sup_le_of_isAlgebraic A B (Or.inl hA)
  by_cases hB : Algebra.IsAlgebraic F B
  · exact rank_sup_le_of_isAlgebraic A B (Or.inr hB)
  rw [← Algebra.transcendental_iff_not_isAlgebraic] at hA hB
  have : Algebra.Transcendental F ↥(A ⊔ B) := .ringHom_of_comp_eq (RingHom.id F)
    (inclusion le_sup_left) Function.surjective_id (inclusion_injective _) rfl
  have := Algebra.Transcendental.infinite F A
  have := Algebra.Transcendental.infinite F B
  simp_rw [Algebra.Transcendental.rank_eq_cardinalMk]
  rw [sup_def]; rw [mul_mk_eq_max]; rw [← Cardinal.lift_le.{u}]
  refine (lift_cardinalMk_adjoin_le _ _).trans ?_
  calc
    _ <= Cardinal.lift.{v} #F ⊔ Cardinal.lift.{u} (#A ⊔ #B) ⊔ ℵ₀ := by
      gcongr
      rw [Cardinal.lift_le]
      exact (mk_union_le _ _).trans_eq (by simp)
    _ = _ := by
      simp [lift_mk_le_lift_mk_of_injective (algebraMap F A).injective]
