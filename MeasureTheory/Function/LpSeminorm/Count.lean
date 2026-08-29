/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# `L^p`-seminorms on `count` and `dirac`
-/

public section

open MeasureTheory Measure ENNReal Set Filter
variable {α ε : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  [TopologicalSpace ε] [ContinuousENorm ε] {f : α -> ε} {p : Real>=0∞} {x : α}

namespace MeasureTheory

@[simp]
/--
lemma `eLpNorm_dirac` / 引理 `eLpNorm_dirac`

English:
lemma eLpNorm_dirac
  given: (f : α -> ε) (i : α) (hp : p != 0)
  proof: by
  simp_rw [eLpNorm, if_neg hp]
  split_ifs
  · simp [eLpNormEssSup, essSup, limsup, limsSup, Set.Ici_def]
  · simp [eLpNorm', ENNReal.toReal_eq_zero_iff, *]

中文:
引理 eLpNorm_dirac
  条件: (f : α -> ε) (i : α) (hp : p != 0)
  证明: by
  simp_rw [eLpNorm, if_neg hp]
  split_ifs
  · simp [eLpNormEssSup, essSup, limsup, limsSup, Set.Ici_def]
  · simp [eLpNorm', ENNReal.toReal_eq_zero_iff, *]

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_zero_iff, Ici_def, Set.Ici_def, eLpNorm, eLpNormEssSup, essSup, if_neg, limsSup, limsup, simp_rw, split_ifs, toReal_eq_zero_iff
-/
lemma eLpNorm_dirac (f : α -> ε) (i : α) (hp : p != 0) :
    eLpNorm f p (dirac i) = ‖f i‖ₑ := by
  simp_rw [eLpNorm, if_neg hp]
  split_ifs
  · simp [eLpNormEssSup, essSup, limsup, limsSup, Set.Ici_def]
  · simp [eLpNorm', ENNReal.toReal_eq_zero_iff, *]

/--
lemma `enorm_le_eLpNorm_count` / 引理 `enorm_le_eLpNorm_count`

English:
lemma enorm_le_eLpNorm_count
  given: (f : α -> ε) (i : α) (hp : p != 0)
  proof: by
  calc
    ‖f i‖ₑ = eLpNorm f p (dirac i) := by rw [eLpNorm_dirac f i hp]
      _ = eLpNorm f p (count.restrict {i}) := by simp
      _ <= eLpNorm f p count := eLpNorm_restrict_le ..

omit [MeasurableSingletonClass α] in

中文:
引理 enorm_le_eLpNorm_count
  条件: (f : α -> ε) (i : α) (hp : p != 0)
  证明: by
  calc
    ‖f i‖ₑ = eLpNorm f p (dirac i) := by rw [eLpNorm_dirac f i hp]
      _ = eLpNorm f p (count.restrict {i}) := by simp
      _ <= eLpNorm f p count := eLpNorm_restrict_le ..

omit [MeasurableSingletonClass α] in

Depends on / 依赖: count.restrict, eLpNorm, eLpNorm_dirac, eLpNorm_restrict_le, restrict
-/
lemma enorm_le_eLpNorm_count (f : α -> ε) (i : α) (hp : p != 0) :
    ‖f i‖ₑ <= eLpNorm f p count := by
  calc
    ‖f i‖ₑ = eLpNorm f p (dirac i) := by rw [eLpNorm_dirac f i hp]
      _ = eLpNorm f p (count.restrict {i}) := by simp
      _ <= eLpNorm f p count := eLpNorm_restrict_le ..

omit [MeasurableSingletonClass α] in
/--
lemma `eLpNorm_count_lt_top_of_lt` / 引理 `eLpNorm_count_lt_top_of_lt`

English:
lemma eLpNorm_count_lt_top_of_lt
  given: [Finite α] (h : forall i, ‖f i‖ₑ < ∞)
  statement: eLpNorm f p .count < ∞
  proof: by
  have := Fintype.ofFinite α
  refine (eLpNorm_mono_enorm (g := fun _ => Finset.univ.sup (‖f ·‖ₑ)) ?_).trans_lt ?_
  · exact fun x => Finset.le_sup (f := (‖f ·‖ₑ)) (Finset.mem_univ x)
  · exact (memLp_const_enorm <| by simp [h, LT.lt.ne]).eLpNorm_lt_top

中文:
引理 eLpNorm_count_lt_top_of_lt
  条件: [有限 α] (h : 对任意 i, ‖f i‖ₑ < ∞)
  结论: eLpNorm f p .count < ∞
  证明: by
  have := Fintype.ofFinite α
  refine (eLpNorm_mono_enorm (g := fun _ => Finset.univ.sup (‖f ·‖ₑ)) ?_).trans_lt ?_
  · exact fun x => Finset.le_sup (f := (‖f ·‖ₑ)) (Finset.mem_univ x)
  · exact (memLp_const_enorm <| by simp [h, LT.lt.ne]).eLpNorm_lt_top

Depends on / 依赖: Finset, Finset.le_sup, Finset.mem_univ, Finset.univ.sup, Fintype, Fintype.ofFinite, LT.lt.ne, eLpNorm_lt_top, eLpNorm_mono_enorm, le_sup, memLp_const_enorm, mem_univ, ofFinite, trans_lt
-/
lemma eLpNorm_count_lt_top_of_lt [Finite α] (h : forall i, ‖f i‖ₑ < ∞) : eLpNorm f p .count < ∞ := by
  have := Fintype.ofFinite α
  refine (eLpNorm_mono_enorm (g := fun _ => Finset.univ.sup (‖f ·‖ₑ)) ?_).trans_lt ?_
  · exact fun x => Finset.le_sup (f := (‖f ·‖ₑ)) (Finset.mem_univ x)
  · exact (memLp_const_enorm <| by simp [h, LT.lt.ne]).eLpNorm_lt_top

/--
lemma `eLpNorm_count_lt_top` / 引理 `eLpNorm_count_lt_top`

English:
lemma eLpNorm_count_lt_top
  given: [Finite α] (hp : p != 0)
  proof: ⟨fun h i => (enorm_le_eLpNorm_count f i hp).trans_lt h, eLpNorm_count_lt_top_of_lt⟩

中文:
引理 eLpNorm_count_lt_top
  条件: [有限 α] (hp : p != 0)
  证明: ⟨fun h i => (enorm_le_eLpNorm_count f i hp).trans_lt h, eLpNorm_count_lt_top_of_lt⟩

Depends on / 依赖: eLpNorm_count_lt_top_of_lt, enorm_le_eLpNorm_count, trans_lt
-/
lemma eLpNorm_count_lt_top [Finite α] (hp : p != 0) :
    eLpNorm f p .count < ∞ ↔ forall i, ‖f i‖ₑ < ∞ :=
  ⟨fun h i => (enorm_le_eLpNorm_count f i hp).trans_lt h, eLpNorm_count_lt_top_of_lt⟩

end MeasureTheory
