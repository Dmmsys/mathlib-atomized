/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Projective measure families and projective limits

A family of measures indexed by finite sets of `ι` is projective if, for finite sets `J ⊆ I`,
the projection from `∀ i : I, α i` to `∀ i : J, α i` maps `P I` to `P J`.
A measure `μ` is the projective limit of such a family of measures if for all `I : Finset ι`,
the projection from `∀ i, α i` to `∀ i : I, α i` maps `μ` to `P I`.

## Main definitions

* `MeasureTheory.IsProjectiveMeasureFamily`: `P : ∀ J : Finset ι, Measure (∀ j : J, α j)` is
  projective if the projection from `∀ i : I, α i` to `∀ i : J, α i` maps `P I` to `P J`
  for all `J ⊆ I`.
* `MeasureTheory.IsProjectiveLimit`: `μ` is the projective limit of the measure family `P` if for
  all `I : Finset ι`, the map of `μ` by the projection to `I` is `P I`.

## Main statements

* `MeasureTheory.IsProjectiveLimit.unique`: the projective limit of a family of finite measures
  is unique.

-/

@[expose] public section

open Set

namespace MeasureTheory

variable {ι : Type*} {α : ι -> Type*} [forall i, MeasurableSpace (α i)]
  {P : forall J : Finset ι, Measure (forall j : J, α j)}

/--
Definition of `IsProjectiveMeasureFamily` / `IsProjectiveMeasureFamily` 的定义

English:
definition IsProjectiveMeasureFamily
  signature: (P : forall J : Finset ι, Measure (forall j : J, α j))
  body: forall (I J : Finset ι) (hJI : J subseteq I),
    P J = (P I).map (Finset.restrict₂ hJI)

中文:
定义 IsProjectiveMeasureFamily
  签名: (P : 对任意 J : 有限集 ι, 测度 (对任意 j : J, α j))
  定义体: forall (I J : Finset ι) (hJI : J subseteq I),
    P J = (P I).map (Finset.restrict₂ hJI)

Depends on / 依赖: Finset, Finset.restrict, subseteq
-/
def IsProjectiveMeasureFamily (P : forall J : Finset ι, Measure (forall j : J, α j)) : Prop :=
  forall (I J : Finset ι) (hJI : J subseteq I),
    P J = (P I).map (Finset.restrict₂ hJI)

namespace IsProjectiveMeasureFamily

variable {I J : Finset ι}

/--
lemma `eq_zero_of_isEmpty` / 引理 `eq_zero_of_isEmpty`

English:
lemma eq_zero_of_isEmpty
  statement: [h : IsEmpty (Π i, α i)]
  proof: by
  classical
  obtain ⟨i, hi⟩ := isEmpty_pi.mp h
  rw [hP (insert i I) I (I.subset_insert i)]
  have : IsEmpty (Π j : ↑(insert i I), α j) := by simp [hi]
  rw [(P (insert i I)).eq_zero_of_isEmpty]
  simp

中文:
引理 eq_zero_of_isEmpty
  结论: [h : 是空 (Π i, α i)]
  证明: by
  classical
  obtain ⟨i, hi⟩ := isEmpty_pi.mp h
  rw [hP (insert i I) I (I.subset_insert i)]
  have : IsEmpty (Π j : ↑(insert i I), α j) := by simp [hi]
  rw [(P (insert i I)).eq_zero_of_isEmpty]
  simp

Depends on / 依赖: I.subset_insert, IsEmpty, classical, eq_zero_of_isEmpty, insert, isEmpty_pi, isEmpty_pi.mp, subset_insert
-/
lemma eq_zero_of_isEmpty [h : IsEmpty (Π i, α i)]
    (hP : IsProjectiveMeasureFamily P) (I : Finset ι) :
    P I = 0 := by
  classical
  obtain ⟨i, hi⟩ := isEmpty_pi.mp h
  rw [hP (insert i I) I (I.subset_insert i)]
  have : IsEmpty (Π j : ↑(insert i I), α j) := by simp [hi]
  rw [(P (insert i I)).eq_zero_of_isEmpty]
  simp

/--
lemma `measure_univ_eq_of_subset` / 引理 `measure_univ_eq_of_subset`

English:
lemma measure_univ_eq_of_subset
  given: (hP : IsProjectiveMeasureFamily P) (hJI : J subseteq I)
  proof: by
  have : (univ : Set (forall i : I, α i)) =
      Finset.restrict₂ hJI ⁻¹' (univ : Set (forall i : J, α i)) := by
    rw [preimage_univ]
  rw [this]; rw [← Measure.map_apply _ MeasurableSet.univ]
  · rw [hP I J hJI]
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

中文:
引理 measure_univ_eq_of_subset
  条件: (hP : IsProjectiveMeasureFamily P) (hJI : J subseteq I)
  证明: by
  have : (univ : Set (forall i : I, α i)) =
      Finset.restrict₂ hJI ⁻¹' (univ : Set (forall i : J, α i)) := by
    rw [preimage_univ]
  rw [this]; rw [← Measure.map_apply _ MeasurableSet.univ]
  · rw [hP I J hJI]
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

Depends on / 依赖: Finset, Finset.restrict, MeasurableSet, MeasurableSet.univ, Measure, Measure.map_apply, map_apply, measurable_pi_apply, measurable_pi_lambda, preimage_univ
-/
lemma measure_univ_eq_of_subset (hP : IsProjectiveMeasureFamily P) (hJI : J subseteq I) :
    P I univ = P J univ := by
  have : (univ : Set (forall i : I, α i)) =
      Finset.restrict₂ hJI ⁻¹' (univ : Set (forall i : J, α i)) := by
    rw [preimage_univ]
  rw [this]; rw [← Measure.map_apply _ MeasurableSet.univ]
  · rw [hP I J hJI]
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/--
lemma `measure_univ_eq` / 引理 `measure_univ_eq`

English:
lemma measure_univ_eq
  given: (hP : IsProjectiveMeasureFamily P) (I J : Finset ι)
  proof: by
  classical
  rw [← hP.measure_univ_eq_of_subset I.subset_union_left]; rw [← hP.measure_univ_eq_of_subset (I.subset_union_right (s₂ := J))]

中文:
引理 measure_univ_eq
  条件: (hP : IsProjectiveMeasureFamily P) (I J : 有限集 ι)
  证明: by
  classical
  rw [← hP.measure_univ_eq_of_subset I.subset_union_left]; rw [← hP.measure_univ_eq_of_subset (I.subset_union_right (s₂ := J))]

Depends on / 依赖: I.subset_union_left, I.subset_union_right, classical, hP.measure_univ_eq_of_subset, measure_univ_eq_of_subset, subset_union_left, subset_union_right
-/
lemma measure_univ_eq (hP : IsProjectiveMeasureFamily P) (I J : Finset ι) :
    P I univ = P J univ := by
  classical
  rw [← hP.measure_univ_eq_of_subset I.subset_union_left]; rw [← hP.measure_univ_eq_of_subset (I.subset_union_right (s₂ := J))]

/--
lemma `congr_cylinder_of_subset` / 引理 `congr_cylinder_of_subset`

English:
lemma congr_cylinder_of_subset
  statement: (hP : IsProjectiveMeasureFamily P)
  proof: by
  cases isEmpty_or_nonempty (forall i, α i) with
  | inl h =>
    suffices forall I, P I univ = 0 by
      simp only [Measure.measure_univ_eq_zero] at this
      simp [this]
    simpa using eq_zero_of_isEmpty hP
  | inr h =>
    have : S = Finset.restrict₂ hJI ⁻¹' T :=
      eq_of_cylinder_eq_of_

中文:
引理 congr_cylinder_of_subset
  结论: (hP : IsProjectiveMeasureFamily P)
  证明: by
  cases isEmpty_or_nonempty (forall i, α i) with
  | inl h =>
    suffices forall I, P I univ = 0 by
      simp only [Measure.measure_univ_eq_zero] at this
      simp [this]
    simpa using eq_zero_of_isEmpty hP
  | inr h =>
    have : S = Finset.restrict₂ hJI ⁻¹' T :=
      eq_of_cylinder_eq_of_

Depends on / 依赖: Finset, Finset.restrict, Measure, Measure.map_apply, Measure.measure_univ_eq_zero, eq_of_cylinder_eq_of_subset, eq_zero_of_isEmpty, h_eq, isEmpty_or_nonempty, map_apply, measurable_pi_apply, measurable_pi_lambda, measure_univ_eq_zero
-/
lemma congr_cylinder_of_subset (hP : IsProjectiveMeasureFamily P)
    {S : Set (forall i : I, α i)} {T : Set (forall i : J, α i)} (hT : MeasurableSet T)
    (h_eq : cylinder I S = cylinder J T) (hJI : J subseteq I) :
    P I S = P J T := by
  cases isEmpty_or_nonempty (forall i, α i) with
  | inl h =>
    suffices forall I, P I univ = 0 by
      simp only [Measure.measure_univ_eq_zero] at this
      simp [this]
    simpa using eq_zero_of_isEmpty hP
  | inr h =>
    have : S = Finset.restrict₂ hJI ⁻¹' T :=
      eq_of_cylinder_eq_of_subset h_eq hJI
    rw [hP I J hJI]; rw [Measure.map_apply _ hT]; rw [this]
    exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/--
lemma `congr_cylinder` / 引理 `congr_cylinder`

English:
lemma congr_cylinder
  statement: (hP : IsProjectiveMeasureFamily P)
  proof: by
  classical
  let U := Finset.restrict₂ Finset.subset_union_left ⁻¹' S inter
      Finset.restrict₂ Finset.subset_union_right ⁻¹' T
  suffices P (I union J) U = P I S ∧ P (I union J) U = P J T from this.1.symm.trans this.2
  constructor
  · have h_eq_union : cylinder I S = cylinder (I union J) U 

中文:
引理 congr_cylinder
  结论: (hP : IsProjectiveMeasureFamily P)
  证明: by
  classical
  let U := Finset.restrict₂ Finset.subset_union_left ⁻¹' S inter
      Finset.restrict₂ Finset.subset_union_right ⁻¹' T
  suffices P (I union J) U = P I S ∧ P (I union J) U = P J T from this.1.symm.trans this.2
  constructor
  · have h_eq_union : cylinder I S = cylinder (I union J) U 

Depends on / 依赖: Finset, Finset.restrict, Finset.subset_union_left, Finset.subset_union_right, classical, congr_cylinder_of_subset, cylinder, hP.congr_cylinder_of_subset, h_eq, h_eq_union, h_eq_union.symm, inter_cylind, inter_cylinder, inter_self, subset_union_left, subset_union_right, symm.trans
-/
lemma congr_cylinder (hP : IsProjectiveMeasureFamily P)
    {S : Set (forall i : I, α i)} {T : Set (forall i : J, α i)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h_eq : cylinder I S = cylinder J T) :
    P I S = P J T := by
  classical
  let U := Finset.restrict₂ Finset.subset_union_left ⁻¹' S inter
      Finset.restrict₂ Finset.subset_union_right ⁻¹' T
  suffices P (I union J) U = P I S ∧ P (I union J) U = P J T from this.1.symm.trans this.2
  constructor
  · have h_eq_union : cylinder I S = cylinder (I union J) U := by
      rw [← inter_cylinder]; rw [h_eq]; rw [inter_self]
    exact hP.congr_cylinder_of_subset hS h_eq_union.symm Finset.subset_union_left
  · have h_eq_union : cylinder J T = cylinder (I union J) U := by
      rw [← inter_cylinder]; rw [h_eq]; rw [inter_self]
    exact hP.congr_cylinder_of_subset hT h_eq_union.symm Finset.subset_union_right

end IsProjectiveMeasureFamily

/--
Definition of `IsProjectiveLimit` / `IsProjectiveLimit` 的定义

English:
definition IsProjectiveLimit
  signature: (μ : Measure (forall i, α i))
  body: forall I : Finset ι, (μ.map I.restrict) = P I

中文:
定义 IsProjectiveLimit
  签名: (μ : 测度 (对任意 i, α i))
  定义体: forall I : Finset ι, (μ.map I.restrict) = P I

Depends on / 依赖: Finset, I.restrict, restrict
-/
def IsProjectiveLimit (μ : Measure (forall i, α i))
    (P : forall J : Finset ι, Measure (forall j : J, α j)) : Prop :=
  forall I : Finset ι, (μ.map I.restrict) = P I

namespace IsProjectiveLimit

variable {μ ν : Measure (forall i, α i)}

/--
lemma `measure_cylinder` / 引理 `measure_cylinder`

English:
lemma measure_cylinder
  statement: (h : IsProjectiveLimit μ P)
  proof: by
  rw [cylinder]; rw [← Measure.map_apply _ hs]; rw [h I]
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

中文:
引理 measure_cylinder
  结论: (h : IsProjectiveLimit μ P)
  证明: by
  rw [cylinder]; rw [← Measure.map_apply _ hs]; rw [h I]
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

Depends on / 依赖: Measure, Measure.map_apply, cylinder, map_apply, measurable_pi_apply, measurable_pi_lambda
-/
lemma measure_cylinder (h : IsProjectiveLimit μ P)
    (I : Finset ι) {s : Set (forall i : I, α i)} (hs : MeasurableSet s) :
    μ (cylinder I s) = P I s := by
  rw [cylinder]; rw [← Measure.map_apply _ hs]; rw [h I]
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/--
lemma `measure_univ_eq` / 引理 `measure_univ_eq`

English:
lemma measure_univ_eq
  given: (hμ : IsProjectiveLimit μ P) (I : Finset ι)
  proof: by
  rw [← cylinder_univ I]; rw [hμ.measure_cylinder _ MeasurableSet.univ]

中文:
引理 measure_univ_eq
  条件: (hμ : IsProjectiveLimit μ P) (I : 有限集 ι)
  证明: by
  rw [← cylinder_univ I]; rw [hμ.measure_cylinder _ MeasurableSet.univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, cylinder_univ, measure_cylinder
-/
lemma measure_univ_eq (hμ : IsProjectiveLimit μ P) (I : Finset ι) :
    μ univ = P I univ := by
  rw [← cylinder_univ I]; rw [hμ.measure_cylinder _ MeasurableSet.univ]

/--
lemma `isFiniteMeasure` / 引理 `isFiniteMeasure`

English:
lemma isFiniteMeasure
  given: [forall i, IsFiniteMeasure (P i)] (hμ : IsProjectiveLimit μ P)
  proof: by
  constructor
  rw [hμ.measure_univ_eq (∅ : Finset ι)]
  exact measure_lt_top _ _

中文:
引理 isFiniteMeasure
  条件: [对任意 i, 是有限测度 (P i)] (hμ : IsProjectiveLimit μ P)
  证明: by
  constructor
  rw [hμ.measure_univ_eq (∅ : Finset ι)]
  exact measure_lt_top _ _

Depends on / 依赖: Finset, measure_lt_top, measure_univ_eq
-/
lemma isFiniteMeasure [forall i, IsFiniteMeasure (P i)] (hμ : IsProjectiveLimit μ P) :
    IsFiniteMeasure μ := by
  constructor
  rw [hμ.measure_univ_eq (∅ : Finset ι)]
  exact measure_lt_top _ _

/--
lemma `isProbabilityMeasure` / 引理 `isProbabilityMeasure`

English:
lemma isProbabilityMeasure
  given: [forall i, IsProbabilityMeasure (P i)] (hμ : IsProjectiveLimit μ P)
  proof: by
  constructor
  rw [hμ.measure_univ_eq (∅ : Finset ι)]
  exact measure_univ

中文:
引理 isProbabilityMeasure
  条件: [对任意 i, 是概率测度 (P i)] (hμ : IsProjectiveLimit μ P)
  证明: by
  constructor
  rw [hμ.measure_univ_eq (∅ : Finset ι)]
  exact measure_univ

Depends on / 依赖: Finset, measure_univ, measure_univ_eq
-/
lemma isProbabilityMeasure [forall i, IsProbabilityMeasure (P i)] (hμ : IsProjectiveLimit μ P) :
    IsProbabilityMeasure μ := by
  constructor
  rw [hμ.measure_univ_eq (∅ : Finset ι)]
  exact measure_univ

/--
lemma `measure_univ_unique` / 引理 `measure_univ_unique`

English:
lemma measure_univ_unique
  given: (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P)
  proof: by
  rw [hμ.measure_univ_eq (∅ : Finset ι)]; rw [hν.measure_univ_eq (∅ : Finset ι)]

中文:
引理 measure_univ_unique
  条件: (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P)
  证明: by
  rw [hμ.measure_univ_eq (∅ : Finset ι)]; rw [hν.measure_univ_eq (∅ : Finset ι)]

Depends on / 依赖: Finset, measure_univ_eq
-/
lemma measure_univ_unique (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) :
    μ univ = ν univ := by
  rw [hμ.measure_univ_eq (∅ : Finset ι)]; rw [hν.measure_univ_eq (∅ : Finset ι)]

/--
theorem `unique` / 定理 `unique`

English:
theorem unique
  statement: [forall i, IsFiniteMeasure (P i)]
  proof: by
  have : IsFiniteMeasure μ := hμ.isFiniteMeasure
  refine ext_of_generate_finite (measurableCylinders α) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun s hs => ?_) (hμ.measure_univ_unique hν)
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
  rw [hμ.mea

中文:
定理 unique
  结论: [对任意 i, 是有限测度 (P i)]
  证明: by
  have : IsFiniteMeasure μ := hμ.isFiniteMeasure
  refine ext_of_generate_finite (measurableCylinders α) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun s hs => ?_) (hμ.measure_univ_unique hν)
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
  rw [hμ.mea

Depends on / 依赖: IsFiniteMeasure, ext_of_generate_finite, generateFrom_measurableCylinders, generateFrom_measurableCylinders.symm, isFiniteMeasure, isPiSystem_measurableCylinders, measurableCylinders, measure_cylinder, measure_univ_unique, mem_measurableCylinders
-/
theorem unique [forall i, IsFiniteMeasure (P i)]
    (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) :
    μ = ν := by
  have : IsFiniteMeasure μ := hμ.isFiniteMeasure
  refine ext_of_generate_finite (measurableCylinders α) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun s hs => ?_) (hμ.measure_univ_unique hν)
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
  rw [hμ.measure_cylinder _ hS]; rw [hν.measure_cylinder _ hS]

end IsProjectiveLimit

end MeasureTheory
