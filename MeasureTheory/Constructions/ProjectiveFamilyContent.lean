/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.AddContent
public import Mathlib.MeasureTheory.SetAlgebra

/-!
# Additive content built from a projective family of measures

Let `P` be a projective family of measures on a family of measurable spaces indexed by `ι`.
That is, for each finite set `I` of indices, `P I` is a measure on `Π j : I, α j`, and for `J ⊆ I`,
the projection from `Π i : I, α i` to `Π i : J, α i` maps `P I` to `P J`.

We build an additive content `projectiveFamilyContent` on the measurable cylinders, by setting
`projectiveFamilyContent s = P I S` for `s = cylinder I S`, where `I` is a finite set of indices
and `S` is a measurable set in `Π i : I, α i`.

This content will be used to define the projective limit of the family of measures `P`.
For a countable index set and a projective family given by a sequence of kernels,
the projective limit is given by the Ionescu-Tulcea theorem.
For an arbitrary index set but under topological conditions on the spaces, this is the result of
the Kolmogorov extension theorem.
(both results are not yet in Mathlib)

## Main definitions

* `projectiveFamilyContent`: additive content on the measurable cylinders, defined from a projective
  family of measures.

-/

@[expose] public section


open Finset

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} {α : ι -> Type*} {mα : forall i, MeasurableSpace (α i)}
  {P : forall J : Finset ι, Measure (Π j : J, α j)} {s t : Set (Π i, α i)} {I : Finset ι}
  {S : Set (Π i : I, α i)}

section MeasurableCylinders

/--
lemma `isSetAlgebra_measurableCylinders` / 引理 `isSetAlgebra_measurableCylinders`

English:
lemma isSetAlgebra_measurableCylinders
  statement: IsSetAlgebra (measurableCylinders α) where
  proof: empty_mem_measurableCylinders α
  compl_mem _ := compl_mem_measurableCylinders
  union_mem _ _ := union_mem_measurableCylinders

中文:
引理 isSetAlgebra_measurableCylinders
  结论: IsSetAlgebra (measurableCylinders α) where
  证明: empty_mem_measurableCylinders α
  compl_mem _ := compl_mem_measurableCylinders
  union_mem _ _ := union_mem_measurableCylinders

Depends on / 依赖: empty_mem_measurableCylinders
-/
lemma isSetAlgebra_measurableCylinders : IsSetAlgebra (measurableCylinders α) where
  empty_mem := empty_mem_measurableCylinders α
  compl_mem _ := compl_mem_measurableCylinders
  union_mem _ _ := union_mem_measurableCylinders

/--
lemma `isSetRing_measurableCylinders` / 引理 `isSetRing_measurableCylinders`

English:
lemma isSetRing_measurableCylinders
  statement: IsSetRing (measurableCylinders α)
  proof: isSetAlgebra_measurableCylinders.isSetRing

中文:
引理 isSetRing_measurableCylinders
  结论: IsSetRing (measurableCylinders α)
  证明: isSetAlgebra_measurableCylinders.isSetRing

Depends on / 依赖: isSetAlgebra_measurableCylinders, isSetAlgebra_measurableCylinders.isSetRing, isSetRing
-/
lemma isSetRing_measurableCylinders : IsSetRing (measurableCylinders α) :=
  isSetAlgebra_measurableCylinders.isSetRing

/--
lemma `isSetSemiring_measurableCylinders` / 引理 `isSetSemiring_measurableCylinders`

English:
lemma isSetSemiring_measurableCylinders
  statement: MeasureTheory.IsSetSemiring (measurableCylinders α)
  proof: isSetRing_measurableCylinders.isSetSemiring

中文:
引理 isSetSemiring_measurableCylinders
  结论: MeasureTheory.IsSetSemiring (measurableCylinders α)
  证明: isSetRing_measurableCylinders.isSetSemiring

Depends on / 依赖: isSetRing_measurableCylinders, isSetRing_measurableCylinders.isSetSemiring, isSetSemiring
-/
lemma isSetSemiring_measurableCylinders : MeasureTheory.IsSetSemiring (measurableCylinders α) :=
  isSetRing_measurableCylinders.isSetSemiring

end MeasurableCylinders

section ProjectiveFamilyFun

open scoped Classical in
/--
Definition of `projectiveFamilyFun` / `projectiveFamilyFun` 的定义

English:
definition projectiveFamilyFun
  signature: (P : forall J : Finset ι, Measure (Π j : J, α j))
  body: if hs : s in measurableCylinders α
    then P (measurableCylinders.finset hs) (measurableCylinders.set hs) else 0

中文:
定义 projectiveFamilyFun
  签名: (P : 对任意 J : Finset ι, Measure (Π j : J, α j))
  定义体: if hs : s in measurableCylinders α
    then P (measurableCylinders.finset hs) (measurableCylinders.set hs) else 0

Depends on / 依赖: finset, measurableCylinders, measurableCylinders.finset, measurableCylinders.set
-/
noncomputable def projectiveFamilyFun (P : forall J : Finset ι, Measure (Π j : J, α j))
    (s : Set (Π i, α i)) : Real>=0∞ :=
  if hs : s in measurableCylinders α
    then P (measurableCylinders.finset hs) (measurableCylinders.set hs) else 0

/--
lemma `projectiveFamilyFun_congr` / 引理 `projectiveFamilyFun_congr`

English:
lemma projectiveFamilyFun_congr
  statement: (hP : IsProjectiveMeasureFamily P)
  proof: by
  rw [projectiveFamilyFun]; rw [dif_pos hs]
  exact hP.congr_cylinder (measurableCylinders.measurableSet hs) hS
    ((measurableCylinders.eq_cylinder hs).symm.trans hs_eq)

中文:
引理 projectiveFamilyFun_congr
  结论: (hP : IsProjectiveMeasureFamily P)
  证明: by
  rw [projectiveFamilyFun]; rw [dif_pos hs]
  exact hP.congr_cylinder (measurableCylinders.measurableSet hs) hS
    ((measurableCylinders.eq_cylinder hs).symm.trans hs_eq)

Depends on / 依赖: congr_cylinder, dif_pos, eq_cylinder, hP.congr_cylinder, hs_eq, measurableCylinders, measurableCylinders.eq_cylinder, measurableCylinders.measurableSet, measurableSet, projectiveFamilyFun, symm.trans
-/
lemma projectiveFamilyFun_congr (hP : IsProjectiveMeasureFamily P)
    (hs : s in measurableCylinders α) (hs_eq : s = cylinder I S) (hS : MeasurableSet S) :
    projectiveFamilyFun P s = P I S := by
  rw [projectiveFamilyFun]; rw [dif_pos hs]
  exact hP.congr_cylinder (measurableCylinders.measurableSet hs) hS
    ((measurableCylinders.eq_cylinder hs).symm.trans hs_eq)

/--
lemma `projectiveFamilyFun_empty` / 引理 `projectiveFamilyFun_empty`

English:
lemma projectiveFamilyFun_empty
  given: (hP : IsProjectiveMeasureFamily P)
  proof: by
  rw [projectiveFamilyFun_congr hP (empty_mem_measurableCylinders α) (cylinder_empty ∅).symm
    MeasurableSet.empty]; rw [measure_empty]

中文:
引理 projectiveFamilyFun_empty
  条件: (hP : IsProjectiveMeasureFamily P)
  证明: by
  rw [projectiveFamilyFun_congr hP (empty_mem_measurableCylinders α) (cylinder_empty ∅).symm
    MeasurableSet.empty]; rw [measure_empty]

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, cylinder_empty, empty_mem_measurableCylinders, measure_empty, projectiveFamilyFun_congr
-/
lemma projectiveFamilyFun_empty (hP : IsProjectiveMeasureFamily P) :
    projectiveFamilyFun P ∅ = 0 := by
  rw [projectiveFamilyFun_congr hP (empty_mem_measurableCylinders α) (cylinder_empty ∅).symm
    MeasurableSet.empty]; rw [measure_empty]

/--
lemma `projectiveFamilyFun_union` / 引理 `projectiveFamilyFun_union`

English:
lemma projectiveFamilyFun_union
  statement: (hP : IsProjectiveMeasureFamily P)
  proof: by
  obtain ⟨I, S, hS, hs_eq⟩ := (mem_measurableCylinders _).1 hs
  obtain ⟨J, T, hT, ht_eq⟩ := (mem_measurableCylinders _).1 ht
  classical
  let S' := restrict₂ (subset_union_left (s₂ := J)) ⁻¹' S
  let T' := restrict₂ (subset_union_right (s₁ := I)) ⁻¹' T
  have hS' : MeasurableSet S' := measurabl

中文:
引理 projectiveFamilyFun_union
  结论: (hP : IsProjectiveMeasureFamily P)
  证明: by
  obtain ⟨I, S, hS, hs_eq⟩ := (mem_measurableCylinders _).1 hs
  obtain ⟨J, T, hT, ht_eq⟩ := (mem_measurableCylinders _).1 ht
  classical
  let S' := restrict₂ (subset_union_left (s₂ := J)) ⁻¹' S
  let T' := restrict₂ (subset_union_right (s₁ := I)) ⁻¹' T
  have hS' : MeasurableSet S' := measurabl

Depends on / 依赖: MeasurableSet, classical, cylinder, cylinder_eq_cylinder_union, h_eq1, h_eq2, hs_eq, ht_eq, mem_measurableCylinders, subset_union_left, subset_union_right
-/
lemma projectiveFamilyFun_union (hP : IsProjectiveMeasureFamily P)
    (hs : s in measurableCylinders α) (ht : t in measurableCylinders α) (hst : Disjoint s t) :
    projectiveFamilyFun P (s union t) = projectiveFamilyFun P s + projectiveFamilyFun P t := by
  obtain ⟨I, S, hS, hs_eq⟩ := (mem_measurableCylinders _).1 hs
  obtain ⟨J, T, hT, ht_eq⟩ := (mem_measurableCylinders _).1 ht
  classical
  let S' := restrict₂ (subset_union_left (s₂ := J)) ⁻¹' S
  let T' := restrict₂ (subset_union_right (s₁ := I)) ⁻¹' T
  have hS' : MeasurableSet S' := measurable_restrict₂ _ hS
  have hT' : MeasurableSet T' := measurable_restrict₂ _ hT
  have h_eq1 : s = cylinder (I union J) S' := by rw [hs_eq]; exact cylinder_eq_cylinder_union I S J
  have h_eq2 : t = cylinder (I union J) T' := by rw [ht_eq]; exact cylinder_eq_cylinder_union J T I
  have h_eq3 : s union t = cylinder (I union J) (S' union T') := by
    rw [hs_eq]; rw [ht_eq]; exact union_cylinder _ _ _ _
  rw [projectiveFamilyFun_congr hP hs h_eq1 hS']; rw [projectiveFamilyFun_congr hP ht h_eq2 hT']; rw [projectiveFamilyFun_congr hP (union_mem_measurableCylinders hs ht) h_eq3 (hS'.union hT')]
  cases isEmpty_or_nonempty (Π i, α i) with
  | inl h => simp [hP.eq_zero_of_isEmpty]
  | inr h =>
    rw [measure_union _ hT']
    rwa [hs_eq, ht_eq, disjoint_cylinder_iff] at hst

end ProjectiveFamilyFun

section ProjectiveFamilyContent

/--
Definition of `projectiveFamilyContent` / `projectiveFamilyContent` 的定义

English:
definition projectiveFamilyContent
  signature: (hP : IsProjectiveMeasureFamily P)
  body: isSetRing_measurableCylinders.addContent_of_union (projectiveFamilyFun P)
    (projectiveFamilyFun_empty hP) (projectiveFamilyFun_union hP)

中文:
定义 projectiveFamilyContent
  签名: (hP : IsProjectiveMeasureFamily P)
  定义体: isSetRing_measurableCylinders.addContent_of_union (projectiveFamilyFun P)
    (projectiveFamilyFun_empty hP) (projectiveFamilyFun_union hP)

Depends on / 依赖: addContent_of_union, isSetRing_measurableCylinders, isSetRing_measurableCylinders.addContent_of_union, projectiveFamilyFun, projectiveFamilyFun_empty, projectiveFamilyFun_union
-/
noncomputable def projectiveFamilyContent (hP : IsProjectiveMeasureFamily P) :
    AddContent Real>=0∞ (measurableCylinders α) :=
  isSetRing_measurableCylinders.addContent_of_union (projectiveFamilyFun P)
    (projectiveFamilyFun_empty hP) (projectiveFamilyFun_union hP)

/--
lemma `projectiveFamilyContent_eq` / 引理 `projectiveFamilyContent_eq`

English:
lemma projectiveFamilyContent_eq
  given: (hP : IsProjectiveMeasureFamily P)
  proof: rfl

中文:
引理 projectiveFamilyContent_eq
  条件: (hP : IsProjectiveMeasureFamily P)
  证明: rfl
-/
lemma projectiveFamilyContent_eq (hP : IsProjectiveMeasureFamily P) :
    projectiveFamilyContent hP s = projectiveFamilyFun P s := rfl

/--
lemma `projectiveFamilyContent_congr` / 引理 `projectiveFamilyContent_congr`

English:
lemma projectiveFamilyContent_congr
  statement: (hP : IsProjectiveMeasureFamily P) (s : Set (Π i, α i))
  proof: by
  rw [projectiveFamilyContent_eq]; rw [projectiveFamilyFun_congr hP ((mem_measurableCylinders s).mpr ⟨I]; rw [S]; rw [hS]; rw [hs_eq⟩) hs_eq hS]

中文:
引理 projectiveFamilyContent_congr
  结论: (hP : IsProjectiveMeasureFamily P) (s : Set (Π i, α i))
  证明: by
  rw [projectiveFamilyContent_eq]; rw [projectiveFamilyFun_congr hP ((mem_measurableCylinders s).mpr ⟨I]; rw [S]; rw [hS]; rw [hs_eq⟩) hs_eq hS]

Depends on / 依赖: hs_eq, mem_measurableCylinders, projectiveFamilyContent_eq, projectiveFamilyFun_congr
-/
lemma projectiveFamilyContent_congr (hP : IsProjectiveMeasureFamily P) (s : Set (Π i, α i))
    (hs_eq : s = cylinder I S) (hS : MeasurableSet S) :
    projectiveFamilyContent hP s = P I S := by
  rw [projectiveFamilyContent_eq]; rw [projectiveFamilyFun_congr hP ((mem_measurableCylinders s).mpr ⟨I]; rw [S]; rw [hS]; rw [hs_eq⟩) hs_eq hS]

/--
lemma `projectiveFamilyContent_cylinder` / 引理 `projectiveFamilyContent_cylinder`

English:
lemma projectiveFamilyContent_cylinder
  given: (hP : IsProjectiveMeasureFamily P) (hS : MeasurableSet S)
  proof: projectiveFamilyContent_congr _ _ rfl hS

中文:
引理 projectiveFamilyContent_cylinder
  条件: (hP : IsProjectiveMeasureFamily P) (hS : MeasurableSet S)
  证明: projectiveFamilyContent_congr _ _ rfl hS

Depends on / 依赖: projectiveFamilyContent_congr
-/
lemma projectiveFamilyContent_cylinder (hP : IsProjectiveMeasureFamily P) (hS : MeasurableSet S) :
    projectiveFamilyContent hP (cylinder I S) = P I S := projectiveFamilyContent_congr _ _ rfl hS

/--
lemma `projectiveFamilyContent_mono` / 引理 `projectiveFamilyContent_mono`

English:
lemma projectiveFamilyContent_mono
  statement: (hP : IsProjectiveMeasureFamily P)
  proof: addContent_mono isSetSemiring_measurableCylinders hs ht hst

中文:
引理 projectiveFamilyContent_mono
  结论: (hP : IsProjectiveMeasureFamily P)
  证明: addContent_mono isSetSemiring_measurableCylinders hs ht hst

Depends on / 依赖: addContent_mono, isSetSemiring_measurableCylinders
-/
lemma projectiveFamilyContent_mono (hP : IsProjectiveMeasureFamily P)
    (hs : s in measurableCylinders α) (ht : t in measurableCylinders α) (hst : s subseteq t) :
    projectiveFamilyContent hP s <= projectiveFamilyContent hP t :=
  addContent_mono isSetSemiring_measurableCylinders hs ht hst

/--
lemma `projectiveFamilyContent_iUnion_le` / 引理 `projectiveFamilyContent_iUnion_le`

English:
lemma projectiveFamilyContent_iUnion_le
  statement: (hP : IsProjectiveMeasureFamily P)
  proof: calc projectiveFamilyContent hP (⋃ i <= n, s i)
  _ = projectiveFamilyContent hP (⋃ i in range (n + 1), s i) := by
    simp only [mem_range_succ_iff]
  _ <= ∑ i in range (n + 1), projectiveFamilyContent hP (s i) :=
    addContent_biUnion_le isSetRing_measurableCylinders (fun i _ => hs i)

中文:
引理 projectiveFamilyContent_iUnion_le
  结论: (hP : IsProjectiveMeasureFamily P)
  证明: calc projectiveFamilyContent hP (⋃ i <= n, s i)
  _ = projectiveFamilyContent hP (⋃ i in range (n + 1), s i) := by
    simp only [mem_range_succ_iff]
  _ <= ∑ i in range (n + 1), projectiveFamilyContent hP (s i) :=
    addContent_biUnion_le isSetRing_measurableCylinders (fun i _ => hs i)

Depends on / 依赖: addContent_biUnion_le, isSetRing_measurableCylinders, mem_range_succ_iff, projectiveFamilyContent
-/
lemma projectiveFamilyContent_iUnion_le (hP : IsProjectiveMeasureFamily P)
    {s : Nat -> Set (Π i : ι, α i)} (hs : forall n, s n in measurableCylinders α) (n : Nat) :
    projectiveFamilyContent hP (⋃ i <= n, s i)
      <= ∑ i in range (n + 1), projectiveFamilyContent hP (s i) :=
  calc projectiveFamilyContent hP (⋃ i <= n, s i)
  _ = projectiveFamilyContent hP (⋃ i in range (n + 1), s i) := by
    simp only [mem_range_succ_iff]
  _ <= ∑ i in range (n + 1), projectiveFamilyContent hP (s i) :=
    addContent_biUnion_le isSetRing_measurableCylinders (fun i _ => hs i)

/--
lemma `projectiveFamilyContent_ne_top` / 引理 `projectiveFamilyContent_ne_top`

English:
lemma projectiveFamilyContent_ne_top
  statement: [forall J, IsFiniteMeasure (P J)]
  proof: by
  rw [projectiveFamilyContent_eq hP]; rw [projectiveFamilyFun]
  finiteness

中文:
引理 projectiveFamilyContent_ne_top
  结论: [对任意 J, IsFiniteMeasure (P J)]
  证明: by
  rw [projectiveFamilyContent_eq hP]; rw [projectiveFamilyFun]
  finiteness

Depends on / 依赖: finiteness, projectiveFamilyContent_eq, projectiveFamilyFun
-/
lemma projectiveFamilyContent_ne_top [forall J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) :
    projectiveFamilyContent hP s != ∞ := by
  rw [projectiveFamilyContent_eq hP]; rw [projectiveFamilyFun]
  finiteness

/--
lemma `projectiveFamilyContent_sdiff` / 引理 `projectiveFamilyContent_sdiff`

English:
lemma projectiveFamilyContent_sdiff
  statement: (hP : IsProjectiveMeasureFamily P)
  proof: le_addContent_sdiff (projectiveFamilyContent hP) isSetRing_measurableCylinders hs ht

@[deprecated (since := "2026-06-03")]
alias projectiveFamilyContent_diff := projectiveFamilyContent_sdiff

中文:
引理 projectiveFamilyContent_sdiff
  结论: (hP : IsProjectiveMeasureFamily P)
  证明: le_addContent_sdiff (projectiveFamilyContent hP) isSetRing_measurableCylinders hs ht

@[deprecated (since := "2026-06-03")]
alias projectiveFamilyContent_diff := projectiveFamilyContent_sdiff

Depends on / 依赖: isSetRing_measurableCylinders, le_addContent_sdiff, projectiveFamilyContent
-/
lemma projectiveFamilyContent_sdiff (hP : IsProjectiveMeasureFamily P)
    (hs : s in measurableCylinders α) (ht : t in measurableCylinders α) :
    projectiveFamilyContent hP s - projectiveFamilyContent hP t
      <= projectiveFamilyContent hP (s \ t) :=
  le_addContent_sdiff (projectiveFamilyContent hP) isSetRing_measurableCylinders hs ht

@[deprecated (since := "2026-06-03")]
alias projectiveFamilyContent_diff := projectiveFamilyContent_sdiff

/--
lemma `projectiveFamilyContent_sdiff_of_subset` / 引理 `projectiveFamilyContent_sdiff_of_subset`

English:
lemma projectiveFamilyContent_sdiff_of_subset
  statement: [forall J, IsFiniteMeasure (P J)]
  proof: addContent_sdiff_of_ne_top (projectiveFamilyContent hP) isSetRing_measurableCylinders
    (fun _ _ => projectiveFamilyContent_ne_top hP) hs ht hts

@[deprecated (since := "2026-06-03")]
alias projectiveFamilyContent_diff_of_subset := projectiveFamilyContent_sdiff_of_subset

中文:
引理 projectiveFamilyContent_sdiff_of_subset
  结论: [对任意 J, IsFiniteMeasure (P J)]
  证明: addContent_sdiff_of_ne_top (projectiveFamilyContent hP) isSetRing_measurableCylinders
    (fun _ _ => projectiveFamilyContent_ne_top hP) hs ht hts

@[deprecated (since := "2026-06-03")]
alias projectiveFamilyContent_diff_of_subset := projectiveFamilyContent_sdiff_of_subset

Depends on / 依赖: addContent_sdiff_of_ne_top, isSetRing_measurableCylinders, projectiveFamilyContent, projectiveFamilyContent_ne_top
-/
lemma projectiveFamilyContent_sdiff_of_subset [forall J, IsFiniteMeasure (P J)]
    (hP : IsProjectiveMeasureFamily P) (hs : s in measurableCylinders α)
    (ht : t in measurableCylinders α) (hts : t subseteq s) :
    projectiveFamilyContent hP (s \ t)
      = projectiveFamilyContent hP s - projectiveFamilyContent hP t :=
  addContent_sdiff_of_ne_top (projectiveFamilyContent hP) isSetRing_measurableCylinders
    (fun _ _ => projectiveFamilyContent_ne_top hP) hs ht hts

@[deprecated (since := "2026-06-03")]
alias projectiveFamilyContent_diff_of_subset := projectiveFamilyContent_sdiff_of_subset

end ProjectiveFamilyContent

end MeasureTheory
